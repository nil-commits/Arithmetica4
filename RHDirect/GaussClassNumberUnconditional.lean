import RHDirect.Stage9LandauSiegel
import RHDirect.Stage9QuadraticFields
import RHDirect.Stage6ClassNumberFormula
import RHDirect.Stage7DedekindZeta
import RHDirect.Stage3RealAnalyticLandau
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.RingTheory.Conductor
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# RHDirect.GaussClassNumberUnconditional

Unconditional (`0` `sorry`, `0` custom `axiom`, `0` proxies, `0` extra hypotheses) Lean 4
formalization of:
1. **Imaginary Quadratic Number Fields `ImagQuadField d = ℚ(√(-d))`** for every squarefree `d > 0`,
   with native `NumberField (ImagQuadField d)`, ring of integers `𝓞 (ImagQuadField d) = ℤ[ω_d]`,
   exact discriminant `NumberField.discr (ImagQuadField d) = -(imagQuadDiscNat d : ℤ)`,
   exact unit group cardinality `Nat.card (𝓞 (ImagQuadField d))ˣ = imagQuadUnitCard d` (`4` for
   `d = 1`, `6` for `d = 3`, `2` otherwise), and primitive odd real Kronecker character
   `imagQuadChar d : DirichletCharacter ℂ (imagQuadDiscNat d)`.
2. **Exact Imaginary Quadratic Dedekind Zeta Factorization & Residue at `s = 1`**:
   `Stage7DedekindZeta.dedekindZeta (ImagQuadField d) s = riemannZeta s * LFunction (imagQuadChar d) s`
   for `1 < s.re`, and `lim_{σ → 1⁺} (σ - 1) (dedekindZeta (ImagQuadField d) σ).re = (LFunction (imagQuadChar d) 1).re`.
3. **Genuine Analytic Class Number Formula on Native `NumberField.classNumber`**:
   via ideal-class bijection `ClassIdeals K C ↔ (A \ {0}) / (𝓞 K)ˣ`, 2D Euclidean lattice
   embedding & fundamental-domain disk tiling, and Abelian summation:
   ```
   (NumberField.classNumber (ImagQuadField d) : ℝ) =
     (imagQuadUnitCard d : ℝ) * Real.sqrt (imagQuadDiscNat d : ℝ) / (2 * Real.pi) *
       (DirichletCharacter.LFunction (imagQuadChar d) 1).re
   ```
4. **Genuine Unconditional Heilbronn–Siegel & Gauss Class Number Problem on Native
   `NumberField.classNumber`**:
   - `heilbronn_siegel_native_classNumber_lower_bound`:
     `∀ ε > 0, ∃ C > 0, ∀ d > 0, Squarefree d → C * d^(1/2 - ε) ≤ NumberField.classNumber (ImagQuadField d)`.
   - `gauss_classNumber_problem_native_unconditional`:
     `∀ M : ℕ, ∃ D₀ : ℕ, ∀ d ≥ D₀, Squarefree d → M ≤ NumberField.classNumber (ImagQuadField d)`.
-/

noncomputable section

open Complex DirichletCharacter Finset Filter Topology IsDedekindDomain MeasureTheory Set
open RHDirect.Stage6ClassNumberFormula RHDirect.Stage7DedekindZeta
open RHDirect.Stage9LandauSiegel RHDirect.Stage9QuadraticFields
open RHDirect.Stage3RealAnalyticLandau
open scoped BigOperators NumberField ENNReal Pointwise nonZeroDivisors

namespace RHDirect.GaussClassNumber

/-! ## Section 1: Imaginary Quadratic Number Fields `ℚ(√(-d))`, `𝓞 K`, Discriminant, & Units -/

section ImaginaryQuadraticFields

/-- Positive parameter `max 1 d` (equals `d` whenever `0 < d`), ensuring unconditional `Field` and
`NumberField` instances on `ImagQuadField d` for every `d : ℕ`. -/
abbrev imagQuadParam (d : ℕ) : ℕ := if d = 0 then 1 else d

lemma imagQuadParam_eq_self {d : ℕ} (hd : 0 < d) : imagQuadParam d = d :=
  if_neg hd.ne'

lemma imagQuadParam_pos (d : ℕ) : 0 < imagQuadParam d := by
  unfold imagQuadParam; split_ifs <;> omega

instance imagQuadParam_neZero (d : ℕ) : NeZero (imagQuadParam d) :=
  ⟨(imagQuadParam_pos d).ne'⟩

/-- Concrete imaginary quadratic number field `ℚ(√(-d)) := QuadraticAlgebra ℚ (-d) 0` (for `d > 0`). -/
abbrev ImagQuadField (d : ℕ) : Type := QuadraticAlgebra ℚ (-(imagQuadParam d : ℚ)) 0

/-- Absolute value of the fundamental discriminant `|D|`:
`d` if `d ≡ 3 [MOD 4]`, and `4 * d` otherwise (for `d > 0`). -/
def imagQuadDiscNat (d : ℕ) : ℕ :=
  let m := imagQuadParam d
  if m % 4 = 3 then m else 4 * m

lemma imagQuadDiscNat_eq {d : ℕ} (hd : 0 < d) :
    imagQuadDiscNat d = if d % 4 = 3 then d else 4 * d := by
  unfold imagQuadDiscNat
  rw [imagQuadParam_eq_self hd]

lemma imagQuadDiscNat_pos (d : ℕ) : 0 < imagQuadDiscNat d := by
  unfold imagQuadDiscNat
  have hm := imagQuadParam_pos d
  dsimp only; split_ifs <;> omega

instance imagQuadDiscNat_neZero (d : ℕ) : NeZero (imagQuadDiscNat d) :=
  ⟨(imagQuadDiscNat_pos d).ne'⟩

lemma le_imagQuadDiscNat {d : ℕ} (hd : 0 < d) : d ≤ imagQuadDiscNat d := by
  rw [imagQuadDiscNat_eq hd]; split_ifs <;> omega

lemma imagQuadDiscNat_le_four_mul {d : ℕ} (hd : 0 < d) : imagQuadDiscNat d ≤ 4 * d := by
  rw [imagQuadDiscNat_eq hd]; split_ifs <;> omega

/-- Number of roots of unity (unit group cardinality) `w_K` in `𝓞 (ℚ(√(-d)))`:
`4` for `d = 1` (`ℚ(i)`), `6` for `d = 3` (`ℚ(√(-3))`), and `2` for all other squarefree `d > 0`. -/
def imagQuadUnitCard (d : ℕ) : ℕ :=
  if d = 1 then 4 else if d = 3 then 6 else 2

lemma two_le_imagQuadUnitCard (d : ℕ) : 2 ≤ imagQuadUnitCard d := by
  unfold imagQuadUnitCard; split_ifs <;> omega

lemma imagQuadUnitCard_pos (d : ℕ) : 0 < imagQuadUnitCard d := by
  have := two_le_imagQuadUnitCard d; omega

/-- Every negative rational `-(m : ℚ)` (`m > 0`) is not a rational square. -/
theorem imagQuadField_irred (d : ℕ) :
    ∀ r : ℚ, r ^ 2 ≠ -(imagQuadParam d : ℚ) + 0 * r := by
  intro r hr
  have hm : (0 : ℚ) < (imagQuadParam d : ℚ) := Nat.cast_pos.mpr (imagQuadParam_pos d)
  have hsq : (0 : ℚ) ≤ r ^ 2 := sq_nonneg r
  linarith

instance imagQuadField_fact_irred (d : ℕ) :
    Fact (∀ r : ℚ, r ^ 2 ≠ -(imagQuadParam d : ℚ) + 0 * r) :=
  ⟨imagQuadField_irred d⟩

instance imagQuadField_field (d : ℕ) : Field (ImagQuadField d) :=
  QuadraticAlgebra.instField

/-- Exact degree `[ℚ(√(-d)) : ℚ] = 2`. -/
theorem imagQuadField_finrank (d : ℕ) :
    Module.finrank ℚ (ImagQuadField d) = 2 := by
  have h := Module.finrank_eq_card_basis (QuadraticAlgebra.basis (-(imagQuadParam d : ℚ)) (0 : ℚ))
  simpa using h

instance imagQuadField_numberField (d : ℕ) : NumberField (ImagQuadField d) where
  to_charZero := QuadraticAlgebra.instCharZero
  to_finiteDimensional :=
    Module.Finite.of_basis (QuadraticAlgebra.basis (-(imagQuadParam d : ℚ)) (0 : ℚ))

/-- Helper: entries of `Algebra.leftMulMatrix (QuadraticAlgebra.basis (-m) 0) x`. -/
private lemma imagQuadField_leftMulMatrix_entries (d : ℕ) (x : ImagQuadField d) :
    let b := QuadraticAlgebra.basis (-(imagQuadParam d : ℚ)) (0 : ℚ)
    Algebra.leftMulMatrix b x 0 0 = x.re ∧
    Algebra.leftMulMatrix b x 1 0 = x.im ∧
    Algebra.leftMulMatrix b x 0 1 = -(imagQuadParam d : ℚ) * x.im ∧
    Algebra.leftMulMatrix b x 1 1 = x.re := by
  set b := QuadraticAlgebra.basis (-(imagQuadParam d : ℚ)) (0 : ℚ)
  have hb0 : b 0 = 1 := by
    apply (QuadraticAlgebra.linearEquivTuple (-(imagQuadParam d : ℚ)) (0 : ℚ)).injective
    ext i; fin_cases i <;>
      simp [b, QuadraticAlgebra.basis, QuadraticAlgebra.linearEquivTuple_apply,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hb1 : b 1 = ⟨0, 1⟩ := by
    apply (QuadraticAlgebra.linearEquivTuple (-(imagQuadParam d : ℚ)) (0 : ℚ)).injective
    ext i; fin_cases i <;>
      simp [b, QuadraticAlgebra.basis, QuadraticAlgebra.linearEquivTuple_apply]
  have hrepr : ∀ (z : ImagQuadField d), b.repr z 0 = z.re ∧ b.repr z 1 = z.im := fun z => by
    constructor <;> simp [b, QuadraticAlgebra.basis, QuadraticAlgebra.linearEquivTuple_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Algebra.leftMulMatrix_eq_repr_mul, hb0, mul_one]; exact (hrepr x).1
  · rw [Algebra.leftMulMatrix_eq_repr_mul, hb0, mul_one]; exact (hrepr x).2
  · rw [Algebra.leftMulMatrix_eq_repr_mul, hb1, (hrepr _).1]
    simp [QuadraticAlgebra.re_mul]
  · rw [Algebra.leftMulMatrix_eq_repr_mul, hb1, (hrepr _).2]
    simp [QuadraticAlgebra.im_mul]

/-- Explicit `Algebra.norm ℚ` formula on `ImagQuadField d`: `N(u + v √(-d)) = u^2 + d * v^2`. -/
theorem imagQuadField_norm_eq (d : ℕ) (x : ImagQuadField d) :
    Algebra.norm ℚ x = x.re ^ 2 + (imagQuadParam d : ℚ) * x.im ^ 2 := by
  rw [Algebra.norm_eq_matrix_det (QuadraticAlgebra.basis (-(imagQuadParam d : ℚ)) (0 : ℚ)) x,
    Matrix.det_fin_two]
  obtain ⟨h00, h10, h01, h11⟩ := imagQuadField_leftMulMatrix_entries d x
  rw [h00, h10, h01, h11]; ring

theorem imagQuadField_norm_eq_of_pos {d : ℕ} (hd : 0 < d) (x : ImagQuadField d) :
    Algebra.norm ℚ x = x.re ^ 2 + (d : ℚ) * x.im ^ 2 := by
  rw [imagQuadField_norm_eq]
  congr 2
  exact_mod_cast imagQuadParam_eq_self hd

/-- Nonnegativity of `Algebra.norm ℚ` on `ImagQuadField d`. -/
theorem imagQuadField_norm_nonneg (d : ℕ) (x : ImagQuadField d) :
    0 ≤ Algebra.norm ℚ x := by
  rw [imagQuadField_norm_eq]
  positivity

/-- Explicit `Algebra.trace ℚ` formula on `ImagQuadField d`: `Tr(u + v √(-d)) = 2 * u`. -/
theorem imagQuadField_trace_eq (d : ℕ) (x : ImagQuadField d) :
    Algebra.trace ℚ (ImagQuadField d) x = 2 * x.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (-(imagQuadParam d : ℚ)) (0 : ℚ)) x,
    Matrix.trace_fin_two]
  obtain ⟨h00, _, _, h11⟩ := imagQuadField_leftMulMatrix_entries d x
  rw [h00, h11]; ring

/-- Standard integral generator `ω_d` of `𝓞 (ImagQuadField d)`:
- `(1 + √(-d)) / 2` if `d ≡ 3 [MOD 4]`
- `√(-d)` otherwise. -/
def imagQuadGenVal (d : ℕ) : ImagQuadField d :=
  if imagQuadParam d % 4 = 3 then ⟨1 / 2, 1 / 2⟩ else ⟨0, 1⟩

/-- Defining monic quadratic polynomial `f_d(X) ∈ ℤ[X]` of `ω_d`:
- `X^2 - X + (d + 1)/4` if `d ≡ 3 [MOD 4]`
- `X^2 + d` otherwise. -/
def imagQuadMinPolyInt (d : ℕ) : Polynomial ℤ :=
  let m := imagQuadParam d
  if m % 4 = 3 then
    Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((m : ℤ) + 1) / 4)
  else
    Polynomial.X ^ 2 + Polynomial.C (m : ℤ)

theorem imagQuadMinPolyInt_monic (d : ℕ) : (imagQuadMinPolyInt d).Monic := by
  unfold imagQuadMinPolyInt
  dsimp only
  split_ifs
  · have hdeg1 : (Polynomial.X - Polynomial.C (((imagQuadParam d : ℤ) + 1) / 4) : Polynomial ℤ).degree <
        (Polynomial.X ^ 2 : Polynomial ℤ).degree := by
      have h1 : (Polynomial.X : Polynomial ℤ).degree = 1 := Polynomial.degree_X
      have h2 : (Polynomial.X ^ 2 : Polynomial ℤ).degree = 2 := by
        rw [Polynomial.degree_X_pow]; rfl
      have hc : (Polynomial.C (((imagQuadParam d : ℤ) + 1) / 4) : Polynomial ℤ).degree ≤ 0 :=
        Polynomial.degree_C_le
      have hle := Polynomial.degree_sub_le (Polynomial.X : Polynomial ℤ)
        (Polynomial.C (((imagQuadParam d : ℤ) + 1) / 4))
      rw [h1] at hle
      rw [h2]
      exact lt_of_le_of_lt hle (by
        have : max (1 : WithBot ℕ)
            (Polynomial.C (((imagQuadParam d : ℤ) + 1) / 4) : Polynomial ℤ).degree ≤ 1 :=
          max_le le_rfl (le_trans hc (by decide))
        exact lt_of_le_of_lt this (by decide))
    rw [show Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((imagQuadParam d : ℤ) + 1) / 4) =
      Polynomial.X ^ 2 - (Polynomial.X - Polynomial.C (((imagQuadParam d : ℤ) + 1) / 4)) by ring]
    exact (Polynomial.monic_X_pow 2).sub_of_left hdeg1
  · exact Polynomial.monic_X_pow_add_C (imagQuadParam d : ℤ) (by norm_num)

theorem imagQuadMinPolyInt_natDegree (d : ℕ) : (imagQuadMinPolyInt d).natDegree = 2 := by
  unfold imagQuadMinPolyInt
  dsimp only
  split_ifs
  · have hdeg1 : (Polynomial.X - Polynomial.C (((imagQuadParam d : ℤ) + 1) / 4) : Polynomial ℤ).natDegree <
        (Polynomial.X ^ 2 : Polynomial ℤ).natDegree := by
      rw [Polynomial.natDegree_X_pow]
      have hle := Polynomial.natDegree_sub_le (Polynomial.X : Polynomial ℤ)
        (Polynomial.C (((imagQuadParam d : ℤ) + 1) / 4))
      rw [Polynomial.natDegree_X, Polynomial.natDegree_C] at hle
      omega
    rw [show Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((imagQuadParam d : ℤ) + 1) / 4) =
      Polynomial.X ^ 2 - (Polynomial.X - Polynomial.C (((imagQuadParam d : ℤ) + 1) / 4)) by ring,
      Polynomial.natDegree_sub_eq_left_of_natDegree_lt hdeg1, Polynomial.natDegree_X_pow]
  · rw [show Polynomial.X ^ 2 + Polynomial.C (imagQuadParam d : ℤ) =
      Polynomial.X ^ 2 - Polynomial.C (-(imagQuadParam d : ℤ)) by simp,
      Polynomial.natDegree_X_pow_sub_C]

theorem imagQuadGenVal_aeval_zero (d : ℕ) :
    Polynomial.aeval (imagQuadGenVal d) (imagQuadMinPolyInt d) = 0 := by
  unfold imagQuadMinPolyInt imagQuadGenVal
  dsimp only
  split_ifs with h3
  · have hm4 : ((imagQuadParam d : ℤ) + 1) / 4 * 4 = (imagQuadParam d : ℤ) + 1 := by omega
    have hq4 : ((((imagQuadParam d : ℤ) + 1) / 4 : ℤ) : ℚ) = ((imagQuadParam d : ℚ) + 1) / 4 := by
      have hq : ((((imagQuadParam d : ℤ) + 1) / 4 : ℤ) : ℚ) * 4 = (imagQuadParam d : ℚ) + 1 := by
        exact_mod_cast hm4
      linarith
    rw [map_add, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast, sq]
    ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.re_zero]
      rw [hq4]; ring
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_sub, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.im_intCast, QuadraticAlgebra.im_zero]
      ring
  · rw [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast, sq]
    ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_zero,
        Int.cast_natCast, QuadraticAlgebra.re_natCast]
      ring
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_zero,
        Int.cast_natCast, QuadraticAlgebra.im_natCast]
      ring

theorem imagQuadGenVal_isIntegral (d : ℕ) :
    IsIntegral ℤ (imagQuadGenVal d) :=
  ⟨imagQuadMinPolyInt d, imagQuadMinPolyInt_monic d, by
    simpa [Polynomial.aeval_def] using imagQuadGenVal_aeval_zero d⟩

/-- The integral generator `ω_d` as an element of `𝓞 (ImagQuadField d)`. -/
def imagQuadIntGen (d : ℕ) : 𝓞 (ImagQuadField d) :=
  ⟨imagQuadGenVal d, imagQuadGenVal_isIntegral d⟩

/-- Helper: squarefree `d` satisfies `d % 4 ≠ 0`. -/
lemma squarefree_mod_four_ne_zero' {d : ℕ} (hsf : Squarefree d) : d % 4 ≠ 0 := by
  intro h0
  have hdvd : 2 * 2 ∣ d := by omega
  exact (by norm_num : ¬ IsUnit (2 : ℕ)) (hsf 2 hdvd)

/-- **Exact Integral Characterization of `𝓞 (ImagQuadField d)`**:
for every `d > 0` squarefree, `x ∈ 𝓞 (ImagQuadField d)` iff `∃ a b : ℤ, x = a + b * ω_d`! -/
theorem mem_ringOfIntegers_imagQuadField_iff {d : ℕ} (hd : 0 < d) (hsf : Squarefree d)
    (x : ImagQuadField d) :
    IsIntegral ℤ x ↔ ∃ a b : ℤ, x = (a : ImagQuadField d) + (b : ImagQuadField d) * imagQuadGenVal d := by
  have hm : imagQuadParam d = d := imagQuadParam_eq_self hd
  constructor
  · intro hx
    have hnorm_int : IsIntegral ℤ (Algebra.norm ℚ x) := Algebra.isIntegral_norm ℚ hx
    have hx1_int : IsIntegral ℤ (x + 1) := hx.add isIntegral_one
    have hnorm1_int : IsIntegral ℤ (Algebra.norm ℚ (x + 1)) := Algebra.isIntegral_norm ℚ hx1_int
    obtain ⟨c, hc⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hnorm_int
    obtain ⟨c₁, hc₁⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hnorm1_int
    have hnc : x.re ^ 2 + (d : ℚ) * x.im ^ 2 = (c : ℚ) := by
      rw [← imagQuadField_norm_eq_of_pos hd x]; exact hc.symm
    have hnc1 : (x.re + 1) ^ 2 + (d : ℚ) * x.im ^ 2 = (c₁ : ℚ) := by
      have h := imagQuadField_norm_eq_of_pos hd (x + 1)
      have hre : (x + 1).re = x.re + 1 := by simp [QuadraticAlgebra.re_one]
      have him : (x + 1).im = x.im := by simp [QuadraticAlgebra.im_one]
      rw [hre, him] at h
      rw [← h]; exact hc₁.symm
    set a : ℤ := c₁ - c - 1
    have ha : (2 : ℚ) * x.re = (a : ℚ) := by
      push_cast [a]; linarith
    set v2 : ℚ := 2 * x.im
    have hv2_sq : (d : ℚ) * v2 ^ 2 = ((4 * c - a ^ 2 : ℤ) : ℚ) := by
      dsimp only [v2]; push_cast; nlinarith
    have hv2_den : v2.den = 1 := by
      have hmul : (v2.num : ℚ) = v2 * (v2.den : ℚ) := (Rat.mul_den_eq_num v2).symm
      have hq_eq : (((d * v2.num.natAbs ^ 2 : ℕ) : ℤ) : ℚ) =
          (((4 * c - a ^ 2) * ((v2.den ^ 2 : ℕ) : ℤ) : ℤ) : ℚ) := by
        push_cast
        rw [sq_abs, hmul, mul_pow]
        have h := hv2_sq
        push_cast at h
        linear_combination (v2.den : ℚ) ^ 2 * h
      have hz_eq : ((d * v2.num.natAbs ^ 2 : ℕ) : ℤ) =
          (4 * c - a ^ 2) * ((v2.den ^ 2 : ℕ) : ℤ) := Int.cast_injective hq_eq
      have hden_dvd_z : ((v2.den ^ 2 : ℕ) : ℤ) ∣ ((d * v2.num.natAbs ^ 2 : ℕ) : ℤ) :=
        ⟨4 * c - a ^ 2, by linarith⟩
      have hden_dvd : v2.den ^ 2 ∣ d * v2.num.natAbs ^ 2 := Int.ofNat_dvd.mp hden_dvd_z
      have hcop : (v2.den ^ 2).Coprime (v2.num.natAbs ^ 2) :=
        (v2.reduced.symm.pow_left 2).pow_right 2
      have hden_dvd_d : v2.den ^ 2 ∣ d := hcop.dvd_of_dvd_mul_right hden_dvd
      have hu : IsUnit v2.den := hsf v2.den (by simpa [sq] using hden_dvd_d)
      exact Nat.isUnit_iff.mp hu
    set b : ℤ := v2.num
    have hb : (2 : ℚ) * x.im = (b : ℚ) := by
      have hmul := (Rat.mul_den_eq_num v2).symm
      rw [hv2_den, Nat.cast_one, mul_one] at hmul
      exact hmul.symm
    have hcong_q : ((a ^ 2 + (d : ℤ) * b ^ 2 : ℤ) : ℚ) = ((4 * c : ℤ) : ℚ) := by
      have h1 : (b : ℚ) = v2 := hb.symm
      push_cast
      rw [h1]
      have h2 := hv2_sq
      push_cast at h2
      linarith
    have hcong : a ^ 2 + (d : ℤ) * b ^ 2 = 4 * c := Int.cast_injective hcong_q
    have hz4 : ((a : ZMod 4) ^ 2 + (d : ZMod 4) * (b : ZMod 4) ^ 2) = 0 := by
      have h := congrArg (Int.cast (R := ZMod 4)) hcong
      have h4 : (4 : ZMod 4) = 0 := by decide
      simpa [h4] using h
    have hd_mod4_ne0 : d % 4 ≠ 0 := squarefree_mod_four_ne_zero' hsf
    by_cases hd3 : d % 4 = 3
    · have hd_z4 : (d : ZMod 4) = 3 := by
        rw [← Nat.cast_ofNat (n := 3), ZMod.natCast_eq_natCast_iff]; exact hd3
      rw [hd_z4] at hz4
      have hab_z2 : (a : ZMod 2) = (b : ZMod 2) := by
        have hcast : ∀ n : ℤ, (n : ZMod 2) = ZMod.cast (n : ZMod 4) := fun n => by
          rw [ZMod.cast_intCast (by norm_num : 2 ∣ 4)]
        rw [hcast a, hcast b]
        generalize ha4 : (a : ZMod 4) = xa at hz4 ⊢
        generalize hb4 : (b : ZMod 4) = xb at hz4 ⊢
        fin_cases xa <;> fin_cases xb <;> first | decide | (exfalso; revert hz4; decide)
      have hpar : (a - b) % 2 = 0 := by
        have h0 : ((a - b : ℤ) : ZMod 2) = 0 := by push_cast; rw [hab_z2, sub_self]
        exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) 2).mp h0)
      refine ⟨(a - b) / 2, b, ?_⟩
      have hab2 : ((a - b) / 2 : ℤ) * 2 = a - b := by omega
      have hab_q : (((a - b) / 2 : ℤ) : ℚ) = ((a : ℚ) - (b : ℚ)) / 2 := by
        have hq : (((a - b) / 2 : ℤ) : ℚ) * 2 = (a : ℚ) - (b : ℚ) := by exact_mod_cast hab2
        linarith
      unfold imagQuadGenVal
      rw [if_pos (by rw [hm]; exact hd3)]
      ext
      · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
          QuadraticAlgebra.im_intCast]
        rw [hab_q]; linarith
      · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast,
          QuadraticAlgebra.im_intCast, zero_mul, add_zero, zero_add]
        linarith
    · have hd_cases : (d : ZMod 4) = 1 ∨ (d : ZMod 4) = 2 := by
        have h12 : d % 4 = 1 ∨ d % 4 = 2 := by omega
        rcases h12 with h1 | h2
        · left; rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]; exact h1
        · right; rw [← Nat.cast_ofNat (n := 2), ZMod.natCast_eq_natCast_iff]; exact h2
      have hab_z2 : (a : ZMod 2) = 0 ∧ (b : ZMod 2) = 0 := by
        have hcast : ∀ n : ℤ, (n : ZMod 2) = ZMod.cast (n : ZMod 4) := fun n => by
          rw [ZMod.cast_intCast (by norm_num : 2 ∣ 4)]
        rw [hcast a, hcast b]
        rcases hd_cases with h1 | h2
        · rw [h1] at hz4
          generalize ha4 : (a : ZMod 4) = xa at hz4 ⊢
          generalize hb4 : (b : ZMod 4) = xb at hz4 ⊢
          fin_cases xa <;> fin_cases xb <;> first | decide | (exfalso; revert hz4; decide)
        · rw [h2] at hz4
          generalize ha4 : (a : ZMod 4) = xa at hz4 ⊢
          generalize hb4 : (b : ZMod 4) = xb at hz4 ⊢
          fin_cases xa <;> fin_cases xb <;> first | decide | (exfalso; revert hz4; decide)
      have ha_ev : a % 2 = 0 :=
        Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mp hab_z2.1)
      have hb_ev : b % 2 = 0 :=
        Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd b 2).mp hab_z2.2)
      refine ⟨a / 2, b / 2, ?_⟩
      have ha2 : (a / 2 : ℤ) * 2 = a := by omega
      have hb2 : (b / 2 : ℤ) * 2 = b := by omega
      have ha_q : ((a / 2 : ℤ) : ℚ) = (a : ℚ) / 2 := by
        have hq : ((a / 2 : ℤ) : ℚ) * 2 = (a : ℚ) := by exact_mod_cast ha2
        linarith
      have hb_q : ((b / 2 : ℤ) : ℚ) = (b : ℚ) / 2 := by
        have hq : ((b / 2 : ℤ) : ℚ) * 2 = (b : ℚ) := by exact_mod_cast hb2
        linarith
      unfold imagQuadGenVal
      rw [if_neg (by rw [hm]; exact hd3)]
      ext
      · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
          QuadraticAlgebra.im_intCast, mul_zero, zero_mul, add_zero]
        rw [ha_q]; linarith
      · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast,
          QuadraticAlgebra.im_intCast, mul_one, zero_mul, add_zero, zero_add]
        rw [hb_q]; linarith
  · rintro ⟨a, b, rfl⟩
    exact (isIntegral_intCast (R := ℤ) a).add
      ((isIntegral_intCast (R := ℤ) b).mul (imagQuadGenVal_isIntegral d))

/-- Explicit `ℤ`-basis `![1, ω_d]` of `𝓞 (ImagQuadField d)`. -/
def imagQuadIntBasis {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) :
    Module.Basis (Fin 2) ℤ (𝓞 (ImagQuadField d)) :=
  Module.Basis.mk (v := ![1, imagQuadIntGen d])
    (by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hval := congrArg Subtype.val hg
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        zsmul_eq_mul, mul_one] at hval
      change (g 0 : ImagQuadField d) + (g 1 : ImagQuadField d) * imagQuadGenVal d = 0 at hval
      have him := congrArg QuadraticAlgebra.im hval
      have hre := congrArg QuadraticAlgebra.re hval
      unfold imagQuadGenVal at him hre
      split_ifs at him hre
      · have hg1 : g 1 = 0 := by
          simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast,
            QuadraticAlgebra.im_intCast, QuadraticAlgebra.im_zero, zero_mul, add_zero, zero_add] at him
          exact_mod_cast (show (g 1 : ℚ) = 0 by linarith)
        have hg0 : g 0 = 0 := by
          simp only [QuadraticAlgebra.re_intCast, QuadraticAlgebra.re_zero, zero_mul, add_zero,
            hg1, Int.cast_zero] at hre
          exact_mod_cast (show (g 0 : ℚ) = 0 by linarith)
        intro i; fin_cases i <;> assumption
      · have hg1 : g 1 = 0 := by
          simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast,
            QuadraticAlgebra.im_intCast, QuadraticAlgebra.im_zero, mul_one, zero_mul, add_zero,
            zero_add] at him
          exact_mod_cast him
        have hg0 : g 0 = 0 := by
          simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
            QuadraticAlgebra.im_intCast, QuadraticAlgebra.re_zero, mul_zero, zero_mul,
            add_zero] at hre
          exact_mod_cast hre
        intro i; fin_cases i <;> assumption)
    (by
      intro x _
      obtain ⟨a, b, hab⟩ := (mem_ringOfIntegers_imagQuadField_iff hd hsf x.1).mp x.2
      have hx_eq : x = a • (1 : 𝓞 (ImagQuadField d)) + b • imagQuadIntGen d := by
        rw [zsmul_eq_mul, zsmul_eq_mul, mul_one]
        apply Subtype.ext
        change (x : ImagQuadField d) = (a : ImagQuadField d) + (b : ImagQuadField d) * imagQuadGenVal d
        exact hab
      rw [hx_eq]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ a (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ b (Submodule.subset_span ⟨1, rfl⟩)))

/-- Monogenicity of `𝓞 (ImagQuadField d)`: `Algebra.adjoin ℤ {imagQuadIntGen d} = ⊤`! -/
theorem imagQuadField_adjoin_eq_top {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) :
    Algebra.adjoin ℤ ({imagQuadIntGen d} : Set (𝓞 (ImagQuadField d))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, hab⟩ := (mem_ringOfIntegers_imagQuadField_iff hd hsf x.1).mp x.2
  have hx_eq : x = algebraMap ℤ (𝓞 (ImagQuadField d)) a +
      algebraMap ℤ (𝓞 (ImagQuadField d)) b * imagQuadIntGen d := by
    apply Subtype.ext
    change (x : ImagQuadField d) = (a : ImagQuadField d) + (b : ImagQuadField d) * imagQuadGenVal d
    exact hab
  rw [hx_eq]
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ a)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ b) (Algebra.subset_adjoin rfl))

/-- Conductor of `imagQuadIntGen d` is `⊤` (so Kummer–Dedekind applies at EVERY rational prime `p`). -/
theorem imagQuadField_conductor_eq_top {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) :
    conductor ℤ (imagQuadIntGen d) = ⊤ :=
  conductor_eq_top_of_adjoin_eq_top (imagQuadField_adjoin_eq_top hd hsf)

/-- Exact minimal polynomial of `imagQuadIntGen d` over `ℤ`. -/
theorem minpoly_imagQuadIntGen (d : ℕ) :
    minpoly ℤ (imagQuadIntGen d) = imagQuadMinPolyInt d := by
  have hint : IsIntegral ℤ (imagQuadIntGen d) := Algebra.IsIntegral.isIntegral (imagQuadIntGen d)
  have haeval : Polynomial.aeval (imagQuadIntGen d) (imagQuadMinPolyInt d) = 0 := by
    apply Subtype.ext
    have h1 := imagQuadGenVal_aeval_zero d
    have hhom := Polynomial.aeval_algebraMap_apply (ImagQuadField d) (imagQuadIntGen d)
      (imagQuadMinPolyInt d)
    change (algebraMap (𝓞 (ImagQuadField d)) (ImagQuadField d))
      (Polynomial.aeval (imagQuadIntGen d) (imagQuadMinPolyInt d)) = 0
    rw [← hhom]
    exact h1
  have hdvd : minpoly ℤ (imagQuadIntGen d) ∣ imagQuadMinPolyInt d :=
    minpoly.isIntegrallyClosed_dvd hint haeval
  have hdeg_le : (minpoly ℤ (imagQuadIntGen d)).natDegree ≤ 2 := by
    rw [← imagQuadMinPolyInt_natDegree d]
    exact Polynomial.natDegree_le_of_dvd hdvd (imagQuadMinPolyInt_monic d).ne_zero
  have hdeg_pos : 0 < (minpoly ℤ (imagQuadIntGen d)).natDegree := minpoly.natDegree_pos hint
  have hdeg_ne1 : (minpoly ℤ (imagQuadIntGen d)).natDegree ≠ 1 := by
    intro h1
    have hmon := minpoly.monic hint
    have hcoeff1 : (minpoly ℤ (imagQuadIntGen d)).coeff 1 = 1 := by
      rw [← h1]; exact hmon.coeff_natDegree
    have hlin : minpoly ℤ (imagQuadIntGen d) =
        Polynomial.X + Polynomial.C ((minpoly ℤ (imagQuadIntGen d)).coeff 0) := by
      have h := Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq h1)
      rw [hcoeff1, map_one, one_mul] at h
      exact h
    have h0 := minpoly.aeval ℤ (imagQuadIntGen d)
    rw [hlin, map_add, Polynomial.aeval_X, Polynomial.aeval_C] at h0
    have hval := congrArg (algebraMap (𝓞 (ImagQuadField d)) (ImagQuadField d)) h0
    rw [map_add, map_zero, eq_intCast, map_intCast] at hval
    have him := congrArg QuadraticAlgebra.im hval
    simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_intCast, QuadraticAlgebra.im_zero,
      add_zero] at him
    change (imagQuadGenVal d).im = 0 at him
    unfold imagQuadGenVal at him
    split_ifs at him <;> norm_num at him
  have hdeg2 : (minpoly ℤ (imagQuadIntGen d)).natDegree = 2 := by omega
  obtain ⟨q, hq⟩ := hdvd
  have hq_mon : q.Monic := by
    have hm := imagQuadMinPolyInt_monic d
    rw [hq] at hm
    exact (Polynomial.Monic.of_mul_monic_left (minpoly.monic hint) hm)
  have hq_deg : q.natDegree = 0 := by
    have h := congrArg Polynomial.natDegree hq
    rw [imagQuadMinPolyInt_natDegree d,
      Polynomial.natDegree_mul (minpoly.ne_zero hint) hq_mon.ne_zero, hdeg2] at h
    omega
  have hq1 : q = 1 := Polynomial.eq_one_of_monic_natDegree_zero hq_mon hq_deg
  rw [hq, hq1, mul_one]

/-- Quadratic relation of `imagQuadIntGen d` in `𝓞 (ImagQuadField d)`. -/
lemma imagQuadIntGen_sq (d : ℕ) :
    imagQuadIntGen d * imagQuadIntGen d =
      if imagQuadParam d % 4 = 3 then
        imagQuadIntGen d - ((((imagQuadParam d : ℤ) + 1) / 4 : ℤ) : 𝓞 (ImagQuadField d))
      else
        -((imagQuadParam d : ℤ) : 𝓞 (ImagQuadField d)) := by
  have h := imagQuadGenVal_aeval_zero d
  unfold imagQuadMinPolyInt at h
  dsimp only at h
  apply Subtype.ext
  split_ifs with h3
  · rw [if_pos h3, map_add, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast] at h
    change imagQuadGenVal d * imagQuadGenVal d =
      imagQuadGenVal d - ((((imagQuadParam d : ℤ) + 1) / 4 : ℤ) : ImagQuadField d)
    rw [← sq]; linear_combination h
  · rw [if_neg h3, map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast] at h
    change imagQuadGenVal d * imagQuadGenVal d = -((imagQuadParam d : ℤ) : ImagQuadField d)
    rw [← sq]; linear_combination h

/-- **Exact Discriminant of `ℚ(√(-d))`**:
`NumberField.discr (ImagQuadField d) = -(imagQuadDiscNat d : ℤ)` (`-d` if `d ≡ 3 [MOD 4]`, `-4d` otherwise). -/
theorem imagQuadField_discr {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) :
    NumberField.discr (ImagQuadField d) = -(imagQuadDiscNat d : ℤ) := by
  rw [← NumberField.discr_eq_discr (ImagQuadField d) (imagQuadIntBasis hd hsf)]
  rw [Algebra.discr_def, Matrix.det_fin_two]
  set b := imagQuadIntBasis hd hsf
  have hb0 : b 0 = 1 := by simp [b, imagQuadIntBasis]
  have hb1 : b 1 = imagQuadIntGen d := by simp [b, imagQuadIntBasis]
  have hrepr : ∀ (u v : ℤ),
      b.repr ((u : 𝓞 (ImagQuadField d)) + (v : 𝓞 (ImagQuadField d)) * imagQuadIntGen d) 0 = u ∧
      b.repr ((u : 𝓞 (ImagQuadField d)) + (v : 𝓞 (ImagQuadField d)) * imagQuadIntGen d) 1 = v := by
    intro u v
    have hlin : (u : 𝓞 (ImagQuadField d)) + (v : 𝓞 (ImagQuadField d)) * imagQuadIntGen d =
        u • b 0 + v • b 1 := by rw [hb0, hb1, zsmul_eq_mul, zsmul_eq_mul, mul_one]
    rw [hlin, map_add, map_smul, map_smul, b.repr_self, b.repr_self]
    simp
  have htr_lin : ∀ (u v : ℤ),
      Algebra.trace ℤ (𝓞 (ImagQuadField d))
        ((u : 𝓞 (ImagQuadField d)) + (v : 𝓞 (ImagQuadField d)) * imagQuadIntGen d) =
        if imagQuadParam d % 4 = 3 then 2 * u + v else 2 * u := by
    intro u v
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two,
      Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, mul_one]
    rw [(hrepr u v).1]
    have hmul : ((u : 𝓞 (ImagQuadField d)) + (v : 𝓞 (ImagQuadField d)) * imagQuadIntGen d) *
        imagQuadIntGen d =
        if imagQuadParam d % 4 = 3 then
          ((-(v * (((imagQuadParam d : ℤ) + 1) / 4)) : ℤ) : 𝓞 (ImagQuadField d)) +
            ((u + v : ℤ) : 𝓞 (ImagQuadField d)) * imagQuadIntGen d
        else
          ((-(v * (imagQuadParam d : ℤ)) : ℤ) : 𝓞 (ImagQuadField d)) +
            (u : 𝓞 (ImagQuadField d)) * imagQuadIntGen d := by
      rw [add_mul, mul_assoc, imagQuadIntGen_sq d]
      split_ifs <;> push_cast <;> ring
    rw [hmul]
    split_ifs
    · rw [(hrepr _ _).2]; ring
    · rw [(hrepr _ _).2]; ring
  have htr1 : Algebra.trace ℤ (𝓞 (ImagQuadField d)) 1 = 2 := by
    have h := htr_lin 1 0
    simp only [Int.cast_one, Int.cast_zero, zero_mul, add_zero] at h
    rw [h]; split_ifs <;> ring
  have htr_w : Algebra.trace ℤ (𝓞 (ImagQuadField d)) (imagQuadIntGen d) =
      if imagQuadParam d % 4 = 3 then 1 else 0 := by
    have h := htr_lin 0 1
    simp only [Int.cast_zero, Int.cast_one, one_mul, zero_add] at h
    rw [h]; split_ifs <;> ring
  have htr_w2 : Algebra.trace ℤ (𝓞 (ImagQuadField d)) (imagQuadIntGen d * imagQuadIntGen d) =
      if imagQuadParam d % 4 = 3 then 1 - 2 * (((imagQuadParam d : ℤ) + 1) / 4)
      else -2 * (imagQuadParam d : ℤ) := by
    rw [imagQuadIntGen_sq d]
    split_ifs with h3
    · have h := htr_lin (-(((imagQuadParam d : ℤ) + 1) / 4)) 1
      simp only [Int.cast_neg, Int.cast_one, one_mul, if_pos h3] at h
      have heq : imagQuadIntGen d - ((((imagQuadParam d : ℤ) + 1) / 4 : ℤ) : 𝓞 (ImagQuadField d)) =
          -((((imagQuadParam d : ℤ) + 1) / 4 : ℤ) : 𝓞 (ImagQuadField d)) + imagQuadIntGen d := by
        ring
      rw [heq, h]; ring
    · have h := htr_lin (-(imagQuadParam d : ℤ)) 0
      simp only [Int.cast_neg, Int.cast_zero, zero_mul, add_zero, if_neg h3] at h
      rw [h]; ring
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb0, hb1, mul_one, one_mul,
    htr1, htr_w, htr_w2]
  unfold imagQuadDiscNat
  dsimp only
  split_ifs with h3
  · have hm4 : ((imagQuadParam d : ℤ) + 1) / 4 * 4 = (imagQuadParam d : ℤ) + 1 := by omega
    linarith
  · push_cast; ring

/-- Helper: unit criterion in `𝓞 (ImagQuadField d)`: `x` is a unit iff `Algebra.norm ℚ (x : K) = 1`. -/
theorem isUnit_ringOfIntegers_imagQuad_iff (d : ℕ) (x : 𝓞 (ImagQuadField d)) :
    IsUnit x ↔ Algebra.norm ℚ (x : ImagQuadField d) = 1 := by
  constructor
  · intro hx
    obtain ⟨u, rfl⟩ := hx
    have hmul : Algebra.norm ℚ ((u : 𝓞 (ImagQuadField d)) : ImagQuadField d) *
        Algebra.norm ℚ (((u⁻¹ : (𝓞 (ImagQuadField d))ˣ) : 𝓞 (ImagQuadField d)) : ImagQuadField d) = 1 := by
      rw [← map_mul]
      have h1 : ((u : 𝓞 (ImagQuadField d)) : ImagQuadField d) *
          (((u⁻¹ : (𝓞 (ImagQuadField d))ˣ) : 𝓞 (ImagQuadField d)) : ImagQuadField d) = 1 := by
        exact_mod_cast u.mul_inv
      rw [h1, map_one]
    have hnu : IsIntegral ℤ (Algebra.norm ℚ ((u : 𝓞 (ImagQuadField d)) : ImagQuadField d)) :=
      Algebra.isIntegral_norm ℚ (u : 𝓞 (ImagQuadField d)).2
    have hnv : IsIntegral ℤ (Algebra.norm ℚ (((u⁻¹ : (𝓞 (ImagQuadField d))ˣ) : 𝓞 (ImagQuadField d)) : ImagQuadField d)) :=
      Algebra.isIntegral_norm ℚ ((u⁻¹ : (𝓞 (ImagQuadField d))ˣ) : 𝓞 (ImagQuadField d)).2
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hnu
    obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hnv
    rw [eq_intCast] at ha hb
    have hab_q : ((a * b : ℤ) : ℚ) = (1 : ℚ) := by push_cast; rw [ha, hb]; exact hmul
    have hab : a * b = 1 := Int.cast_injective hab_q
    have ha_nn : (0 : ℚ) ≤ (a : ℚ) := by rw [ha]; exact imagQuadField_norm_nonneg d _
    have ha_nn_z : (0 : ℤ) ≤ a := by exact_mod_cast ha_nn
    have ha1 : a = 1 := by
      have := Int.eq_one_or_neg_one_of_mul_eq_one hab
      omega
    rw [← ha, ha1, Int.cast_one]
  · intro hnorm
    have hx_ne : (x : ImagQuadField d) ≠ 0 := by
      intro h0
      rw [imagQuadField_norm_eq, h0] at hnorm
      simp at hnorm
    let y : ImagQuadField d := ⟨(x : ImagQuadField d).re, -(x : ImagQuadField d).im⟩
    have hxy : (x : ImagQuadField d) * y = 1 := by
      have hn := imagQuadField_norm_eq d (x : ImagQuadField d)
      rw [hnorm] at hn
      ext
      · simp only [y, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_one]
        linarith
      · simp only [y, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_one]
        ring
    have hy_int : IsIntegral ℤ y := by
      have htr_int : IsIntegral ℤ (Algebra.trace ℚ (ImagQuadField d) (x : ImagQuadField d)) :=
        Algebra.isIntegral_trace x.2
      obtain ⟨t, ht⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp htr_int
      have ht_eq : (2 : ℚ) * (x : ImagQuadField d).re = (t : ℚ) := by
        rw [← imagQuadField_trace_eq d (x : ImagQuadField d)]; exact ht.symm
      have hy_eq : y = (t : ImagQuadField d) - (x : ImagQuadField d) := by
        ext
        · simp only [y, QuadraticAlgebra.re_sub, QuadraticAlgebra.re_intCast]
          linarith
        · simp only [y, QuadraticAlgebra.im_sub, QuadraticAlgebra.im_intCast]
          ring
      rw [hy_eq]
      exact (isIntegral_intCast (R := ℤ) t).sub x.2
    refine isUnit_iff_exists_inv.mpr ⟨⟨y, hy_int⟩, ?_⟩
    apply Subtype.ext
    exact hxy

/-- Helper: map `(a, b) ∈ ℤ × ℤ` to `a + b * ω_d ∈ 𝓞 (ImagQuadField d)`. -/
private def mkIntElem (d : ℕ) (p : ℤ × ℤ) : 𝓞 (ImagQuadField d) :=
  (p.1 : 𝓞 (ImagQuadField d)) + (p.2 : 𝓞 (ImagQuadField d)) * imagQuadIntGen d

private lemma mkIntElem_injective {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) :
    Function.Injective (mkIntElem d) := by
  intro p q hpq
  set b := imagQuadIntBasis hd hsf
  have hb0 : b 0 = 1 := by simp [b, imagQuadIntBasis]
  have hb1 : b 1 = imagQuadIntGen d := by simp [b, imagQuadIntBasis]
  have hrepr : ∀ r : ℤ × ℤ, b.repr (mkIntElem d r) 0 = r.1 ∧ b.repr (mkIntElem d r) 1 = r.2 := by
    intro r
    have hlin : mkIntElem d r = r.1 • b 0 + r.2 • b 1 := by
      simp [mkIntElem, hb0, hb1, zsmul_eq_mul]
    rw [hlin, map_add, map_smul, map_smul, b.repr_self, b.repr_self]
    simp
  ext
  · rw [← (hrepr p).1, ← (hrepr q).1, hpq]
  · rw [← (hrepr p).2, ← (hrepr q).2, hpq]

private lemma mkIntElem_norm_eq {d : ℕ} (hd : 0 < d) (p : ℤ × ℤ) :
    Algebra.norm ℚ ((mkIntElem d p : 𝓞 (ImagQuadField d)) : ImagQuadField d) =
      if d % 4 = 3 then
        ((2 * p.1 + p.2 : ℤ) : ℚ) ^ 2 / 4 + (d : ℚ) * (p.2 : ℚ) ^ 2 / 4
      else
        (p.1 : ℚ) ^ 2 + (d : ℚ) * (p.2 : ℚ) ^ 2 := by
  rw [imagQuadField_norm_eq_of_pos hd]
  have hm : imagQuadParam d = d := imagQuadParam_eq_self hd
  change ((p.1 : ImagQuadField d) + (p.2 : ImagQuadField d) * imagQuadGenVal d).re ^ 2 +
      (d : ℚ) * ((p.1 : ImagQuadField d) + (p.2 : ImagQuadField d) * imagQuadGenVal d).im ^ 2 = _
  unfold imagQuadGenVal
  by_cases h3 : d % 4 = 3
  · rw [if_pos (by rw [hm]; exact h3), if_pos h3]
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
      QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_intCast,
      zero_mul, mul_zero, add_zero, zero_add]
    push_cast; ring
  · rw [if_neg (by rw [hm]; exact h3), if_neg h3]
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
      QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_intCast,
      mul_zero, mul_one, add_zero, zero_add]

/-- **Exact Unit Group Cardinality of `𝓞 (ℚ(√(-d)))`**:
for every squarefree `d > 0`, `Nat.card (𝓞 (ImagQuadField d))ˣ = imagQuadUnitCard d`
(`4` for `d = 1`, `6` for `d = 3`, `2` otherwise), and `(𝓞 (ImagQuadField d))ˣ` is finite! -/
theorem imagQuadUnitCard_eq {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) :
    Nat.card (𝓞 (ImagQuadField d))ˣ = imagQuadUnitCard d := by
  let S : Finset (ℤ × ℤ) :=
    if d = 1 then {(1, 0), (-1, 0), (0, 1), (0, -1)}
    else if d = 3 then {(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)}
    else {(1, 0), (-1, 0)}
  have hS_card : S.card = imagQuadUnitCard d := by
    unfold imagQuadUnitCard
    dsimp only [S]
    split_ifs <;> decide
  have hS_iff : ∀ p : ℤ × ℤ, IsUnit (mkIntElem d p) ↔ p ∈ S := by
    intro ⟨a, b⟩
    rw [isUnit_ringOfIntegers_imagQuad_iff, mkIntElem_norm_eq hd]
    dsimp only [S]
    by_cases hd1 : d = 1
    · subst hd1
      simp only [ite_true, show ¬ (1 % 4 = 3) by decide, ite_false, Nat.cast_one, one_mul,
        Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      have hiff : (a : ℚ) ^ 2 + (b : ℚ) ^ 2 = 1 ↔ a ^ 2 + b ^ 2 = 1 := by
        exact_mod_cast (show ((a ^ 2 + b ^ 2 : ℤ) : ℚ) = ((1 : ℤ) : ℚ) ↔ a ^ 2 + b ^ 2 = 1 from
          Int.cast_injective.eq_iff)
      rw [hiff]
      constructor
      · intro h
        have ha : -1 ≤ a ∧ a ≤ 1 := ⟨by nlinarith [sq_nonneg b], by nlinarith [sq_nonneg b]⟩
        have hb : -1 ≤ b ∧ b ≤ 1 := ⟨by nlinarith [sq_nonneg a], by nlinarith [sq_nonneg a]⟩
        have ha' : a = -1 ∨ a = 0 ∨ a = 1 := by omega
        have hb' : b = -1 ∨ b = 0 ∨ b = 1 := by omega
        rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;> simp_all
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
    · by_cases hd3 : d = 3
      · subst hd3
        simp only [hd1, ite_false, ite_true, show (3 % 4 = 3) by decide,
          Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        have hiff : ((2 * a + b : ℤ) : ℚ) ^ 2 / 4 + ((3 : ℕ) : ℚ) * (b : ℚ) ^ 2 / 4 = 1 ↔
            (2 * a + b) ^ 2 + 3 * b ^ 2 = 4 := by
          constructor
          · intro h
            have hq : (((2 * a + b) ^ 2 + 3 * b ^ 2 : ℤ) : ℚ) = ((4 : ℤ) : ℚ) := by
              push_cast at h ⊢; linarith
            exact Int.cast_injective hq
          · intro h
            have hq : (((2 * a + b) ^ 2 + 3 * b ^ 2 : ℤ) : ℚ) = ((4 : ℤ) : ℚ) := by
              exact_mod_cast h
            push_cast at hq ⊢; linarith
        rw [hiff]
        constructor
        · intro h
          have hb : -1 ≤ b ∧ b ≤ 1 := ⟨by nlinarith [sq_nonneg (2 * a + b)],
            by nlinarith [sq_nonneg (2 * a + b)]⟩
          have hb' : b = -1 ∨ b = 0 ∨ b = 1 := by omega
          rcases hb' with rfl | rfl | rfl
          · have ha : -1 ≤ a ∧ a ≤ 2 := ⟨by nlinarith, by nlinarith⟩
            have ha' : a = -1 ∨ a = 0 ∨ a = 1 ∨ a = 2 := by omega
            rcases ha' with rfl | rfl | rfl | rfl <;> simp_all
          · have ha : -1 ≤ a ∧ a ≤ 1 := ⟨by nlinarith, by nlinarith⟩
            have ha' : a = -1 ∨ a = 0 ∨ a = 1 := by omega
            rcases ha' with rfl | rfl | rfl <;> simp_all
          · have ha : -2 ≤ a ∧ a ≤ 1 := ⟨by nlinarith, by nlinarith⟩
            have ha' : a = -2 ∨ a = -1 ∨ a = 0 ∨ a = 1 := by omega
            rcases ha' with rfl | rfl | rfl | rfl <;> simp_all
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
            norm_num
      · simp only [hd1, hd3, ite_false, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        by_cases hmod3 : d % 4 = 3
        · rw [if_pos hmod3]
          have hd7 : 7 ≤ d := by omega
          have hiff : ((2 * a + b : ℤ) : ℚ) ^ 2 / 4 + (d : ℚ) * (b : ℚ) ^ 2 / 4 = 1 ↔
              (2 * a + b) ^ 2 + (d : ℤ) * b ^ 2 = 4 := by
            constructor
            · intro h
              have hq : (((2 * a + b) ^ 2 + (d : ℤ) * b ^ 2 : ℤ) : ℚ) = ((4 : ℤ) : ℚ) := by
                push_cast at h ⊢; linarith
              exact Int.cast_injective hq
            · intro h
              have hq : (((2 * a + b) ^ 2 + (d : ℤ) * b ^ 2 : ℤ) : ℚ) = ((4 : ℤ) : ℚ) := by
                exact_mod_cast h
              push_cast at hq ⊢; linarith
          rw [hiff]
          constructor
          · intro h
            have hb0 : b = 0 := by
              by_contra hbne
              have hb1 : 1 ≤ b ^ 2 := by
                have := Int.one_le_abs hbne
                nlinarith [sq_abs b]
              have hd7z : (7 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd7
              nlinarith [sq_nonneg (2 * a + b)]
            subst hb0
            have ha : a = 1 ∨ a = -1 := by
              have h1 : a ^ 2 = 1 := by linarith
              exact sq_eq_one_iff.mp h1
            rcases ha with rfl | rfl <;> simp
          · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
        · rw [if_neg hmod3]
          have hd2 : 2 ≤ d := by omega
          have hiff : (a : ℚ) ^ 2 + (d : ℚ) * (b : ℚ) ^ 2 = 1 ↔
              a ^ 2 + (d : ℤ) * b ^ 2 = 1 := by
            constructor
            · intro h
              have hq : ((a ^ 2 + (d : ℤ) * b ^ 2 : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
                push_cast at h ⊢; linarith
              exact Int.cast_injective hq
            · intro h
              have hq : ((a ^ 2 + (d : ℤ) * b ^ 2 : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
                exact_mod_cast h
              push_cast at hq ⊢; linarith
          rw [hiff]
          constructor
          · intro h
            have hb0 : b = 0 := by
              by_contra hbne
              have hb1 : 1 ≤ b ^ 2 := by
                have := Int.one_le_abs hbne
                nlinarith [sq_abs b]
              have hd2z : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd2
              nlinarith [sq_nonneg a]
            subst hb0
            have ha : a = 1 ∨ a = -1 := by
              have h1 : a ^ 2 = 1 := by linarith
              exact sq_eq_one_iff.mp h1
            rcases ha with rfl | rfl <;> simp
          · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
  -- Bijection `(𝓞 (ImagQuadField d))ˣ ≃ S`
  let e : S ≃ (𝓞 (ImagQuadField d))ˣ :=
    { toFun := fun p => ((hS_iff p.1).mpr p.2).unit
      invFun := fun u =>
        let b := imagQuadIntBasis hd hsf
        let p : ℤ × ℤ := (b.repr (u : 𝓞 (ImagQuadField d)) 0, b.repr (u : 𝓞 (ImagQuadField d)) 1)
        ⟨p, (hS_iff p).mp (by
          have hmk : mkIntElem d p = (u : 𝓞 (ImagQuadField d)) := by
            have hsum := b.sum_repr (u : 𝓞 (ImagQuadField d))
            rw [Fin.sum_univ_two] at hsum
            have hb0 : b 0 = 1 := by simp [b, imagQuadIntBasis]
            have hb1 : b 1 = imagQuadIntGen d := by simp [b, imagQuadIntBasis]
            rw [hb0, hb1, zsmul_eq_mul, zsmul_eq_mul, mul_one] at hsum
            exact hsum
          rw [hmk]; exact u.isUnit)⟩
      left_inv := fun ⟨p, hp⟩ => by
        apply Subtype.ext
        apply mkIntElem_injective hd hsf
        set b := imagQuadIntBasis hd hsf
        have hb0 : b 0 = 1 := by simp [b, imagQuadIntBasis]
        have hb1 : b 1 = imagQuadIntGen d := by simp [b, imagQuadIntBasis]
        have hsum := b.sum_repr (((hS_iff p).mpr hp).unit : 𝓞 (ImagQuadField d))
        rw [Fin.sum_univ_two, hb0, hb1, zsmul_eq_mul, zsmul_eq_mul, mul_one,
          IsUnit.unit_spec] at hsum
        exact hsum
      right_inv := fun u => by
        apply Units.ext
        rw [IsUnit.unit_spec]
        set b := imagQuadIntBasis hd hsf
        have hb0 : b 0 = 1 := by simp [b, imagQuadIntBasis]
        have hb1 : b 1 = imagQuadIntGen d := by simp [b, imagQuadIntBasis]
        have hsum := b.sum_repr (u : 𝓞 (ImagQuadField d))
        rw [Fin.sum_univ_two, hb0, hb1, zsmul_eq_mul, zsmul_eq_mul, mul_one] at hsum
        exact hsum }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, hS_card]

theorem imagQuadUnit_finite {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) :
    Finite (𝓞 (ImagQuadField d))ˣ :=
  Nat.finite_of_card_ne_zero (by rw [imagQuadUnitCard_eq hd hsf]; exact (imagQuadUnitCard_pos d).ne')

end ImaginaryQuadraticFields

/-! ## Section 2: Primitive Odd Real Kronecker Character `imagQuadChar d` -/

section ImaginaryKroneckerCharacter

private def intUnitOfPmOne' (z : ℤ) : ℤˣ :=
  if z = 1 then 1 else -1

private lemma coe_intUnitOfPmOne' {z : ℤ} (hz : z = 1 ∨ z = -1) :
    ((intUnitOfPmOne' z : ℤˣ) : ℤ) = z := by
  unfold intUnitOfPmOne'
  rcases hz with rfl | rfl <;> simp

private def jacobiUnitHom' (m : ℕ) [NeZero m] (hm : _root_.Odd m) : (ZMod m)ˣ →* ℤˣ where
  toFun u := intUnitOfPmOne' (jacobiSym ((u : ZMod m).val : ℤ) m)
  map_one' := by
    by_cases h1 : m = 1
    · subst h1
      have h0 : ((1 : ZMod 1).val : ℤ) = 0 := by decide
      simp [intUnitOfPmOne', h0]
    · have hm1 : 1 ≤ m := NeZero.pos m
      have : Fact (1 < m) := ⟨by omega⟩
      have hval : ((1 : (ZMod m)ˣ) : ZMod m).val = 1 := by
        rw [Units.val_one, ZMod.val_one]
      show intUnitOfPmOne' (jacobiSym (((1 : (ZMod m)ˣ) : ZMod m).val : ℤ) m) = 1
      rw [hval, Nat.cast_one, jacobiSym.one_left]
      rfl
  map_mul' u v := by
    have hpm : ∀ w : (ZMod m)ˣ,
        jacobiSym ((w : ZMod m).val : ℤ) m = 1 ∨ jacobiSym ((w : ZMod m).val : ℤ) m = -1 := by
      intro w
      have hcop : Nat.Coprime (w : ZMod m).val m := by
        have hu : IsUnit (((w : ZMod m).val : ℕ) : ZMod m) := by
          rw [ZMod.natCast_zmod_val]; exact w.isUnit
        exact (ZMod.isUnit_iff_coprime _ m).mp hu
      have hne0 : jacobiSym ((w : ZMod m).val : ℤ) m ≠ 0 := by
        intro h0
        have hgcd := ((jacobiSym.eq_zero_iff).mp h0).2
        rw [Int.gcd_natCast_natCast] at hgcd
        exact hgcd hcop.gcd_eq_one
      rcases jacobiSym.trichotomy ((w : ZMod m).val : ℤ) m with h0 | h1 | hm1
      · exact absurd h0 hne0
      · exact Or.inl h1
      · exact Or.inr hm1
    apply Units.ext
    change ((intUnitOfPmOne' (jacobiSym (((u * v : (ZMod m)ˣ) : ZMod m).val : ℤ) m) : ℤˣ) : ℤ) =
      ((intUnitOfPmOne' (jacobiSym ((u : ZMod m).val : ℤ) m) *
        intUnitOfPmOne' (jacobiSym ((v : ZMod m).val : ℤ) m) : ℤˣ) : ℤ)
    rw [coe_intUnitOfPmOne' (hpm (u * v))]
    conv_rhs => rw [Units.val_mul]
    rw [coe_intUnitOfPmOne' (hpm u), coe_intUnitOfPmOne' (hpm v)]
    have hmod : (((u * v : (ZMod m)ˣ) : ZMod m).val : ℤ) ≡
        ((u : ZMod m).val : ℤ) * ((v : ZMod m).val : ℤ) [ZMOD (m : ℕ)] := by
      rw [← ZMod.intCast_eq_intCast_iff]
      push_cast
      simp only [ZMod.natCast_zmod_val]
    rw [jacobiSym.mod_left' hmod, jacobiSym.mul_left]

private lemma coe_jacobiUnitHom' {m : ℕ} [NeZero m] (hm : _root_.Odd m) (u : (ZMod m)ˣ) :
    ((jacobiUnitHom' m hm u : ℤˣ) : ℤ) = jacobiSym ((u : ZMod m).val : ℤ) m := by
  have hcop : Nat.Coprime (u : ZMod m).val m := by
    have hu : IsUnit (((u : ZMod m).val : ℕ) : ZMod m) := by
      rw [ZMod.natCast_zmod_val]; exact u.isUnit
    exact (ZMod.isUnit_iff_coprime _ m).mp hu
  have hne0 : jacobiSym ((u : ZMod m).val : ℤ) m ≠ 0 := by
    intro h0
    have hgcd := ((jacobiSym.eq_zero_iff).mp h0).2
    rw [Int.gcd_natCast_natCast] at hgcd
    exact hgcd hcop.gcd_eq_one
  have hpm : jacobiSym ((u : ZMod m).val : ℤ) m = 1 ∨ jacobiSym ((u : ZMod m).val : ℤ) m = -1 := by
    rcases jacobiSym.trichotomy ((u : ZMod m).val : ℤ) m with h0 | h1 | hm1
    · exact absurd h0 hne0
    · exact Or.inl h1
    · exact Or.inr hm1
  exact coe_intUnitOfPmOne' hpm

private def chi4UnitHom' : (ZMod 4)ˣ →* ℤˣ where
  toFun u := if (u : ZMod 4) = 1 then 1 else -1
  map_one' := by decide
  map_mul' u v := by fin_cases u <;> fin_cases v <;> decide

private def chi8UnitHom' : (ZMod 8)ˣ →* ℤˣ where
  toFun u := if (u : ZMod 8) = 1 ∨ (u : ZMod 8) = 7 then 1 else -1
  map_one' := by decide
  map_mul' u v := by fin_cases u <;> fin_cases v <;> decide

private lemma coe_chi4UnitHom'_nat {n : ℕ} (hn : _root_.Odd n) (hu : IsUnit (n : ZMod 4)) :
    ((chi4UnitHom' hu.unit : ℤˣ) : ℤ) = if n % 4 = 1 then 1 else -1 := by
  obtain ⟨k, hk⟩ := hn
  have hmod : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases hmod with h1 | h3
  · rw [if_pos h1]
    have hc : (n : ZMod 4) = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]; exact h1
    change (((if (hu.unit : ZMod 4) = 1 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) = 1
    rw [IsUnit.unit_spec, hc]; simp
  · rw [if_neg (by omega)]
    have hc : (n : ZMod 4) = 3 := by
      rw [← Nat.cast_ofNat (n := 3), ZMod.natCast_eq_natCast_iff]; exact h3
    change (((if (hu.unit : ZMod 4) = 1 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) = -1
    rw [IsUnit.unit_spec, hc]
    simp [show (3 : ZMod 4) ≠ 1 by decide]

private lemma coe_chi8UnitHom'_nat {n : ℕ} (hn : _root_.Odd n) (hu : IsUnit (n : ZMod 8)) :
    ((chi8UnitHom' hu.unit : ℤˣ) : ℤ) = jacobiSym 2 n := by
  rw [jacobiSym.at_two hn]
  obtain ⟨k, hk⟩ := hn
  have hmod : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  change (((if (hu.unit : ZMod 8) = 1 ∨ (hu.unit : ZMod 8) = 7 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) = _
  rw [IsUnit.unit_spec]
  rcases hmod with h | h | h | h
  · have hc : (n : ZMod 8) = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]; exact h
    rw [hc]; decide
  · have hc : (n : ZMod 8) = 3 := by
      rw [← Nat.cast_ofNat (n := 3), ZMod.natCast_eq_natCast_iff]; exact h
    rw [hc]; decide
  · have hc : (n : ZMod 8) = 5 := by
      rw [← Nat.cast_ofNat (n := 5), ZMod.natCast_eq_natCast_iff]; exact h
    rw [hc]; decide
  · have hc : (n : ZMod 8) = 7 := by
      rw [← Nat.cast_ofNat (n := 7), ZMod.natCast_eq_natCast_iff]; exact h
    rw [hc]; decide

/-- The imaginary quadratic Kronecker unit homomorphism `(ZMod (imagQuadDiscNat d))ˣ →* ℤˣ`:
- `m % 4 = 3`: `jacobiUnitHom' m`
- `m % 4 = 1`: `chi4 * jacobiUnitHom' m`
- `m % 4 = 2, (m/2) % 4 = 1`: `chi4 * chi8 * jacobiUnitHom' (m/2)`
- `m % 4 = 2, (m/2) % 4 = 3`: `chi8 * jacobiUnitHom' (m/2)`
(and trivial `1` in the unreachable `m % 4 = 0` branch). -/
def imagQuadUnitHom (d : ℕ) : (ZMod (imagQuadDiscNat d))ˣ →* ℤˣ :=
  let m := imagQuadParam d
  if h3 : m % 4 = 3 then
    have hD : imagQuadDiscNat d = m := by unfold imagQuadDiscNat; exact if_pos h3
    have hodd : _root_.Odd (imagQuadDiscNat d) := by rw [hD]; exact Nat.odd_iff.mpr (by omega)
    jacobiUnitHom' (imagQuadDiscNat d) hodd
  else if h1 : m % 4 = 1 then
    have hD : imagQuadDiscNat d = 4 * m := by unfold imagQuadDiscNat; exact if_neg h3
    have h4 : 4 ∣ imagQuadDiscNat d := ⟨m, hD⟩
    have hm_dvd : m ∣ imagQuadDiscNat d := ⟨4, by rw [hD, mul_comm]⟩
    have : NeZero m := ⟨(imagQuadParam_pos d).ne'⟩
    have hodd : _root_.Odd m := Nat.odd_iff.mpr (by omega)
    (chi4UnitHom'.comp (ZMod.unitsMap h4)) * ((jacobiUnitHom' m hodd).comp (ZMod.unitsMap hm_dvd))
  else if h2 : m % 4 = 2 then
    have hD : imagQuadDiscNat d = 4 * m := by unfold imagQuadDiscNat; exact if_neg h3
    have hq_odd : _root_.Odd (m / 2) := Nat.odd_iff.mpr (by omega)
    have : NeZero (m / 2) := ⟨by have := imagQuadParam_pos d; omega⟩
    have h4 : 4 ∣ imagQuadDiscNat d := ⟨m, hD⟩
    have h8 : 8 ∣ imagQuadDiscNat d := ⟨m / 2, by omega⟩
    have hq_dvd : m / 2 ∣ imagQuadDiscNat d := ⟨8, by omega⟩
    if (m / 2) % 4 = 1 then
      (chi4UnitHom'.comp (ZMod.unitsMap h4)) * (chi8UnitHom'.comp (ZMod.unitsMap h8)) *
        ((jacobiUnitHom' (m / 2) hq_odd).comp (ZMod.unitsMap hq_dvd))
    else
      (chi8UnitHom'.comp (ZMod.unitsMap h8)) *
        ((jacobiUnitHom' (m / 2) hq_odd).comp (ZMod.unitsMap hq_dvd))
  else 1

/-- **Primitive Odd Real Kronecker Character `χ_{-|D|} : DirichletCharacter ℂ (imagQuadDiscNat d)`**
attached to every imaginary quadratic field `ℚ(√(-d))`. -/
def imagQuadChar (d : ℕ) : DirichletCharacter ℂ (imagQuadDiscNat d) :=
  dirichletCharOfIntUnitHom (imagQuadUnitHom d)

private lemma dirichletCharOfIntUnitHom_apply_isUnit' {q : ℕ} (f : (ZMod q)ˣ →* ℤˣ)
    {a : ZMod q} (ha : IsUnit a) :
    dirichletCharOfIntUnitHom f a = (((f ha.unit : ℤˣ) : ℤ) : ℂ) := by
  have h := dirichletCharOfIntUnitHom_apply_unit f ha.unit
  rwa [IsUnit.unit_spec] at h

theorem imagQuadChar_real (d : ℕ) (a : ZMod (imagQuadDiscNat d)) :
    (imagQuadChar d a).im = 0 := by
  by_cases ha : IsUnit a
  · rw [imagQuadChar, dirichletCharOfIntUnitHom_apply_isUnit' _ ha, Complex.intCast_im]
  · rw [MulChar.map_nonunit _ ha, Complex.zero_im]

theorem imagQuadChar_sq_eq_one (d : ℕ) : (imagQuadChar d) ^ 2 = 1 := by
  ext u
  rw [MulChar.pow_apply_coe, MulChar.one_apply u.isUnit]
  have hu : imagQuadChar d (u : ZMod (imagQuadDiscNat d)) =
      (((imagQuadUnitHom d u : ℤˣ) : ℤ) : ℂ) :=
    dirichletCharOfIntUnitHom_apply_unit (imagQuadUnitHom d) u
  rw [hu]
  rcases Int.units_eq_one_or (imagQuadUnitHom d u) with h | h <;> rw [h] <;> norm_num

/-- Helper: `jacobiSym (-1) m` for odd `m`: `1` if `m % 4 = 1`, `-1` if `m % 4 = 3`. -/
private lemma coe_jacobiUnitHom'_neg_one {m : ℕ} [NeZero m] (hm : _root_.Odd m) :
    ((jacobiUnitHom' m hm (-1 : (ZMod m)ˣ) : ℤˣ) : ℤ) = if m % 4 = 1 then 1 else -1 := by
  rw [coe_jacobiUnitHom' hm]
  have hmod : (((-1 : (ZMod m)ˣ) : ZMod m).val : ℤ) ≡ (-1 : ℤ) [ZMOD (m : ℕ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [jacobiSym.mod_left' hmod, jacobiSym.at_neg_one hm]
  obtain ⟨k, hk⟩ := hm
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h | h
  · rw [if_pos h]
    have hc : (m : ZMod 4) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff m 1 4).mpr h
      simpa using this
    rw [hc]; decide
  · rw [if_neg (by omega)]
    have hc : (m : ZMod 4) = 3 := by
      have := (ZMod.natCast_eq_natCast_iff m 3 4).mpr h
      simpa using this
    rw [hc]; decide

/-- **Oddness of `imagQuadChar d`**: for every squarefree `d > 0`, `imagQuadChar d (-1) = -1`. -/
theorem imagQuadChar_odd {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) :
    (imagQuadChar d).Odd := by
  have hm : imagQuadParam d = d := imagQuadParam_eq_self hd
  have hne0 : d % 4 ≠ 0 := squarefree_mod_four_ne_zero' hsf
  have hneg_u : IsUnit (-1 : ZMod (imagQuadDiscNat d)) := isUnit_one.neg
  change imagQuadChar d (-1 : ZMod (imagQuadDiscNat d)) = -1
  have hu_eq : hneg_u.unit = (-1 : (ZMod (imagQuadDiscNat d))ˣ) := by
    apply Units.ext; simp [IsUnit.unit_spec]
  rw [imagQuadChar, dirichletCharOfIntUnitHom_apply_isUnit' _ hneg_u, hu_eq]
  have hmap_neg : ∀ (k : ℕ) (hk : k ∣ imagQuadDiscNat d),
      ZMod.unitsMap hk (-1 : (ZMod (imagQuadDiscNat d))ˣ) = (-1 : (ZMod k)ˣ) := by
    intro k hk
    apply Units.ext
    change ZMod.castHom hk (ZMod k) (-1 : ZMod (imagQuadDiscNat d)) = (-1 : ZMod k)
    rw [map_neg, map_one]
  have hc4_neg : ((chi4UnitHom' (-1 : (ZMod 4)ˣ) : ℤˣ) : ℤ) = -1 := by decide
  have hc8_neg : ((chi8UnitHom' (-1 : (ZMod 8)ˣ) : ℤˣ) : ℤ) = 1 := by decide
  have hz : ((imagQuadUnitHom d (-1 : (ZMod (imagQuadDiscNat d))ˣ) : ℤˣ) : ℤ) = -1 := by
    unfold imagQuadUnitHom
    dsimp only
    split_ifs with h3 h1 h2 hq1
    · rw [coe_jacobiUnitHom'_neg_one]
      have hD : imagQuadDiscNat d = imagQuadParam d := by unfold imagQuadDiscNat; exact if_pos h3
      rw [hD, if_neg (by omega)]
    · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, hmap_neg,
        hc4_neg, coe_jacobiUnitHom'_neg_one, if_pos h1, mul_one]
    · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, hmap_neg,
        hc4_neg, hc8_neg, coe_jacobiUnitHom'_neg_one, if_pos hq1, mul_one]
    · have hq3 : (imagQuadParam d / 2) % 4 = 3 := by omega
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, hmap_neg,
        hc8_neg, coe_jacobiUnitHom'_neg_one, if_neg (by omega), one_mul]
    · exfalso; rw [hm] at h3 h1 h2; omega
  rw [hz]; norm_num

theorem imagQuadChar_ne_one {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) :
    imagQuadChar d ≠ 1 := by
  intro h1
  have hodd : imagQuadChar d (-1 : ZMod (imagQuadDiscNat d)) = -1 := imagQuadChar_odd hd hsf
  rw [h1, MulChar.one_apply (isUnit_one.neg)] at hodd
  norm_num at hodd

/-- **Exact Evaluation of `imagQuadChar d` at Every Odd Prime `p`**:
`imagQuadChar d (p : ZMod (imagQuadDiscNat d)) = (legendreSym p (-(d : ℤ)) : ℂ)`! -/
theorem imagQuadChar_apply_prime_odd {d : ℕ} (hd : 0 < d) (hsf : Squarefree d)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    imagQuadChar d (p : ZMod (imagQuadDiscNat d)) = (legendreSym p (-(d : ℤ)) : ℂ) := by
  have hp : p.Prime := Fact.out
  have hp_odd : _root_.Odd p := hp.odd_of_ne_two hp2
  have hm : imagQuadParam d = d := imagQuadParam_eq_self hd
  have hne0 : d % 4 ≠ 0 := squarefree_mod_four_ne_zero' hsf
  by_cases hpd : p ∣ d
  · have hpD : p ∣ imagQuadDiscNat d := by
      rw [imagQuadDiscNat_eq hd]; split_ifs
      · exact hpd
      · exact dvd_mul_of_dvd_right hpd 4
    have hnotu : ¬ IsUnit (p : ZMod (imagQuadDiscNat d)) := by
      rw [ZMod.isUnit_iff_coprime]
      intro hcop
      exact hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hpD)
    rw [MulChar.map_nonunit _ hnotu]
    have hleg0 : legendreSym p (-(d : ℤ)) = 0 := by
      rw [legendreSym.eq_zero_iff]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (-(d : ℤ)) p).mpr (dvd_neg.mpr (Int.ofNat_dvd.mpr hpd))
    rw [hleg0, Int.cast_zero]
  · have hcop_d : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr hpd
    have hcop2 : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr fun h2 =>
      hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h2) hp.two_le)
    have hcop_4 : Nat.Coprime p 4 := hcop2.pow_right 2
    have hcop_8 : Nat.Coprime p 8 := hcop2.pow_right 3
    have hcop_D : Nat.Coprime p (imagQuadDiscNat d) := by
      rw [imagQuadDiscNat_eq hd]; split_ifs
      · exact hcop_d
      · exact hcop_4.mul_right hcop_d
    have hpu : IsUnit (p : ZMod (imagQuadDiscNat d)) :=
      (ZMod.isUnit_iff_coprime p (imagQuadDiscNat d)).mpr hcop_D
    have hval_eval : imagQuadChar d (p : ZMod (imagQuadDiscNat d)) =
        (((imagQuadUnitHom d hpu.unit : ℤˣ) : ℤ) : ℂ) :=
      dirichletCharOfIntUnitHom_apply_isUnit' _ hpu
    rw [hval_eval, jacobiSym.legendreSym.to_jacobiSym]
    congr 1
    have hjac_map : ∀ (m : ℕ) [NeZero m] (hm' : _root_.Odd m) (hm_dvd : m ∣ imagQuadDiscNat d),
        ((jacobiUnitHom' m hm' (ZMod.unitsMap hm_dvd hpu.unit) : ℤˣ) : ℤ) = jacobiSym (p : ℤ) m := by
      intro m _ hm' hm_dvd
      rw [coe_jacobiUnitHom' hm']
      have hmod : (((ZMod.unitsMap hm_dvd hpu.unit : (ZMod m)ˣ) : ZMod m).val : ℤ) ≡
          (p : ℤ) [ZMOD (m : ℕ)] := by
        rw [← ZMod.intCast_eq_intCast_iff]
        push_cast
        rw [ZMod.natCast_zmod_val]
        change ZMod.cast (p : ZMod (imagQuadDiscNat d)) = (p : ZMod m)
        exact ZMod.cast_natCast hm_dvd p
      exact jacobiSym.mod_left' hmod
    have hneg_p : jacobiSym (-1) p = if p % 4 = 1 then 1 else -1 := by
      rw [jacobiSym.at_neg_one hp_odd]
      have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by obtain ⟨k, rfl⟩ := hp_odd; omega
      rcases hp4 with hp1 | hp3
      · rw [if_pos hp1]
        have hc : (p : ZMod 4) = 1 := by rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]; exact hp1
        rw [hc]; decide
      · rw [if_neg (by omega)]
        have hc : (p : ZMod 4) = 3 := by
          rw [← Nat.cast_ofNat (n := 3), ZMod.natCast_eq_natCast_iff]; exact hp3
        rw [hc]; decide
    have hneg_mul : jacobiSym (-(d : ℤ)) p = (if p % 4 = 1 then 1 else -1) * jacobiSym (d : ℤ) p := by
      rw [show -(d : ℤ) = (-1) * (d : ℤ) by ring, jacobiSym.mul_left, hneg_p]
    rw [hneg_mul]
    set sgn : ℤ := if p % 4 = 1 then 1 else -1 with hsgn_def
    unfold imagQuadUnitHom
    dsimp only
    split_ifs with h3 h1 h2 hq1
    · have hD : imagQuadDiscNat d = imagQuadParam d := by unfold imagQuadDiscNat; exact if_pos h3
      have hmod : (((hpu.unit : ZMod (imagQuadDiscNat d)).val : ℤ)) ≡
          (p : ℤ) [ZMOD (imagQuadDiscNat d : ℕ)] := by
        rw [← ZMod.intCast_eq_intCast_iff]
        push_cast
        rw [ZMod.natCast_zmod_val, IsUnit.unit_spec]
      rw [coe_jacobiUnitHom', jacobiSym.mod_left' hmod, hD, hm]
      have hd3 : d % 4 = 3 := by rwa [hm] at h3
      have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by obtain ⟨k, rfl⟩ := hp_odd; omega
      rcases hp4 with hp1 | hp3
      · rw [hsgn_def, if_pos hp1, one_mul]
        exact (jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr (by omega)) hp1).symm
      · rw [hsgn_def, if_neg (by omega), neg_one_mul]
        have hqr := jacobiSym.quadratic_reciprocity_three_mod_four hd3 hp3
        linarith
    · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
      have hu4 : IsUnit (p : ZMod 4) := (ZMod.isUnit_iff_coprime p 4).mpr hcop_4
      have h4D : 4 ∣ imagQuadDiscNat d := by unfold imagQuadDiscNat; rw [if_neg h3]; exact ⟨_, rfl⟩
      have hmap4 : ZMod.unitsMap h4D hpu.unit = hu4.unit := by
        apply Units.ext
        change ZMod.cast (p : ZMod (imagQuadDiscNat d)) = (p : ZMod 4)
        exact ZMod.cast_natCast h4D p
      rw [hmap4, coe_chi4UnitHom'_nat hp_odd hu4, hjac_map, hm, hsgn_def]
      have hd1 : d % 4 = 1 := by rwa [hm] at h1
      rw [← jacobiSym.quadratic_reciprocity_one_mod_four hd1 hp_odd]
    · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
      have hu4 : IsUnit (p : ZMod 4) := (ZMod.isUnit_iff_coprime p 4).mpr hcop_4
      have hu8 : IsUnit (p : ZMod 8) := (ZMod.isUnit_iff_coprime p 8).mpr hcop_8
      have h4D : 4 ∣ imagQuadDiscNat d := by unfold imagQuadDiscNat; rw [if_neg h3]; exact ⟨_, rfl⟩
      have h8D : 8 ∣ imagQuadDiscNat d := by
        unfold imagQuadDiscNat; rw [if_neg h3]; exact ⟨imagQuadParam d / 2, by omega⟩
      have hmap4 : ZMod.unitsMap h4D hpu.unit = hu4.unit := by
        apply Units.ext
        change ZMod.cast (p : ZMod (imagQuadDiscNat d)) = (p : ZMod 4)
        exact ZMod.cast_natCast h4D p
      have hmap8 : ZMod.unitsMap h8D hpu.unit = hu8.unit := by
        apply Units.ext
        change ZMod.cast (p : ZMod (imagQuadDiscNat d)) = (p : ZMod 8)
        exact ZMod.cast_natCast h8D p
      rw [hmap4, hmap8, coe_chi4UnitHom'_nat hp_odd hu4, coe_chi8UnitHom'_nat hp_odd hu8,
        hjac_map, hm, hsgn_def]
      have hq1' : (d / 2) % 4 = 1 := by rwa [hm] at hq1
      have hd2' : d % 4 = 2 := by rwa [hm] at h2
      rw [← jacobiSym.quadratic_reciprocity_one_mod_four hq1' hp_odd, mul_assoc,
        ← jacobiSym.mul_left]
      congr 2; omega
    · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
      have hu8 : IsUnit (p : ZMod 8) := (ZMod.isUnit_iff_coprime p 8).mpr hcop_8
      have h8D : 8 ∣ imagQuadDiscNat d := by
        unfold imagQuadDiscNat; rw [if_neg h3]; exact ⟨imagQuadParam d / 2, by omega⟩
      have hmap8 : ZMod.unitsMap h8D hpu.unit = hu8.unit := by
        apply Units.ext
        change ZMod.cast (p : ZMod (imagQuadDiscNat d)) = (p : ZMod 8)
        exact ZMod.cast_natCast h8D p
      rw [hmap8, coe_chi8UnitHom'_nat hp_odd hu8, hjac_map, hm, hsgn_def]
      have hd2' : d % 4 = 2 := by rwa [hm] at h2
      have hq3' : (d / 2) % 4 = 3 := by rw [hm] at h2 hq1; omega
      have hpair : jacobiSym (p : ℤ) (d / 2) =
          (if p % 4 = 1 then 1 else -1) * jacobiSym ((d / 2 : ℕ) : ℤ) p := by
        have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by obtain ⟨k, rfl⟩ := hp_odd; omega
        rcases hp4 with hp1 | hp3
        · rw [if_pos hp1, one_mul]
          exact (jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr (by omega)) hp1).symm
        · rw [if_neg (by omega), neg_one_mul]
          have hqr := jacobiSym.quadratic_reciprocity_three_mod_four hq3' hp3
          linarith
      calc jacobiSym 2 p * jacobiSym (p : ℤ) (d / 2)
          = jacobiSym 2 p * ((if p % 4 = 1 then 1 else -1) * jacobiSym ((d / 2 : ℕ) : ℤ) p) := by
            rw [hpair]
        _ = (if p % 4 = 1 then 1 else -1) * (jacobiSym 2 p * jacobiSym ((d / 2 : ℕ) : ℤ) p) := by
            ring
        _ = (if p % 4 = 1 then 1 else -1) * jacobiSym (2 * ((d / 2 : ℕ) : ℤ)) p := by
            rw [← jacobiSym.mul_left]
        _ = (if p % 4 = 1 then 1 else -1) * jacobiSym (d : ℤ) p := by congr 2; omega
    · exfalso; rw [hm] at h3 h1 h2; omega

/-- **Exact Evaluation of `imagQuadChar d` at `p = 2`**:
- `0` if `d % 4 ≠ 3` (`2 ∣ imagQuadDiscNat d`),
- `1` if `d % 8 = 7`,
- `-1` if `d % 8 = 3`. -/
theorem imagQuadChar_apply_two {d : ℕ} (hd : 0 < d) :
    imagQuadChar d (2 : ZMod (imagQuadDiscNat d)) =
      if d % 4 = 3 then (if d % 8 = 7 then 1 else -1) else 0 := by
  have hm : imagQuadParam d = d := imagQuadParam_eq_self hd
  by_cases h3 : d % 4 = 3
  · rw [if_pos h3]
    have hD : imagQuadDiscNat d = d := by rw [imagQuadDiscNat_eq hd, if_pos h3]
    have hcop : Nat.Coprime 2 (imagQuadDiscNat d) := by
      rw [hD]
      exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr (by omega)
    have h2u : IsUnit (2 : ZMod (imagQuadDiscNat d)) := by
      change IsUnit ((2 : ℕ) : ZMod (imagQuadDiscNat d))
      exact (ZMod.isUnit_iff_coprime 2 (imagQuadDiscNat d)).mpr hcop
    rw [imagQuadChar, dirichletCharOfIntUnitHom_apply_isUnit' _ h2u]
    unfold imagQuadUnitHom
    dsimp only
    rw [dif_pos (by rwa [hm]), coe_jacobiUnitHom']
    have hmod : (((h2u.unit : ZMod (imagQuadDiscNat d)).val : ℤ)) ≡
        (2 : ℤ) [ZMOD (imagQuadDiscNat d : ℕ)] := by
      rw [← ZMod.intCast_eq_intCast_iff]
      push_cast
      rw [ZMod.natCast_zmod_val, IsUnit.unit_spec]
    rw [jacobiSym.mod_left' hmod, hD, jacobiSym.at_two (Nat.odd_iff.mpr (by omega))]
    have h8 : d % 8 = 7 ∨ d % 8 = 3 := by omega
    rcases h8 with hd8 | hd8
    · rw [if_pos hd8]
      have hc : (d : ZMod 8) = 7 := by
        rw [← Nat.cast_ofNat (n := 7), ZMod.natCast_eq_natCast_iff]; exact hd8
      rw [hc]; simp [show ZMod.χ₈ (7 : ZMod 8) = 1 by decide]
    · rw [if_neg (by omega)]
      have hc : (d : ZMod 8) = 3 := by
        rw [← Nat.cast_ofNat (n := 3), ZMod.natCast_eq_natCast_iff]; exact hd8
      rw [hc]; simp [show ZMod.χ₈ (3 : ZMod 8) = -1 by decide]
  · rw [if_neg h3]
    have h2D : 2 ∣ imagQuadDiscNat d := by
      rw [imagQuadDiscNat_eq hd, if_neg h3]; exact ⟨2 * d, by ring⟩
    have hnotu : ¬ IsUnit (2 : ZMod (imagQuadDiscNat d)) := by
      change ¬ IsUnit ((2 : ℕ) : ZMod (imagQuadDiscNat d))
      rw [ZMod.isUnit_iff_coprime]
      intro hcop
      exact (by norm_num : ¬ (2 : ℕ) ∣ 1) (hcop.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl h2D)
    exact MulChar.map_nonunit _ hnotu

/-- Helper: every odd prime `p` has a nonzero quadratic nonresidue in `ZMod p`. -/
private lemma exists_nonsquare_ne_zero_zmod' {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ r : ZMod p, r ≠ 0 ∧ ¬ IsSquare r := by
  have hp : p.Prime := Fact.out
  let sqMap : (ZMod p)ˣ → (ZMod p)ˣ := fun u => u ^ 2
  have hnot_inj : ¬ Function.Injective sqMap := by
    intro hinj
    have h1 : (1 : (ZMod p)ˣ) = -1 := hinj (by simp [sqMap])
    have hv : (1 : ZMod p) = -1 := congrArg Units.val h1
    have h20 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hv
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h20
    exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hp.two_le)
  have hnot_surj : ¬ Function.Surjective sqMap :=
    mt (Finite.injective_iff_surjective (f := sqMap)).mpr hnot_inj
  unfold Function.Surjective at hnot_surj
  push Not at hnot_surj
  obtain ⟨u, hu⟩ := hnot_surj
  refine ⟨(u : ZMod p), u.ne_zero, ?_⟩
  rintro ⟨x, hx⟩
  have hx_ne : x ≠ 0 := fun h0 => u.ne_zero (by rw [hx, h0, mul_zero])
  exact hu (isUnit_iff_ne_zero.mpr hx_ne).unit (Units.ext (by simp [sqMap, sq, hx]))

/-- **Primitivity Criterion**: if for every prime `p ∣ q`, there exists a unit `u : (ZMod q)ˣ`
such that `ZMod.cast (u : ZMod q) = (1 : ZMod (q / p))` and `χ u ≠ 1`, then `χ.IsPrimitive`. -/
private theorem isPrimitive_of_forall_prime_witness {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q}
    (hw : ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ u : (ZMod q)ˣ, (ZMod.cast (u : ZMod q) : ZMod (q / p)) = 1 ∧ χ (u : ZMod q) ≠ 1) :
    χ.IsPrimitive := by
  show χ.conductor = q
  apply Nat.dvd_antisymm χ.conductor_dvd_level
  by_contra hnot
  have hk_dvd : χ.conductor ∣ q := χ.conductor_dvd_level
  have hq_pos : 0 < q := NeZero.pos q
  have hk_pos : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hk_lt : χ.conductor < q := lt_of_le_of_ne (Nat.le_of_dvd hq_pos hk_dvd)
    (by rintro h; exact hnot (by rw [h]))
  have hquot_gt1 : 1 < q / χ.conductor := by
    have hmul : χ.conductor * (q / χ.conductor) = q := Nat.mul_div_cancel' hk_dvd
    nlinarith
  set p := (q / χ.conductor).minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hp_dvd_quot : p ∣ q / χ.conductor := Nat.minFac_dvd _
  have hp_dvd_q : p ∣ q := dvd_trans hp_dvd_quot (Nat.div_dvd_of_dvd hk_dvd)
  have hk_dvd_qp : χ.conductor ∣ q / p := by
    obtain ⟨t, ht⟩ := hp_dvd_quot
    refine ⟨t, ?_⟩
    have hmul1 : χ.conductor * (p * t) = q := by rw [← ht, Nat.mul_div_cancel' hk_dvd]
    have hmul2 : p * (q / p) = q := Nat.mul_div_cancel' hp_dvd_q
    have : p * (χ.conductor * t) = p * (q / p) := by linarith
    exact (Nat.eq_of_mul_eq_mul_left hp.pos this).symm
  obtain ⟨u, hu_mod, hu_ne⟩ := hw p hp hp_dvd_q
  obtain ⟨hdvd_c, ψ, hψ⟩ := χ.factorsThrough_conductor
  have hcast_k : ZMod.cast (u : ZMod q) = (1 : ZMod χ.conductor) := by
    have hqp_dvd : q / p ∣ q := Nat.div_dvd_of_dvd hp_dvd_q
    have hcomp : (ZMod.castHom hk_dvd_qp (ZMod χ.conductor)).comp
        (ZMod.castHom hqp_dvd (ZMod (q / p))) = ZMod.castHom hk_dvd (ZMod χ.conductor) :=
      ZMod.castHom_comp hk_dvd_qp hqp_dvd
    have h1 := congrArg (fun f => f (u : ZMod q)) hcomp
    simp only [RingHom.comp_apply, ZMod.castHom_apply] at h1
    rw [← h1, hu_mod]
    change ZMod.castHom hk_dvd_qp (ZMod χ.conductor) 1 = 1
    exact map_one _
  have hval : χ (u : ZMod q) = 1 := by
    rw [hψ, DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe]
    change ψ ((ZMod.unitsMap hdvd_c u : (ZMod χ.conductor)ˣ) : ZMod χ.conductor) = 1
    have hv : ((ZMod.unitsMap hdvd_c u : (ZMod χ.conductor)ˣ) : ZMod χ.conductor) = 1 := hcast_k
    rw [hv, map_one]
  exact hu_ne hval

/-- **UNCONDITIONAL PRIMITIVITY OF `imagQuadChar d`**:
for EVERY squarefree `d > 0`, `(imagQuadChar d).IsPrimitive`! -/
theorem imagQuadChar_isPrimitive {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) :
    (imagQuadChar d).IsPrimitive := by
  have hm : imagQuadParam d = d := imagQuadParam_eq_self hd
  have hne0 : d % 4 ≠ 0 := squarefree_mod_four_ne_zero' hsf
  refine isPrimitive_of_forall_prime_witness fun p hp hpD => ?_
  by_cases hp2 : p = 2
  · subst hp2
    have hd_ne3 : d % 4 ≠ 3 := by
      intro h3
      have hD : imagQuadDiscNat d = d := by rw [imagQuadDiscNat_eq hd, if_pos h3]
      rw [hD] at hpD; omega
    by_cases hd1 : d % 4 = 1
    · -- `|D| = 4 * d`, `|D| / 2 = 2 * d`, `gcd(4, d) = 1`. Pick `n ≡ 3 [MOD 4]`, `n ≡ 1 [MOD d]`.
      have hD : imagQuadDiscNat d = 4 * d := by rw [imagQuadDiscNat_eq hd, if_neg hd_ne3]
      have hcop4d : Nat.Coprime 4 d := by
        have hcop2d : Nat.Coprime 2 d :=
          (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr (by omega)
        exact hcop2d.pow_left 2
      obtain ⟨n, hn4, hnd⟩ := Nat.chineseRemainder hcop4d 3 1
      have hcop_nD : Nat.Coprime n (imagQuadDiscNat d) := by
        rw [hD]
        refine Nat.Coprime.mul_right ?_ ?_
        · have : n % 4 = 3 := hn4
          have h2 : Nat.Coprime n 2 :=
            (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr (by omega) |>.symm
          exact h2.pow_right 2
        · rw [Nat.Coprime, hnd.gcd_eq]; exact Nat.gcd_one_left d
      have hnu : IsUnit (n : ZMod (imagQuadDiscNat d)) :=
        (ZMod.isUnit_iff_coprime n (imagQuadDiscNat d)).mpr hcop_nD
      refine ⟨hnu.unit, ?_, ?_⟩
      · have hmod2 : n ≡ 1 [MOD 2] := by
          have : n % 4 = 3 := hn4
          change n % 2 = 1 % 2; omega
        have hcop2d : Nat.Coprime 2 d :=
          (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr (by omega)
        have hmod2d : n ≡ 1 [MOD 2 * d] :=
          (Nat.modEq_and_modEq_iff_modEq_mul hcop2d).mp ⟨hmod2, hnd⟩
        have hdiv : imagQuadDiscNat d / 2 = 2 * d := by rw [hD]; omega
        rw [IsUnit.unit_spec, ZMod.cast_natCast (Nat.div_dvd_of_dvd hpD) n, hdiv]
        simpa using (ZMod.natCast_eq_natCast_iff n 1 (2 * d)).mpr hmod2d
      · rw [IsUnit.unit_spec, imagQuadChar, dirichletCharOfIntUnitHom_apply_isUnit' _ hnu]
        have hz : ((imagQuadUnitHom d hnu.unit : ℤˣ) : ℤ) = -1 := by
          unfold imagQuadUnitHom
          dsimp only
          rw [dif_neg (by rw [hm]; exact hd_ne3), dif_pos (by rw [hm]; exact hd1)]
          simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
          have h4D : 4 ∣ imagQuadDiscNat d := by rw [hD]; exact ⟨d, rfl⟩
          have hdD : imagQuadParam d ∣ imagQuadDiscNat d := by rw [hD, hm]; exact ⟨4, by ring⟩
          have hn_odd : _root_.Odd n := by have : n % 4 = 3 := hn4; exact Nat.odd_iff.mpr (by omega)
          have hu4 : IsUnit (n : ZMod 4) := by
            have h3 : (n : ZMod 4) = 3 := by
              rw [← Nat.cast_ofNat (n := 3), ZMod.natCast_eq_natCast_iff]; exact hn4
            rw [h3]; decide
          have hmap4 : ZMod.unitsMap h4D hnu.unit = hu4.unit := by
            apply Units.ext; change ZMod.cast (n : ZMod (imagQuadDiscNat d)) = (n : ZMod 4)
            exact ZMod.cast_natCast h4D n
          rw [hmap4, coe_chi4UnitHom'_nat hn_odd hu4, if_neg (by have : n % 4 = 3 := hn4; omega),
            coe_jacobiUnitHom']
          have hmod1 : (((ZMod.unitsMap hdD hnu.unit : (ZMod (imagQuadParam d))ˣ) :
              ZMod (imagQuadParam d)).val : ℤ) ≡ (1 : ℤ) [ZMOD (imagQuadParam d : ℕ)] := by
            rw [← ZMod.intCast_eq_intCast_iff]; push_cast
            rw [ZMod.natCast_zmod_val]
            change ZMod.cast (n : ZMod (imagQuadDiscNat d)) = (1 : ZMod (imagQuadParam d))
            rw [ZMod.cast_natCast hdD n, hm]
            simpa using (ZMod.natCast_eq_natCast_iff n 1 d).mpr hnd
          rw [jacobiSym.mod_left' hmod1, jacobiSym.one_left, mul_one]
        rw [hz]; norm_num
    · -- `d % 4 = 2`, `|D| = 8 * (d/2)`, `|D|/2 = 4 * (d/2)`, `gcd(8, d/2) = 1`. Pick `n ≡ 5 [MOD 8]`, `n ≡ 1 [MOD d/2]`.
      have hd2 : d % 4 = 2 := by omega
      have hD : imagQuadDiscNat d = 4 * d := by rw [imagQuadDiscNat_eq hd, if_neg hd_ne3]
      have hD8 : imagQuadDiscNat d = 8 * (d / 2) := by omega
      have hq_odd : _root_.Odd (d / 2) := Nat.odd_iff.mpr (by omega)
      have hcop2q : Nat.Coprime 2 (d / 2) :=
        (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr (by omega)
      have hcop8q : Nat.Coprime 8 (d / 2) := hcop2q.pow_left 3
      have hcop4q : Nat.Coprime 4 (d / 2) := hcop2q.pow_left 2
      obtain ⟨n, hn8, hnq⟩ := Nat.chineseRemainder hcop8q 5 1
      have hcop_nD : Nat.Coprime n (imagQuadDiscNat d) := by
        rw [hD8]
        refine Nat.Coprime.mul_right ?_ ?_
        · have : n % 8 = 5 := hn8
          have h2 : Nat.Coprime n 2 :=
            (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr (by omega) |>.symm
          exact h2.pow_right 3
        · rw [Nat.Coprime, hnq.gcd_eq]; exact Nat.gcd_one_left _
      have hnu : IsUnit (n : ZMod (imagQuadDiscNat d)) :=
        (ZMod.isUnit_iff_coprime n (imagQuadDiscNat d)).mpr hcop_nD
      refine ⟨hnu.unit, ?_, ?_⟩
      · have hmod4 : n ≡ 1 [MOD 4] := by
          have : n % 8 = 5 := hn8
          change n % 4 = 1 % 4; omega
        have hmod4q : n ≡ 1 [MOD 4 * (d / 2)] :=
          (Nat.modEq_and_modEq_iff_modEq_mul hcop4q).mp ⟨hmod4, hnq⟩
        have hdiv : imagQuadDiscNat d / 2 = 4 * (d / 2) := by rw [hD8]; omega
        rw [IsUnit.unit_spec, ZMod.cast_natCast (Nat.div_dvd_of_dvd hpD) n, hdiv]
        simpa using (ZMod.natCast_eq_natCast_iff n 1 (4 * (d / 2))).mpr hmod4q
      · rw [IsUnit.unit_spec, imagQuadChar, dirichletCharOfIntUnitHom_apply_isUnit' _ hnu]
        have hn_odd : _root_.Odd n := by have : n % 8 = 5 := hn8; exact Nat.odd_iff.mpr (by omega)
        have h4D : 4 ∣ imagQuadDiscNat d := by rw [hD]; exact ⟨d, rfl⟩
        have h8D : 8 ∣ imagQuadDiscNat d := by rw [hD8]; exact ⟨d / 2, rfl⟩
        have hqD : imagQuadParam d / 2 ∣ imagQuadDiscNat d := by
          rw [hD8, hm]; exact ⟨8, by ring⟩
        have hu4 : IsUnit (n : ZMod 4) := by
          have : (n : ZMod 4) = 1 := by
            rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
            have : n % 8 = 5 := hn8; change n % 4 = 1 % 4; omega
          rw [this]; decide
        have hu8 : IsUnit (n : ZMod 8) := by
          have : (n : ZMod 8) = 5 := by
            rw [← Nat.cast_ofNat (n := 5), ZMod.natCast_eq_natCast_iff]; exact hn8
          rw [this]; decide
        have hmap4 : ZMod.unitsMap h4D hnu.unit = hu4.unit := by
          apply Units.ext; change ZMod.cast (n : ZMod (imagQuadDiscNat d)) = (n : ZMod 4)
          exact ZMod.cast_natCast h4D n
        have hmap8 : ZMod.unitsMap h8D hnu.unit = hu8.unit := by
          apply Units.ext; change ZMod.cast (n : ZMod (imagQuadDiscNat d)) = (n : ZMod 8)
          exact ZMod.cast_natCast h8D n
        have hc4 : ((chi4UnitHom' hu4.unit : ℤˣ) : ℤ) = 1 := by
          rw [coe_chi4UnitHom'_nat hn_odd hu4, if_pos (by have : n % 8 = 5 := hn8; omega)]
        have hc8 : ((chi8UnitHom' hu8.unit : ℤˣ) : ℤ) = -1 := by
          rw [coe_chi8UnitHom'_nat hn_odd hu8, jacobiSym.at_two hn_odd]
          have hc : (n : ZMod 8) = 5 := by
            rw [← Nat.cast_ofNat (n := 5), ZMod.natCast_eq_natCast_iff]; exact hn8
          rw [hc]; decide
        have hjac1 : ∀ (hodd' : _root_.Odd (imagQuadParam d / 2)) [NeZero (imagQuadParam d / 2)],
            ((jacobiUnitHom' (imagQuadParam d / 2) hodd' (ZMod.unitsMap hqD hnu.unit) : ℤˣ) : ℤ) = 1 := by
          intro hodd' _
          rw [coe_jacobiUnitHom' hodd']
          have hmod1 : (((ZMod.unitsMap hqD hnu.unit : (ZMod (imagQuadParam d / 2))ˣ) :
              ZMod (imagQuadParam d / 2)).val : ℤ) ≡ (1 : ℤ) [ZMOD (imagQuadParam d / 2 : ℕ)] := by
            rw [← ZMod.intCast_eq_intCast_iff]; push_cast
            rw [ZMod.natCast_zmod_val]
            change ZMod.cast (n : ZMod (imagQuadDiscNat d)) = (1 : ZMod (imagQuadParam d / 2))
            rw [ZMod.cast_natCast hqD n, hm]
            simpa using (ZMod.natCast_eq_natCast_iff n 1 (d / 2)).mpr hnq
          rw [jacobiSym.mod_left' hmod1, jacobiSym.one_left]
        have hz : ((imagQuadUnitHom d hnu.unit : ℤˣ) : ℤ) = -1 := by
          unfold imagQuadUnitHom
          dsimp only
          rw [dif_neg (by rw [hm]; exact hd_ne3), dif_neg (by rw [hm]; exact hd1),
            dif_pos (by rw [hm]; exact hd2)]
          split_ifs
          · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
            rw [hmap4, hmap8, hc4, hc8, hjac1]; ring
          · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
            rw [hmap8, hc8, hjac1]; ring
        rw [hz]; norm_num
  · -- Odd prime `p ∣ |D|`, so `p ∣ d` and `gcd(p, |D|/p) = 1` by squarefreeness of `d`!
    have : Fact p.Prime := ⟨hp⟩
    have hcop2 : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr fun h2 =>
      hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h2) hp.two_le)
    have hcop4 : Nat.Coprime p 4 := hcop2.pow_right 2
    have hcop8 : Nat.Coprime p 8 := hcop2.pow_right 3
    have hpd : p ∣ d := by
      rw [imagQuadDiscNat_eq hd] at hpD
      split_ifs at hpD
      · exact hpD
      · exact hcop4.dvd_of_dvd_mul_left hpD
    set M : ℕ := imagQuadDiscNat d / p
    have hD_eq : imagQuadDiscNat d = p * M := (Nat.mul_div_cancel' hpD).symm
    have hcop_pM : Nat.Coprime p M := by
      rw [hp.coprime_iff_not_dvd]
      intro hpM
      have hppD : p * p ∣ imagQuadDiscNat d := by
        obtain ⟨k, hk⟩ := hpM; exact ⟨k, by rw [hD_eq, hk]; ring⟩
      have hppd : p * p ∣ d := by
        rw [imagQuadDiscNat_eq hd] at hppD
        split_ifs at hppD
        · exact hppD
        · exact (hcop4.mul_left hcop4).dvd_of_dvd_mul_left hppD
      exact hp.not_isUnit (hsf p hppd)
    obtain ⟨r, hr_ne, hr_nsq⟩ := exists_nonsquare_ne_zero_zmod' (p := p) hp2
    obtain ⟨n, hn_p, hn_M⟩ := Nat.chineseRemainder hcop_pM r.val 1
    let a : ZMod (imagQuadDiscNat d) := (n : ZMod (imagQuadDiscNat d))
    have ha_p : (n : ZMod p) = r := by
      have : (n : ZMod p) = ((r.val : ℕ) : ZMod p) := (ZMod.natCast_eq_natCast_iff n r.val p).mpr hn_p
      rwa [ZMod.natCast_zmod_val] at this
    have ha_M : (n : ZMod M) = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff n 1 M).mpr hn_M
    have ha_u : IsUnit a := by
      dsimp only [a]
      rw [ZMod.isUnit_iff_coprime, hD_eq]
      refine Nat.Coprime.mul_right ?_ ?_
      · have hru : IsUnit (n : ZMod p) := by rw [ha_p]; exact isUnit_iff_ne_zero.mpr hr_ne
        exact (ZMod.isUnit_iff_coprime n p).mp hru
      · have h1u : IsUnit (n : ZMod M) := by rw [ha_M]; exact isUnit_one
        exact (ZMod.isUnit_iff_coprime n M).mp h1u
    have hcast_eq : ∀ (k : ℕ) (hk : k ∣ M), ZMod.cast (R := ZMod k) a = (1 : ZMod k) := by
      intro k hk
      have hkD : k ∣ imagQuadDiscNat d := dvd_trans hk ⟨p, by rw [hD_eq, mul_comm]⟩
      dsimp only [a]
      rw [ZMod.cast_natCast hkD n]
      have hnk : n ≡ 1 [MOD k] := hn_M.of_dvd hk
      simpa using (ZMod.natCast_eq_natCast_iff n 1 k).mpr hnk
    have hjac_p : jacobiSym (a.val : ℤ) p = -1 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym]
      have hmod : (a.val : ZMod p) = r := by
        rw [← ZMod.cast_natCast hpD a.val, ZMod.natCast_zmod_val]
        dsimp only [a]
        rw [ZMod.cast_natCast hpD n, ha_p]
      rw [legendreSym.eq_neg_one_iff]
      intro hsq
      apply hr_nsq
      rwa [← hmod, ← Int.cast_natCast (R := ZMod p)]
    have hjac_div : ∀ (m : ℕ) (hpm : p ∣ m) (hmM : m / p ∣ M),
        jacobiSym (a.val : ℤ) m = -1 := by
      intro m hpm hmM
      have hM_ne : M ≠ 0 := fun h0 => by
        have : imagQuadDiscNat d = 0 := by rw [hD_eq, h0, mul_zero]
        exact NeZero.ne (imagQuadDiscNat d) this
      have hmp_ne : m / p ≠ 0 := fun h0 => hM_ne (by rw [h0] at hmM; exact zero_dvd_iff.mp hmM)
      have : NeZero (m / p) := ⟨hmp_ne⟩
      have hm_eq : m = p * (m / p) := (Nat.mul_div_cancel' hpm).symm
      rw [hm_eq, jacobiSym.mul_right, hjac_p]
      have hmod1 : (a.val : ℤ) ≡ (1 : ℤ) [ZMOD (m / p : ℕ)] := by
        rw [← ZMod.intCast_eq_intCast_iff]
        push_cast
        have hmpD : m / p ∣ imagQuadDiscNat d := dvd_trans hmM ⟨p, by rw [hD_eq, mul_comm]⟩
        rw [← ZMod.cast_natCast hmpD a.val, ZMod.natCast_zmod_val]
        exact hcast_eq (m / p) hmM
      rw [jacobiSym.mod_left' hmod1, jacobiSym.one_left, mul_one]
    have hjac_u : ∀ (m : ℕ) [NeZero m] (hm' : _root_.Odd m) (hpm : p ∣ m) (hmM : m / p ∣ M)
        (hmD : m ∣ imagQuadDiscNat d),
        ((jacobiUnitHom' m hm' (ZMod.unitsMap hmD ha_u.unit) : ℤˣ) : ℤ) = -1 := by
      intro m _ hm' hpm hmM hmD
      rw [coe_jacobiUnitHom' hm']
      have hmod : (((ZMod.unitsMap hmD ha_u.unit : (ZMod m)ˣ) : ZMod m).val : ℤ) ≡
          (a.val : ℤ) [ZMOD (m : ℕ)] := by
        rw [← ZMod.intCast_eq_intCast_iff]
        push_cast
        rw [ZMod.natCast_zmod_val, ← ZMod.cast_natCast hmD a.val, ZMod.natCast_zmod_val]
        rfl
      rw [jacobiSym.mod_left' hmod, hjac_div m hpm hmM]
    refine ⟨ha_u.unit, ?_, ?_⟩
    · rw [IsUnit.unit_spec]
      exact hcast_eq M dvd_rfl
    · rw [IsUnit.unit_spec, imagQuadChar, dirichletCharOfIntUnitHom_apply_isUnit' _ ha_u]
      have hz : ((imagQuadUnitHom d ha_u.unit : ℤˣ) : ℤ) = -1 := by
        unfold imagQuadUnitHom
        dsimp only
        split_ifs with h3 h1 h2 hq1
        · rw [coe_jacobiUnitHom']
          exact hjac_div (imagQuadDiscNat d) hpD dvd_rfl
        · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
          have h4D : 4 ∣ imagQuadDiscNat d := by unfold imagQuadDiscNat; rw [if_neg h3]; exact ⟨_, rfl⟩
          have h4M : 4 ∣ M := hcop4.symm.dvd_of_dvd_mul_left (by rw [← hD_eq]; exact h4D)
          have hmap4 : ((ZMod.unitsMap h4D ha_u.unit : (ZMod 4)ˣ) : ZMod 4) = 1 := by
            change ZMod.cast a = (1 : ZMod 4); exact hcast_eq 4 h4M
          have hc4 : ((chi4UnitHom' (ZMod.unitsMap h4D ha_u.unit) : ℤˣ) : ℤ) = 1 := by
            change (((if ((ZMod.unitsMap h4D ha_u.unit : (ZMod 4)ˣ) : ZMod 4) = 1 then
              (1 : ℤˣ) else -1) : ℤˣ) : ℤ) = 1
            rw [hmap4]; simp
          have hpm : p ∣ imagQuadParam d := by rwa [hm]
          have hmM : imagQuadParam d / p ∣ M := by
            refine ⟨4, ?_⟩
            have hD4 : p * M = 4 * imagQuadParam d := by
              rw [← hD_eq]; unfold imagQuadDiscNat; rw [if_neg h3]
            have hmp : p * (imagQuadParam d / p) = imagQuadParam d := Nat.mul_div_cancel' hpm
            exact Nat.eq_of_mul_eq_mul_left hp.pos (by linarith)
          rw [hc4, hjac_u (imagQuadParam d) _ hpm hmM, one_mul]
        · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
          have h4D : 4 ∣ imagQuadDiscNat d := by unfold imagQuadDiscNat; rw [if_neg h3]; exact ⟨_, rfl⟩
          have h8D : 8 ∣ imagQuadDiscNat d := by
            unfold imagQuadDiscNat; rw [if_neg h3]; exact ⟨imagQuadParam d / 2, by omega⟩
          have h4M : 4 ∣ M := hcop4.symm.dvd_of_dvd_mul_left (by rw [← hD_eq]; exact h4D)
          have h8M : 8 ∣ M := hcop8.symm.dvd_of_dvd_mul_left (by rw [← hD_eq]; exact h8D)
          have hmap4 : ((ZMod.unitsMap h4D ha_u.unit : (ZMod 4)ˣ) : ZMod 4) = 1 := by
            change ZMod.cast a = (1 : ZMod 4); exact hcast_eq 4 h4M
          have hmap8 : ((ZMod.unitsMap h8D ha_u.unit : (ZMod 8)ˣ) : ZMod 8) = 1 := by
            change ZMod.cast a = (1 : ZMod 8); exact hcast_eq 8 h8M
          have hc4 : ((chi4UnitHom' (ZMod.unitsMap h4D ha_u.unit) : ℤˣ) : ℤ) = 1 := by
            change (((if ((ZMod.unitsMap h4D ha_u.unit : (ZMod 4)ˣ) : ZMod 4) = 1 then
              (1 : ℤˣ) else -1) : ℤˣ) : ℤ) = 1
            rw [hmap4]; simp
          have hc8 : ((chi8UnitHom' (ZMod.unitsMap h8D ha_u.unit) : ℤˣ) : ℤ) = 1 := by
            change (((if ((ZMod.unitsMap h8D ha_u.unit : (ZMod 8)ˣ) : ZMod 8) = 1 ∨
              ((ZMod.unitsMap h8D ha_u.unit : (ZMod 8)ˣ) : ZMod 8) = 7 then
              (1 : ℤˣ) else -1) : ℤˣ) : ℤ) = 1
            rw [hmap8]; simp
          have hp_half : p ∣ imagQuadParam d / 2 := by
            have h2half : 2 * (imagQuadParam d / 2) = imagQuadParam d := by omega
            exact hcop2.dvd_of_dvd_mul_left (by rw [h2half, hm]; exact hpd)
          have hmM : (imagQuadParam d / 2) / p ∣ M := by
            refine ⟨8, ?_⟩
            have hD8 : p * M = 8 * (imagQuadParam d / 2) := by
              rw [← hD_eq]; unfold imagQuadDiscNat; rw [if_neg h3]; omega
            have hmp : p * ((imagQuadParam d / 2) / p) = imagQuadParam d / 2 :=
              Nat.mul_div_cancel' hp_half
            exact Nat.eq_of_mul_eq_mul_left hp.pos (by linarith)
          have : NeZero (imagQuadParam d / 2) := ⟨by have := imagQuadParam_pos d; omega⟩
          rw [hc4, hc8, hjac_u (imagQuadParam d / 2) _ hp_half hmM, one_mul, one_mul]
        · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
          have h8D : 8 ∣ imagQuadDiscNat d := by
            unfold imagQuadDiscNat; rw [if_neg h3]; exact ⟨imagQuadParam d / 2, by omega⟩
          have h8M : 8 ∣ M := hcop8.symm.dvd_of_dvd_mul_left (by rw [← hD_eq]; exact h8D)
          have hmap8 : ((ZMod.unitsMap h8D ha_u.unit : (ZMod 8)ˣ) : ZMod 8) = 1 := by
            change ZMod.cast a = (1 : ZMod 8); exact hcast_eq 8 h8M
          have hc8 : ((chi8UnitHom' (ZMod.unitsMap h8D ha_u.unit) : ℤˣ) : ℤ) = 1 := by
            change (((if ((ZMod.unitsMap h8D ha_u.unit : (ZMod 8)ˣ) : ZMod 8) = 1 ∨
              ((ZMod.unitsMap h8D ha_u.unit : (ZMod 8)ˣ) : ZMod 8) = 7 then
              (1 : ℤˣ) else -1) : ℤˣ) : ℤ) = 1
            rw [hmap8]; simp
          have hp_half : p ∣ imagQuadParam d / 2 := by
            have h2half : 2 * (imagQuadParam d / 2) = imagQuadParam d := by omega
            exact hcop2.dvd_of_dvd_mul_left (by rw [h2half, hm]; exact hpd)
          have hmM : (imagQuadParam d / 2) / p ∣ M := by
            refine ⟨8, ?_⟩
            have hD8 : p * M = 8 * (imagQuadParam d / 2) := by
              rw [← hD_eq]; unfold imagQuadDiscNat; rw [if_neg h3]; omega
            have hmp : p * ((imagQuadParam d / 2) / p) = imagQuadParam d / 2 :=
              Nat.mul_div_cancel' hp_half
            exact Nat.eq_of_mul_eq_mul_left hp.pos (by linarith)
          have : NeZero (imagQuadParam d / 2) := ⟨by have := imagQuadParam_pos d; omega⟩
          rw [hc8, hjac_u (imagQuadParam d / 2) _ hp_half hmM, one_mul]
        · exfalso; rw [hm] at h3 h1 h2; omega
      rw [hz]; norm_num

end ImaginaryKroneckerCharacter

/-! ## Section 3: Kummer–Dedekind Prime Splitting & Exact Imaginary Quadratic Dedekind Zeta Factorization -/

section ImaginaryDedekindZeta

/-- Helper: bijection between `PrimesAbove K p` and the set of distinct prime ideals in
`normalizedFactors (Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}))`. -/
private def primesAboveEquivNormalizedFactors' {K : Type*} [Field K] [NumberField K]
    {p : ℕ} (hp : p.Prime) :
    PrimesAbove K p ≃
      {J : Ideal (𝓞 K) // J ∈ UniqueFactorizationMonoid.normalizedFactors
        (Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}))} := by
  have hp_map_ne : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    intro hbot
    have hp_mem : (p : 𝓞 K) ∈ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) := by
      have : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) :=
        Ideal.mem_map_of_mem _ (Ideal.subset_span rfl)
      simpa using this
    rw [hbot, Ideal.mem_bot] at hp_mem
    exact hp.ne_zero (Nat.cast_eq_zero.mp hp_mem)
  refine
    { toFun := fun v => ⟨v.1.asIdeal, ?_⟩
      invFun := fun J =>
        have hP : J.1.IsPrime ∧ J.1 ≠ ⊥ := mem_normalizedFactors_heightOne J.2
        let v : HeightOneSpectrum (𝓞 K) := ⟨J.1, hP.1, hP.2⟩
        ⟨v, by
          rw [dvd_absNorm_iff_liesOver v hp]
          have hdvd : J.1 ∣ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) :=
            UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors J.2
          have hle : Ideal.span {(p : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 K)) J.1 :=
            Ideal.map_le_iff_le_comap.mp (Ideal.dvd_iff_le.mp hdvd)
          have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
            PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
          have : J.1.IsPrime := hP.1
          have hne_top : Ideal.comap (algebraMap ℤ (𝓞 K)) J.1 ≠ ⊤ :=
            Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ _)
          exact ⟨hmax.eq_of_le hne_top hle⟩⟩
      left_inv := fun v => Subtype.ext (HeightOneSpectrum.ext rfl)
      right_inv := fun J => Subtype.ext rfl }
  · have hlo : v.1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
      (dvd_absNorm_iff_liesOver v.1 hp).mp v.2
    have hle : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ v.1.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      exact le_of_eq hlo.over
    have hdvd : v.1.asIdeal ∣ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) :=
      Ideal.dvd_iff_le.mpr hle
    have hirr : Irreducible v.1.asIdeal :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mpr
        (Ideal.prime_of_isPrime v.1.ne_bot v.1.isPrime)
    obtain ⟨q, hq_mem, hq_assoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hp_map_ne hirr hdvd
    have hq_eq : q = v.1.asIdeal := by
      obtain ⟨u, hu⟩ := hq_assoc
      have hu_one : (u : Ideal (𝓞 K)) = 1 := by
        rw [Ideal.one_eq_top, eq_top_iff, ← Ideal.one_eq_top, ← u.mul_inv]
        exact Ideal.mul_le_left
      rw [← hu, hu_one, mul_one]
    rwa [← hq_eq]

private lemma emultiplicity_eq_ramificationIdx' {K : Type*} [Field K] [NumberField K]
    {p : ℕ} (hp : p.Prime) (v : PrimesAbove K p) :
    emultiplicity v.1.asIdeal (Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)})) =
      (v.1.asIdeal.ramificationIdx ℤ : ℕ∞) := by
  have : v.1.asIdeal.IsPrime := v.1.isPrime
  have : v.1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := (dvd_absNorm_iff_liesOver v.1 hp).mp v.2
  have hmap_ne : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    intro hbot
    have hp_mem : (p : 𝓞 K) ∈ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) := by
      have := Ideal.mem_map_of_mem (algebraMap ℤ (𝓞 K)) (Ideal.subset_span (rfl : (p : ℤ) ∈ {(p : ℤ)}))
      simpa using this
    rw [hbot, Ideal.mem_bot] at hp_mem
    exact hp.ne_zero (Nat.cast_eq_zero.mp hp_mem)
  have hfin : FiniteMultiplicity v.1.asIdeal (Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)})) :=
    FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime v.1.ne_bot v.1.isPrime) hmap_ne
  rw [hfin.emultiplicity_eq_multiplicity,
    Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {(p : ℤ)}) v.1.asIdeal hmap_ne]

private lemma irreducible_of_natDegree_two_of_no_roots' {k : Type*} [Field k]
    {g : Polynomial k} (hg_deg : g.natDegree = 2) (hno : ∀ r : k, g.eval r ≠ 0) :
    Irreducible g := by
  have hg0 : g ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hg_deg; norm_num at hg_deg
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
  · have ha0 : a ≠ 0 := fun h => hg0 (by rw [hab, h, zero_mul])
    have hb0 : b ≠ 0 := fun h => hg0 (by rw [hab, h, mul_zero])
    have hsum : a.natDegree + b.natDegree = 2 := by
      rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, hg_deg]
    by_cases ha : a.natDegree = 0
    · left; exact Polynomial.isUnit_iff_degree_eq_zero.mpr
        (by rw [Polynomial.degree_eq_natDegree ha0, ha]; rfl)
    · by_cases hb : b.natDegree = 0
      · right; exact Polynomial.isUnit_iff_degree_eq_zero.mpr
          (by rw [Polynomial.degree_eq_natDegree hb0, hb]; rfl)
      · exfalso
        have ha1 : a.natDegree = 1 := by omega
        obtain ⟨r, hr⟩ := Polynomial.exists_root_of_degree_eq_one
          (by rw [Polynomial.degree_eq_natDegree ha0, ha1]; rfl)
        apply hno r
        rw [hab, Polynomial.eval_mul, Polynomial.IsRoot.def.mp hr, zero_mul]

/-- Exact `PrimesAbove` norm product for `ImagQuadField d` from the 3 Kummer–Dedekind cases. -/
private theorem imagQuad_local_eulerFactor_of_splitting {d : ℕ} (hd : 0 < d) (hsf : Squarefree d)
    {p : ℕ} [Fact p.Prime] [Fintype (PrimesAbove (ImagQuadField d) p)] (s : ℂ) :
    let I : Ideal ℤ := Ideal.span {(p : ℤ)}
    let g : Polynomial (ℤ ⧸ I) := Polynomial.map (Ideal.Quotient.mk I) (imagQuadMinPolyInt d)
    ((∃ r₁ r₂ : ℤ ⧸ I, r₁ ≠ r₂ ∧ g = (Polynomial.X - Polynomial.C r₁) * (Polynomial.X - Polynomial.C r₂)) →
      ∏ v : PrimesAbove (ImagQuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
        (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (1 : ℂ) * (p : ℂ) ^ (-s))⁻¹) ∧
    (Irreducible g →
      ∏ v : PrimesAbove (ImagQuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
        (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (-1 : ℂ) * (p : ℂ) ^ (-s))⁻¹) ∧
    ((∃ r : ℤ ⧸ I, g = (Polynomial.X - Polynomial.C r) ^ 2) →
      ∏ v : PrimesAbove (ImagQuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
        (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (0 : ℂ) * (p : ℂ) ^ (-s))⁻¹) := by
  classical
  have hp : p.Prime := Fact.out
  set I : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hI_max : I.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have : I.IsMaximal := hI_max
  let : Field (ℤ ⧸ I) := Ideal.Quotient.field I
  have hI_ne : I ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact Int.natCast_ne_zero.mpr hp.ne_zero
  have hcond : Ideal.comap (algebraMap ℤ (𝓞 (ImagQuadField d))) (conductor ℤ (imagQuadIntGen d)) ⊔ I = ⊤ := by
    rw [imagQuadField_conductor_eq_top hd hsf, Ideal.comap_top, top_sup_eq]
  have hint : IsIntegral ℤ (imagQuadIntGen d) := Algebra.IsIntegral.isIntegral (imagQuadIntGen d)
  have hg_eq : Polynomial.map (Ideal.Quotient.mk I) (minpoly ℤ (imagQuadIntGen d)) =
      Polynomial.map (Ideal.Quotient.mk I) (imagQuadMinPolyInt d) := by
    rw [minpoly_imagQuadIntGen d]
  let eKD := (primesAboveEquivNormalizedFactors' (K := ImagQuadField d) hp).trans
    (KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI_max hI_ne hcond hint)
  have hsum_ef : ∑ v : PrimesAbove (ImagQuadField d) p,
      v.1.asIdeal.ramificationIdx ℤ * v.1.asIdeal.inertiaDeg ℤ = 2 := by
    rw [sum_ramification_inertia_primesAbove (ImagQuadField d) hp, imagQuadField_finrank d]
  have habsNorm_v : ∀ v : PrimesAbove (ImagQuadField d) p,
      Ideal.absNorm v.1.asIdeal = p ^ v.1.asIdeal.inertiaDeg ℤ := fun v => by
    have : v.1.asIdeal.LiesOver I := (dvd_absNorm_iff_liesOver v.1 hp).mp v.2
    have : v.1.asIdeal.IsMaximal := heightOne_isMaximal v.1
    rw [Ideal.absNorm_eq_pow_inertiaDeg' v.1.asIdeal hp, Ideal.inertiaDeg'_eq_inertiaDeg I v.1.asIdeal]
  refine ⟨?_, ?_, ?_⟩
  · -- Case 1: Split
    rintro ⟨r₁, r₂, hr12, hg_fac⟩
    have hnorm_lin : ∀ r : ℤ ⧸ I, normalize (Polynomial.X - Polynomial.C r) = Polynomial.X - Polynomial.C r :=
      fun r => (Polynomial.monic_X_sub_C r).normalize_eq_self
    have hirr_lin : ∀ r : ℤ ⧸ I, Irreducible (Polynomial.X - Polynomial.C r) :=
      fun r => Polynomial.irreducible_X_sub_C r
    have hnf : UniqueFactorizationMonoid.normalizedFactors
        (Polynomial.map (Ideal.Quotient.mk I) (minpoly ℤ (imagQuadIntGen d))) =
        {Polynomial.X - Polynomial.C r₁, Polynomial.X - Polynomial.C r₂} := by
      rw [hg_eq, hg_fac, UniqueFactorizationMonoid.normalizedFactors_mul
        (Polynomial.monic_X_sub_C r₁).ne_zero (Polynomial.monic_X_sub_C r₂).ne_zero,
        UniqueFactorizationMonoid.normalizedFactors_irreducible (hirr_lin r₁),
        UniqueFactorizationMonoid.normalizedFactors_irreducible (hirr_lin r₂),
        hnorm_lin r₁, hnorm_lin r₂]
      rfl
    have hne_lin : (Polynomial.X - Polynomial.C r₁ : Polynomial (ℤ ⧸ I)) ≠ Polynomial.X - Polynomial.C r₂ := by
      intro h
      have h0 := congrArg (fun q => Polynomial.coeff q 0) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
        zero_sub, neg_inj] at h0
      exact hr12 h0
    have hcard : Fintype.card (PrimesAbove (ImagQuadField d) p) = 2 := by
      let hset : ({q : Polynomial (ℤ ⧸ I) //
          q ∈ UniqueFactorizationMonoid.normalizedFactors
            (Polynomial.map (Ideal.Quotient.mk I) (minpoly ℤ (imagQuadIntGen d)))}) ≃
          ({Polynomial.X - Polynomial.C r₁, Polynomial.X - Polynomial.C r₂} :
            Finset (Polynomial (ℤ ⧸ I))) :=
        { toFun := fun x => ⟨x.1, by
            have hx : x.1 ∈ ({Polynomial.X - Polynomial.C r₁, Polynomial.X - Polynomial.C r₂} :
                Multiset (Polynomial (ℤ ⧸ I))) := hnf ▸ x.2
            simpa using hx⟩
          invFun := fun x => ⟨x.1, by
            have hx : x.1 ∈ ({Polynomial.X - Polynomial.C r₁, Polynomial.X - Polynomial.C r₂} :
                Multiset (Polynomial (ℤ ⧸ I))) := by
              rcases Finset.mem_insert.mp x.2 with h | h
              · exact Multiset.mem_cons.mpr (Or.inl h)
              · exact Multiset.mem_cons.mpr (Or.inr (Multiset.mem_singleton.mpr (Finset.mem_singleton.mp h)))
            exact hnf.symm ▸ hx⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr (eKD.trans hset), Fintype.card_coe, Finset.card_pair hne_lin]
    have hf_all : ∀ v : PrimesAbove (ImagQuadField d) p, v.1.asIdeal.inertiaDeg ℤ = 1 := by
      intro v
      have hge1 : ∀ w : PrimesAbove (ImagQuadField d) p,
          1 ≤ w.1.asIdeal.ramificationIdx ℤ * w.1.asIdeal.inertiaDeg ℤ := fun w => by
        have : w.1.asIdeal.IsPrime := w.1.isPrime
        exact Nat.mul_pos (Ideal.ramificationIdx_pos w.1.asIdeal ℤ)
          (Ideal.inertiaDeg_pos w.1.asIdeal ℤ)
      have hle2 : v.1.asIdeal.ramificationIdx ℤ * v.1.asIdeal.inertiaDeg ℤ +
          ∑ w ∈ Finset.univ.erase v, w.1.asIdeal.ramificationIdx ℤ * w.1.asIdeal.inertiaDeg ℤ = 2 := by
        rw [← hsum_ef]
        exact Finset.add_sum_erase Finset.univ
          (fun w : PrimesAbove (ImagQuadField d) p => w.1.asIdeal.ramificationIdx ℤ * w.1.asIdeal.inertiaDeg ℤ)
          (Finset.mem_univ v)
      have herase_ge : 1 ≤ ∑ w ∈ Finset.univ.erase v,
          w.1.asIdeal.ramificationIdx ℤ * w.1.asIdeal.inertiaDeg ℤ := by
        calc 1 = (Finset.univ.erase v).card := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hcard]
          _ = ∑ _w ∈ Finset.univ.erase v, 1 := by simp
          _ ≤ _ := Finset.sum_le_sum fun w _ => hge1 w
      have hprod1 : v.1.asIdeal.ramificationIdx ℤ * v.1.asIdeal.inertiaDeg ℤ = 1 := by
        have := hge1 v; omega
      exact (mul_eq_one.mp hprod1).2
    calc ∏ v : PrimesAbove (ImagQuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹
        = ∏ _v : PrimesAbove (ImagQuadField d) p, (1 - (p : ℂ) ^ (-s))⁻¹ :=
          Finset.prod_congr rfl fun v _ => by rw [habsNorm_v v, hf_all v, pow_one]
      _ = ((1 - (p : ℂ) ^ (-s))⁻¹) ^ Fintype.card (PrimesAbove (ImagQuadField d) p) := by simp
      _ = (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (1 : ℂ) * (p : ℂ) ^ (-s))⁻¹ := by
          rw [hcard, sq, one_mul]
  · -- Case 2: Inert
    intro hirr_g
    set g : Polynomial (ℤ ⧸ I) := Polynomial.map (Ideal.Quotient.mk I) (imagQuadMinPolyInt d)
    have hnf : UniqueFactorizationMonoid.normalizedFactors
        (Polynomial.map (Ideal.Quotient.mk I) (minpoly ℤ (imagQuadIntGen d))) = {normalize g} := by
      rw [hg_eq, UniqueFactorizationMonoid.normalizedFactors_irreducible hirr_g]
    have hcard : Fintype.card (PrimesAbove (ImagQuadField d) p) = 1 := by
      let hset : ({q : Polynomial (ℤ ⧸ I) //
          q ∈ UniqueFactorizationMonoid.normalizedFactors
            (Polynomial.map (Ideal.Quotient.mk I) (minpoly ℤ (imagQuadIntGen d)))}) ≃
          ({normalize g} : Finset (Polynomial (ℤ ⧸ I))) :=
        { toFun := fun x => ⟨x.1, by
            have hx : x.1 ∈ ({normalize g} : Multiset (Polynomial (ℤ ⧸ I))) := hnf ▸ x.2
            simpa using hx⟩
          invFun := fun x => ⟨x.1, by
            have hx : x.1 ∈ ({normalize g} : Multiset (Polynomial (ℤ ⧸ I))) :=
              Multiset.mem_singleton.mpr (Finset.mem_singleton.mp x.2)
            exact hnf.symm ▸ hx⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr (eKD.trans hset), Fintype.card_coe, Finset.card_singleton]
    obtain ⟨v0, hv0⟩ := Fintype.card_eq_one_iff.mp hcard
    have he1 : v0.1.asIdeal.ramificationIdx ℤ = 1 := by
      have hem := KummerDedekind.emultiplicity_factors_map_eq_emultiplicity hI_max hI_ne hcond hint
        (primesAboveEquivNormalizedFactors' hp v0).2
      have hLHS : emultiplicity ((primesAboveEquivNormalizedFactors' hp v0).1)
          (Ideal.map (algebraMap ℤ (𝓞 (ImagQuadField d))) I) = (v0.1.asIdeal.ramificationIdx ℤ : ℕ∞) :=
        emultiplicity_eq_ramificationIdx' hp v0
      rw [hLHS] at hem
      have hq_eq : ((KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
          hI_max hI_ne hcond hint)
          ⟨(primesAboveEquivNormalizedFactors' hp v0).1,
            (primesAboveEquivNormalizedFactors' hp v0).2⟩ : Polynomial (ℤ ⧸ I)) =
          normalize g := by
        have hm := ((KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
          hI_max hI_ne hcond hint)
          ⟨(primesAboveEquivNormalizedFactors' hp v0).1,
            (primesAboveEquivNormalizedFactors' hp v0).2⟩).2
        have hm' : ((KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
            hI_max hI_ne hcond hint)
            ⟨(primesAboveEquivNormalizedFactors' hp v0).1,
              (primesAboveEquivNormalizedFactors' hp v0).2⟩ : Polynomial (ℤ ⧸ I)) ∈
            ({normalize g} : Multiset (Polynomial (ℤ ⧸ I))) := hnf ▸ hm
        exact Multiset.mem_singleton.mp hm'
      rw [hq_eq, hg_eq] at hem
      have hem1 : emultiplicity (normalize g) g = 1 := by
        have h1 : (normalize g) ^ 1 ∣ g := by rw [pow_one]; exact normalize_dvd_iff.mpr dvd_rfl
        have h2 : ¬ (normalize g) ^ 2 ∣ g := by
          intro h2
          have hg_dvd : g * g ∣ g := by
            rw [sq] at h2
            exact (Associated.mul_mul (normalize_associated g) (normalize_associated g)).dvd_iff_dvd_left.mp h2
          obtain ⟨c, hc⟩ := hg_dvd
          have hc_eq : g * c = 1 := mul_left_cancel₀ hirr_g.ne_zero (by rw [← mul_assoc, ← hc, mul_one])
          exact hirr_g.not_isUnit (isUnit_iff_exists_inv.mpr ⟨c, hc_eq⟩)
        exact emultiplicity_eq_of_dvd_of_not_dvd h1 h2
      rw [hem1] at hem
      exact Nat.cast_injective hem
    have hf2 : v0.1.asIdeal.inertiaDeg ℤ = 2 := by
      have huniv : (Finset.univ : Finset (PrimesAbove (ImagQuadField d) p)) = {v0} := by
        ext v; simp [hv0 v]
      rw [huniv, Finset.sum_singleton, he1, one_mul] at hsum_ef
      exact hsum_ef
    have huniv : (Finset.univ : Finset (PrimesAbove (ImagQuadField d) p)) = {v0} := by
      ext v; simp [hv0 v]
    rw [huniv, Finset.prod_singleton, habsNorm_v v0, hf2]
    have hpow : ((p ^ 2 : ℕ) : ℂ) ^ (-s) = ((p : ℂ) ^ (-s)) ^ 2 := by
      rw [Nat.cast_pow, ← Complex.ofReal_natCast]
      exact ofReal_pow_cpow (Nat.cast_nonneg p) 2 (-s)
    rw [hpow, ← mul_inv]
    congr 1
    ring
  · -- Case 3: Ramified
    rintro ⟨r, hg_sq⟩
    have hnorm_lin : normalize (Polynomial.X - Polynomial.C r) = Polynomial.X - Polynomial.C r :=
      (Polynomial.monic_X_sub_C r).normalize_eq_self
    have hirr_lin : Irreducible (Polynomial.X - Polynomial.C r) := Polynomial.irreducible_X_sub_C r
    have hnf : UniqueFactorizationMonoid.normalizedFactors
        (Polynomial.map (Ideal.Quotient.mk I) (minpoly ℤ (imagQuadIntGen d))) =
        Multiset.replicate 2 (Polynomial.X - Polynomial.C r) := by
      rw [hg_eq, hg_sq, UniqueFactorizationMonoid.normalizedFactors_pow,
        UniqueFactorizationMonoid.normalizedFactors_irreducible hirr_lin, hnorm_lin]
      rfl
    have hcard : Fintype.card (PrimesAbove (ImagQuadField d) p) = 1 := by
      let hset : ({q : Polynomial (ℤ ⧸ I) //
          q ∈ UniqueFactorizationMonoid.normalizedFactors
            (Polynomial.map (Ideal.Quotient.mk I) (minpoly ℤ (imagQuadIntGen d)))}) ≃
          ({Polynomial.X - Polynomial.C r} : Finset (Polynomial (ℤ ⧸ I))) :=
        { toFun := fun x => ⟨x.1, by
            have hx : x.1 ∈ Multiset.replicate 2 (Polynomial.X - Polynomial.C r) := hnf ▸ x.2
            exact Finset.mem_singleton.mpr (Multiset.mem_replicate.mp hx).2⟩
          invFun := fun x => ⟨x.1, by
            have hx : x.1 ∈ Multiset.replicate 2 (Polynomial.X - Polynomial.C r) :=
              Multiset.mem_replicate.mpr ⟨by norm_num, Finset.mem_singleton.mp x.2⟩
            exact hnf.symm ▸ hx⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr (eKD.trans hset), Fintype.card_coe, Finset.card_singleton]
    obtain ⟨v0, hv0⟩ := Fintype.card_eq_one_iff.mp hcard
    have he2 : v0.1.asIdeal.ramificationIdx ℤ = 2 := by
      have hem := KummerDedekind.emultiplicity_factors_map_eq_emultiplicity hI_max hI_ne hcond hint
        (primesAboveEquivNormalizedFactors' hp v0).2
      have hLHS : emultiplicity ((primesAboveEquivNormalizedFactors' hp v0).1)
          (Ideal.map (algebraMap ℤ (𝓞 (ImagQuadField d))) I) = (v0.1.asIdeal.ramificationIdx ℤ : ℕ∞) :=
        emultiplicity_eq_ramificationIdx' hp v0
      rw [hLHS] at hem
      have hq_eq : ((KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
          hI_max hI_ne hcond hint)
          ⟨(primesAboveEquivNormalizedFactors' hp v0).1,
            (primesAboveEquivNormalizedFactors' hp v0).2⟩ : Polynomial (ℤ ⧸ I)) =
          Polynomial.X - Polynomial.C r := by
        have hm := ((KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
          hI_max hI_ne hcond hint)
          ⟨(primesAboveEquivNormalizedFactors' hp v0).1,
            (primesAboveEquivNormalizedFactors' hp v0).2⟩).2
        have hm' : ((KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
            hI_max hI_ne hcond hint)
            ⟨(primesAboveEquivNormalizedFactors' hp v0).1,
              (primesAboveEquivNormalizedFactors' hp v0).2⟩ : Polynomial (ℤ ⧸ I)) ∈
            Multiset.replicate 2 (Polynomial.X - Polynomial.C r) := hnf ▸ hm
        exact (Multiset.mem_replicate.mp hm').2
      rw [hq_eq, hg_eq, hg_sq] at hem
      have hem2 : emultiplicity (Polynomial.X - Polynomial.C r) ((Polynomial.X - Polynomial.C r) ^ 2) = 2 := by
        have h1 : (Polynomial.X - Polynomial.C r) ^ 2 ∣ (Polynomial.X - Polynomial.C r) ^ 2 := dvd_rfl
        have h2 : ¬ (Polynomial.X - Polynomial.C r) ^ 3 ∣ (Polynomial.X - Polynomial.C r) ^ 2 := by
          intro h3
          have hdeg := Polynomial.natDegree_le_of_dvd h3
            (pow_ne_zero 2 (Polynomial.monic_X_sub_C r).ne_zero)
          rw [Polynomial.natDegree_pow, Polynomial.natDegree_pow,
            Polynomial.natDegree_X_sub_C] at hdeg
          norm_num at hdeg
        exact emultiplicity_eq_of_dvd_of_not_dvd h1 h2
      rw [hem2] at hem
      exact Nat.cast_injective hem
    have hf1 : v0.1.asIdeal.inertiaDeg ℤ = 1 := by
      have huniv : (Finset.univ : Finset (PrimesAbove (ImagQuadField d) p)) = {v0} := by
        ext v; simp [hv0 v]
      rw [huniv, Finset.sum_singleton, he2] at hsum_ef
      omega
    have huniv : (Finset.univ : Finset (PrimesAbove (ImagQuadField d) p)) = {v0} := by
      ext v; simp [hv0 v]
    rw [huniv, Finset.prod_singleton, habsNorm_v v0, hf1, pow_one, zero_mul, sub_zero, inv_one,
      mul_one]

/-- **Exact Local Imaginary Quadratic Euler Factor Identity at EVERY Rational Prime `p`**
(split, inert, and ramified, including `p = 2`!). -/
theorem imagQuad_local_eulerFactor_eq {d : ℕ} (hd : 0 < d) (hsf : Squarefree d)
    {p : ℕ} [Fact p.Prime] [Fintype (PrimesAbove (ImagQuadField d) p)] (s : ℂ) :
    ∏ v : PrimesAbove (ImagQuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
      (1 - (p : ℂ) ^ (-s))⁻¹ *
        (1 - imagQuadChar d (p : ZMod (imagQuadDiscNat d)) * (p : ℂ) ^ (-s))⁻¹ := by
  have hp : p.Prime := Fact.out
  have hm : imagQuadParam d = d := imagQuadParam_eq_self hd
  set I : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hI_max : I.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have : I.IsMaximal := hI_max
  let : Field (ℤ ⧸ I) := Ideal.Quotient.field I
  let eQ : ℤ ⧸ I ≃+* ZMod p := Int.quotientSpanNatEquivZMod p
  let ePoly : Polynomial (ℤ ⧸ I) ≃+* Polynomial (ZMod p) := Polynomial.mapEquiv eQ
  set g : Polynomial (ℤ ⧸ I) := Polynomial.map (Ideal.Quotient.mk I) (imagQuadMinPolyInt d)
  set gZ : Polynomial (ZMod p) := Polynomial.map (Int.castRingHom (ZMod p)) (imagQuadMinPolyInt d)
  have hePoly_g : ePoly g = gZ := by
    dsimp only [ePoly, g, gZ]
    rw [Polynomial.mapEquiv_apply, Polynomial.map_map]
    congr 1
  obtain ⟨hSplit, hInert, hRam⟩ := imagQuad_local_eulerFactor_of_splitting hd hsf (p := p) s
  have hsplit_of : (∃ r₁ r₂ : ZMod p, r₁ ≠ r₂ ∧
      gZ = (Polynomial.X - Polynomial.C r₁) * (Polynomial.X - Polynomial.C r₂)) →
      ∏ v : PrimesAbove (ImagQuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
        (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (1 : ℂ) * (p : ℂ) ^ (-s))⁻¹ := by
    rintro ⟨r₁, r₂, hne, hfac⟩
    refine hSplit ⟨eQ.symm r₁, eQ.symm r₂, fun h => hne (eQ.symm.injective h), ?_⟩
    apply ePoly.injective
    rw [hePoly_g, hfac]
    simp [ePoly, Polynomial.mapEquiv_apply]
  have hinert_of : Irreducible gZ →
      ∏ v : PrimesAbove (ImagQuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
        (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (-1 : ℂ) * (p : ℂ) ^ (-s))⁻¹ := by
    intro hirr
    refine hInert ?_
    rw [← hePoly_g] at hirr
    refine ⟨fun hu => hirr.1 (hu.map ePoly), fun a b hab => ?_⟩
    change g = a * b at hab
    have hfac : ePoly g = ePoly a * ePoly b := by rw [hab, map_mul]
    rcases hirr.2 hfac with ha | hb
    · left; simpa using ha.map ePoly.symm
    · right; simpa using hb.map ePoly.symm
  have hram_of : (∃ r : ZMod p, gZ = (Polynomial.X - Polynomial.C r) ^ 2) →
      ∏ v : PrimesAbove (ImagQuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
        (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (0 : ℂ) * (p : ℂ) ^ (-s))⁻¹ := by
    rintro ⟨r, hsq⟩
    refine hRam ⟨eQ.symm r, ?_⟩
    apply ePoly.injective
    rw [hePoly_g, hsq]
    simp [ePoly, Polynomial.mapEquiv_apply]
  by_cases hp2 : p = 2
  · subst hp2
    rw [show ((2 : ℕ) : ZMod (imagQuadDiscNat d)) = (2 : ZMod (imagQuadDiscNat d)) from Nat.cast_ofNat,
      imagQuadChar_apply_two hd]
    by_cases hd3 : d % 4 = 3
    · rw [if_pos hd3]
      have hgZ_eq : gZ = Polynomial.X ^ 2 - Polynomial.X +
          Polynomial.C ((((d : ℤ) + 1) / 4 : ℤ) : ZMod 2) := by
        dsimp only [gZ]; unfold imagQuadMinPolyInt; dsimp only; rw [hm, if_pos hd3]
        simp [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow]
      have h8 : d % 8 = 7 ∨ d % 8 = 3 := by omega
      rcases h8 with hd8 | hd8
      · rw [if_pos hd8]
        have hc0 : ((((d : ℤ) + 1) / 4 : ℤ) : ZMod 2) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; omega
        refine hsplit_of ⟨0, 1, zero_ne_one, ?_⟩
        rw [hgZ_eq, hc0, map_zero, add_zero, sub_zero, map_one]
        ring
      · rw [if_neg (by omega)]
        have hc1 : ((((d : ℤ) + 1) / 4 : ℤ) : ZMod 2) = 1 := by
          have hsub : ((((d : ℤ) + 1) / 4 - 1 : ℤ) : ZMod 2) = 0 := by
            rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; omega
          push_cast at hsub; linear_combination hsub
        refine hinert_of (irreducible_of_natDegree_two_of_no_roots' ?_ ?_)
        · rw [← hePoly_g, Polynomial.mapEquiv_apply, Polynomial.natDegree_map_eq_of_injective eQ.injective]
          have hm' : (imagQuadMinPolyInt d).Monic := imagQuadMinPolyInt_monic d
          rw [hm'.natDegree_map, imagQuadMinPolyInt_natDegree d]
        · intro r
          rw [hgZ_eq, hc1]
          simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
            Polynomial.eval_X, Polynomial.eval_C]
          have hr01 : r = 0 ∨ r = 1 := by
            have hlt := r.val_lt
            have hval : r.val = 0 ∨ r.val = 1 := by omega
            rcases hval with h | h
            · left; rw [← ZMod.natCast_zmod_val r, h]; rfl
            · right; rw [← ZMod.natCast_zmod_val r, h]; rfl
          rcases hr01 with rfl | rfl
          · rw [zero_pow (by norm_num : 2 ≠ 0), sub_zero, zero_add]; exact one_ne_zero
          · rw [one_pow, sub_self, zero_add]; exact one_ne_zero
    · rw [if_neg hd3]
      have hgZ_eq : gZ = Polynomial.X ^ 2 + Polynomial.C (d : ZMod 2) := by
        dsimp only [gZ]; unfold imagQuadMinPolyInt; dsimp only; rw [hm, if_neg hd3]
        simp [Polynomial.map_add, Polynomial.map_pow]
      refine hram_of ⟨(d : ZMod 2), ?_⟩
      rw [hgZ_eq]
      have h2_zmod : (2 : ZMod 2) = 0 := by simpa using CharP.cast_eq_zero (ZMod 2) 2
      have h2 : (2 : Polynomial (ZMod 2)) = 0 := by
        rw [← map_ofNat Polynomial.C 2, h2_zmod, map_zero]
      have hd_sq : (d : ZMod 2) ^ 2 = (d : ZMod 2) := by
        generalize (d : ZMod 2) = x
        fin_cases x
        · exact zero_pow (by norm_num)
        · exact one_pow 2
      calc Polynomial.X ^ 2 + Polynomial.C (d : ZMod 2)
          = Polynomial.X ^ 2 - 2 * Polynomial.X * Polynomial.C (d : ZMod 2) +
              Polynomial.C ((d : ZMod 2) ^ 2) := by
            rw [h2, zero_mul, zero_mul, sub_zero, hd_sq]
        _ = (Polynomial.X - Polynomial.C (d : ZMod 2)) ^ 2 := by rw [map_pow]; ring
  · rw [imagQuadChar_apply_prime_odd hd hsf hp2]
    have h2_ne : (2 : ZMod p) ≠ 0 := by
      intro h0
      have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp h0
      exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hp.two_le)
    set c : ZMod p := if d % 4 = 3 then (2 : ZMod p)⁻¹ else 0
    set Δ : ZMod p := if d % 4 = 3 then -(d : ZMod p) * ((2 : ZMod p)⁻¹) ^ 2 else -(d : ZMod p)
    have hgZ_sq : gZ = (Polynomial.X - Polynomial.C c) ^ 2 - Polynomial.C Δ := by
      dsimp only [gZ, c, Δ]
      unfold imagQuadMinPolyInt
      dsimp only
      rw [hm]
      split_ifs with hd3
      · rw [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
          Polynomial.map_C]
        have hd4 : ((d : ℤ) + 1) / 4 * 4 = (d : ℤ) + 1 := by omega
        have hq4 : Int.castRingHom (ZMod p) (((d : ℤ) + 1) / 4) =
            ((d : ZMod p) + 1) * ((2 : ZMod p)⁻¹) ^ 2 := by
          have hz : ((((d : ℤ) + 1) / 4 : ℤ) : ZMod p) * 4 = (d : ZMod p) + 1 := by
            have := congrArg (Int.cast (R := ZMod p)) hd4
            simpa using this
          have h4inv : (4 : ZMod p) * ((2 : ZMod p)⁻¹) ^ 2 = 1 := by
            rw [show (4 : ZMod p) = 2 ^ 2 by ring, ← mul_pow, mul_inv_cancel₀ h2_ne, one_pow]
          change ((((d : ℤ) + 1) / 4 : ℤ) : ZMod p) = _
          calc ((((d : ℤ) + 1) / 4 : ℤ) : ZMod p)
              = ((((d : ℤ) + 1) / 4 : ℤ) : ZMod p) * (4 * ((2 : ZMod p)⁻¹) ^ 2) := by
                rw [h4inv, mul_one]
            _ = ((((d : ℤ) + 1) / 4 : ℤ) : ZMod p) * 4 * ((2 : ZMod p)⁻¹) ^ 2 := by ring
            _ = ((d : ZMod p) + 1) * ((2 : ZMod p)⁻¹) ^ 2 := by rw [hz]
        have h2c : (2 : Polynomial (ZMod p)) * Polynomial.C (2 : ZMod p)⁻¹ = 1 := by
          rw [(map_ofNat Polynomial.C 2).symm, ← map_mul, mul_inv_cancel₀ h2_ne, map_one]
        rw [hq4]
        calc Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((d : ZMod p) + 1) * (2 : ZMod p)⁻¹ ^ 2)
            = Polynomial.X ^ 2 - (2 * Polynomial.C (2 : ZMod p)⁻¹) * Polynomial.X +
                Polynomial.C (((d : ZMod p) + 1) * (2 : ZMod p)⁻¹ ^ 2) := by rw [h2c, one_mul]
          _ = (Polynomial.X - Polynomial.C (2 : ZMod p)⁻¹) ^ 2 -
                Polynomial.C (-(d : ZMod p) * (2 : ZMod p)⁻¹ ^ 2) := by
              rw [show Polynomial.C (((d : ZMod p) + 1) * (2 : ZMod p)⁻¹ ^ 2) =
                (Polynomial.C (2 : ZMod p)⁻¹) ^ 2 -
                  Polynomial.C (-(d : ZMod p) * (2 : ZMod p)⁻¹ ^ 2) by
                rw [← map_pow, ← map_sub]; congr 1; ring]
              ring
      · simp [Polynomial.map_add, Polynomial.map_pow, sub_eq_add_neg]
    have hΔ_zero : Δ = 0 ↔ (-(d : ℤ) : ZMod p) = 0 := by
      dsimp only [Δ]; split_ifs
      · simp [h2_ne]
      · simp
    have hΔ_sq : IsSquare Δ ↔ IsSquare (-(d : ℤ) : ZMod p) := by
      dsimp only [Δ]; split_ifs
      · constructor
        · rintro ⟨t, ht⟩
          refine ⟨2 * t, ?_⟩
          have : -(d : ZMod p) * ((2 : ZMod p)⁻¹) ^ 2 * 4 = (2 * t) * (2 * t) := by
            rw [ht]; ring
          have h4inv : ((2 : ZMod p)⁻¹) ^ 2 * 4 = 1 := by
            rw [show (4 : ZMod p) = 2 ^ 2 by ring, mul_comm, ← mul_pow, mul_inv_cancel₀ h2_ne, one_pow]
          rw [mul_assoc, h4inv, mul_one] at this
          simpa using this
        · rintro ⟨t, ht⟩
          refine ⟨t * (2 : ZMod p)⁻¹, ?_⟩
          have ht' : -(d : ZMod p) = t * t := by simpa using ht
          rw [ht']; ring
      · simp
    by_cases hd0 : (-(d : ℤ) : ZMod p) = 0
    · have hleg0 : legendreSym p (-(d : ℤ)) = 0 :=
        (legendreSym.eq_zero_iff p (-(d : ℤ))).mpr (by simpa using hd0)
      rw [hleg0, Int.cast_zero]
      refine hram_of ⟨c, ?_⟩
      rw [hgZ_sq, hΔ_zero.mpr hd0, map_zero, sub_zero]
    · by_cases hsq_d : IsSquare (-(d : ℤ) : ZMod p)
      · have hleg1 : legendreSym p (-(d : ℤ)) = 1 :=
          (legendreSym.eq_one_iff p (by simpa using hd0)).mpr (by simpa using hsq_d)
        rw [hleg1, Int.cast_one]
        obtain ⟨t, ht⟩ := hΔ_sq.mpr hsq_d
        have ht_ne : t ≠ 0 := fun h0 => hd0 (hΔ_zero.mp (by rw [ht, h0, zero_mul]))
        have hne_r : c + t ≠ c - t := by
          intro h
          have h2t : (2 : ZMod p) * t = 0 := by linear_combination h
          exact (mul_ne_zero h2_ne ht_ne) h2t
        refine hsplit_of ⟨c + t, c - t, hne_r, ?_⟩
        rw [hgZ_sq, ht, map_mul]
        simp only [map_add, map_sub]
        ring
      · have hlegm1 : legendreSym p (-(d : ℤ)) = -1 :=
          (legendreSym.eq_neg_one_iff p).mpr (by simpa using hsq_d)
        rw [hlegm1, Int.cast_neg, Int.cast_one]
        have hnsq_Δ : ¬ IsSquare Δ := fun h => hsq_d (hΔ_sq.mp h)
        refine hinert_of (irreducible_of_natDegree_two_of_no_roots' ?_ ?_)
        · rw [← hePoly_g, Polynomial.mapEquiv_apply, Polynomial.natDegree_map_eq_of_injective eQ.injective]
          have hm' : (imagQuadMinPolyInt d).Monic := imagQuadMinPolyInt_monic d
          rw [hm'.natDegree_map, imagQuadMinPolyInt_natDegree d]
        · intro r hr
          rw [hgZ_sq] at hr
          simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hr
          exact hnsq_Δ ⟨r - c, by rw [← sq]; linear_combination -hr⟩

/-- **UNCONDITIONAL EXACT IMAGINARY QUADRATIC DEDEKIND ZETA FACTORIZATION (`ζ_{ℚ(√(-d))}(s) = ζ(s) · L(s, χ_{-|D|})`)**:
for EVERY squarefree `d > 0` and EVERY `s : ℂ` with `1 < s.re`:
`Stage7DedekindZeta.dedekindZeta (ImagQuadField d) s = riemannZeta s * DirichletCharacter.LFunction (imagQuadChar d) s`! -/
theorem dedekindZeta_imagQuad_eq_zeta_mul_L {d : ℕ} (hd : 0 < d) (hsf : Squarefree d)
    {s : ℂ} (hs : 1 < s.re) :
    Stage7DedekindZeta.dedekindZeta (ImagQuadField d) s =
      riemannZeta s * DirichletCharacter.LFunction (imagQuadChar d) s := by
  have hzeta := riemannZeta_eulerProduct_hasProd hs
  have hL : HasProd (fun p : Nat.Primes =>
      (1 - imagQuadChar d ((p : ℕ) : ZMod (imagQuadDiscNat d)) * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      (DirichletCharacter.LFunction (imagQuadChar d) s) := by
    rw [DirichletCharacter.LFunction_eq_LSeries (imagQuadChar d) hs]
    exact DirichletCharacter.LSeries_eulerProduct_hasProd (imagQuadChar d) hs
  have hmul : HasProd (fun p : Nat.Primes =>
      (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ *
        (1 - imagQuadChar d ((p : ℕ) : ZMod (imagQuadDiscNat d)) * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      (riemannZeta s * DirichletCharacter.LFunction (imagQuadChar d) s) :=
    hzeta.mul hL
  have hmult_v : Multipliable (fun v : HeightOneSpectrum (𝓞 (ImagQuadField d)) =>
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) :=
    (dedekindZeta_hasProd_eulerProduct (ImagQuadField d) hs).multipliable
  have hmult_sig : Multipliable (fun x : Σ p : Nat.Primes, PrimesAbove (ImagQuadField d) p =>
      (1 - (Ideal.absNorm x.2.1.asIdeal : ℂ) ^ (-s))⁻¹) :=
    (Equiv.multipliable_iff (heightOneEquivSigmaPrimesAbove (ImagQuadField d))).mp hmult_v
  have hfib : ∀ p : Nat.Primes,
      HasProd (fun v : PrimesAbove (ImagQuadField d) p =>
          (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹)
        ((1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ *
          (1 - imagQuadChar d ((p : ℕ) : ZMod (imagQuadDiscNat d)) * ((p : ℕ) : ℂ) ^ (-s))⁻¹) := by
    intro p
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    have : Finite (PrimesAbove (ImagQuadField d) p) := finite_primesAbove (ImagQuadField d) p.2
    classical
    let : Fintype (PrimesAbove (ImagQuadField d) p) := Fintype.ofFinite _
    rw [← imagQuad_local_eulerFactor_eq hd hsf (p := p) s]
    exact hasProd_fintype _
  have hsig : HasProd (fun x : Σ p : Nat.Primes, PrimesAbove (ImagQuadField d) p =>
      (1 - (Ideal.absNorm x.2.1.asIdeal : ℂ) ^ (-s))⁻¹)
      (riemannZeta s * DirichletCharacter.LFunction (imagQuadChar d) s) :=
    HasProd.sigma_of_hasProd hmul hfib hmult_sig
  have hprod_eq : HasProd (fun v : HeightOneSpectrum (𝓞 (ImagQuadField d)) =>
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)
      (riemannZeta s * DirichletCharacter.LFunction (imagQuadChar d) s) :=
    (Equiv.hasProd_iff (heightOneEquivSigmaPrimesAbove (ImagQuadField d))).mpr hsig
  exact (dedekindZeta_hasProd_eulerProduct (ImagQuadField d) hs).unique hprod_eq

/-- Exact complex right-half-plane residue of `ζ_{ℚ(√(-d))}(s)` at `s = 1`:
`lim_{s → 1, Re(s) > 1} (s - 1) * ζ_{ℚ(√(-d))}(s) = L(1, χ_{-|D|})`. -/
theorem dedekindZeta_imagQuad_residue_one {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) :
    Tendsto (fun s : ℂ => (s - 1) * Stage7DedekindZeta.dedekindZeta (ImagQuadField d) s)
      (𝓝[{z : ℂ | 1 < z.re}] (1 : ℂ))
      (nhds (DirichletCharacter.LFunction (imagQuadChar d) 1)) := by
  have hsub : {z : ℂ | 1 < z.re} ⊆ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    intro z hz h1
    rw [Set.mem_singleton_iff] at h1
    rw [Set.mem_ofPred_eq, h1, Complex.one_re] at hz
    exact lt_irrefl 1 hz
  have hEq : (fun s : ℂ => (s - 1) * Stage7DedekindZeta.dedekindZeta (ImagQuadField d) s)
      =ᶠ[𝓝[{z : ℂ | 1 < z.re}] 1]
      (fun s : ℂ => ((s - 1) * riemannZeta s) * DirichletCharacter.LFunction (imagQuadChar d) s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [dedekindZeta_imagQuad_eq_zeta_mul_L hd hsf hs, mul_assoc]
  rw [tendsto_congr' hEq]
  have hres : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s)
      (𝓝[{z : ℂ | 1 < z.re}] (1 : ℂ)) (nhds 1) :=
    riemannZeta_residue_one.mono_left (nhdsWithin_mono 1 hsub)
  have hL : Tendsto (fun s : ℂ => DirichletCharacter.LFunction (imagQuadChar d) s)
      (𝓝[{z : ℂ | 1 < z.re}] (1 : ℂ))
      (nhds (DirichletCharacter.LFunction (imagQuadChar d) 1)) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      ((DirichletCharacter.differentiable_LFunction (imagQuadChar_ne_one hd hsf)).continuous.tendsto 1)
  simpa only [one_mul] using hres.mul hL

/-- Real right-hand limit form `lim_{σ → 1⁺} (σ - 1) * (ζ_{ℚ(√(-d))}(σ)).re = (L(1, χ_{-|D|})).re`. -/
theorem dedekindZeta_imagQuad_residue_one_real {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) :
    Tendsto (fun σ : ℝ => (σ - 1) * (Stage7DedekindZeta.dedekindZeta (ImagQuadField d) (σ : ℂ)).re)
      (𝓝[>] (1 : ℝ))
      (nhds (DirichletCharacter.LFunction (imagQuadChar d) 1).re) := by
  have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[{z : ℂ | 1 < z.re}] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · exact tendsto_nhdsWithin_of_tendsto_nhds
        (by simpa using Complex.continuous_ofReal.continuousAt.tendsto (x := (1 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      simpa using hσ
  have hC := (dedekindZeta_imagQuad_residue_one hd hsf).comp hmap
  have hre := (Complex.continuous_re.continuousAt.tendsto).comp hC
  refine hre.congr fun σ => ?_
  change ((((σ : ℂ) - 1) * Stage7DedekindZeta.dedekindZeta (ImagQuadField d) (σ : ℂ))).re = _
  rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]

end ImaginaryDedekindZeta

/-! ## Section 4: Ideal-Class Bijection & 2D Lattice Disk Counting -/

section IdealClassLatticeCounting

/-- Nonzero integral ideals of `𝓞 (ImagQuadField d)` in a fixed ideal class `C`. -/
abbrev ClassIdeals (d : ℕ) (C : ClassGroup (𝓞 (ImagQuadField d))) : Type :=
  {I : {I : Ideal (𝓞 (ImagQuadField d)) // I ≠ ⊥} //
    ClassGroup.mk0 ⟨I.1, mem_nonZeroDivisors_of_ne_zero I.2⟩ = C}

/-- Number of nonzero integral ideals of `𝓞 (ImagQuadField d)` in class `C` of absolute norm `n`. -/
def classIdealCount (d : ℕ) (C : ClassGroup (𝓞 (ImagQuadField d))) (n : ℕ) : ℕ :=
  Nat.card {I : ClassIdeals d C // Ideal.absNorm I.1.1 = n}

/-- Cumulative count of ideals in class `C` with absolute norm `≤ N`. -/
def classIdealSum (d : ℕ) (C : ClassGroup (𝓞 (ImagQuadField d))) (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 1 N, classIdealCount d C n

lemma classIdealCount_zero (d : ℕ) (C : ClassGroup (𝓞 (ImagQuadField d))) :
    classIdealCount d C 0 = 0 := by
  unfold classIdealCount
  have : IsEmpty {I : ClassIdeals d C // Ideal.absNorm I.1.1 = 0} :=
    ⟨fun ⟨⟨⟨I, hI⟩, _⟩, h0⟩ => hI (Ideal.absNorm_eq_zero_iff.mp h0)⟩
  simp

lemma finite_classIdeals_absNorm_eq (d : ℕ) (C : ClassGroup (𝓞 (ImagQuadField d))) (n : ℕ) :
    Finite {I : ClassIdeals d C // Ideal.absNorm I.1.1 = n} := by
  have : Finite {I : Ideal (𝓞 (ImagQuadField d)) // Ideal.absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 (ImagQuadField d)) n).to_subtype
  refine Finite.of_injective
    (fun I : {I : ClassIdeals d C // Ideal.absNorm I.1.1 = n} =>
      (⟨I.1.1.1, I.2⟩ : {I : Ideal (𝓞 (ImagQuadField d)) // Ideal.absNorm I = n})) ?_
  intro I J hIJ
  exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun x => x.1) hIJ)))

/-- For `x : 𝓞 (ImagQuadField d)`, `(Ideal.absNorm (Ideal.span {x}) : ℝ) = (Algebra.norm ℚ (x : K) : ℝ)`. -/
theorem absNorm_span_singleton_imagQuad (d : ℕ) (x : 𝓞 (ImagQuadField d)) :
    (Ideal.absNorm (Ideal.span {x}) : ℝ) = (Algebra.norm ℚ (x : ImagQuadField d) : ℝ) := by
  rw [Ideal.absNorm_span_singleton]
  have hcoe : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ (x : ImagQuadField d) := by
    exact Algebra.coe_norm_int x
  have hnn_q : (0 : ℚ) ≤ ((Algebra.norm ℤ x : ℤ) : ℚ) := by
    rw [hcoe]; exact imagQuadField_norm_nonneg d _
  have hnn_z : (0 : ℤ) ≤ Algebra.norm ℤ x := by exact_mod_cast hnn_q
  have habs : ((Algebra.norm ℤ x).natAbs : ℤ) = Algebra.norm ℤ x := Int.natAbs_of_nonneg hnn_z
  have hq : (((Algebra.norm ℤ x).natAbs : ℕ) : ℚ) = Algebra.norm ℚ (x : ImagQuadField d) := by
    rw [← Int.cast_natCast, habs, hcoe]
  exact_mod_cast hq

/-- **Exact `w_K`-to-`1` Correspondence in Ideal Class `C` (Single Norm Level `n ≥ 1`)**:
for any integral ideal `A ∈ C⁻¹`,
`classIdealCount d C n * imagQuadUnitCard d = Nat.card {x : 𝓞 K // x ∈ A ∧ x ≠ 0 ∧ N(x) = n * N(A)}`! -/
theorem classIdealCount_mul_unitCard_eq {d : ℕ} (hd : 0 < d) (hsf : Squarefree d)
    (C : ClassGroup (𝓞 (ImagQuadField d)))
    (A : (Ideal (𝓞 (ImagQuadField d)))⁰) (hA : ClassGroup.mk0 A = C⁻¹)
    {n : ℕ} (_hn : 1 ≤ n) :
    classIdealCount d C n * imagQuadUnitCard d =
      Nat.card {x : 𝓞 (ImagQuadField d) //
        x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ x ≠ 0 ∧
          Ideal.absNorm (Ideal.span {x}) = n * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} := by
  classical
  have hA_ne : (A : Ideal (𝓞 (ImagQuadField d))) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp A.2
  have hA_norm_pos : 0 < Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) :=
    absNorm_pos_of_ne_bot hA_ne
  -- Choose a principal generator `g I` for `I * A` for every `I : ClassIdeals d C`.
  have hex_gen : ∀ I : ClassIdeals d C,
      ∃ g : 𝓞 (ImagQuadField d), I.1.1 * (A : Ideal (𝓞 (ImagQuadField d))) = Ideal.span {g} := by
    intro I
    let I0 : (Ideal (𝓞 (ImagQuadField d)))⁰ := ⟨I.1.1, mem_nonZeroDivisors_of_ne_zero I.1.2⟩
    have hmk : ClassGroup.mk0 (I0 * A) = 1 := by
      rw [map_mul, I.2, hA, mul_inv_cancel]
    have hpr : ((I0 * A : (Ideal (𝓞 (ImagQuadField d)))⁰) : Ideal (𝓞 (ImagQuadField d))).IsPrincipal :=
      (ClassGroup.mk0_eq_one_iff (I0 * A).2).mp hmk
    exact ⟨Submodule.IsPrincipal.generator _, (Submodule.IsPrincipal.span_singleton_generator _).symm⟩
  choose g hg using hex_gen
  have hg_ne : ∀ I : ClassIdeals d C, g I ≠ 0 := by
    intro I h0
    have hbot : I.1.1 * (A : Ideal (𝓞 (ImagQuadField d))) = ⊥ := by
      rw [hg I, h0, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero I.1.2 hA_ne hbot
  -- Define the bijection `({I : ClassIdeals d C // N(I) = n} × (𝓞 K)ˣ) ≃ {x ∈ A \ {0} // N(x) = n * N(A)}`.
  have hinv_ex : ∀ x : {x : 𝓞 (ImagQuadField d) //
      x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ x ≠ 0 ∧
        Ideal.absNorm (Ideal.span {x}) = n * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))},
      ∃ J : {I : ClassIdeals d C // Ideal.absNorm I.1.1 = n},
        J.1.1.1 * (A : Ideal (𝓞 (ImagQuadField d))) = Ideal.span {x.1} := by
    intro ⟨x, hxA, hx0, hxN⟩
    have hle : Ideal.span {x} ≤ (A : Ideal (𝓞 (ImagQuadField d))) :=
      (Ideal.span_singleton_le_iff_mem _).mpr hxA
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
    have hJA : J * (A : Ideal (𝓞 (ImagQuadField d))) = Ideal.span {x} := by rw [mul_comm, ← hJ]
    have hJne : J ≠ ⊥ := by
      intro hbot
      rw [hbot, Ideal.bot_mul] at hJA
      exact hx0 (Ideal.span_singleton_eq_bot.mp hJA.symm)
    have hJnorm : Ideal.absNorm J = n := by
      have hmul : Ideal.absNorm J * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) =
          n * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) := by
        rw [← map_mul, hJA, hxN]
      exact Nat.eq_of_mul_eq_mul_right hA_norm_pos hmul
    have hJclass : ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_of_ne_zero hJne⟩ = C := by
      let J0 : (Ideal (𝓞 (ImagQuadField d)))⁰ := ⟨J, mem_nonZeroDivisors_of_ne_zero hJne⟩
      have hmul1 : ClassGroup.mk0 J0 * ClassGroup.mk0 A = 1 := by
        rw [← map_mul]
        refine (ClassGroup.mk0_eq_one_iff (J0 * A).2).mpr ?_
        change (J * (A : Ideal (𝓞 (ImagQuadField d)))).IsPrincipal
        rw [hJA]
        exact ⟨⟨x, rfl⟩⟩
      rw [hA] at hmul1
      exact eq_of_mul_inv_eq_one hmul1
    exact ⟨⟨⟨⟨J, hJne⟩, hJclass⟩, hJnorm⟩, hJA⟩
  have hunit_ex : ∀ x : {x : 𝓞 (ImagQuadField d) //
      x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ x ≠ 0 ∧
        Ideal.absNorm (Ideal.span {x}) = n * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))},
      ∃ u : (𝓞 (ImagQuadField d))ˣ, g (hinv_ex x).choose.1 * (u : 𝓞 (ImagQuadField d)) = x.1 := by
    intro x
    have hsp : Ideal.span {g (hinv_ex x).choose.1} = Ideal.span {x.1} := by
      rw [← hg _, (hinv_ex x).choose_spec]
    exact Ideal.span_singleton_eq_span_singleton.mp hsp
  let toF : ({I : ClassIdeals d C // Ideal.absNorm I.1.1 = n} × (𝓞 (ImagQuadField d))ˣ) →
      {x : 𝓞 (ImagQuadField d) //
        x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ x ≠ 0 ∧
          Ideal.absNorm (Ideal.span {x}) = n * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} :=
    fun p =>
      let I := p.1.1
      let u := p.2
      ⟨g I * (u : 𝓞 (ImagQuadField d)), by
        refine ⟨?_, mul_ne_zero (hg_ne I) u.ne_zero, ?_⟩
        · have hmem : g I * (u : 𝓞 (ImagQuadField d)) ∈ Ideal.span {g I} :=
            Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
          rw [← hg I] at hmem
          exact Ideal.mul_le_right hmem
        · have hsp : Ideal.span {g I * (u : 𝓞 (ImagQuadField d))} = Ideal.span {g I} :=
            Ideal.span_singleton_mul_right_unit u.isUnit (g I)
          rw [hsp, ← hg I, map_mul, p.1.2]⟩
  let e : ({I : ClassIdeals d C // Ideal.absNorm I.1.1 = n} × (𝓞 (ImagQuadField d))ˣ) ≃
      {x : 𝓞 (ImagQuadField d) //
        x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ x ≠ 0 ∧
          Ideal.absNorm (Ideal.span {x}) = n * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} :=
    { toFun := toF
      invFun := fun x => ((hinv_ex x).choose, (hunit_ex x).choose)
      left_inv := fun ⟨⟨I, hI⟩, u⟩ => by
        dsimp only
        set x := toF (⟨I, hI⟩, u)
        have hx_val : x.1 = g I * (u : 𝓞 (ImagQuadField d)) := rfl
        have hI_eq_J : (hinv_ex x).choose = ⟨I, hI⟩ := by
          apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
          have hmul : (hinv_ex x).choose.1.1.1 * (A : Ideal (𝓞 (ImagQuadField d))) =
              I.1.1 * (A : Ideal (𝓞 (ImagQuadField d))) := by
            rw [(hinv_ex x).choose_spec, hx_val, hg I]
            exact Ideal.span_singleton_mul_right_unit u.isUnit (g I)
          exact mul_right_cancel₀ hA_ne hmul
        refine Prod.ext hI_eq_J ?_
        have hJ1 : (hinv_ex x).choose.1 = I := congrArg Subtype.val hI_eq_J
        have hspec : g I * ((hunit_ex x).choose : 𝓞 (ImagQuadField d)) =
            g I * (u : 𝓞 (ImagQuadField d)) := by
          conv_lhs => rw [← hJ1]
          exact (hunit_ex x).choose_spec
        apply Units.ext
        exact mul_left_cancel₀ (hg_ne I) hspec
      right_inv := fun x => Subtype.ext (hunit_ex x).choose_spec }
  rw [← imagQuadUnitCard_eq hd hsf, classIdealCount, ← Nat.card_prod]
  exact Nat.card_congr e

/-- Every set `{x : 𝓞 (ImagQuadField d) // Ideal.absNorm (Ideal.span {x}) ≤ M}` is finite. -/
theorem finite_ringOfIntegers_absNorm_le {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) (M : ℕ) :
    Finite {x : 𝓞 (ImagQuadField d) // Ideal.absNorm (Ideal.span {x}) ≤ M} := by
  let B : ℤ := 2 * (M : ℤ) + 1
  let box : Finset (ℤ × ℤ) := Finset.Icc (-B) B ×ˢ Finset.Icc (-B) B
  let b := imagQuadIntBasis hd hsf
  have hb0 : b 0 = 1 := by simp [b, imagQuadIntBasis]
  have hb1 : b 1 = imagQuadIntGen d := by simp [b, imagQuadIntBasis]
  have hmk : ∀ x : 𝓞 (ImagQuadField d), mkIntElem d (b.repr x 0, b.repr x 1) = x := by
    intro x
    have hsum := b.sum_repr x
    rw [Fin.sum_univ_two, hb0, hb1, zsmul_eq_mul, zsmul_eq_mul, mul_one] at hsum
    exact hsum
  have hmem : ∀ x : {x : 𝓞 (ImagQuadField d) // Ideal.absNorm (Ideal.span {x}) ≤ M},
      (b.repr x.1 0, b.repr x.1 1) ∈ box := by
    intro ⟨x, hx⟩
    set u : ℤ := b.repr x 0
    set v : ℤ := b.repr x 1
    have hnorm_le_q : Algebra.norm ℚ (x : ImagQuadField d) ≤ (M : ℚ) := by
      have h1 : (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hx
      rw [absNorm_span_singleton_imagQuad] at h1
      exact_mod_cast h1
    rw [← hmk x, mkIntElem_norm_eq hd] at hnorm_le_q
    have hd1 : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    have hbd : -B ≤ u ∧ u ≤ B ∧ -B ≤ v ∧ v ≤ B := by
      split_ifs at hnorm_le_q with h3
      · have hq : (((2 * u + v) ^ 2 + (d : ℤ) * v ^ 2 : ℤ) : ℚ) ≤ ((4 * (M : ℤ) : ℤ) : ℚ) := by
          push_cast at hnorm_le_q ⊢; linarith
        have hz : (2 * u + v) ^ 2 + (d : ℤ) * v ^ 2 ≤ 4 * (M : ℤ) := Int.cast_le.mp hq
        have hv_sq : v ^ 2 ≤ 4 * (M : ℤ) := by
          nlinarith [sq_nonneg (2 * u + v), sq_nonneg v]
        have hw_sq : (2 * u + v) ^ 2 ≤ 4 * (M : ℤ) := by
          nlinarith [sq_nonneg v]
        have hB_sq : 4 * (M : ℤ) ≤ B ^ 2 := by dsimp only [B]; nlinarith
        have hv_abs : -B ≤ v ∧ v ≤ B := by
          constructor <;> by_contra hc <;> push Not at hc <;> nlinarith [show (0 : ℤ) ≤ B by dsimp only [B]; omega]
        have hw_abs : -B ≤ 2 * u + v ∧ 2 * u + v ≤ B := by
          constructor <;> by_contra hc <;> push Not at hc <;> nlinarith [show (0 : ℤ) ≤ B by dsimp only [B]; omega]
        exact ⟨by omega, by omega, hv_abs.1, hv_abs.2⟩
      · have hq : ((u ^ 2 + (d : ℤ) * v ^ 2 : ℤ) : ℚ) ≤ ((M : ℤ) : ℚ) := by
          push_cast at hnorm_le_q ⊢; linarith
        have hz : u ^ 2 + (d : ℤ) * v ^ 2 ≤ (M : ℤ) := Int.cast_le.mp hq
        have hu_sq : u ^ 2 ≤ (M : ℤ) := by nlinarith [sq_nonneg v]
        have hv_sq : v ^ 2 ≤ (M : ℤ) := by nlinarith [sq_nonneg u, sq_nonneg v]
        have hB_sq : (M : ℤ) ≤ B ^ 2 := by dsimp only [B]; nlinarith
        have hu_abs : -B ≤ u ∧ u ≤ B := by
          constructor <;> by_contra hc <;> push Not at hc <;> nlinarith [show (0 : ℤ) ≤ B by dsimp only [B]; omega]
        have hv_abs : -B ≤ v ∧ v ≤ B := by
          constructor <;> by_contra hc <;> push Not at hc <;> nlinarith [show (0 : ℤ) ≤ B by dsimp only [B]; omega]
        exact ⟨hu_abs.1, hu_abs.2, hv_abs.1, hv_abs.2⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hbd.1, hbd.2.1⟩,
      Finset.mem_Icc.mpr ⟨hbd.2.2.1, hbd.2.2.2⟩⟩
  refine Finite.of_injective (fun x => (⟨(b.repr x.1 0, b.repr x.1 1), hmem x⟩ : box)) ?_
  intro x y hxy
  apply Subtype.ext
  rw [← hmk x.1, ← hmk y.1]
  have hp : (b.repr x.1 0, b.repr x.1 1) = (b.repr y.1 0, b.repr y.1 1) := congrArg Subtype.val hxy
  rw [hp]

/-- **Exact Cumulative `w_K`-to-`1` Correspondence (`N : ℕ`)**:
`classIdealSum d C N * imagQuadUnitCard d + 1 = Nat.card {x : 𝓞 K // x ∈ A ∧ Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm A}`! -/
theorem classIdealSum_mul_unitCard_add_one_eq {d : ℕ} (hd : 0 < d) (hsf : Squarefree d)
    (C : ClassGroup (𝓞 (ImagQuadField d)))
    (A : (Ideal (𝓞 (ImagQuadField d)))⁰) (hA : ClassGroup.mk0 A = C⁻¹) (N : ℕ) :
    classIdealSum d C N * imagQuadUnitCard d + 1 =
      Nat.card {x : 𝓞 (ImagQuadField d) //
        x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧
          Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} := by
  classical
  have hA_ne : (A : Ideal (𝓞 (ImagQuadField d))) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp A.2
  have hA_norm_pos : 0 < Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) :=
    absNorm_pos_of_ne_bot hA_ne
  have hfin_all : Finite {x : 𝓞 (ImagQuadField d) //
      x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧
        Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} := by
    have := finite_ringOfIntegers_absNorm_le hd hsf (N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))))
    exact Finite.of_injective (fun x => (⟨x.1, x.2.2⟩ :
      {x : 𝓞 (ImagQuadField d) // Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))}))
      (fun _ _ h => Subtype.ext (congrArg (fun y => y.1) h))
  have hfin_nz : Finite {x : 𝓞 (ImagQuadField d) //
      x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ x ≠ 0 ∧
        Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} :=
    Finite.of_injective (fun x => (⟨x.1, x.2.1, x.2.2.2⟩ :
      {x : 𝓞 (ImagQuadField d) // x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧
        Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))}))
      (fun _ _ h => Subtype.ext (congrArg (fun y => y.1) h))
  -- Step 1: sum over `n ∈ Icc 1 N` equals cardinality of nonzero `x ∈ A` with `N(span {x}) ≤ N * N(A)`
  have hnz_eq : classIdealSum d C N * imagQuadUnitCard d =
      Nat.card {x : 𝓞 (ImagQuadField d) //
        x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ x ≠ 0 ∧
          Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} := by
    unfold classIdealSum
    rw [Finset.sum_mul]
    have hterm : ∀ n ∈ Finset.Icc 1 N,
        classIdealCount d C n * imagQuadUnitCard d =
          Nat.card {x : 𝓞 (ImagQuadField d) //
            x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ x ≠ 0 ∧
              Ideal.absNorm (Ideal.span {x}) = n * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} :=
      fun n hn => classIdealCount_mul_unitCard_eq hd hsf C A hA (Finset.mem_Icc.mp hn).1
    rw [Finset.sum_congr rfl hterm]
    have hdvd_norm : ∀ x : 𝓞 (ImagQuadField d),
        x ∈ (A : Ideal (𝓞 (ImagQuadField d))) →
        Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) ∣ Ideal.absNorm (Ideal.span {x}) := by
      intro x hxA
      obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hxA)
      exact ⟨Ideal.absNorm J, by rw [hJ, map_mul]⟩
    let eSig : (Σ n : Finset.Icc 1 N, {x : 𝓞 (ImagQuadField d) //
        x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ x ≠ 0 ∧
          Ideal.absNorm (Ideal.span {x}) = n.1 * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))}) ≃
        {x : 𝓞 (ImagQuadField d) //
          x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ x ≠ 0 ∧
            Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} :=
      { toFun := fun p => ⟨p.2.1, p.2.2.1, p.2.2.2.1, by
          rw [p.2.2.2.2]
          exact Nat.mul_le_mul_right _ (Finset.mem_Icc.mp p.1.2).2⟩
        invFun := fun x =>
          let q := Ideal.absNorm (Ideal.span {x.1}) / Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))
          have hq_mul : q * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) =
              Ideal.absNorm (Ideal.span {x.1}) := by
            rw [mul_comm]; exact Nat.mul_div_cancel' (hdvd_norm x.1 x.2.1)
          have hx_norm_pos : 0 < Ideal.absNorm (Ideal.span {x.1}) :=
            absNorm_pos_of_ne_bot (mt Ideal.span_singleton_eq_bot.mp x.2.2.1)
          have hq1 : 1 ≤ q := Nat.pos_of_ne_zero fun hq0 => by
            rw [hq0, zero_mul] at hq_mul
            exact hx_norm_pos.ne' hq_mul.symm
          have hqN : q ≤ N := by
            have : q * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) ≤
                N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) := by
              rw [hq_mul]; exact x.2.2.2
            exact Nat.le_of_mul_le_mul_right this hA_norm_pos
          ⟨⟨q, Finset.mem_Icc.mpr ⟨hq1, hqN⟩⟩, ⟨x.1, x.2.1, x.2.2.1, hq_mul.symm⟩⟩
        left_inv := fun ⟨⟨n, hn⟩, ⟨x, hxA, hx0, hxN⟩⟩ => by
          dsimp only
          have hq : Ideal.absNorm (Ideal.span {x}) / Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) = n := by
            rw [hxN, Nat.mul_div_cancel _ hA_norm_pos]
          have hmk : ∀ (m₁ m₂ : Finset.Icc 1 N)
              (h1 : Ideal.absNorm (Ideal.span {x}) = m₁.1 * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))))
              (h2 : Ideal.absNorm (Ideal.span {x}) = m₂.1 * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))),
              m₁ = m₂ →
              (⟨m₁, ⟨x, hxA, hx0, h1⟩⟩ : Σ m : Finset.Icc 1 N, {y : 𝓞 (ImagQuadField d) //
                y ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ y ≠ 0 ∧
                  Ideal.absNorm (Ideal.span {y}) = m.1 * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))}) =
                ⟨m₂, ⟨x, hxA, hx0, h2⟩⟩ := by
            rintro _ _ _ _ rfl; rfl
          exact hmk _ _ (by dsimp only; rw [hq]; exact hxN) hxN (Subtype.ext hq)
        right_inv := fun ⟨_, _⟩ => rfl }
    have hfin_fib : ∀ n : Finset.Icc 1 N,
        Finite {x : 𝓞 (ImagQuadField d) //
          x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ x ≠ 0 ∧
            Ideal.absNorm (Ideal.span {x}) = n.1 * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} := by
      intro n
      have := finite_ringOfIntegers_absNorm_le hd hsf (n.1 * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))))
      exact Finite.of_injective (fun x => (⟨x.1, x.2.2.2.le⟩ :
        {x : 𝓞 (ImagQuadField d) // Ideal.absNorm (Ideal.span {x}) ≤ n.1 * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))}))
        (fun _ _ h => Subtype.ext (congrArg (fun y => y.1) h))
    let : ∀ n : Finset.Icc 1 N, Fintype {x : 𝓞 (ImagQuadField d) //
        x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ x ≠ 0 ∧
          Ideal.absNorm (Ideal.span {x}) = n.1 * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} :=
      fun n => Fintype.ofFinite _
    let : Fintype {x : 𝓞 (ImagQuadField d) //
        x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ x ≠ 0 ∧
          Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} :=
      Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, ← Fintype.card_congr eSig, Fintype.card_sigma,
      Finset.univ_eq_attach]
    rw [← Finset.sum_attach (Finset.Icc 1 N)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Nat.card_eq_fintype_card]
  -- Step 2: add `x = 0` via `Option` equivalence
  let eOpt : Option {x : 𝓞 (ImagQuadField d) //
      x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ x ≠ 0 ∧
        Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} ≃
      {x : 𝓞 (ImagQuadField d) //
        x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧
          Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} :=
    { toFun := fun o => match o with
        | none => ⟨0, (A : Ideal (𝓞 (ImagQuadField d))).zero_mem, by
            rw [Ideal.span_singleton_zero, Ideal.absNorm_bot]; exact Nat.zero_le _⟩
        | some x => ⟨x.1, x.2.1, x.2.2.2⟩
      invFun := fun x =>
        if h0 : x.1 = 0 then none else some ⟨x.1, x.2.1, h0, x.2.2⟩
      left_inv := fun o => by cases o with
        | none => simp
        | some x => simp [x.2.2.1]
      right_inv := fun x => by
        by_cases h0 : x.1 = 0
        · simp [h0, Subtype.ext_iff]
        · simp [h0] }
  let : Fintype {x : 𝓞 (ImagQuadField d) //
      x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ x ≠ 0 ∧
        Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} :=
    Fintype.ofFinite _
  let : Fintype {x : 𝓞 (ImagQuadField d) //
      x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧
        Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} :=
    Fintype.ofFinite _
  rw [hnz_eq, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← Fintype.card_congr eOpt,
    Fintype.card_option]

/-! ### 2D Euclidean Lattice Embedding & Fundamental-Domain Disk Tiling -/

/-- Canonical isometric embedding `ImagQuadField d → ℝ²`: `u + v √(-d) ↦ (u, √d · v)`. -/
def imagQuadEmbed (d : ℕ) (z : ImagQuadField d) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(z.re : ℝ), Real.sqrt (imagQuadParam d : ℝ) * (z.im : ℝ)]

lemma imagQuadEmbed_apply_zero (d : ℕ) (z : ImagQuadField d) :
    imagQuadEmbed d z 0 = (z.re : ℝ) := rfl

lemma imagQuadEmbed_apply_one (d : ℕ) (z : ImagQuadField d) :
    imagQuadEmbed d z 1 = Real.sqrt (imagQuadParam d : ℝ) * (z.im : ℝ) := rfl

lemma imagQuadEmbed_zero (d : ℕ) : imagQuadEmbed d 0 = 0 := by
  ext i; fin_cases i <;> simp [imagQuadEmbed]

lemma imagQuadEmbed_add (d : ℕ) (x y : ImagQuadField d) :
    imagQuadEmbed d (x + y) = imagQuadEmbed d x + imagQuadEmbed d y := by
  ext i; fin_cases i
  · simp [imagQuadEmbed]
  · simp [imagQuadEmbed, mul_add]

lemma imagQuadEmbed_sub (d : ℕ) (x y : ImagQuadField d) :
    imagQuadEmbed d (x - y) = imagQuadEmbed d x - imagQuadEmbed d y := by
  ext i; fin_cases i
  · simp [imagQuadEmbed]
  · simp [imagQuadEmbed, mul_sub]

lemma imagQuadEmbed_injective (d : ℕ) : Function.Injective (imagQuadEmbed d) := by
  intro x y hxy
  have h0 : (x.re : ℝ) = (y.re : ℝ) := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hxy
  have h1 : Real.sqrt (imagQuadParam d : ℝ) * (x.im : ℝ) =
      Real.sqrt (imagQuadParam d : ℝ) * (y.im : ℝ) :=
    congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hxy
  have hs : 0 < Real.sqrt (imagQuadParam d : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (imagQuadParam_pos d))
  have him : (x.im : ℝ) = (y.im : ℝ) := mul_left_cancel₀ hs.ne' h1
  ext
  · exact_mod_cast h0
  · exact_mod_cast him

/-- Exact norm-squared identity: `‖imagQuadEmbed d z‖ ^ 2 = (Algebra.norm ℚ z : ℝ)`. -/
theorem norm_sq_imagQuadEmbed (d : ℕ) (z : ImagQuadField d) :
    ‖imagQuadEmbed d z‖ ^ 2 = (Algebra.norm ℚ z : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, imagQuadEmbed_apply_zero, imagQuadEmbed_apply_one,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _), imagQuadField_norm_eq, Rat.cast_add, Rat.cast_pow,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]

theorem norm_sq_imagQuadEmbed_int (d : ℕ) (x : 𝓞 (ImagQuadField d)) :
    ‖imagQuadEmbed d (x : ImagQuadField d)‖ ^ 2 = (Ideal.absNorm (Ideal.span {x}) : ℝ) := by
  rw [norm_sq_imagQuadEmbed, absNorm_span_singleton_imagQuad]

/-- Explicit `ℝ`-linear equivalence sending the standard basis `e₀, e₁` of `ℝ²` to
`imagQuadEmbed d 1` and `imagQuadEmbed d (imagQuadGenVal d)`. -/
def imagQuadBasisEquiv (d : ℕ) : EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  let s : ℝ := Real.sqrt (imagQuadParam d : ℝ)
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (imagQuadParam_pos d))).ne'
  if imagQuadParam d % 4 = 3 then
    { toFun := fun u => WithLp.toLp 2 ![u 0 + (1 / 2 : ℝ) * u 1, (s / 2) * u 1]
      map_add' := fun u v => by ext i; fin_cases i <;> simp <;> ring
      map_smul' := fun c u => by ext i; fin_cases i <;> simp <;> ring
      invFun := fun y => WithLp.toLp 2 ![y 0 - y 1 / s, (2 / s) * y 1]
      left_inv := fun u => by
        ext i; fin_cases i
        · simp; field_simp [hs]; ring
        · simp; field_simp [hs]
      right_inv := fun y => by
        ext i; fin_cases i
        · simp; field_simp [hs]; ring
        · simp; field_simp [hs] }
  else
    { toFun := fun u => WithLp.toLp 2 ![u 0, s * u 1]
      map_add' := fun u v => by
        ext i; fin_cases i
        · simp
        · simp [mul_add]
      map_smul' := fun c u => by
        ext i; fin_cases i
        · simp
        · simp; ring
      invFun := fun y => WithLp.toLp 2 ![y 0, y 1 / s]
      left_inv := fun u => by
        ext i; fin_cases i
        · simp
        · simp; field_simp [hs]
      right_inv := fun y => by
        ext i; fin_cases i
        · simp
        · simp; field_simp [hs] }

/-- `imagQuadBasisEquiv d` maps integer pairs `(a, b)` to `imagQuadEmbed d (mkIntElem d (a, b))`. -/
lemma imagQuadBasisEquiv_int (d : ℕ) (a b : ℤ) :
    imagQuadBasisEquiv d (WithLp.toLp 2 ![(a : ℝ), (b : ℝ)]) =
      imagQuadEmbed d ((mkIntElem d (a, b) : 𝓞 (ImagQuadField d)) : ImagQuadField d) := by
  unfold imagQuadBasisEquiv imagQuadEmbed mkIntElem
  dsimp only
  change _ = WithLp.toLp 2
    ![(((a : ImagQuadField d) + (b : ImagQuadField d) * imagQuadGenVal d).re : ℝ),
      Real.sqrt (imagQuadParam d : ℝ) *
        (((a : ImagQuadField d) + (b : ImagQuadField d) * imagQuadGenVal d).im : ℝ)]
  unfold imagQuadGenVal
  split_ifs with h3
  · ext i; fin_cases i
    · change (a : ℝ) + (1 / 2 : ℝ) * (b : ℝ) = _
      simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]
      push_cast; ring
    · change (Real.sqrt (imagQuadParam d : ℝ) / 2) * (b : ℝ) = _
      simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, zero_mul, add_zero, zero_add]
      push_cast; ring
  · ext i; fin_cases i
    · change (a : ℝ) = _
      simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, mul_zero, zero_mul, add_zero]
      push_cast; rfl
    · change Real.sqrt (imagQuadParam d : ℝ) * (b : ℝ) = _
      simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, mul_one, zero_mul, add_zero, zero_add]
      push_cast; ring

/-- Exact determinant of `imagQuadBasisEquiv d`: `√(imagQuadDiscNat d) / 2`. -/
lemma det_imagQuadBasisEquiv (d : ℕ) :
    (imagQuadBasisEquiv d : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)).det =
      Real.sqrt (imagQuadDiscNat d : ℝ) / 2 := by
  set b0 := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  rw [← LinearMap.det_toMatrix b0, Matrix.det_fin_two]
  have hb0_0 : b0 0 = WithLp.toLp 2 ![(1 : ℝ), 0] := by
    ext i; fin_cases i <;> simp [b0, EuclideanSpace.basisFun_apply]
  have hb0_1 : b0 1 = WithLp.toLp 2 ![(0 : ℝ), 1] := by
    ext i; fin_cases i <;> simp [b0, EuclideanSpace.basisFun_apply]
  have hmat : ∀ i j : Fin 2,
      LinearMap.toMatrix b0 b0 (imagQuadBasisEquiv d : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) i j =
        (imagQuadBasisEquiv d (b0 j)) i := fun i j => by
    rw [LinearMap.toMatrix_apply]
    change (EuclideanSpace.basisFun (Fin 2) ℝ).repr (imagQuadBasisEquiv d (b0 j)) i = _
    rw [EuclideanSpace.basisFun_repr]
  rw [hmat 0 0, hmat 1 1, hmat 0 1, hmat 1 0, hb0_0, hb0_1]
  unfold imagQuadBasisEquiv imagQuadDiscNat
  dsimp only
  split_ifs with h3
  · simp
  · simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, sub_zero, one_mul,
      Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show Real.sqrt (4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    ring

/-- Unit half-open square `[0, 1) × [0, 1)` in `EuclideanSpace ℝ (Fin 2)`. -/
private def unitSquare2 : Set (EuclideanSpace ℝ (Fin 2)) :=
  WithLp.ofLp ⁻¹' Set.univ.pi (fun _ : Fin 2 => Set.Ico (0 : ℝ) 1)

private lemma measurableSet_unitSquare2 : MeasurableSet unitSquare2 := by
  unfold unitSquare2
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Ico).preimage
    (PiLp.volume_preserving_ofLp (Fin 2)).measurable

private lemma volume_unitSquare2 : volume unitSquare2 = 1 := by
  unfold unitSquare2
  rw [(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet,
    MeasureTheory.volume_pi_pi]
  refine Finset.prod_eq_one fun _ _ => ?_
  rw [Real.volume_Ico, sub_zero, ENNReal.ofReal_one]

/-- Fundamental domain `F_O` for the embedded ring of integers `imagQuadEmbed d '' 𝓞 K` in `ℝ²`. -/
private def intFundDomain (d : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  imagQuadBasisEquiv d '' unitSquare2

private lemma intFundDomain_eq_preimage (d : ℕ) :
    intFundDomain d = (imagQuadBasisEquiv d).symm ⁻¹' unitSquare2 := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [Set.mem_preimage] using hu
  · intro hx
    exact ⟨(imagQuadBasisEquiv d).symm x, hx, LinearEquiv.apply_symm_apply _ _⟩

private lemma measurableSet_intFundDomain (d : ℕ) : MeasurableSet (intFundDomain d) := by
  rw [intFundDomain_eq_preimage]
  exact measurableSet_unitSquare2.preimage
    (imagQuadBasisEquiv d).symm.toContinuousLinearMap.continuous.measurable

private lemma volume_intFundDomain (d : ℕ) :
    volume (intFundDomain d) = ENNReal.ofReal (Real.sqrt (imagQuadDiscNat d : ℝ) / 2) := by
  change volume ((imagQuadBasisEquiv d : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) '' unitSquare2) = _
  rw [MeasureTheory.Measure.addHaar_image_linearMap volume
    (imagQuadBasisEquiv d : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) unitSquare2,
    det_imagQuadBasisEquiv, volume_unitSquare2, mul_one,
    abs_of_nonneg (by positivity)]

private lemma intFundDomain_tiling {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) :
    (∀ x : EuclideanSpace ℝ (Fin 2), ∃ v : 𝓞 (ImagQuadField d),
      x ∈ imagQuadEmbed d (v : ImagQuadField d) +ᵥ intFundDomain d) ∧
    (∀ v₁ v₂ : 𝓞 (ImagQuadField d),
      (∃ x, x ∈ imagQuadEmbed d (v₁ : ImagQuadField d) +ᵥ intFundDomain d ∧
            x ∈ imagQuadEmbed d (v₂ : ImagQuadField d) +ᵥ intFundDomain d) → v₁ = v₂) := by
  let b := imagQuadIntBasis hd hsf
  have hb0 : b 0 = 1 := by simp [b, imagQuadIntBasis]
  have hb1 : b 1 = imagQuadIntGen d := by simp [b, imagQuadIntBasis]
  have hmk : ∀ v : 𝓞 (ImagQuadField d), mkIntElem d (b.repr v 0, b.repr v 1) = v := by
    intro v
    have hsum := b.sum_repr v
    rw [Fin.sum_univ_two, hb0, hb1, zsmul_eq_mul, zsmul_eq_mul, mul_one] at hsum
    exact hsum
  constructor
  · intro x
    set w := (imagQuadBasisEquiv d).symm x
    let a : ℤ := ⌊w 0⌋
    let b' : ℤ := ⌊w 1⌋
    refine ⟨mkIntElem d (a, b'), ?_⟩
    rw [Set.mem_vadd_set]
    refine ⟨x - imagQuadEmbed d ((mkIntElem d (a, b') : 𝓞 (ImagQuadField d)) : ImagQuadField d),
      ?_, by simp [vadd_eq_add]⟩
    rw [intFundDomain_eq_preimage, Set.mem_preimage, map_sub,
      ← imagQuadBasisEquiv_int d a b', LinearEquiv.symm_apply_apply]
    simp only [unitSquare2, Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Ico,
      forall_true_left]
    intro i; fin_cases i
    · change 0 ≤ w 0 - (a : ℝ) ∧ w 0 - (a : ℝ) < 1
      exact ⟨sub_nonneg.mpr (Int.floor_le (w 0)), sub_lt_iff_lt_add'.mpr (Int.lt_floor_add_one (w 0))⟩
    · change 0 ≤ w 1 - (b' : ℝ) ∧ w 1 - (b' : ℝ) < 1
      exact ⟨sub_nonneg.mpr (Int.floor_le (w 1)), sub_lt_iff_lt_add'.mpr (Int.lt_floor_add_one (w 1))⟩
  · intro v₁ v₂ ⟨x, hx₁, hx₂⟩
    rw [Set.mem_vadd_set] at hx₁ hx₂
    rcases hx₁ with ⟨y₁, hy₁, hxy₁⟩
    rcases hx₂ with ⟨y₂, hy₂, hxy₂⟩
    rw [intFundDomain_eq_preimage, Set.mem_preimage] at hy₁ hy₂
    have heq : (imagQuadBasisEquiv d).symm (imagQuadEmbed d (v₁ : ImagQuadField d)) +
        (imagQuadBasisEquiv d).symm y₁ =
        (imagQuadBasisEquiv d).symm (imagQuadEmbed d (v₂ : ImagQuadField d)) +
        (imagQuadBasisEquiv d).symm y₂ := by
      rw [← map_add, ← map_add]
      congr 1
      simpa [vadd_eq_add] using hxy₁.trans hxy₂.symm
    have hinv_v : ∀ v : 𝓞 (ImagQuadField d),
        (imagQuadBasisEquiv d).symm (imagQuadEmbed d (v : ImagQuadField d)) =
          WithLp.toLp 2 ![(b.repr v 0 : ℝ), (b.repr v 1 : ℝ)] := fun v => by
      conv_lhs => rw [← hmk v]
      rw [← imagQuadBasisEquiv_int d (b.repr v 0) (b.repr v 1), LinearEquiv.symm_apply_apply]
    rw [hinv_v v₁, hinv_v v₂] at heq
    have hcoord : ∀ i : Fin 2, b.repr v₁ i = b.repr v₂ i := by
      intro i
      have hi := congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u i) heq
      have h1 : 0 ≤ (imagQuadBasisEquiv d).symm y₁ i ∧ (imagQuadBasisEquiv d).symm y₁ i < 1 := by
        simpa [unitSquare2] using hy₁ i
      have h2 : 0 ≤ (imagQuadBasisEquiv d).symm y₂ i ∧ (imagQuadBasisEquiv d).symm y₂ i < 1 := by
        simpa [unitSquare2] using hy₂ i
      have hci : (b.repr v₁ i : ℝ) + (imagQuadBasisEquiv d).symm y₁ i =
          (b.repr v₂ i : ℝ) + (imagQuadBasisEquiv d).symm y₂ i := by
        fin_cases i <;> simpa using hi
      have hlt1 : (b.repr v₁ i : ℝ) < (b.repr v₂ i : ℝ) + 1 := by linarith
      have hlt2 : (b.repr v₂ i : ℝ) < (b.repr v₁ i : ℝ) + 1 := by linarith
      have hz1 : b.repr v₁ i < b.repr v₂ i + 1 := by exact_mod_cast hlt1
      have hz2 : b.repr v₂ i < b.repr v₁ i + 1 := by exact_mod_cast hlt2
      omega
    rw [← hmk v₁, ← hmk v₂, hcoord 0, hcoord 1]

/-- **2D Lattice Disk Counting Asymptotic for Any Ideal Class `C` of `𝓞 (ImagQuadField d)`**:
there exists `M > 0` such that for EVERY `t ≥ 1`:
`|(classIdealSum d C ⌊t⌋₊ : ℝ) - (2 π / (w_K √|D|)) * t| ≤ M * √t`! -/
theorem classIdealSum_asymptotic {d : ℕ} (hd : 0 < d) (hsf : Squarefree d)
    (C : ClassGroup (𝓞 (ImagQuadField d))) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 1 ≤ t →
      |(classIdealSum d C ⌊t⌋₊ : ℝ) -
        (2 * Real.pi / ((imagQuadUnitCard d : ℝ) * Real.sqrt (imagQuadDiscNat d : ℝ))) * t| ≤
        M * Real.sqrt t := by
  classical
  obtain ⟨A, hA⟩ := ClassGroup.mk0_surjective C⁻¹
  have hA_ne : (A : Ideal (𝓞 (ImagQuadField d))) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp A.2
  have hA_norm_pos : 0 < Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) :=
    absNorm_pos_of_ne_bot hA_ne
  have hA_norm_pos_R : (0 : ℝ) < (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ) :=
    Nat.cast_pos.mpr hA_norm_pos
  have hQuot_card : Nat.card (𝓞 (ImagQuadField d) ⧸ (A : Ideal (𝓞 (ImagQuadField d)))) =
      Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hQuot_fin : Finite (𝓞 (ImagQuadField d) ⧸ (A : Ideal (𝓞 (ImagQuadField d)))) :=
    Nat.finite_of_card_ne_zero (hQuot_card.symm ▸ hA_norm_pos.ne')
  let : Fintype (𝓞 (ImagQuadField d) ⧸ (A : Ideal (𝓞 (ImagQuadField d)))) := Fintype.ofFinite _
  have hQuot_fcard : Fintype.card (𝓞 (ImagQuadField d) ⧸ (A : Ideal (𝓞 (ImagQuadField d)))) =
      Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) := by
    rw [← Nat.card_eq_fintype_card, hQuot_card]
  -- Define fundamental domain `F_A = ⋃ q : 𝓞 K ⧸ A, (embed (Quotient.out q) +ᵥ F_O)`.
  let rep : (𝓞 (ImagQuadField d) ⧸ (A : Ideal (𝓞 (ImagQuadField d)))) → 𝓞 (ImagQuadField d) :=
    Quotient.out
  let F_A : Set (EuclideanSpace ℝ (Fin 2)) :=
    ⋃ q : 𝓞 (ImagQuadField d) ⧸ (A : Ideal (𝓞 (ImagQuadField d))),
      imagQuadEmbed d (rep q : ImagQuadField d) +ᵥ intFundDomain d
  have hF_O_meas : MeasurableSet (intFundDomain d) := measurableSet_intFundDomain d
  have hF_A_meas : MeasurableSet F_A :=
    MeasurableSet.iUnion fun q => hF_O_meas.const_vadd _
  obtain ⟨hcov_O, hdisj_O⟩ := intFundDomain_tiling hd hsf
  -- Exact volume of `F_A`: `V_A = N(A) * √|D| / 2`.
  set V_A : ℝ := (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ) *
      Real.sqrt (imagQuadDiscNat d : ℝ) / 2
  have hV_A_pos : 0 < V_A := by
    dsimp only [V_A]
    have hsq : 0 < Real.sqrt (imagQuadDiscNat d : ℝ) :=
      Real.sqrt_pos.mpr (Nat.cast_pos.mpr (imagQuadDiscNat_pos d))
    positivity
  have hvol_F_A : volume F_A = ENNReal.ofReal V_A := by
    have hpw : ∀ q₁ q₂ : 𝓞 (ImagQuadField d) ⧸ (A : Ideal (𝓞 (ImagQuadField d))), q₁ ≠ q₂ →
        Disjoint (imagQuadEmbed d (rep q₁ : ImagQuadField d) +ᵥ intFundDomain d)
                 (imagQuadEmbed d (rep q₂ : ImagQuadField d) +ᵥ intFundDomain d) := by
      intro q₁ q₂ hne
      rw [Set.disjoint_left]
      intro x hx₁ hx₂
      have hrep_eq : rep q₁ = rep q₂ := hdisj_O (rep q₁) (rep q₂) ⟨x, hx₁, hx₂⟩
      apply hne
      rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
      exact congrArg (Ideal.Quotient.mk _) hrep_eq
    have hUnion : F_A = ⋃ q ∈ (Finset.univ : Finset (𝓞 (ImagQuadField d) ⧸ (A : Ideal (𝓞 (ImagQuadField d))))),
        imagQuadEmbed d (rep q : ImagQuadField d) +ᵥ intFundDomain d := by
      ext x; simp [F_A]
    rw [hUnion, MeasureTheory.measure_biUnion_finset (fun q₁ _ q₂ _ h => hpw q₁ q₂ h)
      (fun q _ => hF_O_meas.const_vadd _)]
    have hterm : ∀ q ∈ (Finset.univ : Finset (𝓞 (ImagQuadField d) ⧸ (A : Ideal (𝓞 (ImagQuadField d))))),
        volume (imagQuadEmbed d (rep q : ImagQuadField d) +ᵥ intFundDomain d) =
          ENNReal.ofReal (Real.sqrt (imagQuadDiscNat d : ℝ) / 2) := by
      intro q _
      rw [MeasureTheory.measure_vadd, volume_intFundDomain]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_univ, hQuot_fcard, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1; dsimp only [V_A]; ring
  -- Boundedness of `F_A`: `∃ δ > 0, ∀ y ∈ F_A, ‖y‖ ≤ δ`.
  have hF_A_bdd : ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ F_A, ‖y‖ ≤ δ := by
    set L := (imagQuadBasisEquiv d).toContinuousLinearMap
    have hO_bdd : ∀ z ∈ intFundDomain d, ‖z‖ ≤ ‖L‖ * 2 := by
      intro z hz
      rcases hz with ⟨u, hu, rfl⟩
      have hu_norm : ‖u‖ ≤ 2 := by
        have hsq : ‖u‖ ^ 2 ≤ 4 := by
          rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
          have h0 : 0 ≤ u 0 ∧ u 0 < 1 := by simpa [unitSquare2] using hu 0
          have h1 : 0 ≤ u 1 ∧ u 1 < 1 := by simpa [unitSquare2] using hu 1
          rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
          nlinarith
        nlinarith [norm_nonneg u]
      exact (L.le_opNorm u).trans (mul_le_mul_of_nonneg_left hu_norm (norm_nonneg L))
    set B_rep : ℝ := ∑ q : 𝓞 (ImagQuadField d) ⧸ (A : Ideal (𝓞 (ImagQuadField d))),
        ‖imagQuadEmbed d (rep q : ImagQuadField d)‖
    refine ⟨B_rep + ‖L‖ * 2 + 1, by positivity, fun y hy => ?_⟩
    rcases Set.mem_iUnion.mp hy with ⟨q, hq⟩
    rcases Set.mem_vadd_set.mp hq with ⟨z, hz, rfl⟩
    rw [vadd_eq_add]
    have hq_le : ‖imagQuadEmbed d (rep q : ImagQuadField d)‖ ≤ B_rep :=
      Finset.single_le_sum (f := fun q' => ‖imagQuadEmbed d (rep q' : ImagQuadField d)‖)
        (fun q' _ => norm_nonneg _) (Finset.mem_univ q)
    calc ‖imagQuadEmbed d (rep q : ImagQuadField d) + z‖
        ≤ ‖imagQuadEmbed d (rep q : ImagQuadField d)‖ + ‖z‖ := norm_add_le _ _
      _ ≤ B_rep + ‖L‖ * 2 := add_le_add hq_le (hO_bdd z hz)
      _ ≤ B_rep + ‖L‖ * 2 + 1 := by linarith
  obtain ⟨δ, hδ_pos, hδ_bdd⟩ := hF_A_bdd
  -- Exact tiling of `ℝ²` by `{imagQuadEmbed d a +ᵥ F_A | a ∈ A}`.
  have hF_A_disj : ∀ a₁ a₂ : 𝓞 (ImagQuadField d),
      a₁ ∈ (A : Ideal (𝓞 (ImagQuadField d))) → a₂ ∈ (A : Ideal (𝓞 (ImagQuadField d))) →
      a₁ ≠ a₂ →
      Disjoint (imagQuadEmbed d (a₁ : ImagQuadField d) +ᵥ F_A)
               (imagQuadEmbed d (a₂ : ImagQuadField d) +ᵥ F_A) := by
    intro a₁ a₂ ha₁ ha₂ hne
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    rcases Set.mem_vadd_set.mp hx₁ with ⟨y₁, hy₁, hxy₁⟩
    rcases Set.mem_vadd_set.mp hx₂ with ⟨y₂, hy₂, hxy₂⟩
    rcases Set.mem_iUnion.mp hy₁ with ⟨q₁, hq₁⟩
    rcases Set.mem_iUnion.mp hy₂ with ⟨q₂, hq₂⟩
    rcases Set.mem_vadd_set.mp hq₁ with ⟨z₁, hz₁, hyz₁⟩
    rcases Set.mem_vadd_set.mp hq₂ with ⟨z₂, hz₂, hyz₂⟩
    have hx_O1 : x ∈ imagQuadEmbed d ((a₁ + rep q₁ : 𝓞 (ImagQuadField d)) : ImagQuadField d) +ᵥ intFundDomain d := by
      rw [Set.mem_vadd_set]
      refine ⟨z₁, hz₁, ?_⟩
      simp only [vadd_eq_add] at hxy₁ hyz₁ ⊢
      rw [show ((a₁ + rep q₁ : 𝓞 (ImagQuadField d)) : ImagQuadField d) =
        (a₁ : ImagQuadField d) + (rep q₁ : ImagQuadField d) from rfl,
        imagQuadEmbed_add, add_assoc, hyz₁, hxy₁]
    have hx_O2 : x ∈ imagQuadEmbed d ((a₂ + rep q₂ : 𝓞 (ImagQuadField d)) : ImagQuadField d) +ᵥ intFundDomain d := by
      rw [Set.mem_vadd_set]
      refine ⟨z₂, hz₂, ?_⟩
      simp only [vadd_eq_add] at hxy₂ hyz₂ ⊢
      rw [show ((a₂ + rep q₂ : 𝓞 (ImagQuadField d)) : ImagQuadField d) =
        (a₂ : ImagQuadField d) + (rep q₂ : ImagQuadField d) from rfl,
        imagQuadEmbed_add, add_assoc, hyz₂, hxy₂]
    have hsum_eq : a₁ + rep q₁ = a₂ + rep q₂ := hdisj_O _ _ ⟨x, hx_O1, hx_O2⟩
    have hq_eq : q₁ = q₂ := by
      have hmk := congrArg (Ideal.Quotient.mk (A : Ideal (𝓞 (ImagQuadField d)))) hsum_eq
      rw [map_add, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha₁,
        Ideal.Quotient.eq_zero_iff_mem.mpr ha₂, zero_add, zero_add] at hmk
      simpa [rep, Quotient.out_eq] using hmk
    subst hq_eq
    exact hne (add_right_cancel hsum_eq)
  have hF_A_cov : ∀ x : EuclideanSpace ℝ (Fin 2),
      ∃ a : 𝓞 (ImagQuadField d), a ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧
        x ∈ imagQuadEmbed d (a : ImagQuadField d) +ᵥ F_A := by
    intro x
    obtain ⟨v, hv⟩ := hcov_O x
    rcases Set.mem_vadd_set.mp hv with ⟨z, hz, hxz⟩
    set q := Ideal.Quotient.mk (A : Ideal (𝓞 (ImagQuadField d))) v
    refine ⟨v - rep q, ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
      have hout : Ideal.Quotient.mk (A : Ideal (𝓞 (ImagQuadField d))) (rep q) = q := Quotient.out_eq q
      rw [hout, sub_self]
    · rw [Set.mem_vadd_set]
      refine ⟨imagQuadEmbed d (rep q : ImagQuadField d) +ᵥ z,
        Set.mem_iUnion.mpr ⟨q, Set.mem_vadd_set.mpr ⟨z, hz, rfl⟩⟩, ?_⟩
      simp only [vadd_eq_add] at hxz ⊢
      rw [show ((v - rep q : 𝓞 (ImagQuadField d)) : ImagQuadField d) =
        (v : ImagQuadField d) - (rep q : ImagQuadField d) from rfl, imagQuadEmbed_sub]
      calc imagQuadEmbed d (v : ImagQuadField d) - imagQuadEmbed d (rep q : ImagQuadField d) +
            (imagQuadEmbed d (rep q : ImagQuadField d) + z)
          = imagQuadEmbed d (v : ImagQuadField d) + z := by abel
        _ = x := hxz
  -- Volume of 2D closed Euclidean ball: `volume (closedBall 0 r) = ENNReal.ofReal (π * r^2)` for `r ≥ 0`.
  have hvol_ball : ∀ r : ℝ, 0 ≤ r →
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r) =
        ENNReal.ofReal (Real.pi * r ^ 2) := by
    intro r hr
    rw [EuclideanSpace.volume_closedBall, Fintype.card_fin]
    have hG : Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1) = 1 := by
      have : ((2 : ℕ) : ℝ) / 2 + 1 = ((1 : ℕ) : ℝ) + 1 := by norm_num
      rw [this, Real.Gamma_nat_eq_factorial, Nat.factorial_one, Nat.cast_one]
    rw [hG, div_one, Real.sq_sqrt Real.pi_pos.le, ← ENNReal.ofReal_pow hr,
      ← ENNReal.ofReal_mul (sq_nonneg r), mul_comm]
  -- Disk lattice-point counting bounds for every `N : ℕ` with `R := √(N * N(A))`:
  have hcount_bounds : ∀ N : ℕ,
      let R : ℝ := Real.sqrt ((N : ℝ) * (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ))
      ((classIdealSum d C N * imagQuadUnitCard d + 1 : ℕ) : ℝ) * V_A ≤
        Real.pi * (R + δ) ^ 2 ∧
      (δ ≤ R → Real.pi * (R - δ) ^ 2 ≤
        ((classIdealSum d C N * imagQuadUnitCard d + 1 : ℕ) : ℝ) * V_A) := by
    intro N R
    have hR_nn : 0 ≤ R := Real.sqrt_nonneg _
    have hR_sq : R ^ 2 = (N : ℝ) * (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ) :=
      Real.sq_sqrt (by positivity)
    have hfin_N : Finite {x : 𝓞 (ImagQuadField d) //
        x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧
          Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} := by
      have := finite_ringOfIntegers_absNorm_le hd hsf
        (N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))))
      exact Finite.of_injective (fun x => (⟨x.1, x.2.2⟩ :
        {x : 𝓞 (ImagQuadField d) // Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))}))
        (fun _ _ h => Subtype.ext (congrArg (fun y => y.1) h))
    let : Fintype {x : 𝓞 (ImagQuadField d) //
        x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧
          Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} :=
      Fintype.ofFinite _
    let S_N : Finset (𝓞 (ImagQuadField d)) :=
      Finset.univ.image (fun x : {x : 𝓞 (ImagQuadField d) //
        x ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧
          Ideal.absNorm (Ideal.span {x}) ≤ N * Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d)))} => x.1)
    have hS_N_mem : ∀ a : 𝓞 (ImagQuadField d), a ∈ S_N ↔
        a ∈ (A : Ideal (𝓞 (ImagQuadField d))) ∧ ‖imagQuadEmbed d (a : ImagQuadField d)‖ ≤ R := by
      intro a
      simp only [S_N, Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists]
      constructor
      · rintro ⟨a', ⟨ha'A, ha'N⟩, rfl⟩
        refine ⟨ha'A, ?_⟩
        have hsq : ‖imagQuadEmbed d (a' : ImagQuadField d)‖ ^ 2 ≤ R ^ 2 := by
          rw [norm_sq_imagQuadEmbed_int, hR_sq]
          exact_mod_cast ha'N
        exact (sq_le_sq₀ (norm_nonneg _) hR_nn).mp hsq
      · rintro ⟨haA, hnorm⟩
        refine ⟨a, ⟨haA, ?_⟩, rfl⟩
        have hsq : (Ideal.absNorm (Ideal.span {a}) : ℝ) ≤
            (N : ℝ) * (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ) := by
          rw [← norm_sq_imagQuadEmbed_int, ← hR_sq]
          exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        exact_mod_cast hsq
    have hS_N_card : S_N.card = classIdealSum d C N * imagQuadUnitCard d + 1 := by
      rw [classIdealSum_mul_unitCard_add_one_eq hd hsf C A hA N, Nat.card_eq_fintype_card]
      dsimp only [S_N]
      rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
    have hvol_union : volume (⋃ a ∈ S_N, imagQuadEmbed d (a : ImagQuadField d) +ᵥ F_A) =
        ENNReal.ofReal (((classIdealSum d C N * imagQuadUnitCard d + 1 : ℕ) : ℝ) * V_A) := by
      rw [MeasureTheory.measure_biUnion_finset
        (fun a₁ ha₁ a₂ ha₂ hne => hF_A_disj a₁ a₂ ((hS_N_mem a₁).mp ha₁).1 ((hS_N_mem a₂).mp ha₂).1 hne)
        (fun _ _ => hF_A_meas.const_vadd _)]
      have hterm : ∀ a ∈ S_N, volume (imagQuadEmbed d (a : ImagQuadField d) +ᵥ F_A) = ENNReal.ofReal V_A :=
        fun _ _ => by rw [MeasureTheory.measure_vadd, hvol_F_A]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, hS_N_card, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    constructor
    · -- Upper bound: `⋃_{a ∈ S_N} (embed a +ᵥ F_A) ⊆ closedBall 0 (R + δ)`
      have hsub : (⋃ a ∈ S_N, imagQuadEmbed d (a : ImagQuadField d) +ᵥ F_A) ⊆
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (R + δ) := by
        intro x hx
        rcases Set.mem_iUnion₂.mp hx with ⟨a, ha, hxa⟩
        rcases Set.mem_vadd_set.mp hxa with ⟨y, hy, rfl⟩
        rw [Metric.mem_closedBall, dist_zero_right, vadd_eq_add]
        exact (norm_add_le _ _).trans (add_le_add ((hS_N_mem a).mp ha).2 (hδ_bdd y hy))
      have hm := MeasureTheory.measure_mono (μ := volume) hsub
      rw [hvol_union, hvol_ball (R + δ) (by linarith)] at hm
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hm
    · -- Lower bound (for `δ ≤ R`): `closedBall 0 (R - δ) ⊆ ⋃_{a ∈ S_N} (embed a +ᵥ F_A)`
      intro hδR
      have hsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (R - δ) ⊆
          ⋃ a ∈ S_N, imagQuadEmbed d (a : ImagQuadField d) +ᵥ F_A := by
        intro x hx
        rw [Metric.mem_closedBall, dist_zero_right] at hx
        obtain ⟨a, haA, hxa⟩ := hF_A_cov x
        rcases Set.mem_vadd_set.mp hxa with ⟨y, hy, hxy⟩
        have ha_norm : ‖imagQuadEmbed d (a : ImagQuadField d)‖ ≤ R := by
          have heq : imagQuadEmbed d (a : ImagQuadField d) = x - y := by
            simp only [vadd_eq_add] at hxy; exact eq_sub_of_add_eq hxy
          rw [heq]
          calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
            _ ≤ (R - δ) + δ := add_le_add hx (hδ_bdd y hy)
            _ = R := by ring
        exact Set.mem_iUnion₂.mpr ⟨a, (hS_N_mem a).mpr ⟨haA, ha_norm⟩, hxa⟩
      have hm := MeasureTheory.measure_mono (μ := volume) hsub
      rw [hvol_union, hvol_ball (R - δ) (by linarith)] at hm
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hm
  -- Convert the disk count bounds into `|(classIdealSum d C ⌊t⌋₊ : ℝ) - c_d * t| ≤ M * √t` for all `t ≥ 1`.
  set wR : ℝ := (imagQuadUnitCard d : ℝ)
  set c_d : ℝ := 2 * Real.pi / (wR * Real.sqrt (imagQuadDiscNat d : ℝ))
  have hw_pos : 0 < wR := Nat.cast_pos.mpr (imagQuadUnitCard_pos d)
  have hsqD_pos : 0 < Real.sqrt (imagQuadDiscNat d : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (imagQuadDiscNat_pos d))
  have hc_pos : 0 < c_d := by dsimp only [c_d]; positivity
  set sNA : ℝ := Real.sqrt (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ)
  have hsNA_pos : 0 < sNA := Real.sqrt_pos.mpr hA_norm_pos_R
  have hc_eq : ∀ N : ℕ,
      Real.pi * (Real.sqrt ((N : ℝ) * (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ))) ^ 2 /
        (wR * V_A) = c_d * (N : ℝ) := by
    intro N
    rw [Real.sq_sqrt (by positivity)]
    dsimp only [c_d, V_A]
    field_simp [hw_pos.ne', hsqD_pos.ne', hA_norm_pos_R.ne']
  set M : ℝ := (2 * Real.pi * δ * sNA + Real.pi * δ ^ 2) / (wR * V_A) + 1 / wR +
      c_d + (Real.pi * (2 * δ) ^ 2 / (wR * V_A) + c_d * (δ ^ 2 / (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ) + 1))
  refine ⟨M, by positivity, fun t ht => ?_⟩
  set N : ℕ := ⌊t⌋₊
  have hN_le_t : (N : ℝ) ≤ t := Nat.floor_le (by linarith)
  have ht_lt_N1 : t < (N : ℝ) + 1 := Nat.lt_floor_add_one t
  have hsqt_ge1 : (1 : ℝ) ≤ Real.sqrt t := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt ht
  have hsqN_le_sqt : Real.sqrt (N : ℝ) ≤ Real.sqrt t := Real.sqrt_le_sqrt hN_le_t
  set R : ℝ := Real.sqrt ((N : ℝ) * (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ))
  have hR_eq : R = sNA * Real.sqrt (N : ℝ) := by
    dsimp only [R, sNA]
    rw [Real.sqrt_mul (Nat.cast_nonneg N), mul_comm]
  obtain ⟨hup, hlo⟩ := hcount_bounds N
  have hwVA_pos : 0 < wR * V_A := mul_pos hw_pos hV_A_pos
  have hup_div : (classIdealSum d C N : ℝ) + 1 / wR ≤ Real.pi * (R + δ) ^ 2 / (wR * V_A) := by
    rw [le_div_iff₀ hwVA_pos]
    have hcast : ((classIdealSum d C N * imagQuadUnitCard d + 1 : ℕ) : ℝ) * V_A =
        ((classIdealSum d C N : ℝ) + 1 / wR) * (wR * V_A) := by
      have hwne : (imagQuadUnitCard d : ℝ) ≠ 0 := hw_pos.ne'
      dsimp only [wR]; push_cast; field_simp [hwne]
    linarith
  by_cases hδR : δ ≤ R
  · have hlo_div : Real.pi * (R - δ) ^ 2 / (wR * V_A) ≤ (classIdealSum d C N : ℝ) + 1 / wR := by
      rw [div_le_iff₀ hwVA_pos]
      have hcast : ((classIdealSum d C N * imagQuadUnitCard d + 1 : ℕ) : ℝ) * V_A =
          ((classIdealSum d C N : ℝ) + 1 / wR) * (wR * V_A) := by
        have hwne : (imagQuadUnitCard d : ℝ) ≠ 0 := hw_pos.ne'
        dsimp only [wR]; push_cast; field_simp [hwne]
      linarith [hlo hδR]
    have hdiff_N : |(classIdealSum d C N : ℝ) - c_d * (N : ℝ)| ≤
        (2 * Real.pi * δ * R + Real.pi * δ ^ 2) / (wR * V_A) + 1 / wR := by
      rw [abs_le]
      have hmain : Real.pi * R ^ 2 / (wR * V_A) = c_d * (N : ℝ) := hc_eq N
      have hexp_up : Real.pi * (R + δ) ^ 2 / (wR * V_A) =
          c_d * (N : ℝ) + (2 * Real.pi * δ * R + Real.pi * δ ^ 2) / (wR * V_A) := by
        rw [← hmain]; ring
      have hexp_lo : Real.pi * (R - δ) ^ 2 / (wR * V_A) =
          c_d * (N : ℝ) - 2 * Real.pi * δ * R / (wR * V_A) + Real.pi * δ ^ 2 / (wR * V_A) := by
        rw [← hmain]; ring
      have hpi_d2 : 0 ≤ Real.pi * δ ^ 2 / (wR * V_A) := by positivity
      have h1w : 0 ≤ 1 / wR := by positivity
      have hsplit_up : (2 * Real.pi * δ * R + Real.pi * δ ^ 2) / (wR * V_A) =
          2 * Real.pi * δ * R / (wR * V_A) + Real.pi * δ ^ 2 / (wR * V_A) := by ring
      constructor <;> linarith
    have htri : |(classIdealSum d C N : ℝ) - c_d * t| ≤
        |(classIdealSum d C N : ℝ) - c_d * (N : ℝ)| + c_d * (t - (N : ℝ)) := by
      have h1 : (classIdealSum d C N : ℝ) - c_d * t =
          ((classIdealSum d C N : ℝ) - c_d * (N : ℝ)) - c_d * (t - (N : ℝ)) := by ring
      rw [h1]
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg (mul_nonneg hc_pos.le (by linarith))])
    have hR_le : R ≤ sNA * Real.sqrt t := by rw [hR_eq]; exact mul_le_mul_of_nonneg_left hsqN_le_sqt hsNA_pos.le
    have h1_le : (2 * Real.pi * δ * R + Real.pi * δ ^ 2) / (wR * V_A) + 1 / wR + c_d * (t - (N : ℝ)) ≤
        ((2 * Real.pi * δ * sNA + Real.pi * δ ^ 2) / (wR * V_A) + 1 / wR + c_d) * Real.sqrt t := by
      have hterm1 : 2 * Real.pi * δ * R / (wR * V_A) ≤ (2 * Real.pi * δ * sNA / (wR * V_A)) * Real.sqrt t := by
        have : 2 * Real.pi * δ * R ≤ (2 * Real.pi * δ * sNA) * Real.sqrt t := by
          have := mul_le_mul_of_nonneg_left hR_le (by positivity : 0 ≤ 2 * Real.pi * δ)
          linarith
        have hdiv := div_le_div_of_nonneg_right this hwVA_pos.le
        linarith [show 2 * Real.pi * δ * sNA * Real.sqrt t / (wR * V_A) =
          (2 * Real.pi * δ * sNA / (wR * V_A)) * Real.sqrt t by ring]
      have hterm2 : Real.pi * δ ^ 2 / (wR * V_A) ≤ (Real.pi * δ ^ 2 / (wR * V_A)) * Real.sqrt t :=
        le_mul_of_one_le_right (by positivity) hsqt_ge1
      have hterm3 : 1 / wR ≤ (1 / wR) * Real.sqrt t := le_mul_of_one_le_right (by positivity) hsqt_ge1
      have hterm4 : c_d * (t - (N : ℝ)) ≤ c_d * Real.sqrt t :=
        mul_le_mul_of_nonneg_left (by linarith) hc_pos.le
      linarith [show (2 * Real.pi * δ * R + Real.pi * δ ^ 2) / (wR * V_A) =
        2 * Real.pi * δ * R / (wR * V_A) + Real.pi * δ ^ 2 / (wR * V_A) by ring,
        show ((2 * Real.pi * δ * sNA + Real.pi * δ ^ 2) / (wR * V_A) + 1 / wR + c_d) * Real.sqrt t =
        (2 * Real.pi * δ * sNA / (wR * V_A)) * Real.sqrt t +
          (Real.pi * δ ^ 2 / (wR * V_A)) * Real.sqrt t + (1 / wR) * Real.sqrt t + c_d * Real.sqrt t by ring]
    have hM_ge : (2 * Real.pi * δ * sNA + Real.pi * δ ^ 2) / (wR * V_A) + 1 / wR + c_d ≤ M := by
      dsimp only [M]; linarith [show 0 ≤ Real.pi * (2 * δ) ^ 2 / (wR * V_A) +
        c_d * (δ ^ 2 / (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ) + 1) by positivity]
    calc |(classIdealSum d C N : ℝ) - c_d * t|
        ≤ (2 * Real.pi * δ * R + Real.pi * δ ^ 2) / (wR * V_A) + 1 / wR + c_d * (t - (N : ℝ)) := by
          linarith
      _ ≤ ((2 * Real.pi * δ * sNA + Real.pi * δ ^ 2) / (wR * V_A) + 1 / wR + c_d) * Real.sqrt t := h1_le
      _ ≤ M * Real.sqrt t := mul_le_mul_of_nonneg_right hM_ge (Real.sqrt_nonneg t)
  · push Not at hδR
    have hN_bdd : (N : ℝ) ≤ δ ^ 2 / (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ) := by
      rw [le_div_iff₀ hA_norm_pos_R]
      have hsq : R ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hδR.le 2
      rwa [Real.sq_sqrt (by positivity)] at hsq
    have ht_bdd : t ≤ δ ^ 2 / (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ) + 1 := by linarith
    have hS_bdd : (classIdealSum d C N : ℝ) ≤ Real.pi * (2 * δ) ^ 2 / (wR * V_A) := by
      have h1 : (R + δ) ^ 2 ≤ (2 * δ) ^ 2 := by nlinarith [Real.sqrt_nonneg ((N : ℝ) * (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ))]
      have h2 : Real.pi * (R + δ) ^ 2 / (wR * V_A) ≤ Real.pi * (2 * δ) ^ 2 / (wR * V_A) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 Real.pi_pos.le) hwVA_pos.le
      linarith [show (0 : ℝ) ≤ 1 / wR by positivity]
    have habs_le : |(classIdealSum d C N : ℝ) - c_d * t| ≤
        Real.pi * (2 * δ) ^ 2 / (wR * V_A) +
          c_d * (δ ^ 2 / (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ) + 1) := by
      rw [abs_le]
      have hS_nn : (0 : ℝ) ≤ (classIdealSum d C N : ℝ) := Nat.cast_nonneg _
      have hct_nn : 0 ≤ c_d * t := mul_nonneg hc_pos.le (by linarith)
      have hct_le : c_d * t ≤ c_d * (δ ^ 2 / (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left ht_bdd hc_pos.le
      constructor <;> linarith
    have hM_ge : Real.pi * (2 * δ) ^ 2 / (wR * V_A) +
        c_d * (δ ^ 2 / (Ideal.absNorm (A : Ideal (𝓞 (ImagQuadField d))) : ℝ) + 1) ≤ M := by
      dsimp only [M]
      linarith [show 0 ≤ (2 * Real.pi * δ * sNA + Real.pi * δ ^ 2) / (wR * V_A) + 1 / wR + c_d by positivity]
    exact habs_le.trans (hM_ge.trans (le_mul_of_one_le_right (by positivity) hsqt_ge1))

end IdealClassLatticeCounting

/-! ## Section 5: Abelian Summation & Genuine Analytic Class Number Formula on Native `NumberField.classNumber` -/

section AnalyticClassNumberFormula

/-- **General Real Abelian Residue Theorem**:
for any non-negative sequence `a : ℕ → ℝ` (`a 0 = 0`) whose summatory function
`A(t) = ∑_{1 ≤ n ≤ ⌊t⌋₊} a n` satisfies `|A(t) - c * t| ≤ M * √t` for all `t ≥ 1`:
`lim_{σ → 1⁺} (σ - 1) * ∑' n, a n * n ^ (-σ) = c`! -/
theorem abelian_residue_of_sqrt_error {a : ℕ → ℝ} (ha0 : a 0 = 0) (ha_nn : ∀ n, 0 ≤ a n)
    {c M : ℝ} (hM : 0 < M)
    (hA : ∀ t : ℝ, 1 ≤ t → |∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n - c * t| ≤ M * Real.sqrt t) :
    Tendsto (fun σ : ℝ => (σ - 1) * ∑' n : ℕ, a n * (n : ℝ) ^ (-σ)) (𝓝[>] (1 : ℝ)) (nhds c) := by
  let aC : ℕ → ℂ := fun n => (a n : ℂ)
  let A : ℝ → ℝ := fun t => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n
  have hA_meas : Measurable A := by
    have h : A = (fun k : ℕ => ∑ n ∈ Finset.Icc 1 k, a n) ∘ Nat.floor := rfl
    rw [h]
    exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
  have hstep_re : ∀ t : ℝ, stepSum aC t = (A t : ℂ) := by
    intro t
    unfold stepSum
    dsimp only [aC, A]
    rw [Complex.ofReal_sum]
  have hA_bd : ∀ t : ℝ, 1 ≤ t → |A t| ≤ (M + |c|) * t := by
    intro t ht
    have hsq_le : Real.sqrt t ≤ t := by
      have hsq : Real.sqrt t ^ 2 ≤ t ^ 2 := by rw [Real.sq_sqrt (by linarith)]; nlinarith
      exact (sq_le_sq₀ (Real.sqrt_nonneg t) (by linarith)).mp hsq
    have h1 := hA t ht
    have htri : |A t| ≤ |A t - c * t| + |c * t| := by
      have : A t = (A t - c * t) + c * t := by ring
      conv_lhs => rw [this]
      exact abs_add_le _ _
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)] at htri
    nlinarith [hsq_le]
  -- Step 1: For every `σ > 1`, `∑' n, a n * n^(-σ) = σ * ∫ t in Ioi 1, A t * t^(-σ - 1)`.
  have htsum_eq : ∀ σ : ℝ, 1 < σ →
      ∑' n : ℕ, a n * (n : ℝ) ^ (-σ) = σ * ∫ t in Ioi (1 : ℝ), A t * t ^ (-σ - 1) := by
    intro σ hσ
    have hInt : IntegrableOn (fun t : ℝ => A t * t ^ (-σ - 1)) (Ioi (1 : ℝ)) := by
      have hdom : IntegrableOn (fun t : ℝ => (M + |c|) * t ^ (-σ)) (Ioi (1 : ℝ)) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul (M + |c|)
      refine hdom.mono' (hA_meas.mul (measurable_id.pow_const (-σ - 1))).aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      have hpow : t * t ^ (-σ - 1) = t ^ (-σ) := by
        calc t * t ^ (-σ - 1) = t ^ (1 : ℝ) * t ^ (-σ - 1) := by rw [Real.rpow_one]
          _ = t ^ (1 + (-σ - 1)) := (Real.rpow_add ht0 1 (-σ - 1)).symm
          _ = t ^ (-σ) := by congr 1; ring
      calc |A t| * t ^ (-σ - 1)
          ≤ ((M + |c|) * t) * t ^ (-σ - 1) :=
            mul_le_mul_of_nonneg_right (hA_bd t ht.le) (Real.rpow_nonneg ht0.le _)
        _ = (M + |c|) * (t * t ^ (-σ - 1)) := by ring
        _ = (M + |c|) * t ^ (-σ) := by rw [hpow]
    -- Real Abelian summation at integer upper limit `N ≥ 1`
    have hAb : ∀ N : ℕ, 1 ≤ N →
        ∑ n ∈ Finset.Icc 1 N, a n * (n : ℝ) ^ (-σ) =
          A (N : ℝ) * (N : ℝ) ^ (-σ) + σ * ∫ t in (1 : ℝ)..(N : ℝ), A t * t ^ (-σ - 1) := by
      intro N hN
      have hC := Stage3RealAnalyticLandau.abel_summation_dirichlet aC
        (x := (N : ℝ)) (by exact_mod_cast hN) (σ : ℂ)
      rw [Nat.floor_natCast] at hC
      have hre := congrArg Complex.re hC
      have hLHS : (∑ n ∈ Finset.Icc 1 N, aC n * (n : ℂ) ^ (-(σ : ℂ))).re =
          ∑ n ∈ Finset.Icc 1 N, a n * (n : ℝ) ^ (-σ) := by
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        dsimp only [aC]
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hn0,
          ← Complex.ofReal_mul, Complex.ofReal_re]
      have hBdy : (stepSum aC (N : ℝ) * ((N : ℝ) : ℂ) ^ (-(σ : ℂ))).re =
          A (N : ℝ) * (N : ℝ) ^ (-σ) := by
        rw [hstep_re, ← Complex.ofReal_neg, ← Complex.ofReal_cpow (Nat.cast_nonneg N),
          ← Complex.ofReal_mul, Complex.ofReal_re]
      have hInt_re :
          ((σ : ℂ) * ∫ t in (1 : ℝ)..(N : ℝ), stepSum aC t * (t : ℂ) ^ (-(σ : ℂ) - 1)).re =
            σ * ∫ t in (1 : ℝ)..(N : ℝ), A t * t ^ (-σ - 1) := by
        have hcongr : ∫ t in (1 : ℝ)..(N : ℝ), stepSum aC t * (t : ℂ) ^ (-(σ : ℂ) - 1) =
            ∫ t in (1 : ℝ)..(N : ℝ), ((A t * t ^ (-σ - 1) : ℝ) : ℂ) := by
          refine intervalIntegral.integral_congr fun t ht => ?_
          rw [Set.uIcc_of_le (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ))] at ht
          have ht0 : (0 : ℝ) ≤ t := zero_le_one.trans ht.1
          rw [hstep_re, show -(σ : ℂ) - 1 = ((-σ - 1 : ℝ) : ℂ) by push_cast; rfl,
            ← Complex.ofReal_cpow ht0, ← Complex.ofReal_mul]
        rw [hcongr, intervalIntegral.integral_ofReal, Complex.re_ofReal_mul, Complex.ofReal_re]
      rw [hLHS, Complex.add_re, hBdy, hInt_re] at hre
      exact hre
    -- Take `N → ∞`: boundary term → 0, interval integral → improper integral on `Ioi 1`.
    have hBdy_lim : Tendsto (fun N : ℕ => A (N : ℝ) * (N : ℝ) ^ (-σ)) atTop (nhds 0) := by
      refine squeeze_zero_norm' (a := fun N : ℕ => (M + |c|) * (N : ℝ) ^ (1 - σ)) ?_ ?_
      · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
        have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        have hN0 : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans_le hN1
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hN0.le _)]
        have hpow : (N : ℝ) * (N : ℝ) ^ (-σ) = (N : ℝ) ^ (1 - σ) := by
          calc (N : ℝ) * (N : ℝ) ^ (-σ) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-σ) := by rw [Real.rpow_one]
            _ = (N : ℝ) ^ (1 + (-σ)) := (Real.rpow_add hN0 1 (-σ)).symm
            _ = (N : ℝ) ^ (1 - σ) := by rw [sub_eq_add_neg]
        calc |A (N : ℝ)| * (N : ℝ) ^ (-σ)
            ≤ ((M + |c|) * (N : ℝ)) * (N : ℝ) ^ (-σ) :=
              mul_le_mul_of_nonneg_right (hA_bd (N : ℝ) hN1) (Real.rpow_nonneg hN0.le _)
          _ = (M + |c|) * ((N : ℝ) * (N : ℝ) ^ (-σ)) := by ring
          _ = (M + |c|) * (N : ℝ) ^ (1 - σ) := by rw [hpow]
      · have h0 : Tendsto (fun x : ℝ => x ^ (1 - σ)) atTop (nhds 0) := by
          have h := tendsto_rpow_neg_atTop (show 0 < σ - 1 by linarith)
          exact h.congr fun x => by congr 1; ring
        have h1 : Tendsto (fun N : ℕ => (M + |c|) * (N : ℝ) ^ (1 - σ)) atTop (nhds ((M + |c|) * 0)) :=
          (h0.comp tendsto_natCast_atTop_atTop).const_mul (M + |c|)
        simpa using h1
    have hInt_lim : Tendsto (fun N : ℕ => ∫ t in (1 : ℝ)..(N : ℝ), A t * t ^ (-σ - 1))
        atTop (nhds (∫ t in Ioi (1 : ℝ), A t * t ^ (-σ - 1))) :=
      (MeasureTheory.intervalIntegral_tendsto_integral_Ioi 1 hInt tendsto_id).comp
        tendsto_natCast_atTop_atTop
    have hSum_lim : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℝ) ^ (-σ))
        atTop (nhds (σ * ∫ t in Ioi (1 : ℝ), A t * t ^ (-σ - 1))) := by
      have hEv : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℝ) ^ (-σ)) =ᶠ[atTop]
          (fun N : ℕ => A (N : ℝ) * (N : ℝ) ^ (-σ) + σ * ∫ t in (1 : ℝ)..(N : ℝ), A t * t ^ (-σ - 1)) := by
        filter_upwards [Filter.eventually_ge_atTop 1] with N hN using hAb N hN
      rw [tendsto_congr' hEv]
      simpa only [zero_add] using hBdy_lim.add (hInt_lim.const_mul σ)
    have hRange_lim : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, a n * (n : ℝ) ^ (-σ))
        atTop (nhds (σ * ∫ t in Ioi (1 : ℝ), A t * t ^ (-σ - 1))) := by
      have hshift : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), a n * (n : ℝ) ^ (-σ))
          atTop (nhds (σ * ∫ t in Ioi (1 : ℝ), A t * t ^ (-σ - 1))) := by
        refine hSum_lim.congr fun N => ?_
        have hsplit : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
          ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
        rw [hsplit, Finset.sum_insert (by simp), ha0, zero_mul, zero_add]
      exact (tendsto_add_atTop_iff_nat 1).mp hshift
    have hHasSum : HasSum (fun n : ℕ => a n * (n : ℝ) ^ (-σ))
        (σ * ∫ t in Ioi (1 : ℝ), A t * t ^ (-σ - 1)) :=
      (hasSum_iff_tendsto_nat_of_nonneg
        (fun n => mul_nonneg (ha_nn n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)) _).mpr hRange_lim
    exact hHasSum.tsum_eq
  -- Step 2: Split `A t = c * t + E t` with `|E t| ≤ M * √t`, evaluate main term `c / (σ - 1)` and bound error by `2 M`.
  have hDiff_bd : ∀ σ : ℝ, 1 < σ →
      |(σ - 1) * (∑' n : ℕ, a n * (n : ℝ) ^ (-σ)) - c| ≤
        (σ - 1) * |c| + σ * (σ - 1) * (2 * M) := by
    intro σ hσ
    rw [htsum_eq σ hσ]
    have hInt_main : IntegrableOn (fun t : ℝ => (c * t) * t ^ (-σ - 1)) (Ioi (1 : ℝ)) := by
      have h1 : IntegrableOn (fun t : ℝ => c * t ^ (-σ)) (Ioi (1 : ℝ)) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul c
      refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
      have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
      have hpow : t * t ^ (-σ - 1) = t ^ (-σ) := by
        calc t * t ^ (-σ - 1) = t ^ (1 : ℝ) * t ^ (-σ - 1) := by rw [Real.rpow_one]
          _ = t ^ (1 + (-σ - 1)) := (Real.rpow_add ht0 1 (-σ - 1)).symm
          _ = t ^ (-σ) := by congr 1; ring
      rw [mul_assoc, hpow]
    have hInt_err : IntegrableOn (fun t : ℝ => (A t - c * t) * t ^ (-σ - 1)) (Ioi (1 : ℝ)) := by
      have hdom : IntegrableOn (fun t : ℝ => M * t ^ (-σ - 1 / 2)) (Ioi (1 : ℝ)) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul M
      refine hdom.mono'
        ((hA_meas.sub (measurable_const.mul measurable_id)).mul
          (measurable_id.pow_const (-σ - 1))).aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      have hpow : Real.sqrt t * t ^ (-σ - 1) = t ^ (-σ - 1 / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0]; congr 1; ring
      calc |A t - c * t| * t ^ (-σ - 1)
          ≤ (M * Real.sqrt t) * t ^ (-σ - 1) :=
            mul_le_mul_of_nonneg_right (hA t ht.le) (Real.rpow_nonneg ht0.le _)
        _ = M * (Real.sqrt t * t ^ (-σ - 1)) := by ring
        _ = M * t ^ (-σ - 1 / 2) := by rw [hpow]
    have hsplit : ∫ t in Ioi (1 : ℝ), A t * t ^ (-σ - 1) =
        (∫ t in Ioi (1 : ℝ), (c * t) * t ^ (-σ - 1)) +
        (∫ t in Ioi (1 : ℝ), (A t - c * t) * t ^ (-σ - 1)) := by
      rw [← integral_add hInt_main hInt_err]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
    have hMain_val : ∫ t in Ioi (1 : ℝ), (c * t) * t ^ (-σ - 1) = c / (σ - 1) := by
      have heq : ∫ t in Ioi (1 : ℝ), (c * t) * t ^ (-σ - 1) =
          ∫ t in Ioi (1 : ℝ), c * t ^ (-σ) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
        have hpow : t * t ^ (-σ - 1) = t ^ (-σ) := by
          calc t * t ^ (-σ - 1) = t ^ (1 : ℝ) * t ^ (-σ - 1) := by rw [Real.rpow_one]
            _ = t ^ (1 + (-σ - 1)) := (Real.rpow_add ht0 1 (-σ - 1)).symm
            _ = t ^ (-σ) := by congr 1; ring
        rw [mul_assoc, hpow]
      rw [heq, integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      have hne1 : -σ + 1 ≠ 0 := by linarith
      have hne2 : σ - 1 ≠ 0 := by linarith
      field_simp [hne1, hne2]; ring
    have hErr_bd : |∫ t in Ioi (1 : ℝ), (A t - c * t) * t ^ (-σ - 1)| ≤ 2 * M := by
      have hdom : IntegrableOn (fun t : ℝ => M * t ^ (-σ - 1 / 2)) (Ioi (1 : ℝ)) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul M
      have h1 : |∫ t in Ioi (1 : ℝ), (A t - c * t) * t ^ (-σ - 1)| ≤
          ∫ t in Ioi (1 : ℝ), M * t ^ (-σ - 1 / 2) := by
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hdom ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
        dsimp only
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
        have hpow : Real.sqrt t * t ^ (-σ - 1) = t ^ (-σ - 1 / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0]; congr 1; ring
        calc |A t - c * t| * t ^ (-σ - 1)
            ≤ (M * Real.sqrt t) * t ^ (-σ - 1) :=
              mul_le_mul_of_nonneg_right (hA t ht.le) (Real.rpow_nonneg ht0.le _)
          _ = M * (Real.sqrt t * t ^ (-σ - 1)) := by ring
          _ = M * t ^ (-σ - 1 / 2) := by rw [hpow]
      have heval : ∫ t in Ioi (1 : ℝ), M * t ^ (-σ - 1 / 2) = M / (σ - 1 / 2) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow,
          show (-σ - 1 / 2 + 1 : ℝ) = -(σ - 1 / 2) by ring, div_neg]
        ring
      have hle2 : M / (σ - 1 / 2) ≤ 2 * M := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      exact h1.trans (heval.le.trans hle2)
    rw [hsplit, hMain_val]
    have hrew : (σ - 1) * (σ * (c / (σ - 1) + ∫ t in Ioi (1 : ℝ), (A t - c * t) * t ^ (-σ - 1))) - c =
        (σ - 1) * c + σ * (σ - 1) * (∫ t in Ioi (1 : ℝ), (A t - c * t) * t ^ (-σ - 1)) := by
      have hne : σ - 1 ≠ 0 := by linarith
      field_simp [hne]; ring
    rw [hrew]
    have hpos_prod : 0 < σ * (σ - 1) := mul_pos (by linarith) (by linarith)
    calc |(σ - 1) * c + σ * (σ - 1) * (∫ t in Ioi (1 : ℝ), (A t - c * t) * t ^ (-σ - 1))|
        ≤ |(σ - 1) * c| + |σ * (σ - 1) * (∫ t in Ioi (1 : ℝ), (A t - c * t) * t ^ (-σ - 1))| :=
          abs_add_le _ _
      _ = (σ - 1) * |c| + σ * (σ - 1) * |∫ t in Ioi (1 : ℝ), (A t - c * t) * t ^ (-σ - 1)| := by
          rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < σ - 1), abs_of_pos hpos_prod]
      _ ≤ (σ - 1) * |c| + σ * (σ - 1) * (2 * M) := by
          gcongr
  -- Step 3: Conclude `Tendsto` via `tendsto_iff_norm_sub_tendsto_zero` and `squeeze_zero_norm'`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' (a := fun σ : ℝ => (σ - 1) * |c| + σ * (σ - 1) * (2 * M)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    exact hDiff_bd σ hσ
  · have hlim : Tendsto (fun σ : ℝ => (σ - 1) * |c| + σ * (σ - 1) * (2 * M))
        (𝓝[>] (1 : ℝ)) (nhds ((1 - 1) * |c| + 1 * (1 - 1) * (2 * M))) :=
      tendsto_nhdsWithin_of_tendsto_nhds
        (((continuous_id.sub continuous_const).mul continuous_const).add
          ((continuous_id.mul (continuous_id.sub continuous_const)).mul continuous_const)).continuousAt.tendsto
    simpa using hlim

/-- Partition of `idealCount (ImagQuadField d) n` across all ideal classes `C : ClassGroup (𝓞 K)`
for every `n ≥ 1`. -/
theorem idealCount_eq_sum_classIdealCount (d : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    Stage7DedekindZeta.idealCount (ImagQuadField d) n =
      ∑ C : ClassGroup (𝓞 (ImagQuadField d)), classIdealCount d C n := by
  classical
  have hfin_I : Finite {I : Ideal (𝓞 (ImagQuadField d)) // Ideal.absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 (ImagQuadField d)) n).to_subtype
  let : Fintype {I : Ideal (𝓞 (ImagQuadField d)) // Ideal.absNorm I = n} := Fintype.ofFinite _
  let : ∀ C : ClassGroup (𝓞 (ImagQuadField d)),
      Fintype {I : ClassIdeals d C // Ideal.absNorm I.1.1 = n} := fun C =>
    have := finite_classIdeals_absNorm_eq d C n
    Fintype.ofFinite _
  let e : {I : Ideal (𝓞 (ImagQuadField d)) // Ideal.absNorm I = n} ≃
      Σ C : ClassGroup (𝓞 (ImagQuadField d)), {I : ClassIdeals d C // Ideal.absNorm I.1.1 = n} :=
    { toFun := fun I =>
        have hIne : I.1 ≠ ⊥ := fun hbot => by
          have h := I.2; rw [hbot, Ideal.absNorm_bot] at h; omega
        ⟨ClassGroup.mk0 ⟨I.1, mem_nonZeroDivisors_of_ne_zero hIne⟩, ⟨⟨⟨I.1, hIne⟩, rfl⟩, I.2⟩⟩
      invFun := fun p => ⟨p.2.1.1.1, p.2.2⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨C, ⟨⟨⟨I, hIne⟩, hC⟩, hI⟩⟩ => by
        subst hC; rfl }
  unfold Stage7DedekindZeta.idealCount classIdealCount
  rw [Nat.card_eq_fintype_card, Fintype.card_congr e, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun C _ => Nat.card_eq_fintype_card.symm

/-- **Full Total Ideal-Counting Asymptotic for `𝓞 (ImagQuadField d)`**:
`∑_{1 ≤ n ≤ ⌊t⌋₊} idealCount (ImagQuadField d) n = h(K) * (2 π / (w_K √|D|)) * t + O(√t)`! -/
theorem totalIdealCount_asymptotic {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 1 ≤ t →
      |∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (Stage7DedekindZeta.idealCount (ImagQuadField d) n : ℝ) -
        ((NumberField.classNumber (ImagQuadField d) : ℝ) *
          (2 * Real.pi / ((imagQuadUnitCard d : ℝ) * Real.sqrt (imagQuadDiscNat d : ℝ)))) * t| ≤
        M * Real.sqrt t := by
  classical
  choose M_C hM_pos hM_bd using fun C : ClassGroup (𝓞 (ImagQuadField d)) =>
    classIdealSum_asymptotic hd hsf C
  set c_d : ℝ := 2 * Real.pi / ((imagQuadUnitCard d : ℝ) * Real.sqrt (imagQuadDiscNat d : ℝ))
  set M : ℝ := ∑ C : ClassGroup (𝓞 (ImagQuadField d)), M_C C
  have hM_tot_pos : 0 < M := by
    refine Finset.sum_pos (fun C _ => hM_pos C) ?_
    exact ⟨1, Finset.mem_univ 1⟩
  refine ⟨M, hM_tot_pos, fun t ht => ?_⟩
  have hsum_eq : ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (Stage7DedekindZeta.idealCount (ImagQuadField d) n : ℝ) =
      ∑ C : ClassGroup (𝓞 (ImagQuadField d)), (classIdealSum d C ⌊t⌋₊ : ℝ) := by
    have h1 : ∀ n ∈ Finset.Icc 1 ⌊t⌋₊,
        (Stage7DedekindZeta.idealCount (ImagQuadField d) n : ℝ) =
          ∑ C : ClassGroup (𝓞 (ImagQuadField d)), (classIdealCount d C n : ℝ) := by
      intro n hn
      rw [idealCount_eq_sum_classIdealCount d (Finset.mem_Icc.mp hn).1, Nat.cast_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun C _ => ?_
    unfold classIdealSum
    rw [Nat.cast_sum]
  have hmain_eq : ((NumberField.classNumber (ImagQuadField d) : ℝ) * c_d) * t =
      ∑ _C : ClassGroup (𝓞 (ImagQuadField d)), c_d * t := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    unfold NumberField.classNumber
    ring
  rw [hsum_eq, hmain_eq, ← Finset.sum_sub_distrib]
  calc |∑ C : ClassGroup (𝓞 (ImagQuadField d)), ((classIdealSum d C ⌊t⌋₊ : ℝ) - c_d * t)|
      ≤ ∑ C : ClassGroup (𝓞 (ImagQuadField d)), |(classIdealSum d C ⌊t⌋₊ : ℝ) - c_d * t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ C : ClassGroup (𝓞 (ImagQuadField d)), M_C C * Real.sqrt t :=
        Finset.sum_le_sum fun C _ => hM_bd C t ht
    _ = M * Real.sqrt t := by rw [← Finset.sum_mul]

/-- **GENUINE ANALYTIC CLASS NUMBER FORMULA FOR ALL IMAGINARY QUADRATIC NUMBER FIELDS (`0` PROXIES,
`0` EXTRA HYPOTHESES!)**:
for EVERY squarefree `d > 0`, on Mathlib's NATIVE `NumberField.classNumber (ImagQuadField d)`:
`(NumberField.classNumber (ImagQuadField d) : ℝ) =
  (imagQuadUnitCard d : ℝ) * Real.sqrt (imagQuadDiscNat d : ℝ) / (2 * Real.pi) *
    (DirichletCharacter.LFunction (imagQuadChar d) 1).re`! -/
theorem dirichlet_classNumber_formula_imagQuad (d : ℕ) (hd : 0 < d) (hsf : Squarefree d) :
    (NumberField.classNumber (ImagQuadField d) : ℝ) =
      (imagQuadUnitCard d : ℝ) * Real.sqrt (imagQuadDiscNat d : ℝ) / (2 * Real.pi) *
        (DirichletCharacter.LFunction (imagQuadChar d) 1).re := by
  let a : ℕ → ℝ := fun n => if n = 0 then 0 else (Stage7DedekindZeta.idealCount (ImagQuadField d) n : ℝ)
  have ha0 : a 0 = 0 := if_pos rfl
  have ha_nn : ∀ n, 0 ≤ a n := fun n => by dsimp only [a]; split_ifs <;> positivity
  obtain ⟨M, hM, hAsymp⟩ := totalIdealCount_asymptotic hd hsf
  have hA : ∀ t : ℝ, 1 ≤ t →
      |∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n -
        ((NumberField.classNumber (ImagQuadField d) : ℝ) *
          (2 * Real.pi / ((imagQuadUnitCard d : ℝ) * Real.sqrt (imagQuadDiscNat d : ℝ)))) * t| ≤
        M * Real.sqrt t := by
    intro t ht
    have hcongr : ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n =
        ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (Stage7DedekindZeta.idealCount (ImagQuadField d) n : ℝ) :=
      Finset.sum_congr rfl fun n hn => by
        dsimp only [a]; rw [if_neg (by have := (Finset.mem_Icc.mp hn).1; omega)]
    rw [hcongr]
    exact hAsymp t ht
  have hLim_lattice := abelian_residue_of_sqrt_error ha0 ha_nn hM hA
  have hZeta_eq : ∀ σ : ℝ, 1 < σ →
      (Stage7DedekindZeta.dedekindZeta (ImagQuadField d) (σ : ℂ)).re =
        ∑' n : ℕ, a n * (n : ℝ) ^ (-σ) := by
    intro σ hσ
    rw [dedekindZeta_eq_tsum_complexDirichletTerm (ImagQuadField d) (s := (σ : ℂ)) (by simpa using hσ)]
    have hsum_c : Summable (Stage7DedekindZeta.complexDirichletTerm (ImagQuadField d) (σ : ℂ)) := by
      have h1 := (Stage7DedekindZeta.summable_and_tsum_realDirichletTerm_le (ImagQuadField d) hσ).1
      refine Summable.of_norm ?_
      refine h1.congr fun n => ?_
      unfold Stage7DedekindZeta.complexDirichletTerm Stage7DedekindZeta.realDirichletTerm
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, ite_false, norm_mul, Complex.norm_natCast,
          Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.neg_re,
          Complex.ofReal_re]
    have hmap := Complex.reCLM.map_tsum hsum_c
    change (∑' n : ℕ, Stage7DedekindZeta.complexDirichletTerm (ImagQuadField d) (σ : ℂ) n).re =
      ∑' n : ℕ, (Stage7DedekindZeta.complexDirichletTerm (ImagQuadField d) (σ : ℂ) n).re at hmap
    rw [hmap]
    refine tsum_congr fun n => ?_
    unfold Stage7DedekindZeta.complexDirichletTerm
    dsimp only [a]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ite_false]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_neg,
        ← Complex.ofReal_cpow (Nat.cast_nonneg n), ← Complex.ofReal_mul, Complex.ofReal_re]
  have hLim_zeta :
      Tendsto (fun σ : ℝ => (σ - 1) * (Stage7DedekindZeta.dedekindZeta (ImagQuadField d) (σ : ℂ)).re)
        (𝓝[>] (1 : ℝ))
        (nhds ((NumberField.classNumber (ImagQuadField d) : ℝ) *
          (2 * Real.pi / ((imagQuadUnitCard d : ℝ) * Real.sqrt (imagQuadDiscNat d : ℝ))))) := by
    refine hLim_lattice.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [hZeta_eq σ hσ]
  have hLim_L := dedekindZeta_imagQuad_residue_one_real hd hsf
  have hEq : (NumberField.classNumber (ImagQuadField d) : ℝ) *
      (2 * Real.pi / ((imagQuadUnitCard d : ℝ) * Real.sqrt (imagQuadDiscNat d : ℝ))) =
      (DirichletCharacter.LFunction (imagQuadChar d) 1).re :=
    tendsto_nhds_unique hLim_zeta hLim_L
  have hw_pos : (0 : ℝ) < (imagQuadUnitCard d : ℝ) := Nat.cast_pos.mpr (imagQuadUnitCard_pos d)
  have hsqD_pos : 0 < Real.sqrt (imagQuadDiscNat d : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (imagQuadDiscNat_pos d))
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  rw [← hEq]
  field_simp [hw_pos.ne', hsqD_pos.ne', hpi_pos.ne']

end AnalyticClassNumberFormula

/-! ## Section 6: Genuine Unconditional Heilbronn–Siegel & Gauss Class Number Problem on Native `NumberField.classNumber` -/

section HeilbronnSiegelAndGauss

/-- **GENUINE UNCONDITIONAL HEILBRONN–SIEGEL THEOREM ON MATHLIB'S NATIVE `NumberField.classNumber`
(`0` PROXIES, `0` EXCEPTIONS, `0` EXTRA HYPOTHESES!)**:
for EVERY `ε > 0`, there exists `C > 0` such that for EVERY squarefree `d > 0`:
`C * (d : ℝ) ^ (1 / 2 - ε) ≤ (NumberField.classNumber (ImagQuadField d) : ℝ)`! -/
theorem heilbronn_siegel_native_classNumber_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d → Squarefree d →
      C * (d : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (NumberField.classNumber (ImagQuadField d) : ℝ) := by
  obtain ⟨C₁, hC₁, hsiegel⟩ := Stage9LandauSiegel.siegel_theorem_L1_lower_bound ε hε
  refine ⟨C₁ / (Real.pi * (4 : ℝ) ^ ε), by positivity, fun d hd hsf => ?_⟩
  have hprim : (imagQuadChar d).IsPrimitive := imagQuadChar_isPrimitive hd hsf
  have hsq1 : (imagQuadChar d) ^ 2 = 1 := imagQuadChar_sq_eq_one d
  have hne1 : imagQuadChar d ≠ 1 := imagQuadChar_ne_one hd hsf
  have hL_lo : C₁ / (imagQuadDiscNat d : ℝ) ^ ε ≤
      (DirichletCharacter.LFunction (imagQuadChar d) 1).re :=
    hsiegel (imagQuadDiscNat d) (imagQuadChar d) hprim hsq1 hne1
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hD_ge : (d : ℝ) ≤ (imagQuadDiscNat d : ℝ) := by exact_mod_cast le_imagQuadDiscNat hd
  have hD_le : (imagQuadDiscNat d : ℝ) ≤ 4 * (d : ℝ) := by
    exact_mod_cast imagQuadDiscNat_le_four_mul hd
  have hD_pow_le : (imagQuadDiscNat d : ℝ) ^ ε ≤ (4 : ℝ) ^ ε * (d : ℝ) ^ ε := by
    calc (imagQuadDiscNat d : ℝ) ^ ε
        ≤ (4 * (d : ℝ)) ^ ε := Real.rpow_le_rpow (by positivity) hD_le hε.le
      _ = (4 : ℝ) ^ ε * (d : ℝ) ^ ε := Real.mul_rpow (by norm_num) hd_pos.le
  have hL_lo_d : C₁ / ((4 : ℝ) ^ ε * (d : ℝ) ^ ε) ≤
      (DirichletCharacter.LFunction (imagQuadChar d) 1).re := by
    refine le_trans ?_ hL_lo
    exact div_le_div_of_nonneg_left hC₁.le (Real.rpow_pos_of_pos (by linarith) _) hD_pow_le
  have hw_ge2 : (2 : ℝ) ≤ (imagQuadUnitCard d : ℝ) := by exact_mod_cast two_le_imagQuadUnitCard d
  have hsq_ge : Real.sqrt (d : ℝ) ≤ Real.sqrt (imagQuadDiscNat d : ℝ) := Real.sqrt_le_sqrt hD_ge
  have hcoeff_ge : Real.sqrt (d : ℝ) / Real.pi ≤
      (imagQuadUnitCard d : ℝ) * Real.sqrt (imagQuadDiscNat d : ℝ) / (2 * Real.pi) := by
    rw [div_le_div_iff₀ Real.pi_pos (by positivity)]
    have hmul := mul_le_mul hw_ge2 hsq_ge (Real.sqrt_nonneg _) (by positivity)
    nlinarith [Real.pi_pos]
  have hL_nn : 0 ≤ (DirichletCharacter.LFunction (imagQuadChar d) 1).re :=
    le_trans (by positivity) hL_lo_d
  rw [dirichlet_classNumber_formula_imagQuad d hd hsf]
  calc (C₁ / (Real.pi * (4 : ℝ) ^ ε)) * (d : ℝ) ^ ((1 : ℝ) / 2 - ε)
      = (Real.sqrt (d : ℝ) / Real.pi) * (C₁ / ((4 : ℝ) ^ ε * (d : ℝ) ^ ε)) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_sub hd_pos]
        have h4 : (4 : ℝ) ^ ε ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) ε).ne'
        have hdε : (d : ℝ) ^ ε ≠ 0 := (Real.rpow_pos_of_pos hd_pos ε).ne'
        field_simp [Real.pi_pos.ne', h4, hdε]
    _ ≤ (Real.sqrt (d : ℝ) / Real.pi) * (DirichletCharacter.LFunction (imagQuadChar d) 1).re :=
        mul_le_mul_of_nonneg_left hL_lo_d (by positivity)
    _ ≤ ((imagQuadUnitCard d : ℝ) * Real.sqrt (imagQuadDiscNat d : ℝ) / (2 * Real.pi)) *
          (DirichletCharacter.LFunction (imagQuadChar d) 1).re :=
        mul_le_mul_of_nonneg_right hcoeff_ge hL_nn

/-- **GENUINE UNCONDITIONAL SOLUTION OF GAUSS'S CLASS NUMBER PROBLEM ON MATHLIB'S NATIVE
`NumberField.classNumber` (`h(ℚ(√(-d))) → ∞`, `0` PROXIES, `0` EXTRA HYPOTHESES!)**:
for EVERY `M : ℕ`, there exists `D₀ : ℕ` such that for EVERY squarefree `d ≥ D₀`:
`M ≤ NumberField.classNumber (ImagQuadField d)`! -/
theorem gauss_classNumber_problem_native_unconditional :
    ∀ M : ℕ, ∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d → Squarefree d →
      M ≤ NumberField.classNumber (ImagQuadField d) := by
  obtain ⟨C, hC, hhs⟩ := heilbronn_siegel_native_classNumber_lower_bound (1 / 4) (by norm_num)
  intro M
  set A : ℝ := max (M : ℝ) 1 / C
  have hA_pos : 0 < A := by positivity
  refine ⟨Nat.ceil (A ^ 4) + 1, fun d hd hsf => ?_⟩
  have hd_pos : 0 < d := by omega
  have hlow := hhs d hd_pos hsf
  have hexp : ((1 : ℝ) / 2 - 1 / 4) = 1 / 4 := by norm_num
  rw [hexp] at hlow
  have hA4_le : A ^ 4 ≤ (d : ℝ) := by
    have h1 : A ^ 4 ≤ (Nat.ceil (A ^ 4) : ℝ) := Nat.le_ceil (A ^ 4)
    have h2 : (Nat.ceil (A ^ 4) : ℝ) ≤ ((Nat.ceil (A ^ 4) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ _
    have h3 : ((Nat.ceil (A ^ 4) + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hpow : A ≤ (d : ℝ) ^ ((1 : ℝ) / 4) := by
    have h := Real.rpow_le_rpow (by positivity) hA4_le (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast A 4, ← Real.rpow_mul hA_pos.le] at h
    norm_num at h
    exact h
  have hM_le : (M : ℝ) ≤ C * (d : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 : (M : ℝ) ≤ max (M : ℝ) 1 := le_max_left _ _
    have h2 : max (M : ℝ) 1 = C * A := by dsimp only [A]; field_simp [hC.ne']
    have h3 : C * A ≤ C * (d : ℝ) ^ ((1 : ℝ) / 4) := mul_le_mul_of_nonneg_left hpow hC.le
    linarith
  exact_mod_cast hM_le.trans hlow

/-- Explicit `ℚ`-algebra isomorphism confirming `ImagQuadField d ≃ₐ[ℚ] AdjoinRoot (X^2 + d)`
for every `d > 0`. -/
def imagQuadField_equiv_adjoinRoot (d : ℕ) (hd : 0 < d) :
    ImagQuadField d ≃ₐ[ℚ] AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) :=
  let P : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C (d : ℚ)
  have hroot_sq : AdjoinRoot.root P * AdjoinRoot.root P =
      (-(imagQuadParam d : ℚ)) • (1 : AdjoinRoot P) + (0 : ℚ) • AdjoinRoot.root P := by
    have hroot := AdjoinRoot.eval₂_root P
    simp only [P, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at hroot
    have hm : (imagQuadParam d : ℚ) = (d : ℚ) := by exact_mod_cast imagQuadParam_eq_self hd
    rw [hm, zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one, map_neg]
    change AdjoinRoot.root P * AdjoinRoot.root P = -(AdjoinRoot.of P (d : ℚ))
    rw [← sq]
    linear_combination hroot
  let f : ImagQuadField d →ₐ[ℚ] AdjoinRoot P :=
    QuadraticAlgebra.lift (R := ℚ) (a := -(imagQuadParam d : ℚ)) (b := (0 : ℚ))
      ⟨AdjoinRoot.root P, hroot_sq⟩
  let g : AdjoinRoot P →ₐ[ℚ] ImagQuadField d :=
    AdjoinRoot.liftAlgHom P (Algebra.ofId ℚ (ImagQuadField d))
      (QuadraticAlgebra.omega (R := ℚ) (a := -(imagQuadParam d : ℚ)) (b := (0 : ℚ))) (by
        have hm : (imagQuadParam d : ℚ) = (d : ℚ) := by exact_mod_cast imagQuadParam_eq_self hd
        dsimp only [P]
        rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
        ext
        · change (QuadraticAlgebra.omega ^ 2 : ImagQuadField d).re + (d : ℚ) = 0
          rw [sq]
          have hre : (QuadraticAlgebra.omega * QuadraticAlgebra.omega : ImagQuadField d).re =
              -(imagQuadParam d : ℚ) := by
            unfold QuadraticAlgebra.omega
            rw [QuadraticAlgebra.re_mul]
            ring
          rw [hre, hm]; ring
        · change (QuadraticAlgebra.omega ^ 2 : ImagQuadField d).im + 0 = 0
          rw [sq]
          unfold QuadraticAlgebra.omega
          rw [QuadraticAlgebra.im_mul]
          ring)
  have hf_omega :
      f (QuadraticAlgebra.omega (R := ℚ) (a := -(imagQuadParam d : ℚ)) (b := (0 : ℚ))) =
        AdjoinRoot.root P :=
    congrArg Subtype.val
      (Equiv.symm_apply_apply
        (QuadraticAlgebra.lift (R := ℚ) (a := -(imagQuadParam d : ℚ)) (b := (0 : ℚ)) (A := AdjoinRoot P))
        ⟨AdjoinRoot.root P, hroot_sq⟩)
  AlgEquiv.ofAlgHom f g
    (by
      apply AdjoinRoot.algHom_ext
      change f (g (AdjoinRoot.root P)) = AdjoinRoot.root P
      have hg : g (AdjoinRoot.root P) =
          QuadraticAlgebra.omega (R := ℚ) (a := -(imagQuadParam d : ℚ)) (b := (0 : ℚ)) :=
        AdjoinRoot.liftAlgHom_root _ _ _ _
      rw [hg]
      exact hf_omega)
    (by
      apply QuadraticAlgebra.algHom_ext
      change g (f (QuadraticAlgebra.omega (R := ℚ) (a := -(imagQuadParam d : ℚ)) (b := (0 : ℚ)))) =
        QuadraticAlgebra.omega (R := ℚ) (a := -(imagQuadParam d : ℚ)) (b := (0 : ℚ))
      rw [hf_omega]
      exact AdjoinRoot.liftAlgHom_root _ _ _ _)

end HeilbronnSiegelAndGauss

end RHDirect.GaussClassNumber
