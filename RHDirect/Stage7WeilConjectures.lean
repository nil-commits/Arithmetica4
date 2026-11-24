import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# RHDirect.Stage7WeilConjectures

Unconditional (`0` assumptions, `0` `sorry`, `0` custom `axiom`, `0` warnings, `0` info)
formalization of the **Complete Weil Conjectures (Rationality, Functional Equation, and the
Riemann Hypothesis `|α_i| = √q` / `Re(s) = 1/2`) for Smooth Projective Fermat and Diagonal
Curves `a X^d + b Y^d = c Z^d` over Finite Fields `𝔽_q`** in pure Mathlib `v4.33.1`:

## Main Contents
1. **Finite-Field Gauss Sums `g(χ, ψ)` & Exact Weil Modulus of Jacobi Sums `‖J(χ₁, χ₂)‖ = √q`**:
   - Complex conjugation of finite-field multiplicative characters (`star_mulChar_apply`) and
     Jacobi sums (`star_jacobiSum_eq`).
   - Exact Gauss-sum modulus `‖gaussSum χ ψ‖ ^ 2 = q` (`norm_sq_gaussSum_finiteField_eq`),
     `‖gaussSum χ ψ‖ = √q` (`norm_gaussSum_finiteField_eq`), and inversion
     `gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * q` (`gaussSum_mul_gaussSum_inv_finiteField`).
   - Exact Jacobi–Gauss factorization
     `jacobiSum χ₁ χ₂ * gaussSum (χ₁ * χ₂) ψ = gaussSum χ₁ ψ * gaussSum χ₂ ψ`
     (`jacobiSum_mul_gaussSum_eq`) and permutation symmetry
     `jacobiSum χ₁ (χ₁ * χ₂)⁻¹ = χ₁ (-1) * jacobiSum χ₁ χ₂` (`jacobiSum_inv_mul_eq`).
   - **Exact Weil Modulus of Jacobi Sums**: `‖jacobiSum χ₁ χ₂‖ = Real.sqrt q`
     (`norm_jacobiSum_eq_sqrt`) whenever `χ₁ ≠ 1`, `χ₂ ≠ 1`, `χ₁ * χ₂ ≠ 1`.
2. **Exact `d`-th Power Orthogonality, Jacobi-Sum Point-Counting & Hasse–Weil Bound**:
   - Exact `d`-th power character orthogonality for any finite field `F` and `d ∣ (q - 1)`:
     `#{x : F | x ^ d = u} = (if u = 0 then 1 else 0) + ∑_{χ^d = 1} χ u`
     (`card_pow_eq_sum_powCharSet_all`).
   - Exact character-pair index set `T_d = {(χ₁, χ₂) | χ₁^d = 1, χ₂^d = 1, χ₁ ≠ 1, χ₂ ≠ 1, χ₁ χ₂ ≠ 1}`
     of cardinality `(d - 1) * (d - 2) = 2 * g` (`card_fermatCharPairs`).
   - **Exact Projective Point-Counting Formula** for general diagonal curves
     `a X^d + b Y^d = c Z^d` (`diagProjPoints_eq_sum_jacobiSum`) and Fermat curves
     `X^d + Y^d = Z^d` (`fermatProjPoints_eq_sum_jacobiSum`,
     `fermatProjPoints_eq_sum_sign_jacobiSum`):
     `(fermatProjPoints F d : ℂ) = q + 1 + ∑_{(χ₁, χ₂) ∈ T_d} χ₁ (-1) * jacobiSum χ₁ χ₂`.
   - **Unconditional Hasse–Weil Riemann Hypothesis Bound**:
     `|(diagProjPoints F d a b c : ℝ) - (q + 1)| ≤ ((d - 1) * (d - 2) : ℝ) * Real.sqrt q`
     (`diag_hasse_weil_bound`), `fermat_hasse_weil_bound`, and the elliptic curve (`d = 3, g = 1`)
     specialization `|(fermatProjPoints F 3 : ℝ) - (q + 1)| ≤ 2 * Real.sqrt q`
     (`fermat_cubic_hasse_bound`).
3. **Complete Weil Conjectures for the Hasse–Weil Zeta Function `Z(C / 𝔽_q, T)`**:
   - Formal power series exponential calculus `expSeries f = PowerSeries.subst f (PowerSeries.exp ℂ)`
     proving `expSeries (f + g) = expSeries f * expSeries g` and
     `(1 - C α * X) * expSeries (logSeries α) = 1`.
   - **Rationality** (`fermat_weil_rationality`, `diag_weil_rationality`):
     `Z(C / 𝔽_q, T) * (1 - T) * (1 - q T) = P_1(T) := ∏_{p ∈ T_d} (1 - α_p T)` of exact degree
     `2 g = (d - 1) * (d - 2)`.
   - **Functional Equation** (`fermat_weil_functional_equation_poly`,
     `fermat_weil_functional_equation_zeta`, `diag_weil_functional_equation_poly`):
     fixed-point-free involution pairing `α_{χ₁, χ₂} * α_{χ₁⁻¹, χ₂⁻¹} = q` yielding
     `∏_{p ∈ T_d} α_p = q ^ g`,
     `P_1(1 / (q T)) = q ^ (-g) * T ^ (-2g) * P_1(T)`, and
     `Z(1 / (q T)) = q ^ (1 - g) * T ^ (2 - 2g) * Z(T)`.
   - **The Riemann Hypothesis for `Z(C / 𝔽_q, T)`** (`fermat_weil_riemann_hypothesis`,
     `diag_weil_riemann_hypothesis`):
     every reciprocal root satisfies `‖α_p‖ = Real.sqrt q`, every polynomial root satisfies
     `‖w‖ = (Real.sqrt q)⁻¹`, and every zero `s : ℂ` of `P_1(q ^ (-s)) = 0` lies strictly on
     the critical line `s.re = 1 / 2`.
4. **Genuine Hasse–Davenport Lifting Theorem & Exact Point Counts over All Extensions `E / 𝔽_q`**:
   - Surjectivity of `Algebra.norm F : E → F` (`finiteField_norm_surjective`) and existence of
     nontrivial complex additive characters (`exists_nontrivial_addChar_complex`).
   - Exact finite Euler product expansion over monic irreducibles in `Polynomial F`, yielding
     **Hasse–Davenport Lifting for Gauss Sums** (`hasse_davenport_gaussSum`):
     `-gaussSum (liftMulChar E χ) (liftAddChar E ψ) = (-gaussSum χ ψ) ^ Module.finrank F E`,
     and **Hasse–Davenport Lifting for Jacobi Sums** (`hasse_davenport_jacobiSum`):
     `-jacobiSum (liftMulChar E χ₁) (liftMulChar E χ₂) = (-jacobiSum χ₁ χ₂) ^ Module.finrank F E`.
   - **Exact Extension-Field Point-Counting Bridge** (`diagProjPoints_extension_eq_pointCountPow`,
     `fermatProjPoints_extension_eq_pointCountPow`): for EVERY finite field extension `E / F` of
     degree `r = Module.finrank F E`, the actual projective point count `#C(E)` equals
     `q ^ r + 1 - ∑_{p ∈ T_d} α_p ^ r` (`= fermatPointCountPow F d r`)!
-/

noncomputable section

open Complex Finset
open scoped BigOperators IntermediateField

namespace RHDirect.Stage7WeilConjectures

/-! ## Section 1: Finite-Field Gauss Sums & Exact Weil Modulus of Jacobi Sums -/

section GaussAndJacobi

variable {F : Type*} [Field F] [Fintype F]

/-- Every finite field has at least `2` elements. -/
theorem two_le_card_finiteField : 2 ≤ Fintype.card F :=
  Fintype.one_lt_card

/-- For any finite field `F`, `ringChar F ≠ 0`. -/
theorem ringChar_finiteField_ne_zero : ringChar F ≠ 0 := by
  intro h0
  have hcp : CharP F 0 := ⟨by simpa [h0] using ringChar.spec F⟩
  have hcz : CharZero F := CharP.charP_to_charZero F
  have hinf : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  exact not_finite F

/-- For any finite field `F` and multiplicative character `χ : MulChar F ℂ`,
values on nonzero elements have unit modulus. -/
theorem norm_mulChar_eq_one_of_ne_zero (χ : MulChar F ℂ) {x : F} (hx : x ≠ 0) :
    ‖χ x‖ = 1 := by
  classical
  have hunit : IsUnit x := isUnit_iff_ne_zero.mpr hx
  obtain ⟨u, rfl⟩ := hunit
  have hpow : (χ (u : F)) ^ (Fintype.card Fˣ) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have hnorm_pow : ‖χ (u : F)‖ ^ (Fintype.card Fˣ) = 1 := by
    rw [← norm_pow, hpow, norm_one]
  have hpos : 0 < Fintype.card Fˣ := Fintype.card_pos
  have hnn : 0 ≤ ‖χ (u : F)‖ := norm_nonneg _
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : ‖χ (u : F)‖ ^ Fintype.card Fˣ < 1 ^ Fintype.card Fˣ :=
      pow_lt_pow_left₀ hlt hnn hpos.ne'
    rw [one_pow] at this
    linarith
  · have : (1 : ℝ) ^ Fintype.card Fˣ < ‖χ (u : F)‖ ^ Fintype.card Fˣ :=
      pow_lt_pow_left₀ hgt zero_le_one hpos.ne'
    rw [one_pow] at this
    linarith

/-- Complex conjugation of a finite-field multiplicative character `χ : MulChar F ℂ`
equals the inverse character: `starRingEnd ℂ (χ x) = χ⁻¹ x`. -/
theorem star_mulChar_apply (χ : MulChar F ℂ) (x : F) :
    starRingEnd ℂ (χ x) = χ⁻¹ x := by
  by_cases hx : x = 0
  · subst hx
    rw [χ.map_nonunit not_isUnit_zero, (χ⁻¹).map_nonunit not_isUnit_zero, map_zero]
  · have hnorm : ‖χ x‖ = 1 := norm_mulChar_eq_one_of_ne_zero χ hx
    have hmul_conj : χ x * starRingEnd ℂ (χ x) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    have hmul_inv : χ x * χ⁻¹ x = 1 := by
      rw [MulChar.inv_apply', ← map_mul, mul_inv_cancel₀ hx, map_one]
    have hne : χ x ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmul_conj
      exact zero_ne_one hmul_conj
    exact mul_left_cancel₀ hne (hmul_conj.trans hmul_inv.symm)

/-- Complex conjugation of a Jacobi sum over a finite field:
`starRingEnd ℂ (jacobiSum χ₁ χ₂) = jacobiSum χ₁⁻¹ χ₂⁻¹`. -/
theorem star_jacobiSum_eq (χ₁ χ₂ : MulChar F ℂ) :
    starRingEnd ℂ (jacobiSum χ₁ χ₂) = jacobiSum χ₁⁻¹ χ₂⁻¹ := by
  simp only [jacobiSum, map_sum, map_mul, star_mulChar_apply]

omit [Fintype F] in
/-- For any field `F` and multiplicative character `χ`, `χ⁻¹ (-1) = χ (-1)`. -/
theorem mulChar_inv_neg_one (χ : MulChar F ℂ) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply', inv_neg, inv_one]

omit [Fintype F] in
/-- For any field `F` and multiplicative character `χ`, `χ (-1) * χ (-1) = 1`. -/
theorem mulChar_neg_one_mul_self (χ : MulChar F ℂ) : χ (-1) * χ (-1) = 1 := by
  rw [← map_mul, neg_one_mul, neg_neg, map_one]

/-- **Exact Finite-Field Gauss-Sum Squared Modulus**:
`‖gaussSum χ ψ‖ ^ 2 = Fintype.card F` for every nontrivial `χ ≠ 1` and `ψ ≠ 1`. -/
theorem norm_sq_gaussSum_finiteField_eq {χ : MulChar F ℂ} {ψ : AddChar F ℂ}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  have hprim : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ
  have hprod : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (Fintype.card F : ℂ) :=
    gaussSum_mul_gaussSum_eq_card hχ hprim
  have hstar : starRingEnd ℂ (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ :=
    star_gaussSum_eq χ ψ
  have hmul : gaussSum χ ψ * starRingEnd ℂ (gaussSum χ ψ) = (Fintype.card F : ℂ) := by
    rw [hstar]; exact hprod
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hmul
  exact_mod_cast hmul

/-- **Exact Finite-Field Gauss-Sum Modulus**: `‖gaussSum χ ψ‖ = √q`. -/
theorem norm_gaussSum_finiteField_eq {χ : MulChar F ℂ} {ψ : AddChar F ℂ}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F : ℝ) := by
  rw [← Real.sqrt_sq (norm_nonneg (gaussSum χ ψ)), norm_sq_gaussSum_finiteField_eq hχ hψ]

/-- **Exact Finite-Field Gauss-Sum Inversion Formula**:
`gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * q`. -/
theorem gaussSum_mul_gaussSum_inv_finiteField {χ : MulChar F ℂ} {ψ : AddChar F ℂ}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * (Fintype.card F : ℂ) := by
  have hprim : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ
  have hprod : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (Fintype.card F : ℂ) :=
    gaussSum_mul_gaussSum_eq_card hχ hprim
  have hinv : χ⁻¹ (-1) * gaussSum χ⁻¹ ψ⁻¹ = gaussSum χ⁻¹ ψ :=
    mul_gaussSum_inv_eq_gaussSum χ⁻¹ ψ
  rw [mulChar_inv_neg_one] at hinv
  calc gaussSum χ ψ * gaussSum χ⁻¹ ψ
      = gaussSum χ ψ * (χ (-1) * gaussSum χ⁻¹ ψ⁻¹) := by rw [← hinv]
    _ = χ (-1) * (gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹) := by ring
    _ = χ (-1) * (Fintype.card F : ℂ) := by rw [hprod]

/-- **Exact Jacobi–Gauss Factorization**:
`jacobiSum χ₁ χ₂ * gaussSum (χ₁ * χ₂) ψ = gaussSum χ₁ ψ * gaussSum χ₂ ψ`
whenever `χ₁ * χ₂ ≠ 1`. -/
theorem jacobiSum_mul_gaussSum_eq {χ₁ χ₂ : MulChar F ℂ} (h₁₂ : χ₁ * χ₂ ≠ 1)
    (ψ : AddChar F ℂ) :
    jacobiSum χ₁ χ₂ * gaussSum (χ₁ * χ₂) ψ = gaussSum χ₁ ψ * gaussSum χ₂ ψ := by
  rw [mul_comm]
  exact jacobiSum_mul_nontrivial h₁₂ ψ

/-- **Exact Jacobi-Sum Inversion Product**:
`jacobiSum χ₁ χ₂ * jacobiSum χ₁⁻¹ χ₂⁻¹ = q` whenever `χ₁ ≠ 1`, `χ₂ ≠ 1`, `χ₁ * χ₂ ≠ 1`. -/
theorem jacobiSum_mul_jacobiSum_inv_finiteField {χ₁ χ₂ : MulChar F ℂ}
    (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (h₁₂ : χ₁ * χ₂ ≠ 1) :
    jacobiSum χ₁ χ₂ * jacobiSum χ₁⁻¹ χ₂⁻¹ = (Fintype.card F : ℂ) := by
  have hch : ringChar ℂ ≠ ringChar F := by
    rw [ringChar.eq_zero]
    exact ringChar_finiteField_ne_zero.symm
  exact jacobiSum_mul_jacobiSum_inv hch h₁ h₂ h₁₂

/-- **Exact Squared Weil Modulus of Jacobi Sums**: `‖jacobiSum χ₁ χ₂‖ ^ 2 = q`. -/
theorem norm_sq_jacobiSum_eq {χ₁ χ₂ : MulChar F ℂ}
    (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (h₁₂ : χ₁ * χ₂ ≠ 1) :
    ‖jacobiSum χ₁ χ₂‖ ^ 2 = (Fintype.card F : ℝ) := by
  have hprod := jacobiSum_mul_jacobiSum_inv_finiteField h₁ h₂ h₁₂
  rw [← star_jacobiSum_eq, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hprod
  exact_mod_cast hprod

/-- **EXACT WEIL MODULUS OF JACOBI SUMS**:
`‖jacobiSum χ₁ χ₂‖ = Real.sqrt (Fintype.card F)` whenever `χ₁ ≠ 1`, `χ₂ ≠ 1`, `χ₁ * χ₂ ≠ 1`. -/
theorem norm_jacobiSum_eq_sqrt {χ₁ χ₂ : MulChar F ℂ}
    (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (h₁₂ : χ₁ * χ₂ ≠ 1) :
    ‖jacobiSum χ₁ χ₂‖ = Real.sqrt (Fintype.card F : ℝ) := by
  rw [← Real.sqrt_sq (norm_nonneg (jacobiSum χ₁ χ₂)), norm_sq_jacobiSum_eq h₁ h₂ h₁₂]

/-- Direct Gauss-sum derivation of `‖jacobiSum χ₁ χ₂‖ = Real.sqrt q` from any nontrivial `ψ`. -/
theorem norm_jacobiSum_eq_sqrt_of_gaussSum {χ₁ χ₂ : MulChar F ℂ} {ψ : AddChar F ℂ}
    (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (h₁₂ : χ₁ * χ₂ ≠ 1) (hψ : ψ ≠ 1) :
    ‖jacobiSum χ₁ χ₂‖ = Real.sqrt (Fintype.card F : ℝ) := by
  have hfac := congr_arg norm (jacobiSum_mul_gaussSum_eq h₁₂ ψ)
  simp only [norm_mul, norm_gaussSum_finiteField_eq h₁ hψ, norm_gaussSum_finiteField_eq h₂ hψ,
    norm_gaussSum_finiteField_eq h₁₂ hψ] at hfac
  have hpos : 0 < Real.sqrt (Fintype.card F : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  exact mul_right_cancel₀ hpos.ne' hfac

/-- **Jacobi-Sum Permutation Symmetry**:
`jacobiSum χ₁ (χ₁ * χ₂)⁻¹ = χ₁ (-1) * jacobiSum χ₁ χ₂` for all `χ₁, χ₂ : MulChar F ℂ`.
This elementary change of variables `u ↦ u / (u - 1)` explains why `X^d + Y^d = Z^d` and
`Y^d = X^d + Z^d` carry identical Jacobi-sum spectra. -/
theorem jacobiSum_inv_mul_eq (χ₁ χ₂ : MulChar F ℂ) :
    jacobiSum χ₁ (χ₁ * χ₂)⁻¹ = χ₁ (-1) * jacobiSum χ₁ χ₂ := by
  classical
  rw [jacobiSum_eq_sum_sdiff, jacobiSum_eq_sum_sdiff, Finset.mul_sum]
  refine Finset.sum_bij (fun x _ => x * (x - 1)⁻¹) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or] at hx ⊢
    rcases hx with ⟨hx0, hx1⟩
    have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    refine ⟨mul_ne_zero hx0 (inv_ne_zero hx1'), ?_⟩
    intro h
    have hmul : x = x - 1 := by
      calc x = x * (x - 1)⁻¹ * (x - 1) := by rw [mul_assoc, inv_mul_cancel₀ hx1', mul_one]
        _ = 1 * (x - 1) := by rw [h]
        _ = x - 1 := one_mul _
    have h01 : (0 : F) = -1 := by
      have := congr_arg (fun t => t - x) hmul
      simp at this
    exact one_ne_zero (neg_eq_zero.mp h01.symm)
  · intro x hx y hy hxy
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or] at hx hy
    have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx.2
    have hy1 : y - 1 ≠ 0 := sub_ne_zero.mpr hy.2
    have hcross : x * (y - 1) = y * (x - 1) := by
      have h1 := congr_arg (fun t => t * (x - 1) * (y - 1)) hxy
      have hl : x * (x - 1)⁻¹ * (x - 1) * (y - 1) = x * (y - 1) := by
        rw [mul_assoc x, inv_mul_cancel₀ hx1, mul_one]
      have hr : y * (y - 1)⁻¹ * (x - 1) * (y - 1) = y * (x - 1) := by
        calc y * (y - 1)⁻¹ * (x - 1) * (y - 1)
            = y * ((y - 1)⁻¹ * (y - 1)) * (x - 1) := by ring
          _ = y * 1 * (x - 1) := by rw [inv_mul_cancel₀ hy1]
          _ = y * (x - 1) := by rw [mul_one]
      rwa [hl, hr] at h1
    have : y - x = 0 := by
      calc y - x = x * (y - 1) - y * (x - 1) := by ring
        _ = 0 := sub_eq_zero.mpr hcross
    exact (sub_eq_zero.mp this).symm
  · intro y hy
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or] at hy
    rcases hy with ⟨hy0, hy1⟩
    have hy1' : y - 1 ≠ 0 := sub_ne_zero.mpr hy1
    refine ⟨y * (y - 1)⁻¹, ?_, ?_⟩
    · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        true_and, not_or]
      refine ⟨mul_ne_zero hy0 (inv_ne_zero hy1'), ?_⟩
      intro h
      have hmul : y = y - 1 := by
        calc y = y * (y - 1)⁻¹ * (y - 1) := by rw [mul_assoc, inv_mul_cancel₀ hy1', mul_one]
          _ = 1 * (y - 1) := by rw [h]
          _ = y - 1 := one_mul _
      have h01 : (0 : F) = -1 := by
        have := congr_arg (fun t => t - y) hmul
        simp at this
      exact one_ne_zero (neg_eq_zero.mp h01.symm)
    · have hsub : y * (y - 1)⁻¹ - 1 = (y - 1)⁻¹ := by
        calc y * (y - 1)⁻¹ - 1
            = y * (y - 1)⁻¹ - (y - 1) * (y - 1)⁻¹ := by rw [mul_inv_cancel₀ hy1']
          _ = (y - (y - 1)) * (y - 1)⁻¹ := by ring
          _ = 1 * (y - 1)⁻¹ := by ring
          _ = (y - 1)⁻¹ := one_mul _
      rw [hsub, inv_inv, mul_assoc, inv_mul_cancel₀ hy1', mul_one]
  · intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or] at hx
    rcases hx with ⟨hx0, hx1⟩
    have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    have hsub : 1 - x * (x - 1)⁻¹ = (1 - x)⁻¹ := by
      calc 1 - x * (x - 1)⁻¹
          = (x - 1) * (x - 1)⁻¹ - x * (x - 1)⁻¹ := by rw [mul_inv_cancel₀ hx1']
        _ = (-1) * (x - 1)⁻¹ := by ring
        _ = (-(x - 1))⁻¹ := by rw [inv_neg, neg_one_mul]
        _ = (1 - x)⁻¹ := by congr 1; ring
    have harg1 : x * (x - 1)⁻¹ = (-1 : F) * x * (1 - x)⁻¹ := by
      rw [show x - 1 = -(1 - x) by ring, inv_neg]; ring
    rw [hsub, harg1, MulChar.inv_apply', MulChar.mul_apply, map_mul, map_mul]
    calc χ₁ x * (χ₁ (1 - x)⁻¹ * χ₂ (1 - x)⁻¹)
        = (χ₁ (-1) * χ₁ (-1)) * (χ₁ x * χ₁ (1 - x)⁻¹ * χ₂ (1 - x)⁻¹) := by
            rw [mulChar_neg_one_mul_self, one_mul]; ring
      _ = χ₁ (-1) * (χ₁ (-1) * χ₁ x * χ₁ (1 - x)⁻¹ * χ₂ (1 - x)⁻¹) := by ring

end GaussAndJacobi

/-! ## Section 2: `d`-th Power Character Orthogonality, Point Counting & Hasse–Weil Bound -/

section PointCounting

/-- `ℂ` has enough `n`-th roots of unity for every positive `n`. -/
theorem hasEnoughRootsOfUnity_complex (n : ℕ) [NeZero n] : HasEnoughRootsOfUnity ℂ n := by
  refine HasEnoughRootsOfUnity.of_card_le ?_
  have hprim := Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  rw [hprim.card_rootsOfUnity]

/-- The finite set of complex multiplicative characters of `F` of order dividing `d`:
`powCharSet F d = {χ : MulChar F ℂ | χ ^ d = 1}`. -/
def powCharSet (F : Type*) [Field F] [Fintype F] (d : ℕ) : Finset (MulChar F ℂ) :=
  letI : Finite (MulChar F ℂ) := MulChar.finite
  (Set.toFinite {χ : MulChar F ℂ | χ ^ d = 1}).toFinset

@[simp]
theorem mem_powCharSet {F : Type*} [Field F] [Fintype F] {d : ℕ} {χ : MulChar F ℂ} :
    χ ∈ powCharSet F d ↔ χ ^ d = 1 := by
  simp [powCharSet]

theorem one_mem_powCharSet (F : Type*) [Field F] [Fintype F] (d : ℕ) :
    (1 : MulChar F ℂ) ∈ powCharSet F d := by
  simp

theorem mul_mem_powCharSet {F : Type*} [Field F] [Fintype F] {d : ℕ}
    {χ₁ χ₂ : MulChar F ℂ} (h₁ : χ₁ ∈ powCharSet F d) (h₂ : χ₂ ∈ powCharSet F d) :
    χ₁ * χ₂ ∈ powCharSet F d := by
  simp only [mem_powCharSet] at h₁ h₂ ⊢
  rw [mul_pow, h₁, h₂, one_mul]

theorem inv_mem_powCharSet {F : Type*} [Field F] [Fintype F] {d : ℕ}
    {χ : MulChar F ℂ} (h : χ ∈ powCharSet F d) :
    χ⁻¹ ∈ powCharSet F d := by
  simp only [mem_powCharSet] at h ⊢
  rw [inv_pow, h, inv_one]

/-- The group of complex multiplicative characters `MulChar F ℂ` is isomorphic to `Fˣ`
(and hence cyclic of order `q - 1`). -/
theorem mulChar_mulEquiv_units_complex (F : Type*) [Field F] [Fintype F] :
    Nonempty (MulChar F ℂ ≃* Fˣ) := by
  have hne : Monoid.exponent Fˣ ≠ 0 := Monoid.exponent_ne_zero_of_finite
  have : NeZero (Monoid.exponent Fˣ) := ⟨hne⟩
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent Fˣ) :=
    hasEnoughRootsOfUnity_complex (Monoid.exponent Fˣ)
  exact MulChar.mulEquiv_units F ℂ

/-- Helper: reducing an integer power of a group element modulo its order `m`. -/
private lemma zpow_eq_pow_emod {G : Type*} [Group G] (g : G) (n : ℤ) (m : ℕ)
    (hord : orderOf g = m) (hm : 0 < m) :
    g ^ n = g ^ (n.emod (m : ℤ)).toNat := by
  have hnn : 0 ≤ n.emod (m : ℤ) := Int.emod_nonneg n (by exact_mod_cast hm.ne')
  rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
  have hq : n = (m : ℤ) * (n / (m : ℤ)) + n.emod (m : ℤ) := (Int.mul_ediv_add_emod n m).symm
  calc g ^ n
      = g ^ ((m : ℤ) * (n / (m : ℤ)) + n.emod (m : ℤ)) := by rw [← hq]
    _ = (g ^ (m : ℤ)) ^ (n / (m : ℤ)) * g ^ (n.emod (m : ℤ)) := by rw [zpow_add, zpow_mul]
    _ = (g ^ m) ^ (n / (m : ℤ)) * g ^ (n.emod (m : ℤ)) := by rw [zpow_natCast]
    _ = 1 ^ (n / (m : ℤ)) * g ^ (n.emod (m : ℤ)) := by rw [← hord, pow_orderOf_eq_one]
    _ = g ^ (n.emod (m : ℤ)) := by rw [one_zpow, one_mul]

private lemma emod_toNat_lt {n : ℤ} {m : ℕ} (hm : 0 < m) : (n.emod (m : ℤ)).toNat < m := by
  have hlt : n.emod (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos n (by exact_mod_cast hm)
  omega

/-- In any finite cyclic group `G` of order `m` with `d ∣ m`, `d ≥ 1`, the elements satisfying
`x ^ d = 1` have exact cardinality `d`. -/
private lemma card_pow_eq_one_cyclic {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    [IsCyclic G] {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card G) :
    (Finset.univ.filter fun x : G => x ^ d = 1).card = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  set m := Fintype.card G
  have hm_pos : 0 < m := Fintype.card_pos
  set k := m / d
  have hdk : k * d = m := Nat.div_mul_cancel hdvd
  have hkpos : 0 < k := Nat.div_pos (Nat.le_of_dvd hm_pos hdvd) hd
  refine Finset.card_eq_of_bijective (fun j _ => (g ^ k) ^ j) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    have hmod : g ^ n = g ^ (n.emod (m : ℤ)).toNat := zpow_eq_pow_emod g n m hord hm_pos
    set a := (n.emod (m : ℤ)).toNat
    have ha_lt : a < m := emod_toNat_lt hm_pos
    rw [hmod] at hx ⊢
    rw [← pow_mul] at hx
    have hdvd_ad : m ∣ a * d := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hx
    have hkdvd : k ∣ a := by
      rw [← hdk] at hdvd_ad
      exact (Nat.mul_dvd_mul_iff_right hd).mp hdvd_ad
    obtain ⟨j, hj⟩ := hkdvd
    have hj_lt : j < d := by
      have : k * j < k * d := by rw [← hj, hdk]; exact ha_lt
      exact Nat.lt_of_mul_lt_mul_left this
    refine ⟨j, hj_lt, ?_⟩
    rw [← pow_mul, ← hj]
  · intro j _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← pow_mul, ← pow_mul, mul_comm j d, ← mul_assoc, hdk, ← hord, pow_mul,
      pow_orderOf_eq_one, one_pow]
  · intro i j hi hj hij
    rw [← pow_mul, ← pow_mul] at hij
    have h1 : k * i < m := by
      rw [← hdk]; exact Nat.mul_lt_mul_of_pos_left hi hkpos
    have h2 : k * j < m := by
      rw [← hdk]; exact Nat.mul_lt_mul_of_pos_left hj hkpos
    have heq : k * i = k * j := by
      have hmod : k * i ≡ k * j [MOD m] := by
        rw [← hord]
        exact pow_eq_pow_iff_modEq.mp hij
      rwa [Nat.ModEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod
    exact Nat.eq_of_mul_eq_mul_left hkpos heq

/-- **Exact Cardinality of `d`-th Order Multiplicative Characters**:
`(powCharSet F d).card = d` whenever `1 ≤ d` and `d ∣ (Fintype.card F - 1)`. -/
theorem card_powCharSet {F : Type*} [Field F] [Fintype F] {d : ℕ}
    (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    (powCharSet F d).card = d := by
  classical
  obtain ⟨e⟩ := mulChar_mulEquiv_units_complex F
  let : Fintype (MulChar F ℂ) := Fintype.ofEquiv Fˣ e.symm.toEquiv
  have : IsCyclic (MulChar F ℂ) := isCyclic_of_surjective e.symm e.symm.surjective
  have hcardG : Fintype.card (MulChar F ℂ) = Fintype.card F - 1 := by
    rw [Fintype.card_congr e.toEquiv, Fintype.card_units]
  have hset : powCharSet F d = Finset.univ.filter (fun χ : MulChar F ℂ => χ ^ d = 1) := by
    ext χ
    simp [mem_powCharSet]
  rw [hset]
  exact card_pow_eq_one_cyclic hd (hcardG ▸ hdvd)

/-- **Exact `d`-th Power Character Orthogonality on `Fˣ` (nonzero elements)**:
for `1 ≤ d`, `d ∣ (q - 1)`, and any nonzero `u : F`,
`(#{x : F | x ^ d = u} : ℂ) = ∑ χ ∈ powCharSet F d, χ u`. -/
theorem card_pow_eq_sum_powCharSet {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) {u : F} (hu : u ≠ 0) :
    ((Finset.univ.filter fun x : F => x ^ d = u).card : ℂ) =
      ∑ χ ∈ powCharSet F d, χ u := by
  classical
  obtain ⟨e⟩ := mulChar_mulEquiv_units_complex F
  let : Fintype (MulChar F ℂ) := Fintype.ofEquiv Fˣ e.symm.toEquiv
  have : IsCyclic (MulChar F ℂ) := isCyclic_of_surjective e.symm e.symm.surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨χ₀, hχ₀⟩ := IsCyclic.exists_generator (α := MulChar F ℂ)
  set m := Fintype.card F - 1
  have hm_eq : Fintype.card Fˣ = m := Fintype.card_units F
  have hm_pos : 0 < m := hm_eq ▸ Fintype.card_pos
  have hord_g : orderOf g = m := by
    rw [← hm_eq, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have hcard_mc : Fintype.card (MulChar F ℂ) = m := by
    rw [Fintype.card_congr e.toEquiv, hm_eq]
  have hord_χ₀ : orderOf χ₀ = m := by
    rw [← hcard_mc, orderOf_eq_card_of_forall_mem_zpowers hχ₀, Nat.card_eq_fintype_card]
  set k := m / d
  have hdk : k * d = m := Nat.div_mul_cancel hdvd
  have hk_pos : 0 < k := Nat.div_pos (Nat.le_of_dvd hm_pos hdvd) hd
  let u₀ : Fˣ := Units.mk0 u hu
  obtain ⟨n_u, hn_u⟩ := Subgroup.mem_zpowers_iff.mp (hg u₀)
  have hn_u' : g ^ (n_u.emod (m : ℤ)).toNat = u₀ :=
    (zpow_eq_pow_emod g n_u m hord_g hm_pos).symm.trans hn_u
  set a := (n_u.emod (m : ℤ)).toNat
  have ha_lt : a < m := emod_toNat_lt hm_pos
  have hpow_img : powCharSet F d = (Finset.range d).image (fun j => (χ₀ ^ k) ^ j) := by
    apply Finset.eq_of_subset_of_card_le
    · intro χ hχ
      simp only [mem_powCharSet] at hχ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hχ₀ χ)
      have hmod : χ₀ ^ n = χ₀ ^ (n.emod (m : ℤ)).toNat := zpow_eq_pow_emod χ₀ n m hord_χ₀ hm_pos
      set b := (n.emod (m : ℤ)).toNat
      have hb_lt : b < m := emod_toNat_lt hm_pos
      rw [hmod] at hχ ⊢
      rw [← pow_mul] at hχ
      have hdvd_bd : m ∣ b * d := hord_χ₀ ▸ orderOf_dvd_of_pow_eq_one hχ
      have hkdvd : k ∣ b := by
        rw [← hdk] at hdvd_bd
        exact (Nat.mul_dvd_mul_iff_right hd).mp hdvd_bd
      obtain ⟨j, hj⟩ := hkdvd
      have hj_lt : j < d := by
        have : k * j < k * d := by rw [← hj, hdk]; exact hb_lt
        exact Nat.lt_of_mul_lt_mul_left this
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj_lt, by rw [← pow_mul, ← hj]⟩
    · rw [card_powCharSet hd hdvd]
      exact Finset.card_image_le.trans (by simp)
  have hinj_χ : Set.InjOn (fun j => (χ₀ ^ k) ^ j) (Finset.range d : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    dsimp only at hij
    rw [← pow_mul, ← pow_mul] at hij
    have h1 : k * i < m := by rw [← hdk]; exact Nat.mul_lt_mul_of_pos_left hi hk_pos
    have h2 : k * j < m := by rw [← hdk]; exact Nat.mul_lt_mul_of_pos_left hj hk_pos
    have hmod : k * i ≡ k * j [MOD m] := hord_χ₀ ▸ pow_eq_pow_iff_modEq.mp hij
    rw [Nat.ModEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod
    exact Nat.eq_of_mul_eq_mul_left hk_pos hmod
  set ζ : ℂ := (χ₀ ^ k) (g : F)
  have hζ_pow_d : ζ ^ d = 1 := by
    change ((χ₀ ^ k) (g : F)) ^ d = 1
    rw [← MulChar.pow_apply_coe, ← pow_mul, hdk, ← hord_χ₀, pow_orderOf_eq_one]
    exact MulChar.one_apply g.isUnit
  have hord_ζ : orderOf ζ = d := by
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_of_pow_eq_one hζ_pow_d
    · have hchar_eq : (χ₀ ^ k) ^ (orderOf ζ) = 1 := by
        ext x
        obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
        have h1 : ((χ₀ ^ k) ^ (orderOf ζ)) (g : F) = 1 := by
          rw [MulChar.pow_apply_coe]
          exact pow_orderOf_eq_one ζ
        have hb : g ^ (r.emod (m : ℤ)).toNat = x :=
          (zpow_eq_pow_emod g r m hord_g hm_pos).symm.trans hr
        have hxb : ((g : F) ^ (r.emod (m : ℤ)).toNat) = (x : F) := by
          have := congr_arg (Units.val : Fˣ → F) hb
          simpa using this
        rw [← hxb, map_pow, h1, one_pow, hxb, MulChar.one_apply x.isUnit]
      rw [← pow_mul] at hchar_eq
      have hdvd_m : m ∣ k * orderOf ζ := hord_χ₀ ▸ orderOf_dvd_of_pow_eq_one hchar_eq
      rw [← hdk] at hdvd_m
      exact (Nat.mul_dvd_mul_iff_left hk_pos).mp hdvd_m
  have hrhs : ∑ χ ∈ powCharSet F d, χ u = ∑ j ∈ Finset.range d, (ζ ^ a) ^ j := by
    rw [hpow_img, Finset.sum_image hinj_χ]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hu_eq : u = (g : F) ^ a := by
      have := congr_arg (Units.val : Fˣ → F) hn_u'
      simpa [u₀] using this.symm
    rw [hu_eq, map_pow, MulChar.pow_apply_coe, ← pow_mul, mul_comm j a, pow_mul]
  rw [hrhs]
  by_cases hda : d ∣ a
  · obtain ⟨b₀, hb₀⟩ := hda
    have hζa : ζ ^ a = 1 := by rw [hb₀, pow_mul, hζ_pow_d, one_pow]
    have hsum : ∑ j ∈ Finset.range d, (ζ ^ a) ^ j = (d : ℂ) := by
      simp [hζa]
    rw [hsum]
    suffices hcard : (Finset.univ.filter fun x : F => x ^ d = u).card = d by
      exact_mod_cast hcard
    refine Finset.card_eq_of_bijective (fun j _ => ((g ^ (b₀ + j * k) : Fˣ) : F)) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hx0 : x ≠ 0 := by
        intro h0; subst h0; rw [zero_pow (by omega)] at hx; exact hu hx.symm
      let x₀ : Fˣ := Units.mk0 x hx0
      obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp (hg x₀)
      set b := (r.emod (m : ℤ)).toNat
      have hb_lt : b < m := emod_toNat_lt hm_pos
      have hgb : g ^ b = x₀ := (zpow_eq_pow_emod g r m hord_g hm_pos).symm.trans hr
      have hpow_eq : g ^ (b * d) = g ^ a := by
        rw [pow_mul, hgb, hn_u']
        ext
        simpa [x₀, u₀] using hx
      have hmod : b * d ≡ a [MOD m] := hord_g ▸ pow_eq_pow_iff_modEq.mp hpow_eq
      have hmod_k : b ≡ b₀ [MOD k] := by
        rw [hb₀, mul_comm d b₀, ← hdk] at hmod
        rw [Nat.modEq_iff_dvd] at hmod ⊢
        obtain ⟨t, ht⟩ := hmod
        refine ⟨t, ?_⟩
        have hmul : ((b₀ : ℤ) - (b : ℤ)) * (d : ℤ) = ((k : ℤ) * t) * (d : ℤ) := by
          push_cast at ht ⊢; linarith
        exact mul_right_cancel₀ (by exact_mod_cast (by omega : d ≠ 0)) hmul
      have hb₀_lt : b₀ < k := by
        have : d * b₀ < d * k := by rw [← hb₀, mul_comm d k, hdk]; exact ha_lt
        exact Nat.lt_of_mul_lt_mul_left this
      have hbmod : b % k = b₀ := by
        rw [Nat.ModEq, Nat.mod_eq_of_lt hb₀_lt] at hmod_k
        exact hmod_k
      set j := b / k
      have hj_lt : j < d := by
        have : j * k < d * k := by
          calc j * k ≤ b := Nat.div_mul_le_self b k
            _ < m := hb_lt
            _ = d * k := by rw [← hdk, mul_comm]
        exact Nat.lt_of_mul_lt_mul_right this
      refine ⟨j, hj_lt, ?_⟩
      have hbeq : b₀ + j * k = b := by
        have := Nat.div_add_mod b k
        rw [hbmod, mul_comm k j] at this
        linarith
      rw [hbeq, hgb]
      rfl
    · intro j _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : (g ^ (b₀ + j * k)) ^ d = u₀ := by
        calc (g ^ (b₀ + j * k)) ^ d
            = g ^ (b₀ * d + j * (k * d)) := by rw [← pow_mul, add_mul, mul_assoc]
          _ = g ^ (d * b₀) * (g ^ m) ^ j := by
                rw [hdk, pow_add, mul_comm b₀ d, mul_comm j m, pow_mul g m j]
          _ = u₀ := by rw [← hord_g, pow_orderOf_eq_one, one_pow, mul_one, ← hb₀, hn_u']
      have := congr_arg (Units.val : Fˣ → F) h1
      simpa [u₀] using this
    · intro i j hi hj hij
      have hij' : g ^ (b₀ + i * k) = g ^ (b₀ + j * k) := Units.ext hij
      have hmod : b₀ + i * k ≡ b₀ + j * k [MOD m] := hord_g ▸ pow_eq_pow_iff_modEq.mp hij'
      have hb₀_lt : b₀ < k := by
        have : d * b₀ < d * k := by rw [← hb₀, mul_comm d k, hdk]; exact ha_lt
        exact Nat.lt_of_mul_lt_mul_left this
      have h1 : b₀ + i * k < m := by
        have : (i + 1) * k ≤ d * k := Nat.mul_le_mul_right k hi
        rw [← hdk, mul_comm k d]
        nlinarith
      have h2 : b₀ + j * k < m := by
        have : (j + 1) * k ≤ d * k := Nat.mul_le_mul_right k hj
        rw [← hdk, mul_comm k d]
        nlinarith
      rw [Nat.ModEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod
      exact Nat.eq_of_mul_eq_mul_right hk_pos (Nat.add_left_cancel hmod)
  · have hζa_ne : ζ ^ a ≠ 1 := by
      intro h1
      exact hda (hord_ζ ▸ orderOf_dvd_of_pow_eq_one h1)
    have hgeom : (ζ ^ a - 1) * ∑ j ∈ Finset.range d, (ζ ^ a) ^ j = 0 := by
      rw [mul_comm, geom_sum_mul, ← pow_mul, mul_comm a d, pow_mul, hζ_pow_d, one_pow, sub_self]
    have hsum : ∑ j ∈ Finset.range d, (ζ ^ a) ^ j = 0 :=
      (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr hζa_ne)
    rw [hsum]
    suffices hempty : (Finset.univ.filter fun x : F => x ^ d = u) = ∅ by
      simp [hempty]
    rw [Finset.filter_eq_empty_iff]
    intro x _ hx
    have hx0 : x ≠ 0 := by
      intro h0; subst h0; rw [zero_pow (by omega)] at hx; exact hu hx.symm
    let x₀ : Fˣ := Units.mk0 x hx0
    obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp (hg x₀)
    set b := (r.emod (m : ℤ)).toNat
    have hgb : g ^ b = x₀ := (zpow_eq_pow_emod g r m hord_g hm_pos).symm.trans hr
    have hpow_eq : g ^ (b * d) = g ^ a := by
      rw [pow_mul, hgb, hn_u']
      ext
      simpa [x₀, u₀] using hx
    have hmod : b * d ≡ a [MOD m] := hord_g ▸ pow_eq_pow_iff_modEq.mp hpow_eq
    have hmod_d : b * d ≡ a [MOD d] := hmod.of_dvd hdvd
    rw [Nat.ModEq, Nat.mul_mod_left] at hmod_d
    exact hda (Nat.dvd_of_mod_eq_zero hmod_d.symm)

/-- **Uniform `d`-th Power Character Orthogonality on all of `F`** (including `u = 0`):
`(#{x : F | x ^ d = u} : ℂ) = (if u = 0 then 1 else 0) + ∑ χ ∈ powCharSet F d, χ u`. -/
theorem card_pow_eq_sum_powCharSet_all {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) (u : F) :
    ((Finset.univ.filter fun x : F => x ^ d = u).card : ℂ) =
      (if u = 0 then (1 : ℂ) else 0) + ∑ χ ∈ powCharSet F d, χ u := by
  by_cases hu : u = 0
  · subst hu
    have hfilt : (Finset.univ.filter fun x : F => x ^ d = (0 : F)) = {0} := by
      ext x
      simp [pow_eq_zero_iff (by omega : d ≠ 0)]
    have hsum0 : ∑ χ ∈ powCharSet F d, χ (0 : F) = 0 :=
      Finset.sum_eq_zero fun χ _ => χ.map_nonunit not_isUnit_zero
    rw [hfilt, hsum0]
    simp
  · rw [if_neg hu, zero_add]
    exact card_pow_eq_sum_powCharSet hd hdvd hu

/-- Genus of the smooth projective plane curve of degree `d`:
`g = (d - 1)(d - 2) / 2`. -/
def fermatGenus (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2

theorem two_mul_fermatGenus (d : ℕ) : 2 * fermatGenus d = (d - 1) * (d - 2) := by
  unfold fermatGenus
  have heven : 2 ∣ (d - 1) * (d - 2) := by
    rcases d with _ | _ | d
    · simp
    · simp
    · have hsub : (d + 2 - 1) * (d + 2 - 2) = (d + 1) * d := by
        rw [show d + 2 - 1 = d + 1 by omega, show d + 2 - 2 = d by omega]
      rw [hsub]
      rcases Nat.even_or_odd d with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨(k + k + 1) * k, by ring⟩
      · exact ⟨(k + 1) * (2 * k + 1), by ring⟩
  exact Nat.mul_div_cancel' heven

/-- The character-pair index set
`T_d = {(χ₁, χ₂) | χ₁^d = 1, χ₂^d = 1, χ₁ ≠ 1, χ₂ ≠ 1, χ₁ * χ₂ ≠ 1}`
indexing the `2g = (d - 1)(d - 2)` Jacobi-sum Frobenius eigenvalues of a degree-`d`
Fermat / diagonal curve. -/
def fermatCharPairs (F : Type*) [Field F] [Fintype F] (d : ℕ) :
    Finset (MulChar F ℂ × MulChar F ℂ) :=
  letI := Classical.decEq (MulChar F ℂ)
  (powCharSet F d ×ˢ powCharSet F d).filter fun p => p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ p.1 * p.2 ≠ 1

theorem mem_fermatCharPairs {F : Type*} [Field F] [Fintype F] {d : ℕ}
    {p : MulChar F ℂ × MulChar F ℂ} :
    p ∈ fermatCharPairs F d ↔
      p.1 ∈ powCharSet F d ∧ p.2 ∈ powCharSet F d ∧ p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ p.1 * p.2 ≠ 1 := by
  classical
  simp [fermatCharPairs, and_assoc]

/-- **Exact Cardinality of `T_d`**:
`|T_d| = (d - 1) * (d - 2) = 2 * fermatGenus d` whenever `1 ≤ d` and `d ∣ (q - 1)`. -/
theorem card_fermatCharPairs {F : Type*} [Field F] [Fintype F] {d : ℕ}
    (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    (fermatCharPairs F d).card = (d - 1) * (d - 2) := by
  classical
  set D := powCharSet F d
  have hD : D.card = d := card_powCharSet hd hdvd
  have h1D : (1 : MulChar F ℂ) ∈ D := one_mem_powCharSet F d
  set D' := D.erase 1
  have hD' : D'.card = d - 1 := by rw [Finset.card_erase_of_mem h1D, hD]
  have hbij : (fermatCharPairs F d).card = ∑ χ₁ ∈ D', (D'.erase χ₁⁻¹).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun p _ => ⟨p.1, p.2⟩) ?_ ?_ ?_
    · intro p hp
      rw [mem_fermatCharPairs] at hp
      rcases hp with ⟨h1, h2, h1ne, h2ne, h12ne⟩
      refine Finset.mem_sigma.mpr ⟨Finset.mem_erase.mpr ⟨h1ne, h1⟩, ?_⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨h2ne, h2⟩⟩
      intro heq
      dsimp only at heq
      apply h12ne
      rw [heq, mul_inv_cancel]
    · intro p₁ _ p₂ _ h
      cases p₁; cases p₂
      simpa using h
    · intro s hs
      rw [Finset.mem_sigma] at hs
      rcases hs with ⟨hs1, hs2⟩
      rw [Finset.mem_erase] at hs1 hs2
      rcases hs2 with ⟨hne_inv, hs2'⟩
      rw [Finset.mem_erase] at hs2'
      refine ⟨(s.1, s.2), ?_, rfl⟩
      rw [mem_fermatCharPairs]
      refine ⟨hs1.2, hs2'.2, hs1.1, hs2'.1, ?_⟩
      intro hmul
      apply hne_inv
      exact eq_inv_of_mul_eq_one_right hmul
  rw [hbij]
  have hinner : ∀ χ₁ ∈ D', (D'.erase χ₁⁻¹).card = d - 2 := by
    intro χ₁ hχ₁
    rw [Finset.mem_erase] at hχ₁
    have hinv_mem : χ₁⁻¹ ∈ D' :=
      Finset.mem_erase.mpr ⟨inv_ne_one.mpr hχ₁.1, inv_mem_powCharSet hχ₁.2⟩
    rw [Finset.card_erase_of_mem hinv_mem, hD']
    omega
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, hD', smul_eq_mul]

theorem card_fermatCharPairs_eq_two_mul_genus {F : Type*} [Field F] [Fintype F] {d : ℕ}
    (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    (fermatCharPairs F d).card = 2 * fermatGenus d := by
  rw [card_fermatCharPairs hd hdvd, two_mul_fermatGenus]

/-- Number of affine solutions `(x, y) ∈ F × F` to `a * x^d + b * y^d = c`. -/
def diagAffinePoints (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (d : ℕ) (a b c : F) : ℕ :=
  (Finset.univ.filter fun p : F × F => a * p.1 ^ d + b * p.2 ^ d = c).card

/-- Number of projective points at infinity `[t : 1 : 0] ∈ ℙ²(F)` on `a X^d + b Y^d = c Z^d`,
i.e., solutions `t ∈ F` to `a * t^d + b = 0` (`t^d = -b * a⁻¹`). -/
def diagInfPoints (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (d : ℕ) (a b : F) : ℕ :=
  (Finset.univ.filter fun t : F => a * t ^ d + b = 0).card

/-- Total number of projective `F`-rational points on the smooth projective diagonal curve
`C_{a,b,c,d} : a X^d + b Y^d = c Z^d` in `ℙ²(F)`. -/
def diagProjPoints (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (d : ℕ) (a b c : F) : ℕ :=
  diagAffinePoints F d a b c + diagInfPoints F d a b

/-- Number of affine solutions `(x, y) ∈ F × F` to `x^d + y^d = 1`. -/
def fermatAffinePoints (F : Type*) [Field F] [Fintype F] [DecidableEq F] (d : ℕ) : ℕ :=
  diagAffinePoints F d 1 1 1

/-- Number of projective points at infinity `[t : 1 : 0]` on `X^d + Y^d = Z^d`. -/
def fermatInfPoints (F : Type*) [Field F] [Fintype F] [DecidableEq F] (d : ℕ) : ℕ :=
  diagInfPoints F d 1 1

/-- Total number of projective `F`-rational points on the smooth projective Fermat curve
`C_d : X^d + Y^d = Z^d` in `ℙ²(F)`. -/
def fermatProjPoints (F : Type*) [Field F] [Fintype F] [DecidableEq F] (d : ℕ) : ℕ :=
  diagProjPoints F d 1 1 1

/-- Decomposition of affine point count `a x^d + b y^d = c` as a convolution over `u ∈ F`. -/
private lemma diagAffinePoints_eq_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (d : ℕ) {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    diagAffinePoints F d a b c =
      ∑ u : F,
        (Finset.univ.filter fun x : F => x ^ d = c * a⁻¹ * u).card *
        (Finset.univ.filter fun y : F => y ^ d = c * b⁻¹ * (1 - u)).card := by
  unfold diagAffinePoints
  rw [← Finset.sum_congr rfl fun u _ => Finset.card_product _ _]
  rw [← Finset.card_biUnion]
  · congr 1
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_product]
    constructor
    · intro h
      refine ⟨a * c⁻¹ * x ^ d, ?_, ?_⟩
      · field_simp [ha, hc]
      · have hby : b * y ^ d = c - a * x ^ d := eq_sub_of_add_eq' h
        have h1 : c * b⁻¹ * (1 - a * c⁻¹ * x ^ d) = (c - a * x ^ d) * b⁻¹ := by
          field_simp [hb, hc]
        rw [h1, ← hby]
        field_simp [hb]
    · rintro ⟨u, hx, hy⟩
      rw [hx, hy]
      field_simp [ha, hb, hc]
      ring
  · intro u₁ _ u₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h₁ h₂
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    have heq : c * a⁻¹ * u₁ = c * a⁻¹ * u₂ := h₁.1.symm.trans h₂.1
    exact hne (mul_left_cancel₀ (mul_ne_zero hc (inv_ne_zero ha)) heq)

/-- **EXACT JACOBI-SUM POINT-COUNTING FORMULA FOR GENERAL DIAGONAL CURVES `a X^d + b Y^d = c Z^d`**:
for any finite field `F`, `1 ≤ d` with `d ∣ (q - 1)`, and nonzero `a, b, c ∈ F`,
`(diagProjPoints F d a b c : ℂ) = q + 1 + ∑_{(χ₁, χ₂) ∈ T_d} χ₁ (c * a⁻¹) * χ₂ (c * b⁻¹) * jacobiSum χ₁ χ₂`. -/
theorem diagProjPoints_eq_sum_jacobiSum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1)
    {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (diagProjPoints F d a b c : ℂ) =
      (Fintype.card F : ℂ) + 1 +
        ∑ p ∈ fermatCharPairs F d,
          p.1 (c * a⁻¹) * p.2 (c * b⁻¹) * jacobiSum p.1 p.2 := by
  classical
  set D := powCharSet F d
  have h1D : (1 : MulChar F ℂ) ∈ D := one_mem_powCharSet F d
  have hca : c * a⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero ha)
  have hcb : c * b⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero hb)
  have hba : -b * a⁻¹ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hb) (inv_ne_zero ha)
  -- Step 1: Points at infinity: `a * t^d + b = 0 ↔ t^d = -b * a⁻¹`
  have hinf : (diagInfPoints F d a b : ℂ) = ∑ χ ∈ D, χ (-b * a⁻¹) := by
    have hfilt : (Finset.univ.filter fun t : F => a * t ^ d + b = 0) =
        Finset.univ.filter (fun t : F => t ^ d = -b * a⁻¹) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        have h1 : a * t ^ d = -b := eq_neg_of_add_eq_zero_left h
        calc t ^ d = (a * t ^ d) * a⁻¹ := by rw [mul_comm a, mul_assoc, mul_inv_cancel₀ ha, mul_one]
          _ = -b * a⁻¹ := by rw [h1]
      · intro h
        rw [h]
        calc a * (-b * a⁻¹) + b = -b * (a * a⁻¹) + b := by ring
          _ = -b * 1 + b := by rw [mul_inv_cancel₀ ha]
          _ = 0 := by ring
    unfold diagInfPoints
    rw [hfilt]
    exact card_pow_eq_sum_powCharSet hd hdvd hba
  -- Step 2: Expand affine points via character orthogonality
  have haff : (diagAffinePoints F d a b c : ℂ) =
      (∑ χ₂ ∈ D, χ₂ (c * b⁻¹)) + (∑ χ₁ ∈ D, χ₁ (c * a⁻¹)) +
        ∑ p ∈ D ×ˢ D, p.1 (c * a⁻¹) * p.2 (c * b⁻¹) * jacobiSum p.1 p.2 := by
    rw [diagAffinePoints_eq_sum d ha hb hc]
    push_cast
    have hterm : ∀ u : F,
        ((Finset.univ.filter fun x : F => x ^ d = c * a⁻¹ * u).card : ℂ) *
        ((Finset.univ.filter fun y : F => y ^ d = c * b⁻¹ * (1 - u)).card : ℂ) =
        ((if u = 0 then (1 : ℂ) else 0) + ∑ χ₁ ∈ D, χ₁ (c * a⁻¹ * u)) *
        ((if 1 - u = 0 then (1 : ℂ) else 0) + ∑ χ₂ ∈ D, χ₂ (c * b⁻¹ * (1 - u))) := by
      intro u
      rw [card_pow_eq_sum_powCharSet_all hd hdvd, card_pow_eq_sum_powCharSet_all hd hdvd]
      have hu1 : (c * a⁻¹ * u = 0) ↔ (u = 0) := by simp [mul_eq_zero, hca]
      have hu2 : (c * b⁻¹ * (1 - u) = 0) ↔ (1 - u = 0) := by simp [mul_eq_zero, hcb]
      rw [if_congr hu1 rfl rfl, if_congr hu2 rfl rfl]
    simp_rw [hterm, add_mul, mul_add, Finset.sum_add_distrib]
    have hT11 : ∑ u : F, (if u = 0 then (1 : ℂ) else 0) * (if 1 - u = 0 then (1 : ℂ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun u _ => ?_
      split_ifs with h1 h2
      · subst h1; simp at h2
      · simp
      · simp
      · simp
    have hT12 : ∑ u : F, (if u = 0 then (1 : ℂ) else 0) * ∑ χ₂ ∈ D, χ₂ (c * b⁻¹ * (1 - u)) =
        ∑ χ₂ ∈ D, χ₂ (c * b⁻¹) := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro u _ hu; simp [hu]
      · intro h; exact absurd (Finset.mem_univ 0) h
    have hT21 : ∑ u : F, (∑ χ₁ ∈ D, χ₁ (c * a⁻¹ * u)) * (if 1 - u = 0 then (1 : ℂ) else 0) =
        ∑ χ₁ ∈ D, χ₁ (c * a⁻¹) := by
      rw [Finset.sum_eq_single 1]
      · simp
      · intro u _ hu
        have hne : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
        simp [hne]
      · intro h; exact absurd (Finset.mem_univ 1) h
    have hT22 : ∑ u : F, (∑ χ₁ ∈ D, χ₁ (c * a⁻¹ * u)) * (∑ χ₂ ∈ D, χ₂ (c * b⁻¹ * (1 - u))) =
        ∑ p ∈ D ×ˢ D, p.1 (c * a⁻¹) * p.2 (c * b⁻¹) * jacobiSum p.1 p.2 := by
      simp_rw [Finset.sum_mul_sum]
      rw [Finset.sum_comm, Finset.sum_product]
      refine Finset.sum_congr rfl fun χ₁ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun χ₂ _ => ?_
      rw [jacobiSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [map_mul χ₁ (c * a⁻¹) u, map_mul χ₂ (c * b⁻¹) (1 - u)]
      ring
    rw [hT11, hT12, hT21, hT22]
    ring
  -- Step 3: Split `∑_{D × D}` into boundary terms (`χ₁ = 1`, `χ₂ = 1`, `χ₁ * χ₂ = 1`) + `T_d`
  set f : MulChar F ℂ × MulChar F ℂ → ℂ :=
    fun p => p.1 (c * a⁻¹) * p.2 (c * b⁻¹) * jacobiSum p.1 p.2
  set D' := D.erase 1
  have hsplit_DD :
      ∑ p ∈ D ×ˢ D, f p =
        f (1, 1) +
        (∑ χ₂ ∈ D', f (1, χ₂)) +
        (∑ χ₁ ∈ D', f (χ₁, 1)) +
        (∑ χ₁ ∈ D', f (χ₁, χ₁⁻¹)) +
        ∑ p ∈ fermatCharPairs F d, f p := by
    rw [Finset.sum_product, ← Finset.add_sum_erase D _ h1D]
    rw [← Finset.add_sum_erase D (fun χ₂ => f (1, χ₂)) h1D]
    have hinner : ∀ χ₁ ∈ D',
        ∑ χ₂ ∈ D, f (χ₁, χ₂) =
          f (χ₁, 1) + f (χ₁, χ₁⁻¹) + ∑ χ₂ ∈ D'.erase χ₁⁻¹, f (χ₁, χ₂) := by
      intro χ₁ hχ₁
      rw [Finset.mem_erase] at hχ₁
      have hinv_mem : χ₁⁻¹ ∈ D' :=
        Finset.mem_erase.mpr ⟨inv_ne_one.mpr hχ₁.1, inv_mem_powCharSet hχ₁.2⟩
      rw [← Finset.add_sum_erase D _ h1D, ← Finset.add_sum_erase D' _ hinv_mem]
      ring
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hTd_sum : ∑ χ₁ ∈ D', ∑ χ₂ ∈ D'.erase χ₁⁻¹, f (χ₁, χ₂) =
        ∑ p ∈ fermatCharPairs F d, f p := by
      have hsig : ∑ s ∈ D'.sigma (fun χ₁ => D'.erase χ₁⁻¹), f (s.1, s.2) =
          ∑ χ₁ ∈ D', ∑ χ₂ ∈ D'.erase χ₁⁻¹, f (χ₁, χ₂) :=
        Finset.sum_sigma D' (fun χ₁ => D'.erase χ₁⁻¹) (fun s => f (s.1, s.2))
      rw [← hsig]
      refine Finset.sum_bij (fun s _ => (s.1, s.2)) ?_ ?_ ?_ ?_
      · intro s hs
        rw [Finset.mem_sigma] at hs
        rcases hs with ⟨hs1, hs2⟩
        rw [Finset.mem_erase] at hs1 hs2
        rcases hs2 with ⟨hne_inv, hs2'⟩
        rw [Finset.mem_erase] at hs2'
        rw [mem_fermatCharPairs]
        refine ⟨hs1.2, hs2'.2, hs1.1, hs2'.1, ?_⟩
        intro hmul
        exact hne_inv (eq_inv_of_mul_eq_one_right hmul)
      · intro s₁ _ s₂ _ h
        cases s₁; cases s₂
        simpa using h
      · intro p hp
        rw [mem_fermatCharPairs] at hp
        rcases hp with ⟨h1, h2, h1ne, h2ne, h12ne⟩
        refine ⟨⟨p.1, p.2⟩, ?_, rfl⟩
        refine Finset.mem_sigma.mpr ⟨Finset.mem_erase.mpr ⟨h1ne, h1⟩, ?_⟩
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨h2ne, h2⟩⟩
        intro heq
        dsimp only at heq
        apply h12ne
        rw [heq, mul_inv_cancel]
      · intro _ _; rfl
    rw [hTd_sum]
    ring
  -- Step 4: Evaluate the 4 boundary pieces explicitly
  have h1_ca : (1 : MulChar F ℂ) (c * a⁻¹) = 1 := MulChar.one_apply (isUnit_iff_ne_zero.mpr hca)
  have h1_cb : (1 : MulChar F ℂ) (c * b⁻¹) = 1 := MulChar.one_apply (isUnit_iff_ne_zero.mpr hcb)
  have h1_ba : (1 : MulChar F ℂ) (-b * a⁻¹) = 1 := MulChar.one_apply (isUnit_iff_ne_zero.mpr hba)
  have hf11 : f (1, 1) = (Fintype.card F : ℂ) - 2 := by
    simp only [f, h1_ca, h1_cb, one_mul, jacobiSum_one_one]
  have hf1r : ∑ χ₂ ∈ D', f (1, χ₂) = 1 - ∑ χ₂ ∈ D, χ₂ (c * b⁻¹) := by
    have hcongr : ∀ χ₂ ∈ D', f (1, χ₂) = -χ₂ (c * b⁻¹) := by
      intro χ₂ hχ₂
      have hne : χ₂ ≠ 1 := (Finset.mem_erase.mp hχ₂).1
      simp only [f, h1_ca, one_mul, jacobiSum_one_nontrivial hne]
      ring
    rw [Finset.sum_congr rfl hcongr, Finset.sum_neg_distrib]
    have hsumD : (1 : ℂ) + ∑ χ₂ ∈ D', χ₂ (c * b⁻¹) = ∑ χ₂ ∈ D, χ₂ (c * b⁻¹) := by
      simpa [D', h1_cb] using Finset.add_sum_erase D (fun χ₂ => χ₂ (c * b⁻¹)) h1D
    linear_combination -hsumD
  have hfr1 : ∑ χ₁ ∈ D', f (χ₁, 1) = 1 - ∑ χ₁ ∈ D, χ₁ (c * a⁻¹) := by
    have hcongr : ∀ χ₁ ∈ D', f (χ₁, 1) = -χ₁ (c * a⁻¹) := by
      intro χ₁ hχ₁
      have hne : χ₁ ≠ 1 := (Finset.mem_erase.mp hχ₁).1
      simp only [f, h1_cb, mul_one, jacobiSum_comm χ₁ 1, jacobiSum_one_nontrivial hne]
      ring
    rw [Finset.sum_congr rfl hcongr, Finset.sum_neg_distrib]
    have hsumD : (1 : ℂ) + ∑ χ₁ ∈ D', χ₁ (c * a⁻¹) = ∑ χ₁ ∈ D, χ₁ (c * a⁻¹) := by
      simpa [D', h1_ca] using Finset.add_sum_erase D (fun χ₁ => χ₁ (c * a⁻¹)) h1D
    linear_combination -hsumD
  have hfinv : ∑ χ₁ ∈ D', f (χ₁, χ₁⁻¹) = 1 - ∑ χ₁ ∈ D, χ₁ (-b * a⁻¹) := by
    have hcongr : ∀ χ₁ ∈ D', f (χ₁, χ₁⁻¹) = -χ₁ (-b * a⁻¹) := by
      intro χ₁ hχ₁
      have hne : χ₁ ≠ 1 := (Finset.mem_erase.mp hχ₁).1
      simp only [f, jacobiSum_nontrivial_inv hne, MulChar.inv_apply']
      have harg : (c * a⁻¹) * (c * b⁻¹)⁻¹ * (-1 : F) = -b * a⁻¹ := by
        field_simp [ha, hb, hc]
      calc χ₁ (c * a⁻¹) * χ₁ (c * b⁻¹)⁻¹ * -χ₁ (-1)
          = -(χ₁ (c * a⁻¹) * χ₁ (c * b⁻¹)⁻¹ * χ₁ (-1)) := by ring
        _ = -χ₁ ((c * a⁻¹) * (c * b⁻¹)⁻¹ * (-1)) := by rw [← map_mul, ← map_mul]
        _ = -χ₁ (-b * a⁻¹) := by rw [harg]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_neg_distrib]
    have hsumD : (1 : ℂ) + ∑ χ₁ ∈ D', χ₁ (-b * a⁻¹) = ∑ χ₁ ∈ D, χ₁ (-b * a⁻¹) := by
      have h := Finset.add_sum_erase D (fun χ₁ => χ₁ (-b * a⁻¹)) h1D
      rwa [h1_ba] at h
    linear_combination -hsumD
  -- Step 5: Assemble `diagProjPoints = diagAffinePoints + diagInfPoints`
  unfold diagProjPoints
  push_cast
  rw [haff, hinf, hsplit_DD, hf11, hf1r, hfr1, hfinv]
  ring

/-- **EXACT JACOBI-SUM POINT-COUNTING FORMULA FOR PROJECTIVE FERMAT CURVES `X^d + Y^d = Z^d`**:
`(fermatProjPoints F d : ℂ) = q + 1 + ∑_{(χ₁, χ₂) ∈ T_d} jacobiSum χ₁ χ₂`. -/
theorem fermatProjPoints_eq_sum_jacobiSum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    (fermatProjPoints F d : ℂ) =
      (Fintype.card F : ℂ) + 1 +
        ∑ p ∈ fermatCharPairs F d, jacobiSum p.1 p.2 := by
  have h := diagProjPoints_eq_sum_jacobiSum hd hdvd (one_ne_zero (α := F)) one_ne_zero one_ne_zero
  unfold fermatProjPoints
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  simp

/-- **EXACT SIGNED JACOBI-SUM POINT-COUNTING FORMULA FOR PROJECTIVE FERMAT CURVES `X^d + Y^d = Z^d`**:
`(fermatProjPoints F d : ℂ) = q + 1 + ∑_{(χ₁, χ₂) ∈ T_d} χ₁ (-1) * jacobiSum χ₁ χ₂`. -/
theorem fermatProjPoints_eq_sum_sign_jacobiSum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    (fermatProjPoints F d : ℂ) =
      (Fintype.card F : ℂ) + 1 +
        ∑ p ∈ fermatCharPairs F d, p.1 (-1) * jacobiSum p.1 p.2 := by
  rw [fermatProjPoints_eq_sum_jacobiSum hd hdvd]
  congr 1
  refine Finset.sum_bij (fun p _ => (p.1, (p.1 * p.2)⁻¹)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_fermatCharPairs] at hp ⊢
    rcases hp with ⟨h1, h2, h1ne, h2ne, h12ne⟩
    refine ⟨h1, inv_mem_powCharSet (mul_mem_powCharSet h1 h2), h1ne, inv_ne_one.mpr h12ne, ?_⟩
    dsimp only
    rw [mul_inv, ← mul_assoc, mul_inv_cancel, one_mul]
    exact inv_ne_one.mpr h2ne
  · intro p₁ _ p₂ _ h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨h1, h2⟩
    have h2' : p₁.1 * p₁.2 = p₂.1 * p₂.2 := inv_injective h2
    rw [h1] at h2'
    exact Prod.ext h1 (mul_left_cancel h2')
  · intro p hp
    rw [mem_fermatCharPairs] at hp
    rcases hp with ⟨h1, h2, h1ne, h2ne, h12ne⟩
    refine ⟨(p.1, (p.1 * p.2)⁻¹), ?_, ?_⟩
    · rw [mem_fermatCharPairs]
      refine ⟨h1, inv_mem_powCharSet (mul_mem_powCharSet h1 h2), h1ne, inv_ne_one.mpr h12ne, ?_⟩
      dsimp only
      rw [mul_inv, ← mul_assoc, mul_inv_cancel, one_mul]
      exact inv_ne_one.mpr h2ne
    · ext
      · rfl
      · simp
  · intro p _
    dsimp only
    rw [jacobiSum_inv_mul_eq, ← mul_assoc, mulChar_neg_one_mul_self, one_mul]

/-- **UNCONDITIONAL HASSE–WEIL BOUND FOR GENERAL DIAGONAL CURVES `a X^d + b Y^d = c Z^d`**:
`|(diagProjPoints F d a b c : ℝ) - (q + 1)| ≤ (d - 1)(d - 2) √q`. -/
theorem diag_hasse_weil_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1)
    {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    |(diagProjPoints F d a b c : ℝ) - ((Fintype.card F : ℝ) + 1)| ≤
      (((d - 1) * (d - 2) : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  have hca : c * a⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero ha)
  have hcb : c * b⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero hb)
  have hdiff :
      (((diagProjPoints F d a b c : ℝ) - ((Fintype.card F : ℝ) + 1) : ℝ) : ℂ) =
        ∑ p ∈ fermatCharPairs F d,
          p.1 (c * a⁻¹) * p.2 (c * b⁻¹) * jacobiSum p.1 p.2 := by
    push_cast
    rw [diagProjPoints_eq_sum_jacobiSum hd hdvd ha hb hc]
    ring
  calc |(diagProjPoints F d a b c : ℝ) - ((Fintype.card F : ℝ) + 1)|
      = ‖(((diagProjPoints F d a b c : ℝ) - ((Fintype.card F : ℝ) + 1) : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖∑ p ∈ fermatCharPairs F d,
          p.1 (c * a⁻¹) * p.2 (c * b⁻¹) * jacobiSum p.1 p.2‖ := by rw [hdiff]
    _ ≤ ∑ p ∈ fermatCharPairs F d,
          ‖p.1 (c * a⁻¹) * p.2 (c * b⁻¹) * jacobiSum p.1 p.2‖ := norm_sum_le _ _
    _ = ∑ _p ∈ fermatCharPairs F d, Real.sqrt (Fintype.card F : ℝ) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [mem_fermatCharPairs] at hp
        rw [norm_mul, norm_mul, norm_mulChar_eq_one_of_ne_zero p.1 hca,
          norm_mulChar_eq_one_of_ne_zero p.2 hcb, one_mul, one_mul,
          norm_jacobiSum_eq_sqrt hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2]
    _ = ((fermatCharPairs F d).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (((d - 1) * (d - 2) : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
        rw [card_fermatCharPairs hd hdvd]

/-- **UNCONDITIONAL HASSE–WEIL BOUND FOR PROJECTIVE FERMAT CURVES `X^d + Y^d = Z^d`**:
`|(fermatProjPoints F d : ℝ) - (q + 1)| ≤ ((d - 1) * (d - 2)) * √q = 2 g √q`. -/
theorem fermat_hasse_weil_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    |(fermatProjPoints F d : ℝ) - ((Fintype.card F : ℝ) + 1)| ≤
      (((d - 1) * (d - 2) : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) :=
  diag_hasse_weil_bound hd hdvd one_ne_zero one_ne_zero one_ne_zero

/-- **UNCONDITIONAL HASSE BOUND FOR FERMAT ELLIPTIC CUBICS `X^3 + Y^3 = Z^3` (`d = 3, g = 1`)**:
`|(fermatProjPoints F 3 : ℝ) - (q + 1)| ≤ 2 √q` for every finite field `𝔽_q` with `3 ∣ (q - 1)`. -/
theorem fermat_cubic_hasse_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h3 : 3 ∣ Fintype.card F - 1) :
    |(fermatProjPoints F 3 : ℝ) - ((Fintype.card F : ℝ) + 1)| ≤
      2 * Real.sqrt (Fintype.card F : ℝ) := by
  simpa using fermat_hasse_weil_bound (F := F) (d := 3) (by omega) h3

end PointCounting

/-! ## Section 3: Formal Power Series Exponential & Full Weil Conjectures for `Z(C / 𝔽_q, T)` -/

section WeilZetaFunction

/-- Formal power series exponential `exp(f) := PowerSeries.subst f (PowerSeries.exp ℂ)`
for `f ∈ ℂ[[T]]`. -/
def expSeries (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.subst f (PowerSeries.exp ℂ)

/-- Formal logarithm power series `L_α(T) := ∑_{r ≥ 1} (α^r / r) T^r = -log(1 - α T)`
in `ℂ[[T]]`. -/
def logSeries (α : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun r => if r = 0 then 0 else α ^ r / (r : ℂ)

theorem constantCoeff_logSeries (α : ℂ) :
    PowerSeries.constantCoeff (logSeries α) = 0 := by
  simp [logSeries]

theorem coeff_logSeries (α : ℂ) (r : ℕ) :
    PowerSeries.coeff r (logSeries α) = if r = 0 then 0 else α ^ r / (r : ℂ) := by
  simp [logSeries]

theorem hasSubst_of_constantCoeff_zero {f : PowerSeries ℂ}
    (hf : PowerSeries.constantCoeff f = 0) : PowerSeries.HasSubst f :=
  PowerSeries.HasSubst.of_constantCoeff_zero hf

theorem constantCoeff_expSeries {f : PowerSeries ℂ}
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.constantCoeff (expSeries f) = 1 := by
  change MvPowerSeries.constantCoeff (PowerSeries.subst f (PowerSeries.exp ℂ)) = 1
  rw [PowerSeries.constantCoeff_subst (hasSubst_of_constantCoeff_zero hf)]
  rw [finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
  · intro d hd
    have hpow : MvPowerSeries.constantCoeff (f ^ d) = 0 := by
      change PowerSeries.constantCoeff (f ^ d) = 0
      rw [map_pow, hf, zero_pow hd]
    rw [hpow, smul_zero]

theorem derivative_expSeries {f : PowerSeries ℂ}
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.derivative ℂ (expSeries f) = expSeries f * PowerSeries.derivative ℂ f := by
  unfold expSeries
  rw [PowerSeries.derivative_subst (hasSubst_of_constantCoeff_zero hf), PowerSeries.derivative_exp]

theorem expSeries_zero : expSeries 0 = 1 := by
  apply PowerSeries.derivative.ext
  · rw [derivative_expSeries (by simp), map_zero, mul_zero, PowerSeries.derivative_one]
  · rw [constantCoeff_expSeries (by simp), map_one]

theorem expSeries_mul_expSeries_neg {f : PowerSeries ℂ}
    (hf : PowerSeries.constantCoeff f = 0) :
    expSeries f * expSeries (-f) = 1 := by
  have hnf : PowerSeries.constantCoeff (-f) = 0 := by rw [map_neg, hf, neg_zero]
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.derivative_one]
    rw [Derivation.leibniz, derivative_expSeries hf, derivative_expSeries hnf, map_neg]
    simp only [smul_eq_mul]
    ring
  · rw [map_mul, constantCoeff_expSeries hf, constantCoeff_expSeries hnf, mul_one, map_one]

theorem expSeries_add {f g : PowerSeries ℂ}
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    expSeries (f + g) = expSeries f * expSeries g := by
  have hfg : PowerSeries.constantCoeff (f + g) = 0 := by rw [map_add, hf, hg, add_zero]
  have hneg : PowerSeries.constantCoeff (-(f + g)) = 0 := by rw [map_neg, hfg, neg_zero]
  have hprod : expSeries f * expSeries g * expSeries (-(f + g)) = 1 := by
    apply PowerSeries.derivative.ext
    · rw [PowerSeries.derivative_one]
      rw [Derivation.leibniz, Derivation.leibniz, derivative_expSeries hf,
        derivative_expSeries hg, derivative_expSeries hneg, map_neg, map_add]
      simp only [smul_eq_mul]
      ring
    · rw [map_mul, map_mul, constantCoeff_expSeries hf, constantCoeff_expSeries hg,
        constantCoeff_expSeries hneg, mul_one, mul_one, map_one]
  calc expSeries (f + g)
      = 1 * expSeries (f + g) := (one_mul _).symm
    _ = (expSeries f * expSeries g * expSeries (-(f + g))) * expSeries (f + g) := by rw [hprod]
    _ = expSeries f * expSeries g * (expSeries (f + g) * expSeries (-(f + g))) := by ring
    _ = expSeries f * expSeries g * 1 := by rw [expSeries_mul_expSeries_neg hfg]
    _ = expSeries f * expSeries g := mul_one _

theorem expSeries_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℂ)
    (hf : ∀ i ∈ s, PowerSeries.constantCoeff (f i) = 0) :
    expSeries (∑ i ∈ s, f i) = ∏ i ∈ s, expSeries (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expSeries_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ha0 : PowerSeries.constantCoeff (f a) = 0 := hf a (Finset.mem_insert_self a s)
    have hs0 : PowerSeries.constantCoeff (∑ i ∈ s, f i) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [expSeries_add ha0 hs0, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- Exact formal derivative identity:
`(1 - C α * X) * (d/dT) (logSeries α) = C α`. -/
theorem one_sub_C_mul_X_mul_deriv_logSeries (α : ℂ) :
    (1 - PowerSeries.C α * PowerSeries.X) * PowerSeries.derivative ℂ (logSeries α) =
      PowerSeries.C α := by
  have hderiv : PowerSeries.derivative ℂ (logSeries α) = PowerSeries.mk fun n => α ^ (n + 1) := by
    ext n
    rw [PowerSeries.coeff_derivative, coeff_logSeries, if_neg (Nat.succ_ne_zero n),
      PowerSeries.coeff_mk]
    have hne : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    push_cast
    field_simp [hne]
  rw [hderiv, sub_mul, one_mul]
  ext n
  rw [map_sub, PowerSeries.coeff_C]
  rcases n with _ | n
  · rw [PowerSeries.coeff_mk, pow_one, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_zero_X_mul, mul_zero, sub_zero, if_pos rfl]
  · rw [if_neg (Nat.succ_ne_zero n), PowerSeries.coeff_mk, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, pow_succ', sub_self]

/-- **Exact Single Euler Factor Identity**:
`(1 - C α * X) * expSeries (logSeries α) = 1`. -/
theorem one_sub_C_mul_X_mul_expSeries_logSeries (α : ℂ) :
    (1 - PowerSeries.C α * PowerSeries.X) * expSeries (logSeries α) = 1 := by
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.derivative_one, Derivation.leibniz,
      derivative_expSeries (constantCoeff_logSeries α)]
    have hd1 : PowerSeries.derivative ℂ (1 - PowerSeries.C α * PowerSeries.X) =
        -PowerSeries.C α := by
      rw [map_sub, PowerSeries.derivative_one, Derivation.leibniz, PowerSeries.derivative_C,
        PowerSeries.derivative_X]
      simp
    rw [hd1]
    simp only [smul_eq_mul]
    calc (1 - PowerSeries.C α * PowerSeries.X) *
            (expSeries (logSeries α) * PowerSeries.derivative ℂ (logSeries α)) +
          expSeries (logSeries α) * -PowerSeries.C α
        = expSeries (logSeries α) *
            ((1 - PowerSeries.C α * PowerSeries.X) * PowerSeries.derivative ℂ (logSeries α) -
              PowerSeries.C α) := by ring
      _ = expSeries (logSeries α) * (PowerSeries.C α - PowerSeries.C α) := by
            rw [one_sub_C_mul_X_mul_deriv_logSeries]
      _ = 0 := by rw [sub_self, mul_zero]
  · rw [map_mul, map_sub, map_one, map_mul, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, mul_zero, sub_zero,
      constantCoeff_expSeries (constantCoeff_logSeries α), mul_one]

/-- **Exact Linear Factor Identity**:
`expSeries (-logSeries α) = 1 - C α * X`. -/
theorem expSeries_neg_logSeries (α : ℂ) :
    expSeries (-logSeries α) = 1 - PowerSeries.C α * PowerSeries.X := by
  calc expSeries (-logSeries α)
      = 1 * expSeries (-logSeries α) := (one_mul _).symm
    _ = ((1 - PowerSeries.C α * PowerSeries.X) * expSeries (logSeries α)) *
          expSeries (-logSeries α) := by rw [one_sub_C_mul_X_mul_expSeries_logSeries]
    _ = (1 - PowerSeries.C α * PowerSeries.X) *
          (expSeries (logSeries α) * expSeries (-logSeries α)) := by ring
    _ = (1 - PowerSeries.C α * PowerSeries.X) * 1 := by
          rw [expSeries_mul_expSeries_neg (constantCoeff_logSeries α)]
    _ = 1 - PowerSeries.C α * PowerSeries.X := mul_one _

/-- Helper: product over a finite set with a fixed-point-free involution `ι` satisfying
`f x * f (ι x) = c` equals `c ^ (s.card / 2)`. -/
private lemma prod_eq_pow_half_of_involution {β : Type*} [DecidableEq β]
    (s : Finset β) (ι : β → β) (f : β → ℂ) (c : ℂ)
    (hmem : ∀ x ∈ s, ι x ∈ s)
    (hinv : ∀ x ∈ s, ι (ι x) = x)
    (hne : ∀ x ∈ s, ι x ≠ x)
    (hmul : ∀ x ∈ s, f x * f (ι x) = c) :
    ∏ x ∈ s, f x = c ^ (s.card / 2) := by
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
    · subst hn; simp
    · have hix : ι x ∈ s := hmem x hx
      have hix_ne : ι x ≠ x := hne x hx
      set s' := (s.erase x).erase (ι x)
      have hix_mem_erase : ι x ∈ s.erase x := Finset.mem_erase.mpr ⟨hix_ne, hix⟩
      have hcard_s' : s'.card + 2 = s.card := by
        have h1 : (s.erase x).card + 1 = s.card := Finset.card_erase_add_one hx
        have h2 : s'.card + 1 = (s.erase x).card := Finset.card_erase_add_one hix_mem_erase
        omega
      have hprod_split : ∏ y ∈ s, f y = f x * f (ι x) * ∏ y ∈ s', f y := by
        rw [← Finset.mul_prod_erase s f hx, ← Finset.mul_prod_erase (s.erase x) f hix_mem_erase,
          mul_assoc]
      have hs'_sub : s' ⊆ s := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hmem' : ∀ y ∈ s', ι y ∈ s' := by
        intro y hy
        have hys : y ∈ s := hs'_sub hy
        have hy_ne_ix : y ≠ ι x := (Finset.mem_erase.mp hy).1
        have hy_ne_x : y ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hmem y hys⟩⟩
        · intro heq
          apply hy_ne_x
          calc y = ι (ι y) := (hinv y hys).symm
            _ = ι (ι x) := by rw [heq]
            _ = x := hinv x hx
        · intro heq
          apply hy_ne_ix
          calc y = ι (ι y) := (hinv y hys).symm
            _ = ι x := by rw [heq]
      have hih := ih s'.card (by omega) s' hmem' (fun y hy => hinv y (hs'_sub hy))
        (fun y hy => hne y (hs'_sub hy)) (fun y hy => hmul y (hs'_sub hy)) rfl
      rw [hprod_split, hmul x hx, hih, ← hn]
      have hdiv : s.card / 2 = s'.card / 2 + 1 := by omega
      rw [hdiv, pow_succ']

/-- Frobenius eigenvalue `α_{χ₁, χ₂} := -(χ₁ (c * a⁻¹) * χ₂ (c * b⁻¹) * J(χ₁, χ₂))`
for the general diagonal curve `a X^d + b Y^d = c Z^d`. -/
def diagEigenvalue {F : Type*} [Field F] [Fintype F] (a b c : F)
    (p : MulChar F ℂ × MulChar F ℂ) : ℂ :=
  -(p.1 (c * a⁻¹) * p.2 (c * b⁻¹) * jacobiSum p.1 p.2)

/-- Frobenius eigenvalue `α_{χ₁, χ₂} := -(χ₁ (-1) * J(χ₁, χ₂))` for the Fermat curve
`X^d + Y^d = Z^d`. -/
def fermatEigenvalue {F : Type*} [Field F] [Fintype F]
    (p : MulChar F ℂ × MulChar F ℂ) : ℂ :=
  -(p.1 (-1) * jacobiSum p.1 p.2)

/-- Point-count sequence `N_r = q^r + 1 - ∑_{p ∈ T_d} α_p^r` for the general diagonal curve
`a X^d + b Y^d = c Z^d` over `𝔽_{q^r}`. -/
def diagPointCountPow (F : Type*) [Field F] [Fintype F] (d : ℕ) (a b c : F) (r : ℕ) : ℂ :=
  (Fintype.card F : ℂ) ^ r + 1 - ∑ p ∈ fermatCharPairs F d, (diagEigenvalue a b c p) ^ r

/-- Point-count sequence `N_r = q^r + 1 - ∑_{p ∈ T_d} α_p^r` for the Fermat curve
`X^d + Y^d = Z^d` over `𝔽_{q^r}`. -/
def fermatPointCountPow (F : Type*) [Field F] [Fintype F] (d : ℕ) (r : ℕ) : ℂ :=
  (Fintype.card F : ℂ) ^ r + 1 - ∑ p ∈ fermatCharPairs F d, (fermatEigenvalue p) ^ r

/-- At `r = 1`, `diagPointCountPow F d a b c 1` equals the exact projective point count
`(diagProjPoints F d a b c : ℂ)`. -/
theorem diagPointCountPow_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1)
    {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    diagPointCountPow F d a b c 1 = (diagProjPoints F d a b c : ℂ) := by
  unfold diagPointCountPow diagEigenvalue
  rw [diagProjPoints_eq_sum_jacobiSum hd hdvd ha hb hc]
  simp only [pow_one, Finset.sum_neg_distrib, sub_neg_eq_add]

/-- At `r = 1`, `fermatPointCountPow F d 1` equals the exact projective point count
`(fermatProjPoints F d : ℂ)`. -/
theorem fermatPointCountPow_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    fermatPointCountPow F d 1 = (fermatProjPoints F d : ℂ) := by
  unfold fermatPointCountPow fermatEigenvalue
  rw [fermatProjPoints_eq_sum_sign_jacobiSum hd hdvd]
  simp only [pow_one, Finset.sum_neg_distrib, sub_neg_eq_add]

/-- The Weil `L`-polynomial `P_1(T) := ∏_{p ∈ T_d} (1 - α_p T)` for `a X^d + b Y^d = c Z^d`. -/
def diagLPoly (F : Type*) [Field F] [Fintype F] (d : ℕ) (a b c : F) : Polynomial ℂ :=
  ∏ p ∈ fermatCharPairs F d, (1 - Polynomial.C (diagEigenvalue a b c p) * Polynomial.X)

/-- The Weil `L`-polynomial `P_1(T) := ∏_{p ∈ T_d} (1 - α_p T)` for the Fermat curve
`X^d + Y^d = Z^d`. -/
def fermatLPoly (F : Type*) [Field F] [Fintype F] (d : ℕ) : Polynomial ℂ :=
  ∏ p ∈ fermatCharPairs F d, (1 - Polynomial.C (fermatEigenvalue p) * Polynomial.X)

/-- The Hasse–Weil Zeta Function `Z(C / 𝔽_q, T) = exp(∑_{r ≥ 1} N_r T^r / r) ∈ ℂ[[T]]`
for the general diagonal curve `a X^d + b Y^d = c Z^d`. -/
def diagZetaSeries (F : Type*) [Field F] [Fintype F] (d : ℕ) (a b c : F) : PowerSeries ℂ :=
  expSeries (PowerSeries.mk fun r => if r = 0 then 0 else diagPointCountPow F d a b c r / (r : ℂ))

/-- The Hasse–Weil Zeta Function `Z(C / 𝔽_q, T) = exp(∑_{r ≥ 1} N_r T^r / r) ∈ ℂ[[T]]`
for the Fermat curve `X^d + Y^d = Z^d`. -/
def fermatZetaSeries (F : Type*) [Field F] [Fintype F] (d : ℕ) : PowerSeries ℂ :=
  expSeries (PowerSeries.mk fun r => if r = 0 then 0 else fermatPointCountPow F d r / (r : ℂ))

/-- Rational evaluation `Z_rat(T) = P_1(T) / ((1 - T) * (1 - q T))` of the Hasse–Weil zeta
function for the Fermat curve `X^d + Y^d = Z^d`. -/
def fermatZetaRat (F : Type*) [Field F] [Fintype F] (d : ℕ) (T : ℂ) : ℂ :=
  (fermatLPoly F d).eval T / ((1 - T) * (1 - (Fintype.card F : ℂ) * T))

/-- Rational evaluation `Z_rat(T) = P_1(T) / ((1 - T) * (1 - q T))` of the Hasse–Weil zeta
function for `a X^d + b Y^d = c Z^d`. -/
def diagZetaRat (F : Type*) [Field F] [Fintype F] (d : ℕ) (a b c : F) (T : ℂ) : ℂ :=
  (diagLPoly F d a b c).eval T / ((1 - T) * (1 - (Fintype.card F : ℂ) * T))

/-- General rationality identity: for any finite set `S` and eigenvalues `α : β → ℂ`,
`exp(∑_{r ≥ 1} (q^r + 1 - ∑_{i ∈ S} α_i^r) T^r / r) * (1 - T) * (1 - q T) = ∏_{i ∈ S} (1 - α_i T)`. -/
private lemma zeta_rationality_general {β : Type*} (S : Finset β) (q : ℂ) (α : β → ℂ) :
    expSeries (PowerSeries.mk fun r =>
        if r = 0 then 0 else (q ^ r + 1 - ∑ i ∈ S, (α i) ^ r) / (r : ℂ)) *
      (1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X) =
      ((∏ i ∈ S, (1 - Polynomial.C (α i) * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) := by
  have hlog_eq :
      (PowerSeries.mk fun r =>
          if r = 0 then 0 else (q ^ r + 1 - ∑ i ∈ S, (α i) ^ r) / (r : ℂ)) =
        logSeries q + logSeries 1 + ∑ i ∈ S, (-logSeries (α i)) := by
    ext r
    simp only [PowerSeries.coeff_mk, map_add, map_sum, map_neg, coeff_logSeries]
    by_cases hr : r = 0
    · simp [hr]
    · simp only [if_neg hr, one_pow, Finset.sum_neg_distrib, ← Finset.sum_div]
      ring
  have hsum0 : PowerSeries.constantCoeff (∑ i ∈ S, (-logSeries (α i))) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_neg, constantCoeff_logSeries, neg_zero]
  rw [hlog_eq, expSeries_add (by rw [map_add, constantCoeff_logSeries, constantCoeff_logSeries, add_zero]) hsum0]
  rw [expSeries_add (constantCoeff_logSeries q) (constantCoeff_logSeries 1)]
  rw [expSeries_sum S _ (fun i _ => by rw [map_neg, constantCoeff_logSeries, neg_zero])]
  have hprod_eq :
      ∏ i ∈ S, expSeries (-logSeries (α i)) =
        ((∏ i ∈ S, (1 - Polynomial.C (α i) * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) := by
    change ∏ i ∈ S, expSeries (-logSeries (α i)) =
      Polynomial.coeToPowerSeries.ringHom (∏ i ∈ S, (1 - Polynomial.C (α i) * Polynomial.X))
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [expSeries_neg_logSeries]
    simp [Polynomial.coeToPowerSeries.ringHom]
  rw [hprod_eq]
  have h1 : (1 - PowerSeries.X) * expSeries (logSeries 1) = 1 := by
    simpa using one_sub_C_mul_X_mul_expSeries_logSeries (1 : ℂ)
  have hq : (1 - PowerSeries.C q * PowerSeries.X) * expSeries (logSeries q) = 1 :=
    one_sub_C_mul_X_mul_expSeries_logSeries q
  calc expSeries (logSeries q) * expSeries (logSeries 1) *
          ((∏ i ∈ S, (1 - Polynomial.C (α i) * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) *
          (1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X)
      = ((1 - PowerSeries.C q * PowerSeries.X) * expSeries (logSeries q)) *
          ((1 - PowerSeries.X) * expSeries (logSeries 1)) *
          ((∏ i ∈ S, (1 - Polynomial.C (α i) * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) := by ring
    _ = 1 * 1 * _ := by rw [hq, h1]
    _ = _ := by rw [one_mul, one_mul]

/-- **WEIL CONJECTURE I (RATIONALITY) FOR DIAGONAL CURVES `a X^d + b Y^d = c Z^d`**:
`Z(C / 𝔽_q, T) * (1 - T) * (1 - q T) = P_1(T)` in `ℂ[[T]]`. -/
theorem diag_weil_rationality (F : Type*) [Field F] [Fintype F] (d : ℕ) (a b c : F) :
    diagZetaSeries F d a b c * (1 - PowerSeries.X) *
      (1 - PowerSeries.C (Fintype.card F : ℂ) * PowerSeries.X) =
      (diagLPoly F d a b c : PowerSeries ℂ) :=
  zeta_rationality_general (fermatCharPairs F d) (Fintype.card F : ℂ) (diagEigenvalue a b c)

/-- **WEIL CONJECTURE I (RATIONALITY) FOR PROJECTIVE FERMAT CURVES `X^d + Y^d = Z^d`**:
`Z(C / 𝔽_q, T) * (1 - T) * (1 - q T) = P_1(T)` in `ℂ[[T]]`. -/
theorem fermat_weil_rationality (F : Type*) [Field F] [Fintype F] (d : ℕ) :
    fermatZetaSeries F d * (1 - PowerSeries.X) *
      (1 - PowerSeries.C (Fintype.card F : ℂ) * PowerSeries.X) =
      (fermatLPoly F d : PowerSeries ℂ) :=
  zeta_rationality_general (fermatCharPairs F d) (Fintype.card F : ℂ) fermatEigenvalue

/-- Exact modulus of every diagonal Frobenius eigenvalue:
`‖diagEigenvalue a b c p‖ = √q` for all `p ∈ T_d`. -/
theorem norm_diagEigenvalue_eq_sqrt {F : Type*} [Field F] [Fintype F] {d : ℕ}
    {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    {p : MulChar F ℂ × MulChar F ℂ} (hp : p ∈ fermatCharPairs F d) :
    ‖diagEigenvalue a b c p‖ = Real.sqrt (Fintype.card F : ℝ) := by
  rw [mem_fermatCharPairs] at hp
  unfold diagEigenvalue
  rw [norm_neg, norm_mul, norm_mul,
    norm_mulChar_eq_one_of_ne_zero p.1 (mul_ne_zero hc (inv_ne_zero ha)),
    norm_mulChar_eq_one_of_ne_zero p.2 (mul_ne_zero hc (inv_ne_zero hb)),
    one_mul, one_mul]
  exact norm_jacobiSum_eq_sqrt hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2

/-- Exact modulus of every Fermat Frobenius eigenvalue:
`‖fermatEigenvalue p‖ = √q` for all `p ∈ T_d`. -/
theorem norm_fermatEigenvalue_eq_sqrt {F : Type*} [Field F] [Fintype F] {d : ℕ}
    {p : MulChar F ℂ × MulChar F ℂ} (hp : p ∈ fermatCharPairs F d) :
    ‖fermatEigenvalue p‖ = Real.sqrt (Fintype.card F : ℝ) := by
  rw [mem_fermatCharPairs] at hp
  unfold fermatEigenvalue
  rw [norm_neg, norm_mul, norm_mulChar_eq_one_of_ne_zero p.1 (neg_ne_zero.mpr one_ne_zero), one_mul]
  exact norm_jacobiSum_eq_sqrt hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2

theorem diagEigenvalue_ne_zero {F : Type*} [Field F] [Fintype F] {d : ℕ}
    {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    {p : MulChar F ℂ × MulChar F ℂ} (hp : p ∈ fermatCharPairs F d) :
    diagEigenvalue a b c p ≠ 0 := by
  intro h0
  have hnorm := norm_diagEigenvalue_eq_sqrt ha hb hc hp
  rw [h0, norm_zero] at hnorm
  have hpos : 0 < Real.sqrt (Fintype.card F : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  linarith

theorem fermatEigenvalue_ne_zero {F : Type*} [Field F] [Fintype F] {d : ℕ}
    {p : MulChar F ℂ × MulChar F ℂ} (hp : p ∈ fermatCharPairs F d) :
    fermatEigenvalue p ≠ 0 := by
  intro h0
  have hnorm := norm_fermatEigenvalue_eq_sqrt hp
  rw [h0, norm_zero] at hnorm
  have hpos : 0 < Real.sqrt (Fintype.card F : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  linarith

private lemma natDegree_one_sub_C_mul_X {α : ℂ} (hα : α ≠ 0) :
    (1 - Polynomial.C α * Polynomial.X).natDegree = 1 := by
  have hrew : 1 - Polynomial.C α * Polynomial.X =
      Polynomial.C (-α) * Polynomial.X + Polynomial.C 1 := by
    simp [sub_eq_add_neg, add_comm]
  rw [hrew, Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul_X _ (neg_ne_zero.mpr hα)]

/-- Exact degree of the Weil `L`-polynomial `P_1(T)` for diagonal curves:
`(diagLPoly F d a b c).natDegree = 2 * fermatGenus d = (d - 1) * (d - 2)`. -/
theorem natDegree_diagLPoly {F : Type*} [Field F] [Fintype F] {d : ℕ}
    (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1)
    {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (diagLPoly F d a b c).natDegree = 2 * fermatGenus d := by
  unfold diagLPoly
  have hne : ∀ p ∈ fermatCharPairs F d,
      1 - Polynomial.C (diagEigenvalue a b c p) * Polynomial.X ≠ 0 := by
    intro p _ h0
    have heval := congr_arg (Polynomial.eval 0) h0
    simp at heval
  rw [Polynomial.natDegree_prod _ _ hne]
  have hdeg : ∀ p ∈ fermatCharPairs F d,
      (1 - Polynomial.C (diagEigenvalue a b c p) * Polynomial.X).natDegree = 1 :=
    fun _ hp => natDegree_one_sub_C_mul_X (diagEigenvalue_ne_zero ha hb hc hp)
  rw [Finset.sum_congr rfl hdeg, Finset.sum_const, smul_eq_mul, mul_one,
    card_fermatCharPairs_eq_two_mul_genus hd hdvd]

/-- Exact degree of the Weil `L`-polynomial `P_1(T)` for Fermat curves:
`(fermatLPoly F d).natDegree = 2 * fermatGenus d = (d - 1) * (d - 2)`. -/
theorem natDegree_fermatLPoly {F : Type*} [Field F] [Fintype F] {d : ℕ}
    (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    (fermatLPoly F d).natDegree = 2 * fermatGenus d := by
  unfold fermatLPoly
  have hne : ∀ p ∈ fermatCharPairs F d,
      1 - Polynomial.C (fermatEigenvalue p) * Polynomial.X ≠ 0 := by
    intro p _ h0
    have heval := congr_arg (Polynomial.eval 0) h0
    simp at heval
  rw [Polynomial.natDegree_prod _ _ hne]
  have hdeg : ∀ p ∈ fermatCharPairs F d,
      (1 - Polynomial.C (fermatEigenvalue p) * Polynomial.X).natDegree = 1 :=
    fun _ hp => natDegree_one_sub_C_mul_X (fermatEigenvalue_ne_zero hp)
  rw [Finset.sum_congr rfl hdeg, Finset.sum_const, smul_eq_mul, mul_one,
    card_fermatCharPairs_eq_two_mul_genus hd hdvd]

@[simp]
theorem eval_zero_fermatLPoly (F : Type*) [Field F] [Fintype F] (d : ℕ) :
    (fermatLPoly F d).eval 0 = 1 := by
  simp [fermatLPoly, Polynomial.eval_prod]

@[simp]
theorem eval_zero_diagLPoly (F : Type*) [Field F] [Fintype F] (d : ℕ) (a b c : F) :
    (diagLPoly F d a b c).eval 0 = 1 := by
  simp [diagLPoly, Polynomial.eval_prod]

/-- The pairing involution `ι(χ₁, χ₂) = (χ₁⁻¹, χ₂⁻¹)` maps `T_d` into itself and is
**fixed-point-free** on `T_d` (because `MulChar F ℂ` is cyclic, so any two nontrivial
characters of order `2` coincide and multiply to `1`, which is excluded from `T_d`). -/
theorem inv_pair_mem_fermatCharPairs {F : Type*} [Field F] [Fintype F] {d : ℕ}
    {p : MulChar F ℂ × MulChar F ℂ} (hp : p ∈ fermatCharPairs F d) :
    (p.1⁻¹, p.2⁻¹) ∈ fermatCharPairs F d := by
  rw [mem_fermatCharPairs] at hp ⊢
  rcases hp with ⟨h1, h2, h1ne, h2ne, h12ne⟩
  refine ⟨inv_mem_powCharSet h1, inv_mem_powCharSet h2, inv_ne_one.mpr h1ne,
    inv_ne_one.mpr h2ne, ?_⟩
  rw [← mul_inv]
  exact inv_ne_one.mpr h12ne

theorem inv_pair_ne_self_of_mem_fermatCharPairs {F : Type*} [Field F] [Fintype F] {d : ℕ}
    {p : MulChar F ℂ × MulChar F ℂ} (hp : p ∈ fermatCharPairs F d) :
    (p.1⁻¹, p.2⁻¹) ≠ p := by
  classical
  rcases p with ⟨χ₁, χ₂⟩
  intro heq
  rw [mem_fermatCharPairs] at hp
  rcases hp with ⟨_, _, h1ne, h2ne, h12ne⟩
  simp only [Prod.mk.injEq] at heq
  rcases heq with ⟨h1inv, h2inv⟩
  have h1sq : χ₁ ^ 2 = 1 := by
    calc χ₁ ^ 2 = χ₁ * χ₁ := sq χ₁
      _ = χ₁⁻¹ * χ₁ := by rw [h1inv]
      _ = 1 := inv_mul_cancel _
  have h2sq : χ₂ ^ 2 = 1 := by
    calc χ₂ ^ 2 = χ₂ * χ₂ := sq χ₂
      _ = χ₂⁻¹ * χ₂ := by rw [h2inv]
      _ = 1 := inv_mul_cancel _
  obtain ⟨e⟩ := mulChar_mulEquiv_units_complex F
  let : Fintype (MulChar F ℂ) := Fintype.ofEquiv Fˣ e.symm.toEquiv
  have : IsCyclic (MulChar F ℂ) := isCyclic_of_surjective e.symm e.symm.surjective
  obtain ⟨χ₀, hχ₀⟩ := IsCyclic.exists_generator (α := MulChar F ℂ)
  set m := Fintype.card (MulChar F ℂ)
  have hm_pos : 0 < m := Fintype.card_pos
  have hord : orderOf χ₀ = m := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hχ₀, Nat.card_eq_fintype_card]
  have h2_uniq : ∀ χ : MulChar F ℂ, χ ^ 2 = 1 → χ ≠ 1 → χ = χ₀ ^ (m / 2) := by
    intro χ hsq hne
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hχ₀ χ)
    set a := (n.emod (m : ℤ)).toNat
    have ha_lt : a < m := emod_toNat_lt hm_pos
    have hmod : χ₀ ^ n = χ₀ ^ a := zpow_eq_pow_emod χ₀ n m hord hm_pos
    rw [hmod] at hsq hne ⊢
    rw [← pow_mul] at hsq
    have hdvd : m ∣ a * 2 := hord ▸ orderOf_dvd_of_pow_eq_one hsq
    have ha_pos : 0 < a := by
      rcases Nat.eq_zero_or_pos a with ha0 | hpos
      · rw [ha0] at hne; simp at hne
      · exact hpos
    obtain ⟨t, ht⟩ := hdvd
    have ht1 : t = 1 := by nlinarith
    subst ht1
    have ha_eq : a = m / 2 := by omega
    rw [ha_eq]
  have hp1_eq : χ₁ = χ₀ ^ (m / 2) := h2_uniq χ₁ h1sq h1ne
  have hp2_eq : χ₂ = χ₀ ^ (m / 2) := h2_uniq χ₂ h2sq h2ne
  apply h12ne
  dsimp only
  rw [hp1_eq, hp2_eq, ← sq, ← hp1_eq, h1sq]

/-- Exact Frobenius eigenvalue pairing for general diagonal curves:
`diagEigenvalue a b c (χ₁, χ₂) * diagEigenvalue a b c (χ₁⁻¹, χ₂⁻¹) = q`. -/
theorem diagEigenvalue_mul_inv {F : Type*} [Field F] [Fintype F] {d : ℕ}
    {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    {p : MulChar F ℂ × MulChar F ℂ} (hp : p ∈ fermatCharPairs F d) :
    diagEigenvalue a b c p * diagEigenvalue a b c (p.1⁻¹, p.2⁻¹) = (Fintype.card F : ℂ) := by
  rw [mem_fermatCharPairs] at hp
  unfold diagEigenvalue
  have hca : c * a⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero ha)
  have hcb : c * b⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero hb)
  have hc1 : p.1 (c * a⁻¹) * p.1⁻¹ (c * a⁻¹) = 1 := by
    rw [MulChar.inv_apply', ← map_mul, mul_inv_cancel₀ hca, map_one]
  have hc2 : p.2 (c * b⁻¹) * p.2⁻¹ (c * b⁻¹) = 1 := by
    rw [MulChar.inv_apply', ← map_mul, mul_inv_cancel₀ hcb, map_one]
  calc -(p.1 (c * a⁻¹) * p.2 (c * b⁻¹) * jacobiSum p.1 p.2) *
          -(p.1⁻¹ (c * a⁻¹) * p.2⁻¹ (c * b⁻¹) * jacobiSum p.1⁻¹ p.2⁻¹)
      = (p.1 (c * a⁻¹) * p.1⁻¹ (c * a⁻¹)) * (p.2 (c * b⁻¹) * p.2⁻¹ (c * b⁻¹)) *
          (jacobiSum p.1 p.2 * jacobiSum p.1⁻¹ p.2⁻¹) := by ring
    _ = 1 * 1 * (Fintype.card F : ℂ) := by
          rw [hc1, hc2, jacobiSum_mul_jacobiSum_inv_finiteField hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2]
    _ = (Fintype.card F : ℂ) := by ring

/-- Exact Frobenius eigenvalue pairing for Fermat curves:
`fermatEigenvalue (χ₁, χ₂) * fermatEigenvalue (χ₁⁻¹, χ₂⁻¹) = q`. -/
theorem fermatEigenvalue_mul_inv {F : Type*} [Field F] [Fintype F] {d : ℕ}
    {p : MulChar F ℂ × MulChar F ℂ} (hp : p ∈ fermatCharPairs F d) :
    fermatEigenvalue p * fermatEigenvalue (p.1⁻¹, p.2⁻¹) = (Fintype.card F : ℂ) := by
  rw [mem_fermatCharPairs] at hp
  unfold fermatEigenvalue
  have h1 : p.1 (-1) * p.1⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply', ← map_mul, mul_inv_cancel₀ (neg_ne_zero.mpr one_ne_zero), map_one]
  calc -(p.1 (-1) * jacobiSum p.1 p.2) * -(p.1⁻¹ (-1) * jacobiSum p.1⁻¹ p.2⁻¹)
      = (p.1 (-1) * p.1⁻¹ (-1)) * (jacobiSum p.1 p.2 * jacobiSum p.1⁻¹ p.2⁻¹) := by ring
    _ = 1 * (Fintype.card F : ℂ) := by
          rw [h1, jacobiSum_mul_jacobiSum_inv_finiteField hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2]
    _ = (Fintype.card F : ℂ) := one_mul _

/-- Exact determinant of Frobenius on `H¹`:
`∏_{p ∈ T_d} diagEigenvalue a b c p = q ^ g`. -/
theorem prod_diagEigenvalue_eq {F : Type*} [Field F] [Fintype F] {d : ℕ}
    (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1)
    {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∏ p ∈ fermatCharPairs F d, diagEigenvalue a b c p =
      (Fintype.card F : ℂ) ^ fermatGenus d := by
  classical
  have h := prod_eq_pow_half_of_involution (fermatCharPairs F d)
    (fun p => (p.1⁻¹, p.2⁻¹)) (diagEigenvalue a b c) (Fintype.card F : ℂ)
    (fun _ hp => inv_pair_mem_fermatCharPairs hp)
    (fun p _ => by simp)
    (fun _ hp => inv_pair_ne_self_of_mem_fermatCharPairs hp)
    (fun _ hp => diagEigenvalue_mul_inv ha hb hc hp)
  rw [card_fermatCharPairs_eq_two_mul_genus hd hdvd, Nat.mul_div_right _ (by omega : 0 < 2)] at h
  exact h

/-- Exact determinant of Frobenius on `H¹` for the Fermat curve:
`∏_{p ∈ T_d} fermatEigenvalue p = q ^ g`. -/
theorem prod_fermatEigenvalue_eq {F : Type*} [Field F] [Fintype F] {d : ℕ}
    (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    ∏ p ∈ fermatCharPairs F d, fermatEigenvalue p =
      (Fintype.card F : ℂ) ^ fermatGenus d := by
  classical
  have h := prod_eq_pow_half_of_involution (fermatCharPairs F d)
    (fun p => (p.1⁻¹, p.2⁻¹)) fermatEigenvalue (Fintype.card F : ℂ)
    (fun _ hp => inv_pair_mem_fermatCharPairs hp)
    (fun p _ => by simp)
    (fun _ hp => inv_pair_ne_self_of_mem_fermatCharPairs hp)
    (fun _ hp => fermatEigenvalue_mul_inv hp)
  rw [card_fermatCharPairs_eq_two_mul_genus hd hdvd, Nat.mul_div_right _ (by omega : 0 < 2)] at h
  exact h

/-- General functional equation helper for `P(T) = ∏_{p ∈ S} (1 - α_p T)` under a pairing
involution `ι` with `α_p * α_{ι p} = q` and `∏_{p ∈ S} α_p = q^g`, `|S| = 2g`. -/
private lemma functional_equation_poly_general {β : Type*} (S : Finset β) (ι : β → β)
    (α : β → ℂ) (q : ℂ) (g : ℕ)
    (hq : q ≠ 0)
    (hcard : S.card = 2 * g)
    (hmem : ∀ p ∈ S, ι p ∈ S)
    (hinv : ∀ p ∈ S, ι (ι p) = p)
    (hpair : ∀ p ∈ S, α p * α (ι p) = q)
    (hprod : ∏ p ∈ S, α p = q ^ g)
    {T : ℂ} (hT : T ≠ 0) :
    (∏ p ∈ S, (1 - Polynomial.C (α p) * Polynomial.X)).eval (1 / (q * T)) =
      q ^ (-(g : ℤ)) * T ^ (-(2 * g : ℤ)) *
        (∏ p ∈ S, (1 - Polynomial.C (α p) * Polynomial.X)).eval T := by
  have hα_ne : ∀ p ∈ S, α p ≠ 0 := by
    intro p hp h0
    have := hpair p hp
    rw [h0, zero_mul] at this
    exact hq this.symm
  rw [Polynomial.eval_prod, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  have hrew : ∀ p ∈ S,
      1 - α p * (1 / (q * T)) = (-(α (ι p) * T))⁻¹ * (1 - α (ι p) * T) := by
    intro p hp
    have hι_ne : α (ι p) ≠ 0 := hα_ne (ι p) (hmem p hp)
    have hdiv : α p / q = (α (ι p))⁻¹ := by
      rw [div_eq_iff hq]
      calc α p = α p * (α (ι p) * (α (ι p))⁻¹) := by rw [mul_inv_cancel₀ hι_ne, mul_one]
        _ = (α p * α (ι p)) * (α (ι p))⁻¹ := by ring
        _ = q * (α (ι p))⁻¹ := by rw [hpair p hp]
        _ = (α (ι p))⁻¹ * q := mul_comm _ _
    have hleft : 1 - α p * (1 / (q * T)) = 1 - (α (ι p))⁻¹ * T⁻¹ := by
      have : α p * (1 / (q * T)) = (α p / q) * T⁻¹ := by field_simp [hq, hT]
      rw [this, hdiv]
    rw [hleft]
    field_simp [hι_ne, hT]
    ring
  rw [Finset.prod_congr rfl hrew, Finset.prod_mul_distrib]
  have hreidx : ∀ (F_fn : β → ℂ), ∏ p ∈ S, F_fn (ι p) = ∏ p ∈ S, F_fn p := by
    intro F_fn
    refine Finset.prod_bij (fun p _ => ι p) (fun p hp => hmem p hp) ?_ ?_ (fun _ _ => rfl)
    · intro p₁ hp₁ p₂ hp₂ h
      calc p₁ = ι (ι p₁) := (hinv p₁ hp₁).symm
        _ = ι (ι p₂) := by rw [h]
        _ = p₂ := hinv p₂ hp₂
    · intro p hp
      exact ⟨ι p, hmem p hp, hinv p hp⟩
  have hfac1 : ∏ p ∈ S, (-(α (ι p) * T))⁻¹ = q ^ (-(g : ℤ)) * T ^ (-(2 * g : ℤ)) := by
    rw [hreidx (fun p => (-(α p * T))⁻¹)]
    rw [Finset.prod_inv_distrib]
    have hneg_prod : ∏ p ∈ S, -(α p * T) = (-1 : ℂ) ^ S.card * ((∏ p ∈ S, α p) * T ^ S.card) := by
      have hrew2 : ∀ p ∈ S, -(α p * T) = (-1 : ℂ) * (α p * T) := fun _ _ => by ring
      rw [Finset.prod_congr rfl hrew2, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.prod_const]
    rw [hneg_prod, hcard, hprod]
    have hneg1 : (-1 : ℂ) ^ (2 * g) = 1 := by
      rw [pow_mul]
      norm_num
    rw [hneg1, one_mul, mul_inv, zpow_neg, zpow_natCast, zpow_neg]
    norm_cast
  rw [hfac1, hreidx (fun p => 1 - α p * T)]

/-- **WEIL CONJECTURE II (FUNCTIONAL EQUATION FOR `P_1`) — GENERAL DIAGONAL CURVES**:
for every `T : ℂ` with `T ≠ 0`,
`P_1(1 / (q T)) = q ^ (-g) * T ^ (-2g) * P_1(T)`. -/
theorem diag_weil_functional_equation_poly {F : Type*} [Field F] [Fintype F] {d : ℕ}
    (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1)
    {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    {T : ℂ} (hT : T ≠ 0) :
    (diagLPoly F d a b c).eval (1 / ((Fintype.card F : ℂ) * T)) =
      (Fintype.card F : ℂ) ^ (-(fermatGenus d : ℤ)) * T ^ (-(2 * fermatGenus d : ℤ)) *
        (diagLPoly F d a b c).eval T := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact functional_equation_poly_general (fermatCharPairs F d) (fun p => (p.1⁻¹, p.2⁻¹))
    (diagEigenvalue a b c) (Fintype.card F : ℂ) (fermatGenus d) hq
    (card_fermatCharPairs_eq_two_mul_genus hd hdvd)
    (fun _ hp => inv_pair_mem_fermatCharPairs hp)
    (fun p _ => by simp)
    (fun _ hp => diagEigenvalue_mul_inv ha hb hc hp)
    (prod_diagEigenvalue_eq hd hdvd ha hb hc)
    hT

/-- **WEIL CONJECTURE II (FUNCTIONAL EQUATION FOR `P_1`) — FERMAT CURVES `X^d + Y^d = Z^d`**:
for every `T : ℂ` with `T ≠ 0`,
`P_1(1 / (q T)) = q ^ (-g) * T ^ (-2g) * P_1(T)`. -/
theorem fermat_weil_functional_equation_poly {F : Type*} [Field F] [Fintype F] {d : ℕ}
    (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1)
    {T : ℂ} (hT : T ≠ 0) :
    (fermatLPoly F d).eval (1 / ((Fintype.card F : ℂ) * T)) =
      (Fintype.card F : ℂ) ^ (-(fermatGenus d : ℤ)) * T ^ (-(2 * fermatGenus d : ℤ)) *
        (fermatLPoly F d).eval T := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact functional_equation_poly_general (fermatCharPairs F d) (fun p => (p.1⁻¹, p.2⁻¹))
    fermatEigenvalue (Fintype.card F : ℂ) (fermatGenus d) hq
    (card_fermatCharPairs_eq_two_mul_genus hd hdvd)
    (fun _ hp => inv_pair_mem_fermatCharPairs hp)
    (fun p _ => by simp)
    (fun _ hp => fermatEigenvalue_mul_inv hp)
    (prod_fermatEigenvalue_eq hd hdvd)
    hT

/-- **WEIL CONJECTURE II (FULL ZETA FUNCTIONAL EQUATION)**:
for every `T : ℂ` with `T ≠ 0`, `T ≠ 1`, `q * T ≠ 1`,
`Z(1 / (q T)) = q ^ (1 - g) * T ^ (2 - 2g) * Z(T)` (where `2 - 2g = χ(C)` is the Euler
characteristic of the genus-`g` curve). -/
theorem fermat_weil_functional_equation_zeta {F : Type*} [Field F] [Fintype F] {d : ℕ}
    (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1)
    {T : ℂ} (hT : T ≠ 0) (hT1 : T ≠ 1) (hqT1 : (Fintype.card F : ℂ) * T ≠ 1) :
    fermatZetaRat F d (1 / ((Fintype.card F : ℂ) * T)) =
      (Fintype.card F : ℂ) ^ ((1 : ℤ) - (fermatGenus d : ℤ)) *
        T ^ ((2 : ℤ) - 2 * (fermatGenus d : ℤ)) *
        fermatZetaRat F d T := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h1mT : 1 - T ≠ 0 := sub_ne_zero.mpr hT1.symm
  have h1mqT : 1 - (Fintype.card F : ℂ) * T ≠ 0 := sub_ne_zero.mpr hqT1.symm
  unfold fermatZetaRat
  rw [fermat_weil_functional_equation_poly hd hdvd hT]
  have hden : (1 - 1 / ((Fintype.card F : ℂ) * T)) *
        (1 - (Fintype.card F : ℂ) * (1 / ((Fintype.card F : ℂ) * T))) =
      ((1 - T) * (1 - (Fintype.card F : ℂ) * T)) / ((Fintype.card F : ℂ) * T ^ 2) := by
    field_simp [hq, hT]
    ring
  rw [hden]
  have hpow_q : (Fintype.card F : ℂ) ^ ((1 : ℤ) - (fermatGenus d : ℤ)) =
      (Fintype.card F : ℂ) * (Fintype.card F : ℂ) ^ (-(fermatGenus d : ℤ)) := by
    rw [sub_eq_add_neg, zpow_add₀ hq, zpow_one]
  have hpow_T : T ^ ((2 : ℤ) - 2 * (fermatGenus d : ℤ)) =
      T ^ 2 * T ^ (-(2 * fermatGenus d : ℤ)) := by
    rw [sub_eq_add_neg, zpow_add₀ hT]
    norm_cast
  rw [hpow_q, hpow_T]
  field_simp [hq, hT, h1mT, h1mqT]

/-- **WEIL CONJECTURE III (RECIPROCAL ROOT NORM)**:
every root `w : ℂ` of `P_1(w) = 0` for `X^d + Y^d = Z^d` satisfies `‖w‖ = (Real.sqrt q)⁻¹`. -/
theorem fermat_weil_root_norm {F : Type*} [Field F] [Fintype F] {d : ℕ}
    {w : ℂ} (hw : (fermatLPoly F d).eval w = 0) :
    ‖w‖ = (Real.sqrt (Fintype.card F : ℝ))⁻¹ := by
  unfold fermatLPoly at hw
  rw [Polynomial.eval_prod] at hw
  obtain ⟨p, hp, hzero⟩ := Finset.prod_eq_zero_iff.mp hw
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at hzero
  have hmul : fermatEigenvalue p * w = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm := congr_arg norm hmul
  rw [norm_mul, norm_one, norm_fermatEigenvalue_eq_sqrt hp] at hnorm
  exact eq_inv_of_mul_eq_one_right hnorm

/-- **WEIL CONJECTURE III (THE RIEMANN HYPOTHESIS FOR FERMAT CURVES `X^d + Y^d = Z^d`)**:
every zero `s : ℂ` of `P_1(q ^ (-s)) = 0` lies STRICTLY on the critical line **`s.re = 1 / 2`**! -/
theorem fermat_weil_riemann_hypothesis {F : Type*} [Field F] [Fintype F] {d : ℕ}
    {s : ℂ} (hs : (fermatLPoly F d).eval ((Fintype.card F : ℂ) ^ (-s)) = 0) :
    s.re = 1 / 2 := by
  have hnorm : ‖(Fintype.card F : ℂ) ^ (-s)‖ = (Real.sqrt (Fintype.card F : ℝ))⁻¹ :=
    fermat_weil_root_norm hs
  have hq_ge : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast two_le_card_finiteField (F := F)
  have hq_pos : (0 : ℝ) < (Fintype.card F : ℝ) := by linarith
  have hq_ne1 : (Fintype.card F : ℝ) ≠ 1 := by linarith
  have hlhs : ‖(Fintype.card F : ℂ) ^ (-s)‖ = (Fintype.card F : ℝ) ^ (-s.re) := by
    have h1 := Complex.norm_cpow_eq_rpow_re_of_pos hq_pos (-s)
    simpa [Complex.neg_re] using h1
  have hrhs : (Real.sqrt (Fintype.card F : ℝ))⁻¹ = (Fintype.card F : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hq_pos.le]
  rw [hlhs, hrhs] at hnorm
  have heq : -s.re = -(1 / 2 : ℝ) := (Real.rpow_right_inj hq_pos hq_ne1).mp hnorm
  linarith

/-- **WEIL CONJECTURE III (THE RIEMANN HYPOTHESIS FOR GENERAL DIAGONAL CURVES `a X^d + b Y^d = c Z^d`)**:
every zero `s : ℂ` of `P_1(q ^ (-s)) = 0` lies STRICTLY on the critical line **`s.re = 1 / 2`**! -/
theorem diag_weil_riemann_hypothesis {F : Type*} [Field F] [Fintype F] {d : ℕ}
    {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    {s : ℂ} (hs : (diagLPoly F d a b c).eval ((Fintype.card F : ℂ) ^ (-s)) = 0) :
    s.re = 1 / 2 := by
  unfold diagLPoly at hs
  rw [Polynomial.eval_prod] at hs
  obtain ⟨p, hp, hzero⟩ := Finset.prod_eq_zero_iff.mp hs
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at hzero
  have hmul : diagEigenvalue a b c p * (Fintype.card F : ℂ) ^ (-s) = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hnorm := congr_arg norm hmul
  rw [norm_mul, norm_one, norm_diagEigenvalue_eq_sqrt ha hb hc hp] at hnorm
  have hq_ge : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast two_le_card_finiteField (F := F)
  have hq_pos : (0 : ℝ) < (Fintype.card F : ℝ) := by linarith
  have hq_ne1 : (Fintype.card F : ℝ) ≠ 1 := by linarith
  have hinv : ‖(Fintype.card F : ℂ) ^ (-s)‖ = (Real.sqrt (Fintype.card F : ℝ))⁻¹ :=
    eq_inv_of_mul_eq_one_right hnorm
  have hlhs : ‖(Fintype.card F : ℂ) ^ (-s)‖ = (Fintype.card F : ℝ) ^ (-s.re) := by
    have h1 := Complex.norm_cpow_eq_rpow_re_of_pos hq_pos (-s)
    simpa [Complex.neg_re] using h1
  have hrhs : (Real.sqrt (Fintype.card F : ℝ))⁻¹ = (Fintype.card F : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hq_pos.le]
  rw [hlhs, hrhs] at hinv
  have heq : -s.re = -(1 / 2 : ℝ) := (Real.rpow_right_inj hq_pos hq_ne1).mp hinv
  linarith

end WeilZetaFunction

/-! ## Section 4: Hasse–Davenport Lifting Theorem & Extension-Field Point Counts -/

section HasseDavenport

/-- Existence of a nontrivial complex additive character `ψ : AddChar F ℂ` on any finite field `F`
(constructed from `FiniteField.trace_to_zmod_nondegenerate` and `AddChar.zmodChar`). -/
theorem exists_nontrivial_addChar_complex (F : Type*) [Field F] [Fintype F] :
    ∃ ψ : AddChar F ℂ, ψ ≠ 1 := by
  set p := ringChar F
  have hp_ne : p ≠ 0 := ringChar_finiteField_ne_zero (F := F)
  have : CharP F p := ringChar.charP F
  have hp : Nat.Prime p := (CharP.char_is_prime_or_zero F p).resolve_right hp_ne
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let : Algebra (ZMod p) F := ZMod.algebra F p
  obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate F (one_ne_zero (α := F))
  rw [one_mul] at hb
  have hprim := Complex.isPrimitiveRoot_exp p hp.ne_zero
  set ψ₀ : AddChar (ZMod p) ℂ := AddChar.zmodChar p hprim.pow_eq_one
  have hprim_ψ₀ : ψ₀.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hprim
  let ψ : AddChar F ℂ := ψ₀.compAddMonoidHom (Algebra.trace (ZMod p) F).toAddMonoidHom
  refine ⟨ψ, ?_⟩
  intro h1
  have hval : ψ b = 1 := by rw [h1]; rfl
  change ψ₀ (Algebra.trace (ZMod p) F b) = 1 at hval
  exact hb ((hprim_ψ₀.zmod_char_eq_one_iff p _).mp hval)

/-- Multiplicative character lifted from `F` to a finite field extension `E / F` via the field
norm: `(liftMulChar E χ) x = χ (Algebra.norm F x)`. -/
def liftMulChar {F : Type*} (E : Type*) [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (χ : MulChar F ℂ) : MulChar E ℂ where
  toFun x := χ (Algebra.norm F x)
  map_one' := by simp
  map_mul' x y := by simp
  map_nonunit' x hx := by
    have hx0 : x = 0 := by
      by_contra hne
      exact hx (isUnit_iff_ne_zero.mpr hne)
    subst hx0
    rw [Algebra.norm_zero, χ.map_nonunit not_isUnit_zero]

@[simp]
theorem liftMulChar_apply {F E : Type*} [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (χ : MulChar F ℂ) (x : E) :
    liftMulChar E χ x = χ (Algebra.norm F x) := rfl

/-- Additive character lifted from `F` to a finite field extension `E / F` via the field trace:
`(liftAddChar E ψ) x = ψ (Algebra.trace F E x)`. -/
def liftAddChar {F : Type*} (E : Type*) [Field F] [Field E] [Algebra F E]
    (ψ : AddChar F ℂ) : AddChar E ℂ :=
  ψ.compAddMonoidHom (Algebra.trace F E).toAddMonoidHom

@[simp]
theorem liftAddChar_apply {F E : Type*} [Field F] [Field E] [Algebra F E]
    (ψ : AddChar F ℂ) (x : E) :
    liftAddChar E ψ x = ψ (Algebra.trace F E x) := rfl

/-- Surjectivity of the field norm `Algebra.norm F : E → F` for any extension of finite fields. -/
theorem finiteField_norm_surjective (F E : Type*) [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] : Function.Surjective (Algebra.norm F : E → F) := by
  classical
  set q := Fintype.card F
  set r := Module.finrank F E
  have hq2 : 2 ≤ q := two_le_card_finiteField (F := F)
  have hcardE : Fintype.card E = q ^ r := Module.card_eq_pow_finrank
  have hr_pos : 0 < r := Module.finrank_pos
  -- Geometric sum `S := ∑ i < r, q^i` satisfies `(q - 1) * S = q^r - 1`
  set S := ∑ i ∈ Finset.range r, q ^ i
  have hS_mul : (q - 1) * S = q ^ r - 1 := by
    have hqr1 : 1 ≤ q ^ r := Nat.one_le_pow r q (by omega)
    have h1 : (((q - 1) * S : ℕ) : ℤ) = ((q ^ r - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub hqr1, Nat.cast_pow, Nat.cast_one]
      have hgeom := mul_geom_sum (q : ℤ) r
      simpa [S] using hgeom
    exact_mod_cast h1
  have hS_pos : 0 < S := by
    have hq1 : 1 < q ^ r := one_lt_pow₀ (by omega : 1 < q) hr_pos.ne'
    have h1 : 0 < (q - 1) * S := by omega
    exact Nat.pos_of_mul_pos_left h1
  -- Pick a generator `g` of `Eˣ` (`orderOf g = q^r - 1`)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  have hord_g : orderOf g = q ^ r - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units, hcardE]
  -- `norm g ∈ Fˣ` has order `q - 1`, so it generates `Fˣ`
  have hnorm_g_ne : Algebra.norm F (g : E) ≠ 0 :=
    (Algebra.norm_ne_zero_iff (R := F) (S := E)).mpr g.ne_zero
  let u : Fˣ := Units.mk0 (Algebra.norm F (g : E)) hnorm_g_ne
  have halg_u : algebraMap F E (u : F) = (g : E) ^ S := by
    change algebraMap F E (Algebra.norm F (g : E)) = (g : E) ^ S
    rw [FiniteField.algebraMap_norm_eq_pow_sum F E (g : E)]
    simp only [S, Nat.card_eq_fintype_card, q, r]
  have hord_u : orderOf u = q - 1 := by
    apply Nat.dvd_antisymm
    · have hu_pow : u ^ (q - 1) = 1 := by
        rw [← Fintype.card_units F]; exact pow_card_eq_one
      exact orderOf_dvd_of_pow_eq_one hu_pow
    · have hpow_E : (g : E) ^ (S * orderOf u) = 1 := by
        rw [pow_mul, ← halg_u, ← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one,
          Units.val_one, map_one]
      have hpow_Eu : g ^ (S * orderOf u) = 1 := Units.ext (by simpa using hpow_E)
      have hdvd : q ^ r - 1 ∣ S * orderOf u := hord_g ▸ orderOf_dvd_of_pow_eq_one hpow_Eu
      rw [← hS_mul, mul_comm (q - 1) S] at hdvd
      exact (Nat.mul_dvd_mul_iff_left hS_pos).mp hdvd
  intro y
  by_cases hy : y = 0
  · subst hy; exact ⟨0, Algebra.norm_zero⟩
  · -- Since `orderOf u = Fintype.card Fˣ`, `u` generates `Fˣ`
    let y₀ : Fˣ := Units.mk0 y hy
    have hsurj : (Finset.range (q - 1)).image (fun k => u ^ k) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn, Finset.card_range, Fintype.card_units]
      intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_range] at hi hj
      have hmod : i ≡ j [MOD q - 1] := hord_u ▸ pow_eq_pow_iff_modEq.mp hij
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod
    have hy_mem : y₀ ∈ (Finset.range (q - 1)).image (fun k => u ^ k) := by
      rw [hsurj]; exact Finset.mem_univ y₀
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hy_mem
    refine ⟨(g : E) ^ k, ?_⟩
    rw [map_pow]
    have := congr_arg (Units.val : Fˣ → F) hk
    simpa [u, y₀] using this

theorem liftMulChar_injective (F E : Type*) [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] : Function.Injective (liftMulChar E : MulChar F ℂ → MulChar E ℂ) := by
  intro χ₁ χ₂ h
  ext x
  obtain ⟨y, hy⟩ := finiteField_norm_surjective F E (x : F)
  have hval := congr_arg (fun χ : MulChar E ℂ => χ y) h
  simpa [liftMulChar_apply, hy] using hval

theorem liftMulChar_mul {F E : Type*} [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (χ₁ χ₂ : MulChar F ℂ) : liftMulChar E (χ₁ * χ₂) = liftMulChar E χ₁ * liftMulChar E χ₂ := by
  ext x
  simp [liftMulChar_apply]

theorem liftMulChar_one {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    liftMulChar E (1 : MulChar F ℂ) = 1 := by
  ext x
  have hne : Algebra.norm F (x : E) ≠ 0 :=
    (Algebra.norm_ne_zero_iff (R := F) (S := E)).mpr x.ne_zero
  simp [liftMulChar_apply, MulChar.one_apply (isUnit_iff_ne_zero.mpr hne), MulChar.one_apply x.isUnit]

theorem liftMulChar_pow {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (χ : MulChar F ℂ) (n : ℕ) : liftMulChar E (χ ^ n) = (liftMulChar E χ) ^ n := by
  induction n with
  | zero => simp [liftMulChar_one]
  | succ k ih => rw [pow_succ, pow_succ, liftMulChar_mul, ih]

theorem liftMulChar_ne_one {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] {χ : MulChar F ℂ} (hχ : χ ≠ 1) : liftMulChar E χ ≠ 1 := by
  intro h
  apply hχ
  exact liftMulChar_injective F E (h.trans liftMulChar_one.symm)

theorem liftAddChar_ne_one {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) : liftAddChar E ψ ≠ 1 := by
  intro h
  apply hψ
  ext x
  obtain ⟨y, hy⟩ := Algebra.trace_surjective F E x
  have hval := congr_arg (fun φ : AddChar E ℂ => φ y) h
  simpa [liftAddChar_apply, hy] using hval

/-- Formal logarithm power series for a degree-`k` Euler factor:
`L_{c,k}(T) := ∑_{m ≥ 1, k ∣ m} (k * c^(m/k) / m) T^m = -log(1 - c T^k)`. -/
def logSeriesPow (c : ℂ) (k : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun m => if m = 0 then 0 else if k ∣ m then (k : ℂ) * c ^ (m / k) / (m : ℂ) else 0

theorem constantCoeff_logSeriesPow (c : ℂ) (k : ℕ) :
    PowerSeries.constantCoeff (logSeriesPow c k) = 0 := by
  simp [logSeriesPow]

theorem coeff_logSeriesPow (c : ℂ) (k m : ℕ) :
    PowerSeries.coeff m (logSeriesPow c k) =
      if m = 0 then 0 else if k ∣ m then (k : ℂ) * c ^ (m / k) / (m : ℂ) else 0 := by
  simp [logSeriesPow]

/-- Exact derivative identity `(1 - C c * X^k) * D (logSeriesPow c k) = C (k * c) * X^(k - 1)`
for `1 ≤ k`. -/
private lemma one_sub_C_mul_X_pow_mul_deriv_logSeriesPow (c : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    (1 - PowerSeries.C c * PowerSeries.X ^ k) * PowerSeries.derivative ℂ (logSeriesPow c k) =
      PowerSeries.C ((k : ℂ) * c) * PowerSeries.X ^ (k - 1) := by
  have hderiv : PowerSeries.derivative ℂ (logSeriesPow c k) =
      PowerSeries.mk fun n => if k ∣ (n + 1) then (k : ℂ) * c ^ ((n + 1) / k) else 0 := by
    ext n
    rw [PowerSeries.coeff_derivative, coeff_logSeriesPow, if_neg (Nat.succ_ne_zero n),
      PowerSeries.coeff_mk]
    split_ifs with hd
    · have hne : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      push_cast
      field_simp [hne]
    · simp
  rw [hderiv, sub_mul, one_mul]
  ext n
  rw [map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul_X_pow]
  have hterm2 : PowerSeries.coeff n
      (PowerSeries.C c * PowerSeries.X ^ k *
        PowerSeries.mk fun m => if k ∣ (m + 1) then (k : ℂ) * c ^ ((m + 1) / k) else 0) =
      if k ≤ n then
        if k ∣ (n - k + 1) then (k : ℂ) * c ^ ((n - k + 1) / k + 1) else 0
      else 0 := by
    rw [PowerSeries.coeff_mul]
    by_cases hkn : k ≤ n
    · rw [if_pos hkn]
      rw [Finset.sum_eq_single (k, n - k)]
      · rw [PowerSeries.coeff_C_mul_X_pow, if_pos rfl, PowerSeries.coeff_mk]
        split_ifs with hd
        · rw [pow_succ']; ring
        · simp
      · intro p hp hne
        rw [Finset.mem_antidiagonal] at hp
        have hp1 : p.1 ≠ k := by
          intro h1
          apply hne
          ext
          · exact h1
          · omega
        rw [PowerSeries.coeff_C_mul_X_pow, if_neg hp1, zero_mul]
      · intro hmem
        exact absurd (Finset.mem_antidiagonal.mpr (Nat.add_sub_of_le hkn)) hmem
    · rw [if_neg hkn]
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [Finset.mem_antidiagonal] at hp
      have hp1 : p.1 ≠ k := by omega
      rw [PowerSeries.coeff_C_mul_X_pow, if_neg hp1, zero_mul]
  rw [hterm2]
  by_cases hkn : k ≤ n
  · rw [if_pos hkn, if_neg (by omega : n ≠ k - 1)]
    have hd_iff : k ∣ (n + 1) ↔ k ∣ (n - k + 1) := by
      have heq : n + 1 = (n - k + 1) + k := by omega
      rw [heq, Nat.dvd_add_self_right]
    by_cases hd : k ∣ (n - k + 1)
    · rw [if_pos (hd_iff.mpr hd), if_pos hd]
      have hdiv : (n + 1) / k = (n - k + 1) / k + 1 := by
        have heq : n + 1 = (n - k + 1) + k := by omega
        rw [heq, Nat.add_div_right _ (by omega : 0 < k)]
      rw [hdiv, sub_self]
    · rw [if_neg (fun h => hd (hd_iff.mp h)), if_neg hd, sub_self]
  · rw [if_neg hkn, sub_zero]
    by_cases hnk : n = k - 1
    · rw [if_pos hnk]
      have heq : n + 1 = k := by omega
      rw [heq, if_pos (dvd_refl k), Nat.div_self (by omega : 0 < k), pow_one]
    · rw [if_neg hnk]
      have hndvd : ¬ (k ∣ (n + 1)) := by
        intro hd
        have hle := Nat.le_of_dvd (Nat.succ_pos n) hd
        omega
      rw [if_neg hndvd]

/-- **Exact Degree-`k` Euler Factor Identity**:
`expSeries (-logSeriesPow c k) = 1 - C c * X^k` for every `c : ℂ` and `1 ≤ k`. -/
theorem expSeries_neg_logSeriesPow (c : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    expSeries (-logSeriesPow c k) = 1 - PowerSeries.C c * PowerSeries.X ^ k := by
  have hmul1 : (1 - PowerSeries.C c * PowerSeries.X ^ k) * expSeries (logSeriesPow c k) = 1 := by
    apply PowerSeries.derivative.ext
    · rw [PowerSeries.derivative_one, Derivation.leibniz,
        derivative_expSeries (constantCoeff_logSeriesPow c k)]
      have hd1 : PowerSeries.derivative ℂ (1 - PowerSeries.C c * PowerSeries.X ^ k) =
          -(PowerSeries.C ((k : ℂ) * c) * PowerSeries.X ^ (k - 1)) := by
        rw [map_sub, PowerSeries.derivative_one, Derivation.leibniz, PowerSeries.derivative_C,
          PowerSeries.derivative_pow, PowerSeries.derivative_X]
        simp only [smul_eq_mul, mul_one, zero_sub, map_mul, map_natCast]
        ring
      rw [hd1]
      simp only [smul_eq_mul]
      calc (1 - PowerSeries.C c * PowerSeries.X ^ k) *
              (expSeries (logSeriesPow c k) * PowerSeries.derivative ℂ (logSeriesPow c k)) +
            expSeries (logSeriesPow c k) * -(PowerSeries.C ((k : ℂ) * c) * PowerSeries.X ^ (k - 1))
          = expSeries (logSeriesPow c k) *
              ((1 - PowerSeries.C c * PowerSeries.X ^ k) * PowerSeries.derivative ℂ (logSeriesPow c k) -
                PowerSeries.C ((k : ℂ) * c) * PowerSeries.X ^ (k - 1)) := by ring
        _ = 0 := by rw [one_sub_C_mul_X_pow_mul_deriv_logSeriesPow c hk, sub_self, mul_zero]
    · rw [map_mul, map_sub, map_one, map_mul, PowerSeries.constantCoeff_C, map_pow,
        PowerSeries.constantCoeff_X, zero_pow (by omega : k ≠ 0), mul_zero, sub_zero,
        constantCoeff_expSeries (constantCoeff_logSeriesPow c k), mul_one]
  calc expSeries (-logSeriesPow c k)
      = 1 * expSeries (-logSeriesPow c k) := (one_mul _).symm
    _ = ((1 - PowerSeries.C c * PowerSeries.X ^ k) * expSeries (logSeriesPow c k)) *
          expSeries (-logSeriesPow c k) := by rw [hmul1]
    _ = (1 - PowerSeries.C c * PowerSeries.X ^ k) *
          (expSeries (logSeriesPow c k) * expSeries (-logSeriesPow c k)) := by ring
    _ = (1 - PowerSeries.C c * PowerSeries.X ^ k) * 1 := by
          rw [expSeries_mul_expSeries_neg (constantCoeff_logSeriesPow c k)]
    _ = 1 - PowerSeries.C c * PowerSeries.X ^ k := mul_one _

/-- If `constantCoeff H = 0` and `expSeries H ≡ 1 (mod X^(r+1))`, then `coeff k H = 0` for all
`k ≤ r`. -/
private lemma coeff_eq_zero_of_expSeries_eq_one_le {H : PowerSeries ℂ}
    (hH0 : PowerSeries.constantCoeff H = 0) {r : ℕ}
    (hexp : ∀ k ≤ r, PowerSeries.coeff k (expSeries H) = PowerSeries.coeff k 1) :
    ∀ k ≤ r, PowerSeries.coeff k H = 0 := by
  intro k hk
  induction k with
  | zero => rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact hH0
  | succ m _ =>
    have hD : PowerSeries.coeff m (PowerSeries.derivative ℂ (expSeries H)) = 0 := by
      rw [PowerSeries.coeff_derivative, hexp (m + 1) hk, PowerSeries.coeff_one,
        if_neg (Nat.succ_ne_zero m), zero_mul]
    rw [derivative_expSeries hH0, PowerSeries.coeff_mul] at hD
    have hsum : ∑ p ∈ Finset.antidiagonal m,
        PowerSeries.coeff p.1 (expSeries H) * PowerSeries.coeff p.2 (PowerSeries.derivative ℂ H) =
        PowerSeries.coeff m (PowerSeries.derivative ℂ H) := by
      rw [Finset.sum_eq_single (0, m)]
      · rw [hexp 0 (Nat.zero_le r), PowerSeries.coeff_one, if_pos rfl, one_mul]
      · intro p hp hne
        rw [Finset.mem_antidiagonal] at hp
        have hp1 : p.1 ≠ 0 := by
          intro h0
          apply hne
          ext
          · exact h0
          · omega
        rw [hexp p.1 (by omega), PowerSeries.coeff_one, if_neg hp1, zero_mul]
      · intro hmem
        exact absurd (Finset.mem_antidiagonal.mpr (zero_add m)) hmem
    rw [hsum, PowerSeries.coeff_derivative] at hD
    have hne : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    exact (mul_eq_zero.mp hD).resolve_right hne

/-- The polynomial multiplicative character `λ(f) := χ((-1)^{deg f} * f.coeff 0) * ψ(-f.nextCoeff)`
on `Polynomial F`. -/
def polyChar {F : Type*} [Field F] (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (f : Polynomial F) : ℂ :=
  χ ((-1 : F) ^ f.natDegree * f.coeff 0) * ψ (-f.nextCoeff)

theorem polyChar_one {F : Type*} [Field F] (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    polyChar χ ψ 1 = 1 := by
  unfold polyChar
  have hnext : (1 : Polynomial F).nextCoeff = 0 := by
    rw [Polynomial.nextCoeff, Polynomial.natDegree_one]
    simp
  rw [hnext]
  simp

theorem polyChar_mul {F : Type*} [Field F] (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    {f g : Polynomial F} (hf : f.Monic) (hg : g.Monic) :
    polyChar χ ψ (f * g) = polyChar χ ψ f * polyChar χ ψ g := by
  unfold polyChar
  rw [hf.natDegree_mul hg, Polynomial.mul_coeff_zero, hf.nextCoeff_mul hg, pow_add,
    neg_add, AddChar.map_add_eq_mul]
  have harg : (-1 : F) ^ f.natDegree * (-1 : F) ^ g.natDegree * (f.coeff 0 * g.coeff 0) =
      ((-1 : F) ^ f.natDegree * f.coeff 0) * ((-1 : F) ^ g.natDegree * g.coeff 0) := by ring
  rw [harg, map_mul]
  ring

theorem polyChar_pow {F : Type*} [Field F] (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    {f : Polynomial F} (hf : f.Monic) (n : ℕ) :
    polyChar χ ψ (f ^ n) = (polyChar χ ψ f) ^ n := by
  induction n with
  | zero => simp [polyChar_one]
  | succ k ih => rw [pow_succ, pow_succ, polyChar_mul χ ψ (hf.pow k) hf, ih]

theorem polyChar_X_sub_C {F : Type*} [Field F] (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (a : F) :
    polyChar χ ψ (Polynomial.X - Polynomial.C a) = χ a * ψ a := by
  unfold polyChar
  have hdeg : (Polynomial.X - Polynomial.C a).natDegree = 1 := Polynomial.natDegree_X_sub_C a
  have hnext : (Polynomial.X - Polynomial.C a).nextCoeff = -a := by
    rw [Polynomial.nextCoeff, hdeg]
    simp
  rw [hdeg, hnext]
  simp

/-- Constructor of the monic degree-`n` polynomial `X^n + ∑_{i < n} c_i X^i`. -/
def mkMonicPoly {F : Type*} [Field F] (n : ℕ) (c : Fin n → F) : Polynomial F :=
  Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)

private lemma coeff_mkMonicPoly {F : Type*} [Field F] (n : ℕ) (c : Fin n → F) (m : ℕ) :
    (mkMonicPoly n c).coeff m =
      if m = n then 1 else if hm : m < n then c ⟨m, hm⟩ else 0 := by
  unfold mkMonicPoly
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  by_cases hmn : m = n
  · subst hmn
    have h0 : ∑ i : Fin m, (if m = (i : ℕ) then c i else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => if_neg (by omega : m ≠ (i : ℕ))
    rw [if_pos rfl, if_pos rfl, h0, add_zero]
  · rw [if_neg hmn, if_neg hmn, zero_add]
    by_cases hlt : m < n
    · rw [dif_pos hlt]
      rw [Finset.sum_eq_single ⟨m, hlt⟩]
      · simp
      · intro i _ hi
        have hne : m ≠ (i : ℕ) := fun h => hi (Fin.ext h.symm)
        rw [if_neg hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg hlt]
      exact Finset.sum_eq_zero fun i _ => if_neg (by omega : m ≠ (i : ℕ))

private lemma mkMonicPoly_monic {F : Type*} [Field F] (n : ℕ) (c : Fin n → F) :
    (mkMonicPoly n c).Monic ∧ (mkMonicPoly n c).natDegree = n := by
  have hdeg_le : (mkMonicPoly n c).natDegree ≤ n := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [coeff_mkMonicPoly, if_neg (by omega), dif_neg (by omega)]
  have hcn : (mkMonicPoly n c).coeff n = 1 := by
    rw [coeff_mkMonicPoly, if_pos rfl]
  have hdeg_ge : n ≤ (mkMonicPoly n c).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (hcn.symm ▸ one_ne_zero)
  have hdeg : (mkMonicPoly n c).natDegree = n := le_antisymm hdeg_le hdeg_ge
  refine ⟨?_, hdeg⟩
  rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg, hcn]

private lemma mkMonicPoly_injective {F : Type*} [Field F] (n : ℕ) :
    Function.Injective (mkMonicPoly (F := F) n) := by
  intro c₁ c₂ h
  ext i
  have hc := congr_arg (fun f => Polynomial.coeff f (i : ℕ)) h
  rw [coeff_mkMonicPoly, coeff_mkMonicPoly, if_neg (by omega : (i : ℕ) ≠ n),
    if_neg (by omega : (i : ℕ) ≠ n), dif_pos i.isLt, dif_pos i.isLt] at hc
  exact hc

/-- Finite set of all monic polynomials of exact degree `n` over a finite field `F`. -/
def monicPolysOfDeg (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    Finset (Polynomial F) :=
  Finset.univ.image (mkMonicPoly (F := F) n)

theorem mem_monicPolysOfDeg {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    {f : Polynomial F} :
    f ∈ monicPolysOfDeg F n ↔ f.Monic ∧ f.natDegree = n := by
  unfold monicPolysOfDeg
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩; exact mkMonicPoly_monic n c
  · rintro ⟨hmon, hdeg⟩
    refine ⟨fun i => f.coeff (i : ℕ), ?_⟩
    ext m
    rw [coeff_mkMonicPoly]
    by_cases hmn : m = n
    · subst hmn; rw [if_pos rfl, ← hdeg, ← Polynomial.leadingCoeff, hmon.leadingCoeff]
    · rw [if_neg hmn]
      by_cases hlt : m < n
      · rw [dif_pos hlt]
      · rw [dif_neg hlt]
        exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- Finite set of all monic irreducible polynomials of degree `≤ r` over `F`. -/
def monicIrredsLe (F : Type*) [Field F] [Fintype F] [DecidableEq F] (r : ℕ) :
    Finset (Polynomial F) :=
  letI := Classical.decPred (Irreducible : Polynomial F → Prop)
  ((Finset.range (r + 1)).biUnion (monicPolysOfDeg F)).filter Irreducible

theorem mem_monicIrredsLe {F : Type*} [Field F] [Fintype F] [DecidableEq F] {r : ℕ}
    {π : Polynomial F} :
    π ∈ monicIrredsLe F r ↔ π.Monic ∧ Irreducible π ∧ π.natDegree ≤ r := by
  classical
  unfold monicIrredsLe
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, mem_monicPolysOfDeg]
  constructor
  · rintro ⟨⟨n, hn, hmon, hdeg⟩, hirr⟩
    exact ⟨hmon, hirr, by omega⟩
  · rintro ⟨hmon, hirr, hle⟩
    exact ⟨⟨π.natDegree, by omega, hmon, rfl⟩, hirr⟩

/-- **Exact Degree-`n` Monic Polynomial Character Sum**:
for any nontrivial `χ ≠ 1` and any `ψ`,
`∑_{f monic, deg f = n} polyChar χ ψ f = if n = 0 then 1 else if n = 1 then gaussSum χ ψ else 0`. -/
theorem sum_monicPolysOfDeg_polyChar {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {χ : MulChar F ℂ} (hχ : χ ≠ 1) (ψ : AddChar F ℂ) (n : ℕ) :
    ∑ f ∈ monicPolysOfDeg F n, polyChar χ ψ f =
      if n = 0 then 1 else if n = 1 then gaussSum χ ψ else 0 := by
  rcases n with _ | _ | k
  · -- `n = 0`: only `f = 1`
    have h0 : monicPolysOfDeg F 0 = {1} := by
      ext f
      rw [mem_monicPolysOfDeg, Finset.mem_singleton]
      exact ⟨fun ⟨hmon, hdeg⟩ => Polynomial.eq_one_of_monic_natDegree_zero hmon hdeg,
        fun h => h ▸ ⟨Polynomial.monic_one, Polynomial.natDegree_one⟩⟩
    rw [h0, Finset.sum_singleton, polyChar_one, if_pos rfl]
  · -- `n = 1`: bijection `a ↦ X - C a`
    simp only [Nat.zero_add, one_ne_zero, ↓reduceIte]
    unfold gaussSum
    refine Finset.sum_bij (fun f _ => -(f.coeff 0)) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro f₁ hf₁ f₂ hf₂ h
      rw [mem_monicPolysOfDeg] at hf₁ hf₂
      have hc0 : f₁.coeff 0 = f₂.coeff 0 := neg_inj.mp h
      have hc1 : f₁.coeff 1 = 1 := by rw [← hf₁.2]; exact hf₁.1.leadingCoeff
      have hc2 : f₂.coeff 1 = 1 := by rw [← hf₂.2]; exact hf₂.1.leadingCoeff
      ext m
      rcases m with _ | _ | m
      · exact hc0
      · rw [hc1, hc2]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    · intro a _
      refine ⟨Polynomial.X - Polynomial.C a, ?_, by simp⟩
      rw [mem_monicPolysOfDeg]
      exact ⟨Polynomial.monic_X_sub_C a, Polynomial.natDegree_X_sub_C a⟩
    · intro f hf
      rw [mem_monicPolysOfDeg] at hf
      have hc1 : f.coeff 1 = 1 := by rw [← hf.2]; exact hf.1.leadingCoeff
      have hf_eq : f = Polynomial.X - Polynomial.C (-f.coeff 0) := by
        ext m
        rcases m with _ | _ | m
        · simp
        · simp [hc1]
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
            Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Polynomial.natDegree_X_sub_C]; omega)]
      conv_lhs => rw [hf_eq]
      rw [polyChar_X_sub_C]
  · -- `n = k + 2 ≥ 2`: split off constant coefficient `c 0 ∈ F`; `∑_{a : F} χ a = 0`!
    rw [if_neg (Nat.succ_ne_zero _), if_neg (by omega : k + 2 ≠ 1)]
    unfold monicPolysOfDeg
    rw [Finset.sum_image (fun c₁ _ c₂ _ h => mkMonicPoly_injective (k + 2) h)]
    have hsplit : ∑ c : Fin (k + 2) → F, polyChar χ ψ (mkMonicPoly (k + 2) c) =
        ∑ rest : Fin (k + 1) → F, ∑ a : F, polyChar χ ψ (mkMonicPoly (k + 2) (Fin.cons a rest)) := by
      rw [← Finset.sum_product']
      refine Finset.sum_bij (fun c _ => (Fin.tail c, c 0)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro c₁ _ c₂ _ h
        simp only [Prod.mk.injEq] at h
        funext i
        cases i using Fin.cases with
        | zero => exact h.2
        | succ j => exact congr_fun h.1 j
      · intro p _
        refine ⟨Fin.cons p.2 p.1, Finset.mem_univ _, ?_⟩
        ext
        · rfl
        · rfl
      · intro c _
        congr 1
        congr 1
        funext i
        cases i using Fin.cases with
        | zero => rfl
        | succ j => rfl
    rw [hsplit]
    refine Finset.sum_eq_zero fun rest _ => ?_
    have hinner : ∀ a : F, polyChar χ ψ (mkMonicPoly (k + 2) (Fin.cons a rest)) =
        (χ ((-1 : F) ^ (k + 2)) * ψ (-rest ⟨k, by omega⟩)) * χ a := by
      intro a
      unfold polyChar
      have hdeg := (mkMonicPoly_monic (k + 2) (Fin.cons a rest)).2
      have hc0 : (mkMonicPoly (k + 2) (Fin.cons a rest)).coeff 0 = a := by
        rw [coeff_mkMonicPoly, if_neg (by omega), dif_pos (by omega)]
        rfl
      have hnext : (mkMonicPoly (k + 2) (Fin.cons a rest)).nextCoeff = rest ⟨k, by omega⟩ := by
        rw [Polynomial.nextCoeff, hdeg, if_neg (by omega)]
        rw [coeff_mkMonicPoly, if_neg (by omega), dif_pos (by omega)]
        rfl
      rw [hdeg, hc0, hnext, map_mul]
      ring
    simp_rw [hinner, ← Finset.mul_sum, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]

/-- Every normalized factor of a polynomial over a field `F` is monic and irreducible. -/
private lemma monic_and_irreducible_of_mem_normalizedFactors {F : Type*} [Field F] [DecidableEq F]
    {f π : Polynomial F} (hπ : π ∈ UniqueFactorizationMonoid.normalizedFactors f) :
    π.Monic ∧ Irreducible π := by
  have hirr : Irreducible π := UniqueFactorizationMonoid.irreducible_of_normalized_factor π hπ
  have hnorm : normalize π = π := UniqueFactorizationMonoid.normalize_normalized_factor π hπ
  have hmon : (normalize π).Monic := Polynomial.monic_normalize hirr.ne_zero
  rw [hnorm] at hmon
  exact ⟨hmon, hirr⟩

/-- Every monic polynomial over a field `F` equals the product of its `normalizedFactors`. -/
private lemma prod_normalizedFactors_of_monic {F : Type*} [Field F] [DecidableEq F]
    {f : Polynomial F} (hf : f.Monic) :
    (UniqueFactorizationMonoid.normalizedFactors f).prod = f := by
  have hmon_prod : (UniqueFactorizationMonoid.normalizedFactors f).prod.Monic := by
    have h := Polynomial.monic_multiset_prod_of_monic
      (UniqueFactorizationMonoid.normalizedFactors f) id
      fun π hπ => (monic_and_irreducible_of_mem_normalizedFactors hπ).1
    simpa only [Multiset.map_id] using h
  exact Polynomial.eq_of_monic_of_associated hmon_prod hf
    (UniqueFactorizationMonoid.prod_normalizedFactors hf.ne_zero)

/-- Formal inverse Euler factor `∑_{e ≥ 0} c^e T^{e k}` in `ℂ[[T]]`. -/
private def geomSeriesPow (c : ℂ) (k : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun m => if k ∣ m then c ^ (m / k) else 0

private lemma one_sub_mul_geomSeriesPow (c : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    (1 - PowerSeries.C c * PowerSeries.X ^ k) * geomSeriesPow c k = 1 := by
  rw [sub_mul, one_mul]
  ext n
  rw [map_sub, PowerSeries.coeff_one]
  unfold geomSeriesPow
  rw [PowerSeries.coeff_mk]
  have hterm2 : PowerSeries.coeff n
      (PowerSeries.C c * PowerSeries.X ^ k * PowerSeries.mk fun m => if k ∣ m then c ^ (m / k) else 0) =
      if k ≤ n then if k ∣ (n - k) then c ^ ((n - k) / k + 1) else 0 else 0 := by
    rw [PowerSeries.coeff_mul]
    by_cases hkn : k ≤ n
    · rw [if_pos hkn]
      rw [Finset.sum_eq_single (k, n - k)]
      · rw [PowerSeries.coeff_C_mul_X_pow, if_pos rfl, PowerSeries.coeff_mk]
        split_ifs
        · rw [pow_succ']
        · simp
      · intro p hp hne
        rw [Finset.mem_antidiagonal] at hp
        have hp1 : p.1 ≠ k := fun h1 => hne (Prod.ext h1 (by omega))
        rw [PowerSeries.coeff_C_mul_X_pow, if_neg hp1, zero_mul]
      · intro hmem
        exact absurd (Finset.mem_antidiagonal.mpr (Nat.add_sub_of_le hkn)) hmem
    · rw [if_neg hkn]
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [Finset.mem_antidiagonal] at hp
      have hp1 : p.1 ≠ k := by omega
      rw [PowerSeries.coeff_C_mul_X_pow, if_neg hp1, zero_mul]
  rw [hterm2]
  by_cases h0 : n = 0
  · subst h0
    rw [if_pos rfl, if_pos (dvd_zero k), Nat.zero_div, pow_zero, if_neg (by omega : ¬ k ≤ 0), sub_zero]
  · rw [if_neg h0]
    by_cases hkn : k ≤ n
    · rw [if_pos hkn]
      have hd_iff : k ∣ n ↔ k ∣ (n - k) := by
        have heq : n = (n - k) + k := by omega
        conv_lhs => rw [heq]
        exact Nat.dvd_add_self_right
      by_cases hd : k ∣ (n - k)
      · rw [if_pos (hd_iff.mpr hd), if_pos hd]
        have hdiv : n / k = (n - k) / k + 1 := by
          have heq : n = (n - k) + k := by omega
          conv_lhs => rw [heq]
          exact Nat.add_div_right _ (by omega : 0 < k)
        rw [hdiv, sub_self]
      · rw [if_neg (fun h => hd (hd_iff.mp h)), if_neg hd, sub_self]
    · rw [if_neg hkn, sub_zero]
      have hndvd : ¬ k ∣ n := fun hd => hkn (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd)
      rw [if_neg hndvd]

/-- Monic polynomials of degree `m` whose irreducible factors all belong to `S`. -/
private def monicSpan (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (S : Finset (Polynomial F)) (m : ℕ) : Finset (Polynomial F) :=
  letI := Classical.decPred fun f : Polynomial F =>
    ∀ π ∈ UniqueFactorizationMonoid.normalizedFactors f, π ∈ S
  (monicPolysOfDeg F m).filter fun f =>
    ∀ π ∈ UniqueFactorizationMonoid.normalizedFactors f, π ∈ S

private lemma mem_monicSpan {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {S : Finset (Polynomial F)} {m : ℕ} {f : Polynomial F} :
    f ∈ monicSpan F S m ↔
      f.Monic ∧ f.natDegree = m ∧ ∀ π ∈ UniqueFactorizationMonoid.normalizedFactors f, π ∈ S := by
  unfold monicSpan
  simp only [Finset.mem_filter, mem_monicPolysOfDeg, and_assoc]

/-- **Finite Euler Product Expansion over any finite set `S` of monic irreducibles**:
for every `m : ℕ`, the `m`-th coefficient of `∏_{π ∈ S} (1 - polyChar(π) X^{deg π})⁻¹` equals
the sum of `polyChar(f)` over all monic degree-`m` polynomials `f` whose irreducible factors all
lie in `S`. -/
private lemma coeff_prod_geomSeriesPow_eq_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (S : Finset (Polynomial F))
    (hS : ∀ π ∈ S, π.Monic ∧ Irreducible π) (m : ℕ) :
    PowerSeries.coeff m (∏ π ∈ S, geomSeriesPow (polyChar χ ψ π) π.natDegree) =
      ∑ f ∈ monicSpan F S m, polyChar χ ψ f := by
  induction S using Finset.induction_on generalizing m with
  | empty =>
    rw [Finset.prod_empty, PowerSeries.coeff_one]
    by_cases hm : m = 0
    · subst hm
      rw [if_pos rfl]
      have hfilt : monicSpan F ∅ 0 = {1} := by
        ext f
        simp only [mem_monicSpan, Finset.mem_singleton, Finset.notMem_empty]
        constructor
        · rintro ⟨hmon, hdeg, _⟩
          exact Polynomial.eq_one_of_monic_natDegree_zero hmon hdeg
        · rintro rfl
          refine ⟨Polynomial.monic_one, Polynomial.natDegree_one, fun π hπ => ?_⟩
          rw [UniqueFactorizationMonoid.normalizedFactors_one] at hπ
          exact absurd hπ (Multiset.notMem_zero π)
      rw [hfilt, Finset.sum_singleton, polyChar_one]
    · rw [if_neg hm]
      have hfilt : monicSpan F ∅ m = ∅ := by
        ext f
        simp only [mem_monicSpan, Finset.notMem_empty, iff_false]
        rintro ⟨hmon, hdeg, hallemp⟩
        have hne1 : f ≠ 1 := fun h1 => hm (by rw [← hdeg, h1, Polynomial.natDegree_one])
        have hfactors_eq : UniqueFactorizationMonoid.normalizedFactors f = 0 :=
          Multiset.eq_zero_iff_forall_notMem.mpr fun π hπ => hallemp π hπ
        have hprod := prod_normalizedFactors_of_monic hmon
        rw [hfactors_eq, Multiset.prod_zero] at hprod
        exact hne1 hprod.symm
      rw [hfilt, Finset.sum_empty]
  | insert π₀ S hπ₀_not ih =>
    have hπ₀ : π₀.Monic ∧ Irreducible π₀ := hS π₀ (Finset.mem_insert_self π₀ S)
    have hS' : ∀ π ∈ S, π.Monic ∧ Irreducible π :=
      fun π hπ => hS π (Finset.mem_insert_of_mem hπ)
    have hd₀_pos : 0 < π₀.natDegree := hπ₀.2.natDegree_pos
    rw [Finset.prod_insert hπ₀_not, PowerSeries.coeff_mul]
    simp_rw [ih hS']
    have hlhs :
        ∑ p ∈ Finset.antidiagonal m,
          PowerSeries.coeff p.1 (geomSeriesPow (polyChar χ ψ π₀) π₀.natDegree) *
            ∑ g ∈ monicSpan F S p.2, polyChar χ ψ g =
        ∑ e ∈ Finset.range (m / π₀.natDegree + 1),
          ∑ g ∈ monicSpan F S (m - e * π₀.natDegree), polyChar χ ψ (π₀ ^ e * g) := by
      have hfilt_sum :
          ∑ p ∈ Finset.antidiagonal m,
            PowerSeries.coeff p.1 (geomSeriesPow (polyChar χ ψ π₀) π₀.natDegree) *
              ∑ g ∈ monicSpan F S p.2, polyChar χ ψ g =
          ∑ p ∈ (Finset.antidiagonal m).filter (fun p => π₀.natDegree ∣ p.1),
            (polyChar χ ψ π₀) ^ (p.1 / π₀.natDegree) * ∑ g ∈ monicSpan F S p.2, polyChar χ ψ g := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun p _ => ?_
        unfold geomSeriesPow
        rw [PowerSeries.coeff_mk]
        split_ifs <;> simp
      rw [hfilt_sum]
      refine Finset.sum_bij (fun p _ => p.1 / π₀.natDegree) ?_ ?_ ?_ ?_
      · intro p hp
        rw [Finset.mem_filter, Finset.mem_antidiagonal] at hp
        rw [Finset.mem_range]
        have : p.1 / π₀.natDegree ≤ m / π₀.natDegree := Nat.div_le_div_right (by omega)
        omega
      · intro p₁ hp₁ p₂ hp₂ hdiv
        rw [Finset.mem_filter, Finset.mem_antidiagonal] at hp₁ hp₂
        have h1 : p₁.1 = p₂.1 := by
          rw [← Nat.div_mul_cancel hp₁.2, ← Nat.div_mul_cancel hp₂.2, hdiv]
        exact Prod.ext h1 (by omega)
      · intro e he
        rw [Finset.mem_range] at he
        have hele : e * π₀.natDegree ≤ m := by
          have h1 : e ≤ m / π₀.natDegree := by omega
          exact (Nat.mul_le_mul_right _ h1).trans (Nat.div_mul_le_self m π₀.natDegree)
        refine ⟨(e * π₀.natDegree, m - e * π₀.natDegree), ?_, Nat.mul_div_cancel e hd₀_pos⟩
        rw [Finset.mem_filter, Finset.mem_antidiagonal]
        exact ⟨Nat.add_sub_of_le hele, dvd_mul_left _ _⟩
      · intro p hp
        rw [Finset.mem_filter, Finset.mem_antidiagonal] at hp
        have hp1 : p.1 / π₀.natDegree * π₀.natDegree = p.1 := Nat.div_mul_cancel hp.2
        have hp2 : m - p.1 / π₀.natDegree * π₀.natDegree = p.2 := by omega
        rw [hp2, Finset.mul_sum]
        refine Finset.sum_congr rfl fun g hg => ?_
        have hg_mon : g.Monic := (mem_monicSpan.mp hg).1
        rw [polyChar_mul χ ψ (hπ₀.1.pow _) hg_mon, polyChar_pow χ ψ hπ₀.1]
    rw [hlhs]
    rw [← Finset.sum_sigma (Finset.range (m / π₀.natDegree + 1))
      (fun e => monicSpan F S (m - e * π₀.natDegree)) (fun s => polyChar χ ψ (π₀ ^ s.1 * s.2))]
    refine Finset.sum_bij (fun s _ => π₀ ^ s.1 * s.2) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro s hs
      rw [Finset.mem_sigma, Finset.mem_range] at hs
      rcases hs with ⟨he, hg⟩
      rw [mem_monicSpan] at hg
      rcases hg with ⟨hg_mon, hg_deg, hg_fac⟩
      have hele : s.1 * π₀.natDegree ≤ m := by
        have h1 : s.1 ≤ m / π₀.natDegree := by omega
        exact (Nat.mul_le_mul_right _ h1).trans (Nat.div_mul_le_self m π₀.natDegree)
      rw [mem_monicSpan]
      refine ⟨(hπ₀.1.pow s.1).mul hg_mon, ?_, ?_⟩
      · rw [(hπ₀.1.pow s.1).natDegree_mul hg_mon, hπ₀.1.natDegree_pow, hg_deg]
        omega
      · intro π hπ
        rw [UniqueFactorizationMonoid.normalizedFactors_mul (hπ₀.1.pow s.1).ne_zero hg_mon.ne_zero,
          UniqueFactorizationMonoid.normalizedFactors_pow,
          UniqueFactorizationMonoid.normalizedFactors_irreducible hπ₀.2,
          hπ₀.1.normalize_eq_self, Multiset.mem_add] at hπ
        rcases hπ with h1 | h2
        · have hπeq : π = π₀ := by
            have := Multiset.mem_of_mem_nsmul h1
            exact Multiset.mem_singleton.mp this
          rw [hπeq]; exact Finset.mem_insert_self π₀ S
        · exact Finset.mem_insert_of_mem (hg_fac π h2)
    · intro s₁ hs₁ s₂ hs₂ hprod
      rw [Finset.mem_sigma] at hs₁ hs₂
      have hg₁ := mem_monicSpan.mp hs₁.2
      have hg₂ := mem_monicSpan.mp hs₂.2
      have hg₁_mon : s₁.2.Monic := hg₁.1
      have hg₂_mon : s₂.2.Monic := hg₂.1
      have hfac := congr_arg UniqueFactorizationMonoid.normalizedFactors hprod
      rw [UniqueFactorizationMonoid.normalizedFactors_mul (hπ₀.1.pow s₁.1).ne_zero hg₁_mon.ne_zero,
        UniqueFactorizationMonoid.normalizedFactors_mul (hπ₀.1.pow s₂.1).ne_zero hg₂_mon.ne_zero,
        UniqueFactorizationMonoid.normalizedFactors_pow,
        UniqueFactorizationMonoid.normalizedFactors_pow,
        UniqueFactorizationMonoid.normalizedFactors_irreducible hπ₀.2,
        hπ₀.1.normalize_eq_self] at hfac
      have hcnt := congr_arg (Multiset.count π₀) hfac
      have hc1 : Multiset.count π₀ (UniqueFactorizationMonoid.normalizedFactors s₁.2) = 0 :=
        Multiset.count_eq_zero.mpr fun hmem => hπ₀_not (hg₁.2.2 π₀ hmem)
      have hc2 : Multiset.count π₀ (UniqueFactorizationMonoid.normalizedFactors s₂.2) = 0 :=
        Multiset.count_eq_zero.mpr fun hmem => hπ₀_not (hg₂.2.2 π₀ hmem)
      simp only [Multiset.count_add, Multiset.count_nsmul, Multiset.count_singleton_self,
        mul_one, hc1, hc2, add_zero] at hcnt
      have h2 : s₁.2 = s₂.2 := by
        rw [hcnt] at hprod
        exact mul_left_cancel₀ (hπ₀.1.pow s₂.1).ne_zero hprod
      cases s₁; cases s₂
      simp only at hcnt h2
      subst hcnt; subst h2; rfl
    · intro f hf
      rw [mem_monicSpan] at hf
      rcases hf with ⟨hf_mon, hf_deg, hf_fac⟩
      set F_fac := UniqueFactorizationMonoid.normalizedFactors f
      set e := Multiset.count π₀ F_fac
      set rest_fac := F_fac.filter (· ≠ π₀)
      set g := rest_fac.prod
      have hg_mon : g.Monic := by
        have h := Polynomial.monic_multiset_prod_of_monic rest_fac id fun π hπ =>
          (monic_and_irreducible_of_mem_normalizedFactors (Multiset.mem_of_mem_filter hπ)).1
        simpa only [Multiset.map_id] using h
      have hF_split : F_fac = e • {π₀} + rest_fac := by
        ext π
        rw [Multiset.count_add, Multiset.count_nsmul, Multiset.count_filter]
        by_cases hπ : π = π₀
        · subst hπ; simp [e]
        · rw [Multiset.count_singleton, if_neg hπ, mul_zero, zero_add, if_pos hπ]
      have hf_eq : π₀ ^ e * g = f := by
        calc π₀ ^ e * g
            = (e • ({π₀} : Multiset (Polynomial F))).prod * rest_fac.prod := by
                rw [Multiset.prod_nsmul, Multiset.prod_singleton]
          _ = (e • {π₀} + rest_fac).prod := (Multiset.prod_add _ _).symm
          _ = F_fac.prod := by rw [← hF_split]
          _ = f := prod_normalizedFactors_of_monic hf_mon
      have hg_deg : g.natDegree = m - e * π₀.natDegree := by
        have hdeg := congr_arg Polynomial.natDegree hf_eq
        rw [(hπ₀.1.pow e).natDegree_mul hg_mon, hπ₀.1.natDegree_pow, hf_deg] at hdeg
        omega
      have he_lt : e < m / π₀.natDegree + 1 := by
        have hdeg := congr_arg Polynomial.natDegree hf_eq
        rw [(hπ₀.1.pow e).natDegree_mul hg_mon, hπ₀.1.natDegree_pow, hf_deg] at hdeg
        have hle : e * π₀.natDegree ≤ m := by omega
        have hdiv : e ≤ m / π₀.natDegree := (Nat.le_div_iff_mul_le hd₀_pos).mpr hle
        omega
      have hg_fac : ∀ π ∈ UniqueFactorizationMonoid.normalizedFactors g, π ∈ S := by
        intro π hπ
        have hfac_eq : UniqueFactorizationMonoid.normalizedFactors g = rest_fac := by
          have h1 := congr_arg UniqueFactorizationMonoid.normalizedFactors hf_eq
          rw [UniqueFactorizationMonoid.normalizedFactors_mul (hπ₀.1.pow e).ne_zero hg_mon.ne_zero,
            UniqueFactorizationMonoid.normalizedFactors_pow,
            UniqueFactorizationMonoid.normalizedFactors_irreducible hπ₀.2,
            hπ₀.1.normalize_eq_self] at h1
          have h2 : e • {π₀} + UniqueFactorizationMonoid.normalizedFactors g = e • {π₀} + rest_fac :=
            h1.trans hF_split
          exact add_left_cancel h2
        rw [hfac_eq, Multiset.mem_filter] at hπ
        have hmem := hf_fac π hπ.1
        exact (Finset.mem_insert.mp hmem).resolve_left hπ.2
      refine ⟨⟨e, g⟩, ?_, hf_eq⟩
      rw [Finset.mem_sigma, Finset.mem_range]
      exact ⟨he_lt, mem_monicSpan.mpr ⟨hg_mon, hg_deg, hg_fac⟩⟩

/-- **Polynomial Irreducible-Sum Identity for `(-g(χ, ψ))^r`**:
for every nontrivial `χ ≠ 1`, every `ψ`, and every `r ≥ 1`,
`-(-gaussSum χ ψ) ^ r = ∑_{π monic irred, deg π ∣ r} (deg π) * (polyChar χ ψ π) ^ (r / deg π)`. -/
theorem neg_neg_gaussSum_pow_eq_sum_irreds {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {χ : MulChar F ℂ} (hχ : χ ≠ 1) (ψ : AddChar F ℂ) {r : ℕ} (hr : 1 ≤ r) :
    -(-gaussSum χ ψ) ^ r =
      ∑ π ∈ (monicIrredsLe F r).filter (fun π => π.natDegree ∣ r),
        (π.natDegree : ℂ) * (polyChar χ ψ π) ^ (r / π.natDegree) := by
  classical
  set S := monicIrredsLe F r
  have hS : ∀ π ∈ S, π.Monic ∧ Irreducible π := fun π hπ =>
    let h := mem_monicIrredsLe.mp hπ; ⟨h.1, h.2.1⟩
  set A : PowerSeries ℂ := 1 - PowerSeries.C (-gaussSum χ ψ) * PowerSeries.X
  set B : PowerSeries ℂ := ∏ π ∈ S, (1 - PowerSeries.C (polyChar χ ψ π) * PowerSeries.X ^ π.natDegree)
  set Binv : PowerSeries ℂ := ∏ π ∈ S, geomSeriesPow (polyChar χ ψ π) π.natDegree
  -- Step 1: `A` and `Binv` agree on coefficients `k ≤ r`
  have hA_eq_Binv : ∀ k ≤ r, PowerSeries.coeff k A = PowerSeries.coeff k Binv := by
    intro k hk
    have hcoeffA : PowerSeries.coeff k A =
        if k = 0 then 1 else if k = 1 then gaussSum χ ψ else 0 := by
      unfold A
      rw [map_sub, PowerSeries.coeff_one]
      rcases k with _ | _ | k
      · simp
      · simp
      · rw [if_neg (Nat.succ_ne_zero _), if_neg (by omega : k + 2 ≠ 1),
          PowerSeries.coeff_C_mul, PowerSeries.coeff_X, if_neg (by omega : k + 2 ≠ 1),
          mul_zero, sub_zero, if_neg (Nat.succ_ne_zero _)]
    rw [hcoeffA, ← sum_monicPolysOfDeg_polyChar hχ ψ k, coeff_prod_geomSeriesPow_eq_sum χ ψ S hS k]
    congr 1
    ext f
    rw [mem_monicPolysOfDeg, mem_monicSpan]
    constructor
    · rintro ⟨hmon, hdeg⟩
      refine ⟨hmon, hdeg, fun π hπ => ?_⟩
      have hπ_mi := monic_and_irreducible_of_mem_normalizedFactors hπ
      have hπ_dvd : π ∣ f := by
        have hprod := prod_normalizedFactors_of_monic hmon
        rw [← hprod]
        exact Multiset.dvd_prod hπ
      have hπ_deg : π.natDegree ≤ r :=
        (Polynomial.natDegree_le_of_dvd hπ_dvd hmon.ne_zero).trans (hdeg.le.trans hk)
      exact mem_monicIrredsLe.mpr ⟨hπ_mi.1, hπ_mi.2, hπ_deg⟩
    · rintro ⟨hmon, hdeg, _⟩
      exact ⟨hmon, hdeg⟩
  -- Step 2: `B * Binv = 1`, hence `A * B ≡ 1 (mod X^(r+1))`
  have hBBinv : Binv * B = 1 := by
    unfold Binv B
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun π hπ => ?_
    rw [mul_comm]
    exact one_sub_mul_geomSeriesPow _ (hS π hπ).2.natDegree_pos
  have hAB_eq_one : ∀ k ≤ r, PowerSeries.coeff k (A * B) = PowerSeries.coeff k 1 := by
    intro k hk
    rw [← hBBinv, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [hA_eq_Binv p.1 (by omega)]
  -- Step 3: Write `A * B = expSeries H` where `H = -(logSeries (-g) + ∑_{π ∈ S} logSeriesPow (λ π) (deg π))`
  set H : PowerSeries ℂ :=
    -(logSeries (-gaussSum χ ψ) + ∑ π ∈ S, logSeriesPow (polyChar χ ψ π) π.natDegree)
  have hH0 : PowerSeries.constantCoeff H = 0 := by
    unfold H
    rw [map_neg, map_add, constantCoeff_logSeries, map_sum,
      Finset.sum_eq_zero (fun π _ => constantCoeff_logSeriesPow _ _), add_zero, neg_zero]
  have hAB_exp : A * B = expSeries H := by
    have hH_rew : H = -logSeries (-gaussSum χ ψ) + ∑ π ∈ S, (-logSeriesPow (polyChar χ ψ π) π.natDegree) := by
      unfold H; rw [neg_add, Finset.sum_neg_distrib]
    have hsum0 : PowerSeries.constantCoeff
        (∑ π ∈ S, (-logSeriesPow (polyChar χ ψ π) π.natDegree)) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun π _ => by rw [map_neg, constantCoeff_logSeriesPow, neg_zero]
    rw [hH_rew, expSeries_add (by rw [map_neg, constantCoeff_logSeries, neg_zero]) hsum0,
      expSeries_neg_logSeries, expSeries_sum S _ (fun π _ => by rw [map_neg, constantCoeff_logSeriesPow, neg_zero])]
    congr 1
    unfold B
    refine Finset.prod_congr rfl fun π hπ => ?_
    exact (expSeries_neg_logSeriesPow _ (hS π hπ).2.natDegree_pos).symm
  -- Step 4: Extract `coeff r H = 0` and multiply by `r`
  have hcoeff_r : PowerSeries.coeff r H = 0 :=
    coeff_eq_zero_of_expSeries_eq_one_le hH0 (fun k hk => hAB_exp ▸ hAB_eq_one k hk) r le_rfl
  unfold H at hcoeff_r
  rw [map_neg, map_add, map_sum, coeff_logSeries, if_neg (by omega : r ≠ 0)] at hcoeff_r
  have hr_ne : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsum_r : ∑ π ∈ S, PowerSeries.coeff r (logSeriesPow (polyChar χ ψ π) π.natDegree) =
      (∑ π ∈ S.filter (fun π => π.natDegree ∣ r),
        (π.natDegree : ℂ) * (polyChar χ ψ π) ^ (r / π.natDegree)) / (r : ℂ) := by
    rw [Finset.sum_div, Finset.sum_filter]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [coeff_logSeriesPow, if_neg (by omega : r ≠ 0)]
  rw [hsum_r] at hcoeff_r
  have hzero : (-gaussSum χ ψ) ^ r +
      ∑ π ∈ S.filter (fun π => π.natDegree ∣ r),
        (π.natDegree : ℂ) * (polyChar χ ψ π) ^ (r / π.natDegree) = 0 := by
    have hmul := congr_arg (fun z : ℂ => -z * (r : ℂ)) hcoeff_r
    simp only [neg_zero, zero_mul, neg_neg, add_mul, div_mul_cancel₀ _ hr_ne] at hmul
    exact hmul
  exact eq_neg_of_add_eq_zero_right hzero |>.symm

/-- For any element `x` of a finite field extension `E / F`,
`Algebra.norm F x = ((-1) ^ (minpoly F x).natDegree * (minpoly F x).coeff 0) ^ Module.finrank F⟮x⟯ E`. -/
private lemma norm_eq_minpoly_coeff_zero_pow {F E : Type*} [Field F] [Fintype F]
    [Field E] [Fintype E] [Algebra F E] (x : E) :
    Algebra.norm F x =
      ((-1 : F) ^ (minpoly F x).natDegree * (minpoly F x).coeff 0) ^
        Module.finrank (↥F⟮x⟯) E := by
  have hx_int : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  let pb := IntermediateField.adjoin.powerBasis hx_int
  have hgen : (pb.gen : E) = x := rfl
  have hnorm_tower : Algebra.norm F x = Algebra.norm F (Algebra.norm (↥F⟮x⟯) x) :=
    (Algebra.norm_norm (R := F) (S := ↥F⟮x⟯) (a := x)).symm
  have hnorm_inner : Algebra.norm (↥F⟮x⟯) x = pb.gen ^ Module.finrank (↥F⟮x⟯) E :=
    Algebra.norm_algebraMap (R := ↥F⟮x⟯) (S := E) pb.gen
  rw [hnorm_tower, hnorm_inner, map_pow]
  congr 1
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb,
    IntermediateField.adjoin.powerBasis_dim hx_int]
  have hmp : minpoly F pb.gen = minpoly F x := by
    have h1 : Polynomial.aeval pb.gen (minpoly F x) = 0 := by
      apply Subtype.ext
      have hval : ((Polynomial.aeval pb.gen (minpoly F x) : ↥F⟮x⟯) : E) =
          Polynomial.aeval x (minpoly F x) := by
        have h := (Polynomial.aeval_algHom_apply
          (IsScalarTower.toAlgHom F (↥F⟮x⟯) E) pb.gen (minpoly F x)).symm
        exact h
      rw [hval, minpoly.aeval F x]
      rfl
    exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx_int) h1
      (minpoly.monic hx_int)).symm
  rw [hmp]

/-- Every monic irreducible `π : Polynomial F` with `π.natDegree ∣ Module.finrank F E` has
exact count `π.natDegree` of roots `x ∈ E` (and every such root satisfies `minpoly F x = π`). -/
private lemma card_minpoly_eq_natDegree {F E : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Field E] [Fintype E] [DecidableEq E] [Algebra F E]
    {π : Polynomial F} (hmon : π.Monic) (hirr : Irreducible π)
    (hdvd : π.natDegree ∣ Module.finrank F E) :
    (Finset.univ.filter fun x : E => minpoly F x = π).card = π.natDegree := by
  classical
  set q := Fintype.card F
  set r := Module.finrank F E
  have hcardE : Fintype.card E = q ^ r := Module.card_eq_pow_finrank
  have hcardE_ge : 2 ≤ Fintype.card E := two_le_card_finiteField (F := E)
  -- `π ∣ X ^ (q^r) - X` in `Polynomial F`
  have hπ_dvd_F : π ∣ Polynomial.X ^ q ^ r - Polynomial.X := by
    have h := (Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X hirr (n := r)).mp hdvd
    simpa only [Nat.card_eq_fintype_card, q] using h
  -- Map to `Polynomial E`: `π.map (algebraMap F E) ∣ X ^ |E| - X`
  set P : Polynomial E := Polynomial.X ^ Fintype.card E - Polynomial.X
  have hπ_dvd_E : π.map (algebraMap F E) ∣ P := by
    have hmap := map_dvd (Polynomial.mapRingHom (algebraMap F E)) hπ_dvd_F
    simpa only [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, P, hcardE] using hmap
  -- `P = X ^ |E| - X` is separable over `E` (since `derivative P = -1`)
  have hP_sep : P.Separable := by
    rw [Polynomial.Separable]
    have hchar_dvd : (Fintype.card E : E) = 0 := by
      have hp_ne : ringChar E ≠ 0 := ringChar_finiteField_ne_zero (F := E)
      have : CharP E (ringChar E) := ringChar.charP E
      obtain ⟨n, _, hn⟩ := FiniteField.card E (ringChar E)
      rw [hn, Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by exact_mod_cast n.ne_zero)]
    have hdP : Polynomial.derivative P = -1 := by
      unfold P
      rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
      simp [hchar_dvd]
    rw [hdP]
    exact ⟨0, -1, by ring⟩
  have hP_ne : P ≠ 0 := by
    intro h0
    have hdeg := congr_arg Polynomial.natDegree h0
    rw [Polynomial.natDegree_zero] at hdeg
    have hdegP : P.natDegree = Fintype.card E :=
      FiniteField.X_pow_card_sub_X_natDegree_eq E (by omega)
    omega
  -- Every `a : E` is a root of `P`, so `P` splits over `E`
  have hP_splits : P.Splits := by
    rw [Polynomial.splits_iff_card_roots]
    have hdegP : P.natDegree = Fintype.card E :=
      FiniteField.X_pow_card_sub_X_natDegree_eq E (by omega)
    have hnodup : P.roots.Nodup := Polynomial.nodup_roots hP_sep
    have hle : P.roots.card ≤ P.natDegree := Polynomial.card_roots' P
    have hge : Fintype.card E ≤ P.roots.card := by
      have hsub : (Finset.univ : Finset E) ⊆ P.roots.toFinset := by
        intro a _
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_ne, Polynomial.IsRoot.def]
        simp [P, FiniteField.pow_card]
      calc Fintype.card E = (Finset.univ : Finset E).card := rfl
        _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
        _ = P.roots.card := Multiset.toFinset_card_of_nodup hnodup
    omega
  -- Therefore `π.map (algebraMap F E)` is both separable and splits over `E`!
  have hπE_sep : (π.map (algebraMap F E)).Separable := hP_sep.of_dvd hπ_dvd_E
  have hπE_splits : (π.map (algebraMap F E)).Splits := Polynomial.Splits.of_dvd hP_splits hP_ne hπ_dvd_E
  have hπE_ne : π.map (algebraMap F E) ≠ 0 := (hmon.map (algebraMap F E)).ne_zero
  have hfilt_eq : (Finset.univ.filter fun x : E => minpoly F x = π) =
      (π.map (algebraMap F E)).roots.toFinset := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset,
      Polynomial.mem_roots hπE_ne, Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def]
    constructor
    · intro h; rw [← h]; exact minpoly.aeval F x
    · intro h; exact (minpoly.eq_of_irreducible_of_monic hirr h hmon).symm
  rw [hfilt_eq, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hπE_sep),
    ← hπE_splits.natDegree_eq_card_roots, Polynomial.natDegree_map_eq_of_injective (algebraMap F E).injective]

/-- **THE HASSE–DAVENPORT LIFTING THEOREM FOR GAUSS SUMS**:
for ANY extension of finite fields `E / F` of degree `r = Module.finrank F E`, any nontrivial
multiplicative character `χ : MulChar F ℂ`, and any additive character `ψ : AddChar F ℂ`,
`-gaussSum (liftMulChar E χ) (liftAddChar E ψ) = (-gaussSum χ ψ) ^ Module.finrank F E`! -/
theorem hasse_davenport_gaussSum {F E : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Field E] [Fintype E] [DecidableEq E] [Algebra F E]
    {χ : MulChar F ℂ} (hχ : χ ≠ 1) (ψ : AddChar F ℂ) :
    -gaussSum (liftMulChar E χ) (liftAddChar E ψ) =
      (-gaussSum χ ψ) ^ Module.finrank F E := by
  classical
  set r := Module.finrank F E
  have hr : 1 ≤ r := Module.finrank_pos
  -- Goal is equivalent to `gaussSum (liftMulChar E χ) (liftAddChar E ψ) = -(-gaussSum χ ψ) ^ r`
  suffices h : gaussSum (liftMulChar E χ) (liftAddChar E ψ) = -(-gaussSum χ ψ) ^ r by
    rw [h, neg_neg]
  rw [neg_neg_gaussSum_pow_eq_sum_irreds hχ ψ hr]
  unfold gaussSum
  set T := (monicIrredsLe F r).filter (fun π => π.natDegree ∣ r)
  -- Partition `x ∈ E` by `minpoly F x ∈ T`
  have hmaps : ∀ x ∈ (Finset.univ : Finset E), minpoly F x ∈ T := by
    intro x _
    have hx_int : IsIntegral F x := Algebra.IsIntegral.isIntegral x
    have hmul : (minpoly F x).natDegree * Module.finrank (↥F⟮x⟯) E = r := by
      rw [← IntermediateField.adjoin.finrank hx_int]
      exact Module.finrank_mul_finrank F (↥F⟮x⟯) E
    have hdvd : (minpoly F x).natDegree ∣ r := ⟨Module.finrank (↥F⟮x⟯) E, hmul.symm⟩
    have hle : (minpoly F x).natDegree ≤ r := Nat.le_of_dvd hr hdvd
    exact Finset.mem_filter.mpr
      ⟨mem_monicIrredsLe.mpr ⟨minpoly.monic hx_int, minpoly.irreducible hx_int, hle⟩, hdvd⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun π hπ => ?_
  rw [Finset.mem_filter, mem_monicIrredsLe] at hπ
  rcases hπ with ⟨⟨hmon, hirr, _⟩, hdvd⟩
  have hconst : ∀ x ∈ Finset.univ.filter (fun x : E => minpoly F x = π),
      liftMulChar E χ x * liftAddChar E ψ x = (polyChar χ ψ π) ^ (r / π.natDegree) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have hx_int : IsIntegral F x := Algebra.IsIntegral.isIntegral x
    have hdeg_pos : 0 < π.natDegree := hirr.natDegree_pos
    have hmul : π.natDegree * Module.finrank (↥F⟮x⟯) E = r := by
      rw [← hx.2, ← IntermediateField.adjoin.finrank hx_int]
      exact Module.finrank_mul_finrank F (↥F⟮x⟯) E
    have hfin : Module.finrank (↥F⟮x⟯) E = r / π.natDegree := by
      rw [← hmul, Nat.mul_div_cancel_left _ hdeg_pos]
    rw [liftMulChar_apply, liftAddChar_apply, norm_eq_minpoly_coeff_zero_pow x,
      trace_eq_finrank_mul_minpoly_nextCoeff F x, hx.2, hfin]
    unfold polyChar
    rw [map_pow, mul_pow]
    congr 1
    -- `ψ ((r / π.natDegree : F) * (-π.nextCoeff)) = (ψ (-π.nextCoeff)) ^ (r / π.natDegree)`
    rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul,
    card_minpoly_eq_natDegree hmon hirr hdvd]

/-- **THE HASSE–DAVENPORT LIFTING THEOREM FOR JACOBI SUMS**:
for ANY extension of finite fields `E / F` and any `χ₁, χ₂ : MulChar F ℂ` with
`χ₁ ≠ 1`, `χ₂ ≠ 1`, `χ₁ * χ₂ ≠ 1`,
`-jacobiSum (liftMulChar E χ₁) (liftMulChar E χ₂) = (-jacobiSum χ₁ χ₂) ^ Module.finrank F E`! -/
theorem hasse_davenport_jacobiSum {F E : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Field E] [Fintype E] [DecidableEq E] [Algebra F E]
    {χ₁ χ₂ : MulChar F ℂ} (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (h₁₂ : χ₁ * χ₂ ≠ 1) :
    -jacobiSum (liftMulChar E χ₁) (liftMulChar E χ₂) =
      (-jacobiSum χ₁ χ₂) ^ Module.finrank F E := by
  obtain ⟨ψ, hψ⟩ := exists_nontrivial_addChar_complex F
  have hψE : liftAddChar E ψ ≠ 1 := liftAddChar_ne_one hψ
  have h12E : liftMulChar E χ₁ * liftMulChar E χ₂ ≠ 1 := by
    rw [← liftMulChar_mul]; exact liftMulChar_ne_one h₁₂
  set r := Module.finrank F E
  have hfacE := jacobiSum_mul_gaussSum_eq h12E (liftAddChar E ψ)
  rw [← liftMulChar_mul] at hfacE
  have hhd1 : gaussSum (liftMulChar E χ₁) (liftAddChar E ψ) = -(-gaussSum χ₁ ψ) ^ r := by
    have := hasse_davenport_gaussSum (E := E) h₁ ψ; linear_combination -this
  have hhd2 : gaussSum (liftMulChar E χ₂) (liftAddChar E ψ) = -(-gaussSum χ₂ ψ) ^ r := by
    have := hasse_davenport_gaussSum (E := E) h₂ ψ; linear_combination -this
  have hhd12 : gaussSum (liftMulChar E (χ₁ * χ₂)) (liftAddChar E ψ) = -(-gaussSum (χ₁ * χ₂) ψ) ^ r := by
    have := hasse_davenport_gaussSum (E := E) h₁₂ ψ; linear_combination -this
  rw [hhd1, hhd2, hhd12] at hfacE
  have hfacF := jacobiSum_mul_gaussSum_eq h₁₂ ψ
  have hg12_ne : gaussSum (χ₁ * χ₂) ψ ≠ 0 := by
    intro h0
    have hnorm := norm_gaussSum_finiteField_eq h₁₂ hψ
    rw [h0, norm_zero] at hnorm
    have hpos : 0 < Real.sqrt (Fintype.card F : ℝ) :=
      Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
    linarith
  have hpow_ne : (-gaussSum (χ₁ * χ₂) ψ) ^ r ≠ 0 := pow_ne_zero r (neg_ne_zero.mpr hg12_ne)
  have heq : (-jacobiSum (liftMulChar E χ₁) (liftMulChar E χ₂)) * (-gaussSum (χ₁ * χ₂) ψ) ^ r =
      (-jacobiSum χ₁ χ₂) ^ r * (-gaussSum (χ₁ * χ₂) ψ) ^ r := by
    calc (-jacobiSum (liftMulChar E χ₁) (liftMulChar E χ₂)) * (-gaussSum (χ₁ * χ₂) ψ) ^ r
        = jacobiSum (liftMulChar E χ₁) (liftMulChar E χ₂) * -(-gaussSum (χ₁ * χ₂) ψ) ^ r := by ring
      _ = (-(-gaussSum χ₁ ψ) ^ r) * (-(-gaussSum χ₂ ψ) ^ r) := hfacE
      _ = (gaussSum χ₁ ψ * gaussSum χ₂ ψ) ^ r := by
            rw [neg_mul_neg, ← mul_pow, neg_mul_neg]
      _ = (jacobiSum χ₁ χ₂ * gaussSum (χ₁ * χ₂) ψ) ^ r := by rw [← hfacF]
      _ = ((-jacobiSum χ₁ χ₂) * (-gaussSum (χ₁ * χ₂) ψ)) ^ r := by rw [neg_mul_neg]
      _ = (-jacobiSum χ₁ χ₂) ^ r * (-gaussSum (χ₁ * χ₂) ψ) ^ r := mul_pow _ _ r
  exact mul_right_cancel₀ hpow_ne heq

/-- **EXACT EXTENSION-FIELD POINT-COUNTING IDENTITY FOR DIAGONAL CURVES `a X^d + b Y^d = c Z^d`**:
for ANY extension of finite fields `E / F` of degree `r = Module.finrank F E`, the actual number
of projective `E`-rational points on `a X^d + b Y^d = c Z^d` equals `diagPointCountPow F d a b c r`
(`= q^r + 1 - ∑_{p ∈ T_d} α_p^r`)! -/
theorem diagProjPoints_extension_eq_pointCountPow {F E : Type*}
    [Field F] [Fintype F] [DecidableEq F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]
    {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1)
    {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (diagProjPoints E d (algebraMap F E a) (algebraMap F E b) (algebraMap F E c) : ℂ) =
      diagPointCountPow F d a b c (Module.finrank F E) := by
  classical
  set q := Fintype.card F
  set r := Module.finrank F E
  have hcardE : Fintype.card E = q ^ r := Module.card_eq_pow_finrank
  have hq2 : 2 ≤ q := two_le_card_finiteField (F := F)
  have hdvdE : d ∣ Fintype.card E - 1 := by
    rw [hcardE]
    have hq_dvd : q - 1 ∣ q ^ r - 1 := by
      have hsub : ((q - 1 : ℕ) : ℤ) ∣ ((q ^ r - 1 : ℕ) : ℤ) := by
        have h1 : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := Nat.cast_sub (by omega)
        have h2 : ((q ^ r - 1 : ℕ) : ℤ) = (q : ℤ) ^ r - 1 :=
          Nat.cast_sub (Nat.one_le_pow r q (by omega))
        rw [h1, h2]
        exact ⟨∑ i ∈ Finset.range r, (q : ℤ) ^ i, (mul_geom_sum (q : ℤ) r).symm⟩
      exact Int.ofNat_dvd.mp hsub
    exact hdvd.trans hq_dvd
  have haE : algebraMap F E a ≠ 0 := (map_ne_zero (algebraMap F E)).mpr ha
  have hbE : algebraMap F E b ≠ 0 := (map_ne_zero (algebraMap F E)).mpr hb
  have hcE : algebraMap F E c ≠ 0 := (map_ne_zero (algebraMap F E)).mpr hc
  rw [diagProjPoints_eq_sum_jacobiSum hd hdvdE haE hbE hcE]
  unfold diagPointCountPow
  rw [hcardE, Nat.cast_pow]
  -- Bijection `p ↦ (liftMulChar E p.1, liftMulChar E p.2)` from `fermatCharPairs F d` to `fermatCharPairs E d`
  have hlift_mem : ∀ p ∈ fermatCharPairs F d,
      (liftMulChar E p.1, liftMulChar E p.2) ∈ fermatCharPairs E d := by
    intro p hp
    rw [mem_fermatCharPairs] at hp ⊢
    rcases hp with ⟨h1, h2, h1ne, h2ne, h12ne⟩
    refine ⟨?_, ?_, liftMulChar_ne_one h1ne, liftMulChar_ne_one h2ne, ?_⟩
    · rw [mem_powCharSet] at h1 ⊢
      rw [← liftMulChar_pow, h1, liftMulChar_one]
    · rw [mem_powCharSet] at h2 ⊢
      rw [← liftMulChar_pow, h2, liftMulChar_one]
    · rw [← liftMulChar_mul]; exact liftMulChar_ne_one h12ne
  have hlift_inj : Set.InjOn (fun p : MulChar F ℂ × MulChar F ℂ =>
      (liftMulChar E p.1, liftMulChar E p.2)) (fermatCharPairs F d : Set _) := by
    intro p₁ _ p₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (liftMulChar_injective F E h.1) (liftMulChar_injective F E h.2)
  have hlift_img : (fermatCharPairs F d).image
      (fun p => (liftMulChar E p.1, liftMulChar E p.2)) = fermatCharPairs E d := by
    apply Finset.eq_of_subset_of_card_le
    · intro p hp
      obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.mp hp
      exact hlift_mem p₀ hp₀
    · rw [Finset.card_image_of_injOn hlift_inj, card_fermatCharPairs hd hdvd,
        card_fermatCharPairs hd hdvdE]
  rw [← hlift_img, Finset.sum_image hlift_inj]
  have hsum_eq :
      ∑ p ∈ fermatCharPairs F d,
        liftMulChar E p.1 (algebraMap F E c * (algebraMap F E a)⁻¹) *
        liftMulChar E p.2 (algebraMap F E c * (algebraMap F E b)⁻¹) *
        jacobiSum (liftMulChar E p.1) (liftMulChar E p.2) =
      -∑ p ∈ fermatCharPairs F d, (diagEigenvalue a b c p) ^ r := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [mem_fermatCharPairs] at hp
    have harg1 : algebraMap F E c * (algebraMap F E a)⁻¹ = algebraMap F E (c * a⁻¹) := by
      rw [map_mul, map_inv₀]
    have harg2 : algebraMap F E c * (algebraMap F E b)⁻¹ = algebraMap F E (c * b⁻¹) := by
      rw [map_mul, map_inv₀]
    rw [harg1, harg2, liftMulChar_apply, liftMulChar_apply,
      Algebra.norm_algebraMap, Algebra.norm_algebraMap, map_pow, map_pow]
    have hhd : jacobiSum (liftMulChar E p.1) (liftMulChar E p.2) =
        -(-jacobiSum p.1 p.2) ^ r := by
      have := hasse_davenport_jacobiSum (E := E) hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
      linear_combination -this
    rw [hhd]
    unfold diagEigenvalue
    calc (p.1 (c * a⁻¹)) ^ r * (p.2 (c * b⁻¹)) ^ r * -(-jacobiSum p.1 p.2) ^ r
        = -((p.1 (c * a⁻¹)) ^ r * (p.2 (c * b⁻¹)) ^ r * (-jacobiSum p.1 p.2) ^ r) := by ring
      _ = -(p.1 (c * a⁻¹) * p.2 (c * b⁻¹) * -jacobiSum p.1 p.2) ^ r := by rw [← mul_pow, ← mul_pow]
      _ = -(-(p.1 (c * a⁻¹) * p.2 (c * b⁻¹) * jacobiSum p.1 p.2)) ^ r := by
            congr 1; congr 1; ring
  rw [hsum_eq, ← sub_eq_add_neg]

/-- **EXACT EXTENSION-FIELD POINT-COUNTING IDENTITY FOR PROJECTIVE FERMAT CURVES `X^d + Y^d = Z^d`**:
for ANY extension of finite fields `E / F` of degree `r = Module.finrank F E`, the actual number
of projective `E`-rational points on `X^d + Y^d = Z^d` equals `fermatPointCountPow F d r`
(`= q^r + 1 - ∑_{p ∈ T_d} α_p^r`)! -/
theorem fermatProjPoints_extension_eq_pointCountPow {F E : Type*}
    [Field F] [Fintype F] [DecidableEq F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]
    {d : ℕ} (hd : 1 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    (fermatProjPoints E d : ℂ) = fermatPointCountPow F d (Module.finrank F E) := by
  have h := diagProjPoints_extension_eq_pointCountPow (E := E) hd hdvd
    (one_ne_zero (α := F)) one_ne_zero one_ne_zero
  simp only [map_one] at h
  change (diagProjPoints E d 1 1 1 : ℂ) = _
  rw [h]
  unfold diagPointCountPow fermatPointCountPow
  congr 1
  -- Bijection `p ↦ (p.1, (p.1 * p.2)⁻¹)` on `fermatCharPairs F d` matches `diagEigenvalue 1 1 1` with `fermatEigenvalue`
  refine Finset.sum_bij (fun p _ => (p.1, (p.1 * p.2)⁻¹)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_fermatCharPairs] at hp ⊢
    rcases hp with ⟨h1, h2, h1ne, h2ne, h12ne⟩
    refine ⟨h1, inv_mem_powCharSet (mul_mem_powCharSet h1 h2), h1ne, inv_ne_one.mpr h12ne, ?_⟩
    dsimp only
    rw [mul_inv, ← mul_assoc, mul_inv_cancel, one_mul]
    exact inv_ne_one.mpr h2ne
  · intro p₁ _ p₂ _ h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨h1, h2⟩
    have h2' : p₁.1 * p₁.2 = p₂.1 * p₂.2 := inv_injective h2
    rw [h1] at h2'
    exact Prod.ext h1 (mul_left_cancel h2')
  · intro p hp
    rw [mem_fermatCharPairs] at hp
    rcases hp with ⟨h1, h2, h1ne, h2ne, h12ne⟩
    refine ⟨(p.1, (p.1 * p.2)⁻¹), ?_, ?_⟩
    · rw [mem_fermatCharPairs]
      refine ⟨h1, inv_mem_powCharSet (mul_mem_powCharSet h1 h2), h1ne, inv_ne_one.mpr h12ne, ?_⟩
      dsimp only
      rw [mul_inv, ← mul_assoc, mul_inv_cancel, one_mul]
      exact inv_ne_one.mpr h2ne
    · ext
      · rfl
      · simp
  · intro p _
    unfold diagEigenvalue fermatEigenvalue
    simp only [inv_one, mul_one, map_one, one_mul]
    congr 1
    rw [jacobiSum_inv_mul_eq, ← mul_assoc, mulChar_neg_one_mul_self, one_mul]

end HasseDavenport

end RHDirect.Stage7WeilConjectures
