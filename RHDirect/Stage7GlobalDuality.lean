import RHDirect.Stage2GaloisCohomology
import RHDirect.Stage5NumberFieldCohom
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# RHDirect.Stage7GlobalDuality

Unconditional (`0` assumptions, `0` `sorry`, `0` custom `axiom`) formalization of:
1. **Concrete Local Hilbert Symbols `(a, b)_v ∈ ℤˣ`** at `v = ∞`, `v = 2`, and every odd prime `p`,
   with complete proofs of **bimultiplicativity**, **symmetry**, **Steinberg relation**
   `(a, 1 - a)_v = 1` and `(a, -a)_v = 1`, and **nondegeneracy** at every place of `ℚ`.
2. **Actual Local Square-Class `𝔽₂`-Vector Spaces `ℚ_vˣ / (ℚ_vˣ)²`** (`dim = 1` at `∞`,
   `dim = 2` at odd `p`, `dim = 3` at `p = 2` via `Real.sqrt` and `hensels_lemma`) instantiating
   `Stage2GaloisCohomology.LocalDualityPairing (ZMod 2)` at every place `v` of `ℚ`.
3. **Unconditional Hilbert-Symbol Reciprocity Product Formula over `ℚ`**:
   `hilbert_reciprocity : ∀ a b : ℚˣ, hilbertSymInf a b * hilbertSymTwo a b * ∏ᶠ p : OddPrime, hilbertSymOdd p.1 p.2.1 p.2.2 a b = 1`,
   proved directly from Mathlib's `legendreSym.at_neg_one`, `legendreSym.at_two`, and
   `legendreSym.quadratic_reciprocity`.
4. **Concrete Global Poitou–Tate Self-Orthogonality Theorem on `ℚ`** (`im(loc) = im(loc)^⊥` for
   `KummerSelmer ℚ S 2` inside `∏_{v ∈ S} H¹(ℚ_v, μ₂)` of dimension `2|S|`, with exact half-dimension
   `dim(im loc) = |S|`), plus **Hasse–Minkowski Binary Norm Corollaries**.

Zero `sorry`, zero custom `axiom`s.
-/

open scoped BigOperators
open Finset RHDirect.Stage2GaloisCohomology RHDirect.Stage5NumberFieldCohom

namespace RHDirect.Stage7GlobalDuality

/-! ## Section 1: Sign-Unit (`ℤˣ` ↔ `ZMod 2`) & Rational `p`-adic Unit Reduction Machinery -/

section ComputableSignHelpers

/-- Map `{±1} = ℤˣ` additively to `ZMod 2`: `1 ↦ 0`, `-1 ↦ 1`. -/
def unitsToZMod2 (u : ℤˣ) : ZMod 2 :=
  if u = 1 then 0 else 1

/-- Map `ZMod 2` multiplicatively to `{±1} = ℤˣ`: `0 ↦ 1`, `1 ↦ -1`. -/
def negOnePowZMod2 (x : ZMod 2) : ℤˣ :=
  if x = 0 then 1 else -1

/-- Convert an integer `z ∈ {1, -1}` to `ℤˣ`. -/
def intToSignUnit (z : ℤ) : ℤˣ :=
  if z = -1 then -1 else 1

/-- `ε(u) = (u - 1) / 2 mod 2` on odd residues in `ZMod 8`. -/
def eps8 (x : ZMod 8) : ZMod 2 :=
  ((x.val / 2 : ℕ) : ZMod 2)

/-- `ω(u) = (u² - 1) / 8 mod 2` on odd residues in `ZMod 8`. -/
def omega8 (x : ZMod 8) : ZMod 2 :=
  (((x.val * x.val - 1) / 8 : ℕ) : ZMod 2)

theorem intUnits_eq_one_or_neg_one (u : ℤˣ) : u = 1 ∨ u = -1 :=
  Int.units_eq_one_or u

@[simp]
theorem unitsToZMod2_one : unitsToZMod2 1 = 0 := rfl

@[simp]
theorem unitsToZMod2_neg_one : unitsToZMod2 (-1) = 1 := by decide

@[simp]
theorem negOnePowZMod2_zero : negOnePowZMod2 0 = 1 := rfl

@[simp]
theorem negOnePowZMod2_one : negOnePowZMod2 1 = -1 := by decide

theorem unitsToZMod2_negOnePowZMod2 (x : ZMod 2) : unitsToZMod2 (negOnePowZMod2 x) = x := by
  fin_cases x
  · rfl
  · change unitsToZMod2 (negOnePowZMod2 1) = 1; decide

theorem negOnePowZMod2_unitsToZMod2 (u : ℤˣ) : negOnePowZMod2 (unitsToZMod2 u) = u := by
  rcases intUnits_eq_one_or_neg_one u with rfl | rfl <;> decide

theorem unitsToZMod2_mul (u v : ℤˣ) :
    unitsToZMod2 (u * v) = unitsToZMod2 u + unitsToZMod2 v := by
  rcases intUnits_eq_one_or_neg_one u with rfl | rfl <;>
    rcases intUnits_eq_one_or_neg_one v with rfl | rfl <;> decide

theorem negOnePowZMod2_add (x y : ZMod 2) :
    negOnePowZMod2 (x + y) = negOnePowZMod2 x * negOnePowZMod2 y := by
  fin_cases x <;> fin_cases y <;> dsimp <;> decide

theorem unitsToZMod2_eq_zero_iff (u : ℤˣ) : unitsToZMod2 u = 0 ↔ u = 1 := by
  rcases intUnits_eq_one_or_neg_one u with rfl | rfl <;> decide

theorem unitsToZMod2_eq_one_iff (u : ℤˣ) : unitsToZMod2 u = 1 ↔ u = -1 := by
  rcases intUnits_eq_one_or_neg_one u with rfl | rfl <;> decide

theorem negOnePowZMod2_eq_one_iff (x : ZMod 2) : negOnePowZMod2 x = 1 ↔ x = 0 := by
  fin_cases x <;> simp [negOnePowZMod2]

theorem negOnePowZMod2_eq_neg_one_iff (x : ZMod 2) : negOnePowZMod2 x = -1 ↔ x = 1 := by
  fin_cases x
  · change negOnePowZMod2 0 = -1 ↔ (0 : ZMod 2) = 1; decide
  · change negOnePowZMod2 1 = -1 ↔ (1 : ZMod 2) = 1; decide

theorem intUnits_mul_self (u : ℤˣ) : u * u = 1 := by
  rcases intUnits_eq_one_or_neg_one u with rfl | rfl <;> decide

theorem intUnits_inv_eq (u : ℤˣ) : u⁻¹ = u := by
  rcases intUnits_eq_one_or_neg_one u with rfl | rfl <;> decide

theorem negOnePowZMod2_natCast (n : ℕ) :
    negOnePowZMod2 (n : ZMod 2) = (-1 : ℤˣ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, negOnePowZMod2_add, ih, negOnePowZMod2_one, pow_succ]

theorem negOnePowZMod2_intCast (n : ℤ) :
    negOnePowZMod2 (n : ZMod 2) = (-1 : ℤˣ) ^ n := by
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast, zpow_natCast]
    exact negOnePowZMod2_natCast n
  | negSucc n =>
    rw [zpow_negSucc, intUnits_inv_eq]
    have hneg : ((Int.negSucc n : ℤ) : ZMod 2) = ((n + 1 : ℕ) : ZMod 2) := by
      rw [Int.negSucc_eq]
      push_cast
      have h2 : ∀ x : ZMod 2, -x = x := by decide
      exact h2 _
    rw [hneg, negOnePowZMod2_natCast]

theorem unitsToZMod2_zpow (u : ℤˣ) (k : ℤ) :
    unitsToZMod2 (u ^ k) = (k : ZMod 2) * unitsToZMod2 u := by
  rcases intUnits_eq_one_or_neg_one u with rfl | rfl
  · simp
  · rw [← negOnePowZMod2_intCast, unitsToZMod2_negOnePowZMod2, unitsToZMod2_neg_one, mul_one]

theorem coe_intToSignUnit {z : ℤ} (hz : z = 1 ∨ z = -1) : (intToSignUnit z : ℤ) = z := by
  rcases hz with rfl | rfl <;> simp [intToSignUnit]

theorem intToSignUnit_mul {z₁ z₂ : ℤ} (h₁ : z₁ = 1 ∨ z₁ = -1) (h₂ : z₂ = 1 ∨ z₂ = -1) :
    intToSignUnit (z₁ * z₂) = intToSignUnit z₁ * intToSignUnit z₂ := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> decide

@[simp]
theorem intToSignUnit_one : intToSignUnit 1 = 1 := by decide

@[simp]
theorem intToSignUnit_neg_one : intToSignUnit (-1) = -1 := by decide

theorem intToSignUnit_neg_one_pow (n : ℕ) :
    intToSignUnit ((-1 : ℤ) ^ n) = (-1 : ℤˣ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, intToSignUnit_mul (neg_one_pow_eq_or ℤ n) (Or.inr rfl), ih,
      intToSignUnit_neg_one]

theorem eps8_mul {x y : ZMod 8} (hx : x.val % 2 = 1) (hy : y.val % 2 = 1) :
    eps8 (x * y) = eps8 x + eps8 y := by
  revert hx hy; fin_cases x <;> fin_cases y <;> decide

theorem omega8_mul {x y : ZMod 8} (hx : x.val % 2 = 1) (hy : y.val % 2 = 1) :
    omega8 (x * y) = omega8 x + omega8 y := by
  revert hx hy; fin_cases x <;> fin_cases y <;> decide

@[simp] theorem eps8_one : eps8 1 = 0 := by decide
@[simp] theorem omega8_one : omega8 1 = 0 := by decide
@[simp] theorem eps8_neg_one : eps8 (-1) = 1 := by decide
@[simp] theorem omega8_neg_one : omega8 (-1) = 0 := by decide

theorem eps8_neg {x : ZMod 8} (hx : x.val % 2 = 1) : eps8 (-x) = eps8 x + 1 := by
  revert hx; fin_cases x <;> decide

theorem omega8_neg {x : ZMod 8} (hx : x.val % 2 = 1) : omega8 (-x) = omega8 x := by
  revert hx; fin_cases x <;> decide

theorem steinberg_zmod8_alpha_one {u : ZMod 8} (hu : u.val % 2 = 1) :
    eps8 u * eps8 (1 - 2 * u) + omega8 (1 - 2 * u) = 0 := by
  revert hu; fin_cases u <;> decide

theorem steinberg_zmod8_alpha_two {u : ZMod 8} (hu : u.val % 2 = 1) :
    eps8 (1 - 4 * u) = 0 := by
  revert hu; fin_cases u <;> decide

theorem zmod8_eq_one_of_eps_omega_zero {w : ZMod 8} (hw : w.val % 2 = 1)
    (he : eps8 w = 0) (ho : omega8 w = 0) : w = 1 := by
  have h : ∀ u : ZMod 8, u.val % 2 = 1 → eps8 u = 0 → omega8 u = 0 → u = 1 := by decide
  exact h w hw he ho

end ComputableSignHelpers

noncomputable section

section PadicReduction

/-! ### Rational `p`-adic Valuation & Unit Part Decomposition -/

/-- Prime `p` as a unit in `ℚˣ`. -/
def primeUnit (p : ℕ) (hp : p.Prime) : ℚˣ :=
  Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero)

@[simp]
theorem coe_primeUnit (p : ℕ) (hp : p.Prime) : ((primeUnit p hp : ℚˣ) : ℚ) = (p : ℚ) := rfl

/-- The `p`-adic unit part `u = a * p^(-v_p(a))` of `a : ℚˣ`. -/
def pUnit (p : ℕ) (hp : p.Prime) (a : ℚˣ) : ℚˣ :=
  a * (primeUnit p hp) ^ (-padicValRat p (a : ℚ))

theorem pUnit_spec (p : ℕ) (hp : p.Prime) (a : ℚˣ) :
    a = (primeUnit p hp) ^ (padicValRat p (a : ℚ)) * pUnit p hp a := by
  unfold pUnit
  rw [mul_comm ((primeUnit p hp) ^ _), mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]

theorem padicValRat_zpow_unit {p : ℕ} (hp : p.Prime) (w : ℚˣ) (k : ℤ) :
    padicValRat p ((w ^ k : ℚˣ) : ℚ) = k * padicValRat p (w : ℚ) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Units.val_zpow_eq_zpow_val]
  exact padicValRat.zpow (w : ℚ)

theorem padicValRat_pow_unit {p : ℕ} (hp : p.Prime) (w : ℚˣ) (n : ℕ) :
    padicValRat p ((w ^ n : ℚˣ) : ℚ) = n * padicValRat p (w : ℚ) := by
  simpa [zpow_natCast] using padicValRat_zpow_unit hp w n

theorem padicValRat_pUnit (p : ℕ) (hp : p.Prime) (a : ℚˣ) :
    padicValRat p (pUnit p hp a : ℚ) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  unfold pUnit
  rw [Units.val_mul, padicValRat.mul a.ne_zero (Units.ne_zero _),
    padicValRat_zpow_unit hp (primeUnit p hp), coe_primeUnit, padicValRat.self hp.one_lt]
  ring

theorem pUnit_mul (p : ℕ) (hp : p.Prime) (a b : ℚˣ) :
    pUnit p hp (a * b) = pUnit p hp a * pUnit p hp b := by
  have : Fact p.Prime := ⟨hp⟩
  unfold pUnit
  rw [Units.val_mul, padicValRat.mul a.ne_zero b.ne_zero, neg_add, zpow_add]
  exact mul_mul_mul_comm a b _ _

theorem pUnit_one (p : ℕ) (hp : p.Prime) : pUnit p hp 1 = 1 := by
  unfold pUnit
  simp

theorem pUnit_inv (p : ℕ) (hp : p.Prime) (a : ℚˣ) : pUnit p hp a⁻¹ = (pUnit p hp a)⁻¹ := by
  apply mul_left_cancel (a := pUnit p hp a)
  rw [← pUnit_mul, mul_inv_cancel, pUnit_one, mul_inv_cancel]

theorem pUnit_neg (p : ℕ) (hp : p.Prime) (a : ℚˣ) : pUnit p hp (-a) = -(pUnit p hp a) := by
  unfold pUnit
  rw [Units.val_neg, padicValRat.neg]
  simp

theorem pUnit_primeUnit (p : ℕ) (hp : p.Prime) : pUnit p hp (primeUnit p hp) = 1 := by
  unfold pUnit
  rw [coe_primeUnit, padicValRat.self hp.one_lt]
  simp

theorem pUnit_of_val_zero (p : ℕ) (hp : p.Prime) {a : ℚˣ} (ha : padicValRat p (a : ℚ) = 0) :
    pUnit p hp a = a := by
  unfold pUnit
  rw [ha, neg_zero, zpow_zero, mul_one]

/-- If `0 < padicValNat p n`, then `p ∣ n`. -/
theorem dvd_of_pos_padicValNat {p n : ℕ} (h : 0 < padicValNat p n) : p ∣ n := by
  by_contra hnd
  rw [padicValNat.eq_zero_of_not_dvd hnd] at h
  omega

/-- If `0 ≤ padicValRat p q`, then `p ∤ q.den`. -/
theorem not_dvd_den_of_nonneg_padicValRat {p : ℕ} (hp : p.Prime) {q : ℚ}
    (hq : 0 ≤ padicValRat p q) : ¬ p ∣ q.den := by
  have : Fact p.Prime := ⟨hp⟩
  intro hdvd
  have hden_pos : 0 < padicValNat p q.den :=
    one_le_padicValNat_of_dvd q.den_nz hdvd
  rw [padicValRat_def] at hq
  have hnum_pos : 0 < padicValInt p q.num := by omega
  have hnum_dvd : p ∣ q.num.natAbs := dvd_of_pos_padicValNat hnum_pos
  have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
  exact hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hnum_dvd hdvd)

/-- If `padicValRat p q = 0` and `q ≠ 0`, then `p ∤ q.num` and `p ∤ q.den`. -/
theorem not_dvd_num_and_den_of_padicValRat_eq_zero {p : ℕ} (hp : p.Prime) {q : ℚ}
    (hq0 : q ≠ 0) (hq : padicValRat p q = 0) :
    ¬ (p : ℤ) ∣ q.num ∧ ¬ p ∣ q.den := by
  have : Fact p.Prime := ⟨hp⟩
  have hden : ¬ p ∣ q.den := not_dvd_den_of_nonneg_padicValRat hp (le_of_eq hq.symm)
  refine ⟨?_, hden⟩
  intro hnum
  have hnum_nat : p ∣ q.num.natAbs := Int.natCast_dvd.mp hnum
  have hnum_pos : 0 < padicValNat p q.num.natAbs :=
    one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq0)) hnum_nat
  have hden_zero : padicValNat p q.den = 0 := padicValNat.eq_zero_of_not_dvd hden
  rw [padicValRat_def, hden_zero] at hq
  change (padicValNat p q.num.natAbs : ℤ) - 0 = 0 at hq
  omega

/-- If `0 < padicValRat p q`, then `(p : ℤ) ∣ q.num` and `¬ p ∣ q.den`. -/
theorem dvd_num_of_pos_padicValRat {p : ℕ} (hp : p.Prime) {q : ℚ}
    (hq : 0 < padicValRat p q) : (p : ℤ) ∣ q.num ∧ ¬ p ∣ q.den := by
  have : Fact p.Prime := ⟨hp⟩
  have hden : ¬ p ∣ q.den := not_dvd_den_of_nonneg_padicValRat hp (le_of_lt hq)
  refine ⟨?_, hden⟩
  have hden_zero : padicValNat p q.den = 0 := padicValNat.eq_zero_of_not_dvd hden
  rw [padicValRat_def, hden_zero] at hq
  have hnum_pos : 0 < padicValNat p q.num.natAbs := by
    change 0 < (padicValNat p q.num.natAbs : ℤ) - 0 at hq
    omega
  exact Int.natCast_dvd.mpr (dvd_of_pos_padicValNat hnum_pos)

/-- Reduction modulo a prime `p` on `ℤ_(p) ⊂ ℚ`: `q ↦ q.num * q.den⁻¹ ∈ ZMod p`. -/
def redModP (p : ℕ) (q : ℚ) : ZMod p :=
  (q.num : ZMod p) * ((q.den : ZMod p))⁻¹

theorem zmod_den_ne_zero_of_not_dvd {p : ℕ} {q : ℚ} (hd : ¬ p ∣ q.den) :
    (q.den : ZMod p) ≠ 0 := by
  intro h
  exact hd ((ZMod.natCast_eq_zero_iff q.den p).mp h)

theorem redModP_mul {p : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h₁ : ¬ p ∣ q₁.den) (h₂ : ¬ p ∣ q₂.den) :
    redModP p (q₁ * q₂) = redModP p q₁ * redModP p q₂ := by
  have : Fact p.Prime := ⟨hp⟩
  have h12 : ¬ p ∣ (q₁ * q₂).den := by
    intro hd
    have hdiv : (q₁ * q₂).den ∣ q₁.den * q₂.den := Rat.mul_den_dvd q₁ q₂
    rcases hp.dvd_mul.mp (dvd_trans hd hdiv) with h | h
    · exact h₁ h
    · exact h₂ h
  have hd1 : (q₁.den : ZMod p) ≠ 0 := zmod_den_ne_zero_of_not_dvd h₁
  have hd2 : (q₂.den : ZMod p) ≠ 0 := zmod_den_ne_zero_of_not_dvd h₂
  have hd12 : ((q₁ * q₂).den : ZMod p) ≠ 0 := zmod_den_ne_zero_of_not_dvd h12
  have hEqQ : ((q₁ * q₂).num : ℚ) / ((q₁ * q₂).den : ℚ) =
      (q₁.num : ℚ) / (q₁.den : ℚ) * ((q₂.num : ℚ) / (q₂.den : ℚ)) := by
    rw [Rat.num_div_den, Rat.num_div_den, Rat.num_div_den]
  have hEqZ : (q₁ * q₂).num * ((q₁.den : ℤ) * (q₂.den : ℤ)) =
      (q₁.num * q₂.num) * ((q₁ * q₂).den : ℤ) := by
    have hq : ((q₁ * q₂).num : ℚ) * ((q₁.den : ℚ) * (q₂.den : ℚ)) =
        ((q₁.num : ℚ) * (q₂.num : ℚ)) * ((q₁ * q₂).den : ℚ) := by
      have hne1 : (q₁.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q₁.den_nz
      have hne2 : (q₂.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q₂.den_nz
      have hne12 : ((q₁ * q₂).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (q₁ * q₂).den_nz
      field_simp at hEqQ
      linarith
    exact_mod_cast hq
  have hMod : (((q₁ * q₂).num : ZMod p)) * ((q₁.den : ZMod p) * (q₂.den : ZMod p)) =
      ((q₁.num : ZMod p) * (q₂.num : ZMod p)) * ((q₁ * q₂).den : ZMod p) := by
    exact_mod_cast congrArg (Int.cast (R := ZMod p)) hEqZ
  unfold redModP
  calc ((q₁ * q₂).num : ZMod p) * ((q₁ * q₂).den : ZMod p)⁻¹
      = (((q₁ * q₂).num : ZMod p) * ((q₁.den : ZMod p) * (q₂.den : ZMod p))) *
          (((q₁ * q₂).den : ZMod p)⁻¹ * (q₁.den : ZMod p)⁻¹ * (q₂.den : ZMod p)⁻¹) := by
        field_simp
    _ = ((q₁.num : ZMod p) * (q₂.num : ZMod p) * ((q₁ * q₂).den : ZMod p)) *
          (((q₁ * q₂).den : ZMod p)⁻¹ * (q₁.den : ZMod p)⁻¹ * (q₂.den : ZMod p)⁻¹) := by
        rw [hMod]
    _ = (q₁.num : ZMod p) * (q₁.den : ZMod p)⁻¹ * ((q₂.num : ZMod p) * (q₂.den : ZMod p)⁻¹) := by
        field_simp

theorem redModP_add {p : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h₁ : ¬ p ∣ q₁.den) (h₂ : ¬ p ∣ q₂.den) :
    redModP p (q₁ + q₂) = redModP p q₁ + redModP p q₂ := by
  have : Fact p.Prime := ⟨hp⟩
  have h12 : ¬ p ∣ (q₁ + q₂).den := by
    intro hd
    have hdiv : (q₁ + q₂).den ∣ q₁.den * q₂.den := Rat.add_den_dvd q₁ q₂
    rcases hp.dvd_mul.mp (dvd_trans hd hdiv) with h | h
    · exact h₁ h
    · exact h₂ h
  have hd1 : (q₁.den : ZMod p) ≠ 0 := zmod_den_ne_zero_of_not_dvd h₁
  have hd2 : (q₂.den : ZMod p) ≠ 0 := zmod_den_ne_zero_of_not_dvd h₂
  have hd12 : ((q₁ + q₂).den : ZMod p) ≠ 0 := zmod_den_ne_zero_of_not_dvd h12
  have hEqQ : ((q₁ + q₂).num : ℚ) / ((q₁ + q₂).den : ℚ) =
      (q₁.num : ℚ) / (q₁.den : ℚ) + (q₂.num : ℚ) / (q₂.den : ℚ) := by
    rw [Rat.num_div_den, Rat.num_div_den, Rat.num_div_den]
  have hEqZ : (q₁ + q₂).num * ((q₁.den : ℤ) * (q₂.den : ℤ)) =
      (q₁.num * (q₂.den : ℤ) + q₂.num * (q₁.den : ℤ)) * ((q₁ + q₂).den : ℤ) := by
    have hq : ((q₁ + q₂).num : ℚ) * ((q₁.den : ℚ) * (q₂.den : ℚ)) =
        ((q₁.num : ℚ) * (q₂.den : ℚ) + (q₂.num : ℚ) * (q₁.den : ℚ)) * ((q₁ + q₂).den : ℚ) := by
      have hne1 : (q₁.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q₁.den_nz
      have hne2 : (q₂.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q₂.den_nz
      have hne12 : ((q₁ + q₂).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (q₁ + q₂).den_nz
      field_simp at hEqQ
      linarith
    exact_mod_cast hq
  have hMod : (((q₁ + q₂).num : ZMod p)) * ((q₁.den : ZMod p) * (q₂.den : ZMod p)) =
      ((q₁.num : ZMod p) * (q₂.den : ZMod p) + (q₂.num : ZMod p) * (q₁.den : ZMod p)) *
        ((q₁ + q₂).den : ZMod p) := by
    exact_mod_cast congrArg (Int.cast (R := ZMod p)) hEqZ
  unfold redModP
  calc ((q₁ + q₂).num : ZMod p) * ((q₁ + q₂).den : ZMod p)⁻¹
      = (((q₁ + q₂).num : ZMod p) * ((q₁.den : ZMod p) * (q₂.den : ZMod p))) *
          (((q₁ + q₂).den : ZMod p)⁻¹ * (q₁.den : ZMod p)⁻¹ * (q₂.den : ZMod p)⁻¹) := by
        field_simp
    _ = (((q₁.num : ZMod p) * (q₂.den : ZMod p) + (q₂.num : ZMod p) * (q₁.den : ZMod p)) *
          ((q₁ + q₂).den : ZMod p)) *
          (((q₁ + q₂).den : ZMod p)⁻¹ * (q₁.den : ZMod p)⁻¹ * (q₂.den : ZMod p)⁻¹) := by
        rw [hMod]
    _ = (q₁.num : ZMod p) * (q₁.den : ZMod p)⁻¹ + (q₂.num : ZMod p) * (q₂.den : ZMod p)⁻¹ := by
        field_simp

theorem redModP_neg (p : ℕ) (q : ℚ) : redModP p (-q) = -redModP p q := by
  unfold redModP
  simp [Rat.neg_num, Rat.neg_den]

theorem redModP_sub {p : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h₁ : ¬ p ∣ q₁.den) (h₂ : ¬ p ∣ q₂.den) :
    redModP p (q₁ - q₂) = redModP p q₁ - redModP p q₂ := by
  rw [sub_eq_add_neg, redModP_add hp h₁ (by simpa [Rat.neg_den] using h₂), redModP_neg,
    ← sub_eq_add_neg]

@[simp]
theorem redModP_intCast (p : ℕ) (z : ℤ) : redModP p (z : ℚ) = (z : ZMod p) := by
  unfold redModP
  simp

@[simp]
theorem redModP_natCast (p : ℕ) (n : ℕ) : redModP p (n : ℚ) = (n : ZMod p) := by
  unfold redModP
  simp

@[simp]
theorem redModP_one (p : ℕ) : redModP p 1 = 1 := by
  unfold redModP
  simp

theorem redModP_eq_zero_of_pos_val {p : ℕ} (hp : p.Prime) {q : ℚ}
    (hq : 0 < padicValRat p q) : redModP p q = 0 := by
  have hnum : (p : ℤ) ∣ q.num := (dvd_num_of_pos_padicValRat hp hq).1
  unfold redModP
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd q.num p).mpr hnum, zero_mul]

theorem redModP_ne_zero_of_val_eq_zero {p : ℕ} (hp : p.Prime) {q : ℚ}
    (hq0 : q ≠ 0) (hq : padicValRat p q = 0) : redModP p q ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hnum, hden⟩ := not_dvd_num_and_den_of_padicValRat_eq_zero hp hq0 hq
  unfold redModP
  apply mul_ne_zero
  · intro h
    exact hnum ((ZMod.intCast_zmod_eq_zero_iff_dvd q.num p).mp h)
  · exact inv_ne_zero (zmod_den_ne_zero_of_not_dvd hden)

/-- Rational `p`-adic unit Legendre symbol via `legendreSym p (u.num * u.den)`. -/
def ratUnitLegendre (p : ℕ) (hp : p.Prime) (u : ℚ) : ℤ :=
  letI : Fact p.Prime := ⟨hp⟩
  legendreSym p (u.num * u.den)

/-- `ratUnitLegendre` coincides with `quadraticChar (ZMod p) (redModP p u)` on `p`-adic units. -/
theorem ratUnitLegendre_eq_quadraticChar {p : ℕ} (hp : p.Prime) {u : ℚ}
    (hu0 : u ≠ 0) (hu : padicValRat p u = 0) :
    letI : Fact p.Prime := ⟨hp⟩
    ratUnitLegendre p hp u = quadraticChar (ZMod p) (redModP p u) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨_, hden⟩ := not_dvd_num_and_den_of_padicValRat_eq_zero hp hu0 hu
  have hd : (u.den : ZMod p) ≠ 0 := zmod_den_ne_zero_of_not_dvd hden
  unfold ratUnitLegendre redModP
  rw [legendreSym, Int.cast_mul, Int.cast_natCast, map_mul, map_mul]
  congr 1
  have hinv : quadraticChar (ZMod p) (u.den : ZMod p) *
      quadraticChar (ZMod p) ((u.den : ZMod p)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd, map_one]
  rcases quadraticChar_dichotomy hd with h | h
  · rw [h, one_mul] at hinv; rw [h, hinv]
  · rw [h] at hinv ⊢; omega

theorem ratUnitLegendre_eq_one_or_neg_one {p : ℕ} (hp : p.Prime) {u : ℚ}
    (hu0 : u ≠ 0) (hu : padicValRat p u = 0) :
    ratUnitLegendre p hp u = 1 ∨ ratUnitLegendre p hp u = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [ratUnitLegendre_eq_quadraticChar hp hu0 hu]
  exact quadraticChar_dichotomy (redModP_ne_zero_of_val_eq_zero hp hu0 hu)

theorem ratUnitLegendre_mul {p : ℕ} (hp : p.Prime) {u v : ℚ}
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu : padicValRat p u = 0) (hv : padicValRat p v = 0) :
    ratUnitLegendre p hp (u * v) = ratUnitLegendre p hp u * ratUnitLegendre p hp v := by
  have : Fact p.Prime := ⟨hp⟩
  have huv0 : u * v ≠ 0 := mul_ne_zero hu0 hv0
  have huv : padicValRat p (u * v) = 0 := by rw [padicValRat.mul hu0 hv0, hu, hv, add_zero]
  rw [ratUnitLegendre_eq_quadraticChar hp huv0 huv,
    ratUnitLegendre_eq_quadraticChar hp hu0 hu,
    ratUnitLegendre_eq_quadraticChar hp hv0 hv,
    redModP_mul hp (not_dvd_den_of_nonneg_padicValRat hp (le_of_eq hu.symm))
      (not_dvd_den_of_nonneg_padicValRat hp (le_of_eq hv.symm)),
    map_mul]

/-- The `p`-adic unit Legendre symbol of `pUnit p hp a` as a sign unit in `ℤˣ`. -/
def pUnitLegUnit (p : ℕ) (hp : p.Prime) (a : ℚˣ) : ℤˣ :=
  intToSignUnit (ratUnitLegendre p hp (pUnit p hp a : ℚ))

theorem coe_pUnitLegUnit (p : ℕ) (hp : p.Prime) (a : ℚˣ) :
    (pUnitLegUnit p hp a : ℤ) = ratUnitLegendre p hp (pUnit p hp a : ℚ) :=
  coe_intToSignUnit (ratUnitLegendre_eq_one_or_neg_one hp (pUnit p hp a).ne_zero
    (padicValRat_pUnit p hp a))

theorem pUnitLegUnit_mul (p : ℕ) (hp : p.Prime) (a b : ℚˣ) :
    pUnitLegUnit p hp (a * b) = pUnitLegUnit p hp a * pUnitLegUnit p hp b := by
  unfold pUnitLegUnit
  rw [pUnit_mul, Units.val_mul,
    ratUnitLegendre_mul hp (pUnit p hp a).ne_zero (pUnit p hp b).ne_zero
      (padicValRat_pUnit p hp a) (padicValRat_pUnit p hp b)]
  exact intToSignUnit_mul
    (ratUnitLegendre_eq_one_or_neg_one hp (pUnit p hp a).ne_zero (padicValRat_pUnit p hp a))
    (ratUnitLegendre_eq_one_or_neg_one hp (pUnit p hp b).ne_zero (padicValRat_pUnit p hp b))

theorem pUnitLegUnit_one (p : ℕ) (hp : p.Prime) : pUnitLegUnit p hp 1 = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  unfold pUnitLegUnit
  rw [pUnit_one, Units.val_one, ratUnitLegendre_eq_quadraticChar hp one_ne_zero padicValRat.one,
    redModP_one, map_one]
  exact intToSignUnit_one

theorem pUnitLegUnit_inv (p : ℕ) (hp : p.Prime) (a : ℚˣ) :
    pUnitLegUnit p hp a⁻¹ = pUnitLegUnit p hp a := by
  have h := pUnitLegUnit_mul p hp a a⁻¹
  rw [mul_inv_cancel, pUnitLegUnit_one] at h
  calc pUnitLegUnit p hp a⁻¹
      = pUnitLegUnit p hp a * (pUnitLegUnit p hp a * pUnitLegUnit p hp a⁻¹) := by
        rw [← mul_assoc, intUnits_mul_self, one_mul]
    _ = pUnitLegUnit p hp a := by rw [← h, mul_one]

theorem pUnitLegUnit_neg_one (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    pUnitLegUnit p hp (-1) = (-1 : ℤˣ) ^ (p / 2) := by
  have : Fact p.Prime := ⟨hp⟩
  unfold pUnitLegUnit
  have hv : padicValRat p ((-1 : ℚˣ) : ℚ) = 0 := by simp
  rw [pUnit_of_val_zero p hp hv]
  rw [ratUnitLegendre_eq_quadraticChar hp (Units.ne_zero _) hv]
  have hred : redModP p ((-1 : ℚˣ) : ℚ) = (-1 : ZMod p) := by
    rw [Units.val_neg, Units.val_one, redModP_neg, redModP_one]
  rw [hred]
  have hleg : quadraticChar (ZMod p) (-1 : ZMod p) = legendreSym p (-1) := by
    simp [legendreSym]
  rw [hleg, legendreSym.at_neg_one hp2, ZMod.χ₄_eq_neg_one_pow (hp.mod_two_eq_one_iff_ne_two.mpr hp2)]
  exact intToSignUnit_neg_one_pow (p / 2)

/-! ### Reduction Modulo `8` on `ℤ_(2) ⊂ ℚ` -/

/-- Every odd residue in `ZMod 8` squares to `1`. -/
theorem zmod8_odd_sq_eq_one (x : ZMod 8) (hx : x.val % 2 = 1) : x * x = 1 := by
  revert hx; fin_cases x <;> decide

theorem nat_cast_zmod8_odd {n : ℕ} (hn : ¬ 2 ∣ n) : ((n : ZMod 8).val) % 2 = 1 := by
  have hmod : n % 2 = 1 := by omega
  rw [ZMod.val_natCast]
  omega

theorem int_cast_zmod8_odd {z : ℤ} (hz : ¬ (2 : ℤ) ∣ z) : ((z : ZMod 8).val) % 2 = 1 := by
  have hmod : z % 2 = 1 := by omega
  have hval : ((z : ZMod 8).val : ℤ) = z % 8 := ZMod.val_intCast z
  omega

/-- Reduction modulo `8` on `ℤ_(2) ⊂ ℚ`: since `d² ≡ 1 (mod 8)` for odd `d`, `a / d ≡ a * d (mod 8)`. -/
def redMod8 (q : ℚ) : ZMod 8 :=
  (q.num : ZMod 8) * (q.den : ZMod 8)

theorem redMod8_mul {q₁ q₂ : ℚ} (h₁ : ¬ 2 ∣ q₁.den) (h₂ : ¬ 2 ∣ q₂.den) :
    redMod8 (q₁ * q₂) = redMod8 q₁ * redMod8 q₂ := by
  have h12 : ¬ 2 ∣ (q₁ * q₂).den := by
    intro hd
    have hdiv : (q₁ * q₂).den ∣ q₁.den * q₂.den := Rat.mul_den_dvd q₁ q₂
    rcases Nat.prime_two.dvd_mul.mp (dvd_trans hd hdiv) with h | h
    · exact h₁ h
    · exact h₂ h
  have hs1 : (q₁.den : ZMod 8) * (q₁.den : ZMod 8) = 1 :=
    zmod8_odd_sq_eq_one _ (nat_cast_zmod8_odd h₁)
  have hs2 : (q₂.den : ZMod 8) * (q₂.den : ZMod 8) = 1 :=
    zmod8_odd_sq_eq_one _ (nat_cast_zmod8_odd h₂)
  have hs12 : ((q₁ * q₂).den : ZMod 8) * ((q₁ * q₂).den : ZMod 8) = 1 :=
    zmod8_odd_sq_eq_one _ (nat_cast_zmod8_odd h12)
  have hEqQ : ((q₁ * q₂).num : ℚ) / ((q₁ * q₂).den : ℚ) =
      (q₁.num : ℚ) / (q₁.den : ℚ) * ((q₂.num : ℚ) / (q₂.den : ℚ)) := by
    rw [Rat.num_div_den, Rat.num_div_den, Rat.num_div_den]
  have hEqZ : (q₁ * q₂).num * ((q₁.den : ℤ) * (q₂.den : ℤ)) =
      (q₁.num * q₂.num) * ((q₁ * q₂).den : ℤ) := by
    have hq : ((q₁ * q₂).num : ℚ) * ((q₁.den : ℚ) * (q₂.den : ℚ)) =
        ((q₁.num : ℚ) * (q₂.num : ℚ)) * ((q₁ * q₂).den : ℚ) := by
      have hne1 : (q₁.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q₁.den_nz
      have hne2 : (q₂.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q₂.den_nz
      have hne12 : ((q₁ * q₂).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (q₁ * q₂).den_nz
      field_simp at hEqQ
      linarith
    exact_mod_cast hq
  have hMod : (((q₁ * q₂).num : ZMod 8)) * ((q₁.den : ZMod 8) * (q₂.den : ZMod 8)) =
      ((q₁.num : ZMod 8) * (q₂.num : ZMod 8)) * ((q₁ * q₂).den : ZMod 8) := by
    exact_mod_cast congrArg (Int.cast (R := ZMod 8)) hEqZ
  have hM := congrArg
    (fun t : ZMod 8 => t * ((q₁.den : ZMod 8) * (q₂.den : ZMod 8) * ((q₁ * q₂).den : ZMod 8))) hMod
  unfold redMod8
  calc ((q₁ * q₂).num : ZMod 8) * ((q₁ * q₂).den : ZMod 8)
      = ((q₁ * q₂).num : ZMod 8) * ((q₁ * q₂).den : ZMod 8) *
          ((q₁.den : ZMod 8) * (q₁.den : ZMod 8)) * ((q₂.den : ZMod 8) * (q₂.den : ZMod 8)) := by
        rw [hs1, hs2, mul_one, mul_one]
    _ = ((q₁ * q₂).num : ZMod 8) * ((q₁.den : ZMod 8) * (q₂.den : ZMod 8)) *
          ((q₁.den : ZMod 8) * (q₂.den : ZMod 8) * ((q₁ * q₂).den : ZMod 8)) := by ring
    _ = ((q₁.num : ZMod 8) * (q₂.num : ZMod 8)) * ((q₁ * q₂).den : ZMod 8) *
          ((q₁.den : ZMod 8) * (q₂.den : ZMod 8) * ((q₁ * q₂).den : ZMod 8)) := hM
    _ = ((q₁.num : ZMod 8) * (q₁.den : ZMod 8)) * ((q₂.num : ZMod 8) * (q₂.den : ZMod 8)) *
          (((q₁ * q₂).den : ZMod 8) * ((q₁ * q₂).den : ZMod 8)) := by ring
    _ = (q₁.num : ZMod 8) * (q₁.den : ZMod 8) * ((q₂.num : ZMod 8) * (q₂.den : ZMod 8)) := by
        rw [hs12, mul_one]

theorem redMod8_add {q₁ q₂ : ℚ} (h₁ : ¬ 2 ∣ q₁.den) (h₂ : ¬ 2 ∣ q₂.den) :
    redMod8 (q₁ + q₂) = redMod8 q₁ + redMod8 q₂ := by
  have h12 : ¬ 2 ∣ (q₁ + q₂).den := by
    intro hd
    have hdiv : (q₁ + q₂).den ∣ q₁.den * q₂.den := Rat.add_den_dvd q₁ q₂
    rcases Nat.prime_two.dvd_mul.mp (dvd_trans hd hdiv) with h | h
    · exact h₁ h
    · exact h₂ h
  have hs1 : (q₁.den : ZMod 8) * (q₁.den : ZMod 8) = 1 :=
    zmod8_odd_sq_eq_one _ (nat_cast_zmod8_odd h₁)
  have hs2 : (q₂.den : ZMod 8) * (q₂.den : ZMod 8) = 1 :=
    zmod8_odd_sq_eq_one _ (nat_cast_zmod8_odd h₂)
  have hs12 : ((q₁ + q₂).den : ZMod 8) * ((q₁ + q₂).den : ZMod 8) = 1 :=
    zmod8_odd_sq_eq_one _ (nat_cast_zmod8_odd h12)
  have hEqQ : ((q₁ + q₂).num : ℚ) / ((q₁ + q₂).den : ℚ) =
      (q₁.num : ℚ) / (q₁.den : ℚ) + (q₂.num : ℚ) / (q₂.den : ℚ) := by
    rw [Rat.num_div_den, Rat.num_div_den, Rat.num_div_den]
  have hEqZ : (q₁ + q₂).num * ((q₁.den : ℤ) * (q₂.den : ℤ)) =
      (q₁.num * (q₂.den : ℤ) + q₂.num * (q₁.den : ℤ)) * ((q₁ + q₂).den : ℤ) := by
    have hq : ((q₁ + q₂).num : ℚ) * ((q₁.den : ℚ) * (q₂.den : ℚ)) =
        ((q₁.num : ℚ) * (q₂.den : ℚ) + (q₂.num : ℚ) * (q₁.den : ℚ)) * ((q₁ + q₂).den : ℚ) := by
      have hne1 : (q₁.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q₁.den_nz
      have hne2 : (q₂.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q₂.den_nz
      have hne12 : ((q₁ + q₂).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (q₁ + q₂).den_nz
      field_simp at hEqQ
      linarith
    exact_mod_cast hq
  have hMod : (((q₁ + q₂).num : ZMod 8)) * ((q₁.den : ZMod 8) * (q₂.den : ZMod 8)) =
      ((q₁.num : ZMod 8) * (q₂.den : ZMod 8) + (q₂.num : ZMod 8) * (q₁.den : ZMod 8)) *
        ((q₁ + q₂).den : ZMod 8) := by
    exact_mod_cast congrArg (Int.cast (R := ZMod 8)) hEqZ
  have hM := congrArg
    (fun t : ZMod 8 => t * ((q₁.den : ZMod 8) * (q₂.den : ZMod 8) * ((q₁ + q₂).den : ZMod 8))) hMod
  unfold redMod8
  calc ((q₁ + q₂).num : ZMod 8) * ((q₁ + q₂).den : ZMod 8)
      = ((q₁ + q₂).num : ZMod 8) * ((q₁ + q₂).den : ZMod 8) *
          ((q₁.den : ZMod 8) * (q₁.den : ZMod 8)) * ((q₂.den : ZMod 8) * (q₂.den : ZMod 8)) := by
        rw [hs1, hs2, mul_one, mul_one]
    _ = ((q₁ + q₂).num : ZMod 8) * ((q₁.den : ZMod 8) * (q₂.den : ZMod 8)) *
          ((q₁.den : ZMod 8) * (q₂.den : ZMod 8) * ((q₁ + q₂).den : ZMod 8)) := by ring
    _ = ((q₁.num : ZMod 8) * (q₂.den : ZMod 8) + (q₂.num : ZMod 8) * (q₁.den : ZMod 8)) *
          ((q₁ + q₂).den : ZMod 8) *
          ((q₁.den : ZMod 8) * (q₂.den : ZMod 8) * ((q₁ + q₂).den : ZMod 8)) := hM
    _ = (q₁.num : ZMod 8) * (q₁.den : ZMod 8) * ((q₂.den : ZMod 8) * (q₂.den : ZMod 8)) *
          (((q₁ + q₂).den : ZMod 8) * ((q₁ + q₂).den : ZMod 8)) +
        (q₂.num : ZMod 8) * (q₂.den : ZMod 8) * ((q₁.den : ZMod 8) * (q₁.den : ZMod 8)) *
          (((q₁ + q₂).den : ZMod 8) * ((q₁ + q₂).den : ZMod 8)) := by ring
    _ = (q₁.num : ZMod 8) * (q₁.den : ZMod 8) + (q₂.num : ZMod 8) * (q₂.den : ZMod 8) := by
        rw [hs1, hs2, hs12]; ring

theorem redMod8_neg (q : ℚ) : redMod8 (-q) = -redMod8 q := by
  unfold redMod8
  simp [Rat.neg_num, Rat.neg_den]

theorem redMod8_sub {q₁ q₂ : ℚ} (h₁ : ¬ 2 ∣ q₁.den) (h₂ : ¬ 2 ∣ q₂.den) :
    redMod8 (q₁ - q₂) = redMod8 q₁ - redMod8 q₂ := by
  rw [sub_eq_add_neg, redMod8_add h₁ (by simpa [Rat.neg_den] using h₂), redMod8_neg,
    ← sub_eq_add_neg]

@[simp]
theorem redMod8_intCast (z : ℤ) : redMod8 (z : ℚ) = (z : ZMod 8) := by
  unfold redMod8
  simp

@[simp]
theorem redMod8_natCast (n : ℕ) : redMod8 (n : ℚ) = (n : ZMod 8) := by
  unfold redMod8
  simp

@[simp]
theorem redMod8_one : redMod8 1 = 1 := by
  unfold redMod8
  simp

theorem redMod8_odd_of_val_eq_zero {q : ℚ} (hq0 : q ≠ 0) (hq : padicValRat 2 q = 0) :
    (redMod8 q).val % 2 = 1 := by
  obtain ⟨hnum, hden⟩ := not_dvd_num_and_den_of_padicValRat_eq_zero Nat.prime_two hq0 hq
  have hn := int_cast_zmod8_odd hnum
  have hd := nat_cast_zmod8_odd hden
  unfold redMod8
  generalize (q.num : ZMod 8) = x at hn ⊢
  generalize (q.den : ZMod 8) = y at hd ⊢
  revert hn hd
  fin_cases x <;> fin_cases y <;> decide

theorem eps8_eq_div_two_nat {n : ℕ} (hn : n % 2 = 1) :
    eps8 (n : ZMod 8) = ((n / 2 : ℕ) : ZMod 2) := by
  unfold eps8
  rw [ZMod.val_natCast]
  have h : (n % 8) / 2 % 2 = (n / 2) % 2 := by omega
  apply ZMod.val_injective
  simp only [ZMod.val_natCast, h]

theorem omega8_eq_chi8_nat {n : ℕ} (hn : n % 2 = 1) :
    (negOnePowZMod2 (omega8 (n : ZMod 8)) : ℤ) = ZMod.χ₈ n := by
  have hcases : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  have hval : (n : ZMod 8) = ((n % 8 : ℕ) : ZMod 8) := by
    apply ZMod.val_injective
    simp [ZMod.val_natCast]
  rw [hval]
  rcases hcases with h | h | h | h
  · rw [h]; simp [ZMod.χ₈]
  · rw [h]; simp [ZMod.χ₈]; decide
  · rw [h]; simp [ZMod.χ₈]; decide
  · rw [h]; simp [ZMod.χ₈]; decide

end PadicReduction

/-! ## Section 2: Concrete Local Hilbert Symbols `(a, b)_v ∈ ℤˣ` & All Local Laws -/

section LocalHilbertSymbols

/-! ### 2A. The Archimedean Place `v = ∞` -/

/-- Local Hilbert symbol `(a, b)_∞ ∈ {±1}` at the real place `∞`:
`(a, b)_∞ = -1` iff `a < 0 ∧ b < 0`, else `1`. -/
def hilbertSymInf (a b : ℚˣ) : ℤˣ :=
  if (a : ℚ) < 0 ∧ (b : ℚ) < 0 then -1 else 1

/-- Real sign coordinate `ℚˣ → ZMod 2`: `1` iff `a < 0`. -/
def signInf (a : ℚˣ) : ZMod 2 :=
  if (a : ℚ) < 0 then 1 else 0

theorem signInf_mul (a b : ℚˣ) : signInf (a * b) = signInf a + signInf b := by
  unfold signInf
  rw [Units.val_mul]
  rcases lt_or_gt_of_ne a.ne_zero with ha | ha <;>
    rcases lt_or_gt_of_ne b.ne_zero with hb | hb
  · have h : 0 < (a : ℚ) * (b : ℚ) := mul_pos_of_neg_of_neg ha hb
    simp [ha, hb, not_lt.mpr h.le]; decide
  · have h : (a : ℚ) * (b : ℚ) < 0 := mul_neg_of_neg_of_pos ha hb
    simp [ha, not_lt.mpr hb.le, h]
  · have h : (a : ℚ) * (b : ℚ) < 0 := mul_neg_of_pos_of_neg ha hb
    simp [not_lt.mpr ha.le, hb, h]
  · have h : 0 < (a : ℚ) * (b : ℚ) := mul_pos ha hb
    simp [not_lt.mpr ha.le, not_lt.mpr hb.le, not_lt.mpr h.le]

@[simp]
theorem signInf_one : signInf 1 = 0 := by simp [signInf]

@[simp]
theorem signInf_neg_one : signInf (-1) = 1 := by simp [signInf]

theorem signInf_pos {a : ℚˣ} (ha : 0 < (a : ℚ)) : signInf a = 0 := by
  simp [signInf, not_lt.mpr ha.le]

theorem signInf_inv (a : ℚˣ) : signInf a⁻¹ = signInf a := by
  have h := signInf_mul a a⁻¹
  rw [mul_inv_cancel, signInf_one] at h
  have : ∀ x y : ZMod 2, 0 = x + y → y = x := by decide
  exact this _ _ h

theorem hilbertSymInf_eq_negOnePow (a b : ℚˣ) :
    hilbertSymInf a b = negOnePowZMod2 (signInf a * signInf b) := by
  unfold hilbertSymInf signInf
  by_cases ha : (a : ℚ) < 0 <;> by_cases hb : (b : ℚ) < 0 <;> simp [ha, hb]

theorem unitsToZMod2_hilbertSymInf (a b : ℚˣ) :
    unitsToZMod2 (hilbertSymInf a b) = signInf a * signInf b := by
  rw [hilbertSymInf_eq_negOnePow, unitsToZMod2_negOnePowZMod2]

theorem hilbertSymInf_symm (a b : ℚˣ) : hilbertSymInf a b = hilbertSymInf b a := by
  rw [hilbertSymInf_eq_negOnePow, hilbertSymInf_eq_negOnePow, mul_comm]

theorem hilbertSymInf_mul_left (a₁ a₂ b : ℚˣ) :
    hilbertSymInf (a₁ * a₂) b = hilbertSymInf a₁ b * hilbertSymInf a₂ b := by
  simp only [hilbertSymInf_eq_negOnePow, signInf_mul, add_mul, negOnePowZMod2_add]

theorem hilbertSymInf_mul_right (a b₁ b₂ : ℚˣ) :
    hilbertSymInf a (b₁ * b₂) = hilbertSymInf a b₁ * hilbertSymInf a b₂ := by
  rw [hilbertSymInf_symm, hilbertSymInf_mul_left, hilbertSymInf_symm, hilbertSymInf_symm b₂]

theorem hilbertSymInf_sq_left (a b : ℚˣ) : hilbertSymInf (a ^ 2) b = 1 := by
  rw [sq, hilbertSymInf_mul_left, intUnits_mul_self]

theorem hilbertSymInf_inv_left (a b : ℚˣ) : hilbertSymInf a⁻¹ b = hilbertSymInf a b := by
  simp only [hilbertSymInf_eq_negOnePow, signInf_inv]

theorem hilbertSymInf_self_neg (a : ℚˣ) : hilbertSymInf a (-a) = 1 := by
  unfold hilbertSymInf
  simp only [Units.val_neg, Left.neg_neg_iff]
  split_ifs with h
  · linarith
  · rfl

/-- **Steinberg Relation at `v = ∞`**: `(a, 1 - a)_∞ = 1` whenever `a ≠ 0, 1`. -/
theorem hilbertSymInf_steinberg (a b : ℚˣ) (hab : (b : ℚ) = 1 - (a : ℚ)) :
    hilbertSymInf a b = 1 := by
  unfold hilbertSymInf
  rw [hab]
  split_ifs with h
  · linarith
  · rfl

/-! ### 2B. Every Odd Prime `p ≠ 2` -/

/-- Local coordinate pair `(v_p(a) mod 2, (u_p(a) / p) in ZMod 2)` at an odd prime `p`. -/
def oddCoords (p : ℕ) (hp : p.Prime) (a : ℚˣ) : ZMod 2 × ZMod 2 :=
  ((padicValRat p (a : ℚ) : ZMod 2), unitsToZMod2 (pUnitLegUnit p hp a))

theorem oddCoords_mul (p : ℕ) (hp : p.Prime) (a b : ℚˣ) :
    oddCoords p hp (a * b) = oddCoords p hp a + oddCoords p hp b := by
  have : Fact p.Prime := ⟨hp⟩
  ext
  · change ((padicValRat p ((a * b : ℚˣ) : ℚ) : ZMod 2)) =
      (padicValRat p (a : ℚ) : ZMod 2) + (padicValRat p (b : ℚ) : ZMod 2)
    rw [Units.val_mul, padicValRat.mul a.ne_zero b.ne_zero, Int.cast_add]
  · change unitsToZMod2 (pUnitLegUnit p hp (a * b)) =
      unitsToZMod2 (pUnitLegUnit p hp a) + unitsToZMod2 (pUnitLegUnit p hp b)
    rw [pUnitLegUnit_mul, unitsToZMod2_mul]

theorem oddCoords_one (p : ℕ) (hp : p.Prime) : oddCoords p hp 1 = 0 := by
  ext
  · simp [oddCoords]
  · simp [oddCoords, pUnitLegUnit_one]

theorem oddCoords_inv (p : ℕ) (hp : p.Prime) (a : ℚˣ) : oddCoords p hp a⁻¹ = oddCoords p hp a := by
  have h := oddCoords_mul p hp a a⁻¹
  rw [mul_inv_cancel, oddCoords_one] at h
  have h2 : ∀ x y : ZMod 2, 0 = x + y → y = x := by decide
  exact Prod.ext (h2 _ _ (congrArg Prod.fst h)) (h2 _ _ (congrArg Prod.snd h))

/-- Local Hilbert symbol `(a, b)_p ∈ ℤˣ` at an odd prime `p ≠ 2`, via the tame-symbol formula
`(-1)^(α β (p-1)/2) * legendreSym p ((u^β * v^α).num * (u^β * v^α).den)` where `a = p^α u`, `b = p^β v`. -/
def hilbertSymOdd (p : ℕ) (hp : p.Prime) (_hp2 : p ≠ 2) (a b : ℚˣ) : ℤˣ :=
  let α : ℤ := padicValRat p (a : ℚ)
  let β : ℤ := padicValRat p (b : ℚ)
  let u : ℚˣ := pUnit p hp a
  let v : ℚˣ := pUnit p hp b
  (-1 : ℤˣ) ^ (α * β * ((p / 2 : ℕ) : ℤ)) *
    intToSignUnit (ratUnitLegendre p hp ((u ^ β * v ^ α : ℚˣ) : ℚ))

/-- Bilinear `ZMod 2` formula for `hilbertSymOdd`:
`unitsToZMod2 (hilbertSymOdd p a b) = ε_p * α₂ * β₂ + u₂ * β₂ + α₂ * v₂`. -/
theorem unitsToZMod2_hilbertSymOdd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a b : ℚˣ) :
    unitsToZMod2 (hilbertSymOdd p hp hp2 a b) =
      ((p / 2 : ℕ) : ZMod 2) * (oddCoords p hp a).1 * (oddCoords p hp b).1 +
        (oddCoords p hp a).2 * (oddCoords p hp b).1 +
        (oddCoords p hp a).1 * (oddCoords p hp b).2 := by
  have : Fact p.Prime := ⟨hp⟩
  set α : ℤ := padicValRat p (a : ℚ)
  set β : ℤ := padicValRat p (b : ℚ)
  set u : ℚˣ := pUnit p hp a
  set v : ℚˣ := pUnit p hp b
  have hu : padicValRat p (u : ℚ) = 0 := padicValRat_pUnit p hp a
  have hv : padicValRat p (v : ℚ) = 0 := padicValRat_pUnit p hp b
  have hleg_zpow : ∀ (w : ℚˣ) (_hw : padicValRat p (w : ℚ) = 0) (k : ℤ),
      intToSignUnit (ratUnitLegendre p hp ((w ^ k : ℚˣ) : ℚ)) =
        (intToSignUnit (ratUnitLegendre p hp (w : ℚ))) ^ k := by
    intro w hw k
    have hw_val : ∀ m : ℤ, padicValRat p ((w ^ m : ℚˣ) : ℚ) = 0 := fun m => by
      rw [padicValRat_zpow_unit hp w m, hw, mul_zero]
    have hw_mul : ∀ m n : ℤ,
        intToSignUnit (ratUnitLegendre p hp ((w ^ (m + n) : ℚˣ) : ℚ)) =
          intToSignUnit (ratUnitLegendre p hp ((w ^ m : ℚˣ) : ℚ)) *
            intToSignUnit (ratUnitLegendre p hp ((w ^ n : ℚˣ) : ℚ)) := by
      intro m n
      rw [zpow_add, Units.val_mul,
        ratUnitLegendre_mul hp (w ^ m).ne_zero (w ^ n).ne_zero (hw_val m) (hw_val n)]
      exact intToSignUnit_mul
        (ratUnitLegendre_eq_one_or_neg_one hp (w ^ m).ne_zero (hw_val m))
        (ratUnitLegendre_eq_one_or_neg_one hp (w ^ n).ne_zero (hw_val n))
    have hnat : ∀ n : ℕ,
        intToSignUnit (ratUnitLegendre p hp ((w ^ (n : ℤ) : ℚˣ) : ℚ)) =
          (intToSignUnit (ratUnitLegendre p hp (w : ℚ))) ^ n := by
      intro n
      induction n with
      | zero =>
        simp only [Nat.cast_zero, zpow_zero, Units.val_one, pow_zero]
        rw [ratUnitLegendre_eq_quadraticChar hp one_ne_zero padicValRat.one, redModP_one, map_one]
        exact intToSignUnit_one
      | succ n ih =>
        rw [Nat.cast_succ, hw_mul, ih, zpow_one, pow_succ]
    cases k with
    | ofNat n =>
      simpa using hnat n
    | negSucc n =>
      have h0 : intToSignUnit (ratUnitLegendre p hp ((w ^ (Int.negSucc n + (n + 1 : ℤ)) : ℚˣ) : ℚ)) = 1 := by
        have hsum : Int.negSucc n + (n + 1 : ℤ) = 0 := by omega
        rw [hsum, zpow_zero, Units.val_one,
          ratUnitLegendre_eq_quadraticChar hp one_ne_zero padicValRat.one, redModP_one, map_one]
        exact intToSignUnit_one
      rw [hw_mul] at h0
      have hpos' : intToSignUnit (ratUnitLegendre p hp ((w ^ (n + 1 : ℤ) : ℚˣ) : ℚ)) =
          (intToSignUnit (ratUnitLegendre p hp (w : ℚ))) ^ (n + 1) := by
        simpa using hnat (n + 1)
      rw [hpos'] at h0
      have hinv : intToSignUnit (ratUnitLegendre p hp ((w ^ Int.negSucc n : ℚˣ) : ℚ)) =
          (intToSignUnit (ratUnitLegendre p hp (w : ℚ))) ^ (n + 1) := by
        set x := intToSignUnit (ratUnitLegendre p hp ((w ^ Int.negSucc n : ℚˣ) : ℚ))
        set y := (intToSignUnit (ratUnitLegendre p hp (w : ℚ))) ^ (n + 1)
        calc x = x * (y * y) := by rw [intUnits_mul_self, mul_one]
          _ = (x * y) * y := by rw [mul_assoc]
          _ = y := by rw [h0, one_mul]
      rw [hinv, zpow_negSucc, intUnits_inv_eq]
  have huv_val : padicValRat p ((u ^ β : ℚˣ) : ℚ) = 0 ∧ padicValRat p ((v ^ α : ℚˣ) : ℚ) = 0 :=
    ⟨by rw [padicValRat_zpow_unit hp u β, hu, mul_zero],
     by rw [padicValRat_zpow_unit hp v α, hv, mul_zero]⟩
  unfold hilbertSymOdd
  dsimp only
  rw [Units.val_mul, ratUnitLegendre_mul hp (u ^ β).ne_zero (v ^ α).ne_zero huv_val.1 huv_val.2,
    intToSignUnit_mul
      (ratUnitLegendre_eq_one_or_neg_one hp (u ^ β).ne_zero huv_val.1)
      (ratUnitLegendre_eq_one_or_neg_one hp (v ^ α).ne_zero huv_val.2),
    hleg_zpow u hu β, hleg_zpow v hv α,
    unitsToZMod2_mul, unitsToZMod2_mul, unitsToZMod2_zpow, unitsToZMod2_zpow, unitsToZMod2_zpow,
    unitsToZMod2_neg_one, mul_one, Int.cast_mul, Int.cast_mul, Int.cast_natCast]
  unfold oddCoords pUnitLegUnit
  dsimp only
  ring

theorem hilbertSymOdd_eq_negOnePow (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a b : ℚˣ) :
    hilbertSymOdd p hp hp2 a b =
      negOnePowZMod2
        (((p / 2 : ℕ) : ZMod 2) * (oddCoords p hp a).1 * (oddCoords p hp b).1 +
          (oddCoords p hp a).2 * (oddCoords p hp b).1 +
          (oddCoords p hp a).1 * (oddCoords p hp b).2) := by
  rw [← unitsToZMod2_hilbertSymOdd p hp hp2 a b, negOnePowZMod2_unitsToZMod2]

theorem hilbertSymOdd_symm (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a b : ℚˣ) :
    hilbertSymOdd p hp hp2 a b = hilbertSymOdd p hp hp2 b a := by
  rw [hilbertSymOdd_eq_negOnePow, hilbertSymOdd_eq_negOnePow]
  congr 1; ring

theorem hilbertSymOdd_mul_left (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a₁ a₂ b : ℚˣ) :
    hilbertSymOdd p hp hp2 (a₁ * a₂) b =
      hilbertSymOdd p hp hp2 a₁ b * hilbertSymOdd p hp hp2 a₂ b := by
  rw [hilbertSymOdd_eq_negOnePow, hilbertSymOdd_eq_negOnePow, hilbertSymOdd_eq_negOnePow,
    ← negOnePowZMod2_add, oddCoords_mul]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem hilbertSymOdd_mul_right (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a b₁ b₂ : ℚˣ) :
    hilbertSymOdd p hp hp2 a (b₁ * b₂) =
      hilbertSymOdd p hp hp2 a b₁ * hilbertSymOdd p hp hp2 a b₂ := by
  rw [hilbertSymOdd_symm p hp hp2 a (b₁ * b₂), hilbertSymOdd_mul_left,
    hilbertSymOdd_symm p hp hp2 b₁ a, hilbertSymOdd_symm p hp hp2 b₂ a]

theorem hilbertSymOdd_sq_left (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a b : ℚˣ) :
    hilbertSymOdd p hp hp2 (a ^ 2) b = 1 := by
  rw [sq, hilbertSymOdd_mul_left, intUnits_mul_self]

theorem hilbertSymOdd_inv_left (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a b : ℚˣ) :
    hilbertSymOdd p hp hp2 a⁻¹ b = hilbertSymOdd p hp hp2 a b := by
  simp only [hilbertSymOdd_eq_negOnePow, oddCoords_inv]

theorem hilbertSymOdd_eq_one_of_even_val (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {a b : ℚˣ}
    (ha : (2 : ℤ) ∣ padicValRat p (a : ℚ)) (hb : (2 : ℤ) ∣ padicValRat p (b : ℚ)) :
    hilbertSymOdd p hp hp2 a b = 1 := by
  rw [hilbertSymOdd_eq_negOnePow]
  have ha0 : (oddCoords p hp a).1 = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr ha
  have hb0 : (oddCoords p hp b).1 = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hb
  rw [ha0, hb0]
  simp

theorem hilbertSymOdd_eq_one_of_val_zero (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {a b : ℚˣ}
    (ha : padicValRat p (a : ℚ) = 0) (hb : padicValRat p (b : ℚ) = 0) :
    hilbertSymOdd p hp hp2 a b = 1 :=
  hilbertSymOdd_eq_one_of_even_val p hp hp2 (ha ▸ dvd_zero 2) (hb ▸ dvd_zero 2)

theorem hilbertSymOdd_self_neg (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a : ℚˣ) :
    hilbertSymOdd p hp hp2 a (-a) = 1 := by
  rw [hilbertSymOdd_eq_negOnePow]
  have hneg : -a = (-1 : ℚˣ) * a := by simp
  have hcoords : oddCoords p hp (-a) = oddCoords p hp (-1) + oddCoords p hp a := by
    rw [hneg, oddCoords_mul]
  have h1 : (oddCoords p hp (-1)).1 = 0 := by simp [oddCoords]
  have h2 : (oddCoords p hp (-1)).2 = ((p / 2 : ℕ) : ZMod 2) := by
    change unitsToZMod2 (pUnitLegUnit p hp (-1)) = _
    rw [pUnitLegUnit_neg_one p hp hp2, ← negOnePowZMod2_natCast, unitsToZMod2_negOnePowZMod2]
  rw [hcoords]
  simp only [Prod.fst_add, Prod.snd_add, h1, h2, zero_add]
  have hz : ∀ x y e : ZMod 2, e * x * x + y * x + x * (e + y) = 0 := by decide
  rw [hz]
  rfl

/-- Helper: if `0 < padicValRat p a` and `(b : ℚ) = 1 - (a : ℚ)`, then `oddCoords p hp b = 0`. -/
private theorem oddCoords_one_sub_of_pos_val (p : ℕ) (hp : p.Prime) {a b : ℚˣ}
    (ha : 0 < padicValRat p (a : ℚ)) (hab : (b : ℚ) = 1 - (a : ℚ)) :
    oddCoords p hp b = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hadd_ne : (1 : ℚ) + -(a : ℚ) ≠ 0 := by
    rw [← sub_eq_add_neg, ← hab]; exact b.ne_zero
  have hb_val : padicValRat p (b : ℚ) = 0 := by
    rw [hab, sub_eq_add_neg]
    have hne : padicValRat p (1 : ℚ) ≠ padicValRat p (-(a : ℚ)) := by
      rw [padicValRat.one, padicValRat.neg]; omega
    rw [padicValRat.add_eq_min hadd_ne one_ne_zero (neg_ne_zero.mpr a.ne_zero) hne,
      padicValRat.one, padicValRat.neg]
    exact min_eq_left (le_of_lt ha)
  have hred : redModP p (b : ℚ) = 1 := by
    rw [hab, redModP_sub hp (by simp [hp.not_dvd_one]) (dvd_num_of_pos_padicValRat hp ha).2,
      redModP_one, redModP_eq_zero_of_pos_val hp ha, sub_zero]
  ext
  · change (padicValRat p (b : ℚ) : ZMod 2) = 0
    rw [hb_val, Int.cast_zero]
  · change unitsToZMod2 (pUnitLegUnit p hp b) = 0
    unfold pUnitLegUnit
    rw [pUnit_of_val_zero p hp hb_val, ratUnitLegendre_eq_quadraticChar hp b.ne_zero hb_val,
      hred, map_one, intToSignUnit_one, unitsToZMod2_one]

/-- **Steinberg Relation at Every Odd Prime `p`**: `(a, 1 - a)_p = 1` whenever `a ≠ 0, 1`. -/
theorem hilbertSymOdd_steinberg (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a b : ℚˣ)
    (hab : (b : ℚ) = 1 - (a : ℚ)) :
    hilbertSymOdd p hp hp2 a b = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases lt_trichotomy 0 (padicValRat p (a : ℚ)) with hpos | hzero | hneg
  · have hb0 := oddCoords_one_sub_of_pos_val p hp hpos hab
    rw [hilbertSymOdd_eq_negOnePow, hb0]
    simp
  · have hadd_ne : (1 : ℚ) + -(a : ℚ) ≠ 0 := by
      rw [← sub_eq_add_neg, ← hab]; exact b.ne_zero
    have hb_ge : 0 ≤ padicValRat p (b : ℚ) := by
      rw [hab, sub_eq_add_neg]
      have h := padicValRat.min_le_padicValRat_add (p := p) hadd_ne
      rw [padicValRat.one, padicValRat.neg, ← hzero, min_self] at h
      exact h
    rcases eq_or_lt_of_le hb_ge with hb0 | hbpos
    · exact hilbertSymOdd_eq_one_of_val_zero p hp hp2 hzero.symm hb0.symm
    · have ha_eq : (a : ℚ) = 1 - (b : ℚ) := by linarith
      have ha0 := oddCoords_one_sub_of_pos_val p hp hbpos ha_eq
      rw [hilbertSymOdd_eq_negOnePow, ha0]
      simp
  · have hpos_inv : 0 < padicValRat p ((a⁻¹ : ℚˣ) : ℚ) := by
      rw [Units.val_inv_eq_inv_val, padicValRat.inv]; omega
    have hne : 1 - ((a⁻¹ : ℚˣ) : ℚ) ≠ 0 := by
      intro h0
      have ha1 : (a : ℚ) = 1 := by
        rw [Units.val_inv_eq_inv_val] at h0
        exact inv_eq_one.mp (by linarith)
      exact b.ne_zero (by rw [hab, ha1, sub_self])
    let c : ℚˣ := Units.mk0 (1 - ((a⁻¹ : ℚˣ) : ℚ)) hne
    have hbc : b = (-a) * c := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_neg, c, Units.val_mk0, Units.val_inv_eq_inv_val, hab]
      field_simp [a.ne_zero]
      ring
    have hc0 : oddCoords p hp c = 0 := oddCoords_one_sub_of_pos_val p hp hpos_inv rfl
    rw [hbc, hilbertSymOdd_mul_right, hilbertSymOdd_self_neg, one_mul,
      hilbertSymOdd_eq_negOnePow, hc0]
    simp

/-! ### 2C. The Dyadic Prime `p = 2` -/

/-- Local coordinate triple `(v_2(a) mod 2, ε(u_2(a)), ω(u_2(a))) ∈ (ZMod 2)³` at `p = 2`. -/
def twoCoords (a : ℚˣ) : ZMod 2 × ZMod 2 × ZMod 2 :=
  ((padicValRat 2 (a : ℚ) : ZMod 2),
    eps8 (redMod8 (pUnit 2 Nat.prime_two a : ℚ)),
    omega8 (redMod8 (pUnit 2 Nat.prime_two a : ℚ)))

theorem twoCoords_mul (a b : ℚˣ) : twoCoords (a * b) = twoCoords a + twoCoords b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu : padicValRat 2 (pUnit 2 Nat.prime_two a : ℚ) = 0 := padicValRat_pUnit 2 Nat.prime_two a
  have hv : padicValRat 2 (pUnit 2 Nat.prime_two b : ℚ) = 0 := padicValRat_pUnit 2 Nat.prime_two b
  have hdu : ¬ 2 ∣ (pUnit 2 Nat.prime_two a : ℚ).den :=
    not_dvd_den_of_nonneg_padicValRat Nat.prime_two (le_of_eq hu.symm)
  have hdv : ¬ 2 ∣ (pUnit 2 Nat.prime_two b : ℚ).den :=
    not_dvd_den_of_nonneg_padicValRat Nat.prime_two (le_of_eq hv.symm)
  have hou : (redMod8 (pUnit 2 Nat.prime_two a : ℚ)).val % 2 = 1 :=
    redMod8_odd_of_val_eq_zero (pUnit 2 Nat.prime_two a).ne_zero hu
  have hov : (redMod8 (pUnit 2 Nat.prime_two b : ℚ)).val % 2 = 1 :=
    redMod8_odd_of_val_eq_zero (pUnit 2 Nat.prime_two b).ne_zero hv
  unfold twoCoords
  rw [Units.val_mul, padicValRat.mul a.ne_zero b.ne_zero, Int.cast_add, pUnit_mul, Units.val_mul,
    redMod8_mul hdu hdv, eps8_mul hou hov, omega8_mul hou hov]
  rfl

theorem twoCoords_one : twoCoords 1 = 0 := by
  unfold twoCoords
  simp [pUnit_one]

theorem twoCoords_inv (a : ℚˣ) : twoCoords a⁻¹ = twoCoords a := by
  have h := twoCoords_mul a a⁻¹
  rw [mul_inv_cancel, twoCoords_one] at h
  have h2 : ∀ x y : ZMod 2, 0 = x + y → y = x := by decide
  refine Prod.ext (h2 _ _ (congrArg Prod.fst h))
    (Prod.ext (h2 _ _ (congrArg (fun p => p.2.1) h)) (h2 _ _ (congrArg (fun p => p.2.2) h)))

/-- Local Hilbert symbol `(a, b)_2 ∈ ℤˣ` at `p = 2` via the exact `ZMod 8` formula
`(-1)^(ε(u) ε(v) + α ω(v) + β ω(u))` where `a = 2^α u`, `b = 2^β v`. -/
def hilbertSymTwo (a b : ℚˣ) : ℤˣ :=
  negOnePowZMod2
    ((twoCoords a).2.1 * (twoCoords b).2.1 +
      (twoCoords a).1 * (twoCoords b).2.2 +
      (twoCoords b).1 * (twoCoords a).2.2)

theorem unitsToZMod2_hilbertSymTwo (a b : ℚˣ) :
    unitsToZMod2 (hilbertSymTwo a b) =
      (twoCoords a).2.1 * (twoCoords b).2.1 +
        (twoCoords a).1 * (twoCoords b).2.2 +
        (twoCoords b).1 * (twoCoords a).2.2 :=
  unitsToZMod2_negOnePowZMod2 _

theorem hilbertSymTwo_symm (a b : ℚˣ) : hilbertSymTwo a b = hilbertSymTwo b a := by
  unfold hilbertSymTwo
  congr 1; ring

theorem hilbertSymTwo_mul_left (a₁ a₂ b : ℚˣ) :
    hilbertSymTwo (a₁ * a₂) b = hilbertSymTwo a₁ b * hilbertSymTwo a₂ b := by
  unfold hilbertSymTwo
  rw [← negOnePowZMod2_add, twoCoords_mul]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem hilbertSymTwo_mul_right (a b₁ b₂ : ℚˣ) :
    hilbertSymTwo a (b₁ * b₂) = hilbertSymTwo a b₁ * hilbertSymTwo a b₂ := by
  rw [hilbertSymTwo_symm, hilbertSymTwo_mul_left, hilbertSymTwo_symm, hilbertSymTwo_symm b₂]

theorem hilbertSymTwo_sq_left (a b : ℚˣ) : hilbertSymTwo (a ^ 2) b = 1 := by
  rw [sq, hilbertSymTwo_mul_left, intUnits_mul_self]

theorem hilbertSymTwo_inv_left (a b : ℚˣ) : hilbertSymTwo a⁻¹ b = hilbertSymTwo a b := by
  simp only [hilbertSymTwo, twoCoords_inv]

theorem twoCoords_neg_one : twoCoords (-1) = (0, 1, 0) := by
  unfold twoCoords
  have hv : padicValRat 2 ((-1 : ℚˣ) : ℚ) = 0 := by simp
  rw [pUnit_of_val_zero 2 Nat.prime_two hv, hv, Int.cast_zero]
  have hr : redMod8 ((-1 : ℚˣ) : ℚ) = -1 := by
    rw [Units.val_neg, Units.val_one, redMod8_neg, redMod8_one]
  rw [hr, eps8_neg_one, omega8_neg_one]

theorem hilbertSymTwo_self_neg (a : ℚˣ) : hilbertSymTwo a (-a) = 1 := by
  unfold hilbertSymTwo
  have hneg : -a = (-1 : ℚˣ) * a := by simp
  have hcoords : twoCoords (-a) = twoCoords (-1) + twoCoords a := by
    rw [hneg, twoCoords_mul]
  rw [hcoords, twoCoords_neg_one]
  simp only [Prod.fst_add, Prod.snd_add, zero_add]
  have hz : ∀ α ε ω : ZMod 2, ε * (1 + ε) + α * ω + α * ω = 0 := by decide
  rw [hz]
  rfl

/-- Helper: Steinberg relation at `p = 2` when `0 < padicValRat 2 a`. -/
private theorem hilbertSymTwo_steinberg_of_pos_val {a b : ℚˣ}
    (ha : 0 < padicValRat 2 (a : ℚ)) (hab : (b : ℚ) = 1 - (a : ℚ)) :
    hilbertSymTwo a b = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadd_ne : (1 : ℚ) + -(a : ℚ) ≠ 0 := by
    rw [← sub_eq_add_neg, ← hab]; exact b.ne_zero
  have hb_val : padicValRat 2 (b : ℚ) = 0 := by
    rw [hab, sub_eq_add_neg]
    have hne : padicValRat 2 (1 : ℚ) ≠ padicValRat 2 (-(a : ℚ)) := by
      rw [padicValRat.one, padicValRat.neg]; omega
    rw [padicValRat.add_eq_min hadd_ne one_ne_zero (neg_ne_zero.mpr a.ne_zero) hne,
      padicValRat.one, padicValRat.neg]
    exact min_eq_left (le_of_lt ha)
  set α : ℤ := padicValRat 2 (a : ℚ)
  set k : ℕ := α.toNat
  have hk_eq : (k : ℤ) = α := Int.toNat_of_nonneg (le_of_lt ha)
  set u : ℚˣ := pUnit 2 Nat.prime_two a
  have hu_val : padicValRat 2 (u : ℚ) = 0 := padicValRat_pUnit 2 Nat.prime_two a
  have hdu : ¬ 2 ∣ (u : ℚ).den :=
    not_dvd_den_of_nonneg_padicValRat Nat.prime_two (le_of_eq hu_val.symm)
  have hou : (redMod8 (u : ℚ)).val % 2 = 1 := redMod8_odd_of_val_eq_zero u.ne_zero hu_val
  have ha_eq : (a : ℚ) = (2 : ℚ) ^ k * (u : ℚ) := by
    have hs := congrArg (fun x : ℚˣ => (x : ℚ)) (pUnit_spec 2 Nat.prime_two a)
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, coe_primeUnit] at hs
    change (a : ℚ) = (2 : ℚ) ^ α * (u : ℚ) at hs
    rw [← hk_eq, zpow_natCast] at hs
    exact hs
  have hda : ¬ 2 ∣ (a : ℚ).den := not_dvd_den_of_nonneg_padicValRat Nat.prime_two (le_of_lt ha)
  have hred_a : redMod8 (a : ℚ) = (2 : ZMod 8) ^ k * redMod8 (u : ℚ) := by
    rw [ha_eq]
    have hpow_den : ¬ 2 ∣ ((2 : ℚ) ^ k).den := by
      have : ((2 : ℚ) ^ k) = (((2 ^ k : ℕ) : ℚ)) := by norm_cast
      rw [this]; simp
    rw [redMod8_mul hpow_den hdu]
    have hpow_mod : redMod8 ((2 : ℚ) ^ k) = (2 : ZMod 8) ^ k := by
      have : ((2 : ℚ) ^ k) = (((2 ^ k : ℕ) : ℚ)) := by norm_cast
      rw [this, redMod8_natCast, Nat.cast_pow, Nat.cast_ofNat]
    rw [hpow_mod]
  have hred_b : redMod8 (b : ℚ) = 1 - (2 : ZMod 8) ^ k * redMod8 (u : ℚ) := by
    rw [hab, redMod8_sub (by simp) hda, redMod8_one, hred_a]
  have hcb_eq : twoCoords b = (0, eps8 (redMod8 (b : ℚ)), omega8 (redMod8 (b : ℚ))) := by
    unfold twoCoords
    rw [hb_val, Int.cast_zero, pUnit_of_val_zero 2 Nat.prime_two hb_val]
  unfold hilbertSymTwo
  rw [hcb_eq]
  change negOnePowZMod2
    (eps8 (redMod8 (u : ℚ)) * eps8 (redMod8 (b : ℚ)) +
      (α : ZMod 2) * omega8 (redMod8 (b : ℚ)) +
      0 * omega8 (redMod8 (u : ℚ))) = 1
  rw [zero_mul, add_zero, hred_b, ← hk_eq, Int.cast_natCast]
  have hk_ge1 : 1 ≤ k := by omega
  rcases eq_or_lt_of_le hk_ge1 with hk1 | hk_ge2
  · rw [← hk1]
    simp only [pow_one, Nat.cast_one, one_mul]
    rw [steinberg_zmod8_alpha_one hou]
    rfl
  · have hk_ge2' : 2 ≤ k := hk_ge2
    rcases eq_or_lt_of_le hk_ge2' with hk2 | hk_ge3
    · rw [← hk2]
      have h22 : ((2 : ℕ) : ZMod 2) = 0 := ZMod.natCast_self 2
      have hpow2 : (2 : ZMod 8) ^ 2 = 4 := by decide
      rw [h22, zero_mul, add_zero, hpow2, steinberg_zmod8_alpha_two hou, mul_zero]
      rfl
    · have hpow0 : (2 : ZMod 8) ^ k = 0 := by
        obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hk_ge3
        rw [hm, pow_add]
        have h23 : (2 : ZMod 8) ^ 3 = 0 := by decide
        rw [h23, zero_mul]
      rw [hpow0, zero_mul, sub_zero, eps8_one, omega8_one, mul_zero, mul_zero, add_zero]
      rfl

/-- **Steinberg Relation at `p = 2`**: `(a, 1 - a)_2 = 1` whenever `a ≠ 0, 1`. -/
theorem hilbertSymTwo_steinberg (a b : ℚˣ) (hab : (b : ℚ) = 1 - (a : ℚ)) :
    hilbertSymTwo a b = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases lt_trichotomy 0 (padicValRat 2 (a : ℚ)) with hpos | hzero | hneg
  · exact hilbertSymTwo_steinberg_of_pos_val hpos hab
  · have hb_pos : 0 < padicValRat 2 (b : ℚ) := by
      obtain ⟨_, hden⟩ := not_dvd_num_and_den_of_padicValRat_eq_zero Nat.prime_two a.ne_zero hzero.symm
      have hden_odd : ¬ 2 ∣ (b : ℚ).den := by
        rw [hab, sub_eq_add_neg]
        intro hd
        have hdiv : (1 + -(a : ℚ)).den ∣ (1 : ℚ).den * (-(a : ℚ)).den := Rat.add_den_dvd 1 (-(a : ℚ))
        rw [Rat.den_one, one_mul, Rat.neg_den] at hdiv
        exact hden (dvd_trans hd hdiv)
      have hred_b : (redMod8 (b : ℚ)).val % 2 = 0 := by
        have hrb : redMod8 (b : ℚ) = 1 - redMod8 (a : ℚ) := by
          rw [hab, redMod8_sub (by simp) hden, redMod8_one]
        have hoa := redMod8_odd_of_val_eq_zero a.ne_zero hzero.symm
        rw [hrb]
        generalize redMod8 (a : ℚ) = x at hoa ⊢
        revert hoa; fin_cases x <;> decide
      have h2_dvd_num : (2 : ℤ) ∣ (b : ℚ).num := by
        by_contra hnd
        have hb_odd : (redMod8 (b : ℚ)).val % 2 = 1 := by
          have hn := int_cast_zmod8_odd hnd
          have hd := nat_cast_zmod8_odd hden_odd
          unfold redMod8
          generalize ((b : ℚ).num : ZMod 8) = x at hn ⊢
          generalize ((b : ℚ).den : ZMod 8) = y at hd ⊢
          revert hn hd; fin_cases x <;> fin_cases y <;> decide
        omega
      have hden_val : padicValNat 2 (b : ℚ).den = 0 := padicValNat.eq_zero_of_not_dvd hden_odd
      have hnum_val : 0 < padicValNat 2 (b : ℚ).num.natAbs :=
        one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr b.ne_zero))
          (Int.natCast_dvd.mp h2_dvd_num)
      rw [padicValRat_def, hden_val]
      change 0 < (padicValNat 2 (b : ℚ).num.natAbs : ℤ) - 0
      omega
    have ha_eq : (a : ℚ) = 1 - (b : ℚ) := by linarith
    rw [hilbertSymTwo_symm]
    exact hilbertSymTwo_steinberg_of_pos_val hb_pos ha_eq
  · have hpos_inv : 0 < padicValRat 2 ((a⁻¹ : ℚˣ) : ℚ) := by
      rw [Units.val_inv_eq_inv_val, padicValRat.inv]; omega
    have hne : 1 - ((a⁻¹ : ℚˣ) : ℚ) ≠ 0 := by
      intro h0
      have ha1 : (a : ℚ) = 1 := by
        rw [Units.val_inv_eq_inv_val] at h0
        exact inv_eq_one.mp (by linarith)
      exact b.ne_zero (by rw [hab, ha1, sub_self])
    let c : ℚˣ := Units.mk0 (1 - ((a⁻¹ : ℚˣ) : ℚ)) hne
    have hbc : b = (-a) * c := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_neg, c, Units.val_mk0, Units.val_inv_eq_inv_val, hab]
      field_simp [a.ne_zero]
      ring
    rw [hbc, hilbertSymTwo_mul_right, hilbertSymTwo_self_neg, one_mul, ← hilbertSymTwo_inv_left]
    exact hilbertSymTwo_steinberg_of_pos_val hpos_inv rfl

end LocalHilbertSymbols

/-! ## Section 3: Unconditional Hilbert-Symbol Reciprocity Product Formula over `ℚ` -/

section HilbertReciprocity

/-- The type of odd rational primes `{p : ℕ // p.Prime ∧ p ≠ 2}`. -/
abbrev OddPrime : Type := {p : ℕ // p.Prime ∧ p ≠ 2}

/-- If `padicValRat p q ≠ 0`, then `p ∣ q.num.natAbs ∨ p ∣ q.den`. -/
theorem dvd_num_or_den_of_padicValRat_ne_zero {p : ℕ} {q : ℚ}
    (h : padicValRat p q ≠ 0) :
    p ∣ q.num.natAbs ∨ p ∣ q.den := by
  by_contra hnor
  push Not at hnor
  have h1 : padicValNat p q.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hnor.1
  have h2 : padicValNat p q.den = 0 := padicValNat.eq_zero_of_not_dvd hnor.2
  rw [padicValRat_def] at h
  have h1' : padicValInt p q.num = 0 := h1
  rw [h1', h2] at h
  exact h (by simp)

/-- **Finite Multiplicative Support of Local Hilbert Symbols**:
for every `a, b ∈ ℚˣ`, `hilbertSymOdd p a b = 1` for all but finitely many odd primes `p`. -/
theorem hasFiniteMulSupport_hilbertSym (a b : ℚˣ) :
    (Function.mulSupport fun p : OddPrime => hilbertSymOdd p.1 p.2.1 p.2.2 a b).Finite := by
  let S : Finset ℕ :=
    (a : ℚ).num.natAbs.primeFactors ∪ (a : ℚ).den.primeFactors ∪
      (b : ℚ).num.natAbs.primeFactors ∪ (b : ℚ).den.primeFactors
  have hsub :
      (Function.mulSupport fun p : OddPrime => hilbertSymOdd p.1 p.2.1 p.2.2 a b) ⊆
        Subtype.val ⁻¹' (S : Set ℕ) := by
    intro p hp
    rw [Function.mem_mulSupport] at hp
    have hval : padicValRat p.1 (a : ℚ) ≠ 0 ∨ padicValRat p.1 (b : ℚ) ≠ 0 := by
      by_contra hboth
      push Not at hboth
      exact hp (hilbertSymOdd_eq_one_of_val_zero p.1 p.2.1 p.2.2 hboth.1 hboth.2)
    simp only [Set.mem_preimage, Finset.mem_coe, S, Finset.mem_union, Nat.mem_primeFactors]
    rcases hval with ha | hb
    · rcases dvd_num_or_den_of_padicValRat_ne_zero ha with h | h
      · exact Or.inl (Or.inl (Or.inl ⟨p.2.1, h, Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr a.ne_zero)⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨p.2.1, h, (a : ℚ).den_nz⟩))
    · rcases dvd_num_or_den_of_padicValRat_ne_zero hb with h | h
      · exact Or.inl (Or.inr ⟨p.2.1, h, Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr b.ne_zero)⟩)
      · exact Or.inr ⟨p.2.1, h, (b : ℚ).den_nz⟩
  exact ((S.finite_toSet).preimage Subtype.val_injective.injOn).subset hsub

/-- The global Hilbert-symbol product `∏_v (a, b)_v` over all places `v ∈ {∞, 2} ∪ OddPrime`. -/
def hilbertProd (a b : ℚˣ) : ℤˣ :=
  hilbertSymInf a b * hilbertSymTwo a b *
    ∏ᶠ p : OddPrime, hilbertSymOdd p.1 p.2.1 p.2.2 a b

theorem hilbertProd_symm (a b : ℚˣ) : hilbertProd a b = hilbertProd b a := by
  unfold hilbertProd
  rw [hilbertSymInf_symm, hilbertSymTwo_symm]
  congr 1
  apply finprod_congr
  intro p
  exact hilbertSymOdd_symm p.1 p.2.1 p.2.2 a b

theorem hilbertProd_mul_left (a₁ a₂ b : ℚˣ) :
    hilbertProd (a₁ * a₂) b = hilbertProd a₁ b * hilbertProd a₂ b := by
  unfold hilbertProd
  rw [hilbertSymInf_mul_left, hilbertSymTwo_mul_left]
  have hfp :
      (∏ᶠ p : OddPrime, hilbertSymOdd p.1 p.2.1 p.2.2 (a₁ * a₂) b) =
        (∏ᶠ p : OddPrime, hilbertSymOdd p.1 p.2.1 p.2.2 a₁ b) *
          (∏ᶠ p : OddPrime, hilbertSymOdd p.1 p.2.1 p.2.2 a₂ b) := by
    rw [← finprod_mul_distrib (hasFiniteMulSupport_hilbertSym a₁ b)
      (hasFiniteMulSupport_hilbertSym a₂ b)]
    apply finprod_congr
    intro p
    exact hilbertSymOdd_mul_left p.1 p.2.1 p.2.2 a₁ a₂ b
  rw [hfp]
  ac_rfl

theorem hilbertProd_mul_right (a b₁ b₂ : ℚˣ) :
    hilbertProd a (b₁ * b₂) = hilbertProd a b₁ * hilbertProd a b₂ := by
  rw [hilbertProd_symm, hilbertProd_mul_left, hilbertProd_symm, hilbertProd_symm b₂]

theorem hilbertProd_one_left (b : ℚˣ) : hilbertProd 1 b = 1 := by
  have h := hilbertProd_mul_left 1 1 b
  rw [one_mul, intUnits_mul_self] at h
  exact h

theorem hilbertProd_inv_left (a b : ℚˣ) : hilbertProd a⁻¹ b = hilbertProd a b := by
  have h := hilbertProd_mul_left a a⁻¹ b
  rw [mul_inv_cancel, hilbertProd_one_left] at h
  calc hilbertProd a⁻¹ b = hilbertProd a b * (hilbertProd a b * hilbertProd a⁻¹ b) := by
        rw [← mul_assoc, intUnits_mul_self, one_mul]
    _ = hilbertProd a b := by rw [← h, mul_one]

theorem hilbertProd_one_right (a : ℚˣ) : hilbertProd a 1 = 1 := by
  rw [hilbertProd_symm, hilbertProd_one_left]

theorem hilbertProd_inv_right (a b : ℚˣ) : hilbertProd a b⁻¹ = hilbertProd a b := by
  rw [hilbertProd_symm, hilbertProd_inv_left, hilbertProd_symm]

/-- Generating set `{-1} ∪ {p | p.Prime}` of `ℚˣ`. -/
def ratUnitsGen : Set ℚˣ :=
  {-1} ∪ {x | ∃ (p : ℕ) (hp : p.Prime), x = primeUnit p hp}

/-- Every nonzero natural number lies in `Subgroup.closure ratUnitsGen`. -/
theorem nat_unit_mem_closure_ratUnitsGen :
    ∀ (n : ℕ) (hn : n ≠ 0),
      Units.mk0 (n : ℚ) (Nat.cast_ne_zero.mpr hn) ∈ Subgroup.closure ratUnitsGen := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst h1
      have : Units.mk0 ((1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn) = 1 := Units.ext (by simp)
      rw [this]
      exact (Subgroup.closure ratUnitsGen).one_mem
    · have hgt : 1 < n := by omega
      let p := n.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpdvd : p ∣ n := Nat.minFac_dvd n
      let m := n / p
      have hm_ne : m ≠ 0 := by
        have : p ≤ n := Nat.le_of_dvd (by omega) hpdvd
        exact (Nat.div_pos this hp.pos).ne'
      have hm_lt : m < n := Nat.div_lt_self (by omega) hp.one_lt
      have hmul : Units.mk0 (n : ℚ) (Nat.cast_ne_zero.mpr hn) =
          primeUnit p hp * Units.mk0 (m : ℚ) (Nat.cast_ne_zero.mpr hm_ne) := by
        apply Units.ext
        simp only [Units.val_mul, Units.val_mk0, coe_primeUnit]
        exact_mod_cast (Nat.mul_div_cancel' hpdvd).symm
      rw [hmul]
      refine Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr ⟨p, hp, rfl⟩)) (ih m hm_lt hm_ne)

/-- `{-1} ∪ {p | p.Prime}` generates `ℚˣ`. -/
theorem subgroup_closure_ratUnitsGen : Subgroup.closure ratUnitsGen = ⊤ := by
  rw [eq_top_iff]
  intro a _
  have hnum0 : (a : ℚ).num ≠ 0 := Rat.num_ne_zero.mpr a.ne_zero
  have hnumAbs0 : (a : ℚ).num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hnum0
  have hden0 : (a : ℚ).den ≠ 0 := (a : ℚ).den_nz
  let uNum : ℚˣ := Units.mk0 ((a : ℚ).num.natAbs : ℚ) (Nat.cast_ne_zero.mpr hnumAbs0)
  let uDen : ℚˣ := Units.mk0 ((a : ℚ).den : ℚ) (Nat.cast_ne_zero.mpr hden0)
  have huNum : uNum ∈ Subgroup.closure ratUnitsGen :=
    nat_unit_mem_closure_ratUnitsGen _ hnumAbs0
  have huDen : uDen ∈ Subgroup.closure ratUnitsGen :=
    nat_unit_mem_closure_ratUnitsGen _ hden0
  rcases lt_or_gt_of_ne hnum0 with hlt | hgt
  · have ha_eq : a = (-1 : ℚˣ) * uNum * uDen⁻¹ := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_neg, Units.val_one, Units.val_inv_eq_inv_val,
        uNum, uDen, Units.val_mk0]
      have habs : (((a : ℚ).num.natAbs : ℤ) : ℚ) = -((a : ℚ).num : ℚ) := by
        exact_mod_cast Int.ofNat_natAbs_of_nonpos (le_of_lt hlt)
      rw [← Int.cast_natCast, habs, neg_one_mul, neg_neg, ← div_eq_mul_inv, Rat.num_div_den]
    rw [ha_eq]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl)) huNum)
      (Subgroup.inv_mem _ huDen)
  · have ha_eq : a = uNum * uDen⁻¹ := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, uNum, uDen, Units.val_mk0]
      have habs : (((a : ℚ).num.natAbs : ℤ) : ℚ) = ((a : ℚ).num : ℚ) := by
        exact_mod_cast Int.natAbs_of_nonneg (le_of_lt hgt)
      rw [← Int.cast_natCast, habs, ← div_eq_mul_inv, Rat.num_div_den]
    rw [ha_eq]
    exact Subgroup.mul_mem _ huNum (Subgroup.inv_mem _ huDen)

/-- Helper: `padicValRat p q = 0` for distinct primes `p ≠ q`. -/
theorem padicValRat_prime_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    padicValRat p (q : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  have hnd : ¬ p ∣ q := fun hd => hpq ((hq.eq_one_or_self_of_dvd p hd).resolve_left hp.ne_one)
  rw [padicValNat.eq_zero_of_not_dvd hnd, Nat.cast_zero]

/-- Helper: `twoCoords (primeUnit 2 Nat.prime_two) = (1, 0, 0)`. -/
theorem twoCoords_two : twoCoords (primeUnit 2 Nat.prime_two) = (1, 0, 0) := by
  unfold twoCoords
  rw [pUnit_primeUnit, coe_primeUnit, padicValRat.self (by norm_num : 1 < 2), Units.val_one,
    redMod8_one, eps8_one, omega8_one]
  rfl

/-- Helper: `twoCoords (primeUnit q hq)` for odd prime `q`. -/
theorem twoCoords_oddPrime {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    twoCoords (primeUnit q hq) = (0, ((q / 2 : ℕ) : ZMod 2), omega8 (q : ZMod 8)) := by
  unfold twoCoords
  have hv : padicValRat 2 (primeUnit q hq : ℚ) = 0 := by
    rw [coe_primeUnit]
    exact padicValRat_prime_of_ne Nat.prime_two hq hq2.symm
  rw [pUnit_of_val_zero 2 Nat.prime_two hv, hv, Int.cast_zero, coe_primeUnit, redMod8_natCast,
    eps8_eq_div_two_nat (hq.mod_two_eq_one_iff_ne_two.mpr hq2)]

/-- Helper: `hilbertSymOdd q hq hq2 a (primeUnit q hq)` when `v_q(a) = 0`. -/
theorem hilbertSymOdd_of_val_zero_primeUnit {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {a : ℚˣ}
    (ha : padicValRat q (a : ℚ) = 0) :
    hilbertSymOdd q hq hq2 a (primeUnit q hq) = pUnitLegUnit q hq a := by
  rw [hilbertSymOdd_eq_negOnePow]
  have ha1 : (oddCoords q hq a).1 = 0 := by simp [oddCoords, ha]
  have hq1 : (oddCoords q hq (primeUnit q hq)).1 = 1 := by
    simp [oddCoords, coe_primeUnit, padicValRat.self hq.one_lt]
  have hq2' : (oddCoords q hq (primeUnit q hq)).2 = 0 := by
    change unitsToZMod2 (pUnitLegUnit q hq (primeUnit q hq)) = 0
    unfold pUnitLegUnit
    rw [pUnit_primeUnit, Units.val_one]
    have : Fact q.Prime := ⟨hq⟩
    rw [ratUnitLegendre_eq_quadraticChar hq one_ne_zero padicValRat.one, redModP_one, map_one,
      intToSignUnit_one, unitsToZMod2_one]
  rw [ha1, hq1, hq2']
  simp only [mul_zero, mul_one, zero_add, add_zero]
  exact negOnePowZMod2_unitsToZMod2 _

/-- Generator Pair 1: `hilbertProd (-1) (-1) = 1`. -/
theorem hilbertProd_neg_one_neg_one : hilbertProd (-1) (-1) = 1 := by
  unfold hilbertProd
  have hinf : hilbertSymInf (-1) (-1) = -1 := by simp [hilbertSymInf]
  have htwo : hilbertSymTwo (-1) (-1) = -1 := by
    unfold hilbertSymTwo
    rw [twoCoords_neg_one]
    decide
  have hodd : (∏ᶠ p : OddPrime, hilbertSymOdd p.1 p.2.1 p.2.2 (-1) (-1)) = 1 := by
    rw [finprod_eq_one_of_forall_eq_one]
    intro p
    exact hilbertSymOdd_eq_one_of_val_zero p.1 p.2.1 p.2.2 (by simp) (by simp)
  rw [hinf, htwo, hodd]
  decide

/-- Generator Pair 2: `hilbertProd (-1) 2 = 1`. -/
theorem hilbertProd_neg_one_two : hilbertProd (-1) (primeUnit 2 Nat.prime_two) = 1 := by
  unfold hilbertProd
  have hinf : hilbertSymInf (-1) (primeUnit 2 Nat.prime_two) = 1 := by
    simp [hilbertSymInf, primeUnit]
  have htwo : hilbertSymTwo (-1) (primeUnit 2 Nat.prime_two) = 1 := by
    unfold hilbertSymTwo
    rw [twoCoords_neg_one, twoCoords_two]
    decide
  have hodd : (∏ᶠ p : OddPrime, hilbertSymOdd p.1 p.2.1 p.2.2 (-1) (primeUnit 2 Nat.prime_two)) = 1 := by
    rw [finprod_eq_one_of_forall_eq_one]
    intro p
    exact hilbertSymOdd_eq_one_of_val_zero p.1 p.2.1 p.2.2 (by simp)
      (padicValRat_prime_of_ne p.2.1 Nat.prime_two p.2.2)
  rw [hinf, htwo, hodd]
  decide

/-- Generator Pair 3: `hilbertProd 2 2 = 1`. -/
theorem hilbertProd_two_two :
    hilbertProd (primeUnit 2 Nat.prime_two) (primeUnit 2 Nat.prime_two) = 1 := by
  unfold hilbertProd
  have hinf : hilbertSymInf (primeUnit 2 Nat.prime_two) (primeUnit 2 Nat.prime_two) = 1 := by
    simp [hilbertSymInf, primeUnit]
  have htwo : hilbertSymTwo (primeUnit 2 Nat.prime_two) (primeUnit 2 Nat.prime_two) = 1 := by
    unfold hilbertSymTwo
    rw [twoCoords_two]
    decide
  have hodd : (∏ᶠ p : OddPrime,
      hilbertSymOdd p.1 p.2.1 p.2.2 (primeUnit 2 Nat.prime_two) (primeUnit 2 Nat.prime_two)) = 1 := by
    rw [finprod_eq_one_of_forall_eq_one]
    intro p
    exact hilbertSymOdd_eq_one_of_val_zero p.1 p.2.1 p.2.2
      (padicValRat_prime_of_ne p.2.1 Nat.prime_two p.2.2)
      (padicValRat_prime_of_ne p.2.1 Nat.prime_two p.2.2)
  rw [hinf, htwo, hodd]
  decide

/-- Generator Pair 4: `hilbertProd (-1) q = 1` for every odd prime `q`, via `legendreSym.at_neg_one`. -/
theorem hilbertProd_neg_one_oddPrime {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    hilbertProd (-1) (primeUnit q hq) = 1 := by
  unfold hilbertProd
  have hinf : hilbertSymInf (-1) (primeUnit q hq) = 1 := by
    have hpos : (0 : ℚ) < (q : ℚ) := Nat.cast_pos.mpr hq.pos
    simp [hilbertSymInf, coe_primeUnit, not_lt.mpr hpos.le]
  have htwo : hilbertSymTwo (-1) (primeUnit q hq) = (-1 : ℤˣ) ^ (q / 2) := by
    unfold hilbertSymTwo
    rw [twoCoords_neg_one, twoCoords_oddPrime hq hq2]
    simp only [one_mul, zero_mul, add_zero]
    exact negOnePowZMod2_natCast (q / 2)
  let qO : OddPrime := ⟨q, hq, hq2⟩
  have hodd :
      (∏ᶠ p : OddPrime, hilbertSymOdd p.1 p.2.1 p.2.2 (-1) (primeUnit q hq)) =
        hilbertSymOdd q hq hq2 (-1) (primeUnit q hq) := by
    rw [finprod_eq_single _ qO]
    intro p hpq
    have hne : p.1 ≠ q := fun h => hpq (Subtype.ext h)
    exact hilbertSymOdd_eq_one_of_val_zero p.1 p.2.1 p.2.2 (by simp)
      (padicValRat_prime_of_ne p.2.1 hq hne)
  have hq_val : hilbertSymOdd q hq hq2 (-1) (primeUnit q hq) = (-1 : ℤˣ) ^ (q / 2) := by
    rw [hilbertSymOdd_of_val_zero_primeUnit hq hq2 (by simp), pUnitLegUnit_neg_one q hq hq2]
  rw [hinf, htwo, hodd, hq_val, one_mul, intUnits_mul_self]

/-- Generator Pair 5: `hilbertProd 2 q = 1` for every odd prime `q`, via `legendreSym.at_two`. -/
theorem hilbertProd_two_oddPrime {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    hilbertProd (primeUnit 2 Nat.prime_two) (primeUnit q hq) = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  unfold hilbertProd
  have hinf : hilbertSymInf (primeUnit 2 Nat.prime_two) (primeUnit q hq) = 1 := by
    have hpos : (0 : ℚ) < (q : ℚ) := Nat.cast_pos.mpr hq.pos
    simp [hilbertSymInf, coe_primeUnit, not_lt.mpr hpos.le]
  have htwo : hilbertSymTwo (primeUnit 2 Nat.prime_two) (primeUnit q hq) =
      negOnePowZMod2 (omega8 (q : ZMod 8)) := by
    unfold hilbertSymTwo
    rw [twoCoords_two, twoCoords_oddPrime hq hq2]
    simp
  let qO : OddPrime := ⟨q, hq, hq2⟩
  have hodd :
      (∏ᶠ p : OddPrime, hilbertSymOdd p.1 p.2.1 p.2.2 (primeUnit 2 Nat.prime_two) (primeUnit q hq)) =
        hilbertSymOdd q hq hq2 (primeUnit 2 Nat.prime_two) (primeUnit q hq) := by
    rw [finprod_eq_single _ qO]
    intro p hpq
    have hne : p.1 ≠ q := fun h => hpq (Subtype.ext h)
    exact hilbertSymOdd_eq_one_of_val_zero p.1 p.2.1 p.2.2
      (padicValRat_prime_of_ne p.2.1 Nat.prime_two p.2.2)
      (padicValRat_prime_of_ne p.2.1 hq hne)
  have hq_val :
      hilbertSymOdd q hq hq2 (primeUnit 2 Nat.prime_two) (primeUnit q hq) =
        negOnePowZMod2 (omega8 (q : ZMod 8)) := by
    have hv2 : padicValRat q (primeUnit 2 Nat.prime_two : ℚ) = 0 :=
      padicValRat_prime_of_ne hq Nat.prime_two hq2
    rw [hilbertSymOdd_of_val_zero_primeUnit hq hq2 hv2]
    apply Units.ext
    rw [coe_pUnitLegUnit, pUnit_of_val_zero q hq hv2, coe_primeUnit,
      omega8_eq_chi8_nat (hq.mod_two_eq_one_iff_ne_two.mpr hq2)]
    unfold ratUnitLegendre
    have hnum2 : (((2 : ℕ) : ℚ).num * (((2 : ℕ) : ℚ).den : ℤ)) = 2 := by norm_num
    rw [hnum2, legendreSym.at_two hq2]
  rw [hinf, htwo, hodd, hq_val, one_mul, intUnits_mul_self]

/-- Generator Pair 6a: `hilbertProd p p = 1` for every odd prime `p`. -/
theorem hilbertProd_oddPrime_self {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    hilbertProd (primeUnit p hp) (primeUnit p hp) = 1 := by
  unfold hilbertProd
  have hinf : hilbertSymInf (primeUnit p hp) (primeUnit p hp) = 1 := by
    have hpos : (0 : ℚ) < (p : ℚ) := Nat.cast_pos.mpr hp.pos
    simp [hilbertSymInf, coe_primeUnit, not_lt.mpr hpos.le]
  have htwo : hilbertSymTwo (primeUnit p hp) (primeUnit p hp) = (-1 : ℤˣ) ^ (p / 2) := by
    unfold hilbertSymTwo
    rw [twoCoords_oddPrime hp hp2]
    simp only [zero_mul, add_zero]
    have hsq : ∀ x : ZMod 2, x * x = x := by decide
    rw [hsq, negOnePowZMod2_natCast]
  let pO : OddPrime := ⟨p, hp, hp2⟩
  have hodd :
      (∏ᶠ r : OddPrime, hilbertSymOdd r.1 r.2.1 r.2.2 (primeUnit p hp) (primeUnit p hp)) =
        hilbertSymOdd p hp hp2 (primeUnit p hp) (primeUnit p hp) := by
    rw [finprod_eq_single _ pO]
    intro r hrp
    have hne : r.1 ≠ p := fun h => hrp (Subtype.ext h)
    exact hilbertSymOdd_eq_one_of_val_zero r.1 r.2.1 r.2.2
      (padicValRat_prime_of_ne r.2.1 hp hne)
      (padicValRat_prime_of_ne r.2.1 hp hne)
  have hp_val : hilbertSymOdd p hp hp2 (primeUnit p hp) (primeUnit p hp) = (-1 : ℤˣ) ^ (p / 2) := by
    rw [hilbertSymOdd_eq_negOnePow]
    have hp1 : (oddCoords p hp (primeUnit p hp)).1 = 1 := by
      simp [oddCoords, coe_primeUnit, padicValRat.self hp.one_lt]
    have hp2' : (oddCoords p hp (primeUnit p hp)).2 = 0 := by
      change unitsToZMod2 (pUnitLegUnit p hp (primeUnit p hp)) = 0
      unfold pUnitLegUnit
      rw [pUnit_primeUnit, Units.val_one]
      have : Fact p.Prime := ⟨hp⟩
      rw [ratUnitLegendre_eq_quadraticChar hp one_ne_zero padicValRat.one, redModP_one, map_one,
        intToSignUnit_one, unitsToZMod2_one]
    rw [hp1, hp2']
    simp only [mul_one, mul_zero, add_zero]
    exact negOnePowZMod2_natCast (p / 2)
  rw [hinf, htwo, hodd, hp_val, one_mul, intUnits_mul_self]

/-- Generator Pair 6b: `hilbertProd p q = 1` for distinct odd primes `p ≠ q`,
directly from Mathlib's `legendreSym.quadratic_reciprocity`! -/
theorem hilbertProd_oddPrime_ne {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    hilbertProd (primeUnit p hp) (primeUnit q hq) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  unfold hilbertProd
  have hinf : hilbertSymInf (primeUnit p hp) (primeUnit q hq) = 1 := by
    have hpos : (0 : ℚ) < (p : ℚ) := Nat.cast_pos.mpr hp.pos
    simp [hilbertSymInf, coe_primeUnit, not_lt.mpr hpos.le]
  have htwo : hilbertSymTwo (primeUnit p hp) (primeUnit q hq) =
      (-1 : ℤˣ) ^ (p / 2 * (q / 2)) := by
    unfold hilbertSymTwo
    rw [twoCoords_oddPrime hp hp2, twoCoords_oddPrime hq hq2]
    simp only [zero_mul, add_zero]
    rw [← Nat.cast_mul, negOnePowZMod2_natCast]
  let pO : OddPrime := ⟨p, hp, hp2⟩
  let qO : OddPrime := ⟨q, hq, hq2⟩
  have hpO_ne_qO : pO ≠ qO := fun h => hpq (congrArg Subtype.val h)
  have hsupp : (Function.mulSupport fun r : OddPrime =>
      hilbertSymOdd r.1 r.2.1 r.2.2 (primeUnit p hp) (primeUnit q hq)) ⊆
      ({pO, qO} : Finset OddPrime) := by
    intro r hr
    rw [Function.mem_mulSupport] at hr
    by_contra hnot
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    have hrp : r.1 ≠ p := fun h => hnot.1 (Subtype.ext h)
    have hrq : r.1 ≠ q := fun h => hnot.2 (Subtype.ext h)
    exact hr (hilbertSymOdd_eq_one_of_val_zero r.1 r.2.1 r.2.2
      (padicValRat_prime_of_ne r.2.1 hp hrp)
      (padicValRat_prime_of_ne r.2.1 hq hrq))
  have hodd :
      (∏ᶠ r : OddPrime, hilbertSymOdd r.1 r.2.1 r.2.2 (primeUnit p hp) (primeUnit q hq)) =
        hilbertSymOdd p hp hp2 (primeUnit p hp) (primeUnit q hq) *
          hilbertSymOdd q hq hq2 (primeUnit p hp) (primeUnit q hq) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsupp, Finset.prod_pair hpO_ne_qO]
  have hp_val : (hilbertSymOdd p hp hp2 (primeUnit p hp) (primeUnit q hq) : ℤ) = legendreSym p q := by
    rw [hilbertSymOdd_symm, hilbertSymOdd_of_val_zero_primeUnit hp hp2
      (padicValRat_prime_of_ne hp hq hpq), coe_pUnitLegUnit,
      pUnit_of_val_zero p hp (padicValRat_prime_of_ne hp hq hpq), coe_primeUnit]
    unfold ratUnitLegendre
    simp
  have hq_val : (hilbertSymOdd q hq hq2 (primeUnit p hp) (primeUnit q hq) : ℤ) = legendreSym q p := by
    rw [hilbertSymOdd_of_val_zero_primeUnit hq hq2 (padicValRat_prime_of_ne hq hp hpq.symm),
      coe_pUnitLegUnit, pUnit_of_val_zero q hq (padicValRat_prime_of_ne hq hp hpq.symm),
      coe_primeUnit]
    unfold ratUnitLegendre
    simp
  have hqr :
      hilbertSymOdd p hp hp2 (primeUnit p hp) (primeUnit q hq) *
        hilbertSymOdd q hq hq2 (primeUnit p hp) (primeUnit q hq) =
      (-1 : ℤˣ) ^ (p / 2 * (q / 2)) := by
    apply Units.ext
    rw [Units.val_mul, hp_val, hq_val, mul_comm,
      legendreSym.quadratic_reciprocity hp2 hq2 hpq, Units.val_pow_eq_pow_val]
    rfl
  rw [hinf, htwo, hodd, hqr, one_mul, intUnits_mul_self]

/-- Helper: `hilbertProd a b = 1` for all generator pairs `a, b ∈ ratUnitsGen`. -/
theorem hilbertProd_of_mem_gen {a b : ℚˣ} (ha : a ∈ ratUnitsGen) (hb : b ∈ ratUnitsGen) :
    hilbertProd a b = 1 := by
  rcases ha with rfl | ⟨p, hp, rfl⟩
  · rcases hb with rfl | ⟨q, hq, rfl⟩
    · exact hilbertProd_neg_one_neg_one
    · by_cases hq2 : q = 2
      · subst hq2; exact hilbertProd_neg_one_two
      · exact hilbertProd_neg_one_oddPrime hq hq2
  · rcases hb with rfl | ⟨q, hq, rfl⟩
    · rw [hilbertProd_symm]
      by_cases hp2 : p = 2
      · subst hp2; exact hilbertProd_neg_one_two
      · exact hilbertProd_neg_one_oddPrime hp hp2
    · by_cases hp2 : p = 2
      · subst hp2
        by_cases hq2 : q = 2
        · subst hq2; exact hilbertProd_two_two
        · exact hilbertProd_two_oddPrime hq hq2
      · by_cases hq2 : q = 2
        · subst hq2
          rw [hilbertProd_symm]
          exact hilbertProd_two_oddPrime hp hp2
        · by_cases hpq : p = q
          · subst hpq; exact hilbertProd_oddPrime_self hp hp2
          · exact hilbertProd_oddPrime_ne hp hp2 hq hq2 hpq

/-- **UNCONDITIONAL HILBERT-SYMBOL RECIPROCITY PRODUCT FORMULA OVER `ℚ`**:
for EVERY `a, b ∈ ℚˣ`,
`(a, b)_∞ * (a, b)_2 * ∏_{p odd prime} (a, b)_p = 1`! -/
theorem hilbert_reciprocity (a b : ℚˣ) :
    hilbertSymInf a b * hilbertSymTwo a b *
      ∏ᶠ p : {p : ℕ // p.Prime ∧ p ≠ 2}, hilbertSymOdd p.1 p.2.1 p.2.2 a b = 1 := by
  change hilbertProd a b = 1
  have hgen_right : ∀ x ∈ ratUnitsGen, ∀ y : ℚˣ, hilbertProd x y = 1 := by
    intro x hx y
    have hy : y ∈ Subgroup.closure ratUnitsGen := by
      rw [subgroup_closure_ratUnitsGen]; trivial
    refine Subgroup.closure_induction (p := fun y _ => hilbertProd x y = 1)
      (fun g hg => hilbertProd_of_mem_gen hx hg)
      (hilbertProd_one_right x)
      (fun u v _ _ hu hv => by rw [hilbertProd_mul_right, hu, hv, mul_one])
      (fun u _ hu => by rw [hilbertProd_inv_right, hu])
      hy
  have ha : a ∈ Subgroup.closure ratUnitsGen := by
    rw [subgroup_closure_ratUnitsGen]; trivial
  exact Subgroup.closure_induction (p := fun x _ => hilbertProd x b = 1)
    (fun g hg => hgen_right g hg b)
    (hilbertProd_one_left b)
    (fun u v _ _ hu hv => by rw [hilbertProd_mul_left, hu, hv, mul_one])
    (fun u _ hu => by rw [hilbertProd_inv_left, hu])
    ha

end HilbertReciprocity

/-! ## Section 4: Concrete Local Square-Class Spaces `ℚ_vˣ / (ℚ_vˣ)²` & `LocalDualityPairing (ZMod 2)` -/

section LocalDualityPairings

theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Any 2-torsion `AddCommGroup` carries a canonical `ZMod 2`-vector space structure. -/
@[instance_reducible]
def zmod2ModuleOfTwoTorsion {V : Type*} [AddCommGroup V] (h2 : ∀ x : V, x + x = 0) :
    Module (ZMod 2) V where
  smul c x := if c = 0 then 0 else x
  one_smul x := by
    change (if (1 : ZMod 2) = 0 then 0 else x) = x
    simp
  mul_smul c₁ c₂ x := by
    change (if c₁ * c₂ = 0 then 0 else x) =
      if c₁ = 0 then 0 else (if c₂ = 0 then 0 else x)
    rcases zmod2_eq_zero_or_one c₁ with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one c₂ with rfl | rfl <;> simp
  smul_zero c := by
    change (if c = 0 then (0 : V) else 0) = 0
    split_ifs <;> rfl
  smul_add c x y := by
    change (if c = 0 then (0 : V) else x + y) =
      (if c = 0 then 0 else x) + (if c = 0 then 0 else y)
    split_ifs <;> simp
  add_smul c₁ c₂ x := by
    change (if c₁ + c₂ = 0 then (0 : V) else x) =
      (if c₁ = 0 then 0 else x) + (if c₂ = 0 then 0 else x)
    rcases zmod2_eq_zero_or_one c₁ with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one c₂ with rfl | rfl
    · simp
    · simp
    · simp
    · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      simp [h11, h2 x]
  zero_smul x := by
    change (if (0 : ZMod 2) = 0 then (0 : V) else x) = 0
    simp

/-- Every `AddMonoidHom` between `ZMod 2`-vector spaces is automatically `ZMod 2`-linear. -/
def addMonoidHomToZMod2LinearMap {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] (f : V →+ W) : V →ₗ[ZMod 2] W where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    rcases zmod2_eq_zero_or_one c with rfl | rfl <;> simp

/-- Every `AddEquiv` between `ZMod 2`-vector spaces is automatically a `ZMod 2`-linear equivalence. -/
def addEquivToZMod2LinearEquiv {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] (e : V ≃+ W) : V ≃ₗ[ZMod 2] W where
  toAddEquiv := e
  map_smul' c x := by
    rcases zmod2_eq_zero_or_one c with rfl | rfl <;> simp

/-- Square-class group `G ⧸ G²` written additively as an `𝔽₂`-vector space. -/
abbrev SqQuot (G : Type*) [CommGroup G] : Type _ :=
  Additive (G ⧸ (powMonoidHom (α := G) 2).range)

/-- Canonical `ZMod 2`-module structure on `SqQuot G = Additive (G ⧸ G²)`. -/
instance instModuleZMod2SqQuot (G : Type*) [CommGroup G] : Module (ZMod 2) (SqQuot G) :=
  zmod2ModuleOfTwoTorsion (fun x => by
    change Additive.ofMul (Additive.toMul x * Additive.toMul x) = Additive.ofMul 1
    congr 1
    induction Additive.toMul x using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk (g * g) : G ⧸ (powMonoidHom (α := G) 2).range) = 1
      rw [QuotientGroup.eq_one_iff]
      exact ⟨g, sq g⟩)

/-- Helper: lift a group homomorphism `φ : G →* Multiplicative W` (where `W` is a `ZMod 2`-space)
whose kernel equals `G²` and which is surjective, to a `ZMod 2`-linear equivalence
`SqQuot G ≃ₗ[ZMod 2] W`. -/
def sqQuotEquivOfHom {G W : Type*} [CommGroup G] [AddCommGroup W] [Module (ZMod 2) W]
    (φ : G →* Multiplicative W) (hsurj : Function.Surjective φ)
    (hker : φ.ker = (powMonoidHom (α := G) 2).range) :
    SqQuot G ≃ₗ[ZMod 2] W :=
  let eMul : (G ⧸ (powMonoidHom (α := G) 2).range) ≃* Multiplicative W :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)
  addEquivToZMod2LinearEquiv (MulEquiv.toAdditive eMul)

/-- Transport a symmetric `LocalDualityPairing` along a linear equivalence `e : V ≃ₗ[k] W`. -/
def localDualityPairingCongr {k V W : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (e : V ≃ₗ[k] W) (P : LocalDualityPairing k W W) :
    LocalDualityPairing k V V where
  pair :=
    { toFun := fun x => (P.pair (e x)).comp e.toLinearMap
      map_add' := fun x₁ x₂ => by ext y; simp
      map_smul' := fun c x => by ext y; simp }
  left_nondeg := by
    intro x₁ x₂ h
    apply e.injective
    apply P.left_nondeg
    ext w
    have hv := LinearMap.congr_fun h (e.symm w)
    simpa using hv
  right_nondeg := by
    intro y₁ y₂ h
    apply e.injective
    apply P.right_nondeg
    ext w
    have hv := LinearMap.congr_fun h (e.symm w)
    simpa using hv

/-! ### 4A. Concrete Coordinate `LocalDualityPairing (ZMod 2)` at `∞`, Odd `p`, and `2` -/

/-- Nondegenerate local Tate / Hilbert pairing at `v = ∞` on `ZMod 2` (`dim = 1`). -/
def localPairingInf : LocalDualityPairing (ZMod 2) (ZMod 2) (ZMod 2) where
  pair :=
    { toFun := fun x =>
        { toFun := fun y => x * y
          map_add' := fun y₁ y₂ => mul_add x y₁ y₂
          map_smul' := fun c y => by simp [smul_eq_mul]; ring }
      map_add' := fun x₁ x₂ => by apply LinearMap.ext; intro y; exact add_mul x₁ x₂ y
      map_smul' := fun c x => by apply LinearMap.ext; intro y; simp [smul_eq_mul]; ring }
  left_nondeg := by
    intro x₁ x₂ h
    have h1 := LinearMap.congr_fun h 1
    simpa using h1
  right_nondeg := by
    intro y₁ y₂ h
    have h1 := LinearMap.congr_fun h 1
    simpa using h1

/-- Nondegenerate local Tate / Hilbert pairing at an odd prime `p` on `ZMod 2 × ZMod 2` (`dim = 2`). -/
def localPairingOdd (p : ℕ) (_hp : p.Prime) (_hp2 : p ≠ 2) :
    LocalDualityPairing (ZMod 2) (ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2) where
  pair :=
    { toFun := fun x =>
        { toFun := fun y => ((p / 2 : ℕ) : ZMod 2) * x.1 * y.1 + x.2 * y.1 + x.1 * y.2
          map_add' := fun y₁ y₂ => by simp only [Prod.fst_add, Prod.snd_add]; ring
          map_smul' := fun c y => by
            simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring }
      map_add' := fun x₁ x₂ => by
        apply LinearMap.ext; intro y
        change ((p / 2 : ℕ) : ZMod 2) * (x₁.1 + x₂.1) * y.1 + (x₁.2 + x₂.2) * y.1 +
            (x₁.1 + x₂.1) * y.2 =
          (((p / 2 : ℕ) : ZMod 2) * x₁.1 * y.1 + x₁.2 * y.1 + x₁.1 * y.2) +
          (((p / 2 : ℕ) : ZMod 2) * x₂.1 * y.1 + x₂.2 * y.1 + x₂.1 * y.2)
        ring
      map_smul' := fun c x => by
        apply LinearMap.ext; intro y
        change ((p / 2 : ℕ) : ZMod 2) * (c * x.1) * y.1 + (c * x.2) * y.1 + (c * x.1) * y.2 =
          c * (((p / 2 : ℕ) : ZMod 2) * x.1 * y.1 + x.2 * y.1 + x.1 * y.2)
        ring }
  left_nondeg := by
    intro x₁ x₂ h
    have h01 := LinearMap.congr_fun h (0, 1)
    have h10 := LinearMap.congr_fun h (1, 0)
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk] at h01 h10
    have hx1 : x₁.1 = x₂.1 := by simpa using h01
    have hx2 : x₁.2 = x₂.2 := by
      simp only [hx1, mul_one, mul_zero, add_zero] at h10
      exact add_left_cancel h10
    exact Prod.ext hx1 hx2
  right_nondeg := by
    intro y₁ y₂ h
    have h01 := LinearMap.congr_fun h (0, 1)
    have h10 := LinearMap.congr_fun h (1, 0)
    dsimp only [LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk] at h01 h10
    have hy1 : y₁.1 = y₂.1 := by simpa using h01
    have hy2 : y₁.2 = y₂.2 := by
      simp only [hy1, mul_one, one_mul, zero_mul, add_zero] at h10
      exact add_left_cancel h10
    exact Prod.ext hy1 hy2

/-- Nondegenerate local Tate / Hilbert pairing at `p = 2` on `ZMod 2 × ZMod 2 × ZMod 2` (`dim = 3`). -/
def localPairingTwo :
    LocalDualityPairing (ZMod 2) (ZMod 2 × ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2 × ZMod 2) where
  pair :=
    { toFun := fun x =>
        { toFun := fun y => x.2.1 * y.2.1 + x.1 * y.2.2 + y.1 * x.2.2
          map_add' := fun y₁ y₂ => by simp only [Prod.fst_add, Prod.snd_add]; ring
          map_smul' := fun c y => by
            simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring }
      map_add' := fun x₁ x₂ => by
        apply LinearMap.ext; intro y
        change (x₁.2.1 + x₂.2.1) * y.2.1 + (x₁.1 + x₂.1) * y.2.2 + y.1 * (x₁.2.2 + x₂.2.2) =
          (x₁.2.1 * y.2.1 + x₁.1 * y.2.2 + y.1 * x₁.2.2) +
          (x₂.2.1 * y.2.1 + x₂.1 * y.2.2 + y.1 * x₂.2.2)
        ring
      map_smul' := fun c x => by
        apply LinearMap.ext; intro y
        change (c * x.2.1) * y.2.1 + (c * x.1) * y.2.2 + y.1 * (c * x.2.2) =
          c * (x.2.1 * y.2.1 + x.1 * y.2.2 + y.1 * x.2.2)
        ring }
  left_nondeg := by
    intro x₁ x₂ h
    have h001 := LinearMap.congr_fun h (0, 0, 1)
    have h010 := LinearMap.congr_fun h (0, 1, 0)
    have h100 := LinearMap.congr_fun h (1, 0, 0)
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk] at h001 h010 h100
    exact Prod.ext (by simpa using h001) (Prod.ext (by simpa using h010) (by simpa using h100))
  right_nondeg := by
    intro y₁ y₂ h
    have h001 := LinearMap.congr_fun h (0, 0, 1)
    have h010 := LinearMap.congr_fun h (0, 1, 0)
    have h100 := LinearMap.congr_fun h (1, 0, 0)
    dsimp only [LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk] at h001 h010 h100
    exact Prod.ext (by simpa using h001) (Prod.ext (by simpa using h010) (by simpa using h100))

/-! ### 4B. Actual Local Field Square-Class Isomorphisms `ℚ_vˣ / (ℚ_vˣ)²` (`dim 1, 2, 3`) -/

/-- Sign homomorphism `ℝˣ →* Multiplicative (ZMod 2)`. -/
def realSignHom : ℝˣ →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (if (x : ℝ) < 0 then (1 : ZMod 2) else 0)
  map_one' := by simp
  map_mul' x y := by
    change Multiplicative.ofAdd (if (x : ℝ) * (y : ℝ) < 0 then (1 : ZMod 2) else 0) =
      Multiplicative.ofAdd ((if (x : ℝ) < 0 then (1 : ZMod 2) else 0) +
        (if (y : ℝ) < 0 then (1 : ZMod 2) else 0))
    congr 1
    rcases lt_or_gt_of_ne x.ne_zero with hx | hx <;>
      rcases lt_or_gt_of_ne y.ne_zero with hy | hy
    · have h : 0 < (x : ℝ) * (y : ℝ) := mul_pos_of_neg_of_neg hx hy
      simp [hx, hy, not_lt.mpr h.le]; decide
    · have h : (x : ℝ) * (y : ℝ) < 0 := mul_neg_of_neg_of_pos hx hy
      simp [hx, not_lt.mpr hy.le, h]
    · have h : (x : ℝ) * (y : ℝ) < 0 := mul_neg_of_pos_of_neg hx hy
      simp [not_lt.mpr hx.le, hy, h]
    · have h : 0 < (x : ℝ) * (y : ℝ) := mul_pos hx hy
      simp [not_lt.mpr hx.le, not_lt.mpr hy.le, not_lt.mpr h.le]

/-- **Actual Archimedean Square-Class Isomorphism**: `ℝˣ ⧸ (ℝˣ)² ≃ₗ[ZMod 2] ZMod 2` (`dim = 1`). -/
def realSqQuotEquiv : SqQuot ℝˣ ≃ₗ[ZMod 2] ZMod 2 :=
  sqQuotEquivOfHom realSignHom
    (by
      intro y
      rcases zmod2_eq_zero_or_one (Multiplicative.toAdd y) with hy | hy
      · refine ⟨1, ?_⟩
        apply Multiplicative.toAdd.injective
        simpa [realSignHom, show ¬ ((1 : ℝ) < 0) by norm_num] using hy.symm
      · refine ⟨-1, ?_⟩
        apply Multiplicative.toAdd.injective
        simpa [realSignHom, show ((-1 : ℝ) < 0) by norm_num] using hy.symm)
    (by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_range]
      constructor
      · intro hx
        have hpos : ¬ (x : ℝ) < 0 := by
          intro hlt
          have h1 : (if (x : ℝ) < 0 then (1 : ZMod 2) else 0) = 0 := by
            simpa [realSignHom] using congrArg Multiplicative.toAdd hx
          rw [if_pos hlt] at h1
          exact (by decide : (1 : ZMod 2) ≠ 0) h1
        have hgt : 0 < (x : ℝ) := lt_of_le_of_ne (not_lt.mp hpos) x.ne_zero.symm
        let y : ℝˣ := Units.mk0 (Real.sqrt (x : ℝ)) (Real.sqrt_ne_zero'.mpr hgt)
        refine ⟨y, Units.ext ?_⟩
        change (Real.sqrt (x : ℝ)) ^ 2 = (x : ℝ)
        exact Real.sq_sqrt hgt.le
      · rintro ⟨y, rfl⟩
        change realSignHom (y ^ 2) = 1
        rw [sq, map_mul]
        apply Multiplicative.toAdd.injective
        change Multiplicative.toAdd (realSignHom y) + Multiplicative.toAdd (realSignHom y) = 0
        have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
        exact h2 _)

instance instFiniteDimensionalRealSqQuot : FiniteDimensional (ZMod 2) (SqQuot ℝˣ) :=
  realSqQuotEquiv.symm.finiteDimensional

/-- Exact dimension `dim_{𝔽₂}(ℝˣ / (ℝˣ)²) = 1`. -/
theorem finrank_realSqQuot : Module.finrank (ZMod 2) (SqQuot ℝˣ) = 1 := by
  rw [realSqQuotEquiv.finrank_eq, Module.finrank_self]

/-- **Concrete `LocalDualityPairing (ZMod 2)` on `ℝˣ / (ℝˣ)²`**! -/
def realLocalDualityPairing : LocalDualityPairing (ZMod 2) (SqQuot ℝˣ) (SqQuot ℝˣ) :=
  localDualityPairingCongr realSqQuotEquiv localPairingInf

/-! #### Hensel Square-Class Isomorphisms for `ℚ_[p]ˣ` (Odd `p` and `p = 2`) -/

/-- Helper: extract the `p`-adic integer unit part of `x : ℚ_[p]ˣ`: `u = x * p^(-v_p(x)) ∈ ℤ_[p]ˣ`. -/
def padicUnitPart {p : ℕ} [Fact p.Prime] (x : ℚ_[p]ˣ) : ℤ_[p]ˣ :=
  let v : ℤ := Padic.valuation (x : ℚ_[p])
  let uQ : ℚ_[p] := (x : ℚ_[p]) * (p : ℚ_[p]) ^ (-v)
  have huNorm : ‖uQ‖ = 1 := by
    have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
    dsimp only [uQ]
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation x.ne_zero, Padic.norm_p_zpow, neg_neg,
      ← zpow_add₀ hp_pos.ne', neg_add_cancel, zpow_zero]
  let uZ : ℤ_[p] := ⟨uQ, le_of_eq huNorm⟩
  have huNormZ : ‖uZ‖ = 1 := huNorm
  (PadicInt.isUnit_iff.mpr huNormZ).unit

theorem coe_padicUnitPart {p : ℕ} [Fact p.Prime] (x : ℚ_[p]ˣ) :
    ((padicUnitPart x : ℤ_[p]) : ℚ_[p]) = (x : ℚ_[p]) * (p : ℚ_[p]) ^ (-Padic.valuation (x : ℚ_[p])) := by
  unfold padicUnitPart
  rfl

theorem padicUnitPart_mul {p : ℕ} [Fact p.Prime] (x y : ℚ_[p]ˣ) :
    padicUnitPart (x * y) = padicUnitPart x * padicUnitPart y := by
  apply Units.ext
  apply Subtype.ext
  change ((padicUnitPart (x * y) : ℤ_[p]) : ℚ_[p]) =
    ((padicUnitPart x : ℤ_[p]) : ℚ_[p]) * ((padicUnitPart y : ℤ_[p]) : ℚ_[p])
  rw [coe_padicUnitPart, coe_padicUnitPart, coe_padicUnitPart, Units.val_mul,
    Padic.valuation_mul x.ne_zero y.ne_zero, neg_add,
    zpow_add₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]
  ring

theorem padicUnitPart_one {p : ℕ} [Fact p.Prime] : padicUnitPart (1 : ℚ_[p]ˣ) = 1 := by
  apply Units.ext
  apply Subtype.ext
  change ((padicUnitPart (1 : ℚ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = 1
  rw [coe_padicUnitPart, Units.val_one]
  simp

theorem padic_eq_p_zpow_mul_unitPart {p : ℕ} [Fact p.Prime] (x : ℚ_[p]ˣ) :
    (x : ℚ_[p]) = (p : ℚ_[p]) ^ (Padic.valuation (x : ℚ_[p])) * ((padicUnitPart x : ℤ_[p]) : ℚ_[p]) := by
  rw [coe_padicUnitPart, mul_comm ((p : ℚ_[p]) ^ _), mul_assoc,
    ← zpow_add₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero), neg_add_cancel, zpow_zero,
    mul_one]

/-- Helper: `PadicInt.toZMod u ≠ 0` for every unit `u : ℤ_[p]ˣ`. -/
theorem toZMod_padicIntUnit_ne_zero {p : ℕ} [Fact p.Prime] (u : ℤ_[p]ˣ) :
    PadicInt.toZMod (u : ℤ_[p]) ≠ 0 := by
  intro h0
  have hmem : (u : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := h0
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal] at hmem
  exact hmem u.isUnit

/-- Local coordinate homomorphism `ℚ_[p]ˣ →* Multiplicative (ZMod 2 × ZMod 2)` at odd prime `p`. -/
def padicOddCoordHom (p : ℕ) [Fact p.Prime] :
    ℚ_[p]ˣ →* Multiplicative (ZMod 2 × ZMod 2) where
  toFun x :=
    Multiplicative.ofAdd
      ((Padic.valuation (x : ℚ_[p]) : ZMod 2),
        unitsToZMod2 (intToSignUnit (quadraticChar (ZMod p) (PadicInt.toZMod (padicUnitPart x : ℤ_[p])))))
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext
    · simp
    · change unitsToZMod2 (intToSignUnit (quadraticChar (ZMod p)
        (PadicInt.toZMod (padicUnitPart (1 : ℚ_[p]ˣ) : ℤ_[p])))) = 0
      rw [padicUnitPart_one]
      simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    ext
    · change (Padic.valuation ((x * y : ℚ_[p]ˣ) : ℚ_[p]) : ZMod 2) =
        (Padic.valuation (x : ℚ_[p]) : ZMod 2) + (Padic.valuation (y : ℚ_[p]) : ZMod 2)
      rw [Units.val_mul, Padic.valuation_mul x.ne_zero y.ne_zero, Int.cast_add]
    · change unitsToZMod2 (intToSignUnit (quadraticChar (ZMod p)
          (PadicInt.toZMod (padicUnitPart (x * y) : ℤ_[p])))) =
        unitsToZMod2 (intToSignUnit (quadraticChar (ZMod p)
          (PadicInt.toZMod (padicUnitPart x : ℤ_[p])))) +
        unitsToZMod2 (intToSignUnit (quadraticChar (ZMod p)
          (PadicInt.toZMod (padicUnitPart y : ℤ_[p]))))
      rw [padicUnitPart_mul, Units.val_mul, map_mul, map_mul,
        intToSignUnit_mul
          (quadraticChar_dichotomy (toZMod_padicIntUnit_ne_zero (padicUnitPart x)))
          (quadraticChar_dichotomy (toZMod_padicIntUnit_ne_zero (padicUnitPart y))),
        unitsToZMod2_mul]

/-- **Hensel Square Criterion at Odd Prime `p`**: a `p`-adic unit `u : ℤ_[p]ˣ` whose reduction mod `p`
is a square in `ZMod p` is a square in `ℤ_[p]`. -/
theorem exists_sq_padicInt_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (u : ℤ_[p]ˣ)
    (hsq : IsSquare (PadicInt.toZMod (u : ℤ_[p]))) :
    ∃ z : ℤ_[p], z ^ 2 = (u : ℤ_[p]) := by
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact toZMod_padicIntUnit_ne_zero u hr
  let a : ℤ_[p] := (r.val : ℤ_[p])
  have ha_mod : PadicInt.toZMod a = r := by
    simp [a]
  have ha_unit : IsUnit a := by
    by_contra hnu
    have hmem : a ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
      exact hnu
    exact hr0 (ha_mod ▸ hmem)
  have h2_unit : IsUnit (2 : ℤ_[p]) := by
    by_contra hnu
    have hmem : (2 : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
      exact hnu
    have h20 : (2 : ZMod p) = 0 := by
      change PadicInt.toZMod (2 : ℤ_[p]) = 0 at hmem
      rwa [map_ofNat] at hmem
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h20)
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact hp2 (le_antisymm hle hge)
  let F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[p])
  have hF_eval : Polynomial.aeval a F = a ^ 2 - (u : ℤ_[p]) := by simp [F]
  have hF_deriv : Polynomial.aeval a (Polynomial.derivative F) = 2 * a := by
    simp [F, Polynomial.derivative_sub, Polynomial.derivative_pow, Polynomial.derivative_C]
  have hderiv_norm : ‖Polynomial.aeval a (Polynomial.derivative F)‖ = 1 := by
    rw [hF_deriv, norm_mul, PadicInt.isUnit_iff.mp h2_unit, PadicInt.isUnit_iff.mp ha_unit, mul_one]
  have heval_lt : ‖Polynomial.aeval a F‖ < 1 := by
    rw [← PadicInt.not_isUnit_iff]
    intro huF
    have hker : Polynomial.aeval a F ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      change PadicInt.toZMod (Polynomial.aeval a F) = 0
      rw [hF_eval, map_sub, map_pow, ha_mod, hr, sq, sub_self]
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal] at hker
    exact hker huF
  have hnorm : ‖Polynomial.aeval a F‖ < ‖Polynomial.aeval a (Polynomial.derivative F)‖ ^ 2 := by
    rw [hderiv_norm, one_pow]
    exact heval_lt
  obtain ⟨z, hz, _⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  have hz' : z ^ 2 - (u : ℤ_[p]) = 0 := by simpa [F] using hz
  exact sub_eq_zero.mp hz'

/-- **Actual Odd-Prime `p`-adic Square-Class Isomorphism**:
`ℚ_[p]ˣ ⧸ (ℚ_[p]ˣ)² ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2)` (`dim = 2`), via Hensel's Lemma! -/
def padicSqQuotEquivOdd (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    SqQuot ℚ_[p]ˣ ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
  sqQuotEquivOfHom (padicOddCoordHom p)
    (by
      have hp : p.Prime := Fact.out
      have hrc : ringChar (ZMod p) ≠ 2 := (ZMod.ringChar_zmod_n p).substr hp2
      obtain ⟨r, hr⟩ := quadraticChar_exists_neg_one hrc
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [quadraticChar_zero] at hr
        norm_num at hr
      let uZ : ℤ_[p] := (r.val : ℤ_[p])
      have huZ_mod : PadicInt.toZMod uZ = r := by simp [uZ]
      have huZ_unit : IsUnit uZ := by
        by_contra hnu
        have hmem : uZ ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
          rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]; exact hnu
        exact hr0 (huZ_mod ▸ hmem)
      let g2 : ℚ_[p]ˣ := Units.mk0 (uZ : ℚ_[p]) (by
        intro h0
        have : uZ = 0 := Subtype.ext h0
        exact huZ_unit.ne_zero this)
      have hg2_val : Padic.valuation (g2 : ℚ_[p]) = 0 := by
        have hnorm : ‖(g2 : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.mp huZ_unit
        have h1 := Padic.norm_eq_zpow_neg_valuation g2.ne_zero
        rw [hnorm] at h1
        have hp_gt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
        by_contra hne
        have hlt_or_gt : (Padic.valuation (g2 : ℚ_[p]) < 0) ∨ (0 < Padic.valuation (g2 : ℚ_[p])) :=
          lt_or_gt_of_ne hne
        rcases hlt_or_gt with hlt | hgt
        · have : (1 : ℝ) < (p : ℝ) ^ (-Padic.valuation (g2 : ℚ_[p])) :=
            one_lt_zpow₀ hp_gt (by omega)
          linarith
        · have : (p : ℝ) ^ (-Padic.valuation (g2 : ℚ_[p])) < 1 :=
            zpow_lt_one_of_neg₀ hp_gt (by omega)
          linarith
      have hg2_map : padicOddCoordHom p g2 = Multiplicative.ofAdd ((0 : ZMod 2), (1 : ZMod 2)) := by
        apply Multiplicative.toAdd.injective
        ext
        · change (Padic.valuation (g2 : ℚ_[p]) : ZMod 2) = 0
          rw [hg2_val, Int.cast_zero]
        · change unitsToZMod2 (intToSignUnit (quadraticChar (ZMod p)
              (PadicInt.toZMod (padicUnitPart g2 : ℤ_[p])))) = 1
          have hup : (padicUnitPart g2 : ℤ_[p]) = uZ := by
            apply Subtype.ext
            rw [coe_padicUnitPart, hg2_val, neg_zero, zpow_zero, mul_one]
            rfl
          rw [hup, huZ_mod, hr, intToSignUnit_neg_one, unitsToZMod2_neg_one]
      let g1 : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr hp.ne_zero)
      have hg1_val : Padic.valuation (g1 : ℚ_[p]) = 1 := by
        change Padic.valuation (p : ℚ_[p]) = 1
        rw [Padic.valuation_natCast, padicValNat.self hp.one_lt, Nat.cast_one]
      have hg1_map : padicOddCoordHom p g1 = Multiplicative.ofAdd ((1 : ZMod 2), (0 : ZMod 2)) := by
        apply Multiplicative.toAdd.injective
        ext
        · change (Padic.valuation (g1 : ℚ_[p]) : ZMod 2) = 1
          rw [hg1_val, Int.cast_one]
        · change unitsToZMod2 (intToSignUnit (quadraticChar (ZMod p)
              (PadicInt.toZMod (padicUnitPart g1 : ℤ_[p])))) = 0
          have hup : (padicUnitPart g1 : ℤ_[p]) = 1 := by
            apply Subtype.ext
            rw [coe_padicUnitPart, hg1_val]
            change (p : ℚ_[p]) * (p : ℚ_[p]) ^ (-1 : ℤ) = 1
            rw [zpow_neg_one, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hp.ne_zero)]
          rw [hup, map_one, map_one, intToSignUnit_one, unitsToZMod2_one]
      intro y
      rcases zmod2_eq_zero_or_one (Multiplicative.toAdd y).1 with h1 | h1 <;>
        rcases zmod2_eq_zero_or_one (Multiplicative.toAdd y).2 with h2 | h2
      · refine ⟨1, ?_⟩; apply Multiplicative.toAdd.injective
        exact Prod.ext (by simpa using h1.symm) (by simpa using h2.symm)
      · refine ⟨g2, ?_⟩; apply Multiplicative.toAdd.injective
        rw [hg2_map]; exact Prod.ext (by simpa using h1.symm) (by simpa using h2.symm)
      · refine ⟨g1, ?_⟩; apply Multiplicative.toAdd.injective
        rw [hg1_map]; exact Prod.ext (by simpa using h1.symm) (by simpa using h2.symm)
      · refine ⟨g1 * g2, ?_⟩; apply Multiplicative.toAdd.injective
        rw [map_mul, hg1_map, hg2_map]
        exact Prod.ext (by simpa using h1.symm) (by simpa using h2.symm))
    (by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_range]
      constructor
      · intro hx
        have hpair := congrArg Multiplicative.toAdd hx
        have hv0 : (Padic.valuation (x : ℚ_[p]) : ZMod 2) = 0 := congrArg Prod.fst hpair
        have hu0 : unitsToZMod2 (intToSignUnit (quadraticChar (ZMod p)
            (PadicInt.toZMod (padicUnitPart x : ℤ_[p])))) = 0 := congrArg Prod.snd hpair
        obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hv0
        have hq1 : quadraticChar (ZMod p) (PadicInt.toZMod (padicUnitPart x : ℤ_[p])) = 1 := by
          have hsu : intToSignUnit (quadraticChar (ZMod p)
              (PadicInt.toZMod (padicUnitPart x : ℤ_[p]))) = 1 :=
            (unitsToZMod2_eq_zero_iff _).mp hu0
          have hcoe := coe_intToSignUnit
            (quadraticChar_dichotomy (toZMod_padicIntUnit_ne_zero (padicUnitPart x)))
          rw [hsu, Units.val_one] at hcoe
          exact hcoe.symm
        have hsq_mod : IsSquare (PadicInt.toZMod (padicUnitPart x : ℤ_[p])) :=
          (quadraticChar_one_iff_isSquare
            (toZMod_padicIntUnit_ne_zero (padicUnitPart x))).mp hq1
        obtain ⟨z, hz⟩ := exists_sq_padicInt_odd hp2 (padicUnitPart x) hsq_mod
        have hz0 : (z : ℚ_[p]) ≠ 0 := by
          intro h0
          have hz_zero : z = 0 := Subtype.ext h0
          rw [hz_zero, zero_pow two_ne_zero] at hz
          exact (padicUnitPart x).ne_zero hz.symm
        have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
        let yQ : ℚ_[p] := (p : ℚ_[p]) ^ k * (z : ℚ_[p])
        let y : ℚ_[p]ˣ := Units.mk0 yQ (mul_ne_zero (zpow_ne_zero k hp_ne) hz0)
        refine ⟨y, Units.ext ?_⟩
        change yQ ^ 2 = (x : ℚ_[p])
        dsimp only [yQ]
        have hk' : Padic.valuation (x : ℚ_[p]) = k * ((2 : ℕ) : ℤ) := by rw [hk]; ring
        rw [mul_pow, ← zpow_natCast ((p : ℚ_[p]) ^ k), ← zpow_mul, ← hk']
        have hzQ : (z : ℚ_[p]) ^ 2 = ((padicUnitPart x : ℤ_[p]) : ℚ_[p]) := by
          rw [← PadicInt.coe_pow, hz]
        rw [hzQ, ← padic_eq_p_zpow_mul_unitPart x]
      · rintro ⟨y, rfl⟩
        change padicOddCoordHom p (y ^ 2) = 1
        rw [sq, map_mul]
        apply Multiplicative.toAdd.injective
        change Multiplicative.toAdd (padicOddCoordHom p y) +
          Multiplicative.toAdd (padicOddCoordHom p y) = 0
        have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
        exact Prod.ext (h2 _) (h2 _))

/-- Exact dimension `dim_{𝔽₂}(ℚ_[p]ˣ / (ℚ_[p]ˣ)²) = 2` for every odd prime `p`. -/
theorem finrank_padicSqQuotOdd (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    Module.finrank (ZMod 2) (SqQuot ℚ_[p]ˣ) = 2 := by
  rw [(padicSqQuotEquivOdd p hp2).finrank_eq, Module.finrank_prod, Module.finrank_self]

/-- Helper: `PadicInt.toZModPow 3 u` is odd in `ZMod 8` for every `u : ℤ_[2]ˣ`. -/
theorem toZModPow3_padicIntUnit_odd (u : ℤ_[2]ˣ) :
    (PadicInt.toZModPow 3 (u : ℤ_[2])).val % 2 = 1 := by
  have hcast : ZMod.cast (PadicInt.toZModPow 3 (u : ℤ_[2])) = PadicInt.toZModPow 1 (u : ℤ_[2]) :=
    PadicInt.cast_toZModPow 1 3 (by norm_num) (u : ℤ_[2])
  have hmod1 : (PadicInt.toZModPow 1 (u : ℤ_[2]) : ZMod (2 ^ 1)) ≠ 0 := by
    intro h0
    have hker : (u : ℤ_[2]) ∈ RingHom.ker (PadicInt.toZModPow 1) := h0
    rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
      IsLocalRing.mem_maximalIdeal] at hker
    exact hker u.isUnit
  have hmod8 : (PadicInt.toZModPow 3 (u : ℤ_[2])).val % 2 ≠ 0 := by
    intro heven
    apply hmod1
    rw [← hcast]
    have hcast_eq : (ZMod.cast (PadicInt.toZModPow 3 (u : ℤ_[2])) : ZMod (2 ^ 1)) =
        (((PadicInt.toZModPow 3 (u : ℤ_[2])).val : ℕ) : ZMod (2 ^ 1)) := by
      rw [ZMod.cast_eq_val]
    rw [hcast_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero (by simpa using heven)
  omega

/-- Local coordinate homomorphism `ℚ_[2]ˣ →* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)`. -/
def padicTwoCoordHom : ℚ_[2]ˣ →* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2) where
  toFun x :=
    let u8 : ZMod 8 := PadicInt.toZModPow 3 (padicUnitPart x : ℤ_[2])
    Multiplicative.ofAdd ((Padic.valuation (x : ℚ_[2]) : ZMod 2), eps8 u8, omega8 u8)
  map_one' := by
    apply Multiplicative.toAdd.injective
    refine Prod.ext (by simp) (Prod.ext ?_ ?_)
    · change eps8 (PadicInt.toZModPow 3 (padicUnitPart (1 : ℚ_[2]ˣ) : ℤ_[2])) = 0
      rw [padicUnitPart_one]; simp
    · change omega8 (PadicInt.toZModPow 3 (padicUnitPart (1 : ℚ_[2]ˣ) : ℤ_[2])) = 0
      rw [padicUnitPart_one]; simp
  map_mul' x y := by
    have hx := toZModPow3_padicIntUnit_odd (padicUnitPart x)
    have hy := toZModPow3_padicIntUnit_odd (padicUnitPart y)
    apply Multiplicative.toAdd.injective
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · change (Padic.valuation ((x * y : ℚ_[2]ˣ) : ℚ_[2]) : ZMod 2) =
        (Padic.valuation (x : ℚ_[2]) : ZMod 2) + (Padic.valuation (y : ℚ_[2]) : ZMod 2)
      rw [Units.val_mul, Padic.valuation_mul x.ne_zero y.ne_zero, Int.cast_add]
    · change eps8 (PadicInt.toZModPow 3 (padicUnitPart (x * y) : ℤ_[2])) =
        eps8 (PadicInt.toZModPow 3 (padicUnitPart x : ℤ_[2])) +
        eps8 (PadicInt.toZModPow 3 (padicUnitPart y : ℤ_[2]))
      rw [padicUnitPart_mul, Units.val_mul, map_mul]
      exact eps8_mul hx hy
    · change omega8 (PadicInt.toZModPow 3 (padicUnitPart (x * y) : ℤ_[2])) =
        omega8 (PadicInt.toZModPow 3 (padicUnitPart x : ℤ_[2])) +
        omega8 (PadicInt.toZModPow 3 (padicUnitPart y : ℤ_[2]))
      rw [padicUnitPart_mul, Units.val_mul, map_mul]
      exact omega8_mul hx hy

/-- **Hensel Square Criterion at `p = 2`**: a `2`-adic unit `u : ℤ_[2]ˣ` with `u ≡ 1 (mod 8)`
is a square in `ℤ_[2]`. -/
theorem exists_sq_padicInt_two (u : ℤ_[2]ˣ)
    (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) = 1) :
    ∃ z : ℤ_[2], z ^ 2 = (u : ℤ_[2]) := by
  let F : Polynomial ℤ_[2] := Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[2])
  have hF_eval : Polynomial.aeval (1 : ℤ_[2]) F = 1 - (u : ℤ_[2]) := by simp [F]
  have hF_deriv : Polynomial.aeval (1 : ℤ_[2]) (Polynomial.derivative F) = 2 := by
    simp [F, Polynomial.derivative_sub, Polynomial.derivative_pow, Polynomial.derivative_C]
  have hderiv_norm : ‖Polynomial.aeval (1 : ℤ_[2]) (Polynomial.derivative F)‖ = (2 : ℝ)⁻¹ := by
    rw [hF_deriv]
    exact PadicInt.norm_p (p := 2)
  have hmem : 1 - (u : ℤ_[2]) ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ 3} := by
    rw [← PadicInt.ker_toZModPow 3]
    change PadicInt.toZModPow 3 (1 - (u : ℤ_[2])) = 0
    rw [map_sub, map_one, hu, sub_self]
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have heval_le : ‖Polynomial.aeval (1 : ℤ_[2]) F‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
    rw [hF_eval, hc, norm_mul, PadicInt.norm_p_pow (p := 2) 3]
    have hc_le : ‖c‖ ≤ 1 := PadicInt.norm_le_one c
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (-3 : ℤ) := by positivity
    calc (2 : ℝ) ^ (-3 : ℤ) * ‖c‖ ≤ (2 : ℝ) ^ (-3 : ℤ) * 1 :=
          mul_le_mul_of_nonneg_left hc_le hpos
      _ = (2 : ℝ) ^ (-3 : ℤ) := mul_one _
  have hnorm : ‖Polynomial.aeval (1 : ℤ_[2]) F‖ <
      ‖Polynomial.aeval (1 : ℤ_[2]) (Polynomial.derivative F)‖ ^ 2 := by
    rw [hderiv_norm]
    have hlt : (2 : ℝ) ^ (-3 : ℤ) < ((2 : ℝ)⁻¹) ^ 2 := by norm_num
    exact lt_of_le_of_lt heval_le hlt
  obtain ⟨z, hz, _⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  have hz' : z ^ 2 - (u : ℤ_[2]) = 0 := by simpa [F] using hz
  exact sub_eq_zero.mp hz'

/-- **Actual Dyadic `2`-adic Square-Class Isomorphism**:
`ℚ_[2]ˣ ⧸ (ℚ_[2]ˣ)² ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2 × ZMod 2)` (`dim = 3`), via Hensel's Lemma! -/
def padicSqQuotEquivTwo : SqQuot ℚ_[2]ˣ ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2 × ZMod 2) :=
  sqQuotEquivOfHom padicTwoCoordHom
    (by
      let g1 : ℚ_[2]ˣ := Units.mk0 (2 : ℚ_[2]) (by norm_num)
      let g2 : ℚ_[2]ˣ := -1
      let g3 : ℚ_[2]ˣ := Units.mk0 (5 : ℚ_[2]) (by norm_num)
      have hg1_val : Padic.valuation (g1 : ℚ_[2]) = 1 := by
        change Padic.valuation (2 : ℚ_[2]) = 1
        rw [Padic.valuation_ofNat, padicValNat.self (by norm_num), Nat.cast_one]
      have hg1 : padicTwoCoordHom g1 = Multiplicative.ofAdd ((1 : ZMod 2), (0 : ZMod 2), (0 : ZMod 2)) := by
        apply Multiplicative.toAdd.injective
        have hup : (padicUnitPart g1 : ℤ_[2]) = 1 := by
          apply Subtype.ext
          rw [coe_padicUnitPart, hg1_val]
          change (2 : ℚ_[2]) * (2 : ℚ_[2]) ^ (-1 : ℤ) = 1
          rw [zpow_neg_one, mul_inv_cancel₀ (by norm_num)]
        refine Prod.ext (by change (Padic.valuation (g1 : ℚ_[2]) : ZMod 2) = 1; rw [hg1_val]; simp)
          (Prod.ext
            (by change eps8 (PadicInt.toZModPow 3 (padicUnitPart g1 : ℤ_[2])) = 0; rw [hup]; simp)
            (by change omega8 (PadicInt.toZModPow 3 (padicUnitPart g1 : ℤ_[2])) = 0; rw [hup]; simp))
      have hg2_val : Padic.valuation (g2 : ℚ_[2]) = 0 := by
        change Padic.valuation (-1 : ℚ_[2]) = 0
        rw [← Int.cast_one, ← Int.cast_neg, Padic.valuation_intCast]
        simp
      have hg2 : padicTwoCoordHom g2 = Multiplicative.ofAdd ((0 : ZMod 2), (1 : ZMod 2), (0 : ZMod 2)) := by
        apply Multiplicative.toAdd.injective
        have hup : (padicUnitPart g2 : ℤ_[2]) = -1 := by
          apply Subtype.ext
          rw [coe_padicUnitPart, hg2_val, neg_zero, zpow_zero, mul_one]
          rfl
        refine Prod.ext (by change (Padic.valuation (g2 : ℚ_[2]) : ZMod 2) = 0; rw [hg2_val]; simp)
          (Prod.ext
            (by change eps8 (PadicInt.toZModPow 3 (padicUnitPart g2 : ℤ_[2])) = 1; rw [hup, map_neg, map_one]; exact eps8_neg_one)
            (by change omega8 (PadicInt.toZModPow 3 (padicUnitPart g2 : ℤ_[2])) = 0; rw [hup, map_neg, map_one]; exact omega8_neg_one))
      have hg3_val : Padic.valuation (g3 : ℚ_[2]) = 0 := by
        change Padic.valuation (5 : ℚ_[2]) = 0
        rw [Padic.valuation_ofNat, padicValNat.eq_zero_of_not_dvd (by norm_num), Nat.cast_zero]
      have hg3 : padicTwoCoordHom g3 = Multiplicative.ofAdd ((0 : ZMod 2), (0 : ZMod 2), (1 : ZMod 2)) := by
        apply Multiplicative.toAdd.injective
        have hup : (padicUnitPart g3 : ℤ_[2]) = 5 := by
          apply Subtype.ext
          rw [coe_padicUnitPart, hg3_val, neg_zero, zpow_zero, mul_one]
          rfl
        have h5mod : (PadicInt.toZModPow 3 (5 : ℤ_[2]) : ZMod 8) = 5 :=
          map_ofNat (PadicInt.toZModPow 3) 5
        refine Prod.ext (by change (Padic.valuation (g3 : ℚ_[2]) : ZMod 2) = 0; rw [hg3_val]; simp)
          (Prod.ext
            (by change eps8 (PadicInt.toZModPow 3 (padicUnitPart g3 : ℤ_[2])) = 0; rw [hup, h5mod]; decide)
            (by change omega8 (PadicInt.toZModPow 3 (padicUnitPart g3 : ℤ_[2])) = 1; rw [hup, h5mod]; decide))
      intro y
      let a := (Multiplicative.toAdd y).1
      let b := (Multiplicative.toAdd y).2.1
      let c := (Multiplicative.toAdd y).2.2
      refine ⟨g1 ^ a.val * g2 ^ b.val * g3 ^ c.val, ?_⟩
      rw [map_mul, map_mul, map_pow, map_pow, map_pow, hg1, hg2, hg3]
      apply Multiplicative.toAdd.injective
      rcases zmod2_eq_zero_or_one a with ha | ha <;>
        rcases zmod2_eq_zero_or_one b with hb | hb <;>
        rcases zmod2_eq_zero_or_one c with hc | hc <;>
        exact Prod.ext (by simp [a, ha, hb, hc]) (Prod.ext (by simp [b, ha, hb, hc]) (by simp [c, ha, hb, hc])))
    (by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_range]
      constructor
      · intro hx
        have htriple := congrArg Multiplicative.toAdd hx
        have hv0 : (Padic.valuation (x : ℚ_[2]) : ZMod 2) = 0 := congrArg Prod.fst htriple
        have heps0 : eps8 (PadicInt.toZModPow 3 (padicUnitPart x : ℤ_[2])) = 0 :=
          congrArg (fun t => t.2.1) htriple
        have hom0 : omega8 (PadicInt.toZModPow 3 (padicUnitPart x : ℤ_[2])) = 0 :=
          congrArg (fun t => t.2.2) htriple
        obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hv0
        have hu8_eq1 : (PadicInt.toZModPow 3 (padicUnitPart x : ℤ_[2]) : ZMod 8) = 1 :=
          zmod8_eq_one_of_eps_omega_zero (toZModPow3_padicIntUnit_odd (padicUnitPart x)) heps0 hom0
        obtain ⟨z, hz⟩ := exists_sq_padicInt_two (padicUnitPart x) hu8_eq1
        have hz0 : (z : ℚ_[2]) ≠ 0 := by
          intro h0
          have hz_zero : z = 0 := Subtype.ext h0
          rw [hz_zero, zero_pow two_ne_zero] at hz
          exact (padicUnitPart x).ne_zero hz.symm
        let yQ : ℚ_[2] := (2 : ℚ_[2]) ^ k * (z : ℚ_[2])
        let y : ℚ_[2]ˣ := Units.mk0 yQ (mul_ne_zero (zpow_ne_zero k (by norm_num)) hz0)
        refine ⟨y, Units.ext ?_⟩
        change yQ ^ 2 = (x : ℚ_[2])
        dsimp only [yQ]
        have hk' : Padic.valuation (x : ℚ_[2]) = k * ((2 : ℕ) : ℤ) := by rw [hk]; ring
        rw [mul_pow, ← zpow_natCast ((2 : ℚ_[2]) ^ k), ← zpow_mul, ← hk']
        have hzQ : (z : ℚ_[2]) ^ 2 = ((padicUnitPart x : ℤ_[2]) : ℚ_[2]) := by
          rw [← PadicInt.coe_pow, hz]
        rw [hzQ]
        simpa using (padic_eq_p_zpow_mul_unitPart x).symm
      · rintro ⟨y, rfl⟩
        change padicTwoCoordHom (y ^ 2) = 1
        rw [sq, map_mul]
        apply Multiplicative.toAdd.injective
        change Multiplicative.toAdd (padicTwoCoordHom y) +
          Multiplicative.toAdd (padicTwoCoordHom y) = 0
        have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
        exact Prod.ext (h2 _) (Prod.ext (h2 _) (h2 _)))

/-- `SqQuot ℚ_[p]ˣ` is finite-dimensional over `ZMod 2` for EVERY prime `p` (`dim 3` at `2`, `dim 2` at odd `p`). -/
instance instFiniteDimensionalPadicSqQuot (p : ℕ) [Fact p.Prime] :
    FiniteDimensional (ZMod 2) (SqQuot ℚ_[p]ˣ) := by
  by_cases hp2 : p = 2
  · subst hp2; exact padicSqQuotEquivTwo.symm.finiteDimensional
  · exact (padicSqQuotEquivOdd p hp2).symm.finiteDimensional

/-- Exact dimension `dim_{𝔽₂}(ℚ_[2]ˣ / (ℚ_[2]ˣ)²) = 3`. -/
theorem finrank_padicSqQuotTwo : Module.finrank (ZMod 2) (SqQuot ℚ_[2]ˣ) = 3 := by
  rw [padicSqQuotEquivTwo.finrank_eq, Module.finrank_prod, Module.finrank_prod,
    Module.finrank_self]

/-- **Concrete `LocalDualityPairing (ZMod 2)` on `ℚ_[p]ˣ / (ℚ_[p]ˣ)²`** for every odd prime `p`! -/
def padicLocalDualityPairingOdd (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    LocalDualityPairing (ZMod 2) (SqQuot ℚ_[p]ˣ) (SqQuot ℚ_[p]ˣ) :=
  localDualityPairingCongr (padicSqQuotEquivOdd p hp2) (localPairingOdd p Fact.out hp2)

/-- **Concrete `LocalDualityPairing (ZMod 2)` on `ℚ_[2]ˣ / (ℚ_[2]ˣ)²`**! -/
def padicLocalDualityPairingTwo : LocalDualityPairing (ZMod 2) (SqQuot ℚ_[2]ˣ) (SqQuot ℚ_[2]ˣ) :=
  localDualityPairingCongr padicSqQuotEquivTwo localPairingTwo

end LocalDualityPairings

/-! ## Section 5: Concrete Global Poitou–Tate Self-Orthogonality on `ℚ` & Hasse–Minkowski Corollaries -/

section GlobalPoitouTateQ

/-! ### 5A. Exact Valuation Bridge `adicVal ℚ v x = padicValRat (primesEquiv v) x` -/

/-- For every finite place `v : Place ℚ`, the prime ideal `v.asIdeal` in `𝒪_ℚ` is generated by
the natural prime `p = (Rat.HeightOneSpectrum.primesEquiv v).1`. -/
theorem asIdeal_eq_span_natGenerator (v : Place ℚ) :
    v.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.primesEquiv v).1 : OK ℚ)} := by
  let e : OK ℚ ≃+* ℤ := Rat.IsIntegralClosure.intEquiv (OK ℚ)
  have hspan : Ideal.span {((Rat.HeightOneSpectrum.primesEquiv v).1 : ℤ)} = v.asIdeal.map e :=
    Rat.HeightOneSpectrum.span_natGenerator v
  have hback : Ideal.map (e.symm : ℤ →+* OK ℚ)
      (Ideal.span {((Rat.HeightOneSpectrum.primesEquiv v).1 : ℤ)}) =
      Ideal.map (e.symm : ℤ →+* OK ℚ) (Ideal.map (e : OK ℚ →+* ℤ) v.asIdeal) :=
    congrArg (Ideal.map (e.symm : ℤ →+* OK ℚ)) hspan
  have hcomp : (e.symm : ℤ →+* OK ℚ).comp (e : OK ℚ →+* ℤ) = RingHom.id (OK ℚ) := by
    apply RingHom.ext
    intro x
    exact e.symm_apply_apply x
  rw [Ideal.map_map, hcomp, Ideal.map_id, Ideal.map_span] at hback
  rw [← hback]
  congr 1
  ext y
  simp

/-- **Exact Valuation Bridge on `ℚ`**: Mathlib's `DedekindDomain` fractional-ideal valuation
`Stage5NumberFieldCohom.adicVal ℚ v x` equals `padicValRat (primesEquiv v).1 x` for every
finite place `v : Place ℚ` and every `x : ℚˣ`. -/
theorem adicVal_rat_eq_padicValRat (v : Place ℚ) (x : ℚˣ) :
    adicVal ℚ v x = padicValRat (Rat.HeightOneSpectrum.primesEquiv v).1 (x : ℚ) := by
  let p : ℕ := (Rat.HeightOneSpectrum.primesEquiv v).1
  have hp : p.Prime := (Rat.HeightOneSpectrum.primesEquiv v).2
  have : Fact p.Prime := ⟨hp⟩
  have hgen : ∀ g ∈ ratUnitsGen, adicVal ℚ v g = padicValRat p (g : ℚ) := by
    intro g hg
    rcases hg with rfl | ⟨q, hq, rfl⟩
    · have hu : (-1 : ℚˣ) = Units.map (algebraMap (OK ℚ) ℚ : OK ℚ →* ℚ) (-1) := by
        apply Units.ext; simp
      rw [hu, adicVal_unit_eq_zero]
      simp
    · let w : Place ℚ := Rat.HeightOneSpectrum.primesEquiv.symm ⟨q, hq⟩
      have hw_gen : (Rat.HeightOneSpectrum.primesEquiv w).1 = q := by
        exact congrArg Subtype.val (Equiv.apply_symm_apply Rat.HeightOneSpectrum.primesEquiv ⟨q, hq⟩)
      have hw_ideal : w.asIdeal = Ideal.span {(q : OK ℚ)} := by
        simpa [hw_gen] using asIdeal_eq_span_natGenerator w
      have hspan_eq :
          FractionalIdeal.spanSingleton (nonZeroDivisors (OK ℚ)) (primeUnit q hq : ℚ) =
            (w.asIdeal : FractionalIdeal (nonZeroDivisors (OK ℚ)) ℚ) := by
        rw [hw_ideal, FractionalIdeal.coeIdeal_span_singleton, coe_primeUnit, map_natCast]
      unfold adicVal
      rw [hspan_eq, coe_primeUnit]
      by_cases hqp : q = p
      · subst hqp
        have hwv : w = v := by
          apply Rat.HeightOneSpectrum.primesEquiv.injective
          apply Subtype.ext
          exact hw_gen
        rw [hwv, FractionalIdeal.count_self, padicValRat.self hp.one_lt]
      · have hwv : w ≠ v := by
          intro h
          apply hqp
          calc q = (Rat.HeightOneSpectrum.primesEquiv w).1 := hw_gen.symm
            _ = (Rat.HeightOneSpectrum.primesEquiv v).1 := by rw [h]
        rw [FractionalIdeal.count_maximal_coprime ℚ v hwv, padicValRat_prime_of_ne hp hq (Ne.symm hqp)]
  have hx : x ∈ Subgroup.closure ratUnitsGen := by
    rw [subgroup_closure_ratUnitsGen]; trivial
  exact Subgroup.closure_induction (p := fun y _ => adicVal ℚ v y = padicValRat p (y : ℚ))
    hgen
    (by simp)
    (fun a b _ _ ha hb => by
      rw [adicVal_mul, ha, hb, Units.val_mul, padicValRat.mul a.ne_zero b.ne_zero])
    (fun a _ ha => by
      rw [adicVal_inv, ha, Units.val_inv_eq_inv_val, padicValRat.inv])
    hx

/-! ### 5B. Exact `𝔽₂`-Vector Space Structure & Dimension of `KummerSelmer ℚ S_fin 2` -/

/-- Helper: a positive natural number whose `p`-adic valuation is even at every prime `p`
is a square in `ℕ`. -/
theorem exists_sq_nat_of_even_padicValNat :
    ∀ (n : ℕ), 0 < n → (∀ p : ℕ, p.Prime → Even (padicValNat p n)) → ∃ k : ℕ, k ^ 2 = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn heven
    by_cases h1 : n = 1
    · exact ⟨1, by omega⟩
    · let p := n.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have : Fact p.Prime := ⟨hp⟩
      have hpdvd : p ∣ n := Nat.minFac_dvd n
      have hval_pos : 1 ≤ padicValNat p n := one_le_padicValNat_of_dvd hn.ne' hpdvd
      obtain ⟨r, hr⟩ := heven p hp
      have hval_ge2 : 2 ≤ padicValNat p n := by omega
      have hp2dvd : p ^ 2 ∣ n := (padicValNat_dvd_iff_le (p := p) hn.ne').mpr hval_ge2
      let m := n / p ^ 2
      have hm_eq : n = p ^ 2 * m := (Nat.mul_div_cancel' hp2dvd).symm
      have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hn hp2dvd) (pow_pos hp.pos 2)
      have hm_lt : m < n := Nat.div_lt_self hn (by have := hp.two_le; nlinarith)
      have hm_even : ∀ q : ℕ, q.Prime → Even (padicValNat q m) := by
        intro q hq
        have : Fact q.Prime := ⟨hq⟩
        have hmul := padicValNat.mul (p := q) (a := p ^ 2) (b := m) (pow_ne_zero 2 hp.ne_zero) hm_pos.ne'
        rw [← hm_eq, sq, padicValNat.mul (p := q) hp.ne_zero hp.ne_zero] at hmul
        obtain ⟨s, hs⟩ := heven q hq
        rw [hmul] at hs
        exact ⟨s - padicValNat q p, by omega⟩
      obtain ⟨k, hk⟩ := ih m hm_lt hm_pos hm_even
      refine ⟨p * k, ?_⟩
      rw [mul_pow, hk, ← hm_eq]

/-- **Concrete Square Criterion on `ℚˣ`**: a positive rational `a : ℚˣ` whose `p`-adic valuation
is even at every prime `p` is a square in `ℚˣ`. -/
theorem isSquare_ratUnits_of_pos_of_even_val {a : ℚˣ} (hpos : 0 < (a : ℚ))
    (heven : ∀ p : ℕ, p.Prime → (2 : ℤ) ∣ padicValRat p (a : ℚ)) :
    ∃ y : ℚˣ, y ^ 2 = a := by
  have hnum_pos : 0 < (a : ℚ).num := Rat.num_pos.mpr hpos
  have hnumAbs_pos : 0 < (a : ℚ).num.natAbs := Int.natAbs_pos.mpr hnum_pos.ne'
  have hden_pos : 0 < (a : ℚ).den := (a : ℚ).pos
  have hnum_even : ∀ p : ℕ, p.Prime → Even (padicValNat p (a : ℚ).num.natAbs) := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := heven p hp
    rw [padicValRat_def] at hk
    by_cases hd : p ∣ (a : ℚ).den
    · have hnd : ¬ p ∣ (a : ℚ).num.natAbs := fun hn =>
        hp.not_dvd_one ((a : ℚ).reduced.gcd_eq_one ▸ Nat.dvd_gcd hn hd)
      rw [padicValNat.eq_zero_of_not_dvd hnd]
      exact ⟨0, rfl⟩
    · rw [padicValNat.eq_zero_of_not_dvd hd] at hk
      change (padicValNat p (a : ℚ).num.natAbs : ℤ) - 0 = 2 * k at hk
      exact ⟨k.toNat, by omega⟩
  have hden_even : ∀ p : ℕ, p.Prime → Even (padicValNat p (a : ℚ).den) := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := heven p hp
    rw [padicValRat_def] at hk
    by_cases hn : p ∣ (a : ℚ).num.natAbs
    · have hnd : ¬ p ∣ (a : ℚ).den := fun hd =>
        hp.not_dvd_one ((a : ℚ).reduced.gcd_eq_one ▸ Nat.dvd_gcd hn hd)
      rw [padicValNat.eq_zero_of_not_dvd hnd]
      exact ⟨0, rfl⟩
    · have h0 : padicValInt p (a : ℚ).num = 0 := padicValNat.eq_zero_of_not_dvd hn
      rw [h0] at hk
      change (0 : ℤ) - (padicValNat p (a : ℚ).den : ℤ) = 2 * k at hk
      exact ⟨(-k).toNat, by omega⟩
  obtain ⟨r, hr⟩ := exists_sq_nat_of_even_padicValNat _ hnumAbs_pos hnum_even
  obtain ⟨s, hs⟩ := exists_sq_nat_of_even_padicValNat _ hden_pos hden_even
  have hr0 : r ≠ 0 := fun h => by rw [h, zero_pow two_ne_zero] at hr; omega
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_pow two_ne_zero] at hs; omega
  let yQ : ℚ := (r : ℚ) / (s : ℚ)
  let y : ℚˣ := Units.mk0 yQ (div_ne_zero (Nat.cast_ne_zero.mpr hr0) (Nat.cast_ne_zero.mpr hs0))
  refine ⟨y, Units.ext ?_⟩
  change ((r : ℚ) / (s : ℚ)) ^ 2 = (a : ℚ)
  rw [div_pow, ← Nat.cast_pow, ← Nat.cast_pow, hr, hs]
  have habs : (((a : ℚ).num.natAbs : ℤ) : ℚ) = ((a : ℚ).num : ℚ) := by
    exact_mod_cast Int.natAbs_of_nonneg hnum_pos.le
  rw [← Int.cast_natCast, habs, Rat.num_div_den]

/-- Concrete global `2`-Selmer space `KummerSelmerQ S_fin := Additive (KummerSelmer ℚ S_fin 2)`
wired directly to `Stage5NumberFieldCohom.KummerSelmer`! -/
abbrev KummerSelmerQ (S_fin : Finset (Place ℚ)) : Type :=
  Additive (KummerSelmer ℚ S_fin 2)

/-- Canonical `ZMod 2`-vector space structure on `KummerSelmerQ S_fin`. -/
instance instModuleZMod2KummerSelmerQ (S_fin : Finset (Place ℚ)) :
    Module (ZMod 2) (KummerSelmerQ S_fin) :=
  zmod2ModuleOfTwoTorsion (fun x => by
    change Additive.ofMul (Additive.toMul x * Additive.toMul x) = Additive.ofMul 1
    congr 1
    apply Subtype.ext
    change (Additive.toMul x).1 * (Additive.toMul x).1 = 1
    induction (Additive.toMul x).1 using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk (g * g) : ℚˣ ⧸ (powMonoidHom (α := ℚˣ) 2).range) = 1
      rw [QuotientGroup.eq_one_iff]
      exact ⟨g, sq g⟩)

/-- Helper: sign-and-`S`-valuation homomorphism `ℚˣ →* Multiplicative (Option S_fin → ZMod 2)`. -/
def ratSignValHom (S_fin : Finset (Place ℚ)) :
    ℚˣ →* Multiplicative (Option S_fin → ZMod 2) where
  toFun a :=
    Multiplicative.ofAdd fun o => match o with
      | none => signInf a
      | some v => (padicValRat (Rat.HeightOneSpectrum.primesEquiv v.1).1 (a : ℚ) : ZMod 2)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext o
    cases o with
    | none => simp
    | some v => simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext o
    cases o with
    | none => exact signInf_mul a b
    | some v =>
      have : Fact (Rat.HeightOneSpectrum.primesEquiv v.1).1.Prime :=
        ⟨(Rat.HeightOneSpectrum.primesEquiv v.1).2⟩
      change (padicValRat _ ((a * b : ℚˣ) : ℚ) : ZMod 2) =
        (padicValRat _ (a : ℚ) : ZMod 2) + (padicValRat _ (b : ℚ) : ZMod 2)
      rw [Units.val_mul, padicValRat.mul a.ne_zero b.ne_zero, Int.cast_add]

/-- Descent of `ratSignValHom` to `SqQuot ℚˣ →ₗ[ZMod 2] (Option S_fin → ZMod 2)`. -/
def ratSignValSqQuot (S_fin : Finset (Place ℚ)) :
    SqQuot ℚˣ →ₗ[ZMod 2] (Option S_fin → ZMod 2) :=
  addMonoidHomToZMod2LinearMap
    (MonoidHom.toAdditive
      (QuotientGroup.lift (powMonoidHom (α := ℚˣ) 2).range (ratSignValHom S_fin) (by
        rintro _ ⟨y, rfl⟩
        change ratSignValHom S_fin (y ^ 2) = 1
        rw [sq, map_mul]
        apply Multiplicative.toAdd.injective
        funext o
        change Multiplicative.toAdd (ratSignValHom S_fin y) o +
          Multiplicative.toAdd (ratSignValHom S_fin y) o = 0
        have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
        exact h2 _)))

/-- Restriction of `ratSignValSqQuot` to `KummerSelmerQ S_fin →ₗ[ZMod 2] (Option S_fin → ZMod 2)`. -/
def kummerSelmerQToCoords (S_fin : Finset (Place ℚ)) :
    KummerSelmerQ S_fin →ₗ[ZMod 2] (Option S_fin → ZMod 2) :=
  (ratSignValSqQuot S_fin).comp
    (addMonoidHomToZMod2LinearMap (MonoidHom.toAdditive (KummerSelmer ℚ S_fin 2).subtype))

/-- **Exact `𝔽₂`-Linear Isomorphism for `KummerSelmer ℚ S_fin 2`**:
`KummerSelmerQ S_fin ≃ₗ[ZMod 2] (Option S_fin → ZMod 2)`! -/
def kummerSelmerQEquiv (S_fin : Finset (Place ℚ)) :
    KummerSelmerQ S_fin ≃ₗ[ZMod 2] (Option S_fin → ZMod 2) :=
  LinearEquiv.ofBijective (kummerSelmerQToCoords S_fin)
    ⟨by
      intro x₁ x₂ h
      have hsub : kummerSelmerQToCoords S_fin (x₁ - x₂) = 0 := by
        rw [map_sub, h, sub_self]
      suffices h0 : x₁ - x₂ = 0 from sub_eq_zero.mp h0
      generalize hdiff : x₁ - x₂ = x at hsub ⊢
      clear hdiff h x₁ x₂
      change Additive.ofMul (Additive.toMul x) = Additive.ofMul 1
      congr 1
      apply Subtype.ext
      rcases x with ⟨q, hq⟩
      induction q using QuotientGroup.induction_on with
      | H a =>
        change (QuotientGroup.mk a : ℚˣ ⧸ (powMonoidHom (α := ℚˣ) 2).range) = 1
        rw [QuotientGroup.eq_one_iff]
        have hsign : signInf a = 0 := congrFun hsub none
        have hpos : 0 < (a : ℚ) := by
          rcases lt_or_gt_of_ne a.ne_zero with hlt | hgt
          · exfalso
            have h1 : signInf a = 1 := if_pos hlt
            rw [h1] at hsign
            exact (by decide : (1 : ZMod 2) ≠ 0) hsign
          · exact hgt
        have heven : ∀ p : ℕ, p.Prime → (2 : ℤ) ∣ padicValRat p (a : ℚ) := by
          intro p hp
          let v : Place ℚ := Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, hp⟩
          have hvp : (Rat.HeightOneSpectrum.primesEquiv v).1 = p :=
            congrArg Subtype.val (Equiv.apply_symm_apply Rat.HeightOneSpectrum.primesEquiv ⟨p, hp⟩)
          by_cases hv : v ∈ S_fin
          · have h0 : (padicValRat (Rat.HeightOneSpectrum.primesEquiv v).1 (a : ℚ) : ZMod 2) = 0 :=
              congrFun hsub (some ⟨v, hv⟩)
            rw [hvp] at h0
            exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h0
          · have hdvd := (mem_kummerSelmer_iff ℚ S_fin 2 a).mp hq v hv
            rw [adicVal_rat_eq_padicValRat v a, hvp] at hdvd
            exact hdvd
        exact isSquare_ratUnits_of_pos_of_even_val hpos heven,
     by
      classical
      intro f
      let a : ℚˣ := (-1 : ℚˣ) ^ (f none).val *
        ∏ v ∈ S_fin.attach,
          primeUnit (Rat.HeightOneSpectrum.primesEquiv v.1).1
            (Rat.HeightOneSpectrum.primesEquiv v.1).2 ^ (f (some v)).val
      have ha_pos_prod : ∀ s : Finset S_fin,
          0 < ((∏ v ∈ s,
            primeUnit (Rat.HeightOneSpectrum.primesEquiv v.1).1
              (Rat.HeightOneSpectrum.primesEquiv v.1).2 ^ (f (some v)).val : ℚˣ) : ℚ) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | insert v s hv ih =>
          rw [Finset.prod_insert hv, Units.val_mul, Units.val_pow_eq_pow_val, coe_primeUnit]
          exact mul_pos (pow_pos (Nat.cast_pos.mpr (Rat.HeightOneSpectrum.primesEquiv v.1).2.pos) _) ih
      have ha_val : ∀ w : Place ℚ,
          padicValRat (Rat.HeightOneSpectrum.primesEquiv w).1 (a : ℚ) =
            if hw : w ∈ S_fin then ((f (some ⟨w, hw⟩)).val : ℤ) else 0 := by
        intro w
        let p := (Rat.HeightOneSpectrum.primesEquiv w).1
        have hp : p.Prime := (Rat.HeightOneSpectrum.primesEquiv w).2
        have : Fact p.Prime := ⟨hp⟩
        have hval_prod : ∀ s : Finset S_fin,
            padicValRat p ((∏ v ∈ s,
              primeUnit (Rat.HeightOneSpectrum.primesEquiv v.1).1
                (Rat.HeightOneSpectrum.primesEquiv v.1).2 ^ (f (some v)).val : ℚˣ) : ℚ) =
              ∑ v ∈ s, if v.1 = w then ((f (some v)).val : ℤ) else 0 := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp
          | insert v s hv ih =>
            rw [Finset.prod_insert hv, Units.val_mul,
              padicValRat.mul (Units.ne_zero _) (Units.ne_zero _), ih, Finset.sum_insert hv]
            congr 1
            rw [padicValRat_pow_unit hp, coe_primeUnit]
            by_cases hvw : v.1 = w
            · rw [if_pos hvw]
              have hpeq : (Rat.HeightOneSpectrum.primesEquiv v.1).1 = p := by rw [hvw]
              rw [hpeq, padicValRat.self hp.one_lt, mul_one]
            · rw [if_neg hvw]
              have hpne : p ≠ (Rat.HeightOneSpectrum.primesEquiv v.1).1 := by
                intro heq
                apply hvw
                apply Rat.HeightOneSpectrum.primesEquiv.injective
                exact Subtype.ext heq.symm
              rw [padicValRat_prime_of_ne hp (Rat.HeightOneSpectrum.primesEquiv v.1).2 hpne,
                mul_zero]
        dsimp only [a]
        rw [Units.val_mul, padicValRat.mul (Units.ne_zero _) (Units.ne_zero _)]
        have hneg_val : padicValRat p (((-1 : ℚˣ) ^ (f none).val : ℚˣ) : ℚ) = 0 := by
          rw [padicValRat_pow_unit hp (-1) (f none).val]
          simp
        rw [hneg_val, zero_add, hval_prod]
        by_cases hw : w ∈ S_fin
        · rw [dif_pos hw, Finset.sum_eq_single (⟨w, hw⟩ : S_fin)]
          · simp
          · intro v _ hvw
            have hne : v.1 ≠ w := fun h => hvw (Subtype.ext h)
            simp [hne]
          · intro h; exact absurd (Finset.mem_attach S_fin ⟨w, hw⟩) h
        · rw [dif_neg hw]
          refine Finset.sum_eq_zero fun v _ => ?_
          have hne : v.1 ≠ w := fun h => hw (h ▸ v.2)
          simp [hne]
      have ha_mem : (QuotientGroup.mk a : ℚˣ ⧸ (powMonoidHom (α := ℚˣ) 2).range) ∈
          KummerSelmer ℚ S_fin 2 := by
        rw [mem_kummerSelmer_iff]
        intro w hw
        rw [adicVal_rat_eq_padicValRat w a, ha_val w, dif_neg hw]
        exact dvd_zero 2
      refine ⟨Additive.ofMul ⟨QuotientGroup.mk a, ha_mem⟩, ?_⟩
      funext o
      cases o with
      | none =>
        change signInf a = f none
        dsimp only [a]
        rw [signInf_mul, signInf_pos (ha_pos_prod _), add_zero]
        rcases zmod2_eq_zero_or_one (f none) with h0 | h1
        · rw [h0]; simp
        · rw [h1]
          have hval : (1 : ZMod 2).val = 1 := rfl
          rw [hval, pow_one, signInf_neg_one]
      | some v =>
        change (padicValRat (Rat.HeightOneSpectrum.primesEquiv v.1).1 (a : ℚ) : ZMod 2) = f (some v)
        rw [ha_val v.1, dif_pos v.2, Int.cast_natCast, ZMod.natCast_zmod_val]⟩

instance instFiniteDimensionalKummerSelmerQ (S_fin : Finset (Place ℚ)) :
    FiniteDimensional (ZMod 2) (KummerSelmerQ S_fin) :=
  (kummerSelmerQEquiv S_fin).symm.finiteDimensional

/-- **Exact `𝔽₂`-Dimension of `KummerSelmer ℚ S_fin 2`**:
`dim_{𝔽₂} K(S_fin, 2) = |S_fin| + 1` (the exact count of places `S = {∞} ∪ S_fin`)! -/
theorem kummerSelmerQ_finrank (S_fin : Finset (Place ℚ)) :
    Module.finrank (ZMod 2) (KummerSelmerQ S_fin) = S_fin.card + 1 := by
  rw [(kummerSelmerQEquiv S_fin).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_option, Fintype.card_coe]

/-! ### 5C. Unified Places of `ℚ`, Product Local Duality Pairing & Poitou–Tate Self-Orthogonality -/

/-- All places of `ℚ`: `inf` (`∞`), `two` (`p = 2`), and `odd p` (every odd prime `p ≠ 2`). -/
inductive QPlace : Type
  | inf : QPlace
  | two : QPlace
  | odd : OddPrime → QPlace
  deriving DecidableEq

/-- The finite place of `ℚ` corresponding to `p = 2`. -/
def twoPlace : Place ℚ :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩

/-- Map a finite place `v : Place ℚ` to its `QPlace` (`two` or `odd p`). -/
def placeToQPlace (v : Place ℚ) : QPlace :=
  let p := Rat.HeightOneSpectrum.primesEquiv v
  if h : p.1 = 2 then QPlace.two else QPlace.odd ⟨p.1, p.2, h⟩

theorem placeToQPlace_twoPlace : placeToQPlace twoPlace = QPlace.two := by
  unfold placeToQPlace twoPlace
  have h2 : (Rat.HeightOneSpectrum.primesEquiv (R := OK ℚ)
      ((Rat.HeightOneSpectrum.primesEquiv (R := OK ℚ)).symm ⟨2, Nat.prime_two⟩)).1 = 2 :=
    congrArg Subtype.val
      (Equiv.apply_symm_apply (Rat.HeightOneSpectrum.primesEquiv (R := OK ℚ)) ⟨2, Nat.prime_two⟩)
  dsimp only
  rw [dif_pos h2]

theorem placeToQPlace_ne_inf (v : Place ℚ) : placeToQPlace v ≠ QPlace.inf := by
  unfold placeToQPlace
  dsimp only
  split_ifs <;> simp

theorem placeToQPlace_injective : Function.Injective placeToQPlace := by
  intro v₁ v₂ h
  unfold placeToQPlace at h
  dsimp only at h
  by_cases h1 : (Rat.HeightOneSpectrum.primesEquiv v₁).1 = 2 <;>
    by_cases h2 : (Rat.HeightOneSpectrum.primesEquiv v₂).1 = 2
  · apply Rat.HeightOneSpectrum.primesEquiv.injective
    exact Subtype.ext (h1.trans h2.symm)
  · rw [dif_pos h1, dif_neg h2] at h
    exact absurd h (by simp)
  · rw [dif_neg h1, dif_pos h2] at h
    exact absurd h (by simp)
  · rw [dif_neg h1, dif_neg h2] at h
    have hEq := QPlace.odd.inj h
    have h12 : (Rat.HeightOneSpectrum.primesEquiv v₁).1 = (Rat.HeightOneSpectrum.primesEquiv v₂).1 :=
      congrArg (fun x : OddPrime => x.1) hEq
    exact Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext h12)

/-- The finite set of places `S = {∞} ∪ S_fin` of `ℚ` attached to a finite set of finite places `S_fin`. -/
def SPlaces (S_fin : Finset (Place ℚ)) : Finset QPlace :=
  insert QPlace.inf (S_fin.image placeToQPlace)

theorem card_SPlaces (S_fin : Finset (Place ℚ)) :
    (SPlaces S_fin).card = S_fin.card + 1 := by
  unfold SPlaces
  have hnotmem : QPlace.inf ∉ S_fin.image placeToQPlace := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro v _
    exact placeToQPlace_ne_inf v
  rw [Finset.card_insert_of_notMem hnotmem, Finset.card_image_of_injective _ placeToQPlace_injective]

theorem mem_SPlaces_inf (S_fin : Finset (Place ℚ)) : QPlace.inf ∈ SPlaces S_fin :=
  Finset.mem_insert_self _ _

theorem mem_SPlaces_two {S_fin : Finset (Place ℚ)} (h2 : twoPlace ∈ S_fin) :
    QPlace.two ∈ SPlaces S_fin := by
  apply Finset.mem_insert_of_mem
  rw [Finset.mem_image]
  exact ⟨twoPlace, h2, placeToQPlace_twoPlace⟩

/-- Concrete local cohomology space `H¹(ℚ_v, μ₂)` at every place `v : QPlace`:
`dim = 1` at `∞`, `dim = 3` at `2`, `dim = 2` at every odd prime `p`. -/
def LocalH1 : QPlace → Type
  | QPlace.inf => ZMod 2
  | QPlace.two => ZMod 2 × ZMod 2 × ZMod 2
  | QPlace.odd _ => ZMod 2 × ZMod 2

instance instAddCommGroupLocalH1 : (v : QPlace) → AddCommGroup (LocalH1 v)
  | QPlace.inf => inferInstanceAs (AddCommGroup (ZMod 2))
  | QPlace.two => inferInstanceAs (AddCommGroup (ZMod 2 × ZMod 2 × ZMod 2))
  | QPlace.odd _ => inferInstanceAs (AddCommGroup (ZMod 2 × ZMod 2))

instance instModuleLocalH1 : (v : QPlace) → Module (ZMod 2) (LocalH1 v)
  | QPlace.inf => inferInstanceAs (Module (ZMod 2) (ZMod 2))
  | QPlace.two => inferInstanceAs (Module (ZMod 2) (ZMod 2 × ZMod 2 × ZMod 2))
  | QPlace.odd _ => inferInstanceAs (Module (ZMod 2) (ZMod 2 × ZMod 2))

instance instFiniteDimensionalLocalH1 : (v : QPlace) → FiniteDimensional (ZMod 2) (LocalH1 v)
  | QPlace.inf => inferInstanceAs (FiniteDimensional (ZMod 2) (ZMod 2))
  | QPlace.two => inferInstanceAs (FiniteDimensional (ZMod 2) (ZMod 2 × ZMod 2 × ZMod 2))
  | QPlace.odd _ => inferInstanceAs (FiniteDimensional (ZMod 2) (ZMod 2 × ZMod 2))

theorem finrank_localH1_inf : Module.finrank (ZMod 2) (LocalH1 QPlace.inf) = 1 :=
  Module.finrank_self (ZMod 2)

theorem finrank_localH1_two : Module.finrank (ZMod 2) (LocalH1 QPlace.two) = 3 := by
  change Module.finrank (ZMod 2) (ZMod 2 × ZMod 2 × ZMod 2) = 3
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self]

theorem finrank_localH1_odd (p : OddPrime) : Module.finrank (ZMod 2) (LocalH1 (QPlace.odd p)) = 2 := by
  change Module.finrank (ZMod 2) (ZMod 2 × ZMod 2) = 2
  rw [Module.finrank_prod, Module.finrank_self]

/-- Concrete nondegenerate local Tate / Hilbert pairing at every place `v : QPlace`. -/
def localPairingAt : (v : QPlace) → LocalDualityPairing (ZMod 2) (LocalH1 v) (LocalH1 v)
  | QPlace.inf => localPairingInf
  | QPlace.two => localPairingTwo
  | QPlace.odd p => localPairingOdd p.1 p.2.1 p.2.2

/-- **Concrete Product Local Tate Pairing** on `∏_{v ∈ S} H¹(ℚ_v, μ₂)` via
`Stage2GaloisCohomology.LocalDualityPairing.prodPairing`! -/
def globalProductPairing (S_fin : Finset (Place ℚ)) :
    LocalDualityPairing (ZMod 2)
      (∀ v : SPlaces S_fin, LocalH1 v.1) (∀ v : SPlaces S_fin, LocalH1 v.1) :=
  LocalDualityPairing.prodPairing (fun v : SPlaces S_fin => localPairingAt v.1)

/-- **Exact Ambient Dimension Formula `dim(∏_{v ∈ S} H¹(ℚ_v, μ₂)) = 2|S|`**:
`1 (at ∞) + 3 (at 2) + 2 (|S| - 2) (at odd primes) = 2|S|` whenever `2 ∈ S_fin`! -/
theorem finrank_prodLocalH1 {S_fin : Finset (Place ℚ)} (h2 : twoPlace ∈ S_fin) :
    Module.finrank (ZMod 2) (∀ v : SPlaces S_fin, LocalH1 v.1) = 2 * (SPlaces S_fin).card := by
  rw [Module.finrank_pi_fintype (ZMod 2)]
  have hsum : (∑ v : SPlaces S_fin, Module.finrank (ZMod 2) (LocalH1 v.1)) =
      ∑ v ∈ SPlaces S_fin, Module.finrank (ZMod 2) (LocalH1 v) :=
    Finset.sum_attach (SPlaces S_fin) (fun v => Module.finrank (ZMod 2) (LocalH1 v))
  rw [hsum]
  let S_rest : Finset QPlace := (SPlaces S_fin).erase QPlace.inf |>.erase QPlace.two
  have hinf_mem : QPlace.inf ∈ SPlaces S_fin := mem_SPlaces_inf S_fin
  have htwo_mem : QPlace.two ∈ (SPlaces S_fin).erase QPlace.inf :=
    Finset.mem_erase.mpr ⟨by simp, mem_SPlaces_two h2⟩
  have hsplit1 := Finset.add_sum_erase (SPlaces S_fin)
    (fun v => Module.finrank (ZMod 2) (LocalH1 v)) hinf_mem
  have hsplit2 := Finset.add_sum_erase ((SPlaces S_fin).erase QPlace.inf)
    (fun v => Module.finrank (ZMod 2) (LocalH1 v)) htwo_mem
  have hrest_val : ∀ v ∈ S_rest, Module.finrank (ZMod 2) (LocalH1 v) = 2 := by
    intro v hv
    have hv1 : v ≠ QPlace.two := (Finset.mem_erase.mp hv).1
    have hv2 : v ≠ QPlace.inf := (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
    cases v with
    | inf => exact absurd rfl hv2
    | two => exact absurd rfl hv1
    | odd p => exact finrank_localH1_odd p
  have hrest_sum : ∑ v ∈ S_rest, Module.finrank (ZMod 2) (LocalH1 v) = 2 * S_rest.card := by
    rw [Finset.sum_congr rfl hrest_val, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcard1 : ((SPlaces S_fin).erase QPlace.inf).card + 1 = (SPlaces S_fin).card :=
    Finset.card_erase_add_one hinf_mem
  have hcard2 : S_rest.card + 1 = ((SPlaces S_fin).erase QPlace.inf).card :=
    Finset.card_erase_add_one htwo_mem
  rw [← hsplit1, ← hsplit2, finrank_localH1_inf, finrank_localH1_two, hrest_sum]
  omega

/-- Local coordinate map `ℚˣ → LocalH1 v` at any place `v : QPlace`. -/
def locAt : (v : QPlace) → ℚˣ → LocalH1 v
  | QPlace.inf, a => signInf a
  | QPlace.two, a => twoCoords a
  | QPlace.odd p, a => oddCoords p.1 p.2.1 a

theorem locAt_mul (v : QPlace) (a b : ℚˣ) : locAt v (a * b) = locAt v a + locAt v b := by
  cases v with
  | inf => exact signInf_mul a b
  | two => exact twoCoords_mul a b
  | odd p => exact oddCoords_mul p.1 p.2.1 a b

theorem locAt_one (v : QPlace) : locAt v 1 = 0 := by
  cases v with
  | inf => exact signInf_one
  | two => exact twoCoords_one
  | odd p => exact oddCoords_one p.1 p.2.1

/-- Unified local Hilbert symbol `(a, b)_v ∈ ℤˣ` at every place `v : QPlace`. -/
def hilbertSymAt : QPlace → ℚˣ → ℚˣ → ℤˣ
  | QPlace.inf, a, b => hilbertSymInf a b
  | QPlace.two, a, b => hilbertSymTwo a b
  | QPlace.odd p, a, b => hilbertSymOdd p.1 p.2.1 p.2.2 a b

/-- Exact compatibility: the `LocalDualityPairing` at `v` on `(locAt v a, locAt v b)` equals
`unitsToZMod2 (hilbertSymAt v a b)`! -/
theorem localPairingAt_locAt (v : QPlace) (a b : ℚˣ) :
    (localPairingAt v).pair (locAt v a) (locAt v b) = unitsToZMod2 (hilbertSymAt v a b) := by
  cases v with
  | inf =>
    exact (unitsToZMod2_hilbertSymInf a b).symm
  | two =>
    exact (unitsToZMod2_hilbertSymTwo a b).symm
  | odd p =>
    exact (unitsToZMod2_hilbertSymOdd p.1 p.2.1 p.2.2 a b).symm

/-- Global-to-local localization homomorphism `ℚˣ →* Multiplicative (∀ v : SPlaces S_fin, LocalH1 v.1)`. -/
def locRatHom (S_fin : Finset (Place ℚ)) :
    ℚˣ →* Multiplicative (∀ v : SPlaces S_fin, LocalH1 v.1) where
  toFun a := Multiplicative.ofAdd (fun v => locAt v.1 a)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext v
    exact locAt_one v.1
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext v
    exact locAt_mul v.1 a b

/-- **Concrete Global-to-Local Localization Linear Map**:
`locGlobal S_fin : KummerSelmerQ S_fin →ₗ[ZMod 2] (∀ v : SPlaces S_fin, LocalH1 v.1)`. -/
def locGlobal (S_fin : Finset (Place ℚ)) :
    KummerSelmerQ S_fin →ₗ[ZMod 2] (∀ v : SPlaces S_fin, LocalH1 v.1) :=
  let liftHom : (ℚˣ ⧸ (powMonoidHom (α := ℚˣ) 2).range) →*
      Multiplicative (∀ v : SPlaces S_fin, LocalH1 v.1) :=
    QuotientGroup.lift (powMonoidHom (α := ℚˣ) 2).range (locRatHom S_fin) (by
      rintro _ ⟨y, rfl⟩
      change locRatHom S_fin (y ^ 2) = 1
      rw [sq, map_mul]
      apply Multiplicative.toAdd.injective
      funext v
      change locAt v.1 y + locAt v.1 y = 0
      cases v.1 with
      | inf =>
        have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
        exact h2 _
      | two =>
        have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
        exact Prod.ext (h2 _) (Prod.ext (h2 _) (h2 _))
      | odd _ =>
        have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
        exact Prod.ext (h2 _) (h2 _))
  addMonoidHomToZMod2LinearMap
    { toFun := fun x => Multiplicative.toAdd (liftHom (Additive.toMul x).1)
      map_zero' := by
        change Multiplicative.toAdd (liftHom 1) = 0
        rw [map_one]; rfl
      map_add' := fun x y => by
        change Multiplicative.toAdd (liftHom ((Additive.toMul x).1 * (Additive.toMul y).1)) =
          Multiplicative.toAdd (liftHom (Additive.toMul x).1) +
            Multiplicative.toAdd (liftHom (Additive.toMul y).1)
        rw [map_mul]; rfl }

/-- Evaluation of `locGlobal S_fin` on a global Selmer class represented by `a : ℚˣ`. -/
theorem locGlobal_apply_mk (S_fin : Finset (Place ℚ)) {a : ℚˣ}
    (ha : (QuotientGroup.mk a : ℚˣ ⧸ (powMonoidHom (α := ℚˣ) 2).range) ∈ KummerSelmer ℚ S_fin 2)
    (v : SPlaces S_fin) :
    locGlobal S_fin (Additive.ofMul ⟨QuotientGroup.mk a, ha⟩) v = locAt v.1 a :=
  rfl

/-- **Concrete Hasse Square Principle (`Ш¹_S(ℚ, μ₂) = 0`)**:
the global-to-local localization map `locGlobal S_fin` is INJECTIVE for every finite `S_fin`! -/
theorem locGlobal_injective (S_fin : Finset (Place ℚ)) :
    Function.Injective (locGlobal S_fin) := by
  intro x₁ x₂ h
  apply (kummerSelmerQEquiv S_fin).injective
  funext o
  have hsub : locGlobal S_fin (x₁ - x₂) = 0 := by rw [map_sub, h, sub_self]
  suffices h0 : kummerSelmerQToCoords S_fin (x₁ - x₂) o = 0 by
    have hlin : kummerSelmerQToCoords S_fin (x₁ - x₂) o =
        kummerSelmerQToCoords S_fin x₁ o - kummerSelmerQToCoords S_fin x₂ o := by
      rw [map_sub]; rfl
    exact sub_eq_zero.mp (hlin ▸ h0)
  generalize hdiff : x₁ - x₂ = x at hsub ⊢
  clear hdiff h x₁ x₂
  rcases x with ⟨q, hq⟩
  induction q using QuotientGroup.induction_on with
  | H a =>
    cases o with
    | none =>
      have hv := congrFun hsub ⟨QPlace.inf, mem_SPlaces_inf S_fin⟩
      exact hv
    | some w =>
      have hw_mem : placeToQPlace w.1 ∈ SPlaces S_fin :=
        Finset.mem_insert_of_mem (Finset.mem_image_of_mem placeToQPlace w.2)
      have hv := congrFun hsub ⟨placeToQPlace w.1, hw_mem⟩
      change locAt (placeToQPlace w.1) a = 0 at hv
      change (padicValRat (Rat.HeightOneSpectrum.primesEquiv w.1).1 (a : ℚ) : ZMod 2) = 0
      suffices ∀ (q : QPlace), q = placeToQPlace w.1 → locAt q a = 0 →
          (padicValRat (Rat.HeightOneSpectrum.primesEquiv w.1).1 (a : ℚ) : ZMod 2) = 0 from
        this (placeToQPlace w.1) rfl hv
      intro q hq_eq hloc
      cases q with
      | inf => exact absurd hq_eq (placeToQPlace_ne_inf w.1).symm
      | two =>
        have hp2 : (Rat.HeightOneSpectrum.primesEquiv w.1).1 = 2 := by
          unfold placeToQPlace at hq_eq; dsimp only at hq_eq
          by_contra hne
          rw [dif_neg hne] at hq_eq
          cases hq_eq
        have hf : (twoCoords a).1 = 0 := congrArg Prod.fst hloc
        simpa [twoCoords, hp2] using hf
      | odd p =>
        have hpeq : (Rat.HeightOneSpectrum.primesEquiv w.1).1 = p.1 := by
          unfold placeToQPlace at hq_eq; dsimp only at hq_eq
          by_cases h2 : (Rat.HeightOneSpectrum.primesEquiv w.1).1 = 2
          · rw [dif_pos h2] at hq_eq; cases hq_eq
          · rw [dif_neg h2] at hq_eq
            exact (congrArg (fun z : OddPrime => z.1) (QPlace.odd.inj hq_eq)).symm
        have hf : (oddCoords p.1 p.2.1 a).1 = 0 := congrArg Prod.fst hloc
        simpa [oddCoords, hpeq] using hf

/-- Exact dimension of `im(locGlobal S_fin)`: equals `|SPlaces S_fin| = |S_fin| + 1`. -/
theorem finrank_range_locGlobal (S_fin : Finset (Place ℚ)) :
    Module.finrank (ZMod 2) (LinearMap.range (locGlobal S_fin)) = (SPlaces S_fin).card := by
  rw [LinearMap.finrank_range_of_inj (locGlobal_injective S_fin), kummerSelmerQ_finrank, card_SPlaces]

/-- Helper: `unitsToZMod2` of a `Finset.prod` equals the `Finset.sum` of `unitsToZMod2`. -/
theorem unitsToZMod2_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℤˣ) :
    unitsToZMod2 (∏ i ∈ s, f i) = ∑ i ∈ s, unitsToZMod2 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, unitsToZMod2_mul, ih]

/-- **Concrete Global Reciprocity Isotropy (`im(loc) ≤ im(loc)^⊥`)**:
for every `S_fin` containing `twoPlace` and all `x, y ∈ im(locGlobal S_fin)`,
`(globalProductPairing S_fin).pair x y = 0` — proved DIRECTLY from `hilbert_reciprocity`! -/
theorem locGlobal_totally_isotropic {S_fin : Finset (Place ℚ)} (h2 : twoPlace ∈ S_fin)
    {x y : ∀ v : SPlaces S_fin, LocalH1 v.1}
    (hx : x ∈ LinearMap.range (locGlobal S_fin))
    (hy : y ∈ LinearMap.range (locGlobal S_fin)) :
    (globalProductPairing S_fin).pair x y = 0 := by
  obtain ⟨⟨qx, hqx⟩, rfl⟩ := hx
  obtain ⟨⟨qy, hqy⟩, rfl⟩ := hy
  induction qx using QuotientGroup.induction_on with
  | H a =>
    induction qy using QuotientGroup.induction_on with
    | H b =>
      change ∑ v : SPlaces S_fin,
        (localPairingAt v.1).pair (locAt v.1 a) (locAt v.1 b) = 0
      have hsum :
          (∑ v : SPlaces S_fin, (localPairingAt v.1).pair (locAt v.1 a) (locAt v.1 b)) =
            ∑ v ∈ SPlaces S_fin, unitsToZMod2 (hilbertSymAt v a b) := by
        rw [← Finset.sum_attach (SPlaces S_fin) (fun v => unitsToZMod2 (hilbertSymAt v a b))]
        refine Finset.sum_congr rfl fun v _ => localPairingAt_locAt v.1 a b
      rw [hsum, ← unitsToZMod2_finset_prod, unitsToZMod2_eq_zero_iff]
      let S_rest : Finset QPlace := ((SPlaces S_fin).erase QPlace.inf).erase QPlace.two
      have hinf_mem : QPlace.inf ∈ SPlaces S_fin := mem_SPlaces_inf S_fin
      have htwo_mem : QPlace.two ∈ (SPlaces S_fin).erase QPlace.inf :=
        Finset.mem_erase.mpr ⟨by simp, mem_SPlaces_two h2⟩
      have hprod1 := Finset.mul_prod_erase (SPlaces S_fin) (fun v => hilbertSymAt v a b) hinf_mem
      have hprod2 := Finset.mul_prod_erase ((SPlaces S_fin).erase QPlace.inf)
        (fun v => hilbertSymAt v a b) htwo_mem
      rw [← hprod1, ← hprod2]
      change hilbertSymInf a b * (hilbertSymTwo a b * ∏ v ∈ S_rest, hilbertSymAt v a b) = 1
      let S_odd : Finset OddPrime :=
        S_fin.attach.biUnion fun v =>
          if h : (Rat.HeightOneSpectrum.primesEquiv v.1).1 = 2 then ∅
          else {⟨(Rat.HeightOneSpectrum.primesEquiv v.1).1,
            (Rat.HeightOneSpectrum.primesEquiv v.1).2, h⟩}
      have hSrest_eq : S_rest = S_odd.image QPlace.odd := by
        ext q
        simp only [S_rest, S_odd, Finset.mem_erase, SPlaces, Finset.mem_insert, Finset.mem_image,
          Finset.mem_biUnion, Finset.mem_attach, true_and]
        constructor
        · rintro ⟨hq2, hqinf, hq_or⟩
          rcases hq_or with rfl | ⟨v, hv, rfl⟩
          · exact absurd rfl hqinf
          · unfold placeToQPlace at hq2 ⊢
            dsimp only at hq2 ⊢
            split_ifs at hq2 ⊢ with hp2
            · exact absurd rfl hq2
            · refine ⟨⟨(Rat.HeightOneSpectrum.primesEquiv v).1,
                (Rat.HeightOneSpectrum.primesEquiv v).2, hp2⟩, ?_, rfl⟩
              exact ⟨⟨v, hv⟩, by simp [hp2]⟩
        · rintro ⟨p, ⟨⟨v, hv⟩, hpv⟩, rfl⟩
          refine ⟨by simp, by simp, Or.inr ⟨v, hv, ?_⟩⟩
          split_ifs at hpv with hp2
          · simp at hpv
          · simp only [Finset.mem_singleton] at hpv
            unfold placeToQPlace
            simp [hp2, hpv]
      have hodd_prod : (∏ v ∈ S_rest, hilbertSymAt v a b) =
          ∏ p ∈ S_odd, hilbertSymOdd p.1 p.2.1 p.2.2 a b := by
        rw [hSrest_eq, Finset.prod_image (fun _ _ _ _ h => QPlace.odd.inj h)]
        rfl
      have hsupp :
          (Function.mulSupport fun p : OddPrime => hilbertSymOdd p.1 p.2.1 p.2.2 a b) ⊆
            (S_odd : Set OddPrime) := by
        intro p hp
        rw [Function.mem_mulSupport] at hp
        by_contra hpnot
        let v : Place ℚ := (Rat.HeightOneSpectrum.primesEquiv (R := OK ℚ)).symm ⟨p.1, p.2.1⟩
        have hv1 : (Rat.HeightOneSpectrum.primesEquiv (R := OK ℚ) v).1 = p.1 :=
          congrArg Subtype.val
            (Equiv.apply_symm_apply (Rat.HeightOneSpectrum.primesEquiv (R := OK ℚ)) ⟨p.1, p.2.1⟩)
        have hv_not : v ∉ S_fin := by
          intro hv
          apply hpnot
          simp only [Finset.mem_coe, S_odd, Finset.mem_biUnion, Finset.mem_attach, true_and]
          refine ⟨⟨v, hv⟩, ?_⟩
          have hvne : (Rat.HeightOneSpectrum.primesEquiv (R := OK ℚ) v).1 ≠ 2 := by
            rw [hv1]; exact p.2.2
          simp only [dif_neg hvne, Finset.mem_singleton]
          exact Subtype.ext hv1.symm
        have ha_even : (2 : ℤ) ∣ padicValRat p.1 (a : ℚ) := by
          have h := (mem_kummerSelmer_iff ℚ S_fin 2 a).mp hqx v hv_not
          rw [adicVal_rat_eq_padicValRat v a, hv1] at h
          exact h
        have hb_even : (2 : ℤ) ∣ padicValRat p.1 (b : ℚ) := by
          have h := (mem_kummerSelmer_iff ℚ S_fin 2 b).mp hqy v hv_not
          rw [adicVal_rat_eq_padicValRat v b, hv1] at h
          exact h
        exact hp (hilbertSymOdd_eq_one_of_even_val p.1 p.2.1 p.2.2 ha_even hb_even)
      rw [hodd_prod, ← finprod_eq_prod_of_mulSupport_subset _ hsupp, ← mul_assoc]
      exact hilbert_reciprocity a b

/-- **CONCRETE GLOBAL POITOU–TATE SELF-ORTHOGONALITY THEOREM FOR `K = ℚ, m = 2`** (ZERO ASSUMPTIONS!):
for EVERY finite set of finite places `S_fin` containing `2` (so `S = {∞} ∪ S_fin ⊇ {2, ∞}`):
1. `im(loc) = im(loc)^⊥` under the concrete `Stage2GaloisCohomology.LocalDualityPairing` on `∏_{v ∈ S} H¹(ℚ_v, μ₂)`,
2. `dim_{𝔽₂}(im loc) = |S| = (1/2) dim_{𝔽₂}(∏_{v ∈ S} H¹(ℚ_v, μ₂))`,
3. `ker(loc) = ⊥` (`Ш¹_S(ℚ, μ₂) = 0`)! -/
theorem poitou_tate_self_orthogonal_Q {S_fin : Finset (Place ℚ)} (h2 : twoPlace ∈ S_fin) :
    LinearMap.range (locGlobal S_fin) =
        (globalProductPairing S_fin).ortho (LinearMap.range (locGlobal S_fin)) ∧
      Module.finrank (ZMod 2) (LinearMap.range (locGlobal S_fin)) = (SPlaces S_fin).card ∧
      Module.finrank (ZMod 2) (∀ v : SPlaces S_fin, LocalH1 v.1) = 2 * (SPlaces S_fin).card ∧
      LinearMap.ker (locGlobal S_fin) = ⊥ := by
  have hle : LinearMap.range (locGlobal S_fin) ≤
      (globalProductPairing S_fin).ortho (LinearMap.range (locGlobal S_fin)) := by
    intro y hy x hx
    exact locGlobal_totally_isotropic h2 hx hy
  have hdim_range : Module.finrank (ZMod 2) (LinearMap.range (locGlobal S_fin)) =
      (SPlaces S_fin).card := finrank_range_locGlobal S_fin
  have hdim_amb : Module.finrank (ZMod 2) (∀ v : SPlaces S_fin, LocalH1 v.1) =
      2 * (SPlaces S_fin).card := finrank_prodLocalH1 h2
  have hortho_add := (globalProductPairing S_fin).ortho_finrank_add (LinearMap.range (locGlobal S_fin))
  have hdim_eq : Module.finrank (ZMod 2) (LinearMap.range (locGlobal S_fin)) =
      Module.finrank (ZMod 2) ((globalProductPairing S_fin).ortho (LinearMap.range (locGlobal S_fin))) := by
    omega
  refine ⟨Submodule.eq_of_le_of_finrank_eq hle hdim_eq, hdim_range, hdim_amb,
    LinearMap.ker_eq_bot.mpr (locGlobal_injective S_fin)⟩

/-! ### 5D. Hasse–Minkowski Binary Norm Corollaries & Even Ramification Law -/

theorem hilbertSymAt_mul_left (v : QPlace) (a₁ a₂ b : ℚˣ) :
    hilbertSymAt v (a₁ * a₂) b = hilbertSymAt v a₁ b * hilbertSymAt v a₂ b := by
  cases v with
  | inf => exact hilbertSymInf_mul_left a₁ a₂ b
  | two => exact hilbertSymTwo_mul_left a₁ a₂ b
  | odd p => exact hilbertSymOdd_mul_left p.1 p.2.1 p.2.2 a₁ a₂ b

theorem hilbertSymAt_mul_right (v : QPlace) (a b₁ b₂ : ℚˣ) :
    hilbertSymAt v a (b₁ * b₂) = hilbertSymAt v a b₁ * hilbertSymAt v a b₂ := by
  cases v with
  | inf => exact hilbertSymInf_mul_right a b₁ b₂
  | two => exact hilbertSymTwo_mul_right a b₁ b₂
  | odd p => exact hilbertSymOdd_mul_right p.1 p.2.1 p.2.2 a b₁ b₂

theorem hilbertSymAt_sq_left (v : QPlace) (a b : ℚˣ) : hilbertSymAt v (a ^ 2) b = 1 := by
  rw [sq, hilbertSymAt_mul_left, intUnits_mul_self]

theorem hilbertSymAt_sq_right (v : QPlace) (a b : ℚˣ) : hilbertSymAt v a (b ^ 2) = 1 := by
  rw [sq, hilbertSymAt_mul_right, intUnits_mul_self]

theorem hilbertSymAt_self_neg (v : QPlace) (a : ℚˣ) : hilbertSymAt v a (-a) = 1 := by
  cases v with
  | inf => exact hilbertSymInf_self_neg a
  | two => exact hilbertSymTwo_self_neg a
  | odd p => exact hilbertSymOdd_self_neg p.1 p.2.1 p.2.2 a

theorem hilbertSymAt_steinberg (v : QPlace) (a b : ℚˣ) (hab : (b : ℚ) = 1 - (a : ℚ)) :
    hilbertSymAt v a b = 1 := by
  cases v with
  | inf => exact hilbertSymInf_steinberg a b hab
  | two => exact hilbertSymTwo_steinberg a b hab
  | odd p => exact hilbertSymOdd_steinberg p.1 p.2.1 p.2.2 a b hab

/-- **Hasse–Minkowski Binary Norm Corollary**:
if `b` is a norm from `ℚ(√a)` (`b = x² - a y²` for some `x, y ∈ ℚ`), then `(a, b)_v = 1`
at EVERY place `v` of `ℚ` (`∞`, `2`, and every odd prime `p`)! -/
theorem hilbertSymAt_eq_one_of_binary_norm {a b : ℚˣ}
    (hnorm : ∃ x y : ℚ, (b : ℚ) = x ^ 2 - (a : ℚ) * y ^ 2) (v : QPlace) :
    hilbertSymAt v a b = 1 := by
  obtain ⟨x, y, hxy⟩ := hnorm
  by_cases hy : y = 0
  · subst hy
    have hx : x ≠ 0 := by
      intro hx0
      rw [hx0] at hxy
      simp at hxy
    have hbeq : b = (Units.mk0 x hx) ^ 2 := Units.ext (by simpa [sq] using hxy)
    rw [hbeq]
    exact hilbertSymAt_sq_right v a _
  · by_cases hx : x = 0
    · subst hx
      have hbeq : b = (-a) * (Units.mk0 y hy) ^ 2 :=
        Units.ext (by simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val,
          Units.val_mk0]; linarith)
      rw [hbeq, hilbertSymAt_mul_right, hilbertSymAt_self_neg, hilbertSymAt_sq_right, mul_one]
    · let ux : ℚˣ := Units.mk0 x hx
      let uy : ℚˣ := Units.mk0 y hy
      let c : ℚˣ := a * (uy * ux⁻¹) ^ 2
      let d : ℚˣ := b * (ux⁻¹) ^ 2
      have hcd : (d : ℚ) = 1 - (c : ℚ) := by
        simp only [c, d, ux, uy, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
          Units.val_mk0, hxy]
        field_simp [hx]
      have h1 : hilbertSymAt v c d = hilbertSymAt v a b := by
        dsimp only [c, d]
        rw [hilbertSymAt_mul_left, hilbertSymAt_sq_left, mul_one,
          hilbertSymAt_mul_right, hilbertSymAt_sq_right, mul_one]
      rw [← h1]
      exact hilbertSymAt_steinberg v c d hcd

/-- **Local Obstruction Corollary**: a single place `v` with `(a, b)_v = -1` obstructs global
representability `b = x² - a y²` over `ℚ`! -/
theorem not_binary_norm_of_local_obstruction {a b : ℚˣ}
    (hobs : ∃ v : QPlace, hilbertSymAt v a b = -1) :
    ¬ ∃ x y : ℚ, (b : ℚ) = x ^ 2 - (a : ℚ) * y ^ 2 := by
  intro hnorm
  obtain ⟨v, hv⟩ := hobs
  have h1 := hilbertSymAt_eq_one_of_binary_norm hnorm v
  rw [h1] at hv
  exact (by decide : (1 : ℤˣ) ≠ -1) hv

/-- **Hilbert Reciprocity Single-Place Corollary**:
if `(a, b)_v = 1` at EVERY place `v ≠ v₀`, then `(a, b)_{v₀} = 1` as well! -/
theorem hilbertSymAt_eq_one_of_others_eq_one {a b : ℚˣ} (v₀ : QPlace)
    (h : ∀ v : QPlace, v ≠ v₀ → hilbertSymAt v a b = 1) :
    hilbertSymAt v₀ a b = 1 := by
  have hrec := hilbert_reciprocity a b
  cases v₀ with
  | inf =>
    have h2 : hilbertSymTwo a b = 1 := h QPlace.two (by simp)
    have hodd : (∏ᶠ p : OddPrime, hilbertSymOdd p.1 p.2.1 p.2.2 a b) = 1 := by
      rw [finprod_eq_one_of_forall_eq_one]
      intro p
      exact h (QPlace.odd p) (by simp)
    change hilbertSymInf a b = 1
    simpa [h2, hodd] using hrec
  | two =>
    have hinf : hilbertSymInf a b = 1 := h QPlace.inf (by simp)
    have hodd : (∏ᶠ p : OddPrime, hilbertSymOdd p.1 p.2.1 p.2.2 a b) = 1 := by
      rw [finprod_eq_one_of_forall_eq_one]
      intro p
      exact h (QPlace.odd p) (by simp)
    change hilbertSymTwo a b = 1
    simpa [hinf, hodd] using hrec
  | odd p₀ =>
    have hinf : hilbertSymInf a b = 1 := h QPlace.inf (by simp)
    have h2 : hilbertSymTwo a b = 1 := h QPlace.two (by simp)
    have hodd : (∏ᶠ p : OddPrime, hilbertSymOdd p.1 p.2.1 p.2.2 a b) =
        hilbertSymOdd p₀.1 p₀.2.1 p₀.2.2 a b := by
      rw [finprod_eq_single _ p₀]
      intro p hp
      exact h (QPlace.odd p) (fun heq => hp (QPlace.odd.inj heq))
    change hilbertSymOdd p₀.1 p₀.2.1 p₀.2.2 a b = 1
    simpa [hinf, h2, hodd] using hrec

/-- **Hilbert Reciprocity Even-Ramification Law**: for EVERY `a, b ∈ ℚˣ`, the finite set of places
`v : QPlace` where `(a, b)_v = -1` has EVEN cardinality! -/
theorem even_ramified_places (a b : ℚˣ) :
    ∃ (R : Finset QPlace), (∀ v : QPlace, v ∈ R ↔ hilbertSymAt v a b = -1) ∧ Even R.card := by
  classical
  let sOdd : Finset OddPrime := (hasFiniteMulSupport_hilbertSym a b).toFinset
  let R : Finset QPlace :=
    (insert QPlace.inf (insert QPlace.two (sOdd.image QPlace.odd))).filter
      (fun v => hilbertSymAt v a b = -1)
  have hmem : ∀ v : QPlace, v ∈ R ↔ hilbertSymAt v a b = -1 := by
    intro v
    simp only [R, Finset.mem_filter, Finset.mem_insert, Finset.mem_image,
      Set.Finite.mem_toFinset, Function.mem_mulSupport, sOdd]
    constructor
    · exact fun h => h.2
    · intro hv
      refine ⟨?_, hv⟩
      cases v with
      | inf => exact Or.inl rfl
      | two => exact Or.inr (Or.inl rfl)
      | odd p =>
        refine Or.inr (Or.inr ⟨p, ?_, rfl⟩)
        change hilbertSymOdd p.1 p.2.1 p.2.2 a b = -1 at hv
        rw [hv]
        decide
  have hprod : (∏ v ∈ R, hilbertSymAt v a b) = 1 := by
    let U : Finset QPlace := insert QPlace.inf (insert QPlace.two (sOdd.image QPlace.odd))
    have hU : (∏ v ∈ U, hilbertSymAt v a b) = ∏ v ∈ R, hilbertSymAt v a b := by
      rw [Finset.prod_filter]
      refine Finset.prod_congr rfl fun v _ => ?_
      rcases intUnits_eq_one_or_neg_one (hilbertSymAt v a b) with h1 | h1 <;> simp [h1]
    rw [← hU]
    have hinf_not : QPlace.inf ∉ insert QPlace.two (sOdd.image QPlace.odd) := by simp
    have htwo_not : QPlace.two ∉ sOdd.image QPlace.odd := by simp
    dsimp only [U]
    rw [Finset.prod_insert hinf_not, Finset.prod_insert htwo_not,
      Finset.prod_image (fun _ _ _ _ h => QPlace.odd.inj h), ← mul_assoc]
    have hfp : (∏ p ∈ sOdd, hilbertSymAt (QPlace.odd p) a b) =
        ∏ᶠ p : OddPrime, hilbertSymOdd p.1 p.2.1 p.2.2 a b := by
      symm
      exact finprod_eq_prod_of_mulSupport_subset _ (by
        intro p hp
        exact (Set.Finite.mem_toFinset _).mpr hp)
    rw [hfp]
    exact hilbert_reciprocity a b
  have hneg_pow : (-1 : ℤˣ) ^ R.card = 1 := by
    calc (-1 : ℤˣ) ^ R.card = ∏ _v ∈ R, (-1 : ℤˣ) := by simp
      _ = ∏ v ∈ R, hilbertSymAt v a b :=
        Finset.prod_congr rfl fun v hv => ((hmem v).mp hv).symm
      _ = 1 := hprod
  have hzmod : (R.card : ZMod 2) = 0 := by
    have h1 := congrArg unitsToZMod2 hneg_pow
    rw [← negOnePowZMod2_natCast, unitsToZMod2_negOnePowZMod2, unitsToZMod2_one] at h1
    exact h1
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff R.card 2).mp hzmod
  exact ⟨R, hmem, ⟨k, by omega⟩⟩

/-- Concrete Hasse–Minkowski arithmetic witness: `3` is NOT a sum of two rational squares,
proved directly from the `2`-adic Hilbert symbol `(-1, 3)_2 = -1`! -/
theorem not_sum_two_squares_three : ¬ ∃ x y : ℚ, (3 : ℚ) = x ^ 2 + y ^ 2 := by
  intro ⟨x, y, hxy⟩
  have hp3 : Nat.Prime 3 := by decide
  have hnorm : ∃ x y : ℚ, ((primeUnit 3 hp3 : ℚˣ) : ℚ) =
      x ^ 2 - ((-1 : ℚˣ) : ℚ) * y ^ 2 :=
    ⟨x, y, by simp [coe_primeUnit]; linarith⟩
  have hobs : hilbertSymAt QPlace.two (-1) (primeUnit 3 hp3) = -1 := by
    change hilbertSymTwo (-1) (primeUnit 3 hp3) = -1
    unfold hilbertSymTwo
    rw [twoCoords_neg_one, twoCoords_oddPrime hp3 (by decide)]
    decide
  exact not_binary_norm_of_local_obstruction ⟨QPlace.two, hobs⟩ hnorm

end GlobalPoitouTateQ

end

end RHDirect.Stage7GlobalDuality
