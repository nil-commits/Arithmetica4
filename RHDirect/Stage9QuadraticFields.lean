import RHDirect.Stage6ClassNumberFormula
import RHDirect.Stage7DedekindZeta
import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.Zsqrtd.ToReal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.RingTheory.Conductor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# RHDirect.Stage9QuadraticFields

Unconditional (0 `sorry`, 0 custom `axiom`, 0 errors, 0 warnings, 0 info) formalization of
**Real Quadratic Number Fields, Exact Closed-Form `L(1, χ_d)` via Cyclotomic Units, Pell's
Equation & Fundamental Unit Structure, Quadratic Dedekind Zeta Factorization, & Concrete
Class-Number-One Verifications** in pure Mathlib `v4.33.1`:

1. **Exact Closed-Form Value of `L(1, χ)` for Every Even Primitive Real Character (`0` Assumptions)**:
   - `LFunction_one_even_real_eq_log_sin`:
     `(LFunction χ 1).re = -(1 / √q) * ∑_{a=1}^{q-1} (χ a).re * log(2 sin(π a / q))`.
   - `LFunction_one_even_real_eq_half_log_sin`:
     `(LFunction χ 1).re = -(2 / √q) * ∑_{a=1}^{⌊q/2⌋} (χ a).re * log(sin(π a / q))`.
   - `LFunction_one_even_real_eq_log_cyclotomic_ratio`:
     `√q * (LFunction χ 1).re = log(∏_{χ(a) = -1} (2 sin(π a / q)) / ∏_{χ(a) = 1} (2 sin(π a / q)))`.
   - Concrete closed forms for `q = 5` (`χ₅`, `ℚ(√5)`), `q = 8` (`χ₈`, `ℚ(√2)`), and
     `q = 12` (`χ₁₂`, `ℚ(√3)`):
     - `L(1, χ₅) = (2 / √5) * log ((1 + √5) / 2)`
     - `L(1, χ₈) = (1 / √2) * log (1 + √2)`
     - `L(1, χ₁₂) = (1 / √3) * log (2 + √3)`
2. **Concrete Pell Equation, Fundamental Unit Structure of `(Zsqrtd d)ˣ`, & Pell Regulator**:
   - Exact fundamental norm-`+1` Pell solution `fundamentalPellSol₁ d` and exact fundamental unit
     `fundamentalPellUnit d : (Zsqrtd d)ˣ` with `1 < Zsqrtd.toReal _ (ε_d : Zsqrtd d)`.
   - Exact group isomorphism `zsqrtd_units_equiv_int : (Zsqrtd d)ˣ ≃* Multiplicative (ZMod 2) × Multiplicative ℤ`
     (every unit is uniquely `± ε_d^k` for `k : ℤ`).
   - Concrete Pell regulator `pellRegulator d := Real.log (Zsqrtd.toReal _ ε_d)` with
     `0 < pellRegulator d`.
   - Explicit computations for `d = 2` (`1 + √2` norm `-1`, `3 + 2√2` norm `+1`),
     `d = 3` (`2 + √3` norm `+1`, no norm-`-1` unit), `d = 5` (`2 + √5` norm `-1`, `9 + 4√5` norm `+1`),
     and the maximal order `ℤ[(1 + √5)/2] = QuadraticAlgebra ℤ 1 1` with golden ratio fundamental
     unit `(1 + √5)/2`.
3. **Real Quadratic Number Fields `QuadField d = ℚ(√d)`, Ring of Integers `𝓞 (QuadField d)`,
   Exact Discriminant `fundDisc d`, & Minkowski Class-Number-One Criterion**:
   - Concrete `NumberField (QuadField d)` with `[QuadField d : ℚ] = 2`, totally real (`r₂ = 0`),
     explicit monogenic `ℤ`-basis `𝓞 (QuadField d) = ℤ[ω_d]`, and `NumberField.discr (QuadField d) = fundDisc d`.
   - Minkowski class-number-one theorem for every real quadratic field with `fundDisc d < 16`,
     yielding `NumberField.classNumber (QuadField d) = 1` for `d = 5, 2, 3, 13`.
4. **Kronecker Character `χ_D`, Exact Prime-Ideal Splitting via Kummer–Dedekind, Exact Dedekind
   Zeta Factorization `ζ_{ℚ(√d)}(s) = ζ(s) · L(s, χ_D)`, & Residue at `s = 1`**:
   - Exact local Euler factor matching at every prime `p` (split, inert, and ramified, including `p = 2`).
   - Exact global factorization `dedekindZeta (QuadField d) s = riemannZeta s * LFunction (kroneckerChar d) s`
     on `1 < s.re` and exact residue `lim_{s → 1⁺} (s - 1) ζ_{ℚ(√d)}(s) = L(1, χ_D)`.
5. **Concrete Real Quadratic Class Number Formula Identities (`2 h(D) log ε_D = √D L(1, χ_D)`)**:
   - Unconditional verification for `ℚ(√5)`, `ℚ(√2)`, and `ℚ(√3)`.
-/

noncomputable section

open Complex DirichletCharacter Finset Filter Topology IsDedekindDomain
open RHDirect.Stage6ClassNumberFormula RHDirect.Stage7DedekindZeta
open scoped BigOperators NumberField

namespace RHDirect.Stage9QuadraticFields

/-! ## Section 1: Exact Closed-Form `L(1, χ)` for Every Even Primitive Real Character -/

section EvenRealLFunction

/-- Helper: any non-principal Dirichlet character mod `q` has modulus `q ≥ 3`. -/
theorem three_le_of_dirichletChar_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : 3 ≤ q := by
  have hq0 : 0 < q := NeZero.pos q
  by_contra hlt
  have h12 : q = 1 ∨ q = 2 := by omega
  rcases h12 with rfl | rfl
  · exact hχ (DirichletCharacter.level_one χ)
  · apply hχ
    ext u
    have hu : u = 1 := by
      apply Units.ext
      have hlt2 : (u : ZMod 2).val < 2 := ZMod.val_lt _
      have hne0 : (u : ZMod 2) ≠ 0 := u.ne_zero
      have hv01 : (u : ZMod 2).val = 0 ∨ (u : ZMod 2).val = 1 := by omega
      have hv1 : (u : ZMod 2).val = 1 := by
        rcases hv01 with h0 | h1
        · exfalso
          apply hne0
          rw [← ZMod.natCast_zmod_val (u : ZMod 2), h0]
          simp
        · exact h1
      rw [← ZMod.natCast_zmod_val (u : ZMod 2), hv1]
      rfl
    rw [hu, Units.val_one, map_one, map_one]

/-- Helper: for any real Dirichlet character `χ` mod `q` and any `a : ZMod q`,
`χ a = ((χ a).re : ℂ)`. -/
lemma char_eq_ofReal_re {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (a : ZMod q) :
    χ a = ((χ a).re : ℂ) :=
  Complex.ext (by simp) (by simpa using hreal a)

/-- Helper: for a real Dirichlet character `χ` mod `q` and unit `u : (ZMod q)ˣ`,
`χ u = 1 ∨ χ u = -1`. -/
lemma real_char_unit_eq_one_or_neg_one' {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (u : (ZMod q)ˣ) :
    χ (u : ZMod q) = 1 ∨ χ (u : ZMod q) = -1 := by
  have hpow : χ (u : ZMod q) ^ Fintype.card (ZMod q)ˣ = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have hre_pow : (χ (u : ZMod q)).re ^ Fintype.card (ZMod q)ˣ = 1 := by
    have h := congrArg Complex.re hpow
    rw [char_eq_ofReal_re hreal (u : ZMod q), ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.one_re] at h
    exact h
  have habs_pow : |(χ (u : ZMod q)).re| ^ Fintype.card (ZMod q)ˣ = 1 := by
    rw [← abs_pow, hre_pow, abs_one]
  have habs : |(χ (u : ZMod q)).re| = 1 := by
    by_contra hne
    have hpos : 0 < Fintype.card (ZMod q)ˣ := Fintype.card_pos
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : |(χ (u : ZMod q)).re| ^ Fintype.card (ZMod q)ˣ < 1 :=
        pow_lt_one₀ (abs_nonneg _) hlt hpos.ne'
      linarith
    · have : 1 < |(χ (u : ZMod q)).re| ^ Fintype.card (ZMod q)ˣ :=
        one_lt_pow₀ hgt hpos.ne'
      linarith
  rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp habs with h1 | hm1
  · left; exact Complex.ext (by simpa using h1) (by simpa using hreal _)
  · right; exact Complex.ext (by simpa using hm1) (by simpa using hreal _)

/-- Helper: for a real Dirichlet character `χ` mod `q`, every value `χ a` is `0`, `1`, or `-1`. -/
lemma real_char_eq_zero_or_one_or_neg_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (a : ZMod q) :
    χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by
  by_cases hu : IsUnit a
  · right
    simpa [IsUnit.unit_spec] using real_char_unit_eq_one_or_neg_one' hreal hu.unit
  · left
    exact MulChar.map_nonunit χ hu

/-- **Exact Closed-Form Value of `L(1, χ)` for Every Even Primitive Real Character (`0` Assumptions)**:
`(LFunction χ 1).re = -(1 / √q) * ∑_{a=1}^{q-1} (χ a).re * log(2 sin(π a / q))`. -/
theorem LFunction_one_even_real_eq_log_sin {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (heven : χ.Even)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    (DirichletCharacter.LFunction χ 1).re =
      -(1 / Real.sqrt (q : ℝ)) *
        ∑ a ∈ Finset.Ico 1 q,
          (χ (a : ZMod q)).re * Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hsqrt_pos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq_pos
  have hL := LFunction_one_eq_even hprim hχ heven
  have hgauss : gaussSum χ ZMod.stdAddChar = (Real.sqrt (q : ℝ) : ℂ) := by
    have h := gaussSum_real_primitive_eq hprim hreal
    rwa [if_pos heven, one_mul] at h
  rw [hgauss, dirichletChar_inv_eq_self_of_real hreal] at hL
  have hsum_real :
      ∑ a ∈ Finset.Ico 1 q,
          χ (a : ZMod q) * (Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) : ℂ) =
        ((∑ a ∈ Finset.Ico 1 q,
          (χ (a : ZMod q)).re * Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [char_eq_ofReal_re hreal]
    push_cast
    rfl
  have hre := congrArg Complex.re hL
  rw [hsum_real, show -((Real.sqrt (q : ℝ) : ℂ) / (q : ℂ)) =
    ((-(Real.sqrt (q : ℝ) / (q : ℝ)) : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_mul, Complex.ofReal_re] at hre
  have hdiv : Real.sqrt (q : ℝ) / (q : ℝ) = 1 / Real.sqrt (q : ℝ) := by
    have hsq : Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) = (q : ℝ) := Real.mul_self_sqrt hq_pos.le
    field_simp [hsqrt_pos.ne', hq_pos.ne']
    linarith
  rw [hre, hdiv]

/-- Full complex form of `LFunction_one_even_real_eq_log_sin`. -/
theorem LFunction_one_even_real_eq_log_sin_complex {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (heven : χ.Even)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    DirichletCharacter.LFunction χ 1 =
      ((-(1 / Real.sqrt (q : ℝ)) *
        ∑ a ∈ Finset.Ico 1 q,
          (χ (a : ZMod q)).re * Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
    exact LFunction_one_even_real_eq_log_sin hprim hχ heven hreal
  · rw [Complex.ofReal_im]
    exact (LFunction_one_pos_of_real χ hχ hreal).2

/-- Helper: for any `q ≥ 3`, any even `χ mod q`, and any function `f : ℕ → ℝ` symmetric under
`a ↦ q - a` on `Ico 1 q`, `∑_{a=1}^{q-1} (χ a).re * f a = 2 * ∑_{a=1}^{q/2} (χ a).re * f a`. -/
theorem sum_even_char_Ico_eq_two_mul_Icc {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq3 : 3 ≤ q) (heven : χ.Even) (f : ℕ → ℝ)
    (hsym : ∀ a ∈ Finset.Ico 1 q, f (q - a) = f a) :
    ∑ a ∈ Finset.Ico 1 q, (χ (a : ZMod q)).re * f a =
      2 * ∑ a ∈ Finset.Icc 1 (q / 2), (χ (a : ZMod q)).re * f a := by
  have hchar_sym : ∀ a : ℕ, a ≤ q → (χ ((q - a : ℕ) : ZMod q)).re = (χ (a : ZMod q)).re := by
    intro a ha
    have hcast : ((q - a : ℕ) : ZMod q) = (-1 : ZMod q) * (a : ZMod q) := by
      rw [Nat.cast_sub ha, ZMod.natCast_self, zero_sub, neg_one_mul]
    rw [hcast, map_mul, heven, one_mul]
  have hpart : Finset.Ico 1 q = Finset.Icc 1 (q / 2) ∪ Finset.Ico (q / 2 + 1) q := by
    ext a; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 (q / 2)) (Finset.Ico (q / 2 + 1) q) := by
    rw [Finset.disjoint_left]
    intro a h1 h2; simp only [Finset.mem_Icc, Finset.mem_Ico] at h1 h2; omega
  rw [hpart, Finset.sum_union hdisj]
  rcases Nat.even_or_odd q with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk2 : 2 ≤ k := by omega
    have hdiv : q / 2 = k := by omega
    have hχ_mid : χ (k : ZMod q) = 0 := by
      refine MulChar.map_nonunit χ fun hu => ?_
      have hcop := (ZMod.isUnit_iff_coprime k q).mp hu
      have hdvd : k ∣ q := ⟨2, by omega⟩
      have hk1 : k ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hdvd
      have := Nat.le_of_dvd (by norm_num) hk1
      omega
    have hlow : ∑ a ∈ Finset.Icc 1 (q / 2), (χ (a : ZMod q)).re * f a =
        ∑ a ∈ Finset.Ico 1 k, (χ (a : ZMod q)).re * f a := by
      rw [hdiv]
      have hs : Finset.Icc 1 k = insert k (Finset.Ico 1 k) := by
        ext a; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
      have hnot : k ∉ Finset.Ico 1 k := by simp only [Finset.mem_Ico]; omega
      rw [hs, Finset.sum_insert hnot, hχ_mid, Complex.zero_re, zero_mul, zero_add]
    have hup : ∑ a ∈ Finset.Ico (q / 2 + 1) q, (χ (a : ZMod q)).re * f a =
        ∑ a ∈ Finset.Ico 1 k, (χ (a : ZMod q)).re * f a := by
      refine Finset.sum_bij (fun a _ => q - a) ?_ ?_ ?_ ?_
      · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; omega
      · intro a₁ ha₁ a₂ ha₂ h; simp only [Finset.mem_Ico] at ha₁ ha₂; omega
      · intro b hb; simp only [Finset.mem_Ico] at hb
        refine ⟨q - b, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro a ha
        have ha' : a ∈ Finset.Ico 1 q := by simp only [Finset.mem_Ico] at ha ⊢; omega
        rw [hchar_sym a (by simp only [Finset.mem_Ico] at ha; omega), hsym a ha']
    rw [hlow, hup]; ring
  · have hup : ∑ a ∈ Finset.Ico (q / 2 + 1) q, (χ (a : ZMod q)).re * f a =
        ∑ a ∈ Finset.Icc 1 (q / 2), (χ (a : ZMod q)).re * f a := by
      refine Finset.sum_bij (fun a _ => q - a) ?_ ?_ ?_ ?_
      · intro a ha; simp only [Finset.mem_Ico, Finset.mem_Icc] at ha ⊢; omega
      · intro a₁ ha₁ a₂ ha₂ h; simp only [Finset.mem_Ico] at ha₁ ha₂; omega
      · intro b hb; simp only [Finset.mem_Icc] at hb
        refine ⟨q - b, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro a ha
        have ha' : a ∈ Finset.Ico 1 q := by simp only [Finset.mem_Ico] at ha ⊢; omega
        rw [hchar_sym a (by simp only [Finset.mem_Ico] at ha; omega), hsym a ha']
    rw [hup]; ring

/-- Half-interval orthogonality: for every even non-principal `χ ≠ 1` mod `q`,
`∑_{a=1}^{⌊q/2⌋} (χ a).re = 0`. -/
theorem sum_even_char_Icc_half_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (heven : χ.Even) :
    ∑ a ∈ Finset.Icc 1 (q / 2), (χ (a : ZMod q)).re = 0 := by
  have hq3 : 3 ≤ q := three_le_of_dirichletChar_ne_one hχ
  have htot : ∑ a ∈ Finset.Ico 1 q, (χ (a : ZMod q)).re = 0 := by
    have hsum0 : ∑ x : ZMod q, χ x = 0 := MulChar.sum_eq_zero_of_ne_one hχ
    have hIco : ∑ a ∈ Finset.Ico 1 q, χ (a : ZMod q) = ∑ x : ZMod q, χ x := by
      have hrange : ∑ a ∈ Finset.range q, χ (a : ZMod q) = ∑ x : ZMod q, χ x :=
        Finset.sum_bij (fun a _ => (a : ZMod q))
          (fun _ _ => Finset.mem_univ _)
          (fun a₁ ha₁ a₂ ha₂ h => by
            have := congrArg ZMod.val h
            rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha₁),
              ZMod.val_natCast_of_lt (Finset.mem_range.mp ha₂)] at this
            exact this)
          (fun x _ => ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩)
          (fun _ _ => rfl)
      rw [← hrange]
      have hsplit : Finset.range q = insert 0 (Finset.Ico 1 q) := by
        ext a; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
      rw [hsplit, Finset.sum_insert (by simp), Nat.cast_zero, χ.map_zero' (by omega), zero_add]
    have hre := congrArg Complex.re (hIco.trans hsum0)
    simpa [Complex.re_sum] using hre
  have h2 := sum_even_char_Ico_eq_two_mul_Icc (χ := χ) hq3 heven (fun _ => (1 : ℝ)) (fun _ _ => rfl)
  simp only [mul_one] at h2
  linarith

/-- **Half-Interval Exact Closed-Form Value of `L(1, χ)` for Every Even Primitive Real Character**:
`(LFunction χ 1).re = -(2 / √q) * ∑_{a=1}^{⌊q/2⌋} (χ a).re * log(sin(π a / q))`. -/
theorem LFunction_one_even_real_eq_half_log_sin {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (heven : χ.Even)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    (DirichletCharacter.LFunction χ 1).re =
      -(2 / Real.sqrt (q : ℝ)) *
        ∑ a ∈ Finset.Icc 1 (q / 2),
          (χ (a : ZMod q)).re * Real.log (Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) := by
  have hq3 : 3 ≤ q := three_le_of_dirichletChar_ne_one hχ
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  rw [LFunction_one_even_real_eq_log_sin hprim hχ heven hreal]
  have hsym : ∀ a ∈ Finset.Ico 1 q,
      Real.log (2 * Real.sin (Real.pi * ((q - a : ℕ) : ℝ) / (q : ℝ))) =
        Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) := by
    intro a ha
    have ha' := Finset.mem_Ico.mp ha
    have harg : Real.pi * ((q - a : ℕ) : ℝ) / (q : ℝ) = Real.pi - Real.pi * (a : ℝ) / (q : ℝ) := by
      rw [Nat.cast_sub ha'.2.le]
      field_simp [hq_pos.ne']
    rw [harg, Real.sin_pi_sub]
  rw [sum_even_char_Ico_eq_two_mul_Icc (χ := χ) hq3 heven _ hsym]
  have hlog2 :
      ∑ a ∈ Finset.Icc 1 (q / 2),
          (χ (a : ZMod q)).re * Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) =
        ∑ a ∈ Finset.Icc 1 (q / 2),
          (χ (a : ZMod q)).re * Real.log (Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) := by
    have hsplit :
        ∑ a ∈ Finset.Icc 1 (q / 2),
            (χ (a : ZMod q)).re * Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) =
          (∑ a ∈ Finset.Icc 1 (q / 2), (χ (a : ZMod q)).re) * Real.log 2 +
            ∑ a ∈ Finset.Icc 1 (q / 2),
              (χ (a : ZMod q)).re * Real.log (Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha' := Finset.mem_Icc.mp ha
      have hsin_pos : 0 < Real.sin (Real.pi * (a : ℝ) / (q : ℝ)) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · have ha_pos : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr (by omega)
          positivity
        · have ha_lt : (a : ℝ) < (q : ℝ) := Nat.cast_lt.mpr (by omega)
          rw [div_lt_iff₀ hq_pos]
          nlinarith [Real.pi_pos]
      rw [Real.log_mul (by norm_num) hsin_pos.ne']
      ring
    rw [hsplit, sum_even_char_Icc_half_eq_zero hχ heven, zero_mul, zero_add]
  rw [hlog2]
  ring

open Classical in
/-- **Exact Cyclotomic Unit Product Formula for Every Even Primitive Real Character**:
`√q * (LFunction χ 1).re = log(∏_{χ(a) = -1} (2 sin(π a / q)) / ∏_{χ(a) = 1} (2 sin(π a / q)))`. -/
theorem LFunction_one_even_real_eq_log_cyclotomic_ratio {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (heven : χ.Even)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    Real.sqrt (q : ℝ) * (DirichletCharacter.LFunction χ 1).re =
      Real.log
        ((∏ a ∈ (Finset.Ico 1 q).filter (fun a : ℕ => χ (a : ZMod q) = -1),
            (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))) /
         (∏ a ∈ (Finset.Ico 1 q).filter (fun a : ℕ => χ (a : ZMod q) = 1),
            (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))))) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hsqrt_pos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq_pos
  have hsin_pos : ∀ a ∈ Finset.Ico 1 q, 0 < 2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ)) := by
    intro a ha
    have ha' := Finset.mem_Ico.mp ha
    have h1 : 0 < Real.pi * (a : ℝ) / (q : ℝ) := by
      have ha_pos : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr (by omega)
      positivity
    have h2 : Real.pi * (a : ℝ) / (q : ℝ) < Real.pi := by
      have ha_lt : (a : ℝ) < (q : ℝ) := Nat.cast_lt.mpr ha'.2
      rw [div_lt_iff₀ hq_pos]
      nlinarith [Real.pi_pos]
    exact mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  have hprod_neg_pos :
      0 < ∏ a ∈ (Finset.Ico 1 q).filter (fun a : ℕ => χ (a : ZMod q) = -1),
            (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) :=
    Finset.prod_pos fun a ha => hsin_pos a (Finset.mem_filter.mp ha).1
  have hprod_pos_pos :
      0 < ∏ a ∈ (Finset.Ico 1 q).filter (fun a : ℕ => χ (a : ZMod q) = 1),
            (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) :=
    Finset.prod_pos fun a ha => hsin_pos a (Finset.mem_filter.mp ha).1
  rw [Real.log_div hprod_neg_pos.ne' hprod_pos_pos.ne',
    Real.log_prod (fun a ha => (hsin_pos a (Finset.mem_filter.mp ha).1).ne'),
    Real.log_prod (fun a ha => (hsin_pos a (Finset.mem_filter.mp ha).1).ne')]
  rw [LFunction_one_even_real_eq_log_sin hprim hχ heven hreal]
  have hmul :
      Real.sqrt (q : ℝ) * (-(1 / Real.sqrt (q : ℝ)) *
        ∑ a ∈ Finset.Ico 1 q,
          (χ (a : ZMod q)).re * Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))) =
      -∑ a ∈ Finset.Ico 1 q,
          (χ (a : ZMod q)).re * Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) := by
    field_simp [hsqrt_pos.ne']
  rw [hmul]
  have hsplit :
      ∑ a ∈ Finset.Ico 1 q,
          (χ (a : ZMod q)).re * Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) =
        (∑ a ∈ (Finset.Ico 1 q).filter (fun a : ℕ => χ (a : ZMod q) = 1),
            Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))) -
        (∑ a ∈ (Finset.Ico 1 q).filter (fun a : ℕ => χ (a : ZMod q) = -1),
            Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rcases real_char_eq_zero_or_one_or_neg_one hreal (a : ZMod q) with h0 | h1 | hm1
    · rw [h0]; norm_num
    · rw [h1]; norm_num
    · rw [hm1]; norm_num
  rw [hsplit]
  ring

/-! ### Explicit Closed-Form Evaluations at `q = 5`, `q = 8`, and `q = 12` -/

/-- Helper: lift a `ℤˣ`-valued unit homomorphism on `(ZMod q)ˣ` to a `DirichletCharacter ℂ q`. -/
def dirichletCharOfIntUnitHom {q : ℕ} (f : (ZMod q)ˣ →* ℤˣ) : DirichletCharacter ℂ q :=
  MulChar.ofUnitHom ((Units.map (Int.castRingHom ℂ : ℤ →* ℂ)).comp f)

lemma dirichletCharOfIntUnitHom_apply_unit {q : ℕ} (f : (ZMod q)ˣ →* ℤˣ) (u : (ZMod q)ˣ) :
    dirichletCharOfIntUnitHom f (u : ZMod q) = (((f u : ℤˣ) : ℤ) : ℂ) := by
  unfold dirichletCharOfIntUnitHom
  rw [MulChar.ofUnitHom_coe]
  simp only [MonoidHom.comp_apply, Units.coe_map]
  rfl

lemma dirichletCharOfIntUnitHom_apply_isUnit {q : ℕ} (f : (ZMod q)ˣ →* ℤˣ)
    {a : ZMod q} (ha : IsUnit a) :
    dirichletCharOfIntUnitHom f a = (((f ha.unit : ℤˣ) : ℤ) : ℂ) := by
  simpa only [IsUnit.unit_spec] using dirichletCharOfIntUnitHom_apply_unit f ha.unit

/-- Concrete even primitive real Dirichlet character `χ₅` modulo `5` (associated to `ℚ(√5)`):
`χ₅(1) = χ₅(4) = 1`, `χ₅(2) = χ₅(3) = -1`. -/
def chi5 : DirichletCharacter ℂ 5 :=
  dirichletCharOfIntUnitHom
    { toFun := fun u => if (u : ZMod 5) = 1 ∨ (u : ZMod 5) = 4 then 1 else -1
      map_one' := by decide
      map_mul' := fun u v => by fin_cases u <;> fin_cases v <;> decide }

theorem chi5_apply_val (a : ZMod 5) :
    chi5 a = if IsUnit a then (if a = 1 ∨ a = 4 then 1 else -1) else 0 := by
  by_cases ha : IsUnit a
  · rw [if_pos ha]
    have heq : a = (ha.unit : ZMod 5) := rfl
    rw [heq, chi5, dirichletCharOfIntUnitHom, MulChar.ofUnitHom_coe]
    simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
    split_ifs <;> simp
  · rw [if_neg ha, MulChar.map_nonunit chi5 ha]

theorem chi5_real (a : ZMod 5) : (chi5 a).im = 0 := by
  rw [chi5_apply_val]; split_ifs <;> simp

theorem chi5_even : chi5.Even := by
  show chi5 (-1 : ZMod 5) = 1
  have h4u : IsUnit (4 : ZMod 5) := (ZMod.isUnit_iff_coprime 4 5).mpr (by decide)
  rw [show (-1 : ZMod 5) = 4 by decide, chi5_apply_val, if_pos h4u]
  simp

theorem chi5_ne_one : chi5 ≠ 1 := by
  intro h1
  have h2u : IsUnit (2 : ZMod 5) := (ZMod.isUnit_iff_coprime 2 5).mpr (by decide)
  have h := congrArg (fun χ : DirichletCharacter ℂ 5 => χ (2 : ZMod 5)) h1
  rw [MulChar.one_apply h2u, chi5_apply_val, if_pos h2u] at h
  norm_num [show (2 : ZMod 5) ≠ 1 by decide, show (2 : ZMod 5) ≠ 4 by decide] at h

theorem chi5_isPrimitive : chi5.IsPrimitive := by
  show chi5.conductor = 5
  have hdvd : chi5.conductor ∣ 5 := DirichletCharacter.conductor_dvd_level chi5
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
  · exact absurd ((DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h1) chi5_ne_one
  · exact h5

/-- **Exact Closed-Form Evaluation `L(1, χ₅) = (2 / √5) * log ((1 + √5) / 2)`** (`ℚ(√5)`,
golden ratio fundamental unit!). -/
theorem LFunction_one_chi5_eq :
    (DirichletCharacter.LFunction chi5 1).re =
      (2 / Real.sqrt 5) * Real.log ((1 + Real.sqrt 5) / 2) := by
  rw [LFunction_one_even_real_eq_half_log_sin chi5_isPrimitive chi5_ne_one chi5_even chi5_real]
  have hIcc : Finset.Icc 1 (5 / 2) = {1, 2} := by decide
  rw [hIcc, Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)]
  have h1 : (chi5 ((1 : ℕ) : ZMod 5)).re = 1 := by
    rw [Nat.cast_one, chi5_apply_val, if_pos isUnit_one]; simp
  have h2 : (chi5 ((2 : ℕ) : ZMod 5)).re = -1 := by
    have h2u : IsUnit (2 : ZMod 5) := (ZMod.isUnit_iff_coprime 2 5).mpr (by decide)
    rw [Nat.cast_ofNat, chi5_apply_val, if_pos h2u]
    simp [show (2 : ZMod 5) ≠ 1 by decide, show (2 : ZMod 5) ≠ 4 by decide]
  rw [h1, h2]
  have hsin1_pos : 0 < Real.sin (Real.pi * ((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> push_cast <;> linarith [Real.pi_pos]
  have hsin2_pos : 0 < Real.sin (Real.pi * ((2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> push_cast <;> linarith [Real.pi_pos]
  have hratio :
      Real.sin (Real.pi * ((2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) /
          Real.sin (Real.pi * ((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) =
        (1 + Real.sqrt 5) / 2 := by
    have h2arg : Real.pi * ((2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) = 2 * (Real.pi / 5) := by
      push_cast; ring
    have h1arg : Real.pi * ((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) = Real.pi / 5 := by
      push_cast; ring
    rw [h2arg, h1arg, Real.sin_two_mul]
    have hsne : Real.sin (Real.pi / 5) ≠ 0 := by
      rw [h1arg] at hsin1_pos; exact hsin1_pos.ne'
    field_simp [hsne]
    rw [Real.cos_pi_div_five]
    ring
  have hlog :
      1 * Real.log (Real.sin (Real.pi * ((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))) +
          (-1) * Real.log (Real.sin (Real.pi * ((2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))) =
        -Real.log ((1 + Real.sqrt 5) / 2) := by
    rw [← hratio, Real.log_div hsin2_pos.ne' hsin1_pos.ne']
    ring
  rw [hlog]
  norm_num

theorem LFunction_one_chi5_complex_eq :
    DirichletCharacter.LFunction chi5 1 =
      (((2 / Real.sqrt 5) * Real.log ((1 + Real.sqrt 5) / 2) : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]; exact LFunction_one_chi5_eq
  · rw [Complex.ofReal_im]; exact (LFunction_one_pos_of_real chi5 chi5_ne_one chi5_real).2

/-- Concrete even primitive real Dirichlet character `χ₈` modulo `8` (associated to `ℚ(√2)`):
`χ₈(1) = χ₈(7) = 1`, `χ₈(3) = χ₈(5) = -1`. -/
def chi8 : DirichletCharacter ℂ 8 :=
  dirichletCharOfIntUnitHom
    { toFun := fun u => if (u : ZMod 8) = 1 ∨ (u : ZMod 8) = 7 then 1 else -1
      map_one' := by decide
      map_mul' := fun u v => by fin_cases u <;> fin_cases v <;> decide }

theorem chi8_apply_val (a : ZMod 8) :
    chi8 a = if IsUnit a then (if a = 1 ∨ a = 7 then 1 else -1) else 0 := by
  by_cases ha : IsUnit a
  · rw [if_pos ha]
    have heq : a = (ha.unit : ZMod 8) := rfl
    rw [heq, chi8, dirichletCharOfIntUnitHom, MulChar.ofUnitHom_coe]
    simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
    split_ifs <;> simp
  · rw [if_neg ha, MulChar.map_nonunit chi8 ha]

theorem chi8_real (a : ZMod 8) : (chi8 a).im = 0 := by
  rw [chi8_apply_val]; split_ifs <;> simp

theorem chi8_even : chi8.Even := by
  show chi8 (-1 : ZMod 8) = 1
  have h7u : IsUnit (7 : ZMod 8) := (ZMod.isUnit_iff_coprime 7 8).mpr (by decide)
  rw [show (-1 : ZMod 8) = 7 by decide, chi8_apply_val, if_pos h7u]
  simp

theorem chi8_ne_one : chi8 ≠ 1 := by
  intro h1
  have h3u : IsUnit (3 : ZMod 8) := (ZMod.isUnit_iff_coprime 3 8).mpr (by decide)
  have h := congrArg (fun χ : DirichletCharacter ℂ 8 => χ (3 : ZMod 8)) h1
  rw [MulChar.one_apply h3u, chi8_apply_val, if_pos h3u] at h
  norm_num [show (3 : ZMod 8) ≠ 1 by decide, show (3 : ZMod 8) ≠ 7 by decide] at h

theorem chi8_isPrimitive : chi8.IsPrimitive := by
  show chi8.conductor = 8
  have hdvd : chi8.conductor ∣ 8 := DirichletCharacter.conductor_dvd_level chi8
  have hnot4 : ¬ chi8.FactorsThrough 4 := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (by norm_num : 4 ∣ 8)]
    intro hle
    have h5u : IsUnit (5 : ZMod 8) := (ZMod.isUnit_iff_coprime 5 8).mpr (by decide)
    have hmem : h5u.unit ∈ (ZMod.unitsMap (by norm_num : 4 ∣ 8)).ker := by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      change ZMod.cast (5 : ZMod 8) = (1 : ZMod 4)
      decide
    have hker := hle hmem
    rw [MonoidHom.mem_ker] at hker
    have hv := congrArg Units.val hker
    rw [MulChar.coe_toUnitHom, Units.val_one] at hv
    change chi8 (5 : ZMod 8) = 1 at hv
    rw [chi8_apply_val, if_pos h5u] at hv
    norm_num [show (5 : ZMod 8) ≠ 1 by decide, show (5 : ZMod 8) ≠ 7 by decide] at hv
  have hnot_dvd4 : ¬ chi8.conductor ∣ 4 := fun h =>
    hnot4 ((DirichletCharacter.mem_conductorSet_iff_conductor_dvd chi8 (by norm_num : 4 ∣ 8)).mpr h)
  have hle8 : chi8.conductor ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < chi8.conductor := Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero chi8)
  interval_cases h : chi8.conductor <;> simp_all

/-- **Exact Closed-Form Evaluation `L(1, χ₈) = (1 / √2) * log (1 + √2)`** (`ℚ(√2)`,
silver ratio fundamental unit!). -/
theorem LFunction_one_chi8_eq :
    (DirichletCharacter.LFunction chi8 1).re =
      (1 / Real.sqrt 2) * Real.log (1 + Real.sqrt 2) := by
  rw [LFunction_one_even_real_eq_half_log_sin chi8_isPrimitive chi8_ne_one chi8_even chi8_real]
  have hIcc : Finset.Icc 1 (8 / 2) = {1, 2, 3, 4} := by decide
  rw [hIcc]
  have hsum4 :
      ∑ a ∈ ({1, 2, 3, 4} : Finset ℕ),
          (chi8 (a : ZMod 8)).re * Real.log (Real.sin (Real.pi * (a : ℝ) / ((8 : ℕ) : ℝ))) =
        (chi8 ((1 : ℕ) : ZMod 8)).re * Real.log (Real.sin (Real.pi * ((1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) +
        (chi8 ((2 : ℕ) : ZMod 8)).re * Real.log (Real.sin (Real.pi * ((2 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) +
        (chi8 ((3 : ℕ) : ZMod 8)).re * Real.log (Real.sin (Real.pi * ((3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) +
        (chi8 ((4 : ℕ) : ZMod 8)).re * Real.log (Real.sin (Real.pi * ((4 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) := by
    simp [Finset.sum_insert, Finset.sum_singleton]
    ring
  rw [hsum4]
  have h1 : (chi8 ((1 : ℕ) : ZMod 8)).re = 1 := by
    rw [Nat.cast_one, chi8_apply_val, if_pos isUnit_one]; simp
  have h2 : (chi8 ((2 : ℕ) : ZMod 8)).re = 0 := by
    rw [Nat.cast_ofNat, chi8_apply_val, if_neg (fun hu => by
      have := (ZMod.isUnit_iff_coprime 2 8).mp hu; norm_num at this)]; simp
  have h3 : (chi8 ((3 : ℕ) : ZMod 8)).re = -1 := by
    have h3u : IsUnit (3 : ZMod 8) := (ZMod.isUnit_iff_coprime 3 8).mpr (by decide)
    rw [Nat.cast_ofNat, chi8_apply_val, if_pos h3u]
    simp [show (3 : ZMod 8) ≠ 1 by decide, show (3 : ZMod 8) ≠ 7 by decide]
  have h4 : (chi8 ((4 : ℕ) : ZMod 8)).re = 0 := by
    rw [Nat.cast_ofNat, chi8_apply_val, if_neg (fun hu => by
      have := (ZMod.isUnit_iff_coprime 4 8).mp hu; norm_num at this)]; simp
  rw [h1, h2, h3, h4]
  have hsin1_pos : 0 < Real.sin (Real.pi * ((1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> push_cast <;> linarith [Real.pi_pos]
  have hsin3_pos : 0 < Real.sin (Real.pi * ((3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> push_cast <;> linarith [Real.pi_pos]
  have hratio :
      Real.sin (Real.pi * ((3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) /
          Real.sin (Real.pi * ((1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) =
        1 + Real.sqrt 2 := by
    have h1arg : Real.pi * ((1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = Real.pi / 8 := by push_cast; ring
    have h3arg : Real.pi * ((3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = Real.pi / 2 - Real.pi / 8 := by
      push_cast; ring
    rw [h3arg, h1arg, Real.sin_pi_div_two_sub]
    have hs_pos : 0 < Real.sin (Real.pi / 8) := by rwa [h1arg] at hsin1_pos
    have hc_pos : 0 < Real.cos (Real.pi / 8) := by
      rw [← Real.sin_pi_div_two_sub, ← h3arg]; exact hsin3_pos
    have h2sin_cos : 2 * Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8) = Real.sqrt 2 / 2 := by
      rw [← Real.sin_two_mul, show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.sin_pi_div_four]
    have hcos_sq : 2 * Real.cos (Real.pi / 8) ^ 2 = 1 + Real.sqrt 2 / 2 := by
      have h := Real.cos_two_mul (Real.pi / 8)
      rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four] at h
      linarith
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [div_eq_iff hs_pos.ne']
    apply mul_left_cancel₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hc_pos).ne'
    calc 2 * Real.cos (Real.pi / 8) * Real.cos (Real.pi / 8)
        = 2 * Real.cos (Real.pi / 8) ^ 2 := by ring
      _ = 1 + Real.sqrt 2 / 2 := hcos_sq
      _ = (1 + Real.sqrt 2) * (Real.sqrt 2 / 2) := by nlinarith
      _ = (1 + Real.sqrt 2) * (2 * Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8)) := by
          rw [h2sin_cos]
      _ = 2 * Real.cos (Real.pi / 8) * ((1 + Real.sqrt 2) * Real.sin (Real.pi / 8)) := by ring
  have hlog :
      1 * Real.log (Real.sin (Real.pi * ((1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) +
        0 * Real.log (Real.sin (Real.pi * ((2 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) +
        (-1) * Real.log (Real.sin (Real.pi * ((3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) +
        0 * Real.log (Real.sin (Real.pi * ((4 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) =
      -Real.log (1 + Real.sqrt 2) := by
    rw [← hratio, Real.log_div hsin3_pos.ne' hsin1_pos.ne']
    ring
  rw [hlog]
  have hsqrt8 : Real.sqrt ((8 : ℕ) : ℝ) = 2 * Real.sqrt 2 := by
    rw [show ((8 : ℕ) : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [hsqrt8]
  have hsq2_ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp [hsq2_ne]

theorem LFunction_one_chi8_complex_eq :
    DirichletCharacter.LFunction chi8 1 =
      (((1 / Real.sqrt 2) * Real.log (1 + Real.sqrt 2) : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]; exact LFunction_one_chi8_eq
  · rw [Complex.ofReal_im]; exact (LFunction_one_pos_of_real chi8 chi8_ne_one chi8_real).2

/-- Concrete even primitive real Dirichlet character `χ₁₂` modulo `12` (associated to `ℚ(√3)`):
`χ₁₂(1) = χ₁₂(11) = 1`, `χ₁₂(5) = χ₁₂(7) = -1`. -/
def chi12 : DirichletCharacter ℂ 12 :=
  dirichletCharOfIntUnitHom
    { toFun := fun u => if (u : ZMod 12) = 1 ∨ (u : ZMod 12) = 11 then 1 else -1
      map_one' := by decide
      map_mul' := fun u v => by fin_cases u <;> fin_cases v <;> decide }

theorem chi12_apply_val (a : ZMod 12) :
    chi12 a = if IsUnit a then (if a = 1 ∨ a = 11 then 1 else -1) else 0 := by
  by_cases ha : IsUnit a
  · rw [if_pos ha]
    have heq : a = (ha.unit : ZMod 12) := rfl
    rw [heq, chi12, dirichletCharOfIntUnitHom, MulChar.ofUnitHom_coe]
    simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
    split_ifs <;> simp
  · rw [if_neg ha, MulChar.map_nonunit chi12 ha]

theorem chi12_real (a : ZMod 12) : (chi12 a).im = 0 := by
  rw [chi12_apply_val]; split_ifs <;> simp

theorem chi12_even : chi12.Even := by
  show chi12 (-1 : ZMod 12) = 1
  have h11u : IsUnit (11 : ZMod 12) := (ZMod.isUnit_iff_coprime 11 12).mpr (by decide)
  rw [show (-1 : ZMod 12) = 11 by decide, chi12_apply_val, if_pos h11u]
  simp

theorem chi12_ne_one : chi12 ≠ 1 := by
  intro h1
  have h5u : IsUnit (5 : ZMod 12) := (ZMod.isUnit_iff_coprime 5 12).mpr (by decide)
  have h := congrArg (fun χ : DirichletCharacter ℂ 12 => χ (5 : ZMod 12)) h1
  rw [MulChar.one_apply h5u, chi12_apply_val, if_pos h5u] at h
  norm_num [show (5 : ZMod 12) ≠ 1 by decide, show (5 : ZMod 12) ≠ 11 by decide] at h

theorem chi12_isPrimitive : chi12.IsPrimitive := by
  show chi12.conductor = 12
  have hdvd : chi12.conductor ∣ 12 := DirichletCharacter.conductor_dvd_level chi12
  have hnot4 : ¬ chi12.FactorsThrough 4 := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (by norm_num : 4 ∣ 12)]
    intro hle
    have h5u : IsUnit (5 : ZMod 12) := (ZMod.isUnit_iff_coprime 5 12).mpr (by decide)
    have hmem : h5u.unit ∈ (ZMod.unitsMap (by norm_num : 4 ∣ 12)).ker := by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      change ZMod.cast (5 : ZMod 12) = (1 : ZMod 4)
      decide
    have hker := hle hmem
    rw [MonoidHom.mem_ker] at hker
    have hv := congrArg Units.val hker
    rw [MulChar.coe_toUnitHom, Units.val_one] at hv
    change chi12 (5 : ZMod 12) = 1 at hv
    rw [chi12_apply_val, if_pos h5u] at hv
    norm_num [show (5 : ZMod 12) ≠ 1 by decide, show (5 : ZMod 12) ≠ 11 by decide] at hv
  have hnot6 : ¬ chi12.FactorsThrough 6 := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (by norm_num : 6 ∣ 12)]
    intro hle
    have h7u : IsUnit (7 : ZMod 12) := (ZMod.isUnit_iff_coprime 7 12).mpr (by decide)
    have hmem : h7u.unit ∈ (ZMod.unitsMap (by norm_num : 6 ∣ 12)).ker := by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      change ZMod.cast (7 : ZMod 12) = (1 : ZMod 6)
      decide
    have hker := hle hmem
    rw [MonoidHom.mem_ker] at hker
    have hv := congrArg Units.val hker
    rw [MulChar.coe_toUnitHom, Units.val_one] at hv
    change chi12 (7 : ZMod 12) = 1 at hv
    rw [chi12_apply_val, if_pos h7u] at hv
    norm_num [show (7 : ZMod 12) ≠ 1 by decide, show (7 : ZMod 12) ≠ 11 by decide] at hv
  have hndvd4 : ¬ chi12.conductor ∣ 4 := fun h =>
    hnot4 ((DirichletCharacter.mem_conductorSet_iff_conductor_dvd chi12 (by norm_num : 4 ∣ 12)).mpr h)
  have hndvd6 : ¬ chi12.conductor ∣ 6 := fun h =>
    hnot6 ((DirichletCharacter.mem_conductorSet_iff_conductor_dvd chi12 (by norm_num : 6 ∣ 12)).mpr h)
  have hle12 : chi12.conductor ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < chi12.conductor := Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero chi12)
  interval_cases h : chi12.conductor <;> simp_all

/-- **Exact Closed-Form Evaluation `L(1, χ₁₂) = (1 / √3) * log (2 + √3)`** (`ℚ(√3)`). -/
theorem LFunction_one_chi12_eq :
    (DirichletCharacter.LFunction chi12 1).re =
      (1 / Real.sqrt 3) * Real.log (2 + Real.sqrt 3) := by
  rw [LFunction_one_even_real_eq_half_log_sin chi12_isPrimitive chi12_ne_one chi12_even chi12_real]
  have hIcc : Finset.Icc 1 (12 / 2) = {1, 2, 3, 4, 5, 6} := by decide
  rw [hIcc]
  have hsum6 :
      ∑ a ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ),
          (chi12 (a : ZMod 12)).re * Real.log (Real.sin (Real.pi * (a : ℝ) / ((12 : ℕ) : ℝ))) =
        (chi12 ((1 : ℕ) : ZMod 12)).re * Real.log (Real.sin (Real.pi * ((1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ))) +
        (chi12 ((2 : ℕ) : ZMod 12)).re * Real.log (Real.sin (Real.pi * ((2 : ℕ) : ℝ) / ((12 : ℕ) : ℝ))) +
        (chi12 ((3 : ℕ) : ZMod 12)).re * Real.log (Real.sin (Real.pi * ((3 : ℕ) : ℝ) / ((12 : ℕ) : ℝ))) +
        (chi12 ((4 : ℕ) : ZMod 12)).re * Real.log (Real.sin (Real.pi * ((4 : ℕ) : ℝ) / ((12 : ℕ) : ℝ))) +
        (chi12 ((5 : ℕ) : ZMod 12)).re * Real.log (Real.sin (Real.pi * ((5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ))) +
        (chi12 ((6 : ℕ) : ZMod 12)).re * Real.log (Real.sin (Real.pi * ((6 : ℕ) : ℝ) / ((12 : ℕ) : ℝ))) := by
    simp [Finset.sum_insert, Finset.sum_singleton]
    ring
  rw [hsum6]
  have h1 : (chi12 ((1 : ℕ) : ZMod 12)).re = 1 := by
    rw [Nat.cast_one, chi12_apply_val, if_pos isUnit_one]; simp
  have h2 : (chi12 ((2 : ℕ) : ZMod 12)).re = 0 := by
    rw [Nat.cast_ofNat, chi12_apply_val, if_neg (fun hu => by
      have := (ZMod.isUnit_iff_coprime 2 12).mp hu; norm_num at this)]; simp
  have h3 : (chi12 ((3 : ℕ) : ZMod 12)).re = 0 := by
    rw [Nat.cast_ofNat, chi12_apply_val, if_neg (fun hu => by
      have := (ZMod.isUnit_iff_coprime 3 12).mp hu; norm_num at this)]; simp
  have h4 : (chi12 ((4 : ℕ) : ZMod 12)).re = 0 := by
    rw [Nat.cast_ofNat, chi12_apply_val, if_neg (fun hu => by
      have := (ZMod.isUnit_iff_coprime 4 12).mp hu; norm_num at this)]; simp
  have h5 : (chi12 ((5 : ℕ) : ZMod 12)).re = -1 := by
    have h5u : IsUnit (5 : ZMod 12) := (ZMod.isUnit_iff_coprime 5 12).mpr (by decide)
    rw [Nat.cast_ofNat, chi12_apply_val, if_pos h5u]
    simp [show (5 : ZMod 12) ≠ 1 by decide, show (5 : ZMod 12) ≠ 11 by decide]
  have h6 : (chi12 ((6 : ℕ) : ZMod 12)).re = 0 := by
    rw [Nat.cast_ofNat, chi12_apply_val, if_neg (fun hu => by
      have := (ZMod.isUnit_iff_coprime 6 12).mp hu; norm_num at this)]; simp
  rw [h1, h2, h3, h4, h5, h6]
  have hsin1_pos : 0 < Real.sin (Real.pi * ((1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> push_cast <;> linarith [Real.pi_pos]
  have hsin5_pos : 0 < Real.sin (Real.pi * ((5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> push_cast <;> linarith [Real.pi_pos]
  have hratio :
      Real.sin (Real.pi * ((5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) /
          Real.sin (Real.pi * ((1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) =
        2 + Real.sqrt 3 := by
    have h1arg : Real.pi * ((1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) = Real.pi / 12 := by push_cast; ring
    have h5arg : Real.pi * ((5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) = Real.pi / 2 - Real.pi / 12 := by
      push_cast; ring
    rw [h5arg, h1arg, Real.sin_pi_div_two_sub]
    have hs_pos : 0 < Real.sin (Real.pi / 12) := by rwa [h1arg] at hsin1_pos
    have hc_pos : 0 < Real.cos (Real.pi / 12) := by
      rw [← Real.sin_pi_div_two_sub, ← h5arg]; exact hsin5_pos
    have h2sin_cos : 2 * Real.sin (Real.pi / 12) * Real.cos (Real.pi / 12) = 1 / 2 := by
      rw [← Real.sin_two_mul, show 2 * (Real.pi / 12) = Real.pi / 6 by ring, Real.sin_pi_div_six]
    have hcos_sq : 2 * Real.cos (Real.pi / 12) ^ 2 = 1 + Real.sqrt 3 / 2 := by
      have h := Real.cos_two_mul (Real.pi / 12)
      rw [show 2 * (Real.pi / 12) = Real.pi / 6 by ring, Real.cos_pi_div_six] at h
      linarith
    rw [div_eq_iff hs_pos.ne']
    apply mul_left_cancel₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hc_pos).ne'
    calc 2 * Real.cos (Real.pi / 12) * Real.cos (Real.pi / 12)
        = 2 * Real.cos (Real.pi / 12) ^ 2 := by ring
      _ = 1 + Real.sqrt 3 / 2 := hcos_sq
      _ = (2 + Real.sqrt 3) * (1 / 2) := by ring
      _ = (2 + Real.sqrt 3) * (2 * Real.sin (Real.pi / 12) * Real.cos (Real.pi / 12)) := by
          rw [h2sin_cos]
      _ = 2 * Real.cos (Real.pi / 12) * ((2 + Real.sqrt 3) * Real.sin (Real.pi / 12)) := by ring
  have hlog :
      1 * Real.log (Real.sin (Real.pi * ((1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ))) +
        0 * Real.log (Real.sin (Real.pi * ((2 : ℕ) : ℝ) / ((12 : ℕ) : ℝ))) +
        0 * Real.log (Real.sin (Real.pi * ((3 : ℕ) : ℝ) / ((12 : ℕ) : ℝ))) +
        0 * Real.log (Real.sin (Real.pi * ((4 : ℕ) : ℝ) / ((12 : ℕ) : ℝ))) +
        (-1) * Real.log (Real.sin (Real.pi * ((5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ))) +
        0 * Real.log (Real.sin (Real.pi * ((6 : ℕ) : ℝ) / ((12 : ℕ) : ℝ))) =
      -Real.log (2 + Real.sqrt 3) := by
    rw [← hratio, Real.log_div hsin5_pos.ne' hsin1_pos.ne']
    ring
  rw [hlog]
  have hsqrt12 : Real.sqrt ((12 : ℕ) : ℝ) = 2 * Real.sqrt 3 := by
    rw [show ((12 : ℕ) : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [hsqrt12]
  have hsq3_ne : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp [hsq3_ne]

theorem LFunction_one_chi12_complex_eq :
    DirichletCharacter.LFunction chi12 1 =
      (((1 / Real.sqrt 3) * Real.log (2 + Real.sqrt 3) : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]; exact LFunction_one_chi12_eq
  · rw [Complex.ofReal_im]; exact (LFunction_one_pos_of_real chi12 chi12_ne_one chi12_real).2

end EvenRealLFunction

/-! ## Section 2: Concrete Pell Equation, Fundamental Unit Structure of `(Zsqrtd d)ˣ`, & Regulator -/

section PellAndUnits

/-- Helper: `¬ IsSquare (d : ℕ)` implies `¬ IsSquare (d : ℤ)`. -/
lemma not_isSquare_int_of_nat {d : ℕ} (hd : ¬ IsSquare d) : ¬ IsSquare (d : ℤ) := by
  rintro ⟨r, hr⟩
  apply hd
  refine ⟨r.natAbs, ?_⟩
  have h : (d : ℤ) = ((r.natAbs * r.natAbs : ℕ) : ℤ) := by
    rw [hr, Int.natAbs_mul_self]
  exact_mod_cast h

/-- Canonical multiplicative homomorphism `Pell.Solution₁ d →* (Zsqrtd d)ˣ`
(since `Pell.Solution₁ d` is `unitary (Zsqrtd d)`). -/
def pellSolToUnitHom (d : ℤ) : Pell.Solution₁ d →* (Zsqrtd d)ˣ where
  toFun a :=
    ⟨(a : Zsqrtd d), (a⁻¹ : Pell.Solution₁ d),
      by
        ext
        · change a.x * (a⁻¹).x + d * a.y * (a⁻¹).y = 1
          rw [Pell.Solution₁.x_inv, Pell.Solution₁.y_inv]
          have h := a.prop; linarith
        · change a.x * (a⁻¹).y + a.y * (a⁻¹).x = 0
          rw [Pell.Solution₁.x_inv, Pell.Solution₁.y_inv]; ring,
      by
        ext
        · change (a⁻¹).x * a.x + d * (a⁻¹).y * a.y = 1
          rw [Pell.Solution₁.x_inv, Pell.Solution₁.y_inv]
          have h := a.prop; linarith
        · change (a⁻¹).x * a.y + (a⁻¹).y * a.x = 0
          rw [Pell.Solution₁.x_inv, Pell.Solution₁.y_inv]; ring⟩
  map_one' := Units.ext (by
    ext
    · exact Pell.Solution₁.x_one
    · exact Pell.Solution₁.y_one)
  map_mul' a b := Units.ext (by
    ext
    · change (a * b).x = a.x * b.x + d * a.y * b.y
      rw [Pell.Solution₁.x_mul]; ring
    · change (a * b).y = a.x * b.y + a.y * b.x
      rw [Pell.Solution₁.y_mul])

lemma pellSolToUnitHom_neg {d : ℤ} (a : Pell.Solution₁ d) :
    pellSolToUnitHom d (-a) = -pellSolToUnitHom d a :=
  Units.ext (by
    ext
    · exact Pell.Solution₁.x_neg a
    · exact Pell.Solution₁.y_neg a)

/-- Every unit `u : (Zsqrtd d)ˣ` has `u.val.norm = 1` or `u.val.norm = -1`. -/
theorem zsqrtd_unit_norm_eq_one_or_neg_one {d : ℤ} (u : (Zsqrtd d)ˣ) :
    (u : Zsqrtd d).norm = 1 ∨ (u : Zsqrtd d).norm = -1 := by
  have h := Zsqrtd.norm_eq_one_iff.mpr u.isUnit
  exact Int.natAbs_eq_iff.mp h

/-- Lift a norm-`+1` unit `u : (Zsqrtd d)ˣ` to `Pell.Solution₁ d`. -/
def unitToPellSol {d : ℤ} (u : (Zsqrtd d)ˣ) (hnorm : (u : Zsqrtd d).norm = 1) :
    Pell.Solution₁ d :=
  Pell.Solution₁.mk (u : Zsqrtd d).re (u : Zsqrtd d).im (by
    have hdef : (u : Zsqrtd d).norm = (u : Zsqrtd d).re * (u : Zsqrtd d).re -
        d * (u : Zsqrtd d).im * (u : Zsqrtd d).im := rfl
    linarith)

lemma pellSolToUnitHom_unitToPellSol {d : ℤ} (u : (Zsqrtd d)ˣ)
    (hnorm : (u : Zsqrtd d).norm = 1) :
    pellSolToUnitHom d (unitToPellSol u hnorm) = u := by
  have hp : (u : Zsqrtd d).re ^ 2 - d * (u : Zsqrtd d).im ^ 2 = 1 := by
    have hdef : (u : Zsqrtd d).norm = (u : Zsqrtd d).re * (u : Zsqrtd d).re -
        d * (u : Zsqrtd d).im * (u : Zsqrtd d).im := rfl
    linarith
  apply Units.ext
  ext
  · exact Pell.Solution₁.x_mk _ _ hp
  · exact Pell.Solution₁.y_mk _ _ hp

/-- For `d > 0` non-square, `Zsqrtd d` has no nontrivial square roots of `1`:
`u ^ 2 = 1 → u = 1 ∨ u = -1`. -/
lemma zsqrtd_unit_sq_eq_one {d : ℕ} (hd : ¬ IsSquare d) (u : (Zsqrtd (d : ℤ))ˣ)
    (hu : u ^ 2 = 1) : u = 1 ∨ u = -1 := by
  have hns : ∀ n : ℤ, (d : ℤ) ≠ n * n := fun n hn =>
    not_isSquare_int_of_nat hd ⟨n, hn⟩
  have htr : (Zsqrtd.toReal (Nat.cast_nonneg d) (u : Zsqrtd (d : ℤ))) ^ 2 = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]
  rcases sq_eq_one_iff.mp htr with h1 | hm1
  · left
    exact Units.ext (Zsqrtd.toReal_injective (Nat.cast_nonneg d) hns (by simpa using h1))
  · right
    exact Units.ext (Zsqrtd.toReal_injective (Nat.cast_nonneg d) hns (by simpa using hm1))

/-- The unique fundamental norm-`+1` Pell solution `a₁ : Pell.Solution₁ d` (`x > 1, y > 0` minimal)
for every positive non-square `d : ℕ`. -/
def fundamentalPellSol₁ (d : ℕ) (hd0 : 0 < d) (hd : ¬ IsSquare d) : Pell.Solution₁ (d : ℤ) :=
  Classical.choose
    (Pell.IsFundamental.exists_of_not_isSquare (Int.natCast_pos.mpr hd0) (not_isSquare_int_of_nat hd))

theorem fundamentalPellSol₁_isFundamental (d : ℕ) (hd0 : 0 < d) (hd : ¬ IsSquare d) :
    Pell.IsFundamental (fundamentalPellSol₁ d hd0 hd) :=
  Classical.choose_spec
    (Pell.IsFundamental.exists_of_not_isSquare (Int.natCast_pos.mpr hd0) (not_isSquare_int_of_nat hd))

theorem fundamentalPellSol₁_eq_of_isFundamental {d : ℕ} (hd0 : 0 < d) (hd : ¬ IsSquare d)
    {a : Pell.Solution₁ (d : ℤ)} (ha : Pell.IsFundamental a) :
    fundamentalPellSol₁ d hd0 hd = a :=
  Pell.IsFundamental.subsingleton (fundamentalPellSol₁_isFundamental d hd0 hd) ha

/-- Real embedding of `fundamentalPellSol₁ d` is strictly greater than `1`. -/
theorem one_lt_toReal_fundamentalPellSol₁ (d : ℕ) (hd0 : 0 < d) (hd : ¬ IsSquare d) :
    1 < Zsqrtd.toReal (Nat.cast_nonneg d) (fundamentalPellSol₁ d hd0 hd : Zsqrtd (d : ℤ)) := by
  have hfund := fundamentalPellSol₁_isFundamental d hd0 hd
  rw [Zsqrtd.toReal_apply]
  have hx : (1 : ℝ) < ((fundamentalPellSol₁ d hd0 hd).x : ℝ) := by exact_mod_cast hfund.1
  have hy : (0 : ℝ) < ((fundamentalPellSol₁ d hd0 hd).y : ℝ) := by exact_mod_cast hfund.2.1
  have hsq : 0 < Real.sqrt ((d : ℤ) : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd0)
  change 1 < ((fundamentalPellSol₁ d hd0 hd).x : ℝ) +
    ((fundamentalPellSol₁ d hd0 hd).y : ℝ) * Real.sqrt ((d : ℤ) : ℝ)
  nlinarith

/-- Helper: if a norm-`-1` unit exists in `(Zsqrtd d)ˣ`, there is a norm-`-1` unit `η` with
`η ^ 2 = fundamentalPellSol₁` and `1 < toReal η`. -/
private theorem exists_neg_norm_sqrt_fundamental (d : ℕ) (hd0 : 0 < d) (hd : ¬ IsSquare d)
    (hex : ∃ v : (Zsqrtd (d : ℤ))ˣ, (v : Zsqrtd (d : ℤ)).norm = -1) :
    ∃ η : (Zsqrtd (d : ℤ))ˣ,
      (η : Zsqrtd (d : ℤ)).norm = -1 ∧
      η ^ 2 = pellSolToUnitHom (d : ℤ) (fundamentalPellSol₁ d hd0 hd) ∧
      1 < Zsqrtd.toReal (Nat.cast_nonneg d) (η : Zsqrtd (d : ℤ)) := by
  obtain ⟨v, hv⟩ := hex
  set a₁ := fundamentalPellSol₁ d hd0 hd
  have hfund : Pell.IsFundamental a₁ := fundamentalPellSol₁_isFundamental d hd0 hd
  have hv2_norm : ((v ^ 2 : (Zsqrtd (d : ℤ))ˣ) : Zsqrtd (d : ℤ)).norm = 1 := by
    rw [Units.val_pow_eq_pow_val, sq, Zsqrtd.norm_mul, hv]; norm_num
  set s : Pell.Solution₁ (d : ℤ) := unitToPellSol (v ^ 2) hv2_norm
  have hs_x_pos : 0 < s.x := by
    have hre : s.x = (v : Zsqrtd (d : ℤ)).re * (v : Zsqrtd (d : ℤ)).re +
        (d : ℤ) * (v : Zsqrtd (d : ℤ)).im * (v : Zsqrtd (d : ℤ)).im := by
      dsimp only [s, unitToPellSol]
      rw [Pell.Solution₁.x_mk, Units.val_pow_eq_pow_val, sq]
      rfl
    rw [hre]
    have h1 : (v : Zsqrtd (d : ℤ)).re ^ 2 - (d : ℤ) * (v : Zsqrtd (d : ℤ)).im ^ 2 = -1 := by
      have hdef : (v : Zsqrtd (d : ℤ)).norm = (v : Zsqrtd (d : ℤ)).re * (v : Zsqrtd (d : ℤ)).re -
          (d : ℤ) * (v : Zsqrtd (d : ℤ)).im * (v : Zsqrtd (d : ℤ)).im := rfl
      linarith
    have hd_pos : (0 : ℤ) < (d : ℤ) := Int.natCast_pos.mpr hd0
    nlinarith [sq_nonneg (v : Zsqrtd (d : ℤ)).re, sq_nonneg (v : Zsqrtd (d : ℤ)).im]
  obtain ⟨k, hk | hk⟩ := hfund.eq_zpow_or_neg_zpow s
  · have hk_odd : Odd k := by
      refine Int.not_even_iff_odd.mp ?_
      rintro ⟨m, rfl⟩
      have hsq : (v * (pellSolToUnitHom (d : ℤ) a₁) ^ (-m)) ^ 2 = 1 := by
        rw [mul_pow, ← zpow_natCast (pellSolToUnitHom (d : ℤ) a₁ ^ (-m)), ← zpow_mul,
          show (-m : ℤ) * (2 : ℕ) = -(m + m) by push_cast; ring, zpow_neg]
        have hv2 : v ^ 2 = pellSolToUnitHom (d : ℤ) a₁ ^ (m + m) := by
          rw [← pellSolToUnitHom_unitToPellSol (v ^ 2) hv2_norm]
          change pellSolToUnitHom (d : ℤ) s = _
          rw [hk, map_zpow]
        rw [hv2, mul_inv_cancel]
      rcases zsqrtd_unit_sq_eq_one hd _ hsq with h1 | hm1
      · have hv_eq : v = pellSolToUnitHom (d : ℤ) a₁ ^ m := by
          have := congrArg (· * pellSolToUnitHom (d : ℤ) a₁ ^ m) h1
          simpa [mul_assoc, ← zpow_add] using this
        have hn1 : (v : Zsqrtd (d : ℤ)).norm = 1 := by
          rw [hv_eq, ← map_zpow]
          have hsol := (a₁ ^ m).prop
          change (a₁ ^ m).x * (a₁ ^ m).x - (d : ℤ) * (a₁ ^ m).y * (a₁ ^ m).y = 1
          linarith
        linarith
      · have hv_eq : v = -(pellSolToUnitHom (d : ℤ) a₁ ^ m) := by
          have := congrArg (· * pellSolToUnitHom (d : ℤ) a₁ ^ m) hm1
          simpa [mul_assoc, ← zpow_add] using this
        have hn1 : (v : Zsqrtd (d : ℤ)).norm = 1 := by
          rw [hv_eq, Units.val_neg, Zsqrtd.norm_neg, ← map_zpow]
          have hsol := (a₁ ^ m).prop
          change (a₁ ^ m).x * (a₁ ^ m).x - (d : ℤ) * (a₁ ^ m).y * (a₁ ^ m).y = 1
          linarith
        linarith
    obtain ⟨m, rfl⟩ := hk_odd
    set w : (Zsqrtd (d : ℤ))ˣ := v * (pellSolToUnitHom (d : ℤ) a₁) ^ (-m)
    have hw_sq : w ^ 2 = pellSolToUnitHom (d : ℤ) a₁ := by
      dsimp only [w]
      rw [mul_pow, ← zpow_natCast (pellSolToUnitHom (d : ℤ) a₁ ^ (-m)), ← zpow_mul]
      have hv2 : v ^ 2 = pellSolToUnitHom (d : ℤ) a₁ ^ (2 * m + 1) := by
        rw [← pellSolToUnitHom_unitToPellSol (v ^ 2) hv2_norm]
        change pellSolToUnitHom (d : ℤ) s = _
        rw [hk, map_zpow]
      rw [hv2, ← zpow_add]
      have hexp : 2 * m + 1 + -m * (2 : ℕ) = 1 := by push_cast; ring
      rw [hexp, zpow_one]
    have hw_norm : (w : Zsqrtd (d : ℤ)).norm = -1 := by
      dsimp only [w]
      rw [Units.val_mul, Zsqrtd.norm_mul, hv, ← map_zpow]
      have hsol := (a₁ ^ (-m)).prop
      have h1 : ((pellSolToUnitHom (d : ℤ) (a₁ ^ (-m)) : (Zsqrtd (d : ℤ))ˣ) : Zsqrtd (d : ℤ)).norm = 1 := by
        change (a₁ ^ (-m)).x * (a₁ ^ (-m)).x - (d : ℤ) * (a₁ ^ (-m)).y * (a₁ ^ (-m)).y = 1
        linarith
      rw [h1, mul_one]
    have htr_sq : (Zsqrtd.toReal (Nat.cast_nonneg d) (w : Zsqrtd (d : ℤ))) ^ 2 =
        Zsqrtd.toReal (Nat.cast_nonneg d) (a₁ : Zsqrtd (d : ℤ)) := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hw_sq]; rfl
    have ha1_gt1 : 1 < Zsqrtd.toReal (Nat.cast_nonneg d) (a₁ : Zsqrtd (d : ℤ)) :=
      one_lt_toReal_fundamentalPellSol₁ d hd0 hd
    by_cases hpos : 0 < Zsqrtd.toReal (Nat.cast_nonneg d) (w : Zsqrtd (d : ℤ))
    · refine ⟨w, hw_norm, hw_sq, ?_⟩
      nlinarith
    · refine ⟨-w, by rw [Units.val_neg, Zsqrtd.norm_neg, hw_norm], by rw [neg_sq, hw_sq], ?_⟩
      rw [Units.val_neg, map_neg]
      nlinarith
  · exfalso
    have hx_pos := Pell.Solution₁.x_zpow_pos hfund.x_pos k
    have hx_neg : s.x < 0 := by
      rw [hk, Pell.Solution₁.x_neg]
      omega
    omega

/-- **Exact Fundamental Unit `ε_d` of `(Zsqrtd d)ˣ`** for every positive non-square `d : ℕ`:
- If a norm-`-1` unit exists, `ε_d` is the unique norm-`-1` unit with `ε_d ^ 2 = fundamentalPellSol₁`
  and `Zsqrtd.toReal _ ε_d > 1`;
- Otherwise, `ε_d = fundamentalPellSol₁` (norm `+1`, `Zsqrtd.toReal _ ε_d > 1`). -/
def fundamentalPellUnit (d : ℕ) (hd0 : 0 < d) (hd : ¬ IsSquare d) : (Zsqrtd (d : ℤ))ˣ :=
  open Classical in
  if h : ∃ v : (Zsqrtd (d : ℤ))ˣ, (v : Zsqrtd (d : ℤ)).norm = -1 then
    Classical.choose (exists_neg_norm_sqrt_fundamental d hd0 hd h)
  else
    pellSolToUnitHom (d : ℤ) (fundamentalPellSol₁ d hd0 hd)

/-- The real embedding of `fundamentalPellUnit d` is strictly greater than `1`. -/
theorem one_lt_toReal_fundamentalPellUnit (d : ℕ) (hd0 : 0 < d) (hd : ¬ IsSquare d) :
    1 < Zsqrtd.toReal (Nat.cast_nonneg d) (fundamentalPellUnit d hd0 hd : Zsqrtd (d : ℤ)) := by
  classical
  unfold fundamentalPellUnit
  split_ifs with h
  · exact (Classical.choose_spec (exists_neg_norm_sqrt_fundamental d hd0 hd h)).2.2
  · exact one_lt_toReal_fundamentalPellSol₁ d hd0 hd

/-- Helper: every element of `ZMod 2` is `0` or `1`. -/
private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

/-- Every unit `u : (Zsqrtd d)ˣ` has a unique representation `u = ± (fundamentalPellUnit d) ^ k`. -/
theorem fundamentalPellUnit_unique_rep (d : ℕ) (hd0 : 0 < d) (hd : ¬ IsSquare d)
    (u : (Zsqrtd (d : ℤ))ˣ) :
    ∃! p : ZMod 2 × ℤ,
      u = (if p.1 = 0 then (1 : (Zsqrtd (d : ℤ))ˣ) else -1) *
        (fundamentalPellUnit d hd0 hd) ^ p.2 := by
  classical
  set ε := fundamentalPellUnit d hd0 hd
  set a₁ := fundamentalPellSol₁ d hd0 hd
  have hfund : Pell.IsFundamental a₁ := fundamentalPellSol₁_isFundamental d hd0 hd
  have hε_gt1 : 1 < Zsqrtd.toReal (Nat.cast_nonneg d) (ε : Zsqrtd (d : ℤ)) :=
    one_lt_toReal_fundamentalPellUnit d hd0 hd
  have hpow_ne : ∀ (s₁ s₂ : ZMod 2) (k₁ k₂ : ℤ),
      (if s₁ = 0 then (1 : (Zsqrtd (d : ℤ))ˣ) else -1) * ε ^ k₁ =
        (if s₂ = 0 then (1 : (Zsqrtd (d : ℤ))ˣ) else -1) * ε ^ k₂ →
      (s₁, k₁) = (s₂, k₂) := by
    intro s₁ s₂ k₁ k₂ heq
    have htr := congrArg (fun x : (Zsqrtd (d : ℤ))ˣ =>
      Zsqrtd.toReal (Nat.cast_nonneg d) (x : Zsqrtd (d : ℤ))) heq
    have htoReal_zpow : ∀ k : ℤ,
        Zsqrtd.toReal (Nat.cast_nonneg d) ((ε ^ k : (Zsqrtd (d : ℤ))ˣ) : Zsqrtd (d : ℤ)) =
          (Zsqrtd.toReal (Nat.cast_nonneg d) (ε : Zsqrtd (d : ℤ))) ^ k := by
      intro k
      let hhom : Zsqrtd (d : ℤ) →* ℝ := (Zsqrtd.toReal (Nat.cast_nonneg d)).toMonoidHom
      have h1 : Units.map hhom (ε ^ k) = (Units.map hhom ε) ^ k := map_zpow _ ε k
      have h2 := congrArg Units.val h1
      simpa only [hhom, RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe,
        Units.val_zpow_eq_zpow_val] using h2
    have hε_pos : 0 < Zsqrtd.toReal (Nat.cast_nonneg d) (ε : Zsqrtd (d : ℤ)) := by linarith
    have hpow_pos : ∀ k : ℤ, 0 < (Zsqrtd.toReal (Nat.cast_nonneg d) (ε : Zsqrtd (d : ℤ))) ^ k :=
      fun k => zpow_pos hε_pos k
    have hs_eq : s₁ = s₂ := by
      rcases zmod2_eq_zero_or_one s₁ with rfl | rfl <;>
        rcases zmod2_eq_zero_or_one s₂ with rfl | rfl
      · rfl
      · exfalso
        simp only [ite_true, show (1 : ZMod 2) ≠ 0 by decide, ite_false, one_mul, neg_mul,
          Units.val_neg, map_neg, htoReal_zpow] at htr
        linarith [hpow_pos k₁, hpow_pos k₂]
      · exfalso
        simp only [ite_true, show (1 : ZMod 2) ≠ 0 by decide, ite_false, one_mul, neg_mul,
          Units.val_neg, map_neg, htoReal_zpow] at htr
        linarith [hpow_pos k₁, hpow_pos k₂]
      · rfl
    subst hs_eq
    have htr_eq : (Zsqrtd.toReal (Nat.cast_nonneg d) (ε : Zsqrtd (d : ℤ))) ^ k₁ =
        (Zsqrtd.toReal (Nat.cast_nonneg d) (ε : Zsqrtd (d : ℤ))) ^ k₂ := by
      by_cases hs : s₁ = 0
      · simpa [hs, htoReal_zpow] using htr
      · simp only [hs, ite_false, neg_mul, one_mul, Units.val_neg, map_neg, htoReal_zpow] at htr
        linarith
    have hk_eq : k₁ = k₂ := (zpow_right_strictMono₀ hε_gt1).injective htr_eq
    exact Prod.ext rfl hk_eq
  have hex : ∃ p : ZMod 2 × ℤ,
      u = (if p.1 = 0 then (1 : (Zsqrtd (d : ℤ))ˣ) else -1) * ε ^ p.2 := by
    by_cases hneg : ∃ v : (Zsqrtd (d : ℤ))ˣ, (v : Zsqrtd (d : ℤ)).norm = -1
    · have hε_eq : ε = Classical.choose (exists_neg_norm_sqrt_fundamental d hd0 hd hneg) := by
        dsimp only [ε, fundamentalPellUnit]; rw [dif_pos hneg]
      have hε_spec := Classical.choose_spec (exists_neg_norm_sqrt_fundamental d hd0 hd hneg)
      rw [← hε_eq] at hε_spec
      obtain ⟨hε_norm, hε_sq, _⟩ := hε_spec
      rcases zsqrtd_unit_norm_eq_one_or_neg_one u with hu1 | hum1
      · obtain ⟨k, hk | hk⟩ := hfund.eq_zpow_or_neg_zpow (unitToPellSol u hu1)
        · refine ⟨(0, 2 * k), ?_⟩
          simp only [ite_true, one_mul, zpow_mul, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl,
            zpow_natCast, hε_sq, ← map_zpow]
          rw [← hk, pellSolToUnitHom_unitToPellSol]
        · refine ⟨(1, 2 * k), ?_⟩
          simp only [show (1 : ZMod 2) ≠ 0 by decide, ite_false, neg_mul, one_mul, zpow_mul,
            show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, hε_sq, ← map_zpow,
            ← pellSolToUnitHom_neg]
          rw [← hk, pellSolToUnitHom_unitToPellSol]
      · have huε_norm : ((u * ε⁻¹ : (Zsqrtd (d : ℤ))ˣ) : Zsqrtd (d : ℤ)).norm = 1 := by
          have hεinv_norm : ((ε⁻¹ : (Zsqrtd (d : ℤ))ˣ) : Zsqrtd (d : ℤ)).norm = -1 := by
            have h1 : (ε : Zsqrtd (d : ℤ)).norm * ((ε⁻¹ : (Zsqrtd (d : ℤ))ˣ) : Zsqrtd (d : ℤ)).norm = 1 := by
              rw [← Zsqrtd.norm_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Zsqrtd.norm_one]
            rw [hε_norm] at h1; linarith
          rw [Units.val_mul, Zsqrtd.norm_mul, hum1, hεinv_norm]; norm_num
        obtain ⟨k, hk | hk⟩ := hfund.eq_zpow_or_neg_zpow (unitToPellSol (u * ε⁻¹) huε_norm)
        · refine ⟨(0, 2 * k + 1), ?_⟩
          have huε : u * ε⁻¹ = ε ^ (2 * k) := by
            rw [← pellSolToUnitHom_unitToPellSol (u * ε⁻¹) huε_norm, hk, map_zpow, ← hε_sq,
              ← zpow_natCast, ← zpow_mul]
            congr 1
          have := congrArg (· * ε) huε
          simp only [inv_mul_cancel_right, ite_true, one_mul, zpow_add_one] at this ⊢
          exact this
        · refine ⟨(1, 2 * k + 1), ?_⟩
          have huε : u * ε⁻¹ = -(ε ^ (2 * k)) := by
            rw [← pellSolToUnitHom_unitToPellSol (u * ε⁻¹) huε_norm, hk, pellSolToUnitHom_neg,
              map_zpow, ← hε_sq, ← zpow_natCast, ← zpow_mul]
            congr 2
          have := congrArg (· * ε) huε
          simp only [inv_mul_cancel_right, show (1 : ZMod 2) ≠ 0 by decide, ite_false, neg_mul,
            one_mul, zpow_add_one] at this ⊢
          exact this
    · have hε_eq : ε = pellSolToUnitHom (d : ℤ) a₁ := by
        dsimp only [ε, fundamentalPellUnit]; rw [dif_neg hneg]
      have hu1 : (u : Zsqrtd (d : ℤ)).norm = 1 := by
        rcases zsqrtd_unit_norm_eq_one_or_neg_one u with h1 | hm1
        · exact h1
        · exact absurd ⟨u, hm1⟩ hneg
      obtain ⟨k, hk | hk⟩ := hfund.eq_zpow_or_neg_zpow (unitToPellSol u hu1)
      · refine ⟨(0, k), ?_⟩
        simp only [ite_true, one_mul, hε_eq, ← map_zpow]
        rw [← hk, pellSolToUnitHom_unitToPellSol]
      · refine ⟨(1, k), ?_⟩
        simp only [show (1 : ZMod 2) ≠ 0 by decide, ite_false, neg_mul, one_mul, hε_eq,
          ← map_zpow, ← pellSolToUnitHom_neg]
        rw [← hk, pellSolToUnitHom_unitToPellSol]
  obtain ⟨p, hp⟩ := hex
  exact ⟨p, hp, fun q hq => hpow_ne q.1 p.1 q.2 p.2 (hq.symm.trans hp)⟩

/-- **Exact Unit Group Structure Isomorphism of `ℤ[√d]ˣ` (`d > 0` non-square)**:
`(Zsqrtd d)ˣ ≃* Multiplicative (ZMod 2) × Multiplicative ℤ`! -/
def zsqrtd_units_equiv_int (d : ℕ) (hd0 : 0 < d) (hd : ¬ IsSquare d) :
    (Zsqrtd (d : ℤ))ˣ ≃* Multiplicative (ZMod 2) × Multiplicative ℤ :=
  let φ : Multiplicative (ZMod 2) × Multiplicative ℤ →* (Zsqrtd (d : ℤ))ˣ :=
    { toFun := fun p =>
        (if Multiplicative.toAdd p.1 = 0 then (1 : (Zsqrtd (d : ℤ))ˣ) else -1) *
          (fundamentalPellUnit d hd0 hd) ^ (Multiplicative.toAdd p.2)
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, zpow_add]
        rcases zmod2_eq_zero_or_one (Multiplicative.toAdd p.1) with h1 | h1 <;>
          rcases zmod2_eq_zero_or_one (Multiplicative.toAdd q.1) with h2 | h2
        · simp [h1, h2]
        · simp [h1, h2, show (1 : ZMod 2) ≠ 0 by decide]
        · simp [h1, h2, show (1 : ZMod 2) ≠ 0 by decide]
        · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
          simp [h1, h2, h11, show (1 : ZMod 2) ≠ 0 by decide] }
  have hbij : Function.Bijective φ := by
    constructor
    · intro p q h
      have hu := fundamentalPellUnit_unique_rep d hd0 hd (φ q)
      have hp1 : (Multiplicative.toAdd p.1, Multiplicative.toAdd p.2) =
          (Multiplicative.toAdd q.1, Multiplicative.toAdd q.2) :=
        hu.unique h.symm rfl
      exact Prod.ext (Multiplicative.toAdd.injective (congrArg Prod.fst hp1))
        (Multiplicative.toAdd.injective (congrArg Prod.snd hp1))
    · intro u
      obtain ⟨p, hp, _⟩ := fundamentalPellUnit_unique_rep d hd0 hd u
      exact ⟨(Multiplicative.ofAdd p.1, Multiplicative.ofAdd p.2), by simpa [φ] using hp.symm⟩
  (MulEquiv.ofBijective φ hbij).symm

/-- **Concrete Pell Regulator `R(ℤ[√d]) := Real.log (ε_d)`** for every positive non-square `d : ℕ`. -/
def pellRegulator (d : ℕ) (hd0 : 0 < d) (hd : ¬ IsSquare d) : ℝ :=
  Real.log (Zsqrtd.toReal (Nat.cast_nonneg d) (fundamentalPellUnit d hd0 hd : Zsqrtd (d : ℤ)))

/-- Strict positivity of the Pell regulator `0 < pellRegulator d`. -/
theorem pellRegulator_pos (d : ℕ) (hd0 : 0 < d) (hd : ¬ IsSquare d) :
    0 < pellRegulator d hd0 hd :=
  Real.log_pos (one_lt_toReal_fundamentalPellUnit d hd0 hd)

/-! ### Explicit Fundamental Units for `d = 2`, `d = 3`, `d = 5`, and `𝒪_{ℚ(√5)} = ℤ[(1 + √5)/2]` -/

lemma not_isSquare_two : ¬ IsSquare (2 : ℕ) := by
  rintro ⟨k, hk⟩
  have hlt : k < 2 := by nlinarith
  interval_cases k <;> norm_num at hk

lemma not_isSquare_three : ¬ IsSquare (3 : ℕ) := by
  rintro ⟨k, hk⟩
  have hlt : k < 2 := by nlinarith
  interval_cases k <;> norm_num at hk

lemma not_isSquare_five : ¬ IsSquare (5 : ℕ) := by
  rintro ⟨k, hk⟩
  have hlt : k < 3 := by nlinarith
  interval_cases k <;> norm_num at hk

/-- Helper: characterize `fundamentalPellUnit d` uniquely when a norm-`-1` unit `η` satisfies
`η ^ 2 = fundamentalPellSol₁` and `1 < toReal η`. -/
private theorem fundamentalPellUnit_eq_of_neg_norm_sq {d : ℕ} (hd0 : 0 < d) (hd : ¬ IsSquare d)
    (η : (Zsqrtd (d : ℤ))ˣ) (hnorm : (η : Zsqrtd (d : ℤ)).norm = -1)
    (hsq : η ^ 2 = pellSolToUnitHom (d : ℤ) (fundamentalPellSol₁ d hd0 hd))
    (hgt1 : 1 < Zsqrtd.toReal (Nat.cast_nonneg d) (η : Zsqrtd (d : ℤ))) :
    fundamentalPellUnit d hd0 hd = η := by
  classical
  have hex : ∃ v : (Zsqrtd (d : ℤ))ˣ, (v : Zsqrtd (d : ℤ)).norm = -1 := ⟨η, hnorm⟩
  have hdef : fundamentalPellUnit d hd0 hd =
      Classical.choose (exists_neg_norm_sqrt_fundamental d hd0 hd hex) := by
    unfold fundamentalPellUnit; rw [dif_pos hex]
  have hspec := Classical.choose_spec (exists_neg_norm_sqrt_fundamental d hd0 hd hex)
  rw [← hdef] at hspec
  have hsq_eq : (fundamentalPellUnit d hd0 hd * η⁻¹) ^ 2 = 1 := by
    rw [mul_pow, inv_pow, hspec.2.1, hsq, mul_inv_cancel]
  rcases zsqrtd_unit_sq_eq_one hd _ hsq_eq with h1 | hm1
  · exact mul_inv_eq_one.mp h1
  · exfalso
    have hneg : fundamentalPellUnit d hd0 hd = -η := by
      have := congrArg (· * η) hm1
      simpa [inv_mul_cancel_right] using this
    have htr := congrArg (fun x : (Zsqrtd (d : ℤ))ˣ =>
      Zsqrtd.toReal (Nat.cast_nonneg d) (x : Zsqrtd (d : ℤ))) hneg
    rw [Units.val_neg, map_neg] at htr
    linarith [hspec.2.2]

/-- Explicit norm-`+1` fundamental Pell solution for `d = 2`: `3 + 2√2`. -/
theorem fundamentalPellSol₁_two :
    (fundamentalPellSol₁ 2 (by norm_num) not_isSquare_two : Zsqrtd 2) = ⟨3, 2⟩ := by
  let a : Pell.Solution₁ (2 : ℤ) := Pell.Solution₁.mk 3 2 (by norm_num)
  have ha : Pell.IsFundamental a := by
    refine ⟨by simp [a], by simp [a], fun {b} hb1 => ?_⟩
    change (3 : ℤ) ≤ b.x
    by_contra hlt
    push Not at hlt
    have hprop := b.prop
    have hx2 : b.x = 2 := by omega
    rw [hx2] at hprop
    have hy_sq : 2 * b.y ^ 2 = 3 := by linarith
    omega
  have heq := fundamentalPellSol₁_eq_of_isFundamental (d := 2) (by norm_num) not_isSquare_two ha
  rw [heq]
  ext
  · exact Pell.Solution₁.x_mk 3 2 _
  · exact Pell.Solution₁.y_mk 3 2 _

/-- Explicit fundamental unit of `ℤ[√2]ˣ`: `ε₂ = 1 + √2` (norm `-1`, `ε₂² = 3 + 2√2`). -/
theorem fundamentalPellUnit_two :
    (fundamentalPellUnit 2 (by norm_num) not_isSquare_two : Zsqrtd 2) = ⟨1, 1⟩ := by
  let η : (Zsqrtd (2 : ℤ))ˣ :=
    ⟨⟨1, 1⟩, ⟨-1, 1⟩, by ext <;> decide, by ext <;> decide⟩
  have hnorm : (η : Zsqrtd 2).norm = -1 := by decide
  have hsq : η ^ 2 = pellSolToUnitHom 2 (fundamentalPellSol₁ 2 (by norm_num) not_isSquare_two) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, sq]
    change (⟨1, 1⟩ : Zsqrtd 2) * ⟨1, 1⟩ = (fundamentalPellSol₁ 2 (by norm_num) not_isSquare_two : Zsqrtd 2)
    rw [fundamentalPellSol₁_two]
    ext <;> decide
  have hgt1 : 1 < Zsqrtd.toReal (by norm_num : (0 : ℤ) ≤ 2) (η : Zsqrtd 2) := by
    rw [Zsqrtd.toReal_apply]
    simp only [η, Int.cast_one, one_mul, Int.cast_ofNat]
    linarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
  rw [fundamentalPellUnit_eq_of_neg_norm_sq (by norm_num) not_isSquare_two η hnorm hsq hgt1]

theorem pellRegulator_two :
    pellRegulator 2 (by norm_num) not_isSquare_two = Real.log (1 + Real.sqrt 2) := by
  unfold pellRegulator
  rw [fundamentalPellUnit_two, Zsqrtd.toReal_apply]
  simp

/-- Explicit fundamental unit of `ℤ[√3]ˣ`: `ε₃ = 2 + √3` (norm `+1`; no norm-`-1` unit exists!). -/
theorem fundamentalPellSol₁_three :
    (fundamentalPellSol₁ 3 (by norm_num) not_isSquare_three : Zsqrtd 3) = ⟨2, 1⟩ := by
  let a : Pell.Solution₁ (3 : ℤ) := Pell.Solution₁.mk 2 1 (by norm_num)
  have ha : Pell.IsFundamental a := by
    refine ⟨by simp [a], by simp [a], fun {b} hb1 => ?_⟩
    change (2 : ℤ) ≤ b.x
    omega
  have heq := fundamentalPellSol₁_eq_of_isFundamental (d := 3) (by norm_num) not_isSquare_three ha
  rw [heq]
  ext
  · exact Pell.Solution₁.x_mk 2 1 _
  · exact Pell.Solution₁.y_mk 2 1 _

theorem no_neg_norm_unit_three :
    ¬ ∃ v : (Zsqrtd (3 : ℤ))ˣ, (v : Zsqrtd (3 : ℤ)).norm = -1 := by
  rintro ⟨v, hv⟩
  have hdef : (v : Zsqrtd 3).re * (v : Zsqrtd 3).re =
      3 * ((v : Zsqrtd 3).im * (v : Zsqrtd 3).im) - 1 := by
    have h : (v : Zsqrtd 3).re * (v : Zsqrtd 3).re - 3 * (v : Zsqrtd 3).im * (v : Zsqrtd 3).im = -1 := hv
    linarith
  have hmod : ((v : Zsqrtd 3).re * (v : Zsqrtd 3).re) % 3 = 2 := by omega
  have hr : (v : Zsqrtd 3).re % 3 = 0 ∨ (v : Zsqrtd 3).re % 3 = 1 ∨ (v : Zsqrtd 3).re % 3 = 2 := by omega
  rw [Int.mul_emod] at hmod
  rcases hr with h | h | h <;> rw [h] at hmod <;> norm_num at hmod

theorem fundamentalPellUnit_three :
    (fundamentalPellUnit 3 (by norm_num) not_isSquare_three : Zsqrtd 3) = ⟨2, 1⟩ := by
  classical
  unfold fundamentalPellUnit
  rw [dif_neg (by simpa using no_neg_norm_unit_three)]
  exact fundamentalPellSol₁_three

theorem pellRegulator_three :
    pellRegulator 3 (by norm_num) not_isSquare_three = Real.log (2 + Real.sqrt 3) := by
  unfold pellRegulator
  rw [fundamentalPellUnit_three, Zsqrtd.toReal_apply]
  simp

/-- Explicit norm-`+1` fundamental Pell solution for `d = 5`: `9 + 4√5`. -/
theorem fundamentalPellSol₁_five :
    (fundamentalPellSol₁ 5 (by norm_num) not_isSquare_five : Zsqrtd 5) = ⟨9, 4⟩ := by
  let a : Pell.Solution₁ (5 : ℤ) := Pell.Solution₁.mk 9 4 (by norm_num)
  have ha : Pell.IsFundamental a := by
    refine ⟨by simp [a], by simp [a], fun {b} hb1 => ?_⟩
    change (9 : ℤ) ≤ b.x
    by_contra hlt
    push Not at hlt
    have hprop := b.prop
    have hysq : b.y ^ 2 = (b.y.natAbs : ℤ) ^ 2 := by
      rw [sq, sq, ← Nat.cast_mul, Int.natAbs_mul_self]
    rw [hysq] at hprop
    have hy_le : b.y.natAbs < 4 := by
      by_contra hge
      push Not at hge
      have : (4 : ℤ) ≤ (b.y.natAbs : ℤ) := by exact_mod_cast hge
      nlinarith
    have hx_le : b.x < 9 := hlt
    have hx_gt : 1 < b.x := hb1
    interval_cases b.x <;> interval_cases b.y.natAbs <;> norm_num at hprop
  have heq := fundamentalPellSol₁_eq_of_isFundamental (d := 5) (by norm_num) not_isSquare_five ha
  rw [heq]
  ext
  · exact Pell.Solution₁.x_mk 9 4 _
  · exact Pell.Solution₁.y_mk 9 4 _

/-- Explicit fundamental unit of `ℤ[√5]ˣ`: `2 + √5` (norm `-1`, `(2 + √5)² = 9 + 4√5`). -/
theorem fundamentalPellUnit_five :
    (fundamentalPellUnit 5 (by norm_num) not_isSquare_five : Zsqrtd 5) = ⟨2, 1⟩ := by
  let η : (Zsqrtd (5 : ℤ))ˣ :=
    ⟨⟨2, 1⟩, ⟨-2, 1⟩, by ext <;> decide, by ext <;> decide⟩
  have hnorm : (η : Zsqrtd 5).norm = -1 := by decide
  have hsq : η ^ 2 = pellSolToUnitHom 5 (fundamentalPellSol₁ 5 (by norm_num) not_isSquare_five) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, sq]
    change (⟨2, 1⟩ : Zsqrtd 5) * ⟨2, 1⟩ = (fundamentalPellSol₁ 5 (by norm_num) not_isSquare_five : Zsqrtd 5)
    rw [fundamentalPellSol₁_five]
    ext <;> decide
  have hgt1 : 1 < Zsqrtd.toReal (by norm_num : (0 : ℤ) ≤ 5) (η : Zsqrtd 5) := by
    rw [Zsqrtd.toReal_apply]
    simp only [η, Int.cast_ofNat, Int.cast_one, one_mul]
    linarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)]
  rw [fundamentalPellUnit_eq_of_neg_norm_sq (by norm_num) not_isSquare_five η hnorm hsq hgt1]

theorem pellRegulator_five :
    pellRegulator 5 (by norm_num) not_isSquare_five = Real.log (2 + Real.sqrt 5) := by
  unfold pellRegulator
  rw [fundamentalPellUnit_five, Zsqrtd.toReal_apply]
  simp

/-- The golden ratio fundamental unit `φ = (1 + √5)/2` in the maximal order
`ℤ[(1 + √5)/2] = QuadraticAlgebra ℤ 1 1` (`ω² = ω + 1`), satisfying `norm φ = -1`,
`φ³ = 2 + √5`, and `φ⁶ = 9 + 4√5`. -/
def goldenUnit : (QuadraticAlgebra ℤ 1 1)ˣ where
  val := ⟨0, 1⟩
  inv := ⟨-1, 1⟩
  val_inv := by ext <;> decide
  inv_val := by ext <;> decide

theorem goldenUnit_norm : QuadraticAlgebra.norm (goldenUnit : QuadraticAlgebra ℤ 1 1) = -1 := by
  rw [QuadraticAlgebra.norm_def]
  simp [goldenUnit]

theorem goldenUnit_cube :
    ((goldenUnit ^ 3 : (QuadraticAlgebra ℤ 1 1)ˣ) : QuadraticAlgebra ℤ 1 1) = ⟨1, 2⟩ := by
  rw [Units.val_pow_eq_pow_val]
  ext <;> simp [goldenUnit, pow_succ]

theorem goldenUnit_pow_six :
    ((goldenUnit ^ 6 : (QuadraticAlgebra ℤ 1 1)ˣ) : QuadraticAlgebra ℤ 1 1) = ⟨5, 8⟩ := by
  rw [Units.val_pow_eq_pow_val]
  ext <;> simp [goldenUnit, pow_succ]

/-- Real embedding `ℤ[(1 + √5)/2] →+* ℝ` sending `a + b ω ↦ a + b * (1 + √5) / 2`. -/
def goldenOrderToReal : QuadraticAlgebra ℤ 1 1 →+* ℝ :=
  (QuadraticAlgebra.lift (R := ℤ) (a := 1) (b := 1) (A := ℝ)
    ⟨(1 + Real.sqrt 5) / 2, by
      have hsq : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
      simp only [one_smul]
      nlinarith⟩).toRingHom

theorem goldenOrderToReal_goldenUnit :
    goldenOrderToReal (goldenUnit : QuadraticAlgebra ℤ 1 1) = (1 + Real.sqrt 5) / 2 := by
  change (QuadraticAlgebra.lift (R := ℤ) (a := 1) (b := 1) (A := ℝ) _)
    (QuadraticAlgebra.omega (R := ℤ) (a := 1) (b := 1)) = (1 + Real.sqrt 5) / 2
  simp

end PellAndUnits

/-! ## Section 3: Real Quadratic Number Fields `ℚ(√d)`, Ring of Integers, Discriminant, & Minkowski `h = 1` -/

section RealQuadraticNumberFields

/-- Concrete real quadratic number field `ℚ(√d) := QuadraticAlgebra ℚ (d : ℚ) 0`. -/
abbrev QuadField (d : ℕ) : Type := QuadraticAlgebra ℚ (d : ℚ) 0

/-- Fundamental discriminant `D = d` (if `d ≡ 1 [MOD 4]`) or `D = 4d` (if `d ≡ 2, 3 [MOD 4]`). -/
abbrev fundDisc (d : ℕ) : ℕ := if d % 4 = 1 then d else 4 * d

lemma fundDisc_pos {d : ℕ} (hd : 0 < d) : 0 < fundDisc d := by
  unfold fundDisc; split_ifs <;> omega

instance fundDisc_neZero (d : ℕ) [Fact (1 < d)] : NeZero (fundDisc d) :=
  ⟨(fundDisc_pos (by have := Fact.out (p := 1 < d); omega)).ne'⟩

/-- Every squarefree `d > 1` is not a rational square: `∀ r : ℚ, r ^ 2 ≠ d + 0 * r`. -/
theorem quadField_irred {d : ℕ} (hd : Squarefree d) (hd1 : 1 < d) :
    ∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r := by
  intro r hr
  rw [zero_mul, add_zero] at hr
  have hmul : (r.num : ℚ) = r * (r.den : ℚ) := (Rat.mul_den_eq_num r).symm
  have hsq_q : ((r.num.natAbs ^ 2 : ℕ) : ℚ) = ((d * r.den ^ 2 : ℕ) : ℚ) := by
    have hnum_sq : ((r.num.natAbs ^ 2 : ℕ) : ℚ) = (r.num : ℚ) ^ 2 := by
      have h1 : (r.num.natAbs : ℚ) = |(r.num : ℚ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [Nat.cast_pow, h1, sq_abs]
    rw [hnum_sq, hmul, mul_pow, hr]
    push_cast; rfl
  have hsq : r.num.natAbs ^ 2 = d * r.den ^ 2 := Nat.cast_injective hsq_q
  have hcop : (r.den ^ 2).Coprime (r.num.natAbs ^ 2) := (r.reduced.symm.pow_left 2).pow_right 2
  have hdvd_den : r.den ^ 2 ∣ 1 := by
    have h1 : r.den ^ 2 ∣ r.num.natAbs ^ 2 := ⟨d, by linarith⟩
    exact hcop.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl h1
  have hden1 : r.den = 1 := by
    have h1 : r.den ^ 2 = 1 := Nat.dvd_one.mp hdvd_den
    nlinarith
  rw [hden1, one_pow, mul_one] at hsq
  have hu : IsUnit r.num.natAbs := hd r.num.natAbs (by rw [← hsq, sq])
  have hnum1 : r.num.natAbs = 1 := Nat.isUnit_iff.mp hu
  rw [hnum1, one_pow] at hsq
  omega

instance quadField_fact_irred (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
  ⟨quadField_irred Fact.out Fact.out⟩

instance quadField_field (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] : Field (QuadField d) :=
  QuadraticAlgebra.instField

/-- Exact degree `[ℚ(√d) : ℚ] = 2`. -/
theorem quadField_finrank (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    Module.finrank ℚ (QuadField d) = 2 := by
  have h := Module.finrank_eq_card_basis (QuadraticAlgebra.basis (d : ℚ) (0 : ℚ))
  simpa using h

instance quadField_numberField (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    NumberField (QuadField d) where
  to_charZero := QuadraticAlgebra.instCharZero
  to_finiteDimensional := Module.Finite.of_basis (QuadraticAlgebra.basis (d : ℚ) (0 : ℚ))

/-- Canonical positive real embedding `ℚ(√d) →+* ℝ` sending `a + b √d ↦ a + b * √d`. -/
def quadFieldToReal (d : ℕ) : QuadField d →+* ℝ :=
  (QuadraticAlgebra.lift (R := ℚ) (a := (d : ℚ)) (b := (0 : ℚ)) (A := ℝ)
    ⟨Real.sqrt (d : ℝ), by
      simp only [zero_smul, add_zero, Rat.smul_def, mul_one, Rat.cast_natCast]
      exact Real.mul_self_sqrt (Nat.cast_nonneg d)⟩).toRingHom

open Classical in
/-- `ℚ(√d)` is totally real: `nrComplexPlaces (QuadField d) = 0` and `nrRealPlaces = 2`. -/
theorem quadField_nrComplexPlaces (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    NumberField.InfinitePlace.nrComplexPlaces (QuadField d) = 0 := by
  let φ : QuadField d →+* ℂ := Complex.ofRealHom.comp (quadFieldToReal d)
  let w : NumberField.InfinitePlace (QuadField d) := NumberField.InfinitePlace.mk φ
  have hw_real : w.IsReal := by
    rw [NumberField.InfinitePlace.isReal_mk_iff]
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    simp [φ, Complex.conj_ofReal]
  have hpos : 0 < NumberField.InfinitePlace.nrRealPlaces (QuadField d) := by
    unfold NumberField.InfinitePlace.nrRealPlaces
    exact Fintype.card_pos_iff.mpr ⟨⟨w, hw_real⟩⟩
  have hcard := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (QuadField d)
  rw [quadField_finrank d] at hcard
  omega

theorem quadField_nrRealPlaces (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    NumberField.InfinitePlace.nrRealPlaces (QuadField d) = 2 := by
  have hcard := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (QuadField d)
  rw [quadField_finrank d, quadField_nrComplexPlaces d] at hcard
  omega

/-- Helper: entries of `Algebra.leftMulMatrix (QuadraticAlgebra.basis (d : ℚ) 0) x`. -/
private lemma quadField_leftMulMatrix_entries (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)]
    (x : QuadField d) :
    let b := QuadraticAlgebra.basis (d : ℚ) (0 : ℚ)
    Algebra.leftMulMatrix b x 0 0 = x.re ∧
    Algebra.leftMulMatrix b x 1 0 = x.im ∧
    Algebra.leftMulMatrix b x 0 1 = (d : ℚ) * x.im ∧
    Algebra.leftMulMatrix b x 1 1 = x.re := by
  set b := QuadraticAlgebra.basis (d : ℚ) (0 : ℚ)
  have hb0 : b 0 = 1 := by
    apply (QuadraticAlgebra.linearEquivTuple (d : ℚ) (0 : ℚ)).injective
    ext i; fin_cases i <;>
      simp [b, QuadraticAlgebra.basis, QuadraticAlgebra.linearEquivTuple_apply,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hb1 : b 1 = ⟨0, 1⟩ := by
    apply (QuadraticAlgebra.linearEquivTuple (d : ℚ) (0 : ℚ)).injective
    ext i; fin_cases i <;>
      simp [b, QuadraticAlgebra.basis, QuadraticAlgebra.linearEquivTuple_apply]
  have hrepr : ∀ (z : QuadField d), b.repr z 0 = z.re ∧ b.repr z 1 = z.im := fun z => by
    constructor <;> simp [b, QuadraticAlgebra.basis, QuadraticAlgebra.linearEquivTuple_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Algebra.leftMulMatrix_eq_repr_mul, hb0, mul_one]; exact (hrepr x).1
  · rw [Algebra.leftMulMatrix_eq_repr_mul, hb0, mul_one]; exact (hrepr x).2
  · rw [Algebra.leftMulMatrix_eq_repr_mul, hb1, (hrepr _).1]
    simp [QuadraticAlgebra.re_mul]
  · rw [Algebra.leftMulMatrix_eq_repr_mul, hb1, (hrepr _).2]
    simp [QuadraticAlgebra.im_mul]

/-- Explicit `Algebra.norm ℚ` formula on `QuadField d`: `N(u + v √d) = u^2 - d * v^2`. -/
theorem quadField_norm_eq (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] (x : QuadField d) :
    Algebra.norm ℚ x = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := by
  rw [Algebra.norm_eq_matrix_det (QuadraticAlgebra.basis (d : ℚ) (0 : ℚ)) x, Matrix.det_fin_two]
  obtain ⟨h00, h10, h01, h11⟩ := quadField_leftMulMatrix_entries d x
  rw [h00, h10, h01, h11]; ring

/-- Explicit `Algebra.trace ℚ` formula on `QuadField d`: `Tr(u + v √d) = 2 * u`. -/
theorem quadField_trace_eq (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] (x : QuadField d) :
    Algebra.trace ℚ (QuadField d) x = 2 * x.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (d : ℚ) (0 : ℚ)) x, Matrix.trace_fin_two]
  obtain ⟨h00, _, _, h11⟩ := quadField_leftMulMatrix_entries d x
  rw [h00, h11]; ring

/-- The standard integral generator `ω_d` of `𝓞 (QuadField d)` inside `QuadField d`:
`ω_d = (1 + √d) / 2` if `d ≡ 1 [MOD 4]`, and `ω_d = √d` if `d ≡ 2, 3 [MOD 4]`. -/
def quadGenVal (d : ℕ) : QuadField d :=
  if d % 4 = 1 then ⟨1 / 2, 1 / 2⟩ else ⟨0, 1⟩

/-- The defining monic quadratic polynomial `f_d(X) ∈ ℤ[X]` of `ω_d`:
- `X^2 - X - (d - 1)/4` if `d ≡ 1 [MOD 4]`
- `X^2 - d` if `d ≡ 2, 3 [MOD 4]`. -/
def quadMinPolyInt (d : ℕ) : Polynomial ℤ :=
  if d % 4 = 1 then
    Polynomial.X ^ 2 - Polynomial.X - Polynomial.C (((d : ℤ) - 1) / 4)
  else
    Polynomial.X ^ 2 - Polynomial.C (d : ℤ)

theorem quadMinPolyInt_monic (d : ℕ) : (quadMinPolyInt d).Monic := by
  unfold quadMinPolyInt
  split_ifs
  · have hdeg1 : (Polynomial.X + Polynomial.C (((d : ℤ) - 1) / 4) : Polynomial ℤ).degree <
        (Polynomial.X ^ 2 : Polynomial ℤ).degree := by
      have h1 : (Polynomial.X : Polynomial ℤ).degree = 1 := Polynomial.degree_X
      have h2 : (Polynomial.X ^ 2 : Polynomial ℤ).degree = 2 := by
        rw [Polynomial.degree_X_pow]; rfl
      have hc : (Polynomial.C (((d : ℤ) - 1) / 4) : Polynomial ℤ).degree ≤ 0 :=
        Polynomial.degree_C_le
      have hle := Polynomial.degree_add_le (Polynomial.X : Polynomial ℤ)
        (Polynomial.C (((d : ℤ) - 1) / 4))
      rw [h1] at hle
      rw [h2]
      exact lt_of_le_of_lt hle (by
        have : max (1 : WithBot ℕ) (Polynomial.C (((d : ℤ) - 1) / 4) : Polynomial ℤ).degree ≤ 1 :=
          max_le le_rfl (le_trans hc (by decide))
        exact lt_of_le_of_lt this (by decide))
    rw [sub_sub]
    exact (Polynomial.monic_X_pow 2).sub_of_left hdeg1
  · exact Polynomial.monic_X_pow_sub_C (d : ℤ) (by norm_num)

theorem quadMinPolyInt_natDegree (d : ℕ) : (quadMinPolyInt d).natDegree = 2 := by
  unfold quadMinPolyInt
  split_ifs
  · rw [sub_sub]
    have hdeg1 : (Polynomial.X + Polynomial.C (((d : ℤ) - 1) / 4) : Polynomial ℤ).natDegree <
        (Polynomial.X ^ 2 : Polynomial ℤ).natDegree := by
      rw [Polynomial.natDegree_X_pow]
      have hle := Polynomial.natDegree_add_le (Polynomial.X : Polynomial ℤ)
        (Polynomial.C (((d : ℤ) - 1) / 4))
      rw [Polynomial.natDegree_X, Polynomial.natDegree_C] at hle
      omega
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hdeg1, Polynomial.natDegree_X_pow]
  · rw [Polynomial.natDegree_X_pow_sub_C]

theorem quadGenVal_aeval_zero (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    Polynomial.aeval (quadGenVal d) (quadMinPolyInt d) = 0 := by
  unfold quadMinPolyInt quadGenVal
  split_ifs with h1
  · have hd4 : ((d : ℤ) - 1) / 4 * 4 = (d : ℤ) - 1 := by omega
    have hq4 : ((((d : ℤ) - 1) / 4 : ℤ) : ℚ) = ((d : ℚ) - 1) / 4 := by
      have hq : ((((d : ℤ) - 1) / 4 : ℤ) : ℚ) * 4 = (d : ℚ) - 1 := by exact_mod_cast hd4
      linarith
    rw [map_sub, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast, sq]
    ext
    · simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
        QuadraticAlgebra.re_zero]
      rw [hq4]; ring
    · simp only [QuadraticAlgebra.im_sub, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_intCast,
        QuadraticAlgebra.im_zero]
      ring
  · rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast, sq]
    ext
    · simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_zero,
        Int.cast_natCast, QuadraticAlgebra.re_natCast]
      ring
    · simp only [QuadraticAlgebra.im_sub, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_zero,
        Int.cast_natCast, QuadraticAlgebra.im_natCast]
      ring

theorem quadGenVal_isIntegral (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    IsIntegral ℤ (quadGenVal d) :=
  ⟨quadMinPolyInt d, quadMinPolyInt_monic d, by
    simpa [Polynomial.aeval_def] using quadGenVal_aeval_zero d⟩

/-- The integral generator `ω_d` as an element of `𝓞 (QuadField d)`. -/
def quadIntGen (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] : 𝓞 (QuadField d) :=
  ⟨quadGenVal d, quadGenVal_isIntegral d⟩

/-- **Exact Integral Characterization of `𝓞 (QuadField d)`**:
`x ∈ 𝓞 (QuadField d)` iff `∃ a b : ℤ, x = a + b * ω_d`! -/
theorem mem_ringOfIntegers_quadField_iff (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)]
    (x : QuadField d) :
    IsIntegral ℤ x ↔ ∃ a b : ℤ, x = (a : QuadField d) + (b : QuadField d) * quadGenVal d := by
  have hsqf : Squarefree d := Fact.out
  constructor
  · intro hx
    have hnorm_int : IsIntegral ℤ (Algebra.norm ℚ x) := Algebra.isIntegral_norm ℚ hx
    have hx1_int : IsIntegral ℤ (x + 1) := hx.add isIntegral_one
    have hnorm1_int : IsIntegral ℤ (Algebra.norm ℚ (x + 1)) := Algebra.isIntegral_norm ℚ hx1_int
    obtain ⟨c, hc⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hnorm_int
    obtain ⟨c₁, hc₁⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hnorm1_int
    have hnc : x.re ^ 2 - (d : ℚ) * x.im ^ 2 = (c : ℚ) := by
      rw [← quadField_norm_eq d x]; exact hc.symm
    have hnc1 : (x.re + 1) ^ 2 - (d : ℚ) * x.im ^ 2 = (c₁ : ℚ) := by
      have h := quadField_norm_eq d (x + 1)
      have hre : (x + 1).re = x.re + 1 := by simp [QuadraticAlgebra.re_one]
      have him : (x + 1).im = x.im := by simp [QuadraticAlgebra.im_one]
      rw [hre, him] at h
      rw [← h]; exact hc₁.symm
    set a : ℤ := c₁ - c - 1
    have ha : (2 : ℚ) * x.re = (a : ℚ) := by
      push_cast [a]; linarith
    set v2 : ℚ := 2 * x.im
    have hv2_sq : (d : ℚ) * v2 ^ 2 = ((a ^ 2 - 4 * c : ℤ) : ℚ) := by
      dsimp only [v2]; push_cast; nlinarith
    have hv2_den : v2.den = 1 := by
      have hmul : (v2.num : ℚ) = v2 * (v2.den : ℚ) := (Rat.mul_den_eq_num v2).symm
      have hq_eq : (((d * v2.num.natAbs ^ 2 : ℕ) : ℤ) : ℚ) =
          (((a ^ 2 - 4 * c) * ((v2.den ^ 2 : ℕ) : ℤ) : ℤ) : ℚ) := by
        push_cast
        rw [sq_abs, hmul, mul_pow]
        have h := hv2_sq
        push_cast at h
        linear_combination (v2.den : ℚ) ^ 2 * h
      have hz_eq : ((d * v2.num.natAbs ^ 2 : ℕ) : ℤ) =
          (a ^ 2 - 4 * c) * ((v2.den ^ 2 : ℕ) : ℤ) := Int.cast_injective hq_eq
      have hden_dvd_z : ((v2.den ^ 2 : ℕ) : ℤ) ∣ ((d * v2.num.natAbs ^ 2 : ℕ) : ℤ) :=
        ⟨a ^ 2 - 4 * c, by linarith⟩
      have hden_dvd : v2.den ^ 2 ∣ d * v2.num.natAbs ^ 2 := Int.ofNat_dvd.mp hden_dvd_z
      have hcop : (v2.den ^ 2).Coprime (v2.num.natAbs ^ 2) :=
        (v2.reduced.symm.pow_left 2).pow_right 2
      have hden_dvd_d : v2.den ^ 2 ∣ d := hcop.dvd_of_dvd_mul_right hden_dvd
      have hu : IsUnit v2.den := hsqf v2.den (by simpa [sq] using hden_dvd_d)
      exact Nat.isUnit_iff.mp hu
    set b : ℤ := v2.num
    have hb : (2 : ℚ) * x.im = (b : ℚ) := by
      have hmul := (Rat.mul_den_eq_num v2).symm
      rw [hv2_den, Nat.cast_one, mul_one] at hmul
      exact hmul.symm
    have hcong_q : ((a ^ 2 - (d : ℤ) * b ^ 2 : ℤ) : ℚ) = ((4 * c : ℤ) : ℚ) := by
      have h1 : (b : ℚ) = v2 := hb.symm
      push_cast
      rw [h1]
      have h2 := hv2_sq
      push_cast at h2
      linarith
    have hcong : a ^ 2 - (d : ℤ) * b ^ 2 = 4 * c := Int.cast_injective hcong_q
    have hz4 : ((a : ZMod 4) ^ 2 - (d : ZMod 4) * (b : ZMod 4) ^ 2) = 0 := by
      have h := congrArg (Int.cast (R := ZMod 4)) hcong
      have h4 : (4 : ZMod 4) = 0 := by decide
      simpa [h4] using h
    have hd_mod4_ne0 : d % 4 ≠ 0 := by
      intro h0
      have hdvd4 : 2 * 2 ∣ d := by omega
      have hu2 : IsUnit (2 : ℕ) := hsqf 2 hdvd4
      exact (by norm_num : ¬ IsUnit (2 : ℕ)) hu2
    by_cases hd1 : d % 4 = 1
    · have hd_z4 : (d : ZMod 4) = 1 := by
        rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]; exact hd1
      rw [hd_z4, one_mul] at hz4
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
      unfold quadGenVal
      rw [if_pos hd1]
      ext
      · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
          QuadraticAlgebra.im_intCast]
        rw [hab_q]; linarith
      · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast,
          QuadraticAlgebra.im_intCast, zero_mul, add_zero, zero_add]
        linarith
    · have hd_cases : (d : ZMod 4) = 2 ∨ (d : ZMod 4) = 3 := by
        have h23 : d % 4 = 2 ∨ d % 4 = 3 := by omega
        rcases h23 with h2 | h3
        · left; rw [← Nat.cast_ofNat (n := 2), ZMod.natCast_eq_natCast_iff]; exact h2
        · right; rw [← Nat.cast_ofNat (n := 3), ZMod.natCast_eq_natCast_iff]; exact h3
      have hab_z2 : (a : ZMod 2) = 0 ∧ (b : ZMod 2) = 0 := by
        have hcast : ∀ n : ℤ, (n : ZMod 2) = ZMod.cast (n : ZMod 4) := fun n => by
          rw [ZMod.cast_intCast (by norm_num : 2 ∣ 4)]
        rw [hcast a, hcast b]
        rcases hd_cases with h2 | h3
        · rw [h2] at hz4
          generalize ha4 : (a : ZMod 4) = xa at hz4 ⊢
          generalize hb4 : (b : ZMod 4) = xb at hz4 ⊢
          fin_cases xa <;> fin_cases xb <;> first | decide | (exfalso; revert hz4; decide)
        · rw [h3] at hz4
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
      unfold quadGenVal
      rw [if_neg hd1]
      ext
      · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
          QuadraticAlgebra.im_intCast, mul_zero, zero_mul, add_zero]
        rw [ha_q]; linarith
      · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast,
          QuadraticAlgebra.im_intCast, mul_one, zero_mul, add_zero, zero_add]
        rw [hb_q]; linarith
  · rintro ⟨a, b, rfl⟩
    exact (isIntegral_intCast (R := ℤ) a).add ((isIntegral_intCast (R := ℤ) b).mul (quadGenVal_isIntegral d))

/-- Explicit `ℤ`-basis `![1, ω_d]` of `𝓞 (QuadField d)`. -/
def quadIntBasis (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    Module.Basis (Fin 2) ℤ (𝓞 (QuadField d)) :=
  Module.Basis.mk (v := ![1, quadIntGen d])
    (by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hval := congrArg Subtype.val hg
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        zsmul_eq_mul, mul_one] at hval
      change (g 0 : QuadField d) + (g 1 : QuadField d) * quadGenVal d = 0 at hval
      have him := congrArg QuadraticAlgebra.im hval
      have hre := congrArg QuadraticAlgebra.re hval
      unfold quadGenVal at him hre
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
      obtain ⟨a, b, hab⟩ := (mem_ringOfIntegers_quadField_iff d x.1).mp x.2
      have hx_eq : x = a • (1 : 𝓞 (QuadField d)) + b • quadIntGen d := by
        rw [zsmul_eq_mul, zsmul_eq_mul, mul_one]
        apply Subtype.ext
        change (x : QuadField d) = (a : QuadField d) + (b : QuadField d) * quadGenVal d
        exact hab
      rw [hx_eq]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ a (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ b (Submodule.subset_span ⟨1, rfl⟩)))

/-- Monogenicity of `𝓞 (QuadField d)`: `Algebra.adjoin ℤ {quadIntGen d} = ⊤`! -/
theorem quadField_adjoin_eq_top (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    Algebra.adjoin ℤ ({quadIntGen d} : Set (𝓞 (QuadField d))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, hab⟩ := (mem_ringOfIntegers_quadField_iff d x.1).mp x.2
  have hx_eq : x = algebraMap ℤ (𝓞 (QuadField d)) a +
      algebraMap ℤ (𝓞 (QuadField d)) b * quadIntGen d := by
    apply Subtype.ext
    change (x : QuadField d) = (a : QuadField d) + (b : QuadField d) * quadGenVal d
    exact hab
  rw [hx_eq]
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ a)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ b) (Algebra.subset_adjoin rfl))

/-- Therefore the conductor of `quadIntGen d` is `⊤` (so Kummer–Dedekind applies at EVERY prime `p`)! -/
theorem quadField_conductor_eq_top (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    conductor ℤ (quadIntGen d) = ⊤ :=
  conductor_eq_top_of_adjoin_eq_top (quadField_adjoin_eq_top d)

/-- Exact minimal polynomial of `quadIntGen d` over `ℤ`: `minpoly ℤ (quadIntGen d) = quadMinPolyInt d`. -/
theorem minpoly_quadIntGen (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    minpoly ℤ (quadIntGen d) = quadMinPolyInt d := by
  have hint : IsIntegral ℤ (quadIntGen d) := Algebra.IsIntegral.isIntegral (quadIntGen d)
  have haeval : Polynomial.aeval (quadIntGen d) (quadMinPolyInt d) = 0 := by
    apply Subtype.ext
    have h1 := quadGenVal_aeval_zero d
    have hhom := Polynomial.aeval_algebraMap_apply (QuadField d) (quadIntGen d) (quadMinPolyInt d)
    change (algebraMap (𝓞 (QuadField d)) (QuadField d))
      (Polynomial.aeval (quadIntGen d) (quadMinPolyInt d)) = 0
    rw [← hhom]
    exact h1
  have hdvd : minpoly ℤ (quadIntGen d) ∣ quadMinPolyInt d :=
    minpoly.isIntegrallyClosed_dvd hint haeval
  have hdeg_le : (minpoly ℤ (quadIntGen d)).natDegree ≤ 2 := by
    rw [← quadMinPolyInt_natDegree d]
    exact Polynomial.natDegree_le_of_dvd hdvd (quadMinPolyInt_monic d).ne_zero
  have hdeg_pos : 0 < (minpoly ℤ (quadIntGen d)).natDegree := minpoly.natDegree_pos hint
  have hdeg_ne1 : (minpoly ℤ (quadIntGen d)).natDegree ≠ 1 := by
    intro h1
    have hmon := minpoly.monic hint
    have hcoeff1 : (minpoly ℤ (quadIntGen d)).coeff 1 = 1 := by
      rw [← h1]; exact hmon.coeff_natDegree
    have hlin : minpoly ℤ (quadIntGen d) =
        Polynomial.X + Polynomial.C ((minpoly ℤ (quadIntGen d)).coeff 0) := by
      have h := Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq h1)
      rw [hcoeff1, map_one, one_mul] at h
      exact h
    have h0 := minpoly.aeval ℤ (quadIntGen d)
    rw [hlin, map_add, Polynomial.aeval_X, Polynomial.aeval_C] at h0
    have hval := congrArg (algebraMap (𝓞 (QuadField d)) (QuadField d)) h0
    rw [map_add, map_zero, eq_intCast, map_intCast] at hval
    have him := congrArg QuadraticAlgebra.im hval
    simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_intCast, QuadraticAlgebra.im_zero,
      add_zero] at him
    change (quadGenVal d).im = 0 at him
    unfold quadGenVal at him
    split_ifs at him <;> norm_num at him
  have hdeg2 : (minpoly ℤ (quadIntGen d)).natDegree = 2 := by omega
  obtain ⟨q, hq⟩ := hdvd
  have hq_mon : q.Monic := by
    have hm := quadMinPolyInt_monic d
    rw [hq] at hm
    exact (Polynomial.Monic.of_mul_monic_left (minpoly.monic hint) hm)
  have hq_deg : q.natDegree = 0 := by
    have h := congrArg Polynomial.natDegree hq
    rw [quadMinPolyInt_natDegree d,
      Polynomial.natDegree_mul (minpoly.ne_zero hint) hq_mon.ne_zero, hdeg2] at h
    omega
  have hq1 : q = 1 := Polynomial.eq_one_of_monic_natDegree_zero hq_mon hq_deg
  rw [hq, hq1, mul_one]

/-- Helper: quadratic relation of `quadIntGen d` in `𝓞 (QuadField d)`. -/
lemma quadIntGen_sq (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    quadIntGen d * quadIntGen d =
      if d % 4 = 1 then
        ((((d : ℤ) - 1) / 4 : ℤ) : 𝓞 (QuadField d)) + quadIntGen d
      else
        ((d : ℤ) : 𝓞 (QuadField d)) := by
  have h := quadGenVal_aeval_zero d
  unfold quadMinPolyInt at h
  apply Subtype.ext
  split_ifs with h1
  · rw [if_pos h1, map_sub, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast] at h
    change quadGenVal d * quadGenVal d = ((((d : ℤ) - 1) / 4 : ℤ) : QuadField d) + quadGenVal d
    rw [← sq]; linear_combination h
  · rw [if_neg h1, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast] at h
    change quadGenVal d * quadGenVal d = ((d : ℤ) : QuadField d)
    rw [← sq]; linear_combination h

/-- **Exact Discriminant of `ℚ(√d)`**: `NumberField.discr (QuadField d) = fundDisc d`! -/
theorem quadField_discr (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    NumberField.discr (QuadField d) = (fundDisc d : ℤ) := by
  rw [← NumberField.discr_eq_discr (QuadField d) (quadIntBasis d)]
  rw [Algebra.discr_def, Matrix.det_fin_two]
  set b := quadIntBasis d
  have hb0 : b 0 = 1 := by simp [b, quadIntBasis]
  have hb1 : b 1 = quadIntGen d := by simp [b, quadIntBasis]
  have hrepr : ∀ (u v : ℤ), b.repr ((u : 𝓞 (QuadField d)) + (v : 𝓞 (QuadField d)) * quadIntGen d) 0 = u ∧
      b.repr ((u : 𝓞 (QuadField d)) + (v : 𝓞 (QuadField d)) * quadIntGen d) 1 = v := by
    intro u v
    have hlin : (u : 𝓞 (QuadField d)) + (v : 𝓞 (QuadField d)) * quadIntGen d =
        u • b 0 + v • b 1 := by rw [hb0, hb1, zsmul_eq_mul, zsmul_eq_mul, mul_one]
    rw [hlin, map_add, map_smul, map_smul, b.repr_self, b.repr_self]
    simp
  have htr_lin : ∀ (u v : ℤ),
      Algebra.trace ℤ (𝓞 (QuadField d)) ((u : 𝓞 (QuadField d)) + (v : 𝓞 (QuadField d)) * quadIntGen d) =
        if d % 4 = 1 then 2 * u + v else 2 * u := by
    intro u v
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two,
      Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, mul_one]
    rw [(hrepr u v).1]
    have hmul : ((u : 𝓞 (QuadField d)) + (v : 𝓞 (QuadField d)) * quadIntGen d) * quadIntGen d =
        if d % 4 = 1 then
          ((v * (((d : ℤ) - 1) / 4) : ℤ) : 𝓞 (QuadField d)) +
            ((u + v : ℤ) : 𝓞 (QuadField d)) * quadIntGen d
        else
          ((v * (d : ℤ) : ℤ) : 𝓞 (QuadField d)) + (u : 𝓞 (QuadField d)) * quadIntGen d := by
      rw [add_mul, mul_assoc, quadIntGen_sq d]
      split_ifs <;> push_cast <;> ring
    rw [hmul]
    split_ifs
    · rw [(hrepr _ _).2]; ring
    · rw [(hrepr _ _).2]; ring
  have htr1 : Algebra.trace ℤ (𝓞 (QuadField d)) 1 = 2 := by
    have h := htr_lin 1 0
    simp only [Int.cast_one, Int.cast_zero, zero_mul, add_zero] at h
    rw [h]; split_ifs <;> ring
  have htr_w : Algebra.trace ℤ (𝓞 (QuadField d)) (quadIntGen d) = if d % 4 = 1 then 1 else 0 := by
    have h := htr_lin 0 1
    simp only [Int.cast_zero, Int.cast_one, one_mul, zero_add] at h
    rw [h]; split_ifs <;> ring
  have htr_w2 : Algebra.trace ℤ (𝓞 (QuadField d)) (quadIntGen d * quadIntGen d) =
      if d % 4 = 1 then 2 * (((d : ℤ) - 1) / 4) + 1 else 2 * (d : ℤ) := by
    rw [quadIntGen_sq d]
    split_ifs with h1
    · have h := htr_lin (((d : ℤ) - 1) / 4) 1
      simp only [Int.cast_one, one_mul, if_pos h1] at h
      exact h
    · have h := htr_lin (d : ℤ) 0
      simp only [Int.cast_zero, zero_mul, add_zero, if_neg h1] at h
      exact h
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb0, hb1, mul_one, one_mul,
    htr1, htr_w, htr_w2]
  unfold fundDisc
  split_ifs with h1
  · have hd4 : ((d : ℤ) - 1) / 4 * 4 = (d : ℤ) - 1 := by omega
    linarith
  · push_cast; ring

/-- **Minkowski Class-Number-One Theorem for Real Quadratic Fields**:
Every real quadratic field `ℚ(√d)` (`d > 1` squarefree) with fundamental discriminant `fundDisc d < 16`
(in particular `ℚ(√5)`, `ℚ(√2)`, `ℚ(√3)`, `ℚ(√13)`) has **class number `1`** (`h(D) = 1`)! -/
theorem classNumber_quadField_eq_one_of_fundDisc_lt_16 (d : ℕ)
    [Fact (Squarefree d)] [Fact (1 < d)] (hlt : fundDisc d < 16) :
    NumberField.classNumber (QuadField d) = 1 := by
  have hsub : Subsingleton (ClassGroup (𝓞 (QuadField d))) := by
    refine ⟨fun C₁ C₂ => ?_⟩
    have htriv : ∀ C : ClassGroup (𝓞 (QuadField d)), C = 1 := by
      intro C
      obtain ⟨I, hIC, hnorm⟩ := NumberField.exists_ideal_in_class_of_norm_le C
      rw [quadField_nrComplexPlaces d, quadField_finrank d, quadField_discr d, pow_zero, one_mul] at hnorm
      have hdiscr_lt : (|(fundDisc d : ℝ)|) < 16 := by
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast hlt
      have hsqrt_lt : Real.sqrt (|(fundDisc d : ℝ)|) < 4 := by
        rw [show (4 : ℝ) = Real.sqrt 16 by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_lt_sqrt (abs_nonneg _) hdiscr_lt
      have hnorm_lt2 : (Ideal.absNorm (I : Ideal (𝓞 (QuadField d))) : ℝ) < 2 := by
        have hfac : ((2 : ℕ).factorial : ℝ) / ((2 : ℕ) : ℝ) ^ 2 = 1 / 2 := by norm_num
        simp only [Int.cast_natCast] at hnorm
        rw [hfac] at hnorm
        linarith
      have hnorm_lt2_nat : Ideal.absNorm (I : Ideal (𝓞 (QuadField d))) < 2 := by
        exact_mod_cast hnorm_lt2
      have hIne : (I : Ideal (𝓞 (QuadField d))) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
      have hnorm_pos : 0 < Ideal.absNorm (I : Ideal (𝓞 (QuadField d))) :=
        absNorm_pos_of_ne_bot hIne
      have hnorm1 : Ideal.absNorm (I : Ideal (𝓞 (QuadField d))) = 1 := by omega
      have hItop : (I : Ideal (𝓞 (QuadField d))) = ⊤ := Ideal.absNorm_eq_one_iff.mp hnorm1
      rw [← hIC]
      have hI1 : I = 1 := Subtype.ext (by simpa using hItop)
      rw [hI1, map_one]
    rw [htriv C₁, htriv C₂]
  let : Unique (ClassGroup (𝓞 (QuadField d))) := uniqueOfSubsingleton 1
  unfold NumberField.classNumber
  exact Fintype.card_unique

lemma squarefree_two : Squarefree (2 : ℕ) := (by norm_num : Nat.Prime 2).squarefree
lemma squarefree_three : Squarefree (3 : ℕ) := (by norm_num : Nat.Prime 3).squarefree
lemma squarefree_five : Squarefree (5 : ℕ) := (by norm_num : Nat.Prime 5).squarefree
lemma squarefree_thirteen : Squarefree (13 : ℕ) := (by norm_num : Nat.Prime 13).squarefree

instance : Fact (Squarefree (2 : ℕ)) := ⟨squarefree_two⟩
instance : Fact (1 < (2 : ℕ)) := ⟨by norm_num⟩
instance : Fact (Squarefree (3 : ℕ)) := ⟨squarefree_three⟩
instance : Fact (1 < (3 : ℕ)) := ⟨by norm_num⟩
instance : Fact (Squarefree (5 : ℕ)) := ⟨squarefree_five⟩
instance : Fact (1 < (5 : ℕ)) := ⟨by norm_num⟩
instance : Fact (Squarefree (13 : ℕ)) := ⟨squarefree_thirteen⟩
instance : Fact (1 < (13 : ℕ)) := ⟨by norm_num⟩

/-- **Concrete Class-Number-One Verification for `ℚ(√5)` (`D = 5`, `h(5) = 1`)**! -/
theorem classNumber_quadField_5 : NumberField.classNumber (QuadField 5) = 1 :=
  classNumber_quadField_eq_one_of_fundDisc_lt_16 5 (by decide)

/-- **Concrete Class-Number-One Verification for `ℚ(√2)` (`D = 8`, `h(8) = 1`)**! -/
theorem classNumber_quadField_2 : NumberField.classNumber (QuadField 2) = 1 :=
  classNumber_quadField_eq_one_of_fundDisc_lt_16 2 (by decide)

/-- **Concrete Class-Number-One Verification for `ℚ(√3)` (`D = 12`, `h(12) = 1`)**! -/
theorem classNumber_quadField_3 : NumberField.classNumber (QuadField 3) = 1 :=
  classNumber_quadField_eq_one_of_fundDisc_lt_16 3 (by decide)

/-- **Bonus Concrete Class-Number-One Verification for `ℚ(√13)` (`D = 13`, `h(13) = 1`)**! -/
theorem classNumber_quadField_13 : NumberField.classNumber (QuadField 13) = 1 :=
  classNumber_quadField_eq_one_of_fundDisc_lt_16 13 (by decide)

end RealQuadraticNumberFields

/-! ## Section 4: Kronecker Character `χ_D`, Kummer–Dedekind Prime Splitting, & Exact Dedekind Zeta Factorization -/

section QuadraticDedekindZeta

/-- Convert `z ∈ {1, -1} ⊂ ℤ` to a unit in `ℤˣ`. -/
private def intUnitOfPmOne (z : ℤ) : ℤˣ :=
  if z = 1 then 1 else -1

private lemma coe_intUnitOfPmOne {z : ℤ} (hz : z = 1 ∨ z = -1) :
    ((intUnitOfPmOne z : ℤˣ) : ℤ) = z := by
  unfold intUnitOfPmOne
  rcases hz with rfl | rfl <;> simp

/-- Jacobi symbol as a `ℤˣ`-valued homomorphism on `(ZMod m)ˣ` for any odd `m`. -/
private def jacobiUnitHom (m : ℕ) [NeZero m] (hm : _root_.Odd m) : (ZMod m)ˣ →* ℤˣ where
  toFun u := intUnitOfPmOne (jacobiSym ((u : ZMod m).val : ℤ) m)
  map_one' := by
    have hm1 : 1 ≤ m := NeZero.pos m
    by_cases h1 : m = 1
    · subst h1
      have h0 : ((1 : ZMod 1).val : ℤ) = 0 := by decide
      simp [intUnitOfPmOne, h0]
    · have : Fact (1 < m) := ⟨by omega⟩
      have hval : ((1 : (ZMod m)ˣ) : ZMod m).val = 1 := by
        rw [Units.val_one, ZMod.val_one]
      show intUnitOfPmOne (jacobiSym (((1 : (ZMod m)ˣ) : ZMod m).val : ℤ) m) = 1
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
    change ((intUnitOfPmOne (jacobiSym (((u * v : (ZMod m)ˣ) : ZMod m).val : ℤ) m) : ℤˣ) : ℤ) =
      ((intUnitOfPmOne (jacobiSym ((u : ZMod m).val : ℤ) m) *
        intUnitOfPmOne (jacobiSym ((v : ZMod m).val : ℤ) m) : ℤˣ) : ℤ)
    rw [coe_intUnitOfPmOne (hpm (u * v))]
    conv_rhs => rw [Units.val_mul]
    rw [coe_intUnitOfPmOne (hpm u), coe_intUnitOfPmOne (hpm v)]
    have hmod : (((u * v : (ZMod m)ˣ) : ZMod m).val : ℤ) ≡
        ((u : ZMod m).val : ℤ) * ((v : ZMod m).val : ℤ) [ZMOD (m : ℕ)] := by
      rw [← ZMod.intCast_eq_intCast_iff]
      push_cast
      simp only [ZMod.natCast_zmod_val]
    rw [jacobiSym.mod_left' hmod, jacobiSym.mul_left]

private lemma coe_jacobiUnitHom {m : ℕ} [NeZero m] (hm : _root_.Odd m) (u : (ZMod m)ˣ) :
    ((jacobiUnitHom m hm u : ℤˣ) : ℤ) = jacobiSym ((u : ZMod m).val : ℤ) m := by
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
  exact coe_intUnitOfPmOne hpm

private def chi4UnitHom : (ZMod 4)ˣ →* ℤˣ where
  toFun u := if (u : ZMod 4) = 1 then 1 else -1
  map_one' := by decide
  map_mul' u v := by fin_cases u <;> fin_cases v <;> decide

private def chi8UnitHom : (ZMod 8)ˣ →* ℤˣ where
  toFun u := if (u : ZMod 8) = 1 ∨ (u : ZMod 8) = 7 then 1 else -1
  map_one' := by decide
  map_mul' u v := by fin_cases u <;> fin_cases v <;> decide

private lemma coe_chi4UnitHom_nat {n : ℕ} (hn : _root_.Odd n) (hu : IsUnit (n : ZMod 4)) :
    ((chi4UnitHom hu.unit : ℤˣ) : ℤ) = if n % 4 = 1 then 1 else -1 := by
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

private lemma coe_chi8UnitHom_nat {n : ℕ} (hn : _root_.Odd n) (hu : IsUnit (n : ZMod 8)) :
    ((chi8UnitHom hu.unit : ℤˣ) : ℤ) = jacobiSym 2 n := by
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

/-- Helper: squarefree `d > 1` satisfies `d % 4 ∈ {1, 2, 3}`. -/
private lemma squarefree_mod_four_ne_zero {d : ℕ} (hd : Squarefree d) : d % 4 ≠ 0 := by
  intro h0
  have hdvd : 2 * 2 ∣ d := by omega
  exact (by norm_num : ¬ IsUnit (2 : ℕ)) (hd 2 hdvd)

/-- The Kronecker quadratic unit homomorphism `(ZMod (fundDisc d))ˣ →* ℤˣ` for every squarefree
`d > 1`. -/
def kroneckerUnitHom (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    (ZMod (fundDisc d))ˣ →* ℤˣ :=
  if h1 : d % 4 = 1 then
    have hD : fundDisc d = d := if_pos h1
    have hodd : _root_.Odd (fundDisc d) := by rw [hD]; exact Nat.odd_iff.mpr (by omega)
    jacobiUnitHom (fundDisc d) hodd
  else if h3 : d % 4 = 3 then
    have hD : fundDisc d = 4 * d := if_neg h1
    have h4 : 4 ∣ fundDisc d := ⟨d, hD⟩
    have hd_dvd : d ∣ fundDisc d := ⟨4, by rw [hD, mul_comm]⟩
    have : NeZero d := ⟨by have := Fact.out (p := 1 < d); omega⟩
    have hodd : _root_.Odd d := Nat.odd_iff.mpr (by omega)
    (chi4UnitHom.comp (ZMod.unitsMap h4)) * ((jacobiUnitHom d hodd).comp (ZMod.unitsMap hd_dvd))
  else
    have h2 : d % 4 = 2 := by
      have hne0 := squarefree_mod_four_ne_zero (Fact.out (p := Squarefree d)); omega
    have hD : fundDisc d = 4 * d := if_neg h1
    have hm_odd : _root_.Odd (d / 2) := Nat.odd_iff.mpr (by omega)
    have : NeZero (d / 2) := ⟨by have := Fact.out (p := 1 < d); omega⟩
    have h4 : 4 ∣ fundDisc d := ⟨d, hD⟩
    have h8 : 8 ∣ fundDisc d := ⟨d / 2, by omega⟩
    have hm_dvd : d / 2 ∣ fundDisc d := ⟨8, by omega⟩
    if (d / 2) % 4 = 1 then
      (chi8UnitHom.comp (ZMod.unitsMap h8)) * ((jacobiUnitHom (d / 2) hm_odd).comp (ZMod.unitsMap hm_dvd))
    else
      (chi4UnitHom.comp (ZMod.unitsMap h4)) * (chi8UnitHom.comp (ZMod.unitsMap h8)) *
        ((jacobiUnitHom (d / 2) hm_odd).comp (ZMod.unitsMap hm_dvd))

/-- **Concrete Kronecker Character `χ_D : DirichletCharacter ℂ (fundDisc d)`** attached to every
real quadratic number field `ℚ(√d)` (`d > 1` squarefree). -/
def kroneckerChar (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    DirichletCharacter ℂ (fundDisc d) :=
  dirichletCharOfIntUnitHom (kroneckerUnitHom d)

theorem kroneckerChar_real (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)]
    (a : ZMod (fundDisc d)) : (kroneckerChar d a).im = 0 := by
  by_cases ha : IsUnit a
  · rw [kroneckerChar, dirichletCharOfIntUnitHom_apply_isUnit _ ha, Complex.intCast_im]
  · rw [MulChar.map_nonunit _ ha, Complex.zero_im]

/-- **Exact Evaluation of `kroneckerChar d` at Every Odd Prime `p`**:
`kroneckerChar d (p : ZMod (fundDisc d)) = (legendreSym p (d : ℤ) : ℂ)`! -/
theorem kroneckerChar_apply_prime_odd (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    kroneckerChar d (p : ZMod (fundDisc d)) = (legendreSym p (d : ℤ) : ℂ) := by
  have hp : p.Prime := Fact.out
  have hp_odd : _root_.Odd p := hp.odd_of_ne_two hp2
  have hd_gt1 : 1 < d := Fact.out
  have hsqf : Squarefree d := Fact.out
  by_cases hpd : p ∣ d
  · have hpD : p ∣ fundDisc d := by
      unfold fundDisc; split_ifs
      · exact hpd
      · exact dvd_mul_of_dvd_right hpd 4
    have hnotu : ¬ IsUnit (p : ZMod (fundDisc d)) := by
      rw [ZMod.isUnit_iff_coprime]
      intro hcop
      exact hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hpD)
    rw [MulChar.map_nonunit _ hnotu]
    have hleg0 : legendreSym p (d : ℤ) = 0 := by
      rw [legendreSym.eq_zero_iff]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (d : ℤ) p).mpr (Int.ofNat_dvd.mpr hpd)
    rw [hleg0, Int.cast_zero]
  · have hcop_d : Nat.Coprime p d := (hp.coprime_iff_not_dvd).mpr hpd
    have hcop_4 : Nat.Coprime p 4 := by
      have hcop2 : Nat.Coprime p 2 := (hp.coprime_iff_not_dvd).mpr fun h2 =>
        hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h2) hp.two_le)
      exact hcop2.pow_right 2
    have hcop_D : Nat.Coprime p (fundDisc d) := by
      unfold fundDisc; split_ifs
      · exact hcop_d
      · exact hcop_4.mul_right hcop_d
    have hpu : IsUnit (p : ZMod (fundDisc d)) := (ZMod.isUnit_iff_coprime p (fundDisc d)).mpr hcop_D
    have hval_eval : kroneckerChar d (p : ZMod (fundDisc d)) =
        (((kroneckerUnitHom d hpu.unit : ℤˣ) : ℤ) : ℂ) :=
      dirichletCharOfIntUnitHom_apply_isUnit _ hpu
    rw [hval_eval, jacobiSym.legendreSym.to_jacobiSym]
    congr 1
    have hjac_map : ∀ (m : ℕ) [NeZero m] (hm : _root_.Odd m) (hm_dvd : m ∣ fundDisc d),
        ((jacobiUnitHom m hm (ZMod.unitsMap hm_dvd hpu.unit) : ℤˣ) : ℤ) = jacobiSym (p : ℤ) m := by
      intro m _ hm hm_dvd
      rw [coe_jacobiUnitHom hm]
      have hmod : (((ZMod.unitsMap hm_dvd hpu.unit : (ZMod m)ˣ) : ZMod m).val : ℤ) ≡
          (p : ℤ) [ZMOD (m : ℕ)] := by
        rw [← ZMod.intCast_eq_intCast_iff]
        push_cast
        rw [ZMod.natCast_zmod_val]
        change ZMod.cast (p : ZMod (fundDisc d)) = (p : ZMod m)
        exact ZMod.cast_natCast hm_dvd p
      exact jacobiSym.mod_left' hmod
    unfold kroneckerUnitHom
    split_ifs with h1 h3 hm1
    · have hD : fundDisc d = d := if_pos h1
      have hmod : (((hpu.unit : ZMod (fundDisc d)).val : ℤ)) ≡ (p : ℤ) [ZMOD (fundDisc d : ℕ)] := by
        rw [← ZMod.intCast_eq_intCast_iff]
        push_cast
        rw [ZMod.natCast_zmod_val, IsUnit.unit_spec]
      rw [coe_jacobiUnitHom, jacobiSym.mod_left' hmod, hD]
      exact (jacobiSym.quadratic_reciprocity_one_mod_four h1 hp_odd).symm
    · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
      have hu4 : IsUnit (p : ZMod 4) := (ZMod.isUnit_iff_coprime p 4).mpr hcop_4
      have h4D : 4 ∣ fundDisc d := by unfold fundDisc; rw [if_neg h1]; exact ⟨d, rfl⟩
      have hmap4 : ZMod.unitsMap h4D hpu.unit = hu4.unit := by
        apply Units.ext
        change ZMod.cast (p : ZMod (fundDisc d)) = (p : ZMod 4)
        exact ZMod.cast_natCast h4D p
      rw [hmap4, coe_chi4UnitHom_nat hp_odd hu4, hjac_map]
      have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by obtain ⟨k, rfl⟩ := hp_odd; omega
      rcases hp4 with hp1 | hp3
      · rw [if_pos hp1, one_mul]
        exact (jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr (by omega)) hp1).symm
      · rw [if_neg (by omega), neg_one_mul]
        have hqr := jacobiSym.quadratic_reciprocity_three_mod_four h3 hp3
        linarith
    · have h2 : d % 4 = 2 := by have := squarefree_mod_four_ne_zero hsqf; omega
      have hcop8 : Nat.Coprime p 8 := by
        have hcop2 : Nat.Coprime p 2 := (hp.coprime_iff_not_dvd).mpr fun h2' =>
          hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h2') hp.two_le)
        exact hcop2.pow_right 3
      have hu8 : IsUnit (p : ZMod 8) := (ZMod.isUnit_iff_coprime p 8).mpr hcop8
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
      have h8D : 8 ∣ fundDisc d := by unfold fundDisc; rw [if_neg h1]; exact ⟨d / 2, by omega⟩
      have hmap8 : ZMod.unitsMap h8D hpu.unit = hu8.unit := by
        apply Units.ext
        change ZMod.cast (p : ZMod (fundDisc d)) = (p : ZMod 8)
        exact ZMod.cast_natCast h8D p
      rw [hmap8, coe_chi8UnitHom_nat hp_odd hu8, hjac_map]
      rw [← jacobiSym.quadratic_reciprocity_one_mod_four hm1 hp_odd, ← jacobiSym.mul_left]
      congr 1
      omega
    · have h2 : d % 4 = 2 := by have := squarefree_mod_four_ne_zero hsqf; omega
      have hm3 : (d / 2) % 4 = 3 := by omega
      have hcop8 : Nat.Coprime p 8 := by
        have hcop2 : Nat.Coprime p 2 := (hp.coprime_iff_not_dvd).mpr fun h2' =>
          hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h2') hp.two_le)
        exact hcop2.pow_right 3
      have hu4 : IsUnit (p : ZMod 4) := (ZMod.isUnit_iff_coprime p 4).mpr hcop_4
      have hu8 : IsUnit (p : ZMod 8) := (ZMod.isUnit_iff_coprime p 8).mpr hcop8
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
      have h4D : 4 ∣ fundDisc d := by unfold fundDisc; rw [if_neg h1]; exact ⟨d, rfl⟩
      have h8D : 8 ∣ fundDisc d := by unfold fundDisc; rw [if_neg h1]; exact ⟨d / 2, by omega⟩
      have hmap4 : ZMod.unitsMap h4D hpu.unit = hu4.unit := by
        apply Units.ext
        change ZMod.cast (p : ZMod (fundDisc d)) = (p : ZMod 4)
        exact ZMod.cast_natCast h4D p
      have hmap8 : ZMod.unitsMap h8D hpu.unit = hu8.unit := by
        apply Units.ext
        change ZMod.cast (p : ZMod (fundDisc d)) = (p : ZMod 8)
        exact ZMod.cast_natCast h8D p
      rw [hmap4, hmap8, coe_chi4UnitHom_nat hp_odd hu4, coe_chi8UnitHom_nat hp_odd hu8, hjac_map]
      have hpair : (if p % 4 = 1 then (1 : ℤ) else -1) * jacobiSym (p : ℤ) (d / 2) =
          jacobiSym ((d / 2 : ℕ) : ℤ) p := by
        have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by obtain ⟨k, rfl⟩ := hp_odd; omega
        rcases hp4 with hp1 | hp3
        · rw [if_pos hp1, one_mul]
          exact (jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr (by omega)) hp1).symm
        · rw [if_neg (by omega), neg_one_mul]
          have hqr := jacobiSym.quadratic_reciprocity_three_mod_four hm3 hp3
          linarith
      calc (if p % 4 = 1 then (1 : ℤ) else -1) * jacobiSym 2 p * jacobiSym (p : ℤ) (d / 2)
          = jacobiSym 2 p * ((if p % 4 = 1 then (1 : ℤ) else -1) * jacobiSym (p : ℤ) (d / 2)) := by ring
        _ = jacobiSym 2 p * jacobiSym ((d / 2 : ℕ) : ℤ) p := by rw [hpair]
        _ = jacobiSym (2 * ((d / 2 : ℕ) : ℤ)) p := (jacobiSym.mul_left _ _ _).symm
        _ = jacobiSym (d : ℤ) p := by congr 1; omega

/-- **Exact Evaluation of `kroneckerChar d` at `p = 2`**:
- `0` if `d % 4 ≠ 1` (`2 ∣ fundDisc d`),
- `1` if `d % 8 = 1`,
- `-1` if `d % 8 = 5`. -/
theorem kroneckerChar_apply_two (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    kroneckerChar d (2 : ZMod (fundDisc d)) =
      if d % 4 = 1 then (if d % 8 = 1 then 1 else -1) else 0 := by
  have hd_gt1 : 1 < d := Fact.out
  by_cases h1 : d % 4 = 1
  · rw [if_pos h1]
    have hD : fundDisc d = d := if_pos h1
    have hcop : Nat.Coprime 2 (fundDisc d) := by
      rw [hD]
      exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr (by omega)
    have h2u : IsUnit (2 : ZMod (fundDisc d)) := by
      change IsUnit ((2 : ℕ) : ZMod (fundDisc d))
      exact (ZMod.isUnit_iff_coprime 2 (fundDisc d)).mpr hcop
    rw [kroneckerChar, dirichletCharOfIntUnitHom_apply_isUnit _ h2u]
    unfold kroneckerUnitHom
    rw [dif_pos h1, coe_jacobiUnitHom]
    have hmod : (((h2u.unit : ZMod (fundDisc d)).val : ℤ)) ≡ (2 : ℤ) [ZMOD (fundDisc d : ℕ)] := by
      rw [← ZMod.intCast_eq_intCast_iff]
      push_cast
      rw [ZMod.natCast_zmod_val, IsUnit.unit_spec]
    rw [jacobiSym.mod_left' hmod, hD, jacobiSym.at_two (Nat.odd_iff.mpr (by omega))]
    have h8 : d % 8 = 1 ∨ d % 8 = 5 := by omega
    rcases h8 with hd8 | hd8
    · rw [if_pos hd8]
      have hc : (d : ZMod 8) = 1 := by rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]; exact hd8
      rw [hc]; simp [show ZMod.χ₈ (1 : ZMod 8) = 1 by decide]
    · rw [if_neg (by omega)]
      have hc : (d : ZMod 8) = 5 := by
        rw [← Nat.cast_ofNat (n := 5), ZMod.natCast_eq_natCast_iff]; exact hd8
      rw [hc]; simp [show ZMod.χ₈ (5 : ZMod 8) = -1 by decide]
  · rw [if_neg h1]
    have h2D : 2 ∣ fundDisc d := by unfold fundDisc; rw [if_neg h1]; exact ⟨2 * d, by ring⟩
    have hnotu : ¬ IsUnit (2 : ZMod (fundDisc d)) := by
      change ¬ IsUnit ((2 : ℕ) : ZMod (fundDisc d))
      rw [ZMod.isUnit_iff_coprime]
      intro hcop
      exact (by norm_num : ¬ (2 : ℕ) ∣ 1) (hcop.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl h2D)
    exact MulChar.map_nonunit _ hnotu

/-- Helper: every odd prime `p` has a nonzero quadratic nonresidue in `ZMod p`. -/
private lemma exists_nonsquare_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
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

/-- Every `kroneckerChar d` (`d > 1` squarefree) is non-principal (`kroneckerChar d ≠ 1`). -/
theorem kroneckerChar_ne_one (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    kroneckerChar d ≠ 1 := by
  have hd_gt1 : 1 < d := Fact.out
  have hsqf : Squarefree d := Fact.out
  intro h1
  by_cases hd2 : d = 2
  · subst hd2
    have h3u : IsUnit ((3 : ℕ) : ZMod (fundDisc 2)) :=
      (ZMod.isUnit_iff_coprime 3 8).mpr (by decide)
    have h3 := congrArg (fun χ : DirichletCharacter ℂ (fundDisc 2) => χ ((3 : ℕ) : ZMod (fundDisc 2))) h1
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [kroneckerChar_apply_prime_odd 2 (by norm_num), MulChar.one_apply h3u] at h3
    have hleg : legendreSym 3 ((2 : ℕ) : ℤ) = -1 := by
      rw [Nat.cast_ofNat, legendreSym.at_two (by norm_num)]; decide
    rw [hleg] at h3
    norm_num at h3
  · have hex_odd_p : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ d := by
      rcases Nat.even_or_odd d with ⟨k, hk⟩ | hodd
      · have h2d : 2 ∣ d := ⟨k, by omega⟩
        have hq_gt1 : 1 < d / 2 := by omega
        have hq_odd : ¬ 2 ∣ (d / 2) := fun h2q =>
          (by norm_num : ¬ IsUnit (2 : ℕ)) (hsqf 2 ⟨d / 2 / 2, by omega⟩)
        have hhalf : d / 2 ∣ d := ⟨2, by omega⟩
        refine ⟨(d / 2).minFac, Nat.minFac_prime (by omega), ?_,
          dvd_trans (Nat.minFac_dvd (d / 2)) hhalf⟩
        intro h2
        have hdvd := Nat.minFac_dvd (d / 2)
        rw [h2] at hdvd
        exact hq_odd hdvd
      · refine ⟨d.minFac, Nat.minFac_prime (by omega), ?_, Nat.minFac_dvd d⟩
        intro h2
        have h2d : 2 ∣ d := h2 ▸ Nat.minFac_dvd d
        obtain ⟨k, hk⟩ := hodd; omega
    obtain ⟨p, hp, hp2, hpd⟩ := hex_odd_p
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨r, hr⟩ := exists_nonsquare_ne_zero_zmod (p := p) hp2
    have hpD : p ∣ fundDisc d := by
      unfold fundDisc; split_ifs
      · exact hpd
      · exact dvd_mul_of_dvd_right hpd 4
    set M : ℕ := fundDisc d / p
    have hD_eq : fundDisc d = p * M := (Nat.mul_div_cancel' hpD).symm
    have hcop_pM : Nat.Coprime p M := by
      rw [hp.coprime_iff_not_dvd]
      intro hpM
      have hppD : p * p ∣ fundDisc d := by
        obtain ⟨k, hk⟩ := hpM; exact ⟨k, by rw [hD_eq, hk]; ring⟩
      have hppd : p * p ∣ d := by
        unfold fundDisc at hppD
        split_ifs at hppD
        · exact hppD
        · have hcop4 : Nat.Coprime (p * p) 4 := by
            have hcop2 : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr fun h =>
              hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h) hp.two_le)
            exact (hcop2.mul_left hcop2).pow_right 2
          exact hcop4.dvd_of_dvd_mul_left hppD
      exact hp.not_isUnit (hsqf p hppd)
    obtain ⟨n, hn_p, hn_M⟩ := Nat.chineseRemainder hcop_pM r.val 1
    let a : ZMod (fundDisc d) := (n : ZMod (fundDisc d))
    have ha_p : (n : ZMod p) = r := by
      have : (n : ZMod p) = ((r.val : ℕ) : ZMod p) := (ZMod.natCast_eq_natCast_iff n r.val p).mpr hn_p
      rwa [ZMod.natCast_zmod_val] at this
    have ha_M : (n : ZMod M) = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff n 1 M).mpr hn_M
    have ha_u : IsUnit a := by
      dsimp only [a]
      rw [ZMod.isUnit_iff_coprime, hD_eq]
      refine Nat.Coprime.mul_right ?_ ?_
      · have hru : IsUnit (n : ZMod p) := by rw [ha_p]; exact isUnit_iff_ne_zero.mpr hr.1
        exact (ZMod.isUnit_iff_coprime n p).mp hru
      · have h1u : IsUnit (n : ZMod M) := by rw [ha_M]; exact isUnit_one
        exact (ZMod.isUnit_iff_coprime n M).mp h1u
    have hcast_eq : ∀ (k : ℕ) (hk : k ∣ M), ZMod.cast (R := ZMod k) a = (1 : ZMod k) := by
      intro k hk
      have hkD : k ∣ fundDisc d := dvd_trans hk ⟨p, by rw [hD_eq, mul_comm]⟩
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
      apply hr.2
      rwa [← hmod, ← Int.cast_natCast (R := ZMod p)]
    have hjac_div : ∀ (m : ℕ) (hpm : p ∣ m) (hmM : m / p ∣ M),
        jacobiSym (a.val : ℤ) m = -1 := by
      intro m hpm hmM
      have hM_ne : M ≠ 0 := fun h0 => by
        have : fundDisc d = 0 := by rw [hD_eq, h0, mul_zero]
        exact NeZero.ne (fundDisc d) this
      have hmp_ne : m / p ≠ 0 := fun h0 => hM_ne (by rw [h0] at hmM; exact zero_dvd_iff.mp hmM)
      have : NeZero (m / p) := ⟨hmp_ne⟩
      have hm_eq : m = p * (m / p) := (Nat.mul_div_cancel' hpm).symm
      rw [hm_eq, jacobiSym.mul_right, hjac_p]
      have hmod1 : (a.val : ℤ) ≡ (1 : ℤ) [ZMOD (m / p : ℕ)] := by
        rw [← ZMod.intCast_eq_intCast_iff]
        push_cast
        have hmpD : m / p ∣ fundDisc d := dvd_trans hmM ⟨p, by rw [hD_eq, mul_comm]⟩
        rw [← ZMod.cast_natCast hmpD a.val, ZMod.natCast_zmod_val]
        exact hcast_eq (m / p) hmM
      rw [jacobiSym.mod_left' hmod1, jacobiSym.one_left, mul_one]
    have hval_eval : kroneckerChar d a = (((kroneckerUnitHom d ha_u.unit : ℤˣ) : ℤ) : ℂ) :=
      dirichletCharOfIntUnitHom_apply_isUnit _ ha_u
    have hneg1 : ((kroneckerUnitHom d ha_u.unit : ℤˣ) : ℤ) = -1 := by
      have hjac_u : ∀ (m : ℕ) [NeZero m] (hm : _root_.Odd m) (hpm : p ∣ m) (hmM : m / p ∣ M)
          (hmD : m ∣ fundDisc d),
          ((jacobiUnitHom m hm (ZMod.unitsMap hmD ha_u.unit) : ℤˣ) : ℤ) = -1 := by
        intro m _ hm hpm hmM hmD
        rw [coe_jacobiUnitHom hm]
        have hmod : (((ZMod.unitsMap hmD ha_u.unit : (ZMod m)ˣ) : ZMod m).val : ℤ) ≡
            (a.val : ℤ) [ZMOD (m : ℕ)] := by
          rw [← ZMod.intCast_eq_intCast_iff]
          push_cast
          rw [ZMod.natCast_zmod_val, ← ZMod.cast_natCast hmD a.val, ZMod.natCast_zmod_val]
          rfl
        rw [jacobiSym.mod_left' hmod, hjac_div m hpm hmM]
      unfold kroneckerUnitHom
      split_ifs with h1' h3' hm1'
      · rw [coe_jacobiUnitHom]
        exact hjac_div (fundDisc d) hpD dvd_rfl
      · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
        have h4M : 4 ∣ M := by
          have hcop4 : Nat.Coprime p 4 := (hp.coprime_iff_not_dvd.mpr fun h =>
            hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h) hp.two_le)).pow_right 2
          exact hcop4.symm.dvd_of_dvd_mul_left (by rw [← hD_eq]; unfold fundDisc; rw [if_neg h1']; exact ⟨d, rfl⟩)
        have h4D : 4 ∣ fundDisc d := by unfold fundDisc; rw [if_neg h1']; exact ⟨d, rfl⟩
        have hmap4 : ((ZMod.unitsMap h4D ha_u.unit : (ZMod 4)ˣ) : ZMod 4) = 1 := by
          change ZMod.cast a = (1 : ZMod 4); exact hcast_eq 4 h4M
        have hc4 : ((chi4UnitHom (ZMod.unitsMap h4D ha_u.unit) : ℤˣ) : ℤ) = 1 := by
          change (((if ((ZMod.unitsMap h4D ha_u.unit : (ZMod 4)ˣ) : ZMod 4) = 1 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) = 1
          rw [hmap4]; simp
        have hdM : d / p ∣ M := by
          refine ⟨4, ?_⟩
          have hD4 : p * M = 4 * d := by rw [← hD_eq]; unfold fundDisc; rw [if_neg h1']
          have hdp : p * (d / p) = d := Nat.mul_div_cancel' hpd
          have : p * M = p * (d / p * 4) := by linarith
          exact Nat.eq_of_mul_eq_mul_left hp.pos this
        rw [hc4, hjac_u d _ hpd hdM, one_mul]
      · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
        have h2' : d % 4 = 2 := by have := squarefree_mod_four_ne_zero hsqf; omega
        have h8M : 8 ∣ M := by
          have hcop8 : Nat.Coprime p 8 := (hp.coprime_iff_not_dvd.mpr fun h =>
            hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h) hp.two_le)).pow_right 3
          exact hcop8.symm.dvd_of_dvd_mul_left (by rw [← hD_eq]; unfold fundDisc; rw [if_neg h1']; exact ⟨d / 2, by omega⟩)
        have h8D : 8 ∣ fundDisc d := by unfold fundDisc; rw [if_neg h1']; exact ⟨d / 2, by omega⟩
        have hmap8 : ((ZMod.unitsMap h8D ha_u.unit : (ZMod 8)ˣ) : ZMod 8) = 1 := by
          change ZMod.cast a = (1 : ZMod 8); exact hcast_eq 8 h8M
        have hc8 : ((chi8UnitHom (ZMod.unitsMap h8D ha_u.unit) : ℤˣ) : ℤ) = 1 := by
          change (((if ((ZMod.unitsMap h8D ha_u.unit : (ZMod 8)ˣ) : ZMod 8) = 1 ∨
            ((ZMod.unitsMap h8D ha_u.unit : (ZMod 8)ˣ) : ZMod 8) = 7 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) = 1
          rw [hmap8]; simp
        have hp_half : p ∣ d / 2 := by
          have hcop2 : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr fun h =>
            hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h) hp.two_le)
          have h2half : 2 * (d / 2) = d := by omega
          exact hcop2.dvd_of_dvd_mul_left (by rw [h2half]; exact hpd)
        have hmM : (d / 2) / p ∣ M := by
          refine ⟨8, ?_⟩
          have hD8 : p * M = 8 * (d / 2) := by rw [← hD_eq]; unfold fundDisc; rw [if_neg h1']; omega
          have hmp : p * ((d / 2) / p) = d / 2 := Nat.mul_div_cancel' hp_half
          have : p * M = p * ((d / 2) / p * 8) := by linarith
          exact Nat.eq_of_mul_eq_mul_left hp.pos this
        have : NeZero (d / 2) := ⟨by omega⟩
        rw [hc8, hjac_u (d / 2) _ hp_half hmM, one_mul]
      · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
        have h2' : d % 4 = 2 := by have := squarefree_mod_four_ne_zero hsqf; omega
        have h4M : 4 ∣ M := by
          have hcop4 : Nat.Coprime p 4 := (hp.coprime_iff_not_dvd.mpr fun h =>
            hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h) hp.two_le)).pow_right 2
          exact hcop4.symm.dvd_of_dvd_mul_left (by rw [← hD_eq]; unfold fundDisc; rw [if_neg h1']; exact ⟨d, rfl⟩)
        have h8M : 8 ∣ M := by
          have hcop8 : Nat.Coprime p 8 := (hp.coprime_iff_not_dvd.mpr fun h =>
            hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h) hp.two_le)).pow_right 3
          exact hcop8.symm.dvd_of_dvd_mul_left (by rw [← hD_eq]; unfold fundDisc; rw [if_neg h1']; exact ⟨d / 2, by omega⟩)
        have h4D : 4 ∣ fundDisc d := by unfold fundDisc; rw [if_neg h1']; exact ⟨d, rfl⟩
        have h8D : 8 ∣ fundDisc d := by unfold fundDisc; rw [if_neg h1']; exact ⟨d / 2, by omega⟩
        have hmap4 : ((ZMod.unitsMap h4D ha_u.unit : (ZMod 4)ˣ) : ZMod 4) = 1 := by
          change ZMod.cast a = (1 : ZMod 4); exact hcast_eq 4 h4M
        have hmap8 : ((ZMod.unitsMap h8D ha_u.unit : (ZMod 8)ˣ) : ZMod 8) = 1 := by
          change ZMod.cast a = (1 : ZMod 8); exact hcast_eq 8 h8M
        have hc4 : ((chi4UnitHom (ZMod.unitsMap h4D ha_u.unit) : ℤˣ) : ℤ) = 1 := by
          change (((if ((ZMod.unitsMap h4D ha_u.unit : (ZMod 4)ˣ) : ZMod 4) = 1 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) = 1
          rw [hmap4]; simp
        have hc8 : ((chi8UnitHom (ZMod.unitsMap h8D ha_u.unit) : ℤˣ) : ℤ) = 1 := by
          change (((if ((ZMod.unitsMap h8D ha_u.unit : (ZMod 8)ˣ) : ZMod 8) = 1 ∨
            ((ZMod.unitsMap h8D ha_u.unit : (ZMod 8)ˣ) : ZMod 8) = 7 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) = 1
          rw [hmap8]; simp
        have hp_half : p ∣ d / 2 := by
          have hcop2 : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr fun h =>
            hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h) hp.two_le)
          have h2half : 2 * (d / 2) = d := by omega
          exact hcop2.dvd_of_dvd_mul_left (by rw [h2half]; exact hpd)
        have hmM : (d / 2) / p ∣ M := by
          refine ⟨8, ?_⟩
          have hD8 : p * M = 8 * (d / 2) := by rw [← hD_eq]; unfold fundDisc; rw [if_neg h1']; omega
          have hmp : p * ((d / 2) / p) = d / 2 := Nat.mul_div_cancel' hp_half
          have : p * M = p * ((d / 2) / p * 8) := by linarith
          exact Nat.eq_of_mul_eq_mul_left hp.pos this
        have : NeZero (d / 2) := ⟨by omega⟩
        rw [hc4, hc8, hjac_u (d / 2) _ hp_half hmM, one_mul, one_mul]
    have ha_one := congrArg (fun χ : DirichletCharacter ℂ (fundDisc d) => χ a) h1
    rw [hval_eval, hneg1, MulChar.one_apply ha_u] at ha_one
    norm_num at ha_one

/-- Concrete identifications `kroneckerChar 5 = chi5`, `kroneckerChar 2 = chi8`, `kroneckerChar 3 = chi12`! -/
theorem kroneckerChar_five_eq_chi5 : kroneckerChar 5 = chi5 := by
  ext u
  revert u; intro (u : (ZMod 5)ˣ)
  have hu : (u : ZMod 5) = 1 ∨ (u : ZMod 5) = 2 ∨ (u : ZMod 5) = 3 ∨ (u : ZMod 5) = 4 := by
    fin_cases u <;> decide
  have hj2 : jacobiSym 2 5 = -1 := by rw [jacobiSym.at_two (by decide)]; decide
  have hj3 : jacobiSym 3 5 = -1 := by
    have hqr := jacobiSym.quadratic_reciprocity_one_mod_four (by decide : 5 % 4 = 1)
      (by decide : _root_.Odd 3)
    change jacobiSym ((3 : ℕ) : ℤ) 5 = -1
    rw [← hqr, jacobiSym.mod_left' (show ((5 : ℕ) : ℤ) ≡ 2 [ZMOD (3 : ℕ)] by decide),
      jacobiSym.at_two (by decide : _root_.Odd 3)]
    decide
  have hj4 : jacobiSym 4 5 = 1 := by
    rw [show (4 : ℤ) = 2 * 2 by norm_num, jacobiSym.mul_left, hj2]; norm_num
  rw [kroneckerChar, dirichletCharOfIntUnitHom_apply_unit, chi5_apply_val, if_pos u.isUnit]
  unfold kroneckerUnitHom
  rw [dif_pos (by decide : 5 % 4 = 1), coe_jacobiUnitHom]
  rcases hu with h | h | h | h <;> rw [h]
  · change ((jacobiSym ((1 : ZMod 5).val : ℤ) 5 : ℤ) : ℂ) = _
    rw [show ((1 : ZMod 5).val : ℤ) = 1 by decide, jacobiSym.one_left]; simp
  · change ((jacobiSym ((2 : ZMod 5).val : ℤ) 5 : ℤ) : ℂ) = _
    rw [show ((2 : ZMod 5).val : ℤ) = 2 by decide, hj2]
    simp [show (2 : ZMod 5) ≠ 1 by decide, show (2 : ZMod 5) ≠ 4 by decide]
  · change ((jacobiSym ((3 : ZMod 5).val : ℤ) 5 : ℤ) : ℂ) = _
    rw [show ((3 : ZMod 5).val : ℤ) = 3 by decide, hj3]
    simp [show (3 : ZMod 5) ≠ 1 by decide, show (3 : ZMod 5) ≠ 4 by decide]
  · change ((jacobiSym ((4 : ZMod 5).val : ℤ) 5 : ℤ) : ℂ) = _
    rw [show ((4 : ZMod 5).val : ℤ) = 4 by decide, hj4]; simp

theorem kroneckerChar_two_eq_chi8 : kroneckerChar 2 = chi8 := by
  ext u
  revert u; intro (u : (ZMod 8)ˣ)
  have hu : (u : ZMod 8) = 1 ∨ (u : ZMod 8) = 3 ∨ (u : ZMod 8) = 5 ∨ (u : ZMod 8) = 7 := by
    fin_cases u <;> decide
  rw [kroneckerChar, dirichletCharOfIntUnitHom_apply_unit, chi8_apply_val, if_pos u.isUnit]
  unfold kroneckerUnitHom
  rw [dif_neg (by decide : ¬ 2 % 4 = 1), dif_neg (by decide : ¬ 2 % 4 = 3),
    if_pos (by decide : (2 / 2) % 4 = 1)]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, Int.cast_mul]
  have hj1 : ((jacobiUnitHom (2 / 2) (by decide)
      (ZMod.unitsMap (by decide : 2 / 2 ∣ fundDisc 2) u) : ℤˣ) : ℤ) = 1 := by
    rw [coe_jacobiUnitHom]; simp
  rw [hj1, Int.cast_one, mul_one]
  have hm8 : ZMod.unitsMap (by decide : 8 ∣ fundDisc 2) u = u := by
    apply Units.ext
    change ZMod.cast (u : ZMod 8) = (u : ZMod 8)
    simp
  rw [hm8]
  rcases hu with h | h | h | h
  · change ((((if (u : ZMod 8) = 1 ∨ (u : ZMod 8) = 7 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) : ℂ) = _
    rw [h]; simp
  · change ((((if (u : ZMod 8) = 1 ∨ (u : ZMod 8) = 7 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) : ℂ) = _
    rw [h]; simp [show (3 : ZMod 8) ≠ 1 by decide, show (3 : ZMod 8) ≠ 7 by decide]
  · change ((((if (u : ZMod 8) = 1 ∨ (u : ZMod 8) = 7 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) : ℂ) = _
    rw [h]; simp [show (5 : ZMod 8) ≠ 1 by decide, show (5 : ZMod 8) ≠ 7 by decide]
  · change ((((if (u : ZMod 8) = 1 ∨ (u : ZMod 8) = 7 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) : ℂ) = _
    rw [h]; simp

theorem kroneckerChar_three_eq_chi12 : kroneckerChar 3 = chi12 := by
  ext u
  revert u; intro (u : (ZMod 12)ˣ)
  have hu : (u : ZMod 12) = 1 ∨ (u : ZMod 12) = 5 ∨ (u : ZMod 12) = 7 ∨ (u : ZMod 12) = 11 := by
    fin_cases u <;> decide
  have hj23 : jacobiSym 2 3 = -1 := by rw [jacobiSym.at_two (by decide)]; decide
  rw [kroneckerChar, dirichletCharOfIntUnitHom_apply_unit, chi12_apply_val, if_pos u.isUnit]
  unfold kroneckerUnitHom
  rw [dif_neg (by decide : ¬ 3 % 4 = 1), dif_pos (by decide : 3 % 4 = 3)]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, Int.cast_mul,
    coe_jacobiUnitHom]
  change ((((if (ZMod.cast (u : ZMod 12) : ZMod 4) = 1 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) : ℂ) *
      ((jacobiSym ((ZMod.cast (u : ZMod 12) : ZMod 3).val : ℤ) 3 : ℤ) : ℂ) = _
  rcases hu with h | h | h | h <;> rw [h]
  · rw [show (ZMod.cast (1 : ZMod 12) : ZMod 4) = 1 by decide,
      show ((ZMod.cast (1 : ZMod 12) : ZMod 3).val : ℤ) = 1 by decide, jacobiSym.one_left]
    simp
  · rw [show (ZMod.cast (5 : ZMod 12) : ZMod 4) = 1 by decide,
      show ((ZMod.cast (5 : ZMod 12) : ZMod 3).val : ℤ) = 2 by decide, hj23]
    simp [show (5 : ZMod 12) ≠ 1 by decide, show (5 : ZMod 12) ≠ 11 by decide]
  · rw [if_neg (show (ZMod.cast (7 : ZMod 12) : ZMod 4) ≠ 1 by decide),
      show ((ZMod.cast (7 : ZMod 12) : ZMod 3).val : ℤ) = 1 by decide, jacobiSym.one_left]
    simp [show (7 : ZMod 12) ≠ 1 by decide, show (7 : ZMod 12) ≠ 11 by decide]
  · rw [if_neg (show (ZMod.cast (11 : ZMod 12) : ZMod 4) ≠ 1 by decide),
      show ((ZMod.cast (11 : ZMod 12) : ZMod 3).val : ℤ) = 2 by decide, hj23]
    simp

/-! ### Exact Kummer–Dedekind Prime-Ideal Splitting & Local Euler Factors in `ℚ(√d)` -/

/-- Helper: bijection between `PrimesAbove K p` and the set of distinct prime ideals in
`normalizedFactors (Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}))`. -/
private def primesAboveEquivNormalizedFactors {K : Type*} [Field K] [NumberField K]
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

/-- Helper: `emultiplicity` of a prime ideal `P` in `(p) 𝓞 K` equals `P.ramificationIdx ℤ`. -/
private lemma emultiplicity_eq_ramificationIdx {K : Type*} [Field K] [NumberField K]
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

/-- Helper: monic degree-2 polynomial over a field `k` with no roots is irreducible. -/
private lemma irreducible_of_natDegree_two_of_no_roots {k : Type*} [Field k]
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

/-- Helper: exact `PrimesAbove` norm product for a quadratic field from the 3 Kummer–Dedekind cases
for `g = map (Quotient.mk (p)) (minpoly ℤ (quadIntGen d))`. -/
private theorem quad_local_eulerFactor_of_splitting (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)]
    {p : ℕ} [Fact p.Prime] [Fintype (PrimesAbove (QuadField d) p)] (s : ℂ) :
    let I : Ideal ℤ := Ideal.span {(p : ℤ)}
    let g : Polynomial (ℤ ⧸ I) := Polynomial.map (Ideal.Quotient.mk I) (quadMinPolyInt d)
    ((∃ r₁ r₂ : ℤ ⧸ I, r₁ ≠ r₂ ∧ g = (Polynomial.X - Polynomial.C r₁) * (Polynomial.X - Polynomial.C r₂)) →
      ∏ v : PrimesAbove (QuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
        (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (1 : ℂ) * (p : ℂ) ^ (-s))⁻¹) ∧
    (Irreducible g →
      ∏ v : PrimesAbove (QuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
        (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (-1 : ℂ) * (p : ℂ) ^ (-s))⁻¹) ∧
    ((∃ r : ℤ ⧸ I, g = (Polynomial.X - Polynomial.C r) ^ 2) →
      ∏ v : PrimesAbove (QuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
        (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (0 : ℂ) * (p : ℂ) ^ (-s))⁻¹) := by
  classical
  have hp : p.Prime := Fact.out
  set I : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hI_max : I.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have : I.IsMaximal := hI_max
  let : Field (ℤ ⧸ I) := Ideal.Quotient.field I
  have hI_ne : I ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact Int.natCast_ne_zero.mpr hp.ne_zero
  have hcond : Ideal.comap (algebraMap ℤ (𝓞 (QuadField d))) (conductor ℤ (quadIntGen d)) ⊔ I = ⊤ := by
    rw [quadField_conductor_eq_top d, Ideal.comap_top, top_sup_eq]
  have hint : IsIntegral ℤ (quadIntGen d) := Algebra.IsIntegral.isIntegral (quadIntGen d)
  have hg_eq : Polynomial.map (Ideal.Quotient.mk I) (minpoly ℤ (quadIntGen d)) =
      Polynomial.map (Ideal.Quotient.mk I) (quadMinPolyInt d) := by
    rw [minpoly_quadIntGen d]
  let eKD := (primesAboveEquivNormalizedFactors (K := QuadField d) hp).trans
    (KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI_max hI_ne hcond hint)
  have hsum_ef : ∑ v : PrimesAbove (QuadField d) p,
      v.1.asIdeal.ramificationIdx ℤ * v.1.asIdeal.inertiaDeg ℤ = 2 := by
    rw [sum_ramification_inertia_primesAbove (QuadField d) hp, quadField_finrank d]
  have habsNorm_v : ∀ v : PrimesAbove (QuadField d) p,
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
        (Polynomial.map (Ideal.Quotient.mk I) (minpoly ℤ (quadIntGen d))) =
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
    have hcard : Fintype.card (PrimesAbove (QuadField d) p) = 2 := by
      let hset : ({q : Polynomial (ℤ ⧸ I) //
          q ∈ UniqueFactorizationMonoid.normalizedFactors
            (Polynomial.map (Ideal.Quotient.mk I) (minpoly ℤ (quadIntGen d)))}) ≃
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
    have hf_all : ∀ v : PrimesAbove (QuadField d) p, v.1.asIdeal.inertiaDeg ℤ = 1 := by
      intro v
      have hge1 : ∀ w : PrimesAbove (QuadField d) p,
          1 ≤ w.1.asIdeal.ramificationIdx ℤ * w.1.asIdeal.inertiaDeg ℤ := fun w => by
        have : w.1.asIdeal.IsPrime := w.1.isPrime
        exact Nat.mul_pos (Ideal.ramificationIdx_pos w.1.asIdeal ℤ)
          (Ideal.inertiaDeg_pos w.1.asIdeal ℤ)
      have hle2 : v.1.asIdeal.ramificationIdx ℤ * v.1.asIdeal.inertiaDeg ℤ +
          ∑ w ∈ Finset.univ.erase v, w.1.asIdeal.ramificationIdx ℤ * w.1.asIdeal.inertiaDeg ℤ = 2 := by
        rw [← hsum_ef]
        exact Finset.add_sum_erase Finset.univ
          (fun w : PrimesAbove (QuadField d) p => w.1.asIdeal.ramificationIdx ℤ * w.1.asIdeal.inertiaDeg ℤ)
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
    calc ∏ v : PrimesAbove (QuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹
        = ∏ _v : PrimesAbove (QuadField d) p, (1 - (p : ℂ) ^ (-s))⁻¹ :=
          Finset.prod_congr rfl fun v _ => by rw [habsNorm_v v, hf_all v, pow_one]
      _ = ((1 - (p : ℂ) ^ (-s))⁻¹) ^ Fintype.card (PrimesAbove (QuadField d) p) := by simp
      _ = (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (1 : ℂ) * (p : ℂ) ^ (-s))⁻¹ := by
          rw [hcard, sq, one_mul]
  · -- Case 2: Inert
    intro hirr_g
    set g : Polynomial (ℤ ⧸ I) := Polynomial.map (Ideal.Quotient.mk I) (quadMinPolyInt d)
    have hnf : UniqueFactorizationMonoid.normalizedFactors
        (Polynomial.map (Ideal.Quotient.mk I) (minpoly ℤ (quadIntGen d))) = {normalize g} := by
      rw [hg_eq, UniqueFactorizationMonoid.normalizedFactors_irreducible hirr_g]
    have hcard : Fintype.card (PrimesAbove (QuadField d) p) = 1 := by
      let hset : ({q : Polynomial (ℤ ⧸ I) //
          q ∈ UniqueFactorizationMonoid.normalizedFactors
            (Polynomial.map (Ideal.Quotient.mk I) (minpoly ℤ (quadIntGen d)))}) ≃
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
        (primesAboveEquivNormalizedFactors hp v0).2
      have hLHS : emultiplicity ((primesAboveEquivNormalizedFactors hp v0).1)
          (Ideal.map (algebraMap ℤ (𝓞 (QuadField d))) I) = (v0.1.asIdeal.ramificationIdx ℤ : ℕ∞) :=
        emultiplicity_eq_ramificationIdx hp v0
      rw [hLHS] at hem
      have hq_eq : ((KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
          hI_max hI_ne hcond hint)
          ⟨(primesAboveEquivNormalizedFactors hp v0).1,
            (primesAboveEquivNormalizedFactors hp v0).2⟩ : Polynomial (ℤ ⧸ I)) =
          normalize g := by
        have hm := ((KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
          hI_max hI_ne hcond hint)
          ⟨(primesAboveEquivNormalizedFactors hp v0).1,
            (primesAboveEquivNormalizedFactors hp v0).2⟩).2
        have hm' : ((KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
            hI_max hI_ne hcond hint)
            ⟨(primesAboveEquivNormalizedFactors hp v0).1,
              (primesAboveEquivNormalizedFactors hp v0).2⟩ : Polynomial (ℤ ⧸ I)) ∈
            ({normalize g} : Multiset (Polynomial (ℤ ⧸ I))) := hnf ▸ hm
        exact Multiset.mem_singleton.mp hm'
      rw [hq_eq, hg_eq] at hem
      have hem1 : emultiplicity (normalize g) g = 1 := by
        have h1 : (normalize g) ^ 1 ∣ g := by rw [pow_one]; exact normalize_dvd_iff.mpr dvd_rfl
        have h2 : ¬ (normalize g) ^ 2 ∣ g := by
          intro h2
          have hg_dvd : g * g ∣ g := by
            rw [sq] at h2; exact (Associated.mul_mul (normalize_associated g) (normalize_associated g)).dvd_iff_dvd_left.mp h2
          obtain ⟨c, hc⟩ := hg_dvd
          have hc_eq : g * c = 1 := mul_left_cancel₀ hirr_g.ne_zero (by rw [← mul_assoc, ← hc, mul_one])
          exact hirr_g.not_isUnit (isUnit_iff_exists_inv.mpr ⟨c, hc_eq⟩)
        exact emultiplicity_eq_of_dvd_of_not_dvd h1 h2
      rw [hem1] at hem
      exact Nat.cast_injective hem
    have hf2 : v0.1.asIdeal.inertiaDeg ℤ = 2 := by
      have huniv : (Finset.univ : Finset (PrimesAbove (QuadField d) p)) = {v0} := by
        ext v; simp [hv0 v]
      rw [huniv, Finset.sum_singleton, he1, one_mul] at hsum_ef
      exact hsum_ef
    have huniv : (Finset.univ : Finset (PrimesAbove (QuadField d) p)) = {v0} := by
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
        (Polynomial.map (Ideal.Quotient.mk I) (minpoly ℤ (quadIntGen d))) =
        Multiset.replicate 2 (Polynomial.X - Polynomial.C r) := by
      rw [hg_eq, hg_sq, UniqueFactorizationMonoid.normalizedFactors_pow,
        UniqueFactorizationMonoid.normalizedFactors_irreducible hirr_lin, hnorm_lin]
      rfl
    have hcard : Fintype.card (PrimesAbove (QuadField d) p) = 1 := by
      let hset : ({q : Polynomial (ℤ ⧸ I) //
          q ∈ UniqueFactorizationMonoid.normalizedFactors
            (Polynomial.map (Ideal.Quotient.mk I) (minpoly ℤ (quadIntGen d)))}) ≃
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
        (primesAboveEquivNormalizedFactors hp v0).2
      have hLHS : emultiplicity ((primesAboveEquivNormalizedFactors hp v0).1)
          (Ideal.map (algebraMap ℤ (𝓞 (QuadField d))) I) = (v0.1.asIdeal.ramificationIdx ℤ : ℕ∞) :=
        emultiplicity_eq_ramificationIdx hp v0
      rw [hLHS] at hem
      have hq_eq : ((KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
          hI_max hI_ne hcond hint)
          ⟨(primesAboveEquivNormalizedFactors hp v0).1,
            (primesAboveEquivNormalizedFactors hp v0).2⟩ : Polynomial (ℤ ⧸ I)) =
          Polynomial.X - Polynomial.C r := by
        have hm := ((KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
          hI_max hI_ne hcond hint)
          ⟨(primesAboveEquivNormalizedFactors hp v0).1,
            (primesAboveEquivNormalizedFactors hp v0).2⟩).2
        have hm' : ((KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
            hI_max hI_ne hcond hint)
            ⟨(primesAboveEquivNormalizedFactors hp v0).1,
              (primesAboveEquivNormalizedFactors hp v0).2⟩ : Polynomial (ℤ ⧸ I)) ∈
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
      have huniv : (Finset.univ : Finset (PrimesAbove (QuadField d) p)) = {v0} := by
        ext v; simp [hv0 v]
      rw [huniv, Finset.sum_singleton, he2] at hsum_ef
      omega
    have huniv : (Finset.univ : Finset (PrimesAbove (QuadField d) p)) = {v0} := by
      ext v; simp [hv0 v]
    rw [huniv, Finset.prod_singleton, habsNorm_v v0, hf1, pow_one, zero_mul, sub_zero, inv_one,
      mul_one]

/-- **Exact Local Quadratic Euler Factor Identity at EVERY Rational Prime `p`** (split, inert, and
ramified, including `p = 2`!):
`∏_{v ∣ p} (1 - N(v)^{-s})⁻¹ = (1 - p^{-s})⁻¹ * (1 - χ_D(p) p^{-s})⁻¹`. -/
theorem quad_local_eulerFactor_eq (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)]
    {p : ℕ} [Fact p.Prime] [Fintype (PrimesAbove (QuadField d) p)] (s : ℂ) :
    ∏ v : PrimesAbove (QuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
      (1 - (p : ℂ) ^ (-s))⁻¹ *
        (1 - kroneckerChar d (p : ZMod (fundDisc d)) * (p : ℂ) ^ (-s))⁻¹ := by
  have hp : p.Prime := Fact.out
  set I : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hI_max : I.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have : I.IsMaximal := hI_max
  let : Field (ℤ ⧸ I) := Ideal.Quotient.field I
  let eQ : ℤ ⧸ I ≃+* ZMod p := Int.quotientSpanNatEquivZMod p
  let ePoly : Polynomial (ℤ ⧸ I) ≃+* Polynomial (ZMod p) := Polynomial.mapEquiv eQ
  set g : Polynomial (ℤ ⧸ I) := Polynomial.map (Ideal.Quotient.mk I) (quadMinPolyInt d)
  set gZ : Polynomial (ZMod p) := Polynomial.map (Int.castRingHom (ZMod p)) (quadMinPolyInt d)
  have hePoly_g : ePoly g = gZ := by
    dsimp only [ePoly, g, gZ]
    rw [Polynomial.mapEquiv_apply, Polynomial.map_map]
    congr 1
  obtain ⟨hSplit, hInert, hRam⟩ := quad_local_eulerFactor_of_splitting d (p := p) s
  have hsplit_of : (∃ r₁ r₂ : ZMod p, r₁ ≠ r₂ ∧
      gZ = (Polynomial.X - Polynomial.C r₁) * (Polynomial.X - Polynomial.C r₂)) →
      ∏ v : PrimesAbove (QuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
        (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (1 : ℂ) * (p : ℂ) ^ (-s))⁻¹ := by
    rintro ⟨r₁, r₂, hne, hfac⟩
    refine hSplit ⟨eQ.symm r₁, eQ.symm r₂, fun h => hne (eQ.symm.injective h), ?_⟩
    apply ePoly.injective
    rw [hePoly_g, hfac]
    simp [ePoly, Polynomial.mapEquiv_apply]
  have hinert_of : Irreducible gZ →
      ∏ v : PrimesAbove (QuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
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
      ∏ v : PrimesAbove (QuadField d) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
        (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (0 : ℂ) * (p : ℂ) ^ (-s))⁻¹ := by
    rintro ⟨r, hsq⟩
    refine hRam ⟨eQ.symm r, ?_⟩
    apply ePoly.injective
    rw [hePoly_g, hsq]
    simp [ePoly, Polynomial.mapEquiv_apply]
  by_cases hp2 : p = 2
  · subst hp2
    rw [show ((2 : ℕ) : ZMod (fundDisc d)) = (2 : ZMod (fundDisc d)) from Nat.cast_ofNat,
      kroneckerChar_apply_two d]
    by_cases hd1 : d % 4 = 1
    · rw [if_pos hd1]
      have hgZ_eq : gZ = Polynomial.X ^ 2 - Polynomial.X -
          Polynomial.C ((((d : ℤ) - 1) / 4 : ℤ) : ZMod 2) := by
        dsimp only [gZ]; unfold quadMinPolyInt; rw [if_pos hd1]
        simp [Polynomial.map_sub, Polynomial.map_pow]
      have h8 : d % 8 = 1 ∨ d % 8 = 5 := by omega
      rcases h8 with hd8 | hd8
      · rw [if_pos hd8]
        have hc0 : ((((d : ℤ) - 1) / 4 : ℤ) : ZMod 2) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; omega
        refine hsplit_of ⟨0, 1, zero_ne_one, ?_⟩
        rw [hgZ_eq, hc0, map_zero, sub_zero, sub_zero, map_one]
        ring
      · rw [if_neg (by omega)]
        have hc1 : ((((d : ℤ) - 1) / 4 : ℤ) : ZMod 2) = 1 := by
          have hsub : ((((d : ℤ) - 1) / 4 - 1 : ℤ) : ZMod 2) = 0 := by
            rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; omega
          push_cast at hsub; linear_combination hsub
        refine hinert_of (irreducible_of_natDegree_two_of_no_roots ?_ ?_)
        · rw [← hePoly_g, Polynomial.mapEquiv_apply, Polynomial.natDegree_map_eq_of_injective eQ.injective]
          have hm : (quadMinPolyInt d).Monic := quadMinPolyInt_monic d
          rw [hm.natDegree_map, quadMinPolyInt_natDegree d]
        · intro r
          rw [hgZ_eq, hc1]
          simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
          have hr01 : r = 0 ∨ r = 1 := by
            have hlt := r.val_lt
            have hval : r.val = 0 ∨ r.val = 1 := by omega
            rcases hval with h | h
            · left; rw [← ZMod.natCast_zmod_val r, h]; rfl
            · right; rw [← ZMod.natCast_zmod_val r, h]; rfl
          rcases hr01 with rfl | rfl
          · rw [zero_pow (by norm_num : 2 ≠ 0), sub_zero, zero_sub, neg_ne_zero]; exact one_ne_zero
          · rw [one_pow, sub_self, zero_sub, neg_ne_zero]; exact one_ne_zero
    · rw [if_neg hd1]
      have hgZ_eq : gZ = Polynomial.X ^ 2 - Polynomial.C (d : ZMod 2) := by
        dsimp only [gZ]; unfold quadMinPolyInt; rw [if_neg hd1]
        simp [Polynomial.map_sub, Polynomial.map_pow]
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
      have hsub : -(Polynomial.C (d : ZMod 2)) = Polynomial.C (d : ZMod 2) := by
        rw [← map_neg]; congr 1
        have hadd : (d : ZMod 2) + (d : ZMod 2) = 0 := by rw [← two_mul, h2_zmod, zero_mul]
        exact neg_eq_iff_add_eq_zero.mpr hadd
      calc Polynomial.X ^ 2 - Polynomial.C (d : ZMod 2)
          = Polynomial.X ^ 2 - 2 * Polynomial.X * Polynomial.C (d : ZMod 2) +
              Polynomial.C ((d : ZMod 2) ^ 2) := by
            rw [h2, zero_mul, zero_mul, sub_zero, hd_sq, sub_eq_add_neg, hsub]
        _ = (Polynomial.X - Polynomial.C (d : ZMod 2)) ^ 2 := by rw [map_pow]; ring
  · rw [kroneckerChar_apply_prime_odd d hp2]
    have h2_ne : (2 : ZMod p) ≠ 0 := by
      intro h0
      have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp h0
      exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hp.two_le)
    set c : ZMod p := if d % 4 = 1 then (2 : ZMod p)⁻¹ else 0
    set Δ : ZMod p := if d % 4 = 1 then (d : ZMod p) * ((2 : ZMod p)⁻¹) ^ 2 else (d : ZMod p)
    have hgZ_sq : gZ = (Polynomial.X - Polynomial.C c) ^ 2 - Polynomial.C Δ := by
      dsimp only [gZ, c, Δ]
      unfold quadMinPolyInt
      split_ifs with hd1
      · rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
          Polynomial.map_C]
        have hd4 : ((d : ℤ) - 1) / 4 * 4 = (d : ℤ) - 1 := by omega
        have hq4 : Int.castRingHom (ZMod p) (((d : ℤ) - 1) / 4) =
            ((d : ZMod p) - 1) * ((2 : ZMod p)⁻¹) ^ 2 := by
          have hz : ((((d : ℤ) - 1) / 4 : ℤ) : ZMod p) * 4 = (d : ZMod p) - 1 := by
            have := congrArg (Int.cast (R := ZMod p)) hd4
            simpa using this
          have h4inv : (4 : ZMod p) * ((2 : ZMod p)⁻¹) ^ 2 = 1 := by
            rw [show (4 : ZMod p) = 2 ^ 2 by ring, ← mul_pow, mul_inv_cancel₀ h2_ne, one_pow]
          change ((((d : ℤ) - 1) / 4 : ℤ) : ZMod p) = _
          calc ((((d : ℤ) - 1) / 4 : ℤ) : ZMod p)
              = ((((d : ℤ) - 1) / 4 : ℤ) : ZMod p) * (4 * ((2 : ZMod p)⁻¹) ^ 2) := by
                rw [h4inv, mul_one]
            _ = ((((d : ℤ) - 1) / 4 : ℤ) : ZMod p) * 4 * ((2 : ZMod p)⁻¹) ^ 2 := by ring
            _ = ((d : ZMod p) - 1) * ((2 : ZMod p)⁻¹) ^ 2 := by rw [hz]
        have h2c : (2 : Polynomial (ZMod p)) * Polynomial.C (2 : ZMod p)⁻¹ = 1 := by
          rw [(map_ofNat Polynomial.C 2).symm, ← map_mul, mul_inv_cancel₀ h2_ne, map_one]
        rw [hq4]
        calc Polynomial.X ^ 2 - Polynomial.X - Polynomial.C (((d : ZMod p) - 1) * (2 : ZMod p)⁻¹ ^ 2)
            = Polynomial.X ^ 2 - (2 * Polynomial.C (2 : ZMod p)⁻¹) * Polynomial.X -
                Polynomial.C (((d : ZMod p) - 1) * (2 : ZMod p)⁻¹ ^ 2) := by rw [h2c, one_mul]
          _ = (Polynomial.X - Polynomial.C (2 : ZMod p)⁻¹) ^ 2 -
                Polynomial.C ((d : ZMod p) * (2 : ZMod p)⁻¹ ^ 2) := by
              rw [show Polynomial.C (((d : ZMod p) - 1) * (2 : ZMod p)⁻¹ ^ 2) =
                Polynomial.C ((d : ZMod p) * (2 : ZMod p)⁻¹ ^ 2) -
                  (Polynomial.C (2 : ZMod p)⁻¹) ^ 2 by rw [← map_pow, ← map_sub]; congr 1; ring]
              ring
      · simp [Polynomial.map_sub, Polynomial.map_pow]
    have hΔ_zero : Δ = 0 ↔ (d : ZMod p) = 0 := by
      dsimp only [Δ]; split_ifs
      · simp [h2_ne]
      · rfl
    have hΔ_sq : IsSquare Δ ↔ IsSquare (d : ZMod p) := by
      dsimp only [Δ]; split_ifs
      · constructor
        · rintro ⟨t, ht⟩
          refine ⟨2 * t, ?_⟩
          have : (d : ZMod p) * ((2 : ZMod p)⁻¹) ^ 2 * 4 = (2 * t) * (2 * t) := by
            rw [ht]; ring
          have h4inv : ((2 : ZMod p)⁻¹) ^ 2 * 4 = 1 := by
            rw [show (4 : ZMod p) = 2 ^ 2 by ring, mul_comm, ← mul_pow, mul_inv_cancel₀ h2_ne, one_pow]
          rw [mul_assoc, h4inv, mul_one] at this
          exact this
        · rintro ⟨t, ht⟩
          refine ⟨t * (2 : ZMod p)⁻¹, ?_⟩
          rw [ht]; ring
      · rfl
    by_cases hd0 : (d : ZMod p) = 0
    · have hleg0 : legendreSym p (d : ℤ) = 0 := (legendreSym.eq_zero_iff p (d : ℤ)).mpr (by simpa using hd0)
      rw [hleg0, Int.cast_zero]
      refine hram_of ⟨c, ?_⟩
      rw [hgZ_sq, hΔ_zero.mpr hd0, map_zero, sub_zero]
    · by_cases hsq_d : IsSquare (d : ZMod p)
      · have hleg1 : legendreSym p (d : ℤ) = 1 :=
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
      · have hlegm1 : legendreSym p (d : ℤ) = -1 :=
          (legendreSym.eq_neg_one_iff p).mpr (by simpa using hsq_d)
        rw [hlegm1, Int.cast_neg, Int.cast_one]
        have hnsq_Δ : ¬ IsSquare Δ := fun h => hsq_d (hΔ_sq.mp h)
        refine hinert_of (irreducible_of_natDegree_two_of_no_roots ?_ ?_)
        · rw [← hePoly_g, Polynomial.mapEquiv_apply, Polynomial.natDegree_map_eq_of_injective eQ.injective]
          have hm : (quadMinPolyInt d).Monic := quadMinPolyInt_monic d
          rw [hm.natDegree_map, quadMinPolyInt_natDegree d]
        · intro r hr
          rw [hgZ_sq] at hr
          simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hr
          exact hnsq_Δ ⟨r - c, by rw [← sq]; linear_combination -hr⟩

/-- **UNCONDITIONAL EXACT QUADRATIC DEDEKIND ZETA FACTORIZATION (`ζ_{ℚ(√d)}(s) = ζ(s) · L(s, χ_D)`)**:
for EVERY squarefree `d > 1` and EVERY `s : ℂ` with `1 < s.re`:
`Stage7DedekindZeta.dedekindZeta (QuadField d) s = riemannZeta s * DirichletCharacter.LFunction (kroneckerChar d) s`! -/
theorem dedekindZeta_quadratic_eq_zeta_mul_L (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)]
    {s : ℂ} (hs : 1 < s.re) :
    Stage7DedekindZeta.dedekindZeta (QuadField d) s =
      riemannZeta s * DirichletCharacter.LFunction (kroneckerChar d) s := by
  have hzeta := riemannZeta_eulerProduct_hasProd hs
  have hL : HasProd (fun p : Nat.Primes =>
      (1 - kroneckerChar d ((p : ℕ) : ZMod (fundDisc d)) * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      (DirichletCharacter.LFunction (kroneckerChar d) s) := by
    rw [DirichletCharacter.LFunction_eq_LSeries (kroneckerChar d) hs]
    exact DirichletCharacter.LSeries_eulerProduct_hasProd (kroneckerChar d) hs
  have hmul : HasProd (fun p : Nat.Primes =>
      (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ *
        (1 - kroneckerChar d ((p : ℕ) : ZMod (fundDisc d)) * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      (riemannZeta s * DirichletCharacter.LFunction (kroneckerChar d) s) :=
    hzeta.mul hL
  have hmult_v : Multipliable (fun v : HeightOneSpectrum (𝓞 (QuadField d)) =>
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) :=
    (dedekindZeta_hasProd_eulerProduct (QuadField d) hs).multipliable
  have hmult_sig : Multipliable (fun x : Σ p : Nat.Primes, PrimesAbove (QuadField d) p =>
      (1 - (Ideal.absNorm x.2.1.asIdeal : ℂ) ^ (-s))⁻¹) :=
    (Equiv.multipliable_iff (heightOneEquivSigmaPrimesAbove (QuadField d))).mp hmult_v
  have hfib : ∀ p : Nat.Primes,
      HasProd (fun v : PrimesAbove (QuadField d) p =>
          (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹)
        ((1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ *
          (1 - kroneckerChar d ((p : ℕ) : ZMod (fundDisc d)) * ((p : ℕ) : ℂ) ^ (-s))⁻¹) := by
    intro p
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    have : Finite (PrimesAbove (QuadField d) p) := finite_primesAbove (QuadField d) p.2
    classical
    let : Fintype (PrimesAbove (QuadField d) p) := Fintype.ofFinite _
    rw [← quad_local_eulerFactor_eq d (p := p) s]
    exact hasProd_fintype _
  have hsig : HasProd (fun x : Σ p : Nat.Primes, PrimesAbove (QuadField d) p =>
      (1 - (Ideal.absNorm x.2.1.asIdeal : ℂ) ^ (-s))⁻¹)
      (riemannZeta s * DirichletCharacter.LFunction (kroneckerChar d) s) :=
    HasProd.sigma_of_hasProd hmul hfib hmult_sig
  have hprod_eq : HasProd (fun v : HeightOneSpectrum (𝓞 (QuadField d)) =>
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)
      (riemannZeta s * DirichletCharacter.LFunction (kroneckerChar d) s) :=
    (Equiv.hasProd_iff (heightOneEquivSigmaPrimesAbove (QuadField d))).mpr hsig
  exact (dedekindZeta_hasProd_eulerProduct (QuadField d) hs).unique hprod_eq

/-- **UNCONDITIONAL EXACT RESIDUE OF `ζ_{ℚ(√d)}(s)` AT `s = 1`** (right half-plane limit):
`lim_{s → 1, Re(s) > 1} (s - 1) * ζ_{ℚ(√d)}(s) = L(1, χ_D)`! -/
theorem dedekindZeta_quadratic_residue_one (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    Tendsto (fun s : ℂ => (s - 1) * Stage7DedekindZeta.dedekindZeta (QuadField d) s)
      (𝓝[{z : ℂ | 1 < z.re}] (1 : ℂ))
      (nhds (DirichletCharacter.LFunction (kroneckerChar d) 1)) := by
  have hsub : {z : ℂ | 1 < z.re} ⊆ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    intro z hz h1
    rw [Set.mem_singleton_iff] at h1
    rw [Set.mem_ofPred_eq, h1, Complex.one_re] at hz
    exact lt_irrefl 1 hz
  have hEq : (fun s : ℂ => (s - 1) * Stage7DedekindZeta.dedekindZeta (QuadField d) s) =ᶠ[𝓝[{z : ℂ | 1 < z.re}] 1]
      (fun s : ℂ => ((s - 1) * riemannZeta s) * DirichletCharacter.LFunction (kroneckerChar d) s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [dedekindZeta_quadratic_eq_zeta_mul_L d hs, mul_assoc]
  rw [tendsto_congr' hEq]
  have hres : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s)
      (𝓝[{z : ℂ | 1 < z.re}] (1 : ℂ)) (nhds 1) :=
    riemannZeta_residue_one.mono_left (nhdsWithin_mono 1 hsub)
  have hL : Tendsto (fun s : ℂ => DirichletCharacter.LFunction (kroneckerChar d) s)
      (𝓝[{z : ℂ | 1 < z.re}] (1 : ℂ))
      (nhds (DirichletCharacter.LFunction (kroneckerChar d) 1)) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      ((DirichletCharacter.differentiable_LFunction (kroneckerChar_ne_one d)).continuous.tendsto 1)
  simpa only [one_mul] using hres.mul hL

/-- Real right-hand limit form `lim_{σ → 1⁺} (σ - 1) * ζ_{ℚ(√d)}(σ) = L(1, χ_D)`. -/
theorem dedekindZeta_quadratic_residue_one_real (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)] :
    Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * Stage7DedekindZeta.dedekindZeta (QuadField d) (σ : ℂ))
      (𝓝[>] (1 : ℝ))
      (nhds (DirichletCharacter.LFunction (kroneckerChar d) 1)) := by
  have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[{z : ℂ | 1 < z.re}] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · exact tendsto_nhdsWithin_of_tendsto_nhds
        (by simpa using Complex.continuous_ofReal.continuousAt.tendsto (x := (1 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      simpa using hσ
  exact (dedekindZeta_quadratic_residue_one d).comp hmap

end QuadraticDedekindZeta

/-! ## Section 5: Concrete Real Quadratic Class Number Formula Identities & Master Theorem -/

section ConcreteClassNumberFormula

/-- **Exact Real Quadratic Class Number Formula for `ℚ(√5)` (`D = 5`, `h = 1`, `ε = (1 + √5)/2`)**:
`2 * h(ℚ(√5)) * log ((1 + √5) / 2) = √5 * L(1, χ₅)`. -/
theorem dirichlet_class_number_formula_quad5 :
    2 * (NumberField.classNumber (QuadField 5) : ℝ) *
        Real.log (goldenOrderToReal (goldenUnit : QuadraticAlgebra ℤ 1 1)) =
      Real.sqrt |(NumberField.discr (QuadField 5) : ℝ)| *
        (DirichletCharacter.LFunction (kroneckerChar 5) 1).re := by
  rw [classNumber_quadField_5, goldenOrderToReal_goldenUnit, quadField_discr 5,
    kroneckerChar_five_eq_chi5, LFunction_one_chi5_eq]
  have hD : fundDisc 5 = 5 := by decide
  rw [hD, Nat.cast_one, mul_one]
  have hsq5 : 0 < Real.sqrt (5 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have habs : |((5 : ℕ) : ℝ)| = (5 : ℝ) := by norm_num
  rw [Int.cast_natCast, habs]
  field_simp [hsq5.ne']

/-- **Exact Real Quadratic Class Number Formula for `ℚ(√2)` (`D = 8`, `h = 1`, `ε = 1 + √2`)**:
`2 * h(ℚ(√2)) * R(ℤ[√2]) = √8 * L(1, χ₈)`. -/
theorem dirichlet_class_number_formula_quad2 :
    2 * (NumberField.classNumber (QuadField 2) : ℝ) *
        pellRegulator 2 (by norm_num) not_isSquare_two =
      Real.sqrt |(NumberField.discr (QuadField 2) : ℝ)| *
        (DirichletCharacter.LFunction (kroneckerChar 2) 1).re := by
  rw [classNumber_quadField_2, pellRegulator_two, quadField_discr 2,
    kroneckerChar_two_eq_chi8, LFunction_one_chi8_eq]
  have hD : fundDisc 2 = 8 := by decide
  rw [hD, Nat.cast_one, mul_one]
  have hsqrt8 : Real.sqrt |((8 : ℕ) : ℝ)| = 2 * Real.sqrt 2 := by
    rw [show |((8 : ℕ) : ℝ)| = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [Int.cast_natCast, hsqrt8]
  have hsq2 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  field_simp [hsq2.ne']

/-- **Exact Real Quadratic Class Number Formula for `ℚ(√3)` (`D = 12`, `h = 1`, `ε = 2 + √3`)**:
`2 * h(ℚ(√3)) * R(ℤ[√3]) = √12 * L(1, χ₁₂)`. -/
theorem dirichlet_class_number_formula_quad3 :
    2 * (NumberField.classNumber (QuadField 3) : ℝ) *
        pellRegulator 3 (by norm_num) not_isSquare_three =
      Real.sqrt |(NumberField.discr (QuadField 3) : ℝ)| *
        (DirichletCharacter.LFunction (kroneckerChar 3) 1).re := by
  rw [classNumber_quadField_3, pellRegulator_three, quadField_discr 3,
    kroneckerChar_three_eq_chi12, LFunction_one_chi12_eq]
  have hD : fundDisc 3 = 12 := by decide
  rw [hD, Nat.cast_one, mul_one]
  have hsqrt12 : Real.sqrt |((12 : ℕ) : ℝ)| = 2 * Real.sqrt 3 := by
    rw [show |((12 : ℕ) : ℝ)| = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [Int.cast_natCast, hsqrt12]
  have hsq3 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  field_simp [hsq3.ne']

/-- **Master Unconditional Stage 9 Real Quadratic Fields Theorem (`0` Assumptions)**:
simultaneously packaging all four unconditional pillars:
1. Exact closed-form `L(1, χ)` via cyclotomic log-sine sums and explicit evaluations at
   `q = 5` (`(2/√5) log ((1+√5)/2)`), `q = 8` (`(1/√2) log (1+√2)`), `q = 12` (`(1/√3) log (2+√3)`).
2. Exact unit group structure `(Zsqrtd d)ˣ ≃* ℤ/2ℤ × ℤ` and strict positivity of the Pell regulator
   `0 < pellRegulator d` for every positive non-square `d`.
3. Exact quadratic Dedekind zeta factorization `ζ_{ℚ(√d)}(s) = ζ(s) · L(s, χ_D)` on `1 < s.re` and
   exact residue `lim_{s → 1⁺} (s - 1) ζ_{ℚ(√d)}(s) = L(1, χ_D)` for every squarefree `d > 1`.
4. Concrete class-number-one verifications `h(ℚ(√5)) = h(ℚ(√2)) = h(ℚ(√3)) = 1` and exact
   Dirichlet real quadratic class number formula `2 h(D) log ε_D = √D L(1, χ_D)` for
   `ℚ(√5), ℚ(√2), ℚ(√3)`. -/
theorem stage9_quadraticFields_unconditional :
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ.Even → (∀ a : ZMod q, (χ a).im = 0) →
      (DirichletCharacter.LFunction χ 1).re =
        -(1 / Real.sqrt (q : ℝ)) *
          ∑ a ∈ Finset.Ico 1 q,
            (χ (a : ZMod q)).re * Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))) ∧
    ((DirichletCharacter.LFunction chi5 1).re =
        (2 / Real.sqrt 5) * Real.log ((1 + Real.sqrt 5) / 2) ∧
      (DirichletCharacter.LFunction chi8 1).re =
        (1 / Real.sqrt 2) * Real.log (1 + Real.sqrt 2) ∧
      (DirichletCharacter.LFunction chi12 1).re =
        (1 / Real.sqrt 3) * Real.log (2 + Real.sqrt 3)) ∧
    (∀ (d : ℕ) (hd0 : 0 < d) (hd : ¬ IsSquare d),
      Nonempty ((Zsqrtd (d : ℤ))ˣ ≃* Multiplicative (ZMod 2) × Multiplicative ℤ) ∧
      0 < pellRegulator d hd0 hd) ∧
    (∀ (d : ℕ) [Fact (Squarefree d)] [Fact (1 < d)],
      (∀ s : ℂ, 1 < s.re →
        Stage7DedekindZeta.dedekindZeta (QuadField d) s =
          riemannZeta s * DirichletCharacter.LFunction (kroneckerChar d) s) ∧
      Tendsto (fun s : ℂ => (s - 1) * Stage7DedekindZeta.dedekindZeta (QuadField d) s)
        (𝓝[{z : ℂ | 1 < z.re}] (1 : ℂ))
        (nhds (DirichletCharacter.LFunction (kroneckerChar d) 1))) ∧
    (NumberField.classNumber (QuadField 5) = 1 ∧
      NumberField.classNumber (QuadField 2) = 1 ∧
      NumberField.classNumber (QuadField 3) = 1) :=
  ⟨fun _ _ _ hprim hχ heven hreal => LFunction_one_even_real_eq_log_sin hprim hχ heven hreal,
   ⟨LFunction_one_chi5_eq, LFunction_one_chi8_eq, LFunction_one_chi12_eq⟩,
   fun d hd0 hd => ⟨⟨zsqrtd_units_equiv_int d hd0 hd⟩, pellRegulator_pos d hd0 hd⟩,
   fun d _ _ => ⟨fun _ hs => dedekindZeta_quadratic_eq_zeta_mul_L d hs,
     dedekindZeta_quadratic_residue_one d⟩,
   ⟨classNumber_quadField_5, classNumber_quadField_2, classNumber_quadField_3⟩⟩

end ConcreteClassNumberFormula

end RHDirect.Stage9QuadraticFields

end
