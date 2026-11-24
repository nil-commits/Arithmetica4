import RHDirect.Stage8HasseMinkowski
import RHDirect.Stage5DirichletDensity
import RHDirect.Stage7GlobalDuality
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Data.Nat.ChineseRemainder

/-!
# RHDirect.HasseMinkowskiGeneral

Unconditional (`0` assumptions, `0` `sorry`, `0` custom `axiom`, `0` `native_decide`,
`0` `import Mathlib`) formalization of the **Full General `n`-Variable Hasse–Minkowski
Local–Global Principle over `ℚ`** for ALL dimensions `n : ℕ` and ALL nondegenerate
quadratic forms `Q : QuadraticForm ℚ (Fin n → ℚ)` (as well as arbitrary finite-dimensional
`ℚ`-vector spaces `V`).

## Proof Architecture (Serre, *A Course in Arithmetic*, Ch. IV §3.2)
1. **Diagonal Reduction & Low Dimensions (`n = 0, 1, 2, 3`)**:
   - `n = 0, 1`: Anisotropic over every field (`ℚ`, `ℝ`, `ℚ_[p]`).
   - `n = 2`: Reduces to `a ∈ (ℚˣ)² ↔ a > 0 ∧ ∀ p, 2 ∣ v_p(a)` via
     `Stage7GlobalDuality.isSquare_ratUnits_of_pos_of_even_val`.
   - `n = 3`: Unconditional `Stage8HasseMinkowski.hasse_minkowski_ternary_local_global_Q`.
2. **Constructive Weak Approximation for `ℚ` in `ℝ × ∏_{p ∈ S} ℚ_[p]`** and open square classes.
3. **Dimension `n = 4` (`a x² + b y² - c z² - d w² = 0`)**:
   - Pick local target values `t_v ∈ ℚ_vˣ` represented by both binary subforms at bad places `v ∈ S`.
   - Use Chinese Remainder Theorem (`Nat.chineseRemainderOfFinset`) + Dirichlet's theorem on primes
     in arithmetic progressions (`Stage5DirichletDensity.infinite_primes_modEq_of_density`) to find
     `t = ± (∏_{p ∈ S_fin} p^{e_p}) * q` with `q ∉ S_fin` prime, matching the square class of `t_v`
     at every `v ∈ S`.
   - All odd primes `p ∉ S_fin ∪ {q}` are unramified (`hilbertSymOdd = 1`), and **Hilbert
     Reciprocity** (`Stage7GlobalDuality.hilbertSymAt_eq_one_of_others_eq_one`) forces triviality
     at `q` as well; applying `n = 3` (`Stage8HasseMinkowski.hasse_minkowski_ternary_Q`) twice
     yields a global solution.
4. **Dimension `n ≥ 5` (Induction via `n - 1`)**:
   - Split `Q = Q₁(x₁, x₂) ⊥ Q₂(x₃, ..., x_n)`. Since `n - 2 ≥ 3`, `Q₂` is automatically
     isotropic at all good odd primes `p ∉ S_fin`.
   - Use weak approximation at `S` to choose `(x₁, x₂) ∈ ℚ²` with `a := Q₁(x₁, x₂) ≠ 0` such that
     `a u² + Q₂ = 0` is locally isotropic everywhere, and invoke the `(n - 1)`-dimensional IH.
5. **General Nondegenerate `QuadraticForm ℚ V` & `QuadraticForm ℚ (Fin n → ℚ)`**:
   - Diagonalize via `QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'` and
     extend scalars cleanly via `QuadraticForm.baseChange`.

Zero `sorry`, zero custom `axiom`s, `leanchecker`-verified.
-/

open scoped BigOperators TensorProduct
open Finset RHDirect.Stage5DirichletDensity RHDirect.Stage7GlobalDuality
  RHDirect.Stage8HasseMinkowski

namespace RHDirect.HasseMinkowskiGeneral

noncomputable section

/-! ## Section 1: Diagonal Forms, Square-Class Helpers, and Low Dimensions (`n = 0, 1, 2, 3`) -/

section DiagonalForms

/-- Nontrivial zero of a diagonal quadratic form `∑ i, a i * (v i)^2 = 0` over a field `K`. -/
def HasDiagZeroK {K : Type*} [Field K] {n : ℕ} (a : Fin n → K) : Prop :=
  ∃ v : Fin n → K, v ≠ 0 ∧ (∑ i : Fin n, a i * (v i) ^ 2) = 0

/-- Nontrivial rational zero of a diagonal form with unit coefficients `a : Fin n → ℚˣ`. -/
def HasDiagZeroQ {n : ℕ} (a : Fin n → ℚˣ) : Prop :=
  HasDiagZeroK (fun i => (a i : ℚ))

/-- Nontrivial real zero of a diagonal form with coefficients `a : Fin n → ℚˣ`. -/
def HasDiagZeroReal {n : ℕ} (a : Fin n → ℚˣ) : Prop :=
  HasDiagZeroK (fun i => ((a i : ℚ) : ℝ))

/-- Nontrivial `p`-adic zero of a diagonal form with coefficients `a : Fin n → ℚˣ`. -/
def HasDiagZeroPadic (p : ℕ) [Fact p.Prime] {n : ℕ} (a : Fin n → ℚˣ) : Prop :=
  HasDiagZeroK (fun i => ((a i : ℚ) : ℚ_[p]))

/-- Unified local isotropy predicate for diagonal forms at any place `v : QPlace`. -/
def HasDiagZeroAt (v : QPlace) {n : ℕ} (a : Fin n → ℚˣ) : Prop :=
  match v with
  | QPlace.inf => HasDiagZeroReal a
  | QPlace.two => @HasDiagZeroPadic 2 ⟨Nat.prime_two⟩ n a
  | QPlace.odd p => @HasDiagZeroPadic p.1 ⟨p.2.1⟩ n a

/-- Any isotropic binary form `a x² + b y² = 0` (`a, b ≠ 0`, `2 ≠ 0`) represents every element `t : K`. -/
theorem binary_represents_all_of_isotropic {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hiso : ∃ x y : K, (x ≠ 0 ∨ y ≠ 0) ∧ a * x ^ 2 + b * y ^ 2 = 0) (t : K) :
    ∃ x y : K, a * x ^ 2 + b * y ^ 2 = t := by
  obtain ⟨x₀, y₀, hne, heq⟩ := hiso
  have hx0 : x₀ ≠ 0 := by
    intro hx
    subst hx
    simp only [zero_pow two_ne_zero, mul_zero, zero_add, mul_eq_zero] at heq
    rcases heq with h | h
    · exact hb h
    · have hy : y₀ = 0 := eq_zero_of_pow_eq_zero h
      rcases hne with h1 | h1
      · exact h1 rfl
      · exact h1 hy
  let δ : K := t / (4 * a * x₀)
  refine ⟨x₀ + δ, y₀ * (1 - δ / x₀), ?_⟩
  have hby : b * y₀ ^ 2 = -a * x₀ ^ 2 := by linear_combination heq
  have h4 : (4 : K) ≠ 0 := by
    intro h4z
    apply h2
    have : (2 : K) ^ 2 = 0 := by linear_combination h4z
    exact eq_zero_of_pow_eq_zero this
  have h4a : (4 * a * x₀) ≠ 0 := mul_ne_zero (mul_ne_zero h4 ha) hx0
  calc a * (x₀ + δ) ^ 2 + b * (y₀ * (1 - δ / x₀)) ^ 2
      = a * (x₀ + δ) ^ 2 + (b * y₀ ^ 2) * (1 - δ / x₀) ^ 2 := by ring
    _ = a * (x₀ + δ) ^ 2 + (-a * x₀ ^ 2) * (1 - δ / x₀) ^ 2 := by rw [hby]
    _ = 4 * a * x₀ * δ := by field_simp [hx0, h4]; ring
    _ = t := by dsimp [δ]; field_simp [h4a]

/-- Over any field of char `≠ 2`, `a x² + b y² = t` is solvable iff `a x² + b y² - t z² = 0` is
nontrivially solvable (for `a, b, t ≠ 0`). -/
theorem binary_repr_iff_ternary_zero {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {a b t : K} (ha : a ≠ 0) (hb : b ≠ 0) (_ht : t ≠ 0) :
    (∃ x y : K, a * x ^ 2 + b * y ^ 2 = t) ↔ HasTernaryZeroK a b (-t) := by
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨x, y, 1, Or.inr (Or.inr one_ne_zero), ?_⟩
    linear_combination hxy
  · rintro ⟨x, y, z, hne, heq⟩
    by_cases hz : z = 0
    · subst hz
      simp only [zero_pow two_ne_zero, mul_zero, add_zero] at heq
      have hne2 : x ≠ 0 ∨ y ≠ 0 := by
        rcases hne with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd rfl h
      exact binary_represents_all_of_isotropic h2 ha hb ⟨x, y, hne2, heq⟩ t
    · refine ⟨x / z, y / z, ?_⟩
      field_simp [hz]
      linear_combination heq

/-- Dimension `0`: vacuously anisotropic. -/
theorem hasse_minkowski_diag_0 (a : Fin 0 → ℚˣ) :
    HasDiagZeroQ a ↔ HasDiagZeroReal a ∧ ∀ p : ℕ, [Fact p.Prime] → HasDiagZeroPadic p a := by
  constructor
  · rintro ⟨v, hv, _⟩
    exact absurd (Subsingleton.elim v 0) hv
  · rintro ⟨⟨v, hv, _⟩, _⟩
    exact absurd (Subsingleton.elim v 0) hv

/-- Dimension `1`: `a₀ x₀² = 0` (`a₀ ≠ 0`) has only the trivial solution over any field. -/
theorem not_hasDiagZeroK_one {K : Type*} [Field K] {a : Fin 1 → K} (ha : a 0 ≠ 0) :
    ¬ HasDiagZeroK a := by
  rintro ⟨v, hv, hsum⟩
  simp only [Fin.sum_univ_one] at hsum
  rcases mul_eq_zero.mp hsum with h | h
  · exact ha h
  · have hv0 : v 0 = 0 := eq_zero_of_pow_eq_zero h
    apply hv
    ext i
    fin_cases i
    exact hv0

theorem hasse_minkowski_diag_1 (a : Fin 1 → ℚˣ) :
    HasDiagZeroQ a ↔ HasDiagZeroReal a ∧ ∀ p : ℕ, [Fact p.Prime] → HasDiagZeroPadic p a := by
  have hQ : ¬ HasDiagZeroQ a := not_hasDiagZeroK_one (a 0).ne_zero
  have hR : ¬ HasDiagZeroReal a := not_hasDiagZeroK_one (Rat.cast_ne_zero.mpr (a 0).ne_zero)
  constructor
  · intro h; exact absurd h hQ
  · rintro ⟨h, _⟩; exact absurd h hR

/-- Dimension `2` over any field `K`: `a₀ x₀² + a₁ x₁² = 0` ↔ `IsSquare (-a₀ * a₁⁻¹)`. -/
theorem hasDiagZeroK_two_iff_isSquare {K : Type*} [Field K] {a : Fin 2 → K}
    (_ha0 : a 0 ≠ 0) (ha1 : a 1 ≠ 0) :
    HasDiagZeroK a ↔ IsSquare (-a 0 * (a 1)⁻¹) := by
  constructor
  · rintro ⟨v, hv, hsum⟩
    simp only [Fin.sum_univ_two, Fin.isValue] at hsum
    have hv0 : v 0 ≠ 0 := by
      intro h0
      rw [h0, zero_pow two_ne_zero, mul_zero, zero_add] at hsum
      rcases mul_eq_zero.mp hsum with h | h
      · exact ha1 h
      · have hv1 : v 1 = 0 := eq_zero_of_pow_eq_zero h
        apply hv
        ext i
        fin_cases i <;> assumption
    refine ⟨v 1 / v 0, ?_⟩
    field_simp [ha1, hv0]
    linear_combination -hsum
  · rintro ⟨r, hr⟩
    refine ⟨![1, r], ?_, ?_⟩
    · intro h0
      have := congrFun h0 0
      simp at this
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, one_pow, mul_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      rw [← sq] at hr
      rw [← hr]
      field_simp [ha1]
      ring

/-- Dimension `2` Hasse–Minkowski via `Stage7GlobalDuality.isSquare_ratUnits_of_pos_of_even_val`. -/
theorem hasse_minkowski_diag_2 (a : Fin 2 → ℚˣ) :
    HasDiagZeroQ a ↔ HasDiagZeroReal a ∧ ∀ p : ℕ, [Fact p.Prime] → HasDiagZeroPadic p a := by
  let q : ℚˣ := -a 0 * (a 1)⁻¹
  have hQ : HasDiagZeroQ a ↔ IsSquare (q : ℚ) := by
    simpa [q, HasDiagZeroQ] using
      hasDiagZeroK_two_iff_isSquare (a := fun i => (a i : ℚ)) (a 0).ne_zero (a 1).ne_zero
  have hR : HasDiagZeroReal a ↔ IsSquare ((q : ℚ) : ℝ) := by
    simpa [q, HasDiagZeroReal] using
      hasDiagZeroK_two_iff_isSquare (K := ℝ)
        (Rat.cast_ne_zero.mpr (a 0).ne_zero) (Rat.cast_ne_zero.mpr (a 1).ne_zero)
  have hP : ∀ (p : ℕ) [Fact p.Prime], HasDiagZeroPadic p a ↔ IsSquare ((q : ℚ) : ℚ_[p]) := by
    intro p _
    simpa [q, HasDiagZeroPadic] using
      hasDiagZeroK_two_iff_isSquare (K := ℚ_[p])
        (Rat.cast_ne_zero.mpr (a 0).ne_zero) (Rat.cast_ne_zero.mpr (a 1).ne_zero)
  rw [hQ, hR]
  simp_rw [hP]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨⟨(r : ℝ), by exact_mod_cast hr⟩, fun p _ => ⟨(r : ℚ_[p]), by exact_mod_cast hr⟩⟩
  · rintro ⟨⟨rR, hrR⟩, hpad⟩
    have hnonneg : (0 : ℝ) ≤ ((q : ℚ) : ℝ) := by
      rw [hrR, ← sq]
      exact sq_nonneg rR
    have hposQ : 0 < (q : ℚ) := by
      have hle : (0 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hnonneg
      exact lt_of_le_of_ne hle q.ne_zero.symm
    have heven : ∀ p : ℕ, p.Prime → (2 : ℤ) ∣ padicValRat p (q : ℚ) := by
      intro p hp
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨z, hz⟩ := hpad p
      have hz0 : z ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hz
        exact (Rat.cast_ne_zero.mpr q.ne_zero) hz
      have hval : Padic.valuation ((q : ℚ) : ℚ_[p]) = 2 * Padic.valuation z := by
        rw [hz, Padic.valuation_mul hz0 hz0]
        ring
      rw [Padic.valuation_ratCast] at hval
      exact ⟨Padic.valuation z, hval⟩
    obtain ⟨y, hy⟩ := isSquare_ratUnits_of_pos_of_even_val hposQ heven
    exact ⟨(y : ℚ), by rw [← hy, sq, Units.val_mul]⟩

/-- Equivalence between `HasDiagZeroK` for `Fin 3` and `HasTernaryZeroK`. -/
theorem hasDiagZeroK_three_iff {K : Type*} [Field K] (a : Fin 3 → K) :
    HasDiagZeroK a ↔ HasTernaryZeroK (a 0) (a 1) (a 2) := by
  constructor
  · rintro ⟨v, hv, hsum⟩
    refine ⟨v 0, v 1, v 2, ?_, ?_⟩
    · by_contra h0
      push Not at h0
      apply hv
      ext i
      fin_cases i <;> tauto
    · simpa [Fin.sum_univ_three] using hsum
  · rintro ⟨x, y, z, hne, heq⟩
    refine ⟨![x, y, z], ?_, ?_⟩
    · intro h0
      rcases hne with h | h | h
      · exact h (by simpa using congrFun h0 0)
      · exact h (by simpa using congrFun h0 1)
      · exact h (by simpa using congrFun h0 2)
    · simpa [Fin.sum_univ_three] using heq

/-- Dimension `3` Hasse–Minkowski directly from `Stage8HasseMinkowski.hasse_minkowski_ternary_local_global_Q`. -/
theorem hasse_minkowski_diag_3 (a : Fin 3 → ℚˣ) :
    HasDiagZeroQ a ↔ HasDiagZeroReal a ∧ ∀ p : ℕ, [Fact p.Prime] → HasDiagZeroPadic p a := by
  have hQ : HasDiagZeroQ a ↔ HasTernaryZeroQ (a 0) (a 1) (a 2) :=
    hasDiagZeroK_three_iff (fun i => (a i : ℚ))
  have hR : HasDiagZeroReal a ↔ HasTernaryZeroReal (a 0) (a 1) (a 2) :=
    hasDiagZeroK_three_iff (fun i => ((a i : ℚ) : ℝ))
  have hP : ∀ (p : ℕ) [Fact p.Prime],
      HasDiagZeroPadic p a ↔ HasTernaryZeroPadic p (a 0) (a 1) (a 2) := fun p _ =>
    hasDiagZeroK_three_iff (fun i => ((a i : ℚ) : ℚ_[p]))
  rw [hQ, hR]
  simp_rw [hP]
  exact hasse_minkowski_ternary_local_global_Q (a 0) (a 1) (a 2)

end DiagonalForms

/-! ## Section 2: Unramified Odd Primes, Square-Class Openness, and Weak Approximation -/

section LocalAndWeakApprox

/-- At an odd prime `p` where `a, b` are `p`-adic units (`v_p(a) = v_p(b) = 0`),
the Hilbert symbol `(a, b)_p` equals `1`. -/
theorem hilbertSymOdd_eq_one_of_val_zero (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {a b : ℚˣ}
    (ha : padicValRat p (a : ℚ) = 0) (hb : padicValRat p (b : ℚ) = 0) :
    hilbertSymOdd p hp hp2 a b = 1 := by
  rw [← unitsToZMod2_eq_zero_iff, unitsToZMod2_hilbertSymOdd]
  have h1 : (oddCoords p hp a).1 = 0 := by simp [oddCoords, ha]
  have h2 : (oddCoords p hp b).1 = 0 := by simp [oddCoords, hb]
  rw [h1, h2]
  ring

/-- Any three `p`-adic units at an odd prime `p` yield a nontrivial `ℚ_[p]`-zero of `a x² + b y² + c z² = 0`. -/
theorem hasTernaryZeroPadic_of_val_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {a b c : ℚˣ}
    (ha : padicValRat p (a : ℚ) = 0) (hb : padicValRat p (b : ℚ) = 0)
    (hc : padicValRat p (c : ℚ) = 0) :
    HasTernaryZeroPadic p a b c := by
  have hp : p.Prime := Fact.out
  rw [← hilbertSymOdd_ternary_iff p hp2 a b c]
  have hac : padicValRat p ((-a * c : ℚˣ) : ℚ) = 0 := by
    rw [Units.val_mul, Units.val_neg, padicValRat.mul (neg_ne_zero.mpr a.ne_zero) c.ne_zero,
      padicValRat.neg, ha, hc, add_zero]
  have hbc : padicValRat p ((-b * c : ℚˣ) : ℚ) = 0 := by
    rw [Units.val_mul, Units.val_neg, padicValRat.mul (neg_ne_zero.mpr b.ne_zero) c.ne_zero,
      padicValRat.neg, hb, hc, add_zero]
  exact hilbertSymOdd_eq_one_of_val_zero p hp hp2 hac hbc

/-- Finite set of primes dividing numerator or denominator of `q : ℚˣ`, union `{2}`. -/
def ratBadPrimes (q : ℚˣ) : Finset ℕ :=
  insert 2 ((q : ℚ).num.natAbs.primeFactors ∪ (q : ℚ).den.primeFactors)

theorem prime_mem_ratBadPrimes {q : ℚˣ} {p : ℕ} (hp : p ∈ ratBadPrimes q) : p.Prime := by
  simp only [ratBadPrimes, Finset.mem_insert, Finset.mem_union, Nat.mem_primeFactors] at hp
  rcases hp with rfl | ⟨hp, _⟩ | ⟨hp, _⟩
  · exact Nat.prime_two
  · exact hp
  · exact hp

theorem two_mem_ratBadPrimes (q : ℚˣ) : 2 ∈ ratBadPrimes q :=
  Finset.mem_insert_self 2 _

theorem padicValRat_eq_zero_of_not_mem_ratBadPrimes {q : ℚˣ} {p : ℕ} (hp : p.Prime)
    (hnot : p ∉ ratBadPrimes q) : padicValRat p (q : ℚ) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  simp only [ratBadPrimes, Finset.mem_insert, Finset.mem_union, Nat.mem_primeFactors,
    not_or, not_and] at hnot
  have hnum_ne : (q : ℚ).num.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr q.ne_zero)
  have hden_ne : (q : ℚ).den ≠ 0 := (q : ℚ).den_nz
  have hndvd_num : ¬ p ∣ (q : ℚ).num.natAbs := fun hd => hnot.2.1 hp hd hnum_ne
  have hndvd_den : ¬ p ∣ (q : ℚ).den := fun hd => hnot.2.2 hp hd hden_ne
  rw [padicValRat_def]
  change (padicValNat p (q : ℚ).num.natAbs : ℤ) - (padicValNat p (q : ℚ).den : ℤ) = 0
  rw [padicValNat.eq_zero_of_not_dvd hndvd_num, padicValNat.eq_zero_of_not_dvd hndvd_den]
  norm_num

/-- Real square-class openness: if `|z - y| < |y|` in `ℝ` (`y ≠ 0`), then `z / y > 0` and `z = c² * y`. -/
theorem real_same_sq_class_of_dist_lt {y z : ℝ} (hy : y ≠ 0) (hdist : |z - y| < |y|) :
    ∃ c : ℝˣ, z = (c : ℝ) ^ 2 * y := by
  have hzy_pos : 0 < z / y := by
    rw [abs_sub_comm] at hdist
    rcases lt_or_gt_of_ne hy with hyn | hyp
    · rw [abs_of_neg hyn] at hdist
      have hz_neg : z < 0 := by
        have := (abs_lt.mp hdist).1
        linarith
      exact div_pos_of_neg_of_neg hz_neg hyn
    · rw [abs_of_pos hyp] at hdist
      have hz_pos : 0 < z := by
        have := (abs_lt.mp hdist).2
        linarith
      exact div_pos hz_pos hyp
  refine ⟨Units.mk0 (Real.sqrt (z / y)) (Real.sqrt_ne_zero'.mpr hzy_pos), ?_⟩
  simp only [Units.val_mk0, Real.sq_sqrt hzy_pos.le]
  field_simp [hy]

/-- Helper: a `p`-adic integer unit `u : ℤ_[p]` with `‖u - 1‖ < 1` has `‖u‖ = 1`. -/
private lemma padic_norm_eq_one_of_sub_one_lt {p : ℕ} [Fact p.Prime] {w : ℚ_[p]}
    (hw : ‖w - 1‖ < 1) : ‖w‖ = 1 := by
  have hw_le : ‖w‖ ≤ 1 := by
    calc ‖w‖ = ‖(w - 1) + 1‖ := by ring_nf
      _ ≤ max ‖w - 1‖ ‖(1 : ℚ_[p])‖ := Padic.nonarchimedean _ _
      _ = 1 := by rw [norm_one]; exact max_eq_right hw.le
  refine le_antisymm hw_le (le_of_not_gt fun hlt => ?_)
  have h1 : (1 : ℝ) = ‖(1 : ℚ_[p])‖ := norm_one.symm
  have hlt1 : ‖(1 : ℚ_[p])‖ < 1 := by
    calc ‖(1 : ℚ_[p])‖ = ‖(1 - w) + w‖ := by ring_nf
      _ ≤ max ‖1 - w‖ ‖w‖ := Padic.nonarchimedean _ _
      _ < 1 := max_lt (by rwa [norm_sub_rev]) hlt
  linarith [h1]

/-- Helper: if `n : ℕ` is not divisible by `p`, then `(n : ℤ_[p])` is a unit (`‖(n : ℚ_[p])‖ = 1`). -/
private lemma padicInt_isUnit_natCast_of_not_dvd {p n : ℕ} [Fact p.Prime] (hnd : ¬ p ∣ n) :
    IsUnit (n : ℤ_[p]) := by
  apply PadicInt.isUnit_iff.mpr
  refine le_antisymm (PadicInt.norm_le_one _) (le_of_not_gt fun hlt => hnd ?_)
  have hdvd : ((p : ℕ) : ℤ_[p]) ∣ (n : ℤ_[p]) := (PadicInt.norm_lt_one_iff_dvd (n : ℤ_[p])).mp hlt
  obtain ⟨y, hy⟩ := hdvd
  have hmod : (n : ZMod p) = 0 := by
    have := congrArg (PadicInt.toZMod (p := p)) hy
    simpa using this
  exact (ZMod.natCast_eq_zero_iff n p).mp hmod

/-- `p`-adic square-class openness: if `‖z - y‖ ≤ ‖y‖ * (p : ℝ) ^ (-3 : ℤ)` in `ℚ_[p]` (`y ≠ 0`),
then `z = c² * y` for some `c : ℚ_[p]ˣ`. -/
theorem padic_same_sq_class_of_norm_le {p : ℕ} [Fact p.Prime] {y z : ℚ_[p]} (hy : y ≠ 0)
    (hdist : ‖z - y‖ ≤ ‖y‖ * (p : ℝ) ^ (-3 : ℤ)) :
    ∃ c : ℚ_[p]ˣ, z = (c : ℚ_[p]) ^ 2 * y := by
  have hp : p.Prime := Fact.out
  let w : ℚ_[p] := z / y
  have hw_sub : ‖w - 1‖ ≤ (p : ℝ) ^ (-3 : ℤ) := by
    have heq : w - 1 = (z - y) / y := by dsimp [w]; field_simp [hy]
    rw [heq, norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hy)).mpr (by simpa [mul_comm] using hdist)
  have hw_sub_lt : ‖w - 1‖ < 1 := by
    have hlt : (p : ℝ) ^ (-3 : ℤ) < 1 := by
      have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
      exact zpow_lt_one_of_neg₀ hp1 (by norm_num)
    exact lt_of_le_of_lt hw_sub hlt
  have hw_norm : ‖w‖ = 1 := padic_norm_eq_one_of_sub_one_lt hw_sub_lt
  let wZ : ℤ_[p] := ⟨w, hw_norm.le⟩
  have hwZ_unit : IsUnit wZ := PadicInt.isUnit_iff.mpr hw_norm
  let uZ : ℤ_[p]ˣ := hwZ_unit.unit
  have huZ_val : ((uZ : ℤ_[p]) : ℚ_[p]) = w := rfl
  have hsubZ_norm : ‖wZ - 1‖ ≤ (p : ℝ) ^ (-3 : ℤ) := hw_sub
  by_cases hp2 : p = 2
  · subst hp2
    have hmem : wZ - 1 ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ 3} :=
      (PadicInt.norm_le_pow_iff_mem_span_pow (wZ - 1) 3).mp hsubZ_norm
    rw [← PadicInt.ker_toZModPow 3] at hmem
    have hto : PadicInt.toZModPow 3 (uZ : ℤ_[2]) = 1 := by
      change PadicInt.toZModPow 3 (wZ - 1) = 0 at hmem
      rw [map_sub, map_one, sub_eq_zero] at hmem
      exact hmem
    obtain ⟨cZ, hcZ⟩ := exists_sq_padicInt_two uZ hto
    have hcw : (cZ : ℚ_[2]) ^ 2 = w := by
      simpa [huZ_val] using congrArg ((↑) : ℤ_[2] → ℚ_[2]) hcZ
    have hcZ0 : (cZ : ℚ_[2]) ≠ 0 := by
      intro h0
      have hw0 : w = 0 := by rw [← hcw, h0, zero_pow two_ne_zero]
      rw [hw0, norm_zero] at hw_norm
      norm_num at hw_norm
    refine ⟨Units.mk0 (cZ : ℚ_[2]) hcZ0, ?_⟩
    simp only [Units.val_mk0, hcw, w]
    field_simp [hy]
  · have hmem : wZ - 1 ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod]
      change ¬ IsUnit (wZ - 1)
      rw [PadicInt.not_isUnit_iff]
      exact lt_of_le_of_lt hsubZ_norm (zpow_lt_one_of_neg₀ (by exact_mod_cast hp.one_lt) (by norm_num))
    have hto : PadicInt.toZMod (uZ : ℤ_[p]) = 1 := by
      change PadicInt.toZMod (wZ - 1) = 0 at hmem
      rw [map_sub, map_one, sub_eq_zero] at hmem
      exact hmem
    obtain ⟨cZ, hcZ⟩ := exists_sq_padicInt_odd hp2 uZ (by rw [hto]; exact ⟨1, by simp⟩)
    have hcw : (cZ : ℚ_[p]) ^ 2 = w := by
      simpa [huZ_val] using congrArg ((↑) : ℤ_[p] → ℚ_[p]) hcZ
    have hcZ0 : (cZ : ℚ_[p]) ≠ 0 := by
      intro h0
      have hw0 : w = 0 := by rw [← hcw, h0, zero_pow two_ne_zero]
      rw [hw0, norm_zero] at hw_norm
      norm_num at hw_norm
    refine ⟨Units.mk0 (cZ : ℚ_[p]) hcZ0, ?_⟩
    simp only [Units.val_mk0, hcw, w]
    field_simp [hy]

/-- A single `p`-adic element `x : ℚ_[p]` can be approximated within `p^(-K : ℤ)` by `z / p^m`
for `z : ℕ` and `m : ℕ`. -/
theorem padic_approx_dyadic_rat (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (K : ℕ) :
    ∃ (z m : ℕ), ‖((z : ℚ) / (p : ℚ) ^ m : ℚ_[p]) - x‖ ≤ (p : ℝ) ^ (-(K : ℤ)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  let m : ℕ := if x = 0 then 0 else (-Padic.valuation x).toNat
  let N : ℕ := K + m
  have hy_norm : ‖(p : ℚ_[p]) ^ m * x‖ ≤ 1 := by
    by_cases hx : x = 0
    · simp [hx]
    · have hm : m = (-Padic.valuation x).toNat := by dsimp [m]; rw [if_neg hx]
      rw [norm_mul, Padic.norm_p_pow m, Padic.norm_eq_zpow_neg_valuation hx,
        ← zpow_add₀ hp_pos.ne']
      have hexp : (-(m : ℤ)) + (-Padic.valuation x) ≤ 0 := by
        rw [hm]
        omega
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
      calc (p : ℝ) ^ (-(m : ℤ) + -Padic.valuation x)
          ≤ (p : ℝ) ^ (0 : ℤ) := zpow_le_zpow_right₀ hp1 hexp
        _ = 1 := zpow_zero _
  let y : ℤ_[p] := ⟨(p : ℚ_[p]) ^ m * x, hy_norm⟩
  let z : ℕ := (PadicInt.toZModPow N y).val
  have hz_mem : (z : ℤ_[p]) - y ∈ Ideal.span {((p : ℕ) : ℤ_[p]) ^ N} := by
    rw [← PadicInt.ker_toZModPow N]
    change PadicInt.toZModPow N ((z : ℤ_[p]) - y) = 0
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  have hz_norm : ‖(z : ℤ_[p]) - y‖ ≤ (p : ℝ) ^ (-(N : ℤ)) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow ((z : ℤ_[p]) - y) N).mpr hz_mem
  refine ⟨z, m, ?_⟩
  have hdiff : ((z : ℚ) / (p : ℚ) ^ m : ℚ_[p]) - x =
      (((z : ℤ_[p]) - y : ℤ_[p]) : ℚ_[p]) / (p : ℚ_[p]) ^ m := by
    have hpm : (p : ℚ_[p]) ^ m ≠ 0 := pow_ne_zero m hp_ne
    have hy_coe : (y : ℚ_[p]) = (p : ℚ_[p]) ^ m * x := rfl
    have hz_coe : ((z : ℤ_[p]) : ℚ_[p]) = (z : ℚ_[p]) := rfl
    rw [PadicInt.coe_sub, hz_coe, hy_coe]
    push_cast
    field_simp [hpm]
  rw [hdiff, norm_div, Padic.norm_p_pow m, div_eq_mul_inv, ← zpow_neg, neg_neg]
  have hz_norm' : ‖(((z : ℤ_[p]) - y : ℤ_[p]) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(N : ℤ)) := hz_norm
  calc ‖(((z : ℤ_[p]) - y : ℤ_[p]) : ℚ_[p])‖ * (p : ℝ) ^ (m : ℤ)
      ≤ (p : ℝ) ^ (-(N : ℤ)) * (p : ℝ) ^ (m : ℤ) :=
        mul_le_mul_of_nonneg_right hz_norm' (zpow_nonneg hp_pos.le _)
    _ = (p : ℝ) ^ (-(K : ℤ)) := by
        rw [← zpow_add₀ hp_pos.ne']
        congr 1
        dsimp [N]
        omega

/-- **Constructive Weak Approximation for `ℚ` inside `ℝ × ∏_{p ∈ S} ℚ_[p]`**. -/
theorem weak_approx_Q (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (x_inf : ℝ) (ε : ℝ) (hε : 0 < ε)
    (x_p : ∀ (p : ℕ) [Fact p.Prime], ℚ_[p]) (K_p : ℕ → ℕ) :
    ∃ r : ℚ, |((r : ℚ) : ℝ) - x_inf| < ε ∧
      ∀ (p : ℕ) [Fact p.Prime], p ∈ S →
        ‖(r : ℚ_[p]) - x_p p‖ ≤ (p : ℝ) ^ (-(K_p p : ℤ)) := by
  classical
  have hex : ∀ p : ℕ, ∃ z m : ℕ, ∀ hp : p ∈ S,
      letI : Fact p.Prime := ⟨hS p hp⟩
      ‖((z : ℚ) / (p : ℚ) ^ m : ℚ_[p]) - x_p p‖ ≤ (p : ℝ) ^ (-(K_p p : ℤ)) := by
    intro p
    by_cases hp : p ∈ S
    · have : Fact p.Prime := ⟨hS p hp⟩
      obtain ⟨z, m, hzm⟩ := padic_approx_dyadic_rat p (x_p p) (K_p p)
      exact ⟨z, m, fun _ => hzm⟩
    · exact ⟨0, 0, fun h => absurd h hp⟩
  let zf : ℕ → ℕ := fun p => (hex p).choose
  let mf : ℕ → ℕ := fun p => (hex p).choose_spec.choose
  have hzm : ∀ (p : ℕ) (hp : p ∈ S),
      letI : Fact p.Prime := ⟨hS p hp⟩
      ‖((zf p : ℚ) / (p : ℚ) ^ mf p : ℚ_[p]) - x_p p‖ ≤ (p : ℝ) ^ (-(K_p p : ℤ)) :=
    fun p hp => (hex p).choose_spec.choose_spec hp
  let Ef : ℕ → ℕ := fun p => K_p p + mf p
  let D : ℕ := ∏ p ∈ S, p ^ mf p
  let P : ℕ := ∏ p ∈ S, p ^ Ef p
  have hD_pos : 0 < D := Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _
  have hP_pos : 0 < P := Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _
  obtain ⟨q, hq_ge, hq_prime⟩ := Nat.exists_infinite_primes (S.sup id + 1)
  have hq_not : q ∉ S := fun hmem => by
    have hle : q ≤ S.sup id := Finset.le_sup (f := id) hmem
    omega
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq_prime.one_lt
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt ((P : ℝ) / ((D : ℝ) * ε)) hq1
  have hstep : (P : ℝ) / ((D : ℝ) * (q : ℝ) ^ t) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    calc (P : ℝ) = ((P : ℝ) / ((D : ℝ) * ε)) * ((D : ℝ) * ε) := by
          have : (D : ℝ) * ε ≠ 0 := by positivity
          field_simp [this]
      _ < (q : ℝ) ^ t * ((D : ℝ) * ε) := by
          exact mul_lt_mul_of_pos_right ht (by positivity)
      _ = ε * ((D : ℝ) * (q : ℝ) ^ t) := by ring
  let Drest : ℕ → ℕ := fun p => ∏ p' ∈ S.erase p, p' ^ mf p'
  let cf : ℕ → ℕ := fun p => q ^ t * zf p * Drest p
  let sf : ℕ → ℕ := fun p => p ^ Ef p
  have hs_ne : ∀ p ∈ S, sf p ≠ 0 := fun p hp => pow_ne_zero _ (hS p hp).ne_zero
  have hs_cop : (S : Set ℕ).Pairwise (Function.onFun Nat.Coprime sf) := by
    intro p₁ hp₁ p₂ hp₂ hne
    exact Nat.Coprime.pow _ _ ((hS p₁ hp₁).coprime_iff_not_dvd.mpr
      ((Nat.prime_dvd_prime_iff_eq (hS p₁ hp₁) (hS p₂ hp₂)).not.mpr hne))
  obtain ⟨w, hw⟩ := Nat.chineseRemainderOfFinset cf sf S hs_ne hs_cop
  let k : ℤ := ⌊(x_inf * ((D : ℝ) * (q : ℝ) ^ t) - (w : ℝ)) / (P : ℝ)⌋
  let r : ℚ := ((w : ℤ) + k * (P : ℤ)) / ((D : ℤ) * (q : ℤ) ^ t)
  refine ⟨r, ?_, ?_⟩
  · have hfloor_le : (k : ℝ) ≤ (x_inf * ((D : ℝ) * (q : ℝ) ^ t) - (w : ℝ)) / (P : ℝ) :=
      Int.floor_le _
    have hlt_floor : (x_inf * ((D : ℝ) * (q : ℝ) ^ t) - (w : ℝ)) / (P : ℝ) < (k : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hP_r : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP_pos
    have hDq_r : (0 : ℝ) < (D : ℝ) * (q : ℝ) ^ t := by positivity
    have hlow : (k : ℝ) * (P : ℝ) ≤ x_inf * ((D : ℝ) * (q : ℝ) ^ t) - (w : ℝ) :=
      (le_div_iff₀ hP_r).mp hfloor_le
    have hhigh : x_inf * ((D : ℝ) * (q : ℝ) ^ t) - (w : ℝ) < ((k : ℝ) + 1) * (P : ℝ) :=
      (div_lt_iff₀ hP_r).mp hlt_floor
    have hr_cast : ((r : ℚ) : ℝ) = ((w : ℝ) + (k : ℝ) * (P : ℝ)) / ((D : ℝ) * (q : ℝ) ^ t) := by
      simp [r]
    rw [hr_cast, abs_sub_lt_iff]
    constructor
    · have hnum : ((w : ℝ) + (k : ℝ) * (P : ℝ)) - x_inf * ((D : ℝ) * (q : ℝ) ^ t) < (P : ℝ) := by
        linarith
      calc ((w : ℝ) + (k : ℝ) * (P : ℝ)) / ((D : ℝ) * (q : ℝ) ^ t) - x_inf
          = (((w : ℝ) + (k : ℝ) * (P : ℝ)) - x_inf * ((D : ℝ) * (q : ℝ) ^ t)) /
              ((D : ℝ) * (q : ℝ) ^ t) := by field_simp [hDq_r.ne']
        _ < (P : ℝ) / ((D : ℝ) * (q : ℝ) ^ t) := div_lt_div_of_pos_right hnum hDq_r
        _ < ε := hstep
    · have hnum : x_inf * ((D : ℝ) * (q : ℝ) ^ t) - ((w : ℝ) + (k : ℝ) * (P : ℝ)) < (P : ℝ) := by
        linarith
      calc x_inf - ((w : ℝ) + (k : ℝ) * (P : ℝ)) / ((D : ℝ) * (q : ℝ) ^ t)
          = (x_inf * ((D : ℝ) * (q : ℝ) ^ t) - ((w : ℝ) + (k : ℝ) * (P : ℝ))) /
              ((D : ℝ) * (q : ℝ) ^ t) := by field_simp [hDq_r.ne']
        _ < (P : ℝ) / ((D : ℝ) * (q : ℝ) ^ t) := div_lt_div_of_pos_right hnum hDq_r
        _ < ε := hstep
  · intro p _ hp
    have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (hS p hp).pos
    have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (hS p hp).ne_zero
    have hD_eq : D = p ^ mf p * Drest p := (Finset.mul_prod_erase S (fun x => x ^ mf x) hp).symm
    have hDrest_ndvd : ¬ p ∣ Drest p := by
      intro hd
      rw [Prime.dvd_finsetProd_iff (hS p hp).prime] at hd
      obtain ⟨p', hp', hd'⟩ := hd
      rw [Finset.mem_erase] at hp'
      have hdvd_p : p ∣ p' := (hS p hp).dvd_of_dvd_pow hd'
      exact hp'.1 ((Nat.prime_dvd_prime_iff_eq (hS p hp) (hS p' hp'.2)).mp hdvd_p).symm
    have hqt_ndvd : ¬ p ∣ q ^ t := by
      intro hd
      have hdvd_q : p ∣ q := (hS p hp).dvd_of_dvd_pow hd
      exact hq_not ((Nat.prime_dvd_prime_iff_eq (hS p hp) hq_prime).mp hdvd_q ▸ hp)
    have hDq_ndvd : ¬ p ∣ Drest p * q ^ t :=
      fun hd => ((hS p hp).dvd_mul.mp hd).elim hDrest_ndvd hqt_ndvd
    have hDq_norm : ‖((Drest p * q ^ t : ℕ) : ℚ_[p])‖ = 1 :=
      PadicInt.isUnit_iff.mp (padicInt_isUnit_natCast_of_not_dvd hDq_ndvd)
    have hcong : (p ^ Ef p : ℤ) ∣ ((w : ℤ) - (cf p : ℤ)) := by
      have hmod := Nat.modEq_iff_dvd.mp (hw p hp).symm
      exact_mod_cast hmod
    have hPdvd : (p ^ Ef p : ℤ) ∣ (P : ℤ) := by
      have hnat : p ^ Ef p ∣ P := Finset.dvd_prod_of_mem _ hp
      exact_mod_cast hnat
    have hnum_dvd : (p ^ Ef p : ℤ) ∣ ((w : ℤ) - (cf p : ℤ) + k * (P : ℤ)) :=
      dvd_add hcong (dvd_mul_of_dvd_right hPdvd k)
    let numZ : ℤ := (w : ℤ) - (cf p : ℤ) + k * (P : ℤ)
    have hnum_mem : (numZ : ℤ_[p]) ∈ Ideal.span {((p : ℕ) : ℤ_[p]) ^ Ef p} := by
      obtain ⟨m', hm'⟩ := hnum_dvd
      rw [Ideal.mem_span_singleton]
      refine ⟨(m' : ℤ_[p]), ?_⟩
      rw [show numZ = (w : ℤ) - (cf p : ℤ) + k * (P : ℤ) from rfl, hm']
      push_cast
      ring
    have hnum_norm : ‖(numZ : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(Ef p : ℤ)) := by
      change ‖(numZ : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(Ef p : ℤ))
      exact (PadicInt.norm_le_pow_iff_mem_span_pow (numZ : ℤ_[p]) (Ef p)).mpr hnum_mem
    have hdiff_eq : (r : ℚ_[p]) - ((zf p : ℚ) / (p : ℚ) ^ mf p : ℚ_[p]) =
        (numZ : ℚ_[p]) / ((p : ℚ_[p]) ^ mf p * ((Drest p * q ^ t : ℕ) : ℚ_[p])) := by
      have hp_m_ne : (p : ℚ_[p]) ^ mf p ≠ 0 := pow_ne_zero _ hp_ne
      have hDrest_ne : (Drest p : ℚ_[p]) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Finset.prod_pos (fun p' hp' =>
          pow_pos (hS p' (Finset.mem_of_mem_erase hp')).pos _)).ne'
      have hq_ne : (q : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hq_prime.ne_zero
      have hD_cast : (D : ℚ_[p]) = (p : ℚ_[p]) ^ mf p * (Drest p : ℚ_[p]) := by
        exact_mod_cast hD_eq
      dsimp [r, numZ, cf]
      push_cast
      rw [hD_cast]
      field_simp [hp_m_ne, hDrest_ne, hq_ne]
      ring
    have hdiff_norm : ‖(r : ℚ_[p]) - ((zf p : ℚ) / (p : ℚ) ^ mf p : ℚ_[p])‖ ≤
        (p : ℝ) ^ (-(K_p p : ℤ)) := by
      rw [hdiff_eq, norm_div, norm_mul, hDq_norm, mul_one, Padic.norm_p_pow (mf p),
        div_eq_mul_inv, ← zpow_neg, neg_neg]
      calc ‖(numZ : ℚ_[p])‖ * (p : ℝ) ^ (mf p : ℤ)
          ≤ (p : ℝ) ^ (-(Ef p : ℤ)) * (p : ℝ) ^ (mf p : ℤ) :=
            mul_le_mul_of_nonneg_right hnum_norm (zpow_nonneg hp_pos.le _)
        _ = (p : ℝ) ^ (-(K_p p : ℤ)) := by
            rw [← zpow_add₀ hp_pos.ne']
            congr 1
            dsimp [Ef]
            omega
    calc ‖(r : ℚ_[p]) - x_p p‖
        = ‖((r : ℚ_[p]) - ((zf p : ℚ) / (p : ℚ) ^ mf p : ℚ_[p])) +
            (((zf p : ℚ) / (p : ℚ) ^ mf p : ℚ_[p]) - x_p p)‖ := by ring_nf
      _ ≤ max ‖(r : ℚ_[p]) - ((zf p : ℚ) / (p : ℚ) ^ mf p : ℚ_[p])‖
            ‖((zf p : ℚ) / (p : ℚ) ^ mf p : ℚ_[p]) - x_p p‖ := Padic.nonarchimedean _ _
      _ ≤ (p : ℝ) ^ (-(K_p p : ℤ)) := max_le hdiff_norm (hzm p hp)

end LocalAndWeakApprox

/-! ## Section 3: Dimension `n = 4` via CRT + Dirichlet AP + Hilbert Reciprocity -/

section DimFour

/-- Over any field `K` with `2 ≠ 0`, if `a₀ x² + a₁ y² - c₀ z² - c₁ w² = 0` is nontrivially
solvable (`a₀, a₁, c₀, c₁ ≠ 0`), then there exists `t ∈ Kˣ` represented by BOTH `a₀ x² + a₁ y²`
and `c₀ z² + c₁ w²`. -/
theorem exists_common_binary_repr {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {a₀ a₁ c₀ c₁ : K} (ha₀ : a₀ ≠ 0) (ha₁ : a₁ ≠ 0) (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    (hsol : ∃ x y z w : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0) ∧
      a₀ * x ^ 2 + a₁ * y ^ 2 + (-c₀) * z ^ 2 + (-c₁) * w ^ 2 = 0) :
    ∃ t : Kˣ, (∃ x y : K, a₀ * x ^ 2 + a₁ * y ^ 2 = (t : K)) ∧
      (∃ z w : K, c₀ * z ^ 2 + c₁ * w ^ 2 = (t : K)) := by
  obtain ⟨x, y, z, w, hne, heq⟩ := hsol
  by_cases hval : c₀ * z ^ 2 + c₁ * w ^ 2 = 0
  · by_cases hzw : z ≠ 0 ∨ w ≠ 0
    · refine ⟨Units.mk0 a₀ ha₀, ⟨1, 0, by simp⟩, ?_⟩
      exact binary_represents_all_of_isotropic h2 hc₀ hc₁ ⟨z, w, hzw, hval⟩ a₀
    · push Not at hzw
      have hxy : x ≠ 0 ∨ y ≠ 0 := by
        rcases hne with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd hzw.1 h
        · exact absurd hzw.2 h
      have hxy0 : a₀ * x ^ 2 + a₁ * y ^ 2 = 0 := by
        rw [hzw.1, hzw.2] at heq
        linear_combination heq
      refine ⟨Units.mk0 c₀ hc₀, ?_, ⟨1, 0, by simp⟩⟩
      exact binary_represents_all_of_isotropic h2 ha₀ ha₁ ⟨x, y, hxy, hxy0⟩ c₀
  · refine ⟨Units.mk0 (c₀ * z ^ 2 + c₁ * w ^ 2) hval, ⟨x, y, ?_⟩, ⟨z, w, rfl⟩⟩
    rw [Units.val_mk0]
    linear_combination heq

private lemma diag_local_of_global {n : ℕ} (a : Fin n → ℚˣ) (hQ : HasDiagZeroQ a) :
    HasDiagZeroReal a ∧ ∀ p : ℕ, [Fact p.Prime] → HasDiagZeroPadic p a := by
  obtain ⟨v, hv, hsum⟩ := hQ
  refine ⟨⟨fun i => (v i : ℝ), ?_, ?_⟩, fun p _ => ⟨fun i => (v i : ℚ_[p]), ?_, ?_⟩⟩
  · intro h0
    apply hv
    ext i
    simpa using congrFun h0 i
  · have hcast := congrArg (Rat.cast (K := ℝ)) hsum
    simpa [HasDiagZeroK] using hcast
  · intro h0
    apply hv
    ext i
    simpa using congrFun h0 i
  · have hcast := congrArg (Rat.cast (K := ℚ_[p])) hsum
    simpa [HasDiagZeroK] using hcast

/-- **Dimension `n = 4` Hasse–Minkowski Theorem over `ℚ`**. -/
theorem hasse_minkowski_diag_4 (a : Fin 4 → ℚˣ) :
    HasDiagZeroQ a ↔ HasDiagZeroReal a ∧ ∀ p : ℕ, [Fact p.Prime] → HasDiagZeroPadic p a := by
  constructor
  · exact diag_local_of_global a
  · rintro ⟨hR, hP⟩
    let a₀ : ℚˣ := a 0
    let a₁ : ℚˣ := a 1
    let c₀ : ℚˣ := -a 2
    let c₁ : ℚˣ := -a 3
    have hR4 : ∃ x y z w : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0) ∧
        ((a₀ : ℚ) : ℝ) * x ^ 2 + ((a₁ : ℚ) : ℝ) * y ^ 2 +
          (-((c₀ : ℚ) : ℝ)) * z ^ 2 + (-((c₁ : ℚ) : ℝ)) * w ^ 2 = 0 := by
      obtain ⟨v, hv, hsum⟩ := hR
      refine ⟨v 0, v 1, v 2, v 3, ?_, ?_⟩
      · by_contra h0
        push Not at h0
        apply hv
        ext i
        fin_cases i <;> tauto
      · simp only [Fin.sum_univ_four] at hsum
        simpa [a₀, a₁, c₀, c₁] using hsum
    obtain ⟨t_inf, ht_inf_L, ht_inf_R⟩ := exists_common_binary_repr (by norm_num : (2 : ℝ) ≠ 0)
      (Rat.cast_ne_zero.mpr a₀.ne_zero) (Rat.cast_ne_zero.mpr a₁.ne_zero)
      (Rat.cast_ne_zero.mpr c₀.ne_zero) (Rat.cast_ne_zero.mpr c₁.ne_zero) hR4
    let S_fin : Finset ℕ :=
      ratBadPrimes a₀ ∪ ratBadPrimes a₁ ∪ ratBadPrimes c₀ ∪ ratBadPrimes c₁
    have hS_prime : ∀ p ∈ S_fin, p.Prime := by
      intro p hp
      simp only [S_fin, Finset.mem_union] at hp
      rcases hp with ((h | h) | h) | h <;> exact prime_mem_ratBadPrimes h
    have h2S : 2 ∈ S_fin := by
      simp only [S_fin, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (two_mem_ratBadPrimes a₀)))
    have hP_repr : ∀ (p : ℕ) [Fact p.Prime], p ∈ S_fin →
        ∃ t_p : ℚ_[p]ˣ,
          (∃ x y : ℚ_[p], ((a₀ : ℚ) : ℚ_[p]) * x ^ 2 + ((a₁ : ℚ) : ℚ_[p]) * y ^ 2 = (t_p : ℚ_[p])) ∧
          (∃ z w : ℚ_[p], ((c₀ : ℚ) : ℚ_[p]) * z ^ 2 + ((c₁ : ℚ) : ℚ_[p]) * w ^ 2 = (t_p : ℚ_[p])) := by
      intro p _ _
      obtain ⟨v, hv, hsum⟩ := hP p
      refine exists_common_binary_repr (by norm_num : (2 : ℚ_[p]) ≠ 0)
        (Rat.cast_ne_zero.mpr a₀.ne_zero) (Rat.cast_ne_zero.mpr a₁.ne_zero)
        (Rat.cast_ne_zero.mpr c₀.ne_zero) (Rat.cast_ne_zero.mpr c₁.ne_zero) ?_
      refine ⟨v 0, v 1, v 2, v 3, ?_, ?_⟩
      · by_contra h0
        push Not at h0
        apply hv
        ext i
        fin_cases i <;> tauto
      · simp only [Fin.sum_univ_four] at hsum
        simpa [a₀, a₁, c₀, c₁] using hsum
    let su : ℚˣ := if (0 : ℝ) < (t_inf : ℝ) then 1 else -1
    let ef : ℕ → ℕ := fun p =>
      if hp : p ∈ S_fin then
        letI : Fact p.Prime := ⟨hS_prime p hp⟩
        if Even (Padic.valuation ((hP_repr p hp).choose : ℚ_[p])) then 0 else 1
      else 0
    let rf : ℕ → ℕ := fun p => if p = 2 then 3 else 1
    let P_S : ℕ := ∏ p ∈ S_fin, p ^ ef p
    let P_rest : ℕ → ℕ := fun p => ∏ p' ∈ S_fin.erase p, p' ^ ef p'
    let M : ℕ := ∏ p ∈ S_fin, p ^ rf p
    have hM_pos : 0 < M := Finset.prod_pos fun p hp => pow_pos (hS_prime p hp).pos _
    have : NeZero M := ⟨hM_pos.ne'⟩
    have hres_p : ∀ p : ℕ, ∃ a_p : ℕ, ∀ (hp : p ∈ S_fin),
        letI : Fact p.Prime := ⟨hS_prime p hp⟩
        Nat.Coprime a_p (p ^ rf p) ∧
        (((su : ℚ).num * (P_rest p : ℤ) * (a_p : ℤ) : ℤ) : ZMod (p ^ rf p)) =
          PadicInt.toZModPow (rf p) ((padicUnitPart (hP_repr p hp).choose : ℤ_[p])) := by
      intro p
      by_cases hp : p ∈ S_fin
      · have : Fact p.Prime := ⟨hS_prime p hp⟩
        let t_p : ℚ_[p]ˣ := (hP_repr p hp).choose
        let u_p : ℤ_[p]ˣ := padicUnitPart t_p
        let w_u : (ZMod (p ^ rf p))ˣ := Units.map (PadicInt.toZModPow (rf p)).toMonoidHom u_p
        have : NeZero (p ^ rf p) := ⟨(pow_pos (hS_prime p hp).pos _).ne'⟩
        have hsu_cop : IsUnit ((su : ℚ).num : ZMod (p ^ rf p)) := by
          dsimp [su]
          split_ifs <;> simp
        have hPrest_ndvd : ¬ p ∣ P_rest p := by
          intro hd
          rw [Prime.dvd_finsetProd_iff (hS_prime p hp).prime] at hd
          obtain ⟨p', hp', hd'⟩ := hd
          rw [Finset.mem_erase] at hp'
          exact hp'.1 ((Nat.prime_dvd_prime_iff_eq (hS_prime p hp) (hS_prime p' hp'.2)).mp
            ((hS_prime p hp).dvd_of_dvd_pow hd')).symm
        have hPrest_cop : Nat.Coprime (P_rest p) (p ^ rf p) :=
          ((hS_prime p hp).coprime_iff_not_dvd.mpr hPrest_ndvd).symm.pow_right _
        let v_u : (ZMod (p ^ rf p))ˣ :=
          hsu_cop.unit * (ZMod.unitOfCoprime (P_rest p) hPrest_cop)
        let target : (ZMod (p ^ rf p))ˣ := v_u⁻¹ * w_u
        refine ⟨(target : ZMod (p ^ rf p)).val, fun _ => ⟨?_, ?_⟩⟩
        · exact ZMod.val_coe_unit_coprime target
        · have hval : ((target : ZMod (p ^ rf p)).val : ZMod (p ^ rf p)) = (target : ZMod (p ^ rf p)) :=
            ZMod.natCast_zmod_val _
          push_cast [hval]
          have hvu : ((su : ℚ).num : ZMod (p ^ rf p)) * (P_rest p : ZMod (p ^ rf p)) =
              (v_u : ZMod (p ^ rf p)) := by
            simp [v_u, ZMod.coe_unitOfCoprime]
          calc ((su : ℚ).num : ZMod (p ^ rf p)) * (P_rest p : ZMod (p ^ rf p)) *
                (target : ZMod (p ^ rf p))
              = (v_u : ZMod (p ^ rf p)) * (target : ZMod (p ^ rf p)) := by rw [hvu]
            _ = ((v_u * (v_u⁻¹ * w_u) : (ZMod (p ^ rf p))ˣ) : ZMod (p ^ rf p)) := rfl
            _ = ((1 * w_u : (ZMod (p ^ rf p))ˣ) : ZMod (p ^ rf p)) := by
                rw [← mul_assoc, mul_inv_cancel]
            _ = (w_u : ZMod (p ^ rf p)) := by rw [one_mul]
            _ = PadicInt.toZModPow (rf p) (u_p : ℤ_[p]) := rfl
      · exact ⟨1, fun h => absurd h hp⟩
    let af : ℕ → ℕ := fun p => (hres_p p).choose
    let mf : ℕ → ℕ := fun p => p ^ rf p
    have hm_ne : ∀ p ∈ S_fin, mf p ≠ 0 := fun p hp => pow_ne_zero _ (hS_prime p hp).ne_zero
    have hm_cop : (S_fin : Set ℕ).Pairwise (Function.onFun Nat.Coprime mf) := by
      intro p₁ hp₁ p₂ hp₂ hne
      exact Nat.Coprime.pow _ _ ((hS_prime p₁ hp₁).coprime_iff_not_dvd.mpr
        ((Nat.prime_dvd_prime_iff_eq (hS_prime p₁ hp₁) (hS_prime p₂ hp₂)).not.mpr hne))
    obtain ⟨A, hA⟩ := Nat.chineseRemainderOfFinset af mf S_fin hm_ne hm_cop
    have hA_cop : Nat.Coprime A M := by
      rw [show M = ∏ p ∈ S_fin, mf p from rfl]
      refine Nat.Coprime.prod_right fun p hp => ?_
      have hcop := ((hres_p p).choose_spec hp).1
      have hrf_pos : 0 < rf p := by dsimp [rf]; split_ifs <;> norm_num
      have hp_ndvd_a : ¬ p ∣ af p := fun hd =>
        (hS_prime p hp).not_dvd_one (hcop ▸ Nat.dvd_gcd hd (dvd_pow_self p hrf_pos.ne'))
      have hmodp : A % p = af p % p := (hA p hp).of_dvd (dvd_pow_self p hrf_pos.ne')
      exact ((hS_prime p hp).coprime_iff_not_dvd.mpr fun hd =>
        hp_ndvd_a (Nat.dvd_of_mod_eq_zero (hmodp ▸ Nat.mod_eq_zero_of_dvd hd))).symm.pow_right _
    have hinf_primes : {q : ℕ | q.Prime ∧ q ≡ A [MOD M]}.Infinite :=
      infinite_primes_modEq_of_density hA_cop
    obtain ⟨q, ⟨hq_prime, hq_mod⟩, hq_notS⟩ := (hinf_primes.sdiff S_fin.finite_toSet).nonempty
    change q ∉ S_fin at hq_notS
    have hq2 : q ≠ 2 := fun h => hq_notS (h ▸ h2S)
    have hPS_pos : 0 < P_S := Finset.prod_pos fun p hp => pow_pos (hS_prime p hp).pos _
    let t : ℚˣ := su * Units.mk0 ((P_S * q : ℕ) : ℚ) (Nat.cast_ne_zero.mpr (mul_ne_zero hPS_pos.ne' hq_prime.ne_zero))
    have ht_inf_sq : ∃ c : ℝˣ, ((t : ℚ) : ℝ) = (c : ℝ) ^ 2 * (t_inf : ℝ) := by
      have ht_pos_Pq : (0 : ℝ) < ((P_S * q : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos hPS_pos hq_prime.pos
      have hsame : 0 < ((t : ℚ) : ℝ) / (t_inf : ℝ) := by
        dsimp [t, su]
        split_ifs with hpos
        · simp only [Units.val_one, one_mul, Rat.cast_natCast]
          exact div_pos ht_pos_Pq hpos
        · have hneg : (t_inf : ℝ) < 0 := lt_of_le_of_ne (not_lt.mp hpos) t_inf.ne_zero
          simp only [Units.val_neg, Units.val_one, neg_mul, one_mul, Rat.cast_neg, Rat.cast_natCast]
          exact div_pos_of_neg_of_neg (neg_lt_zero.mpr ht_pos_Pq) hneg
      refine ⟨Units.mk0 (Real.sqrt (((t : ℚ) : ℝ) / (t_inf : ℝ))) (Real.sqrt_ne_zero'.mpr hsame), ?_⟩
      simp only [Units.val_mk0, Real.sq_sqrt hsame.le]
      field_simp [t_inf.ne_zero]
    have ht_pad_sq : ∀ (p : ℕ) [Fact p.Prime] (hp : p ∈ S_fin),
        ∃ c : ℚ_[p]ˣ, ((t : ℚ) : ℚ_[p]) = (c : ℚ_[p]) ^ 2 * ((hP_repr p hp).choose : ℚ_[p]) := by
      intro p _ hp
      let t_p : ℚ_[p]ˣ := (hP_repr p hp).choose
      let u_p : ℤ_[p]ˣ := padicUnitPart t_p
      have hPrest_ndvd : ¬ p ∣ P_rest p := by
        intro hd
        rw [Prime.dvd_finsetProd_iff (hS_prime p hp).prime] at hd
        obtain ⟨p', hp', hd'⟩ := hd
        rw [Finset.mem_erase] at hp'
        exact hp'.1 ((Nat.prime_dvd_prime_iff_eq (hS_prime p hp) (hS_prime p' hp'.2)).mp
          ((hS_prime p hp).dvd_of_dvd_pow hd')).symm
      have hq_ndvd : ¬ p ∣ q := fun hd =>
        hq_notS ((Nat.prime_dvd_prime_iff_eq (hS_prime p hp) hq_prime).mp hd ▸ hp)
      have hPS_eq : P_S = p ^ ef p * P_rest p := (Finset.mul_prod_erase S_fin (fun x => x ^ ef x) hp).symm
      have hq_mod_p : q ≡ af p [MOD p ^ rf p] := by
        have hdiv : p ^ rf p ∣ M := Finset.dvd_prod_of_mem _ hp
        exact (hq_mod.of_dvd hdiv).trans (hA p hp)
      have hsu_num : ((su : ℚ) : ℚ_[p]) = ((su : ℚ).num : ℤ_[p]) := by
        dsimp [su]; split_ifs <;> simp
      let u_t : ℤ_[p] := ((su : ℚ).num : ℤ_[p]) * (P_rest p : ℤ_[p]) * (q : ℤ_[p])
      have hu_t_mod : PadicInt.toZModPow (rf p) u_t = PadicInt.toZModPow (rf p) (u_p : ℤ_[p]) := by
        have hq_zmod : (q : ZMod (p ^ rf p)) = (af p : ZMod (p ^ rf p)) :=
          (ZMod.natCast_eq_natCast_iff q (af p) (p ^ rf p)).mpr hq_mod_p
        have heq := ((hres_p p).choose_spec hp).2
        dsimp [u_t]
        rw [map_mul, map_mul, map_intCast, map_natCast, map_natCast, hq_zmod]
        simpa [af] using heq
      have hu_t_unit : IsUnit u_t := by
        have h1 : IsUnit ((su : ℚ).num : ℤ_[p]) := by dsimp [su]; split_ifs <;> simp
        have h2 : IsUnit (P_rest p : ℤ_[p]) := padicInt_isUnit_natCast_of_not_dvd hPrest_ndvd
        have h3 : IsUnit (q : ℤ_[p]) := padicInt_isUnit_natCast_of_not_dvd hq_ndvd
        exact (h1.mul h2).mul h3
      let ratioZ : ℤ_[p]ˣ := hu_t_unit.unit * u_p⁻¹
      have hratio_sq : ∃ cZ : ℤ_[p], cZ ^ 2 = (ratioZ : ℤ_[p]) := by
        by_cases hp2 : p = 2
        · subst hp2
          have hrf2 : rf 2 = 3 := rfl
          have hu2 : PadicInt.toZModPow 3 u_t = PadicInt.toZModPow 3 (u_p : ℤ_[2]) := by
            rw [← hrf2]; exact hu_t_mod
          have hto : PadicInt.toZModPow 3 (ratioZ : ℤ_[2]) = 1 := by
            have hunit_u : ((hu_t_unit.unit : ℤ_[2])) = u_t := rfl
            simp only [ratioZ, Units.val_mul, map_mul]
            rw [hunit_u, hu2, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
          exact exists_sq_padicInt_two ratioZ hto
        · have hrfp : rf p = 1 := if_neg hp2
          have hu_p1 : PadicInt.toZModPow 1 u_t = PadicInt.toZModPow 1 (u_p : ℤ_[p]) := by
            rw [← hrfp]; exact hu_t_mod
          have hto : PadicInt.toZMod (ratioZ : ℤ_[p]) = 1 := by
            have hker : u_t - (u_p : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
              rw [PadicInt.ker_toZMod]
              change ¬ IsUnit (u_t - (u_p : ℤ_[p]))
              rw [PadicInt.not_isUnit_iff]
              have hmem1 : u_t - (u_p : ℤ_[p]) ∈ Ideal.span {((p : ℕ) : ℤ_[p]) ^ 1} := by
                rw [← PadicInt.ker_toZModPow 1]
                change PadicInt.toZModPow 1 (u_t - (u_p : ℤ_[p])) = 0
                rw [map_sub, hu_p1, sub_self]
              rw [pow_one] at hmem1
              exact (PadicInt.norm_lt_one_iff_dvd (u_t - (u_p : ℤ_[p]))).mpr
                (Ideal.mem_span_singleton.mp hmem1)
            have hmod : PadicInt.toZMod u_t = PadicInt.toZMod (u_p : ℤ_[p]) := by
              change PadicInt.toZMod (u_t - (u_p : ℤ_[p])) = 0 at hker
              rwa [map_sub, sub_eq_zero] at hker
            have hunit_u : ((hu_t_unit.unit : ℤ_[p])) = u_t := rfl
            simp only [ratioZ, Units.val_mul, map_mul]
            rw [hunit_u, hmod, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
          exact exists_sq_padicInt_odd hp2 ratioZ (by rw [hto]; exact ⟨1, by simp⟩)
      obtain ⟨cZ, hcZ⟩ := hratio_sq
      have hcZ0 : (cZ : ℚ_[p]) ≠ 0 := by
        intro h0
        have : ((ratioZ : ℤ_[p]) : ℚ_[p]) = 0 := by
          have := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hcZ
          simpa [h0] using this.symm
        have hnorm1 : ‖((ratioZ : ℤ_[p]) : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.mp ratioZ.isUnit
        rw [this, norm_zero] at hnorm1
        norm_num at hnorm1
      let v_p : ℤ := Padic.valuation (t_p : ℚ_[p])
      have hef_eq : ef p = if Even v_p then 0 else 1 := by
        dsimp [ef, v_p, t_p]; exact dif_pos hp
      have hev : Even ((ef p : ℤ) - v_p) := by
        rw [hef_eq]
        split_ifs with hv_even
        · obtain ⟨k, hk⟩ := hv_even
          exact ⟨-k, by omega⟩
        · have hv_odd : Odd v_p := Int.not_even_iff_odd.mp hv_even
          obtain ⟨k, hk⟩ := hv_odd
          exact ⟨-k, by omega⟩
      obtain ⟨m_val, hm_val⟩ := hev
      have hm_val' : (ef p : ℤ) - v_p = 2 * m_val := by omega
      have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (hS_prime p hp).ne_zero
      let c : ℚ_[p] := (cZ : ℚ_[p]) * (p : ℚ_[p]) ^ m_val
      have hc0 : c ≠ 0 := mul_ne_zero hcZ0 (zpow_ne_zero _ hp_ne)
      refine ⟨Units.mk0 c hc0, ?_⟩
      have ht_eq : ((t : ℚ) : ℚ_[p]) = (p : ℚ_[p]) ^ (ef p : ℤ) * (u_t : ℚ_[p]) := by
        simp only [t, Units.val_mul, Units.val_mk0, Rat.cast_mul, Rat.cast_natCast, hPS_eq]
        rw [hsu_num]
        dsimp [u_t]
        push_cast
        rw [zpow_natCast]
        ring
      have htp_eq : (t_p : ℚ_[p]) = (p : ℚ_[p]) ^ v_p * ((u_p : ℤ_[p]) : ℚ_[p]) :=
        padic_eq_p_zpow_mul_unitPart t_p
      have hcz_eq : (cZ : ℚ_[p]) ^ 2 * ((u_p : ℤ_[p]) : ℚ_[p]) = (u_t : ℚ_[p]) := by
        have hprodZ : (cZ : ℤ_[p]) ^ 2 * (u_p : ℤ_[p]) = u_t := by
          calc (cZ : ℤ_[p]) ^ 2 * (u_p : ℤ_[p])
              = (ratioZ : ℤ_[p]) * (u_p : ℤ_[p]) := by rw [hcZ]
            _ = (hu_t_unit.unit : ℤ_[p]) * ((u_p⁻¹ : ℤ_[p]ˣ) * u_p : ℤ_[p]ˣ) := by
                simp only [ratioZ, Units.val_mul, mul_assoc]
            _ = u_t := by rw [inv_mul_cancel, Units.val_one, mul_one]; rfl
        have hcast := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hprodZ
        simpa using hcast
      have hm_pow : ((p : ℚ_[p]) ^ m_val) ^ 2 = (p : ℚ_[p]) ^ (2 * m_val) := by
        rw [← zpow_natCast ((p : ℚ_[p]) ^ m_val) 2, ← zpow_mul]
        congr 1
        push_cast
        ring
      have hpow_add : (p : ℚ_[p]) ^ (2 * m_val) * (p : ℚ_[p]) ^ v_p = (p : ℚ_[p]) ^ (ef p : ℤ) := by
        rw [← zpow_add₀ hp_ne]
        congr 1
        omega
      simp only [Units.val_mk0, c]
      symm
      calc ((cZ : ℚ_[p]) * (p : ℚ_[p]) ^ m_val) ^ 2 * (t_p : ℚ_[p])
          = ((cZ : ℚ_[p]) ^ 2 * ((u_p : ℤ_[p]) : ℚ_[p])) *
              (((p : ℚ_[p]) ^ m_val) ^ 2 * (p : ℚ_[p]) ^ v_p) := by
            rw [htp_eq]; ring
        _ = (u_t : ℚ_[p]) * (p : ℚ_[p]) ^ (ef p : ℤ) := by
            rw [hcz_eq, hm_pow, hpow_add]
        _ = ((t : ℚ) : ℚ_[p]) := by rw [ht_eq, mul_comm]
    -- Now verify (a₀*t, a₁*t)_v = 1 and (c₀*t, c₁*t)_v = 1 for all v ≠ q, then all v!
    have hgood_odd : ∀ (p : ℕ) (hp : p.Prime) (_hp2 : p ≠ 2), p ∉ S_fin → p ≠ q →
        padicValRat p (t : ℚ) = 0 := by
      intro p hp _ hpS hpq
      have : Fact p.Prime := ⟨hp⟩
      have hsu_val : padicValRat p (su : ℚ) = 0 := by
        dsimp [su]; split_ifs <;> simp
      have hPS_ndvd : ¬ p ∣ P_S := by
        intro hd
        rw [Prime.dvd_finsetProd_iff hp.prime] at hd
        obtain ⟨p', hp', hd'⟩ := hd
        exact hpS ((Nat.prime_dvd_prime_iff_eq hp (hS_prime p' hp')).mp (hp.dvd_of_dvd_pow hd') ▸ hp')
      have hPq_ndvd : ¬ p ∣ P_S * q := fun hd =>
        (hp.dvd_mul.mp hd).elim hPS_ndvd (fun hdq =>
          hpq ((Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hdq))
      have hPq_val : padicValRat p ((P_S * q : ℕ) : ℚ) = 0 := by
        rw [padicValRat_def]
        change (padicValNat p (((P_S * q : ℕ) : ℚ).num.natAbs) : ℤ) -
          (padicValNat p (((P_S * q : ℕ) : ℚ).den) : ℤ) = 0
        rw [Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast,
          padicValNat.eq_zero_of_not_dvd hPq_ndvd, padicValNat_one_right]
        norm_num
      simp only [t, Units.val_mul, Units.val_mk0, padicValRat.mul su.ne_zero
        (Nat.cast_ne_zero.mpr (mul_ne_zero hPS_pos.ne' hq_prime.ne_zero)), hsu_val, hPq_val, add_zero]
    have hhilb_pair : ∀ (x₀ x₁ : ℚˣ),
        ratBadPrimes x₀ ⊆ S_fin → ratBadPrimes x₁ ⊆ S_fin →
        (∃ x y : ℝ, ((x₀ : ℚ) : ℝ) * x ^ 2 + ((x₁ : ℚ) : ℝ) * y ^ 2 = (t_inf : ℝ)) →
        (∀ (p : ℕ) [Fact p.Prime] (hp : p ∈ S_fin),
          ∃ x y : ℚ_[p], ((x₀ : ℚ) : ℚ_[p]) * x ^ 2 + ((x₁ : ℚ) : ℚ_[p]) * y ^ 2 =
            ((hP_repr p hp).choose : ℚ_[p])) →
        ∀ v : QPlace, hilbertSymAt v (-x₀ * (-t)) (-x₁ * (-t)) = 1 := by
      intro x₀ x₁ hx₀ hx₁ hxR hxP
      have hv_ne_q : ∀ v : QPlace, v ≠ QPlace.odd ⟨q, hq_prime, hq2⟩ →
          hilbertSymAt v (-x₀ * (-t)) (-x₁ * (-t)) = 1 := by
        intro v hvq
        cases v with
        | inf =>
          change hilbertSymInf (-x₀ * (-t)) (-x₁ * (-t)) = 1
          rw [hilbertSymInf_ternary_iff]
          obtain ⟨c, hc⟩ := ht_inf_sq
          obtain ⟨x, y, hxy⟩ := hxR
          have hsol : ∃ x' y' : ℝ, ((x₀ : ℚ) : ℝ) * x' ^ 2 + ((x₁ : ℚ) : ℝ) * y' ^ 2 =
              ((t : ℚ) : ℝ) := ⟨(c : ℝ) * x, (c : ℝ) * y, by rw [hc]; linear_combination (c : ℝ) ^ 2 * hxy⟩
          have htern := (binary_repr_iff_ternary_zero (by norm_num : (2 : ℝ) ≠ 0)
            (Rat.cast_ne_zero.mpr x₀.ne_zero) (Rat.cast_ne_zero.mpr x₁.ne_zero)
            (Rat.cast_ne_zero.mpr t.ne_zero)).mp hsol
          simpa [HasTernaryZeroReal, HasTernaryZeroK] using htern
        | two =>
          change hilbertSymTwo (-x₀ * (-t)) (-x₁ * (-t)) = 1
          rw [hilbertSymTwo_ternary_iff]
          have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          obtain ⟨c, hc⟩ := ht_pad_sq 2 h2S
          obtain ⟨x, y, hxy⟩ := hxP 2 h2S
          have hsol : ∃ x' y' : ℚ_[2], ((x₀ : ℚ) : ℚ_[2]) * x' ^ 2 + ((x₁ : ℚ) : ℚ_[2]) * y' ^ 2 =
              ((t : ℚ) : ℚ_[2]) := ⟨(c : ℚ_[2]) * x, (c : ℚ_[2]) * y, by rw [hc]; linear_combination (c : ℚ_[2]) ^ 2 * hxy⟩
          have htern := (binary_repr_iff_ternary_zero (by norm_num : (2 : ℚ_[2]) ≠ 0)
            (Rat.cast_ne_zero.mpr x₀.ne_zero) (Rat.cast_ne_zero.mpr x₁.ne_zero)
            (Rat.cast_ne_zero.mpr t.ne_zero)).mp hsol
          simpa [HasTernaryZeroPadic, HasTernaryZeroK] using htern
        | odd p =>
          change hilbertSymOdd p.1 p.2.1 p.2.2 (-x₀ * (-t)) (-x₁ * (-t)) = 1
          by_cases hpS : p.1 ∈ S_fin
          · have : Fact p.1.Prime := ⟨p.2.1⟩
            rw [hilbertSymOdd_ternary_iff p.1 p.2.2]
            obtain ⟨c, hc⟩ := ht_pad_sq p.1 hpS
            obtain ⟨x, y, hxy⟩ := hxP p.1 hpS
            have hsol : ∃ x' y' : ℚ_[p.1], ((x₀ : ℚ) : ℚ_[p.1]) * x' ^ 2 + ((x₁ : ℚ) : ℚ_[p.1]) * y' ^ 2 =
                ((t : ℚ) : ℚ_[p.1]) := ⟨(c : ℚ_[p.1]) * x, (c : ℚ_[p.1]) * y, by rw [hc]; linear_combination (c : ℚ_[p.1]) ^ 2 * hxy⟩
            have htern := (binary_repr_iff_ternary_zero (by norm_num : (2 : ℚ_[p.1]) ≠ 0)
              (Rat.cast_ne_zero.mpr x₀.ne_zero) (Rat.cast_ne_zero.mpr x₁.ne_zero)
              (Rat.cast_ne_zero.mpr t.ne_zero)).mp hsol
            simpa [HasTernaryZeroPadic, HasTernaryZeroK] using htern
          · have hpq : p.1 ≠ q := fun heq => hvq (by
              congr 1; exact Subtype.ext heq)
            have ht_val := hgood_odd p.1 p.2.1 p.2.2 hpS hpq
            have hx0_val := padicValRat_eq_zero_of_not_mem_ratBadPrimes p.2.1 (fun h => hpS (hx₀ h))
            have hx1_val := padicValRat_eq_zero_of_not_mem_ratBadPrimes p.2.1 (fun h => hpS (hx₁ h))
            have h0t : padicValRat p.1 ((-x₀ * (-t) : ℚˣ) : ℚ) = 0 := by
              have : Fact p.1.Prime := ⟨p.2.1⟩
              simp [padicValRat.mul, hx0_val, ht_val]
            have h1t : padicValRat p.1 ((-x₁ * (-t) : ℚˣ) : ℚ) = 0 := by
              have : Fact p.1.Prime := ⟨p.2.1⟩
              simp [padicValRat.mul, hx1_val, ht_val]
            exact hilbertSymOdd_eq_one_of_val_zero p.1 p.2.1 p.2.2 h0t h1t
      intro v
      by_cases hv : v = QPlace.odd ⟨q, hq_prime, hq2⟩
      · subst hv
        exact hilbertSymAt_eq_one_of_others_eq_one _ hv_ne_q
      · exact hv_ne_q v hv
    have ha_tern : HasTernaryZeroQ a₀ a₁ (-t) := (hasse_minkowski_ternary_Q a₀ a₁ (-t)).mpr
      (hhilb_pair a₀ a₁ (by intro p hp; simp [S_fin, hp]) (by intro p hp; simp [S_fin, hp])
        ht_inf_L (fun p _ hp => (hP_repr p hp).choose_spec.1))
    have hc_tern : HasTernaryZeroQ c₀ c₁ (-t) := (hasse_minkowski_ternary_Q c₀ c₁ (-t)).mpr
      (hhilb_pair c₀ c₁ (by intro p hp; simp [S_fin, hp]) (by intro p hp; simp [S_fin, hp])
        ht_inf_R (fun p _ hp => (hP_repr p hp).choose_spec.2))
    have ha_repr : ∃ x y : ℚ, (a₀ : ℚ) * x ^ 2 + (a₁ : ℚ) * y ^ 2 = (t : ℚ) :=
      (binary_repr_iff_ternary_zero (by norm_num : (2 : ℚ) ≠ 0) a₀.ne_zero a₁.ne_zero t.ne_zero).mpr ha_tern
    have hc_repr : ∃ z w : ℚ, (c₀ : ℚ) * z ^ 2 + (c₁ : ℚ) * w ^ 2 = (t : ℚ) :=
      (binary_repr_iff_ternary_zero (by norm_num : (2 : ℚ) ≠ 0) c₀.ne_zero c₁.ne_zero t.ne_zero).mpr hc_tern
    obtain ⟨x, y, hxy⟩ := ha_repr
    obtain ⟨z, w, hzw⟩ := hc_repr
    refine ⟨![x, y, z, w], ?_, ?_⟩
    · intro h0
      have hx0 : x = 0 := by simpa using congrFun h0 0
      have hy0 : y = 0 := by simpa using congrFun h0 1
      rw [hx0, hy0] at hxy
      simp at hxy
      exact t.ne_zero hxy.symm
    · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three]
      have ha2 : (a 2 : ℚ) = -(c₀ : ℚ) := by simp [c₀]
      have ha3 : (a 3 : ℚ) = -(c₁ : ℚ) := by simp [c₁]
      change (a₀ : ℚ) * x ^ 2 + (a₁ : ℚ) * y ^ 2 + (a 2 : ℚ) * z ^ 2 + (a 3 : ℚ) * w ^ 2 = 0
      rw [ha2, ha3]
      linear_combination hxy - hzw

end DimFour

/-! ## Section 4: Dimension `n ≥ 5` by Induction & Full Diagonal Hasse–Minkowski -/

section DimGeFive

/-- Padding a `(m + 3)`-vector with 2 leading zeros preserves diagonal-form evaluation. -/
theorem hasDiagZeroK_tail_of_head_three {K : Type*} [Field K] {m : ℕ}
    {b : Fin (m + 3) → K} (_hb0 : b 0 ≠ 0) (_hb1 : b 1 ≠ 0) (_hb2 : b 2 ≠ 0)
    (htern : HasTernaryZeroK (b 0) (b 1) (b 2)) :
    HasDiagZeroK b := by
  obtain ⟨x, y, z, hne, heq⟩ := htern
  let v : Fin (m + 3) → K := fun j =>
    if j.1 = 0 then x else if j.1 = 1 then y else if j.1 = 2 then z else 0
  refine ⟨v, ?_, ?_⟩
  · intro h0
    rcases hne with h | h | h
    · exact h (by simpa [v] using congrFun h0 ⟨0, by omega⟩)
    · exact h (by simpa [v] using congrFun h0 ⟨1, by omega⟩)
    · exact h (by simpa [v] using congrFun h0 ⟨2, by omega⟩)
  · have hsum : (∑ j : Fin (m + 3), b j * (v j) ^ 2) =
        b 0 * x ^ 2 + b 1 * y ^ 2 + b 2 * z ^ 2 := by
      have hsplit : (∑ j : Fin (m + 3), b j * (v j) ^ 2) =
          ∑ j ∈ ({⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin (m + 3))),
            b j * (v j) ^ 2 := by
        rw [← Finset.sum_subset (Finset.subset_univ _)]
        intro j _ hj
        simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, not_or] at hj
        have hvj : v j = 0 := by
          dsimp [v]
          rw [if_neg hj.1, if_neg hj.2.1, if_neg hj.2.2]
        rw [hvj, zero_pow two_ne_zero, mul_zero]
      rw [hsplit, Finset.sum_insert (by simp [Fin.ext_iff]),
        Finset.sum_insert (by simp [Fin.ext_iff]), Finset.sum_singleton]
      have hv0 : v ⟨0, by omega⟩ = x := by simp [v]
      have hv1 : v ⟨1, by omega⟩ = y := by simp [v]
      have hv2 : v ⟨2, by omega⟩ = z := by simp [v]
      have hb0' : b ⟨0, by omega⟩ = b 0 := rfl
      have hb1' : b ⟨1, by omega⟩ = b 1 := rfl
      have hb2' : b ⟨2, by omega⟩ = b 2 := rfl
      rw [hv0, hv1, hv2, hb0', hb1', hb2']
      ring
    rw [hsum, heq]

private lemma diag_sum_split {K : Type*} [Field K] {m : ℕ}
    (a : Fin (m + 5) → ℚˣ) (f : ℚˣ → K) (v : Fin (m + 5) → K) :
    (∑ i : Fin (m + 5), f (a i) * (v i) ^ 2) =
      f (a 0) * (v 0) ^ 2 + f (a 1) * (v 1) ^ 2 +
        ∑ j : Fin (m + 3), f (a ⟨j.1 + 2, by omega⟩) * (v ⟨j.1 + 2, by omega⟩) ^ 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hsum : (∑ j : Fin (m + 3), f (a j.succ.succ) * (v j.succ.succ) ^ 2) =
      ∑ j : Fin (m + 3), f (a ⟨j.1 + 2, by omega⟩) * (v ⟨j.1 + 2, by omega⟩) ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : j.succ.succ = ⟨j.1 + 2, by omega⟩ := by ext; simp
    rw [hj]
  have h1 : (0 : Fin (m + 4)).succ = (1 : Fin (m + 5)) := by ext; rfl
  rw [hsum, h1]
  exact (add_assoc _ _ _).symm

/-- Inductive step for `n = m + 5 ≥ 5`: reduces `n`-variable diagonal Hasse–Minkowski to `n - 1`. -/
theorem hasse_minkowski_diag_step (m : ℕ)
    (IH : ∀ c : Fin (m + 4) → ℚˣ,
      HasDiagZeroReal c ∧ (∀ p : ℕ, [Fact p.Prime] → HasDiagZeroPadic p c) → HasDiagZeroQ c)
    (a : Fin (m + 5) → ℚˣ)
    (hR : HasDiagZeroReal a)
    (hP : ∀ p : ℕ, [Fact p.Prime] → HasDiagZeroPadic p a) :
    HasDiagZeroQ a := by
  classical
  let a₀ : ℚˣ := a 0
  let a₁ : ℚˣ := a 1
  let b : Fin (m + 3) → ℚˣ := fun j => a ⟨j.1 + 2, by omega⟩
  let S_fin : Finset ℕ := Finset.univ.biUnion (fun i : Fin (m + 5) => ratBadPrimes (a i))
  have hS_prime : ∀ p ∈ S_fin, p.Prime := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨i, _, hi⟩ := hp
    exact prime_mem_ratBadPrimes hi
  have hb_good_odd : ∀ (p : ℕ) [Fact p.Prime], p ∉ S_fin →
      HasDiagZeroPadic p b := by
    intro p _ hpS
    have hp : p.Prime := Fact.out
    have hp2 : p ≠ 2 := fun h => hpS (Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, h ▸ two_mem_ratBadPrimes _⟩)
    have hval : ∀ j : Fin (m + 3), padicValRat p (b j : ℚ) = 0 := fun j =>
      padicValRat_eq_zero_of_not_mem_ratBadPrimes hp
        (fun h => hpS (Finset.mem_biUnion.mpr ⟨⟨j.1 + 2, by omega⟩, Finset.mem_univ _, h⟩))
    have htern := hasTernaryZeroPadic_of_val_zero p hp2 (hval 0) (hval 1) (hval 2)
    exact hasDiagZeroK_tail_of_head_three (Rat.cast_ne_zero.mpr (b 0).ne_zero)
      (Rat.cast_ne_zero.mpr (b 1).ne_zero) (Rat.cast_ne_zero.mpr (b 2).ne_zero) htern
  -- Helper: extract local `(x₀, x₁, y)` at any field where `a` is isotropic and `b` is anisotropic
  have extract_aniso : ∀ {K : Type} [Field K] (_h2 : (2 : K) ≠ 0) (f : ℚˣ → K) (hf : ∀ u, f u ≠ 0)
      (_hzero : HasDiagZeroK (fun i => f (a i))) (_haniso : ¬ HasDiagZeroK (fun j => f (b j))),
      ∃ x₀ x₁ : K, f a₀ * x₀ ^ 2 + f a₁ * x₁ ^ 2 ≠ 0 ∧
        ∃ y : Fin (m + 3) → K, y ≠ 0 ∧
          f a₀ * x₀ ^ 2 + f a₁ * x₁ ^ 2 + ∑ j : Fin (m + 3), f (b j) * (y j) ^ 2 = 0 := by
    intro K _ h2 f hf ⟨v, hv, hsum⟩ haniso
    change (∑ i : Fin (m + 5), f (a i) * (v i) ^ 2) = 0 at hsum
    rw [diag_sum_split a f v] at hsum
    let y : Fin (m + 3) → K := fun j => v ⟨j.1 + 2, by omega⟩
    by_cases hy : y = 0
    · have hv01 : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
        by_contra h01
        push Not at h01
        apply hv
        ext i
        rcases lt_or_ge i.1 2 with hi | hi
        · interval_cases hval : i.1
          · exact (show i = 0 from Fin.ext hval) ▸ h01.1
          · exact (show i = 1 from Fin.ext hval) ▸ h01.2
        · have hj := congrFun hy ⟨i.1 - 2, by omega⟩
          simpa [y, show i.1 - 2 + 2 = i.1 by omega, Fin.ext_iff] using hj
      have hxy0 : f a₀ * (v 0) ^ 2 + f a₁ * (v 1) ^ 2 = 0 := by
        have hys : (∑ j : Fin (m + 3), f (b j) * (y j) ^ 2) = 0 := by simp [hy]
        linear_combination hsum - hys
      obtain ⟨x₀, x₁, hx⟩ := binary_represents_all_of_isotropic h2 (hf a₀) (hf a₁)
        ⟨v 0, v 1, hv01, hxy0⟩ (-f (b 0))
      let e0 : Fin (m + 3) → K := fun j => if j = 0 then 1 else 0
      refine ⟨x₀, x₁, ?_, e0, ?_, ?_⟩
      · rw [hx]; exact neg_ne_zero.mpr (hf (b 0))
      · intro h0
        have := congrFun h0 0
        simp [e0] at this
      · have hys : (∑ j : Fin (m + 3), f (b j) * (e0 j) ^ 2) = f (b 0) := by
          rw [Finset.sum_eq_single (0 : Fin (m + 3))]
          · simp [e0]
          · intro j _ hj
            simp [e0, hj]
          · simp
        rw [hx, hys, neg_add_cancel]
    · have hne_sum : (∑ j : Fin (m + 3), f (b j) * (y j) ^ 2) ≠ 0 :=
        fun h0 => haniso ⟨y, hy, h0⟩
      refine ⟨v 0, v 1, ?_, y, hy, hsum⟩
      intro h0
      apply hne_sum
      linear_combination hsum - h0
  -- Choose `(x₀, x₁) ∈ ℚ²` with `c := a₀ x₀² + a₁ x₁² ≠ 0` making `c u² + Q_b` locally isotropic everywhere
  have hpick : ∃ x₀ x₁ : ℚ,
      let cℚ : ℚ := (a₀ : ℚ) * x₀ ^ 2 + (a₁ : ℚ) * x₁ ^ 2
      ∃ hc : cℚ ≠ 0,
        let c : ℚˣ := Units.mk0 cℚ hc
        HasDiagZeroReal (Fin.cons c b) ∧
        ∀ p : ℕ, [Fact p.Prime] → HasDiagZeroPadic p (Fin.cons c b) := by
    by_cases h_all_iso : HasDiagZeroReal b ∧ ∀ (p : ℕ) [Fact p.Prime], p ∈ S_fin →
        HasDiagZeroPadic p b
    · refine ⟨1, 0, ?_⟩
      have hc0 : (a₀ : ℚ) * 1 ^ 2 + (a₁ : ℚ) * 0 ^ 2 ≠ 0 := by simp [a₀.ne_zero]
      refine ⟨hc0, ?_, ?_⟩
      · obtain ⟨y, hy, hys⟩ := h_all_iso.1
        refine ⟨Fin.cons 0 y, ?_, ?_⟩
        · intro h0
          apply hy
          ext j
          have := congrFun h0 j.succ
          simpa using this
        · simpa [Fin.sum_univ_succ] using hys
      · intro p _
        by_cases hpS : p ∈ S_fin
        · obtain ⟨y, hy, hys⟩ := h_all_iso.2 p hpS
          refine ⟨Fin.cons 0 y, ?_, ?_⟩
          · intro h0
            apply hy
            ext j
            have := congrFun h0 j.succ
            simpa using this
          · simpa [Fin.sum_univ_succ] using hys
        · obtain ⟨y, hy, hys⟩ := hb_good_odd p hpS
          refine ⟨Fin.cons 0 y, ?_, ?_⟩
          · intro h0
            apply hy
            ext j
            have := congrFun h0 j.succ
            simpa using this
          · simpa [Fin.sum_univ_succ] using hys
    · -- At least one place in `{∞} ∪ S_fin` has `b` anisotropic; approximate locally via `weak_approx_Q`
      have hR_data : ∃ x₀ x₁ : ℝ,
          HasDiagZeroReal b ∨
          (let t := ((a₀ : ℚ) : ℝ) * x₀ ^ 2 + ((a₁ : ℚ) : ℝ) * x₁ ^ 2
           t ≠ 0 ∧ ∃ y : Fin (m + 3) → ℝ, y ≠ 0 ∧
             t + ∑ j : Fin (m + 3), ((b j : ℚ) : ℝ) * (y j) ^ 2 = 0) := by
        by_cases hbR : HasDiagZeroReal b
        · exact ⟨1, 0, Or.inl hbR⟩
        · obtain ⟨x₀, x₁, ht, y, hy, hsum⟩ := extract_aniso (by norm_num : (2 : ℝ) ≠ 0)
            (fun u => ((u : ℚ) : ℝ)) (fun u => Rat.cast_ne_zero.mpr u.ne_zero) hR hbR
          exact ⟨x₀, x₁, Or.inr ⟨ht, y, hy, hsum⟩⟩
      obtain ⟨xR0, xR1, hR_case⟩ := hR_data
      have hP_data : ∀ (p : ℕ) [Fact p.Prime], ∃ x₀ x₁ : ℚ_[p], p ∈ S_fin →
          HasDiagZeroPadic p b ∨
          (let t := ((a₀ : ℚ) : ℚ_[p]) * x₀ ^ 2 + ((a₁ : ℚ) : ℚ_[p]) * x₁ ^ 2
           t ≠ 0 ∧ ∃ y : Fin (m + 3) → ℚ_[p], y ≠ 0 ∧
             t + ∑ j : Fin (m + 3), ((b j : ℚ) : ℚ_[p]) * (y j) ^ 2 = 0) := by
        intro p _
        by_cases hp : p ∈ S_fin
        · by_cases hbp : HasDiagZeroPadic p b
          · exact ⟨1, 0, fun _ => Or.inl hbp⟩
          · obtain ⟨x₀, x₁, ht, y, hy, hsum⟩ := extract_aniso (by norm_num : (2 : ℚ_[p]) ≠ 0)
              (fun u => ((u : ℚ) : ℚ_[p])) (fun u => Rat.cast_ne_zero.mpr u.ne_zero) (hP p) hbp
            exact ⟨x₀, x₁, fun _ => Or.inr ⟨ht, y, hy, hsum⟩⟩
        · exact ⟨0, 0, fun h => absurd h hp⟩
      let xP0 : ∀ (p : ℕ) [Fact p.Prime], ℚ_[p] := fun p _ => (hP_data p).choose
      let xP1 : ∀ (p : ℕ) [Fact p.Prime], ℚ_[p] := fun p _ => (hP_data p).choose_spec.choose
      let tR : ℝ := ((a₀ : ℚ) : ℝ) * xR0 ^ 2 + ((a₁ : ℚ) : ℝ) * xR1 ^ 2
      let ε : ℝ :=
        if h : HasDiagZeroReal b then 1
        else min 1 (|tR| / (2 * (|((a₀ : ℚ) : ℝ)| * (2 * |xR0| + 1) +
          |((a₁ : ℚ) : ℝ)| * (2 * |xR1| + 1) + 1)))
      have hε_pos : 0 < ε := by
        dsimp [ε]
        split_ifs with h
        · norm_num
        · rcases hR_case with h1 | ⟨htR, _⟩
          · exact absurd h1 h
          · have hden : 0 < 2 * (|((a₀ : ℚ) : ℝ)| * (2 * |xR0| + 1) +
                |((a₁ : ℚ) : ℝ)| * (2 * |xR1| + 1) + 1) := by positivity
            exact lt_min one_pos (div_pos (abs_pos.mpr htR) hden)
      let KP : ℕ → ℕ := fun p =>
        if hp : p ∈ S_fin then
          letI : Fact p.Prime := ⟨hS_prime p hp⟩
          let t_p : ℚ_[p] := ((a₀ : ℚ) : ℚ_[p]) * (xP0 p) ^ 2 + ((a₁ : ℚ) : ℚ_[p]) * (xP1 p) ^ 2
          if hbp : HasDiagZeroPadic p b then 0
          else
            let C0 : ℝ := max (‖((a₀ : ℚ) : ℚ_[p])‖ * max 1 (2 * ‖xP0 p‖ + 1))
              (‖((a₁ : ℚ) : ℚ_[p])‖ * max 1 (2 * ‖xP1 p‖ + 1))
            (Padic.valuation t_p).natAbs + (Nat.clog p (Nat.ceil (max 1 C0) + 1)) + 4
        else 0
      obtain ⟨x₀, hx₀R, hx₀P⟩ := weak_approx_Q S_fin hS_prime xR0 ε hε_pos xP0 KP
      obtain ⟨x₁, hx₁R, hx₁P⟩ := weak_approx_Q S_fin hS_prime xR1 ε hε_pos xP1 KP
      let cℚ : ℚ := (a₀ : ℚ) * x₀ ^ 2 + (a₁ : ℚ) * x₁ ^ 2
      have hR_diff_bd : ¬ HasDiagZeroReal b → |(cℚ : ℝ) - tR| < |tR| := by
        intro hbR
        obtain ⟨htR, _⟩ := hR_case.resolve_left hbR
        have hε_le1 : ε ≤ 1 := by
          dsimp [ε]; rw [if_neg hbR]; exact min_le_left _ _
        have hx0_bd : |(x₀ : ℝ) + xR0| ≤ 2 * |xR0| + 1 := by
          have h1 : |(x₀ : ℝ) - xR0| < 1 := lt_of_lt_of_le hx₀R hε_le1
          calc |(x₀ : ℝ) + xR0| = |((x₀ : ℝ) - xR0) + 2 * xR0| := by ring_nf
            _ ≤ |(x₀ : ℝ) - xR0| + |2 * xR0| := abs_add_le _ _
            _ ≤ 1 + 2 * |xR0| := by
                rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
                linarith
            _ = 2 * |xR0| + 1 := by ring
        have hx1_bd : |(x₁ : ℝ) + xR1| ≤ 2 * |xR1| + 1 := by
          have h1 : |(x₁ : ℝ) - xR1| < 1 := lt_of_lt_of_le hx₁R hε_le1
          calc |(x₁ : ℝ) + xR1| = |((x₁ : ℝ) - xR1) + 2 * xR1| := by ring_nf
            _ ≤ |(x₁ : ℝ) - xR1| + |2 * xR1| := abs_add_le _ _
            _ ≤ 1 + 2 * |xR1| := by
                rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
                linarith
            _ = 2 * |xR1| + 1 := by ring
        have hdecomp : (cℚ : ℝ) - tR =
            ((a₀ : ℚ) : ℝ) * ((x₀ : ℝ) - xR0) * ((x₀ : ℝ) + xR0) +
            ((a₁ : ℚ) : ℝ) * ((x₁ : ℝ) - xR1) * ((x₁ : ℝ) + xR1) := by
          dsimp [cℚ, tR]; push_cast; ring
        have hD_pos : 0 < |((a₀ : ℚ) : ℝ)| * (2 * |xR0| + 1) +
            |((a₁ : ℚ) : ℝ)| * (2 * |xR1| + 1) + 1 := by positivity
        have hε_bound : ε ≤ |tR| / (2 * (|((a₀ : ℚ) : ℝ)| * (2 * |xR0| + 1) +
            |((a₁ : ℚ) : ℝ)| * (2 * |xR1| + 1) + 1)) := by
          dsimp [ε]; rw [if_neg hbR]; exact min_le_right _ _
        calc |(cℚ : ℝ) - tR|
            ≤ |((a₀ : ℚ) : ℝ) * ((x₀ : ℝ) - xR0) * ((x₀ : ℝ) + xR0)| +
              |((a₁ : ℚ) : ℝ) * ((x₁ : ℝ) - xR1) * ((x₁ : ℝ) + xR1)| := by
                rw [hdecomp]; exact abs_add_le _ _
          _ = |((a₀ : ℚ) : ℝ)| * |(x₀ : ℝ) - xR0| * |(x₀ : ℝ) + xR0| +
              |((a₁ : ℚ) : ℝ)| * |(x₁ : ℝ) - xR1| * |(x₁ : ℝ) + xR1| := by
                simp only [abs_mul]
          _ ≤ |((a₀ : ℚ) : ℝ)| * ε * (2 * |xR0| + 1) +
              |((a₁ : ℚ) : ℝ)| * ε * (2 * |xR1| + 1) := by
                gcongr
          _ < ε * (|((a₀ : ℚ) : ℝ)| * (2 * |xR0| + 1) +
              |((a₁ : ℚ) : ℝ)| * (2 * |xR1| + 1) + 1) := by linarith
          _ ≤ |tR| / 2 := by
                have := mul_le_mul_of_nonneg_right hε_bound hD_pos.le
                have hne : |((a₀ : ℚ) : ℝ)| * (2 * |xR0| + 1) +
                    |((a₁ : ℚ) : ℝ)| * (2 * |xR1| + 1) + 1 ≠ 0 := hD_pos.ne'
                calc ε * _ ≤ (|tR| / (2 * _)) * _ := this
                  _ = |tR| / 2 := by field_simp [hne]
          _ < |tR| := half_lt_self (abs_pos.mpr htR)
      have hP_diff_bd : ∀ (p : ℕ) [Fact p.Prime] (hpS : p ∈ S_fin),
          ¬ HasDiagZeroPadic p b →
          let t_p : ℚ_[p] := ((a₀ : ℚ) : ℚ_[p]) * (xP0 p) ^ 2 +
            ((a₁ : ℚ) : ℚ_[p]) * (xP1 p) ^ 2
          ‖(cℚ : ℚ_[p]) - t_p‖ ≤ ‖t_p‖ * (p : ℝ) ^ (-3 : ℤ) := by
        intro p _ hpS hbp
        obtain ⟨htp, _⟩ := ((hP_data p).choose_spec.choose_spec hpS).resolve_left hbp
        have hp : p.Prime := hS_prime p hpS
        have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
        have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
        let t_p : ℚ_[p] := ((a₀ : ℚ) : ℚ_[p]) * (xP0 p) ^ 2 +
          ((a₁ : ℚ) : ℚ_[p]) * (xP1 p) ^ 2
        let C0 : ℝ := max (‖((a₀ : ℚ) : ℚ_[p])‖ * max 1 (2 * ‖xP0 p‖ + 1))
          (‖((a₁ : ℚ) : ℚ_[p])‖ * max 1 (2 * ‖xP1 p‖ + 1))
        have hx0n := hx₀P p hpS
        have hx1n := hx₁P p hpS
        have hKP_def : KP p = (Padic.valuation t_p).natAbs +
            Nat.clog p (Nat.ceil (max 1 C0) + 1) + 4 := by
          dsimp [KP]; rw [dif_pos hpS, dif_neg hbp]
        have hK_le1 : (p : ℝ) ^ (-(KP p : ℤ)) ≤ 1 := by
          have hexp : -(KP p : ℤ) ≤ 0 := by omega
          calc (p : ℝ) ^ (-(KP p : ℤ)) ≤ (p : ℝ) ^ (0 : ℤ) := zpow_le_zpow_right₀ hp1 hexp
            _ = 1 := zpow_zero _
        have hadd_bd : ∀ (x x0 : ℚ_[p]), ‖x - x0‖ ≤ 1 →
            ‖x + x0‖ ≤ max 1 (2 * ‖x0‖ + 1) := by
          intro x x0 hx
          calc ‖x + x0‖ = ‖(x - x0) + 2 * x0‖ := by ring_nf
            _ ≤ max ‖x - x0‖ ‖2 * x0‖ := Padic.nonarchimedean _ _
            _ ≤ max 1 (2 * ‖x0‖ + 1) := by
                refine max_le_max hx ?_
                rw [norm_mul]
                have h2n : ‖(2 : ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (2 : ℤ_[p])
                calc ‖(2 : ℚ_[p])‖ * ‖x0‖ ≤ 1 * ‖x0‖ := mul_le_mul_of_nonneg_right h2n (norm_nonneg _)
                  _ ≤ 2 * ‖x0‖ + 1 := by linarith [norm_nonneg x0]
        have hx0_sum := hadd_bd (x₀ : ℚ_[p]) (xP0 p) (hx0n.trans hK_le1)
        have hx1_sum := hadd_bd (x₁ : ℚ_[p]) (xP1 p) (hx1n.trans hK_le1)
        have hdecomp : (cℚ : ℚ_[p]) - t_p =
            ((a₀ : ℚ) : ℚ_[p]) * ((x₀ : ℚ_[p]) - xP0 p) * ((x₀ : ℚ_[p]) + xP0 p) +
            ((a₁ : ℚ) : ℚ_[p]) * ((x₁ : ℚ_[p]) - xP1 p) * ((x₁ : ℚ_[p]) + xP1 p) := by
          dsimp [cℚ, t_p]; push_cast; ring
        have hterm0 : ‖((a₀ : ℚ) : ℚ_[p]) * ((x₀ : ℚ_[p]) - xP0 p) *
            ((x₀ : ℚ_[p]) + xP0 p)‖ ≤ (p : ℝ) ^ (-(KP p : ℤ)) * C0 := by
          rw [norm_mul, norm_mul]
          calc ‖((a₀ : ℚ) : ℚ_[p])‖ * ‖(x₀ : ℚ_[p]) - xP0 p‖ * ‖(x₀ : ℚ_[p]) + xP0 p‖
              ≤ ‖((a₀ : ℚ) : ℚ_[p])‖ * (p : ℝ) ^ (-(KP p : ℤ)) * max 1 (2 * ‖xP0 p‖ + 1) := by
                gcongr
            _ = (p : ℝ) ^ (-(KP p : ℤ)) * (‖((a₀ : ℚ) : ℚ_[p])‖ * max 1 (2 * ‖xP0 p‖ + 1)) := by ring
            _ ≤ (p : ℝ) ^ (-(KP p : ℤ)) * C0 := by
                gcongr; exact le_max_left _ _
        have hterm1 : ‖((a₁ : ℚ) : ℚ_[p]) * ((x₁ : ℚ_[p]) - xP1 p) *
            ((x₁ : ℚ_[p]) + xP1 p)‖ ≤ (p : ℝ) ^ (-(KP p : ℤ)) * C0 := by
          rw [norm_mul, norm_mul]
          calc ‖((a₁ : ℚ) : ℚ_[p])‖ * ‖(x₁ : ℚ_[p]) - xP1 p‖ * ‖(x₁ : ℚ_[p]) + xP1 p‖
              ≤ ‖((a₁ : ℚ) : ℚ_[p])‖ * (p : ℝ) ^ (-(KP p : ℤ)) * max 1 (2 * ‖xP1 p‖ + 1) := by
                gcongr
            _ = (p : ℝ) ^ (-(KP p : ℤ)) * (‖((a₁ : ℚ) : ℚ_[p])‖ * max 1 (2 * ‖xP1 p‖ + 1)) := by ring
            _ ≤ (p : ℝ) ^ (-(KP p : ℤ)) * C0 := by
                gcongr; exact le_max_right _ _
        have hdiff_le : ‖(cℚ : ℚ_[p]) - t_p‖ ≤ (p : ℝ) ^ (-(KP p : ℤ)) * max 1 C0 := by
          rw [hdecomp]
          calc ‖_ + _‖ ≤ max ‖_‖ ‖_‖ := Padic.nonarchimedean _ _
            _ ≤ (p : ℝ) ^ (-(KP p : ℤ)) * C0 := max_le hterm0 hterm1
            _ ≤ (p : ℝ) ^ (-(KP p : ℤ)) * max 1 C0 := by
                gcongr; exact le_max_right _ _
        have hC0_pow : max 1 C0 ≤ (p : ℝ) ^ (Nat.clog p (Nat.ceil (max 1 C0) + 1) : ℤ) := by
          have h1 : max 1 C0 ≤ (Nat.ceil (max 1 C0) + 1 : ℕ) := by
            have := Nat.le_ceil (max 1 C0)
            push_cast
            linarith
          have h2 : Nat.ceil (max 1 C0) + 1 ≤ p ^ Nat.clog p (Nat.ceil (max 1 C0) + 1) :=
            Nat.le_pow_clog hp.one_lt _
          calc max 1 C0 ≤ (Nat.ceil (max 1 C0) + 1 : ℕ) := h1
            _ ≤ ((p ^ Nat.clog p (Nat.ceil (max 1 C0) + 1) : ℕ) : ℝ) := by exact_mod_cast h2
            _ = (p : ℝ) ^ (Nat.clog p (Nat.ceil (max 1 C0) + 1) : ℤ) := by norm_cast
        have htp' : t_p ≠ 0 := htp
        dsimp only
        rw [Padic.norm_eq_zpow_neg_valuation htp', ← zpow_add₀ hp_pos.ne']
        calc ‖(cℚ : ℚ_[p]) - t_p‖
            ≤ (p : ℝ) ^ (-(KP p : ℤ)) * max 1 C0 := hdiff_le
          _ ≤ (p : ℝ) ^ (-(KP p : ℤ)) *
              (p : ℝ) ^ (Nat.clog p (Nat.ceil (max 1 C0) + 1) : ℤ) := by gcongr
          _ = (p : ℝ) ^ (-(KP p : ℤ) + (Nat.clog p (Nat.ceil (max 1 C0) + 1) : ℤ)) := by
                rw [zpow_add₀ hp_pos.ne']
          _ ≤ (p : ℝ) ^ (-Padic.valuation t_p + -3) := by
                refine zpow_le_zpow_right₀ hp1 ?_
                have hvle : Padic.valuation t_p ≤ ((Padic.valuation t_p).natAbs : ℤ) := Int.le_natAbs
                rw [hKP_def]
                omega
      have hc0 : cℚ ≠ 0 := by
        intro hc_zero
        push Not at h_all_iso
        by_cases hbR : HasDiagZeroReal b
        · obtain ⟨p, _, hpS, hbp⟩ := h_all_iso hbR
          obtain ⟨htp, _⟩ := ((hP_data p).choose_spec.choose_spec hpS).resolve_left hbp
          have hbd := hP_diff_bd p hpS hbp
          dsimp only at hbd
          rw [hc_zero, Rat.cast_zero, zero_sub, norm_neg] at hbd
          have hlt : (p : ℝ) ^ (-3 : ℤ) < 1 :=
            zpow_lt_one_of_neg₀ (by exact_mod_cast (hS_prime p hpS).one_lt) (by norm_num)
          have htp_pos : 0 < ‖((a₀ : ℚ) : ℚ_[p]) * (xP0 p) ^ 2 +
              ((a₁ : ℚ) : ℚ_[p]) * (xP1 p) ^ 2‖ := norm_pos_iff.mpr htp
          linarith [mul_lt_of_lt_one_right htp_pos hlt]
        · obtain ⟨htR, _⟩ := hR_case.resolve_left hbR
          have hbd := hR_diff_bd hbR
          rw [hc_zero, Rat.cast_zero, zero_sub, abs_neg] at hbd
          exact lt_irrefl _ hbd
      refine ⟨x₀, x₁, hc0, ?_, fun p _ => ?_⟩
      · by_cases hbR : HasDiagZeroReal b
        · obtain ⟨y, hy, hys⟩ := hbR
          exact ⟨Fin.cons 0 y, fun h0 => hy (funext fun j => by simpa using congrFun h0 j.succ),
            by simpa [Fin.sum_univ_succ] using hys⟩
        · obtain ⟨htR, y, hy, hsum⟩ := hR_case.resolve_left hbR
          obtain ⟨u, hu⟩ := real_same_sq_class_of_dist_lt htR (hR_diff_bd hbR)
          let yR : Fin (m + 4) → ℝ := Fin.cons ((u : ℝ)⁻¹) y
          refine ⟨yR, ?_, ?_⟩
          · intro h0; apply hy; ext j; have := congrFun h0 j.succ; simpa [yR] using this
          · dsimp only [HasDiagZeroK, yR]
            rw [Fin.sum_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ, Units.val_mk0]
            have huc : (cℚ : ℝ) * ((u : ℝ)⁻¹) ^ 2 = tR := by rw [hu]; dsimp [tR]; field_simp [u.ne_zero]
            rw [huc]
            exact hsum
      · by_cases hpS : p ∈ S_fin
        · by_cases hbp : HasDiagZeroPadic p b
          · obtain ⟨y, hy, hys⟩ := hbp
            exact ⟨Fin.cons 0 y, fun h0 => hy (funext fun j => by simpa using congrFun h0 j.succ),
              by simpa [Fin.sum_univ_succ] using hys⟩
          · obtain ⟨htp, y, hy, hsum⟩ := ((hP_data p).choose_spec.choose_spec hpS).resolve_left hbp
            obtain ⟨u, hu⟩ := padic_same_sq_class_of_norm_le htp (hP_diff_bd p hpS hbp)
            let yP : Fin (m + 4) → ℚ_[p] := Fin.cons ((u : ℚ_[p])⁻¹) y
            refine ⟨yP, ?_, ?_⟩
            · intro h0; apply hy; ext j; have := congrFun h0 j.succ; simpa [yP] using this
            · dsimp only [HasDiagZeroK, yP]
              rw [Fin.sum_univ_succ]
              simp only [Fin.cons_zero, Fin.cons_succ, Units.val_mk0]
              have huc : (cℚ : ℚ_[p]) * ((u : ℚ_[p])⁻¹) ^ 2 =
                  ((a₀ : ℚ) : ℚ_[p]) * (xP0 p) ^ 2 + ((a₁ : ℚ) : ℚ_[p]) * (xP1 p) ^ 2 := by
                rw [hu]; field_simp [u.ne_zero]; rfl
              rw [huc]
              exact hsum
        · obtain ⟨y, hy, hys⟩ := hb_good_odd p hpS
          exact ⟨Fin.cons 0 y, fun h0 => hy (funext fun j => by simpa using congrFun h0 j.succ),
            by simpa [Fin.sum_univ_succ] using hys⟩
  obtain ⟨x₀, x₁, hc0, hRc, hPc⟩ := hpick
  let c : ℚˣ := Units.mk0 ((a₀ : ℚ) * x₀ ^ 2 + (a₁ : ℚ) * x₁ ^ 2) hc0
  obtain ⟨w, hw, hsumw⟩ := IH (Fin.cons c b) ⟨hRc, hPc⟩
  let u : ℚ := w 0
  let y : Fin (m + 3) → ℚ := fun j => w j.succ
  have hu_sum : (c : ℚ) * u ^ 2 + ∑ j : Fin (m + 3), (b j : ℚ) * (y j) ^ 2 = 0 := by
    simpa [u, y, Fin.sum_univ_succ] using hsumw
  let v : Fin (m + 5) → ℚ := fun i =>
    if h0 : i.1 = 0 then u * x₀
    else if h1 : i.1 = 1 then u * x₁
    else y ⟨i.1 - 2, by omega⟩
  refine ⟨v, ?_, ?_⟩
  · intro hv0
    have hy0 : y = 0 := by
      ext j
      have hj := congrFun hv0 ⟨j.1 + 2, by omega⟩
      have hj' : y ⟨j.1 + 2 - 2, by omega⟩ = 0 := by
        simpa [v] using hj
      simpa [Fin.ext_iff] using hj'
    have hu0 : u = 0 := by
      have h0 := congrFun hv0 0
      have h1 := congrFun hv0 1
      simp only [v, Fin.val_zero, ↓reduceDIte, Pi.zero_apply] at h0
      simp only [v, Fin.val_one, one_ne_zero, ↓reduceDIte, Pi.zero_apply] at h1
      by_contra hu_ne
      have hx0 : x₀ = 0 := (mul_eq_zero.mp h0).resolve_left hu_ne
      have hx1 : x₁ = 0 := (mul_eq_zero.mp h1).resolve_left hu_ne
      apply hc0
      simp [hx0, hx1]
    apply hw
    ext i
    cases i using Fin.cases with
    | zero => exact hu0
    | succ j => exact congrFun hy0 j
  · change (∑ i : Fin (m + 5), (a i : ℚ) * (v i) ^ 2) = 0
    rw [diag_sum_split a (fun q => (q : ℚ)) v]
    have hv0 : v 0 = u * x₀ := by simp [v]
    have hv1 : v 1 = u * x₁ := by simp [v]
    have hvy : (∑ j : Fin (m + 3), (b j : ℚ) * (v ⟨j.1 + 2, by omega⟩) ^ 2) =
        ∑ j : Fin (m + 3), (b j : ℚ) * (y j) ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [v]
    rw [hv0, hv1]
    change (a₀ : ℚ) * (u * x₀) ^ 2 + (a₁ : ℚ) * (u * x₁) ^ 2 +
      ∑ j : Fin (m + 3), (b j : ℚ) * (v ⟨j.1 + 2, by omega⟩) ^ 2 = 0
    rw [hvy]
    have hc_eq : (c : ℚ) = (a₀ : ℚ) * x₀ ^ 2 + (a₁ : ℚ) * x₁ ^ 2 := rfl
    linear_combination hu_sum - u ^ 2 * hc_eq

/-- **Full `n`-variable Diagonal Hasse–Minkowski Theorem over `ℚ`**. -/
theorem hasse_minkowski_diag_Q : ∀ (n : ℕ) (a : Fin n → ℚˣ),
    HasDiagZeroQ a ↔ HasDiagZeroReal a ∧ ∀ p : ℕ, [Fact p.Prime] → HasDiagZeroPadic p a
  | 0, a => hasse_minkowski_diag_0 a
  | 1, a => hasse_minkowski_diag_1 a
  | 2, a => hasse_minkowski_diag_2 a
  | 3, a => hasse_minkowski_diag_3 a
  | 4, a => hasse_minkowski_diag_4 a
  | m + 5, a => by
    constructor
    · exact diag_local_of_global a
    · rintro ⟨hR, hP⟩
      exact hasse_minkowski_diag_step m
        (fun c hc => (hasse_minkowski_diag_Q (m + 4) c).mpr hc) a hR hP

end DimGeFive

/-! ## Section 5: General Nondegenerate `QuadraticForm` over `ℚ` -/

section GeneralQuadraticForms

private lemma associated_weightedSumSquares {R : Type*} [CommRing R] [Invertible (2 : R)]
    {m : ℕ} (c : Fin m → R) (v₁ v₂ : Fin m → R) :
    QuadraticMap.associated (QuadraticMap.weightedSumSquares R c) v₁ v₂ =
      ∑ i : Fin m, c i * (v₁ i * v₂ i) := by
  rw [QuadraticMap.associated_apply]
  have hsum : (QuadraticMap.weightedSumSquares R c) (v₁ + v₂) -
      (QuadraticMap.weightedSumSquares R c) v₁ -
      (QuadraticMap.weightedSumSquares R c) v₂ =
      2 * ∑ i : Fin m, c i * (v₁ i * v₂ i) := by
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, Pi.add_apply]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum]
  change ⅟(2 : R) * (2 * ∑ i : Fin m, c i * (v₁ i * v₂ i)) = _
  rw [← mul_assoc, invOf_mul_self, one_mul]

/-- Base change of `QuadraticMap.weightedSumSquares ℚ w` to an `ℚ`-algebra `A` agrees with
`weightedSumSquares A (algebraMap ℚ A ∘ w)` under `TensorProduct.piScalarRight`. -/
theorem baseChange_weightedSumSquares_apply {A : Type*} [CommRing A] [Algebra ℚ A]
    [Invertible (2 : A)] {m : ℕ} (w : Fin m → ℚ) (x : A ⊗[ℚ] (Fin m → ℚ)) :
    QuadraticForm.baseChange A (QuadraticMap.weightedSumSquares ℚ w) x =
      ∑ i : Fin m, (algebraMap ℚ A (w i)) * (TensorProduct.piScalarRight ℚ A A (Fin m) x i) ^ 2 := by
  let Q₀ : QuadraticForm ℚ (Fin m → ℚ) := QuadraticMap.weightedSumSquares ℚ w
  let Q₁ : QuadraticForm A (A ⊗[ℚ] (Fin m → ℚ)) := QuadraticForm.baseChange A Q₀
  let Φ : (A ⊗[ℚ] (Fin m → ℚ)) →ₗ[A] (Fin m → A) :=
    (TensorProduct.piScalarRight ℚ A A (Fin m)).toLinearMap
  let Q₂ : QuadraticForm A (A ⊗[ℚ] (Fin m → ℚ)) :=
    (QuadraticMap.weightedSumSquares A (fun i => algebraMap ℚ A (w i))).comp Φ
  have hassoc : QuadraticMap.associated Q₁ = QuadraticMap.associated Q₂ := by
    apply LinearMap.ext
    intro x'
    apply LinearMap.ext
    intro y'
    have hfun : ∀ x' y' : A ⊗[ℚ] (Fin m → ℚ),
        QuadraticMap.associated Q₁ x' y' = QuadraticMap.associated Q₂ x' y' := by
      intro x'
      refine TensorProduct.induction_on x' ?_ ?_ ?_
      · intro y'; simp
      · intro a₁ u₁ y'
        refine TensorProduct.induction_on y' ?_ ?_ ?_
        · simp
        · intro a₂ u₂
          have h1 : QuadraticMap.associated Q₁ (a₁ ⊗ₜ[ℚ] u₁) (a₂ ⊗ₜ[ℚ] u₂) =
              algebraMap ℚ A (QuadraticMap.associated Q₀ u₁ u₂) * (a₁ * a₂) := by
            dsimp [Q₁]
            rw [QuadraticForm.associated_baseChange, LinearMap.BilinForm.baseChange_tmul,
              Algebra.smul_def]
          have h2 : QuadraticMap.associated Q₂ (a₁ ⊗ₜ[ℚ] u₁) (a₂ ⊗ₜ[ℚ] u₂) =
              QuadraticMap.associated
                (QuadraticMap.weightedSumSquares A (fun i => algebraMap ℚ A (w i)))
                (Φ (a₁ ⊗ₜ[ℚ] u₁)) (Φ (a₂ ⊗ₜ[ℚ] u₂)) := by
            dsimp [Q₂]
            rw [QuadraticMap.associated_comp, LinearMap.compl₁₂_apply]
          have hΦ1 : Φ (a₁ ⊗ₜ[ℚ] u₁) = fun i => algebraMap ℚ A (u₁ i) * a₁ := by
            ext i
            change (TensorProduct.piScalarRight ℚ A A (Fin m)) (a₁ ⊗ₜ[ℚ] u₁) i = _
            rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
            dsimp
            rw [Algebra.smul_def]
          have hΦ2 : Φ (a₂ ⊗ₜ[ℚ] u₂) = fun i => algebraMap ℚ A (u₂ i) * a₂ := by
            ext i
            change (TensorProduct.piScalarRight ℚ A A (Fin m)) (a₂ ⊗ₜ[ℚ] u₂) i = _
            rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
            dsimp
            rw [Algebra.smul_def]
          rw [h1, h2, hΦ1, hΦ2]
          change algebraMap ℚ A (QuadraticMap.associated (QuadraticMap.weightedSumSquares ℚ w) u₁ u₂) * (a₁ * a₂) =
            QuadraticMap.associated (QuadraticMap.weightedSumSquares A (fun i => algebraMap ℚ A (w i)))
              (fun i => algebraMap ℚ A (u₁ i) * a₁) (fun i => algebraMap ℚ A (u₂ i) * a₂)
          rw [associated_weightedSumSquares w u₁ u₂,
            associated_weightedSumSquares (fun i => algebraMap ℚ A (w i)) _ _]
          simp only [map_sum, map_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        · intro y₁ y₂ hy₁ hy₂
          simp only [map_add, hy₁, hy₂]
      · intro x₁ x₂ hx₁ hx₂ y'
        simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
    exact hfun x' y'
  have hq : Q₁ x = Q₂ x := by
    rw [← QuadraticMap.associated_eq_self_apply A Q₁ x,
      ← QuadraticMap.associated_eq_self_apply A Q₂ x, hassoc]
  simpa [Q₁, Q₀, Q₂, Φ, QuadraticMap.weightedSumSquares_apply, smul_eq_mul, sq] using hq

private lemma diag_baseChange_equiv {V : Type*} [AddCommGroup V] [Module ℚ V]
    (A : Type) [Field A] [Algebra ℚ A] [Invertible (2 : A)]
    {m : ℕ} (Q : QuadraticForm ℚ V) (w : Fin m → ℚˣ)
    (e : Q.IsometryEquiv (QuadraticMap.weightedSumSquares ℚ w)) :
    (∃ v : A ⊗[ℚ] V, v ≠ 0 ∧ Q.baseChange A v = 0) ↔
      HasDiagZeroK (fun i : Fin m => algebraMap ℚ A (w i : ℚ)) := by
  let eQ : V ≃ₗ[ℚ] (Fin m → ℚ) := e.toLinearEquiv
  have hcomp : Q = (QuadraticMap.weightedSumSquares ℚ (fun i => (w i : ℚ))).comp eQ.toLinearMap := by
    ext v
    have hmap := e.map_app v
    change (QuadraticMap.weightedSumSquares ℚ w) (eQ v) = Q v at hmap
    rw [← hmap]
    simp [QuadraticMap.weightedSumSquares_apply, Units.smul_def, smul_eq_mul]
  let eA : (A ⊗[ℚ] V) ≃ₗ[A] (A ⊗[ℚ] (Fin m → ℚ)) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) eQ
  let Ψ : (A ⊗[ℚ] V) ≃ₗ[A] (Fin m → A) :=
    eA.trans (TensorProduct.piScalarRight ℚ A A (Fin m))
  have hQ_eval : ∀ v : A ⊗[ℚ] V, Q.baseChange A v =
      ∑ i : Fin m, algebraMap ℚ A (w i : ℚ) * (Ψ v i) ^ 2 := by
    intro v
    have hbase_eq : Q.baseChange A v =
        QuadraticForm.baseChange A (QuadraticMap.weightedSumSquares ℚ (fun i => (w i : ℚ))) (eA v) := by
      let Q₁ := Q.baseChange A
      let Q₂ := (QuadraticForm.baseChange A (QuadraticMap.weightedSumSquares ℚ (fun i => (w i : ℚ)))).comp
        eA.toLinearMap
      have hassoc : QuadraticMap.associated Q₁ = QuadraticMap.associated Q₂ := by
        apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
        have hfun : ∀ x y : A ⊗[ℚ] V,
            QuadraticMap.associated Q₁ x y = QuadraticMap.associated Q₂ x y := by
          intro x; refine TensorProduct.induction_on x ?_ ?_ ?_
          · intro y; simp
          · intro a₁ u₁ y; refine TensorProduct.induction_on y ?_ ?_ ?_
            · simp
            · intro a₂ u₂
              have hL : QuadraticMap.associated Q₁ (a₁ ⊗ₜ[ℚ] u₁) (a₂ ⊗ₜ[ℚ] u₂) =
                  (QuadraticMap.associated Q u₁ u₂) • (a₁ * a₂) := by
                dsimp [Q₁]
                rw [QuadraticForm.associated_baseChange, LinearMap.BilinForm.baseChange_tmul]
              have hR : QuadraticMap.associated Q₂ (a₁ ⊗ₜ[ℚ] u₁) (a₂ ⊗ₜ[ℚ] u₂) =
                  (QuadraticMap.associated
                    (QuadraticMap.weightedSumSquares ℚ (fun i => (w i : ℚ))) (eQ u₁) (eQ u₂)) •
                    (a₁ * a₂) := by
                dsimp [Q₂]
                rw [QuadraticMap.associated_comp, LinearMap.compl₁₂_apply]
                have heA1 : eA (a₁ ⊗ₜ[ℚ] u₁) = a₁ ⊗ₜ[ℚ] (eQ u₁) := rfl
                have heA2 : eA (a₂ ⊗ₜ[ℚ] u₂) = a₂ ⊗ₜ[ℚ] (eQ u₂) := rfl
                change QuadraticMap.associated
                  (QuadraticForm.baseChange A (QuadraticMap.weightedSumSquares ℚ fun i => (w i : ℚ)))
                  (eA (a₁ ⊗ₜ[ℚ] u₁)) (eA (a₂ ⊗ₜ[ℚ] u₂)) = _
                rw [heA1, heA2, QuadraticForm.associated_baseChange, LinearMap.BilinForm.baseChange_tmul]
              rw [hL, hR, hcomp, QuadraticMap.associated_comp, LinearMap.compl₁₂_apply]
              rfl
            · intro y₁ y₂ hy₁ hy₂; simp only [map_add, hy₁, hy₂]
          · intro x₁ x₂ hx₁ hx₂ y; simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
        exact hfun x y
      rw [← QuadraticMap.associated_eq_self_apply A Q₁ v, hassoc,
        QuadraticMap.associated_eq_self_apply A Q₂ v]
      rfl
    rw [hbase_eq, baseChange_weightedSumSquares_apply (fun i => (w i : ℚ)) (eA v)]
    rfl
  constructor
  · rintro ⟨v, hv, h0⟩
    refine ⟨Ψ v, ?_, ?_⟩
    · intro hΨ0; apply hv; exact Ψ.injective (by simpa using hΨ0)
    · rw [← hQ_eval v, h0]
  · rintro ⟨u, hu, h0⟩
    refine ⟨Ψ.symm u, ?_, ?_⟩
    · intro h0'; apply hu; simpa using congrArg Ψ h0'
    · rw [hQ_eval (Ψ.symm u)]
      simpa using h0

/-- **Full General Hasse–Minkowski Theorem over `ℚ` for any finite-dimensional space `V`**. -/
theorem hasse_minkowski_general_V {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (Q : QuadraticForm ℚ V) (hnd : Q.Nondegenerate) :
    (∃ v : V, v ≠ 0 ∧ Q v = 0) ↔
      (∃ v : ℝ ⊗[ℚ] V, v ≠ 0 ∧ Q.baseChange ℝ v = 0) ∧
      (∀ p : ℕ, [Fact p.Prime] → ∃ v : ℚ_[p] ⊗[ℚ] V, v ≠ 0 ∧ Q.baseChange ℚ_[p] v = 0) := by
  have hsep : LinearMap.SeparatingLeft (QuadraticMap.associated Q) := by
    rw [← QuadraticMap.nondegenerate_associated_iff (Q := Q)] at hnd
    exact hnd.1
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q hsep
  let m : ℕ := Module.finrank ℚ V
  have hQ_diag : (∃ v : V, v ≠ 0 ∧ Q v = 0) ↔ HasDiagZeroQ w := by
    constructor
    · rintro ⟨v, hv, h0⟩
      refine ⟨e v, ?_, ?_⟩
      · intro he0; apply hv; exact e.toLinearEquiv.injective (by simpa using he0)
      · have h1 := (e.map_app v).trans h0
        simp only [QuadraticMap.weightedSumSquares_apply, Units.smul_def, smul_eq_mul] at h1
        simpa only [sq] using h1
    · rintro ⟨u, hu, h0⟩
      refine ⟨e.symm u, ?_, ?_⟩
      · intro he0; apply hu; simpa using congrArg e he0
      · have hmap := e.map_app (e.symm u)
        rw [e.apply_symm_apply] at hmap
        rw [← hmap]
        simpa [QuadraticMap.weightedSumSquares_apply, Units.smul_def, smul_eq_mul, sq] using h0
  have hR_diag : (∃ v : ℝ ⊗[ℚ] V, v ≠ 0 ∧ Q.baseChange ℝ v = 0) ↔ HasDiagZeroReal w :=
    diag_baseChange_equiv ℝ Q w e
  have hP_diag : ∀ (p : ℕ) [Fact p.Prime],
      (∃ v : ℚ_[p] ⊗[ℚ] V, v ≠ 0 ∧ Q.baseChange ℚ_[p] v = 0) ↔ HasDiagZeroPadic p w :=
    fun p _ => diag_baseChange_equiv ℚ_[p] Q w e
  rw [hQ_diag, hR_diag]
  simp_rw [hP_diag]
  exact hasse_minkowski_diag_Q m w

/-- **FULL GENERAL `n`-VARIABLE HASSE–MINKOWSKI THEOREM OVER `ℚ` (Unconditional, `0` Assumptions!)**:
For EVERY dimension `n : ℕ` and EVERY nondegenerate `QuadraticForm ℚ (Fin n → ℚ)`,
`Q` has a nontrivial rational zero iff `Q.baseChange ℝ` has a nontrivial real zero and
`Q.baseChange ℚ_[p]` has a nontrivial `p`-adic zero for every prime `p`. -/
theorem hasse_minkowski_general_Q {n : ℕ} (Q : QuadraticForm ℚ (Fin n → ℚ))
    (hnd : Q.Nondegenerate) :
    (∃ v : Fin n → ℚ, v ≠ 0 ∧ Q v = 0) ↔
      (∃ v : ℝ ⊗[ℚ] (Fin n → ℚ), v ≠ 0 ∧ Q.baseChange ℝ v = 0) ∧
      (∀ p : ℕ, [Fact p.Prime] →
        ∃ v : ℚ_[p] ⊗[ℚ] (Fin n → ℚ), v ≠ 0 ∧ Q.baseChange ℚ_[p] v = 0) :=
  hasse_minkowski_general_V Q hnd

/-- Coordinate-space form (`Fin n → ℝ` and `Fin n → ℚ_[p]`) of `hasse_minkowski_general_Q`
via `TensorProduct.piScalarRight`. -/
def baseChangeFin (A : Type*) [Field A] [Algebra ℚ A] [Invertible (2 : A)] {n : ℕ}
    (Q : QuadraticForm ℚ (Fin n → ℚ)) : QuadraticForm A (Fin n → A) :=
  (Q.baseChange A).comp (TensorProduct.piScalarRight ℚ A A (Fin n)).symm.toLinearMap

private lemma baseChangeFin_equiv (A : Type) [Field A] [Algebra ℚ A] [Invertible (2 : A)] {n : ℕ}
    (Q : QuadraticForm ℚ (Fin n → ℚ)) :
    (∃ v : A ⊗[ℚ] (Fin n → ℚ), v ≠ 0 ∧ Q.baseChange A v = 0) ↔
      (∃ v : Fin n → A, v ≠ 0 ∧ baseChangeFin A Q v = 0) := by
  let Φ := TensorProduct.piScalarRight ℚ A A (Fin n)
  constructor
  · rintro ⟨v, hv, h0⟩
    refine ⟨Φ v, fun h => hv (Φ.injective (by simpa using h)), ?_⟩
    change (Q.baseChange A) (Φ.symm (Φ v)) = 0
    rw [Φ.symm_apply_apply]
    exact h0
  · rintro ⟨v, hv, h0⟩
    refine ⟨Φ.symm v, fun h => hv (by simpa using congrArg Φ h), ?_⟩
    exact h0

theorem hasse_minkowski_fin_Q {n : ℕ} (Q : QuadraticForm ℚ (Fin n → ℚ))
    (hnd : Q.Nondegenerate) :
    (∃ v : Fin n → ℚ, v ≠ 0 ∧ Q v = 0) ↔
      (∃ v : Fin n → ℝ, v ≠ 0 ∧ baseChangeFin ℝ Q v = 0) ∧
      (∀ p : ℕ, [Fact p.Prime] → ∃ v : Fin n → ℚ_[p], v ≠ 0 ∧ baseChangeFin ℚ_[p] Q v = 0) := by
  rw [hasse_minkowski_general_Q Q hnd, baseChangeFin_equiv ℝ Q]
  simp_rw [fun (p : ℕ) (_ : Fact p.Prime) => baseChangeFin_equiv ℚ_[p] Q]

end GeneralQuadraticForms

end

end RHDirect.HasseMinkowskiGeneral

#print axioms RHDirect.HasseMinkowskiGeneral.hasse_minkowski_diag_Q
#print axioms RHDirect.HasseMinkowskiGeneral.hasse_minkowski_general_V
#print axioms RHDirect.HasseMinkowskiGeneral.hasse_minkowski_general_Q
#print axioms RHDirect.HasseMinkowskiGeneral.hasse_minkowski_fin_Q

