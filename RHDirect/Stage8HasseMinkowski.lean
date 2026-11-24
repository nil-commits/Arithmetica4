import RHDirect.Stage7GlobalDuality
import Mathlib.Algebra.Quaternion
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Sqrt

/-!
# RHDirect.Stage8HasseMinkowski

Unconditional (`0` assumptions, `0` `sorry`, `0` custom `axiom`) formalization of:
1. **Concrete Local Solvability Characterization via Hilbert Symbols** at EVERY place
   `v ∈ {∞, 2} ∪ OddPrime` of `ℚ`:
   `hilbertSymAt v (-a * c) (-b * c) = 1 ↔ HasTernaryZeroAt v a b c`
   (over `ℝ`, `ℚ_[2]`, and every `ℚ_[p]` for odd prime `p`, via `Real.sqrt`, `hensels_lemma`,
   pigeonhole on `ZMod p`, and `Stage7GlobalDuality`).
2. **Unconditional Legendre's Three-Variable Theorem & Hasse–Minkowski Local-Global Principle
   for Ternary Quadratic Forms and Binary Norms over `ℚ`** (`0` assumptions):
   - `legendre_ternary_quadratic`: pairwise coprime squarefree nonzero integers `a, b, c` not all
     of the same sign represent `0` nontrivially iff `-b*c`, `-c*a`, `-a*b` are squares modulo
     `|a|`, `|b|`, `|c|` respectively (via Dirichlet pigeonhole on `Fin (⌊√|bc|⌋+1) × ...`).
   - `hasse_minkowski_ternary_Q`: `HasTernaryZeroQ a b c ↔ ∀ v, hilbertSymAt v (-a * c) (-b * c) = 1`.
   - `hasse_minkowski_ternary_local_global_Q`:
     `HasTernaryZeroQ a b c ↔ HasTernaryZeroReal a b c ∧ ∀ p [Fact p.Prime], HasTernaryZeroPadic p a b c`.
   - `hasse_minkowski_binary_norm_Q`:
     `(∃ x y : ℚ, x ^ 2 - a * y ^ 2 = b) ↔ ∀ v, hilbertSymAt v a b = 1`.
3. **Rational Quaternion Algebra Splitting & Legendre's Three-Squares Obstruction**:
   - Concrete rational quaternion algebra `RatQuatAlg a b := QuaternionAlgebra ℚ a 0 b`, reduced
     norm `nrd`, explicit `AlgEquiv` splitting `RatQuatAlg a b ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ`,
     and `quaternion_splits_iff_hilbert_trivial` + even finite ramification locus `ramifiedPlaces`.
   - `not_sum_three_squares_of_four_pow_mul_eight_add_seven`: no integer `4^k * (8*m + 7)` is a
     sum of three rational (or integer or natural) squares, directly from `hilbertSymTwo`.

Zero `sorry`, zero custom `axiom`s.
-/

open scoped BigOperators
open Finset RHDirect.Stage7GlobalDuality

namespace RHDirect.Stage8HasseMinkowski

noncomputable section

/-! ## Section 1: Ternary Quadratic Forms, Binary Norms, and Hilbert-Symbol Symmetries -/

section TernaryForms

/-- Nontrivial zero of the diagonal ternary quadratic form `a x² + b y² + c z² = 0` over a field `K`. -/
def HasTernaryZeroK {K : Type*} [Field K] (a b c : K) : Prop :=
  ∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0

/-- Nontrivial rational zero of `a x² + b y² + c z² = 0` for `a b c : ℚˣ`. -/
def HasTernaryZeroQ (a b c : ℚˣ) : Prop :=
  ∃ x y z : ℚ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ (a : ℚ) * x ^ 2 + (b : ℚ) * y ^ 2 + (c : ℚ) * z ^ 2 = 0

/-- Nontrivial real zero of `a x² + b y² + c z² = 0` for `a b c : ℚˣ`. -/
def HasTernaryZeroReal (a b c : ℚˣ) : Prop :=
  ∃ x y z : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
    ((a : ℚ) : ℝ) * x ^ 2 + ((b : ℚ) : ℝ) * y ^ 2 + ((c : ℚ) : ℝ) * z ^ 2 = 0

/-- Nontrivial `p`-adic zero of `a x² + b y² + c z² = 0` for `a b c : ℚˣ`. -/
def HasTernaryZeroPadic (p : ℕ) [Fact p.Prime] (a b c : ℚˣ) : Prop :=
  ∃ x y z : ℚ_[p], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
    ((a : ℚ) : ℚ_[p]) * x ^ 2 + ((b : ℚ) : ℚ_[p]) * y ^ 2 + ((c : ℚ) : ℚ_[p]) * z ^ 2 = 0

/-- Unified local isotropy predicate at any place `v : QPlace` of `ℚ`. -/
def HasTernaryZeroAt : QPlace → ℚˣ → ℚˣ → ℚˣ → Prop
  | QPlace.inf, a, b, c => HasTernaryZeroReal a b c
  | QPlace.two, a, b, c => @HasTernaryZeroPadic 2 ⟨Nat.prime_two⟩ a b c
  | QPlace.odd p, a, b, c => @HasTernaryZeroPadic p.1 ⟨p.2.1⟩ a b c

/-- Algebraic equivalence between `a x² + b y² + c z² = 0` and `(-a c) x² + (-b c) y² = w²`
over any field `K` (for `c ≠ 0`). -/
theorem hasTernaryZeroK_iff_norm_form {K : Type*} [Field K] {a b c : K} (hc : c ≠ 0) :
    HasTernaryZeroK a b c ↔
      ∃ x y w : K, (x ≠ 0 ∨ y ≠ 0 ∨ w ≠ 0) ∧ (-a * c) * x ^ 2 + (-b * c) * y ^ 2 = w ^ 2 := by
  constructor
  · rintro ⟨x, y, z, hne, heq⟩
    refine ⟨x, y, c * z, ?_, ?_⟩
    · rcases hne with hx | hy | hz
      · exact Or.inl hx
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr (mul_ne_zero hc hz))
    · linear_combination -c * heq
  · rintro ⟨x, y, w, hne, heq⟩
    refine ⟨x, y, w / c, ?_, ?_⟩
    · rcases hne with hx | hy | hw
      · exact Or.inl hx
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr (div_ne_zero hw hc))
    · field_simp [hc]
      linear_combination -heq

/-- Equivalence between `A x² + B y² = w²` (nontrivial) and binary norm `u² - A v² = B`
over any field `K` of characteristic `≠ 2` (for `A ≠ 0`). -/
theorem norm_form_iff_binary_norm {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {A B : K} (hA : A ≠ 0) :
    (∃ x y w : K, (x ≠ 0 ∨ y ≠ 0 ∨ w ≠ 0) ∧ A * x ^ 2 + B * y ^ 2 = w ^ 2) ↔
      ∃ u v : K, u ^ 2 - A * v ^ 2 = B := by
  constructor
  · rintro ⟨x, y, w, hne, heq⟩
    by_cases hy : y = 0
    · subst hy
      simp only [zero_pow two_ne_zero, mul_zero, add_zero] at heq
      have hx : x ≠ 0 := by
        intro hx0
        subst hx0
        simp only [zero_pow two_ne_zero, mul_zero] at heq
        have hw0 : w = 0 := eq_zero_of_pow_eq_zero heq.symm
        rcases hne with h | h | h
        · exact h rfl
        · exact h rfl
        · exact h hw0
      have hw : w ≠ 0 := by
        intro hw0
        subst hw0
        simp only [zero_pow two_ne_zero] at heq
        rcases mul_eq_zero.mp heq with h | h
        · exact hA h
        · exact hx (eq_zero_of_pow_eq_zero h)
      let t : K := w / x
      have ht : t ≠ 0 := div_ne_zero hw hx
      have htsq : t ^ 2 = A := by
        dsimp only [t]
        rw [div_pow, ← heq, mul_div_cancel_right₀ A (pow_ne_zero 2 hx)]
      refine ⟨(B + 1) / 2, (B - 1) / (2 * t), ?_⟩
      rw [← htsq]
      field_simp [h2, ht]
      ring
    · refine ⟨w / y, x / y, ?_⟩
      field_simp [hy]
      linear_combination -heq
  · rintro ⟨u, v, huv⟩
    exact ⟨v, 1, u, Or.inr (Or.inl one_ne_zero), by linear_combination -huv⟩

/-- Combined equivalence: `HasTernaryZeroK a b c ↔ ∃ u v : K, u² - (-a c) v² = -b c`
over any field `K` with `2 ≠ 0` and `a, c ≠ 0`. -/
theorem hasTernaryZeroK_iff_binary_norm {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {a b c : K} (ha : a ≠ 0) (hc : c ≠ 0) :
    HasTernaryZeroK a b c ↔ ∃ u v : K, u ^ 2 - (-a * c) * v ^ 2 = -b * c := by
  rw [hasTernaryZeroK_iff_norm_form hc,
    norm_form_iff_binary_norm h2 (mul_ne_zero (neg_ne_zero.mpr ha) hc)]

theorem hasTernaryZeroK_scale_squares {K : Type*} [Field K]
    {a b c : K} {r s t : K} (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) :
    HasTernaryZeroK (a * r ^ 2) (b * s ^ 2) (c * t ^ 2) ↔ HasTernaryZeroK a b c := by
  constructor
  · rintro ⟨x, y, z, hne, heq⟩
    refine ⟨r * x, s * y, t * z, ?_, ?_⟩
    · rcases hne with hx | hy | hz
      · exact Or.inl (mul_ne_zero hr hx)
      · exact Or.inr (Or.inl (mul_ne_zero hs hy))
      · exact Or.inr (Or.inr (mul_ne_zero ht hz))
    · linear_combination heq
  · rintro ⟨x, y, z, hne, heq⟩
    refine ⟨x / r, y / s, z / t, ?_, ?_⟩
    · rcases hne with hx | hy | hz
      · exact Or.inl (div_ne_zero hx hr)
      · exact Or.inr (Or.inl (div_ne_zero hy hs))
      · exact Or.inr (Or.inr (div_ne_zero hz ht))
    · field_simp [hr, hs, ht]
      linear_combination heq

theorem hasTernaryZeroK_scale {K : Type*} [Field K] {a b c t : K} (ht : t ≠ 0) :
    HasTernaryZeroK (t * a) (t * b) (t * c) ↔ HasTernaryZeroK a b c := by
  constructor
  · rintro ⟨x, y, z, hne, heq⟩
    refine ⟨x, y, z, hne, ?_⟩
    have hfac : t * (a * x ^ 2 + b * y ^ 2 + c * z ^ 2) = 0 := by linear_combination heq
    exact (mul_eq_zero.mp hfac).resolve_left ht
  · rintro ⟨x, y, z, hne, heq⟩
    exact ⟨x, y, z, hne, by linear_combination t * heq⟩

theorem hilbertSymAt_symm (v : QPlace) (a b : ℚˣ) :
    hilbertSymAt v a b = hilbertSymAt v b a := by
  cases v with
  | inf => exact hilbertSymInf_symm a b
  | two => exact hilbertSymTwo_symm a b
  | odd p => exact hilbertSymOdd_symm p.1 p.2.1 p.2.2 a b

theorem hilbertSymAt_inv_left (v : QPlace) (a b : ℚˣ) :
    hilbertSymAt v a⁻¹ b = hilbertSymAt v a b := by
  cases v with
  | inf => exact hilbertSymInf_inv_left a b
  | two => exact hilbertSymTwo_inv_left a b
  | odd p => exact hilbertSymOdd_inv_left p.1 p.2.1 p.2.2 a b

theorem hilbertSymAt_inv_right (v : QPlace) (a b : ℚˣ) :
    hilbertSymAt v a b⁻¹ = hilbertSymAt v a b := by
  rw [hilbertSymAt_symm, hilbertSymAt_inv_left, hilbertSymAt_symm]

/-- Full `S₃`-symmetry of the ternary Hilbert invariant `(-a*c, -b*c)_v` in `(a, b, c)`. -/
theorem hilbertSymAt_ternary_swap_ab (v : QPlace) (a b c : ℚˣ) :
    hilbertSymAt v (-b * c) (-a * c) = hilbertSymAt v (-a * c) (-b * c) :=
  hilbertSymAt_symm v (-b * c) (-a * c)

theorem hilbertSymAt_ternary_swap_bc (v : QPlace) (a b c : ℚˣ) :
    hilbertSymAt v (-a * b) (-c * b) = hilbertSymAt v (-a * c) (-b * c) := by
  let u : ℚˣ := -a * c
  let w : ℚˣ := -b * c
  have h1 : -a * b = (-u * w) * (c⁻¹) ^ 2 := by
    apply Units.ext; simp [u, w]; field_simp [c.ne_zero]
  have h2 : -c * b = w := by apply Units.ext; simp [w]; ring
  rw [h1, h2, hilbertSymAt_mul_left, hilbertSymAt_sq_left, mul_one,
    hilbertSymAt_mul_left, hilbertSymAt_symm v (-u) w,
    show (-u) = -(u) from rfl]
  have h3 : hilbertSymAt v w (-u) * hilbertSymAt v w w = hilbertSymAt v u w := by
    have hneg : -u = (-1 : ℚˣ) * u := by simp
    have hww : hilbertSymAt v w w = hilbertSymAt v w (-1) := by
      have hsn := hilbertSymAt_self_neg v w
      rw [show -w = (-1 : ℚˣ) * w by simp, hilbertSymAt_mul_right] at hsn
      calc hilbertSymAt v w w
          = hilbertSymAt v w (-1) * (hilbertSymAt v w (-1) * hilbertSymAt v w w) := by
              rw [← mul_assoc, intUnits_mul_self, one_mul]
        _ = hilbertSymAt v w (-1) := by rw [hsn, mul_one]
    rw [hneg, hilbertSymAt_mul_right, hww, mul_comm (hilbertSymAt v w (-1)) (hilbertSymAt v w u),
      mul_assoc, intUnits_mul_self, mul_one, hilbertSymAt_symm]
  exact h3

theorem hilbertSymAt_ternary_swap_ac (v : QPlace) (a b c : ℚˣ) :
    hilbertSymAt v (-c * a) (-b * a) = hilbertSymAt v (-a * c) (-b * c) := by
  calc hilbertSymAt v (-c * a) (-b * a)
      = hilbertSymAt v (-b * a) (-c * a) := hilbertSymAt_symm v _ _
    _ = hilbertSymAt v (-b * c) (-a * c) := hilbertSymAt_ternary_swap_bc v b a c
    _ = hilbertSymAt v (-a * c) (-b * c) := hilbertSymAt_symm v _ _

theorem hilbertSymAt_ternary_scale (v : QPlace) (a b c t : ℚˣ) :
    hilbertSymAt v (-(t * a) * (t * c)) (-(t * b) * (t * c)) = hilbertSymAt v (-a * c) (-b * c) := by
  have h1 : -(t * a) * (t * c) = (-a * c) * t ^ 2 := by apply Units.ext; simp; ring
  have h2 : -(t * b) * (t * c) = (-b * c) * t ^ 2 := by apply Units.ext; simp; ring
  rw [h1, h2, hilbertSymAt_mul_left, hilbertSymAt_sq_left, mul_one,
    hilbertSymAt_mul_right, hilbertSymAt_sq_right, mul_one]

theorem hilbertSymAt_ternary_scale_squares (v : QPlace) (a b c r s t : ℚˣ) :
    hilbertSymAt v (-(a * r ^ 2) * (c * t ^ 2)) (-(b * s ^ 2) * (c * t ^ 2)) =
      hilbertSymAt v (-a * c) (-b * c) := by
  have h1 : -(a * r ^ 2) * (c * t ^ 2) = (-a * c) * (r * t) ^ 2 := by apply Units.ext; simp; ring
  have h2 : -(b * s ^ 2) * (c * t ^ 2) = (-b * c) * (s * t) ^ 2 := by apply Units.ext; simp; ring
  rw [h1, h2, hilbertSymAt_mul_left, hilbertSymAt_sq_left, mul_one,
    hilbertSymAt_mul_right, hilbertSymAt_sq_right, mul_one]

end TernaryForms

/-! ## Section 2: Concrete Local Solvability Characterization via Hilbert Symbols (All Places) -/

section LocalSolvability

/-! ### 2A. Archimedean Place `v = ∞` (`ℝ`) -/

/-- **Hilbert Symbol Characterization of Real Isotropy (`v = ∞`)**:
`(-a*c, -b*c)_∞ = 1` iff `a x² + b y² + c z² = 0` has a nontrivial real solution
(equivalently, `a, b, c` do not all have the same sign). -/
theorem hilbertSymInf_ternary_iff (a b c : ℚˣ) :
    hilbertSymInf (-a * c) (-b * c) = 1 ↔ HasTernaryZeroReal a b c := by
  have ha : ((a : ℚ) : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr a.ne_zero
  have hb : ((b : ℚ) : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr b.ne_zero
  have hc : ((c : ℚ) : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr c.ne_zero
  have hinf : hilbertSymInf (-a * c) (-b * c) = 1 ↔
      ¬ (0 < ((a : ℚ) : ℝ) * ((c : ℚ) : ℝ) ∧ 0 < ((b : ℚ) : ℝ) * ((c : ℚ) : ℝ)) := by
    unfold hilbertSymInf
    simp only [Units.val_mul, Units.val_neg]
    have hq1 : -((a : ℚ)) * (c : ℚ) < 0 ↔ 0 < ((a : ℚ) : ℝ) * ((c : ℚ) : ℝ) := by
      rw [neg_mul, neg_lt_zero]; exact_mod_cast Iff.rfl
    have hq2 : -((b : ℚ)) * (c : ℚ) < 0 ↔ 0 < ((b : ℚ) : ℝ) * ((c : ℚ) : ℝ) := by
      rw [neg_mul, neg_lt_zero]; exact_mod_cast Iff.rfl
    split_ifs with h
    · constructor
      · intro h1; exact absurd h1 (by decide)
      · intro hnot; exact absurd ⟨hq1.mp h.1, hq2.mp h.2⟩ hnot
    · constructor
      · intro _ hpos; exact h ⟨hq1.mpr hpos.1, hq2.mpr hpos.2⟩
      · intro _; rfl
  rw [hinf]
  constructor
  · intro hnot
    have hor : ((a : ℚ) : ℝ) * ((c : ℚ) : ℝ) < 0 ∨ ((b : ℚ) : ℝ) * ((c : ℚ) : ℝ) < 0 := by
      by_contra hnone
      push Not at hnone
      apply hnot
      exact ⟨lt_of_le_of_ne hnone.1 (mul_ne_zero ha hc).symm,
        lt_of_le_of_ne hnone.2 (mul_ne_zero hb hc).symm⟩
    rcases hor with hac | hbc
    · have hpos : 0 < -((c : ℚ) : ℝ) / ((a : ℚ) : ℝ) := by
        have h : -((c : ℚ) : ℝ) / ((a : ℚ) : ℝ) = -(((a : ℚ) : ℝ) * ((c : ℚ) : ℝ)) / ((a : ℚ) : ℝ) ^ 2 := by
          field_simp [ha]
        rw [h]
        exact div_pos (by linarith) (sq_pos_of_ne_zero ha)
      refine ⟨Real.sqrt (-((c : ℚ) : ℝ) / ((a : ℚ) : ℝ)), 0, 1, Or.inr (Or.inr one_ne_zero), ?_⟩
      rw [Real.sq_sqrt hpos.le]
      field_simp [ha]
      ring
    · have hpos : 0 < -((c : ℚ) : ℝ) / ((b : ℚ) : ℝ) := by
        have h : -((c : ℚ) : ℝ) / ((b : ℚ) : ℝ) = -(((b : ℚ) : ℝ) * ((c : ℚ) : ℝ)) / ((b : ℚ) : ℝ) ^ 2 := by
          field_simp [hb]
        rw [h]
        exact div_pos (by linarith) (sq_pos_of_ne_zero hb)
      refine ⟨0, Real.sqrt (-((c : ℚ) : ℝ) / ((b : ℚ) : ℝ)), 1, Or.inr (Or.inr one_ne_zero), ?_⟩
      rw [Real.sq_sqrt hpos.le]
      field_simp [hb]
      ring
  · rintro ⟨x, y, z, hne, heq⟩ ⟨hac, hbc⟩
    have hmul : (((a : ℚ) : ℝ) * ((c : ℚ) : ℝ)) * x ^ 2 +
        (((b : ℚ) : ℝ) * ((c : ℚ) : ℝ)) * y ^ 2 + (((c : ℚ) : ℝ) * z) ^ 2 = 0 := by
      linear_combination ((c : ℚ) : ℝ) * heq
    have hx2 : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (((c : ℚ) : ℝ) * z)]
    have hy2 : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (((c : ℚ) : ℝ) * z)]
    have hcz2 : (((c : ℚ) : ℝ) * z) ^ 2 = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (((c : ℚ) : ℝ) * z)]
    have hx0 : x = 0 := eq_zero_of_pow_eq_zero hx2
    have hy0 : y = 0 := eq_zero_of_pow_eq_zero hy2
    have hcz0 : ((c : ℚ) : ℝ) * z = 0 := eq_zero_of_pow_eq_zero hcz2
    have hz0 : z = 0 := (mul_eq_zero.mp hcz0).resolve_left hc
    rcases hne with h | h | h
    · exact h hx0
    · exact h hy0
    · exact h hz0

/-! ### 2B. `p`-adic Hilbert Symbols on `ℚ_[p]ˣ` & Steinberg Relation -/

/-- Embed `ℚˣ` into `ℚ_[p]ˣ`. -/
def ratToPadicUnit (p : ℕ) [Fact p.Prime] (a : ℚˣ) : ℚ_[p]ˣ :=
  Units.map (Rat.castHom ℚ_[p]).toMonoidHom a

@[simp]
theorem coe_ratToPadicUnit (p : ℕ) [Fact p.Prime] (a : ℚˣ) :
    ((ratToPadicUnit p a : ℚ_[p]ˣ) : ℚ_[p]) = ((a : ℚ) : ℚ_[p]) := rfl

theorem ratToPadicUnit_mul (p : ℕ) [Fact p.Prime] (a b : ℚˣ) :
    ratToPadicUnit p (a * b) = ratToPadicUnit p a * ratToPadicUnit p b :=
  map_mul _ a b

theorem ratToPadicUnit_neg (p : ℕ) [Fact p.Prime] (a : ℚˣ) :
    ratToPadicUnit p (-a) = -(ratToPadicUnit p a) := by
  apply Units.ext; simp

/-- `Padic.valuation` of `ratToPadicUnit p a` equals `padicValRat p a`. -/
theorem padic_valuation_ratToPadicUnit (p : ℕ) [Fact p.Prime] (a : ℚˣ) :
    Padic.valuation (ratToPadicUnit p a : ℚ_[p]) = padicValRat p (a : ℚ) :=
  Padic.valuation_ratCast (a : ℚ)

/-- The `p`-adic unit part of `ratToPadicUnit p a` equals `(pUnit p hp a : ℚ)` in `ℚ_[p]`. -/
theorem coe_padicUnitPart_ratToPadicUnit (p : ℕ) [Fact p.Prime] (a : ℚˣ) :
    ((padicUnitPart (ratToPadicUnit p a) : ℤ_[p]) : ℚ_[p]) =
      ((pUnit p Fact.out a : ℚ) : ℚ_[p]) := by
  rw [coe_padicUnitPart, coe_ratToPadicUnit, Padic.valuation_ratCast]
  unfold pUnit
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, coe_primeUnit]
  push_cast
  rfl

/-- Reduction of a rational `p`-adic unit via `PadicInt.toZMod` matches `redModP`. -/
theorem toZMod_padicUnitPart_rat (p : ℕ) [Fact p.Prime] (a : ℚˣ) :
    PadicInt.toZMod (padicUnitPart (ratToPadicUnit p a) : ℤ_[p]) =
      redModP p (pUnit p Fact.out a : ℚ) := by
  have hp : p.Prime := Fact.out
  let q : ℚ := (pUnit p hp a : ℚ)
  have hq0 : q ≠ 0 := (pUnit p hp a).ne_zero
  have hqval : padicValRat p q = 0 := padicValRat_pUnit p hp a
  have hden : ¬ p ∣ q.den := (not_dvd_num_and_den_of_padicValRat_eq_zero hp hq0 hqval).2
  have hd_ne : (q.den : ZMod p) ≠ 0 := zmod_den_ne_zero_of_not_dvd hden
  let uZ : ℤ_[p] := (padicUnitPart (ratToPadicUnit p a) : ℤ_[p])
  have huZ_coe : (uZ : ℚ_[p]) = (q : ℚ_[p]) := coe_padicUnitPart_ratToPadicUnit p a
  have hEqZ : (q.den : ℤ_[p]) * uZ = (q.num : ℤ_[p]) := by
    apply Subtype.ext
    change ((q.den : ℕ) : ℚ_[p]) * (uZ : ℚ_[p]) = (q.num : ℚ_[p])
    rw [huZ_coe]
    have hq_rat : (q.den : ℚ) * q = (q.num : ℚ) := by
      have hne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
      calc (q.den : ℚ) * q = (q.den : ℚ) * ((q.num : ℚ) / (q.den : ℚ)) := by rw [Rat.num_div_den]
        _ = (q.num : ℚ) := mul_div_cancel₀ _ hne
    exact_mod_cast hq_rat
  have hmod := congrArg (PadicInt.toZMod (p := p)) hEqZ
  simp only [map_mul, map_natCast, map_intCast] at hmod
  unfold redModP
  calc PadicInt.toZMod uZ
      = ((q.den : ZMod p) * PadicInt.toZMod uZ) * (q.den : ZMod p)⁻¹ := by
          rw [mul_comm (q.den : ZMod p), mul_assoc, mul_inv_cancel₀ hd_ne, mul_one]
    _ = (q.num : ZMod p) * (q.den : ZMod p)⁻¹ := by rw [hmod]

/-- Reduction mod `8` of a rational `2`-adic unit via `PadicInt.toZModPow 3` matches `redMod8`. -/
theorem toZModPow3_padicUnitPart_rat (a : ℚˣ) :
    PadicInt.toZModPow 3 (padicUnitPart (ratToPadicUnit 2 a) : ℤ_[2]) =
      redMod8 (pUnit 2 Nat.prime_two a : ℚ) := by
  let q : ℚ := (pUnit 2 Nat.prime_two a : ℚ)
  have hq0 : q ≠ 0 := (pUnit 2 Nat.prime_two a).ne_zero
  have hqval : padicValRat 2 q = 0 := padicValRat_pUnit 2 Nat.prime_two a
  have hden : ¬ 2 ∣ q.den := (not_dvd_num_and_den_of_padicValRat_eq_zero Nat.prime_two hq0 hqval).2
  have hsq : (q.den : ZMod 8) * (q.den : ZMod 8) = 1 :=
    zmod8_odd_sq_eq_one _ (nat_cast_zmod8_odd hden)
  let uZ : ℤ_[2] := (padicUnitPart (ratToPadicUnit 2 a) : ℤ_[2])
  have huZ_coe : (uZ : ℚ_[2]) = (q : ℚ_[2]) := coe_padicUnitPart_ratToPadicUnit 2 a
  have hEqZ : (q.den : ℤ_[2]) * uZ = (q.num : ℤ_[2]) := by
    apply Subtype.ext
    change ((q.den : ℕ) : ℚ_[2]) * (uZ : ℚ_[2]) = (q.num : ℚ_[2])
    rw [huZ_coe]
    have hq_rat : (q.den : ℚ) * q = (q.num : ℚ) := by
      have hne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
      calc (q.den : ℚ) * q = (q.den : ℚ) * ((q.num : ℚ) / (q.den : ℚ)) := by rw [Rat.num_div_den]
        _ = (q.num : ℚ) := mul_div_cancel₀ _ hne
    exact_mod_cast hq_rat
  have hmod : (q.den : ZMod 8) * (PadicInt.toZModPow 3 uZ : ZMod 8) = (q.num : ZMod 8) := by
    have h := congrArg (PadicInt.toZModPow 3) hEqZ
    simpa only [map_mul, map_natCast, map_intCast] using h
  unfold redMod8
  calc (PadicInt.toZModPow 3 uZ : ZMod 8)
      = ((q.den : ZMod 8) * (q.den : ZMod 8)) * (PadicInt.toZModPow 3 uZ : ZMod 8) := by
          rw [hsq, one_mul]
    _ = ((q.den : ZMod 8) * (PadicInt.toZModPow 3 uZ : ZMod 8)) * (q.den : ZMod 8) := by ring
    _ = (q.num : ZMod 8) * (q.den : ZMod 8) := by rw [hmod]

/-- Local Hilbert symbol on `ℚ_[p]ˣ` for an odd prime `p`. -/
def hilbertSymPadicOdd (p : ℕ) [Fact p.Prime] (_hp2 : p ≠ 2) (x y : ℚ_[p]ˣ) : ℤˣ :=
  let cx := Multiplicative.toAdd (padicOddCoordHom p x)
  let cy := Multiplicative.toAdd (padicOddCoordHom p y)
  negOnePowZMod2 (((p / 2 : ℕ) : ZMod 2) * cx.1 * cy.1 + cx.2 * cy.1 + cx.1 * cy.2)

/-- Local Hilbert symbol on `ℚ_[2]ˣ`. -/
def hilbertSymPadicTwo (x y : ℚ_[2]ˣ) : ℤˣ :=
  let cx := Multiplicative.toAdd (padicTwoCoordHom x)
  let cy := Multiplicative.toAdd (padicTwoCoordHom y)
  negOnePowZMod2 (cx.2.1 * cy.2.1 + cx.1 * cy.2.2 + cy.1 * cx.2.2)

theorem padicOddCoordHom_ratToPadicUnit (p : ℕ) [Fact p.Prime] (a : ℚˣ) :
    Multiplicative.toAdd (padicOddCoordHom p (ratToPadicUnit p a)) = oddCoords p Fact.out a := by
  have hp : p.Prime := Fact.out
  ext
  · change (Padic.valuation (ratToPadicUnit p a : ℚ_[p]) : ZMod 2) = (padicValRat p (a : ℚ) : ZMod 2)
    rw [padic_valuation_ratToPadicUnit]
  · change unitsToZMod2 (intToSignUnit (quadraticChar (ZMod p)
        (PadicInt.toZMod (padicUnitPart (ratToPadicUnit p a) : ℤ_[p])))) =
      unitsToZMod2 (pUnitLegUnit p hp a)
    rw [toZMod_padicUnitPart_rat p a]
    unfold pUnitLegUnit
    rw [ratUnitLegendre_eq_quadraticChar hp (pUnit p hp a).ne_zero (padicValRat_pUnit p hp a)]

theorem padicTwoCoordHom_ratToPadicUnit (a : ℚˣ) :
    Multiplicative.toAdd (padicTwoCoordHom (ratToPadicUnit 2 a)) = twoCoords a := by
  unfold padicTwoCoordHom twoCoords
  dsimp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  rw [padic_valuation_ratToPadicUnit 2 a, toZModPow3_padicUnitPart_rat a]

theorem hilbertSymPadicOdd_ratCast (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a b : ℚˣ) :
    hilbertSymPadicOdd p hp2 (ratToPadicUnit p a) (ratToPadicUnit p b) =
      hilbertSymOdd p Fact.out hp2 a b := by
  unfold hilbertSymPadicOdd
  rw [padicOddCoordHom_ratToPadicUnit p a, padicOddCoordHom_ratToPadicUnit p b,
    ← hilbertSymOdd_eq_negOnePow]

theorem hilbertSymPadicTwo_ratCast (a b : ℚˣ) :
    hilbertSymPadicTwo (ratToPadicUnit 2 a) (ratToPadicUnit 2 b) = hilbertSymTwo a b := by
  unfold hilbertSymPadicTwo hilbertSymTwo
  rw [padicTwoCoordHom_ratToPadicUnit a, padicTwoCoordHom_ratToPadicUnit b]

/-! #### Algebraic Laws & Steinberg Relation for `hilbertSymPadicOdd` -/

theorem hilbertSymPadicOdd_symm (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (x y : ℚ_[p]ˣ) :
    hilbertSymPadicOdd p hp2 x y = hilbertSymPadicOdd p hp2 y x := by
  unfold hilbertSymPadicOdd; dsimp only; congr 1; ring

theorem hilbertSymPadicOdd_mul_left (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (x₁ x₂ y : ℚ_[p]ˣ) :
    hilbertSymPadicOdd p hp2 (x₁ * x₂) y =
      hilbertSymPadicOdd p hp2 x₁ y * hilbertSymPadicOdd p hp2 x₂ y := by
  unfold hilbertSymPadicOdd
  dsimp only
  rw [← negOnePowZMod2_add, map_mul, toAdd_mul]
  congr 1; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem hilbertSymPadicOdd_mul_right (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (x y₁ y₂ : ℚ_[p]ˣ) :
    hilbertSymPadicOdd p hp2 x (y₁ * y₂) =
      hilbertSymPadicOdd p hp2 x y₁ * hilbertSymPadicOdd p hp2 x y₂ := by
  rw [hilbertSymPadicOdd_symm, hilbertSymPadicOdd_mul_left,
    hilbertSymPadicOdd_symm p hp2 y₁ x, hilbertSymPadicOdd_symm p hp2 y₂ x]

theorem hilbertSymPadicOdd_sq_left (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (x y : ℚ_[p]ˣ) :
    hilbertSymPadicOdd p hp2 (x ^ 2) y = 1 := by
  rw [sq, hilbertSymPadicOdd_mul_left, intUnits_mul_self]

theorem hilbertSymPadicOdd_sq_right (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (x y : ℚ_[p]ˣ) :
    hilbertSymPadicOdd p hp2 x (y ^ 2) = 1 := by
  rw [sq, hilbertSymPadicOdd_mul_right, intUnits_mul_self]

theorem hilbertSymPadicOdd_inv_left (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (x y : ℚ_[p]ˣ) :
    hilbertSymPadicOdd p hp2 x⁻¹ y = hilbertSymPadicOdd p hp2 x y := by
  have h : hilbertSymPadicOdd p hp2 (x * x⁻¹) y = 1 := by
    rw [mul_inv_cancel]
    unfold hilbertSymPadicOdd
    simp
  rw [hilbertSymPadicOdd_mul_left] at h
  calc hilbertSymPadicOdd p hp2 x⁻¹ y
      = hilbertSymPadicOdd p hp2 x y *
          (hilbertSymPadicOdd p hp2 x y * hilbertSymPadicOdd p hp2 x⁻¹ y) := by
            rw [← mul_assoc, intUnits_mul_self, one_mul]
    _ = hilbertSymPadicOdd p hp2 x y := by rw [h, mul_one]

theorem hilbertSymPadicOdd_self_neg (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (x : ℚ_[p]ˣ) :
    hilbertSymPadicOdd p hp2 x (-x) = 1 := by
  have hp : p.Prime := Fact.out
  have hneg1 : Multiplicative.toAdd (padicOddCoordHom p (-1 : ℚ_[p]ˣ)) =
      (0, ((p / 2 : ℕ) : ZMod 2)) := by
    have h := padicOddCoordHom_ratToPadicUnit p (-1)
    rw [ratToPadicUnit_neg, show ratToPadicUnit p 1 = 1 from map_one _] at h
    rw [h]
    ext
    · simp [oddCoords]
    · change unitsToZMod2 (pUnitLegUnit p hp (-1)) = _
      rw [pUnitLegUnit_neg_one p hp hp2, ← negOnePowZMod2_natCast, unitsToZMod2_negOnePowZMod2]
  have hnegx : -x = (-1 : ℚ_[p]ˣ) * x := by simp
  unfold hilbertSymPadicOdd
  rw [hnegx, map_mul, toAdd_mul, hneg1]
  simp only [Prod.fst_add, Prod.snd_add, zero_add]
  have hz : ∀ a b e : ZMod 2, e * a * a + b * a + a * (e + b) = 0 := by decide
  rw [hz]; rfl

/-- Helper: if `0 < Padic.valuation x` and `y = 1 - x` in `ℚ_[p]ˣ`, then `padicOddCoordHom p y = 1`. -/
private theorem padicOddCoordHom_one_sub_of_pos_val {p : ℕ} [Fact p.Prime] {x y : ℚ_[p]ˣ}
    (hx : 0 < Padic.valuation (x : ℚ_[p])) (hxy : (y : ℚ_[p]) = 1 - (x : ℚ_[p])) :
    padicOddCoordHom p y = 1 := by
  have hp : p.Prime := Fact.out
  have hp_gt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hx_norm_lt : ‖(x : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation x.ne_zero]
    exact zpow_lt_one_of_neg₀ hp_gt (by omega)
  let xZ : ℤ_[p] := ⟨(x : ℚ_[p]), hx_norm_lt.le⟩
  have hxZ_mod : PadicInt.toZMod xZ = 0 := by
    change xZ ∈ RingHom.ker (PadicInt.toZMod (p := p))
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit xZ
    rw [PadicInt.not_isUnit_iff]
    exact hx_norm_lt
  have h1mx_unit : IsUnit (1 - xZ) := by
    by_contra hnu
    have hker : 1 - xZ ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]; exact hnu
    change PadicInt.toZMod (1 - xZ) = 0 at hker
    rw [map_sub, map_one, hxZ_mod, sub_zero] at hker
    exact one_ne_zero hker
  have hy_norm : ‖(y : ℚ_[p])‖ = 1 := by
    have h := PadicInt.isUnit_iff.mp h1mx_unit
    change ‖(1 : ℚ_[p]) - (x : ℚ_[p])‖ = 1 at h
    rwa [← hxy] at h
  have hy_val : Padic.valuation (y : ℚ_[p]) = 0 := by
    have h1 := Padic.norm_eq_zpow_neg_valuation y.ne_zero
    rw [hy_norm] at h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (1 : ℝ) < (p : ℝ) ^ (-Padic.valuation (y : ℚ_[p])) := one_lt_zpow₀ hp_gt (by omega)
      linarith
    · have : (p : ℝ) ^ (-Padic.valuation (y : ℚ_[p])) < 1 := zpow_lt_one_of_neg₀ hp_gt (by omega)
      linarith
  have hyZ_eq : (padicUnitPart y : ℤ_[p]) = 1 - xZ := by
    apply Subtype.ext
    rw [coe_padicUnitPart, hy_val, neg_zero, zpow_zero, mul_one, hxy]
    rfl
  apply Multiplicative.toAdd.injective
  ext
  · change (Padic.valuation (y : ℚ_[p]) : ZMod 2) = 0
    rw [hy_val, Int.cast_zero]
  · change unitsToZMod2 (intToSignUnit (quadraticChar (ZMod p)
        (PadicInt.toZMod (padicUnitPart y : ℤ_[p])))) = 0
    rw [hyZ_eq, map_sub, map_one, hxZ_mod, sub_zero, map_one, intToSignUnit_one, unitsToZMod2_one]

/-- **Steinberg Relation on `ℚ_[p]ˣ` (odd `p`)**: `(x, 1 - x)_p = 1`. -/
theorem hilbertSymPadicOdd_steinberg (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (x y : ℚ_[p]ˣ)
    (hxy : (y : ℚ_[p]) = 1 - (x : ℚ_[p])) :
    hilbertSymPadicOdd p hp2 x y = 1 := by
  have hp : p.Prime := Fact.out
  have hp_gt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  rcases lt_trichotomy 0 (Padic.valuation (x : ℚ_[p])) with hpos | hzero | hneg
  · have hy1 := padicOddCoordHom_one_sub_of_pos_val hpos hxy
    unfold hilbertSymPadicOdd
    rw [hy1]; simp
  · have hx_norm : ‖(x : ℚ_[p])‖ = 1 := by
      rw [Padic.norm_eq_zpow_neg_valuation x.ne_zero, ← hzero, neg_zero, zpow_zero]
    have hy_norm_le : ‖(y : ℚ_[p])‖ ≤ 1 := by
      let xZ : ℤ_[p] := ⟨(x : ℚ_[p]), le_of_eq hx_norm⟩
      have h : ‖((1 - xZ : ℤ_[p]) : ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (1 - xZ)
      change ‖(1 : ℚ_[p]) - (x : ℚ_[p])‖ ≤ 1 at h
      rwa [← hxy] at h
    have hy_ge : 0 ≤ Padic.valuation (y : ℚ_[p]) := by
      by_contra hlt
      push Not at hlt
      have h1 := Padic.norm_eq_zpow_neg_valuation y.ne_zero
      have : (1 : ℝ) < (p : ℝ) ^ (-Padic.valuation (y : ℚ_[p])) := one_lt_zpow₀ hp_gt (by omega)
      linarith
    rcases eq_or_lt_of_le hy_ge with hy0 | hypos
    · unfold hilbertSymPadicOdd
      dsimp only
      have h1 : (Multiplicative.toAdd (padicOddCoordHom p x)).1 = 0 := by
        change (Padic.valuation (x : ℚ_[p]) : ZMod 2) = 0; rw [← hzero, Int.cast_zero]
      have h2 : (Multiplicative.toAdd (padicOddCoordHom p y)).1 = 0 := by
        change (Padic.valuation (y : ℚ_[p]) : ZMod 2) = 0; rw [← hy0, Int.cast_zero]
      rw [h1, h2]; simp
    · have hx1 := padicOddCoordHom_one_sub_of_pos_val hypos
        (by rw [hxy]; ring : (x : ℚ_[p]) = 1 - (y : ℚ_[p]))
      unfold hilbertSymPadicOdd
      rw [hx1]; simp
  · have hpos_inv : 0 < Padic.valuation ((x⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) := by
      rw [Units.val_inv_eq_inv_val, Padic.valuation_inv]; omega
    have hne : 1 - ((x⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) ≠ 0 := by
      intro h0
      have hx1 : (x : ℚ_[p]) = 1 := by
        rw [Units.val_inv_eq_inv_val] at h0
        exact inv_eq_one.mp (by linear_combination -h0)
      exact y.ne_zero (by rw [hxy, hx1, sub_self])
    let c : ℚ_[p]ˣ := Units.mk0 (1 - ((x⁻¹ : ℚ_[p]ˣ) : ℚ_[p])) hne
    have hyc : y = (-x) * c := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_neg, c, Units.val_mk0, Units.val_inv_eq_inv_val, hxy]
      field_simp [x.ne_zero]; ring
    have hc1 := padicOddCoordHom_one_sub_of_pos_val hpos_inv (rfl : (c : ℚ_[p]) = 1 - ((x⁻¹ : ℚ_[p]ˣ) : ℚ_[p]))
    rw [hyc, hilbertSymPadicOdd_mul_right, hilbertSymPadicOdd_self_neg, one_mul]
    unfold hilbertSymPadicOdd
    rw [hc1]; simp

theorem hilbertSymPadicOdd_eq_one_of_binary_norm (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {a b : ℚ_[p]ˣ} (hnorm : ∃ u v : ℚ_[p], u ^ 2 - (a : ℚ_[p]) * v ^ 2 = (b : ℚ_[p])) :
    hilbertSymPadicOdd p hp2 a b = 1 := by
  obtain ⟨u, v, huv⟩ := hnorm
  by_cases hv : v = 0
  · subst hv
    have hu : u ≠ 0 := by
      intro hu0; rw [hu0] at huv; simp at huv; exact b.ne_zero huv.symm
    have hbeq : b = (Units.mk0 u hu) ^ 2 := Units.ext (by simpa [sq] using huv.symm)
    rw [hbeq]; exact hilbertSymPadicOdd_sq_right p hp2 a _
  · by_cases hu : u = 0
    · subst hu
      have hbeq : b = (-a) * (Units.mk0 v hv) ^ 2 :=
        Units.ext (by simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mk0]; linear_combination -huv)
      rw [hbeq, hilbertSymPadicOdd_mul_right, hilbertSymPadicOdd_self_neg,
        hilbertSymPadicOdd_sq_right, mul_one]
    · let uu : ℚ_[p]ˣ := Units.mk0 u hu
      let uv : ℚ_[p]ˣ := Units.mk0 v hv
      let c : ℚ_[p]ˣ := a * (uv * uu⁻¹) ^ 2
      let d : ℚ_[p]ˣ := b * (uu⁻¹) ^ 2
      have hcd : (d : ℚ_[p]) = 1 - (c : ℚ_[p]) := by
        simp only [c, d, uu, uv, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
          Units.val_mk0, ← huv]
        field_simp [hu]
      have h1 : hilbertSymPadicOdd p hp2 c d = hilbertSymPadicOdd p hp2 a b := by
        dsimp only [c, d]
        rw [hilbertSymPadicOdd_mul_left, hilbertSymPadicOdd_sq_left, mul_one,
          hilbertSymPadicOdd_mul_right, hilbertSymPadicOdd_sq_right, mul_one]
      rw [← h1]
      exact hilbertSymPadicOdd_steinberg p hp2 c d hcd

/-! #### Algebraic Laws & Steinberg Relation for `hilbertSymPadicTwo` -/

theorem hilbertSymPadicTwo_symm (x y : ℚ_[2]ˣ) :
    hilbertSymPadicTwo x y = hilbertSymPadicTwo y x := by
  unfold hilbertSymPadicTwo; dsimp only; congr 1; ring

theorem hilbertSymPadicTwo_mul_left (x₁ x₂ y : ℚ_[2]ˣ) :
    hilbertSymPadicTwo (x₁ * x₂) y = hilbertSymPadicTwo x₁ y * hilbertSymPadicTwo x₂ y := by
  unfold hilbertSymPadicTwo
  dsimp only
  rw [← negOnePowZMod2_add, map_mul, toAdd_mul]
  congr 1; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem hilbertSymPadicTwo_mul_right (x y₁ y₂ : ℚ_[2]ˣ) :
    hilbertSymPadicTwo x (y₁ * y₂) = hilbertSymPadicTwo x y₁ * hilbertSymPadicTwo x y₂ := by
  rw [hilbertSymPadicTwo_symm, hilbertSymPadicTwo_mul_left,
    hilbertSymPadicTwo_symm y₁ x, hilbertSymPadicTwo_symm y₂ x]

theorem hilbertSymPadicTwo_sq_left (x y : ℚ_[2]ˣ) :
    hilbertSymPadicTwo (x ^ 2) y = 1 := by
  rw [sq, hilbertSymPadicTwo_mul_left, intUnits_mul_self]

theorem hilbertSymPadicTwo_sq_right (x y : ℚ_[2]ˣ) :
    hilbertSymPadicTwo x (y ^ 2) = 1 := by
  rw [sq, hilbertSymPadicTwo_mul_right, intUnits_mul_self]

theorem hilbertSymPadicTwo_inv_left (x y : ℚ_[2]ˣ) :
    hilbertSymPadicTwo x⁻¹ y = hilbertSymPadicTwo x y := by
  have h : hilbertSymPadicTwo (x * x⁻¹) y = 1 := by
    rw [mul_inv_cancel]; unfold hilbertSymPadicTwo; simp
  rw [hilbertSymPadicTwo_mul_left] at h
  calc hilbertSymPadicTwo x⁻¹ y
      = hilbertSymPadicTwo x y * (hilbertSymPadicTwo x y * hilbertSymPadicTwo x⁻¹ y) := by
          rw [← mul_assoc, intUnits_mul_self, one_mul]
    _ = hilbertSymPadicTwo x y := by rw [h, mul_one]

theorem hilbertSymPadicTwo_self_neg (x : ℚ_[2]ˣ) :
    hilbertSymPadicTwo x (-x) = 1 := by
  have hneg1 : Multiplicative.toAdd (padicTwoCoordHom (-1 : ℚ_[2]ˣ)) = (0, 1, 0) := by
    have h := padicTwoCoordHom_ratToPadicUnit (-1)
    rw [ratToPadicUnit_neg, show ratToPadicUnit 2 1 = 1 from map_one _, twoCoords_neg_one] at h
    exact h
  have hnegx : -x = (-1 : ℚ_[2]ˣ) * x := by simp
  unfold hilbertSymPadicTwo
  rw [hnegx, map_mul, toAdd_mul, hneg1]
  simp only [Prod.fst_add, Prod.snd_add, zero_add]
  have hz : ∀ α ε ω : ZMod 2, ε * (1 + ε) + α * ω + α * ω = 0 := by decide
  rw [hz]; rfl

/-- Helper: Steinberg relation on `ℚ_[2]ˣ` when `0 < Padic.valuation x`. -/
private theorem hilbertSymPadicTwo_steinberg_of_pos_val {x y : ℚ_[2]ˣ}
    (hx : 0 < Padic.valuation (x : ℚ_[2])) (hxy : (y : ℚ_[2]) = 1 - (x : ℚ_[2])) :
    hilbertSymPadicTwo x y = 1 := by
  have h2gt : (1 : ℝ) < (2 : ℝ) := by norm_num
  have hx_norm_lt : ‖(x : ℚ_[2])‖ < 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation x.ne_zero]
    simpa only [Nat.cast_ofNat] using zpow_lt_one_of_neg₀ h2gt (show -Padic.valuation (x : ℚ_[2]) < 0 by omega)
  let xZ : ℤ_[2] := ⟨(x : ℚ_[2]), hx_norm_lt.le⟩
  have hxZ_mod : PadicInt.toZMod xZ = 0 := by
    change xZ ∈ RingHom.ker (PadicInt.toZMod (p := 2))
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit xZ
    rw [PadicInt.not_isUnit_iff]
    exact hx_norm_lt
  have h1mx_unit : IsUnit (1 - xZ) := by
    by_contra hnu
    have hker : 1 - xZ ∈ RingHom.ker (PadicInt.toZMod (p := 2)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]; exact hnu
    change PadicInt.toZMod (1 - xZ) = 0 at hker
    rw [map_sub, map_one, hxZ_mod, sub_zero] at hker
    exact one_ne_zero hker
  have hy_norm : ‖(y : ℚ_[2])‖ = 1 := by
    have h := PadicInt.isUnit_iff.mp h1mx_unit
    change ‖(1 : ℚ_[2]) - (x : ℚ_[2])‖ = 1 at h
    rwa [← hxy] at h
  have hy_val : Padic.valuation (y : ℚ_[2]) = 0 := by
    have h1 := Padic.norm_eq_zpow_neg_valuation y.ne_zero
    simp only [Nat.cast_ofNat] at h1
    rw [hy_norm] at h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (1 : ℝ) < (2 : ℝ) ^ (-Padic.valuation (y : ℚ_[2])) := one_lt_zpow₀ h2gt (by omega)
      linarith
    · have : (2 : ℝ) ^ (-Padic.valuation (y : ℚ_[2])) < 1 := zpow_lt_one_of_neg₀ h2gt (by omega)
      linarith
  set α : ℤ := Padic.valuation (x : ℚ_[2])
  set k : ℕ := α.toNat
  have hk_eq : (k : ℤ) = α := Int.toNat_of_nonneg (le_of_lt hx)
  set uZ : ℤ_[2]ˣ := padicUnitPart x
  have hou : (PadicInt.toZModPow 3 (uZ : ℤ_[2])).val % 2 = 1 := toZModPow3_padicIntUnit_odd uZ
  have hyZ_eq : (padicUnitPart y : ℤ_[2]) = 1 - (2 : ℤ_[2]) ^ k * (uZ : ℤ_[2]) := by
    apply Subtype.ext
    rw [coe_padicUnitPart, hy_val, neg_zero, zpow_zero, mul_one, hxy]
    have hx_spec := padic_eq_p_zpow_mul_unitPart x
    simp only [Nat.cast_ofNat] at hx_spec
    change 1 - (x : ℚ_[2]) = 1 - (2 : ℚ_[2]) ^ k * ((uZ : ℤ_[2]) : ℚ_[2])
    rw [hx_spec]
    congr 1
    change (2 : ℚ_[2]) ^ α * ((uZ : ℤ_[2]) : ℚ_[2]) = (2 : ℚ_[2]) ^ k * ((uZ : ℤ_[2]) : ℚ_[2])
    rw [← hk_eq, zpow_natCast]
  have hred_y : (PadicInt.toZModPow 3 (padicUnitPart y : ℤ_[2]) : ZMod 8) =
      1 - (2 : ZMod 8) ^ k * (PadicInt.toZModPow 3 (uZ : ℤ_[2]) : ZMod 8) := by
    rw [hyZ_eq, map_sub, map_one, map_mul, map_pow]
    have h2 : (PadicInt.toZModPow 3 (2 : ℤ_[2]) : ZMod 8) = 2 := map_ofNat (PadicInt.toZModPow 3) 2
    rw [h2]
  unfold hilbertSymPadicTwo padicTwoCoordHom
  dsimp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  rw [hy_val, Int.cast_zero, zero_mul, add_zero, hred_y]
  change negOnePowZMod2
    (eps8 (PadicInt.toZModPow 3 (uZ : ℤ_[2])) *
        eps8 (1 - (2 : ZMod 8) ^ k * PadicInt.toZModPow 3 (uZ : ℤ_[2])) +
      (α : ZMod 2) *
        omega8 (1 - (2 : ZMod 8) ^ k * PadicInt.toZModPow 3 (uZ : ℤ_[2]))) = 1
  rw [← hk_eq, Int.cast_natCast]
  have hk_ge1 : 1 ≤ k := by omega
  rcases eq_or_lt_of_le hk_ge1 with hk1 | hk_ge2
  · rw [← hk1]
    simp only [pow_one, Nat.cast_one, one_mul]
    rw [steinberg_zmod8_alpha_one hou]; rfl
  · rcases eq_or_lt_of_le (show 2 ≤ k from hk_ge2) with hk2 | hk_ge3
    · rw [← hk2]
      have h22 : ((2 : ℕ) : ZMod 2) = 0 := ZMod.natCast_self 2
      have hpow2 : (2 : ZMod 8) ^ 2 = 4 := by decide
      rw [h22, zero_mul, add_zero, hpow2, steinberg_zmod8_alpha_two hou, mul_zero]; rfl
    · have hpow0 : (2 : ZMod 8) ^ k = 0 := by
        obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hk_ge3
        rw [hm, pow_add]
        have h23 : (2 : ZMod 8) ^ 3 = 0 := by decide
        rw [h23, zero_mul]
      rw [hpow0, zero_mul, sub_zero, eps8_one, omega8_one, mul_zero, mul_zero, add_zero]; rfl

/-- **Steinberg Relation on `ℚ_[2]ˣ`**: `(x, 1 - x)_2 = 1`. -/
theorem hilbertSymPadicTwo_steinberg (x y : ℚ_[2]ˣ) (hxy : (y : ℚ_[2]) = 1 - (x : ℚ_[2])) :
    hilbertSymPadicTwo x y = 1 := by
  have h2gt : (1 : ℝ) < (2 : ℝ) := by norm_num
  rcases lt_trichotomy 0 (Padic.valuation (x : ℚ_[2])) with hpos | hzero | hneg
  · exact hilbertSymPadicTwo_steinberg_of_pos_val hpos hxy
  · have hy_pos : 0 < Padic.valuation (y : ℚ_[2]) := by
      have hxZ_eq : ((padicUnitPart x : ℤ_[2]) : ℚ_[2]) = (x : ℚ_[2]) := by
        rw [coe_padicUnitPart, ← hzero, neg_zero, zpow_zero, mul_one]
      have hx1 : (PadicInt.toZModPow 1 (padicUnitPart x : ℤ_[2]) : ZMod (2 ^ 1)) = 1 := by
        have hodd := toZModPow3_padicIntUnit_odd (padicUnitPart x)
        have hcast := PadicInt.cast_toZModPow 1 3 (by norm_num) (padicUnitPart x : ℤ_[2])
        rw [← hcast, ZMod.cast_eq_val]
        have hne0 : (((PadicInt.toZModPow 3 (padicUnitPart x : ℤ_[2])).val : ℕ) : ZMod (2 ^ 1)) ≠ 0 := by
          intro h0
          have hd : 2 ^ 1 ∣ (PadicInt.toZModPow 3 (padicUnitPart x : ℤ_[2])).val :=
            (ZMod.natCast_eq_zero_iff _ _).mp h0
          omega
        generalize (((PadicInt.toZModPow 3 (padicUnitPart x : ℤ_[2])).val : ℕ) : ZMod (2 ^ 1)) = t at hne0 ⊢
        fin_cases t
        · exact absurd rfl hne0
        · rfl
      let yZ : ℤ_[2] := 1 - (padicUnitPart x : ℤ_[2])
      have hyZ_coe : (yZ : ℚ_[2]) = (y : ℚ_[2]) := by
        change (1 : ℚ_[2]) - ((padicUnitPart x : ℤ_[2]) : ℚ_[2]) = (y : ℚ_[2])
        rw [hxZ_eq, hxy]
      have hyZ_ker : yZ ∈ RingHom.ker (PadicInt.toZModPow 1) := by
        change PadicInt.toZModPow 1 (1 - (padicUnitPart x : ℤ_[2])) = 0
        rw [map_sub, map_one, hx1, sub_self]
      rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
        IsLocalRing.mem_maximalIdeal] at hyZ_ker
      have hyZ_nunit : ¬ IsUnit yZ := hyZ_ker
      rw [PadicInt.not_isUnit_iff] at hyZ_nunit
      have hy_lt : ‖(y : ℚ_[2])‖ < 1 := by simpa [← hyZ_coe] using hyZ_nunit
      by_contra hle
      push Not at hle
      have h1 := Padic.norm_eq_zpow_neg_valuation y.ne_zero
      simp only [Nat.cast_ofNat] at h1
      have hge : (1 : ℝ) ≤ (2 : ℝ) ^ (-Padic.valuation (y : ℚ_[2])) := one_le_zpow₀ h2gt.le (by omega)
      linarith
    rw [hilbertSymPadicTwo_symm]
    exact hilbertSymPadicTwo_steinberg_of_pos_val hy_pos (by rw [hxy]; ring)
  · have hpos_inv : 0 < Padic.valuation ((x⁻¹ : ℚ_[2]ˣ) : ℚ_[2]) := by
      rw [Units.val_inv_eq_inv_val, Padic.valuation_inv]; omega
    have hne : 1 - ((x⁻¹ : ℚ_[2]ˣ) : ℚ_[2]) ≠ 0 := by
      intro h0
      have hx1 : (x : ℚ_[2]) = 1 := by
        rw [Units.val_inv_eq_inv_val] at h0
        exact inv_eq_one.mp (by linear_combination -h0)
      exact y.ne_zero (by rw [hxy, hx1, sub_self])
    let c : ℚ_[2]ˣ := Units.mk0 (1 - ((x⁻¹ : ℚ_[2]ˣ) : ℚ_[2])) hne
    have hyc : y = (-x) * c := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_neg, c, Units.val_mk0, Units.val_inv_eq_inv_val, hxy]
      field_simp [x.ne_zero]; ring
    rw [hyc, hilbertSymPadicTwo_mul_right, hilbertSymPadicTwo_self_neg, one_mul,
      ← hilbertSymPadicTwo_inv_left]
    exact hilbertSymPadicTwo_steinberg_of_pos_val hpos_inv rfl

theorem hilbertSymPadicTwo_eq_one_of_binary_norm {a b : ℚ_[2]ˣ}
    (hnorm : ∃ u v : ℚ_[2], u ^ 2 - (a : ℚ_[2]) * v ^ 2 = (b : ℚ_[2])) :
    hilbertSymPadicTwo a b = 1 := by
  obtain ⟨u, v, huv⟩ := hnorm
  by_cases hv : v = 0
  · subst hv
    have hu : u ≠ 0 := by
      intro hu0; rw [hu0] at huv; simp at huv; exact b.ne_zero huv.symm
    have hbeq : b = (Units.mk0 u hu) ^ 2 := Units.ext (by simpa [sq] using huv.symm)
    rw [hbeq]; exact hilbertSymPadicTwo_sq_right a _
  · by_cases hu : u = 0
    · subst hu
      have hbeq : b = (-a) * (Units.mk0 v hv) ^ 2 :=
        Units.ext (by simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mk0]; linear_combination -huv)
      rw [hbeq, hilbertSymPadicTwo_mul_right, hilbertSymPadicTwo_self_neg,
        hilbertSymPadicTwo_sq_right, mul_one]
    · let uu : ℚ_[2]ˣ := Units.mk0 u hu
      let uv : ℚ_[2]ˣ := Units.mk0 v hv
      let c : ℚ_[2]ˣ := a * (uv * uu⁻¹) ^ 2
      let d : ℚ_[2]ˣ := b * (uu⁻¹) ^ 2
      have hcd : (d : ℚ_[2]) = 1 - (c : ℚ_[2]) := by
        simp only [c, d, uu, uv, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
          Units.val_mk0, ← huv]
        field_simp [hu]
      have h1 : hilbertSymPadicTwo c d = hilbertSymPadicTwo a b := by
        dsimp only [c, d]
        rw [hilbertSymPadicTwo_mul_left, hilbertSymPadicTwo_sq_left, mul_one,
          hilbertSymPadicTwo_mul_right, hilbertSymPadicTwo_sq_right, mul_one]
      rw [← h1]
      exact hilbertSymPadicTwo_steinberg c d hcd

/-! ### 2C. Exact Local Solvability Characterization at Every Odd Prime `p` -/

/-- Pigeonhole on `ZMod p` (odd prime `p`): for any nonzero `u, v ∈ ZMod p`, `u x² + v y² = 1`
has a solution in `ZMod p`. -/
theorem exists_sol_zmod_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {u v : ZMod p}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ x y : ZMod p, u * x ^ 2 + v * y ^ 2 = 1 := by
  have hp : p.Prime := Fact.out
  have hp_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  let S : Finset (ZMod p) := Finset.univ.image (fun x : ZMod p => u * x ^ 2)
  let T : Finset (ZMod p) := Finset.univ.image (fun y : ZMod p => 1 - v * y ^ 2)
  have hcard_sq : ∀ (c : ZMod p) (hc : c ≠ 0) (f : ZMod p → ZMod p)
      (hf : ∀ x₁ x₂ : ZMod p, f x₁ = f x₂ → x₁ = x₂ ∨ x₁ = -x₂),
      p < 2 * (Finset.univ.image f).card := by
    intro c hc f hf
    have hfib : ∀ z ∈ Finset.univ.image f, (Finset.univ.filter (fun x => f x = z)).card ≤ 2 := by
      intro z hz
      obtain ⟨x₀, _, rfl⟩ := Finset.mem_image.mp hz
      have hsub : Finset.univ.filter (fun x => f x = f x₀) ⊆ ({x₀, -x₀} : Finset (ZMod p)) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact hf x x₀ hx
      exact le_trans (Finset.card_le_card hsub) (Finset.card_le_two)
    have hfib0 : (Finset.univ.filter (fun x => f x = f 0)).card = 1 := by
      have heq : Finset.univ.filter (fun x => f x = f 0) = {0} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          rcases hf x 0 h with rfl | hneg
          · rfl
          · simpa using hneg
        · rintro rfl; rfl
      rw [heq, Finset.card_singleton]
    have hsum : ∑ z ∈ Finset.univ.image f, (Finset.univ.filter (fun x => f x = z)).card = p := by
      rw [← Finset.card_eq_sum_card_image f Finset.univ]
      exact ZMod.card p
    have hf0_mem : f 0 ∈ Finset.univ.image f := Finset.mem_image_of_mem f (Finset.mem_univ 0)
    have hsum_le : ∑ z ∈ Finset.univ.image f, (Finset.univ.filter (fun x => f x = z)).card ≤
        2 * (Finset.univ.image f).card - 1 := by
      have hsplit := Finset.add_sum_erase (Finset.univ.image f)
        (fun z => (Finset.univ.filter (fun x => f x = z)).card) hf0_mem
      rw [hfib0] at hsplit
      have herase_le : ∑ z ∈ (Finset.univ.image f).erase (f 0),
          (Finset.univ.filter (fun x => f x = z)).card ≤
          2 * ((Finset.univ.image f).erase (f 0)).card := by
        calc ∑ z ∈ (Finset.univ.image f).erase (f 0),
              (Finset.univ.filter (fun x => f x = z)).card
            ≤ ∑ _z ∈ (Finset.univ.image f).erase (f 0), 2 :=
              Finset.sum_le_sum fun z hz => hfib z (Finset.mem_of_mem_erase hz)
          _ = 2 * ((Finset.univ.image f).erase (f 0)).card := by
              rw [Finset.sum_const, smul_eq_mul, mul_comm]
      have hcard_pos : 1 ≤ (Finset.univ.image f).card := Finset.card_pos.mpr ⟨f 0, hf0_mem⟩
      have hcard_er : ((Finset.univ.image f).erase (f 0)).card + 1 = (Finset.univ.image f).card :=
        Finset.card_erase_add_one hf0_mem
      omega
    omega
  have hS : p < 2 * S.card := hcard_sq u hu (fun x => u * x ^ 2) (fun x₁ x₂ h => by
    have hsq : x₁ ^ 2 = x₂ ^ 2 := mul_left_cancel₀ hu h
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq)
  have hT : p < 2 * T.card := hcard_sq v hv (fun y => 1 - v * y ^ 2) (fun y₁ y₂ h => by
    have h1 : v * y₁ ^ 2 = v * y₂ ^ 2 := by linear_combination -h
    have hsq : y₁ ^ 2 = y₂ ^ 2 := mul_left_cancel₀ hv h1
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq)
  have hcard_gt : Fintype.card (ZMod p) < S.card + T.card := by
    rw [ZMod.card p]; omega
  have hnonempty : (S ∩ T).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hdisj : Disjoint S T := Finset.disjoint_iff_inter_eq_empty.mpr hemp
    have hle : (S ∪ T).card ≤ Fintype.card (ZMod p) := Finset.card_le_univ _
    rw [Finset.card_union_of_disjoint hdisj] at hle
    omega
  obtain ⟨z, hz⟩ := hnonempty
  obtain ⟨hzS, hzT⟩ := Finset.mem_inter.mp hz
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hzS
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hzT
  exact ⟨x, y, by linear_combination hx - hy⟩

/-- Helper: any two `p`-adic units `u, v : ℤ_[p]ˣ` (odd `p`) represent `1` as `u x² + v y² = w²`
in `ℚ_[p]` (via pigeonhole mod `p` + Hensel's lemma). -/
theorem exists_unit_ternary_padic_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (u v : ℤ_[p]ˣ) :
    ∃ x y z : ℚ_[p], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      ((u : ℤ_[p]) : ℚ_[p]) * x ^ 2 + ((v : ℤ_[p]) : ℚ_[p]) * y ^ 2 = z ^ 2 := by
  have hu0 : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 := toZMod_padicIntUnit_ne_zero u
  have hv0 : PadicInt.toZMod (v : ℤ_[p]) ≠ 0 := toZMod_padicIntUnit_ne_zero v
  obtain ⟨x0, y0, hxy0⟩ := exists_sol_zmod_odd hp2 hu0 hv0
  let xZ : ℤ_[p] := (x0.val : ℤ_[p])
  let yZ : ℤ_[p] := (y0.val : ℤ_[p])
  let wZ : ℤ_[p] := (u : ℤ_[p]) * xZ ^ 2 + (v : ℤ_[p]) * yZ ^ 2
  have hwZ_mod : PadicInt.toZMod wZ = 1 := by
    dsimp only [wZ, xZ, yZ]
    simp only [map_add, map_mul, map_pow, map_natCast, ZMod.natCast_zmod_val]
    exact hxy0
  have hwZ_unit : IsUnit wZ := by
    by_contra hnu
    have hker : wZ ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]; exact hnu
    change PadicInt.toZMod wZ = 0 at hker
    rw [hwZ_mod] at hker
    exact one_ne_zero hker
  obtain ⟨zZ, hzZ⟩ := exists_sq_padicInt_odd hp2 hwZ_unit.unit (by
    change IsSquare (PadicInt.toZMod wZ)
    rw [hwZ_mod]; exact ⟨1, (one_mul 1).symm⟩)
  have hzZ_ne : (zZ : ℚ_[p]) ≠ 0 := by
    intro h0
    have hz0 : zZ = 0 := Subtype.ext h0
    rw [hz0, zero_pow two_ne_zero] at hzZ
    exact hwZ_unit.ne_zero hzZ.symm
  refine ⟨(xZ : ℚ_[p]), (yZ : ℚ_[p]), (zZ : ℚ_[p]), Or.inr (Or.inr hzZ_ne), ?_⟩
  have hcoe := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hzZ
  simpa [wZ] using hcoe.symm

/-- Helper: if two elements `x, y : ℚ_[p]ˣ` have the same `padicOddCoordHom`, then `x = y * w²`. -/
theorem eq_mul_sq_of_padicOddCoordHom_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {x y : ℚ_[p]ˣ}
    (h : padicOddCoordHom p x = padicOddCoordHom p y) :
    ∃ w : ℚ_[p]ˣ, x = y * w ^ 2 := by
  have hker : x * y⁻¹ ∈ (padicOddCoordHom p).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have hsq_ker : (padicOddCoordHom p).ker = (powMonoidHom (α := ℚ_[p]ˣ) 2).range := by
    ext z
    constructor
    · intro hz
      have hq1 : (padicSqQuotEquivOdd p hp2) (Additive.ofMul (QuotientGroup.mk z)) = 0 := by
        unfold padicSqQuotEquivOdd sqQuotEquivOfHom addEquivToZMod2LinearEquiv
        change Multiplicative.toAdd (padicOddCoordHom p z) = 0
        rw [MonoidHom.mem_ker.mp hz]; rfl
      have hq0 : (Additive.ofMul (QuotientGroup.mk z) : SqQuot ℚ_[p]ˣ) = 0 :=
        (padicSqQuotEquivOdd p hp2).injective (by rw [hq1, map_zero])
      have hq1' : (QuotientGroup.mk z : ℚ_[p]ˣ ⧸ (powMonoidHom (α := ℚ_[p]ˣ) 2).range) = 1 :=
        Additive.ofMul.injective hq0
      exact (QuotientGroup.eq_one_iff z).mp hq1'
    · rintro ⟨w, rfl⟩
      rw [MonoidHom.mem_ker]; change padicOddCoordHom p (w ^ 2) = 1
      rw [sq, map_mul]
      apply Multiplicative.toAdd.injective
      have h2 : ∀ t : ZMod 2, t + t = 0 := by decide
      exact Prod.ext (h2 _) (h2 _)
  rw [hsq_ker] at hker
  obtain ⟨w, hw⟩ := hker
  refine ⟨w, ?_⟩
  change w ^ 2 = x * y⁻¹ at hw
  calc x = (x * y⁻¹) * y := (inv_mul_cancel_right x y).symm
    _ = w ^ 2 * y := by rw [hw]
    _ = y * w ^ 2 := mul_comm _ _

/-- **Exact `p`-adic Solvability Criterion at Every Odd Prime `p`**:
`hilbertSymPadicOdd p hp2 x y = 1 ↔ ∃ u v w : ℚ_[p], (u, v, w) ≠ 0 ∧ x u² + y v² = w²`. -/
theorem hilbertSymPadicOdd_eq_one_iff_norm_form (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (x y : ℚ_[p]ˣ) :
    hilbertSymPadicOdd p hp2 x y = 1 ↔
      ∃ u v w : ℚ_[p], (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧
        (x : ℚ_[p]) * u ^ 2 + (y : ℚ_[p]) * v ^ 2 = w ^ 2 := by
  have hp : p.Prime := Fact.out
  have h2ne : (2 : ℚ_[p]) ≠ 0 := by norm_num
  constructor
  · intro hsym
    -- Build explicit square-class representatives {1, u_ns, p, p * u_ns}
    have hrc : ringChar (ZMod p) ≠ 2 := (ZMod.ringChar_zmod_n p).substr hp2
    obtain ⟨r, hr⟩ := quadraticChar_exists_neg_one hrc
    have hr0 : r ≠ 0 := by
      rintro rfl; rw [quadraticChar_zero] at hr; norm_num at hr
    let uZ : ℤ_[p] := (r.val : ℤ_[p])
    have huZ_mod : PadicInt.toZMod uZ = r := by simp [uZ]
    have huZ_unit : IsUnit uZ := by
      by_contra hnu
      have hmem : uZ ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
        rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]; exact hnu
      exact hr0 (huZ_mod ▸ hmem)
    let gU : ℚ_[p]ˣ := Units.mk0 (uZ : ℚ_[p]) (fun h0 => huZ_unit.ne_zero (Subtype.ext h0))
    let gP : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr hp.ne_zero)
    have hgU_val : Padic.valuation (gU : ℚ_[p]) = 0 := by
      have hnorm : ‖(gU : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.mp huZ_unit
      have h1 := Padic.norm_eq_zpow_neg_valuation gU.ne_zero
      rw [hnorm] at h1
      have hp_gt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := one_lt_zpow₀ hp_gt (show 0 < -Padic.valuation (gU : ℚ_[p]) by omega); linarith
      · have := zpow_lt_one_of_neg₀ hp_gt (show -Padic.valuation (gU : ℚ_[p]) < 0 by omega); linarith
    have hgU_coord : Multiplicative.toAdd (padicOddCoordHom p gU) = (0, 1) := by
      ext
      · change (Padic.valuation (gU : ℚ_[p]) : ZMod 2) = 0; rw [hgU_val, Int.cast_zero]
      · change unitsToZMod2 (intToSignUnit (quadraticChar (ZMod p)
            (PadicInt.toZMod (padicUnitPart gU : ℤ_[p])))) = 1
        have hup : (padicUnitPart gU : ℤ_[p]) = uZ := by
          apply Subtype.ext; rw [coe_padicUnitPart, hgU_val, neg_zero, zpow_zero, mul_one]; rfl
        rw [hup, huZ_mod, hr, intToSignUnit_neg_one, unitsToZMod2_neg_one]
    have hgP_val : Padic.valuation (gP : ℚ_[p]) = 1 := by
      change Padic.valuation (p : ℚ_[p]) = 1
      rw [Padic.valuation_natCast, padicValNat.self hp.one_lt, Nat.cast_one]
    have hgP_coord : Multiplicative.toAdd (padicOddCoordHom p gP) = (1, 0) := by
      ext
      · change (Padic.valuation (gP : ℚ_[p]) : ZMod 2) = 1; rw [hgP_val, Int.cast_one]
      · change unitsToZMod2 (intToSignUnit (quadraticChar (ZMod p)
            (PadicInt.toZMod (padicUnitPart gP : ℤ_[p])))) = 0
        have hup : (padicUnitPart gP : ℤ_[p]) = 1 := by
          apply Subtype.ext; rw [coe_padicUnitPart, hgP_val]
          change (p : ℚ_[p]) * (p : ℚ_[p]) ^ (-1 : ℤ) = 1
          rw [zpow_neg_one, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hp.ne_zero)]
        rw [hup, map_one, map_one, intToSignUnit_one, unitsToZMod2_one]
    -- Helper: reduce x, y to square-class reps x₀, y₀
    have hrep : ∀ z : ℚ_[p]ˣ, ∃ z₀ w : ℚ_[p]ˣ, z = z₀ * w ^ 2 ∧
        (z₀ = 1 ∨ z₀ = gU ∨ z₀ = gP ∨ z₀ = gP * gU) := by
      intro z
      rcases zmod2_eq_zero_or_one (Multiplicative.toAdd (padicOddCoordHom p z)).1 with h1 | h1 <;>
        rcases zmod2_eq_zero_or_one (Multiplicative.toAdd (padicOddCoordHom p z)).2 with h2 | h2
      · obtain ⟨w, hw⟩ := eq_mul_sq_of_padicOddCoordHom_eq hp2 (x := z) (y := 1) (by
          apply Multiplicative.toAdd.injective; exact Prod.ext (by simpa using h1) (by simpa using h2))
        exact ⟨1, w, hw, Or.inl rfl⟩
      · obtain ⟨w, hw⟩ := eq_mul_sq_of_padicOddCoordHom_eq hp2 (x := z) (y := gU) (by
          apply Multiplicative.toAdd.injective; rw [hgU_coord]; exact Prod.ext h1 h2)
        exact ⟨gU, w, hw, Or.inr (Or.inl rfl)⟩
      · obtain ⟨w, hw⟩ := eq_mul_sq_of_padicOddCoordHom_eq hp2 (x := z) (y := gP) (by
          apply Multiplicative.toAdd.injective; rw [hgP_coord]; exact Prod.ext h1 h2)
        exact ⟨gP, w, hw, Or.inr (Or.inr (Or.inl rfl))⟩
      · obtain ⟨w, hw⟩ := eq_mul_sq_of_padicOddCoordHom_eq hp2 (x := z) (y := gP * gU) (by
          apply Multiplicative.toAdd.injective
          rw [map_mul, toAdd_mul, hgP_coord, hgU_coord]
          exact Prod.ext (by simpa using h1) (by simpa using h2))
        exact ⟨gP * gU, w, hw, Or.inr (Or.inr (Or.inr rfl))⟩
    obtain ⟨x₀, wx, rfl, hx₀⟩ := hrep x
    obtain ⟨y₀, wy, rfl, hy₀⟩ := hrep y
    rw [hilbertSymPadicOdd_mul_left, hilbertSymPadicOdd_sq_left, mul_one,
      hilbertSymPadicOdd_mul_right, hilbertSymPadicOdd_sq_right, mul_one] at hsym
    suffices h0 : ∃ u v w : ℚ_[p], (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧
        (x₀ : ℚ_[p]) * u ^ 2 + (y₀ : ℚ_[p]) * v ^ 2 = w ^ 2 by
      obtain ⟨u, v, w, hne, heq⟩ := h0
      refine ⟨u / (wx : ℚ_[p]), v / (wy : ℚ_[p]), w, ?_, ?_⟩
      · rcases hne with hu | hv | hw
        · exact Or.inl (div_ne_zero hu wx.ne_zero)
        · exact Or.inr (Or.inl (div_ne_zero hv wy.ne_zero))
        · exact Or.inr (Or.inr hw)
      · simp only [Units.val_mul, Units.val_pow_eq_pow_val]
        field_simp [wx.ne_zero, wy.ne_zero]
        linear_combination heq
    -- Helper: if (-1 : ZMod p) is a square, then -1 is a square in ℤ_[p]
    have hneg1_sq : ((p / 2 : ℕ) : ZMod 2) = 0 → ∃ s : ℚ_[p], s ^ 2 = -1 := by
      intro hdiv
      have hleg : legendreSym p (-1) = 1 := by
        rw [legendreSym.at_neg_one hp2, ZMod.χ₄_eq_neg_one_pow (hp.mod_two_eq_one_iff_ne_two.mpr hp2)]
        have heven : 2 ∣ (p / 2) := (ZMod.natCast_eq_zero_iff (p / 2) 2).mp hdiv
        obtain ⟨k, hk⟩ := heven
        rw [hk, pow_mul]; norm_num
      have hsq : IsSquare (PadicInt.toZMod ((-1 : ℤ_[p]ˣ) : ℤ_[p])) := by
        rw [Units.val_neg, Units.val_one, map_neg, map_one]
        exact (quadraticChar_one_iff_isSquare (by
          intro h0; exact neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0) h0)).mp (by
            simpa [legendreSym] using hleg)
      obtain ⟨z, hz⟩ := exists_sq_padicInt_odd hp2 (-1 : ℤ_[p]ˣ) hsq
      refine ⟨(z : ℚ_[p]), ?_⟩
      have hcoe := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hz
      simpa using hcoe
    -- Helper: if (-1 : ZMod p) is a non-square, then -uZ is a square in ℤ_[p]
    have hnegu_sq : ((p / 2 : ℕ) : ZMod 2) = 1 → ∃ s : ℚ_[p], s ^ 2 = -(gU : ℚ_[p]) := by
      intro hdiv
      have hleg : legendreSym p (-1) = -1 := by
        rw [legendreSym.at_neg_one hp2, ZMod.χ₄_eq_neg_one_pow (hp.mod_two_eq_one_iff_ne_two.mpr hp2)]
        have hodd : (p / 2) % 2 = 1 := by
          have := congrArg ZMod.val hdiv
          rw [ZMod.val_natCast] at this
          exact this
        have : ∃ k, p / 2 = 2 * k + 1 := ⟨(p / 2) / 2, by omega⟩
        obtain ⟨k, hk⟩ := this
        rw [hk, pow_add, pow_mul]; norm_num
      have hqc_neg1 : quadraticChar (ZMod p) (-1 : ZMod p) = -1 := by
        simpa [legendreSym] using hleg
      have hsq : IsSquare (PadicInt.toZMod ((-huZ_unit.unit : ℤ_[p]ˣ) : ℤ_[p])) := by
        rw [Units.val_neg, map_neg]
        change IsSquare (-PadicInt.toZMod uZ)
        rw [huZ_mod]
        apply (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr hr0)).mp
        rw [neg_eq_neg_one_mul, map_mul, hqc_neg1, hr]; norm_num
      obtain ⟨z, hz⟩ := exists_sq_padicInt_odd hp2 (-huZ_unit.unit) hsq
      refine ⟨(z : ℚ_[p]), ?_⟩
      have hcoe := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hz
      simpa [gU] using hcoe
    -- Check all 4 × 4 = 16 pairs (x₀, y₀) ∈ {1, gU, gP, gP*gU}²
    have hgPU_coord : Multiplicative.toAdd (padicOddCoordHom p (gP * gU)) = (1, 1) := by
      rw [map_mul, toAdd_mul, hgP_coord, hgU_coord]; rfl
    rcases hx₀ with rfl | rfl | rfl | rfl
    · exact ⟨1, 0, 1, Or.inl one_ne_zero, by simp⟩
    · rcases hy₀ with rfl | rfl | rfl | rfl
      · exact ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero), by simp⟩
      · exact exists_unit_ternary_padic_odd hp2 huZ_unit.unit huZ_unit.unit
      · exfalso
        unfold hilbertSymPadicOdd at hsym
        rw [hgU_coord, hgP_coord] at hsym
        simp only [mul_zero, mul_one, add_zero, zero_add] at hsym
        exact (by decide : negOnePowZMod2 (1 : ZMod 2) ≠ 1) hsym
      · exfalso
        unfold hilbertSymPadicOdd at hsym
        rw [hgU_coord, hgPU_coord] at hsym
        simp only [mul_zero, mul_one, add_zero, zero_add] at hsym
        exact (by decide : negOnePowZMod2 (1 : ZMod 2) ≠ 1) hsym
    · rcases hy₀ with rfl | rfl | rfl | rfl
      · exact ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero), by simp⟩
      · exfalso
        unfold hilbertSymPadicOdd at hsym
        rw [hgP_coord, hgU_coord] at hsym
        simp only [mul_zero, mul_one, add_zero, zero_add] at hsym
        exact (by decide : negOnePowZMod2 (1 : ZMod 2) ≠ 1) hsym
      · have he0 : ((p / 2 : ℕ) : ZMod 2) = 0 := by
          unfold hilbertSymPadicOdd at hsym
          rw [hgP_coord] at hsym
          simp only [mul_one, mul_zero, add_zero] at hsym
          exact (negOnePowZMod2_eq_one_iff _).mp hsym
        obtain ⟨s, hs⟩ := hneg1_sq he0
        exact ⟨1, s, 0, Or.inl one_ne_zero, by rw [one_pow, mul_one, hs]; ring⟩
      · have he1 : ((p / 2 : ℕ) : ZMod 2) = 1 := by
          unfold hilbertSymPadicOdd at hsym
          rw [hgP_coord, hgPU_coord] at hsym
          simp only [mul_one, add_zero] at hsym
          have h0 := (negOnePowZMod2_eq_one_iff _).mp hsym
          rcases zmod2_eq_zero_or_one ((p / 2 : ℕ) : ZMod 2) with h | h
          · rw [h] at h0; exact absurd h0 (by decide)
          · exact h
        obtain ⟨s, hs⟩ := hnegu_sq he1
        exact ⟨s, 1, 0, Or.inr (Or.inl one_ne_zero), by
          rw [Units.val_mul, hs, one_pow, mul_one]; ring⟩
    · rcases hy₀ with rfl | rfl | rfl | rfl
      · exact ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero), by simp⟩
      · exfalso
        unfold hilbertSymPadicOdd at hsym
        rw [hgPU_coord, hgU_coord] at hsym
        simp only [mul_zero, mul_one, add_zero, zero_add] at hsym
        exact (by decide : negOnePowZMod2 (1 : ZMod 2) ≠ 1) hsym
      · have he1 : ((p / 2 : ℕ) : ZMod 2) = 1 := by
          unfold hilbertSymPadicOdd at hsym
          rw [hgPU_coord, hgP_coord] at hsym
          simp only [mul_one, mul_zero, add_zero] at hsym
          have h0 := (negOnePowZMod2_eq_one_iff _).mp hsym
          rcases zmod2_eq_zero_or_one ((p / 2 : ℕ) : ZMod 2) with h | h
          · rw [h] at h0; exact absurd h0 (by decide)
          · exact h
        obtain ⟨s, hs⟩ := hnegu_sq he1
        exact ⟨1, s, 0, Or.inl one_ne_zero, by
          rw [Units.val_mul, hs, one_pow, mul_one]; ring⟩
      · have he0 : ((p / 2 : ℕ) : ZMod 2) = 0 := by
          unfold hilbertSymPadicOdd at hsym
          rw [hgPU_coord] at hsym
          simp only [mul_one] at hsym
          have h0 := (negOnePowZMod2_eq_one_iff _).mp hsym
          have h11 : (1 : ZMod 2) + 1 = 0 := by decide
          rw [add_assoc, h11, add_zero] at h0
          exact h0
        obtain ⟨s, hs⟩ := hneg1_sq he0
        exact ⟨1, s, 0, Or.inl one_ne_zero, by rw [one_pow, mul_one, hs]; ring⟩
  · intro hsol
    rw [norm_form_iff_binary_norm h2ne x.ne_zero] at hsol
    exact hilbertSymPadicOdd_eq_one_of_binary_norm p hp2 hsol

/-- **Hilbert Symbol Characterization of `ℚ_[p]`-Isotropy at Every Odd Prime `p`**:
`(-a*c, -b*c)_p = 1 ↔ HasTernaryZeroPadic p a b c`! -/
theorem hilbertSymOdd_ternary_iff (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a b c : ℚˣ) :
    hilbertSymOdd p Fact.out hp2 (-a * c) (-b * c) = 1 ↔ HasTernaryZeroPadic p a b c := by
  have hc : ((c : ℚ) : ℚ_[p]) ≠ 0 := Rat.cast_ne_zero.mpr c.ne_zero
  rw [← hilbertSymPadicOdd_ratCast p hp2 (-a * c) (-b * c),
    hilbertSymPadicOdd_eq_one_iff_norm_form p hp2]
  change (∃ u v w : ℚ_[p], (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧
      (-((a : ℚ) : ℚ_[p]) * ((c : ℚ) : ℚ_[p])) * u ^ 2 +
        (-((b : ℚ) : ℚ_[p]) * ((c : ℚ) : ℚ_[p])) * v ^ 2 = w ^ 2) ↔
    HasTernaryZeroK ((a : ℚ) : ℚ_[p]) ((b : ℚ) : ℚ_[p]) ((c : ℚ) : ℚ_[p])
  exact (hasTernaryZeroK_iff_norm_form hc).symm

/-! ### 2D. Exact Local Solvability Characterization at `p = 2` (`ℚ_[2]`) -/

/-- Helper: if `x, y : ℚ_[2]ˣ` have the same `padicTwoCoordHom`, then `x = y * w²`. -/
theorem eq_mul_sq_of_padicTwoCoordHom_eq {x y : ℚ_[2]ˣ}
    (h : padicTwoCoordHom x = padicTwoCoordHom y) :
    ∃ w : ℚ_[2]ˣ, x = y * w ^ 2 := by
  have hker : x * y⁻¹ ∈ padicTwoCoordHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have hsq_ker : padicTwoCoordHom.ker = (powMonoidHom (α := ℚ_[2]ˣ) 2).range := by
    ext z
    constructor
    · intro hz
      have hq1 : padicSqQuotEquivTwo (Additive.ofMul (QuotientGroup.mk z)) = 0 := by
        unfold padicSqQuotEquivTwo sqQuotEquivOfHom addEquivToZMod2LinearEquiv
        change Multiplicative.toAdd (padicTwoCoordHom z) = 0
        rw [MonoidHom.mem_ker.mp hz]; rfl
      have hq0 : (Additive.ofMul (QuotientGroup.mk z) : SqQuot ℚ_[2]ˣ) = 0 :=
        padicSqQuotEquivTwo.injective (by rw [hq1, map_zero])
      have hq1' : (QuotientGroup.mk z : ℚ_[2]ˣ ⧸ (powMonoidHom (α := ℚ_[2]ˣ) 2).range) = 1 :=
        Additive.ofMul.injective hq0
      exact (QuotientGroup.eq_one_iff z).mp hq1'
    · rintro ⟨w, rfl⟩
      rw [MonoidHom.mem_ker]; change padicTwoCoordHom (w ^ 2) = 1
      rw [sq, map_mul]
      apply Multiplicative.toAdd.injective
      have h2 : ∀ t : ZMod 2, t + t = 0 := by decide
      exact Prod.ext (h2 _) (Prod.ext (h2 _) (h2 _))
  rw [hsq_ker] at hker
  obtain ⟨w, hw⟩ := hker
  refine ⟨w, ?_⟩
  change w ^ 2 = x * y⁻¹ at hw
  calc x = (x * y⁻¹) * y := (inv_mul_cancel_right x y).symm
    _ = w ^ 2 * y := by rw [hw]
    _ = y * w ^ 2 := mul_comm _ _

/-- Helper: any integer `m ≡ 1 (mod 8)` is a square in `ℚ_[2]` (via `exists_sq_padicInt_two`). -/
theorem exists_sq_padic_two_of_mod_eight {m : ℤ} (hm : (m : ZMod 8) = 1) :
    ∃ w : ℚ_[2], w ^ 2 = (m : ℚ_[2]) := by
  have hm_unit : IsUnit (m : ℤ_[2]) := by
    by_contra hnu
    have hker : (m : ℤ_[2]) ∈ RingHom.ker (PadicInt.toZModPow 1) := by
      rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
        IsLocalRing.mem_maximalIdeal]; exact hnu
    have hcast := PadicInt.cast_toZModPow 1 3 (by norm_num) (m : ℤ_[2])
    have hm3 : (PadicInt.toZModPow 3 (m : ℤ_[2]) : ZMod 8) = 1 := by
      rw [map_intCast]; exact hm
    have h1 : (PadicInt.toZModPow 1 (m : ℤ_[2]) : ZMod (2 ^ 1)) = 1 := by
      rw [← hcast, hm3]; rfl
    change PadicInt.toZModPow 1 (m : ℤ_[2]) = 0 at hker
    rw [h1] at hker
    exact (by decide : (1 : ZMod (2 ^ 1)) ≠ 0) hker
  have hm3 : (PadicInt.toZModPow 3 (hm_unit.unit : ℤ_[2]) : ZMod 8) = 1 := by
    change (PadicInt.toZModPow 3 (m : ℤ_[2]) : ZMod 8) = 1
    rw [map_intCast]; exact hm
  obtain ⟨z, hz⟩ := exists_sq_padicInt_two hm_unit.unit hm3
  refine ⟨(z : ℚ_[2]), ?_⟩
  have hcoe := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hz
  simpa using hcoe

/-- Concrete `2`-adic representative table `{1, -1, 5, -5, 2, -2, 10, -10}` indexed by `Fin 8`. -/
def repTwoVal : Fin 8 → ℤ
  | 0 => 1
  | 1 => -1
  | 2 => 5
  | 3 => -5
  | 4 => 2
  | 5 => -2
  | 6 => 10
  | 7 => -10

def repTwoCoords : Fin 8 → ZMod 2 × ZMod 2 × ZMod 2
  | 0 => (0, 0, 0)
  | 1 => (0, 1, 0)
  | 2 => (0, 0, 1)
  | 3 => (0, 1, 1)
  | 4 => (1, 0, 0)
  | 5 => (1, 1, 0)
  | 6 => (1, 0, 1)
  | 7 => (1, 1, 1)

def repTwoUnit (i : Fin 8) : ℚ_[2]ˣ :=
  Units.mk0 (repTwoVal i : ℚ_[2]) (by fin_cases i <;> norm_num [repTwoVal])

theorem padicTwoCoordHom_repTwoUnit (i : Fin 8) :
    Multiplicative.toAdd (padicTwoCoordHom (repTwoUnit i)) = repTwoCoords i := by
  have hq : ∀ (q : ℚˣ), ((q : ℚ) : ℚ_[2]) = (repTwoUnit i : ℚ_[2]) →
      Multiplicative.toAdd (padicTwoCoordHom (repTwoUnit i)) = twoCoords q := by
    intro q hq
    have hu : repTwoUnit i = ratToPadicUnit 2 q := Units.ext hq.symm
    rw [hu, padicTwoCoordHom_ratToPadicUnit]
  let g1 : ℚˣ := 1
  let gm1 : ℚˣ := -1
  let g5 : ℚˣ := Units.mk0 5 (by norm_num)
  let gm5 : ℚˣ := Units.mk0 (-5) (by norm_num)
  let g2 : ℚˣ := primeUnit 2 Nat.prime_two
  let gm2 : ℚˣ := -(primeUnit 2 Nat.prime_two)
  let g10 : ℚˣ := primeUnit 2 Nat.prime_two * Units.mk0 5 (by norm_num)
  let gm10 : ℚˣ := -(primeUnit 2 Nat.prime_two * Units.mk0 5 (by norm_num))
  have hc5 : twoCoords g5 = (0, 0, 1) := by
    have hv : padicValRat 2 (g5 : ℚ) = 0 := by
      change padicValRat 2 (5 : ℚ) = 0
      rw [show (5 : ℚ) = ((5 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
        padicValNat.eq_zero_of_not_dvd (by norm_num), Nat.cast_zero]
    unfold twoCoords
    rw [pUnit_of_val_zero 2 Nat.prime_two hv, hv, Int.cast_zero]
    have hr : redMod8 (g5 : ℚ) = 5 := by
      change redMod8 ((5 : ℕ) : ℚ) = 5; rw [redMod8_natCast]; decide
    rw [hr]; decide
  fin_cases i
  · rw [hq g1 (by simp [g1, repTwoUnit, repTwoVal]), twoCoords_one]; rfl
  · rw [hq gm1 (by simp [gm1, repTwoUnit, repTwoVal]), twoCoords_neg_one]; rfl
  · rw [hq g5 (by simp [g5, repTwoUnit, repTwoVal]), hc5]; rfl
  · have hgm5 : gm5 = (-1 : ℚˣ) * g5 := Units.ext (by simp [gm5, g5])
    rw [hq gm5 (by simp [gm5, repTwoUnit, repTwoVal]), hgm5, twoCoords_mul, twoCoords_neg_one, hc5]
    decide
  · rw [hq g2 (by simp [g2, repTwoUnit, repTwoVal]), twoCoords_two]; rfl
  · have hgm2 : gm2 = (-1 : ℚˣ) * g2 := Units.ext (by simp [gm2, g2])
    rw [hq gm2 (by simp [gm2, repTwoUnit, repTwoVal]), hgm2, twoCoords_mul, twoCoords_neg_one,
      twoCoords_two]
    decide
  · have hg10 : g10 = g2 * g5 := rfl
    rw [hq g10 (by simp [g10, repTwoUnit, repTwoVal]; norm_num), hg10, twoCoords_mul,
      twoCoords_two, hc5]
    decide
  · have hgm10 : gm10 = (-1 : ℚˣ) * (g2 * g5) := Units.ext (by simp [gm10, g2, g5])
    rw [hq gm10 (by simp [gm10, repTwoUnit, repTwoVal]; norm_num), hgm10, twoCoords_mul,
      twoCoords_mul, twoCoords_neg_one, twoCoords_two, hc5]
    decide

/-- Explicit solver for all 64 pairs `(repTwoUnit i, repTwoUnit j)` with `(x, y)_2 = 1`. -/
private theorem repTwoUnit_sol_of_hilbert_eq_one (i j : Fin 8)
    (hsym : hilbertSymPadicTwo (repTwoUnit i) (repTwoUnit j) = 1) :
    ∃ u v w : ℚ_[2], (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧
      (repTwoUnit i : ℚ_[2]) * u ^ 2 + (repTwoUnit j : ℚ_[2]) * v ^ 2 = w ^ 2 := by
  have hsq7 : ∃ w : ℚ_[2], w ^ 2 = (-7 : ℚ_[2]) := by
    simpa using exists_sq_padic_two_of_mod_eight (m := -7) (by decide)
  have hsq15 : ∃ w : ℚ_[2], w ^ 2 = (-15 : ℚ_[2]) := by
    simpa using exists_sq_padic_two_of_mod_eight (m := -15) (by decide)
  have hsym' : (repTwoCoords i).2.1 * (repTwoCoords j).2.1 +
      (repTwoCoords i).1 * (repTwoCoords j).2.2 +
      (repTwoCoords j).1 * (repTwoCoords i).2.2 = 0 := by
    unfold hilbertSymPadicTwo at hsym
    rw [padicTwoCoordHom_repTwoUnit i, padicTwoCoordHom_repTwoUnit j] at hsym
    exact (negOnePowZMod2_eq_one_iff _).mp hsym
  -- Handle all 64 cases; the 28 cases with Hilbert symbol = -1 close immediately by `decide`!
  fin_cases i <;> fin_cases j <;>
    (try exact absurd hsym' (by decide)) <;>
    simp only [repTwoUnit, repTwoVal, Units.val_mk0, Int.cast_neg, Int.cast_one, Int.cast_ofNat]
  -- Remaining 36 cases (all have Hilbert symbol = 1):
  -- i = 0 (1): j = 0..7
  · exact ⟨1, 0, 1, Or.inl one_ne_zero, by ring⟩
  · exact ⟨1, 0, 1, Or.inl one_ne_zero, by ring⟩
  · exact ⟨1, 0, 1, Or.inl one_ne_zero, by ring⟩
  · exact ⟨1, 0, 1, Or.inl one_ne_zero, by ring⟩
  · exact ⟨1, 0, 1, Or.inl one_ne_zero, by ring⟩
  · exact ⟨1, 0, 1, Or.inl one_ne_zero, by ring⟩
  · exact ⟨1, 0, 1, Or.inl one_ne_zero, by ring⟩
  · exact ⟨1, 0, 1, Or.inl one_ne_zero, by ring⟩
  -- i = 1 (-1): j ∈ {0, 2, 4, 6} = {1, 5, 2, 10}
  · exact ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero), by ring⟩
  · exact ⟨2, 1, 1, Or.inr (Or.inl one_ne_zero), by ring⟩
  · exact ⟨1, 1, 1, Or.inr (Or.inl one_ne_zero), by ring⟩
  · exact ⟨3, 1, 1, Or.inr (Or.inl one_ne_zero), by ring⟩
  -- i = 2 (5): j ∈ {0, 1, 2, 3} = {1, -1, 5, -5}
  · exact ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero), by ring⟩
  · exact ⟨1, 2, 1, Or.inl one_ne_zero, by ring⟩
  · exact ⟨1, 2, 5, Or.inl one_ne_zero, by ring⟩
  · exact ⟨1, 1, 0, Or.inl one_ne_zero, by ring⟩
  -- i = 3 (-5): j ∈ {0, 2, 5, 7} = {1, 5, -2, -10}
  · exact ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero), by ring⟩
  · exact ⟨1, 1, 0, Or.inl one_ne_zero, by ring⟩
  · obtain ⟨w, hw⟩ := hsq7; exact ⟨1, 1, w, Or.inl one_ne_zero, by rw [hw]; ring⟩
  · obtain ⟨w, hw⟩ := hsq15; exact ⟨1, 1, w, Or.inl one_ne_zero, by rw [hw]; ring⟩
  -- i = 4 (2): j ∈ {0, 1, 4, 5} = {1, -1, 2, -2}
  · exact ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero), by ring⟩
  · exact ⟨1, 1, 1, Or.inl one_ne_zero, by ring⟩
  · exact ⟨1, 1, 2, Or.inl one_ne_zero, by ring⟩
  · exact ⟨1, 1, 0, Or.inl one_ne_zero, by ring⟩
  -- i = 5 (-2): j ∈ {0, 3, 4, 7} = {1, -5, 2, -10}
  · exact ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero), by ring⟩
  · obtain ⟨w, hw⟩ := hsq7; exact ⟨1, 1, w, Or.inl one_ne_zero, by rw [hw]; ring⟩
  · exact ⟨1, 1, 0, Or.inl one_ne_zero, by ring⟩
  · obtain ⟨w, hw⟩ := hsq7; exact ⟨3, 1, 2 * w, Or.inr (Or.inl one_ne_zero), by rw [mul_pow, hw]; ring⟩
  -- i = 6 (10): j ∈ {0, 1, 6, 7} = {1, -1, 10, -10}
  · exact ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero), by ring⟩
  · exact ⟨1, 3, 1, Or.inl one_ne_zero, by ring⟩
  · exact ⟨1, 3, 10, Or.inl one_ne_zero, by ring⟩
  · exact ⟨1, 1, 0, Or.inl one_ne_zero, by ring⟩
  -- i = 7 (-10): j ∈ {0, 3, 5, 6} = {1, -5, -2, 10}
  · exact ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero), by ring⟩
  · obtain ⟨w, hw⟩ := hsq15; exact ⟨1, 1, w, Or.inl one_ne_zero, by rw [hw]; ring⟩
  · obtain ⟨w, hw⟩ := hsq7; exact ⟨1, 3, 2 * w, Or.inl one_ne_zero, by rw [mul_pow, hw]; ring⟩
  · exact ⟨1, 1, 0, Or.inl one_ne_zero, by ring⟩

/-- **Exact `2`-adic Solvability Criterion**:
`hilbertSymPadicTwo x y = 1 ↔ ∃ u v w : ℚ_[2], (u, v, w) ≠ 0 ∧ x u² + y v² = w²`. -/
theorem hilbertSymPadicTwo_eq_one_iff_norm_form (x y : ℚ_[2]ˣ) :
    hilbertSymPadicTwo x y = 1 ↔
      ∃ u v w : ℚ_[2], (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧
        (x : ℚ_[2]) * u ^ 2 + (y : ℚ_[2]) * v ^ 2 = w ^ 2 := by
  have h2ne : (2 : ℚ_[2]) ≠ 0 := by norm_num
  constructor
  · intro hsym
    have hrep : ∀ z : ℚ_[2]ˣ, ∃ (i : Fin 8) (w : ℚ_[2]ˣ), z = repTwoUnit i * w ^ 2 := by
      intro z
      have hex : ∃ i : Fin 8, repTwoCoords i = Multiplicative.toAdd (padicTwoCoordHom z) := by
        rcases Multiplicative.toAdd (padicTwoCoordHom z) with ⟨a, b, c⟩
        rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
          rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
          rcases zmod2_eq_zero_or_one c with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨3, rfl⟩
        · exact ⟨4, rfl⟩
        · exact ⟨6, rfl⟩
        · exact ⟨5, rfl⟩
        · exact ⟨7, rfl⟩
      obtain ⟨i, hi⟩ := hex
      obtain ⟨w, hw⟩ := eq_mul_sq_of_padicTwoCoordHom_eq (x := z) (y := repTwoUnit i) (by
        apply Multiplicative.toAdd.injective
        rw [padicTwoCoordHom_repTwoUnit i, hi])
      exact ⟨i, w, hw⟩
    obtain ⟨i, wx, rfl⟩ := hrep x
    obtain ⟨j, wy, rfl⟩ := hrep y
    rw [hilbertSymPadicTwo_mul_left, hilbertSymPadicTwo_sq_left, mul_one,
      hilbertSymPadicTwo_mul_right, hilbertSymPadicTwo_sq_right, mul_one] at hsym
    obtain ⟨u, v, w, hne, heq⟩ := repTwoUnit_sol_of_hilbert_eq_one i j hsym
    refine ⟨u / (wx : ℚ_[2]), v / (wy : ℚ_[2]), w, ?_, ?_⟩
    · rcases hne with hu | hv | hw
      · exact Or.inl (div_ne_zero hu wx.ne_zero)
      · exact Or.inr (Or.inl (div_ne_zero hv wy.ne_zero))
      · exact Or.inr (Or.inr hw)
    · simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      field_simp [wx.ne_zero, wy.ne_zero]
      linear_combination heq
  · intro hsol
    rw [norm_form_iff_binary_norm h2ne x.ne_zero] at hsol
    exact hilbertSymPadicTwo_eq_one_of_binary_norm hsol

/-- **Hilbert Symbol Characterization of `ℚ_[2]`-Isotropy**:
`(-a*c, -b*c)_2 = 1 ↔ HasTernaryZeroPadic 2 a b c`! -/
theorem hilbertSymTwo_ternary_iff (a b c : ℚˣ) :
    hilbertSymTwo (-a * c) (-b * c) = 1 ↔ @HasTernaryZeroPadic 2 ⟨Nat.prime_two⟩ a b c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : ((c : ℚ) : ℚ_[2]) ≠ 0 := Rat.cast_ne_zero.mpr c.ne_zero
  rw [← hilbertSymPadicTwo_ratCast (-a * c) (-b * c),
    hilbertSymPadicTwo_eq_one_iff_norm_form]
  change (∃ u v w : ℚ_[2], (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧
      (-((a : ℚ) : ℚ_[2]) * ((c : ℚ) : ℚ_[2])) * u ^ 2 +
        (-((b : ℚ) : ℚ_[2]) * ((c : ℚ) : ℚ_[2])) * v ^ 2 = w ^ 2) ↔
    HasTernaryZeroK ((a : ℚ) : ℚ_[2]) ((b : ℚ) : ℚ_[2]) ((c : ℚ) : ℚ_[2])
  exact (hasTernaryZeroK_iff_norm_form hc).symm

/-- **Unified Local Hilbert Symbol Characterization at EVERY Place `v : QPlace` of `ℚ`**:
`( -a*c, -b*c )_v = 1 ↔ HasTernaryZeroAt v a b c`! -/
theorem hilbertSymAt_ternary_iff (v : QPlace) (a b c : ℚˣ) :
    hilbertSymAt v (-a * c) (-b * c) = 1 ↔ HasTernaryZeroAt v a b c := by
  cases v with
  | inf => exact hilbertSymInf_ternary_iff a b c
  | two => exact hilbertSymTwo_ternary_iff a b c
  | odd p =>
    have : Fact p.1.Prime := ⟨p.2.1⟩
    exact hilbertSymOdd_ternary_iff p.1 p.2.2 a b c

end LocalSolvability

/-! ## Section 3: Unconditional Legendre's Three-Variable Theorem & Hasse–Minkowski over `ℚ` -/

section LegendreAndHasseMinkowski

/-! ### 3A. Legendre's Three-Variable Theorem via Dirichlet Pigeonhole -/

/-- A squarefree natural number `n > 1` is never a square, so `(Nat.sqrt n)^2 < n`. -/
theorem sq_sqrt_lt_of_squarefree {n : ℕ} (h1 : 1 < n) (hsq : Squarefree n) :
    (Nat.sqrt n) ^ 2 < n := by
  have hle : (Nat.sqrt n) ^ 2 ≤ n := by rw [sq]; exact Nat.sqrt_le n
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hdvd : Nat.sqrt n * Nat.sqrt n ∣ n := by rw [← sq, heq]
  have hu : IsUnit (Nat.sqrt n) := hsq (Nat.sqrt n) hdvd
  have hsqrt1 : Nat.sqrt n = 1 := Nat.isUnit_iff.mp hu
  rw [hsqrt1, one_pow] at heq
  omega

/-- **Core Positive Legendre Theorem**: for positive, pairwise coprime, squarefree `A, B, C : ℕ`,
if `B*C`, `C*A`, `-A*B` are squares modulo `A`, `B`, `C` respectively, then
`A x² + B y² = C z²` has a nontrivial integer solution!
Proved unconditionally via Dirichlet pigeonhole + the algebraic descent identity
`A(xz + By)² + B(yz - Ax)² = (Ax² + By²)(z² + AB)`. -/
theorem legendre_ternary_pos {A B C : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAB : Nat.Coprime A B) (hBC : Nat.Coprime B C) (hCA : Nat.Coprime C A)
    (hsqA : Squarefree A) (hsqB : Squarefree B) (hsqC : Squarefree C)
    {uA uB uC : ℤ}
    (huA : (A : ℤ) ∣ uA ^ 2 - (B : ℤ) * (C : ℤ))
    (huB : (B : ℤ) ∣ uB ^ 2 - (C : ℤ) * (A : ℤ))
    (huC : (C : ℤ) ∣ uC ^ 2 + (A : ℤ) * (B : ℤ)) :
    ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      (A : ℤ) * x ^ 2 + (B : ℤ) * y ^ 2 - (C : ℤ) * z ^ 2 = 0 := by
  by_cases hAB1 : A = 1 ∧ B = 1
  · rcases hAB1 with ⟨rfl, rfl⟩
    by_cases hC1 : C = 1
    · subst hC1
      exact ⟨1, 0, 1, Or.inl one_ne_zero, by norm_num⟩
    · have hCgt : 1 < C := by omega
      have : NeZero C := ⟨hC.ne'⟩
      let S : ℕ := Nat.sqrt C
      have hS_lt : S ^ 2 < C := sq_sqrt_lt_of_squarefree hCgt hsqC
      have hC_lt : C < (S + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt C
      let f : Fin (S + 1) × Fin (S + 1) → ZMod C := fun p =>
        ((p.1.1 : ℕ) : ZMod C) - (uC : ZMod C) * ((p.2.1 : ℕ) : ZMod C)
      have hcard : Fintype.card (ZMod C) < Fintype.card (Fin (S + 1) × Fin (S + 1)) := by
        rw [ZMod.card C, Fintype.card_prod, Fintype.card_fin, ← sq]
        exact hC_lt
      obtain ⟨p₁, p₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
      let x : ℤ := (p₁.1.1 : ℤ) - (p₂.1.1 : ℤ)
      let y : ℤ := (p₁.2.1 : ℤ) - (p₂.2.1 : ℤ)
      have hxy_ne : x ≠ 0 ∨ y ≠ 0 := by
        by_contra hboth
        push Not at hboth
        apply hne
        exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
      have hx_sq : x ^ 2 ≤ (S : ℤ) ^ 2 := by
        have h1 : |x| ≤ (S : ℤ) := by
          have hp1 := p₁.1.2; have hp2 := p₂.1.2
          rw [abs_le]; omega
        nlinarith [sq_abs x, abs_nonneg x]
      have hy_sq : y ^ 2 ≤ (S : ℤ) ^ 2 := by
        have h1 : |y| ≤ (S : ℤ) := by
          have hp1 := p₁.2.2; have hp2 := p₂.2.2
          rw [abs_le]; omega
        nlinarith [sq_abs y, abs_nonneg y]
      have hmod : ((x - uC * y : ℤ) : ZMod C) = 0 := by
        have hsub : f p₁ - f p₂ = 0 := sub_eq_zero.mpr heq
        dsimp only [f] at hsub
        dsimp only [x, y]
        push_cast
        linear_combination hsub
      have hdvd1 : (C : ℤ) ∣ x - uC * y := (ZMod.intCast_zmod_eq_zero_iff_dvd _ C).mp hmod
      have hdvd_sum : (C : ℤ) ∣ x ^ 2 + y ^ 2 := by
        have hid : x ^ 2 + y ^ 2 = (x - uC * y) * (x + uC * y) + (uC ^ 2 + (1 : ℕ) * (1 : ℕ)) * y ^ 2 := by
          push_cast; ring
        rw [hid]
        exact dvd_add (dvd_mul_of_dvd_left hdvd1 _) (dvd_mul_of_dvd_left huC _)
      obtain ⟨k, hk⟩ := hdvd_sum
      have hpos_sum : 0 < x ^ 2 + y ^ 2 := by
        rcases hxy_ne with hx | hy
        · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg y]
        · nlinarith [sq_pos_of_ne_zero hy, sq_nonneg x]
      have hlt_sum : x ^ 2 + y ^ 2 < 2 * (C : ℤ) := by
        have hS_lt' : (S : ℤ) ^ 2 < (C : ℤ) := by exact_mod_cast hS_lt
        linarith
      have hk1 : k = 1 := by nlinarith
      subst hk1
      refine ⟨x, y, 1, Or.inr (Or.inr one_ne_zero), ?_⟩
      push_cast; linarith
  · have : NeZero A := ⟨hA.ne'⟩
    have : NeZero B := ⟨hB.ne'⟩
    have : NeZero C := ⟨hC.ne'⟩
    let X : ℕ := Nat.sqrt (B * C)
    let Y : ℕ := Nat.sqrt (C * A)
    let Z : ℕ := Nat.sqrt (A * B)
    have hX_le : X ^ 2 ≤ B * C := by rw [sq]; exact Nat.sqrt_le (B * C)
    have hY_le : Y ^ 2 ≤ C * A := by rw [sq]; exact Nat.sqrt_le (C * A)
    have hAB_gt1 : 1 < A * B := by
      rcases eq_or_lt_of_le (show 1 ≤ A by omega) with rfl | hAgt
      · have hBgt : 1 < B := by omega
        omega
      · nlinarith
    have hsqAB : Squarefree (A * B) := Nat.squarefree_mul_iff.mpr ⟨hAB, hsqA, hsqB⟩
    have hZ_lt : Z ^ 2 < A * B := sq_sqrt_lt_of_squarefree hAB_gt1 hsqAB
    have hupper_strict : (A : ℤ) * (X : ℤ) ^ 2 + (B : ℤ) * (Y : ℤ) ^ 2 <
        2 * (A : ℤ) * (B : ℤ) * (C : ℤ) := by
      have hX_le' : (X : ℤ) ^ 2 ≤ (B : ℤ) * (C : ℤ) := by exact_mod_cast hX_le
      have hY_le' : (Y : ℤ) ^ 2 ≤ (C : ℤ) * (A : ℤ) := by exact_mod_cast hY_le
      by_cases hA1 : 1 < A
      · have hCA_gt1 : 1 < C * A := by nlinarith
        have hsqCA : Squarefree (C * A) := Nat.squarefree_mul_iff.mpr ⟨hCA, hsqC, hsqA⟩
        have hY_lt : (Y : ℤ) ^ 2 < (C : ℤ) * (A : ℤ) := by
          exact_mod_cast sq_sqrt_lt_of_squarefree hCA_gt1 hsqCA
        nlinarith
      · have hB1 : 1 < B := by omega
        have hBC_gt1 : 1 < B * C := by nlinarith
        have hsqBC : Squarefree (B * C) := Nat.squarefree_mul_iff.mpr ⟨hBC, hsqB, hsqC⟩
        have hX_lt : (X : ℤ) ^ 2 < (B : ℤ) * (C : ℤ) := by
          exact_mod_cast sq_sqrt_lt_of_squarefree hBC_gt1 hsqBC
        nlinarith
    have hcard_nat : A * B * C < (X + 1) * (Y + 1) * (Z + 1) := by
      have h1 : B * C < (X + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt (B * C)
      have h2 : C * A < (Y + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt (C * A)
      have h3 : A * B < (Z + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt (A * B)
      have hsq_lt : (A * B * C) ^ 2 < ((X + 1) * (Y + 1) * (Z + 1)) ^ 2 := by
        calc (A * B * C) ^ 2 = (B * C) * (C * A) * (A * B) := by ring
          _ < (X + 1) ^ 2 * (Y + 1) ^ 2 * (Z + 1) ^ 2 :=
              Nat.mul_lt_mul_of_lt_of_lt (Nat.mul_lt_mul_of_lt_of_lt h1 h2) h3
          _ = ((X + 1) * (Y + 1) * (Z + 1)) ^ 2 := by ring
      by_contra hle
      push Not at hle
      have : ((X + 1) * (Y + 1) * (Z + 1)) ^ 2 ≤ (A * B * C) ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    let f : Fin (X + 1) × Fin (Y + 1) × Fin (Z + 1) → ZMod A × ZMod B × ZMod C := fun p =>
      ((B : ZMod A) * ((p.2.1.1 : ℕ) : ZMod A) - (uA : ZMod A) * ((p.2.2.1 : ℕ) : ZMod A),
       (A : ZMod B) * ((p.1.1 : ℕ) : ZMod B) - (uB : ZMod B) * ((p.2.2.1 : ℕ) : ZMod B),
       (A : ZMod C) * ((p.1.1 : ℕ) : ZMod C) - (uC : ZMod C) * ((p.2.1.1 : ℕ) : ZMod C))
    have hcard : Fintype.card (ZMod A × ZMod B × ZMod C) <
        Fintype.card (Fin (X + 1) × Fin (Y + 1) × Fin (Z + 1)) := by
      simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card]
      simpa [mul_assoc] using hcard_nat
    obtain ⟨p₁, p₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
    let x : ℤ := (p₁.1.1 : ℤ) - (p₂.1.1 : ℤ)
    let y : ℤ := (p₁.2.1.1 : ℤ) - (p₂.2.1.1 : ℤ)
    let z : ℤ := (p₁.2.2.1 : ℤ) - (p₂.2.2.1 : ℤ)
    have hxyz_ne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hne
      exact Prod.ext (Fin.ext (by omega))
        (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
    have hx_sq : x ^ 2 ≤ (X : ℤ) ^ 2 := by
      have h1 : |x| ≤ (X : ℤ) := by
        have hp1 := p₁.1.2; have hp2 := p₂.1.2; rw [abs_le]; omega
      nlinarith [sq_abs x, abs_nonneg x]
    have hy_sq : y ^ 2 ≤ (Y : ℤ) ^ 2 := by
      have h1 : |y| ≤ (Y : ℤ) := by
        have hp1 := p₁.2.1.2; have hp2 := p₂.2.1.2; rw [abs_le]; omega
      nlinarith [sq_abs y, abs_nonneg y]
    have hz_sq : z ^ 2 ≤ (Z : ℤ) ^ 2 := by
      have h1 : |z| ≤ (Z : ℤ) := by
        have hp1 := p₁.2.2.2; have hp2 := p₂.2.2.2; rw [abs_le]; omega
      nlinarith [sq_abs z, abs_nonneg z]
    set M : ℤ := (A : ℤ) * x ^ 2 + (B : ℤ) * y ^ 2 - (C : ℤ) * z ^ 2
    -- Divisibility by A, B, C
    have hdvdA : (A : ℤ) ∣ M := by
      have h1 : (((B : ℤ) * y - uA * z : ℤ) : ZMod A) = 0 := by
        have hsub := sub_eq_zero.mpr (congrArg Prod.fst heq)
        dsimp only [f] at hsub
        dsimp only [y, z]; push_cast; linear_combination hsub
      have h2 : (A : ℤ) ∣ (B : ℤ) * y - uA * z := (ZMod.intCast_zmod_eq_zero_iff_dvd _ A).mp h1
      have h3 : (A : ℤ) ∣ (B : ℤ) * ((B : ℤ) * y ^ 2 - (C : ℤ) * z ^ 2) := by
        have hid : (B : ℤ) * ((B : ℤ) * y ^ 2 - (C : ℤ) * z ^ 2) =
            ((B : ℤ) * y - uA * z) * ((B : ℤ) * y + uA * z) + (uA ^ 2 - (B : ℤ) * (C : ℤ)) * z ^ 2 := by
          ring
        rw [hid]
        exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_left huA _)
      have hcopAB : IsCoprime (A : ℤ) (B : ℤ) := Int.isCoprime_iff_nat_coprime.mpr hAB
      have h4 : (A : ℤ) ∣ (B : ℤ) * y ^ 2 - (C : ℤ) * z ^ 2 := hcopAB.dvd_of_dvd_mul_left h3
      have hM : M = (A : ℤ) * x ^ 2 + ((B : ℤ) * y ^ 2 - (C : ℤ) * z ^ 2) := by dsimp [M]; ring
      rw [hM]; exact dvd_add (dvd_mul_right _ _) h4
    have hdvdB : (B : ℤ) ∣ M := by
      have h1 : (((A : ℤ) * x - uB * z : ℤ) : ZMod B) = 0 := by
        have hsub := sub_eq_zero.mpr (congrArg (fun q => q.2.1) heq)
        dsimp only [f] at hsub
        dsimp only [x, z]; push_cast; linear_combination hsub
      have h2 : (B : ℤ) ∣ (A : ℤ) * x - uB * z := (ZMod.intCast_zmod_eq_zero_iff_dvd _ B).mp h1
      have h3 : (B : ℤ) ∣ (A : ℤ) * ((A : ℤ) * x ^ 2 - (C : ℤ) * z ^ 2) := by
        have hid : (A : ℤ) * ((A : ℤ) * x ^ 2 - (C : ℤ) * z ^ 2) =
            ((A : ℤ) * x - uB * z) * ((A : ℤ) * x + uB * z) + (uB ^ 2 - (C : ℤ) * (A : ℤ)) * z ^ 2 := by
          ring
        rw [hid]
        exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_left huB _)
      have hcopBA : IsCoprime (B : ℤ) (A : ℤ) := Int.isCoprime_iff_nat_coprime.mpr hAB.symm
      have h4 : (B : ℤ) ∣ (A : ℤ) * x ^ 2 - (C : ℤ) * z ^ 2 := hcopBA.dvd_of_dvd_mul_left h3
      have hM : M = (B : ℤ) * y ^ 2 + ((A : ℤ) * x ^ 2 - (C : ℤ) * z ^ 2) := by dsimp [M]; ring
      rw [hM]; exact dvd_add (dvd_mul_right _ _) h4
    have hdvdC : (C : ℤ) ∣ M := by
      have h1 : (((A : ℤ) * x - uC * y : ℤ) : ZMod C) = 0 := by
        have hsub := sub_eq_zero.mpr (congrArg (fun q => q.2.2) heq)
        dsimp only [f] at hsub
        dsimp only [x, y]; push_cast; linear_combination hsub
      have h2 : (C : ℤ) ∣ (A : ℤ) * x - uC * y := (ZMod.intCast_zmod_eq_zero_iff_dvd _ C).mp h1
      have h3 : (C : ℤ) ∣ (A : ℤ) * ((A : ℤ) * x ^ 2 + (B : ℤ) * y ^ 2) := by
        have hid : (A : ℤ) * ((A : ℤ) * x ^ 2 + (B : ℤ) * y ^ 2) =
            ((A : ℤ) * x - uC * y) * ((A : ℤ) * x + uC * y) + (uC ^ 2 + (A : ℤ) * (B : ℤ)) * y ^ 2 := by
          ring
        rw [hid]
        exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_left huC _)
      have hcopCA : IsCoprime (C : ℤ) (A : ℤ) := Int.isCoprime_iff_nat_coprime.mpr hCA
      have h4 : (C : ℤ) ∣ (A : ℤ) * x ^ 2 + (B : ℤ) * y ^ 2 := hcopCA.dvd_of_dvd_mul_left h3
      have hM : M = ((A : ℤ) * x ^ 2 + (B : ℤ) * y ^ 2) - (C : ℤ) * z ^ 2 := rfl
      rw [hM]; exact dvd_sub h4 (dvd_mul_right _ _)
    have hdvdABC : (A : ℤ) * (B : ℤ) * (C : ℤ) ∣ M := by
      have hcopAB : IsCoprime (A : ℤ) (B : ℤ) := Int.isCoprime_iff_nat_coprime.mpr hAB
      have hcopAC : IsCoprime (A : ℤ) (C : ℤ) := Int.isCoprime_iff_nat_coprime.mpr hCA.symm
      have hcopBC : IsCoprime (B : ℤ) (C : ℤ) := Int.isCoprime_iff_nat_coprime.mpr hBC
      have hcopABC : IsCoprime ((A : ℤ) * (B : ℤ)) (C : ℤ) := hcopAC.mul_left hcopBC
      exact hcopABC.mul_dvd (hcopAB.mul_dvd hdvdA hdvdB) hdvdC
    obtain ⟨k, hk⟩ := hdvdABC
    have hZ_lt' : (Z : ℤ) ^ 2 < (A : ℤ) * (B : ℤ) := by exact_mod_cast hZ_lt
    have hM_gt : -((A : ℤ) * (B : ℤ) * (C : ℤ)) < M := by
      have hA0 : (0 : ℤ) < A := by exact_mod_cast hA
      have hB0 : (0 : ℤ) < B := by exact_mod_cast hB
      have hC0 : (0 : ℤ) < C := by exact_mod_cast hC
      nlinarith [sq_nonneg x, sq_nonneg y]
    have hM_lt : M < 2 * ((A : ℤ) * (B : ℤ) * (C : ℤ)) := by
      have hA0 : (0 : ℤ) < A := by exact_mod_cast hA
      have hB0 : (0 : ℤ) < B := by exact_mod_cast hB
      have hC0 : (0 : ℤ) < C := by exact_mod_cast hC
      nlinarith [sq_nonneg z]
    have hABC_pos : (0 : ℤ) < (A : ℤ) * (B : ℤ) * (C : ℤ) := by positivity
    have hk_cases : k = 0 ∨ k = 1 := by
      have hk_gt : -1 < k := by nlinarith
      have hk_lt : k < 2 := by nlinarith
      omega
    rcases hk_cases with rfl | rfl
    · rw [mul_zero] at hk
      exact ⟨x, y, z, hxyz_ne, hk⟩
    · rw [mul_one] at hk
      -- Algebraic identity: A(xz + By)² + B(yz - Ax)² = (Ax² + By²)(z² + AB) = C(z² + AB)²
      let X' : ℤ := x * z + (B : ℤ) * y
      let Y' : ℤ := y * z - (A : ℤ) * x
      let Z' : ℤ := z ^ 2 + (A : ℤ) * (B : ℤ)
      have hZ'_pos : (0 : ℤ) < Z' := by
        have hAB_pos : (0 : ℤ) < (A : ℤ) * (B : ℤ) := by positivity
        nlinarith [sq_nonneg z]
      refine ⟨X', Y', Z', Or.inr (Or.inr hZ'_pos.ne'), ?_⟩
      have hsum : (A : ℤ) * x ^ 2 + (B : ℤ) * y ^ 2 = (C : ℤ) * (z ^ 2 + (A : ℤ) * (B : ℤ)) := by
        dsimp [M] at hk; linarith
      dsimp only [X', Y', Z']
      linear_combination (z ^ 2 + (A : ℤ) * (B : ℤ)) * hsum

/-! ### 3B. CRT Square Lifting & Extracting Legendre Congruences from Hilbert Symbols -/

/-- CRT square-lifting for positive squarefree `n : ℕ`: `m` is a square mod `n` iff `m` is a
square mod every prime `p ∣ n`. -/
theorem isSquare_zmod_of_forall_prime_dvd :
    ∀ (n : ℕ), 0 < n → Squarefree n → ∀ (m : ℤ),
      (∀ p : ℕ, p.Prime → p ∣ n → IsSquare (m : ZMod p)) →
      IsSquare (m : ZMod n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hsq m hprimes
    by_cases h1 : n = 1
    · subst h1
      exact ⟨0, Subsingleton.elim _ _⟩
    · have hgt : 1 < n := by omega
      let p := n.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpdvd : p ∣ n := Nat.minFac_dvd n
      let k := n / p
      have hnk : n = p * k := (Nat.mul_div_cancel' hpdvd).symm
      rw [hnk] at hsq
      obtain ⟨hcop, _, hsqk⟩ := Nat.squarefree_mul_iff.mp hsq
      have hk_pos : 0 < k := Nat.div_pos (Nat.le_of_dvd hn hpdvd) hp.pos
      have hk_lt : k < n := Nat.div_lt_self hn hp.one_lt
      obtain ⟨r, hr⟩ := hprimes p hp hpdvd
      obtain ⟨s, hs⟩ := ih k hk_lt hk_pos hsqk m (fun q hq hqk =>
        hprimes q hq (hnk ▸ dvd_mul_of_dvd_right hqk p))
      let e : ZMod (p * k) ≃+* ZMod p × ZMod k := ZMod.chineseRemainder hcop
      have hm_map : e (m : ZMod (p * k)) = ((m : ZMod p), (m : ZMod k)) := by
        rw [map_intCast]; rfl
      rw [hnk]
      refine ⟨e.symm (r, s), ?_⟩
      apply e.injective
      rw [map_mul, e.apply_symm_apply, hm_map]
      exact Prod.ext hr hs

/-- Helper: every integer is a square in `ZMod 2`. -/
theorem isSquare_zmod_two (m : ℤ) : IsSquare (m : ZMod 2) := by
  rcases zmod2_eq_zero_or_one (m : ZMod 2) with h | h
  · exact ⟨0, by rw [h]; decide⟩
  · exact ⟨1, by rw [h]; decide⟩

/-- Helper: if `a, b, c : ℤ` are pairwise coprime squarefree nonzero integers and
`hilbertSymAt v (-a*c) (-b*c) = 1` at every place `v`, then `-b*c` is a square mod `|a|`. -/
theorem isSquare_mod_of_hilbert_trivial {a b c : ℤ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hAB : Nat.Coprime a.natAbs b.natAbs) (hCA : Nat.Coprime c.natAbs a.natAbs)
    (hsqA : Squarefree a.natAbs)
    (hhilb : ∀ v : QPlace,
      hilbertSymAt v
        (-(Units.mk0 (a : ℚ) (Int.cast_ne_zero.mpr ha0)) *
          Units.mk0 (c : ℚ) (Int.cast_ne_zero.mpr hc0))
        (-(Units.mk0 (b : ℚ) (Int.cast_ne_zero.mpr hb0)) *
          Units.mk0 (c : ℚ) (Int.cast_ne_zero.mpr hc0)) = 1) :
    IsSquare ((-b * c : ℤ) : ZMod a.natAbs) := by
  apply isSquare_zmod_of_forall_prime_dvd a.natAbs (Int.natAbs_pos.mpr ha0) hsqA
  intro p hp hpdvd
  by_cases hp2 : p = 2
  · subst hp2; exact isSquare_zmod_two (-b * c)
  · have : Fact p.Prime := ⟨hp⟩
    let ua : ℚˣ := Units.mk0 (a : ℚ) (Int.cast_ne_zero.mpr ha0)
    let ub : ℚˣ := Units.mk0 (b : ℚ) (Int.cast_ne_zero.mpr hb0)
    let uc : ℚˣ := Units.mk0 (c : ℚ) (Int.cast_ne_zero.mpr hc0)
    have hp_ndvd_b : ¬ p ∣ b.natAbs := fun hb =>
      hp.not_dvd_one (hAB.gcd_eq_one ▸ Nat.dvd_gcd hpdvd hb)
    have hp_ndvd_c : ¬ p ∣ c.natAbs := fun hc =>
      hp.not_dvd_one (hCA.gcd_eq_one ▸ Nat.dvd_gcd hc hpdvd)
    have hval_a : padicValRat p (ua : ℚ) = 1 := by
      change padicValRat p (a : ℚ) = 1
      rw [padicValRat.of_int]
      have hge1 : 1 ≤ padicValNat p a.natAbs :=
        one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr ha0) hpdvd
      have hlt2 : padicValNat p a.natAbs < 2 := by
        by_contra hge2
        push Not at hge2
        have hp2dvd : p ^ 2 ∣ a.natAbs := (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr ha0)).mpr hge2
        have hu : IsUnit p := hsqA p (by simpa [sq] using hp2dvd)
        exact hp.ne_one (Nat.isUnit_iff.mp hu)
      have heq1 : padicValNat p a.natAbs = 1 := by omega
      change (padicValNat p a.natAbs : ℤ) = 1
      omega
    have hval_b : padicValRat p (ub : ℚ) = 0 := by
      change padicValRat p (b : ℚ) = 0
      rw [padicValRat.of_int]
      change (padicValNat p b.natAbs : ℤ) = 0
      rw [padicValNat.eq_zero_of_not_dvd hp_ndvd_b]; rfl
    have hval_c : padicValRat p (uc : ℚ) = 0 := by
      change padicValRat p (c : ℚ) = 0
      rw [padicValRat.of_int]
      change (padicValNat p c.natAbs : ℤ) = 0
      rw [padicValNat.eq_zero_of_not_dvd hp_ndvd_c]; rfl
    have hval_ac : padicValRat p ((-ua * uc : ℚˣ) : ℚ) = 1 := by
      rw [Units.val_mul, Units.val_neg, padicValRat.mul (neg_ne_zero.mpr ua.ne_zero) uc.ne_zero,
        padicValRat.neg, hval_a, hval_c, add_zero]
    have hval_bc : padicValRat p ((-ub * uc : ℚˣ) : ℚ) = 0 := by
      rw [Units.val_mul, Units.val_neg, padicValRat.mul (neg_ne_zero.mpr ub.ne_zero) uc.ne_zero,
        padicValRat.neg, hval_b, hval_c, add_zero]
    have hsym := hhilb (QPlace.odd ⟨p, hp, hp2⟩)
    change hilbertSymOdd p hp hp2 (-ua * uc) (-ub * uc) = 1 at hsym
    have hz := congrArg unitsToZMod2 hsym
    rw [unitsToZMod2_hilbertSymOdd, unitsToZMod2_one] at hz
    have h1 : (oddCoords p hp (-ua * uc)).1 = 1 := by
      change (padicValRat p ((-ua * uc : ℚˣ) : ℚ) : ZMod 2) = 1; rw [hval_ac]; rfl
    have h2 : (oddCoords p hp (-ub * uc)).1 = 0 := by
      change (padicValRat p ((-ub * uc : ℚˣ) : ℚ) : ZMod 2) = 0; rw [hval_bc]; rfl
    rw [h1, h2, mul_zero, mul_zero, one_mul, zero_add, zero_add] at hz
    have hleg1 : pUnitLegUnit p hp (-ub * uc) = 1 := (unitsToZMod2_eq_zero_iff _).mp hz
    have hcoe := coe_pUnitLegUnit p hp (-ub * uc)
    rw [hleg1, Units.val_one, pUnit_of_val_zero p hp hval_bc,
      ratUnitLegendre_eq_quadraticChar hp (-ub * uc).ne_zero hval_bc] at hcoe
    have hred : redModP p ((-ub * uc : ℚˣ) : ℚ) = ((-b * c : ℤ) : ZMod p) := by
      have hcast : ((-ub * uc : ℚˣ) : ℚ) = ((-b * c : ℤ) : ℚ) := by
        simp [ub, uc]
      rw [hcast, redModP_intCast]
    rw [hred] at hcoe
    have hne0 : ((-b * c : ℤ) : ZMod p) ≠ 0 := by
      rw [← hred]
      exact redModP_ne_zero_of_val_eq_zero hp (-ub * uc).ne_zero hval_bc
    exact (quadraticChar_one_iff_isSquare hne0).mp hcoe.symm

/-- **UNCONDITIONAL LEGENDRE'S THREE-VARIABLE THEOREM (`0` ASSUMPTIONS!)**:
For pairwise coprime squarefree nonzero integers `a, b, c` not all of the same sign,
`a x² + b y² + c z² = 0` has a nontrivial integer solution IFF `-b*c` is a square mod `|a|`,
`-c*a` is a square mod `|b|`, and `-a*b` is a square mod `|c|`! -/
theorem legendre_ternary_quadratic {a b c : ℤ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hAB : Nat.Coprime a.natAbs b.natAbs)
    (hBC : Nat.Coprime b.natAbs c.natAbs)
    (hCA : Nat.Coprime c.natAbs a.natAbs)
    (hsqA : Squarefree a.natAbs) (hsqB : Squarefree b.natAbs) (hsqC : Squarefree c.natAbs)
    (hsign : ¬ (0 < a * c ∧ 0 < b * c)) :
    (∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) ↔
      IsSquare ((-b * c : ℤ) : ZMod a.natAbs) ∧
      IsSquare ((-c * a : ℤ) : ZMod b.natAbs) ∧
      IsSquare ((-a * b : ℤ) : ZMod c.natAbs) := by
  let ua : ℚˣ := Units.mk0 (a : ℚ) (Int.cast_ne_zero.mpr ha0)
  let ub : ℚˣ := Units.mk0 (b : ℚ) (Int.cast_ne_zero.mpr hb0)
  let uc : ℚˣ := Units.mk0 (c : ℚ) (Int.cast_ne_zero.mpr hc0)
  constructor
  · rintro ⟨x, y, z, hne, heq⟩
    have hQ : HasTernaryZeroQ ua ub uc := by
      refine ⟨(x : ℚ), (y : ℚ), (z : ℚ), ?_, ?_⟩
      · rcases hne with h | h | h
        · exact Or.inl (Int.cast_ne_zero.mpr h)
        · exact Or.inr (Or.inl (Int.cast_ne_zero.mpr h))
        · exact Or.inr (Or.inr (Int.cast_ne_zero.mpr h))
      · simp only [ua, ub, uc, Units.val_mk0]
        exact_mod_cast heq
    have hnorm : ∃ u v : ℚ, ((-ub * uc : ℚˣ) : ℚ) = u ^ 2 - ((-ua * uc : ℚˣ) : ℚ) * v ^ 2 := by
      have hK : HasTernaryZeroK (ua : ℚ) (ub : ℚ) (uc : ℚ) := hQ
      rw [hasTernaryZeroK_iff_binary_norm (by norm_num : (2 : ℚ) ≠ 0) ua.ne_zero uc.ne_zero] at hK
      obtain ⟨u, v, huv⟩ := hK
      exact ⟨u, v, by simpa using huv.symm⟩
    have hhilb : ∀ v : QPlace, hilbertSymAt v (-ua * uc) (-ub * uc) = 1 :=
      hilbertSymAt_eq_one_of_binary_norm hnorm
    refine ⟨isSquare_mod_of_hilbert_trivial ha0 hb0 hc0 hAB hCA hsqA hhilb,
      isSquare_mod_of_hilbert_trivial hb0 hc0 ha0 hBC hAB hsqB (fun v => ?_),
      isSquare_mod_of_hilbert_trivial hc0 ha0 hb0 hCA hBC hsqC (fun v => ?_)⟩
    · calc hilbertSymAt v (-ub * ua) (-uc * ua)
          = hilbertSymAt v (-uc * ua) (-ub * ua) := hilbertSymAt_symm v _ _
        _ = hilbertSymAt v (-ua * uc) (-ub * uc) := hilbertSymAt_ternary_swap_ac v ua ub uc
        _ = 1 := hhilb v
    · calc hilbertSymAt v (-uc * ub) (-ua * ub)
          = hilbertSymAt v (-ua * ub) (-uc * ub) := hilbertSymAt_symm v _ _
        _ = hilbertSymAt v (-ua * uc) (-ub * uc) := hilbertSymAt_ternary_swap_bc v ua ub uc
        _ = 1 := hhilb v
  · rintro ⟨⟨rA, hrA⟩, ⟨rB, hrB⟩, ⟨rC, hrC⟩⟩
    have hA_dvd : (a.natAbs : ℤ) ∣ (rA.val : ℤ) ^ 2 + b * c := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ a.natAbs).mp
      have : NeZero a.natAbs := ⟨Int.natAbs_ne_zero.mpr ha0⟩
      push_cast
      rw [ZMod.natCast_zmod_val, sq, ← hrA]
      push_cast; ring
    have hB_dvd : (b.natAbs : ℤ) ∣ (rB.val : ℤ) ^ 2 + c * a := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ b.natAbs).mp
      have : NeZero b.natAbs := ⟨Int.natAbs_ne_zero.mpr hb0⟩
      push_cast
      rw [ZMod.natCast_zmod_val, sq, ← hrB]
      push_cast; ring
    have hC_dvd : (c.natAbs : ℤ) ∣ (rC.val : ℤ) ^ 2 + a * b := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ c.natAbs).mp
      have : NeZero c.natAbs := ⟨Int.natAbs_ne_zero.mpr hc0⟩
      push_cast
      rw [ZMod.natCast_zmod_val, sq, ← hrC]
      push_cast; ring
    have hApos : 0 < a.natAbs := Int.natAbs_pos.mpr ha0
    have hBpos : 0 < b.natAbs := Int.natAbs_pos.mpr hb0
    have hCpos : 0 < c.natAbs := Int.natAbs_pos.mpr hc0
    -- Case split on signs of (a, b, c): 6 valid sign patterns (all-pos and all-neg excluded by hsign)
    rcases lt_or_gt_of_ne ha0 with ha_neg | ha_pos <;>
      rcases lt_or_gt_of_ne hb0 with hb_neg | hb_pos <;>
      rcases lt_or_gt_of_ne hc0 with hc_neg | hc_pos
    · exfalso; exact hsign ⟨mul_pos_of_neg_of_neg ha_neg hc_neg, mul_pos_of_neg_of_neg hb_neg hc_neg⟩
    · -- a < 0, b < 0, c > 0 -> (-a) x² + (-b) y² - c z² = 0
      have hae : (a.natAbs : ℤ) = -a := Int.ofNat_natAbs_of_nonpos ha_neg.le
      have hbe : (b.natAbs : ℤ) = -b := Int.ofNat_natAbs_of_nonpos hb_neg.le
      have hce : (c.natAbs : ℤ) = c := Int.natAbs_of_nonneg hc_pos.le
      obtain ⟨x, y, z, hne, heq⟩ := legendre_ternary_pos hApos hBpos hCpos hAB hBC hCA hsqA hsqB hsqC
        (uA := rA.val) (uB := rB.val) (uC := rC.val)
        (by rw [hbe, hce]; simpa [neg_mul] using hA_dvd)
        (by rw [hce, hae]; simpa [mul_neg] using hB_dvd)
        (by rw [hae, hbe]; simpa using hC_dvd)
      exact ⟨x, y, z, hne, by rw [hae, hbe, hce] at heq; linarith⟩
    · -- a < 0, b > 0, c < 0 -> (-a) x² + (-c) z² - b y² = 0
      have hae : (a.natAbs : ℤ) = -a := Int.ofNat_natAbs_of_nonpos ha_neg.le
      have hbe : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg hb_pos.le
      have hce : (c.natAbs : ℤ) = -c := Int.ofNat_natAbs_of_nonpos hc_neg.le
      obtain ⟨x, z, y, hne, heq⟩ := legendre_ternary_pos hApos hCpos hBpos hCA.symm hBC.symm hAB.symm hsqA hsqC hsqB
        (uA := rA.val) (uB := rC.val) (uC := rB.val)
        (by rw [hce, hbe]; simpa [neg_mul, mul_comm] using hA_dvd)
        (by rw [hbe, hae]; simpa [mul_neg, mul_comm] using hC_dvd)
        (by rw [hae, hce]; simpa [mul_comm] using hB_dvd)
      exact ⟨x, y, z, by rcases hne with h | h | h; exacts [Or.inl h, Or.inr (Or.inr h), Or.inr (Or.inl h)],
        by rw [hae, hbe, hce] at heq; linarith⟩
    · -- a < 0, b > 0, c > 0 -> b y² + c z² - (-a) x² = 0
      have hae : (a.natAbs : ℤ) = -a := Int.ofNat_natAbs_of_nonpos ha_neg.le
      have hbe : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg hb_pos.le
      have hce : (c.natAbs : ℤ) = c := Int.natAbs_of_nonneg hc_pos.le
      obtain ⟨y, z, x, hne, heq⟩ := legendre_ternary_pos hBpos hCpos hApos hBC hCA hAB hsqB hsqC hsqA
        (uA := rB.val) (uB := rC.val) (uC := rA.val)
        (by rw [hce, hae]; simpa [mul_neg] using hB_dvd)
        (by rw [hae, hbe]; simpa [neg_mul] using hC_dvd)
        (by rw [hbe, hce]; simpa using hA_dvd)
      exact ⟨x, y, z, by rcases hne with h | h | h; exacts [Or.inr (Or.inl h), Or.inr (Or.inr h), Or.inl h],
        by rw [hae, hbe, hce] at heq; linarith⟩
    · -- a > 0, b < 0, c < 0 -> (-b) y² + (-c) z² - a x² = 0
      have hae : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha_pos.le
      have hbe : (b.natAbs : ℤ) = -b := Int.ofNat_natAbs_of_nonpos hb_neg.le
      have hce : (c.natAbs : ℤ) = -c := Int.ofNat_natAbs_of_nonpos hc_neg.le
      obtain ⟨y, z, x, hne, heq⟩ := legendre_ternary_pos hBpos hCpos hApos hBC hCA hAB hsqB hsqC hsqA
        (uA := rB.val) (uB := rC.val) (uC := rA.val)
        (by rw [hce, hae]; simpa [neg_mul] using hB_dvd)
        (by rw [hae, hbe]; simpa [mul_neg] using hC_dvd)
        (by rw [hbe, hce]; simpa using hA_dvd)
      exact ⟨x, y, z, by rcases hne with h | h | h; exacts [Or.inr (Or.inl h), Or.inr (Or.inr h), Or.inl h],
        by rw [hae, hbe, hce] at heq; linarith⟩
    · -- a > 0, b < 0, c > 0 -> a x² + c z² - (-b) y² = 0
      have hae : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha_pos.le
      have hbe : (b.natAbs : ℤ) = -b := Int.ofNat_natAbs_of_nonpos hb_neg.le
      have hce : (c.natAbs : ℤ) = c := Int.natAbs_of_nonneg hc_pos.le
      obtain ⟨x, z, y, hne, heq⟩ := legendre_ternary_pos hApos hCpos hBpos hCA.symm hBC.symm hAB.symm hsqA hsqC hsqB
        (uA := rA.val) (uB := rC.val) (uC := rB.val)
        (by rw [hce, hbe]; simpa [mul_neg, mul_comm] using hA_dvd)
        (by rw [hbe, hae]; simpa [neg_mul, mul_comm] using hC_dvd)
        (by rw [hae, hce]; simpa [mul_comm] using hB_dvd)
      exact ⟨x, y, z, by rcases hne with h | h | h; exacts [Or.inl h, Or.inr (Or.inr h), Or.inr (Or.inl h)],
        by rw [hae, hbe, hce] at heq; linarith⟩
    · -- a > 0, b > 0, c < 0 -> a x² + b y² - (-c) z² = 0
      have hae : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha_pos.le
      have hbe : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg hb_pos.le
      have hce : (c.natAbs : ℤ) = -c := Int.ofNat_natAbs_of_nonpos hc_neg.le
      obtain ⟨x, y, z, hne, heq⟩ := legendre_ternary_pos hApos hBpos hCpos hAB hBC hCA hsqA hsqB hsqC
        (uA := rA.val) (uB := rB.val) (uC := rC.val)
        (by rw [hbe, hce]; simpa [mul_neg] using hA_dvd)
        (by rw [hce, hae]; simpa [neg_mul] using hB_dvd)
        (by rw [hae, hbe]; simpa using hC_dvd)
      exact ⟨x, y, z, hne, by rw [hae, hbe, hce] at heq; linarith⟩
    · exfalso; exact hsign ⟨mul_pos ha_pos hc_pos, mul_pos hb_pos hc_pos⟩

/-! ### 3C. Reduction of Arbitrary `a, b, c : ℚˣ` to Pairwise Coprime Squarefree Integers -/

/-- Every positive natural number factors as `m * k^2` with `m` squarefree and `k > 0`. -/
theorem exists_squarefree_mul_sq_nat :
    ∀ n : ℕ, 0 < n → ∃ m k : ℕ, 0 < m ∧ 0 < k ∧ Squarefree m ∧ n = m * k ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hsq : Squarefree n
    · exact ⟨n, 1, hn, Nat.one_pos, hsq, by ring⟩
    · -- Find a prime p with p^2 ∣ n
      have hex : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n := by
        rw [Nat.squarefree_iff_prime_squarefree] at hsq
        push Not at hsq
        obtain ⟨p, hp, hd⟩ := hsq
        exact ⟨p, hp, by simpa [sq] using hd⟩
      obtain ⟨p, hp, hp2⟩ := hex
      let n' := n / p ^ 2
      have hn'_eq : n = n' * p ^ 2 := (Nat.div_mul_cancel hp2).symm
      have hn'_pos : 0 < n' := Nat.div_pos (Nat.le_of_dvd hn hp2) (pow_pos hp.pos 2)
      have hn'_lt : n' < n := Nat.div_lt_self hn (by have := hp.two_le; nlinarith)
      obtain ⟨m, k, hm, hk, hsqm, heq⟩ := ih n' hn'_lt hn'_pos
      refine ⟨m, k * p, hm, mul_pos hk hp.pos, hsqm, ?_⟩
      rw [hn'_eq, heq]; ring

/-- Every `q : ℚˣ` equals `(m : ℚ) * r^2` for a nonzero squarefree integer `m` and `r : ℚˣ`. -/
theorem exists_squarefree_mul_sq_rat (q : ℚˣ) :
    ∃ (m : ℤ) (hm : m ≠ 0) (r : ℚˣ), Squarefree m.natAbs ∧
      q = Units.mk0 (m : ℚ) (Int.cast_ne_zero.mpr hm) * r ^ 2 := by
  let d : ℕ := (q : ℚ).den
  have hd_nz : d ≠ 0 := (q : ℚ).den_nz
  have hd : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd_nz
  let z : ℤ := (q : ℚ).num * (d : ℤ)
  have hz0 : z ≠ 0 := mul_ne_zero (Rat.num_ne_zero.mpr q.ne_zero) (Int.natCast_ne_zero.mpr hd_nz)
  obtain ⟨mN, kN, hmN, hkN, hsqm, hzeq⟩ :=
    exists_squarefree_mul_sq_nat z.natAbs (Int.natAbs_pos.mpr hz0)
  let rQ : ℚ := (kN : ℚ) / (d : ℚ)
  have hrQ : rQ ≠ 0 := div_ne_zero (Nat.cast_ne_zero.mpr hkN.ne') hd
  let r : ℚˣ := Units.mk0 rQ hrQ
  have hq_eq : (q : ℚ) = (z : ℚ) / (d : ℚ) ^ 2 := by
    have hz_cast : (z : ℚ) = ((q : ℚ).num : ℚ) * (d : ℚ) := by
      dsimp only [z]; push_cast; rfl
    rw [hz_cast]
    calc (q : ℚ) = ((q : ℚ).num : ℚ) / (d : ℚ) := (Rat.num_div_den (q : ℚ)).symm
      _ = ((q : ℚ).num : ℚ) * (d : ℚ) / (d : ℚ) ^ 2 := by field_simp [hd]
  rcases lt_or_gt_of_ne hz0 with hz_neg | hz_pos
  · let m : ℤ := -(mN : ℤ)
    have hm0 : m ≠ 0 := by omega
    refine ⟨m, hm0, r, by simpa [m] using hsqm, Units.ext ?_⟩
    have hzeqZ : z = m * (kN : ℤ) ^ 2 := by
      have habs : (z.natAbs : ℤ) = -z := Int.ofNat_natAbs_of_nonpos hz_neg.le
      have hcast : (z.natAbs : ℤ) = (mN : ℤ) * (kN : ℤ) ^ 2 := by exact_mod_cast hzeq
      dsimp only [m]; linarith
    have hzQ : (z : ℚ) = (m : ℚ) * (kN : ℚ) ^ 2 := by exact_mod_cast hzeqZ
    change (q : ℚ) = (m : ℚ) * rQ ^ 2
    rw [hq_eq, hzQ]
    dsimp only [rQ]
    field_simp [hd]
  · let m : ℤ := (mN : ℤ)
    have hm0 : m ≠ 0 := by omega
    refine ⟨m, hm0, r, by simpa [m] using hsqm, Units.ext ?_⟩
    have hzeqZ : z = m * (kN : ℤ) ^ 2 := by
      have habs : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hz_pos.le
      have hcast : (z.natAbs : ℤ) = (mN : ℤ) * (kN : ℤ) ^ 2 := by exact_mod_cast hzeq
      dsimp only [m]; linarith
    have hzQ : (z : ℚ) = (m : ℚ) * (kN : ℚ) ^ 2 := by exact_mod_cast hzeqZ
    change (q : ℚ) = (m : ℚ) * rQ ^ 2
    rw [hq_eq, hzQ]
    dsimp only [rQ]
    field_simp [hd]

/-- Helper: strong induction reducing any squarefree nonzero integer triple `(a, b, c)` to a
pairwise coprime squarefree nonzero integer triple `(a', b', c')` with identical `HasTernaryZeroQ`
and identical Hilbert symbols `hilbertSymAt v (-a*c) (-b*c)` at every place `v`. -/
theorem reduce_to_coprime_squarefree :
    ∀ (N : ℕ) (a b c : ℤ) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0),
      a.natAbs * b.natAbs * c.natAbs = N →
      Squarefree a.natAbs → Squarefree b.natAbs → Squarefree c.natAbs →
      ∃ (a' b' c' : ℤ) (ha' : a' ≠ 0) (hb' : b' ≠ 0) (hc' : c' ≠ 0),
        Nat.Coprime a'.natAbs b'.natAbs ∧
        Nat.Coprime b'.natAbs c'.natAbs ∧
        Nat.Coprime c'.natAbs a'.natAbs ∧
        Squarefree a'.natAbs ∧ Squarefree b'.natAbs ∧ Squarefree c'.natAbs ∧
        (HasTernaryZeroQ (Units.mk0 (a' : ℚ) (Int.cast_ne_zero.mpr ha'))
          (Units.mk0 (b' : ℚ) (Int.cast_ne_zero.mpr hb'))
          (Units.mk0 (c' : ℚ) (Int.cast_ne_zero.mpr hc')) ↔
         HasTernaryZeroQ (Units.mk0 (a : ℚ) (Int.cast_ne_zero.mpr ha0))
          (Units.mk0 (b : ℚ) (Int.cast_ne_zero.mpr hb0))
          (Units.mk0 (c : ℚ) (Int.cast_ne_zero.mpr hc0))) ∧
        (∀ v : QPlace,
          hilbertSymAt v
            (-(Units.mk0 (a' : ℚ) (Int.cast_ne_zero.mpr ha')) *
              Units.mk0 (c' : ℚ) (Int.cast_ne_zero.mpr hc'))
            (-(Units.mk0 (b' : ℚ) (Int.cast_ne_zero.mpr hb')) *
              Units.mk0 (c' : ℚ) (Int.cast_ne_zero.mpr hc')) =
          hilbertSymAt v
            (-(Units.mk0 (a : ℚ) (Int.cast_ne_zero.mpr ha0)) *
              Units.mk0 (c : ℚ) (Int.cast_ne_zero.mpr hc0))
            (-(Units.mk0 (b : ℚ) (Int.cast_ne_zero.mpr hb0)) *
              Units.mk0 (c : ℚ) (Int.cast_ne_zero.mpr hc0))) := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro a b c ha0 hb0 hc0 hN hsqA hsqB hsqC
    let ua : ℚˣ := Units.mk0 (a : ℚ) (Int.cast_ne_zero.mpr ha0)
    let ub : ℚˣ := Units.mk0 (b : ℚ) (Int.cast_ne_zero.mpr hb0)
    let uc : ℚˣ := Units.mk0 (c : ℚ) (Int.cast_ne_zero.mpr hc0)
    have hApos : 0 < a.natAbs := Int.natAbs_pos.mpr ha0
    have hBpos : 0 < b.natAbs := Int.natAbs_pos.mpr hb0
    have hCpos : 0 < c.natAbs := Int.natAbs_pos.mpr hc0
    -- Helper: if prime p divides both x and y (and possibly z), reduce N!
    have hstep_common_all : ∀ p : ℕ, p.Prime → p ∣ a.natAbs → p ∣ b.natAbs → p ∣ c.natAbs →
        ∃ (a' b' c' : ℤ) (ha' : a' ≠ 0) (hb' : b' ≠ 0) (hc' : c' ≠ 0),
          Nat.Coprime a'.natAbs b'.natAbs ∧ Nat.Coprime b'.natAbs c'.natAbs ∧
          Nat.Coprime c'.natAbs a'.natAbs ∧
          Squarefree a'.natAbs ∧ Squarefree b'.natAbs ∧ Squarefree c'.natAbs ∧
          (HasTernaryZeroQ (Units.mk0 (a' : ℚ) (Int.cast_ne_zero.mpr ha'))
            (Units.mk0 (b' : ℚ) (Int.cast_ne_zero.mpr hb'))
            (Units.mk0 (c' : ℚ) (Int.cast_ne_zero.mpr hc')) ↔ HasTernaryZeroQ ua ub uc) ∧
          (∀ v : QPlace,
            hilbertSymAt v
              (-(Units.mk0 (a' : ℚ) (Int.cast_ne_zero.mpr ha')) *
                Units.mk0 (c' : ℚ) (Int.cast_ne_zero.mpr hc'))
              (-(Units.mk0 (b' : ℚ) (Int.cast_ne_zero.mpr hb')) *
                Units.mk0 (c' : ℚ) (Int.cast_ne_zero.mpr hc')) =
            hilbertSymAt v (-ua * uc) (-ub * uc)) := by
      intro p hp hpa hpb hpc
      have hpaZ : (p : ℤ) ∣ a := Int.natCast_dvd.mpr hpa
      have hpbZ : (p : ℤ) ∣ b := Int.natCast_dvd.mpr hpb
      have hpcZ : (p : ℤ) ∣ c := Int.natCast_dvd.mpr hpc
      let a₁ : ℤ := a / (p : ℤ)
      let b₁ : ℤ := b / (p : ℤ)
      let c₁ : ℤ := c / (p : ℤ)
      have ha_eq : (p : ℤ) * a₁ = a := Int.mul_ediv_cancel' hpaZ
      have hb_eq : (p : ℤ) * b₁ = b := Int.mul_ediv_cancel' hpbZ
      have hc_eq : (p : ℤ) * c₁ = c := Int.mul_ediv_cancel' hpcZ
      have ha₁ : a₁ ≠ 0 := fun h => ha0 (by rw [← ha_eq, h, mul_zero])
      have hb₁ : b₁ ≠ 0 := fun h => hb0 (by rw [← hb_eq, h, mul_zero])
      have hc₁ : c₁ ≠ 0 := fun h => hc0 (by rw [← hc_eq, h, mul_zero])
      have hA1 : a.natAbs = p * a₁.natAbs := by
        simpa [Int.natAbs_mul] using congrArg Int.natAbs ha_eq.symm
      have hB1 : b.natAbs = p * b₁.natAbs := by
        simpa [Int.natAbs_mul] using congrArg Int.natAbs hb_eq.symm
      have hC1 : c.natAbs = p * c₁.natAbs := by
        simpa [Int.natAbs_mul] using congrArg Int.natAbs hc_eq.symm
      have hsqA1 : Squarefree a₁.natAbs := (Nat.squarefree_mul_iff.mp (hA1 ▸ hsqA)).2.2
      have hsqB1 : Squarefree b₁.natAbs := (Nat.squarefree_mul_iff.mp (hB1 ▸ hsqB)).2.2
      have hsqC1 : Squarefree c₁.natAbs := (Nat.squarefree_mul_iff.mp (hC1 ▸ hsqC)).2.2
      have hlt : a₁.natAbs * b₁.natAbs * c₁.natAbs < N := by
        rw [← hN, hA1, hB1, hC1]
        have hp3 : 1 < p ^ 3 := one_lt_pow₀ hp.one_lt (by decide)
        have h1 : 0 < a₁.natAbs * b₁.natAbs * c₁.natAbs := by
          have := Int.natAbs_pos.mpr ha₁; have := Int.natAbs_pos.mpr hb₁
          have := Int.natAbs_pos.mpr hc₁; positivity
        have hmul : p * a₁.natAbs * (p * b₁.natAbs) * (p * c₁.natAbs) =
            p ^ 3 * (a₁.natAbs * b₁.natAbs * c₁.natAbs) := by ring
        rw [hmul]
        exact lt_mul_of_one_lt_left h1 hp3
      obtain ⟨a', b', c', ha', hb', hc', hc1, hc2, hc3, hs1, hs2, hs3, hzero, hhilb⟩ :=
        ih _ hlt a₁ b₁ c₁ ha₁ hb₁ hc₁ rfl hsqA1 hsqB1 hsqC1
      let up : ℚˣ := primeUnit p hp
      let ua₁ : ℚˣ := Units.mk0 (a₁ : ℚ) (Int.cast_ne_zero.mpr ha₁)
      let ub₁ : ℚˣ := Units.mk0 (b₁ : ℚ) (Int.cast_ne_zero.mpr hb₁)
      let uc₁ : ℚˣ := Units.mk0 (c₁ : ℚ) (Int.cast_ne_zero.mpr hc₁)
      have hua : ua = up * ua₁ := Units.ext (by simp [ua, up, ua₁]; exact_mod_cast ha_eq.symm)
      have hub : ub = up * ub₁ := Units.ext (by simp [ub, up, ub₁]; exact_mod_cast hb_eq.symm)
      have huc : uc = up * uc₁ := Units.ext (by simp [uc, up, uc₁]; exact_mod_cast hc_eq.symm)
      refine ⟨a', b', c', ha', hb', hc', hc1, hc2, hc3, hs1, hs2, hs3, ?_, ?_⟩
      · rw [hzero, hua, hub, huc]
        exact (hasTernaryZeroK_scale (K := ℚ) up.ne_zero).symm
      · intro v
        rw [hhilb v, hua, hub, huc]
        exact (hilbertSymAt_ternary_scale v ua₁ ub₁ uc₁ up).symm
    by_cases hAB : Nat.Coprime a.natAbs b.natAbs
    · by_cases hBC : Nat.Coprime b.natAbs c.natAbs
      · by_cases hCA : Nat.Coprime c.natAbs a.natAbs
        · exact ⟨a, b, c, ha0, hb0, hc0, hAB, hBC, hCA, hsqA, hsqB, hsqC, Iff.rfl, fun _ => rfl⟩
        · -- Some prime p divides c and a
          have hg : Nat.gcd c.natAbs a.natAbs ≠ 1 := hCA
          let p := (Nat.gcd c.natAbs a.natAbs).minFac
          have hp : p.Prime := Nat.minFac_prime hg
          have hpdvd : p ∣ Nat.gcd c.natAbs a.natAbs := Nat.minFac_dvd _
          have hpc : p ∣ c.natAbs := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
          have hpa : p ∣ a.natAbs := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
          by_cases hpb : p ∣ b.natAbs
          · exact hstep_common_all p hp hpa hpb hpc
          · -- Replace (a, b, c) with (a/p, p*b, c/p)
            let a₁ : ℤ := a / (p : ℤ)
            let b₁ : ℤ := (p : ℤ) * b
            let c₁ : ℤ := c / (p : ℤ)
            have ha_eq : (p : ℤ) * a₁ = a := Int.mul_ediv_cancel' (Int.natCast_dvd.mpr hpa)
            have hc_eq : (p : ℤ) * c₁ = c := Int.mul_ediv_cancel' (Int.natCast_dvd.mpr hpc)
            have ha₁ : a₁ ≠ 0 := fun h => ha0 (by rw [← ha_eq, h, mul_zero])
            have hb₁ : b₁ ≠ 0 := mul_ne_zero (Int.natCast_ne_zero.mpr hp.ne_zero) hb0
            have hc₁ : c₁ ≠ 0 := fun h => hc0 (by rw [← hc_eq, h, mul_zero])
            have hA1 : a.natAbs = p * a₁.natAbs := by
              simpa [Int.natAbs_mul] using congrArg Int.natAbs ha_eq.symm
            have hB1 : b₁.natAbs = p * b.natAbs := by simp [b₁, Int.natAbs_mul]
            have hC1 : c.natAbs = p * c₁.natAbs := by
              simpa [Int.natAbs_mul] using congrArg Int.natAbs hc_eq.symm
            have hsqA1 : Squarefree a₁.natAbs := (Nat.squarefree_mul_iff.mp (hA1 ▸ hsqA)).2.2
            have hsqB1 : Squarefree b₁.natAbs := by
              rw [hB1]
              exact Nat.squarefree_mul_iff.mpr
                ⟨hp.coprime_iff_not_dvd.mpr hpb, hp.squarefree, hsqB⟩
            have hsqC1 : Squarefree c₁.natAbs := (Nat.squarefree_mul_iff.mp (hC1 ▸ hsqC)).2.2
            have hlt : a₁.natAbs * b₁.natAbs * c₁.natAbs < N := by
              rw [← hN, hA1, hB1, hC1]
              have h1 : 0 < a₁.natAbs * b.natAbs * c₁.natAbs := by
                have := Int.natAbs_pos.mpr ha₁; have := Int.natAbs_pos.mpr hc₁; positivity
              have hm1 : a₁.natAbs * (p * b.natAbs) * c₁.natAbs =
                  p * (a₁.natAbs * b.natAbs * c₁.natAbs) := by ring
              have hm2 : p * a₁.natAbs * b.natAbs * (p * c₁.natAbs) =
                  p * (p * (a₁.natAbs * b.natAbs * c₁.natAbs)) := by ring
              rw [hm1, hm2]
              exact Nat.mul_lt_mul_of_pos_left (lt_mul_of_one_lt_left h1 hp.one_lt) hp.pos
            obtain ⟨a', b', c', ha', hb', hc', hc1, hc2, hc3, hs1, hs2, hs3, hzero, hhilb⟩ :=
              ih _ hlt a₁ b₁ c₁ ha₁ hb₁ hc₁ rfl hsqA1 hsqB1 hsqC1
            let up : ℚˣ := primeUnit p hp
            let ua₁ : ℚˣ := Units.mk0 (a₁ : ℚ) (Int.cast_ne_zero.mpr ha₁)
            let ub₁ : ℚˣ := Units.mk0 (b₁ : ℚ) (Int.cast_ne_zero.mpr hb₁)
            let uc₁ : ℚˣ := Units.mk0 (c₁ : ℚ) (Int.cast_ne_zero.mpr hc₁)
            have hua : ua = up * ua₁ := Units.ext (by simp [ua, up, ua₁]; exact_mod_cast ha_eq.symm)
            have hub₁ : ub₁ = up * ub := Units.ext (by simp [ub₁, up, ub, b₁])
            have huc : uc = up * uc₁ := Units.ext (by simp [uc, up, uc₁]; exact_mod_cast hc_eq.symm)
            refine ⟨a', b', c', ha', hb', hc', hc1, hc2, hc3, hs1, hs2, hs3, ?_, ?_⟩
            · rw [hzero]
              change HasTernaryZeroK (ua₁ : ℚ) (ub₁ : ℚ) (uc₁ : ℚ) ↔
                HasTernaryZeroK (ua : ℚ) (ub : ℚ) (uc : ℚ)
              have hsc := (hasTernaryZeroK_scale (a := (ua₁ : ℚ)) (b := (ub₁ : ℚ))
                (c := (uc₁ : ℚ)) up.ne_zero).symm
              have hsq := hasTernaryZeroK_scale_squares (a := (ua : ℚ)) (b := (ub : ℚ))
                (c := (uc : ℚ)) one_ne_zero up.ne_zero one_ne_zero
              have he1 : (up : ℚ) * (ua₁ : ℚ) = (ua : ℚ) * (1 : ℚ) ^ 2 := by
                rw [hua, Units.val_mul]; ring
              have he2 : (up : ℚ) * (ub₁ : ℚ) = (ub : ℚ) * (up : ℚ) ^ 2 := by
                rw [hub₁, Units.val_mul]; ring
              have he3 : (up : ℚ) * (uc₁ : ℚ) = (uc : ℚ) * (1 : ℚ) ^ 2 := by
                rw [huc, Units.val_mul]; ring
              rw [he1, he2, he3] at hsc
              exact hsc.trans hsq
            · intro v
              rw [hhilb v]
              change hilbertSymAt v (-ua₁ * uc₁) (-ub₁ * uc₁) = hilbertSymAt v (-ua * uc) (-ub * uc)
              rw [hua, hub₁, huc]
              have h1 : -(up * ua₁) * (up * uc₁) = (-ua₁ * uc₁) * up ^ 2 := by
                apply Units.ext; simp; ring
              have h2 : -(up * ub) * uc₁ = -ub * (up * uc₁) := by
                apply Units.ext; simp; ring
              rw [h1, h2]
              symm
              rw [hilbertSymAt_mul_left, hilbertSymAt_sq_left, mul_one]
      · -- Some prime p divides b and c
        have hg : Nat.gcd b.natAbs c.natAbs ≠ 1 := hBC
        let p := (Nat.gcd b.natAbs c.natAbs).minFac
        have hp : p.Prime := Nat.minFac_prime hg
        have hpdvd : p ∣ Nat.gcd b.natAbs c.natAbs := Nat.minFac_dvd _
        have hpb : p ∣ b.natAbs := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
        have hpc : p ∣ c.natAbs := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
        by_cases hpa : p ∣ a.natAbs
        · exact hstep_common_all p hp hpa hpb hpc
        · -- Replace (a, b, c) with (p*a, b/p, c/p)
          let a₁ : ℤ := (p : ℤ) * a
          let b₁ : ℤ := b / (p : ℤ)
          let c₁ : ℤ := c / (p : ℤ)
          have hb_eq : (p : ℤ) * b₁ = b := Int.mul_ediv_cancel' (Int.natCast_dvd.mpr hpb)
          have hc_eq : (p : ℤ) * c₁ = c := Int.mul_ediv_cancel' (Int.natCast_dvd.mpr hpc)
          have ha₁ : a₁ ≠ 0 := mul_ne_zero (Int.natCast_ne_zero.mpr hp.ne_zero) ha0
          have hb₁ : b₁ ≠ 0 := fun h => hb0 (by rw [← hb_eq, h, mul_zero])
          have hc₁ : c₁ ≠ 0 := fun h => hc0 (by rw [← hc_eq, h, mul_zero])
          have hA1 : a₁.natAbs = p * a.natAbs := by simp [a₁, Int.natAbs_mul]
          have hB1 : b.natAbs = p * b₁.natAbs := by
            simpa [Int.natAbs_mul] using congrArg Int.natAbs hb_eq.symm
          have hC1 : c.natAbs = p * c₁.natAbs := by
            simpa [Int.natAbs_mul] using congrArg Int.natAbs hc_eq.symm
          have hsqA1 : Squarefree a₁.natAbs := by
            rw [hA1]
            exact Nat.squarefree_mul_iff.mpr
              ⟨hp.coprime_iff_not_dvd.mpr hpa, hp.squarefree, hsqA⟩
          have hsqB1 : Squarefree b₁.natAbs := (Nat.squarefree_mul_iff.mp (hB1 ▸ hsqB)).2.2
          have hsqC1 : Squarefree c₁.natAbs := (Nat.squarefree_mul_iff.mp (hC1 ▸ hsqC)).2.2
          have hlt : a₁.natAbs * b₁.natAbs * c₁.natAbs < N := by
            rw [← hN, hA1, hB1, hC1]
            have h1 : 0 < a.natAbs * b₁.natAbs * c₁.natAbs := by
              have := Int.natAbs_pos.mpr hb₁; have := Int.natAbs_pos.mpr hc₁; positivity
            have hm1 : p * a.natAbs * b₁.natAbs * c₁.natAbs =
                p * (a.natAbs * b₁.natAbs * c₁.natAbs) := by ring
            have hm2 : a.natAbs * (p * b₁.natAbs) * (p * c₁.natAbs) =
                p * (p * (a.natAbs * b₁.natAbs * c₁.natAbs)) := by ring
            rw [hm1, hm2]
            exact Nat.mul_lt_mul_of_pos_left (lt_mul_of_one_lt_left h1 hp.one_lt) hp.pos
          obtain ⟨a', b', c', ha', hb', hc', hc1, hc2, hc3, hs1, hs2, hs3, hzero, hhilb⟩ :=
            ih _ hlt a₁ b₁ c₁ ha₁ hb₁ hc₁ rfl hsqA1 hsqB1 hsqC1
          let up : ℚˣ := primeUnit p hp
          let ua₁ : ℚˣ := Units.mk0 (a₁ : ℚ) (Int.cast_ne_zero.mpr ha₁)
          let ub₁ : ℚˣ := Units.mk0 (b₁ : ℚ) (Int.cast_ne_zero.mpr hb₁)
          let uc₁ : ℚˣ := Units.mk0 (c₁ : ℚ) (Int.cast_ne_zero.mpr hc₁)
          have hua₁ : ua₁ = up * ua := Units.ext (by simp [ua₁, up, ua, a₁])
          have hub : ub = up * ub₁ := Units.ext (by simp [ub, up, ub₁]; exact_mod_cast hb_eq.symm)
          have huc : uc = up * uc₁ := Units.ext (by simp [uc, up, uc₁]; exact_mod_cast hc_eq.symm)
          refine ⟨a', b', c', ha', hb', hc', hc1, hc2, hc3, hs1, hs2, hs3, ?_, ?_⟩
          · rw [hzero]
            change HasTernaryZeroK (ua₁ : ℚ) (ub₁ : ℚ) (uc₁ : ℚ) ↔
              HasTernaryZeroK (ua : ℚ) (ub : ℚ) (uc : ℚ)
            have hsc := (hasTernaryZeroK_scale (a := (ua₁ : ℚ)) (b := (ub₁ : ℚ))
              (c := (uc₁ : ℚ)) up.ne_zero).symm
            have hsq := hasTernaryZeroK_scale_squares (a := (ua : ℚ)) (b := (ub : ℚ))
              (c := (uc : ℚ)) up.ne_zero one_ne_zero one_ne_zero
            have he1 : (up : ℚ) * (ua₁ : ℚ) = (ua : ℚ) * (up : ℚ) ^ 2 := by
              rw [hua₁, Units.val_mul]; ring
            have he2 : (up : ℚ) * (ub₁ : ℚ) = (ub : ℚ) * (1 : ℚ) ^ 2 := by
              rw [hub, Units.val_mul]; ring
            have he3 : (up : ℚ) * (uc₁ : ℚ) = (uc : ℚ) * (1 : ℚ) ^ 2 := by
              rw [huc, Units.val_mul]; ring
            rw [he1, he2, he3] at hsc
            exact hsc.trans hsq
          · intro v
            rw [hhilb v]
            change hilbertSymAt v (-ua₁ * uc₁) (-ub₁ * uc₁) = hilbertSymAt v (-ua * uc) (-ub * uc)
            rw [hua₁, hub, huc]
            have h1 : -(up * ua) * uc₁ = -ua * (up * uc₁) := by apply Units.ext; simp; ring
            have h2 : -(up * ub₁) * (up * uc₁) = (-ub₁ * uc₁) * up ^ 2 := by
              apply Units.ext; simp; ring
            rw [h1, h2]
            symm
            rw [hilbertSymAt_mul_right, hilbertSymAt_sq_right, mul_one]
    · -- Some prime p divides a and b
      have hg : Nat.gcd a.natAbs b.natAbs ≠ 1 := hAB
      let p := (Nat.gcd a.natAbs b.natAbs).minFac
      have hp : p.Prime := Nat.minFac_prime hg
      have hpdvd : p ∣ Nat.gcd a.natAbs b.natAbs := Nat.minFac_dvd _
      have hpa : p ∣ a.natAbs := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
      have hpb : p ∣ b.natAbs := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
      by_cases hpc : p ∣ c.natAbs
      · exact hstep_common_all p hp hpa hpb hpc
      · -- Replace (a, b, c) with (a/p, b/p, p*c)
        let a₁ : ℤ := a / (p : ℤ)
        let b₁ : ℤ := b / (p : ℤ)
        let c₁ : ℤ := (p : ℤ) * c
        have ha_eq : (p : ℤ) * a₁ = a := Int.mul_ediv_cancel' (Int.natCast_dvd.mpr hpa)
        have hb_eq : (p : ℤ) * b₁ = b := Int.mul_ediv_cancel' (Int.natCast_dvd.mpr hpb)
        have ha₁ : a₁ ≠ 0 := fun h => ha0 (by rw [← ha_eq, h, mul_zero])
        have hb₁ : b₁ ≠ 0 := fun h => hb0 (by rw [← hb_eq, h, mul_zero])
        have hc₁ : c₁ ≠ 0 := mul_ne_zero (Int.natCast_ne_zero.mpr hp.ne_zero) hc0
        have hA1 : a.natAbs = p * a₁.natAbs := by
          simpa [Int.natAbs_mul] using congrArg Int.natAbs ha_eq.symm
        have hB1 : b.natAbs = p * b₁.natAbs := by
          simpa [Int.natAbs_mul] using congrArg Int.natAbs hb_eq.symm
        have hC1 : c₁.natAbs = p * c.natAbs := by simp [c₁, Int.natAbs_mul]
        have hsqA1 : Squarefree a₁.natAbs := (Nat.squarefree_mul_iff.mp (hA1 ▸ hsqA)).2.2
        have hsqB1 : Squarefree b₁.natAbs := (Nat.squarefree_mul_iff.mp (hB1 ▸ hsqB)).2.2
        have hsqC1 : Squarefree c₁.natAbs := by
          rw [hC1]
          exact Nat.squarefree_mul_iff.mpr
            ⟨hp.coprime_iff_not_dvd.mpr hpc, hp.squarefree, hsqC⟩
        have hlt : a₁.natAbs * b₁.natAbs * c₁.natAbs < N := by
          rw [← hN, hA1, hB1, hC1]
          have h1 : 0 < a₁.natAbs * b₁.natAbs * c.natAbs := by
            have := Int.natAbs_pos.mpr ha₁; have := Int.natAbs_pos.mpr hb₁; positivity
          have hm1 : a₁.natAbs * b₁.natAbs * (p * c.natAbs) =
              p * (a₁.natAbs * b₁.natAbs * c.natAbs) := by ring
          have hm2 : p * a₁.natAbs * (p * b₁.natAbs) * c.natAbs =
              p * (p * (a₁.natAbs * b₁.natAbs * c.natAbs)) := by ring
          rw [hm1, hm2]
          exact Nat.mul_lt_mul_of_pos_left (lt_mul_of_one_lt_left h1 hp.one_lt) hp.pos
        obtain ⟨a', b', c', ha', hb', hc', hc1, hc2, hc3, hs1, hs2, hs3, hzero, hhilb⟩ :=
          ih _ hlt a₁ b₁ c₁ ha₁ hb₁ hc₁ rfl hsqA1 hsqB1 hsqC1
        let up : ℚˣ := primeUnit p hp
        let ua₁ : ℚˣ := Units.mk0 (a₁ : ℚ) (Int.cast_ne_zero.mpr ha₁)
        let ub₁ : ℚˣ := Units.mk0 (b₁ : ℚ) (Int.cast_ne_zero.mpr hb₁)
        let uc₁ : ℚˣ := Units.mk0 (c₁ : ℚ) (Int.cast_ne_zero.mpr hc₁)
        have hua : ua = up * ua₁ := Units.ext (by simp [ua, up, ua₁]; exact_mod_cast ha_eq.symm)
        have hub : ub = up * ub₁ := Units.ext (by simp [ub, up, ub₁]; exact_mod_cast hb_eq.symm)
        have huc₁ : uc₁ = up * uc := Units.ext (by simp [uc₁, up, uc, c₁])
        refine ⟨a', b', c', ha', hb', hc', hc1, hc2, hc3, hs1, hs2, hs3, ?_, ?_⟩
        · rw [hzero]
          change HasTernaryZeroK (ua₁ : ℚ) (ub₁ : ℚ) (uc₁ : ℚ) ↔
            HasTernaryZeroK (ua : ℚ) (ub : ℚ) (uc : ℚ)
          have hsc := (hasTernaryZeroK_scale (a := (ua₁ : ℚ)) (b := (ub₁ : ℚ))
            (c := (uc₁ : ℚ)) up.ne_zero).symm
          have hsq := hasTernaryZeroK_scale_squares (a := (ua : ℚ)) (b := (ub : ℚ))
            (c := (uc : ℚ)) one_ne_zero one_ne_zero up.ne_zero
          have he1 : (up : ℚ) * (ua₁ : ℚ) = (ua : ℚ) * (1 : ℚ) ^ 2 := by
            rw [hua, Units.val_mul]; ring
          have he2 : (up : ℚ) * (ub₁ : ℚ) = (ub : ℚ) * (1 : ℚ) ^ 2 := by
            rw [hub, Units.val_mul]; ring
          have he3 : (up : ℚ) * (uc₁ : ℚ) = (uc : ℚ) * (up : ℚ) ^ 2 := by
            rw [huc₁, Units.val_mul]; ring
          rw [he1, he2, he3] at hsc
          exact hsc.trans hsq
        · intro v
          rw [hhilb v]
          change hilbertSymAt v (-ua₁ * uc₁) (-ub₁ * uc₁) = hilbertSymAt v (-ua * uc) (-ub * uc)
          rw [hua, hub, huc₁]
          have h1 : -ua₁ * (up * uc) = -(up * ua₁) * uc := by apply Units.ext; simp; ring
          have h2 : -ub₁ * (up * uc) = -(up * ub₁) * uc := by apply Units.ext; simp; ring
          rw [h1, h2]

/-! ### 3D. Unconditional Hasse–Minkowski Theorems over `ℚ` (`0` Assumptions!) -/

/-- **UNCONDITIONAL HASSE–MINKOWSKI THEOREM FOR TERNARY QUADRATIC FORMS OVER `ℚ`
(Hilbert-Symbol Form, `0` ASSUMPTIONS!)**:
For EVERY `a, b, c ∈ ℚˣ`,
`a x² + b y² + c z² = 0` has a nontrivial solution in `ℚ` IFF `(-a*c, -b*c)_v = 1` at EVERY
place `v ∈ {∞, 2} ∪ OddPrime` of `ℚ`! -/
theorem hasse_minkowski_ternary_Q (a b c : ℚˣ) :
    HasTernaryZeroQ a b c ↔ ∀ v : QPlace, hilbertSymAt v (-a * c) (-b * c) = 1 := by
  constructor
  · intro hQ v
    have hK : HasTernaryZeroK (a : ℚ) (b : ℚ) (c : ℚ) := hQ
    rw [hasTernaryZeroK_iff_binary_norm (by norm_num : (2 : ℚ) ≠ 0) a.ne_zero c.ne_zero] at hK
    obtain ⟨u, v', huv⟩ := hK
    exact hilbertSymAt_eq_one_of_binary_norm ⟨u, v', by simpa using huv.symm⟩ v
  · intro hhilb
    obtain ⟨a₀, ha₀, ra, hsqA0, ha_eq⟩ := exists_squarefree_mul_sq_rat a
    obtain ⟨b₀, hb₀, rb, hsqB0, hb_eq⟩ := exists_squarefree_mul_sq_rat b
    obtain ⟨c₀, hc₀, rc, hsqC0, hc_eq⟩ := exists_squarefree_mul_sq_rat c
    let ua₀ : ℚˣ := Units.mk0 (a₀ : ℚ) (Int.cast_ne_zero.mpr ha₀)
    let ub₀ : ℚˣ := Units.mk0 (b₀ : ℚ) (Int.cast_ne_zero.mpr hb₀)
    let uc₀ : ℚˣ := Units.mk0 (c₀ : ℚ) (Int.cast_ne_zero.mpr hc₀)
    have hzero_sq : HasTernaryZeroQ a b c ↔ HasTernaryZeroQ ua₀ ub₀ uc₀ := by
      rw [ha_eq, hb_eq, hc_eq]
      change HasTernaryZeroK ((ua₀ : ℚ) * (ra : ℚ) ^ 2) ((ub₀ : ℚ) * (rb : ℚ) ^ 2)
        ((uc₀ : ℚ) * (rc : ℚ) ^ 2) ↔ HasTernaryZeroK (ua₀ : ℚ) (ub₀ : ℚ) (uc₀ : ℚ)
      exact hasTernaryZeroK_scale_squares ra.ne_zero rb.ne_zero rc.ne_zero
    have hhilb₀ : ∀ v : QPlace, hilbertSymAt v (-ua₀ * uc₀) (-ub₀ * uc₀) = 1 := by
      intro v
      have hv := hhilb v
      rw [ha_eq, hb_eq, hc_eq, hilbertSymAt_ternary_scale_squares v ua₀ ub₀ uc₀ ra rb rc] at hv
      exact hv
    obtain ⟨a', b', c', ha', hb', hc', hAB, hBC, hCA, hsqA, hsqB, hsqC, hzero_red, hhilb_red⟩ :=
      reduce_to_coprime_squarefree _ a₀ b₀ c₀ ha₀ hb₀ hc₀ rfl hsqA0 hsqB0 hsqC0
    let ua' : ℚˣ := Units.mk0 (a' : ℚ) (Int.cast_ne_zero.mpr ha')
    let ub' : ℚˣ := Units.mk0 (b' : ℚ) (Int.cast_ne_zero.mpr hb')
    let uc' : ℚˣ := Units.mk0 (c' : ℚ) (Int.cast_ne_zero.mpr hc')
    have hhilb' : ∀ v : QPlace, hilbertSymAt v (-ua' * uc') (-ub' * uc') = 1 := fun v =>
      (hhilb_red v).trans (hhilb₀ v)
    have hsign : ¬ (0 < a' * c' ∧ 0 < b' * c') := by
      rintro ⟨hac, hbc⟩
      have hinf := hhilb' QPlace.inf
      change hilbertSymInf (-ua' * uc') (-ub' * uc') = 1 at hinf
      unfold hilbertSymInf at hinf
      have h1 : ((-ua' * uc' : ℚˣ) : ℚ) < 0 := by
        simp only [ua', uc', Units.val_mul, Units.val_neg, Units.val_mk0, neg_mul, neg_lt_zero]
        exact_mod_cast hac
      have h2 : ((-ub' * uc' : ℚˣ) : ℚ) < 0 := by
        simp only [ub', uc', Units.val_mul, Units.val_neg, Units.val_mk0, neg_mul, neg_lt_zero]
        exact_mod_cast hbc
      rw [if_pos ⟨h1, h2⟩] at hinf
      exact (by decide : (-1 : ℤˣ) ≠ 1) hinf
    have hsq1 : IsSquare ((-b' * c' : ℤ) : ZMod a'.natAbs) :=
      isSquare_mod_of_hilbert_trivial ha' hb' hc' hAB hCA hsqA hhilb'
    have hsq2 : IsSquare ((-c' * a' : ℤ) : ZMod b'.natAbs) :=
      isSquare_mod_of_hilbert_trivial hb' hc' ha' hBC hAB hsqB (fun v => by
        calc hilbertSymAt v (-ub' * ua') (-uc' * ua')
            = hilbertSymAt v (-uc' * ua') (-ub' * ua') := hilbertSymAt_symm v _ _
          _ = hilbertSymAt v (-ua' * uc') (-ub' * uc') := hilbertSymAt_ternary_swap_ac v ua' ub' uc'
          _ = 1 := hhilb' v)
    have hsq3 : IsSquare ((-a' * b' : ℤ) : ZMod c'.natAbs) :=
      isSquare_mod_of_hilbert_trivial hc' ha' hb' hCA hBC hsqC (fun v => by
        calc hilbertSymAt v (-uc' * ub') (-ua' * ub')
            = hilbertSymAt v (-ua' * ub') (-uc' * ub') := hilbertSymAt_symm v _ _
          _ = hilbertSymAt v (-ua' * uc') (-ub' * uc') := hilbertSymAt_ternary_swap_bc v ua' ub' uc'
          _ = 1 := hhilb' v)
    obtain ⟨x, y, z, hne, heq⟩ :=
      (legendre_ternary_quadratic ha' hb' hc' hAB hBC hCA hsqA hsqB hsqC hsign).mpr
        ⟨hsq1, hsq2, hsq3⟩
    rw [hzero_sq, ← hzero_red]
    refine ⟨(x : ℚ), (y : ℚ), (z : ℚ), ?_, ?_⟩
    · rcases hne with h | h | h
      · exact Or.inl (Int.cast_ne_zero.mpr h)
      · exact Or.inr (Or.inl (Int.cast_ne_zero.mpr h))
      · exact Or.inr (Or.inr (Int.cast_ne_zero.mpr h))
    · simp only [Units.val_mk0]
      exact_mod_cast heq

/-- **UNCONDITIONAL HASSE–MINKOWSKI LOCAL-GLOBAL PRINCIPLE FOR TERNARY QUADRATIC FORMS OVER `ℚ`
(Local-Field Form, `0` ASSUMPTIONS!)**:
`a x² + b y² + c z² = 0` has a nontrivial solution in `ℚ` IFF it has a nontrivial solution in `ℝ`
AND in `ℚ_[p]` for EVERY prime `p`! -/
theorem hasse_minkowski_ternary_local_global_Q (a b c : ℚˣ) :
    HasTernaryZeroQ a b c ↔
      HasTernaryZeroReal a b c ∧ ∀ (p : ℕ) [Fact p.Prime], HasTernaryZeroPadic p a b c := by
  rw [hasse_minkowski_ternary_Q]
  constructor
  · intro h
    refine ⟨(hilbertSymInf_ternary_iff a b c).mp (h QPlace.inf), fun p hp => ?_⟩
    by_cases hp2 : p = 2
    · subst hp2
      have h2 := (hilbertSymTwo_ternary_iff a b c).mp (h QPlace.two)
      exact h2
    · exact (hilbertSymOdd_ternary_iff p hp2 a b c).mp (h (QPlace.odd ⟨p, Fact.out, hp2⟩))
  · rintro ⟨hR, hP⟩ v
    cases v with
    | inf => exact (hilbertSymInf_ternary_iff a b c).mpr hR
    | two => exact (hilbertSymTwo_ternary_iff a b c).mpr (@hP 2 ⟨Nat.prime_two⟩)
    | odd p =>
      have : Fact p.1.Prime := ⟨p.2.1⟩
      exact (hilbertSymOdd_ternary_iff p.1 p.2.2 a b c).mpr (hP p.1)

/-- **UNCONDITIONAL HASSE–MINKOWSKI BINARY NORM THEOREM OVER `ℚ` (`0` ASSUMPTIONS!)**:
For EVERY `a, b ∈ ℚˣ`, `b` is a norm from `ℚ(√a)` (`∃ x y : ℚ, x² - a y² = b`) IFF
`(a, b)_v = 1` at EVERY place `v` of `ℚ`! -/
theorem hasse_minkowski_binary_norm_Q (a b : ℚˣ) :
    (∃ x y : ℚ, x ^ 2 - (a : ℚ) * y ^ 2 = (b : ℚ)) ↔
      ∀ v : QPlace, hilbertSymAt v a b = 1 := by
  have htern : HasTernaryZeroQ a b (-1) ↔ ∃ x y : ℚ, x ^ 2 - (a : ℚ) * y ^ 2 = (b : ℚ) := by
    change HasTernaryZeroK (a : ℚ) (b : ℚ) (-1 : ℚ) ↔ _
    rw [hasTernaryZeroK_iff_binary_norm (by norm_num : (2 : ℚ) ≠ 0) a.ne_zero (by norm_num)]
    simp
  rw [← htern, hasse_minkowski_ternary_Q a b (-1)]
  have ha : -a * (-1 : ℚˣ) = a := by apply Units.ext; simp
  have hb : -b * (-1 : ℚˣ) = b := by apply Units.ext; simp
  rw [ha, hb]

end LegendreAndHasseMinkowski

/-! ## Section 4: Rational Quaternion Algebra Splitting & Legendre's Three-Squares Obstruction -/

section QuaternionAndThreeSquares

/-! ### 4A. Concrete Rational Quaternion Algebra `(a, b)_ℚ` & Splitting Criterion -/

/-- The concrete rational quaternion algebra `(a, b)_ℚ = QuaternionAlgebra ℚ a 0 b`
(`i² = a`, `j² = b`, `ij = -ji = k`). -/
abbrev RatQuatAlg (a b : ℚˣ) : Type :=
  QuaternionAlgebra ℚ (a : ℚ) 0 (b : ℚ)

/-- The reduced norm `nrd(q) = q.re² - a q.imI² - b q.imJ² + ab q.imK²` on `RatQuatAlg a b`. -/
def nrd {a b : ℚˣ} (q : RatQuatAlg a b) : ℚ :=
  q.re ^ 2 - (a : ℚ) * q.imI ^ 2 - (b : ℚ) * q.imJ ^ 2 + (a : ℚ) * (b : ℚ) * q.imK ^ 2

theorem mul_star_eq_nrd {a b : ℚˣ} (q : RatQuatAlg a b) :
    q * star q = ⟨nrd q, 0, 0, 0⟩ := by
  ext <;> simp [nrd, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> ring

theorem star_mul_eq_nrd {a b : ℚˣ} (q : RatQuatAlg a b) :
    star q * q = ⟨nrd q, 0, 0, 0⟩ := by
  ext <;> simp [nrd, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> ring

theorem nrd_mul {a b : ℚˣ} (p q : RatQuatAlg a b) :
    nrd (p * q) = nrd p * nrd q := by
  simp only [nrd, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul]
  ring

theorem nrd_zero (a b : ℚˣ) : nrd (0 : RatQuatAlg a b) = 0 := by
  simp [nrd]

/-- Explicit `ℚ`-algebra isomorphism `(a, b)_ℚ ≃ₐ[ℚ] M₂(ℚ)` from any binary norm witness
`x² - a y² = b`! -/
def ratQuatAlgSplitEquiv (a b : ℚˣ) {x y : ℚ} (hxy : x ^ 2 - (a : ℚ) * y ^ 2 = (b : ℚ)) :
    RatQuatAlg a b ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ where
  toFun q := !![q.re + q.imJ * x + q.imK * ((a : ℚ) * y),
                q.imI * (a : ℚ) - q.imJ * ((a : ℚ) * y) - q.imK * ((a : ℚ) * x);
                q.imI + q.imJ * y + q.imK * x,
                q.re - q.imJ * x - q.imK * ((a : ℚ) * y)]
  invFun M :=
    let p : ℚ := (M 0 0 - M 1 1) / 2
    let q : ℚ := ((a : ℚ) * M 1 0 - M 0 1) / (2 * (a : ℚ))
    ⟨(M 0 0 + M 1 1) / 2,
     (M 0 1 + (a : ℚ) * M 1 0) / (2 * (a : ℚ)),
     (x * p - (a : ℚ) * y * q) / (b : ℚ),
     (x * q - y * p) / (b : ℚ)⟩
  left_inv q := by
    rcases q with ⟨q0, q1, q2, q3⟩
    ext
    · simp
    · simp; field_simp [a.ne_zero]; ring
    · simp
      field_simp [a.ne_zero, b.ne_zero]
      rw [← hxy]; ring
    · simp
      field_simp [a.ne_zero, b.ne_zero]
      rw [← hxy]; ring
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp <;>
      field_simp [a.ne_zero, b.ne_zero] <;>
      rw [← hxy] <;> ring
  map_mul' p q := by
    rcases p with ⟨p0, p1, p2, p3⟩
    rcases q with ⟨q0, q1, q2, q3⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      rw [← hxy] <;> ring
  map_add' p q := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.algebraMap_eq_smul_one]

/-- The finite ramification locus `Ram(a, b) = {v : QPlace | (a, b)_v = -1}` of `(a, b)_ℚ`. -/
def ramifiedPlaces (a b : ℚˣ) : Finset QPlace :=
  Classical.choose (even_ramified_places a b)

theorem mem_ramifiedPlaces_iff (a b : ℚˣ) (v : QPlace) :
    v ∈ ramifiedPlaces a b ↔ hilbertSymAt v a b = -1 :=
  (Classical.choose_spec (even_ramified_places a b)).1 v

/-- **Even Finite Ramification Locus of `(a, b)_ℚ`** (directly from `Stage7GlobalDuality.hilbert_reciprocity`):
`Ram(a, b)` is finite and has EVEN cardinality! -/
theorem even_card_ramifiedPlaces (a b : ℚˣ) : Even (ramifiedPlaces a b).card :=
  (Classical.choose_spec (even_ramified_places a b)).2

/-- **Zero-Divisor Splitting Criterion for `(a, b)_ℚ`**:
`RatQuatAlg a b` has a zero divisor IFF `(a, b)_v = 1` at EVERY place `v` of `ℚ`! -/
theorem quaternion_has_zero_divisor_iff_hilbert_trivial (a b : ℚˣ) :
    (∃ p q : RatQuatAlg a b, p ≠ 0 ∧ q ≠ 0 ∧ p * q = 0) ↔
      ∀ v : QPlace, hilbertSymAt v a b = 1 := by
  constructor
  · rintro ⟨p, q, hp0, hq0, hpq⟩
    have hmul : nrd p * nrd q = 0 := by rw [← nrd_mul, hpq, nrd_zero]
    have hex0 : ∃ r : RatQuatAlg a b, r ≠ 0 ∧ nrd r = 0 := by
      rcases mul_eq_zero.mp hmul with h | h
      · exact ⟨p, hp0, h⟩
      · exact ⟨q, hq0, h⟩
    obtain ⟨r, hr0, hr_nrd⟩ := hex0
    have hbin : ∃ x y : ℚ, x ^ 2 - (a : ℚ) * y ^ 2 = (b : ℚ) := by
      by_cases hd : r.imJ ^ 2 - (a : ℚ) * r.imK ^ 2 = 0
      · -- Then a is a square in ℚˣ!
        have ha_sq : ∃ t : ℚ, t ^ 2 = (a : ℚ) := by
          by_cases hk : r.imK ≠ 0
          · refine ⟨r.imJ / r.imK, ?_⟩; field_simp [hk]; linarith
          · push Not at hk
            rw [hk] at hd
            have hj : r.imJ = 0 := eq_zero_of_pow_eq_zero (n := 2) (by linarith)
            have hi : r.imI ≠ 0 := by
              intro hi0
              have hre : r.re = 0 := by
                unfold nrd at hr_nrd
                rw [hi0, hj, hk] at hr_nrd
                exact eq_zero_of_pow_eq_zero (n := 2) (by linarith)
              exact hr0 (by ext <;> simp [hre, hi0, hj, hk])
            refine ⟨r.re / r.imI, ?_⟩
            unfold nrd at hr_nrd
            rw [hj, hk] at hr_nrd
            field_simp [hi]; linarith
        obtain ⟨t, ht⟩ := ha_sq
        have ht0 : t ≠ 0 := fun h => a.ne_zero (by rw [← ht, h]; norm_num)
        refine ⟨((b : ℚ) + 1) / 2, ((b : ℚ) - 1) / (2 * t), ?_⟩
        rw [← ht]; field_simp [ht0]; ring
      · -- Brahmagupta–Fibonacci quotient
        let d : ℚ := r.imJ ^ 2 - (a : ℚ) * r.imK ^ 2
        refine ⟨(r.re * r.imJ - (a : ℚ) * r.imI * r.imK) / d,
                (r.imI * r.imJ - r.re * r.imK) / d, ?_⟩
        have hnum : r.re ^ 2 - (a : ℚ) * r.imI ^ 2 = (b : ℚ) * d := by
          unfold nrd at hr_nrd; dsimp only [d]; linarith
        dsimp only [d] at hnum ⊢
        field_simp [hd]
        linear_combination (r.imJ ^ 2 - (a : ℚ) * r.imK ^ 2) * hnum
    exact (hasse_minkowski_binary_norm_Q a b).mp hbin
  · intro hhilb
    obtain ⟨x, y, hxy⟩ := (hasse_minkowski_binary_norm_Q a b).mpr hhilb
    let q : RatQuatAlg a b := ⟨x, y, 1, 0⟩
    have hq0 : q ≠ 0 := by intro h; have := congrArg QuaternionAlgebra.imJ h; norm_num [q] at this
    have hsq0 : star q ≠ 0 := by
      intro h
      apply hq0
      have := congrArg star h
      simpa using this
    have hnrd0 : nrd q = 0 := by dsimp only [nrd, q]; linarith
    refine ⟨q, star q, hq0, hsq0, ?_⟩
    rw [mul_star_eq_nrd, hnrd0]; rfl

/-- **UNCONDITIONAL QUATERNION ALGEBRA SPLITTING THEOREM OVER `ℚ` (`0` ASSUMPTIONS!)**:
The rational quaternion algebra `(a, b)_ℚ` splits over `ℚ` (`(a, b)_ℚ ≃ₐ[ℚ] M₂(ℚ)`) IFF
`(a, b)_v = 1` at EVERY place `v` of `ℚ` (equivalently, `ramifiedPlaces a b = ∅`)! -/
theorem quaternion_splits_iff_hilbert_trivial (a b : ℚˣ) :
    Nonempty (RatQuatAlg a b ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) ↔
      ∀ v : QPlace, hilbertSymAt v a b = 1 := by
  constructor
  · rintro ⟨e⟩
    apply (quaternion_has_zero_divisor_iff_hilbert_trivial a b).mp
    let E1 : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 0]
    let E2 : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 0, 1]
    have hE1 : E1 ≠ 0 := by intro h; have := congrFun (congrFun h 0) 0; norm_num [E1] at this
    have hE2 : E2 ≠ 0 := by intro h; have := congrFun (congrFun h 1) 1; norm_num [E2] at this
    have hE12 : E1 * E2 = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [E1, E2, Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨e.symm E1, e.symm E2, fun h => hE1 (e.symm.injective (by simpa using h)),
      fun h => hE2 (e.symm.injective (by simpa using h)), ?_⟩
    rw [← map_mul, hE12, map_zero]
  · intro hhilb
    obtain ⟨x, y, hxy⟩ := (hasse_minkowski_binary_norm_Q a b).mpr hhilb
    exact ⟨ratQuatAlgSplitEquiv a b hxy⟩

theorem quaternion_splits_iff_ramifiedPlaces_empty (a b : ℚˣ) :
    Nonempty (RatQuatAlg a b ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) ↔ ramifiedPlaces a b = ∅ := by
  rw [quaternion_splits_iff_hilbert_trivial, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h v hv
    rw [mem_ramifiedPlaces_iff, h v] at hv
    exact (by decide : (1 : ℤˣ) ≠ -1) hv
  · intro h v
    rcases intUnits_eq_one_or_neg_one (hilbertSymAt v a b) with h1 | h1
    · exact h1
    · exact absurd ((mem_ramifiedPlaces_iff a b v).mpr h1) (h v)

/-! ### 4B. Legendre's Three-Squares Obstruction via `hilbertSymTwo` -/

/-- The `2`-adic Hilbert symbol `(-1, 4^k * (8*m + 7))_2 = -1` for every `k, m : ℕ`. -/
theorem hilbertSymTwo_neg_one_four_pow_mul_eight_add_seven (k m : ℕ) :
    hilbertSymTwo (-1)
      (Units.mk0 (((4 ^ k * (8 * m + 7) : ℕ) : ℚ)) (Nat.cast_ne_zero.mpr (by positivity))) = -1 := by
  have h8m7_ne : (8 * m + 7 : ℕ) ≠ 0 := by omega
  let u : ℚˣ := Units.mk0 ((8 * m + 7 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr h8m7_ne)
  let r : ℚˣ := Units.mk0 ((2 ^ k : ℕ) : ℚ) (Nat.cast_ne_zero.mpr (by positivity))
  have heq : Units.mk0 (((4 ^ k * (8 * m + 7) : ℕ) : ℚ)) (Nat.cast_ne_zero.mpr (by positivity)) =
      u * r ^ 2 := by
    apply Units.ext
    simp only [u, r, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    have h4 : ((4 : ℚ) ^ k) = ((2 : ℚ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    push_cast; rw [h4]; ring
  rw [heq, hilbertSymTwo_mul_right, hilbertSymTwo_symm (-1) (r ^ 2), hilbertSymTwo_sq_left, mul_one]
  have hv : padicValRat 2 (u : ℚ) = 0 := by
    change padicValRat 2 ((8 * m + 7 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by omega), Nat.cast_zero]
  have hred : redMod8 (u : ℚ) = 7 := by
    change redMod8 ((8 * m + 7 : ℕ) : ℚ) = 7
    rw [redMod8_natCast]
    push_cast
    have h8 : (8 : ZMod 8) = 0 := rfl
    rw [h8, zero_mul, zero_add]
  unfold hilbertSymTwo
  rw [twoCoords_neg_one]
  unfold twoCoords
  rw [pUnit_of_val_zero 2 Nat.prime_two hv, hv, Int.cast_zero, hred]
  decide

private theorem eps8_seven : eps8 7 = 1 := by decide
private theorem eps8_seven_sub_four_sq (r : ZMod 8) : eps8 (7 - 4 * r ^ 2) = 1 := by
  fin_cases r <;> decide
private theorem eps8_of_two_mul_eq_six (x : ZMod 8) (h : 2 * x = 6) : eps8 x = 1 := by
  revert h; fin_cases x <;> decide
private theorem eps8_four_mul_seven_sub_one : eps8 ((4 : ZMod 8) ^ 1 * 7 - 1) = 1 := by decide
private theorem eps8_zero_sub_one : eps8 (0 - 1 : ZMod 8) = 1 := by decide

/-- Core `2`-adic Hilbert-symbol obstruction for sums of three squares:
for EVERY `m : ℕ` and EVERY `w : ℚ`, `t = (8*m + 7) - w²` is nonzero and satisfies
`(-1, (8*m + 7) - w²)_2 = -1`! -/
theorem hilbertSymTwo_neg_one_eight_add_seven_sub_sq (m : ℕ) (w : ℚ) :
    ∃ hne : ((8 * m + 7 : ℕ) : ℚ) - w ^ 2 ≠ 0,
      hilbertSymTwo (-1) (Units.mk0 (((8 * m + 7 : ℕ) : ℚ) - w ^ 2) hne) = -1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8m7_pos : 0 < (8 * m + 7 : ℕ) := by omega
  let u : ℚˣ := Units.mk0 ((8 * m + 7 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr h8m7_pos.ne')
  have hu_val : padicValRat 2 (u : ℚ) = 0 := by
    change padicValRat 2 ((8 * m + 7 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by omega), Nat.cast_zero]
  have hu_red : redMod8 (u : ℚ) = 7 := by
    change redMod8 ((8 * m + 7 : ℕ) : ℚ) = 7
    rw [redMod8_natCast]; push_cast
    have h8 : (8 : ZMod 8) = 0 := rfl
    rw [h8, zero_mul, zero_add]
  have hne : ((8 * m + 7 : ℕ) : ℚ) - w ^ 2 ≠ 0 := by
    intro h0
    have hw_sq : w ^ 2 = (u : ℚ) := by change w ^ 2 = ((8 * m + 7 : ℕ) : ℚ); linarith
    have hw0 : w ≠ 0 := by intro hw; rw [hw, zero_pow two_ne_zero] at hw_sq; exact u.ne_zero hw_sq.symm
    have hsq_u : (Units.mk0 w hw0) ^ 2 = u := Units.ext (by simpa using hw_sq)
    have hsym := hilbertSymTwo_neg_one_four_pow_mul_eight_add_seven 0 m
    have hu_eq : Units.mk0 (((4 ^ 0 * (8 * m + 7) : ℕ) : ℚ)) (Nat.cast_ne_zero.mpr (by positivity)) = u :=
      Units.ext (by simp [u])
    rw [hu_eq, ← hsq_u, hilbertSymTwo_symm, hilbertSymTwo_sq_left] at hsym
    exact (by decide : (1 : ℤˣ) ≠ -1) hsym
  refine ⟨hne, ?_⟩
  let t : ℚˣ := Units.mk0 (((8 * m + 7 : ℕ) : ℚ) - w ^ 2) hne
  -- Need to show eps8 (redMod8 (pUnit 2 Nat.prime_two t)) = 1
  suffices heps : eps8 (redMod8 (pUnit 2 Nat.prime_two t : ℚ)) = 1 by
    unfold hilbertSymTwo
    rw [twoCoords_neg_one]
    change negOnePowZMod2 (1 * eps8 (redMod8 (pUnit 2 Nat.prime_two t : ℚ)) + 0 * _ + _ * 0) = -1
    rw [heps, one_mul, zero_mul, mul_zero, add_zero, add_zero]
    exact negOnePowZMod2_one
  have hdu : ¬ 2 ∣ (u : ℚ).den :=
    not_dvd_den_of_nonneg_padicValRat Nat.prime_two (le_of_eq hu_val.symm)
  by_cases hw0 : w = 0
  · have htu : t = u := Units.ext (by simp [t, u, hw0])
    rw [htu, pUnit_of_val_zero 2 Nat.prime_two hu_val, hu_red]
    exact eps8_seven
  · rcases lt_trichotomy 0 (padicValRat 2 w) with hw_pos | hw_zero | hw_neg
    · -- Case 1: v_2(w) > 0, so v_2(w^2) >= 2, v_2(t) = 0, redMod8 t ∈ {3, 7}
      have hw2_val : 2 ≤ padicValRat 2 (w ^ 2) := by
        rw [sq, padicValRat.mul hw0 hw0]; omega
      have ht_val : padicValRat 2 (t : ℚ) = 0 := by
        have hadd_ne : (u : ℚ) + -(w ^ 2) ≠ 0 := by
          rw [← sub_eq_add_neg]; exact hne
        have hne_val : padicValRat 2 (u : ℚ) ≠ padicValRat 2 (-(w ^ 2)) := by
          rw [hu_val, padicValRat.neg]; omega
        change padicValRat 2 (((8 * m + 7 : ℕ) : ℚ) - w ^ 2) = 0
        rw [sub_eq_add_neg]
        change padicValRat 2 ((u : ℚ) + -(w ^ 2)) = 0
        rw [padicValRat.add_eq_min hadd_ne u.ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hw0)) hne_val,
          hu_val, padicValRat.neg]
        exact min_eq_left (by omega)
      have hdw2 : ¬ 2 ∣ (w ^ 2).den :=
        not_dvd_den_of_nonneg_padicValRat Nat.prime_two (by omega)
      -- w/2 has nonneg valuation, so w^2 = 4 * (w/2)^2
      let s : ℚ := w / 2
      have hs_ge : 0 ≤ padicValRat 2 s := by
        dsimp only [s]
        rw [padicValRat.div hw0 (by norm_num), show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
          padicValRat.self (by norm_num : 1 < 2)]
        omega
      have hds : ¬ 2 ∣ s.den := not_dvd_den_of_nonneg_padicValRat Nat.prime_two hs_ge
      have hds2 : ¬ 2 ∣ (s ^ 2).den := by
        rw [sq]; intro hd
        rcases Nat.prime_two.dvd_mul.mp (dvd_trans hd (Rat.mul_den_dvd s s)) with h | h <;> exact hds h
      have hw2_eq : w ^ 2 = 4 * s ^ 2 := by dsimp only [s]; ring
      have hred_w2 : redMod8 (w ^ 2) = 4 * (redMod8 s) ^ 2 := by
        rw [hw2_eq, redMod8_mul (by simp) hds2, show (4 : ℚ) = ((4 : ℕ) : ℚ) by norm_num,
          redMod8_natCast, sq, redMod8_mul hds hds, ← sq]; norm_num
      rw [pUnit_of_val_zero 2 Nat.prime_two ht_val]
      have hred_t : redMod8 (t : ℚ) = 7 - 4 * (redMod8 s) ^ 2 := by
        change redMod8 ((u : ℚ) - w ^ 2) = _
        rw [redMod8_sub hdu hdw2, hu_red, hred_w2]
      rw [hred_t]
      exact eps8_seven_sub_four_sq (redMod8 s)
    · -- Case 2: v_2(w) = 0, so w^2 ≡ 1 (mod 8), t ≡ 6 (mod 8), v_2(t) = 1, redMod8 (t/2) ∈ {3, 7}
      have hw2_val : padicValRat 2 (w ^ 2) = 0 := by
        rw [sq, padicValRat.mul hw0 hw0, ← hw_zero, add_zero]
      have hdw : ¬ 2 ∣ w.den := not_dvd_den_of_nonneg_padicValRat Nat.prime_two (le_of_eq hw_zero)
      have hdw2 : ¬ 2 ∣ (w ^ 2).den := not_dvd_den_of_nonneg_padicValRat Nat.prime_two (le_of_eq hw2_val.symm)
      have hw_odd : (redMod8 w).val % 2 = 1 := redMod8_odd_of_val_eq_zero hw0 hw_zero.symm
      have hw2_red : redMod8 (w ^ 2) = 1 := by
        rw [sq, redMod8_mul hdw hdw]
        exact zmod8_odd_sq_eq_one _ hw_odd
      have ht_red : redMod8 (t : ℚ) = 6 := by
        change redMod8 ((u : ℚ) - w ^ 2) = 6
        rw [redMod8_sub hdu hdw2, hu_red, hw2_red]; decide
      have hdt : ¬ 2 ∣ (t : ℚ).den := by
        change ¬ 2 ∣ ((u : ℚ) - w ^ 2).den
        rw [sub_eq_add_neg]
        intro hd
        have hdiv : ((u : ℚ) + -(w ^ 2)).den ∣ (u : ℚ).den * (-(w ^ 2)).den :=
          Rat.add_den_dvd (u : ℚ) (-(w ^ 2))
        rw [Rat.neg_den] at hdiv
        rcases Nat.prime_two.dvd_mul.mp (dvd_trans hd hdiv) with h | h
        · exact hdu h
        · exact hdw2 h
      -- Show v_2(t) = 1 from redMod8 t = 6 (which is 2 mod 4, so 2 ∣ t.num and 4 ∤ t.num)
      have ht_val : padicValRat 2 (t : ℚ) = 1 := by
        have hnum_mod8 : ((t : ℚ).num : ZMod 8) = 6 * ((t : ℚ).den : ZMod 8) := by
          have hsqd := zmod8_odd_sq_eq_one _ (nat_cast_zmod8_odd hdt)
          unfold redMod8 at ht_red
          calc ((t : ℚ).num : ZMod 8)
              = ((t : ℚ).num : ZMod 8) * (((t : ℚ).den : ZMod 8) * ((t : ℚ).den : ZMod 8)) := by
                  rw [hsqd, mul_one]
            _ = (((t : ℚ).num : ZMod 8) * ((t : ℚ).den : ZMod 8)) * ((t : ℚ).den : ZMod 8) := by ring
            _ = 6 * ((t : ℚ).den : ZMod 8) := by rw [ht_red]
        have hnum_m4 : ((t : ℚ).num : ZMod 8).val % 4 = 2 := by
          rw [hnum_mod8]
          have hd_odd := nat_cast_zmod8_odd hdt
          have hdec : ∀ d : ZMod 8, d.val % 2 = 1 → (6 * d).val % 4 = 2 := by decide
          exact hdec _ hd_odd
        have hnum_z : (t : ℚ).num % 4 = 2 := by
          have hv : (((t : ℚ).num : ZMod 8).val : ℤ) = (t : ℚ).num % 8 := ZMod.val_intCast _
          omega
        have h2dvd : 2 ∣ (t : ℚ).num.natAbs := by omega
        have h4ndvd : ¬ 4 ∣ (t : ℚ).num.natAbs := by omega
        have hnum_v1 : padicValNat 2 (t : ℚ).num.natAbs = 1 := by
          have hge1 : 1 ≤ padicValNat 2 (t : ℚ).num.natAbs :=
            one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr t.ne_zero)) h2dvd
          have hlt2 : padicValNat 2 (t : ℚ).num.natAbs < 2 := by
            by_contra hge2
            push Not at hge2
            have h4 : 2 ^ 2 ∣ (t : ℚ).num.natAbs :=
              (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr t.ne_zero))).mpr hge2
            exact h4ndvd h4
          omega
        rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hdt]
        change (padicValNat 2 (t : ℚ).num.natAbs : ℤ) - 0 = 1
        omega
      -- Now t = 2 * pUnit 2 t, so 2 * redMod8 (pUnit 2 t) = redMod8 t = 6 in ZMod 8!
      have hpu_val : padicValRat 2 (pUnit 2 Nat.prime_two t : ℚ) = 0 :=
        padicValRat_pUnit 2 Nat.prime_two t
      have hdpu : ¬ 2 ∣ (pUnit 2 Nat.prime_two t : ℚ).den :=
        not_dvd_den_of_nonneg_padicValRat Nat.prime_two (le_of_eq hpu_val.symm)
      have ht_eq2 : (t : ℚ) = 2 * (pUnit 2 Nat.prime_two t : ℚ) := by
        have hs := congrArg (fun x : ℚˣ => (x : ℚ)) (pUnit_spec 2 Nat.prime_two t)
        rw [ht_val, zpow_one, Units.val_mul, coe_primeUnit] at hs
        simpa using hs
      have h2red : (2 : ZMod 8) * redMod8 (pUnit 2 Nat.prime_two t : ℚ) = 6 := by
        rw [← ht_red, ht_eq2, redMod8_mul (by simp) hdpu]
        have h2r : redMod8 (2 : ℚ) = 2 := by
          rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, redMod8_natCast]; rfl
        rw [h2r]
      exact eps8_of_two_mul_eq_six _ h2red
    · -- Case 3: v_2(w) < 0, let r = (-v_2(w)).toNat ≥ 1; multiply t by 2^(2r) = 4^r
      set r : ℕ := (-padicValRat 2 w).toNat
      have hr_pos : 1 ≤ r := by omega
      have hr_eq : (r : ℤ) = -padicValRat 2 w := Int.toNat_of_nonneg (by omega)
      have hw2_val : padicValRat 2 (w ^ 2) = -(2 * (r : ℤ)) := by
        rw [sq, padicValRat.mul hw0 hw0]; omega
      have ht_val : padicValRat 2 (t : ℚ) = -(2 * (r : ℤ)) := by
        have hadd_ne : (u : ℚ) + -(w ^ 2) ≠ 0 := by rw [← sub_eq_add_neg]; exact hne
        have hne_val : padicValRat 2 (u : ℚ) ≠ padicValRat 2 (-(w ^ 2)) := by
          rw [hu_val, padicValRat.neg, hw2_val]; omega
        change padicValRat 2 ((u : ℚ) - w ^ 2) = _
        rw [sub_eq_add_neg,
          padicValRat.add_eq_min hadd_ne u.ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hw0)) hne_val,
          hu_val, padicValRat.neg, hw2_val]
        exact min_eq_right (by omega)
      -- pUnit 2 t = 2^(2r) * t = 4^r * u - (2^r * w)^2
      let w' : ℚ := (2 : ℚ) ^ r * w
      have hw'0 : w' ≠ 0 := mul_ne_zero (pow_ne_zero r (by norm_num)) hw0
      have hw'_val : padicValRat 2 w' = 0 := by
        dsimp only [w']
        rw [padicValRat.mul (pow_ne_zero r (by norm_num)) hw0,
          show (2 : ℚ) ^ r = ((2 ^ r : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
          padicValNat.prime_pow r]
        omega
      have hdw' : ¬ 2 ∣ w'.den := not_dvd_den_of_nonneg_padicValRat Nat.prime_two (le_of_eq hw'_val.symm)
      have hdw'2 : ¬ 2 ∣ (w' ^ 2).den := by
        rw [sq]; intro hd
        rcases Nat.prime_two.dvd_mul.mp (dvd_trans hd (Rat.mul_den_dvd w' w')) with h | h <;> exact hdw' h
      have hw'2_red : redMod8 (w' ^ 2) = 1 := by
        rw [sq, redMod8_mul hdw' hdw']
        exact zmod8_odd_sq_eq_one _ (redMod8_odd_of_val_eq_zero hw'0 hw'_val)
      have hpu_eq : (pUnit 2 Nat.prime_two t : ℚ) = ((4 ^ r : ℕ) : ℚ) * (u : ℚ) - w' ^ 2 := by
        unfold pUnit
        rw [ht_val, neg_neg, Units.val_mul, Units.val_zpow_eq_zpow_val, coe_primeUnit]
        change ((u : ℚ) - w ^ 2) * ((2 : ℕ) : ℚ) ^ (2 * (r : ℤ)) = _
        rw [show (2 : ℤ) * (r : ℤ) = ((2 * r : ℕ) : ℤ) by omega, zpow_natCast]
        dsimp only [w']
        have h4r : ((4 ^ r : ℕ) : ℚ) = ((2 : ℕ) : ℚ) ^ (2 * r) := by
          push_cast; rw [pow_mul]; norm_num
        rw [h4r]; push_cast; rw [mul_pow, ← pow_mul, mul_comm r 2]; ring
      have hd4u : ¬ 2 ∣ (((4 ^ r : ℕ) : ℚ) * (u : ℚ)).den := by
        intro hd
        rcases Nat.prime_two.dvd_mul.mp (dvd_trans hd (Rat.mul_den_dvd _ _)) with h | h
        · simp at h
        · exact hdu h
      rw [hpu_eq, redMod8_sub hd4u hdw'2, redMod8_mul (by simp) hdu, redMod8_natCast,
        hu_red, hw'2_red, Nat.cast_pow, Nat.cast_ofNat]
      rcases eq_or_lt_of_le hr_pos with hr1 | hr_ge2
      · rw [← hr1]; exact eps8_four_mul_seven_sub_one
      · have h4r0 : (4 : ZMod 8) ^ r = 0 := by
          obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (show 2 ≤ r from hr_ge2)
          rw [hj, pow_add]
          have h42 : (4 : ZMod 8) ^ 2 = 0 := by decide
          rw [h42, zero_mul]
        rw [h4r0, zero_mul]; exact eps8_zero_sub_one

/-- **LEGENDRE'S THREE-SQUARES OBSTRUCTION OVER `ℚ` (Unconditional, via `hilbertSymTwo`)**:
For EVERY `k, m : ℕ`, `n = 4^k * (8*m + 7)` is NOT a sum of three rational squares! -/
theorem not_sum_three_squares_of_four_pow_mul_eight_add_seven (k m : ℕ) :
    ¬ ∃ x y z : ℚ, x ^ 2 + y ^ 2 + z ^ 2 = ((4 ^ k * (8 * m + 7) : ℕ) : ℚ) := by
  rintro ⟨x, y, z, hxyz⟩
  have h2k : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  let x' : ℚ := x / (2 : ℚ) ^ k
  let y' : ℚ := y / (2 : ℚ) ^ k
  let z' : ℚ := z / (2 : ℚ) ^ k
  have hred : x' ^ 2 + y' ^ 2 + z' ^ 2 = ((8 * m + 7 : ℕ) : ℚ) := by
    dsimp only [x', y', z']
    have h4 : ((4 ^ k * (8 * m + 7) : ℕ) : ℚ) = ((2 : ℚ) ^ k) ^ 2 * ((8 * m + 7 : ℕ) : ℚ) := by
      push_cast; rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
    rw [h4] at hxyz
    field_simp [h2k]
    linarith
  obtain ⟨hne, hobs⟩ := hilbertSymTwo_neg_one_eight_add_seven_sub_sq m z'
  have hnorm : ∃ u v : ℚ, (Units.mk0 (((8 * m + 7 : ℕ) : ℚ) - z' ^ 2) hne : ℚ) =
      u ^ 2 - ((-1 : ℚˣ) : ℚ) * v ^ 2 :=
    ⟨x', y', by simp only [Units.val_mk0, Units.val_neg, Units.val_one]; linarith⟩
  exact not_binary_norm_of_local_obstruction ⟨QPlace.two, hobs⟩ hnorm

/-- **Legendre's Three-Squares Obstruction over `ℤ`**:
No integer `4^k * (8*m + 7)` is a sum of three integer squares. -/
theorem not_sum_three_int_squares_of_four_pow_mul_eight_add_seven (k m : ℕ) :
    ¬ ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = (4 ^ k * (8 * m + 7) : ℤ) := by
  rintro ⟨x, y, z, hxyz⟩
  apply not_sum_three_squares_of_four_pow_mul_eight_add_seven k m
  exact ⟨(x : ℚ), (y : ℚ), (z : ℚ), by exact_mod_cast hxyz⟩

/-- **Legendre's Three-Squares Obstruction over `ℕ`**:
No natural number `4^k * (8*m + 7)` is a sum of three natural squares. -/
theorem not_sum_three_nat_squares_of_four_pow_mul_eight_add_seven (k m : ℕ) :
    ¬ ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = 4 ^ k * (8 * m + 7) := by
  rintro ⟨x, y, z, hxyz⟩
  apply not_sum_three_squares_of_four_pow_mul_eight_add_seven k m
  exact ⟨(x : ℚ), (y : ℚ), (z : ℚ), by exact_mod_cast hxyz⟩

end QuaternionAndThreeSquares

end

end RHDirect.Stage8HasseMinkowski
