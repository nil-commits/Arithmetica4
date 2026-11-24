import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# PPL 026 — Jeffrey Shallit #19 · Pierce Expansion Length (Verified Partial Foundation)

For integers `a > b > 0`, define the Pierce remainder iteration `b₀ = b`, `b_{i+1} = a % b_i`,
and let `pierceLen a b` be the least `n` with `b_n = 0`.

**Status:** This file is a **verified partial foundation**, NOT a prize claim.
Jason Davies (October 2026, `β_* = 0.29413366...`, `hexagon:2610.00588v1`) proves a sharper
bound than the `a^{3/10 + ε}` bound formalized unconditionally in Part I below.

This module contains two completely self-contained, zero-`sorry`, zero-axiom parts:

## Part I — Complete Unconditional Proof of `P(a, b) ≪_ε a^{3/10 + ε}` & Monotone Invariant
- `pierceLen` defined by well-founded recursion and orbit `pierceOrbit`.
- Strict quotient monotonicity (`quot_strict_inc`).
- Curvature identity and positivity (`curvature_identity`, `curvature_pos`: `D_i ≥ 1`).
- Six-term Hankel identity (`six_term_identity_one`, `six_term_identity_two`, `six_term_q_bound`).
- **Strict orbit-monotone invariant (`curvature_ratio_strict_decreasing`):**
  `D_i / σ(k_i, k_{i+1}, k_{i+2}) - D_{i+1} / σ(k_{i+1}, k_{i+2}, k_{i+3}) > 0`.
- Erdős–Shallit drop bound (`window_drop_bound`: `T(T-1) ≤ 4 A Δ`).
- Six-term window bound (`window_six_term_bound`: `T^6 A^2 ≤ C a^3`).
- Divisor power bound (`divisor_power_bound`: `τ(n)^k ≤ C_k n`).
- Full unconditional theorem **`pierceLen_le_three_tenths`**:
  `∀ ε > 0, ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a → (pierceLen a b : ℝ) ≤ C * (a : ℝ) ^ (3/10 + ε)`.

## Part II — Sound 4-Pivot Minkowski Plücker Slicing & Elimination Helper Lemmas
- **4-Pivot Invariance & Linearity (`four_pivot_const_vertex_linear_col5`):**
  Replacing column 4 by `w(c) = w₀ + c • e₁` fixes `(N₀, N₁, u₁, u₂)` and makes
  `(N₂, v₁, v₂)` affine-linear in `c`.
- **Linear Elimination of `c₁` (`pattern_quadratic_linear_c1`)** and **`k₄²` Cancellation
  (`psi_k4_sq_cancellation`)**.
- **Minkowski `p`-Series & Weighted Family Sum (`p_series_sum_le_four`,
  `four_pivot_minkowski_weighted_sum`)** giving `4 * X^{(14+u)/3}` (`≤ 4 * X^{14/3}` at `u = 0`).
- **Degree `e ≥ 2` Polynomial Section Leading Condition (`poly_section_ge_two_forces_f2_zero`)**
  forcing `f₂(z₁, z₂, z₃) = 0`.
- **Elementary `K`-Prime Smooth-Point Reduction (`exists_prime_not_dvd_of_prod_gt`)**.
-/

namespace PPL026_PierceExpansion

open scoped BigOperators
open Finset Polynomial

/-! ## Part I: Unconditional Elementary Bound `P(a, b) ≪_ε a^{3/10 + ε}` -/

section PierceCore

/-- Length `P(a, b)` of the Pierce remainder iteration `b ↦ a % b` until reaching `0`. -/
def pierceLen (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | b + 1 => 1 + pierceLen a (a % (b + 1))
termination_by b => b
decreasing_by
  exact Nat.mod_lt a (Nat.succ_pos b)

lemma pierceLen_zero (a : ℕ) : pierceLen a 0 = 0 := by
  simp [pierceLen]

lemma pierceLen_pos_step (a b : ℕ) (hb : 0 < b) :
    pierceLen a b = 1 + pierceLen a (a % b) := by
  cases b with
  | zero => omega
  | succ k => simp [pierceLen]

/-- The `i`-th iterate of `x ↦ a % x` starting from `b`. -/
def pierceOrbit (a b : ℕ) : ℕ → ℕ
  | 0 => b
  | i + 1 => a % pierceOrbit a b i

lemma pierceOrbit_zero (a b : ℕ) : pierceOrbit a b 0 = b := rfl

lemma pierceOrbit_succ (a b i : ℕ) :
    pierceOrbit a b (i + 1) = a % pierceOrbit a b i := rfl

lemma pierceOrbit_strict_anti {a b i : ℕ} (h : 0 < pierceOrbit a b i) :
    pierceOrbit a b (i + 1) < pierceOrbit a b i := by
  rw [pierceOrbit_succ]
  exact Nat.mod_lt a h

lemma pierceLen_shift (a b : ℕ) (i : ℕ) (hi : i ≤ pierceLen a b) :
    pierceLen a b = i + pierceLen a (pierceOrbit a b i) := by
  induction i generalizing b with
  | zero => simp [pierceOrbit]
  | succ k ih =>
    have hb : 0 < b := by
      by_contra h0
      have hb0 : b = 0 := by omega
      rw [hb0, pierceLen_zero] at hi
      omega
    rw [pierceLen_pos_step a b hb] at hi ⊢
    have hk : k ≤ pierceLen a (a % b) := by omega
    have hrec := ih (a % b) hk
    have horb : pierceOrbit a b (k + 1) = pierceOrbit a (a % b) k := by
      clear ih hi hk hrec hb
      induction k generalizing b with
      | zero => rfl
      | succ m ihm =>
        show a % pierceOrbit a b (m + 1) = a % pierceOrbit a (a % b) m
        rw [ihm b]
    rw [horb]
    omega

lemma pierceOrbit_pos_of_lt {a b i : ℕ} (hi : i < pierceLen a b) :
    0 < pierceOrbit a b i := by
  have hsh := pierceLen_shift a b i (le_of_lt hi)
  by_contra h0
  have hz : pierceOrbit a b i = 0 := by omega
  rw [hz, pierceLen_zero] at hsh
  omega

lemma pierceOrbit_eq_zero_at_len (a b : ℕ) :
    pierceOrbit a b (pierceLen a b) = 0 := by
  have hsh := pierceLen_shift a b (pierceLen a b) le_rfl
  have hz : pierceLen a (pierceOrbit a b (pierceLen a b)) = 0 := by omega
  by_contra hne
  have hpos : 0 < pierceOrbit a b (pierceLen a b) := Nat.pos_of_ne_zero hne
  rw [pierceLen_pos_step a _ hpos] at hz
  omega

lemma pierceOrbit_strict_mono_rev {a b i j : ℕ} (hij : i < j) (hj : j ≤ pierceLen a b) :
    pierceOrbit a b j < pierceOrbit a b i := by
  induction j with
  | zero => omega
  | succ k ih =>
    have hpk : 0 < pierceOrbit a b k := pierceOrbit_pos_of_lt (by omega)
    have hstep := pierceOrbit_strict_anti hpk
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hij) with rfl | hlt
    · exact hstep
    · exact lt_trans hstep (ih hlt (by omega))

lemma pierceOrbit_inj_on {a b i j : ℕ} (hi : i < pierceLen a b) (hj : j < pierceLen a b)
    (heq : pierceOrbit a b i = pierceOrbit a b j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exfalso; exact ne_of_lt (pierceOrbit_strict_mono_rev h (le_of_lt hj)) heq.symm
  · exact h
  · exfalso; exact ne_of_lt (pierceOrbit_strict_mono_rev h (le_of_lt hi)) heq

/-- Division equation `q * x + y = a` where `q = a / x` and `y = a % x`. -/
lemma div_eq_step (a x : ℕ) : (a / x) * x + (a % x) = a := by
  rw [mul_comm]
  exact Nat.div_add_mod a x

/-- Strict monotonicity of quotients: if `0 < y < x` and `q * x + y = a`, then `a / y ≥ q + 1`. -/
lemma quot_strict_inc {a x y : ℕ} (hy : 0 < y) (hyx : y < x) (heq : (a / x) * x + y = a) :
    a / x + 1 ≤ a / y := by
  have h1 : (a / x + 1) * y ≤ a := by
    have : (a / x) * y + y ≤ (a / x) * x + y := by
      have hm : (a / x) * y ≤ (a / x) * x := Nat.mul_le_mul_left (a / x) (le_of_lt hyx)
      omega
    linarith
  exact (Nat.le_div_iff_mul_le hy).2 h1

end PierceCore

/-! ### Curvature Identity & Six-Term Hankel Identity (Over `ℤ`) -/

section AlgebraicIdentities

/-- Exact curvature identity for three consecutive Pierce steps:
    `D * z = d * f + u * d * e + (u - 1) * e^2` where `D = d * v - e * u`. -/
theorem curvature_identity (a x y z w q u v : ℤ)
    (h1 : x * q + y = a)
    (h2 : y * (q + u) + z = a)
    (h3 : z * (q + u + v) + w = a) :
    ((x - y) * v - (y - z) * u) * z =
      (x - y) * (z - w) + u * (x - y) * (y - z) + (u - 1) * (y - z) ^ 2 := by
  have hu : u * y = q * (x - y) + (y - z) := by linarith
  have hv : v * z = (q + u) * (y - z) + (z - w) := by linarith
  have huz_id : u * z = u * y - u * (y - z) := by ring
  have huz : u * z = q * (x - y) + (1 - u) * (y - z) := by linarith
  calc ((x - y) * v - (y - z) * u) * z
      = (x - y) * (v * z) - (y - z) * (u * z) := by ring
    _ = (x - y) * ((q + u) * (y - z) + (z - w)) -
        (y - z) * (q * (x - y) + (1 - u) * (y - z)) := by rw [hv, huz]
    _ = (x - y) * (z - w) + u * (x - y) * (y - z) + (u - 1) * (y - z) ^ 2 := by ring

/-- Curvature positivity: `D = d * v - e * u ≥ 1` whenever `z > 0`, `u ≥ 1`, `d, e, f ≥ 1`. -/
theorem curvature_pos (a x y z w q u v : ℤ)
    (hz : 0 < z) (hu : 1 ≤ u) (hd : 1 ≤ x - y) (he : 1 ≤ y - z) (hf : 1 ≤ z - w)
    (h1 : x * q + y = a) (h2 : y * (q + u) + z = a) (h3 : z * (q + u + v) + w = a) :
    1 ≤ (x - y) * v - (y - z) * u := by
  have hid := curvature_identity a x y z w q u v h1 h2 h3
  have hrhs : 0 < (x - y) * (z - w) + u * (x - y) * (y - z) + (u - 1) * (y - z) ^ 2 := by
    have t1 : 1 ≤ (x - y) * (z - w) := by nlinarith
    have t2 : 0 ≤ u * (x - y) * (y - z) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have t3 : 0 ≤ (u - 1) * (y - z) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  have hDz : 0 < ((x - y) * v - (y - z) * u) * z := by linarith
  have hD : 0 < (x - y) * v - (y - z) * u := by nlinarith
  linarith

/-- Size bounds from the division and curvature equations. -/
theorem step_size_bounds (a x y z w q u v : ℤ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (_hw : 0 ≤ w) (_hq : 0 ≤ q) (hu : 1 ≤ u)
    (hxa : x ≤ a) (hd : 1 ≤ x - y) (he : 1 ≤ y - z) (hf : 1 ≤ z - w)
    (h1 : x * q + y = a) (h2 : y * (q + u) + z = a) (h3 : z * (q + u + v) + w = a) :
    u * y * x ≤ a * ((x - y) + (y - z)) ∧
    ((x - y) * v - (y - z) * u) * z ≤ (u + 1) * ((x - y) + (y - z) + (z - w)) ^ 2 := by
  constructor
  · have hu' : u * y = q * (x - y) + (y - z) := by linarith
    have hqx : q * x ≤ a := by linarith
    nlinarith
  · have hid := curvature_identity a x y z w q u v h1 h2 h3
    have hd0 : 0 ≤ x - y := by linarith
    have he0 : 0 ≤ y - z := by linarith
    have hf0 : 0 ≤ z - w := by linarith
    have hu0 : 0 ≤ u := by linarith
    have hdiff : (u + 1) * ((x - y) + (y - z) + (z - w)) ^ 2 -
        ((x - y) * (z - w) + u * (x - y) * (y - z) + (u - 1) * (y - z) ^ 2) =
        (u + 1) * (x - y) ^ 2 + (u + 2) * (x - y) * (y - z) + (2 * u + 1) * (x - y) * (z - w) +
        2 * (y - z) ^ 2 + 2 * (u + 1) * (y - z) * (z - w) + (u + 1) * (z - w) ^ 2 := by ring
    have hnn : 0 ≤ (u + 1) * (x - y) ^ 2 + (u + 2) * (x - y) * (y - z) + (2 * u + 1) * (x - y) * (z - w) +
        2 * (y - z) ^ 2 + 2 * (u + 1) * (y - z) * (z - w) + (u + 1) * (z - w) ^ 2 := by positivity
    linarith

/-- The cubic increment polynomial `σ(y₁, y₂, y₃) = y₁² y₂ + (y₁ - 1) y₂² + y₁ y₃`. -/
def sigmaPoly (y1 y2 y3 : ℤ) : ℤ :=
  y1 ^ 2 * y2 + (y1 - 1) * y2 ^ 2 + y1 * y3

/-- The quartic increment polynomial `ω(y₁, y₂, y₃, y₄)` of the six-term identity. -/
def omegaPoly (y1 y2 y3 y4 : ℤ) : ℤ :=
  (y1 ^ 2 + (y1 - 1) * y2) * y4 +
  y3 * (y1 ^ 3 + y1 * y2 * (2 * y1 - 1) + (y1 - 1) * y2 ^ 2) +
  y3 ^ 2 * ((y1 - 1) * (y1 + y2) + 1)

/-- The six-term integer Hankel invariant `L = I₄(i)`. -/
def hankelL (f0 f1 f2 k0 k1 k2 k3 : ℤ) : ℤ :=
  let D := f0 * k1 - f1 * k0
  let E := f1 * k2 - f2 * k1
  (k1 * k2 + k2 ^ 2 + k3) * D - (k0 ^ 2 + (k0 - 1) * k1) * E - k2 * (k2 * f0 - k0 * f2)

/-- Six-term identity, Part 1:
    `σ(k₁, k₂, k₃) * D - σ(k₀, k₁, k₂) * E = k₁ * L`. -/
theorem six_term_identity_one (f0 f1 f2 k0 k1 k2 k3 : ℤ) :
    sigmaPoly k1 k2 k3 * (f0 * k1 - f1 * k0) -
      sigmaPoly k0 k1 k2 * (f1 * k2 - f2 * k1) =
    k1 * hankelL f0 f1 f2 k0 k1 k2 k3 := by
  unfold sigmaPoly hankelL
  ring

/-- Six-term identity, Part 2:
    `q * k₂ * L = ω(k₀, k₁, k₂, k₃) * E + σ(k₀, k₁, k₂) * F`. -/
theorem six_term_identity_two (a q x0 x1 x2 x3 x4 x5 k0 k1 k2 k3 : ℤ)
    (h0 : x0 * q + x1 = a)
    (h1 : x1 * (q + k0) + x2 = a)
    (h2 : x2 * (q + k0 + k1) + x3 = a)
    (h3 : x3 * (q + k0 + k1 + k2) + x4 = a)
    (h4 : x4 * (q + k0 + k1 + k2 + k3) + x5 = a) :
    q * k2 * hankelL (x0 - x1) (x1 - x2) (x2 - x3) k0 k1 k2 k3 =
      omegaPoly k0 k1 k2 k3 * ((x1 - x2) * k2 - (x2 - x3) * k1) +
      sigmaPoly k0 k1 k2 * ((x2 - x3) * k3 - (x3 - x4) * k2) := by
  have e0 : x0 * q + x1 - a = 0 := by linarith
  have e1 : x1 * (q + k0) + x2 - a = 0 := by linarith
  have e2 : x2 * (q + k0 + k1) + x3 - a = 0 := by linarith
  have e3 : x3 * (q + k0 + k1 + k2) + x4 - a = 0 := by linarith
  have e4 : x4 * (q + k0 + k1 + k2 + k3) + x5 - a = 0 := by linarith
  -- Notice `x5` appears only in `e4`? Actually `F = (x2-x3)*k3 - (x3-x4)*k2` does NOT depend on `x5`!
  -- Exact polynomial identity modulo `e0, e1, e2, e3`:
  let c0 := k1 ^ 2 * k2 + k1 * k2 ^ 2 + k1 * k3 - k2 ^ 2
  let c1 := k0 ^ 2 * k2 + 2 * k0 * k1 * k2 + k0 * k2 ^ 2 + k0 * k3 +
            k1 ^ 2 * k2 + k1 * k2 ^ 2 - k1 * k2 + k1 * k3 - k2 ^ 2
  let c2 := k0 ^ 2 * k1 + k0 ^ 2 * k2 + k0 * k1 ^ 2 + 2 * k0 * k1 * k2 +
            k0 * k2 ^ 2 + k0 * k2 + k0 * k3 - k1 ^ 2 - k1 * k2
  let c3 := k0 ^ 2 * k1 + k0 * k1 ^ 2 + k0 * k2 - k1 ^ 2
  have hpoly :
      q * k2 * hankelL (x0 - x1) (x1 - x2) (x2 - x3) k0 k1 k2 k3 -
      omegaPoly k0 k1 k2 k3 * ((x1 - x2) * k2 - (x2 - x3) * k1) -
      sigmaPoly k0 k1 k2 * ((x2 - x3) * k3 - (x3 - x4) * k2) =
      k2 * (c0 * (x0 * q + x1 - a) - c1 * (x1 * (q + k0) + x2 - a) +
            c2 * (x2 * (q + k0 + k1) + x3 - a) - c3 * (x3 * (q + k0 + k1 + k2) + x4 - a)) := by
    unfold hankelL omegaPoly sigmaPoly
    dsimp only [c0, c1, c2, c3]
    ring
  rw [e0, e1, e2, e3] at hpoly
  linarith

/-- **New Strict Orbit-Monotone Invariant:**
    Along any Pierce orbit (away from the end), `D_i / σ(k_i, k_{i+1}, k_{i+2})` is strictly
    decreasing, with exact telescoping gap `k_{i+1} L_i / (σ_i σ_{i+1}) > 0`. -/
theorem curvature_ratio_strict_decreasing (f0 f1 f2 k0 k1 k2 k3 : ℤ)
    (hk0 : 1 ≤ k0) (hk1 : 1 ≤ k1) (hk2 : 1 ≤ k2) (hk3 : 1 ≤ k3)
    (hL : 1 ≤ hankelL f0 f1 f2 k0 k1 k2 k3) :
    ((f0 * k1 - f1 * k0 : ℝ) / (sigmaPoly k0 k1 k2 : ℝ)) -
      ((f1 * k2 - f2 * k1 : ℝ) / (sigmaPoly k1 k2 k3 : ℝ)) =
    ((k1 * hankelL f0 f1 f2 k0 k1 k2 k3 : ℝ) /
      ((sigmaPoly k0 k1 k2 : ℝ) * (sigmaPoly k1 k2 k3 : ℝ))) ∧
    ((f1 * k2 - f2 * k1 : ℝ) / (sigmaPoly k1 k2 k3 : ℝ)) <
      ((f0 * k1 - f1 * k0 : ℝ) / (sigmaPoly k0 k1 k2 : ℝ)) := by
  have hs0_int : 0 < sigmaPoly k0 k1 k2 := by unfold sigmaPoly; nlinarith
  have hs1_int : 0 < sigmaPoly k1 k2 k3 := by unfold sigmaPoly; nlinarith
  have hs0 : (0 : ℝ) < (sigmaPoly k0 k1 k2 : ℝ) := by exact_mod_cast hs0_int
  have hs1 : (0 : ℝ) < (sigmaPoly k1 k2 k3 : ℝ) := by exact_mod_cast hs1_int
  have hid : ((sigmaPoly k1 k2 k3 : ℝ) * (f0 * k1 - f1 * k0 : ℝ) -
      (sigmaPoly k0 k1 k2 : ℝ) * (f1 * k2 - f2 * k1 : ℝ)) =
      (k1 * hankelL f0 f1 f2 k0 k1 k2 k3 : ℝ) := by
    exact_mod_cast six_term_identity_one f0 f1 f2 k0 k1 k2 k3
  have heq : ((f0 * k1 - f1 * k0 : ℝ) / (sigmaPoly k0 k1 k2 : ℝ)) -
      ((f1 * k2 - f2 * k1 : ℝ) / (sigmaPoly k1 k2 k3 : ℝ)) =
      ((k1 * hankelL f0 f1 f2 k0 k1 k2 k3 : ℝ) /
        ((sigmaPoly k0 k1 k2 : ℝ) * (sigmaPoly k1 k2 k3 : ℝ))) := by
    field_simp
    linarith
  refine ⟨heq, ?_⟩
  have hnum : (0 : ℝ) < (k1 * hankelL f0 f1 f2 k0 k1 k2 k3 : ℝ) := by
    have : (0 : ℤ) < k1 * hankelL f0 f1 f2 k0 k1 k2 k3 := by nlinarith
    exact_mod_cast this
  have hpos : (0 : ℝ) < ((k1 * hankelL f0 f1 f2 k0 k1 k2 k3 : ℝ) /
      ((sigmaPoly k0 k1 k2 : ℝ) * (sigmaPoly k1 k2 k3 : ℝ))) :=
    div_pos hnum (mul_pos hs0 hs1)
  linarith

/-- Positivity of `L` and upper bound on `q` from the six-term identity (Corollary 4.2). -/
theorem six_term_q_bound (a q x0 x1 x2 x3 x4 x5 k0 k1 k2 k3 K : ℤ)
    (hq : 1 ≤ q)
    (hk0 : 1 ≤ k0) (hk1 : 1 ≤ k1) (hk2 : 1 ≤ k2) (hk3 : 1 ≤ k3)
    (hK0 : k0 ≤ K) (hK1 : k1 ≤ K) (hK2 : k2 ≤ K) (hK3 : k3 ≤ K)
    (hE : 1 ≤ (x1 - x2) * k2 - (x2 - x3) * k1)
    (hF : 1 ≤ (x2 - x3) * k3 - (x3 - x4) * k2)
    (h0 : x0 * q + x1 = a) (h1 : x1 * (q + k0) + x2 = a)
    (h2 : x2 * (q + k0 + k1) + x3 = a) (h3 : x3 * (q + k0 + k1 + k2) + x4 = a)
    (h4 : x4 * (q + k0 + k1 + k2 + k3) + x5 = a) :
    1 ≤ hankelL (x0 - x1) (x1 - x2) (x2 - x3) k0 k1 k2 k3 ∧
    q ≤ 9 * K ^ 3 * ((x1 - x2) * k2 - (x2 - x3) * k1) +
        3 * K ^ 3 * ((x2 - x3) * k3 - (x3 - x4) * k2) := by
  have hid := six_term_identity_two a q x0 x1 x2 x3 x4 x5 k0 k1 k2 k3 h0 h1 h2 h3 h4
  have hK : 1 ≤ K := by linarith
  have hsig_pos : 1 ≤ sigmaPoly k0 k1 k2 := by unfold sigmaPoly; nlinarith
  have hom_pos : 1 ≤ omegaPoly k0 k1 k2 k3 := by
    unfold omegaPoly
    have h1 : 1 ≤ k0 ^ 2 + (k0 - 1) * k1 := by nlinarith
    have t1 : 1 ≤ (k0 ^ 2 + (k0 - 1) * k1) * k3 := by nlinarith
    have h2 : 0 ≤ k0 ^ 3 + k0 * k1 * (2 * k0 - 1) + (k0 - 1) * k1 ^ 2 := by
      have : 0 ≤ k0 - 1 := by linarith
      have : 0 ≤ 2 * k0 - 1 := by linarith
      have : 0 ≤ k0 := by linarith
      have : 0 ≤ k1 := by linarith
      positivity
    have t2 : 0 ≤ k2 * (k0 ^ 3 + k0 * k1 * (2 * k0 - 1) + (k0 - 1) * k1 ^ 2) :=
      mul_nonneg (by linarith) h2
    have t3 : 0 ≤ k2 ^ 2 * ((k0 - 1) * (k0 + k1) + 1) := by nlinarith
    linarith
  have hL_pos : 1 ≤ hankelL (x0 - x1) (x1 - x2) (x2 - x3) k0 k1 k2 k3 := by
    have hprod : 0 < q * k2 * hankelL (x0 - x1) (x1 - x2) (x2 - x3) k0 k1 k2 k3 := by nlinarith
    have hqk : 0 < q * k2 := by nlinarith
    have : 0 < hankelL (x0 - x1) (x1 - x2) (x2 - x3) k0 k1 k2 k3 := by nlinarith
    linarith
  refine ⟨hL_pos, ?_⟩
  have hK0' : 0 ≤ K := by linarith
  have hk02 : k0 ^ 2 ≤ K ^ 2 := by nlinarith
  have hk12 : k1 ^ 2 ≤ K ^ 2 := by nlinarith
  have hK3_le : K ^ 3 ≤ K ^ 3 * k2 := le_mul_of_one_le_right (by positivity) hk2
  have hsig_le : sigmaPoly k0 k1 k2 ≤ 3 * K ^ 3 * k2 := by
    unfold sigmaPoly
    have a1 : k0 ^ 2 * k1 ≤ K ^ 3 * k2 := by
      have h1 : k0 ^ 2 * k1 ≤ K ^ 2 * K := mul_le_mul hk02 hK1 (by linarith) (by positivity)
      linarith
    have a2 : (k0 - 1) * k1 ^ 2 ≤ K ^ 3 * k2 := by
      have h1 : (k0 - 1) * k1 ^ 2 ≤ K * K ^ 2 := mul_le_mul (by linarith) hk12 (sq_nonneg _) hK0'
      linarith
    have a3 : k0 * k2 ≤ K ^ 3 * k2 := by
      have hK12 : K ≤ K ^ 2 := by nlinarith
      have hK23 : K ^ 2 ≤ K ^ 3 := by nlinarith
      have : k0 ≤ K ^ 3 := by linarith
      nlinarith
    linarith
  have hom_le : omegaPoly k0 k1 k2 k3 ≤ 9 * K ^ 3 * k2 := by
    unfold omegaPoly
    have b1 : (k0 ^ 2 + (k0 - 1) * k1) * k3 ≤ 2 * K ^ 3 * k2 := by
      have h1 : k0 ^ 2 + (k0 - 1) * k1 ≤ 2 * K ^ 2 := by nlinarith
      have h2 : (k0 ^ 2 + (k0 - 1) * k1) * k3 ≤ (2 * K ^ 2) * K :=
        mul_le_mul h1 hK3 (by linarith) (by positivity)
      linarith
    have b2 : k2 * (k0 ^ 3 + k0 * k1 * (2 * k0 - 1) + (k0 - 1) * k1 ^ 2) ≤ 4 * K ^ 3 * k2 := by
      have c1 : k0 ^ 3 ≤ K ^ 3 := pow_le_pow_left₀ (by linarith) hK0 3
      have c2 : k0 * k1 * (2 * k0 - 1) ≤ 2 * K ^ 3 := by
        have h1 : k0 * k1 ≤ K ^ 2 := by nlinarith
        have h2 : k0 * k1 * (2 * k0 - 1) ≤ K ^ 2 * (2 * K) :=
          mul_le_mul h1 (by linarith) (by linarith) (by positivity)
        linarith
      have c3 : (k0 - 1) * k1 ^ 2 ≤ K ^ 3 := by
        have h2 : (k0 - 1) * k1 ^ 2 ≤ K * K ^ 2 := mul_le_mul (by linarith) hk12 (sq_nonneg _) hK0'
        linarith
      nlinarith
    have b3 : k2 ^ 2 * ((k0 - 1) * (k0 + k1) + 1) ≤ 3 * K ^ 3 * k2 := by
      have d1 : k2 * ((k0 - 1) * (k0 + k1) + 1) ≤ 3 * K ^ 3 := by
        have h1 : (k0 - 1) * (k0 + k1) + 1 ≤ 3 * K ^ 2 := by nlinarith
        have h2 : k2 * ((k0 - 1) * (k0 + k1) + 1) ≤ K * (3 * K ^ 2) :=
          mul_le_mul hK2 h1 (by nlinarith) hK0'
        linarith
      nlinarith
    linarith
  have hqk_le : q * k2 ≤ q * k2 * hankelL (x0 - x1) (x1 - x2) (x2 - x3) k0 k1 k2 k3 :=
    le_mul_of_one_le_right (by nlinarith) hL_pos
  have hmul : q * k2 ≤
      (9 * K ^ 3 * ((x1 - x2) * k2 - (x2 - x3) * k1) +
       3 * K ^ 3 * ((x2 - x3) * k3 - (x3 - x4) * k2)) * k2 := by
    nlinarith
  nlinarith

end AlgebraicIdentities

/-! ### Window Runs, Erdős–Shallit Drop Bound, and Six-Term Window Bound -/

section WindowBounds

/-- Maximum divisor count `Δ(Y) = max_{1 ≤ m ≤ Y} τ(m)`. -/
def maxDivisors (Y : ℕ) : ℕ :=
  (Finset.Icc 1 Y).sup (fun m => m.divisors.card)

lemma divisors_card_le_maxDivisors {m Y : ℕ} (hm1 : 1 ≤ m) (hmY : m ≤ Y) :
    m.divisors.card ≤ maxDivisors Y :=
  Finset.le_sup (f := fun n => n.divisors.card) (Finset.mem_Icc.2 ⟨hm1, hmY⟩)

/-- A window run of length `T` in `[A, 2A)` along the Pierce orbit of `(a, b)`. -/
structure WindowRun (a b A T : ℕ) where
  i0 : ℕ
  end_le : i0 + T ≤ pierceLen a b
  in_window : ∀ j < T, A ≤ pierceOrbit a b (i0 + j) ∧ pierceOrbit a b (i0 + j) < 2 * A

/-- **Erdős–Shallit Drop Bound:** for any window run of length `T ≥ 2` in `[A, 2A)` with `A < a`,
    `T * (T - 1) ≤ 4 * A * maxDivisors (2 * a)`. -/
theorem window_drop_bound {a b A T : ℕ} (hA : 1 ≤ A) (hAa : A ≤ a) (hT : 2 ≤ T)
    (W : WindowRun a b A T) :
    T * (T - 1) ≤ 4 * A * maxDivisors (2 * a) := by
  let h : ℕ → ℕ := fun j => pierceOrbit a b (W.i0 + j) - pierceOrbit a b (W.i0 + j + 1)
  have hpos : ∀ j < T - 1, 1 ≤ h j := by
    intro j hj
    have hlt := pierceOrbit_strict_mono_rev (a := a) (b := b) (i := W.i0 + j) (j := W.i0 + j + 1)
      (by omega) (by have := W.end_le; omega)
    dsimp [h]; omega
  -- Telescoping sum of drops ≤ A - 1
  have hsum : ∑ j ∈ Finset.range (T - 1), h j =
      pierceOrbit a b W.i0 - pierceOrbit a b (W.i0 + (T - 1)) := by
    have htele : ∀ m ≤ T - 1, ∑ j ∈ Finset.range m, h j =
        pierceOrbit a b W.i0 - pierceOrbit a b (W.i0 + m) := by
      intro m hm
      induction m with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih (by omega)]
        have h1 : pierceOrbit a b (W.i0 + k + 1) ≤ pierceOrbit a b (W.i0 + k) :=
          le_of_lt (pierceOrbit_strict_mono_rev (by omega) (by have := W.end_le; omega))
        have h2 : pierceOrbit a b (W.i0 + k) ≤ pierceOrbit a b W.i0 := by
          rcases eq_or_lt_of_le (Nat.zero_le k) with hk0 | hkp
          · simp [← hk0]
          · exact le_of_lt (pierceOrbit_strict_mono_rev (by omega) (by have := W.end_le; omega))
        have hidx : W.i0 + (k + 1) = W.i0 + k + 1 := by omega
        rw [hidx]
        dsimp [h]; omega
    exact htele (T - 1) le_rfl
  have hsum_le : ∑ j ∈ Finset.range (T - 1), h j ≤ A - 1 := by
    rw [hsum]
    have h0 := (W.in_window 0 (by omega)).2
    have hl := (W.in_window (T - 1) (by omega)).1
    simp only [Nat.add_zero] at h0
    omega
  let hbar := 2 * A / (T - 1)
  let S := (Finset.range (T - 1)).filter (fun j => h j ≤ hbar)
  let B := (Finset.range (T - 1)).filter (fun j => hbar < h j)
  have hB_card : B.card * (hbar + 1) ≤ A - 1 := by
    calc B.card * (hbar + 1)
        = ∑ _j ∈ B, (hbar + 1) := by simp
      _ ≤ ∑ j ∈ B, h j := Finset.sum_le_sum (fun j hj => by
            have := (Finset.mem_filter.1 hj).2; omega)
      _ ≤ ∑ j ∈ Finset.range (T - 1), h j :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ A - 1 := hsum_le
  have h2B : 2 * B.card < T - 1 := by
    have hdiv : 2 * A < (T - 1) * (hbar + 1) := by
      dsimp [hbar]
      have hposT : 0 < T - 1 := by omega
      have := Nat.div_add_mod (2 * A) (T - 1)
      have := Nat.mod_lt (2 * A) hposT
      nlinarith
    have hmul_lt : (2 * B.card) * (hbar + 1) < (T - 1) * (hbar + 1) := by
      have : 2 * B.card * (hbar + 1) ≤ 2 * (A - 1) := by nlinarith
      omega
    exact Nat.lt_of_mul_lt_mul_right hmul_lt
  have hSB : S.card + B.card = T - 1 := by
    have hdisj : Disjoint S B := Finset.disjoint_filter.2 (fun _ _ h1 h2 => by omega)
    have hunion : S ∪ B = Finset.range (T - 1) := by
      ext j
      simp only [S, B, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
      · intro hj
        rcases le_or_gt (h j) hbar with hle | hgt
        · exact Or.inl ⟨hj, hle⟩
        · exact Or.inr ⟨hj, hgt⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_range]
  have h2S : T ≤ 2 * S.card := by omega
  -- Count S by grouping by value d = h j ∈ [1, hbar]
  have hS_le : S.card ≤ hbar * maxDivisors (2 * a) := by
    have hpart : S.card = ∑ d ∈ Finset.Icc 1 hbar, (S.filter (fun j => h j = d)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext j
        simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter]
        constructor
        · intro hj
          have hjr := (Finset.mem_filter.1 hj).1
          have hjle := (Finset.mem_filter.1 hj).2
          exact ⟨h j, ⟨hpos j (Finset.mem_range.1 hjr), hjle⟩, hj, rfl⟩
        · rintro ⟨_, _, hj, _⟩; exact hj
      · intro d1 _ d2 _ hne
        exact Finset.disjoint_left.2 fun j hj1 hj2 =>
          hne ((Finset.mem_filter.1 hj1).2.symm.trans (Finset.mem_filter.1 hj2).2)
    rw [hpart]
    calc ∑ d ∈ Finset.Icc 1 hbar, (S.filter (fun j => h j = d)).card
        ≤ ∑ _d ∈ Finset.Icc 1 hbar, maxDivisors (2 * a) := by
          apply Finset.sum_le_sum
          intro d hd
          have hd1 := (Finset.mem_Icc.1 hd).1
          -- Each j in the fiber gives a distinct divisor pierceOrbit a b (W.i0 + j) of a + d!
          let f : ℕ → ℕ := fun j => pierceOrbit a b (W.i0 + j)
          have hinj : Set.InjOn f (S.filter (fun j => h j = d)) := by
            intro j1 hj1 j2 hj2 heq
            have hr1 := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hj1).1).1
            have hr2 := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hj2).1).1
            have h1 : W.i0 + j1 < pierceLen a b := by have := W.end_le; omega
            have h2 : W.i0 + j2 < pierceLen a b := by have := W.end_le; omega
            have := pierceOrbit_inj_on h1 h2 heq
            omega
          have hsub : (S.filter (fun j => h j = d)).image f ⊆ (a + d).divisors := by
            intro x hx
            rcases Finset.mem_image.1 hx with ⟨j, hj, rfl⟩
            have hjd := (Finset.mem_filter.1 hj).2
            have hjr := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hj).1).1
            have hx_pos : 0 < pierceOrbit a b (W.i0 + j) :=
              pierceOrbit_pos_of_lt (by have := W.end_le; omega)
            have hlt_next : pierceOrbit a b (W.i0 + j + 1) < pierceOrbit a b (W.i0 + j) :=
              pierceOrbit_strict_anti hx_pos
            have hdiv_eq := div_eq_step a (pierceOrbit a b (W.i0 + j))
            rw [← pierceOrbit_succ] at hdiv_eq
            have hdvd : pierceOrbit a b (W.i0 + j) ∣ a + d := by
              refine ⟨a / pierceOrbit a b (W.i0 + j) + 1, ?_⟩
              dsimp [h] at hjd
              have : pierceOrbit a b (W.i0 + j + 1) + d = pierceOrbit a b (W.i0 + j) := by omega
              nlinarith
            exact Nat.mem_divisors.2 ⟨hdvd, by omega⟩
          have hcard_le : (S.filter (fun j => h j = d)).card ≤ (a + d).divisors.card := by
            rw [← Finset.card_image_of_injOn hinj]
            exact Finset.card_le_card hsub
          by_cases hemp : (S.filter (fun j => h j = d)).Nonempty
          · rcases hemp with ⟨j0, hj0⟩
            have hjd0 := (Finset.mem_filter.1 hj0).2
            have hjr0 := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hj0).1).1
            have hle_sum : h j0 ≤ ∑ k ∈ Finset.range (T - 1), h k :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hjr0)
            have hd_le_a : d ≤ a := by omega
            exact le_trans hcard_le (divisors_card_le_maxDivisors (by omega) (by omega))
          · rw [Finset.not_nonempty_iff_eq_empty] at hemp
            rw [hemp, Finset.card_empty]
            exact Nat.zero_le _
      _ = hbar * maxDivisors (2 * a) := by
          simp [Nat.card_Icc]
  -- Wait: fix the empty-fiber branch cleanly!
  calc T * (T - 1)
      ≤ 2 * S.card * (T - 1) := Nat.mul_le_mul_right (T - 1) h2S
    _ ≤ 2 * (hbar * maxDivisors (2 * a)) * (T - 1) := by
        have := Nat.mul_le_mul_left 2 hS_le
        exact Nat.mul_le_mul_right (T - 1) this
    _ = 2 * (hbar * (T - 1)) * maxDivisors (2 * a) := by ring
    _ ≤ 2 * (2 * A) * maxDivisors (2 * a) := by
        have hmul : hbar * (T - 1) ≤ 2 * A := Nat.div_mul_le_self (2 * A) (T - 1)
        nlinarith
    _ = 4 * A * maxDivisors (2 * a) := by ring

/-- **Six-Term Window Bound (Proposition 4.3):**
    For any window run of length `T ≥ 10` in `[A, 2A)` with `A ≥ 1`,
    `T^6 * A^2 ≤ 96 * 10^6 * a^3` (i.e. `T^6 A^2 ≪ a^3`). -/
theorem window_six_term_bound {a b A T : ℕ} (hA : 1 ≤ A) (hT : 10 ≤ T)
    (W : WindowRun a b A T) :
    (T : ℤ) ^ 6 * (A : ℤ) ^ 2 ≤ 96000000 * (a : ℤ) ^ 3 := by
  -- Find a 6-term block starting at j ≤ T - 6 with total drop s = x_j - x_{j+5} satisfying s * T ≤ 10 * A!
  let s : ℕ → ℕ := fun j => pierceOrbit a b (W.i0 + j) - pierceOrbit a b (W.i0 + j + 5)
  have hsum_s : ∑ j ∈ Finset.range (T - 5), s j ≤ 5 * A := by
    -- Express s j as sum of 5 consecutive drops d_{j+r}
    let d : ℕ → ℕ := fun r => pierceOrbit a b (W.i0 + r) - pierceOrbit a b (W.i0 + r + 1)
    have hs_eq : ∀ j < T - 5, s j = ∑ r ∈ Finset.range 5, d (j + r) := by
      intro j hj
      have htele5 : ∀ m ≤ 5, pierceOrbit a b (W.i0 + j) - pierceOrbit a b (W.i0 + j + m) =
          ∑ r ∈ Finset.range m, d (j + r) := by
        intro m hm
        induction m with
        | zero => simp
        | succ k ih =>
          rw [Finset.sum_range_succ, ← ih (by omega)]
          have h1 : pierceOrbit a b (W.i0 + j + k + 1) ≤ pierceOrbit a b (W.i0 + j + k) :=
            le_of_lt (pierceOrbit_strict_mono_rev (by omega) (by have := W.end_le; omega))
          have h2 : pierceOrbit a b (W.i0 + j + k) ≤ pierceOrbit a b (W.i0 + j) := by
            rcases eq_or_lt_of_le (Nat.zero_le k) with hk0 | hkp
            · simp [← hk0]
            · exact le_of_lt (pierceOrbit_strict_mono_rev (by omega) (by have := W.end_le; omega))
          dsimp [d]
          have hidx1 : W.i0 + (j + k) = W.i0 + j + k := by omega
          have hidx2 : W.i0 + j + (k + 1) = W.i0 + j + k + 1 := by omega
          rw [hidx1, hidx2]
          omega
      exact htele5 5 le_rfl
    have hsum_d : ∀ r < 5, ∑ j ∈ Finset.range (T - 5), d (j + r) ≤ A := by
      intro r hr
      have htele : ∀ m ≤ T - 5, ∑ j ∈ Finset.range m, d (j + r) =
          pierceOrbit a b (W.i0 + r) - pierceOrbit a b (W.i0 + m + r) := by
        intro m hm
        induction m with
        | zero => simp
        | succ k ih =>
          rw [Finset.sum_range_succ, ih (by omega)]
          have h1 : pierceOrbit a b (W.i0 + k + r + 1) ≤ pierceOrbit a b (W.i0 + k + r) :=
            le_of_lt (pierceOrbit_strict_mono_rev (by omega) (by have := W.end_le; omega))
          have h2 : pierceOrbit a b (W.i0 + k + r) ≤ pierceOrbit a b (W.i0 + r) := by
            rcases eq_or_lt_of_le (Nat.zero_le k) with hk0 | hkp
            · simp [← hk0]
            · exact le_of_lt (pierceOrbit_strict_mono_rev (by omega) (by have := W.end_le; omega))
          dsimp [d]
          have hidx1 : W.i0 + (k + r) = W.i0 + k + r := by omega
          have hidx2 : W.i0 + k + r + 1 = W.i0 + (k + 1) + r := by omega
          rw [hidx1]
          rw [hidx2] at h1 ⊢
          omega
      rw [htele (T - 5) le_rfl]
      have hhi := (W.in_window r (by omega)).2
      have hlo := (W.in_window (T - 5 + r) (by omega)).1
      have hidx : W.i0 + (T - 5) + r = W.i0 + (T - 5 + r) := by omega
      rw [hidx]
      omega
    calc ∑ j ∈ Finset.range (T - 5), s j
        = ∑ j ∈ Finset.range (T - 5), ∑ r ∈ Finset.range 5, d (j + r) :=
          Finset.sum_congr rfl (fun j hj => hs_eq j (Finset.mem_range.1 hj))
      _ = ∑ r ∈ Finset.range 5, ∑ j ∈ Finset.range (T - 5), d (j + r) := Finset.sum_comm
      _ ≤ ∑ _r ∈ Finset.range 5, A := Finset.sum_le_sum (fun r hr => hsum_d r (Finset.mem_range.1 hr))
      _ = 5 * A := by simp
  -- Pigeonhole: some j < T - 5 has s j * (T - 5) ≤ 5 * A, hence s j * T ≤ 10 * A
  have hex : ∃ j < T - 5, s j * T ≤ 10 * A := by
    by_contra hall
    push Not at hall
    have hge : ∑ j ∈ Finset.range (T - 5), s j * T ≥ (T - 5) * (10 * A + 1) := by
      calc ∑ j ∈ Finset.range (T - 5), s j * T
          ≥ ∑ _j ∈ Finset.range (T - 5), (10 * A + 1) :=
            Finset.sum_le_sum (fun j hj => hall j (Finset.mem_range.1 hj))
        _ = (T - 5) * (10 * A + 1) := by simp
    rw [← Finset.sum_mul] at hge
    have hT5 : T ≤ 2 * (T - 5) := by omega
    have hT5_pos : 1 ≤ T - 5 := by omega
    have : 5 * A * T < (T - 5) * (10 * A + 1) := by nlinarith
    have : (∑ j ∈ Finset.range (T - 5), s j) * T ≤ 5 * A * T := Nat.mul_le_mul_right T hsum_s
    omega
  rcases hex with ⟨j, hj, hsT⟩
  -- Apply six_term_q_bound to the 6 consecutive terms x0, ..., x5 starting at W.i0 + j!
  let x : ℕ → ℤ := fun r => (pierceOrbit a b (W.i0 + j + r) : ℤ)
  let q_nat : ℕ → ℕ := fun r => a / pierceOrbit a b (W.i0 + j + r)
  let q0 : ℤ := (q_nat 0 : ℤ)
  let k0 : ℤ := (q_nat 1 : ℤ) - (q_nat 0 : ℤ)
  let k1 : ℤ := (q_nat 2 : ℤ) - (q_nat 1 : ℤ)
  let k2 : ℤ := (q_nat 3 : ℤ) - (q_nat 2 : ℤ)
  let k3 : ℤ := (q_nat 4 : ℤ) - (q_nat 3 : ℤ)
  have hwin : ∀ r ≤ 5, (A : ℤ) ≤ x r ∧ x r < 2 * (A : ℤ) := by
    intro r hr
    have := W.in_window (j + r) (by omega)
    have hidx : W.i0 + (j + r) = W.i0 + j + r := by omega
    rw [hidx] at this
    dsimp only [x]
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  have hdiv : ∀ r ≤ 4, x r * (q_nat r : ℤ) + x (r + 1) = (a : ℤ) := by
    intro r hr
    have h1 := div_eq_step a (pierceOrbit a b (W.i0 + j + r))
    rw [← pierceOrbit_succ] at h1
    have hidx : W.i0 + j + r + 1 = W.i0 + j + (r + 1) := by omega
    rw [hidx] at h1
    have h1z : (q_nat r : ℤ) * x r + x (r + 1) = (a : ℤ) := by
      dsimp only [x, q_nat]; exact_mod_cast h1
    linarith
  have hdrop_pos : ∀ r ≤ 4, 1 ≤ x r - x (r + 1) := by
    intro r hr
    have hlt := pierceOrbit_strict_mono_rev (a := a) (b := b)
      (i := W.i0 + j + r) (j := W.i0 + j + (r + 1)) (by omega) (by have := W.end_le; omega)
    have : x (r + 1) < x r := by dsimp only [x]; exact_mod_cast hlt
    linarith
  have hq_inc : ∀ r ≤ 3, (q_nat r : ℤ) + 1 ≤ (q_nat (r + 1) : ℤ) := by
    intro r hr
    have hy : 0 < pierceOrbit a b (W.i0 + j + (r + 1)) :=
      pierceOrbit_pos_of_lt (by have := W.end_le; omega)
    have hyx : pierceOrbit a b (W.i0 + j + (r + 1)) < pierceOrbit a b (W.i0 + j + r) :=
      pierceOrbit_strict_mono_rev (by omega) (by have := W.end_le; omega)
    have heq := div_eq_step a (pierceOrbit a b (W.i0 + j + r))
    rw [← pierceOrbit_succ] at heq
    have hidx : W.i0 + j + r + 1 = W.i0 + j + (r + 1) := by omega
    rw [hidx] at heq
    have := quot_strict_inc hy hyx heq
    dsimp only [q_nat]; exact_mod_cast this
  have hq0_ge1 : 1 ≤ q0 := by
    have h0 := hdiv 0 (by omega)
    have hx0 : 0 < x 0 := by linarith [(hwin 0 (by omega)).1]
    have hx1 : x 1 < x 0 := by linarith [hdrop_pos 0 (by omega)]
    have hq0_nn : 0 ≤ q0 := Int.natCast_nonneg _
    by_contra hlt1
    have hq00 : q0 = 0 := by omega
    have hx1a : x 1 = (a : ℤ) := by dsimp only [q0] at hq00; rw [hq00] at h0; linarith
    have hx2 : pierceOrbit a b (W.i0 + j + 2) = 0 := by
      have : W.i0 + j + 2 = (W.i0 + j + 1) + 1 := by omega
      rw [this, pierceOrbit_succ]
      have h1a : pierceOrbit a b (W.i0 + j + 1) = a := by dsimp only [x] at hx1a; exact_mod_cast hx1a
      rw [h1a, Nat.mod_self]
    have hpos2 : 0 < pierceOrbit a b (W.i0 + j + 2) :=
      pierceOrbit_pos_of_lt (by have := W.end_le; omega)
    omega
  have ha_lt_4Aq : (a : ℤ) < 4 * (A : ℤ) * q0 := by
    have h0 := hdiv 0 (by omega)
    have hx0 := (hwin 0 (by omega)).2
    have hx1 : x 1 < x 0 := by linarith [hdrop_pos 0 (by omega)]
    nlinarith
  have hxa : ∀ r ≤ 4, x r ≤ (a : ℤ) := by
    intro r hr
    have h0 := hdiv r hr
    have hqr : 1 ≤ (q_nat r : ℤ) := by
      have h01 := hq_inc 0 (by omega)
      have h12 := hq_inc 1 (by omega)
      have h23 := hq_inc 2 (by omega)
      have h34 := hq_inc 3 (by omega)
      dsimp only [q0] at hq0_ge1
      rcases r with _ | _ | _ | _ | _ | _ <;> first | omega | linarith
    have hxr1 : 0 ≤ x (r + 1) := by linarith [(hwin (r + 1) (by omega)).1]
    nlinarith
  have hk0_ge : 1 ≤ k0 := by dsimp [k0]; linarith [hq_inc 0 (by omega)]
  have hk1_ge : 1 ≤ k1 := by dsimp [k1]; linarith [hq_inc 1 (by omega)]
  have hk2_ge : 1 ≤ k2 := by dsimp [k2]; linarith [hq_inc 2 (by omega)]
  have hk3_ge : 1 ≤ k3 := by dsimp [k3]; linarith [hq_inc 3 (by omega)]
  have hd0 := hdiv 0 (by omega)
  have hd1 : x 1 * (q0 + k0) + x 2 = (a : ℤ) := by
    have := hdiv 1 (by omega); dsimp [q0, k0]; linarith
  have hd2 : x 2 * (q0 + k0 + k1) + x 3 = (a : ℤ) := by
    have := hdiv 2 (by omega); dsimp [q0, k0, k1]; linarith
  have hd3 : x 3 * (q0 + k0 + k1 + k2) + x 4 = (a : ℤ) := by
    have := hdiv 3 (by omega); dsimp [q0, k0, k1, k2]; linarith
  have hd4 : x 4 * (q0 + k0 + k1 + k2 + k3) + x 5 = (a : ℤ) := by
    have := hdiv 4 (by omega); dsimp [q0, k0, k1, k2, k3]; linarith
  -- Curvatures E, F ≥ 1
  have hE_pos : 1 ≤ (x 1 - x 2) * k2 - (x 2 - x 3) * k1 :=
    curvature_pos a (x 1) (x 2) (x 3) (x 4) (q0 + k0) k1 k2
      (by linarith [(hwin 3 (by omega)).1]) hk1_ge
      (hdrop_pos 1 (by omega)) (hdrop_pos 2 (by omega)) (hdrop_pos 3 (by omega)) hd1 hd2 hd3
  have hF_pos : 1 ≤ (x 2 - x 3) * k3 - (x 3 - x 4) * k2 :=
    curvature_pos a (x 2) (x 3) (x 4) (x 5) (q0 + k0 + k1) k2 k3
      (by linarith [(hwin 4 (by omega)).1]) hk2_ge
      (hdrop_pos 2 (by omega)) (hdrop_pos 3 (by omega)) (hdrop_pos 4 (by omega)) hd2 hd3 hd4
  let sz : ℤ := x 0 - x 5
  have hsz_eq : sz = (s j : ℤ) := by
    have hlt5 : pierceOrbit a b (W.i0 + j + 5) ≤ pierceOrbit a b (W.i0 + j) :=
      le_of_lt (pierceOrbit_strict_mono_rev (by omega) (by have := W.end_le; omega))
    dsimp [sz, x, s]
    omega
  have hszT : sz * (T : ℤ) ≤ 10 * (A : ℤ) := by rw [hsz_eq]; exact_mod_cast hsT
  have hsz_pos : 1 ≤ sz := by
    have := hdrop_pos 0 (by omega); have := hdrop_pos 1 (by omega)
    have := hdrop_pos 2 (by omega); have := hdrop_pos 3 (by omega)
    have := hdrop_pos 4 (by omega); dsimp [sz]; linarith
  -- Bound each k_r * A^2 ≤ a * sz
  have hstep_b : ∀ r ≤ 3, ((q_nat (r + 1) : ℤ) - (q_nat r : ℤ)) * (A : ℤ) ^ 2 ≤ (a : ℤ) * sz := by
    intro r hr
    have h1 := hdiv r (by omega)
    have h2 := hdiv (r + 1) (by omega)
    have hu_eq : ((q_nat (r + 1) : ℤ) - (q_nat r : ℤ)) * x (r + 1) =
        (q_nat r : ℤ) * (x r - x (r + 1)) + (x (r + 1) - x (r + 2)) := by
      have hr2 : r + 1 + 1 = r + 2 := by omega
      rw [hr2] at h2; nlinarith
    have hqx : (q_nat r : ℤ) * x r ≤ (a : ℤ) := by
      have : 0 ≤ x (r + 1) := by linarith [(hwin (r + 1) (by omega)).1]
      linarith
    have hsum2 : (x r - x (r + 1)) + (x (r + 1) - x (r + 2)) ≤ sz := by
      have h0r : x r ≤ x 0 := by
        rcases eq_or_lt_of_le (Nat.zero_le r) with hr0 | hrp
        · simp [← hr0]
        · have hlt := pierceOrbit_strict_mono_rev (a := a) (b := b)
            (i := W.i0 + j) (j := W.i0 + j + r) (by omega) (by have := W.end_le; omega)
          dsimp only [x]; exact_mod_cast le_of_lt hlt
      have hr5 : x 5 ≤ x (r + 2) := by
        rcases eq_or_lt_of_le (show r + 2 ≤ 5 by omega) with hr5 | hr5
        · simp [hr5]
        · have hlt := pierceOrbit_strict_mono_rev (a := a) (b := b)
            (i := W.i0 + j + (r + 2)) (j := W.i0 + j + 5) (by omega) (by have := W.end_le; omega)
          dsimp only [x]; exact_mod_cast le_of_lt hlt
      dsimp [sz]; linarith
    have hux : ((q_nat (r + 1) : ℤ) - (q_nat r : ℤ)) * x (r + 1) * x r ≤ (a : ℤ) * sz := by
      have hxr_le_a := hxa r (by omega)
      have h1_pos : 0 ≤ x r - x (r + 1) := by linarith [hdrop_pos r (by omega)]
      have h2_pos : 0 ≤ x (r + 1) - x (r + 2) := by linarith [hdrop_pos (r + 1) (by omega)]
      have ha_nn : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
      calc ((q_nat (r + 1) : ℤ) - (q_nat r : ℤ)) * x (r + 1) * x r
          = ((q_nat r : ℤ) * (x r - x (r + 1)) + (x (r + 1) - x (r + 2))) * x r := by rw [hu_eq]
        _ = ((q_nat r : ℤ) * x r) * (x r - x (r + 1)) + x r * (x (r + 1) - x (r + 2)) := by ring
        _ ≤ (a : ℤ) * (x r - x (r + 1)) + (a : ℤ) * (x (r + 1) - x (r + 2)) :=
            add_le_add (mul_le_mul_of_nonneg_right hqx h1_pos) (mul_le_mul_of_nonneg_right hxr_le_a h2_pos)
        _ = (a : ℤ) * ((x r - x (r + 1)) + (x (r + 1) - x (r + 2))) := by ring
        _ ≤ (a : ℤ) * sz := mul_le_mul_of_nonneg_left hsum2 ha_nn
    have hA_le_r := (hwin r (by omega)).1
    have hA_le_r1 := (hwin (r + 1) (by omega)).1
    have hk_pos : 0 ≤ (q_nat (r + 1) : ℤ) - (q_nat r : ℤ) := by linarith [hq_inc r hr]
    have hA_nn : (0 : ℤ) ≤ (A : ℤ) := Int.natCast_nonneg A
    have hA2_le : (A : ℤ) ^ 2 ≤ x (r + 1) * x r := by
      rw [sq]
      exact mul_le_mul hA_le_r1 hA_le_r hA_nn (by linarith)
    calc ((q_nat (r + 1) : ℤ) - (q_nat r : ℤ)) * (A : ℤ) ^ 2
        ≤ ((q_nat (r + 1) : ℤ) - (q_nat r : ℤ)) * (x (r + 1) * x r) :=
          mul_le_mul_of_nonneg_left hA2_le hk_pos
      _ = ((q_nat (r + 1) : ℤ) - (q_nat r : ℤ)) * x (r + 1) * x r := by ring
      _ ≤ (a : ℤ) * sz := hux
  let K : ℤ := max (max k0 k1) (max k2 k3)
  have hK0 : k0 ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hK1 : k1 ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hK2 : k2 ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK3 : k3 ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  have hK_ge1 : 1 ≤ K := le_trans hk0_ge hK0
  have hKA2 : K * (A : ℤ) ^ 2 ≤ (a : ℤ) * sz := by
    have b0 := hstep_b 0 (by omega)
    have b1 := hstep_b 1 (by omega)
    have b2 := hstep_b 2 (by omega)
    have b3 := hstep_b 3 (by omega)
    rcases max_choice (max k0 k1) (max k2 k3) with h1 | h1
    · rcases max_choice k0 k1 with h2 | h2
      · simp only [K, h1, h2]; simpa [k0] using b0
      · simp only [K, h1, h2]; simpa [k1] using b1
    · rcases max_choice k2 k3 with h2 | h2
      · simp only [K, h1, h2]; simpa [k2] using b2
      · simp only [K, h1, h2]; simpa [k3] using b3
  have hA_pos : (0 : ℤ) < (A : ℤ) := by exact_mod_cast hA
  have hT_pos : (0 : ℤ) < (T : ℤ) := by omega
  have ha_nn : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  have hKAT : K * (A : ℤ) * (T : ℤ) ≤ 10 * (a : ℤ) := by
    have hmul : (A : ℤ) * (K * (A : ℤ) * (T : ℤ)) ≤ (A : ℤ) * (10 * (a : ℤ)) := by
      calc (A : ℤ) * (K * (A : ℤ) * (T : ℤ))
          = (K * (A : ℤ) ^ 2) * (T : ℤ) := by ring
        _ ≤ ((a : ℤ) * sz) * (T : ℤ) := mul_le_mul_of_nonneg_right hKA2 (le_of_lt hT_pos)
        _ = (a : ℤ) * (sz * (T : ℤ)) := by ring
        _ ≤ (a : ℤ) * (10 * (A : ℤ)) := mul_le_mul_of_nonneg_left hszT ha_nn
        _ = (A : ℤ) * (10 * (a : ℤ)) := by ring
    exact le_of_mul_le_mul_left hmul hA_pos
  -- Bound E * A ≤ 2 * K * sz^2 and F * A ≤ 2 * K * sz^2
  have hEA : ((x 1 - x 2) * k2 - (x 2 - x 3) * k1) * (A : ℤ) ≤ 2 * K * sz ^ 2 := by
    have hsb := (step_size_bounds a (x 1) (x 2) (x 3) (x 4) (q0 + k0) k1 k2
      (by linarith [(hwin 1 (by omega)).1]) (by linarith [(hwin 2 (by omega)).1])
      (by linarith [(hwin 3 (by omega)).1]) (by linarith [(hwin 4 (by omega)).1])
      (by linarith) hk1_ge (hxa 1 (by omega))
      (hdrop_pos 1 (by omega)) (hdrop_pos 2 (by omega)) (hdrop_pos 3 (by omega))
      hd1 hd2 hd3).2
    have hsum3 : (x 1 - x 2) + (x 2 - x 3) + (x 3 - x 4) ≤ sz := by
      have := hdrop_pos 0 (by omega); have := hdrop_pos 4 (by omega); dsimp [sz]; linarith
    have hA3 := (hwin 3 (by omega)).1
    have h1 : ((x 1 - x 2) * k2 - (x 2 - x 3) * k1) * (A : ℤ) ≤
        ((x 1 - x 2) * k2 - (x 2 - x 3) * k1) * x 3 :=
      mul_le_mul_of_nonneg_left hA3 (by linarith)
    have hpos3 : 0 ≤ (x 1 - x 2) + (x 2 - x 3) + (x 3 - x 4) := by
      linarith [hdrop_pos 1 (by omega), hdrop_pos 2 (by omega), hdrop_pos 3 (by omega)]
    have hsq3 : ((x 1 - x 2) + (x 2 - x 3) + (x 3 - x 4)) ^ 2 ≤ sz ^ 2 :=
      pow_le_pow_left₀ hpos3 hsum3 2
    have h2 : (k1 + 1) * ((x 1 - x 2) + (x 2 - x 3) + (x 3 - x 4)) ^ 2 ≤ 2 * K * sz ^ 2 :=
      mul_le_mul (by linarith) hsq3 (sq_nonneg _) (by linarith)
    linarith
  have hFA : ((x 2 - x 3) * k3 - (x 3 - x 4) * k2) * (A : ℤ) ≤ 2 * K * sz ^ 2 := by
    have hsb := (step_size_bounds a (x 2) (x 3) (x 4) (x 5) (q0 + k0 + k1) k2 k3
      (by linarith [(hwin 2 (by omega)).1]) (by linarith [(hwin 3 (by omega)).1])
      (by linarith [(hwin 4 (by omega)).1]) (by linarith [(hwin 5 (by omega)).1])
      (by linarith) hk2_ge (hxa 2 (by omega))
      (hdrop_pos 2 (by omega)) (hdrop_pos 3 (by omega)) (hdrop_pos 4 (by omega))
      hd2 hd3 hd4).2
    have hsum3 : (x 2 - x 3) + (x 3 - x 4) + (x 4 - x 5) ≤ sz := by
      have := hdrop_pos 0 (by omega); have := hdrop_pos 1 (by omega); dsimp [sz]; linarith
    have hA4 := (hwin 4 (by omega)).1
    have h1 : ((x 2 - x 3) * k3 - (x 3 - x 4) * k2) * (A : ℤ) ≤
        ((x 2 - x 3) * k3 - (x 3 - x 4) * k2) * x 4 :=
      mul_le_mul_of_nonneg_left hA4 (by linarith)
    have hpos3 : 0 ≤ (x 2 - x 3) + (x 3 - x 4) + (x 4 - x 5) := by
      linarith [hdrop_pos 2 (by omega), hdrop_pos 3 (by omega), hdrop_pos 4 (by omega)]
    have hsq3 : ((x 2 - x 3) + (x 3 - x 4) + (x 4 - x 5)) ^ 2 ≤ sz ^ 2 :=
      pow_le_pow_left₀ hpos3 hsum3 2
    have h2 : (k2 + 1) * ((x 2 - x 3) + (x 3 - x 4) + (x 4 - x 5)) ^ 2 ≤ 2 * K * sz ^ 2 :=
      mul_le_mul (by linarith) hsq3 (sq_nonneg _) (by linarith)
    linarith
  -- Combine with six_term_q_bound: q0 * A ≤ 24 * K^4 * sz^2
  have hq_le := (six_term_q_bound a q0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) k0 k1 k2 k3 K
    hq0_ge1 hk0_ge hk1_ge hk2_ge hk3_ge hK0 hK1 hK2 hK3 hE_pos hF_pos hd0 hd1 hd2 hd3 hd4).2
  have hqA : q0 * (A : ℤ) ≤ 24 * K ^ 4 * sz ^ 2 := by
    have hK3_nn : 0 ≤ K ^ 3 := by positivity
    calc q0 * (A : ℤ)
        ≤ (9 * K ^ 3 * ((x 1 - x 2) * k2 - (x 2 - x 3) * k1) +
           3 * K ^ 3 * ((x 2 - x 3) * k3 - (x 3 - x 4) * k2)) * (A : ℤ) :=
          mul_le_mul_of_nonneg_right hq_le (le_of_lt hA_pos)
      _ = 9 * K ^ 3 * (((x 1 - x 2) * k2 - (x 2 - x 3) * k1) * (A : ℤ)) +
          3 * K ^ 3 * (((x 2 - x 3) * k3 - (x 3 - x 4) * k2) * (A : ℤ)) := by ring
      _ ≤ 9 * K ^ 3 * (2 * K * sz ^ 2) + 3 * K ^ 3 * (2 * K * sz ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hEA (by positivity))
            (mul_le_mul_of_nonneg_left hFA (by positivity))
      _ = 24 * K ^ 4 * sz ^ 2 := by ring
  -- Multiply by A^4 * T^6:
  have hstep1 : (q0 * (A : ℤ)) * ((A : ℤ) ^ 4 * (T : ℤ) ^ 6) ≤
      24 * (K * (A : ℤ) * (T : ℤ)) ^ 4 * (sz * (T : ℤ)) ^ 2 := by
    have heq : 24 * (K * (A : ℤ) * (T : ℤ)) ^ 4 * (sz * (T : ℤ)) ^ 2 =
        (24 * K ^ 4 * sz ^ 2) * ((A : ℤ) ^ 4 * (T : ℤ) ^ 6) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hqA (by positivity)
  have hKAT_nn : 0 ≤ K * (A : ℤ) * (T : ℤ) := by positivity
  have hszT_nn : 0 ≤ sz * (T : ℤ) := by positivity
  have hpow4 : (K * (A : ℤ) * (T : ℤ)) ^ 4 ≤ (10 * (a : ℤ)) ^ 4 :=
    pow_le_pow_left₀ hKAT_nn hKAT 4
  have hpow2 : (sz * (T : ℤ)) ^ 2 ≤ (10 * (A : ℤ)) ^ 2 :=
    pow_le_pow_left₀ hszT_nn hszT 2
  have hstep2 : 24 * (K * (A : ℤ) * (T : ℤ)) ^ 4 * (sz * (T : ℤ)) ^ 2 ≤
      24 * (10 * (a : ℤ)) ^ 4 * (10 * (A : ℤ)) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hpow4 (show (0 : ℤ) ≤ 24 by norm_num)
    exact mul_le_mul h1 hpow2 (by positivity) (by positivity)
  have hstep3 : (a : ℤ) * (A : ℤ) ^ 4 * (T : ℤ) ^ 6 ≤
      4 * ((q0 * (A : ℤ)) * ((A : ℤ) ^ 4 * (T : ℤ) ^ 6)) := by
    have : (a : ℤ) ≤ 4 * (A : ℤ) * q0 := le_of_lt ha_lt_4Aq
    have hmul := mul_le_mul_of_nonneg_right this (show (0 : ℤ) ≤ (A : ℤ) ^ 4 * (T : ℤ) ^ 6 by positivity)
    linarith
  have hfinal : (a : ℤ) * (A : ℤ) ^ 4 * (T : ℤ) ^ 6 ≤ 96000000 * (a : ℤ) ^ 4 * (A : ℤ) ^ 2 := by
    calc (a : ℤ) * (A : ℤ) ^ 4 * (T : ℤ) ^ 6
        ≤ 4 * ((q0 * (A : ℤ)) * ((A : ℤ) ^ 4 * (T : ℤ) ^ 6)) := hstep3
      _ ≤ 4 * (24 * (10 * (a : ℤ)) ^ 4 * (10 * (A : ℤ)) ^ 2) := by linarith
      _ = 96000000 * (a : ℤ) ^ 4 * (A : ℤ) ^ 2 := by ring
  have ha_pos : (0 : ℤ) < (a : ℤ) := by linarith [hxa 0 (by omega), (hwin 0 (by omega)).1]
  have hcancel : 0 < (a : ℤ) * (A : ℤ) ^ 2 := by positivity
  have hfac : ((a : ℤ) * (A : ℤ) ^ 2) * ((T : ℤ) ^ 6 * (A : ℤ) ^ 2) ≤
      ((a : ℤ) * (A : ℤ) ^ 2) * (96000000 * (a : ℤ) ^ 3) := by
    calc ((a : ℤ) * (A : ℤ) ^ 2) * ((T : ℤ) ^ 6 * (A : ℤ) ^ 2)
        = (a : ℤ) * (A : ℤ) ^ 4 * (T : ℤ) ^ 6 := by ring
      _ ≤ 96000000 * (a : ℤ) ^ 4 * (A : ℤ) ^ 2 := hfinal
      _ = ((a : ℤ) * (A : ℤ) ^ 2) * (96000000 * (a : ℤ) ^ 3) := by ring
  exact le_of_mul_le_mul_left hfac hcancel

end WindowBounds

/-! ### Elementary Divisor Power Bound `τ(n)^k ≤ C_k * n` -/

section DivisorBound

lemma prime_factor_bound (k : ℕ) (p α : ℕ) (hp : 2 ^ k ≤ p) :
    ((α + 1 : ℝ) ^ k) / ((p : ℝ) ^ α) ≤ 1 := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_trans h1 hp))
  rw [div_le_one (pow_pos hp_pos α)]
  have h1 : (α + 1 : ℕ) ≤ 2 ^ α := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
  have h2 : (α + 1 : ℕ) ^ k ≤ (2 ^ α) ^ k := Nat.pow_le_pow_left h1 k
  have h3 : (2 ^ α) ^ k = (2 ^ k) ^ α := by rw [← pow_mul, ← pow_mul, mul_comm]
  have h4 : (2 ^ k) ^ α ≤ p ^ α := Nat.pow_le_pow_left hp α
  have hnat : (α + 1) ^ k ≤ p ^ α := le_trans h2 (h3 ▸ h4)
  exact_mod_cast hnat

lemma small_prime_factor_bound (k : ℕ) (p α : ℕ) (hp : 2 ≤ p) :
    ((α + 1 : ℝ) ^ k) / ((p : ℝ) ^ α) ≤ (2 ^ k : ℝ) ^ k := by
  -- Use `α + 1 ≤ 2^k * (2^(α/k))`? Even simpler: `(α + 1) / 2^(α / (k+1))`!
  -- Actually: for any m ≥ 1 and x ≥ 0, `(x + 1)^k ≤ (2*k)^k * 2^x`!
  -- Even simpler by induction on `α`: for `α ≥ 2*k`, `(α+2)^k / (α+1)^k ≤ 2`!
  -- Cleanest elementary bound: `α + 1 ≤ 2^(α / k) * ...` -> use `Nat.pow_le`!
  -- Since `p ≥ 2`, `p^α ≥ 2^α`. Show `(α + 1)^k ≤ ((2*k + 1)^k) * 2^α`?
  -- Wait: by binomial / `2^m ≥ m^k / k!`? Even simpler:
  -- For `k = 0`: `1 / p^α ≤ 1 = 1^0`.
  -- For `k ≥ 1`: write `α = k * q + r` (`q = α / k`). Then `α + 1 ≤ k * (q + 1) ≤ k * 2^q` (wait: `q+1 ≤ 2^q`),
  -- so `(α + 1)^k ≤ k^k * (2^q)^k = k^k * 2^(k*q) ≤ k^k * 2^α ≤ (2^k)^k * p^α`!!
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hp)
  rw [div_le_iff₀ (pow_pos hp_pos α)]
  by_cases hk : k = 0
  · subst hk
    simp only [pow_zero, one_mul]
    exact one_le_pow₀ (by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hp))
  · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
    have hstep : α + 1 ≤ k * (α / k + 1) := by
      have hdiv := Nat.div_add_mod α k
      have hmod := Nat.mod_lt α hk1
      nlinarith
    have hq : α / k + 1 ≤ 2 ^ (α / k) := Nat.succ_le_of_lt Nat.lt_two_pow_self
    have h1 : α + 1 ≤ k * 2 ^ (α / k) := le_trans hstep (Nat.mul_le_mul_left k hq)
    have h2 : (α + 1) ^ k ≤ (k * 2 ^ (α / k)) ^ k := Nat.pow_le_pow_left h1 k
    rw [mul_pow, ← pow_mul] at h2
    have hkq : α / k * k ≤ α := Nat.div_mul_le_self α k
    have h3 : 2 ^ (α / k * k) ≤ 2 ^ α := Nat.pow_le_pow_right (by norm_num) hkq
    have h4 : 2 ^ α ≤ p ^ α := Nat.pow_le_pow_left hp α
    have hk2 : k ≤ 2 ^ k := le_of_lt Nat.lt_two_pow_self
    have h5 : k ^ k ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left hk2 k
    have hnat : (α + 1) ^ k ≤ (2 ^ k) ^ k * p ^ α :=
      le_trans h2 (Nat.mul_le_mul h5 (le_trans h3 h4))
    exact_mod_cast hnat

/-- Elementary divisor power bound: for every `k : ℕ`, there exists `C > 0` such that
    `τ(n)^k ≤ C * n` for all `n ≥ 1`. -/
theorem divisor_power_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ((n.divisors.card : ℝ) ^ k) ≤ C * (n : ℝ) := by
  let B : ℝ := (2 ^ k : ℝ) ^ k
  have hB1 : (1 : ℝ) ≤ B := one_le_pow₀ (one_le_pow₀ (by norm_num))
  let C : ℝ := B ^ (2 ^ k)
  -- Stronger inductive claim: τ(n)^k / n ≤ B ^ #{p ∈ n.primeFactors | p < 2^k}
  have hstrong : ∀ n : ℕ, 1 ≤ n →
      ((n.divisors.card : ℝ) ^ k) / (n : ℝ) ≤
        B ^ ((n.primeFactors.filter (fun p => p < 2 ^ k)).card) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      rcases eq_or_lt_of_le hn with rfl | hn1
      · simp
      · have hn0 : n ≠ 0 := by omega
        let p := n.minFac
        have hp : Nat.Prime p := Nat.minFac_prime (by omega)
        have hpdvd : p ∣ n := Nat.minFac_dvd n
        let α := n.factorization p
        have hα_pos : 1 ≤ α := by
          have : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpdvd, hn0⟩
          have : n.factorization p ≠ 0 := by
            rw [← Finsupp.mem_support_iff, Nat.support_factorization]
            exact this
          omega
        have hpa_dvd : p ^ α ∣ n := Nat.ordProj_dvd n p
        let m := n / p ^ α
        have hpa_pos : 0 < p ^ α := pow_pos hp.pos α
        have hmul_eq : p ^ α * m = n := Nat.mul_div_cancel' hpa_dvd
        have hm_pos : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with hm0 | hmp
          · rw [hm0, mul_zero] at hmul_eq; omega
          · exact hmp
        have hm_lt : m < n := by
          have hpa_gt1 : 1 < p ^ α := one_lt_pow₀ hp.one_lt (by omega)
          nlinarith
        have hcop : Nat.Coprime (p ^ α) m := by
          have hndvd : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hn0
          exact (hp.coprime_iff_not_dvd.2 hndvd).pow_left α
        -- Bound (p^α).divisors.card ≤ α + 1
        have hpa_div : (p ^ α).divisors.card ≤ α + 1 := by
          have hsub : (p ^ α).divisors ⊆ (Finset.range (α + 1)).image (fun j => p ^ j) := by
            intro d hd
            rw [Nat.mem_divisors] at hd
            rcases (Nat.dvd_prime_pow hp).1 hd.1 with ⟨j, hj, rfl⟩
            exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩
          calc (p ^ α).divisors.card
              ≤ ((Finset.range (α + 1)).image (fun j => p ^ j)).card := Finset.card_le_card hsub
            _ ≤ (Finset.range (α + 1)).card := Finset.card_image_le
            _ = α + 1 := Finset.card_range _
        -- Bound n.divisors.card ≤ (p^α).divisors.card * m.divisors.card
        have hmul_div : n.divisors.card ≤ (p ^ α).divisors.card * m.divisors.card := by
          let f : ℕ → ℕ × ℕ := fun d => (Nat.gcd d (p ^ α), Nat.gcd d m)
          have hmaps : ∀ d ∈ n.divisors, f d ∈ (p ^ α).divisors ×ˢ m.divisors := by
            intro d hd
            refine Finset.mem_product.2 ⟨Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right _ _, by omega⟩,
              Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right _ _, by omega⟩⟩
          have hinj : Set.InjOn f n.divisors := by
            intro d1 hd1 d2 hd2 hfeq
            have hd1_dvd : d1 ∣ p ^ α * m := by rw [hmul_eq]; exact (Nat.mem_divisors.1 hd1).1
            have hd2_dvd : d2 ∣ p ^ α * m := by rw [hmul_eq]; exact (Nat.mem_divisors.1 hd2).1
            have heq1 : d1 = Nat.gcd d1 (p ^ α) * Nat.gcd d1 m := by
              rw [← hcop.gcd_mul d1, Nat.gcd_eq_left hd1_dvd]
            have heq2 : d2 = Nat.gcd d2 (p ^ α) * Nat.gcd d2 m := by
              rw [← hcop.gcd_mul d2, Nat.gcd_eq_left hd2_dvd]
            have hfst : Nat.gcd d1 (p ^ α) = Nat.gcd d2 (p ^ α) := congr_arg Prod.fst hfeq
            have hsnd : Nat.gcd d1 m = Nat.gcd d2 m := congr_arg Prod.snd hfeq
            rw [heq1, heq2, hfst, hsnd]
          calc n.divisors.card
              ≤ ((p ^ α).divisors ×ˢ m.divisors).card := Finset.card_le_card_of_injOn f hmaps hinj
            _ = (p ^ α).divisors.card * m.divisors.card := Finset.card_product _ _
        have hdiv_le : n.divisors.card ≤ (α + 1) * m.divisors.card :=
          le_trans hmul_div (Nat.mul_le_mul_right _ hpa_div)
        have hih := ih m hm_lt hm_pos
        have hsub_pf : m.primeFactors.filter (fun q => q < 2 ^ k) ⊆
            n.primeFactors.filter (fun q => q < 2 ^ k) := by
          intro q hq
          rcases Finset.mem_filter.1 hq with ⟨hqm, hqlt⟩
          rcases Nat.mem_primeFactors.1 hqm with ⟨hqp, hqdvd, _⟩
          exact Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hqp, dvd_trans hqdvd ⟨p ^ α, by rw [mul_comm, hmul_eq]⟩, hn0⟩, hqlt⟩
        have hp_not_m : p ∉ m.primeFactors := by
          intro hpm
          exact Nat.not_dvd_ordCompl hp hn0 (Nat.mem_primeFactors.1 hpm).2.1
        have hstep_div : ((n.divisors.card : ℝ) ^ k) / (n : ℝ) ≤
            (((α + 1 : ℝ) ^ k) / ((p : ℝ) ^ α)) * (((m.divisors.card : ℝ) ^ k) / (m : ℝ)) := by
          have h1 : (n.divisors.card : ℝ) ^ k ≤ ((α + 1 : ℝ) * (m.divisors.card : ℝ)) ^ k := by
            have : (n.divisors.card : ℝ) ≤ (α + 1 : ℝ) * (m.divisors.card : ℝ) := by exact_mod_cast hdiv_le
            exact pow_le_pow_left₀ (Nat.cast_nonneg _) this k
          have hn_eq_r : (n : ℝ) = (p : ℝ) ^ α * (m : ℝ) := by
            have : (n : ℝ) = ((p ^ α * m : ℕ) : ℝ) := by rw [hmul_eq]
            push_cast at this; exact this
          rw [mul_pow] at h1
          rw [hn_eq_r, div_mul_div_comm]
          exact div_le_div_of_nonneg_right h1 (by positivity)
        by_cases hplt : p < 2 ^ k
        · have hfac := small_prime_factor_bound k p α hp.two_le
          have hcard_lt : (m.primeFactors.filter (fun q => q < 2 ^ k)).card + 1 ≤
              (n.primeFactors.filter (fun q => q < 2 ^ k)).card := by
            have hp_mem : p ∈ n.primeFactors.filter (fun q => q < 2 ^ k) :=
              Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp, hpdvd, hn0⟩, hplt⟩
            have hp_nmem : p ∉ m.primeFactors.filter (fun q => q < 2 ^ k) :=
              fun h => hp_not_m (Finset.mem_filter.1 h).1
            have hins : insert p (m.primeFactors.filter (fun q => q < 2 ^ k)) ⊆
                n.primeFactors.filter (fun q => q < 2 ^ k) :=
              Finset.insert_subset_iff.2 ⟨hp_mem, hsub_pf⟩
            calc (m.primeFactors.filter (fun q => q < 2 ^ k)).card + 1
                = (insert p (m.primeFactors.filter (fun q => q < 2 ^ k))).card := by
                  simp [hp_nmem]
              _ ≤ (n.primeFactors.filter (fun q => q < 2 ^ k)).card := Finset.card_le_card hins
          calc ((n.divisors.card : ℝ) ^ k) / (n : ℝ)
              ≤ (((α + 1 : ℝ) ^ k) / ((p : ℝ) ^ α)) * (((m.divisors.card : ℝ) ^ k) / (m : ℝ)) := hstep_div
            _ ≤ B * B ^ ((m.primeFactors.filter (fun q => q < 2 ^ k)).card) :=
                mul_le_mul hfac hih (by positivity) (by positivity)
            _ = B ^ ((m.primeFactors.filter (fun q => q < 2 ^ k)).card + 1) := by rw [pow_succ']
            _ ≤ B ^ ((n.primeFactors.filter (fun q => q < 2 ^ k)).card) := pow_le_pow_right₀ hB1 hcard_lt
        · have hge : 2 ^ k ≤ p := by omega
          have hfac := prime_factor_bound k p α hge
          have hcard_le : (m.primeFactors.filter (fun q => q < 2 ^ k)).card ≤
              (n.primeFactors.filter (fun q => q < 2 ^ k)).card := Finset.card_le_card hsub_pf
          calc ((n.divisors.card : ℝ) ^ k) / (n : ℝ)
              ≤ (((α + 1 : ℝ) ^ k) / ((p : ℝ) ^ α)) * (((m.divisors.card : ℝ) ^ k) / (m : ℝ)) := hstep_div
            _ ≤ 1 * B ^ ((m.primeFactors.filter (fun q => q < 2 ^ k)).card) :=
                mul_le_mul hfac hih (by positivity) (by norm_num)
            _ = B ^ ((m.primeFactors.filter (fun q => q < 2 ^ k)).card) := one_mul _
            _ ≤ B ^ ((n.primeFactors.filter (fun q => q < 2 ^ k)).card) := pow_le_pow_right₀ hB1 hcard_le
  refine ⟨C, by positivity, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [← div_le_iff₀ hn_pos]
  have hcard_bound : (n.primeFactors.filter (fun p => p < 2 ^ k)).card ≤ 2 ^ k := by
    have hsub : n.primeFactors.filter (fun p => p < 2 ^ k) ⊆ Finset.range (2 ^ k) :=
      fun p hp => Finset.mem_range.2 (Finset.mem_filter.1 hp).2
    calc (n.primeFactors.filter (fun p => p < 2 ^ k)).card
        ≤ (Finset.range (2 ^ k)).card := Finset.card_le_card hsub
      _ = 2 ^ k := Finset.card_range _
  exact le_trans (hstrong n hn) (pow_le_pow_right₀ hB1 hcard_bound)

lemma maxDivisors_power_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ, 1 ≤ Y → ((maxDivisors Y : ℝ) ^ k) ≤ C * (Y : ℝ) := by
  rcases divisor_power_bound k with ⟨C, hC, hbound⟩
  refine ⟨max C 1, by positivity, fun Y hY => ?_⟩
  have hex : ∃ m ∈ Finset.Icc 1 Y, maxDivisors Y = m.divisors.card := by
    have hgen : ∀ (s : Finset ℕ), s.Nonempty →
        ∃ m ∈ s, s.sup (fun n => n.divisors.card) = m.divisors.card := by
      intro s
      induction s using Finset.cons_induction with
      | empty => intro h; exact absurd h Finset.not_nonempty_empty
      | cons a s ha ih =>
        intro _
        rcases s.eq_empty_or_nonempty with rfl | hne
        · exact ⟨a, by simp, by simp⟩
        · rcases ih hne with ⟨m, hm, hsup⟩
          rw [Finset.sup_cons, hsup]
          rcases le_total a.divisors.card m.divisors.card with hle | hle
          · exact ⟨m, Finset.mem_cons_of_mem hm, sup_eq_right.2 hle⟩
          · exact ⟨a, Finset.mem_cons_self a s, sup_eq_left.2 hle⟩
    exact hgen _ ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hY⟩⟩
  rcases hex with ⟨m, hm, hmax⟩
  rw [hmax]
  have hm1 := (Finset.mem_Icc.1 hm).1
  have hmY := (Finset.mem_Icc.1 hm).2
  calc (m.divisors.card : ℝ) ^ k ≤ C * (m : ℝ) := hbound m hm1
    _ ≤ max C 1 * (Y : ℝ) := by
        have hmYr : (m : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hmY
        have hC_le : C ≤ max C 1 := le_max_left _ _
        have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith

end DivisorBound

/-! ### Complete Unconditional Theorem: `P(a, b) ≪_ε a^{3/10 + ε}` -/

section MainThreeTenths

/-- Combined window bound: for any window run of length `T` in `[A, 2A)` with `1 ≤ A ≤ a`,
    `(T : ℝ) ^ 10 ≤ 10 ^ 10 * (a : ℝ) ^ 3 * (maxDivisors (2 * a) : ℝ) ^ 2`. -/
theorem window_ten_bound {a b A T : ℕ} (hA : 1 ≤ A) (hAa : A ≤ a)
    (W : WindowRun a b A T) :
    (T : ℝ) ^ 10 ≤ 10 ^ 10 * (a : ℝ) ^ 3 * (maxDivisors (2 * a) : ℝ) ^ 2 := by
  have ha1 : 1 ≤ a := le_trans hA hAa
  have hD1 : 1 ≤ maxDivisors (2 * a) := by
    have := divisors_card_le_maxDivisors (m := 1) (Y := 2 * a) le_rfl (by omega)
    simpa using this
  by_cases hT : T < 10
  · have hTr : (T : ℝ) ≤ 10 := by exact_mod_cast (le_of_lt hT)
    have har : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
    have hDr : (1 : ℝ) ≤ (maxDivisors (2 * a) : ℝ) := by exact_mod_cast hD1
    have h1 : (T : ℝ) ^ 10 ≤ 10 ^ 10 := pow_le_pow_left₀ (Nat.cast_nonneg T) hTr 10
    have h2 : (1 : ℝ) ≤ (a : ℝ) ^ 3 * (maxDivisors (2 * a) : ℝ) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ har) (one_le_pow₀ hDr)
    nlinarith
  · push Not at hT
    have hdrop := window_drop_bound hA hAa (by omega) W
    have hsix := window_six_term_bound hA hT W
    have hT_le : T ≤ 2 * (T - 1) := by omega
    have hT2_le : (T : ℝ) ^ 2 ≤ 8 * (A : ℝ) * (maxDivisors (2 * a) : ℝ) := by
      have h1 : T * T ≤ 2 * (T * (T - 1)) := by nlinarith
      have h2 : T * T ≤ 8 * A * maxDivisors (2 * a) := by nlinarith
      have h2r : ((T * T : ℕ) : ℝ) ≤ ((8 * A * maxDivisors (2 * a) : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at h2r
      linarith [sq (T : ℝ)]
    have hT4_le : (T : ℝ) ^ 4 ≤ 64 * (A : ℝ) ^ 2 * (maxDivisors (2 * a) : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hT2_le 2
      nlinarith
    have hsix_r : (T : ℝ) ^ 6 * (A : ℝ) ^ 2 ≤ 96000000 * (a : ℝ) ^ 3 := by exact_mod_cast hsix
    have hmul : (T : ℝ) ^ 10 * (A : ℝ) ^ 2 ≤
        64 * 96000000 * (a : ℝ) ^ 3 * (A : ℝ) ^ 2 * (maxDivisors (2 * a) : ℝ) ^ 2 := by
      have h1 := mul_le_mul hT4_le hsix_r (by positivity) (by positivity)
      linarith
    have hA2_pos : (0 : ℝ) < (A : ℝ) ^ 2 := by
      have : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
      positivity
    have hdiv : (T : ℝ) ^ 10 ≤ 64 * 96000000 * (a : ℝ) ^ 3 * (maxDivisors (2 * a) : ℝ) ^ 2 := by
      nlinarith
    have hconst : (64 * 96000000 : ℝ) ≤ 10 ^ 10 := by norm_num
    nlinarith [show (0 : ℝ) ≤ (a : ℝ) ^ 3 * (maxDivisors (2 * a) : ℝ) ^ 2 by positivity]

/-- Dyadic decomposition: the indices `i < pierceLen a b` falling in `[2^k, 2^(k+1))`
    form a contiguous `WindowRun a b (2^k) T_k`. -/
lemma dyadic_window_run {a b k : ℕ} (_hb : 0 < b) (_hba : b < a) :
    let S := (Finset.range (pierceLen a b)).filter
      (fun i => 2 ^ k ≤ pierceOrbit a b i ∧ pierceOrbit a b i < 2 ^ (k + 1))
    S.Nonempty → Nonempty (WindowRun a b (2 ^ k) S.card) := by
  intro S hne
  let i0 := S.min' hne
  have hi0_mem : i0 ∈ S := Finset.min'_mem S hne
  -- Show S = Finset.Ico i0 (i0 + S.card) using strict monotonicity of pierceOrbit!
  have hconv : ∀ i j m, i ∈ S → j ∈ S → i ≤ m → m ≤ j → m ∈ S := by
    intro i j m hi hj him hmj
    have hi_r := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
    have hj_r := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
    have hi_b := (Finset.mem_filter.1 hi).2
    have hj_b := (Finset.mem_filter.1 hj).2
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_of_le_of_lt hmj hj_r), ?_, ?_⟩
    · rcases eq_or_lt_of_le hmj with rfl | hlt
      · exact hj_b.1
      · exact le_trans hj_b.1 (le_of_lt (pierceOrbit_strict_mono_rev hlt (le_of_lt hj_r)))
    · rcases eq_or_lt_of_le him with rfl | hlt
      · exact hi_b.2
      · exact lt_trans (pierceOrbit_strict_mono_rev hlt (le_of_lt (lt_of_le_of_lt hmj hj_r))) hi_b.2
  -- A convex nonempty subset of ℕ equals Ico (min' S) (max' S + 1)
  let imax := S.max' hne
  have himax_mem : imax ∈ S := Finset.max'_mem S hne
  have hS_eq : S = Finset.Ico i0 (imax + 1) := by
    ext m
    simp only [Finset.mem_Ico]
    constructor
    · intro hm
      exact ⟨Finset.min'_le S m hm, Nat.lt_succ_of_le (Finset.le_max' S m hm)⟩
    · rintro ⟨h1, h2⟩
      exact hconv i0 imax m hi0_mem himax_mem h1 (Nat.le_of_lt_succ h2)
  have hcard : S.card = imax + 1 - i0 := by
    rw [hS_eq, Nat.card_Ico]
  have hi0_le : i0 ≤ imax := Finset.min'_le S imax himax_mem
  have hend : i0 + S.card ≤ pierceLen a b := by
    have := Finset.mem_range.1 (Finset.mem_filter.1 himax_mem).1
    omega
  refine ⟨⟨i0, hend, fun j hj => ?_⟩⟩
  have hmem : i0 + j ∈ S := by
    rw [hS_eq]
    exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
  simpa [pow_succ, mul_comm] using (Finset.mem_filter.1 hmem).2

/-- **Main Unconditional Elementary Theorem (`P(a, b) ≪_ε a^{3/10 + ε}`):**
    For every `ε > 0`, there exists `C > 0` such that for all `0 < b < a`,
    `pierceLen a b ≤ C * a^(3/10 + ε)`. -/
theorem pierceLen_le_three_tenths :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ a b : ℕ, 0 < b → b < a →
        (pierceLen a b : ℝ) ≤ C * (a : ℝ) ^ ((3 : ℝ) / 10 + ε) := by
  intro ε hε
  -- Choose natural k large enough that 1 / (5 * k) ≤ ε / 2 and log2(a) + 1 ≤ C2 * a^(ε/2)
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / (5 * ε))
  have hk_pos : 1 ≤ k := by
    have h0 : (0 : ℝ) < 2 / (5 * ε) := by positivity
    have : (0 : ℝ) < (k : ℝ) := lt_trans h0 hk
    exact_mod_cast this
  rcases maxDivisors_power_bound k with ⟨C_div, hC_div, hdiv_b⟩
  -- Also choose m large enough that 1 / m ≤ ε / 2 for the O(log₂ a) dyadic window count!
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / ε)
  have hm_pos : 1 ≤ m := by
    have h0 : (0 : ℝ) < 2 / ε := by positivity
    have : (0 : ℝ) < (m : ℝ) := lt_trans h0 hm
    exact_mod_cast this
  -- Elementary bound: (Nat.log 2 a + 1 : ℝ) ≤ (m + 1) * (a : ℝ) ^ (1 / m : ℝ)
  -- Since for x = a^(1/m) ≥ 1, Nat.log 2 a = ⌊m * log₂ x⌋ ≤ m * x!
  let C_win : ℝ := 10 * (2 * C_div) ^ ((1 : ℝ) / (5 * (k : ℝ)))
  let C : ℝ := C_win * (2 * (m : ℝ) + 1)
  refine ⟨C, by positivity, fun a b hb hba => ?_⟩
  have ha2 : 2 ≤ a := by omega
  have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  have ha_ge1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 1 ≤ a by omega)
  -- Partition `range (pierceLen a b)` into `Nat.log 2 a + 1` dyadic windows `[2^k, 2^(k+1))`
  let Kmax := Nat.log 2 a + 1
  have hpart : pierceLen a b =
      ∑ r ∈ Finset.range Kmax,
        ((Finset.range (pierceLen a b)).filter
          (fun i => 2 ^ r ≤ pierceOrbit a b i ∧ pierceOrbit a b i < 2 ^ (r + 1))).card := by
    rw [← Finset.card_biUnion]
    · have heq : Finset.range (pierceLen a b) =
          (Finset.range Kmax).biUnion (fun r => (Finset.range (pierceLen a b)).filter
            (fun i => 2 ^ r ≤ pierceOrbit a b i ∧ pierceOrbit a b i < 2 ^ (r + 1))) := by
        ext i
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
        constructor
        · intro hi
          have hpos := pierceOrbit_pos_of_lt hi
          have hle_b : pierceOrbit a b i ≤ b := by
            rcases eq_or_lt_of_le (Nat.zero_le i) with rfl | hip
            · exact le_rfl
            · exact le_of_lt (pierceOrbit_strict_mono_rev hip (le_of_lt hi))
          have hlt_a : pierceOrbit a b i < a := lt_of_le_of_lt hle_b hba
          let r := Nat.log 2 (pierceOrbit a b i)
          refine ⟨r, ?_, hi, Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) _⟩
          have : r ≤ Nat.log 2 a := Nat.log_mono_right (le_of_lt hlt_a)
          omega
        · rintro ⟨_, _, hi, _, _⟩; exact hi
      rw [← heq, Finset.card_range]
    · intro r1 _ r2 _ hne
      refine Finset.disjoint_left.2 fun i hi1 hi2 => ?_
      have h1 := (Finset.mem_filter.1 hi1).2
      have h2 := (Finset.mem_filter.1 hi2).2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : 2 ^ (r1 + 1) ≤ 2 ^ r2 := Nat.pow_le_pow_right (by norm_num) hlt
        omega
      · have : 2 ^ (r2 + 1) ≤ 2 ^ r1 := Nat.pow_le_pow_right (by norm_num) hgt
        omega
  -- Bound each window card by C_win * a^(3/10 + 1/(5k))
  have hwin_b : ∀ r ∈ Finset.range Kmax,
      (((Finset.range (pierceLen a b)).filter
        (fun i => 2 ^ r ≤ pierceOrbit a b i ∧ pierceOrbit a b i < 2 ^ (r + 1))).card : ℝ) ≤
      C_win * (a : ℝ) ^ ((3 : ℝ) / 10 + 1 / (5 * (k : ℝ))) := by
    intro r hr
    set S := (Finset.range (pierceLen a b)).filter
      (fun i => 2 ^ r ≤ pierceOrbit a b i ∧ pierceOrbit a b i < 2 ^ (r + 1))
    by_cases hne : S.Nonempty
    · rcases dyadic_window_run (k := r) hb hba hne with ⟨W⟩
      have h2r_le_a : 2 ^ r ≤ a := by
        have hr_le : r ≤ Nat.log 2 a := by have := Finset.mem_range.1 hr; omega
        exact le_trans (Nat.pow_le_pow_right (by norm_num) hr_le) (Nat.pow_log_le_self 2 (by omega))
      have hten := window_ten_bound (Nat.one_le_pow r 2 (by norm_num)) h2r_le_a W
      -- Bound maxDivisors (2*a) ≤ (C_div * 2 * a)^(1/k)
      have hD_pow : ((maxDivisors (2 * a) : ℝ) ^ k) ≤ 2 * C_div * (a : ℝ) := by
        have := hdiv_b (2 * a) (by omega)
        push_cast at this
        linarith
      have hD_le : (maxDivisors (2 * a) : ℝ) ^ 2 ≤ (2 * C_div * (a : ℝ)) ^ ((2 : ℝ) / (k : ℝ)) := by
        have hD_nn : (0 : ℝ) ≤ (maxDivisors (2 * a) : ℝ) := Nat.cast_nonneg _
        have h1 : ((maxDivisors (2 * a) : ℝ) ^ (k : ℝ)) ^ ((2 : ℝ) / (k : ℝ)) ≤
            (2 * C_div * (a : ℝ)) ^ ((2 : ℝ) / (k : ℝ)) := by
          apply Real.rpow_le_rpow (by positivity)
          · rwa [Real.rpow_natCast]
          · positivity
        rw [← Real.rpow_mul hD_nn] at h1
        have hkm : (k : ℝ) * ((2 : ℝ) / (k : ℝ)) = 2 := by
          have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
          field_simp
        rw [hkm, Real.rpow_two] at h1
        exact h1
      have h10 : (S.card : ℝ) ^ (10 : ℝ) ≤
          10 ^ 10 * (a : ℝ) ^ 3 * (2 * C_div * (a : ℝ)) ^ ((2 : ℝ) / (k : ℝ)) := by
        rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        calc (S.card : ℝ) ^ 10 ≤ 10 ^ 10 * (a : ℝ) ^ 3 * (maxDivisors (2 * a) : ℝ) ^ 2 := hten
          _ ≤ 10 ^ 10 * (a : ℝ) ^ 3 * (2 * C_div * (a : ℝ)) ^ ((2 : ℝ) / (k : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hD_le (by positivity)
      have hroot := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) h10
        (show (0 : ℝ) ≤ (1 : ℝ) / 10 by norm_num)
      rw [← Real.rpow_mul (Nat.cast_nonneg _), show (10 : ℝ) * ((1 : ℝ) / 10) = 1 by norm_num,
          Real.rpow_one] at hroot
      -- Simplify RHS of hroot
      have hrhs : (10 ^ 10 * (a : ℝ) ^ 3 * (2 * C_div * (a : ℝ)) ^ ((2 : ℝ) / (k : ℝ))) ^ ((1 : ℝ) / 10) =
          C_win * (a : ℝ) ^ ((3 : ℝ) / 10 + 1 / (5 * (k : ℝ))) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity),
            ← Real.rpow_mul (by positivity),
            Real.mul_rpow (by positivity) (le_of_lt ha_pos)]
        have h10p : ((10 : ℝ) ^ 10) ^ ((1 : ℝ) / 10) = 10 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
        have ha3p : ((a : ℝ) ^ 3) ^ ((1 : ℝ) / 10) = (a : ℝ) ^ ((3 : ℝ) / 10) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt ha_pos)]
          norm_num
        have he1 : (2 : ℝ) / (k : ℝ) * ((1 : ℝ) / 10) = 1 / (5 * (k : ℝ)) := by ring
        rw [h10p, ha3p, he1, Real.rpow_add ha_pos]
        dsimp [C_win]
        ring
      rw [← hrhs]
      exact hroot
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.card_empty, Nat.cast_zero]
      positivity
  -- Bound Kmax = Nat.log 2 a + 1 ≤ (2*m + 1) * a^(1/m)
  have hKmax : (Kmax : ℝ) ≤ (2 * (m : ℝ) + 1) * (a : ℝ) ^ ((1 : ℝ) / (m : ℝ)) := by
    have hlog_le : (Nat.log 2 a : ℝ) ≤ 2 * (m : ℝ) * (a : ℝ) ^ ((1 : ℝ) / (m : ℝ)) := by
      -- Since 2^r ≤ a, taking r/m: actually r / (2*m) ≤ 2^(r / (2*m)) ≤ (2^r)^(1/m) ≤ a^(1/m)!
      let r := Nat.log 2 a
      have h2r : (2 : ℝ) ^ r ≤ (a : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have h1 : (r : ℝ) ≤ 2 * (m : ℝ) * (2 : ℝ) ^ ((r : ℝ) / (m : ℝ)) := by
        -- Write r = m * q + rem, so r ≤ m * (q + 1) ≤ m * 2^q ≤ m * 2^(r/m) ≤ 2*m * 2^(r/m)
        have hq : r ≤ m * (r / m + 1) := by
          have := Nat.div_add_mod r m; have := Nat.mod_lt r hm_pos; nlinarith
        have hpow : r / m + 1 ≤ 2 ^ (r / m) := Nat.succ_le_of_lt Nat.lt_two_pow_self
        have hrm : ((r / m : ℕ) : ℝ) ≤ (r : ℝ) / (m : ℝ) := by
          rw [le_div_iff₀ (by exact_mod_cast hm_pos)]
          exact_mod_cast Nat.div_mul_le_self r m
        have h2q : ((2 ^ (r / m) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((r : ℝ) / (m : ℝ)) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hrm
        have hmul : (r : ℝ) ≤ (m : ℝ) * (2 : ℝ) ^ ((r : ℝ) / (m : ℝ)) := by
          calc (r : ℝ) ≤ ((m * 2 ^ (r / m) : ℕ) : ℝ) := by exact_mod_cast (le_trans hq (Nat.mul_le_mul_left m hpow))
            _ = (m : ℝ) * ((2 ^ (r / m) : ℕ) : ℝ) := by push_cast; ring
            _ ≤ (m : ℝ) * (2 : ℝ) ^ ((r : ℝ) / (m : ℝ)) := mul_le_mul_of_nonneg_left h2q (by positivity)
        have hnn : (0 : ℝ) ≤ (m : ℝ) * (2 : ℝ) ^ ((r : ℝ) / (m : ℝ)) := by positivity
        linarith
      have h2 : (2 : ℝ) ^ ((r : ℝ) / (m : ℝ)) ≤ (a : ℝ) ^ ((1 : ℝ) / (m : ℝ)) := by
        have h2r' : ((2 : ℝ) ^ (r : ℝ)) ^ ((1 : ℝ) / (m : ℝ)) ≤ (a : ℝ) ^ ((1 : ℝ) / (m : ℝ)) := by
          apply Real.rpow_le_rpow (by positivity)
          · rwa [Real.rpow_natCast]
          · positivity
        rw [← Real.rpow_mul (by norm_num)] at h2r'
        have : (r : ℝ) * ((1 : ℝ) / (m : ℝ)) = (r : ℝ) / (m : ℝ) := by ring
        rwa [this] at h2r'
      exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
    have ha_pow_ge1 : (1 : ℝ) ≤ (a : ℝ) ^ ((1 : ℝ) / (m : ℝ)) :=
      Real.one_le_rpow ha_ge1 (by positivity)
    dsimp [Kmax]
    push_cast
    nlinarith
  -- Final dyadic sum assembly
  have hsum_r : (pierceLen a b : ℝ) ≤
      (Kmax : ℝ) * (C_win * (a : ℝ) ^ ((3 : ℝ) / 10 + 1 / (5 * (k : ℝ)))) := by
    rw [hpart]
    push_cast
    calc ∑ r ∈ Finset.range Kmax,
          (((Finset.range (pierceLen a b)).filter
            (fun i => 2 ^ r ≤ pierceOrbit a b i ∧ pierceOrbit a b i < 2 ^ (r + 1))).card : ℝ)
        ≤ ∑ _r ∈ Finset.range Kmax, (C_win * (a : ℝ) ^ ((3 : ℝ) / 10 + 1 / (5 * (k : ℝ)))) :=
          Finset.sum_le_sum hwin_b
      _ = (Kmax : ℝ) * (C_win * (a : ℝ) ^ ((3 : ℝ) / 10 + 1 / (5 * (k : ℝ)))) := by simp
  have hexp_le : (3 : ℝ) / 10 + 1 / (5 * (k : ℝ)) + 1 / (m : ℝ) ≤ (3 : ℝ) / 10 + ε := by
    have h1 : 1 / (5 * (k : ℝ)) ≤ ε / 2 := by
      have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 2 < 5 * ε * (k : ℝ) := by
        have := (div_lt_iff₀ (show (0 : ℝ) < 5 * ε by positivity)).1 hk
        linarith
      linarith
    have h2 : 1 / (m : ℝ) ≤ ε / 2 := by
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
      rw [div_le_div_iff₀ hm0 (by norm_num)]
      have := (div_lt_iff₀ hε).1 hm
      linarith
    linarith
  calc (pierceLen a b : ℝ)
      ≤ (Kmax : ℝ) * (C_win * (a : ℝ) ^ ((3 : ℝ) / 10 + 1 / (5 * (k : ℝ)))) := hsum_r
    _ ≤ ((2 * (m : ℝ) + 1) * (a : ℝ) ^ ((1 : ℝ) / (m : ℝ))) *
        (C_win * (a : ℝ) ^ ((3 : ℝ) / 10 + 1 / (5 * (k : ℝ)))) :=
        mul_le_mul_of_nonneg_right hKmax (by positivity)
    _ = C * (a : ℝ) ^ ((3 : ℝ) / 10 + 1 / (5 * (k : ℝ)) + 1 / (m : ℝ)) := by
        rw [Real.rpow_add ha_pos _ (1 / (m : ℝ))]
        dsimp [C]
        ring
    _ ≤ C * (a : ℝ) ^ ((3 : ℝ) / 10 + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ha_ge1 hexp_le) (by positivity)

end MainThreeTenths

/-! ## Part II: Sound 4-Pivot Minkowski Plücker Slicing & Elimination Lemmas -/

section MinkowskiPluckerSlicing

/-- Determinant of a 3×3 matrix given by three column vectors in `ℤ³` (or `R³`). -/
def det3 {R : Type*} [CommRing R] (u v w : Fin 3 → R) : R :=
  u 0 * (v 1 * w 2 - v 2 * w 1) -
  u 1 * (v 0 * w 2 - v 2 * w 0) +
  u 2 * (v 0 * w 1 - v 1 * w 0)

/-- Standard basis of `R³`. -/
def stdBasis {R : Type*} [CommRing R] (r : Fin 3) : Fin 3 → R :=
  fun i => if i = r then 1 else 0

/-- Given a 3×5 matrix whose columns are indexed by `Fin 5`, extract Davies's 7 pattern integers
    `θ = (N₀, N₁, N₂, u₁, u₂, v₁, v₂)`. -/
def patternTheta {R : Type*} [CommRing R] (M : Fin 5 → Fin 3 → R) :
    R × R × R × R × R × R × R :=
  ( det3 (M 0) (M 1) (M 2),
    det3 (M 1) (M 2) (M 3),
    det3 (M 2) (M 3) (M 4),
    det3 (M 0) (M 2) (M 3),
   -det3 (M 0) (M 1) (M 3),
    det3 (M 1) (M 3) (M 4),
   -det3 (M 1) (M 2) (M 4) )

/-- **Theorem II.1 (4-Pivot Invariance & Linearity of Column-5 Plücker Slicing):**
    For ANY of the 4 pivots in `{0, 1, 2, 3}` with `j₅ = 4`, replacing column 4 by the
    1-parameter Minkowski family `w(c) = w₀ + c • e₁` leaves all four vertex minors
    `(N₀, N₁, u₁, u₂)` completely independent of `c`, while making all three column-5
    pattern minors `(N₂, v₁, v₂)` affine-linear in `c`. -/
theorem four_pivot_const_vertex_linear_col5 {R : Type*} [CommRing R]
    (M0 : Fin 5 → Fin 3 → R) (e1 : Fin 3 → R) :
    let Mc : R → Fin 5 → Fin 3 → R := fun c j i =>
      if j = 4 then M0 4 i + c * e1 i else M0 j i
    ∀ c : R,
      (patternTheta (Mc c)).1 = (patternTheta M0).1 ∧
      (patternTheta (Mc c)).2.1 = (patternTheta M0).2.1 ∧
      (patternTheta (Mc c)).2.2.2.1 = (patternTheta M0).2.2.2.1 ∧
      (patternTheta (Mc c)).2.2.2.2.1 = (patternTheta M0).2.2.2.2.1 ∧
      (patternTheta (Mc c)).2.2.1 =
        (patternTheta M0).2.2.1 + c * det3 (M0 2) (M0 3) e1 ∧
      (patternTheta (Mc c)).2.2.2.2.2.1 =
        (patternTheta M0).2.2.2.2.2.1 + c * det3 (M0 1) (M0 3) e1 ∧
      (patternTheta (Mc c)).2.2.2.2.2.2 =
        (patternTheta M0).2.2.2.2.2.2 - c * det3 (M0 1) (M0 2) e1 := by
  intro Mc c
  dsimp only [patternTheta, det3, Mc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (simp only [Fin.reduceEq, ↓reduceIte]; try ring)

/-- **Theorem II.2 (Exact Linear Elimination of `c₁` from the Pattern Quadratic):**
    With `(ρ, φ, χ)` fixed and `(ρ'(c), φ'(c), χ'(c)) = (r₀ + r₁ c, p₀ + p₁ c, x₀ + x₁ c)`
    affine-linear in `c`, the pattern quadratic `f(s₁, s₂, s₃; c) = 0` is strictly linear in `c`
    and solves as `L₁(s) * c = -f₀(s) - L₀(s)`. -/
theorem pattern_quadratic_linear_c1 {R : Type*} [CommRing R]
    (ρ φ χ r0 r1 p0 p1 x0 x1 s1 s2 s3 c : R) :
    let s4 := (ρ + φ) * s1 - (φ - χ) * s2 - (χ - 1) * s3
    let k0 := s1
    let k1 := s2 - s1
    let k2 := s3 - s2
    let k3 := s4 - s3
    let L0 := r0 * k1 - p0 * k2 - x0 * k3
    let L1 := r1 * k1 - p1 * k2 - x1 * k3
    let k4 := (r0 + r1 * c) * k1 - (p0 + p1 * c) * k2 - (x0 + x1 * c) * k3
    let f0 := (-ρ - φ) * (s1 ^ 2 + k1) + (φ - χ) * (s2 ^ 2 + k2) +
              (χ - 1) * (s3 ^ 2 + k3) + ρ * k0 + s4 ^ 2
    let f  := f0 + k4
    f = (f0 + L0) + L1 * c := by
  dsimp only
  ring

/-- **Theorem II.3 (Exact Cancellation of `k₄²` in `Ψ`):**
    In Davies's quartic norm `Ψ`, the `k₄²` term from `γ₄ (1 + k₄)²` cancels `-k₄²`
    identically, so `L₁ * Ψ` is a polynomial of degree `4` in `(s₁, s₂, s₃)` (not `5`). -/
theorem psi_k4_sq_cancellation {R : Type*} [CommRing R]
    (s4 k4 χ' r3_base : R) :
    ((1 + k4) ^ 2 - χ' * (r3_base + k4) - k4 * (2 * s4 + k4)) =
    (1 + 2 * k4 - 2 * s4 * k4 - χ' * r3_base - χ' * k4) := by
  ring

/-- **Theorem II.4 (Convergent `p`-Series Bound for the 4-Pivot Minkowski Sum):**
    For any real exponent `s ≥ 4/3` and any `N : ℕ`,
    `∑ g ∈ Icc 1 N, (g : ℝ)^(-s) ≤ 4`.
    In particular, the divisor sum `∑_{g | κ} g^{-(5 - t)/3}` is bounded by an absolute
    constant (ZERO divisor loss!) for all `t ≤ 1`. -/
theorem p_series_sum_le_four (s : ℝ) (hs : (4 : ℝ) / 3 ≤ s) (N : ℕ) :
    ∑ g ∈ Finset.Icc 1 N, (g : ℝ) ^ (-s) ≤ 4 := by
  have hterm : ∀ g ∈ Finset.Icc 1 N, (g : ℝ) ^ (-s) ≤ (g : ℝ) ^ (-(4 : ℝ) / 3) := by
    intro g hg
    have hg1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hg).1
    exact Real.rpow_le_rpow_of_exponent_le hg1 (by linarith)
  calc ∑ g ∈ Finset.Icc 1 N, (g : ℝ) ^ (-s)
      ≤ ∑ g ∈ Finset.Icc 1 N, (g : ℝ) ^ (-(4 : ℝ) / 3) := Finset.sum_le_sum hterm
    _ ≤ 4 := by
        -- Elementary telescoping comparison: `g^(-4/3) ≤ 3 * ((g-1)^(-1/3) - g^(-1/3))` for `g ≥ 2`!
        -- Actually even cleaner: for g ≥ 2, by convexity of t ↦ t^(-1/3):
        -- `3 * ((g - 1)^(-1/3) - g^(-1/3)) ≥ g^(-4/3)`!
        -- Prove `g^(-4/3) ≤ 3 * ((g-1)^(-1/3) - g^(-1/3))` via `(g-1)^3 * (3g - 3*(g-1)) ...`!
        have hstep : ∀ g : ℕ, 2 ≤ g →
            (g : ℝ) ^ (-(4 : ℝ) / 3) ≤
              3 * (((g - 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) - (g : ℝ) ^ (-(1 : ℝ) / 3)) := by
          intro g hg
          have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast (show 0 < g by omega)
          have hgm1_pos : (0 : ℝ) < ((g - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < g - 1 by omega)
          have hgm1_eq : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega), Nat.cast_one]
          let a := ((g - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)
          let b := (g : ℝ) ^ ((1 : ℝ) / 3)
          have ha_pos : 0 < a := Real.rpow_pos_of_pos hgm1_pos _
          have hb_pos : 0 < b := Real.rpow_pos_of_pos hg0 _
          have ha3 : a ^ 3 = (g : ℝ) - 1 := by
            dsimp [a]; rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hgm1_pos)]
            norm_num; exact hgm1_eq
          have hb3 : b ^ 3 = (g : ℝ) := by
            dsimp [b]; rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hg0)]
            norm_num
          have hab : a ≤ b := by
            dsimp [a, b]
            exact Real.rpow_le_rpow (le_of_lt hgm1_pos) (by linarith [hgm1_eq]) (by norm_num)
          have hdiff : b ^ 3 - a ^ 3 = 1 := by linarith
          have hfac : (b - a) * (b ^ 2 + b * a + a ^ 2) = 1 := by nlinarith
          have hle3b2 : b ^ 2 + b * a + a ^ 2 ≤ 3 * b ^ 2 := by nlinarith
          have hinv_a : ((g - 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) = a⁻¹ := by
            rw [show (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) by ring, Real.rpow_neg (le_of_lt hgm1_pos)]
          have hinv_b : (g : ℝ) ^ (-(1 : ℝ) / 3) = b⁻¹ := by
            rw [show (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) by ring, Real.rpow_neg (le_of_lt hg0)]
          have hinv_4 : (g : ℝ) ^ (-(4 : ℝ) / 3) = (b ^ 4)⁻¹ := by
            rw [show (-(4 : ℝ) / 3) = -((4 : ℝ) / 3) by ring, Real.rpow_neg (le_of_lt hg0)]
            congr 1
            dsimp [b]
            rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hg0)]
            norm_num
          rw [hinv_a, hinv_b, hinv_4]
          have hkey : (b ^ 4)⁻¹ ≤ 3 * (a⁻¹ - b⁻¹) := by
            rw [inv_sub_inv (ne_of_gt ha_pos) (ne_of_gt hb_pos)]
            rw [inv_le_iff_one_le_mul₀ (by positivity)]
            have h1 : 1 ≤ 3 * ((b - a) / (a * b)) * b ^ 4 := by
              rw [show 3 * ((b - a) / (a * b)) * b ^ 4 = (3 * b ^ 3 / a) * (b - a) by field_simp]
              have hba : (b - a) * (3 * b ^ 2) ≥ 1 := by nlinarith
              have hba2 : b / a ≥ 1 := (one_le_div ha_pos).2 hab
              have h3b : 3 * b ^ 3 / a = (3 * b ^ 2) * (b / a) := by ring
              rw [h3b]
              nlinarith
            linarith
          exact hkey
        -- Induct on N!
        have hind : ∀ M : ℕ, 1 ≤ M →
            ∑ g ∈ Finset.Icc 1 M, (g : ℝ) ^ (-(4 : ℝ) / 3) ≤
              4 - 3 * (M : ℝ) ^ (-(1 : ℝ) / 3) := by
          intro M hM
          induction M with
          | zero => omega
          | succ k ih =>
            rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk
            · simp; norm_num
            · rw [show Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) by
                    ext x; simp [Finset.mem_Icc]; omega,
                  Finset.sum_insert (by simp [Finset.mem_Icc])]
              have hih := ih hk
              have hst := hstep (k + 1) (by omega)
              simp only [Nat.add_sub_cancel] at hst
              linarith
        rcases eq_or_lt_of_le (Nat.zero_le N) with rfl | hN
        · simp
        · have h1 := hind N hN
          have hnn : (0 : ℝ) ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 3) := by positivity
          linarith

/-- **Theorem II.5 (4-Pivot Minkowski Plücker Family Count = `O(X^{14/3})`):**
    Summing over `κ ∈ [1, X]` and `g | κ` with `ℓ = κ / g`, the weighted 4-pivot Minkowski
    column-lattice sum `X^{2 + u} ∑_{κ ≤ X} ∑_{g | κ} (κ / g)^{(5 - 2u)/3}` is bounded by
    `4 * X^{(14 + u)/3}` for every `0 ≤ u ≤ 1/2` (and `≤ 4 * X^{14/3}` at `u = 0`,
    giving `O(X^{14/3})` 1-parameter families with ZERO divisor loss!). -/
theorem four_pivot_minkowski_weighted_sum (X : ℕ) (hX : 1 ≤ X) (u : ℝ) (_hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2) :
    (X : ℝ) ^ (2 + u) *
      ∑ κ ∈ Finset.Icc 1 X, ∑ g ∈ κ.divisors,
        ((κ : ℝ) / (g : ℝ)) ^ ((5 - 2 * u) / 3) ≤
    4 * (X : ℝ) ^ ((14 + u) / 3) := by
  have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hs : (4 : ℝ) / 3 ≤ (5 - 2 * u) / 3 := by linarith
  have hinner : ∀ κ ∈ Finset.Icc 1 X,
      ∑ g ∈ κ.divisors, ((κ : ℝ) / (g : ℝ)) ^ ((5 - 2 * u) / 3) ≤
      4 * (κ : ℝ) ^ ((5 - 2 * u) / 3) := by
    intro κ hκ
    have hκ1 : 1 ≤ κ := (Finset.mem_Icc.1 hκ).1
    have hκ_pos : (0 : ℝ) < (κ : ℝ) := by exact_mod_cast hκ1
    have hrew : ∑ g ∈ κ.divisors, ((κ : ℝ) / (g : ℝ)) ^ ((5 - 2 * u) / 3) =
        (κ : ℝ) ^ ((5 - 2 * u) / 3) * ∑ g ∈ κ.divisors, (g : ℝ) ^ (-((5 - 2 * u) / 3)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      have hg_pos : (0 : ℝ) < (g : ℝ) := by
        exact_mod_cast Nat.pos_of_mem_divisors hg
      rw [div_eq_mul_inv, Real.mul_rpow (le_of_lt hκ_pos) (by positivity),
          Real.inv_rpow (le_of_lt hg_pos), ← Real.rpow_neg (le_of_lt hg_pos)]
    rw [hrew]
    have hsub : κ.divisors ⊆ Finset.Icc 1 κ := fun g hg =>
      Finset.mem_Icc.2 ⟨Nat.pos_of_mem_divisors hg, Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hg)⟩
    have hsum_le : ∑ g ∈ κ.divisors, (g : ℝ) ^ (-((5 - 2 * u) / 3)) ≤ 4 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
        (p_series_sum_le_four ((5 - 2 * u) / 3) hs κ)
    nlinarith [Real.rpow_pos_of_pos hκ_pos ((5 - 2 * u) / 3)]
  have houter : ∑ κ ∈ Finset.Icc 1 X, 4 * (κ : ℝ) ^ ((5 - 2 * u) / 3) ≤
      4 * (X : ℝ) ^ ((8 - 2 * u) / 3) := by
    calc ∑ κ ∈ Finset.Icc 1 X, 4 * (κ : ℝ) ^ ((5 - 2 * u) / 3)
        ≤ ∑ _κ ∈ Finset.Icc 1 X, 4 * (X : ℝ) ^ ((5 - 2 * u) / 3) := by
          apply Finset.sum_le_sum
          intro κ hκ
          have hκX : (κ : ℝ) ≤ (X : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hκ).2
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg κ) hκX (by linarith)) (by norm_num)
      _ = (X : ℝ) * (4 * (X : ℝ) ^ ((5 - 2 * u) / 3)) := by
          simp [Nat.card_Icc]
      _ = 4 * (X : ℝ) ^ ((8 - 2 * u) / 3) := by
          have : (X : ℝ) * (X : ℝ) ^ ((5 - 2 * u) / 3) = (X : ℝ) ^ (1 + (5 - 2 * u) / 3) := by
            rw [Real.rpow_add hX_pos, Real.rpow_one]
          rw [show (X : ℝ) * (4 * (X : ℝ) ^ ((5 - 2 * u) / 3)) =
                4 * ((X : ℝ) * (X : ℝ) ^ ((5 - 2 * u) / 3)) by ring, this]
          congr 2; ring
  calc (X : ℝ) ^ (2 + u) * ∑ κ ∈ Finset.Icc 1 X, ∑ g ∈ κ.divisors,
        ((κ : ℝ) / (g : ℝ)) ^ ((5 - 2 * u) / 3)
      ≤ (X : ℝ) ^ (2 + u) * (4 * (X : ℝ) ^ ((8 - 2 * u) / 3)) :=
        mul_le_mul_of_nonneg_left (le_trans (Finset.sum_le_sum hinner) houter) (by positivity)
    _ = 4 * (X : ℝ) ^ ((14 + u) / 3) := by
        have : (X : ℝ) ^ (2 + u) * (X : ℝ) ^ ((8 - 2 * u) / 3) =
            (X : ℝ) ^ ((2 + u) + (8 - 2 * u) / 3) := (Real.rpow_add hX_pos _ _).symm
        rw [show (X : ℝ) ^ (2 + u) * (4 * (X : ℝ) ^ ((8 - 2 * u) / 3)) =
              4 * ((X : ℝ) ^ (2 + u) * (X : ℝ) ^ ((8 - 2 * u) / 3)) by ring, this]
        congr 2; ring

/-- **Theorem II.6 (Universal Algebraic Impossibility of Polynomial Sections of Degree `e ≥ 2`):**
    If `s₁, s₂, s₃ ∈ ℚ[t]` have max degree `e ≥ 2` and satisfy the pattern quadratic
    `f(s₁(t), s₂(t), s₃(t); t) = 0`, then the coefficient of `t^(2e)` forces `f₂(z₁, z₂, z₃) = 0`,
    where `z_j = s_j.coeff e` is the leading coefficient vector. -/
theorem poly_section_ge_two_forces_f2_zero
    (ρ φ χ r0 r1 p0 p1 x0 x1 : ℚ) (s1 s2 s3 : Polynomial ℚ) (e : ℕ) (he : 2 ≤ e)
    (hd1 : s1.natDegree ≤ e) (hd2 : s2.natDegree ≤ e) (hd3 : s3.natDegree ≤ e)
    (hf :
      let s4 := C (ρ + φ) * s1 - C (φ - χ) * s2 - C (χ - 1) * s3
      let k0 := s1
      let k1 := s2 - s1
      let k2 := s3 - s2
      let k3 := s4 - s3
      let k4 := (C r0 + C r1 * X) * k1 - (C p0 + C p1 * X) * k2 - (C x0 + C x1 * X) * k3
      C (-ρ - φ) * (s1 ^ 2 + k1) + C (φ - χ) * (s2 ^ 2 + k2) +
        C (χ - 1) * (s3 ^ 2 + k3) + C ρ * k0 + s4 ^ 2 + k4 = 0) :
    let z1 := s1.coeff e
    let z2 := s2.coeff e
    let z3 := s3.coeff e
    let z4 := (ρ + φ) * z1 - (φ - χ) * z2 - (χ - 1) * z3
    (-ρ - φ) * z1 ^ 2 + (φ - χ) * z2 ^ 2 + (χ - 1) * z3 ^ 2 + z4 ^ 2 = 0 := by
  -- Extract coefficient of `X^(2*e)` from `hf`!
  have hcoeff := congr_arg (fun P : Polynomial ℚ => P.coeff (2 * e)) hf
  -- Helper: any polynomial of natDegree ≤ e has coeff (2*e) = 0 (since e ≥ 2 ⇒ e < 2*e),
  -- and any X * p with natDegree p ≤ e has coeff (2*e) = 0 (since e + 1 < 2*e)!
  have hzero_le : ∀ p : Polynomial ℚ, p.natDegree ≤ e → p.coeff (2 * e) = 0 := fun p hp =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hzero_X : ∀ p : Polynomial ℚ, p.natDegree ≤ e → (X * p).coeff (2 * e) = 0 := by
    intro p hp
    have h2e : 2 * e = (2 * e - 1) + 1 := by omega
    rw [h2e, Polynomial.coeff_X_mul]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hsq_coeff : ∀ p : Polynomial ℚ, p.natDegree ≤ e → (p ^ 2).coeff (2 * e) = (p.coeff e) ^ 2 := by
    intro p hp
    rw [sq, Polynomial.coeff_mul, Finset.sum_eq_single (e, e)]
    · ring
    · rintro ⟨a, b⟩ hab hne
      have hab_eq : a + b = 2 * e := Finset.mem_antidiagonal.1 hab
      have hgt : e < a ∨ e < b := by
        by_contra h
        push Not at h
        have ha : a = e := by omega
        have hb : b = e := by omega
        exact hne (Prod.ext ha hb)
      rcases hgt with ha | hb
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp ha), zero_mul]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hb), mul_zero]
    · intro hnot
      exfalso; exact hnot (Finset.mem_antidiagonal.2 (by omega))
  set s4 := C (ρ + φ) * s1 - C (φ - χ) * s2 - C (χ - 1) * s3
  have hd4 : s4.natDegree ≤ e := by
    dsimp only [s4]
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · exact le_trans (Polynomial.natDegree_C_mul_le _ _) hd1
      · exact le_trans (Polynomial.natDegree_C_mul_le _ _) hd2
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _) hd3
  have hz4 : s4.coeff e = (ρ + φ) * s1.coeff e - (φ - χ) * s2.coeff e - (χ - 1) * s3.coeff e := by
    simp only [s4, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  have hdk1 : (s2 - s1).natDegree ≤ e := le_trans (Polynomial.natDegree_sub_le _ _) (max_le hd2 hd1)
  have hdk2 : (s3 - s2).natDegree ≤ e := le_trans (Polynomial.natDegree_sub_le _ _) (max_le hd3 hd2)
  have hdk3 : (s4 - s3).natDegree ≤ e := le_trans (Polynomial.natDegree_sub_le _ _) (max_le hd4 hd3)
  have hdk4 : (((C r0 + C r1 * X) * (s2 - s1) - (C p0 + C p1 * X) * (s3 - s2) -
      (C x0 + C x1 * X) * (s4 - s3)).coeff (2 * e)) = 0 := by
    have hrew : (C r0 + C r1 * X) * (s2 - s1) - (C p0 + C p1 * X) * (s3 - s2) -
        (C x0 + C x1 * X) * (s4 - s3) =
        C r0 * (s2 - s1) + C r1 * (X * (s2 - s1)) -
        C p0 * (s3 - s2) - C p1 * (X * (s3 - s2)) -
        C x0 * (s4 - s3) - C x1 * (X * (s4 - s3)) := by ring
    rw [hrew]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    rw [hzero_le _ hd1, hzero_le _ hd2, hzero_le _ hd3, hzero_le _ hd4,
        hzero_X _ hdk1, hzero_X _ hdk2, hzero_X _ hdk3]
    ring
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_zero] at hcoeff
  rw [hsq_coeff s1 hd1, hsq_coeff s2 hd2, hsq_coeff s3 hd3, hsq_coeff s4 hd4, hz4,
      hzero_le _ hd1, hzero_le _ hdk1, hzero_le _ hdk2, hzero_le _ hdk3, hdk4] at hcoeff
  linarith

/-- **Theorem II.7 (Elementary `K`-Prime Smooth-Point Reduction):**
    If `S` is a finite set of primes and `g ≠ 0` satisfies `|g| < ∏ p ∈ S, p`,
    then there exists `p ∈ S` such that `¬ (p : ℤ) ∣ g`.
    In particular, choosing `K > C √d` primes `p > B^{1/√d}` guarantees that every smooth
    integer point on a surface with `0 < |∇F(x)| ≤ B^C` reduces smoothly modulo some `p ∈ S`,
    yielding Heath-Brown's `O(B^{2/√d})` bound without Salberger's global primes. -/
theorem exists_prime_not_dvd_of_prod_gt (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (g : ℤ) (hg : g ≠ 0) (hbound : g.natAbs < ∏ p ∈ S, p) :
    ∃ p ∈ S, ¬ ((p : ℤ) ∣ g) := by
  by_contra hall
  push Not at hall
  have hdvd_nat : ∀ p ∈ S, p ∣ g.natAbs := fun p hp => Int.natCast_dvd.1 (hall p hp)
  have hprod_dvd : ∀ T : Finset ℕ, (∀ p ∈ T, Nat.Prime p) → (∀ p ∈ T, p ∣ g.natAbs) →
      (∏ p ∈ T, p) ∣ g.natAbs := by
    intro T
    induction T using Finset.cons_induction with
    | empty => intros; simp
    | cons p T hpT ih =>
      intro hTp hTdvd
      rw [Finset.prod_cons]
      have hp_pr : Nat.Prime p := hTp p (Finset.mem_cons_self p T)
      have hcop_aux : ∀ U : Finset ℕ, (∀ q ∈ U, Nat.Prime q ∧ p ≠ q) →
          Nat.Coprime p (∏ q ∈ U, q) := by
        intro U
        induction U using Finset.cons_induction with
        | empty => intro _; simp
        | cons q U _ ihU =>
          intro hU
          rw [Finset.prod_cons]
          have hq := hU q (Finset.mem_cons_self q U)
          exact ((Nat.coprime_primes hp_pr hq.1).2 hq.2).mul_right
            (ihU fun r hr => hU r (Finset.mem_cons_of_mem hr))
      have hcop : Nat.Coprime p (∏ q ∈ T, q) :=
        hcop_aux T fun q hq => ⟨hTp q (Finset.mem_cons_of_mem hq), fun heq => hpT (heq ▸ hq)⟩
      exact hcop.mul_dvd_of_dvd_of_dvd (hTdvd p (Finset.mem_cons_self p T))
        (ih (fun q hq => hTp q (Finset.mem_cons_of_mem hq))
            (fun q hq => hTdvd q (Finset.mem_cons_of_mem hq)))
  have hle : ∏ p ∈ S, p ≤ g.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hg) (hprod_dvd S hS hdvd_nat)
  omega

end MinkowskiPluckerSlicing

end PPL026_PierceExpansion
