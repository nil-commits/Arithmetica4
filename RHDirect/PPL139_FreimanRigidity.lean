import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# PPL 139 — Verified Original Obstruction Theorems for Lifting `[BSSZ26]` to `ℚ`/`ℤ`

**Honest Status Label:** This module formalizes **verified original obstruction theorems**
discovered during our PPL 139 (Erdős Problem #52 · Sum-Product Conjecture over `ℤ`)
campaign analyzing Bloom–Sawin–Schildkraut–Zhelezov (`[BSSZ26]`, `arXiv:2605.28781`,
May 2026). It explains rigorously why `[BSSZ26]`'s real/number-field sum-product
counterexample `A = G · P ⊂ 𝒪_K` **cannot** be lifted into `ℚ` or `ℤ` via simultaneous
additive-and-multiplicative Freiman 2-homomorphisms, ring homomorphisms, or small-box
modular lifts.

**This is NOT a resolution of Erdős #52 (PPL 139)**, which remains open over `ℤ`.

## Main Theorems Formalized (0 `sorry`, 0 custom axioms, native Mathlib)

1. **General Quadratic-Unit Simultaneous Freiman 2-Homomorphism Rigidity
   (`no_simultaneous_freiman2_hom_of_quadratic_unit_field`,
    `no_simultaneous_freiman2_hom_of_quadratic_unit`):**
   Over any commutative ring `R` containing an element `u₀` satisfying
   `u₀^2 - c * u₀ + s = 0` (`c ∈ ℤ`, `s ∈ {-1, 1}`) whose quadratic polynomial
   `X^2 - c X + s ∈ ℚ[X]` has no rational root, there exists **no** map `φ : R → ℚ`
   that is simultaneously injective, an additive Freiman 2-homomorphism, and a
   multiplicative Freiman 2-homomorphism on `A = G * P`, as soon as `1, u₀, u₀^2 ∈ G`
   and `P` contains the tiny local additive stencil around a point `p₀` with
   `u₀ * p₀ ≠ p₀` (nonvanishing `φ p₀ ≠ 0` is **derived** from injectivity on `A`).

2. **General Degree-`m` Box-Norm Rigidity (`no_simultaneous_freiman2_hom_of_poly_box`):**
   Full degree-`m` version matching Obstruction 2 of `BSSZ26_Z_OBSTRUCTION_REPORT.md`:
   for any `f ∈ ℤ[X]` with `f(u₀) = 0` in `R` and no root in a field `F`, and any
   subadditive symmetric seminorm `N : R → ℝ` (modeling `max_i |σ_i(·)|` on `𝒪_K`)
   whose box `{p₀ + w | N w ≤ R_box} ⊆ P` contains the partial-sum radius of `f(u₀)`,
   no injective simultaneous additive-and-multiplicative Freiman 2-homomorphism
   `φ : R → F` exists on `A = G * P`.

3. **Concrete Algebraic-Integer Instantiations & No Ring Homomorphisms:**
   - `no_simultaneous_freiman2_hom_quad_field`: Explicit instantiation on `ℤ[√2]`
     (`Zsqrtd 2`) with fundamental unit `u₂ = 1 + √2` (`u₂^2 - 2 u₂ - 1 = 0`) and
     5-point stencil `{p₀, p₀ + 1, p₀ + u₂, p₀ + 2 u₂, p₀ + u₂^2}` (plus a standalone
     definition-free restatement `no_simultaneous_freiman2_hom_zsqrtd2_standalone`).
   - `no_simultaneous_freiman2_hom_zsqrtd3`: Explicit instantiation on `ℤ[√3]`
     (`Zsqrtd 3`) with fundamental unit `u₃ = 2 + √3` (`u₃^2 - 4 u₃ + 1 = 0`, norm `+1`).
   - `no_simultaneous_freiman2_hom_golden_ring`: Explicit instantiation on the golden
     ratio ring `ℤ[(1 + √5)/2]` (`QuadraticAlgebra ℤ 1 1`) with `ω^2 - ω - 1 = 0`
     using the minimal **4-element** stencil `{p₀, p₀ + 1, p₀ + ω, p₀ + ω^2}`.
   - `no_ringHom_zsqrtd_prime`, `no_ringHom_zsqrtd_int_or_rat : IsEmpty (Zsqrtd 2 →+* ℚ)`,
     and `no_ringHom_zsqrtd_int : IsEmpty (Zsqrtd 2 →+* ℤ)` (Obstruction 1).

4. **Small-Box Mod-`M` Unit-Collapse Divisor Bound (Obstruction 4):**
   - `small_box_mod_eq_exact`: If `a * b ≡ T [ZMOD M]` with `2 * |a * b| < M` and
     `2 * |T| < M`, then `a * b = T` exactly in `ℤ`.
   - `small_box_unit_collapse_card_le`: If `hat : α → ℤ` is injective on a finite set
     `G` and `hat u * hat (inv u) = T` (`T ≠ 0`) for every `u ∈ G`, then
     `G.card ≤ 2 * T.natAbs.divisors.card`.
   - `small_box_mod_unit_collapse_bound`: Full end-to-end bound for any ring
     homomorphism `π : R →+* ZMod M` and dilation `t : ZMod M` (covering prime,
     prime-power `p`-adic, and composite CRT moduli simultaneously).
-/

namespace PPL139_FreimanRigidity

open scoped BigOperators
open Finset Polynomial

/-! ## Part 1: Core Definitions & General Freiman 2-Homomorphism Algebra -/

section FreimanCore

/-- Product set `G · P = {u * p | u ∈ G, p ∈ P}` in a commutative ring `R`. -/
def productSet {R : Type*} [Mul R] (G P : Set R) : Set R :=
  {a : R | ∃ u ∈ G, ∃ p ∈ P, a = u * p}

/-- `φ : R → F` is an additive Freiman 2-homomorphism on `A ⊆ R`. -/
def IsAddFreiman2Hom {R F : Type*} [Add R] [Add F] (A : Set R) (φ : R → F) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ a₃ ∈ A, ∀ a₄ ∈ A,
    a₁ + a₂ = a₃ + a₄ → φ a₁ + φ a₂ = φ a₃ + φ a₄

/-- `φ : R → F` is a multiplicative Freiman 2-homomorphism on `A ⊆ R`. -/
def IsMulFreiman2Hom {R F : Type*} [Mul R] [Mul F] (A : Set R) (φ : R → F) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ a₃ ∈ A, ∀ a₄ ∈ A,
    a₁ * a₂ = a₃ * a₄ → φ a₁ * φ a₂ = φ a₃ * φ a₄

lemma mem_productSet {R : Type*} [Mul R] {G P : Set R} {u p : R}
    (hu : u ∈ G) (hp : p ∈ P) : u * p ∈ productSet G P :=
  ⟨u, hu, p, hp, rfl⟩

lemma mem_productSet_of_one {R : Type*} [Monoid R] {G P : Set R} {p : R}
    (h1G : (1 : R) ∈ G) (hp : p ∈ P) : p ∈ productSet G P :=
  ⟨1, h1G, p, hp, (one_mul p).symm⟩

/-- Deriving `φ p₀ ≠ 0` automatically from injectivity and multiplicative Freiman
2-homomorphism on `G · P`, whenever `u₀ * p₀ ≠ p₀` and `1 ≠ 0` in `R`. -/
lemma phi_base_ne_zero {R F : Type*} [CommRing R] [Field F]
    {G P : Set R} {p₀ u₀ : R} {φ : R → F}
    (hInj : Set.InjOn φ (productSet G P))
    (hMul : IsMulFreiman2Hom (productSet G P) φ)
    (h1G : (1 : R) ∈ G) (huG : u₀ ∈ G)
    (hp₀ : p₀ ∈ P) (hp1 : p₀ + 1 ∈ P)
    (hup : u₀ * p₀ ≠ p₀) (h10 : (1 : R) ≠ 0) :
    φ p₀ ≠ 0 := by
  intro h0
  have ha₁ : u₀ * p₀ ∈ productSet G P := mem_productSet huG hp₀
  have ha₂ : p₀ + 1 ∈ productSet G P := mem_productSet_of_one h1G hp1
  have ha₃ : p₀ ∈ productSet G P := mem_productSet_of_one h1G hp₀
  have ha₄ : u₀ * (p₀ + 1) ∈ productSet G P := mem_productSet huG hp1
  have hprod : (u₀ * p₀) * (p₀ + 1) = p₀ * (u₀ * (p₀ + 1)) := by ring
  have hφmul : φ (u₀ * p₀) * φ (p₀ + 1) = φ p₀ * φ (u₀ * (p₀ + 1)) :=
    hMul _ ha₁ _ ha₂ _ ha₃ _ ha₄ hprod
  rw [h0, zero_mul] at hφmul
  rcases mul_eq_zero.mp hφmul with hleft | hright
  · exact hup (hInj ha₁ ha₃ (hleft.trans h0.symm))
  · have hEq : p₀ + 1 = p₀ := hInj ha₂ ha₃ (hright.trans h0.symm)
    have h1eq0 : (1 : R) = 0 := by
      have := congrArg (fun x => x - p₀) hEq
      simpa using this
    exact h10 h1eq0

/-- Multiplicative scaling factor `λ(u) = φ(u * p₀) / φ(p₀)` associated to `u ∈ G`. -/
def scale {R F : Type*} [Mul R] [Div F] (φ : R → F) (p₀ u : R) : F :=
  φ (u * p₀) / φ p₀

/-- Local additive linearization `L(w) = φ(p₀ + w) - φ(p₀)` centered at `p₀`. -/
def localLin {R F : Type*} [Add R] [Sub F] (φ : R → F) (p₀ w : R) : F :=
  φ (p₀ + w) - φ p₀

/-- Multiplicative separation on `G · P`: `φ (u * p) = scale φ p₀ u * φ p`. -/
lemma phi_mul_factor {R F : Type*} [CommRing R] [Field F]
    {G P : Set R} {p₀ u p : R} {φ : R → F}
    (hMul : IsMulFreiman2Hom (productSet G P) φ)
    (h1G : (1 : R) ∈ G) (hu : u ∈ G) (hp₀ : p₀ ∈ P) (hp : p ∈ P)
    (hφ0 : φ p₀ ≠ 0) :
    φ (u * p) = scale φ p₀ u * φ p := by
  have ha₁ : u * p ∈ productSet G P := mem_productSet hu hp
  have ha₂ : p₀ ∈ productSet G P := mem_productSet_of_one h1G hp₀
  have ha₃ : u * p₀ ∈ productSet G P := mem_productSet hu hp₀
  have ha₄ : p ∈ productSet G P := mem_productSet_of_one h1G hp
  have hEq : φ (u * p) * φ p₀ = φ (u * p₀) * φ p :=
    hMul _ ha₁ _ ha₂ _ ha₃ _ ha₄ (by ring)
  unfold scale
  rw [div_mul_eq_mul_div, eq_div_iff hφ0]
  exact hEq

lemma scale_one {R F : Type*} [CommRing R] [Field F]
    {p₀ : R} {φ : R → F} (hφ0 : φ p₀ ≠ 0) :
    scale φ p₀ 1 = 1 := by
  unfold scale
  rw [one_mul, div_self hφ0]

lemma scale_mul {R F : Type*} [CommRing R] [Field F]
    {G P : Set R} {p₀ u v : R} {φ : R → F}
    (hMul : IsMulFreiman2Hom (productSet G P) φ)
    (h1G : (1 : R) ∈ G) (hu : u ∈ G) (hv : v ∈ G) (huv : u * v ∈ G)
    (hp₀ : p₀ ∈ P) (hφ0 : φ p₀ ≠ 0) :
    scale φ p₀ (u * v) = scale φ p₀ u * scale φ p₀ v := by
  have ha₁ : u * p₀ ∈ productSet G P := mem_productSet hu hp₀
  have ha₂ : v * p₀ ∈ productSet G P := mem_productSet hv hp₀
  have ha₃ : (u * v) * p₀ ∈ productSet G P := mem_productSet huv hp₀
  have ha₄ : p₀ ∈ productSet G P := mem_productSet_of_one h1G hp₀
  have hEq : φ (u * p₀) * φ (v * p₀) = φ ((u * v) * p₀) * φ p₀ :=
    hMul _ ha₁ _ ha₂ _ ha₃ _ ha₄ (by ring)
  unfold scale
  rw [div_mul_div_comm, div_eq_div_iff hφ0 (mul_ne_zero hφ0 hφ0)]
  calc φ ((u * v) * p₀) * (φ p₀ * φ p₀)
      = (φ ((u * v) * p₀) * φ p₀) * φ p₀ := by ring
    _ = (φ (u * p₀) * φ (v * p₀)) * φ p₀ := by rw [← hEq]

lemma scale_pow {R F : Type*} [CommRing R] [Field F]
    {G P : Set R} {p₀ u : R} {φ : R → F}
    (hMul : IsMulFreiman2Hom (productSet G P) φ)
    (hp₀ : p₀ ∈ P) (hφ0 : φ p₀ ≠ 0) :
    ∀ k : ℕ, (∀ j ≤ k, u ^ j ∈ G) → scale φ p₀ (u ^ k) = (scale φ p₀ u) ^ k
  | 0, hG => by
      simpa using scale_one (p₀ := p₀) (φ := φ) hφ0
  | k + 1, hG => by
      have h1G : (1 : R) ∈ G := by simpa using hG 0 (Nat.zero_le _)
      have huG : u ∈ G := by simpa using hG 1 (Nat.succ_le_succ (Nat.zero_le k))
      have hukG : u ^ k ∈ G := hG k (Nat.le_succ k)
      have huk1G : u ^ k * u ∈ G := by
        simpa [pow_succ] using hG (k + 1) (le_refl _)
      rw [pow_succ, pow_succ, scale_mul hMul h1G hukG huG huk1G hp₀ hφ0]
      rw [scale_pow hMul hp₀ hφ0 k (fun j hj => hG j (Nat.le_trans hj (Nat.le_succ k)))]

lemma localLin_zero {R F : Type*} [AddCommGroup R] [AddCommGroup F]
    (φ : R → F) (p₀ : R) : localLin φ p₀ 0 = 0 := by
  simp [localLin]

lemma localLin_one_ne_zero {R F : Type*} [CommRing R] [AddCommGroup F]
    {G P : Set R} {p₀ : R} {φ : R → F}
    (hInj : Set.InjOn φ (productSet G P))
    (h1G : (1 : R) ∈ G) (hp₀ : p₀ ∈ P) (hp1 : p₀ + 1 ∈ P) (h10 : (1 : R) ≠ 0) :
    localLin φ p₀ 1 ≠ 0 := by
  intro h0
  unfold localLin at h0
  have hEq : φ (p₀ + 1) = φ p₀ := sub_eq_zero.mp h0
  have hpEq : p₀ + 1 = p₀ :=
    hInj (mem_productSet_of_one h1G hp1) (mem_productSet_of_one h1G hp₀) hEq
  have h1eq0 : (1 : R) = 0 := by
    have := congrArg (fun x => x - p₀) hpEq
    simpa using this
  exact h10 h1eq0

/-- Local additivity of `localLin` whenever `p₀, p₀ + w₁, p₀ + w₂, p₀ + (w₁ + w₂) ∈ P`. -/
lemma localLin_add {R F : Type*} [CommRing R] [CommRing F]
    {G P : Set R} {p₀ w₁ w₂ : R} {φ : R → F}
    (hAdd : IsAddFreiman2Hom (productSet G P) φ)
    (h1G : (1 : R) ∈ G)
    (hp₀ : p₀ ∈ P) (hw₁ : p₀ + w₁ ∈ P) (hw₂ : p₀ + w₂ ∈ P) (hw₁₂ : p₀ + (w₁ + w₂) ∈ P) :
    localLin φ p₀ (w₁ + w₂) = localLin φ p₀ w₁ + localLin φ p₀ w₂ := by
  have ha₁ : p₀ + w₁ ∈ productSet G P := mem_productSet_of_one h1G hw₁
  have ha₂ : p₀ + w₂ ∈ productSet G P := mem_productSet_of_one h1G hw₂
  have ha₃ : p₀ ∈ productSet G P := mem_productSet_of_one h1G hp₀
  have ha₄ : p₀ + (w₁ + w₂) ∈ productSet G P := mem_productSet_of_one h1G hw₁₂
  have hEq : φ (p₀ + w₁) + φ (p₀ + w₂) = φ p₀ + φ (p₀ + (w₁ + w₂)) :=
    hAdd _ ha₁ _ ha₂ _ ha₃ _ ha₄ (by ring)
  unfold localLin
  linear_combination -hEq

lemma localLin_neg {R F : Type*} [CommRing R] [CommRing F]
    {G P : Set R} {p₀ w : R} {φ : R → F}
    (hAdd : IsAddFreiman2Hom (productSet G P) φ)
    (h1G : (1 : R) ∈ G)
    (hp₀ : p₀ ∈ P) (hw : p₀ + w ∈ P) (hnw : p₀ + (-w) ∈ P) :
    localLin φ p₀ (-w) = -localLin φ p₀ w := by
  have h0 : p₀ + (w + -w) ∈ P := by simpa using hp₀
  have hadd := localLin_add hAdd h1G hp₀ hw hnw h0
  rw [add_neg_cancel, localLin_zero] at hadd
  linear_combination -hadd

lemma localLin_natMul {R F : Type*} [CommRing R] [CommRing F]
    {G P : Set R} {p₀ w : R} {φ : R → F}
    (hAdd : IsAddFreiman2Hom (productSet G P) φ)
    (h1G : (1 : R) ∈ G) :
    ∀ n : ℕ, (∀ k : ℕ, k ≤ n → p₀ + (k : R) * w ∈ P) →
      localLin φ p₀ ((n : R) * w) = (n : F) * localLin φ p₀ w
  | 0, _ => by simp [localLin]
  | n + 1, hP => by
      have hp₀ : p₀ ∈ P := by simpa using hP 0 (Nat.zero_le _)
      have hpw : p₀ + w ∈ P := by simpa using hP 1 (Nat.succ_le_succ (Nat.zero_le n))
      have hpnw : p₀ + (n : R) * w ∈ P := hP n (Nat.le_succ n)
      have hpn1w : p₀ + ((n : R) * w + w) ∈ P := by
        have h := hP (n + 1) (le_refl _)
        have heq : ((n + 1 : ℕ) : R) * w = (n : R) * w + w := by push_cast; ring
        rwa [heq] at h
      have hstep : ((n + 1 : ℕ) : R) * w = (n : R) * w + w := by push_cast; ring
      rw [hstep, localLin_add hAdd h1G hp₀ hpnw hpw hpn1w]
      rw [localLin_natMul hAdd h1G n (fun k hk => hP k (Nat.le_trans hk (Nat.le_succ n)))]
      push_cast
      ring

lemma localLin_intMul {R F : Type*} [CommRing R] [CommRing F]
    {G P : Set R} {p₀ w : R} {φ : R → F}
    (hAdd : IsAddFreiman2Hom (productSet G P) φ)
    (h1G : (1 : R) ∈ G)
    (hpw : p₀ + w ∈ P)
    (c : ℤ)
    (hP : ∀ k : ℤ, (0 ≤ k ∧ k ≤ c ∨ c ≤ k ∧ k ≤ 0) → p₀ + (k : R) * w ∈ P) :
    localLin φ p₀ ((c : R) * w) = (c : F) * localLin φ p₀ w := by
  by_cases hc : 0 ≤ c
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hc
    have hnat : ∀ k : ℕ, k ≤ n → p₀ + (k : R) * w ∈ P := by
      intro k hk
      have h := hP (k : ℤ) (Or.inl ⟨Int.natCast_nonneg k, Int.ofNat_le.mpr hk⟩)
      simpa using h
    simpa using localLin_natMul hAdd h1G n hnat
  · have hcneg : c ≤ -1 := by omega
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -c by omega)
    have hceq : c = -(n : ℤ) := by omega
    have hp₀ : p₀ ∈ P := by
      simpa using hP 0 (Or.inr ⟨by omega, le_refl 0⟩)
    have hpnw : p₀ + (-w) ∈ P := by
      have h := hP (-1) (Or.inr ⟨hcneg, by omega⟩)
      simpa using h
    have hnat : ∀ k : ℕ, k ≤ n → p₀ + (k : R) * (-w) ∈ P := by
      intro k hk
      have hk_range : c ≤ -(k : ℤ) ∧ -(k : ℤ) ≤ 0 := by omega
      have h := hP (-(k : ℤ)) (Or.inr hk_range)
      have heq : ((-(k : ℤ) : ℤ) : R) * w = (k : R) * (-w) := by push_cast; ring
      rwa [heq] at h
    have hL := localLin_natMul hAdd h1G n hnat
    have hLneg : localLin φ p₀ (-w) = -localLin φ p₀ w :=
      localLin_neg hAdd h1G hp₀ hpw hpnw
    rw [hceq]
    have hr : ((-(n : ℤ) : ℤ) : R) * w = (n : R) * (-w) := by push_cast; ring
    rw [hr, hL, hLneg]
    push_cast
    ring

/-- Key multiplicative-additive coupling identity:
`L(u * v) = scale φ p₀ u * L(v)` from `(u*(p₀+v)) + p₀ = (u*p₀) + (p₀ + u*v)`. -/
lemma localLin_mul_unit {R F : Type*} [CommRing R] [Field F]
    {G P : Set R} {p₀ u v : R} {φ : R → F}
    (hAdd : IsAddFreiman2Hom (productSet G P) φ)
    (hMul : IsMulFreiman2Hom (productSet G P) φ)
    (h1G : (1 : R) ∈ G) (hu : u ∈ G)
    (hp₀ : p₀ ∈ P) (hpv : p₀ + v ∈ P) (hpuv : p₀ + u * v ∈ P)
    (hφ0 : φ p₀ ≠ 0) :
    localLin φ p₀ (u * v) = scale φ p₀ u * localLin φ p₀ v := by
  have ha₁ : u * (p₀ + v) ∈ productSet G P := mem_productSet hu hpv
  have ha₂ : p₀ ∈ productSet G P := mem_productSet_of_one h1G hp₀
  have ha₃ : u * p₀ ∈ productSet G P := mem_productSet hu hp₀
  have ha₄ : p₀ + u * v ∈ productSet G P := mem_productSet_of_one h1G hpuv
  have hEq : φ (u * (p₀ + v)) + φ p₀ = φ (u * p₀) + φ (p₀ + u * v) :=
    hAdd _ ha₁ _ ha₂ _ ha₃ _ ha₄ (by ring)
  have hf₁ : φ (u * (p₀ + v)) = scale φ p₀ u * φ (p₀ + v) :=
    phi_mul_factor hMul h1G hu hp₀ hpv hφ0
  have hf₃ : φ (u * p₀) = scale φ p₀ u * φ p₀ :=
    phi_mul_factor hMul h1G hu hp₀ hp₀ hφ0
  rw [hf₁, hf₃] at hEq
  unfold localLin
  linear_combination -hEq

end FreimanCore

/-! ## Part 2: Simultaneous Freiman 2-Homomorphism Rigidity for Quadratic Units -/

section QuadraticUnitRigidity

/-- **Simultaneous Freiman 2-Homomorphism Rigidity (Arbitrary Field `F`):**
If `u₀ ∈ G` satisfies `u₀^2 - c * u₀ + s = 0` (`s ∈ {-1, 1}`), the quadratic
`x^2 - c * x + s` has no root in `F`, `1, u₀, u₀^2 ∈ G`, and `P` contains the
local additive stencil around `p₀` (`u₀ * p₀ ≠ p₀`, `1 ≠ 0`), then NO injective
simultaneous additive-and-multiplicative Freiman 2-homomorphism `φ : R → F`
exists on `G · P`. -/
theorem no_simultaneous_freiman2_hom_of_quadratic_unit_field
    {R F : Type*} [CommRing R] [Field F]
    {G P : Set R} {p₀ u₀ : R} {c s : ℤ}
    (hs : s = 1 ∨ s = -1)
    (hquad : u₀ ^ 2 - (c : R) * u₀ + (s : R) = 0)
    (hno_root : ∀ x : F, x ^ 2 - (c : F) * x + (s : F) ≠ 0)
    (h10 : (1 : R) ≠ 0)
    (hup : u₀ * p₀ ≠ p₀)
    (h1G : (1 : R) ∈ G)
    (huG : u₀ ∈ G)
    (hu2G : u₀ ^ 2 ∈ G)
    (hp₀ : p₀ ∈ P)
    (hp1 : p₀ + 1 ∈ P)
    (hpu : p₀ + u₀ ∈ P)
    (hpu2 : p₀ + u₀ ^ 2 ∈ P)
    (hp_step : ∀ k : ℤ, (0 ≤ k ∧ k ≤ c ∨ c ≤ k ∧ k ≤ 0) → p₀ + (k : R) * u₀ ∈ P)
    (φ : R → F)
    (hInj : Set.InjOn φ (productSet G P))
    (hAdd : IsAddFreiman2Hom (productSet G P) φ)
    (hMul : IsMulFreiman2Hom (productSet G P) φ) :
    False := by
  have hφ0 : φ p₀ ≠ 0 := phi_base_ne_zero hInj hMul h1G huG hp₀ hp1 hup h10
  have hL1 : localLin φ p₀ 1 ≠ 0 := localLin_one_ne_zero hInj h1G hp₀ hp1 h10
  set lam : F := scale φ p₀ u₀ with hlam_def
  have hLu : localLin φ p₀ u₀ = lam * localLin φ p₀ 1 := by
    have h := localLin_mul_unit hAdd hMul h1G huG hp₀ hp1 (by simpa using hpu) hφ0
    simpa [hlam_def] using h
  have hscale2 : scale φ p₀ (u₀ ^ 2) = lam ^ 2 := by
    have h := scale_mul hMul h1G huG huG (by simpa [sq] using hu2G) hp₀ hφ0
    simpa [sq, hlam_def] using h
  have hLu2 : localLin φ p₀ (u₀ ^ 2) = lam ^ 2 * localLin φ p₀ 1 := by
    have h := localLin_mul_unit hAdd hMul h1G hu2G hp₀ hp1 (by simpa using hpu2) hφ0
    simpa [hscale2] using h
  have hLcu : localLin φ p₀ ((c : R) * u₀) = (c : F) * lam * localLin φ p₀ 1 := by
    rw [localLin_intMul hAdd h1G hpu c hp_step, hLu]
    ring
  have hpc : p₀ + (c : R) * u₀ ∈ P := hp_step c (by omega)
  rcases hs with rfl | rfl
  · -- Norm `s = +1`: `u₀^2 + 1 = c * u₀`
    have hrel : u₀ ^ 2 + 1 = (c : R) * u₀ := by
      push_cast at hquad
      linear_combination hquad
    have hsumP : p₀ + (u₀ ^ 2 + 1) ∈ P := by rwa [hrel]
    have hadd := localLin_add hAdd h1G hp₀ hpu2 hp1 hsumP
    rw [hrel, hLcu, hLu2] at hadd
    have hfactor : (lam ^ 2 - (c : F) * lam + ((1 : ℤ) : F)) * localLin φ p₀ 1 = 0 := by
      push_cast
      linear_combination -hadd
    have hroot : lam ^ 2 - (c : F) * lam + ((1 : ℤ) : F) = 0 :=
      (mul_eq_zero.mp hfactor).resolve_right hL1
    exact hno_root lam hroot
  · -- Norm `s = -1`: `c * u₀ + 1 = u₀^2`
    have hrel : (c : R) * u₀ + 1 = u₀ ^ 2 := by
      push_cast at hquad
      linear_combination -hquad
    have hsumP : p₀ + ((c : R) * u₀ + 1) ∈ P := by rwa [hrel]
    have hadd := localLin_add hAdd h1G hp₀ hpc hp1 hsumP
    rw [hrel, hLu2, hLcu] at hadd
    have hfactor : (lam ^ 2 - (c : F) * lam + ((-1 : ℤ) : F)) * localLin φ p₀ 1 = 0 := by
      push_cast
      linear_combination hadd
    have hroot : lam ^ 2 - (c : F) * lam + ((-1 : ℤ) : F) = 0 :=
      (mul_eq_zero.mp hfactor).resolve_right hL1
    exact hno_root lam hroot

/-- **Simultaneous Freiman 2-Homomorphism Rigidity over `ℚ` (Polynomial Form):**
Exact `ℚ[X]` formulation of Obstruction 2 for a quadratic unit `u₀` satisfying
`u₀^2 - c * u₀ + s = 0` (`s ∈ {-1, 1}`) with `X^2 - c X + s ∈ ℚ[X]` root-free. -/
theorem no_simultaneous_freiman2_hom_of_quadratic_unit
    {R : Type*} [CommRing R]
    {G P : Set R} {p₀ u₀ : R} {c s : ℤ}
    (hs : s = 1 ∨ s = -1)
    (hquad : u₀ ^ 2 - (c : R) * u₀ + (s : R) = 0)
    (hno_root : ∀ x : ℚ,
      Polynomial.eval x (X ^ 2 - C (c : ℚ) * X + C (s : ℚ)) ≠ 0)
    (h10 : (1 : R) ≠ 0)
    (hup : u₀ * p₀ ≠ p₀)
    (h1G : (1 : R) ∈ G)
    (huG : u₀ ∈ G)
    (hu2G : u₀ ^ 2 ∈ G)
    (hp₀ : p₀ ∈ P)
    (hp1 : p₀ + 1 ∈ P)
    (hpu : p₀ + u₀ ∈ P)
    (hpu2 : p₀ + u₀ ^ 2 ∈ P)
    (hp_step : ∀ k : ℤ, (0 ≤ k ∧ k ≤ c ∨ c ≤ k ∧ k ≤ 0) → p₀ + (k : R) * u₀ ∈ P) :
    ¬ ∃ φ : R → ℚ,
      Set.InjOn φ (productSet G P) ∧
      IsAddFreiman2Hom (productSet G P) φ ∧
      IsMulFreiman2Hom (productSet G P) φ := by
  rintro ⟨φ, hInj, hAdd, hMul⟩
  have hno_root' : ∀ x : ℚ, x ^ 2 - (c : ℚ) * x + (s : ℚ) ≠ 0 := by
    intro x
    have h := hno_root x
    simpa [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] using h
  exact no_simultaneous_freiman2_hom_of_quadratic_unit_field
    hs hquad hno_root' h10 hup h1G huG hu2G hp₀ hp1 hpu hpu2 hp_step φ hInj hAdd hMul

end QuadraticUnitRigidity

/-! ## Part 3: General Degree-`m` Box-Norm Rigidity (Full `[BSSZ26]` Obstruction 2) -/

section GeneralDegreeBoxRigidity

lemma seminorm_natMul_le {R : Type*} [CommRing R] (N : R → ℝ)
    (hN0 : N 0 = 0) (hNadd : ∀ x y : R, N (x + y) ≤ N x + N y) :
    ∀ (n : ℕ) (x : R), N ((n : R) * x) ≤ (n : ℝ) * N x
  | 0, x => by simp [hN0]
  | n + 1, x => by
      have heq : ((n + 1 : ℕ) : R) * x = (n : R) * x + x := by push_cast; ring
      rw [heq]
      have h1 := hNadd ((n : R) * x) x
      have h2 := seminorm_natMul_le N hN0 hNadd n x
      push_cast
      linarith

lemma seminorm_intMul_le {R : Type*} [CommRing R] (N : R → ℝ)
    (hN0 : N 0 = 0) (hNneg : ∀ x : R, N (-x) = N x)
    (hNadd : ∀ x y : R, N (x + y) ≤ N x + N y) (k : ℤ) (x : R) :
    N ((k : R) * x) ≤ |(k : ℝ)| * N x := by
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have habs : |((n : ℤ) : ℝ)| = (n : ℝ) := by
      simp [abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    simpa [habs] using seminorm_natMul_le N hN0 hNadd n x
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -k by omega)
    have hkeq : k = -(n : ℤ) := by omega
    rw [hkeq]
    have hr : ((-(n : ℤ) : ℤ) : R) * x = -((n : R) * x) := by push_cast; ring
    have habs : |((-(n : ℤ) : ℤ) : ℝ)| = (n : ℝ) := by
      push_cast
      rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
    rw [hr, hNneg, habs]
    exact seminorm_natMul_le N hN0 hNadd n x

lemma seminorm_sum_range_le {R : Type*} [CommRing R] (N : R → ℝ)
    (hN0 : N 0 = 0) (hNadd : ∀ x y : R, N (x + y) ≤ N x + N y) (g : ℕ → R) :
    ∀ k : ℕ, N (∑ j ∈ Finset.range k, g j) ≤ ∑ j ∈ Finset.range k, N (g j)
  | 0 => by simp [hN0]
  | k + 1 => by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have h1 := hNadd (∑ j ∈ Finset.range k, g j) (g k)
      have h2 := seminorm_sum_range_le N hN0 hNadd g k
      linarith

/-- **General Degree-`m` Algebraic Obstruction on a Seminorm Box:**
Models `[BSSZ26]`'s additive box `P = p₀ + B^+(R_box)` (with `N(α) = max_i |σ_i(α)|`).
For any polynomial `f ∈ ℤ[X]` vanishing at `u₀ ∈ R` with no root in `F`, if
`1, u₀, ..., u₀^(natDegree f) ∈ G` and the additive box radius `R_box` bounds `N 1`,
`N (u₀^j)`, and `∑_{j=0}^{deg f} |coeff_j f| * N (u₀^j)`, then NO injective
simultaneous additive-and-multiplicative Freiman 2-homomorphism `φ : R → F` exists
on `G · P`. -/
theorem no_simultaneous_freiman2_hom_of_poly_box
    {R F : Type*} [CommRing R] [Field F]
    {G P : Set R} {p₀ u₀ : R}
    (f : Polynomial ℤ)
    (hdeg : 1 ≤ f.natDegree)
    (hf_root : f.eval₂ (Int.castRingHom R) u₀ = 0)
    (hf_no_root : ∀ x : F, f.eval₂ (Int.castRingHom F) x ≠ 0)
    (h10 : (1 : R) ≠ 0)
    (hup : u₀ * p₀ ≠ p₀)
    (N : R → ℝ) (R_box : ℝ)
    (hN0 : N 0 = 0)
    (hNnonneg : ∀ x : R, 0 ≤ N x)
    (hNneg : ∀ x : R, N (-x) = N x)
    (hNadd : ∀ x y : R, N (x + y) ≤ N x + N y)
    (hPbox : ∀ w : R, N w ≤ R_box → p₀ + w ∈ P)
    (hpowG : ∀ j : ℕ, j ≤ f.natDegree → u₀ ^ j ∈ G)
    (hpowBox : ∀ j : ℕ, j ≤ f.natDegree → N (u₀ ^ j) ≤ R_box)
    (hsumBox :
      ∑ j ∈ Finset.range (f.natDegree + 1), |(f.coeff j : ℝ)| * N (u₀ ^ j) ≤ R_box) :
    ¬ ∃ φ : R → F,
      Set.InjOn φ (productSet G P) ∧
      IsAddFreiman2Hom (productSet G P) φ ∧
      IsMulFreiman2Hom (productSet G P) φ := by
  rintro ⟨φ, hInj, hAdd, hMul⟩
  have h1G : (1 : R) ∈ G := by simpa using hpowG 0 (Nat.zero_le _)
  have huG : u₀ ∈ G := by simpa using hpowG 1 hdeg
  have hR_nonneg : 0 ≤ R_box := le_trans (hNnonneg 1) (by simpa using hpowBox 0 (Nat.zero_le _))
  have hp₀ : p₀ ∈ P := by simpa using hPbox 0 (by rw [hN0]; exact hR_nonneg)
  have hp1 : p₀ + 1 ∈ P := hPbox 1 (by simpa using hpowBox 0 (Nat.zero_le _))
  have hφ0 : φ p₀ ≠ 0 := phi_base_ne_zero hInj hMul h1G huG hp₀ hp1 hup h10
  have hL1 : localLin φ p₀ 1 ≠ 0 := localLin_one_ne_zero hInj h1G hp₀ hp1 h10
  set lam : F := scale φ p₀ u₀ with hlam_def
  have hterm_nonneg : ∀ j : ℕ, 0 ≤ |(f.coeff j : ℝ)| * N (u₀ ^ j) :=
    fun j => mul_nonneg (abs_nonneg _) (hNnonneg _)
  have hLpow : ∀ j : ℕ, j ≤ f.natDegree →
      localLin φ p₀ (u₀ ^ j) = lam ^ j * localLin φ p₀ 1 := by
    intro j hj
    have hpu : p₀ + u₀ ^ j ∈ P := hPbox (u₀ ^ j) (hpowBox j hj)
    have hscalej : scale φ p₀ (u₀ ^ j) = lam ^ j :=
      scale_pow hMul hp₀ hφ0 j (fun i hi => hpowG i (Nat.le_trans hi hj))
    have h := localLin_mul_unit hAdd hMul h1G (hpowG j hj) hp₀ hp1 (by simpa using hpu) hφ0
    simpa [hscalej] using h
  have hLterm : ∀ j : ℕ, j ≤ f.natDegree →
      localLin φ p₀ ((f.coeff j : R) * u₀ ^ j) = (f.coeff j : F) * lam ^ j * localLin φ p₀ 1 := by
    intro j hj
    have hpu : p₀ + u₀ ^ j ∈ P := hPbox (u₀ ^ j) (hpowBox j hj)
    have hterm_le : |(f.coeff j : ℝ)| * N (u₀ ^ j) ≤ R_box := by
      have hmem : j ∈ Finset.range (f.natDegree + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
      exact le_trans
        (Finset.single_le_sum (fun i _ => hterm_nonneg i) hmem)
        hsumBox
    have hstep : ∀ k : ℤ, (0 ≤ k ∧ k ≤ f.coeff j ∨ f.coeff j ≤ k ∧ k ≤ 0) →
        p₀ + (k : R) * u₀ ^ j ∈ P := by
      intro k hk
      apply hPbox
      have habs : |(k : ℝ)| ≤ |(f.coeff j : ℝ)| := by
        rcases hk with ⟨h0, hle⟩ | ⟨hle, h0⟩
        · have h0' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h0
          have hle' : (k : ℝ) ≤ (f.coeff j : ℝ) := by exact_mod_cast hle
          rw [abs_of_nonneg h0', abs_of_nonneg (le_trans h0' hle')]
          exact hle'
        · have h0' : (k : ℝ) ≤ 0 := by exact_mod_cast h0
          have hle' : (f.coeff j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hle
          rw [abs_of_nonpos h0', abs_of_nonpos (le_trans hle' h0')]
          linarith
      exact le_trans (seminorm_intMul_le N hN0 hNneg hNadd k (u₀ ^ j))
        (le_trans (mul_le_mul_of_nonneg_right habs (hNnonneg _)) hterm_le)
    rw [localLin_intMul hAdd h1G hpu (f.coeff j) hstep, hLpow j hj]
    ring
  have hpart_norm : ∀ k : ℕ, k ≤ f.natDegree + 1 →
      N (∑ j ∈ Finset.range k, (f.coeff j : R) * u₀ ^ j) ≤ R_box := by
    intro k hk
    calc N (∑ j ∈ Finset.range k, (f.coeff j : R) * u₀ ^ j)
        ≤ ∑ j ∈ Finset.range k, N ((f.coeff j : R) * u₀ ^ j) :=
          seminorm_sum_range_le N hN0 hNadd _ k
      _ ≤ ∑ j ∈ Finset.range k, |(f.coeff j : ℝ)| * N (u₀ ^ j) :=
          Finset.sum_le_sum (fun j _ => seminorm_intMul_le N hN0 hNneg hNadd _ _)
      _ ≤ ∑ j ∈ Finset.range (f.natDegree + 1), |(f.coeff j : ℝ)| * N (u₀ ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
            (fun i _ _ => hterm_nonneg i)
      _ ≤ R_box := hsumBox
  have hLsum : ∀ k : ℕ, k ≤ f.natDegree + 1 →
      localLin φ p₀ (∑ j ∈ Finset.range k, (f.coeff j : R) * u₀ ^ j) =
        (∑ j ∈ Finset.range k, (f.coeff j : F) * lam ^ j) * localLin φ p₀ 1 := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [localLin]
    | succ k ih =>
        intro hk
        have hk_le : k ≤ f.natDegree := Nat.le_of_succ_le_succ hk
        have hSk : p₀ + ∑ j ∈ Finset.range k, (f.coeff j : R) * u₀ ^ j ∈ P :=
          hPbox _ (hpart_norm k (Nat.le_trans (Nat.le_succ k) hk))
        have htermP : p₀ + (f.coeff k : R) * u₀ ^ k ∈ P := by
          apply hPbox
          have hmem : k ∈ Finset.range (f.natDegree + 1) :=
            Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le)
          exact le_trans (seminorm_intMul_le N hN0 hNneg hNadd _ _)
            (le_trans (Finset.single_le_sum (fun i _ => hterm_nonneg i) hmem) hsumBox)
        have hSk1 : p₀ + ((∑ j ∈ Finset.range k, (f.coeff j : R) * u₀ ^ j) +
            (f.coeff k : R) * u₀ ^ k) ∈ P := by
          rw [← Finset.sum_range_succ]
          exact hPbox _ (hpart_norm (k + 1) hk)
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        rw [localLin_add hAdd h1G hp₀ hSk htermP hSk1]
        rw [ih (Nat.le_trans (Nat.le_succ k) hk), hLterm k hk_le]
        ring
  have hfull := hLsum (f.natDegree + 1) (le_refl _)
  have hevalR : ∑ j ∈ Finset.range (f.natDegree + 1), (f.coeff j : R) * u₀ ^ j = 0 := by
    simpa [Polynomial.eval₂_eq_sum_range] using hf_root
  have hevalF : ∑ j ∈ Finset.range (f.natDegree + 1), (f.coeff j : F) * lam ^ j =
      f.eval₂ (Int.castRingHom F) lam := by
    simp [Polynomial.eval₂_eq_sum_range]
  rw [hevalR, localLin_zero, hevalF] at hfull
  have hroot : f.eval₂ (Int.castRingHom F) lam = 0 :=
    (mul_eq_zero.mp hfull.symm).resolve_right hL1
  exact hf_no_root lam hroot

end GeneralDegreeBoxRigidity

/-! ## Part 4: Concrete Instantiations on `ℤ[√2]`, `ℤ[√3]`, `ℤ[(1+√5)/2]` & No Ring Homomorphisms -/

section ConcreteQuadraticRings

/-- Elementary irrationality of `√p` for every prime `p`: no `q : ℚ` satisfies `q^2 = p`. -/
lemma rat_sq_ne_prime {p : ℕ} (hp : Nat.Prime p) (q : ℚ) : q ^ 2 ≠ (p : ℚ) := by
  intro hq
  have hden_ne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hnum_div : ((q.num : ℚ) / (q.den : ℚ)) ^ 2 = (p : ℚ) := by
    rwa [Rat.num_div_den]
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hden_ne)] at hnum_div
  have hint : q.num ^ 2 = (p : ℤ) * (q.den : ℤ) ^ 2 := by
    exact_mod_cast hnum_div
  have hnat : q.num.natAbs ^ 2 = p * q.den ^ 2 := by
    have h := congrArg Int.natAbs hint
    simpa [Int.natAbs_pow, Int.natAbs_mul] using h
  have hp_dvd_num2 : p ∣ q.num.natAbs ^ 2 := ⟨q.den ^ 2, hnat⟩
  have hp_dvd_num : p ∣ q.num.natAbs := hp.dvd_of_dvd_pow hp_dvd_num2
  rcases hp_dvd_num with ⟨k, hk⟩
  have hmul : p * (p * k ^ 2) = p * q.den ^ 2 := by
    calc p * (p * k ^ 2) = (p * k) ^ 2 := by ring
      _ = q.num.natAbs ^ 2 := by rw [← hk]
      _ = p * q.den ^ 2 := hnat
  have hden2 : q.den ^ 2 = p * k ^ 2 := (Nat.mul_left_cancel hp.pos hmul).symm
  have hp_dvd_den : p ∣ q.den := hp.dvd_of_dvd_pow ⟨k ^ 2, hden2⟩
  exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt ⟨k, hk⟩ hp_dvd_den q.reduced

lemma rat_sq_ne_two (q : ℚ) : q ^ 2 ≠ 2 := by
  simpa using rat_sq_ne_prime Nat.prime_two q

lemma rat_sq_ne_three (q : ℚ) : q ^ 2 ≠ 3 := by
  simpa using rat_sq_ne_prime Nat.prime_three q

lemma rat_sq_ne_five (q : ℚ) : q ^ 2 ≠ 5 := by
  simpa using rat_sq_ne_prime (by decide : Nat.Prime 5) q

/-- **Obstruction 1 (General Prime `ℤ[√p]`):**
There is no ring homomorphism `Zsqrtd p →+* ℚ` for any prime `p`. -/
theorem no_ringHom_zsqrtd_prime {p : ℕ} (hp : Nat.Prime p) :
    IsEmpty (Zsqrtd (p : ℤ) →+* ℚ) := by
  refine ⟨fun f => ?_⟩
  have hsq : (⟨0, 1⟩ : Zsqrtd (p : ℤ)) ^ 2 = ((p : ℤ) : Zsqrtd (p : ℤ)) := by
    ext <;> simp [sq]
  have hp_eq : (f ⟨0, 1⟩) ^ 2 = (p : ℚ) := by
    calc (f ⟨0, 1⟩) ^ 2 = f ((⟨0, 1⟩ : Zsqrtd (p : ℤ)) ^ 2) := (map_pow f _ 2).symm
      _ = f ((p : ℤ) : Zsqrtd (p : ℤ)) := by rw [hsq]
      _ = (p : ℚ) := by simp
  exact rat_sq_ne_prime hp (f ⟨0, 1⟩) hp_eq

/-- **Obstruction 1 (`ℤ[√2] →+* ℚ`):**
No ring homomorphism exists from `ℤ[√2]` (`Zsqrtd 2`) into `ℚ`. -/
theorem no_ringHom_zsqrtd_int_or_rat : IsEmpty (Zsqrtd 2 →+* ℚ) := by
  simpa using no_ringHom_zsqrtd_prime Nat.prime_two

/-- **Obstruction 1 (`ℤ[√2] →+* ℤ`):**
No ring homomorphism exists from `ℤ[√2]` (`Zsqrtd 2`) into `ℤ`. -/
theorem no_ringHom_zsqrtd_int : IsEmpty (Zsqrtd 2 →+* ℤ) :=
  ⟨fun f => no_ringHom_zsqrtd_int_or_rat.false ((Int.castRingHom ℚ).comp f)⟩

/-- Fundamental unit `u₂ = 1 + √2 ∈ ℤ[√2]` is indeed a unit of norm `-1`. -/
lemma isUnit_one_add_sqrt2 : IsUnit (⟨1, 1⟩ : Zsqrtd 2) :=
  ⟨⟨⟨1, 1⟩, ⟨-1, 1⟩, by ext <;> norm_num, by ext <;> norm_num⟩, rfl⟩

/-- `u₂ = 1 + √2` satisfies `u₂^2 - 2 * u₂ - 1 = 0` in `ℤ[√2]`. -/
lemma sqrt2_unit_quad :
    (⟨1, 1⟩ : Zsqrtd 2) ^ 2 - (2 : Zsqrtd 2) * ⟨1, 1⟩ + ((-1 : ℤ) : Zsqrtd 2) = 0 := by
  ext <;> simp [sq]

/-- `X^2 - 2 X - 1 ∈ ℚ[X]` has no rational root. -/
lemma sqrt2_unit_poly_no_rat_root (x : ℚ) :
    Polynomial.eval x (X ^ 2 - C (2 : ℚ) * X + C ((-1 : ℤ) : ℚ)) ≠ 0 := by
  intro hx
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Int.cast_neg,
    Int.cast_one] at hx
  have h2 : (x - 1) ^ 2 = 2 := by linear_combination hx
  exact rat_sq_ne_two (x - 1) h2

/-- **Concrete Instantiation (`ℤ[√2]` with `u₂ = 1 + √2`):**
No map `φ : Zsqrtd 2 → ℚ` can be simultaneously injective, an additive Freiman
2-homomorphism, and a multiplicative Freiman 2-homomorphism on `G · P`, whenever
`1, 1 + √2, (1 + √2)^2 ∈ G` and `P` contains the 5-element stencil
`{p₀, p₀ + 1, p₀ + u₂, p₀ + 2 u₂, p₀ + u₂^2}` around any nonzero `p₀ ∈ Zsqrtd 2`. -/
theorem no_simultaneous_freiman2_hom_quad_field
    {G P : Set (Zsqrtd 2)} {p₀ : Zsqrtd 2}
    (hp₀_ne : p₀ ≠ 0)
    (h1G : (1 : Zsqrtd 2) ∈ G)
    (huG : (⟨1, 1⟩ : Zsqrtd 2) ∈ G)
    (hu2G : ((⟨1, 1⟩ : Zsqrtd 2) ^ 2) ∈ G)
    (hp₀ : p₀ ∈ P)
    (hp1 : p₀ + 1 ∈ P)
    (hpu : p₀ + ⟨1, 1⟩ ∈ P)
    (hp2u : p₀ + 2 * ⟨1, 1⟩ ∈ P)
    (hpu2 : p₀ + (⟨1, 1⟩ : Zsqrtd 2) ^ 2 ∈ P) :
    ¬ ∃ φ : Zsqrtd 2 → ℚ,
      Set.InjOn φ (productSet G P) ∧
      IsAddFreiman2Hom (productSet G P) φ ∧
      IsMulFreiman2Hom (productSet G P) φ := by
  have h10 : (1 : Zsqrtd 2) ≠ 0 := by
    intro h
    have := congrArg Zsqrtd.re h
    norm_num at this
  have hup : (⟨1, 1⟩ : Zsqrtd 2) * p₀ ≠ p₀ := by
    intro h
    have hre := congrArg Zsqrtd.re h
    have him := congrArg Zsqrtd.im h
    simp at hre him
    apply hp₀_ne
    ext
    · change p₀.re = 0; omega
    · change p₀.im = 0; omega
  have hp_step : ∀ k : ℤ, (0 ≤ k ∧ k ≤ 2 ∨ 2 ≤ k ∧ k ≤ 0) →
      p₀ + (k : Zsqrtd 2) * ⟨1, 1⟩ ∈ P := by
    intro k hk
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk_cases with rfl | rfl | rfl
    · simpa using hp₀
    · simpa using hpu
    · simpa using hp2u
  exact no_simultaneous_freiman2_hom_of_quadratic_unit (c := 2) (s := -1)
    (Or.inr rfl)
    (by simpa using sqrt2_unit_quad)
    (by simpa using sqrt2_unit_poly_no_rat_root)
    h10 hup h1G huG hu2G hp₀ hp1 hpu hpu2 hp_step

/-- Standalone pure-Mathlib (0 custom definitions in the statement) restatement of
`no_simultaneous_freiman2_hom_quad_field` on `Zsqrtd 2` for rapid third-party audit. -/
theorem no_simultaneous_freiman2_hom_zsqrtd2_standalone
    (G P : Set (Zsqrtd 2)) (p₀ : Zsqrtd 2)
    (hp₀_ne : p₀ ≠ 0)
    (h1G : (1 : Zsqrtd 2) ∈ G)
    (huG : (⟨1, 1⟩ : Zsqrtd 2) ∈ G)
    (hu2G : ((⟨1, 1⟩ : Zsqrtd 2) ^ 2) ∈ G)
    (hp₀ : p₀ ∈ P)
    (hp1 : p₀ + 1 ∈ P)
    (hpu : p₀ + ⟨1, 1⟩ ∈ P)
    (hp2u : p₀ + 2 * ⟨1, 1⟩ ∈ P)
    (hpu2 : p₀ + (⟨1, 1⟩ : Zsqrtd 2) ^ 2 ∈ P) :
    ¬ ∃ φ : Zsqrtd 2 → ℚ,
      let A : Set (Zsqrtd 2) := {a | ∃ u ∈ G, ∃ p ∈ P, a = u * p}
      Set.InjOn φ A ∧
      (∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ a₃ ∈ A, ∀ a₄ ∈ A,
        a₁ + a₂ = a₃ + a₄ → φ a₁ + φ a₂ = φ a₃ + φ a₄) ∧
      (∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ a₃ ∈ A, ∀ a₄ ∈ A,
        a₁ * a₂ = a₃ * a₄ → φ a₁ * φ a₂ = φ a₃ * φ a₄) :=
  no_simultaneous_freiman2_hom_quad_field hp₀_ne h1G huG hu2G hp₀ hp1 hpu hp2u hpu2

/-- **Concrete Instantiation (`ℤ[√3]` with norm-`+1` unit `u₃ = 2 + √3`):**
Exercises the `s = +1` branch (`u₃^2 - 4 u₃ + 1 = 0`). -/
theorem no_simultaneous_freiman2_hom_zsqrtd3
    {G P : Set (Zsqrtd 3)} {p₀ : Zsqrtd 3}
    (hp₀_ne : p₀ ≠ 0)
    (h1G : (1 : Zsqrtd 3) ∈ G)
    (huG : (⟨2, 1⟩ : Zsqrtd 3) ∈ G)
    (hu2G : ((⟨2, 1⟩ : Zsqrtd 3) ^ 2) ∈ G)
    (hp₀ : p₀ ∈ P)
    (hp1 : p₀ + 1 ∈ P)
    (hpu : p₀ + ⟨2, 1⟩ ∈ P)
    (hp2u : p₀ + 2 * ⟨2, 1⟩ ∈ P)
    (hp3u : p₀ + 3 * ⟨2, 1⟩ ∈ P)
    (hp4u : p₀ + 4 * ⟨2, 1⟩ ∈ P)
    (hpu2 : p₀ + (⟨2, 1⟩ : Zsqrtd 3) ^ 2 ∈ P) :
    ¬ ∃ φ : Zsqrtd 3 → ℚ,
      Set.InjOn φ (productSet G P) ∧
      IsAddFreiman2Hom (productSet G P) φ ∧
      IsMulFreiman2Hom (productSet G P) φ := by
  have hquad : (⟨2, 1⟩ : Zsqrtd 3) ^ 2 - ((4 : ℤ) : Zsqrtd 3) * ⟨2, 1⟩ + ((1 : ℤ) : Zsqrtd 3) = 0 := by
    ext <;> simp [sq]
  have hno_root : ∀ x : ℚ,
      Polynomial.eval x (X ^ 2 - C ((4 : ℤ) : ℚ) * X + C ((1 : ℤ) : ℚ)) ≠ 0 := by
    intro x hx
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Int.cast_ofNat,
      Int.cast_one] at hx
    have h3 : (x - 2) ^ 2 = 3 := by linear_combination hx
    exact rat_sq_ne_three (x - 2) h3
  have h10 : (1 : Zsqrtd 3) ≠ 0 := by
    intro h
    have := congrArg Zsqrtd.re h
    norm_num at this
  have hup : (⟨2, 1⟩ : Zsqrtd 3) * p₀ ≠ p₀ := by
    intro h
    have hre := congrArg Zsqrtd.re h
    have him := congrArg Zsqrtd.im h
    simp at hre him
    apply hp₀_ne
    ext
    · change p₀.re = 0; omega
    · change p₀.im = 0; omega
  have hp_step : ∀ k : ℤ, (0 ≤ k ∧ k ≤ 4 ∨ 4 ≤ k ∧ k ≤ 0) →
      p₀ + (k : Zsqrtd 3) * ⟨2, 1⟩ ∈ P := by
    intro k hk
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk_cases with rfl | rfl | rfl | rfl | rfl
    · simpa using hp₀
    · simpa using hpu
    · simpa using hp2u
    · simpa using hp3u
    · simpa using hp4u
  exact no_simultaneous_freiman2_hom_of_quadratic_unit (c := 4) (s := 1)
    (Or.inl rfl) hquad hno_root h10 hup h1G huG hu2G hp₀ hp1 hpu hpu2 hp_step

/-- **Minimal 4-Point Stencil Instantiation (`ℤ[(1 + √5)/2]` via `QuadraticAlgebra ℤ 1 1`):**
For the golden unit `ω = ⟨0, 1⟩` satisfying `ω^2 - ω - 1 = 0`, the exact 4-element
stencil `{p₀, p₀ + 1, p₀ + ω, p₀ + ω^2}` already suffices with no intermediate multiples. -/
theorem no_simultaneous_freiman2_hom_golden_ring
    {G P : Set (QuadraticAlgebra ℤ 1 1)} {p₀ : QuadraticAlgebra ℤ 1 1}
    (hp₀_ne : p₀ ≠ 0)
    (h1G : (1 : QuadraticAlgebra ℤ 1 1) ∈ G)
    (huG : (⟨0, 1⟩ : QuadraticAlgebra ℤ 1 1) ∈ G)
    (hu2G : ((⟨0, 1⟩ : QuadraticAlgebra ℤ 1 1) ^ 2) ∈ G)
    (hp₀ : p₀ ∈ P)
    (hp1 : p₀ + 1 ∈ P)
    (hpu : p₀ + ⟨0, 1⟩ ∈ P)
    (hpu2 : p₀ + (⟨0, 1⟩ : QuadraticAlgebra ℤ 1 1) ^ 2 ∈ P) :
    ¬ ∃ φ : QuadraticAlgebra ℤ 1 1 → ℚ,
      Set.InjOn φ (productSet G P) ∧
      IsAddFreiman2Hom (productSet G P) φ ∧
      IsMulFreiman2Hom (productSet G P) φ := by
  have hquad : (⟨0, 1⟩ : QuadraticAlgebra ℤ 1 1) ^ 2 -
      ((1 : ℤ) : QuadraticAlgebra ℤ 1 1) * ⟨0, 1⟩ +
      ((-1 : ℤ) : QuadraticAlgebra ℤ 1 1) = 0 := by
    ext <;> simp [sq, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hno_root : ∀ x : ℚ,
      Polynomial.eval x (X ^ 2 - C ((1 : ℤ) : ℚ) * X + C ((-1 : ℤ) : ℚ)) ≠ 0 := by
    intro x hx
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Int.cast_neg,
      Int.cast_one] at hx
    have h5 : (2 * x - 1) ^ 2 = 5 := by linear_combination 4 * hx
    exact rat_sq_ne_five (2 * x - 1) h5
  have h10 : (1 : QuadraticAlgebra ℤ 1 1) ≠ 0 := by
    intro h
    have := congrArg QuadraticAlgebra.re h
    simp [QuadraticAlgebra.re_one] at this
  have hup : (⟨0, 1⟩ : QuadraticAlgebra ℤ 1 1) * p₀ ≠ p₀ := by
    intro h
    have hre := congrArg QuadraticAlgebra.re h
    have him := congrArg QuadraticAlgebra.im h
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] at hre him
    apply hp₀_ne
    ext
    · change p₀.re = 0; omega
    · change p₀.im = 0; omega
  have hp_step : ∀ k : ℤ, (0 ≤ k ∧ k ≤ 1 ∨ 1 ≤ k ∧ k ≤ 0) →
      p₀ + (k : QuadraticAlgebra ℤ 1 1) * ⟨0, 1⟩ ∈ P := by
    intro k hk
    have hk_cases : k = 0 ∨ k = 1 := by omega
    rcases hk_cases with rfl | rfl
    · simpa using hp₀
    · simpa using hpu
  exact no_simultaneous_freiman2_hom_of_quadratic_unit (c := 1) (s := -1)
    (Or.inr rfl) hquad hno_root h10 hup h1G huG hu2G hp₀ hp1 hpu hpu2 hp_step

end ConcreteQuadraticRings

/-! ## Part 5: Small-Box Mod-`M` Unit-Collapse Divisor Bound (Obstruction 4) -/

section SmallBoxUnitCollapse

/-- If `a * b ≡ T [ZMOD M]` and both `|a * b| < M / 2` and `|T| < M / 2`
(written integrally as `2 * (a.natAbs * b.natAbs) < M` and `2 * T.natAbs < M`),
then `a * b = T` holds **exactly** in `ℤ`. -/
theorem small_box_mod_eq_exact {M : ℕ} {a b T : ℤ}
    (hmod : a * b ≡ T [ZMOD (M : ℤ)])
    (hab : 2 * (a.natAbs * b.natAbs) < M)
    (hT : 2 * T.natAbs < M) :
    a * b = T := by
  have hdvdZ : (M : ℤ) ∣ T - a * b := Int.modEq_iff_dvd.mp hmod
  have hdvdN : M ∣ (T - a * b).natAbs := by
    rcases hdvdZ with ⟨k, hk⟩
    refine ⟨k.natAbs, ?_⟩
    have h := congrArg Int.natAbs hk
    simpa [Int.natAbs_mul] using h
  have hlt : (T - a * b).natAbs < M := by
    have htri : (T - a * b).natAbs ≤ T.natAbs + (a * b).natAbs := by omega
    rw [Int.natAbs_mul] at htri
    omega
  have hzero : (T - a * b).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdvdN hlt
  have hsub : T - a * b = 0 := Int.natAbs_eq_zero.mp hzero
  omega

/-- **Small-Box Unit-Collapse Divisor Bound:**
If `hat : α → ℤ` is injective on a finite set `G` and every `u ∈ G` satisfies
`hat u * hat (inv u) = T` in `ℤ` for a fixed nonzero `T : ℤ`, then every `hat u`
divides `T`, forcing `G.card ≤ 2 * T.natAbs.divisors.card`. -/
theorem small_box_unit_collapse_card_le {α : Type*}
    (G : Finset α) (hat : α → ℤ) (inv : α → α) (T : ℤ)
    (hT : T ≠ 0)
    (hInj : Set.InjOn hat (G : Set α))
    (hprod : ∀ u ∈ G, hat u * hat (inv u) = T) :
    G.card ≤ 2 * T.natAbs.divisors.card := by
  have hTnat : T.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hT
  have hmem_div : ∀ u ∈ G, (hat u).natAbs ∈ T.natAbs.divisors := by
    intro u hu
    refine Nat.mem_divisors.mpr ⟨⟨(hat (inv u)).natAbs, ?_⟩, hTnat⟩
    have h := congrArg Int.natAbs (hprod u hu)
    simpa [Int.natAbs_mul] using h.symm
  let Gpos := G.filter (fun u => 0 ≤ hat u)
  let Gneg := G.filter (fun u => ¬ (0 ≤ hat u))
  have hpos_le : Gpos.card ≤ T.natAbs.divisors.card := by
    refine Finset.card_le_card_of_injOn (fun u => (hat u).natAbs) ?_ ?_
    · intro u hu
      exact hmem_div u (Finset.mem_filter.mp hu).1
    · intro u₁ hu₁ u₂ hu₂ heq
      dsimp only at heq
      have h1 := Finset.mem_filter.mp hu₁
      have h2 := Finset.mem_filter.mp hu₂
      have hhat : hat u₁ = hat u₂ := by omega
      exact hInj h1.1 h2.1 hhat
  have hneg_le : Gneg.card ≤ T.natAbs.divisors.card := by
    refine Finset.card_le_card_of_injOn (fun u => (hat u).natAbs) ?_ ?_
    · intro u hu
      exact hmem_div u (Finset.mem_filter.mp hu).1
    · intro u₁ hu₁ u₂ hu₂ heq
      dsimp only at heq
      have h1 := Finset.mem_filter.mp hu₁
      have h2 := Finset.mem_filter.mp hu₂
      have hhat : hat u₁ = hat u₂ := by omega
      exact hInj h1.1 h2.1 hhat
  have hsplit : Gpos.card + Gneg.card = G.card :=
    Finset.card_filter_add_card_filter_not (s := G) (fun u => 0 ≤ hat u)
  omega

/-- **Full Small-Box Mod-`M` Unit-Collapse Obstruction (Obstruction 4):**
For any ring homomorphism `π : R →+* ZMod M` (prime `M = p`, prime-power `M = p^k`,
or CRT product `M = p₁⋯pₖ`), any dilation `t : ZMod M`, and any small-box integer
lift `hat : R → ℤ` injective on a symmetric unit subset `G ⊆ R^\times` with
`hat u ≡ t * π u (mod M)` and `2 * |hat u| * |hat (u⁻¹)| < M`, the unit set
collapses to `|G| ≤ 2 * d(|T|)` where `T ≡ t^2 (mod M)` (`2 * |T| < M`, `T ≠ 0`). -/
theorem small_box_mod_unit_collapse_bound
    {R : Type*} [CommRing R] {M : ℕ}
    (π : R →+* ZMod M) (t : ZMod M)
    (G : Finset R) (inv : R → R) (hat : R → ℤ) (T : ℤ)
    (hT : T ≠ 0)
    (hT_box : 2 * T.natAbs < M)
    (hT_mod : (T : ZMod M) = t ^ 2)
    (hInj : Set.InjOn hat (G : Set R))
    (hunit : ∀ u ∈ G, u * inv u = 1)
    (hlift_u : ∀ u ∈ G, (hat u : ZMod M) = t * π u)
    (hlift_inv : ∀ u ∈ G, (hat (inv u) : ZMod M) = t * π (inv u))
    (hsmall : ∀ u ∈ G, 2 * ((hat u).natAbs * (hat (inv u)).natAbs) < M) :
    G.card ≤ 2 * T.natAbs.divisors.card := by
  refine small_box_unit_collapse_card_le G hat inv T hT hInj (fun u hu => ?_)
  have hzmod : ((hat u * hat (inv u) : ℤ) : ZMod M) = (T : ZMod M) := by
    rw [Int.cast_mul, hlift_u u hu, hlift_inv u hu, hT_mod]
    calc (t * π u) * (t * π (inv u))
        = t ^ 2 * (π u * π (inv u)) := by ring
      _ = t ^ 2 * π (u * inv u) := by rw [← map_mul]
      _ = t ^ 2 * π 1 := by rw [hunit u hu]
      _ = t ^ 2 := by rw [map_one, mul_one]
  have hmod : hat u * hat (inv u) ≡ T [ZMOD (M : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff (hat u * hat (inv u)) T M).mp hzmod
  exact small_box_mod_eq_exact hmod (hsmall u hu) hT_box

end SmallBoxUnitCollapse

end PPL139_FreimanRigidity
