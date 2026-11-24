import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.AddChar

/-!
# RHDirect.Stage6AdelicPoisson

Concrete, self-contained, completely unconditional (`0` assumptions, `0` `sorry`, `0` custom
`axiom`s) Lean 4 formalization of:

1. **Concrete Local $p$-adic Additive Character `ψ_p : ℚ_[p] → ℂ` (Tate's Standard Character)**:
   - Concrete $p$-adic fractional part `padicFracPart p : ℚ_[p] → ℚ` extracting the unique
     `p`-power denominator rational `a / p^k ∈ [0, 1)` such that `x - a / p^k ∈ ℤ_[p]`,
     via `PadicInt.appr`.
   - Standard additive character `padicAddChar p x := Complex.exp (2 * π * I * (padicFracPart p x : ℂ))`
     and exact additive homomorphism `padicAddCharHom p : AddChar ℚ_[p] ℂ` /
     `padicAddCharUnitHom p : Multiplicative ℚ_[p] →* ℂˣ`.
   - Unconditional proofs of:
     * `padicAddChar_add`: `ψ_p(x + y) = ψ_p(x) * ψ_p(y)`,
     * `padicAddChar_of_mem_padicInt`: `x ∈ ℤ_[p] → ψ_p(x) = 1`,
     * `padicAddChar_inv_prime_ne_one`: `ψ_p(p⁻¹) = exp(2πi / p) ≠ 1` and exact conductor
       characterization `mem_padicInt_iff_forall_padicAddChar_mul_eq_one`,
     * `norm_padicAddChar`: `‖ψ_p(x)‖ = 1` and `star_padicAddChar`: `star (ψ_p x) = ψ_p (-x)`.

2. **Unconditional Global Adelic Character Product Formula on `ℚ` (`ψ_∞(q) * ∏'_p ψ_p(q) = 1`)**:
   - Archimedean additive character `archAddChar x := Complex.exp (-2 * π * I * x)`.
   - Exact partial-fraction decomposition of every rational number `q : ℚ`:
     `q - ∑'_{p} {q}_p ∈ ℤ` (`rat_sub_finsum_padicFracPart_mem_int`,
     `rat_sub_sum_primeFactors_padicFracPart_mem_int`).
   - Finite multiplicative support `hasFiniteMulSupport_padicAddChar_rat` and unconditional
     global product formula:
     `adelicAddChar_rat_eq_one : ∀ q : ℚ, archAddChar (q : ℝ) * ∏ᶠ p : Nat.Primes, padicAddChar p.1 (q : ℚ_[p.1]) = 1`.
   - Concrete rational adele ring `RatAdele = ℝ × Πʳ p : Nat.Primes, [ℚ_[p.1], PadicInt.subring p.1]`,
     diagonal embedding `diagRatAdele : ℚ →+* RatAdele`, and global additive character
     `adelicAddChar : RatAdele → ℂ` trivial on `ℚ`.

3. **Concrete $p$-adic Haar Integral, Local Fourier Transform, Self-Duality of `1_{ℤ_p}` &
   Fourier Inversion**:
   - Ball/coset indicators `ballInd p a k : ℚ_[p] → ℂ` (`1_{a + p^k ℤ_p}`) and the Schwartz–Bruhat
     predicate `IsPadicSchwartzBruhat p f` (compactly supported and locally constant).
   - Well-defined normalized $p$-adic Haar integral `padicHaarInt p f` (`μ(a + p^k ℤ_p) = p^{-k}`,
     `μ(ℤ_p) = 1`), proved independent of support/constancy cutoffs, linear, translation-invariant,
     and reflection-invariant.
   - Local $p$-adic Fourier transform `padicFourier p f y := padicHaarInt p (fun x ↦ f x * ψ_p(x * y))`:
     * `padicFourier_ballInd`: `ℱ_p(1_{a + p^k ℤ_p})(y) = p^{-k} * ψ_p(a * y) * 1_{p^{-k} ℤ_p}(y)`,
     * `padicFourier_padicIntInd_selfDual`: `ℱ_p(1_{ℤ_p}) = 1_{ℤ_p}` (exact self-duality!),
     * `padicFourier_inversion`: `ℱ_p(ℱ_p f)(x) = f(-x)` for every Schwartz–Bruhat `f`.

4. **Concrete Adelic Poisson Summation on `𝔸_ℚ` (`∑'_{q : ℚ} Φ(q) = ∑'_{q : ℚ} Φ̂(q)`)**:
   - Strong approximation / rational center construction (`exists_rat_center_adelicBox`) for
     every finite-level adelic congruence box `B : AdelicBox` (`∏_p (a_p + p^{k_p} ℤ_p)` with
     arbitrary `k_p ∈ ℤ`, `a_p ∈ ℚ_[p]`, trivial outside a finite set of primes `S`).
   - Global factorizable Schwartz–Bruhat Gaussian test function `adelicGaussianTest t B : RatAdele → ℂ`
     and its global adelic Fourier transform `adelicGaussianFourier t B : RatAdele → ℂ`.
   - Unconditional **Concrete Adelic Poisson Summation Formula**:
     `adelic_poisson_summation_rat_gaussian : ∑' q : ℚ, Φ(q) = ∑' q : ℚ, Φ̂(q)` for all `t > 0`
     and every `B : AdelicBox`, specializing at `B = AdelicBox.spherical` (`k_p = 0, a_p = 0`) to
     Tate's exact theta identity `∑_{n ∈ ℤ} exp(-π t n²) = t^{-1/2} ∑_{n ∈ ℤ} exp(-π n² / t)`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex Real Filter MeasureTheory
open scoped BigOperators FourierTransform Topology Real RestrictedProduct

namespace RHDirect.Stage6AdelicPoisson

local instance instFactPrimePrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-! ## Section 1: Concrete $p$-adic Fractional Part & Tate's Standard Additive Character `ψ_p` -/

section LocalPadicCharacter

variable (p : ℕ) [hp : Fact p.Prime]

private lemma padic_p_pos : (0 : ℝ) < (p : ℝ) := by
  exact_mod_cast hp.out.pos

private lemma padic_one_lt_p : (1 : ℝ) < (p : ℝ) := by
  exact_mod_cast hp.out.one_lt

private lemma padic_p_ne_zero : (p : ℚ_[p]) ≠ 0 := by
  exact_mod_cast hp.out.ne_zero

private lemma padic_p_rat_ne_zero : (p : ℚ) ≠ 0 := by
  exact_mod_cast hp.out.ne_zero

private lemma padic_p_complex_ne_zero : (p : ℂ) ≠ 0 := by
  exact_mod_cast hp.out.ne_zero

/-- For every `x : ℚ_[p]`, multiplying by `p^{(-x.valuation).toNat}` lands inside `ℤ_[p]`. -/
lemma norm_p_pow_mul_le_one (x : ℚ_[p]) :
    ‖(p : ℚ_[p]) ^ (-x.valuation).toNat * x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hx,
      ← zpow_add₀ (padic_p_pos p).ne']
    have hle : -((-x.valuation).toNat : ℤ) + -x.valuation ≤ 0 := by
      have h := Int.self_le_toNat (-x.valuation)
      omega
    exact zpow_le_one_of_nonpos₀ (padic_one_lt_p p).le hle

/-- The integer `p`-adic scaling of `x : ℚ_[p]` into `ℤ_[p]`:
`p^{(-x.valuation).toNat} * x ∈ ℤ_[p]`. -/
def padicScaleToInt (x : ℚ_[p]) : ℤ_[p] :=
  ⟨(p : ℚ_[p]) ^ (-x.valuation).toNat * x, norm_p_pow_mul_le_one p x⟩

/-- **Concrete $p$-adic fractional part `{x}_p ∈ ℚ ∩ [0, 1)`**:
for `k = (-x.valuation).toNat` and `z = p^k x ∈ ℤ_[p]`,
`padicFracPart p x = (z.appr k : ℚ) / p^k`. -/
def padicFracPart (x : ℚ_[p]) : ℚ :=
  let k := (-x.valuation).toNat
  ((padicScaleToInt p x).appr k : ℚ) / (p : ℚ) ^ k

lemma padicFracPart_nonneg (x : ℚ_[p]) : 0 ≤ padicFracPart p x := by
  unfold padicFracPart
  positivity

lemma padicFracPart_lt_one (x : ℚ_[p]) : padicFracPart p x < 1 := by
  unfold padicFracPart
  set k := (-x.valuation).toNat
  have hpos : (0 : ℚ) < (p : ℚ) ^ k := pow_pos (by exact_mod_cast hp.out.pos) k
  rw [div_lt_one hpos]
  exact_mod_cast PadicInt.appr_lt (padicScaleToInt p x) k

lemma padicFracPart_eq_div_pow (x : ℚ_[p]) :
    ∃ (k a : ℕ), a < p ^ k ∧ padicFracPart p x = (a : ℚ) / (p : ℚ) ^ k :=
  ⟨(-x.valuation).toNat, (padicScaleToInt p x).appr (-x.valuation).toNat,
    PadicInt.appr_lt _ _, rfl⟩

/-- Core approximation property: `x - {x}_p ∈ ℤ_[p]`, i.e., `‖x - (padicFracPart p x : ℚ_[p])‖ ≤ 1`. -/
theorem norm_sub_padicFracPart_le_one (x : ℚ_[p]) :
    ‖x - (padicFracPart p x : ℚ_[p])‖ ≤ 1 := by
  set k := (-x.valuation).toNat
  set z : ℤ_[p] := padicScaleToInt p x
  have hspec : z - (z.appr k : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ k} :=
    PadicInt.appr_spec k z
  rw [Ideal.mem_span_singleton] at hspec
  obtain ⟨u, hu⟩ := hspec
  have hcoe : (z : ℚ_[p]) - (z.appr k : ℚ_[p]) = (p : ℚ_[p]) ^ k * (u : ℚ_[p]) := by
    have h1 := congrArg (fun t : ℤ_[p] ↦ (t : ℚ_[p])) hu
    simpa [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast] using h1
  have hpk : (p : ℚ_[p]) ^ k ≠ 0 := pow_ne_zero k (padic_p_ne_zero p)
  have hdiff : x - (padicFracPart p x : ℚ_[p]) = (u : ℚ_[p]) := by
    unfold padicFracPart
    have hcast : (((z.appr k : ℚ) / (p : ℚ) ^ k : ℚ) : ℚ_[p]) =
        (z.appr k : ℚ_[p]) / (p : ℚ_[p]) ^ k := by
      push_cast; rfl
    rw [hcast]
    have hz_val : (z : ℚ_[p]) = (p : ℚ_[p]) ^ k * x := rfl
    rw [hz_val] at hcoe
    apply mul_left_cancel₀ hpk
    calc (p : ℚ_[p]) ^ k * (x - (z.appr k : ℚ_[p]) / (p : ℚ_[p]) ^ k)
        = (p : ℚ_[p]) ^ k * x - (p : ℚ_[p]) ^ k * ((z.appr k : ℚ_[p]) / (p : ℚ_[p]) ^ k) := by
            ring
      _ = (p : ℚ_[p]) ^ k * x - (z.appr k : ℚ_[p]) := by
            rw [mul_div_cancel₀ _ hpk]
      _ = (p : ℚ_[p]) ^ k * (u : ℚ_[p]) := hcoe
  rw [hdiff]
  exact u.2

theorem sub_padicFracPart_mem_padicInt (x : ℚ_[p]) :
    x - (padicFracPart p x : ℚ_[p]) ∈ PadicInt.subring p :=
  norm_sub_padicFracPart_le_one p x

/-- Any rational number of the form `m / p^k` (`m : ℤ`, `k : ℕ`) with `p`-adic norm `≤ 1`
is actually an integer. -/
lemma exists_int_of_eq_div_pow_of_norm_le_one {r : ℚ} {k : ℕ} {m : ℤ}
    (hr : r = (m : ℚ) / (p : ℚ) ^ k) (hnorm : ‖(r : ℚ_[p])‖ ≤ 1) :
    ∃ z : ℤ, r = (z : ℚ) := by
  have hpk_pos : (0 : ℝ) < (p : ℝ) ^ (-(k : ℤ)) := zpow_pos (padic_p_pos p) _
  have hm_norm : ‖(m : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
    have hrcast : (r : ℚ_[p]) = (m : ℚ_[p]) / (p : ℚ_[p]) ^ k := by
      rw [hr]; push_cast; rfl
    rw [hrcast, norm_div, Padic.norm_p_pow] at hnorm
    rwa [div_le_one hpk_pos] at hnorm
  have hdvd : ((p ^ k : ℤ)) ∣ m := (Padic.norm_int_le_pow_iff_dvd m k).mp hm_norm
  obtain ⟨z, hz⟩ := hdvd
  refine ⟨z, ?_⟩
  rw [hr, hz]
  have hpk : (p : ℚ) ^ k ≠ 0 := pow_ne_zero k (padic_p_rat_ne_zero p)
  push_cast
  rw [mul_div_cancel_left₀ _ hpk]

/-- **Uniqueness of the $p$-adic fractional part**:
if `r = m / p^k ∈ [0, 1)` satisfies `‖x - r‖ ≤ 1`, then `r = padicFracPart p x`. -/
theorem padicFracPart_unique {x : ℚ_[p]} {r : ℚ} {k : ℕ} {m : ℤ}
    (hr_eq : r = (m : ℚ) / (p : ℚ) ^ k)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (happrox : ‖x - (r : ℚ_[p])‖ ≤ 1) :
    r = padicFracPart p x := by
  obtain ⟨k', a', _, hfp⟩ := padicFracPart_eq_div_pow p x
  have hsub_norm : ‖((r - padicFracPart p x : ℚ) : ℚ_[p])‖ ≤ 1 := by
    have heq : ((r - padicFracPart p x : ℚ) : ℚ_[p]) =
        (x - (padicFracPart p x : ℚ_[p])) + -(x - (r : ℚ_[p])) := by
      push_cast; ring
    rw [heq]
    refine (Padic.nonarchimedean _ _).trans (max_le (norm_sub_padicFracPart_le_one p x) ?_)
    rw [norm_neg]
    exact happrox
  have hsub_eq : r - padicFracPart p x =
      (((m * (p : ℤ) ^ k' - (a' : ℤ) * (p : ℤ) ^ k : ℤ) : ℚ)) / (p : ℚ) ^ (k + k') := by
    rw [hr_eq, hfp, pow_add]
    have hp1 : (p : ℚ) ^ k ≠ 0 := pow_ne_zero k (padic_p_rat_ne_zero p)
    have hp2 : (p : ℚ) ^ k' ≠ 0 := pow_ne_zero k' (padic_p_rat_ne_zero p)
    push_cast
    field_simp [hp1, hp2]
  obtain ⟨z, hz⟩ := exists_int_of_eq_div_pow_of_norm_le_one p hsub_eq hsub_norm
  have hlt1 : (z : ℚ) < 1 := by
    rw [← hz]
    linarith [padicFracPart_nonneg p x]
  have hgt_neg1 : (-1 : ℚ) < (z : ℚ) := by
    rw [← hz]
    linarith [padicFracPart_lt_one p x]
  have hz_lt : z < 1 := by exact_mod_cast hlt1
  have hz_gt : -1 < z := by exact_mod_cast hgt_neg1
  have hz0 : z = 0 := by omega
  rw [hz0, Int.cast_zero] at hz
  linarith

theorem padicFracPart_of_norm_le_one {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) :
    padicFracPart p x = 0 := by
  symm
  refine padicFracPart_unique p (k := 0) (m := 0) (by simp) le_rfl zero_lt_one ?_
  simpa using hx

theorem padicFracPart_of_mem_padicInt {x : ℚ_[p]} (hx : x ∈ PadicInt.subring p) :
    padicFracPart p x = 0 :=
  padicFracPart_of_norm_le_one p hx

@[simp]
theorem padicFracPart_zero : padicFracPart p (0 : ℚ_[p]) = 0 :=
  padicFracPart_of_norm_le_one p (by simp)

/-- Exact fractional part of `p⁻¹`: `{p⁻¹}_p = 1 / p`. -/
theorem padicFracPart_inv_prime : padicFracPart p (p : ℚ_[p])⁻¹ = (p : ℚ)⁻¹ := by
  symm
  have hp_pos : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  have hp_gt1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  refine padicFracPart_unique p (k := 1) (m := 1) (by simp) (by positivity)
    (inv_lt_one_of_one_lt₀ hp_gt1) ?_
  have hcast : (((p : ℚ)⁻¹ : ℚ) : ℚ_[p]) = (p : ℚ_[p])⁻¹ := by push_cast; rfl
  rw [hcast, sub_self, norm_zero]
  exact zero_le_one

/-- Additivity of `{·}_p` modulo `ℤ`: `{x}_p + {y}_p - {x + y}_p ∈ ℤ`. -/
theorem padicFracPart_add_sub_mem_int (x y : ℚ_[p]) :
    ∃ m : ℤ, padicFracPart p x + padicFracPart p y - padicFracPart p (x + y) = (m : ℚ) := by
  obtain ⟨kx, ax, _, hx⟩ := padicFracPart_eq_div_pow p x
  obtain ⟨ky, ay, _, hy⟩ := padicFracPart_eq_div_pow p y
  obtain ⟨kxy, axy, _, hxy⟩ := padicFracPart_eq_div_pow p (x + y)
  have hnorm :
      ‖((padicFracPart p x + padicFracPart p y - padicFracPart p (x + y) : ℚ) : ℚ_[p])‖ ≤ 1 := by
    have heq :
        ((padicFracPart p x + padicFracPart p y - padicFracPart p (x + y) : ℚ) : ℚ_[p]) =
        ((x + y) - (padicFracPart p (x + y) : ℚ_[p])) +
          (-(x - (padicFracPart p x : ℚ_[p])) + -(y - (padicFracPart p y : ℚ_[p]))) := by
      push_cast; ring
    rw [heq]
    refine (Padic.nonarchimedean _ _).trans (max_le (norm_sub_padicFracPart_le_one p (x + y)) ?_)
    refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
    · rw [norm_neg]; exact norm_sub_padicFracPart_le_one p x
    · rw [norm_neg]; exact norm_sub_padicFracPart_le_one p y
  have hdiv :
      padicFracPart p x + padicFracPart p y - padicFracPart p (x + y) =
      (((ax : ℤ) * (p : ℤ) ^ (ky + kxy) + (ay : ℤ) * (p : ℤ) ^ (kx + kxy) -
          (axy : ℤ) * (p : ℤ) ^ (kx + ky) : ℤ) : ℚ) / (p : ℚ) ^ (kx + ky + kxy) := by
    rw [hx, hy, hxy]
    have h1 : (p : ℚ) ^ kx ≠ 0 := pow_ne_zero _ (padic_p_rat_ne_zero p)
    have h2 : (p : ℚ) ^ ky ≠ 0 := pow_ne_zero _ (padic_p_rat_ne_zero p)
    have h3 : (p : ℚ) ^ kxy ≠ 0 := pow_ne_zero _ (padic_p_rat_ne_zero p)
    push_cast
    rw [pow_add, pow_add, pow_add, pow_add, pow_add]
    field_simp [h1, h2, h3]
  exact exists_int_of_eq_div_pow_of_norm_le_one p hdiv hnorm

/-- At any distinct prime `ℓ ≠ p`, `{x}_p` is an `ℓ`-adic integer (`‖({x}_p : ℚ_[ℓ])‖ ≤ 1`). -/
theorem norm_padicFracPart_other_prime {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hne : ℓ ≠ p) (x : ℚ_[p]) :
    ‖(padicFracPart p x : ℚ_[ℓ])‖ ≤ 1 := by
  obtain ⟨k, a, _, hfp⟩ := padicFracPart_eq_div_pow p x
  have hcast : (padicFracPart p x : ℚ_[ℓ]) = (a : ℚ_[ℓ]) / (p : ℚ_[ℓ]) ^ k := by
    rw [hfp]; push_cast; rfl
  rw [hcast, norm_div, norm_pow]
  have hcop : ℓ.Coprime p := (hℓ.out.coprime_iff_not_dvd).mpr fun hdvd ↦
    hne ((Nat.prime_dvd_prime_iff_eq hℓ.out hp.out).mp hdvd)
  have hp_norm : ‖(p : ℚ_[ℓ])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr hcop
  rw [hp_norm, one_pow, div_one]
  simpa using Padic.norm_int_le_one (p := ℓ) (a : ℤ)

/-- **Tate's Standard Local $p$-adic Additive Character `ψ_p : ℚ_[p] → ℂ`**:
`ψ_p(x) = exp(2πi · {x}_p)`. -/
def padicAddChar (x : ℚ_[p]) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (padicFracPart p x : ℂ))

@[simp]
theorem padicAddChar_zero : padicAddChar p 0 = 1 := by
  simp [padicAddChar]

/-- **Exact Additivity of `ψ_p`**: `ψ_p(x + y) = ψ_p(x) * ψ_p(y)`. -/
theorem padicAddChar_add (x y : ℚ_[p]) :
    padicAddChar p (x + y) = padicAddChar p x * padicAddChar p y := by
  obtain ⟨m, hm⟩ := padicFracPart_add_sub_mem_int p x y
  have hq : padicFracPart p (x + y) = padicFracPart p x + padicFracPart p y - (m : ℚ) := by
    linarith
  have hc : (padicFracPart p (x + y) : ℂ) =
      (padicFracPart p x : ℂ) + (padicFracPart p y : ℂ) - (m : ℂ) := by
    exact_mod_cast hq
  unfold padicAddChar
  rw [hc, ← Complex.exp_add]
  have hsplit :
      2 * (Real.pi : ℂ) * Complex.I *
          ((padicFracPart p x : ℂ) + (padicFracPart p y : ℂ) - (m : ℂ)) =
      (2 * (Real.pi : ℂ) * Complex.I * (padicFracPart p x : ℂ) +
          2 * (Real.pi : ℂ) * Complex.I * (padicFracPart p y : ℂ)) +
        ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `ψ_p` is trivial on `ℤ_[p]` (`‖x‖ ≤ 1 → ψ_p(x) = 1`). -/
theorem padicAddChar_of_norm_le_one {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) :
    padicAddChar p x = 1 := by
  simp [padicAddChar, padicFracPart_of_norm_le_one p hx]

theorem padicAddChar_of_mem_padicInt {x : ℚ_[p]} (hx : x ∈ PadicInt.subring p) :
    padicAddChar p x = 1 :=
  padicAddChar_of_norm_le_one p hx

/-- Exact evaluation at `p⁻¹`: `ψ_p(p⁻¹) = exp(2πi / p)`. -/
theorem padicAddChar_inv_prime :
    padicAddChar p (p : ℚ_[p])⁻¹ = Complex.exp (2 * Real.pi * Complex.I / (p : ℂ)) := by
  unfold padicAddChar
  rw [padicFracPart_inv_prime p]
  push_cast
  rw [div_eq_mul_inv]

/-- Exact nontriviality at `p⁻¹`: `ψ_p(p⁻¹) ≠ 1` (showing conductor = `ℤ_[p]`). -/
theorem padicAddChar_inv_prime_ne_one : padicAddChar p (p : ℚ_[p])⁻¹ ≠ 1 := by
  rw [padicAddChar_inv_prime p, ne_eq, Complex.exp_eq_one_iff]
  rintro ⟨n, hn⟩
  have h2piI : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hEq : (p : ℂ)⁻¹ = (n : ℂ) := by
    apply mul_left_cancel₀ h2piI
    calc 2 * (Real.pi : ℂ) * Complex.I * (p : ℂ)⁻¹
        = 2 * (Real.pi : ℂ) * Complex.I / (p : ℂ) := by rw [div_eq_mul_inv]
      _ = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
      _ = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) := by ring
  have hreal : (((p : ℝ)⁻¹ : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
    push_cast
    exact hEq
  have hR : (p : ℝ)⁻¹ = (n : ℝ) := Complex.ofReal_injective hreal
  have hpos : (0 : ℝ) < (n : ℝ) := by rw [← hR]; exact inv_pos.mpr (padic_p_pos p)
  have hlt1 : (n : ℝ) < 1 := by rw [← hR]; exact inv_lt_one_of_one_lt₀ (padic_one_lt_p p)
  have hn0 : 0 < n := by exact_mod_cast hpos
  have hn1 : n < 1 := by exact_mod_cast hlt1
  omega

/-- Unit modulus: `‖ψ_p(x)‖ = 1` for every `x ∈ ℚ_[p]`. -/
theorem norm_padicAddChar (x : ℚ_[p]) : ‖padicAddChar p x‖ = 1 := by
  unfold padicAddChar
  have hrew : 2 * (Real.pi : ℂ) * Complex.I * (padicFracPart p x : ℂ) =
      (((2 * Real.pi * (padicFracPart p x : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hrew]
  exact Complex.norm_exp_ofReal_mul_I _

theorem padicAddChar_ne_zero (x : ℚ_[p]) : padicAddChar p x ≠ 0 :=
  Complex.exp_ne_zero _

theorem padicAddChar_neg (x : ℚ_[p]) : padicAddChar p (-x) = (padicAddChar p x)⁻¹ := by
  have h := padicAddChar_add p x (-x)
  rw [add_neg_cancel, padicAddChar_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem padicAddChar_sub (x y : ℚ_[p]) :
    padicAddChar p (x - y) = padicAddChar p x * (padicAddChar p y)⁻¹ := by
  rw [sub_eq_add_neg, padicAddChar_add, padicAddChar_neg]

/-- Complex conjugation equals negation: `star (ψ_p(x)) = ψ_p(-x)`. -/
theorem star_padicAddChar (x : ℚ_[p]) : star (padicAddChar p x) = padicAddChar p (-x) := by
  rw [padicAddChar_neg, Complex.star_def]
  have hmul : starRingEnd ℂ (padicAddChar p x) * padicAddChar p x = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_padicAddChar p x]
    simp
  exact eq_inv_of_mul_eq_one_left hmul

/-- **Exact Conductor Theorem**: `x ∈ ℤ_[p]` if and only if `ψ_p(x * y) = 1` for all `y ∈ ℤ_[p]`. -/
theorem mem_padicInt_iff_forall_padicAddChar_mul_eq_one (x : ℚ_[p]) :
    x ∈ PadicInt.subring p ↔ ∀ y ∈ PadicInt.subring p, padicAddChar p (x * y) = 1 := by
  constructor
  · intro hx y hy
    apply padicAddChar_of_norm_le_one p
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg y) hy
  · intro hall
    by_contra hnot
    have hx_gt : 1 < ‖x‖ := lt_of_not_ge hnot
    have hx_ne : x ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hx_gt; linarith
    let y : ℚ_[p] := (p : ℚ_[p])⁻¹ * x⁻¹
    have hy_norm : ‖y‖ ≤ 1 := by
      have hval : x.valuation ≤ -1 := by
        have hlt : ¬ (0 ≤ x.valuation) := by
          rwa [← Padic.norm_le_one_iff_val_nonneg]
        omega
      rw [show ‖y‖ = ‖(p : ℚ_[p])⁻¹‖ * ‖x⁻¹‖ from norm_mul _ _,
        norm_inv, norm_inv, Padic.norm_p, inv_inv, Padic.norm_eq_zpow_neg_valuation hx_ne,
        ← zpow_neg, neg_neg,
        show (p : ℝ) * (p : ℝ) ^ x.valuation = (p : ℝ) ^ (1 + x.valuation) by
          rw [zpow_add₀ (padic_p_pos p).ne', zpow_one]]
      exact zpow_le_one_of_nonpos₀ (padic_one_lt_p p).le (by omega)
    have hxy : x * y = (p : ℚ_[p])⁻¹ := by
      dsimp only [y]
      rw [mul_left_comm, mul_inv_cancel₀ hx_ne, mul_one]
    have h1 := hall y hy_norm
    rw [hxy] at h1
    exact padicAddChar_inv_prime_ne_one p h1

/-- Tate's local additive character packaged as an exact `AddChar ℚ_[p] ℂ`. -/
def padicAddCharHom : AddChar ℚ_[p] ℂ where
  toFun := padicAddChar p
  map_zero_eq_one' := padicAddChar_zero p
  map_add_eq_mul' := padicAddChar_add p

/-- Tate's local additive character packaged as an exact group homomorphism
`Multiplicative ℚ_[p] →* ℂˣ` (equivalently `ℚ_[p] →+ Additive ℂˣ`). -/
def padicAddCharUnitHom : Multiplicative ℚ_[p] →* ℂˣ where
  toFun x := Units.mk0 (padicAddChar p (Multiplicative.toAdd x))
    (padicAddChar_ne_zero p _)
  map_one' := Units.ext (padicAddChar_zero p)
  map_mul' _ _ := Units.ext (padicAddChar_add p _ _)

@[simp]
theorem padicAddCharHom_apply (x : ℚ_[p]) : padicAddCharHom p x = padicAddChar p x := rfl

@[simp]
theorem padicAddCharUnitHom_coe (x : ℚ_[p]) :
    ((padicAddCharUnitHom p (Multiplicative.ofAdd x) : ℂˣ) : ℂ) = padicAddChar p x := rfl

end LocalPadicCharacter

/-! ## Section 2: Unconditional Global Adelic Character Product Formula on `ℚ` -/

section GlobalAdelicCharacter

/-- Archimedean standard additive character `ψ_∞(x) = exp(-2πi x)` on `ℝ`. -/
def archAddChar (x : ℝ) : ℂ :=
  Complex.exp (-2 * Real.pi * Complex.I * (x : ℂ))

@[simp]
theorem archAddChar_zero : archAddChar 0 = 1 := by
  simp [archAddChar]

theorem archAddChar_add (x y : ℝ) : archAddChar (x + y) = archAddChar x * archAddChar y := by
  unfold archAddChar
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

theorem archAddChar_neg (x : ℝ) : archAddChar (-x) = (archAddChar x)⁻¹ := by
  unfold archAddChar
  rw [← Complex.exp_neg]
  congr 1
  push_cast; ring

theorem archAddChar_int (m : ℤ) : archAddChar (m : ℝ) = 1 := by
  unfold archAddChar
  have h : -2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) =
      ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I (-m)

theorem norm_archAddChar (x : ℝ) : ‖archAddChar x‖ = 1 := by
  unfold archAddChar
  have h : -2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) =
      (((-2 * Real.pi * x : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

theorem star_archAddChar (x : ℝ) : star (archAddChar x) = archAddChar (-x) := by
  rw [archAddChar_neg, Complex.star_def]
  have hmul : starRingEnd ℂ (archAddChar x) * archAddChar x = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_archAddChar x]
    simp
  exact eq_inv_of_mul_eq_one_left hmul

/-- If `p ∤ q.den`, then `q ∈ ℤ_[p]` so `{q}_p = 0`. -/
theorem padicFracPart_rat_eq_zero_of_not_dvd_den (p : ℕ) [Fact p.Prime] {q : ℚ}
    (h : ¬ p ∣ q.den) :
    padicFracPart p (q : ℚ_[p]) = 0 :=
  padicFracPart_of_norm_le_one p (Padic.norm_rat_le_one h)

/-- If `p ∤ q.den`, then `ψ_p(q) = 1`. -/
theorem padicAddChar_rat_eq_one_of_not_dvd_den (p : ℕ) [Fact p.Prime] {q : ℚ}
    (h : ¬ p ∣ q.den) :
    padicAddChar p (q : ℚ_[p]) = 1 :=
  padicAddChar_of_norm_le_one p (Padic.norm_rat_le_one h)

/-- The finite set of primes `Nat.Primes` dividing `q.den`. -/
def ratDenPrimes (q : ℚ) : Finset Nat.Primes :=
  q.den.primeFactors.attach.map
    { toFun := fun (p : {x // x ∈ q.den.primeFactors}) ↦ ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩
      inj' := fun _ _ h ↦ Subtype.ext (congrArg (fun x : Nat.Primes ↦ (x : ℕ)) h) }

lemma mem_ratDenPrimes_iff (q : ℚ) (p : Nat.Primes) :
    p ∈ ratDenPrimes q ↔ (p : ℕ) ∣ q.den := by
  simp only [ratDenPrimes, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨n, hn, hnp⟩
    have heq : n = (p : ℕ) := congrArg Subtype.val hnp
    subst heq
    exact Nat.dvd_of_mem_primeFactors hn
  · intro hdvd
    refine ⟨p.1, Nat.mem_primeFactors.mpr ⟨p.2, hdvd, q.den_nz⟩, Subtype.ext rfl⟩

/-- `p ↦ {q}_p` has finite support (contained in `ratDenPrimes q`). -/
theorem hasFiniteSupport_padicFracPart_rat (q : ℚ) :
    (fun p : Nat.Primes ↦ padicFracPart p.1 (q : ℚ_[p.1])).HasFiniteSupport := by
  refine (ratDenPrimes q).finite_toSet.subset ?_
  intro p hp
  simp only [Function.mem_support, ne_eq] at hp
  simp only [Finset.mem_coe, mem_ratDenPrimes_iff]
  by_contra hnot
  exact hp (padicFracPart_rat_eq_zero_of_not_dvd_den p.1 hnot)

/-- `p ↦ ψ_p(q)` has finite multiplicative support (contained in `ratDenPrimes q`). -/
theorem hasFiniteMulSupport_padicAddChar_rat (q : ℚ) :
    (fun p : Nat.Primes ↦ padicAddChar p.1 (q : ℚ_[p.1])).HasFiniteMulSupport := by
  refine (ratDenPrimes q).finite_toSet.subset ?_
  intro p hp
  simp only [Function.mem_mulSupport, ne_eq] at hp
  simp only [Finset.mem_coe, mem_ratDenPrimes_iff]
  by_contra hnot
  exact hp (padicAddChar_rat_eq_one_of_not_dvd_den p.1 hnot)

/-- **Global Integrality Criterion**: if `r : ℚ` lies in `ℤ_[p]` for every prime `p`, then `r.den = 1`
and `r ∈ ℤ`. -/
theorem rat_den_eq_one_of_forall_padicNorm_le_one {r : ℚ}
    (h : ∀ p : Nat.Primes, ‖(r : ℚ_[p.1])‖ ≤ 1) :
    r.den = 1 := by
  by_contra hne
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hne
  have : Fact p.Prime := ⟨hp_prime⟩
  let P : Nat.Primes := ⟨p, hp_prime⟩
  have hle : ‖(r : ℚ_[p])‖ ≤ 1 := h P
  have hr_eq : (r : ℚ_[p]) = (r.num : ℚ_[p]) / (r.den : ℚ_[p]) := by
    have hq : r = (r.num : ℚ) / (r.den : ℚ) := (Rat.num_div_den r).symm
    conv_lhs => rw [hq]
    push_cast; rfl
  have hcop : Nat.Coprime r.num.natAbs r.den := r.reduced
  have hndvd_nat : ¬ p ∣ r.num.natAbs := fun hd ↦
    hp_prime.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hd hp_dvd)
  have hndvd_int : ¬ (p : ℤ) ∣ r.num := fun hd ↦
    hndvd_nat (Int.natCast_dvd.mp hd)
  have hnum_norm : ‖(r.num : ℚ_[p])‖ = 1 := by
    have hle1 : ‖(r.num : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one r.num
    have hnotlt : ¬ ‖(r.num : ℚ_[p])‖ < 1 := by
      rwa [Padic.norm_intCast_lt_one_iff]
    linarith
  have hden_lt : ‖(r.den : ℚ_[p])‖ < 1 := by
    have hd : (p : ℤ) ∣ (r.den : ℤ) := Int.ofNat_dvd.mpr hp_dvd
    simpa using (Padic.norm_intCast_lt_one_iff (p := p) (k := (r.den : ℤ))).mpr hd
  have hden_pos : 0 < ‖(r.den : ℚ_[p])‖ := by
    rw [norm_pos_iff]
    exact_mod_cast r.den_nz
  rw [hr_eq, norm_div, hnum_norm, one_div] at hle
  have hgt : 1 < ‖(r.den : ℚ_[p])‖⁻¹ := one_lt_inv₀ hden_pos |>.mpr hden_lt
  linarith

theorem exists_int_of_forall_padicNorm_le_one {r : ℚ}
    (h : ∀ p : Nat.Primes, ‖(r : ℚ_[p.1])‖ ≤ 1) :
    ∃ m : ℤ, r = (m : ℚ) := by
  refine ⟨r.num, ?_⟩
  have hd := rat_den_eq_one_of_forall_padicNorm_le_one h
  conv_lhs => rw [← Rat.num_div_den r, hd]
  simp

private lemma norm_sum_padic_le_one {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → ℚ_[ℓ]) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∑ i ∈ s, f i‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (Padic.nonarchimedean _ _).trans (max_le (hf a (Finset.mem_insert_self a s)) ?_)
    exact ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)

/-- **Exact Partial-Fraction Decomposition of Every Rational Number `q : ℚ`** (`finsum` form):
`q - ∑ᶠ p : Nat.Primes, {q}_p ∈ ℤ`. -/
theorem rat_sub_finsum_padicFracPart_mem_int (q : ℚ) :
    ∃ m : ℤ, q - ∑ᶠ p : Nat.Primes, padicFracPart p.1 (q : ℚ_[p.1]) = (m : ℚ) := by
  classical
  have hfin : ∑ᶠ p : Nat.Primes, padicFracPart p.1 (q : ℚ_[p.1]) =
      ∑ p ∈ ratDenPrimes q, padicFracPart p.1 (q : ℚ_[p.1]) := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro p hp
    simp only [Function.mem_support, ne_eq] at hp
    simp only [Finset.mem_coe, mem_ratDenPrimes_iff]
    by_contra hnot
    exact hp (padicFracPart_rat_eq_zero_of_not_dvd_den p.1 hnot)
  rw [hfin]
  apply exists_int_of_forall_padicNorm_le_one
  intro ℓ
  by_cases hℓ : ℓ ∈ ratDenPrimes q
  · have hsplit :
        ((q - ∑ p ∈ ratDenPrimes q, padicFracPart p.1 (q : ℚ_[p.1]) : ℚ) : ℚ_[ℓ.1]) =
        ((q : ℚ_[ℓ.1]) - (padicFracPart ℓ.1 (q : ℚ_[ℓ.1]) : ℚ_[ℓ.1])) +
          -(∑ p ∈ (ratDenPrimes q).erase ℓ, (padicFracPart p.1 (q : ℚ_[p.1]) : ℚ_[ℓ.1])) := by
      rw [← Finset.add_sum_erase _ _ hℓ]
      push_cast; ring
    rw [hsplit]
    refine (Padic.nonarchimedean _ _).trans (max_le (norm_sub_padicFracPart_le_one ℓ.1 _) ?_)
    rw [norm_neg]
    refine norm_sum_padic_le_one _ _ fun p hp ↦ ?_
    have hne : ℓ.1 ≠ p.1 := fun h ↦ (Finset.ne_of_mem_erase hp) (Subtype.ext h.symm)
    exact norm_padicFracPart_other_prime p.1 hne _
  · have hndvd : ¬ (ℓ : ℕ) ∣ q.den := by rwa [← mem_ratDenPrimes_iff]
    have hsplit :
        ((q - ∑ p ∈ ratDenPrimes q, padicFracPart p.1 (q : ℚ_[p.1]) : ℚ) : ℚ_[ℓ.1]) =
        (q : ℚ_[ℓ.1]) + -(∑ p ∈ ratDenPrimes q, (padicFracPart p.1 (q : ℚ_[p.1]) : ℚ_[ℓ.1])) := by
      push_cast; ring
    rw [hsplit]
    refine (Padic.nonarchimedean _ _).trans (max_le (Padic.norm_rat_le_one hndvd) ?_)
    rw [norm_neg]
    refine norm_sum_padic_le_one _ _ fun p hp ↦ ?_
    have hne : ℓ.1 ≠ p.1 := fun h ↦ hℓ (Subtype.ext h ▸ hp)
    exact norm_padicFracPart_other_prime p.1 hne _

/-- **Exact Partial-Fraction Decomposition of Every Rational Number `q : ℚ`** (`primeFactors` form):
`q - ∑_{p ∣ q.den} {q}_p ∈ ℤ`. -/
theorem rat_sub_sum_primeFactors_padicFracPart_mem_int (q : ℚ) :
    ∃ m : ℤ,
      q - ∑ p ∈ ratDenPrimes q, padicFracPart p.1 (q : ℚ_[p.1]) = (m : ℚ) := by
  have hfin : ∑ᶠ p : Nat.Primes, padicFracPart p.1 (q : ℚ_[p.1]) =
      ∑ p ∈ ratDenPrimes q, padicFracPart p.1 (q : ℚ_[p.1]) := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro p hp
    simp only [Function.mem_support, ne_eq] at hp
    simp only [Finset.mem_coe, mem_ratDenPrimes_iff]
    by_contra hnot
    exact hp (padicFracPart_rat_eq_zero_of_not_dvd_den p.1 hnot)
  simpa [hfin] using rat_sub_finsum_padicFracPart_mem_int q

/-- **UNCONDITIONAL GLOBAL ADELIC CHARACTER PRODUCT FORMULA ON `ℚ`** (Additive Companion to
Artin–Whaples, `0` assumptions):
for EVERY rational number `q : ℚ`,
`ψ_∞(q) * ∏'_p ψ_p(q) = 1`. -/
theorem adelicAddChar_rat_eq_one (q : ℚ) :
    archAddChar (q : ℝ) * ∏ᶠ p : Nat.Primes, padicAddChar p.1 (q : ℚ_[p.1]) = 1 := by
  obtain ⟨m, hm⟩ := rat_sub_sum_primeFactors_padicFracPart_mem_int q
  have hprod :
      ∏ᶠ p : Nat.Primes, padicAddChar p.1 (q : ℚ_[p.1]) =
      ∏ p ∈ ratDenPrimes q, padicAddChar p.1 (q : ℚ_[p.1]) := by
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    intro p hp
    simp only [Function.mem_mulSupport, ne_eq] at hp
    simp only [Finset.mem_coe, mem_ratDenPrimes_iff]
    by_contra hnot
    exact hp (padicAddChar_rat_eq_one_of_not_dvd_den p.1 hnot)
  rw [hprod]
  unfold archAddChar padicAddChar
  rw [← Complex.exp_sum, ← Complex.exp_add]
  have hsum :
      ∑ p ∈ ratDenPrimes q, 2 * (Real.pi : ℂ) * Complex.I * (padicFracPart p.1 (q : ℚ_[p.1]) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I *
        ((∑ p ∈ ratDenPrimes q, padicFracPart p.1 (q : ℚ_[p.1]) : ℚ) : ℂ) := by
    rw [← Finset.mul_sum]
    push_cast; rfl
  rw [hsum]
  have hq : ((q : ℝ) : ℂ) = (q : ℂ) := by push_cast; rfl
  have hmC : (q : ℂ) - ((∑ p ∈ ratDenPrimes q, padicFracPart p.1 (q : ℚ_[p.1]) : ℚ) : ℂ) =
      (m : ℂ) := by
    exact_mod_cast hm
  have hexp :
      -2 * (Real.pi : ℂ) * Complex.I * ((q : ℝ) : ℂ) +
        2 * (Real.pi : ℂ) * Complex.I *
          ((∑ p ∈ ratDenPrimes q, padicFracPart p.1 (q : ℚ_[p.1]) : ℚ) : ℂ) =
      ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hq]
    calc -2 * (Real.pi : ℂ) * Complex.I * (q : ℂ) +
            2 * (Real.pi : ℂ) * Complex.I *
              ((∑ p ∈ ratDenPrimes q, padicFracPart p.1 (q : ℚ_[p.1]) : ℚ) : ℂ)
        = -2 * (Real.pi : ℂ) * Complex.I *
            ((q : ℂ) - ((∑ p ∈ ratDenPrimes q, padicFracPart p.1 (q : ℚ_[p.1]) : ℚ) : ℂ)) := by
          ring
      _ = -2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) := by rw [hmC]
      _ = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  rw [hexp]
  exact Complex.exp_int_mul_two_pi_mul_I (-m)

/-! ### Concrete Rational Adele Ring `𝔸_ℚ` & Global Additive Character `ψ_𝔸` -/

/-- The concrete finite adele ring `𝔸_{ℚ,f} = ∏'_p (ℚ_[p], ℤ_[p])` over `Nat.Primes`. -/
abbrev RatFinAdele : Type :=
  Πʳ p : Nat.Primes, [ℚ_[p.1], PadicInt.subring p.1]

/-- The concrete rational adele ring `𝔸_ℚ = ℝ × 𝔸_{ℚ,f}`. -/
abbrev RatAdele : Type := ℝ × RatFinAdele

/-- Diagonal embedding of `ℚ` into the finite adele ring `𝔸_{ℚ,f}`. -/
def diagRatFinAdele : ℚ →+* RatFinAdele where
  toFun q := ⟨fun p ↦ (q : ℚ_[p.1]), by
    rw [Filter.eventually_cofinite]
    refine (ratDenPrimes q).finite_toSet.subset ?_
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    simp only [Finset.mem_coe, mem_ratDenPrimes_iff]
    by_contra hnot
    exact hp (Padic.norm_rat_le_one hnot)⟩
  map_one' := by ext p; exact Rat.cast_one
  map_mul' x y := by ext p; exact Rat.cast_mul x y
  map_zero' := by ext p; exact Rat.cast_zero
  map_add' x y := by ext p; exact Rat.cast_add x y

/-- Diagonal principal embedding `ℚ →+* 𝔸_ℚ = ℝ × 𝔸_{ℚ,f}`. -/
def diagRatAdele : ℚ →+* RatAdele :=
  RingHom.prod (Rat.castHom ℝ) diagRatFinAdele

@[simp]
theorem diagRatAdele_fst (q : ℚ) : (diagRatAdele q).1 = (q : ℝ) := rfl

@[simp]
theorem diagRatAdele_snd (q : ℚ) (p : Nat.Primes) :
    (diagRatAdele q).2 p = (q : ℚ_[p.1]) := rfl

theorem hasFiniteMulSupport_padicAddChar_finAdele (x : RatFinAdele) :
    (fun p : Nat.Primes ↦ padicAddChar p.1 (x p)).HasFiniteMulSupport := by
  rw [Function.HasFiniteMulSupport, Function.mulSupport]
  have h := x.2
  rw [Filter.eventually_cofinite] at h
  refine h.subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  intro hmem
  exact hp (padicAddChar_of_mem_padicInt p.1 hmem)

/-- **Global Adelic Additive Character `ψ_𝔸 : 𝔸_ℚ → ℂ`**:
`ψ_𝔸(x_∞, (x_p)) = ψ_∞(x_∞) * ∏'_p ψ_p(x_p)`. -/
def adelicAddChar (x : RatAdele) : ℂ :=
  archAddChar x.1 * ∏ᶠ p : Nat.Primes, padicAddChar p.1 (x.2 p)

@[simp]
theorem adelicAddChar_zero : adelicAddChar 0 = 1 := by
  simp [adelicAddChar]

theorem adelicAddChar_add (x y : RatAdele) :
    adelicAddChar (x + y) = adelicAddChar x * adelicAddChar y := by
  unfold adelicAddChar
  have hfin :
      (∏ᶠ p : Nat.Primes, padicAddChar p.1 ((x + y).2 p)) =
      (∏ᶠ p : Nat.Primes, padicAddChar p.1 (x.2 p)) *
        (∏ᶠ p : Nat.Primes, padicAddChar p.1 (y.2 p)) := by
    have hcongr :
        (fun p : Nat.Primes ↦ padicAddChar p.1 ((x + y).2 p)) =
        fun p : Nat.Primes ↦ padicAddChar p.1 (x.2 p) * padicAddChar p.1 (y.2 p) := by
      funext p
      exact padicAddChar_add p.1 (x.2 p) (y.2 p)
    rw [hcongr]
    exact finprod_mul_distrib (hasFiniteMulSupport_padicAddChar_finAdele x.2)
      (hasFiniteMulSupport_padicAddChar_finAdele y.2)
  rw [Prod.fst_add, archAddChar_add, hfin]
  ring

theorem norm_adelicAddChar (x : RatAdele) : ‖adelicAddChar x‖ = 1 := by
  classical
  unfold adelicAddChar
  rw [norm_mul, norm_archAddChar, one_mul,
    finprod_def, dif_pos (hasFiniteMulSupport_padicAddChar_finAdele x.2), norm_prod]
  exact Finset.prod_eq_one fun p _ ↦ norm_padicAddChar p.1 (x.2 p)

/-- **Global Adelic Character Triviality on `ℚ ↪ 𝔸_ℚ`**:
`ψ_𝔸(q) = 1` for every `q : ℚ`. -/
theorem adelicAddChar_diagRat_eq_one (q : ℚ) :
    adelicAddChar (diagRatAdele q) = 1 :=
  adelicAddChar_rat_eq_one q

end GlobalAdelicCharacter

/-! ## Section 3: Concrete $p$-adic Haar Integral, Local Fourier Transform, Self-Duality of `1_{ℤ_p}` & Fourier Inversion -/

section LocalPadicFourier

variable (p : ℕ) [hp : Fact p.Prime]

/-- Ball / coset indicator `1_{a + p^k ℤ_p} : ℚ_[p] → ℂ`:
equals `1` if `‖x - a‖ ≤ p^{-k}` and `0` otherwise. -/
def ballInd (a : ℚ_[p]) (k : ℤ) (x : ℚ_[p]) : ℂ :=
  if ‖x - a‖ ≤ (p : ℝ) ^ (-k) then 1 else 0

@[simp]
lemma ballInd_apply (a : ℚ_[p]) (k : ℤ) (x : ℚ_[p]) :
    ballInd p a k x = if ‖x - a‖ ≤ (p : ℝ) ^ (-k) then 1 else 0 := rfl

lemma ballInd_eq_one_iff (a : ℚ_[p]) (k : ℤ) (x : ℚ_[p]) :
    ballInd p a k x = 1 ↔ ‖x - a‖ ≤ (p : ℝ) ^ (-k) := by
  unfold ballInd
  split_ifs with h
  · exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩
  · exact ⟨fun h0 ↦ absurd h0 zero_ne_one, fun hle ↦ absurd hle h⟩

lemma ballInd_eq_zero_iff (a : ℚ_[p]) (k : ℤ) (x : ℚ_[p]) :
    ballInd p a k x = 0 ↔ (p : ℝ) ^ (-k) < ‖x - a‖ := by
  unfold ballInd
  split_ifs with h
  · exact ⟨fun h0 ↦ absurd h0 one_ne_zero, fun hlt ↦ absurd h (not_le_of_gt hlt)⟩
  · exact ⟨fun _ ↦ lt_of_not_ge h, fun _ ↦ rfl⟩

lemma ballInd_eq_of_norm_sub_le {a b : ℚ_[p]} {k : ℤ} (hab : ‖a - b‖ ≤ (p : ℝ) ^ (-k)) :
    ballInd p a k = ballInd p b k := by
  funext x
  unfold ballInd
  have hiff : ‖x - a‖ ≤ (p : ℝ) ^ (-k) ↔ ‖x - b‖ ≤ (p : ℝ) ^ (-k) := by
    constructor <;> intro hx
    · have : x - b = (x - a) + (a - b) := by ring
      rw [this]
      exact (Padic.nonarchimedean _ _).trans (max_le hx hab)
    · have : x - a = (x - b) + -(a - b) := by ring
      rw [this]
      refine (Padic.nonarchimedean _ _).trans (max_le hx ?_)
      rwa [norm_neg]
  simp only [hiff]

lemma ballInd_translate (a t : ℚ_[p]) (k : ℤ) (x : ℚ_[p]) :
    ballInd p a k (x + t) = ballInd p (a - t) k x := by
  unfold ballInd
  have : x + t - a = x - (a - t) := by ring
  rw [this]

lemma ballInd_neg_zero (k : ℤ) (x : ℚ_[p]) :
    ballInd p 0 k (-x) = ballInd p 0 k x := by
  simp [ballInd]

/-- Cutoff certificate `(R, N)` (`R ≤ N`) for a $p$-adic Schwartz–Bruhat function `f`:
`f` vanishes outside `p^R ℤ_p` (`‖x‖ > p^{-R}`) and is constant on cosets of `p^N ℤ_p`. -/
def IsPadicSBAt (R N : ℤ) (f : ℚ_[p] → ℂ) : Prop :=
  R ≤ N ∧
  (∀ x : ℚ_[p], (p : ℝ) ^ (-R) < ‖x‖ → f x = 0) ∧
  (∀ x y : ℚ_[p], ‖x - y‖ ≤ (p : ℝ) ^ (-N) → f x = f y)

/-- A function `f : ℚ_[p] → ℂ` is **Schwartz–Bruhat** (compactly supported & locally constant)
if it admits some cutoff pair `(R, N)`. -/
def IsPadicSchwartzBruhat (f : ℚ_[p] → ℂ) : Prop :=
  ∃ R N : ℤ, IsPadicSBAt p R N f

lemma isPadicSBAt_mono {R₁ R₂ N₁ N₂ : ℤ} {f : ℚ_[p] → ℂ}
    (hf : IsPadicSBAt p R₁ N₁ f) (hR : R₂ ≤ R₁) (hN : N₁ ≤ N₂) :
    IsPadicSBAt p R₂ N₂ f := by
  refine ⟨le_trans hR (le_trans hf.1 hN), fun x hx ↦ hf.2.1 x ?_, fun x y hxy ↦ hf.2.2 x y ?_⟩
  · have hle : (p : ℝ) ^ (-R₁) ≤ (p : ℝ) ^ (-R₂) :=
      zpow_le_zpow_right₀ (padic_one_lt_p p).le (by omega)
    exact hle.trans_lt hx
  · have hle : (p : ℝ) ^ (-N₂) ≤ (p : ℝ) ^ (-N₁) :=
      zpow_le_zpow_right₀ (padic_one_lt_p p).le (by omega)
    exact hxy.trans hle

/-- Coset-sum Haar integral at cutoff `(R, N)`:
`p^{-N} * ∑_{j : Fin (p^(N - R).toNat)} f(p^R * j)`. -/
def padicIntAt (R N : ℤ) (f : ℚ_[p] → ℂ) : ℂ :=
  (p : ℂ) ^ (-N) * ∑ j : Fin (p ^ (N - R).toNat), f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]))

private lemma padicIntAt_succ_right {R N : ℤ} {f : ℚ_[p] → ℂ} (hf : IsPadicSBAt p R N f) :
    padicIntAt p R (N + 1) f = padicIntAt p R N f := by
  set d := (N - R).toNat
  have hd_eq : (N + 1 - R).toNat = d + 1 := by
    have hRN : R ≤ N := hf.1
    omega
  have hd_cast : (d : ℤ) = N - R := Int.toNat_of_nonneg (by linarith [hf.1])
  unfold padicIntAt
  rw [hd_eq]
  let e' : Fin p × Fin (p ^ d) ≃ Fin (p ^ (d + 1)) :=
    (finProdFinEquiv.trans (finCongr (by rw [pow_succ, mul_comm])))
  have hsum' :
      ∑ j : Fin (p ^ (d + 1)), f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) =
      ∑ m : Fin p, ∑ j : Fin (p ^ d),
        f ((p : ℚ_[p]) ^ R * ((m.1 * p ^ d + j.1 : ℕ) : ℚ_[p])) := by
    rw [← Equiv.sum_comp e', Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [e', Equiv.trans_apply, finCongr_apply, Fin.val_cast, finProdFinEquiv]
    dsimp only [Equiv.coe_fn_mk]
    congr 2
    push_cast; ring
  rw [hsum']
  have hconst : ∀ (m : Fin p) (j : Fin (p ^ d)),
      f ((p : ℚ_[p]) ^ R * ((m.1 * p ^ d + j.1 : ℕ) : ℚ_[p])) =
      f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) := by
    intro m j
    apply hf.2.2
    have hdiff :
        (p : ℚ_[p]) ^ R * ((m.1 * p ^ d + j.1 : ℕ) : ℚ_[p]) -
          (p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]) =
        (p : ℚ_[p]) ^ N * (m.1 : ℚ_[p]) := by
      push_cast
      have hpow : (p : ℚ_[p]) ^ R * (p : ℚ_[p]) ^ d = (p : ℚ_[p]) ^ N := by
        rw [← zpow_natCast (p : ℚ_[p]) d, ← zpow_add₀ (padic_p_ne_zero p), hd_cast]
        congr 1; omega
      calc (p : ℚ_[p]) ^ R * ((m.1 : ℚ_[p]) * (p : ℚ_[p]) ^ d + (j.1 : ℚ_[p])) -
              (p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])
          = ((p : ℚ_[p]) ^ R * (p : ℚ_[p]) ^ d) * (m.1 : ℚ_[p]) := by ring
        _ = (p : ℚ_[p]) ^ N * (m.1 : ℚ_[p]) := by rw [hpow]
    rw [hdiff, norm_mul, Padic.norm_p_zpow]
    have hm : ‖(m.1 : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := p) (m.1 : ℤ)
    calc (p : ℝ) ^ (-N) * ‖(m.1 : ℚ_[p])‖
        ≤ (p : ℝ) ^ (-N) * 1 := mul_le_mul_of_nonneg_left hm (zpow_nonneg (padic_p_pos p).le _)
      _ = (p : ℝ) ^ (-N) := mul_one _
  simp_rw [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hp_zpow : (p : ℂ) ^ (-(N + 1)) * (p : ℂ) = (p : ℂ) ^ (-N) := by
    have h1 : (p : ℂ) ^ (-(N + 1) + 1) = (p : ℂ) ^ (-(N + 1)) * (p : ℂ) ^ (1 : ℤ) :=
      zpow_add₀ (padic_p_complex_ne_zero p) _ _
    rw [zpow_one] at h1
    rw [← h1]
    congr 1; omega
  rw [← mul_assoc, hp_zpow]

private lemma padicIntAt_pred_left {R N : ℤ} {f : ℚ_[p] → ℂ} (hf : IsPadicSBAt p R N f) :
    padicIntAt p (R - 1) N f = padicIntAt p R N f := by
  set d := (N - R).toNat
  have hd_eq : (N - (R - 1)).toNat = d + 1 := by
    have hRN : R ≤ N := hf.1
    omega
  have hpow_step : (p : ℚ_[p]) ^ (R - 1) * (p : ℚ_[p]) = (p : ℚ_[p]) ^ R := by
    have h1 : (p : ℚ_[p]) ^ (R - 1 + 1) = (p : ℚ_[p]) ^ (R - 1) * (p : ℚ_[p]) ^ (1 : ℤ) :=
      zpow_add₀ (padic_p_ne_zero p) _ _
    rw [zpow_one] at h1
    rw [← h1]
    congr 1; omega
  unfold padicIntAt
  rw [hd_eq]
  congr 1
  let e : Fin (p ^ d) × Fin p ≃ Fin (p ^ (d + 1)) :=
    (finProdFinEquiv.trans (finCongr (by rw [pow_succ])))
  have he_val : ∀ (j : Fin (p ^ d)) (m : Fin p), (e (j, m)).1 = j.1 * p + m.1 := by
    intro j m
    change (finProdFinEquiv (j, m)).1 = j.1 * p + m.1
    simp only [finProdFinEquiv]
    dsimp only [Equiv.coe_fn_mk]
    ring
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_eq_single (⟨0, hp.out.pos⟩ : Fin p)]
  · rw [he_val j ⟨0, hp.out.pos⟩]
    dsimp only
    rw [add_zero]
    push_cast
    congr 1
    calc (p : ℚ_[p]) ^ (R - 1) * ((j.1 : ℚ_[p]) * (p : ℚ_[p]))
        = ((p : ℚ_[p]) ^ (R - 1) * (p : ℚ_[p])) * (j.1 : ℚ_[p]) := by ring
      _ = (p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]) := by rw [hpow_step]
  · intro m _ hm
    apply hf.2.1
    rw [he_val j m]
    have hm_pos : 0 < m.1 := Nat.pos_of_ne_zero (fun h0 ↦ hm (Fin.ext h0))
    have hm_cop : p.Coprime m.1 := (hp.out.coprime_iff_not_dvd).mpr
      (Nat.not_dvd_of_pos_of_lt hm_pos m.2)
    have hm_norm : ‖(m.1 : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr hm_cop
    have hterm1 : ‖(p : ℚ_[p]) ^ (R - 1) * (m.1 : ℚ_[p])‖ = (p : ℝ) ^ (-(R - 1)) := by
      rw [norm_mul, Padic.norm_p_zpow, hm_norm, mul_one]
    have hterm2 : ‖(p : ℚ_[p]) ^ (R - 1) * ((j.1 * p : ℕ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-R) := by
      have hrew : (p : ℚ_[p]) ^ (R - 1) * ((j.1 * p : ℕ) : ℚ_[p]) =
          (p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]) := by
        push_cast
        calc (p : ℚ_[p]) ^ (R - 1) * ((j.1 : ℚ_[p]) * (p : ℚ_[p]))
            = ((p : ℚ_[p]) ^ (R - 1) * (p : ℚ_[p])) * (j.1 : ℚ_[p]) := by ring
          _ = (p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]) := by rw [hpow_step]
      rw [hrew, norm_mul, Padic.norm_p_zpow]
      have hj : ‖(j.1 : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := p) (j.1 : ℤ)
      calc (p : ℝ) ^ (-R) * ‖(j.1 : ℚ_[p])‖
          ≤ (p : ℝ) ^ (-R) * 1 := mul_le_mul_of_nonneg_left hj (zpow_nonneg (padic_p_pos p).le _)
        _ = (p : ℝ) ^ (-R) := mul_one _
    have hlt : (p : ℝ) ^ (-R) < (p : ℝ) ^ (-(R - 1)) :=
      zpow_lt_zpow_right₀ (padic_one_lt_p p) (by omega)
    have hne_norm :
        ‖(p : ℚ_[p]) ^ (R - 1) * ((j.1 * p : ℕ) : ℚ_[p])‖ ≠
        ‖(p : ℚ_[p]) ^ (R - 1) * (m.1 : ℚ_[p])‖ := by
      rw [hterm1]; exact (hterm2.trans_lt hlt).ne
    have hsplit :
        (p : ℚ_[p]) ^ (R - 1) * ((j.1 * p + m.1 : ℕ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ (R - 1) * ((j.1 * p : ℕ) : ℚ_[p]) +
          (p : ℚ_[p]) ^ (R - 1) * (m.1 : ℚ_[p]) := by
      push_cast; ring
    rw [hsplit, Padic.add_eq_max_of_ne hne_norm, hterm1]
    exact hlt.trans_le (le_max_right _ _)
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma padicIntAt_add_right {R N : ℤ} {f : ℚ_[p] → ℂ} (hf : IsPadicSBAt p R N f)
    (k : ℕ) :
    padicIntAt p R (N + k) f = padicIntAt p R N f := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hfk : IsPadicSBAt p R (N + k) f := isPadicSBAt_mono p hf le_rfl (by omega)
    have hstep := padicIntAt_succ_right p hfk
    have heq : N + (k + 1 : ℕ) = N + k + 1 := by omega
    rw [heq, hstep, ih]

private lemma padicIntAt_sub_left {R N : ℤ} {f : ℚ_[p] → ℂ} (hf : IsPadicSBAt p R N f)
    (k : ℕ) :
    padicIntAt p (R - k) N f = padicIntAt p R N f := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hfk : IsPadicSBAt p (R - k) N f := isPadicSBAt_mono p hf (by omega) le_rfl
    have hstep := padicIntAt_pred_left p hfk
    have heq : R - (k + 1 : ℕ) = R - k - 1 := by omega
    rw [heq, hstep, ih]

/-- **Well-definedness of the $p$-adic Haar Integral**:
any two valid Schwartz–Bruhat cutoff pairs `(R₁, N₁)` and `(R₂, N₂)` yield the exact same
coset sum `padicIntAt`. -/
theorem padicIntAt_eq_of_isPadicSBAt {R₁ N₁ R₂ N₂ : ℤ} {f : ℚ_[p] → ℂ}
    (hf₁ : IsPadicSBAt p R₁ N₁ f) (hf₂ : IsPadicSBAt p R₂ N₂ f) :
    padicIntAt p R₁ N₁ f = padicIntAt p R₂ N₂ f := by
  let R := min R₁ R₂
  let N := max N₁ N₂
  have h1 : padicIntAt p R N f = padicIntAt p R₁ N₁ f := by
    have hN : N = N₁ + (N - N₁).toNat := by
      have : N₁ ≤ N := le_max_left _ _; omega
    have hR : R = R₁ - (R₁ - R).toNat := by
      have : R ≤ R₁ := min_le_left _ _; omega
    have hfN : IsPadicSBAt p R₁ N f := isPadicSBAt_mono p hf₁ le_rfl (le_max_left _ _)
    rw [hR, padicIntAt_sub_left p hfN, hN, padicIntAt_add_right p hf₁]
  have h2 : padicIntAt p R N f = padicIntAt p R₂ N₂ f := by
    have hN : N = N₂ + (N - N₂).toNat := by
      have : N₂ ≤ N := le_max_right _ _; omega
    have hR : R = R₂ - (R₂ - R).toNat := by
      have : R ≤ R₂ := min_le_right _ _; omega
    have hfN : IsPadicSBAt p R₂ N f := isPadicSBAt_mono p hf₂ le_rfl (le_max_right _ _)
    rw [hR, padicIntAt_sub_left p hfN, hN, padicIntAt_add_right p hf₂]
  rw [← h1, h2]

/-- **Concrete Normalized $p$-adic Haar Integral `∫_{ℚ_p} f(x) dx`** (with `μ(ℤ_p) = 1`)
on Schwartz–Bruhat functions `f : ℚ_[p] → ℂ`. -/
def padicHaarInt (f : ℚ_[p] → ℂ) : ℂ := by
  classical
  exact if hf : IsPadicSchwartzBruhat p f then
    padicIntAt p hf.choose hf.choose_spec.choose f
  else 0

theorem padicHaarInt_eq_padicIntAt {R N : ℤ} {f : ℚ_[p] → ℂ} (hf : IsPadicSBAt p R N f) :
    padicHaarInt p f = padicIntAt p R N f := by
  classical
  have hex : IsPadicSchwartzBruhat p f := ⟨R, N, hf⟩
  unfold padicHaarInt
  rw [dif_pos hex]
  exact padicIntAt_eq_of_isPadicSBAt p hex.choose_spec.choose_spec hf

theorem padicHaarInt_congr {f g : ℚ_[p] → ℂ} (h : ∀ x, f x = g x) :
    padicHaarInt p f = padicHaarInt p g := by
  congr 1; funext x; exact h x

theorem isPadicSchwartzBruhat_add {f g : ℚ_[p] → ℂ}
    (hf : IsPadicSchwartzBruhat p f) (hg : IsPadicSchwartzBruhat p g) :
    IsPadicSchwartzBruhat p (fun x ↦ f x + g x) := by
  rcases hf with ⟨R₁, N₁, hf₁⟩
  rcases hg with ⟨R₂, N₂, hg₂⟩
  let R := min R₁ R₂
  let N := max N₁ N₂
  have hf' : IsPadicSBAt p R N f := isPadicSBAt_mono p hf₁ (min_le_left R₁ R₂) (le_max_left N₁ N₂)
  have hg' : IsPadicSBAt p R N g := isPadicSBAt_mono p hg₂ (min_le_right R₁ R₂) (le_max_right N₁ N₂)
  exact ⟨R, N, hf'.1,
    fun x hx ↦ by simp [hf'.2.1 x hx, hg'.2.1 x hx],
    fun x y hxy ↦ by simp [hf'.2.2 x y hxy, hg'.2.2 x y hxy]⟩

theorem isPadicSchwartzBruhat_smul (c : ℂ) {f : ℚ_[p] → ℂ}
    (hf : IsPadicSchwartzBruhat p f) :
    IsPadicSchwartzBruhat p (fun x ↦ c * f x) := by
  rcases hf with ⟨R, N, hf⟩
  exact ⟨R, N, hf.1,
    fun x hx ↦ by simp [hf.2.1 x hx],
    fun x y hxy ↦ by simp [hf.2.2 x y hxy]⟩

theorem padicHaarInt_add {f g : ℚ_[p] → ℂ}
    (hf : IsPadicSchwartzBruhat p f) (hg : IsPadicSchwartzBruhat p g) :
    padicHaarInt p (fun x ↦ f x + g x) = padicHaarInt p f + padicHaarInt p g := by
  rcases hf with ⟨R₁, N₁, hf₁⟩
  rcases hg with ⟨R₂, N₂, hg₂⟩
  let R := min R₁ R₂
  let N := max N₁ N₂
  have hf' : IsPadicSBAt p R N f := isPadicSBAt_mono p hf₁ (min_le_left R₁ R₂) (le_max_left N₁ N₂)
  have hg' : IsPadicSBAt p R N g := isPadicSBAt_mono p hg₂ (min_le_right R₁ R₂) (le_max_right N₁ N₂)
  have hfg : IsPadicSBAt p R N (fun x ↦ f x + g x) :=
    ⟨hf'.1, fun x hx ↦ by simp [hf'.2.1 x hx, hg'.2.1 x hx],
     fun x y hxy ↦ by simp [hf'.2.2 x y hxy, hg'.2.2 x y hxy]⟩
  rw [padicHaarInt_eq_padicIntAt p hfg, padicHaarInt_eq_padicIntAt p hf',
    padicHaarInt_eq_padicIntAt p hg']
  unfold padicIntAt
  rw [Finset.sum_add_distrib, mul_add]

theorem padicHaarInt_smul (c : ℂ) {f : ℚ_[p] → ℂ} (hf : IsPadicSchwartzBruhat p f) :
    padicHaarInt p (fun x ↦ c * f x) = c * padicHaarInt p f := by
  rcases hf with ⟨R, N, hf⟩
  have hcf : IsPadicSBAt p R N (fun x ↦ c * f x) :=
    ⟨hf.1, fun x hx ↦ by simp [hf.2.1 x hx], fun x y hxy ↦ by simp [hf.2.2 x y hxy]⟩
  rw [padicHaarInt_eq_padicIntAt p hcf, padicHaarInt_eq_padicIntAt p hf]
  unfold padicIntAt
  rw [← Finset.mul_sum]
  ring

theorem padicHaarInt_zero : padicHaarInt p (fun _ ↦ 0) = 0 := by
  have h0 : IsPadicSBAt p 0 0 (fun _ ↦ 0) := ⟨le_rfl, fun _ _ ↦ rfl, fun _ _ _ ↦ rfl⟩
  rw [padicHaarInt_eq_padicIntAt p h0]
  simp [padicIntAt]

theorem isPadicSchwartzBruhat_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℚ_[p] → ℂ)
    (hF : ∀ i ∈ s, IsPadicSchwartzBruhat p (F i)) :
    IsPadicSchwartzBruhat p (fun x ↦ ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, le_rfl, fun _ _ ↦ by simp, fun _ _ _ ↦ by simp⟩
  | insert a s ha ih =>
    have hFa := hF a (Finset.mem_insert_self a s)
    have hFs := ih (fun i hi ↦ hF i (Finset.mem_insert_of_mem hi))
    have hrew : (fun x ↦ ∑ i ∈ insert a s, F i x) = fun x ↦ F a x + ∑ i ∈ s, F i x := by
      funext x; exact Finset.sum_insert ha
    rw [hrew]
    exact isPadicSchwartzBruhat_add p hFa hFs

theorem padicHaarInt_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℚ_[p] → ℂ)
    (hF : ∀ i ∈ s, IsPadicSchwartzBruhat p (F i)) :
    padicHaarInt p (fun x ↦ ∑ i ∈ s, F i x) = ∑ i ∈ s, padicHaarInt p (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using padicHaarInt_zero p
  | insert a s ha ih =>
    have hFa : IsPadicSchwartzBruhat p (F a) := hF a (Finset.mem_insert_self a s)
    have hFs : ∀ i ∈ s, IsPadicSchwartzBruhat p (F i) :=
      fun i hi ↦ hF i (Finset.mem_insert_of_mem hi)
    have hsum_sb := isPadicSchwartzBruhat_finset_sum p s F hFs
    have hrew : (fun x ↦ ∑ i ∈ insert a s, F i x) = fun x ↦ F a x + ∑ i ∈ s, F i x := by
      funext x; exact Finset.sum_insert ha
    rw [hrew, padicHaarInt_add p hFa hsum_sb, ih hFs, Finset.sum_insert ha]

/-- **Translation Invariance of the $p$-adic Haar Integral**:
`∫_{ℚ_p} f(x + t) dx = ∫_{ℚ_p} f(x) dx` for every Schwartz–Bruhat `f` and every `t ∈ ℚ_[p]`. -/
theorem padicHaarInt_translate (t : ℚ_[p]) {f : ℚ_[p] → ℂ} (hf : IsPadicSchwartzBruhat p f) :
    padicHaarInt p (fun x ↦ f (x + t)) = padicHaarInt p f := by
  rcases hf with ⟨R₀, N₀, hf₀⟩
  let R := min R₀ t.valuation
  let N := max N₀ R
  have hf : IsPadicSBAt p R N f :=
    isPadicSBAt_mono p hf₀ (min_le_left _ _) (le_max_left _ _)
  have ht_norm : ‖t‖ ≤ (p : ℝ) ^ (-R) := by
    by_cases ht0 : t = 0
    · simp [ht0]; exact zpow_nonneg (padic_p_pos p).le _
    · rw [Padic.norm_eq_zpow_neg_valuation ht0]
      exact zpow_le_zpow_right₀ (padic_one_lt_p p).le (by omega)
  have hft : IsPadicSBAt p R N (fun x ↦ f (x + t)) := by
    refine ⟨hf.1, fun x hx ↦ hf.2.1 (x + t) ?_, fun x y hxy ↦ hf.2.2 (x + t) (y + t) ?_⟩
    · have hne : ‖x‖ ≠ ‖t‖ := (ht_norm.trans_lt hx).ne'
      rw [Padic.add_eq_max_of_ne hne]
      exact hx.trans_le (le_max_left _ _)
    · simpa [add_sub_add_right_eq_sub] using hxy
  rw [padicHaarInt_eq_padicIntAt p hft, padicHaarInt_eq_padicIntAt p hf]
  unfold padicIntAt
  congr 1
  set d := (N - R).toNat
  have hd_cast : (d : ℤ) = N - R := Int.toNat_of_nonneg (by linarith [hf.1])
  -- Represent `p^{-R} * t ∈ ℤ_[p]` modulo `p^d` as `c : Fin (p^d)`
  have htr_norm : ‖(p : ℚ_[p]) ^ (-R) * t‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_zpow, neg_neg]
    calc (p : ℝ) ^ R * ‖t‖
        ≤ (p : ℝ) ^ R * (p : ℝ) ^ (-R) :=
          mul_le_mul_of_nonneg_left ht_norm (zpow_nonneg (padic_p_pos p).le _)
      _ = 1 := by rw [← zpow_add₀ (padic_p_pos p).ne', add_neg_cancel, zpow_zero]
  let zt : ℤ_[p] := ⟨(p : ℚ_[p]) ^ (-R) * t, htr_norm⟩
  let c : ℕ := zt.appr d
  have hc_lt : c < p ^ d := PadicInt.appr_lt zt d
  have hct_diff : ‖t - (p : ℚ_[p]) ^ R * (c : ℚ_[p])‖ ≤ (p : ℝ) ^ (-N) := by
    have hspec : zt - (c : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ d} := PadicInt.appr_spec d zt
    rw [Ideal.mem_span_singleton] at hspec
    obtain ⟨u, hu⟩ := hspec
    have hcoe : (zt : ℚ_[p]) - (c : ℚ_[p]) = (p : ℚ_[p]) ^ d * (u : ℚ_[p]) := by
      have h1 := congrArg (fun s : ℤ_[p] ↦ (s : ℚ_[p])) hu
      simpa [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast] using h1
    have hpow : (p : ℚ_[p]) ^ R * (p : ℚ_[p]) ^ d = (p : ℚ_[p]) ^ N := by
      rw [← zpow_natCast (p : ℚ_[p]) d, ← zpow_add₀ (padic_p_ne_zero p), hd_cast]
      congr 1; omega
    have hmul : t - (p : ℚ_[p]) ^ R * (c : ℚ_[p]) = (p : ℚ_[p]) ^ N * (u : ℚ_[p]) := by
      have hzt : (zt : ℚ_[p]) = (p : ℚ_[p]) ^ (-R) * t := rfl
      rw [hzt] at hcoe
      calc t - (p : ℚ_[p]) ^ R * (c : ℚ_[p])
          = (p : ℚ_[p]) ^ R * ((p : ℚ_[p]) ^ (-R) * t - (c : ℚ_[p])) := by
            rw [mul_sub, ← mul_assoc, ← zpow_add₀ (padic_p_ne_zero p), add_neg_cancel,
              zpow_zero, one_mul]
        _ = (p : ℚ_[p]) ^ R * ((p : ℚ_[p]) ^ d * (u : ℚ_[p])) := by rw [hcoe]
        _ = ((p : ℚ_[p]) ^ R * (p : ℚ_[p]) ^ d) * (u : ℚ_[p]) := by ring
        _ = (p : ℚ_[p]) ^ N * (u : ℚ_[p]) := by rw [hpow]
    rw [hmul, norm_mul, Padic.norm_p_zpow]
    calc (p : ℝ) ^ (-N) * ‖(u : ℚ_[p])‖
        ≤ (p : ℝ) ^ (-N) * 1 := mul_le_mul_of_nonneg_left u.2 (zpow_nonneg (padic_p_pos p).le _)
      _ = (p : ℝ) ^ (-N) := mul_one _
  -- Translation by `c` modulo `p^d` gives an explicit bijection on `Fin (p^d)`
  have hpd_pos : 0 < p ^ d := pow_pos hp.out.pos d
  let c' : ℕ := c % p ^ d
  have hc'_lt : c' < p ^ d := Nat.mod_lt _ hpd_pos
  let σ : Fin (p ^ d) ≃ Fin (p ^ d) :=
    { toFun := fun j ↦ ⟨(j.1 + c') % p ^ d, Nat.mod_lt _ hpd_pos⟩
      invFun := fun j ↦ ⟨(j.1 + (p ^ d - c')) % p ^ d, Nat.mod_lt _ hpd_pos⟩
      left_inv := fun j ↦ Fin.ext (by
        dsimp only
        rw [Nat.mod_add_mod, add_assoc, Nat.add_sub_of_le hc'_lt.le,
          Nat.add_mod_right, Nat.mod_eq_of_lt j.2])
      right_inv := fun j ↦ Fin.ext (by
        dsimp only
        rw [Nat.mod_add_mod, add_assoc, Nat.sub_add_cancel hc'_lt.le,
          Nat.add_mod_right, Nat.mod_eq_of_lt j.2]) }
  rw [← Equiv.sum_comp σ (fun j : Fin (p ^ d) ↦ f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])))]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  apply hf.2.2
  -- Show `(p^R * j + t) - p^R * (σ j) ∈ p^N ℤ_p`
  have hσ_val : (σ j).1 = (j.1 + c) % p ^ d := by
    change (j.1 + c % p ^ d) % p ^ d = (j.1 + c) % p ^ d
    rw [Nat.add_mod_mod]
  have hdvd : ((p ^ d : ℤ)) ∣ ((j.1 + c : ℕ) : ℤ) - ((σ j).1 : ℤ) := by
    rw [hσ_val]
    refine ⟨((j.1 + c) / p ^ d : ℕ), ?_⟩
    have hdiv := Nat.div_add_mod (j.1 + c) (p ^ d)
    have hdivZ : ((p ^ d : ℤ)) * (((j.1 + c) / p ^ d : ℕ) : ℤ) +
        (((j.1 + c) % p ^ d : ℕ) : ℤ) = ((j.1 + c : ℕ) : ℤ) := by
      exact_mod_cast hdiv
    linarith
  have hdiff_int : ‖((p : ℚ_[p]) ^ R * ((j.1 + c : ℕ) : ℚ_[p]) -
      (p : ℚ_[p]) ^ R * ((σ j).1 : ℚ_[p]))‖ ≤ (p : ℝ) ^ (-N) := by
    have hfac :
        (p : ℚ_[p]) ^ R * ((j.1 + c : ℕ) : ℚ_[p]) - (p : ℚ_[p]) ^ R * ((σ j).1 : ℚ_[p]) =
        (p : ℚ_[p]) ^ R * ((((j.1 + c : ℕ) : ℤ) - ((σ j).1 : ℤ) : ℤ) : ℚ_[p]) := by
      push_cast; ring
    rw [hfac, norm_mul, Padic.norm_p_zpow]
    have hnorm_d : ‖((((j.1 + c : ℕ) : ℤ) - ((σ j).1 : ℤ) : ℤ) : ℚ_[p])‖ ≤
        (p : ℝ) ^ (-(d : ℤ)) :=
      (Padic.norm_int_le_pow_iff_dvd _ d).mpr (by simpa using hdvd)
    calc (p : ℝ) ^ (-R) * ‖((((j.1 + c : ℕ) : ℤ) - ((σ j).1 : ℤ) : ℤ) : ℚ_[p])‖
        ≤ (p : ℝ) ^ (-R) * (p : ℝ) ^ (-(d : ℤ)) :=
          mul_le_mul_of_nonneg_left hnorm_d (zpow_nonneg (padic_p_pos p).le _)
      _ = (p : ℝ) ^ (-N) := by
          rw [← zpow_add₀ (padic_p_pos p).ne', hd_cast]; congr 1; omega
  have hsplit :
      (p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]) + t - (p : ℚ_[p]) ^ R * ((σ j).1 : ℚ_[p]) =
      (t - (p : ℚ_[p]) ^ R * (c : ℚ_[p])) +
        ((p : ℚ_[p]) ^ R * ((j.1 + c : ℕ) : ℚ_[p]) - (p : ℚ_[p]) ^ R * ((σ j).1 : ℚ_[p])) := by
    push_cast; ring
  rw [hsplit]
  exact (Padic.nonarchimedean _ _).trans (max_le hct_diff hdiff_int)

/-- Every ball indicator `1_{a + p^k ℤ_p}` is Schwartz–Bruhat. -/
theorem isPadicSBAt_ballInd (a : ℚ_[p]) (k : ℤ) :
    IsPadicSBAt p (min k a.valuation) k (ballInd p a k) := by
  refine ⟨min_le_left _ _, ?_, ?_⟩
  · intro x hx
    rw [ballInd_eq_zero_iff]
    have ha : ‖a‖ ≤ (p : ℝ) ^ (-(min k a.valuation)) := by
      by_cases ha0 : a = 0
      · simp [ha0]; exact zpow_nonneg (padic_p_pos p).le _
      · rw [Padic.norm_eq_zpow_neg_valuation ha0]
        exact zpow_le_zpow_right₀ (padic_one_lt_p p).le (by omega)
    have hne : ‖x‖ ≠ ‖-a‖ := by rw [norm_neg]; exact (ha.trans_lt hx).ne'
    have hsub : ‖x - a‖ = ‖x‖ := by
      rw [sub_eq_add_neg, Padic.add_eq_max_of_ne hne, norm_neg, max_eq_left (ha.trans_lt hx).le]
    rw [hsub]
    have hle : (p : ℝ) ^ (-k) ≤ (p : ℝ) ^ (-(min k a.valuation)) :=
      zpow_le_zpow_right₀ (padic_one_lt_p p).le (by omega)
    exact hle.trans_lt hx
  · intro x y hxy
    unfold ballInd
    have hiff : ‖x - a‖ ≤ (p : ℝ) ^ (-k) ↔ ‖y - a‖ ≤ (p : ℝ) ^ (-k) := by
      constructor <;> intro h
      · have : y - a = (x - a) + -(x - y) := by ring
        rw [this]
        refine (Padic.nonarchimedean _ _).trans (max_le h ?_)
        rwa [norm_neg]
      · have : x - a = (y - a) + (x - y) := by ring
        rw [this]
        exact (Padic.nonarchimedean _ _).trans (max_le h hxy)
    simp only [hiff]

theorem isPadicSchwartzBruhat_ballInd (a : ℚ_[p]) (k : ℤ) :
    IsPadicSchwartzBruhat p (ballInd p a k) :=
  ⟨min k a.valuation, k, isPadicSBAt_ballInd p a k⟩

/-- **Exact Haar Measure of `p^k ℤ_p`**: `∫_{ℚ_p} 1_{p^k ℤ_p}(x) dx = p^{-k}`. -/
theorem padicHaarInt_ballInd_zero (k : ℤ) :
    padicHaarInt p (ballInd p 0 k) = (p : ℂ) ^ (-k) := by
  have hsb : IsPadicSBAt p k k (ballInd p 0 k) := by
    refine ⟨le_rfl, fun x hx ↦ ?_, fun x y hxy ↦ ?_⟩
    · rw [ballInd_eq_zero_iff]; simpa using hx
    · exact (isPadicSBAt_ballInd p 0 k).2.2 x y hxy
  rw [padicHaarInt_eq_padicIntAt p hsb]
  unfold padicIntAt
  have hsum : (∑ j : Fin (p ^ (k - k).toNat), ballInd p 0 k ((p : ℚ_[p]) ^ k * (j.1 : ℚ_[p]))) = 1 := by
    have hcard : p ^ (k - k).toNat = 1 := by simp
    let j0 : Fin (p ^ (k - k).toNat) := ⟨0, by rw [hcard]; exact Nat.zero_lt_one⟩
    rw [Finset.sum_eq_single j0]
    · rw [ballInd_eq_one_iff]
      simp [j0, zpow_nonneg (padic_p_pos p).le]
    · intro j _ hj
      exfalso; apply hj; apply Fin.ext
      have hj_lt : j.1 < 1 := hcard ▸ j.2
      exact Nat.lt_one_iff.mp hj_lt
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum, mul_one]

/-- **Exact Haar Measure of Any Coset `a + p^k ℤ_p`**: `μ(a + p^k ℤ_p) = p^{-k}`. -/
theorem padicHaarInt_ballInd (a : ℚ_[p]) (k : ℤ) :
    padicHaarInt p (ballInd p a k) = (p : ℂ) ^ (-k) := by
  have htr : ballInd p a k = fun x ↦ ballInd p 0 k (x + (-a)) := by
    funext x; simp [ballInd, sub_eq_add_neg]
  rw [htr, padicHaarInt_translate p (-a) (isPadicSchwartzBruhat_ballInd p 0 k)]
  exact padicHaarInt_ballInd_zero p k

/-- Normalization: `μ(ℤ_p) = 1`. -/
theorem padicHaarInt_padicIntInd :
    padicHaarInt p (ballInd p 0 0) = 1 := by
  simpa using padicHaarInt_ballInd_zero p 0

/-- Every Schwartz–Bruhat function `f` is a finite linear combination of ball indicators. -/
theorem isPadicSBAt_eq_sum_ballInd {R N : ℤ} {f : ℚ_[p] → ℂ} (hf : IsPadicSBAt p R N f)
    (x : ℚ_[p]) :
    f x = ∑ j : Fin (p ^ (N - R).toNat),
      f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) * ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N x := by
  set d := (N - R).toNat
  have hd_cast : (d : ℤ) = N - R := Int.toNat_of_nonneg (by linarith [hf.1])
  by_cases hx : ‖x‖ ≤ (p : ℝ) ^ (-R)
  · have hxr : ‖(p : ℚ_[p]) ^ (-R) * x‖ ≤ 1 := by
      rw [norm_mul, Padic.norm_p_zpow, neg_neg]
      calc (p : ℝ) ^ R * ‖x‖
          ≤ (p : ℝ) ^ R * (p : ℝ) ^ (-R) :=
            mul_le_mul_of_nonneg_left hx (zpow_nonneg (padic_p_pos p).le _)
        _ = 1 := by rw [← zpow_add₀ (padic_p_pos p).ne', add_neg_cancel, zpow_zero]
    let z : ℤ_[p] := ⟨(p : ℚ_[p]) ^ (-R) * x, hxr⟩
    let j₀ : Fin (p ^ d) := ⟨z.appr d, PadicInt.appr_lt z d⟩
    have hj₀ : ‖x - (p : ℚ_[p]) ^ R * (j₀.1 : ℚ_[p])‖ ≤ (p : ℝ) ^ (-N) := by
      have hspec : z - (j₀.1 : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ d} := PadicInt.appr_spec d z
      rw [Ideal.mem_span_singleton] at hspec
      obtain ⟨u, hu⟩ := hspec
      have hcoe : (z : ℚ_[p]) - (j₀.1 : ℚ_[p]) = (p : ℚ_[p]) ^ d * (u : ℚ_[p]) := by
        have h1 := congrArg (fun s : ℤ_[p] ↦ (s : ℚ_[p])) hu
        simpa [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast] using h1
      have hpow : (p : ℚ_[p]) ^ R * (p : ℚ_[p]) ^ d = (p : ℚ_[p]) ^ N := by
        rw [← zpow_natCast (p : ℚ_[p]) d, ← zpow_add₀ (padic_p_ne_zero p), hd_cast]
        congr 1; omega
      have hmul : x - (p : ℚ_[p]) ^ R * (j₀.1 : ℚ_[p]) = (p : ℚ_[p]) ^ N * (u : ℚ_[p]) := by
        have hz : (z : ℚ_[p]) = (p : ℚ_[p]) ^ (-R) * x := rfl
        rw [hz] at hcoe
        calc x - (p : ℚ_[p]) ^ R * (j₀.1 : ℚ_[p])
            = (p : ℚ_[p]) ^ R * ((p : ℚ_[p]) ^ (-R) * x - (j₀.1 : ℚ_[p])) := by
              rw [mul_sub, ← mul_assoc, ← zpow_add₀ (padic_p_ne_zero p), add_neg_cancel,
                zpow_zero, one_mul]
          _ = (p : ℚ_[p]) ^ R * ((p : ℚ_[p]) ^ d * (u : ℚ_[p])) := by rw [hcoe]
          _ = ((p : ℚ_[p]) ^ R * (p : ℚ_[p]) ^ d) * (u : ℚ_[p]) := by ring
          _ = (p : ℚ_[p]) ^ N * (u : ℚ_[p]) := by rw [hpow]
      rw [hmul, norm_mul, Padic.norm_p_zpow]
      calc (p : ℝ) ^ (-N) * ‖(u : ℚ_[p])‖
          ≤ (p : ℝ) ^ (-N) * 1 := mul_le_mul_of_nonneg_left u.2 (zpow_nonneg (padic_p_pos p).le _)
        _ = (p : ℝ) ^ (-N) := mul_one _
    rw [Finset.sum_eq_single j₀]
    · rw [(ballInd_eq_one_iff p _ _ _).mpr hj₀, mul_one]
      exact hf.2.2 x _ hj₀
    · intro j _ hne
      have h0 : ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N x = 0 := by
        rw [ballInd_eq_zero_iff]
        by_contra hle
        push Not at hle
        have hjj : ‖(p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]) - (p : ℚ_[p]) ^ R * (j₀.1 : ℚ_[p])‖ ≤
            (p : ℝ) ^ (-N) := by
          have : (p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]) - (p : ℚ_[p]) ^ R * (j₀.1 : ℚ_[p]) =
              (x - (p : ℚ_[p]) ^ R * (j₀.1 : ℚ_[p])) + -(x - (p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) := by
            ring
          rw [this]
          refine (Padic.nonarchimedean _ _).trans (max_le hj₀ ?_)
          rwa [norm_neg]
        have hfac :
            (p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]) - (p : ℚ_[p]) ^ R * (j₀.1 : ℚ_[p]) =
            (p : ℚ_[p]) ^ R * (((j.1 : ℤ) - (j₀.1 : ℤ) : ℤ) : ℚ_[p]) := by
          push_cast; ring
        rw [hfac, norm_mul, Padic.norm_p_zpow] at hjj
        have hnorm_d : ‖(((j.1 : ℤ) - (j₀.1 : ℤ) : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(d : ℤ)) := by
          have hposR : 0 < (p : ℝ) ^ (-R) := zpow_pos (padic_p_pos p) _
          have hmul_le : (p : ℝ) ^ (-R) * ‖(((j.1 : ℤ) - (j₀.1 : ℤ) : ℤ) : ℚ_[p])‖ ≤
              (p : ℝ) ^ (-R) * (p : ℝ) ^ (-(d : ℤ)) := by
            rw [← zpow_add₀ (padic_p_pos p).ne', hd_cast]
            convert hjj using 2; omega
          exact le_of_mul_le_mul_left hmul_le hposR
        have hdvd : ((p ^ d : ℤ)) ∣ ((j.1 : ℤ) - (j₀.1 : ℤ)) :=
          (Padic.norm_int_le_pow_iff_dvd _ d).mp hnorm_d
        have hlt1 : |(j.1 : ℤ) - (j₀.1 : ℤ)| < (p ^ d : ℤ) := by
          have h1 : (j.1 : ℤ) < (p ^ d : ℤ) := by exact_mod_cast j.2
          have h2 : (j₀.1 : ℤ) < (p ^ d : ℤ) := by exact_mod_cast j₀.2
          rw [abs_lt]; omega
        have hzero : (j.1 : ℤ) - (j₀.1 : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt1
        exact hne (Fin.ext (by omega))
      rw [h0, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · push Not at hx
    rw [hf.2.1 x hx]
    symm
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have h0 : ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N x = 0 := by
      rw [ballInd_eq_zero_iff]
      have hj : ‖(p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])‖ ≤ (p : ℝ) ^ (-R) := by
        rw [norm_mul, Padic.norm_p_zpow]
        have h1 : ‖(j.1 : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := p) (j.1 : ℤ)
        calc (p : ℝ) ^ (-R) * ‖(j.1 : ℚ_[p])‖
            ≤ (p : ℝ) ^ (-R) * 1 := mul_le_mul_of_nonneg_left h1 (zpow_nonneg (padic_p_pos p).le _)
          _ = (p : ℝ) ^ (-R) := mul_one _
      have hne : ‖x‖ ≠ ‖-((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]))‖ := by
        rw [norm_neg]; exact (hj.trans_lt hx).ne'
      have hsub : ‖x - (p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])‖ = ‖x‖ := by
        rw [sub_eq_add_neg, Padic.add_eq_max_of_ne hne, norm_neg, max_eq_left (hj.trans_lt hx).le]
      rw [hsub]
      have hle : (p : ℝ) ^ (-N) ≤ (p : ℝ) ^ (-R) :=
        zpow_le_zpow_right₀ (padic_one_lt_p p).le (by omega)
      exact hle.trans_lt hx
    rw [h0, mul_zero]

/-- Multiplying a Schwartz–Bruhat function by an additive character `x ↦ ψ_p(x * y)` preserves
the Schwartz–Bruhat space. -/
theorem isPadicSchwartzBruhat_mul_addChar {f : ℚ_[p] → ℂ} (hf : IsPadicSchwartzBruhat p f)
    (y : ℚ_[p]) :
    IsPadicSchwartzBruhat p (fun x ↦ f x * padicAddChar p (x * y)) := by
  rcases hf with ⟨R, N₀, hf₀⟩
  let N := max N₀ (-y.valuation)
  have hf : IsPadicSBAt p R N f := isPadicSBAt_mono p hf₀ le_rfl (le_max_left N₀ (-y.valuation))
  refine ⟨R, N, hf.1, fun x hx ↦ by simp [hf.2.1 x hx], fun x₁ x₂ h12 ↦ ?_⟩
  dsimp only
  rw [hf.2.2 x₁ x₂ h12]
  congr 1
  have hdiff_norm : ‖(x₁ - x₂) * y‖ ≤ 1 := by
    by_cases hy : y = 0
    · simp [hy]
    · rw [norm_mul, Padic.norm_eq_zpow_neg_valuation hy]
      have hleN : (p : ℝ) ^ (-N) ≤ (p : ℝ) ^ y.valuation :=
        zpow_le_zpow_right₀ (padic_one_lt_p p).le (by omega)
      calc ‖x₁ - x₂‖ * (p : ℝ) ^ (-y.valuation)
          ≤ (p : ℝ) ^ y.valuation * (p : ℝ) ^ (-y.valuation) :=
            mul_le_mul_of_nonneg_right (h12.trans hleN) (zpow_nonneg (padic_p_pos p).le _)
        _ = 1 := by rw [← zpow_add₀ (padic_p_pos p).ne', add_neg_cancel, zpow_zero]
  have h1 : padicAddChar p ((x₁ - x₂) * y) = 1 := padicAddChar_of_norm_le_one p hdiff_norm
  have h2 : x₁ * y = (x₁ - x₂) * y + x₂ * y := by ring
  rw [h2, padicAddChar_add, h1, one_mul]

/-- **Concrete Local $p$-adic Fourier Transform `ℱ_p`**:
`(padicFourier p f)(y) = ∫_{ℚ_p} f(x) · ψ_p(x · y) dx`. -/
def padicFourier (f : ℚ_[p] → ℂ) (y : ℚ_[p]) : ℂ :=
  padicHaarInt p (fun x ↦ f x * padicAddChar p (x * y))

theorem padicFourier_add {f g : ℚ_[p] → ℂ}
    (hf : IsPadicSchwartzBruhat p f) (hg : IsPadicSchwartzBruhat p g) (y : ℚ_[p]) :
    padicFourier p (fun x ↦ f x + g x) y = padicFourier p f y + padicFourier p g y := by
  unfold padicFourier
  have hrew : (fun x ↦ (f x + g x) * padicAddChar p (x * y)) =
      fun x ↦ f x * padicAddChar p (x * y) + g x * padicAddChar p (x * y) := by
    funext x; ring
  rw [hrew]
  exact padicHaarInt_add p (isPadicSchwartzBruhat_mul_addChar p hf y)
    (isPadicSchwartzBruhat_mul_addChar p hg y)

theorem padicFourier_smul (c : ℂ) {f : ℚ_[p] → ℂ} (hf : IsPadicSchwartzBruhat p f) (y : ℚ_[p]) :
    padicFourier p (fun x ↦ c * f x) y = c * padicFourier p f y := by
  unfold padicFourier
  have hrew : (fun x ↦ c * f x * padicAddChar p (x * y)) =
      fun x ↦ c * (f x * padicAddChar p (x * y)) := by
    funext x; ring
  rw [hrew]
  exact padicHaarInt_smul p c (isPadicSchwartzBruhat_mul_addChar p hf y)

/-- **Character Orthogonality on `p^k ℤ_p`**:
`ℱ_p(1_{p^k ℤ_p})(y) = p^{-k} * 1_{p^{-k} ℤ_p}(y)`. -/
theorem padicFourier_ballInd_zero (k : ℤ) (y : ℚ_[p]) :
    padicFourier p (ballInd p 0 k) y = (p : ℂ) ^ (-k) * ballInd p 0 (-k) y := by
  unfold padicFourier
  by_cases hy : ‖y‖ ≤ (p : ℝ) ^ k
  · have hball : ballInd p 0 (-k) y = 1 := by
      rw [ballInd_eq_one_iff]; simpa using hy
    rw [hball, mul_one]
    have hcongr : ∀ x : ℚ_[p], ballInd p 0 k x * padicAddChar p (x * y) = ballInd p 0 k x := by
      intro x
      by_cases hx : ‖x‖ ≤ (p : ℝ) ^ (-k)
      · have hxy : ‖x * y‖ ≤ 1 := by
          rw [norm_mul]
          calc ‖x‖ * ‖y‖
              ≤ (p : ℝ) ^ (-k) * (p : ℝ) ^ k :=
                mul_le_mul hx hy (norm_nonneg y) (zpow_nonneg (padic_p_pos p).le _)
            _ = 1 := by rw [← zpow_add₀ (padic_p_pos p).ne', neg_add_cancel, zpow_zero]
        rw [padicAddChar_of_norm_le_one p hxy, mul_one]
      · have h0 : ballInd p 0 k x = 0 := by
          rw [ballInd_eq_zero_iff]; simpa [not_le] using hx
        rw [h0, zero_mul]
    rw [padicHaarInt_congr p hcongr]
    exact padicHaarInt_ballInd_zero p k
  · push Not at hy
    have hball : ballInd p 0 (-k) y = 0 := by
      rw [ballInd_eq_zero_iff]; simpa using hy
    rw [hball, mul_zero]
    have hy_ne : y ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hy
      exact not_lt_of_ge (zpow_nonneg (padic_p_pos p).le k) hy
    let t : ℚ_[p] := (p : ℚ_[p])⁻¹ * y⁻¹
    have ht_norm : ‖t‖ ≤ (p : ℝ) ^ (-k) := by
      have hval : -y.valuation > k := by
        rw [Padic.norm_eq_zpow_neg_valuation hy_ne] at hy
        exact (zpow_lt_zpow_iff_right₀ (padic_one_lt_p p)).mp hy
      rw [show ‖t‖ = ‖(p : ℚ_[p])⁻¹‖ * ‖y⁻¹‖ from norm_mul _ _,
        norm_inv, norm_inv, Padic.norm_p, inv_inv, Padic.norm_eq_zpow_neg_valuation hy_ne,
        ← zpow_neg, neg_neg,
        show (p : ℝ) * (p : ℝ) ^ y.valuation = (p : ℝ) ^ (1 + y.valuation) by
          rw [zpow_add₀ (padic_p_pos p).ne', zpow_one]]
      exact zpow_le_zpow_right₀ (padic_one_lt_p p).le (by omega)
    have hty : t * y = (p : ℚ_[p])⁻¹ := by
      dsimp only [t]; rw [mul_assoc, inv_mul_cancel₀ hy_ne, mul_one]
    set I := padicHaarInt p (fun x ↦ ballInd p 0 k x * padicAddChar p (x * y))
    have hsb := isPadicSchwartzBruhat_mul_addChar p (isPadicSchwartzBruhat_ballInd p 0 k) y
    have htr := padicHaarInt_translate p t hsb
    have hrew : (fun x ↦ ballInd p 0 k (x + t) * padicAddChar p ((x + t) * y)) =
        fun x ↦ padicAddChar p (p : ℚ_[p])⁻¹ * (ballInd p 0 k x * padicAddChar p (x * y)) := by
      funext x
      have hb : ballInd p 0 k (x + t) = ballInd p 0 k x := by
        rw [ballInd_translate, zero_sub]
        have hnt : ‖-t - 0‖ ≤ (p : ℝ) ^ (-k) := by simpa using ht_norm
        exact congrFun (ballInd_eq_of_norm_sub_le p hnt) x
      rw [hb, add_mul, padicAddChar_add, hty]
      ring
    rw [hrew, padicHaarInt_smul p _ hsb] at htr
    have hzero : (padicAddChar p (p : ℚ_[p])⁻¹ - 1) * I = 0 := by
      linear_combination htr
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr (padicAddChar_inv_prime_ne_one p))

/-- **EXACT FOURIER TRANSFORM OF BALL INDICATORS**:
`ℱ_p(1_{a + p^k ℤ_p})(y) = p^{-k} · ψ_p(a · y) · 1_{p^{-k} ℤ_p}(y)`. -/
theorem padicFourier_ballInd (a : ℚ_[p]) (k : ℤ) (y : ℚ_[p]) :
    padicFourier p (ballInd p a k) y =
      (p : ℂ) ^ (-k) * padicAddChar p (a * y) * ballInd p 0 (-k) y := by
  unfold padicFourier
  have hsb := isPadicSchwartzBruhat_mul_addChar p (isPadicSchwartzBruhat_ballInd p a k) y
  rw [← padicHaarInt_translate p a hsb]
  have hrew : (fun x ↦ ballInd p a k (x + a) * padicAddChar p ((x + a) * y)) =
      fun x ↦ padicAddChar p (a * y) * (ballInd p 0 k x * padicAddChar p (x * y)) := by
    funext x
    have hb : ballInd p a k (x + a) = ballInd p 0 k x := by
      simp [ballInd]
    rw [hb, add_mul, padicAddChar_add]
    ring
  rw [hrew, padicHaarInt_smul p _ (isPadicSchwartzBruhat_mul_addChar p
    (isPadicSchwartzBruhat_ballInd p 0 k) y)]
  change padicAddChar p (a * y) * padicFourier p (ballInd p 0 k) y = _
  rw [padicFourier_ballInd_zero p k y]
  ring

/-- **EXACT SELF-DUALITY OF `1_{ℤ_p}`**:
`ℱ_p(1_{ℤ_p}) = 1_{ℤ_p}`! -/
theorem padicFourier_padicIntInd_selfDual :
    padicFourier p (ballInd p 0 0) = ballInd p 0 0 := by
  funext y
  rw [padicFourier_ballInd p 0 0 y]
  simp

/-- Double Fourier transform of a ball indicator: `ℱ_p(ℱ_p(1_{a + p^k ℤ_p}))(x) = 1_{a + p^k ℤ_p}(-x)`. -/
theorem padicFourier_padicFourier_ballInd (a : ℚ_[p]) (k : ℤ) (x : ℚ_[p]) :
    padicFourier p (padicFourier p (ballInd p a k)) x = ballInd p a k (-x) := by
  have h1 : padicFourier p (ballInd p a k) =
      fun y ↦ (p : ℂ) ^ (-k) * (ballInd p 0 (-k) y * padicAddChar p (y * a)) := by
    funext y
    rw [padicFourier_ballInd p a k y, mul_comm y a]
    ring
  rw [h1]
  unfold padicFourier
  have hrew :
      (fun y ↦ (p : ℂ) ^ (-k) * (ballInd p 0 (-k) y * padicAddChar p (y * a)) *
        padicAddChar p (y * x)) =
      fun y ↦ (p : ℂ) ^ (-k) * (ballInd p 0 (-k) y * padicAddChar p (y * (a + x))) := by
    funext y
    rw [mul_add, padicAddChar_add]
    ring
  rw [hrew, padicHaarInt_smul p _ (isPadicSchwartzBruhat_mul_addChar p
    (isPadicSchwartzBruhat_ballInd p 0 (-k)) (a + x))]
  change (p : ℂ) ^ (-k) * padicFourier p (ballInd p 0 (-k)) (a + x) = _
  rw [padicFourier_ballInd_zero p (-k) (a + x), neg_neg, ← mul_assoc,
    ← zpow_add₀ (padic_p_complex_ne_zero p), neg_add_cancel, zpow_zero, one_mul]
  unfold ballInd
  have hnorm : ‖a + x - 0‖ = ‖-x - a‖ := by
    rw [sub_zero, show -x - a = -(a + x) by ring, norm_neg]
  rw [hnorm]

/-- `ℱ_p` maps the $p$-adic Schwartz–Bruhat space into itself. -/
theorem isPadicSchwartzBruhat_padicFourier {f : ℚ_[p] → ℂ} (hf : IsPadicSchwartzBruhat p f) :
    IsPadicSchwartzBruhat p (padicFourier p f) := by
  rcases hf with ⟨R, N, hsb⟩
  have hf_eq : f = fun x ↦ ∑ j : Fin (p ^ (N - R).toNat),
      f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) *
        ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N x :=
    funext (isPadicSBAt_eq_sum_ballInd p hsb)
  have hFf_eq : padicFourier p f = fun y ↦ ∑ j : Fin (p ^ (N - R).toNat),
      (f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) * (p : ℂ) ^ (-N)) *
        (ballInd p 0 (-N) y * padicAddChar p (y * ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])))) := by
    funext y
    conv_lhs => rw [hf_eq]
    unfold padicFourier
    have hmul : (fun x ↦ (∑ j : Fin (p ^ (N - R).toNat),
        f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) *
          ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N x) * padicAddChar p (x * y)) =
        fun x ↦ ∑ j : Fin (p ^ (N - R).toNat),
          f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) *
            (ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N x * padicAddChar p (x * y)) := by
      funext x; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hmul, padicHaarInt_finset_sum p Finset.univ _ (fun j _ ↦
      isPadicSchwartzBruhat_smul p _ (isPadicSchwartzBruhat_mul_addChar p
        (isPadicSchwartzBruhat_ballInd p _ N) y))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [padicHaarInt_smul p _ (isPadicSchwartzBruhat_mul_addChar p
      (isPadicSchwartzBruhat_ballInd p _ N) y)]
    change f _ * padicFourier p (ballInd p _ N) y = _
    rw [padicFourier_ballInd p _ N y, mul_comm y _]
    ring
  rw [hFf_eq]
  -- Finite sum of Schwartz–Bruhat functions
  have hterm : ∀ j : Fin (p ^ (N - R).toNat),
      IsPadicSchwartzBruhat p (fun y ↦
        (f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) * (p : ℂ) ^ (-N)) *
          (ballInd p 0 (-N) y * padicAddChar p (y * ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]))))) :=
    fun j ↦ isPadicSchwartzBruhat_smul p _ (isPadicSchwartzBruhat_mul_addChar p
      (isPadicSchwartzBruhat_ballInd p 0 (-N)) _)
  suffices ∀ s : Finset (Fin (p ^ (N - R).toNat)),
      IsPadicSchwartzBruhat p (fun y ↦ ∑ j ∈ s,
        (f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) * (p : ℂ) ^ (-N)) *
          (ballInd p 0 (-N) y * padicAddChar p (y * ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]))))) from
    this Finset.univ
  intro s
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, le_rfl, fun _ _ ↦ by simp, fun _ _ _ ↦ by simp⟩
  | insert a s ha ih =>
    simpa [Finset.sum_insert ha] using isPadicSchwartzBruhat_add p (hterm a) ih

/-- **EXACT $p$-ADIC FOURIER INVERSION THEOREM**:
for every Schwartz–Bruhat function `f : ℚ_[p] → ℂ` and every `x : ℚ_[p]`,
`ℱ_p(ℱ_p f)(x) = f(-x)`! -/
theorem padicFourier_inversion {f : ℚ_[p] → ℂ} (hf : IsPadicSchwartzBruhat p f) (x : ℚ_[p]) :
    padicFourier p (padicFourier p f) x = f (-x) := by
  rcases hf with ⟨R, N, hsb⟩
  have hf_eq : f = fun u ↦ ∑ j : Fin (p ^ (N - R).toNat),
      f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) *
        ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N u :=
    funext (isPadicSBAt_eq_sum_ballInd p hsb)
  have hFf_eq : padicFourier p f = fun y ↦ ∑ j : Fin (p ^ (N - R).toNat),
      f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) *
        padicFourier p (ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N) y := by
    funext y
    conv_lhs => rw [hf_eq]
    unfold padicFourier
    have hmul : (fun u ↦ (∑ j : Fin (p ^ (N - R).toNat),
        f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) *
          ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N u) * padicAddChar p (u * y)) =
        fun u ↦ ∑ j : Fin (p ^ (N - R).toNat),
          f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) *
            (ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N u * padicAddChar p (u * y)) := by
      funext u; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hmul, padicHaarInt_finset_sum p Finset.univ _ (fun j _ ↦
      isPadicSchwartzBruhat_smul p _ (isPadicSchwartzBruhat_mul_addChar p
        (isPadicSchwartzBruhat_ballInd p _ N) y))]
    refine Finset.sum_congr rfl fun j _ ↦
      padicHaarInt_smul p _ (isPadicSchwartzBruhat_mul_addChar p
        (isPadicSchwartzBruhat_ballInd p _ N) y)
  have hF_ball_sb : ∀ j : Fin (p ^ (N - R).toNat),
      IsPadicSchwartzBruhat p (padicFourier p (ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N)) :=
    fun j ↦ isPadicSchwartzBruhat_padicFourier p (isPadicSchwartzBruhat_ballInd p _ N)
  conv_lhs => rw [hFf_eq]
  change padicHaarInt p (fun y ↦
    (∑ j : Fin (p ^ (N - R).toNat),
      f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) *
        padicFourier p (ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N) y) *
      padicAddChar p (y * x)) = _
  have hmul2 : (fun y ↦ (∑ j : Fin (p ^ (N - R).toNat),
      f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) *
        padicFourier p (ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N) y) *
        padicAddChar p (y * x)) =
      fun y ↦ ∑ j : Fin (p ^ (N - R).toNat),
        f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) *
          (padicFourier p (ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N) y *
            padicAddChar p (y * x)) := by
    funext y; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hmul2, padicHaarInt_finset_sum p Finset.univ _ (fun j _ ↦
    isPadicSchwartzBruhat_smul p _ (isPadicSchwartzBruhat_mul_addChar p (hF_ball_sb j) x))]
  calc ∑ j : Fin (p ^ (N - R).toNat),
        padicHaarInt p (fun y ↦ f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) *
          (padicFourier p (ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N) y *
            padicAddChar p (y * x)))
      = ∑ j : Fin (p ^ (N - R).toNat),
          f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) *
            padicFourier p (padicFourier p (ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N)) x := by
        refine Finset.sum_congr rfl fun j _ ↦
          padicHaarInt_smul p _ (isPadicSchwartzBruhat_mul_addChar p (hF_ball_sb j) x)
    _ = ∑ j : Fin (p ^ (N - R).toNat),
          f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) *
            ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N (-x) := by
        refine Finset.sum_congr rfl fun j _ ↦ by rw [padicFourier_padicFourier_ballInd]
    _ = f (-x) := (isPadicSBAt_eq_sum_ballInd p hsb (-x)).symm

/-- For even Schwartz–Bruhat functions (`f(-x) = f(x)`), `ℱ_p` is an involution: `ℱ_p(ℱ_p f) = f`. -/
theorem padicFourier_involutive_of_even {f : ℚ_[p] → ℂ} (hf : IsPadicSchwartzBruhat p f)
    (heven : ∀ x, f (-x) = f x) :
    padicFourier p (padicFourier p f) = f := by
  funext x
  rw [padicFourier_inversion p hf x, heven x]

end LocalPadicFourier

/-! ## Section 4: Concrete Adelic Poisson Summation on `𝔸_ℚ` (`∑'_{q : ℚ} Φ(q) = ∑'_{q : ℚ} Φ̂(q)`) -/

section AdelicPoissonSummation

/-- Archimedean Gaussian test function `Φ_∞(x) = exp(-π t x²)` on `ℝ`. -/
def archGaussian (t : ℝ) (x : ℝ) : ℂ :=
  Complex.exp (-Real.pi * (t : ℂ) * (x : ℂ) ^ 2)

/-- Exact Archimedean Fourier transform of `archGaussian t` (`t > 0`):
`𝓕(x ↦ exp(-π t x²))(y) = t^{-1/2} exp(-π y² / t)`. -/
theorem fourier_archGaussian {t : ℝ} (ht : 0 < t) (y : ℝ) :
    𝓕 (archGaussian t) y =
      (t : ℂ) ^ (-(1 / 2 : ℂ)) * Complex.exp (-Real.pi / (t : ℂ) * (y : ℂ) ^ 2) := by
  have htC : 0 < ((t : ℂ)).re := by simpa using ht
  have hF := congrFun (fourier_gaussian_pi htC) y
  change 𝓕 (archGaussian t) y = _
  rw [show archGaussian t = fun x : ℝ ↦ Complex.exp (-Real.pi * (t : ℂ) * (x : ℂ) ^ 2) from rfl, hF]
  congr 1
  rw [one_div, Complex.cpow_neg]

/-- Shifted/scaled Archimedean Gaussian Poisson summation directly from Mathlib's
`Real.tsum_eq_tsum_fourier_of_rpow_decay`:
for every `t > 0`, `M > 0`, and `r₀ : ℝ`,
`∑'_{n : ℤ} exp(-π t (r₀ + M n)²) = ∑'_{n : ℤ} 𝓕(archGaussian t)(n / M) * M⁻¹ * exp(2πi r₀ (n / M))`. -/
theorem archGaussian_poisson_shifted {t M : ℝ} (ht : 0 < t) (hM : 0 < M) (r₀ : ℝ) :
    (∑' n : ℤ, archGaussian t (r₀ + M * (n : ℝ))) =
    ∑' n : ℤ, 𝓕 (archGaussian t) ((n : ℝ) / M) * (M : ℂ)⁻¹ *
      Complex.exp (2 * Real.pi * Complex.I * (r₀ : ℂ) * ((n : ℝ) / M : ℂ)) := by
  let a : ℝ := t * M ^ 2
  have ha : 0 < a := mul_pos ht (sq_pos_of_pos hM)
  have haC : 0 < (a : ℂ).re := by simpa using ha
  let f : ℝ → ℂ := fun u ↦ Complex.exp (-Real.pi * (a : ℂ) * (u : ℂ) ^ 2)
  have hFf : 𝓕 f = fun y : ℝ ↦
      1 / (a : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-Real.pi / (a : ℂ) * (y : ℂ) ^ 2) :=
    fourier_gaussian_pi haC
  have h1 : 0 < (Real.pi * (a : ℂ)).re := by
    rw [Complex.re_ofReal_mul]; exact mul_pos Real.pi_pos haC
  have h2 : 0 < (Real.pi / (a : ℂ)).re := by
    have : (Real.pi : ℂ) / (a : ℂ) = ((Real.pi / a : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
    exact div_pos Real.pi_pos ha
  have hf_bd : f =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-2 : ℝ)) := by
    have h0 := (isLittleO_exp_neg_mul_sq_cocompact h1 (-2)).isBigO
    refine h0.congr' (Eventually.of_forall fun x ↦ ?_) EventuallyEq.rfl
    dsimp only [f]
    congr 1; ring
  have hFf_bd : (𝓕 f) =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-2 : ℝ)) := by
    rw [hFf]
    have h0 := ((isLittleO_exp_neg_mul_sq_cocompact h2 (-2)).isBigO).const_mul_left
      (1 / (a : ℂ) ^ (1 / 2 : ℂ))
    refine h0.congr' (Eventually.of_forall fun x ↦ ?_) EventuallyEq.rfl
    dsimp only
    rw [neg_div]
  have hcont : Continuous f := by
    dsimp only [f]
    fun_prop
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay hcont one_lt_two hf_bd hFf_bd (r₀ / M)
  have hpow : (1 : ℂ) / (a : ℂ) ^ (1 / 2 : ℂ) = (t : ℂ) ^ (-(1 / 2 : ℂ)) * (M : ℂ)⁻¹ := by
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    have ha_real : (a : ℂ) ^ (1 / 2 : ℂ) = (((t * M ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [hhalf, ← Complex.ofReal_cpow ha.le]
    have hr : (t * M ^ 2) ^ (1 / 2 : ℝ) = t ^ (1 / 2 : ℝ) * M := by
      rw [Real.mul_rpow ht.le (sq_nonneg M), ← Real.rpow_natCast M 2, ← Real.rpow_mul hM.le]
      norm_num
    rw [ha_real, hr]
    have ht_pow : ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ (1 / 2 : ℂ) := by
      rw [hhalf, ← Complex.ofReal_cpow ht.le]
    rw [Complex.ofReal_mul, ht_pow, one_div, mul_inv, Complex.cpow_neg]
  calc ∑' n : ℤ, archGaussian t (r₀ + M * (n : ℝ))
      = ∑' n : ℤ, f (r₀ / M + (n : ℝ)) := by
        refine tsum_congr fun n ↦ ?_
        dsimp only [archGaussian, f, a]
        congr 1
        have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
        push_cast
        field_simp [hMC]
    _ = ∑' n : ℤ, 𝓕 f (n : ℝ) * fourier n ((r₀ / M : ℝ) : UnitAddCircle) := hP
    _ = ∑' n : ℤ, 𝓕 (archGaussian t) ((n : ℝ) / M) * (M : ℂ)⁻¹ *
          Complex.exp (2 * Real.pi * Complex.I * (r₀ : ℂ) * ((n : ℝ) / M : ℂ)) := by
        refine tsum_congr fun n ↦ ?_
        rw [hFf, hpow, fourier_archGaussian ht, fourier_coe_apply]
        dsimp only
        have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
        have hexp1 :
            -Real.pi / (a : ℂ) * ((n : ℝ) : ℂ) ^ 2 =
            -Real.pi / (t : ℂ) * (((n : ℝ) / M : ℝ) : ℂ) ^ 2 := by
          dsimp only [a]
          have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
          push_cast
          field_simp [hMC, htC]
        have hexp2 :
            2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((r₀ / M : ℝ) : ℂ) / ((1 : ℝ) : ℂ) =
            2 * (Real.pi : ℂ) * Complex.I * (r₀ : ℂ) * (((n : ℝ) : ℂ) / (M : ℂ)) := by
          push_cast
          field_simp [hMC]
        rw [hexp1, hexp2]
        ring

/-- A finite-level adelic congruence box `∏_p (a_p + p^{k_p} ℤ_p) ⊆ 𝔸_{ℚ,f}`:
arbitrary levels `k_p ∈ ℤ` and centers `a_p ∈ ℚ_[p]` on a finite set of primes `S`,
and spherical (`k_p = 0`, `a_p ∈ ℤ_[p]`) outside `S`. -/
structure AdelicBox where
  S : Finset Nat.Primes
  level : Nat.Primes → ℤ
  center : (p : Nat.Primes) → ℚ_[p.1]
  level_eq_zero : ∀ p : Nat.Primes, p ∉ S → level p = 0
  center_mem_int : ∀ p : Nat.Primes, p ∉ S → ‖center p‖ ≤ 1

/-- The canonical spherical box `∏_p ℤ_p` (`S = ∅`, `k_p = 0`, `a_p = 0`). -/
def AdelicBox.spherical : AdelicBox where
  S := ∅
  level := fun _ ↦ 0
  center := fun _ ↦ 0
  level_eq_zero := fun _ _ ↦ rfl
  center_mem_int := fun _ _ ↦ by simp

/-- The positive rational scale `M = ∏_{p ∈ B.S} p^{k_p} ∈ ℚ_{>0}` attached to an `AdelicBox`. -/
def AdelicBox.scale (B : AdelicBox) : ℚ :=
  ∏ p ∈ B.S, (p.1 : ℚ) ^ (B.level p)

lemma AdelicBox.scale_pos (B : AdelicBox) : (0 : ℚ) < B.scale := by
  unfold AdelicBox.scale
  refine Finset.prod_pos fun p _ ↦ zpow_pos (by exact_mod_cast p.2.pos) _

lemma AdelicBox.scale_ne_zero (B : AdelicBox) : B.scale ≠ 0 := B.scale_pos.ne'

lemma AdelicBox.scale_real_pos (B : AdelicBox) : (0 : ℝ) < (B.scale : ℝ) := by
  exact_mod_cast B.scale_pos

@[simp]
lemma AdelicBox.spherical_scale : AdelicBox.spherical.scale = 1 := by
  simp [AdelicBox.scale, AdelicBox.spherical]

/-- At every prime `ℓ`, the `ℓ`-adic norm of `B.scale` equals `ℓ^{-k_ℓ}`! -/
theorem AdelicBox.norm_scale (B : AdelicBox) (ℓ : Nat.Primes) :
    ‖(B.scale : ℚ_[ℓ.1])‖ = (ℓ.1 : ℝ) ^ (-B.level ℓ) := by
  unfold AdelicBox.scale
  have hcast : ((∏ p ∈ B.S, (p.1 : ℚ) ^ (B.level p) : ℚ) : ℚ_[ℓ.1]) =
      ∏ p ∈ B.S, (p.1 : ℚ_[ℓ.1]) ^ (B.level p) := by
    push_cast; rfl
  rw [hcast, norm_prod]
  have hother : ∀ p : Nat.Primes, p ≠ ℓ → ‖(p.1 : ℚ_[ℓ.1]) ^ (B.level p)‖ = 1 := by
    intro p hne
    rw [norm_zpow]
    have hcop : ℓ.1.Coprime p.1 := (ℓ.2.coprime_iff_not_dvd).mpr fun hdvd ↦
      hne (Subtype.ext ((Nat.prime_dvd_prime_iff_eq ℓ.2 p.2).mp hdvd).symm)
    rw [Padic.norm_natCast_eq_one_iff.mpr hcop, one_zpow]
  by_cases hℓ : ℓ ∈ B.S
  · rw [Finset.prod_eq_single ℓ]
    · exact Padic.norm_p_zpow (p := ℓ.1) (B.level ℓ)
    · intro p _ hp; exact hother p hp
    · intro h; exact absurd hℓ h
  · rw [B.level_eq_zero ℓ hℓ, neg_zero, zpow_zero]
    refine Finset.prod_eq_one fun p hp ↦ hother p (fun h ↦ hℓ (h ▸ hp))

/-- **Strong Approximation for `ℚ` via `padicFracPart`**:
for every `AdelicBox` `B`, there exists a rational center `r₀ : ℚ` lying inside every local
coset `B.center p + p^{B.level p} ℤ_p` simultaneously! -/
theorem exists_rat_center_adelicBox (B : AdelicBox) :
    ∃ r₀ : ℚ, ∀ p : Nat.Primes,
      ‖(r₀ : ℚ_[p.1]) - B.center p‖ ≤ (p.1 : ℝ) ^ (-B.level p) := by
  classical
  let M : ℚ := B.scale
  let b₀ : ℚ := ∑ p ∈ B.S, padicFracPart p.1 (B.center p / (M : ℚ_[p.1]))
  refine ⟨M * b₀, fun ℓ ↦ ?_⟩
  have hMℓ_ne : (M : ℚ_[ℓ.1]) ≠ 0 := by exact_mod_cast B.scale_ne_zero
  have hMℓ_norm : ‖(M : ℚ_[ℓ.1])‖ = (ℓ.1 : ℝ) ^ (-B.level ℓ) := B.norm_scale ℓ
  by_cases hℓ : ℓ ∈ B.S
  · have hdiv_norm : ‖(b₀ : ℚ_[ℓ.1]) - B.center ℓ / (M : ℚ_[ℓ.1])‖ ≤ 1 := by
      have hsplit :
          (b₀ : ℚ_[ℓ.1]) - B.center ℓ / (M : ℚ_[ℓ.1]) =
          -((B.center ℓ / (M : ℚ_[ℓ.1])) -
              (padicFracPart ℓ.1 (B.center ℓ / (M : ℚ_[ℓ.1])) : ℚ_[ℓ.1])) +
            ∑ p ∈ B.S.erase ℓ, (padicFracPart p.1 (B.center p / (M : ℚ_[p.1])) : ℚ_[ℓ.1]) := by
        dsimp only [b₀]
        rw [← Finset.add_sum_erase _ _ hℓ]
        push_cast; ring
      rw [hsplit]
      refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
      · rw [norm_neg]; exact norm_sub_padicFracPart_le_one ℓ.1 _
      · refine norm_sum_padic_le_one _ _ fun p hp ↦ ?_
        have hne : ℓ.1 ≠ p.1 := fun h ↦ (Finset.ne_of_mem_erase hp) (Subtype.ext h.symm)
        exact norm_padicFracPart_other_prime p.1 hne _
    have hfac :
        ((M * b₀ : ℚ) : ℚ_[ℓ.1]) - B.center ℓ =
        (M : ℚ_[ℓ.1]) * ((b₀ : ℚ_[ℓ.1]) - B.center ℓ / (M : ℚ_[ℓ.1])) := by
      push_cast
      rw [mul_sub, mul_div_cancel₀ _ hMℓ_ne]
    rw [hfac, norm_mul, hMℓ_norm]
    calc (ℓ.1 : ℝ) ^ (-B.level ℓ) * ‖(b₀ : ℚ_[ℓ.1]) - B.center ℓ / (M : ℚ_[ℓ.1])‖
        ≤ (ℓ.1 : ℝ) ^ (-B.level ℓ) * 1 :=
          mul_le_mul_of_nonneg_left hdiv_norm (zpow_nonneg (padic_p_pos ℓ.1).le _)
      _ = (ℓ.1 : ℝ) ^ (-B.level ℓ) := mul_one _
  · have hb₀_norm : ‖(b₀ : ℚ_[ℓ.1])‖ ≤ 1 := by
      have hcast : (b₀ : ℚ_[ℓ.1]) =
          ∑ p ∈ B.S, (padicFracPart p.1 (B.center p / (M : ℚ_[p.1])) : ℚ_[ℓ.1]) := by
        dsimp only [b₀]; push_cast; rfl
      rw [hcast]
      refine norm_sum_padic_le_one _ _ fun p hp ↦ ?_
      have hne : ℓ.1 ≠ p.1 := fun h ↦ hℓ (Subtype.ext h ▸ hp)
      exact norm_padicFracPart_other_prime p.1 hne _
    have hM1 : ‖(M : ℚ_[ℓ.1])‖ = 1 := by
      rw [hMℓ_norm, B.level_eq_zero ℓ hℓ, neg_zero, zpow_zero]
    have hMb : ‖((M * b₀ : ℚ) : ℚ_[ℓ.1])‖ ≤ 1 := by
      push_cast; rw [norm_mul, hM1, one_mul]; exact hb₀_norm
    rw [B.level_eq_zero ℓ hℓ, neg_zero, zpow_zero, sub_eq_add_neg]
    refine (Padic.nonarchimedean _ _).trans (max_le hMb ?_)
    rw [norm_neg]
    exact B.center_mem_int ℓ hℓ

/-- Global factorizable Gaussian Schwartz–Bruhat test function on `𝔸_ℚ`:
`Φ(x_∞, (x_p)) = exp(-π t x_∞²) * ∏'_p 1_{a_p + p^{k_p} ℤ_p}(x_p)`. -/
def adelicGaussianTest (t : ℝ) (B : AdelicBox) (x : RatAdele) : ℂ :=
  archGaussian t x.1 * ∏ᶠ p : Nat.Primes, ballInd p.1 (B.center p) (B.level p) (x.2 p)

/-- Global adelic Fourier transform `Φ̂` of `adelicGaussianTest t B` on `𝔸_ℚ`:
`Φ̂(y_∞, (y_p)) = 𝓕(archGaussian t)(y_∞) * ∏'_p ℱ_p(1_{a_p + p^{k_p} ℤ_p})(y_p)`. -/
def adelicGaussianFourier (t : ℝ) (B : AdelicBox) (y : RatAdele) : ℂ :=
  𝓕 (archGaussian t) y.1 *
    ∏ᶠ p : Nat.Primes, padicFourier p.1 (ballInd p.1 (B.center p) (B.level p)) (y.2 p)

lemma hasFiniteMulSupport_adelicBox_ballInd (B : AdelicBox) (x : RatFinAdele) :
    (fun p : Nat.Primes ↦ ballInd p.1 (B.center p) (B.level p) (x p)).HasFiniteMulSupport := by
  have hfin : {p : Nat.Primes | x p ∉ PadicInt.subring p.1}.Finite :=
    Filter.eventually_cofinite.mp x.2
  refine (B.S.finite_toSet.union hfin).subset ?_
  intro p hp
  simp only [Function.mem_mulSupport, ne_eq] at hp
  by_contra hnot
  have hpS : p ∉ B.S := fun h ↦ hnot (Or.inl h)
  have hpx : ‖x p‖ ≤ 1 := by
    by_contra hx; exact hnot (Or.inr hx)
  have h1 : ballInd p.1 (B.center p) (B.level p) (x p) = 1 := by
    rw [ballInd_eq_one_iff, B.level_eq_zero p hpS, neg_zero, zpow_zero, sub_eq_add_neg]
    refine (Padic.nonarchimedean _ _).trans (max_le hpx ?_)
    rw [norm_neg]; exact B.center_mem_int p hpS
  exact hp h1

lemma hasFiniteMulSupport_adelicBox_fourier (B : AdelicBox) (y : RatFinAdele) :
    (fun p : Nat.Primes ↦
      padicFourier p.1 (ballInd p.1 (B.center p) (B.level p)) (y p)).HasFiniteMulSupport := by
  have hfin : {p : Nat.Primes | y p ∉ PadicInt.subring p.1}.Finite :=
    Filter.eventually_cofinite.mp y.2
  refine (B.S.finite_toSet.union hfin).subset ?_
  intro p hp
  simp only [Function.mem_mulSupport, ne_eq] at hp
  by_contra hnot
  have hpS : p ∉ B.S := fun h ↦ hnot (Or.inl h)
  have hpy : ‖y p‖ ≤ 1 := by
    by_contra hy; exact hnot (Or.inr hy)
  have h1 : padicFourier p.1 (ballInd p.1 (B.center p) (B.level p)) (y p) = 1 := by
    rw [padicFourier_ballInd, B.level_eq_zero p hpS, neg_zero, zpow_zero, one_mul]
    have hmul : ‖B.center p * y p‖ ≤ 1 := by
      rw [norm_mul]
      exact mul_le_one₀ (B.center_mem_int p hpS) (norm_nonneg _) hpy
    rw [padicAddChar_of_norm_le_one p.1 hmul, one_mul, ballInd_eq_one_iff]
    simpa using hpy
  exact hp h1

private lemma finprod_eq_zero_of_exists {α : Type*} {f : α → ℂ}
    (hf : f.HasFiniteMulSupport) {a₀ : α} (h0 : f a₀ = 0) :
    ∏ᶠ a : α, f a = 0 := by
  classical
  have hf' : (Function.mulSupport f).Finite := hf
  rw [finprod_eq_prod_of_mulSupport_subset f (s := hf'.toFinset) (by simp)]
  have hmem : a₀ ∈ hf'.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, h0]
    exact zero_ne_one
  exact Finset.prod_eq_zero hmem h0

private lemma tsum_eq_tsum_of_injective_support {α β : Type*} (g : β → ℂ) {e : α → β}
    (he : Function.Injective e) (hsupp : ∀ b, b ∉ Set.range e → g b = 0) :
    (∑' b : β, g b) = ∑' a : α, g (e a) := by
  rw [← tsum_subtype_eq_of_support_subset (s := Set.range e) (fun b hb ↦ by
    by_contra hnot; exact hb (hsupp b hnot))]
  exact tsum_range g he

/-- **UNCONDITIONAL CONCRETE ADELIC POISSON SUMMATION ON `𝔸_ℚ`** (`0` assumptions):
for EVERY `t > 0` and EVERY finite-level congruence box `B : AdelicBox`
(`∏_p (a_p + p^{k_p} ℤ_p)` with arbitrary `k_p ∈ ℤ`, `a_p ∈ ℚ_[p]`),
`∑'_{q : ℚ} Φ(q) = ∑'_{q : ℚ} Φ̂(q)`! -/
theorem adelic_poisson_summation_rat_gaussian {t : ℝ} (ht : 0 < t) (B : AdelicBox) :
    (∑' q : ℚ, adelicGaussianTest t B (diagRatAdele q)) =
      ∑' q : ℚ, adelicGaussianFourier t B (diagRatAdele q) := by
  obtain ⟨r₀, hr₀⟩ := exists_rat_center_adelicBox B
  let M : ℚ := B.scale
  have hM_ne : M ≠ 0 := B.scale_ne_zero
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := B.scale_real_pos
  -- Step 1: LHS reduction to `∑'_{n : ℤ} archGaussian t (r₀ + M * n)`
  let embL : ℤ → ℚ := fun n ↦ r₀ + M * (n : ℚ)
  have hembL_inj : Function.Injective embL := by
    intro n₁ n₂ h
    have h1 : M * (n₁ : ℚ) = M * (n₂ : ℚ) := by linarith
    have h2 : (n₁ : ℚ) = (n₂ : ℚ) := mul_left_cancel₀ hM_ne h1
    exact_mod_cast h2
  have hLHS_supp : ∀ q : ℚ, q ∉ Set.range embL →
      adelicGaussianTest t B (diagRatAdele q) = 0 := by
    intro q hnot
    unfold adelicGaussianTest
    by_cases hall : ∀ p : Nat.Primes, ‖(q : ℚ_[p.1]) - B.center p‖ ≤ (p.1 : ℝ) ^ (-B.level p)
    · exfalso
      apply hnot
      have hdiv_le : ∀ p : Nat.Primes, ‖(((q - r₀) / M : ℚ) : ℚ_[p.1])‖ ≤ 1 := by
        intro p
        have hcast : (((q - r₀) / M : ℚ) : ℚ_[p.1]) =
            ((q : ℚ_[p.1]) - (r₀ : ℚ_[p.1])) / (M : ℚ_[p.1]) := by
          push_cast; rfl
        rw [hcast, norm_div, B.norm_scale p]
        have hsub : ‖(q : ℚ_[p.1]) - (r₀ : ℚ_[p.1])‖ ≤ (p.1 : ℝ) ^ (-B.level p) := by
          have : (q : ℚ_[p.1]) - (r₀ : ℚ_[p.1]) =
              ((q : ℚ_[p.1]) - B.center p) + -((r₀ : ℚ_[p.1]) - B.center p) := by ring
          rw [this]
          refine (Padic.nonarchimedean _ _).trans (max_le (hall p) ?_)
          rw [norm_neg]; exact hr₀ p
        exact (div_le_one (zpow_pos (padic_p_pos p.1) _)).mpr hsub
      obtain ⟨n, hn⟩ := exists_int_of_forall_padicNorm_le_one hdiv_le
      refine ⟨n, ?_⟩
      dsimp only [embL]
      have h1 : q - r₀ = M * (n : ℚ) := by
        rw [← hn, mul_div_cancel₀ _ hM_ne]
      linarith
    · push Not at hall
      obtain ⟨p₀, hp₀⟩ := hall
      have h0 : ballInd p₀.1 (B.center p₀) (B.level p₀) ((diagRatAdele q).2 p₀) = 0 :=
        (ballInd_eq_zero_iff p₀.1 _ _ _).mpr hp₀
      rw [finprod_eq_zero_of_exists (hasFiniteMulSupport_adelicBox_ballInd B (diagRatAdele q).2) h0,
        mul_zero]
  have hLHS :
      (∑' q : ℚ, adelicGaussianTest t B (diagRatAdele q)) =
      ∑' n : ℤ, archGaussian t ((r₀ : ℝ) + (M : ℝ) * (n : ℝ)) := by
    rw [tsum_eq_tsum_of_injective_support (fun q ↦ adelicGaussianTest t B (diagRatAdele q))
      hembL_inj hLHS_supp]
    refine tsum_congr fun n ↦ ?_
    unfold adelicGaussianTest
    have hfin1 : ∏ᶠ p : Nat.Primes,
        ballInd p.1 (B.center p) (B.level p) ((diagRatAdele (embL n)).2 p) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun p ↦ (ballInd_eq_one_iff p.1 _ _ _).mpr ?_
      have hdiff : ((embL n : ℚ) : ℚ_[p.1]) - B.center p =
          ((r₀ : ℚ_[p.1]) - B.center p) + (M : ℚ_[p.1]) * (n : ℚ_[p.1]) := by
        dsimp only [embL]; push_cast; ring
      rw [diagRatAdele_snd, hdiff]
      refine (Padic.nonarchimedean _ _).trans (max_le (hr₀ p) ?_)
      rw [norm_mul, B.norm_scale p]
      have hn : ‖(n : ℚ_[p.1])‖ ≤ 1 := Padic.norm_int_le_one n
      calc (p.1 : ℝ) ^ (-B.level p) * ‖(n : ℚ_[p.1])‖
          ≤ (p.1 : ℝ) ^ (-B.level p) * 1 :=
            mul_le_mul_of_nonneg_left hn (zpow_nonneg (padic_p_pos p.1).le _)
        _ = (p.1 : ℝ) ^ (-B.level p) := mul_one _
    rw [hfin1, mul_one, diagRatAdele_fst]
    dsimp only [embL]
    push_cast; rfl
  -- Step 2: RHS reduction to `∑'_{n : ℤ} 𝓕(archGaussian t)(n / M) * M⁻¹ * exp(2πi r₀ (n / M))`
  let embR : ℤ → ℚ := fun n ↦ (n : ℚ) / M
  have hembR_inj : Function.Injective embR := by
    intro n₁ n₂ h
    have h1 : (n₁ : ℚ) = (n₂ : ℚ) := by
      dsimp only [embR] at h
      exact (div_left_inj' hM_ne).mp h
    exact_mod_cast h1
  have hRHS_supp : ∀ q : ℚ, q ∉ Set.range embR →
      adelicGaussianFourier t B (diagRatAdele q) = 0 := by
    intro q hnot
    unfold adelicGaussianFourier
    by_cases hall : ∀ p : Nat.Primes, ‖(q : ℚ_[p.1])‖ ≤ (p.1 : ℝ) ^ (B.level p)
    · exfalso
      apply hnot
      have hmul_le : ∀ p : Nat.Primes, ‖((M * q : ℚ) : ℚ_[p.1])‖ ≤ 1 := by
        intro p
        push_cast
        rw [norm_mul, B.norm_scale p]
        calc (p.1 : ℝ) ^ (-B.level p) * ‖(q : ℚ_[p.1])‖
            ≤ (p.1 : ℝ) ^ (-B.level p) * (p.1 : ℝ) ^ (B.level p) :=
              mul_le_mul_of_nonneg_left (hall p) (zpow_nonneg (padic_p_pos p.1).le _)
          _ = 1 := by rw [← zpow_add₀ (padic_p_pos p.1).ne', neg_add_cancel, zpow_zero]
      obtain ⟨n, hn⟩ := exists_int_of_forall_padicNorm_le_one hmul_le
      refine ⟨n, ?_⟩
      dsimp only [embR]
      rw [← hn, mul_div_cancel_left₀ _ hM_ne]
    · push Not at hall
      obtain ⟨p₀, hp₀⟩ := hall
      have h0 :
          padicFourier p₀.1 (ballInd p₀.1 (B.center p₀) (B.level p₀)) ((diagRatAdele q).2 p₀) = 0 := by
        rw [diagRatAdele_snd, padicFourier_ballInd]
        have hb0 : ballInd p₀.1 0 (-B.level p₀) (q : ℚ_[p₀.1]) = 0 := by
          rw [ballInd_eq_zero_iff]; simpa using hp₀
        rw [hb0, mul_zero]
      rw [finprod_eq_zero_of_exists (hasFiniteMulSupport_adelicBox_fourier B (diagRatAdele q).2) h0,
        mul_zero]
  have hscale_finprod :
      (∏ᶠ p : Nat.Primes, ((p.1 : ℂ) ^ (-B.level p))) = (M : ℂ)⁻¹ := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := B.S) (fun p hp ↦ by
      simp only [Function.mem_mulSupport, ne_eq] at hp
      by_contra hnot
      exact hp (by rw [B.level_eq_zero p hnot, neg_zero, zpow_zero]))]
    dsimp only [M, AdelicBox.scale]
    push_cast
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    rw [zpow_neg]
  have hRHS :
      (∑' q : ℚ, adelicGaussianFourier t B (diagRatAdele q)) =
      ∑' n : ℤ, 𝓕 (archGaussian t) ((n : ℝ) / (M : ℝ)) * ((M : ℝ) : ℂ)⁻¹ *
        Complex.exp (2 * Real.pi * Complex.I * ((r₀ : ℝ) : ℂ) * (((n : ℝ) : ℂ) / ((M : ℝ) : ℂ))) := by
    rw [tsum_eq_tsum_of_injective_support (fun q ↦ adelicGaussianFourier t B (diagRatAdele q))
      hembR_inj hRHS_supp]
    refine tsum_congr fun n ↦ ?_
    set q : ℚ := embR n
    have hq_norm : ∀ p : Nat.Primes, ‖(q : ℚ_[p.1])‖ ≤ (p.1 : ℝ) ^ (B.level p) := by
      intro p
      have hcast : (q : ℚ_[p.1]) = (n : ℚ_[p.1]) / (M : ℚ_[p.1]) := by
        dsimp only [q, embR]; push_cast; rfl
      rw [hcast, norm_div, B.norm_scale p, zpow_neg, div_inv_eq_mul]
      have hn : ‖(n : ℚ_[p.1])‖ ≤ 1 := Padic.norm_int_le_one n
      calc ‖(n : ℚ_[p.1])‖ * (p.1 : ℝ) ^ (B.level p)
          ≤ 1 * (p.1 : ℝ) ^ (B.level p) :=
            mul_le_mul_of_nonneg_right hn (zpow_nonneg (padic_p_pos p.1).le _)
        _ = (p.1 : ℝ) ^ (B.level p) := one_mul _
    have hchar_eq : ∀ p : Nat.Primes,
        padicAddChar p.1 (B.center p * (q : ℚ_[p.1])) =
          padicAddChar p.1 ((r₀ * q : ℚ) : ℚ_[p.1]) := by
      intro p
      have hdiff_norm : ‖(B.center p - (r₀ : ℚ_[p.1])) * (q : ℚ_[p.1])‖ ≤ 1 := by
        rw [norm_mul]
        have hcr : ‖B.center p - (r₀ : ℚ_[p.1])‖ ≤ (p.1 : ℝ) ^ (-B.level p) := by
          rw [norm_sub_rev]; exact hr₀ p
        calc ‖B.center p - (r₀ : ℚ_[p.1])‖ * ‖(q : ℚ_[p.1])‖
            ≤ (p.1 : ℝ) ^ (-B.level p) * (p.1 : ℝ) ^ (B.level p) :=
              mul_le_mul hcr (hq_norm p) (norm_nonneg _) (zpow_nonneg (padic_p_pos p.1).le _)
          _ = 1 := by rw [← zpow_add₀ (padic_p_pos p.1).ne', neg_add_cancel, zpow_zero]
      have h1 : padicAddChar p.1 ((B.center p - (r₀ : ℚ_[p.1])) * (q : ℚ_[p.1])) = 1 :=
        padicAddChar_of_norm_le_one p.1 hdiff_norm
      have hrew : B.center p * (q : ℚ_[p.1]) =
          (B.center p - (r₀ : ℚ_[p.1])) * (q : ℚ_[p.1]) + ((r₀ * q : ℚ) : ℚ_[p.1]) := by
        push_cast; ring
      rw [hrew, padicAddChar_add, h1, one_mul]
    have hfin_prod :
        (∏ᶠ p : Nat.Primes,
          padicFourier p.1 (ballInd p.1 (B.center p) (B.level p)) ((diagRatAdele q).2 p)) =
        (M : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * (r₀ : ℂ) * ((q : ℝ) : ℂ)) := by
      have hfun :
          (fun p : Nat.Primes ↦
            padicFourier p.1 (ballInd p.1 (B.center p) (B.level p)) ((diagRatAdele q).2 p)) =
          fun p : Nat.Primes ↦
            ((p.1 : ℂ) ^ (-B.level p)) * padicAddChar p.1 ((r₀ * q : ℚ) : ℚ_[p.1]) := by
        funext p
        rw [diagRatAdele_snd, padicFourier_ballInd]
        have hb1 : ballInd p.1 0 (-B.level p) (q : ℚ_[p.1]) = 1 := by
          rw [ballInd_eq_one_iff]; simpa using hq_norm p
        rw [hb1, mul_one, hchar_eq p]
      have hsupp1 : (fun p : Nat.Primes ↦ ((p.1 : ℂ) ^ (-B.level p))).HasFiniteMulSupport := by
        refine B.S.finite_toSet.subset ?_
        intro p hp
        simp only [Function.mem_mulSupport, ne_eq] at hp
        by_contra hnot
        exact hp (by rw [B.level_eq_zero p hnot, neg_zero, zpow_zero])
      have hsupp2 := hasFiniteMulSupport_padicAddChar_rat (r₀ * q)
      rw [hfun, finprod_mul_distrib hsupp1 hsupp2, hscale_finprod]
      congr 1
      -- Apply the Unconditional Global Adelic Character Product Formula at `r₀ * q`!
      have hglob := adelicAddChar_rat_eq_one (r₀ * q)
      have hinv : (∏ᶠ p : Nat.Primes, padicAddChar p.1 ((r₀ * q : ℚ) : ℚ_[p.1])) =
          (archAddChar ((r₀ * q : ℚ) : ℝ))⁻¹ :=
        eq_inv_of_mul_eq_one_right hglob
      rw [hinv, ← archAddChar_neg]
      unfold archAddChar
      congr 1
      push_cast; ring
    unfold adelicGaussianFourier
    rw [hfin_prod, diagRatAdele_fst]
    have hq_real : (q : ℝ) = (n : ℝ) / (M : ℝ) := by dsimp only [q, embR]; push_cast; rfl
    rw [hq_real]
    have hMcast : ((M : ℝ) : ℂ) = (M : ℂ) := by push_cast; rfl
    have hr0cast : ((r₀ : ℝ) : ℂ) = (r₀ : ℂ) := by push_cast; rfl
    rw [hMcast, hr0cast]
    push_cast; ring
  -- Step 3: Conclude by Archimedean shifted Gaussian Poisson summation!
  rw [hLHS, hRHS]
  exact archGaussian_poisson_shifted ht hM_real_pos (r₀ : ℝ)

/-- **Specialization at the Spherical Box `k_p = 0, a_p = 0`: Tate's Exact Theta Identity (`ℂ`)**:
for every `t > 0`,
`∑'_{n : ℤ} exp(-π t n²) = t^{-1/2} ∑'_{n : ℤ} exp(-π n² / t)`. -/
theorem tate_theta_identity_complex {t : ℝ} (ht : 0 < t) :
    (∑' n : ℤ, Complex.exp (-Real.pi * (t : ℂ) * (n : ℂ) ^ 2)) =
      (t : ℂ) ^ (-(1 / 2 : ℂ)) * ∑' n : ℤ, Complex.exp (-Real.pi / (t : ℂ) * (n : ℂ) ^ 2) := by
  have hP := adelic_poisson_summation_rat_gaussian ht AdelicBox.spherical
  have hinj : Function.Injective (Int.cast : ℤ → ℚ) := Int.cast_injective
  have hL :
      (∑' q : ℚ, adelicGaussianTest t AdelicBox.spherical (diagRatAdele q)) =
      ∑' n : ℤ, Complex.exp (-Real.pi * (t : ℂ) * (n : ℂ) ^ 2) := by
    rw [tsum_eq_tsum_of_injective_support _ hinj (fun q hnot ↦ by
      unfold adelicGaussianTest
      by_cases hall : ∀ p : Nat.Primes, ‖(q : ℚ_[p.1])‖ ≤ 1
      · exfalso; apply hnot
        obtain ⟨n, hn⟩ := exists_int_of_forall_padicNorm_le_one hall
        exact ⟨n, hn.symm⟩
      · push Not at hall
        obtain ⟨p₀, hp₀⟩ := hall
        have h0 : ballInd p₀.1 (AdelicBox.spherical.center p₀) (AdelicBox.spherical.level p₀)
            ((diagRatAdele q).2 p₀) = 0 := by
          rw [ballInd_eq_zero_iff]; simpa [AdelicBox.spherical] using hp₀
        rw [finprod_eq_zero_of_exists
          (hasFiniteMulSupport_adelicBox_ballInd AdelicBox.spherical (diagRatAdele q).2) h0,
          mul_zero])]
    refine tsum_congr fun n ↦ ?_
    unfold adelicGaussianTest archGaussian
    have h1 : ∏ᶠ p : Nat.Primes,
        ballInd p.1 (AdelicBox.spherical.center p) (AdelicBox.spherical.level p)
          ((diagRatAdele (n : ℚ)).2 p) = 1 :=
      finprod_eq_one_of_forall_eq_one fun p ↦ by
        rw [diagRatAdele_snd, ballInd_eq_one_iff]
        simpa [AdelicBox.spherical] using Padic.norm_int_le_one (p := p.1) n
    rw [h1, mul_one]
    simp
  have hR :
      (∑' q : ℚ, adelicGaussianFourier t AdelicBox.spherical (diagRatAdele q)) =
      (t : ℂ) ^ (-(1 / 2 : ℂ)) * ∑' n : ℤ, Complex.exp (-Real.pi / (t : ℂ) * (n : ℂ) ^ 2) := by
    have hF_eq :
        (∑' q : ℚ, adelicGaussianFourier t AdelicBox.spherical (diagRatAdele q)) =
        ∑' n : ℤ, 𝓕 (archGaussian t) (n : ℝ) := by
      have hself : ∀ q : ℚ,
          adelicGaussianFourier t AdelicBox.spherical (diagRatAdele q) =
          𝓕 (archGaussian t) (q : ℝ) *
            ∏ᶠ p : Nat.Primes, ballInd p.1 0 0 (q : ℚ_[p.1]) := by
        intro q
        unfold adelicGaussianFourier AdelicBox.spherical
        simp only [diagRatAdele_fst, diagRatAdele_snd, padicFourier_padicIntInd_selfDual]
      simp_rw [hself]
      rw [tsum_eq_tsum_of_injective_support _ hinj (fun q hnot ↦ by
        by_cases hall : ∀ p : Nat.Primes, ‖(q : ℚ_[p.1])‖ ≤ 1
        · exfalso; apply hnot
          obtain ⟨n, hn⟩ := exists_int_of_forall_padicNorm_le_one hall
          exact ⟨n, hn.symm⟩
        · push Not at hall
          obtain ⟨p₀, hp₀⟩ := hall
          have h0 : ballInd p₀.1 0 0 (q : ℚ_[p₀.1]) = 0 := by
            rw [ballInd_eq_zero_iff]; simpa using hp₀
          have hsupp : (fun p : Nat.Primes ↦ ballInd p.1 0 0 (q : ℚ_[p.1])).HasFiniteMulSupport :=
            hasFiniteMulSupport_adelicBox_ballInd AdelicBox.spherical (diagRatAdele q).2
          rw [finprod_eq_zero_of_exists hsupp h0, mul_zero])]
      refine tsum_congr fun n ↦ ?_
      have h1 : ∏ᶠ p : Nat.Primes, ballInd p.1 0 0 ((n : ℚ) : ℚ_[p.1]) = 1 :=
        finprod_eq_one_of_forall_eq_one fun p ↦ by
          rw [ballInd_eq_one_iff]
          simpa using Padic.norm_int_le_one (p := p.1) n
      rw [h1, mul_one]
      simp
    rw [hF_eq, ← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    rw [fourier_archGaussian ht]
    simp
  rw [← hL, ← hR]
  exact hP

/-- **Specialization at the Spherical Box `k_p = 0, a_p = 0`: Tate's Exact Theta Identity (`ℝ`)**:
for every `t > 0`,
`∑'_{n : ℤ} exp(-π t n²) = t^{-1/2} ∑'_{n : ℤ} exp(-π n² / t)`. -/
theorem tate_theta_identity_real {t : ℝ} (ht : 0 < t) :
    (∑' n : ℤ, Real.exp (-Real.pi * t * (n : ℝ) ^ 2)) =
      t ^ (-(1 / 2 : ℝ)) * ∑' n : ℤ, Real.exp (-Real.pi / t * (n : ℝ) ^ 2) := by
  have hC := tate_theta_identity_complex ht
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_tsum, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_intCast, Complex.ofReal_cpow ht.le,
    Complex.ofReal_one, Complex.ofReal_ofNat] using hC

end AdelicPoissonSummation

/-! ## Section 5: Unified Unconditional Stage 6 Adelic Poisson Summary -/

/-- **Unified Unconditional Stage 6 Adelic Character, Self-Duality & Poisson Summation Theorem**
(`0` assumptions):
1. Concrete $p$-adic additive character `ψ_p` is a unitary homomorphism with exact conductor `ℤ_[p]`,
2. Unconditional Global Adelic Character Product Formula `ψ_∞(q) * ∏'_p ψ_p(q) = 1` for every `q ∈ ℚ`,
3. Exact $p$-adic ball-indicator Fourier transform, exact self-duality `ℱ_p(1_{ℤ_p}) = 1_{ℤ_p}`,
   and exact $p$-adic Fourier inversion `ℱ_p(ℱ_p f)(x) = f(-x)`,
4. Unconditional Concrete Adelic Poisson Summation `∑'_{q : ℚ} Φ(q) = ∑'_{q : ℚ} Φ̂(q)` for all
   `t > 0` and every finite-level congruence box `B : AdelicBox`, specializing at `k_p = 0, a_p = 0`
   to Tate's theta identity. -/
theorem stage6_adelicPoisson_unconditional :
    (∀ (p : ℕ) [Fact p.Prime],
      (∀ x y : ℚ_[p], padicAddChar p (x + y) = padicAddChar p x * padicAddChar p y) ∧
      (∀ x : ℚ_[p], x ∈ PadicInt.subring p → padicAddChar p x = 1) ∧
      padicAddChar p (p : ℚ_[p])⁻¹ ≠ 1 ∧
      (∀ x : ℚ_[p], ‖padicAddChar p x‖ = 1 ∧ star (padicAddChar p x) = padicAddChar p (-x))) ∧
    (∀ q : ℚ,
      archAddChar (q : ℝ) * ∏ᶠ p : Nat.Primes, padicAddChar p.1 (q : ℚ_[p.1]) = 1) ∧
    (∀ (p : ℕ) [Fact p.Prime],
      (∀ (a : ℚ_[p]) (k : ℤ) (y : ℚ_[p]),
        padicFourier p (ballInd p a k) y =
          (p : ℂ) ^ (-k) * padicAddChar p (a * y) * ballInd p 0 (-k) y) ∧
      padicFourier p (ballInd p 0 0) = ballInd p 0 0 ∧
      (∀ (f : ℚ_[p] → ℂ), IsPadicSchwartzBruhat p f →
        ∀ x : ℚ_[p], padicFourier p (padicFourier p f) x = f (-x))) ∧
    (∀ (t : ℝ), 0 < t →
      (∀ B : AdelicBox,
        (∑' q : ℚ, adelicGaussianTest t B (diagRatAdele q)) =
          ∑' q : ℚ, adelicGaussianFourier t B (diagRatAdele q)) ∧
      (∑' n : ℤ, Real.exp (-Real.pi * t * (n : ℝ) ^ 2)) =
        t ^ (-(1 / 2 : ℝ)) * ∑' n : ℤ, Real.exp (-Real.pi / t * (n : ℝ) ^ 2)) :=
  ⟨fun p _ ↦
    ⟨padicAddChar_add p,
     fun _ hx ↦ padicAddChar_of_mem_padicInt p hx,
     padicAddChar_inv_prime_ne_one p,
     fun x ↦ ⟨norm_padicAddChar p x, star_padicAddChar p x⟩⟩,
   adelicAddChar_rat_eq_one,
   fun p _ ↦
    ⟨padicFourier_ballInd p,
     padicFourier_padicIntInd_selfDual p,
     fun _ hf x ↦ padicFourier_inversion p hf x⟩,
   fun _ ht ↦
    ⟨fun B ↦ adelic_poisson_summation_rat_gaussian ht B,
     tate_theta_identity_real ht⟩⟩

end RHDirect.Stage6AdelicPoisson

end
