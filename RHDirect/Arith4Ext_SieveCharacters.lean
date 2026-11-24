/-
Copyright (c) 2026 Arithmetica4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.GaussSum
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Arith4Ext.SieveCharacters — Selberg Sieve, Gauss Sums & Pólya–Vinogradov, Turán–Kubilius, and Vaughan's Identity

Reusable, 100%-unconditional (`0` assumptions, `0` proxies, `0` `sorry`, `0` custom axioms)
Tier A analytic number theory library on targeted Mathlib imports (`namespace Arith4Ext.SieveCharacters`):

1. **General Abstract Selberg Upper-Bound Sieve**: Exact quadratic-form Möbius diagonalization
   (`h = μ * (1/g)`), explicit optimal Selberg weights `λ_d` with `|λ_d| ≤ 1`, optimality
   `Q(λ) ≥ 1 / G(P, D)`, the general Selberg upper-bound sieve theorem, and explicit
   Brun–Titchmarsh-style corollaries for integers coprime to `P(z)` and primes in intervals.
2. **Gauss Sum Norm & Pólya–Vinogradov Inequality (`MulChar (ZMod q) ℂ`)**: Exact `‖τ(χ)‖^2 = q`
   for every primitive Dirichlet character mod `q`, and the explicit Pólya–Vinogradov inequality
   `‖∑_{n ∈ Icc M (M + N - 1)} χ n‖ ≤ √q * (Real.log q + 1)`.
3. **Turán–Kubilius Inequality & Hardy–Ramanujan Normal Order Corollary**: Full `L^2` variance
   bound for general additive and strongly additive functions `f : ℕ → ℂ` with explicit absolute
   constants, plus the Hardy–Ramanujan normal-order variance and tail bounds for `ω(n)`.
4. **Vaughan's Identity**: Exact ring-level Dirichlet convolution identity, pointwise identity
   for `n > U`, and bilinear Type I / Type II sum decomposition of `ArithmeticFunction.vonMangoldt`.
-/

open Real Complex Finset
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace Arith4Ext.SieveCharacters

noncomputable section

/-! ## Section 1: General Abstract Selberg Upper-Bound Sieve & Brun–Titchmarsh Corollaries -/

/-- The primorial `P(z) = ∏_{p ≤ z, prime} p`. -/
def primorial (z : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, p

lemma primorial_pos (z : ℕ) : 0 < primorial z := by
  unfold primorial
  exact Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos

lemma primorial_ne_zero (z : ℕ) : primorial z ≠ 0 :=
  (primorial_pos z).ne'

lemma squarefree_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    Squarefree (∏ p ∈ S, p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha_prime : Nat.Prime a := hS a (Finset.mem_insert_self a s)
    have hs_primes : ∀ p ∈ s, Nat.Prime p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      have hp_prime : Nat.Prime p := hs_primes p hp
      exact (Nat.coprime_primes ha_prime hp_prime).mpr (fun h => ha (h ▸ hp))
    exact (Nat.squarefree_mul hcop).mpr ⟨ha_prime.squarefree, ih hs_primes⟩

lemma primorial_squarefree (z : ℕ) : Squarefree (primorial z) :=
  squarefree_prod_primes _ fun _ hp => (Finset.mem_filter.mp hp).2

lemma prime_dvd_primorial_iff {z p : ℕ} (hp : Nat.Prime p) :
    p ∣ primorial z ↔ p ≤ z := by
  unfold primorial
  constructor
  · intro hdvd
    rw [hp.prime.dvd_finsetProd_iff] at hdvd
    rcases hdvd with ⟨q, hq, hpq⟩
    have hq_mem := Finset.mem_filter.mp hq
    have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_mem.2).mp hpq
    rw [hpeq]
    exact (Finset.mem_Icc.mp hq_mem.1).2
  · intro hle
    exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_le, hle⟩, hp⟩)

lemma squarefree_eq_prod_primeFactors {m : ℕ} (hm : Squarefree m) :
    m = ∏ p ∈ m.primeFactors, p := by
  have hm0 : m ≠ 0 := hm.ne_zero
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm0]
  rw [Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < m.factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp_prime hm0 (Nat.dvd_of_mem_primeFactors hp)
  have hle1 : m.factorization p ≤ 1 := by
    by_contra hgt
    have hge2 : 2 ≤ m.factorization p := by omega
    have hsq : p * p ∣ m := by
      simpa [sq] using (hp_prime.pow_dvd_iff_le_factorization hm0).mpr hge2
    exact hp_prime.not_isUnit (hm p hsq)
  simp [le_antisymm hle1 hpos]

lemma squarefree_dvd_primorial {z m : ℕ} (hm : Squarefree m) (hle : m ≤ z) :
    m ∣ primorial z := by
  have hm0 : m ≠ 0 := hm.ne_zero
  rw [squarefree_eq_prod_primeFactors hm]
  unfold primorial
  refine Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => ?_
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
  have hp_le : p ≤ z := (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hp_dvd).trans hle
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_prime.one_le, hp_le⟩, hp_prime⟩

/-- The sifting divisor set `S(P, D) = {d ∣ P : d ≤ D}`. -/
def sieveDivisors (P D : ℕ) : Finset ℕ :=
  P.divisors.filter (· ≤ D)

lemma mem_sieveDivisors {P D d : ℕ} (hP : P ≠ 0) :
    d ∈ sieveDivisors P D ↔ d ∣ P ∧ d ≤ D := by
  simp [sieveDivisors, Nat.mem_divisors, hP]

lemma one_mem_sieveDivisors {P D : ℕ} (hP : P ≠ 0) (hD : 1 ≤ D) :
    1 ∈ sieveDivisors P D := by
  rw [mem_sieveDivisors hP]
  exact ⟨one_dvd P, hD⟩

lemma sieveDivisors_dvd_closed {P D m d : ℕ} (hP : P ≠ 0)
    (hd : d ∈ sieveDivisors P D) (hmd : m ∣ d) :
    m ∈ sieveDivisors P D := by
  rw [mem_sieveDivisors hP] at hd ⊢
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (Nat.pos_of_ne_zero hP)
  exact ⟨hmd.trans hd.1, (Nat.le_of_dvd hd0 hmd).trans hd.2⟩

/-- A real-valued density function `g : ℕ → ℝ` is multiplicative on `ℕ`. -/
def IsMultDensity (g : ℕ → ℝ) : Prop :=
  g 1 = 1 ∧ ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b

lemma isMultDensity_prod_primeFactors {g : ℕ → ℝ} (hg : IsMultDensity g)
    {m : ℕ} (hm : Squarefree m) :
    g m = ∏ p ∈ m.primeFactors, g p := by
  conv_lhs => rw [squarefree_eq_prod_primeFactors hm]
  have hprimes : ∀ p ∈ m.primeFactors, Nat.Prime p := fun _ hp => Nat.prime_of_mem_primeFactors hp
  generalize m.primeFactors = S at hprimes ⊢
  classical
  induction S using Finset.induction_on with
  | empty => simp [hg.1]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have ha_p : Nat.Prime a := hprimes a (Finset.mem_insert_self a s)
    have hs_p : ∀ p ∈ s, Nat.Prime p := fun p hp => hprimes p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes ha_p (hs_p p hp)).mpr (fun h => ha (h ▸ hp))
    rw [hg.2 a (∏ p ∈ s, p) hcop, ih hs_p]

lemma isMultDensity_pos_of_squarefree {g : ℕ → ℝ} (hg : IsMultDensity g)
    {m : ℕ} (hm : Squarefree m) (hpos : ∀ p ∈ m.primeFactors, 0 < g p) :
    0 < g m := by
  rw [isMultDensity_prod_primeFactors hg hm]
  exact Finset.prod_pos hpos

lemma isMultDensity_lcm_mul_gcd {g : ℕ → ℝ} (hg : IsMultDensity g)
    {d₁ d₂ : ℕ} (hd₁ : Squarefree d₁) (hd₂ : Squarefree d₂) :
    g (Nat.lcm d₁ d₂) * g (Nat.gcd d₁ d₂) = g d₁ * g d₂ := by
  set k := Nat.gcd d₁ d₂
  have hk_pos : 0 < k := Nat.gcd_pos_of_pos_left d₂ (Nat.pos_of_ne_zero hd₁.ne_zero)
  have hk1 : k ∣ d₁ := Nat.gcd_dvd_left d₁ d₂
  have hk2 : k ∣ d₂ := Nat.gcd_dvd_right d₁ d₂
  set a := d₁ / k
  set b := d₂ / k
  have h1 : d₁ = k * a := (Nat.mul_div_cancel' hk1).symm
  have h2 : d₂ = k * b := (Nat.mul_div_cancel' hk2).symm
  have hcop_ab : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hk_pos
  have hcop_ka : Nat.Coprime k a := by
    rw [h1] at hd₁
    exact Nat.coprime_of_squarefree_mul hd₁
  have hcop_kb : Nat.Coprime k b := by
    rw [h2] at hd₂
    exact Nat.coprime_of_squarefree_mul hd₂
  have hlcm : Nat.lcm d₁ d₂ = k * (a * b) := by
    have hmul := Nat.gcd_mul_lcm d₁ d₂
    change k * Nat.lcm d₁ d₂ = d₁ * d₂ at hmul
    conv_rhs at hmul => rw [h1, h2]
    have : k * Nat.lcm d₁ d₂ = k * (k * (a * b)) := by linarith
    exact Nat.eq_of_mul_eq_mul_left hk_pos this
  rw [hlcm, h1, h2, hg.2 k (a * b) (hcop_ka.mul_right hcop_kb), hg.2 a b hcop_ab,
    hg.2 k a hcop_ka, hg.2 k b hcop_kb]
  ring

/-- The Selberg Möbius-inverted density function `h = μ * (1 / g)`, defined by
`h(m) = ∑_{d₁ d₂ = m} μ(d₁) / g(d₂)`. -/
def selbergH (g : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) * (g x.2)⁻¹

lemma sum_selbergH_divisors (g : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ m ∈ n.divisors, selbergH g m = (g n)⁻¹ := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
    (f := selbergH g) (g := fun k => (g k)⁻¹)).mpr (fun m _ => rfl)
  exact h n hn

lemma selbergH_one {g : ℕ → ℝ} (hg1 : g 1 = 1) : selbergH g 1 = 1 := by
  simp [selbergH, hg1]

lemma selbergH_prime {g : ℕ → ℝ} (hg1 : g 1 = 1) {p : ℕ} (hp : Nat.Prime p) :
    selbergH g p = (g p)⁻¹ - 1 := by
  have hsum := sum_selbergH_divisors g hp.pos
  rw [hp.divisors, Finset.sum_pair hp.ne_one.symm, selbergH_one hg1] at hsum
  linarith

lemma selbergH_mul_coprime {g : ℕ → ℝ} (hg : IsMultDensity g)
    {a b : ℕ} (hcop : Nat.Coprime a b) :
    selbergH g (a * b) = selbergH g a * selbergH g b := by
  let invG : ArithmeticFunction ℝ :=
    { toFun := fun n => if n = 0 then 0 else (g n)⁻¹
      map_zero' := rfl }
  have hinvG_mult : invG.IsMultiplicative := by
    refine ⟨by simp [invG, hg.1], fun {m n} hmn => ?_⟩
    by_cases hm : m = 0
    · simp [invG, hm]
    · by_cases hn : n = 0
      · simp [invG, hn]
      · simp [invG, hm, hn, hg.2 m n hmn]
        ring
  let muR : ArithmeticFunction ℝ := (ArithmeticFunction.moebius : ArithmeticFunction ℤ)
  have hmuR_mult : muR.IsMultiplicative := by
    refine ⟨by simp [muR], fun {m n} hmn => ?_⟩
    have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn
    simp only [muR, ArithmeticFunction.intCoe_apply]
    exact_mod_cast h
  have hconv_mult : (muR * invG).IsMultiplicative := hmuR_mult.mul hinvG_mult
  have heq : ∀ n : ℕ, (muR * invG) n = selbergH g n := by
    intro n
    rw [ArithmeticFunction.mul_apply]
    unfold selbergH
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx2 : x.2 ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp hx).2 |> fun hn0 h0 =>
      hn0 (by rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1, h0, mul_zero])
    simp [muR, invG, hx2]
  rw [← heq (a * b), ← heq a, ← heq b]
  exact hconv_mult.map_mul_of_coprime hcop

lemma selbergH_eq_prod_primeFactors {g : ℕ → ℝ} (hg : IsMultDensity g)
    {m : ℕ} (hm : Squarefree m) :
    selbergH g m = ∏ p ∈ m.primeFactors, ((g p)⁻¹ - 1) := by
  conv_lhs => rw [squarefree_eq_prod_primeFactors hm]
  have hprimes : ∀ p ∈ m.primeFactors, Nat.Prime p := fun _ hp => Nat.prime_of_mem_primeFactors hp
  generalize m.primeFactors = S at hprimes ⊢
  classical
  induction S using Finset.induction_on with
  | empty => simp [selbergH_one hg.1]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have ha_p : Nat.Prime a := hprimes a (Finset.mem_insert_self a s)
    have hs_p : ∀ p ∈ s, Nat.Prime p := fun p hp => hprimes p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes ha_p (hs_p p hp)).mpr (fun h => ha (h ▸ hp))
    rw [selbergH_mul_coprime hg hcop, selbergH_prime hg.1 ha_p, ih hs_p]

lemma selbergH_pos {g : ℕ → ℝ} (hg : IsMultDensity g)
    {m : ℕ} (hm : Squarefree m) (h01 : ∀ p ∈ m.primeFactors, 0 < g p ∧ g p < 1) :
    0 < selbergH g m := by
  rw [selbergH_eq_prod_primeFactors hg hm]
  refine Finset.prod_pos fun p hp => ?_
  have ⟨hpos, hlt⟩ := h01 p hp
  have h1 : 1 < (g p)⁻¹ := (one_lt_inv₀ hpos).mpr hlt
  linarith

lemma divisors_prime_mul_of_coprime {a M : ℕ} (ha : Nat.Prime a) (hM : M ≠ 0)
    (_hcop : Nat.Coprime a M) :
    (a * M).divisors = M.divisors ∪ M.divisors.image (a * ·) := by
  ext e
  simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
  constructor
  · intro ⟨hdvd, _⟩
    by_cases hae : a ∣ e
    · right
      rcases hae with ⟨k, rfl⟩
      exact ⟨k, ⟨(mul_dvd_mul_iff_left ha.ne_zero).mp hdvd, hM⟩, rfl⟩
    · left
      have hcop_ae : Nat.Coprime a e := (ha.coprime_iff_not_dvd).mpr hae
      exact ⟨hcop_ae.symm.dvd_of_dvd_mul_left hdvd, hM⟩
  · rintro (⟨h, _⟩ | ⟨k, ⟨hk, _⟩, rfl⟩)
    · exact ⟨h.trans (dvd_mul_left M a), mul_ne_zero ha.ne_zero hM⟩
    · exact ⟨mul_dvd_mul_left a hk, mul_ne_zero ha.ne_zero hM⟩

lemma disjoint_divisors_image_prime_mul {a M : ℕ} (ha : Nat.Prime a) (hcop : Nat.Coprime a M) :
    Disjoint M.divisors (M.divisors.image (a * ·)) := by
  rw [Finset.disjoint_left]
  intro e he he_img
  rcases Finset.mem_image.mp he_img with ⟨k, _, rfl⟩
  have hdvd : a ∣ M := (dvd_mul_right a k).trans (Nat.dvd_of_mem_divisors he)
  exact ha.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hdvd)

lemma sum_divisors_inv_selbergH {g : ℕ → ℝ} (hg : IsMultDensity g)
    {d : ℕ} (hd : Squarefree d) (h01 : ∀ p ∈ d.primeFactors, 0 < g p ∧ g p < 1) :
    ∑ e ∈ d.divisors, (selbergH g e)⁻¹ = (g d * selbergH g d)⁻¹ := by
  have hprod_d := squarefree_eq_prod_primeFactors hd
  have hprimes : ∀ p ∈ d.primeFactors, Nat.Prime p := fun _ hp => Nat.prime_of_mem_primeFactors hp
  suffices ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) → (∀ p ∈ S, 0 < g p ∧ g p < 1) →
      ∑ e ∈ (∏ p ∈ S, p).divisors, (selbergH g e)⁻¹ =
        (g (∏ p ∈ S, p) * selbergH g (∏ p ∈ S, p))⁻¹ by
    have h := this d.primeFactors hprimes h01
    rwa [← hprod_d] at h
  intro S hSp hS01
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [hg.1, selbergH_one hg.1]
  | @insert a s ha ih =>
    have ha_p : Nat.Prime a := hSp a (Finset.mem_insert_self a s)
    have hs_p : ∀ p ∈ s, Nat.Prime p := fun p hp => hSp p (Finset.mem_insert_of_mem hp)
    have ha_01 := hS01 a (Finset.mem_insert_self a s)
    have hs_01 : ∀ p ∈ s, 0 < g p ∧ g p < 1 := fun p hp => hS01 p (Finset.mem_insert_of_mem hp)
    set M := ∏ p ∈ s, p
    have hM0 : M ≠ 0 := (Finset.prod_pos fun p hp => (hs_p p hp).pos).ne'
    have hcop : Nat.Coprime a M :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes ha_p (hs_p p hp)).mpr (fun h => ha (h ▸ hp))
    rw [Finset.prod_insert ha]
    rw [divisors_prime_mul_of_coprime ha_p hM0 hcop]
    rw [Finset.sum_union (disjoint_divisors_image_prime_mul ha_p hcop)]
    rw [Finset.sum_image (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left ha_p.pos hxy)]
    have himg : ∑ e ∈ M.divisors, (selbergH g (a * e))⁻¹ =
        (selbergH g a)⁻¹ * ∑ e ∈ M.divisors, (selbergH g e)⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      have he_cop : Nat.Coprime a e := hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors he)
      rw [selbergH_mul_coprime hg he_cop, mul_inv]
    rw [himg, ← one_add_mul, ih hs_p hs_01]
    rw [hg.2 a M hcop, selbergH_mul_coprime hg hcop, selbergH_prime hg.1 ha_p]
    have hga_pos : 0 < g a := ha_01.1
    have hga_lt1 : g a < 1 := ha_01.2
    have h1 : g a ≠ 0 := hga_pos.ne'
    have h1m : 1 - g a ≠ 0 := by linarith
    have h2 : (g a)⁻¹ - 1 ≠ 0 := by
      have : 1 < (g a)⁻¹ := (one_lt_inv₀ hga_pos).mpr hga_lt1
      linarith
    have hfactor : 1 + ((g a)⁻¹ - 1)⁻¹ = (g a * ((g a)⁻¹ - 1))⁻¹ := by
      have hga_mul : g a * ((g a)⁻¹ - 1) = 1 - g a := by field_simp [h1]
      rw [hga_mul]
      have hinv : ((g a)⁻¹ - 1)⁻¹ = g a / (1 - g a) := by
        field_simp [h1, h1m, h2]
      rw [hinv]
      field_simp [h1m]
      ring
    rw [hfactor]
    have hring : g a * g M * (((g a)⁻¹ - 1) * selbergH g M) =
        (g a * ((g a)⁻¹ - 1)) * (g M * selbergH g M) := by ring
    rw [hring, ← mul_inv]

/-- The Selberg denominator `G(P, D) = ∑_{m ∈ S(P, D)} 1 / h(m)`. -/
def selbergG (g : ℕ → ℝ) (P D : ℕ) : ℝ :=
  ∑ m ∈ sieveDivisors P D, (selbergH g m)⁻¹

lemma selbergG_ge_one {g : ℕ → ℝ} (hg : IsMultDensity g)
    {P D : ℕ} (hP : Squarefree P) (hD : 1 ≤ D)
    (h01 : ∀ p ∈ P.primeFactors, 0 < g p ∧ g p < 1) :
    1 ≤ selbergG g P D := by
  unfold selbergG
  have h1 : 1 ∈ sieveDivisors P D := one_mem_sieveDivisors hP.ne_zero hD
  have hnonneg : ∀ m ∈ sieveDivisors P D, 0 ≤ (selbergH g m)⁻¹ := by
    intro m hm
    have hdvd : m ∣ P := ((mem_sieveDivisors hP.ne_zero).mp hm).1
    have hm_sq : Squarefree m := hP.squarefree_of_dvd hdvd
    have hm_01 : ∀ p ∈ m.primeFactors, 0 < g p ∧ g p < 1 := fun p hp =>
      h01 p (Nat.primeFactors_mono hdvd hP.ne_zero hp)
    exact inv_nonneg.mpr (selbergH_pos hg hm_sq hm_01).le
  calc (1 : ℝ) = (selbergH g 1)⁻¹ := by simp [selbergH_one hg.1]
    _ ≤ ∑ m ∈ sieveDivisors P D, (selbergH g m)⁻¹ :=
      Finset.single_le_sum hnonneg h1

lemma selbergG_pos {g : ℕ → ℝ} (hg : IsMultDensity g)
    {P D : ℕ} (hP : Squarefree P) (hD : 1 ≤ D)
    (h01 : ∀ p ∈ P.primeFactors, 0 < g p ∧ g p < 1) :
    0 < selbergG g P D :=
  lt_of_lt_of_le zero_lt_one (selbergG_ge_one hg hP hD h01)

/-- The explicit optimal Selberg weights `λ_d`. -/
def selbergWeight (g : ℕ → ℝ) (P D d : ℕ) : ℝ :=
  if d ∈ sieveDivisors P D then
    ((ArithmeticFunction.moebius d : ℝ) / (g d * selbergG g P D)) *
      ∑ m ∈ (sieveDivisors P D).filter (d ∣ ·), (selbergH g m)⁻¹
  else 0

/-- The Selberg linear transform `y_m(λ) = ∑_{d ∈ S(P, D), m ∣ d} λ_d g(d)`. -/
def selbergTransform (g : ℕ → ℝ) (P D : ℕ) (lam : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ (sieveDivisors P D).filter (m ∣ ·), lam d * g d

/-- The Selberg quadratic form `Q(λ) = ∑_{d₁, d₂ ∈ S(P, D)} λ_{d₁} λ_{d₂} g(lcm(d₁, d₂))`. -/
def selbergQuadForm (g : ℕ → ℝ) (P D : ℕ) (lam : ℕ → ℝ) : ℝ :=
  ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
    lam d₁ * lam d₂ * g (Nat.lcm d₁ d₂)

lemma sum_moebius_divisors_eq (t : ℕ) :
    ∑ k ∈ t.divisors, (ArithmeticFunction.moebius k : ℝ) = if t = 1 then 1 else 0 := by
  by_cases ht0 : t = 0
  · subst ht0; simp
  · have h := congr_arg (fun f => ((f t : ℤ) : ℝ)) ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply,
      ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply] at h
    have hsum : (∑ x ∈ t.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℤ) * (if x.2 = 0 then (0 : ℕ) else 1 : ℕ) : ℤ) =
        ∑ k ∈ t.divisors, (ArithmeticFunction.moebius k : ℤ) := by
      rw [Nat.sum_divisorsAntidiagonal (f := fun a b =>
        (ArithmeticFunction.moebius a : ℤ) * (if b = 0 then (0 : ℕ) else 1 : ℕ))]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_dvd : k ∣ t := Nat.dvd_of_mem_divisors hk
      have hdiv_ne : t / k ≠ 0 := by
        intro h0
        have := Nat.mul_div_cancel' hk_dvd
        rw [h0, mul_zero] at this
        exact ht0 this.symm
      simp [hdiv_ne]
    rw [hsum] at h
    push_cast at h
    simpa using h

/-- Exact Selberg quadratic-form Möbius diagonalization:
`Q(λ) = ∑_{m ∈ S(P, D)} h(m) * y_m(λ)^2`. -/
theorem selberg_quadratic_diagonalization {g : ℕ → ℝ} (hg : IsMultDensity g)
    {P D : ℕ} (hP : Squarefree P)
    (h01 : ∀ p ∈ P.primeFactors, 0 < g p ∧ g p < 1) (lam : ℕ → ℝ) :
    selbergQuadForm g P D lam =
      ∑ m ∈ sieveDivisors P D, selbergH g m * (selbergTransform g P D lam m) ^ 2 := by
  have hP0 : P ≠ 0 := hP.ne_zero
  unfold selbergQuadForm selbergTransform
  have hstep1 : ∀ d₁ ∈ sieveDivisors P D, ∀ d₂ ∈ sieveDivisors P D,
      lam d₁ * lam d₂ * g (Nat.lcm d₁ d₂) =
        ∑ m ∈ (Nat.gcd d₁ d₂).divisors,
          selbergH g m * ((lam d₁ * g d₁) * (lam d₂ * g d₂)) := by
    intro d₁ hd₁ d₂ hd₂
    have hd₁_dvd : d₁ ∣ P := ((mem_sieveDivisors hP0).mp hd₁).1
    have hd₂_dvd : d₂ ∣ P := ((mem_sieveDivisors hP0).mp hd₂).1
    have hd₁_sq : Squarefree d₁ := hP.squarefree_of_dvd hd₁_dvd
    have hd₂_sq : Squarefree d₂ := hP.squarefree_of_dvd hd₂_dvd
    have hgcd_dvd : Nat.gcd d₁ d₂ ∣ P := (Nat.gcd_dvd_left d₁ d₂).trans hd₁_dvd
    have hgcd_sq : Squarefree (Nat.gcd d₁ d₂) := hP.squarefree_of_dvd hgcd_dvd
    have hgcd_pos : 0 < Nat.gcd d₁ d₂ := Nat.pos_of_ne_zero hgcd_sq.ne_zero
    have hg_gcd_pos : 0 < g (Nat.gcd d₁ d₂) :=
      isMultDensity_pos_of_squarefree hg hgcd_sq fun p hp =>
        (h01 p (Nat.primeFactors_mono hgcd_dvd hP0 hp)).1
    have hlcm_eq : g (Nat.lcm d₁ d₂) = (g (Nat.gcd d₁ d₂))⁻¹ * (g d₁ * g d₂) := by
      have hmul := isMultDensity_lcm_mul_gcd hg hd₁_sq hd₂_sq
      field_simp [hg_gcd_pos.ne']
      linarith
    rw [← Finset.sum_mul, sum_selbergH_divisors g hgcd_pos, hlcm_eq]
    ring
  calc ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
          lam d₁ * lam d₂ * g (Nat.lcm d₁ d₂)
      = ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
          ∑ m ∈ (Nat.gcd d₁ d₂).divisors,
            selbergH g m * ((lam d₁ * g d₁) * (lam d₂ * g d₂)) := by
        refine Finset.sum_congr rfl fun d₁ hd₁ => Finset.sum_congr rfl fun d₂ hd₂ =>
          hstep1 d₁ hd₁ d₂ hd₂
    _ = ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
          ∑ m ∈ sieveDivisors P D,
            if m ∣ d₁ ∧ m ∣ d₂ then selbergH g m * ((lam d₁ * g d₁) * (lam d₂ * g d₂)) else 0 := by
        refine Finset.sum_congr rfl fun d₁ hd₁ => Finset.sum_congr rfl fun d₂ hd₂ => ?_
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext m
        have hgcd_ne : Nat.gcd d₁ d₂ ≠ 0 :=
          (Nat.gcd_pos_of_pos_left d₂
            (Nat.pos_of_ne_zero (hP.squarefree_of_dvd ((mem_sieveDivisors hP0).mp hd₁).1).ne_zero)).ne'
        simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
        constructor
        · intro ⟨⟨h1, h2⟩, _⟩
          exact ⟨sieveDivisors_dvd_closed hP0 hd₁ h1, h1, h2⟩
        · intro ⟨_, h1, h2⟩
          exact ⟨⟨h1, h2⟩, hgcd_ne⟩
    _ = ∑ m ∈ sieveDivisors P D, selbergH g m *
          (∑ d ∈ (sieveDivisors P D).filter (m ∣ ·), lam d * g d) ^ 2 := by
        have hswap : (∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D, ∑ m ∈ sieveDivisors P D,
            if m ∣ d₁ ∧ m ∣ d₂ then selbergH g m * ((lam d₁ * g d₁) * (lam d₂ * g d₂)) else 0) =
            ∑ m ∈ sieveDivisors P D, ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
              if m ∣ d₁ ∧ m ∣ d₂ then selbergH g m * ((lam d₁ * g d₁) * (lam d₂ * g d₂)) else 0 := by
          have h1 : (∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D, ∑ m ∈ sieveDivisors P D,
              if m ∣ d₁ ∧ m ∣ d₂ then selbergH g m * ((lam d₁ * g d₁) * (lam d₂ * g d₂)) else 0) =
              ∑ d₁ ∈ sieveDivisors P D, ∑ m ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
                if m ∣ d₁ ∧ m ∣ d₂ then selbergH g m * ((lam d₁ * g d₁) * (lam d₂ * g d₂)) else 0 :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          rw [h1, Finset.sum_comm]
        rw [hswap]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [sq, Finset.sum_mul, Finset.mul_sum]
        simp_rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun d₁ _ => ?_
        by_cases h1 : m ∣ d₁
        · simp only [h1, true_and, ↓reduceIte]
        · simp [h1]

lemma selbergTransform_opt {g : ℕ → ℝ} (hg : IsMultDensity g)
    {P D m : ℕ} (hP : Squarefree P) (hD : 1 ≤ D)
    (h01 : ∀ p ∈ P.primeFactors, 0 < g p ∧ g p < 1)
    (hm : m ∈ sieveDivisors P D) :
    selbergTransform g P D (selbergWeight g P D) m =
      (ArithmeticFunction.moebius m : ℝ) / (selbergH g m * selbergG g P D) := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have hG_ne : selbergG g P D ≠ 0 := (selbergG_pos hg hP hD h01).ne'
  unfold selbergTransform
  have hterm : ∀ d ∈ (sieveDivisors P D).filter (m ∣ ·),
      selbergWeight g P D d * g d =
        ∑ r ∈ sieveDivisors P D,
          if d ∣ r then ((ArithmeticFunction.moebius d : ℝ) / selbergG g P D) * (selbergH g r)⁻¹
          else 0 := by
    intro d hd
    have hdS : d ∈ sieveDivisors P D := (Finset.mem_filter.mp hd).1
    have hd_dvd : d ∣ P := ((mem_sieveDivisors hP0).mp hdS).1
    have hgd_ne : g d ≠ 0 :=
      (isMultDensity_pos_of_squarefree hg (hP.squarefree_of_dvd hd_dvd) fun p hp =>
        (h01 p (Nat.primeFactors_mono hd_dvd hP0 hp)).1).ne'
    simp only [selbergWeight, hdS, ↓reduceIte]
    have hcancel : (ArithmeticFunction.moebius d : ℝ) / (g d * selbergG g P D) *
        (∑ r ∈ (sieveDivisors P D).filter (d ∣ ·), (selbergH g r)⁻¹) * g d =
        ((ArithmeticFunction.moebius d : ℝ) / selbergG g P D) *
          ∑ r ∈ (sieveDivisors P D).filter (d ∣ ·), (selbergH g r)⁻¹ := by
      field_simp [hgd_ne, hG_ne]
    rw [hcancel, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  have hinner : ∀ r ∈ sieveDivisors P D,
      (∑ d ∈ (sieveDivisors P D).filter (m ∣ ·),
        if d ∣ r then ((ArithmeticFunction.moebius d : ℝ) / selbergG g P D) * (selbergH g r)⁻¹
        else 0) =
      if r = m then (ArithmeticFunction.moebius m : ℝ) / (selbergH g m * selbergG g P D) else 0 := by
    intro r hr
    by_cases hmr : m ∣ r
    · have hr_dvd : r ∣ P := ((mem_sieveDivisors hP0).mp hr).1
      have hr_sq : Squarefree r := hP.squarefree_of_dvd hr_dvd
      have hm_pos : 0 < m := Nat.pos_of_dvd_of_pos hmr (Nat.pos_of_ne_zero hr_sq.ne_zero)
      set q := r / m
      have hr_eq : r = m * q := (Nat.mul_div_cancel' hmr).symm
      have hcop_mq : Nat.Coprime m q := by
        rw [hr_eq] at hr_sq
        exact Nat.coprime_of_squarefree_mul hr_sq
      rw [← Finset.sum_filter]
      have hfilter_eq : ((sieveDivisors P D).filter (m ∣ ·)).filter (· ∣ r) =
          q.divisors.image (m * ·) := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨_, hmd⟩, hdr⟩
          rcases hmd with ⟨k, rfl⟩
          refine ⟨k, ⟨?_, ?_⟩, rfl⟩
          · rw [hr_eq] at hdr
            exact (mul_dvd_mul_iff_left hm_pos.ne').mp hdr
          · intro hq0
            rw [hq0, mul_zero] at hr_eq
            exact hr_sq.ne_zero hr_eq
        · rintro ⟨k, ⟨hkq, _⟩, rfl⟩
          have hmk_dvd_r : m * k ∣ r := by
            rw [hr_eq]
            exact mul_dvd_mul_left m hkq
          exact ⟨⟨sieveDivisors_dvd_closed hP0 hr hmk_dvd_r, dvd_mul_right m k⟩, hmk_dvd_r⟩
      rw [hfilter_eq, Finset.sum_image (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left hm_pos hxy)]
      have hsum_k : ∑ k ∈ q.divisors,
          ((ArithmeticFunction.moebius (m * k) : ℝ) / selbergG g P D) * (selbergH g r)⁻¹ =
          ((ArithmeticFunction.moebius m : ℝ) / selbergG g P D) * (selbergH g r)⁻¹ *
            ∑ k ∈ q.divisors, (ArithmeticFunction.moebius k : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hcop_mk : Nat.Coprime m k := hcop_mq.coprime_dvd_right (Nat.dvd_of_mem_divisors hk)
        have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_mk
        rw [hmu]
        push_cast
        ring
      rw [hsum_k, sum_moebius_divisors_eq q]
      have hq1_iff : q = 1 ↔ r = m := by
        constructor
        · intro hq1; rw [hr_eq, hq1, mul_one]
        · intro hrm
          have : m * q = m * 1 := by rw [← hr_eq, hrm, mul_one]
          exact Nat.eq_of_mul_eq_mul_left hm_pos this
      split_ifs with h1 h2 h2
      · rw [h2]; ring
      · exact absurd (hq1_iff.mp h1) h2
      · exact absurd (hq1_iff.mpr h2) h1
      · ring
    · have hzero : ∀ d ∈ (sieveDivisors P D).filter (m ∣ ·),
          (if d ∣ r then ((ArithmeticFunction.moebius d : ℝ) / selbergG g P D) * (selbergH g r)⁻¹
          else 0) = 0 := by
        intro d hd
        have hmd : m ∣ d := (Finset.mem_filter.mp hd).2
        have hndr : ¬ d ∣ r := fun hdr => hmr (hmd.trans hdr)
        simp [hndr]
      rw [Finset.sum_eq_zero hzero]
      have hne : r ≠ m := fun h => hmr (h ▸ dvd_rfl)
      simp [hne]
  rw [Finset.sum_congr rfl hinner]
  simp [hm]

lemma selbergWeight_one {g : ℕ → ℝ} (hg : IsMultDensity g)
    {P D : ℕ} (hP : Squarefree P) (hD : 1 ≤ D)
    (h01 : ∀ p ∈ P.primeFactors, 0 < g p ∧ g p < 1) :
    selbergWeight g P D 1 = 1 := by
  have h1 : 1 ∈ sieveDivisors P D := one_mem_sieveDivisors hP.ne_zero hD
  have hG_ne : selbergG g P D ≠ 0 := (selbergG_pos hg hP hD h01).ne'
  simp only [selbergWeight, h1, ↓reduceIte, ArithmeticFunction.moebius_apply_one, Int.cast_one,
    hg.1, one_mul, one_dvd, Finset.filter_true]
  change 1 / selbergG g P D * selbergG g P D = 1
  rw [one_div]
  exact inv_mul_cancel₀ hG_ne

/-- Uniform bound `|λ_d| ≤ 1` for the optimal Selberg weights. -/
theorem abs_selbergWeight_le_one {g : ℕ → ℝ} (hg : IsMultDensity g)
    {P D : ℕ} (hP : Squarefree P) (hD : 1 ≤ D)
    (h01 : ∀ p ∈ P.primeFactors, 0 < g p ∧ g p < 1) (d : ℕ) :
    |selbergWeight g P D d| ≤ 1 := by
  by_cases hd : d ∈ sieveDivisors P D
  · have hP0 : P ≠ 0 := hP.ne_zero
    have hd_mem := (mem_sieveDivisors hP0).mp hd
    have hd_sq : Squarefree d := hP.squarefree_of_dvd hd_mem.1
    have hd_01 : ∀ p ∈ d.primeFactors, 0 < g p ∧ g p < 1 := fun p hp =>
      h01 p (Nat.primeFactors_mono hd_mem.1 hP0 hp)
    have hgd_pos : 0 < g d := isMultDensity_pos_of_squarefree hg hd_sq fun p hp => (hd_01 p hp).1
    have hhd_pos : 0 < selbergH g d := selbergH_pos hg hd_sq hd_01
    have hG_pos : 0 < selbergG g P D := selbergG_pos hg hP hD h01
    have hmu_abs : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
      have h1 : |ArithmeticFunction.moebius d| = 1 :=
        ArithmeticFunction.abs_moebius_eq_one_of_squarefree hd_sq
      exact_mod_cast h1
    have hsum_nonneg : 0 ≤ ∑ m ∈ (sieveDivisors P D).filter (d ∣ ·), (selbergH g m)⁻¹ := by
      refine Finset.sum_nonneg fun m hm => ?_
      have hmS := (Finset.mem_filter.mp hm).1
      have hm_dvd := ((mem_sieveDivisors hP0).mp hmS).1
      exact inv_nonneg.mpr (selbergH_pos hg (hP.squarefree_of_dvd hm_dvd) fun p hp =>
        h01 p (Nat.primeFactors_mono hm_dvd hP0 hp)).le
    simp only [selbergWeight, hd, ↓reduceIte, abs_mul, abs_div, hmu_abs,
      abs_of_pos (mul_pos hgd_pos hG_pos), abs_of_nonneg hsum_nonneg]
    rw [one_div, inv_mul_eq_div, div_le_one (mul_pos hgd_pos hG_pos)]
    -- Prove `(g d)⁻¹ * ∑_{m ∈ S, d ∣ m} (h m)⁻¹ ≤ G(P, D)`
    -- Set `K := {k ∈ S(P, D) | Nat.Coprime d k ∧ d * k ≤ D}`.
    set K := (sieveDivisors P D).filter (fun k => Nat.Coprime d k ∧ d * k ≤ D)
    have hm_bij : ∑ m ∈ (sieveDivisors P D).filter (d ∣ ·), (selbergH g m)⁻¹ =
        (selbergH g d)⁻¹ * ∑ k ∈ K, (selbergH g k)⁻¹ := by
      have hset : (sieveDivisors P D).filter (d ∣ ·) = K.image (d * ·) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_image, K]
        constructor
        · rintro ⟨hmS, ⟨k, rfl⟩⟩
          have hdk_mem := (mem_sieveDivisors hP0).mp hmS
          have hdk_sq : Squarefree (d * k) := hP.squarefree_of_dvd hdk_mem.1
          have hcop : Nat.Coprime d k := Nat.coprime_of_squarefree_mul hdk_sq
          have hkS : k ∈ sieveDivisors P D :=
            sieveDivisors_dvd_closed hP0 hmS (dvd_mul_left k d)
          exact ⟨k, ⟨hkS, hcop, hdk_mem.2⟩, rfl⟩
        · rintro ⟨k, ⟨hkS, hcop, hdk_le⟩, rfl⟩
          have hk_dvd : k ∣ P := ((mem_sieveDivisors hP0).mp hkS).1
          have hdk_dvd : d * k ∣ P := hcop.mul_dvd_of_dvd_of_dvd hd_mem.1 hk_dvd
          exact ⟨(mem_sieveDivisors hP0).mpr ⟨hdk_dvd, hdk_le⟩, dvd_mul_right d k⟩
      rw [hset, Finset.sum_image (fun x _ y _ hxy =>
        Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd_sq.ne_zero) hxy), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hcop : Nat.Coprime d k := (Finset.mem_filter.mp hk).2.1
      rw [selbergH_mul_coprime hg hcop, mul_inv]
    -- Every pair `(e, k) ∈ d.divisors ×ˢ K` maps injectively into `sieveDivisors P D` via `e * k`
    have hprod_le : (∑ e ∈ d.divisors, (selbergH g e)⁻¹) * (∑ k ∈ K, (selbergH g k)⁻¹) ≤
        selbergG g P D := by
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) (↑(d.divisors ×ˢ K)) := by
        intro ⟨e₁, k₁⟩ h1 ⟨e₂, k₂⟩ h2 heq
        dsimp only at heq
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, K, Finset.mem_filter] at h1 h2
        have he₁_dvd : e₁ ∣ d := Nat.dvd_of_mem_divisors h1.1
        have he₂_dvd : e₂ ∣ d := Nat.dvd_of_mem_divisors h2.1
        have hcop12 : Nat.Coprime e₁ k₂ := h2.2.2.1.coprime_dvd_left he₁_dvd
        have hcop21 : Nat.Coprime e₂ k₁ := h1.2.2.1.coprime_dvd_left he₂_dvd
        have he1_dvd_e2 : e₁ ∣ e₂ := by
          have : e₁ ∣ e₂ * k₂ := heq ▸ dvd_mul_right e₁ k₁
          exact hcop12.dvd_of_dvd_mul_right this
        have he2_dvd_e1 : e₂ ∣ e₁ := by
          have : e₂ ∣ e₁ * k₁ := heq.symm ▸ dvd_mul_right e₂ k₂
          exact hcop21.dvd_of_dvd_mul_right this
        have he_eq : e₁ = e₂ := Nat.dvd_antisymm he1_dvd_e2 he2_dvd_e1
        have he_pos : 0 < e₁ := Nat.pos_of_dvd_of_pos he₁_dvd (Nat.pos_of_ne_zero hd_sq.ne_zero)
        have hk_eq : k₁ = k₂ := by
          rw [he_eq] at heq
          exact Nat.eq_of_mul_eq_mul_left (he_eq ▸ he_pos) heq
        exact Prod.ext he_eq hk_eq
      have hsub : (d.divisors ×ˢ K).image (fun x : ℕ × ℕ => x.1 * x.2) ⊆ sieveDivisors P D := by
        intro n hn
        rcases Finset.mem_image.mp hn with ⟨⟨e, k⟩, hek, rfl⟩
        simp only [Finset.mem_product, K, Finset.mem_filter] at hek
        have he_dvd_d : e ∣ d := Nat.dvd_of_mem_divisors hek.1
        have hk_dvd_P : k ∣ P := ((mem_sieveDivisors hP0).mp hek.2.1).1
        have hcop_ek : Nat.Coprime e k := hek.2.2.1.coprime_dvd_left he_dvd_d
        have hek_dvd_P : e * k ∣ P := hcop_ek.mul_dvd_of_dvd_of_dvd (he_dvd_d.trans hd_mem.1) hk_dvd_P
        have he_le_d : e ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd_sq.ne_zero) he_dvd_d
        have hek_le_D : e * k ≤ D := (Nat.mul_le_mul_right k he_le_d).trans hek.2.2.2
        exact (mem_sieveDivisors hP0).mpr ⟨hek_dvd_P, hek_le_D⟩
      have hsum_eq : ∑ x ∈ d.divisors ×ˢ K, (selbergH g x.1)⁻¹ * (selbergH g x.2)⁻¹ =
          ∑ m ∈ (d.divisors ×ˢ K).image (fun x : ℕ × ℕ => x.1 * x.2), (selbergH g m)⁻¹ := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun ⟨e, k⟩ hek => ?_
        simp only [Finset.mem_product, K, Finset.mem_filter] at hek
        have hcop_ek : Nat.Coprime e k := hek.2.2.1.coprime_dvd_left (Nat.dvd_of_mem_divisors hek.1)
        rw [selbergH_mul_coprime hg hcop_ek, mul_inv]
      rw [hsum_eq]
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun m hm _ => ?_
      have hm_dvd := ((mem_sieveDivisors hP0).mp hm).1
      exact inv_nonneg.mpr (selbergH_pos hg (hP.squarefree_of_dvd hm_dvd) fun p hp =>
        h01 p (Nat.primeFactors_mono hm_dvd hP0 hp)).le
    rw [sum_divisors_inv_selbergH hg hd_sq hd_01] at hprod_le
    rw [hm_bij]
    have hmul_le : g d * ((g d * selbergH g d)⁻¹ * ∑ k ∈ K, (selbergH g k)⁻¹) ≤
        g d * selbergG g P D :=
      mul_le_mul_of_nonneg_left hprod_le hgd_pos.le
    have hsimp : g d * ((g d * selbergH g d)⁻¹ * ∑ k ∈ K, (selbergH g k)⁻¹) =
        (selbergH g d)⁻¹ * ∑ k ∈ K, (selbergH g k)⁻¹ := by
      field_simp [hgd_pos.ne', hhd_pos.ne']
    linarith
  · simp [selbergWeight, hd]

/-- Exact minimum value of the Selberg quadratic form at the optimal weights:
`Q(λ^*) = 1 / G(P, D)`. -/
theorem selbergQuadForm_opt {g : ℕ → ℝ} (hg : IsMultDensity g)
    {P D : ℕ} (hP : Squarefree P) (hD : 1 ≤ D)
    (h01 : ∀ p ∈ P.primeFactors, 0 < g p ∧ g p < 1) :
    selbergQuadForm g P D (selbergWeight g P D) = (selbergG g P D)⁻¹ := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have hG_ne : selbergG g P D ≠ 0 := (selbergG_pos hg hP hD h01).ne'
  rw [selberg_quadratic_diagonalization hg hP h01]
  have hterm : ∀ m ∈ sieveDivisors P D,
      selbergH g m * (selbergTransform g P D (selbergWeight g P D) m) ^ 2 =
        (selbergG g P D)⁻¹ ^ 2 * (selbergH g m)⁻¹ := by
    intro m hm
    rw [selbergTransform_opt hg hP hD h01 hm]
    have hm_dvd : m ∣ P := ((mem_sieveDivisors hP0).mp hm).1
    have hm_sq : Squarefree m := hP.squarefree_of_dvd hm_dvd
    have hhm_ne : selbergH g m ≠ 0 :=
      (selbergH_pos hg hm_sq fun p hp => h01 p (Nat.primeFactors_mono hm_dvd hP0 hp)).ne'
    have hmu_sq : (ArithmeticFunction.moebius m : ℝ) ^ 2 = 1 := by
      have h1 : ArithmeticFunction.moebius m ^ 2 = 1 :=
        ArithmeticFunction.moebius_sq_eq_one_of_squarefree hm_sq
      exact_mod_cast h1
    rw [div_pow, hmu_sq]
    field_simp [hhm_ne, hG_ne]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  change (selbergG g P D)⁻¹ ^ 2 * selbergG g P D = (selbergG g P D)⁻¹
  field_simp [hG_ne]

/-- Optimality of the Selberg weights: for any weights `lam : ℕ → ℝ` with `lam 1 = 1`,
`1 / G(P, D) ≤ Q(lam)`. -/
theorem selbergQuadForm_ge_inv_G {g : ℕ → ℝ} (hg : IsMultDensity g)
    {P D : ℕ} (hP : Squarefree P) (hD : 1 ≤ D)
    (h01 : ∀ p ∈ P.primeFactors, 0 < g p ∧ g p < 1)
    (lam : ℕ → ℝ) (hlam1 : lam 1 = 1) :
    (selbergG g P D)⁻¹ ≤ selbergQuadForm g P D lam := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have hG_pos : 0 < selbergG g P D := selbergG_pos hg hP hD h01
  rw [selberg_quadratic_diagonalization hg hP h01]
  have hinv_lam1 : ∑ m ∈ sieveDivisors P D,
      (ArithmeticFunction.moebius m : ℝ) * selbergTransform g P D lam m = 1 := by
    unfold selbergTransform
    simp_rw [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    have hinner : ∀ d ∈ sieveDivisors P D,
        (∑ m ∈ sieveDivisors P D,
          if m ∣ d then (ArithmeticFunction.moebius m : ℝ) * (lam d * g d) else 0) =
        if d = 1 then 1 else 0 := by
      intro d hd
      rw [← Finset.sum_filter]
      have hfd : (sieveDivisors P D).filter (· ∣ d) = d.divisors := by
        ext m
        have hd_ne : d ≠ 0 := (hP.squarefree_of_dvd ((mem_sieveDivisors hP0).mp hd).1).ne_zero
        simp only [Finset.mem_filter, Nat.mem_divisors]
        exact ⟨fun h => ⟨h.2, hd_ne⟩, fun h => ⟨sieveDivisors_dvd_closed hP0 hd h.1, h.1⟩⟩
      rw [hfd, ← Finset.sum_mul, sum_moebius_divisors_eq d]
      split_ifs with hd1
      · rw [hd1, hlam1, hg.1]; ring
      · ring
    rw [Finset.sum_congr rfl hinner]
    simp [one_mem_sieveDivisors hP0 hD]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (sieveDivisors P D)
    (fun m => (ArithmeticFunction.moebius m : ℝ) / Real.sqrt (selbergH g m))
    (fun m => Real.sqrt (selbergH g m) * selbergTransform g P D lam m)
  have hlhs : ∑ m ∈ sieveDivisors P D,
      ((ArithmeticFunction.moebius m : ℝ) / Real.sqrt (selbergH g m)) *
        (Real.sqrt (selbergH g m) * selbergTransform g P D lam m) = 1 := by
    rw [← hinv_lam1]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_dvd : m ∣ P := ((mem_sieveDivisors hP0).mp hm).1
    have hhm_pos : 0 < selbergH g m :=
      selbergH_pos hg (hP.squarefree_of_dvd hm_dvd) fun p hp =>
        h01 p (Nat.primeFactors_mono hm_dvd hP0 hp)
    have hsq_ne : Real.sqrt (selbergH g m) ≠ 0 := (Real.sqrt_pos.mpr hhm_pos).ne'
    field_simp [hsq_ne]
  have hrhs1 : ∑ m ∈ sieveDivisors P D,
      ((ArithmeticFunction.moebius m : ℝ) / Real.sqrt (selbergH g m)) ^ 2 = selbergG g P D := by
    unfold selbergG
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_dvd : m ∣ P := ((mem_sieveDivisors hP0).mp hm).1
    have hm_sq : Squarefree m := hP.squarefree_of_dvd hm_dvd
    have hhm_pos : 0 < selbergH g m :=
      selbergH_pos hg hm_sq fun p hp => h01 p (Nat.primeFactors_mono hm_dvd hP0 hp)
    have hmu_sq : (ArithmeticFunction.moebius m : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hm_sq
    rw [div_pow, hmu_sq, Real.sq_sqrt hhm_pos.le, one_div]
  have hrhs2 : ∑ m ∈ sieveDivisors P D,
      (Real.sqrt (selbergH g m) * selbergTransform g P D lam m) ^ 2 =
      ∑ m ∈ sieveDivisors P D, selbergH g m * (selbergTransform g P D lam m) ^ 2 := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_dvd : m ∣ P := ((mem_sieveDivisors hP0).mp hm).1
    have hhm_pos : 0 < selbergH g m :=
      selbergH_pos hg (hP.squarefree_of_dvd hm_dvd) fun p hp =>
        h01 p (Nat.primeFactors_mono hm_dvd hP0 hp)
    rw [mul_pow, Real.sq_sqrt hhm_pos.le]
  rw [hlhs, hrhs1, hrhs2, one_pow] at hcs
  exact (inv_le_iff_one_le_mul₀' hG_pos).mpr hcs

/-- The sifted sum `S(A, a, P) = ∑_{n ∈ A, gcd(n, P) = 1} a(n)`. -/
def siftedSum (A : Finset ℕ) (a : ℕ → ℝ) (P : ℕ) : ℝ :=
  ∑ n ∈ A.filter (fun n => Nat.Coprime n P), a n

/-- The multiples sum `A_d = ∑_{n ∈ A, d ∣ n} a(n)`. -/
def multiplesSum (A : Finset ℕ) (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ n ∈ A.filter (d ∣ ·), a n

/-- The sieve remainder `r_d = A_d - X * g(d)`. -/
def sieveRemainder (A : Finset ℕ) (a : ℕ → ℝ) (X : ℝ) (g : ℕ → ℝ) (d : ℕ) : ℝ :=
  multiplesSum A a d - X * g d

/-- Fundamental Selberg upper-bound inequality for arbitrary weights `lam` with `lam 1 = 1`. -/
theorem selberg_fundamental_bound (A : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ n ∈ A, 0 ≤ a n) {P D : ℕ} (hP : P ≠ 0) (hD : 1 ≤ D)
    (X : ℝ) (g lam : ℕ → ℝ) (hlam1 : lam 1 = 1) :
    siftedSum A a P ≤
      X * selbergQuadForm g P D lam +
        ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
          lam d₁ * lam d₂ * sieveRemainder A a X g (Nat.lcm d₁ d₂) := by
  have h1S : 1 ∈ sieveDivisors P D := one_mem_sieveDivisors hP hD
  have hsift_le : siftedSum A a P ≤
      ∑ n ∈ A, a n * (∑ d ∈ (sieveDivisors P D).filter (· ∣ n), lam d) ^ 2 := by
    unfold siftedSum
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun n hn => ?_
    split_ifs with hcop
    · have hfilt : (sieveDivisors P D).filter (· ∣ n) = {1} := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro ⟨hdS, hdn⟩
          have hdP : d ∣ P := ((mem_sieveDivisors hP).mp hdS).1
          exact Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hdn hdP)
        · rintro rfl
          exact ⟨h1S, one_dvd n⟩
      rw [hfilt, Finset.sum_singleton, hlam1, one_pow, mul_one]
    · exact mul_nonneg (ha n hn) (sq_nonneg _)
  have hexpand : ∑ n ∈ A, a n * (∑ d ∈ (sieveDivisors P D).filter (· ∣ n), lam d) ^ 2 =
      ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
        lam d₁ * lam d₂ * multiplesSum A a (Nat.lcm d₁ d₂) := by
    have hstep : ∀ n ∈ A,
        a n * (∑ d ∈ (sieveDivisors P D).filter (· ∣ n), lam d) ^ 2 =
          ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
            if Nat.lcm d₁ d₂ ∣ n then lam d₁ * lam d₂ * a n else 0 := by
      intro n _
      rw [sq, Finset.sum_mul, Finset.mul_sum]
      simp_rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun d₁ _ => ?_
      by_cases h1 : d₁ ∣ n
      · simp only [h1, ↓reduceIte]
        refine Finset.sum_congr rfl fun d₂ _ => ?_
        have hlcm_iff : Nat.lcm d₁ d₂ ∣ n ↔ d₁ ∣ n ∧ d₂ ∣ n := Nat.lcm_dvd_iff
        by_cases h2 : d₂ ∣ n
        · simp [hlcm_iff, h1, h2]
          ring
        · simp [hlcm_iff, h1, h2]
      · have hnot : ∀ d₂ ∈ sieveDivisors P D, ¬ Nat.lcm d₁ d₂ ∣ n := fun d₂ _ hl =>
          h1 ((Nat.dvd_lcm_left d₁ d₂).trans hl)
        simp only [h1, ↓reduceIte]
        symm
        exact Finset.sum_eq_zero fun d₂ hd₂ => by simp [hnot d₂ hd₂]
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₂ _ => ?_
    unfold multiplesSum
    rw [Finset.mul_sum, Finset.sum_filter]
  have hsplit : ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
        lam d₁ * lam d₂ * multiplesSum A a (Nat.lcm d₁ d₂) =
      X * selbergQuadForm g P D lam +
        ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
          lam d₁ * lam d₂ * sieveRemainder A a X g (Nat.lcm d₁ d₂) := by
    unfold selbergQuadForm sieveRemainder
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
    ring
  linarith

/-- **General Abstract Selberg Upper-Bound Sieve**:
With explicit optimal weights `λ_d = selbergWeight g P D d`,
`S(A, a, P) ≤ X / G(P, D) + ∑_{d₁, d₂ ∈ S(P, D)} |λ_{d₁} λ_{d₂} r_{lcm(d₁, d₂)}|`. -/
theorem selberg_upper_bound_sieve (A : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ n ∈ A, 0 ≤ a n) {P D : ℕ} (hP : Squarefree P) (hD : 1 ≤ D)
    (X : ℝ) {g : ℕ → ℝ} (hg : IsMultDensity g)
    (h01 : ∀ p ∈ P.primeFactors, 0 < g p ∧ g p < 1) :
    siftedSum A a P ≤
      X / selbergG g P D +
        ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
          |selbergWeight g P D d₁ * selbergWeight g P D d₂ *
            sieveRemainder A a X g (Nat.lcm d₁ d₂)| := by
  have hbase := selberg_fundamental_bound A a ha hP.ne_zero hD X g (selbergWeight g P D)
    (selbergWeight_one hg hP hD h01)
  rw [selbergQuadForm_opt hg hP hD h01, ← div_eq_mul_inv] at hbase
  have herr : ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
        selbergWeight g P D d₁ * selbergWeight g P D d₂ *
          sieveRemainder A a X g (Nat.lcm d₁ d₂) ≤
      ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
        |selbergWeight g P D d₁ * selbergWeight g P D d₂ *
          sieveRemainder A a X g (Nat.lcm d₁ d₂)| :=
    Finset.sum_le_sum fun d₁ _ => Finset.sum_le_sum fun d₂ _ => le_abs_self _
  linarith

/-- **Simplified Selberg Upper-Bound Sieve** using `|λ_d| ≤ 1`:
`S(A, a, P) ≤ X / G(P, D) + ∑_{d₁, d₂ ∈ S(P, D)} |r_{lcm(d₁, d₂)}|`. -/
theorem selberg_upper_bound_sieve_simplified (A : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ n ∈ A, 0 ≤ a n) {P D : ℕ} (hP : Squarefree P) (hD : 1 ≤ D)
    (X : ℝ) {g : ℕ → ℝ} (hg : IsMultDensity g)
    (h01 : ∀ p ∈ P.primeFactors, 0 < g p ∧ g p < 1) :
    siftedSum A a P ≤
      X / selbergG g P D +
        ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
          |sieveRemainder A a X g (Nat.lcm d₁ d₂)| := by
  have h := selberg_upper_bound_sieve A a ha hP hD X hg h01
  have herr : ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
        |selbergWeight g P D d₁ * selbergWeight g P D d₂ *
          sieveRemainder A a X g (Nat.lcm d₁ d₂)| ≤
      ∑ d₁ ∈ sieveDivisors P D, ∑ d₂ ∈ sieveDivisors P D,
        |sieveRemainder A a X g (Nat.lcm d₁ d₂)| := by
    refine Finset.sum_le_sum fun d₁ _ => Finset.sum_le_sum fun d₂ _ => ?_
    rw [abs_mul, abs_mul]
    have h1 := abs_selbergWeight_le_one hg hP hD h01 d₁
    have h2 := abs_selbergWeight_le_one hg hP hD h01 d₂
    have h12 : |selbergWeight g P D d₁| * |selbergWeight g P D d₂| ≤ 1 := by
      calc |selbergWeight g P D d₁| * |selbergWeight g P D d₂| ≤ 1 * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    calc |selbergWeight g P D d₁| * |selbergWeight g P D d₂| *
            |sieveRemainder A a X g (Nat.lcm d₁ d₂)|
        ≤ 1 * |sieveRemainder A a X g (Nat.lcm d₁ d₂)| :=
          mul_le_mul_of_nonneg_right h12 (abs_nonneg _)
      _ = |sieveRemainder A a X g (Nat.lcm d₁ d₂)| := one_mul _
  linarith

/-! ### Explicit Brun–Titchmarsh-Style Corollaries via Selberg's Sieve -/

lemma inv_isMultDensity : IsMultDensity (fun d : ℕ => (d : ℝ)⁻¹) := by
  refine ⟨by simp, fun a b _ => ?_⟩
  push_cast
  rw [mul_inv]

lemma selbergH_inv_eq_totient {m : ℕ} (hm : Squarefree m) :
    selbergH (fun d : ℕ => (d : ℝ)⁻¹) m = (Nat.totient m : ℝ) := by
  rw [selbergH_eq_prod_primeFactors inv_isMultDensity hm]
  have hm0 : m ≠ 0 := hm.ne_zero
  have hprod : m = ∏ p ∈ m.primeFactors, p := squarefree_eq_prod_primeFactors hm
  have htot : (Nat.totient m : ℝ) = ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := by
    conv_lhs => rw [hprod]
    have hprimes : ∀ p ∈ m.primeFactors, Nat.Prime p := fun _ hp => Nat.prime_of_mem_primeFactors hp
    generalize m.primeFactors = S at hprimes ⊢
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have ha_p : Nat.Prime a := hprimes a (Finset.mem_insert_self a s)
      have hs_p : ∀ p ∈ s, Nat.Prime p := fun p hp => hprimes p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
        Nat.Coprime.prod_right fun p hp =>
          (Nat.coprime_primes ha_p (hs_p p hp)).mpr (fun h => ha (h ▸ hp))
      rw [Nat.totient_mul hcop, Nat.totient_prime ha_p]
      push_cast
      rw [Nat.cast_sub ha_p.one_le, Nat.cast_one, ih hs_p]
  rw [htot]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [inv_inv]

/-- Radical of a positive natural number: `rad(n) = ∏_{p ∈ n.primeFactors} p`. -/
def rad (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

lemma rad_squarefree (n : ℕ) : Squarefree (rad n) :=
  squarefree_prod_primes _ fun _ hp => Nat.prime_of_mem_primeFactors hp

lemma rad_dvd_self {n : ℕ} (hn : n ≠ 0) : rad n ∣ n := by
  unfold rad
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
  have hp_prime := Nat.prime_of_mem_primeFactors hp
  have hpos : 1 ≤ n.factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp_prime hn (Nat.dvd_of_mem_primeFactors hp)
  exact dvd_pow_self p (by omega)

lemma rad_le_self {n : ℕ} (hn : 0 < n) : rad n ≤ n :=
  Nat.le_of_dvd hn (rad_dvd_self hn.ne')

lemma rad_primeFactors {n : ℕ} (_hn : n ≠ 0) : (rad n).primeFactors = n.primeFactors := by
  unfold rad
  have hprimes : ∀ p ∈ n.primeFactors, Nat.Prime p := fun _ hp => Nat.prime_of_mem_primeFactors hp
  generalize n.primeFactors = S at hprimes ⊢
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ha_p : Nat.Prime a := hprimes a (Finset.mem_insert_self a s)
    have hs_p : ∀ p ∈ s, Nat.Prime p := fun p hp => hprimes p (Finset.mem_insert_of_mem hp)
    have hs_ne : ∏ p ∈ s, p ≠ 0 := (Finset.prod_pos fun p hp => (hs_p p hp).pos).ne'
    rw [Finset.prod_insert ha, Nat.primeFactors_mul ha_p.ne_zero hs_ne,
      ha_p.primeFactors, ih hs_p]
    ext p
    simp

lemma sum_inv_pow_Icc_le {p D : ℕ} (hp : Nat.Prime p) :
    ∑ k ∈ Finset.Icc 1 D, ((p : ℝ) ^ k)⁻¹ ≤ ((p : ℝ) - 1)⁻¹ := by
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
  have hgeom : ∑ k ∈ Finset.Icc 1 D, ((p : ℝ) ^ k)⁻¹ =
      ((p : ℝ)⁻¹ - ((p : ℝ)⁻¹) ^ (D + 1)) / (1 - (p : ℝ)⁻¹) := by
    have h1 : ∑ k ∈ Finset.Icc 1 D, ((p : ℝ) ^ k)⁻¹ =
        (∑ k ∈ Finset.range (D + 1), ((p : ℝ)⁻¹) ^ k) - 1 := by
      rw [Finset.sum_range_succ', pow_zero, add_sub_cancel_right]
      refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        simp only [Finset.mem_range]
        omega
      · intro k₁ hk₁ k₂ hk₂ heq
        simp only [Finset.mem_Icc] at hk₁ hk₂
        omega
      · intro j hj
        simp only [Finset.mem_range] at hj
        exact ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        rw [inv_pow]
        congr 2
        omega
    rw [h1, geom_sum_eq (ne_of_lt (inv_lt_one_of_one_lt₀ hp_gt1))]
    have h1p : 1 - (p : ℝ)⁻¹ ≠ 0 := by linarith [inv_lt_one_of_one_lt₀ hp_gt1]
    have hneg : ((p : ℝ)⁻¹ ^ (D + 1) - 1) / ((p : ℝ)⁻¹ - 1) =
        (1 - (p : ℝ)⁻¹ ^ (D + 1)) / (1 - (p : ℝ)⁻¹) := by
      rw [← neg_div_neg_eq]
      congr 1 <;> ring
    rw [hneg, div_sub_one h1p]
    congr 1
    ring
  rw [hgeom]
  have hden_pos : 0 < 1 - (p : ℝ)⁻¹ := by linarith [inv_lt_one_of_one_lt₀ hp_gt1]
  have hnum_le : (p : ℝ)⁻¹ - ((p : ℝ)⁻¹) ^ (D + 1) ≤ (p : ℝ)⁻¹ := by
    have : 0 ≤ ((p : ℝ)⁻¹) ^ (D + 1) := by positivity
    linarith
  calc ((p : ℝ)⁻¹ - ((p : ℝ)⁻¹) ^ (D + 1)) / (1 - (p : ℝ)⁻¹)
      ≤ (p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹) := div_le_div_of_nonneg_right hnum_le hden_pos.le
    _ = ((p : ℝ) - 1)⁻¹ := by
        have hsub : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp [hp_pos.ne', hsub]

lemma sum_inv_primeFactors_eq_le (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (D : ℕ) :
    ∑ n ∈ (Finset.Icc 1 D).filter (fun n => n.primeFactors = S), (n : ℝ)⁻¹ ≤
      ∏ p ∈ S, ((p : ℝ) - 1)⁻¹ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    have hsub : (Finset.Icc 1 D).filter (fun n => n.primeFactors = ∅) ⊆ {1} := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      simp only [Finset.mem_singleton]
      by_contra hne1
      have hgt1 : 1 < n := by omega
      rcases Nat.exists_prime_and_dvd (by omega : n ≠ 1) with ⟨p, hp, hpn⟩
      have hp_mem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩
      rw [hn.2] at hp_mem
      exact Finset.notMem_empty p hp_mem
    calc ∑ n ∈ (Finset.Icc 1 D).filter (fun n => n.primeFactors = ∅), (n : ℝ)⁻¹
        ≤ ∑ n ∈ ({1} : Finset ℕ), (n : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = 1 := by simp
  | @insert a s ha ih =>
    have ha_p : Nat.Prime a := hS a (Finset.mem_insert_self a s)
    have hs_p : ∀ p ∈ s, Nat.Prime p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert ha]
    set F := (Finset.Icc 1 D).filter (fun n => n.primeFactors = insert a s)
    set R := (Finset.Icc 1 D).filter (fun r => r.primeFactors = s)
    -- Map `n ∈ F` injectively to `(n.factorization a, n / a ^ (n.factorization a)) ∈ Icc 1 D ×ˢ R`
    set φ : ℕ → ℕ × ℕ := fun n => (n.factorization a, n / a ^ (n.factorization a))
    have hφ_mem : ∀ n ∈ F, φ n ∈ Finset.Icc 1 D ×ˢ R := by
      intro n hn
      simp only [F, Finset.mem_filter, Finset.mem_Icc] at hn
      have hn0 : n ≠ 0 := by omega
      have ha_mem : a ∈ n.primeFactors := by rw [hn.2]; exact Finset.mem_insert_self a s
      have ha_dvd : a ∣ n := Nat.dvd_of_mem_primeFactors ha_mem
      set k := n.factorization a
      have hk_pos : 1 ≤ k := Nat.Prime.factorization_pos_of_dvd ha_p hn0 ha_dvd
      have hpow_dvd : a ^ k ∣ n := Nat.ordProj_dvd n a
      have hk_le : k ≤ D := by
        have h1 : k < a ^ k := Nat.lt_pow_self ha_p.one_lt
        have h2 : a ^ k ≤ n := Nat.le_of_dvd (by omega) hpow_dvd
        omega
      set r := n / a ^ k
      have hnr : a ^ k * r = n := Nat.mul_div_cancel' hpow_dvd
      have hr_pos : 1 ≤ r := by
        by_contra h0
        have hr0 : r = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp h0)
        rw [hr0, mul_zero] at hnr
        exact hn0 hnr.symm
      have hr_le : r ≤ D := (Nat.div_le_self n (a ^ k)).trans hn.1.2
      have hna_dvd_r : ¬ a ∣ r := by
        intro har
        have hpow1 : a ^ (k + 1) ∣ n := by
          rw [pow_succ, ← hnr]
          exact mul_dvd_mul_left (a ^ k) har
        have hle := (ha_p.pow_dvd_iff_le_factorization hn0).mp hpow1
        omega
      have hr_pf : r.primeFactors = s := by
        have hmul_pf : n.primeFactors = (a ^ k).primeFactors ∪ r.primeFactors := by
          rw [← hnr, Nat.primeFactors_mul (pow_ne_zero k ha_p.ne_zero) (by exact Nat.pos_iff_ne_zero.mp hr_pos)]
        have hpow_pf : (a ^ k).primeFactors = {a} := by
          rw [Nat.primeFactors_pow a (Nat.pos_iff_ne_zero.mp hk_pos), ha_p.primeFactors]
        rw [hpow_pf, hn.2] at hmul_pf
        ext p
        constructor
        · intro hp
          have hp_in : p ∈ insert a s := by
            rw [hmul_pf]; exact Finset.mem_union_right _ hp
          rcases Finset.mem_insert.mp hp_in with rfl | hps
          · exact absurd (Nat.dvd_of_mem_primeFactors hp) hna_dvd_r
          · exact hps
        · intro hp
          have hp_in : p ∈ ({a} : Finset ℕ) ∪ r.primeFactors := by
            rw [← hmul_pf]; exact Finset.mem_insert_of_mem hp
          rcases Finset.mem_union.mp hp_in with hpa | hpr
          · rw [Finset.mem_singleton.mp hpa] at hp
            exact absurd hp ha
          · exact hpr
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hk_pos, hk_le⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr_pos, hr_le⟩, hr_pf⟩⟩
    have hφ_inj : Set.InjOn φ ↑F := by
      intro n₁ hn₁ n₂ hn₂ heq
      have h1 : a ^ (n₁.factorization a) * (n₁ / a ^ (n₁.factorization a)) = n₁ :=
        Nat.mul_div_cancel' (Nat.ordProj_dvd n₁ a)
      have h2 : a ^ (n₂.factorization a) * (n₂ / a ^ (n₂.factorization a)) = n₂ :=
        Nat.mul_div_cancel' (Nat.ordProj_dvd n₂ a)
      have hk := congr_arg Prod.fst heq
      have hr := congr_arg Prod.snd heq
      dsimp [φ] at hk hr
      rw [← h1, ← h2, hr, hk]
    have hsum_le : ∑ n ∈ F, (n : ℝ)⁻¹ ≤
        ∑ x ∈ Finset.Icc 1 D ×ˢ R, ((a : ℝ) ^ x.1)⁻¹ * (x.2 : ℝ)⁻¹ := by
      calc ∑ n ∈ F, (n : ℝ)⁻¹
          = ∑ n ∈ F, ((a : ℝ) ^ (φ n).1)⁻¹ * ((φ n).2 : ℝ)⁻¹ := by
            refine Finset.sum_congr rfl fun n _ => ?_
            have hmul : a ^ (n.factorization a) * (n / a ^ (n.factorization a)) = n :=
              Nat.mul_div_cancel' (Nat.ordProj_dvd n a)
            dsimp [φ]
            conv_lhs => rw [← hmul]
            push_cast
            rw [mul_inv]
        _ = ∑ x ∈ F.image φ, ((a : ℝ) ^ x.1)⁻¹ * (x.2 : ℝ)⁻¹ :=
            (Finset.sum_image (f := fun x : ℕ × ℕ => ((a : ℝ) ^ x.1)⁻¹ * (x.2 : ℝ)⁻¹) hφ_inj).symm
        _ ≤ ∑ x ∈ Finset.Icc 1 D ×ˢ R, ((a : ℝ) ^ x.1)⁻¹ * (x.2 : ℝ)⁻¹ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
            intro x hx
            rcases Finset.mem_image.mp hx with ⟨n, hn, rfl⟩
            exact hφ_mem n hn
    rw [Finset.sum_product] at hsum_le
    dsimp only at hsum_le
    rw [← Finset.sum_mul_sum] at hsum_le
    calc ∑ n ∈ F, (n : ℝ)⁻¹
        ≤ (∑ k ∈ Finset.Icc 1 D, ((a : ℝ) ^ k)⁻¹) * (∑ r ∈ R, (r : ℝ)⁻¹) := hsum_le
      _ ≤ ((a : ℝ) - 1)⁻¹ * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ :=
          mul_le_mul (sum_inv_pow_Icc_le ha_p) (ih hs_p)
            (Finset.sum_nonneg fun _ _ => by positivity)
            (inv_nonneg.mpr (by
              have h1a : (1 : ℝ) ≤ (a : ℝ) := Nat.one_le_cast.mpr ha_p.one_le
              linarith))

lemma sum_inv_rad_fiber_le {m D : ℕ} (hm : Squarefree m) :
    ∑ n ∈ (Finset.Icc 1 D).filter (fun n => rad n = m), (n : ℝ)⁻¹ ≤
      (Nat.totient m : ℝ)⁻¹ := by
  have hsub : (Finset.Icc 1 D).filter (fun n => rad n = m) ⊆
      (Finset.Icc 1 D).filter (fun n => n.primeFactors = m.primeFactors) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    refine ⟨hn.1, ?_⟩
    rw [← rad_primeFactors (by omega : n ≠ 0), hn.2]
  have htot_eq : (Nat.totient m : ℝ)⁻¹ = ∏ p ∈ m.primeFactors, ((p : ℝ) - 1)⁻¹ := by
    have h1 := selbergH_inv_eq_totient hm
    rw [selbergH_eq_prod_primeFactors inv_isMultDensity hm] at h1
    rw [← h1, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [inv_inv]
  rw [htot_eq]
  calc ∑ n ∈ (Finset.Icc 1 D).filter (fun n => rad n = m), (n : ℝ)⁻¹
      ≤ ∑ n ∈ (Finset.Icc 1 D).filter (fun n => n.primeFactors = m.primeFactors), (n : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∏ p ∈ m.primeFactors, ((p : ℝ) - 1)⁻¹ :=
        sum_inv_primeFactors_eq_le m.primeFactors
          (fun _ hp => Nat.prime_of_mem_primeFactors hp) D

lemma selbergG_inv_ge_harmonic {z D : ℕ} (hDz : D ≤ z) :
    ∑ n ∈ Finset.Icc 1 D, (n : ℝ)⁻¹ ≤ selbergG (fun d : ℕ => (d : ℝ)⁻¹) (primorial z) D := by
  unfold selbergG
  have hmaps : ∀ n ∈ Finset.Icc 1 D, rad n ∈ sieveDivisors (primorial z) D := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [mem_sieveDivisors (primorial_ne_zero z)]
    have hle : rad n ≤ D := (rad_le_self (by omega)).trans hn.2
    exact ⟨squarefree_dvd_primorial (rad_squarefree n) (hle.trans hDz), hle⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun m hm => ?_
  have hm_dvd : m ∣ primorial z := ((mem_sieveDivisors (primorial_ne_zero z)).mp hm).1
  have hm_sq : Squarefree m := (primorial_squarefree z).squarefree_of_dvd hm_dvd
  rw [selbergH_inv_eq_totient hm_sq]
  exact sum_inv_rad_fiber_le hm_sq

lemma harmonic_ge_log_succ (D : ℕ) :
    Real.log ((D : ℝ) + 1) ≤ ∑ n ∈ Finset.Icc 1 D, (n : ℝ)⁻¹ := by
  induction D with
  | zero => simp
  | succ D ih =>
    have hIcc : Finset.Icc 1 (D + 1) = insert (D + 1) (Finset.Icc 1 D) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : D + 1 ∉ Finset.Icc 1 D := by simp
    rw [hIcc, Finset.sum_insert hnot]
    have hD1_pos : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    have hD2_pos : (0 : ℝ) < (D : ℝ) + 2 := by positivity
    have hlog_step : Real.log (((D + 1 : ℕ) : ℝ) + 1) - Real.log ((D : ℝ) + 1) ≤
        (((D + 1 : ℕ) : ℝ))⁻¹ := by
      have hcast : ((D + 1 : ℕ) : ℝ) + 1 = (D : ℝ) + 2 := by push_cast; ring
      have hcast1 : ((D + 1 : ℕ) : ℝ) = (D : ℝ) + 1 := by push_cast; ring
      rw [hcast, hcast1, ← Real.log_div hD2_pos.ne' hD1_pos.ne']
      have hle := Real.log_le_sub_one_of_pos (div_pos hD2_pos hD1_pos)
      have hEq : ((D : ℝ) + 2) / ((D : ℝ) + 1) - 1 = ((D : ℝ) + 1)⁻¹ := by
        field_simp [hD1_pos.ne']
        ring
      linarith
    linarith

lemma card_multiples_Icc_eq (M N d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Icc (M + 1) (M + N)).filter (d ∣ ·)).card = (M + N) / d - M / d := by
  have hbij : (Finset.Icc (M + 1) (M + N)).filter (d ∣ ·) =
      (Finset.Icc (M / d + 1) ((M + N) / d)).image (d * ·) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · have : M / d < k := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          linarith
        omega
      · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
    · rintro ⟨k, ⟨hlo, hhi⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right d k⟩
      · have hlt : M < k * d := (Nat.div_lt_iff_lt_mul (by omega)).mp (by omega)
        linarith
      · have hle : k * d ≤ M + N := (Nat.le_div_iff_mul_le (by omega)).mp hhi
        linarith
  rw [hbij, Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left (by omega) h),
    Nat.card_Icc]
  have hle : M / d ≤ (M + N) / d := Nat.div_le_div_right (Nat.le_add_right M N)
  omega

lemma abs_sieveRemainder_Icc_le_one (M N d : ℕ) (hd : 1 ≤ d) :
    |sieveRemainder (Finset.Icc (M + 1) (M + N)) (fun _ => (1 : ℝ)) (N : ℝ)
      (fun k => (k : ℝ)⁻¹) d| ≤ 1 := by
  unfold sieveRemainder multiplesSum
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_multiples_Icc_eq M N d hd]
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hle_div : M / d ≤ (M + N) / d := Nat.div_le_div_right (Nat.le_add_right M N)
  rw [Nat.cast_sub hle_div]
  have h1_hi : (((M + N) / d : ℕ) : ℝ) ≤ ((M + N : ℕ) : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hd_pos]
    exact_mod_cast Nat.div_mul_le_self (M + N) d
  have h1_lo : ((M + N : ℕ) : ℝ) / (d : ℝ) - 1 < (((M + N) / d : ℕ) : ℝ) := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hd_pos]
    have hlt : M + N < ((M + N) / d + 1) * d := by
      have := Nat.lt_div_mul_add (a := M + N) (b := d) (by omega)
      linarith
    exact_mod_cast hlt
  have h2_hi : ((M / d : ℕ) : ℝ) ≤ (M : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hd_pos]
    exact_mod_cast Nat.div_mul_le_self M d
  have h2_lo : (M : ℝ) / (d : ℝ) - 1 < ((M / d : ℕ) : ℝ) := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hd_pos]
    have hlt : M < (M / d + 1) * d := by
      have := Nat.lt_div_mul_add (a := M) (b := d) (by omega)
      linarith
    exact_mod_cast hlt
  have hN_eq : ((M + N : ℕ) : ℝ) / (d : ℝ) - (M : ℝ) / (d : ℝ) = (N : ℝ) * (d : ℝ)⁻¹ := by
    push_cast
    ring
  rw [abs_le]
  constructor <;> linarith

/-- **Selberg Sieve Interval Corollary**: For any `M, N, z, D` with `1 ≤ D ≤ z`,
the number of integers in `(M, M + N]` coprime to `P(z)` is at most `N / log(D + 1) + D^2`. -/
theorem selberg_coprime_interval_bound (M N z D : ℕ) (hD : 1 ≤ D) (hDz : D ≤ z) :
    (((Finset.Icc (M + 1) (M + N)).filter (fun n => Nat.Coprime n (primorial z))).card : ℝ) ≤
      (N : ℝ) / Real.log ((D : ℝ) + 1) + (D : ℝ) ^ 2 := by
  have hP := primorial_squarefree z
  have h01 : ∀ p ∈ (primorial z).primeFactors, 0 < (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ < 1 := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.one_lt
    exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ hp_gt1⟩
  have hsel := selberg_upper_bound_sieve_simplified (Finset.Icc (M + 1) (M + N))
    (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) hP hD (N : ℝ) inv_isMultDensity h01
  have hsift_eq : siftedSum (Finset.Icc (M + 1) (M + N)) (fun _ => (1 : ℝ)) (primorial z) =
      (((Finset.Icc (M + 1) (M + N)).filter (fun n => Nat.Coprime n (primorial z))).card : ℝ) := by
    simp [siftedSum]
  rw [hsift_eq] at hsel
  have hlog_pos : 0 < Real.log ((D : ℝ) + 1) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    linarith
  have hG_ge : Real.log ((D : ℝ) + 1) ≤ selbergG (fun d : ℕ => (d : ℝ)⁻¹) (primorial z) D :=
    (harmonic_ge_log_succ D).trans (selbergG_inv_ge_harmonic hDz)
  have hmain : (N : ℝ) / selbergG (fun d : ℕ => (d : ℝ)⁻¹) (primorial z) D ≤
      (N : ℝ) / Real.log ((D : ℝ) + 1) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg N) hlog_pos hG_ge
  have herr_le : ∑ d₁ ∈ sieveDivisors (primorial z) D, ∑ d₂ ∈ sieveDivisors (primorial z) D,
        |sieveRemainder (Finset.Icc (M + 1) (M + N)) (fun _ => (1 : ℝ)) (N : ℝ)
          (fun k => (k : ℝ)⁻¹) (Nat.lcm d₁ d₂)| ≤ (D : ℝ) ^ 2 := by
    have hcard_le : (sieveDivisors (primorial z) D).card ≤ D := by
      have hsub : sieveDivisors (primorial z) D ⊆ Finset.Icc 1 D := by
        intro d hd
        have hd_mem := (mem_sieveDivisors (primorial_ne_zero z)).mp hd
        have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hd_mem.1 (primorial_pos z)
        exact Finset.mem_Icc.mpr ⟨hd_pos, hd_mem.2⟩
      calc (sieveDivisors (primorial z) D).card ≤ (Finset.Icc 1 D).card := Finset.card_le_card hsub
        _ = D := by simp
    have hsum1 : ∑ d₁ ∈ sieveDivisors (primorial z) D, ∑ d₂ ∈ sieveDivisors (primorial z) D,
          |sieveRemainder (Finset.Icc (M + 1) (M + N)) (fun _ => (1 : ℝ)) (N : ℝ)
            (fun k => (k : ℝ)⁻¹) (Nat.lcm d₁ d₂)| ≤
        ∑ _d₁ ∈ sieveDivisors (primorial z) D, ∑ _d₂ ∈ sieveDivisors (primorial z) D, (1 : ℝ) := by
      refine Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => ?_
      have hd₁_pos : 0 < d₁ :=
        Nat.pos_of_dvd_of_pos ((mem_sieveDivisors (primorial_ne_zero z)).mp hd₁).1 (primorial_pos z)
      have hd₂_pos : 0 < d₂ :=
        Nat.pos_of_dvd_of_pos ((mem_sieveDivisors (primorial_ne_zero z)).mp hd₂).1 (primorial_pos z)
      have hlcm_pos : 1 ≤ Nat.lcm d₁ d₂ := Nat.lcm_pos hd₁_pos hd₂_pos
      exact abs_sieveRemainder_Icc_le_one M N (Nat.lcm d₁ d₂) hlcm_pos
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum1
    have hcard_r : ((sieveDivisors (primorial z) D).card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hcard_le
    nlinarith
  linarith

/-- **Primes-in-Interval Upper Bound via Selberg's Sieve**:
For all `M, N : ℕ` and `1 ≤ D`,
`π(M + N) - π(M) ≤ D + N / log(D + 1) + D^2`. -/
theorem selberg_primes_in_interval_bound (M N D : ℕ) (hD : 1 ≤ D) :
    (((Finset.Icc (M + 1) (M + N)).filter Nat.Prime).card : ℝ) ≤
      (D : ℝ) + (N : ℝ) / Real.log ((D : ℝ) + 1) + (D : ℝ) ^ 2 := by
  have hsub : (Finset.Icc (M + 1) (M + N)).filter Nat.Prime ⊆
      Finset.Icc 1 D ∪ (Finset.Icc (M + 1) (M + N)).filter (fun n => Nat.Coprime n (primorial D)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    by_cases hle : p ≤ D
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hp.2.one_le, hle⟩)
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hp.1, ?_⟩)
      rw [hp.2.coprime_iff_not_dvd, prime_dvd_primorial_iff hp.2]
      exact hle
  have hcard : ((Finset.Icc (M + 1) (M + N)).filter Nat.Prime).card ≤
      D + ((Finset.Icc (M + 1) (M + N)).filter (fun n => Nat.Coprime n (primorial D))).card := by
    calc ((Finset.Icc (M + 1) (M + N)).filter Nat.Prime).card
        ≤ (Finset.Icc 1 D ∪ (Finset.Icc (M + 1) (M + N)).filter
            (fun n => Nat.Coprime n (primorial D))).card := Finset.card_le_card hsub
      _ ≤ (Finset.Icc 1 D).card +
          ((Finset.Icc (M + 1) (M + N)).filter (fun n => Nat.Coprime n (primorial D))).card :=
          Finset.card_union_le _ _
      _ = D + ((Finset.Icc (M + 1) (M + N)).filter (fun n => Nat.Coprime n (primorial D))).card := by
          simp
  have hcard_r : (((Finset.Icc (M + 1) (M + N)).filter Nat.Prime).card : ℝ) ≤
      (D : ℝ) + (((Finset.Icc (M + 1) (M + N)).filter
        (fun n => Nat.Coprime n (primorial D))).card : ℝ) := by
    exact_mod_cast hcard
  have hsel := selberg_coprime_interval_bound M N D D hD le_rfl
  linarith

/-- **Explicit Brun–Titchmarsh-Style Upper Bound** for primes in any interval `(M, M + N]` (`N ≥ 2`):
`#((Finset.Icc (M + 1) (M + N)).filter Nat.Prime) ≤ 9 * N / log N`. -/
theorem brun_titchmarsh_interval (M N : ℕ) (hN : 2 ≤ N) :
    (((Finset.Icc (M + 1) (M + N)).filter Nat.Prime).card : ℝ) ≤
      9 * (N : ℝ) / Real.log (N : ℝ) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  set x : ℝ := (N : ℝ) ^ ((1 : ℝ) / 3)
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hN_pos _
  have hx_ge1 : 1 ≤ x := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N)) (by norm_num)
  have hx_cube : x ^ 3 = (N : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]
    norm_num
  set D : ℕ := Nat.floor x
  have hD_ge1 : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr (by
    intro h0
    have hlt : x < 1 := (Nat.floor_eq_zero).mp h0
    linarith)
  have hD_le : (D : ℝ) ≤ x := Nat.floor_le hx_pos.le
  have hD_succ_gt : x < (D : ℝ) + 1 := Nat.lt_floor_add_one x
  have hlog_D1 : Real.log (N : ℝ) / 3 ≤ Real.log ((D : ℝ) + 1) := by
    have hlog_x : Real.log x = Real.log (N : ℝ) / 3 := by
      have h1 : Real.log (x ^ 3) = Real.log (N : ℝ) := by rw [hx_cube]
      rw [Real.log_pow] at h1
      push_cast at h1
      linarith
    rw [← hlog_x]
    exact Real.log_le_log hx_pos hD_succ_gt.le
  have hlog_N_le : Real.log (N : ℝ) ≤ 3 * x := by
    have h1 : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx_pos
    have h2 : Real.log (x ^ 3) = Real.log (N : ℝ) := by rw [hx_cube]
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hterm1 : (N : ℝ) / Real.log ((D : ℝ) + 1) ≤ 3 * (N : ℝ) / Real.log (N : ℝ) := by
    have h1 := div_le_div_of_nonneg_left hN_pos.le (div_pos hlogN_pos (by norm_num)) hlog_D1
    calc (N : ℝ) / Real.log ((D : ℝ) + 1)
        ≤ (N : ℝ) / (Real.log (N : ℝ) / 3) := h1
      _ = 3 * (N : ℝ) / Real.log (N : ℝ) := by ring
  have hterm2 : (D : ℝ) ^ 2 ≤ 3 * (N : ℝ) / Real.log (N : ℝ) := by
    rw [le_div_iff₀ hlogN_pos]
    calc (D : ℝ) ^ 2 * Real.log (N : ℝ)
        ≤ x ^ 2 * (3 * x) :=
          mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg D) hD_le 2) hlog_N_le hlogN_pos.le (by positivity)
      _ = 3 * x ^ 3 := by ring
      _ = 3 * (N : ℝ) := by rw [hx_cube]
  have hterm3 : (D : ℝ) ≤ 3 * (N : ℝ) / Real.log (N : ℝ) := by
    have hD_le_sq : (D : ℝ) ≤ (D : ℝ) ^ 2 := by
      have h1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge1
      nlinarith
    exact hD_le_sq.trans hterm2
  have hbase := selberg_primes_in_interval_bound M N D hD_ge1
  calc (((Finset.Icc (M + 1) (M + N)).filter Nat.Prime).card : ℝ)
      ≤ (D : ℝ) + (N : ℝ) / Real.log ((D : ℝ) + 1) + (D : ℝ) ^ 2 := hbase
    _ ≤ 3 * (N : ℝ) / Real.log (N : ℝ) + 3 * (N : ℝ) / Real.log (N : ℝ) +
          3 * (N : ℝ) / Real.log (N : ℝ) := by linarith
    _ = 9 * (N : ℝ) / Real.log (N : ℝ) := by ring

/-! ## Section 2: Gauss Sum Norm & Pólya–Vinogradov Inequality (`MulChar (ZMod q) ℂ`) -/

/-- The standard primitive additive character `e_q(a) = exp(2πi a / q)` on `ZMod q`. -/
def zmodAddChar (q : ℕ) [NeZero q] : AddChar (ZMod q) ℂ where
  toFun a := Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) / (q : ℂ))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rw [← Complex.exp_add]
    have hq_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    have hval : (a + b).val = (a.val + b.val) % q := ZMod.val_add a b
    have hdiv : (a.val + b.val) % q + q * ((a.val + b.val) / q) = a.val + b.val :=
      Nat.mod_add_div (a.val + b.val) q
    have harg : 2 * Real.pi * Complex.I * (a.val : ℂ) / (q : ℂ) +
        2 * Real.pi * Complex.I * (b.val : ℂ) / (q : ℂ) =
        2 * Real.pi * Complex.I * ((a + b).val : ℂ) / (q : ℂ) +
          (((a.val + b.val) / q : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
      have hcast : ((a.val : ℂ) + (b.val : ℂ)) =
          ((a + b).val : ℂ) + (q : ℂ) * (((a.val + b.val) / q : ℕ) : ℂ) := by
        rw [hval]
        exact_mod_cast hdiv.symm
      calc 2 * Real.pi * Complex.I * (a.val : ℂ) / (q : ℂ) +
              2 * Real.pi * Complex.I * (b.val : ℂ) / (q : ℂ)
          = 2 * Real.pi * Complex.I * ((a.val : ℂ) + (b.val : ℂ)) / (q : ℂ) := by ring
        _ = 2 * Real.pi * Complex.I *
              (((a + b).val : ℂ) + (q : ℂ) * (((a.val + b.val) / q : ℕ) : ℂ)) / (q : ℂ) := by
              rw [hcast]
        _ = 2 * Real.pi * Complex.I * ((a + b).val : ℂ) / (q : ℂ) +
              (((a.val + b.val) / q : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
              field_simp [hq_ne]
    rw [harg, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

lemma zmodAddChar_apply (q : ℕ) [NeZero q] (a : ZMod q) :
    zmodAddChar q a = Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) / (q : ℂ)) :=
  rfl

lemma zmodAddChar_apply_natCast (q : ℕ) [NeZero q] (n : ℕ) :
    zmodAddChar q (n : ZMod q) = Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (q : ℂ)) := by
  rw [zmodAddChar_apply]
  have hq_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hval : (n : ZMod q).val = n % q := ZMod.val_natCast q n
  have hdiv : n % q + q * (n / q) = n := Nat.mod_add_div n q
  have harg : 2 * Real.pi * Complex.I * (n : ℂ) / (q : ℂ) =
      2 * Real.pi * Complex.I * ((n : ZMod q).val : ℂ) / (q : ℂ) +
        ((n / q : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have hcast : (n : ℂ) = ((n : ZMod q).val : ℂ) + (q : ℂ) * ((n / q : ℕ) : ℂ) := by
      rw [hval]
      exact_mod_cast hdiv.symm
    rw [hcast]
    field_simp [hq_ne]
  rw [harg, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

lemma norm_zmodAddChar (q : ℕ) [NeZero q] (a : ZMod q) :
    ‖zmodAddChar q a‖ = 1 := by
  rw [zmodAddChar_apply]
  have harg : 2 * Real.pi * Complex.I * (a.val : ℂ) / (q : ℂ) =
      ((2 * Real.pi * (a.val : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_ofReal_mul_I]

lemma star_zmodAddChar (q : ℕ) [NeZero q] (a : ZMod q) :
    star (zmodAddChar q a) = zmodAddChar q (-a) := by
  have h1 : zmodAddChar q a * zmodAddChar q (-a) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h2 : zmodAddChar q a * star (zmodAddChar q a) = 1 := by
    change zmodAddChar q a * starRingEnd ℂ (zmodAddChar q a) = 1
    rw [Complex.mul_conj', norm_zmodAddChar]
    simp
  have hne : zmodAddChar q a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h2.trans h1.symm)

lemma norm_exp_I_mul_sub_one (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hfactor : Complex.exp ((θ : ℂ) * Complex.I) - 1 =
      Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) -
          Complex.exp (-(((θ / 2 : ℝ) : ℂ) * Complex.I))) := by
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add]
    have hadd : ((θ / 2 : ℝ) : ℂ) * Complex.I + ((θ / 2 : ℝ) : ℂ) * Complex.I =
        (θ : ℂ) * Complex.I := by push_cast; ring
    rw [hadd, add_neg_cancel, Complex.exp_zero]
  have hsin : Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) -
      Complex.exp (-(((θ / 2 : ℝ) : ℂ) * Complex.I)) =
      2 * Complex.I * (Real.sin (θ / 2) : ℂ) := by
    rw [Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [hfactor, hsin, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, norm_mul,
    Complex.norm_ofNat, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

lemma zmodAddChar_ne_one_of_ne_zero (q : ℕ) [NeZero q] {x : ZMod q} (hx : x ≠ 0) :
    zmodAddChar q x ≠ 1 := by
  intro heq
  have hnorm0 : ‖zmodAddChar q x - 1‖ = 0 := by rw [heq, sub_self, norm_zero]
  rw [zmodAddChar_apply] at hnorm0
  have harg : 2 * Real.pi * Complex.I * (x.val : ℂ) / (q : ℂ) =
      ((2 * Real.pi * (x.val : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, norm_exp_I_mul_sub_one] at hnorm0
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hx_pos : 0 < x.val := by
    by_contra h0
    have hv0 : x.val = 0 := Nat.eq_zero_of_not_pos h0
    exact hx ((ZMod.val_eq_zero x).mp hv0)
  have hx_lt : x.val < q := ZMod.val_lt x
  have hθ_pos : 0 < Real.pi * (x.val : ℝ) / (q : ℝ) := by
    have : (0 : ℝ) < (x.val : ℝ) := Nat.cast_pos.mpr hx_pos
    positivity
  have hθ_lt : Real.pi * (x.val : ℝ) / (q : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hq_pos]
    have hx_lt_r : (x.val : ℝ) < (q : ℝ) := Nat.cast_lt.mpr hx_lt
    exact mul_lt_mul_of_pos_left hx_lt_r Real.pi_pos
  have hhalf : 2 * Real.pi * (x.val : ℝ) / (q : ℝ) / 2 = Real.pi * (x.val : ℝ) / (q : ℝ) := by ring
  rw [hhalf] at hnorm0
  have hsin_pos : 0 < Real.sin (Real.pi * (x.val : ℝ) / (q : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt
  rw [abs_of_pos hsin_pos] at hnorm0
  linarith

/-- Additive character orthogonality on `ZMod q`:
`∑_{a ∈ ZMod q} e_q(a * x) = q` if `x = 0` and `0` otherwise. -/
theorem sum_zmodAddChar (q : ℕ) [NeZero q] (x : ZMod q) :
    ∑ a : ZMod q, zmodAddChar q (a * x) = if x = 0 then (q : ℂ) else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp [ZMod.card]
  · simp only [hx, ↓reduceIte]
    set S : ℂ := ∑ a : ZMod q, zmodAddChar q (a * x)
    have hshift : zmodAddChar q x * S = S := by
      dsimp [S]
      rw [Finset.mul_sum]
      calc ∑ a : ZMod q, zmodAddChar q x * zmodAddChar q (a * x)
          = ∑ a : ZMod q, zmodAddChar q ((a + 1) * x) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [← AddChar.map_add_eq_mul]
              congr 1
              ring
        _ = ∑ a : ZMod q, zmodAddChar q (a * x) :=
              Equiv.sum_comp (Equiv.addRight (1 : ZMod q)) (fun a : ZMod q => zmodAddChar q (a * x))
    have hmul0 : (zmodAddChar q x - 1) * S = 0 := by linear_combination hshift
    have hne : zmodAddChar q x - 1 ≠ 0 := sub_ne_zero.mpr (zmodAddChar_ne_one_of_ne_zero q hx)
    exact (mul_eq_zero.mp hmul0).resolve_left hne

/-- The classical Dirichlet Gauss sum `τ(χ) = ∑_{x ∈ ZMod q} χ(x) e_q(x)`. -/
def dirichletGaussSum {q : ℕ} [NeZero q] (χ : MulChar (ZMod q) ℂ) : ℂ :=
  gaussSum χ (zmodAddChar q)

lemma sum_norm_sq_mulChar {q : ℕ} [NeZero q] (χ : MulChar (ZMod q) ℂ) :
    ∑ a : ZMod q, ‖χ a‖ ^ 2 = (Nat.totient q : ℝ) := by
  have hsplit : ∑ a : ZMod q, ‖χ a‖ ^ 2 =
      ∑ a : ZMod q, if IsUnit a then (1 : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hu : IsUnit a
    · rcases hu with ⟨u, rfl⟩
      simp only [Units.isUnit, ↓reduceIte]
      have h1 := DirichletCharacter.unit_norm_eq_one χ u
      rw [h1, one_pow]
    · simp only [hu, ↓reduceIte]
      rw [MulChar.map_nonunit χ hu, norm_zero, zero_pow (by norm_num)]
  rw [hsplit]
  have hcard : (Finset.univ.filter (fun a : ZMod q => IsUnit a)).card = Nat.totient q := by
    rw [← ZMod.card_units_eq_totient q]
    have hbij : Finset.univ.filter (fun a : ZMod q => IsUnit a) =
        Finset.univ.image (fun u : (ZMod q)ˣ => (u : ZMod q)) := by
      ext a
      rw [Finset.mem_filter, Finset.mem_image]
      simp [IsUnit]
    rw [hbij, Finset.card_image_of_injective _ Units.val_injective, Finset.card_univ]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hcard]

/-- **Exact Gauss Sum Norm-Squared Formula**:
For every `q ≥ 1` (`[NeZero q]`) and every primitive Dirichlet character `χ : MulChar (ZMod q) ℂ`,
`‖τ(χ)‖^2 = q`. -/
theorem norm_sq_dirichletGaussSum_eq {q : ℕ} [NeZero q]
    (χ : MulChar (ZMod q) ℂ) (hχ : DirichletCharacter.IsPrimitive χ) :
    ‖dirichletGaussSum χ‖ ^ 2 = (q : ℝ) := by
  -- Evaluate `∑_{a : ZMod q} ‖gaussSum χ ((zmodAddChar q).mulShift a)‖^2` in two ways.
  have hrhs : ∑ a : ZMod q, ‖gaussSum χ ((zmodAddChar q).mulShift a)‖ ^ 2 =
      (Nat.totient q : ℝ) * ‖dirichletGaussSum χ‖ ^ 2 := by
    calc ∑ a : ZMod q, ‖gaussSum χ ((zmodAddChar q).mulShift a)‖ ^ 2
        = ∑ a : ZMod q, ‖χ⁻¹ a‖ ^ 2 * ‖dirichletGaussSum χ‖ ^ 2 := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [gaussSum_mulShift_of_isPrimitive (zmodAddChar q) hχ a, norm_mul, mul_pow]
            rfl
      _ = (∑ a : ZMod q, ‖χ⁻¹ a‖ ^ 2) * ‖dirichletGaussSum χ‖ ^ 2 := (Finset.sum_mul _ _ _).symm
      _ = (Nat.totient q : ℝ) * ‖dirichletGaussSum χ‖ ^ 2 := by rw [sum_norm_sq_mulChar]
  have hlhs_C : (∑ a : ZMod q, ((‖gaussSum χ ((zmodAddChar q).mulShift a)‖ ^ 2 : ℝ) : ℂ)) =
      ((q : ℂ) * (Nat.totient q : ℂ)) := by
    have hnorm_sq : ∀ a : ZMod q,
        ((‖gaussSum χ ((zmodAddChar q).mulShift a)‖ ^ 2 : ℝ) : ℂ) =
          ∑ x : ZMod q, ∑ y : ZMod q,
            χ x * star (χ y) * zmodAddChar q (a * (x - y)) := by
      intro a
      push_cast
      rw [← Complex.mul_conj']
      simp only [gaussSum, AddChar.mulShift_apply, map_sum, map_mul]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      change χ x * zmodAddChar q (a * x) * (star (χ y) * star (zmodAddChar q (a * y))) =
        χ x * star (χ y) * zmodAddChar q (a * (x - y))
      rw [star_zmodAddChar]
      have hmul : zmodAddChar q (a * x) * zmodAddChar q (-(a * y)) =
          zmodAddChar q (a * (x - y)) := by
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      calc χ x * zmodAddChar q (a * x) * (star (χ y) * zmodAddChar q (-(a * y)))
          = χ x * star (χ y) * (zmodAddChar q (a * x) * zmodAddChar q (-(a * y))) := by ring
        _ = χ x * star (χ y) * zmodAddChar q (a * (x - y)) := by rw [hmul]
    simp_rw [hnorm_sq]
    rw [Finset.sum_comm]
    have hswap : ∑ x : ZMod q, ∑ a : ZMod q, ∑ y : ZMod q,
          χ x * star (χ y) * zmodAddChar q (a * (x - y)) =
        ∑ x : ZMod q, ∑ y : ZMod q,
          χ x * star (χ y) * ∑ a : ZMod q, zmodAddChar q (a * (x - y)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
    rw [hswap]
    have hinner : ∀ x : ZMod q,
        ∑ y : ZMod q, χ x * star (χ y) * ∑ a : ZMod q, zmodAddChar q (a * (x - y)) =
          (q : ℂ) * ((‖χ x‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      have hterm : ∀ y : ZMod q,
          χ x * star (χ y) * ∑ a : ZMod q, zmodAddChar q (a * (x - y)) =
            if y = x then (q : ℂ) * ((‖χ x‖ ^ 2 : ℝ) : ℂ) else 0 := by
        intro y
        rw [sum_zmodAddChar]
        by_cases hyx : y = x
        · subst hyx
          simp only [sub_self, ↓reduceIte]
          have hmc : χ y * star (χ y) = ((‖χ y‖ ^ 2 : ℝ) : ℂ) := by
            push_cast
            exact Complex.mul_conj' (χ y)
          rw [hmc]
          ring
        · have hne : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyx)
          simp [hne, hyx]
      rw [Finset.sum_congr rfl fun y _ => hterm y]
      simp
    simp_rw [hinner]
    rw [← Finset.mul_sum]
    have hcast : (∑ x : ZMod q, ((‖χ x‖ ^ 2 : ℝ) : ℂ)) = ((Nat.totient q : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sum, sum_norm_sq_mulChar]
    rw [hcast]
    simp
  have hlhs : ∑ a : ZMod q, ‖gaussSum χ ((zmodAddChar q).mulShift a)‖ ^ 2 =
      (q : ℝ) * (Nat.totient q : ℝ) := by
    have h1 := congr_arg Complex.re hlhs_C
    rw [← Complex.ofReal_sum, Complex.ofReal_re] at h1
    have hr : ((q : ℂ) * (Nat.totient q : ℂ)).re = (q : ℝ) * (Nat.totient q : ℝ) := by
      norm_cast
    linarith
  have htot_pos : (0 : ℝ) < (Nat.totient q : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have heq : (Nat.totient q : ℝ) * ‖dirichletGaussSum χ‖ ^ 2 = (Nat.totient q : ℝ) * (q : ℝ) := by
    linarith
  exact mul_left_cancel₀ htot_pos.ne' heq

/-- **Exact Gauss Sum Norm**: `‖τ(χ)‖ = √q` for every primitive character `χ : MulChar (ZMod q) ℂ`. -/
theorem norm_dirichletGaussSum_eq_sqrt {q : ℕ} [NeZero q]
    (χ : MulChar (ZMod q) ℂ) (hχ : DirichletCharacter.IsPrimitive χ) :
    ‖dirichletGaussSum χ‖ = Real.sqrt (q : ℝ) := by
  have hsq := norm_sq_dirichletGaussSum_eq χ hχ
  have h := congr_arg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _)] at h

lemma isPrimitive_inv {q : ℕ} [NeZero q] {χ : MulChar (ZMod q) ℂ}
    (hχ : DirichletCharacter.IsPrimitive χ) :
    DirichletCharacter.IsPrimitive χ⁻¹ := by
  change DirichletCharacter.conductor χ⁻¹ = q
  rw [DirichletCharacter.conductor_inv]
  exact hχ

lemma harmonic_le_log_add_one {m : ℕ} (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Icc 1 m, (k : ℝ)⁻¹ ≤ Real.log (m : ℝ) + 1 := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : m + 1 ∉ Finset.Icc 1 m := by simp
    rw [hIcc, Finset.sum_insert hnot]
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hstep : (((m + 1 : ℕ) : ℝ))⁻¹ ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
      have hdiv_pos : 0 < (m : ℝ) / ((m + 1 : ℕ) : ℝ) := div_pos hm_pos hm1_pos
      have hlog := Real.log_le_sub_one_of_pos hdiv_pos
      rw [Real.log_div hm_pos.ne' hm1_pos.ne'] at hlog
      have hsub : (m : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = -(((m + 1 : ℕ) : ℝ))⁻¹ := by
        push_cast
        have : (m : ℝ) + 1 ≠ 0 := by positivity
        field_simp [this]
        ring
      linarith
    linarith

lemma sum_inv_sin_pi_div_le {q : ℕ} (hq : 2 ≤ q) :
    ∑ a ∈ Finset.Icc 1 (q - 1), (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ ≤
      (q : ℝ) * (Real.log (q : ℝ) + 1) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  set H : ℕ := q / 2
  have hH_pos : 1 ≤ H := by omega
  have hH_le : H ≤ q := Nat.div_le_self q 2
  have hsplit : Finset.Icc 1 (q - 1) = Finset.Icc 1 H ∪ Finset.Icc (H + 1) (q - 1) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 H) (Finset.Icc (H + 1) (q - 1)) := by
    rw [Finset.disjoint_left]
    intro a h1 h2
    simp only [Finset.mem_Icc] at h1 h2
    omega
  have hbound_lo : ∀ a ∈ Finset.Icc 1 H,
      (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ ≤ (q : ℝ) / (2 * (a : ℝ)) := by
    intro a ha
    simp only [Finset.mem_Icc] at ha
    have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
    have h2a_le : 2 * (a : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 2 * a ≤ q)
    have hx_nonneg : 0 ≤ Real.pi * (a : ℝ) / (q : ℝ) := by positivity
    have hx_le : Real.pi * (a : ℝ) / (q : ℝ) ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hq_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [Real.pi_pos]
    have hsin := Real.mul_le_sin hx_nonneg hx_le
    have hsimp : 2 / Real.pi * (Real.pi * (a : ℝ) / (q : ℝ)) = 2 * (a : ℝ) / (q : ℝ) := by
      field_simp [Real.pi_pos.ne', hq_pos.ne']
    rw [hsimp] at hsin
    have hpos : 0 < 2 * (a : ℝ) / (q : ℝ) := by positivity
    have hinv := inv_anti₀ hpos hsin
    simpa [inv_div] using hinv
  have hsum1 : ∑ a ∈ Finset.Icc 1 H, (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ ≤
      (q : ℝ) / 2 * ∑ a ∈ Finset.Icc 1 H, (a : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    have h := hbound_lo a ha
    linarith [show (q : ℝ) / 2 * (a : ℝ)⁻¹ = (q : ℝ) / (2 * (a : ℝ)) by ring]
  have hsum2 : ∑ a ∈ Finset.Icc (H + 1) (q - 1), (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ ≤
      (q : ℝ) / 2 * ∑ b ∈ Finset.Icc 1 H, (b : ℝ)⁻¹ := by
    have hsub : (Finset.Icc (H + 1) (q - 1)).image (fun a => q - a) ⊆ Finset.Icc 1 H := by
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
      simp only [Finset.mem_Icc] at ha ⊢
      omega
    have hinj : Set.InjOn (fun a => q - a) ↑(Finset.Icc (H + 1) (q - 1)) := by
      intro a₁ h1 a₂ h2 heq
      dsimp only at heq
      simp only [Finset.mem_coe, Finset.mem_Icc] at h1 h2
      omega
    have hsym : ∑ a ∈ Finset.Icc (H + 1) (q - 1), (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ =
        ∑ b ∈ (Finset.Icc (H + 1) (q - 1)).image (fun a => q - a),
          (Real.sin (Real.pi * (b : ℝ) / (q : ℝ)))⁻¹ := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun a ha => ?_
      simp only [Finset.mem_Icc] at ha
      have hcast : ((q - a : ℕ) : ℝ) = (q : ℝ) - (a : ℝ) := Nat.cast_sub (by omega)
      rw [hcast]
      have hpi : Real.pi * ((q : ℝ) - (a : ℝ)) / (q : ℝ) =
          Real.pi - Real.pi * (a : ℝ) / (q : ℝ) := by
        field_simp [hq_pos.ne']
      rw [hpi, Real.sin_pi_sub]
    rw [hsym]
    calc ∑ b ∈ (Finset.Icc (H + 1) (q - 1)).image (fun a => q - a),
            (Real.sin (Real.pi * (b : ℝ) / (q : ℝ)))⁻¹
        ≤ ∑ b ∈ Finset.Icc 1 H, (Real.sin (Real.pi * (b : ℝ) / (q : ℝ)))⁻¹ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun b hb _ => ?_
          simp only [Finset.mem_Icc] at hb
          have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
          have hb_lt : (b : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : b < q)
          have hsin_pos : 0 < Real.sin (Real.pi * (b : ℝ) / (q : ℝ)) :=
            Real.sin_pos_of_pos_of_lt_pi (by positivity)
              (by rw [div_lt_iff₀ hq_pos]; exact mul_lt_mul_of_pos_left hb_lt Real.pi_pos)
          exact inv_nonneg.mpr hsin_pos.le
      _ ≤ (q : ℝ) / 2 * ∑ b ∈ Finset.Icc 1 H, (b : ℝ)⁻¹ := hsum1
  rw [hsplit, Finset.sum_union hdisj]
  have hharm : ∑ a ∈ Finset.Icc 1 H, (a : ℝ)⁻¹ ≤ Real.log (q : ℝ) + 1 := by
    calc ∑ a ∈ Finset.Icc 1 H, (a : ℝ)⁻¹
        ≤ Real.log (H : ℝ) + 1 := harmonic_le_log_add_one hH_pos
      _ ≤ Real.log (q : ℝ) + 1 := by
          have hH_pos_r : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
          have hH_le_r : (H : ℝ) ≤ (q : ℝ) := by exact_mod_cast hH_le
          linarith [Real.log_le_log hH_pos_r hH_le_r]
  calc ∑ a ∈ Finset.Icc 1 H, (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ +
          ∑ a ∈ Finset.Icc (H + 1) (q - 1), (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹
      ≤ (q : ℝ) / 2 * (∑ a ∈ Finset.Icc 1 H, (a : ℝ)⁻¹) +
          (q : ℝ) / 2 * (∑ a ∈ Finset.Icc 1 H, (a : ℝ)⁻¹) := add_le_add hsum1 hsum2
    _ = (q : ℝ) * ∑ a ∈ Finset.Icc 1 H, (a : ℝ)⁻¹ := by ring
    _ ≤ (q : ℝ) * (Real.log (q : ℝ) + 1) := mul_le_mul_of_nonneg_left hharm hq_pos.le

/-- **Explicit Pólya–Vinogradov Inequality**:
For every `q ≥ 2`, every primitive Dirichlet character `χ : MulChar (ZMod q) ℂ`, and all `M, N : ℕ`,
`‖∑_{n ∈ Icc M (M + N - 1)} χ n‖ ≤ √q * (log q + 1)`. -/
theorem polya_vinogradov {q : ℕ} (hq : 2 ≤ q) [NeZero q]
    (χ : MulChar (ZMod q) ℂ) (hχ : DirichletCharacter.IsPrimitive χ) (M N : ℕ) :
    ‖∑ n ∈ Finset.Icc M (M + N - 1), χ (n : ZMod q)‖ ≤
      Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 1) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlog_nonneg : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hrhs_nonneg : 0 ≤ Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 1) := by positivity
  by_cases hN0 : N = 0
  · subst hN0
    by_cases hM0 : M = 0
    · subst hM0
      have h0_nu : ¬ IsUnit (0 : ZMod q) := by
        intro hu
        have : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (by omega)
        exact not_isUnit_zero hu
      simp [MulChar.map_nonunit χ h0_nu, hrhs_nonneg]
    · have hemp : Finset.Icc M (M - 1) = ∅ := Finset.Icc_eq_empty (by omega)
      rw [add_zero, hemp]
      simpa using hrhs_nonneg
  · have hN_pos : 1 ≤ N := Nat.pos_of_ne_zero hN0
    have hχinv_prim : DirichletCharacter.IsPrimitive χ⁻¹ := isPrimitive_inv hχ
    have htau_norm : ‖dirichletGaussSum χ⁻¹‖ = Real.sqrt (q : ℝ) :=
      norm_dirichletGaussSum_eq_sqrt χ⁻¹ hχinv_prim
    have htau_ne : dirichletGaussSum χ⁻¹ ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at htau_norm
      linarith [Real.sqrt_pos.mpr hq_pos]
    -- Expand `χ(n) * τ(χ⁻¹) = ∑_{a : ZMod q} χ⁻¹(a) e_q(a * n)`
    have hFourier : (∑ n ∈ Finset.Icc M (M + N - 1), χ (n : ZMod q)) * dirichletGaussSum χ⁻¹ =
        ∑ a : ZMod q, χ⁻¹ a *
          ∑ n ∈ Finset.Icc M (M + N - 1), zmodAddChar q (a * (n : ZMod q)) := by
      rw [Finset.sum_mul]
      have hpt : ∀ n ∈ Finset.Icc M (M + N - 1),
          χ (n : ZMod q) * dirichletGaussSum χ⁻¹ =
            ∑ a : ZMod q, χ⁻¹ a * zmodAddChar q (a * (n : ZMod q)) := by
        intro n _
        have hg := gaussSum_mulShift_of_isPrimitive (zmodAddChar q) hχinv_prim (n : ZMod q)
        rw [inv_inv] at hg
        unfold dirichletGaussSum
        rw [← hg]
        simp only [gaussSum, AddChar.mulShift_apply]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mul_comm (n : ZMod q) a]
      rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
    -- The `a = 0` term vanishes since `0` is not a unit in `ZMod q` (`q ≥ 2`)
    have h0_vanish : χ⁻¹ (0 : ZMod q) = 0 := by
      have : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (by omega)
      exact MulChar.map_nonunit χ⁻¹ not_isUnit_zero
    -- Bound each geometric sum for `a ≠ 0`
    have hgeom_bound : ∀ a : ZMod q, a ≠ 0 →
        ‖∑ n ∈ Finset.Icc M (M + N - 1), zmodAddChar q (a * (n : ZMod q))‖ ≤
          (Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))⁻¹ := by
      intro a ha
      have hreidx : ∑ n ∈ Finset.Icc M (M + N - 1), zmodAddChar q (a * (n : ZMod q)) =
          zmodAddChar q (a * (M : ZMod q)) * ∑ k ∈ Finset.range N, (zmodAddChar q a) ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun n _ => n - M) ?_ ?_ ?_ ?_
        · intro n hn
          simp only [Finset.mem_Icc] at hn
          simp only [Finset.mem_range]
          omega
        · intro n₁ h1 n₂ h2 heq
          simp only [Finset.mem_Icc] at h1 h2
          omega
        · intro k hk
          simp only [Finset.mem_range] at hk
          exact ⟨M + k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro n hn
          simp only [Finset.mem_Icc] at hn
          rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul, nsmul_eq_mul]
          congr 1
          have hnm : (M : ZMod q) + ((n - M : ℕ) : ZMod q) = (n : ZMod q) := by
            rw [← Nat.cast_add, Nat.add_sub_cancel' hn.1]
          calc a * (n : ZMod q) = a * ((M : ZMod q) + ((n - M : ℕ) : ZMod q)) := by rw [hnm]
            _ = a * (M : ZMod q) + ((n - M : ℕ) : ZMod q) * a := by ring
      rw [hreidx, geom_sum_eq (zmodAddChar_ne_one_of_ne_zero q ha), norm_mul, norm_zmodAddChar,
        one_mul, norm_div]
      have hnum : ‖(zmodAddChar q a) ^ N - 1‖ ≤ 2 := by
        calc ‖(zmodAddChar q a) ^ N - 1‖
            ≤ ‖(zmodAddChar q a) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 1 ^ N + 1 := by rw [norm_pow, norm_zmodAddChar, norm_one]
          _ = 2 := by norm_num
      have hden : ‖zmodAddChar q a - 1‖ = 2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)) := by
        rw [zmodAddChar_apply]
        have harg : 2 * Real.pi * Complex.I * (a.val : ℂ) / (q : ℂ) =
            ((2 * Real.pi * (a.val : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [harg, norm_exp_I_mul_sub_one]
        have hhalf : 2 * Real.pi * (a.val : ℝ) / (q : ℝ) / 2 =
            Real.pi * (a.val : ℝ) / (q : ℝ) := by ring
        rw [hhalf]
        have ha_pos : 0 < a.val := by
          by_contra h0
          exact ha ((ZMod.val_eq_zero a).mp (Nat.eq_zero_of_not_pos h0))
        have ha_lt : a.val < q := ZMod.val_lt a
        have hsin_pos : 0 < Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)) :=
          Real.sin_pos_of_pos_of_lt_pi (by positivity)
            (by rw [div_lt_iff₀ hq_pos]
                exact mul_lt_mul_of_pos_left (Nat.cast_lt.mpr ha_lt) Real.pi_pos)
        rw [abs_of_pos hsin_pos]
      rw [hden]
      have hden_pos : 0 < 2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)) := by
        rw [← hden]
        exact norm_pos_iff.mpr (sub_ne_zero.mpr (zmodAddChar_ne_one_of_ne_zero q ha))
      calc ‖(zmodAddChar q a) ^ N - 1‖ / (2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))
          ≤ 2 / (2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))) :=
            div_le_div_of_nonneg_right hnum hden_pos.le
        _ = (Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))⁻¹ := by
            have hs_ne : Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)) ≠ 0 := by linarith
            field_simp [hs_ne]
    -- Combine Fourier inversion with triangle inequality and `sum_inv_sin_pi_div_le`
    have hmul_bound : ‖∑ n ∈ Finset.Icc M (M + N - 1), χ (n : ZMod q)‖ * Real.sqrt (q : ℝ) ≤
        (q : ℝ) * (Real.log (q : ℝ) + 1) := by
      rw [← htau_norm, ← norm_mul, hFourier]
      calc ‖∑ a : ZMod q, χ⁻¹ a *
              ∑ n ∈ Finset.Icc M (M + N - 1), zmodAddChar q (a * (n : ZMod q))‖
          ≤ ∑ a : ZMod q, ‖χ⁻¹ a *
              ∑ n ∈ Finset.Icc M (M + N - 1), zmodAddChar q (a * (n : ZMod q))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ a : ZMod q, if a = 0 then (0 : ℝ) else
              (Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))⁻¹ := by
            refine Finset.sum_le_sum fun a _ => ?_
            by_cases ha : a = 0
            · simp [ha, h0_vanish]
            · simp only [ha, ↓reduceIte, norm_mul]
              calc ‖χ⁻¹ a‖ * ‖∑ n ∈ Finset.Icc M (M + N - 1), zmodAddChar q (a * (n : ZMod q))‖
                  ≤ 1 * (Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))⁻¹ :=
                    mul_le_mul (DirichletCharacter.norm_le_one χ⁻¹ a) (hgeom_bound a ha)
                      (norm_nonneg _) zero_le_one
                _ = (Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))⁻¹ := one_mul _
        _ = ∑ a ∈ Finset.Icc 1 (q - 1), (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))]
            simp only [↓reduceIte, zero_add]
            refine Finset.sum_bij (fun a _ => a.val) ?_ ?_ ?_ ?_
            · intro a ha
              have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
              have hpos : 0 < a.val := by
                by_contra h0
                exact ha0 ((ZMod.val_eq_zero a).mp (Nat.eq_zero_of_not_pos h0))
              have hlt : a.val < q := ZMod.val_lt a
              exact Finset.mem_Icc.mpr ⟨hpos, by omega⟩
            · intro a₁ _ a₂ _ heq
              exact ZMod.val_injective q heq
            · intro k hk
              simp only [Finset.mem_Icc] at hk
              refine ⟨(k : ZMod q), Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
              · intro h0
                have hv := congr_arg ZMod.val h0
                rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : k < q), ZMod.val_zero] at hv
                omega
              · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : k < q)]
            · intro a ha
              have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
              simp [ha0]
        _ ≤ (q : ℝ) * (Real.log (q : ℝ) + 1) := sum_inv_sin_pi_div_le hq
    have hsqrt_pos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq_pos
    have hq_sq : (q : ℝ) = Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) :=
      (Real.mul_self_sqrt hq_pos.le).symm
    have hmul' : ‖∑ n ∈ Finset.Icc M (M + N - 1), χ (n : ZMod q)‖ * Real.sqrt (q : ℝ) ≤
        (Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 1)) * Real.sqrt (q : ℝ) := by
      calc ‖∑ n ∈ Finset.Icc M (M + N - 1), χ (n : ZMod q)‖ * Real.sqrt (q : ℝ)
          ≤ (q : ℝ) * (Real.log (q : ℝ) + 1) := hmul_bound
        _ = (Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 1)) * Real.sqrt (q : ℝ) := by
            rw [mul_right_comm, ← hq_sq]
    exact le_of_mul_le_mul_right hmul' hsqrt_pos

/-- Corollary: Pólya–Vinogradov inequality for any primitive non-principal character
`χ : MulChar (ZMod q) ℂ` (`χ ≠ 1`), deducing `2 ≤ q` automatically. -/
theorem polya_vinogradov_of_ne_one {q : ℕ} [NeZero q]
    (χ : MulChar (ZMod q) ℂ) (hχ : DirichletCharacter.IsPrimitive χ) (hne1 : χ ≠ 1) (M N : ℕ) :
    ‖∑ n ∈ Finset.Icc M (M + N - 1), χ (n : ZMod q)‖ ≤
      Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 1) := by
  have hq2 : 2 ≤ q := by
    have hq_pos : 1 ≤ q := NeZero.pos q
    by_contra hlt
    have hq1 : q = 1 := by omega
    subst hq1
    apply hne1
    ext x
    have hx : x = 1 := Subsingleton.elim x 1
    rw [hx, Units.val_one, map_one, map_one]
  exact polya_vinogradov hq2 χ hχ M N

/-! ## Section 3: Turán–Kubilius Inequality & Hardy–Ramanujan Normal Order Corollary -/

/-- A complex-valued arithmetic function `f : ℕ → ℂ` is additive if `f(1) = 0` and
`f(m * n) = f(m) + f(n)` for all coprime positive `m, n`. -/
def IsAdditive (f : ℕ → ℂ) : Prop :=
  f 1 = 0 ∧ ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → f (m * n) = f m + f n

/-- A complex-valued arithmetic function `f : ℕ → ℂ` is strongly additive if it is additive
and satisfies `f(p^k) = f(p)` for every prime `p` and `k ≥ 1`. -/
def IsStronglyAdditive (f : ℕ → ℂ) : Prop :=
  IsAdditive f ∧ ∀ p k : ℕ, Nat.Prime p → 1 ≤ k → f (p ^ k) = f p

/-- Exact prime-power divisibility `p^k ‖ n`: `p^k ∣ n ∧ ¬ p^(k+1) ∣ n`. -/
def exactPowDvd (p k n : ℕ) : Prop :=
  p ^ k ∣ n ∧ ¬ p ^ (k + 1) ∣ n

instance (p k n : ℕ) : Decidable (exactPowDvd p k n) :=
  inferInstanceAs (Decidable (p ^ k ∣ n ∧ ¬ p ^ (k + 1) ∣ n))

/-- The finite set of prime-power pairs `(p, k)` with `p` prime, `k ≥ 1`, and `p^k ≤ N`. -/
def primePowers (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).filter Nat.Prime).biUnion fun p =>
    ((Finset.Icc 1 N).filter (fun k => p ^ k ≤ N)).image (p, ·)

lemma mem_primePowers {N p k : ℕ} :
    (p, k) ∈ primePowers N ↔ Nat.Prime p ∧ 1 ≤ k ∧ p ^ k ≤ N := by
  unfold primePowers
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
    Prod.mk.injEq]
  constructor
  · rintro ⟨p', ⟨⟨_, _⟩, hp'⟩, k', ⟨⟨hk1, _⟩, hpk⟩, rfl, rfl⟩
    exact ⟨hp', hk1, hpk⟩
  · rintro ⟨hp, hk1, hpk⟩
    have hp_le : p ≤ N := (Nat.le_self_pow (by omega : k ≠ 0) p).trans hpk
    have hk_le : k ≤ N := (Nat.lt_pow_self hp.one_lt).le.trans hpk
    exact ⟨p, ⟨⟨hp.one_le, hp_le⟩, hp⟩, k, ⟨⟨hk1, hk_le⟩, hpk⟩, rfl, rfl⟩

lemma primePower_val_injOn (N : ℕ) :
    Set.InjOn (fun pk : ℕ × ℕ => pk.1 ^ pk.2) ↑(primePowers N) := by
  intro ⟨p₁, k₁⟩ h1 ⟨p₂, k₂⟩ h2 heq
  dsimp only at heq
  have hm1 := mem_primePowers.mp (Finset.mem_coe.mp h1)
  have hm2 := mem_primePowers.mp (Finset.mem_coe.mp h2)
  have hp1_dvd : p₁ ∣ p₂ ^ k₂ := heq ▸ dvd_pow_self p₁ (by omega)
  have hp1_eq : p₁ = p₂ :=
    (Nat.prime_dvd_prime_iff_eq hm1.1 hm2.1).mp (hm1.1.dvd_of_dvd_pow hp1_dvd)
  subst hp1_eq
  have hk_eq : k₁ = k₂ := Nat.pow_right_injective hm1.1.two_le heq
  exact Prod.ext rfl hk_eq

lemma exactPowDvd_iff_factorization {p k n : ℕ} (hp : Nat.Prime p) (hk : 1 ≤ k) (hn : n ≠ 0) :
    exactPowDvd p k n ↔ p ∈ n.primeFactors ∧ n.factorization p = k := by
  unfold exactPowDvd
  rw [hp.pow_dvd_iff_le_factorization hn, hp.pow_dvd_iff_le_factorization hn]
  constructor
  · intro ⟨h1, h2⟩
    have heq : n.factorization p = k := by omega
    refine ⟨Nat.mem_primeFactors.mpr ⟨hp, ?_, hn⟩, heq⟩
    exact (dvd_pow_self p (by omega : k ≠ 0)).trans
      ((hp.pow_dvd_iff_le_factorization hn).mpr h1)
  · intro ⟨_, heq⟩
    omega

lemma additive_eq_sum_primeFactors {f : ℕ → ℂ} (hf : IsAdditive f) {n : ℕ} (hn : n ≠ 0) :
    f n = ∑ p ∈ n.primeFactors, f (p ^ n.factorization p) := by
  have hprod : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
  conv_lhs => rw [hprod]
  have hprimes : ∀ p ∈ n.primeFactors, Nat.Prime p := fun _ hp => Nat.prime_of_mem_primeFactors hp
  set e : ℕ → ℕ := fun p => n.factorization p
  generalize n.primeFactors = S at hprimes ⊢
  classical
  induction S using Finset.induction_on with
  | empty => simp [hf.1]
  | @insert a s ha ih =>
    have ha_p : Nat.Prime a := hprimes a (Finset.mem_insert_self a s)
    have hs_p : ∀ p ∈ s, Nat.Prime p := fun p hp => hprimes p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hcop : Nat.Coprime (a ^ e a) (∏ p ∈ s, p ^ e p) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      exact ((Nat.coprime_primes ha_p (hs_p p hp)).mpr (fun h => ha (h ▸ hp))).pow _ _
    have hpos1 : 0 < a ^ e a := pow_pos ha_p.pos _
    have hpos2 : 0 < ∏ p ∈ s, p ^ e p := Finset.prod_pos fun p hp => pow_pos (hs_p p hp).pos _
    rw [hf.2 _ _ hpos1 hpos2 hcop, ih hs_p]

lemma additive_eq_sum_primePowers {f : ℕ → ℂ} (hf : IsAdditive f) {N n : ℕ}
    (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    f n = ∑ pk ∈ (primePowers N).filter (fun pk => exactPowDvd pk.1 pk.2 n),
      f (pk.1 ^ pk.2) := by
  have hn0 : n ≠ 0 := by omega
  rw [additive_eq_sum_primeFactors hf hn0]
  refine Finset.sum_bij (fun p _ => (p, n.factorization p)) ?_ ?_ ?_ ?_
  · intro p hp
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hk_pos : 1 ≤ n.factorization p :=
      Nat.Prime.factorization_pos_of_dvd hp_prime hn0 (Nat.dvd_of_mem_primeFactors hp)
    have hpk_le : p ^ n.factorization p ≤ N :=
      (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p)).trans hnN
    exact Finset.mem_filter.mpr ⟨mem_primePowers.mpr ⟨hp_prime, hk_pos, hpk_le⟩,
      (exactPowDvd_iff_factorization hp_prime hk_pos hn0).mpr ⟨hp, rfl⟩⟩
  · intro p₁ _ p₂ _ heq
    exact congr_arg Prod.fst heq
  · intro ⟨p, k⟩ hpk
    simp only [Finset.mem_filter, mem_primePowers] at hpk
    have hex := (exactPowDvd_iff_factorization hpk.1.1 hpk.1.2.1 hn0).mp hpk.2
    exact ⟨p, hex.1, Prod.ext rfl hex.2⟩
  · intro _ _; rfl

/-- Exact prime-power density `c_{p,k} = p^{-k} (1 - p^{-1})`. -/
def tkExactDensity (pk : ℕ × ℕ) : ℝ :=
  ((pk.1 : ℝ) ^ pk.2)⁻¹ * (1 - (pk.1 : ℝ)⁻¹)

/-- Turán–Kubilius exact mean `A(N) = ∑_{p^k ≤ N} f(p^k) p^{-k} (1 - 1/p)`. -/
def tkMean (f : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ pk ∈ primePowers N, f (pk.1 ^ pk.2) * (tkExactDensity pk : ℂ)

/-- Turán–Kubilius simplified mean `Ã(N) = ∑_{p^k ≤ N} f(p^k) / p^k`. -/
def tkMeanSimple (f : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ pk ∈ primePowers N, f (pk.1 ^ pk.2) * (((pk.1 : ℝ) ^ pk.2)⁻¹ : ℂ)

/-- Turán–Kubilius variance `B(N)^2 = ∑_{p^k ≤ N} ‖f(p^k)‖^2 / p^k`. -/
def tkVarSq (f : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ pk ∈ primePowers N, ‖f (pk.1 ^ pk.2)‖ ^ 2 / ((pk.1 : ℝ) ^ pk.2)

/-- Turán–Kubilius standard deviation `B(N) = √(B(N)^2)`. -/
def tkVar (f : ℕ → ℂ) (N : ℕ) : ℝ :=
  Real.sqrt (tkVarSq f N)

/-- Strongly-additive Turán–Kubilius mean `A_s(N) = ∑_{p ≤ N} f(p) / p`. -/
def tkStrongMean (f : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, f p / (p : ℂ)

/-- Strongly-additive Turán–Kubilius variance `B_s(N)^2 = ∑_{p ≤ N} ‖f(p)‖^2 / p`. -/
def tkStrongVarSq (f : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ‖f p‖ ^ 2 / (p : ℝ)

/-- Strongly-additive Turán–Kubilius standard deviation `B_s(N) = √(B_s(N)^2)`. -/
def tkStrongVar (f : ℕ → ℂ) (N : ℕ) : ℝ :=
  Real.sqrt (tkStrongVarSq f N)

lemma tkVarSq_nonneg (f : ℕ → ℂ) (N : ℕ) : 0 ≤ tkVarSq f N :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (by positivity)

lemma tkVar_sq (f : ℕ → ℂ) (N : ℕ) : tkVar f N ^ 2 = tkVarSq f N :=
  Real.sq_sqrt (tkVarSq_nonneg f N)

lemma tkStrongVarSq_nonneg (f : ℕ → ℂ) (N : ℕ) : 0 ≤ tkStrongVarSq f N :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (by positivity)

lemma tkStrongVar_sq (f : ℕ → ℂ) (N : ℕ) : tkStrongVar f N ^ 2 = tkStrongVarSq f N :=
  Real.sq_sqrt (tkStrongVarSq_nonneg f N)

lemma prime_pow_div_dvd_factorial (p N : ℕ) (hp : Nat.Prime p) :
    p ^ (N / p) ∣ Nat.factorial N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.factorial_succ]
    by_cases hdvd : p ∣ N + 1
    · have hdiv : (N + 1) / p = N / p + 1 := by
        rcases hdvd with ⟨m, hm⟩
        have hm_pos : 1 ≤ m := by
          by_contra h0
          have hm0 : m = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp h0)
          rw [hm0, mul_zero] at hm
          omega
        have hN : N = p * (m - 1) + (p - 1) := by
          have : p * m = p * (m - 1) + p := by
            rw [← mul_add_one, Nat.sub_add_cancel hm_pos]
          have hp1 : 1 ≤ p := hp.one_le
          omega
        rw [hm, Nat.mul_div_cancel_left m hp.pos, hN,
          Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by have := hp.one_le; omega), add_zero]
        omega
      rw [hdiv, pow_succ']
      exact mul_dvd_mul hdvd ih
    · have hdiv : (N + 1) / p = N / p := by
        have hmod : (N + 1) % p ≠ 0 := fun h0 => hdvd (Nat.dvd_of_mod_eq_zero h0)
        have h1 : N % p + 1 < p := by
          have hlt := Nat.mod_lt N hp.pos
          by_contra hge
          have heq : N % p + 1 = p := by omega
          have : (N + 1) % p = 0 := by
            rw [Nat.add_mod, Nat.mod_eq_of_lt hp.one_lt, heq, Nat.mod_self]
          exact hmod this
        have hN : N = p * (N / p) + N % p := (Nat.div_add_mod N p).symm
        calc (N + 1) / p = (p * (N / p) + (N % p + 1)) / p := by rw [← add_assoc, ← hN]
          _ = N / p + (N % p + 1) / p := Nat.mul_add_div hp.pos _ _
          _ = N / p := by rw [Nat.div_eq_of_lt h1, add_zero]
      rw [hdiv]
      exact ih.trans (dvd_mul_left _ _)

lemma prod_prime_pow_div_dvd_factorial (N : ℕ) :
    (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, p ^ (N / p)) ∣ Nat.factorial N := by
  have hprimes : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Nat.Prime p :=
    fun _ hp => (Finset.mem_filter.mp hp).2
  generalize (Finset.Icc 1 N).filter Nat.Prime = S at hprimes ⊢
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ha_p : Nat.Prime a := hprimes a (Finset.mem_insert_self a s)
    have hs_p : ∀ p ∈ s, Nat.Prime p := fun p hp => hprimes p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert ha]
    have hcop : Nat.Coprime (a ^ (N / a)) (∏ p ∈ s, p ^ (N / p)) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      exact ((Nat.coprime_primes ha_p (hs_p p hp)).mpr (fun h => ha (h ▸ hp))).pow _ _
    exact hcop.mul_dvd_of_dvd_of_dvd (prime_pow_div_dvd_factorial a N ha_p) (ih hs_p)

lemma log_factorial_le (N : ℕ) (_hN : 1 ≤ N) :
    Real.log (Nat.factorial N : ℝ) ≤ (N : ℝ) * Real.log (N : ℝ) := by
  have hfact_le : Nat.factorial N ≤ N ^ N := by
    have hprod : Nat.factorial N = ∏ k ∈ Finset.Icc 1 N, k := by
      clear _hN
      induction N with
      | zero => simp
      | succ n ih =>
        have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [Nat.factorial_succ, hIcc, Finset.prod_insert (by simp), ih]
    rw [hprod]
    calc ∏ k ∈ Finset.Icc 1 N, k ≤ ∏ _k ∈ Finset.Icc 1 N, N :=
          Finset.prod_le_prod' fun k hk => (Finset.mem_Icc.mp hk).2
      _ = N ^ N := by simp
  have hpos : (0 : ℝ) < (Nat.factorial N : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos N)
  calc Real.log (Nat.factorial N : ℝ)
      ≤ Real.log ((N ^ N : ℕ) : ℝ) := Real.log_le_log hpos (by exact_mod_cast hfact_le)
    _ = (N : ℝ) * Real.log (N : ℝ) := by rw [Nat.cast_pow, Real.log_pow]

lemma sum_log_div_prime_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ≤
      2 * Real.log (N : ℝ) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hdvd := prod_prime_pow_div_dvd_factorial N
  have hle_nat : (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, p ^ (N / p)) ≤ Nat.factorial N :=
    Nat.le_of_dvd (Nat.factorial_pos N) hdvd
  have hprod_pos : (0 : ℝ) < ((∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, p ^ (N / p) : ℕ) : ℝ) := by
    have hnat : 0 < ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, p ^ (N / p) :=
      Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.mp hp).2.pos _
    exact_mod_cast hnat
  have hlog_prod : Real.log ((∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, p ^ (N / p) : ℕ) : ℝ) =
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ((N / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod (fun p hp => by
      have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Finset.mem_filter.mp hp).2.pos
      exact_mod_cast (pow_pos hp_pos _).ne')]
    refine Finset.sum_congr rfl fun p _ => by rw [Nat.cast_pow, Real.log_pow]
  have hsum_le : ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ((N / p : ℕ) : ℝ) * Real.log (p : ℝ) ≤
      (N : ℝ) * Real.log (N : ℝ) := by
    calc ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ((N / p : ℕ) : ℝ) * Real.log (p : ℝ)
        = Real.log ((∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, p ^ (N / p) : ℕ) : ℝ) :=
          hlog_prod.symm
      _ ≤ Real.log (Nat.factorial N : ℝ) := Real.log_le_log hprod_pos (by exact_mod_cast hle_nat)
      _ ≤ (N : ℝ) * Real.log (N : ℝ) := log_factorial_le N hN
  have hhalf : (N : ℝ) / 2 * ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ≤
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ((N / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp_mem := Finset.mem_filter.mp hp
    have hp_Icc := Finset.mem_Icc.mp hp_mem.1
    have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_mem.2.pos
    have hlog_nonneg : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp_mem.2.one_le)
    have hdiv_ge1 : 1 ≤ N / p := (Nat.le_div_iff_mul_le hp_mem.2.pos).mpr (by omega)
    have h2div : N ≤ 2 * (N / p) * p := by
      have hlt := Nat.lt_div_mul_add (a := N) (b := p) hp_mem.2.pos
      have : N / p + 1 ≤ 2 * (N / p) := by omega
      have hmul : (N / p + 1) * p ≤ (2 * (N / p)) * p := Nat.mul_le_mul_right p this
      have : N < (N / p + 1) * p := by linarith
      omega
    have hdiv_r : (N : ℝ) / (2 * (p : ℝ)) ≤ ((N / p : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (p : ℝ))]
      have h2r : (N : ℝ) ≤ 2 * ((N / p : ℕ) : ℝ) * (p : ℝ) := by exact_mod_cast h2div
      linarith
    calc (N : ℝ) / 2 * (Real.log (p : ℝ) / (p : ℝ))
        = ((N : ℝ) / (2 * (p : ℝ))) * Real.log (p : ℝ) := by ring
      _ ≤ ((N / p : ℕ) : ℝ) * Real.log (p : ℝ) := mul_le_mul_of_nonneg_right hdiv_r hlog_nonneg
  have h1 : (N : ℝ) / 2 * ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ≤
      (N : ℝ) / 2 * (2 * Real.log (N : ℝ)) := by linarith
  exact le_of_mul_le_mul_left h1 (by positivity)

lemma sum_inv_higher_primePowers_le (N : ℕ) :
    ∑ pk ∈ (primePowers N).filter (fun pk => 2 ≤ pk.2), ((pk.1 : ℝ) ^ pk.2)⁻¹ ≤ 1 := by
  have hsub : (primePowers N).filter (fun pk => 2 ≤ pk.2) ⊆
      ((Finset.Icc 1 N).filter Nat.Prime).biUnion fun p =>
        (Finset.Icc 2 N).image (p, ·) := by
    intro ⟨p, k⟩ hpk
    simp only [Finset.mem_filter, mem_primePowers] at hpk
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
      Prod.mk.injEq]
    have hp_le : p ≤ N := (Nat.le_self_pow (by omega : k ≠ 0) p).trans hpk.1.2.2
    have hk_le : k ≤ N := (Nat.lt_pow_self hpk.1.1.one_lt).le.trans hpk.1.2.2
    exact ⟨p, ⟨⟨hpk.1.1.one_le, hp_le⟩, hpk.1.1⟩, k, ⟨hpk.2, hk_le⟩, rfl, rfl⟩
  have hdisj : Set.PairwiseDisjoint (↑((Finset.Icc 1 N).filter Nat.Prime) : Set ℕ)
      (fun p => (Finset.Icc 2 N).image (p, ·)) := by
    intro p₁ _ p₂ _ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨k₁, _, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨k₂, _, heq⟩
    exact hne (congr_arg Prod.fst heq).symm
  have h1 : ∑ pk ∈ (primePowers N).filter (fun pk => 2 ≤ pk.2), ((pk.1 : ℝ) ^ pk.2)⁻¹ ≤
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ∑ k ∈ Finset.Icc 2 N, ((p : ℝ) ^ k)⁻¹ := by
    calc ∑ pk ∈ (primePowers N).filter (fun pk => 2 ≤ pk.2), ((pk.1 : ℝ) ^ pk.2)⁻¹
        ≤ ∑ pk ∈ ((Finset.Icc 1 N).filter Nat.Prime).biUnion
            (fun p => (Finset.Icc 2 N).image (p, ·)), ((pk.1 : ℝ) ^ pk.2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            ∑ pk ∈ (Finset.Icc 2 N).image (p, ·), ((pk.1 : ℝ) ^ pk.2)⁻¹ :=
          Finset.sum_biUnion hdisj
      _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            ∑ k ∈ Finset.Icc 2 N, ((p : ℝ) ^ k)⁻¹ := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_image (fun _ _ _ _ h => congr_arg Prod.snd h)]
  have h2 : ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ∑ k ∈ Finset.Icc 2 N, ((p : ℝ) ^ k)⁻¹ ≤
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hp_prime := (Finset.mem_filter.mp hp).2
    have hshift : ∑ k ∈ Finset.Icc 2 N, ((p : ℝ) ^ k)⁻¹ ≤
        (p : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, ((p : ℝ) ^ j)⁻¹ := by
      rw [Finset.mul_sum]
      have hreidx : ∑ k ∈ Finset.Icc 2 N, ((p : ℝ) ^ k)⁻¹ =
          ∑ j ∈ Finset.Icc 1 (N - 1), (p : ℝ)⁻¹ * ((p : ℝ) ^ j)⁻¹ := by
        refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
        · intro k₁ h1 k₂ h2 heq; simp only [Finset.mem_Icc] at h1 h2; omega
        · intro j hj; simp only [Finset.mem_Icc] at hj
          exact ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro k hk
          simp only [Finset.mem_Icc] at hk
          have hk_eq : k = (k - 1) + 1 := by omega
          conv_lhs => rw [hk_eq, pow_succ', mul_inv]
      rw [hreidx]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (Nat.sub_le N 1)) (fun _ _ _ => by positivity)
    calc ∑ k ∈ Finset.Icc 2 N, ((p : ℝ) ^ k)⁻¹
        ≤ (p : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, ((p : ℝ) ^ j)⁻¹ := hshift
      _ ≤ (p : ℝ)⁻¹ * ((p : ℝ) - 1)⁻¹ :=
          mul_le_mul_of_nonneg_left (sum_inv_pow_Icc_le hp_prime) (by positivity)
      _ = ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by rw [mul_inv]
  have hsub2 : (Finset.Icc 1 N).filter Nat.Prime ⊆ Finset.Icc 2 N := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨hp.2.two_le, hp.1.2⟩
  have htele : ∑ m ∈ Finset.Icc 2 N, ((m : ℝ) * ((m : ℝ) - 1))⁻¹ ≤ 1 := by
    clear hsub hdisj h1 h2 hsub2
    induction N with
    | zero => simp
    | succ n ih =>
      by_cases hn : n = 0
      · subst hn; simp
      · have hIcc : Finset.Icc 2 (n + 1) = insert (n + 1) (Finset.Icc 2 n) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp)]
        have hsum_exact : ∀ M : ℕ, 1 ≤ M →
            ∑ m ∈ Finset.Icc 2 M, ((m : ℝ) * ((m : ℝ) - 1))⁻¹ = 1 - (M : ℝ)⁻¹ := by
          intro M hM
          induction M, hM using Nat.le_induction with
          | base => simp
          | succ M hM ihM =>
            have hI : Finset.Icc 2 (M + 1) = insert (M + 1) (Finset.Icc 2 M) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hI, Finset.sum_insert (by simp), ihM]
            have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
            have hM1_pos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
            push_cast
            field_simp [hM_pos.ne', hM1_pos.ne']
            ring
        have hM := hsum_exact (n + 1) (by omega)
        rw [hIcc, Finset.sum_insert (by simp)] at hM
        rw [hM]
        have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
        linarith
  calc ∑ pk ∈ (primePowers N).filter (fun pk => 2 ≤ pk.2), ((pk.1 : ℝ) ^ pk.2)⁻¹
      ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := h1.trans h2
    _ ≤ ∑ m ∈ Finset.Icc 2 N, ((m : ℝ) * ((m : ℝ) - 1))⁻¹ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun m hm _ => ?_
        have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
        exact inv_nonneg.mpr (by nlinarith)
    _ ≤ 1 := htele

lemma sum_inv_large_primePowers_le (N : ℕ) :
    ∑ pk ∈ (primePowers N).filter (fun pk => N < (pk.1 ^ pk.2) ^ 2),
      ((pk.1 : ℝ) ^ pk.2)⁻¹ ≤ 5 := by
  by_cases hN2 : N < 2
  · have hemp : (primePowers N).filter (fun pk => N < (pk.1 ^ pk.2) ^ 2) = ∅ := by
      ext ⟨p, k⟩
      simp only [Finset.mem_filter, mem_primePowers, Finset.notMem_empty, iff_false, not_and]
      intro h _
      have hp2 : 2 ≤ p := h.1.two_le
      have hpk : 2 ≤ p ^ k := hp2.trans (Nat.le_self_pow (by omega : k ≠ 0) p)
      omega
    rw [hemp, Finset.sum_empty]
    norm_num
  · have hN_ge2 : 2 ≤ N := by omega
    have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    -- Split into `k = 1` and `2 ≤ k`
    have hsplit : (primePowers N).filter (fun pk => N < (pk.1 ^ pk.2) ^ 2) ⊆
        ((primePowers N).filter (fun pk => pk.2 = 1 ∧ N < (pk.1 ^ pk.2) ^ 2)) ∪
        ((primePowers N).filter (fun pk => 2 ≤ pk.2)) := by
      intro ⟨p, k⟩ hpk
      simp only [Finset.mem_filter, mem_primePowers, Finset.mem_union] at hpk ⊢
      by_cases hk1 : k = 1
      · left; exact ⟨hpk.1, hk1, hpk.2⟩
      · right; exact ⟨hpk.1, by omega⟩
    have hpart1 : ∑ pk ∈ (primePowers N).filter (fun pk => pk.2 = 1 ∧ N < (pk.1 ^ pk.2) ^ 2),
          ((pk.1 : ℝ) ^ pk.2)⁻¹ ≤ 4 := by
      have hbij : ∑ pk ∈ (primePowers N).filter (fun pk => pk.2 = 1 ∧ N < (pk.1 ^ pk.2) ^ 2),
            ((pk.1 : ℝ) ^ pk.2)⁻¹ =
          ∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (fun p => N < p ^ 2), (p : ℝ)⁻¹ := by
        refine Finset.sum_bij (fun pk _ => pk.1) ?_ ?_ ?_ ?_
        · intro ⟨p, k⟩ hpk
          simp only [Finset.mem_filter, mem_primePowers, Finset.mem_Icc] at hpk ⊢
          rcases hpk with ⟨⟨hp, _, hpk⟩, rfl, hgt⟩
          simp only [pow_one] at hpk hgt
          exact ⟨⟨⟨hp.one_le, hpk⟩, hp⟩, hgt⟩
        · intro ⟨p₁, k₁⟩ h1 ⟨p₂, k₂⟩ h2 heq
          simp only [Finset.mem_filter] at h1 h2
          exact Prod.ext heq (h1.2.1.trans h2.2.1.symm)
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_Icc] at hp
          refine ⟨(p, 1), Finset.mem_filter.mpr
            ⟨mem_primePowers.mpr ⟨hp.1.2, le_rfl, by simpa using hp.1.1.2⟩, rfl,
              by simpa using hp.2⟩, rfl⟩
        · intro ⟨p, k⟩ hpk
          have hk1 : k = 1 := (Finset.mem_filter.mp hpk).2.1
          simp [hk1]
      rw [hbij]
      have hterm_le : ∀ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (fun p => N < p ^ 2),
          (p : ℝ)⁻¹ ≤ (2 / Real.log (N : ℝ)) * (Real.log (p : ℝ) / (p : ℝ)) := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Icc] at hp
        have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.1.2.pos
        have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
        have hlt_r : (N : ℝ) < (p : ℝ) ^ 2 := by exact_mod_cast hp.2
        have hlog_lt : Real.log (N : ℝ) < 2 * Real.log (p : ℝ) := by
          have h1 := Real.log_lt_log hN_pos hlt_r
          rw [Real.log_pow] at h1
          push_cast at h1
          exact h1
        have hfrac : 1 ≤ 2 * Real.log (p : ℝ) / Real.log (N : ℝ) :=
          (one_le_div hlogN_pos).mpr hlog_lt.le
        calc (p : ℝ)⁻¹ = 1 * (p : ℝ)⁻¹ := (one_mul _).symm
          _ ≤ (2 * Real.log (p : ℝ) / Real.log (N : ℝ)) * (p : ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_right hfrac (by positivity)
          _ = (2 / Real.log (N : ℝ)) * (Real.log (p : ℝ) / (p : ℝ)) := by ring
      calc ∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (fun p => N < p ^ 2), (p : ℝ)⁻¹
          ≤ ∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (fun p => N < p ^ 2),
              (2 / Real.log (N : ℝ)) * (Real.log (p : ℝ) / (p : ℝ)) :=
            Finset.sum_le_sum hterm_le
        _ = (2 / Real.log (N : ℝ)) *
              ∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (fun p => N < p ^ 2),
                Real.log (p : ℝ) / (p : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ (2 / Real.log (N : ℝ)) *
              ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p hp _ => ?_
            have hp_prime := (Finset.mem_filter.mp hp).2
            exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp_prime.one_le)) (by positivity)
        _ ≤ (2 / Real.log (N : ℝ)) * (2 * Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_log_div_prime_le N (by omega)) (by positivity)
        _ = 4 := by field_simp [hlogN_pos.ne']; ring
    calc ∑ pk ∈ (primePowers N).filter (fun pk => N < (pk.1 ^ pk.2) ^ 2), ((pk.1 : ℝ) ^ pk.2)⁻¹
        ≤ ∑ pk ∈ ((primePowers N).filter (fun pk => pk.2 = 1 ∧ N < (pk.1 ^ pk.2) ^ 2)) ∪
            ((primePowers N).filter (fun pk => 2 ≤ pk.2)), ((pk.1 : ℝ) ^ pk.2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsplit fun _ _ _ => by positivity
      _ ≤ (∑ pk ∈ (primePowers N).filter (fun pk => pk.2 = 1 ∧ N < (pk.1 ^ pk.2) ^ 2),
            ((pk.1 : ℝ) ^ pk.2)⁻¹) +
          (∑ pk ∈ (primePowers N).filter (fun pk => 2 ≤ pk.2), ((pk.1 : ℝ) ^ pk.2)⁻¹) := by
          have hui := Finset.sum_union_inter
            (s₁ := (primePowers N).filter (fun pk => pk.2 = 1 ∧ N < (pk.1 ^ pk.2) ^ 2))
            (s₂ := (primePowers N).filter (fun pk => 2 ≤ pk.2))
            (f := fun pk : ℕ × ℕ => ((pk.1 : ℝ) ^ pk.2)⁻¹)
          have hinter_nonneg : 0 ≤ ∑ pk ∈
              ((primePowers N).filter (fun pk => pk.2 = 1 ∧ N < (pk.1 ^ pk.2) ^ 2)) ∩
              ((primePowers N).filter (fun pk => 2 ≤ pk.2)), ((pk.1 : ℝ) ^ pk.2)⁻¹ :=
            Finset.sum_nonneg fun _ _ => by positivity
          linarith
      _ ≤ 4 + 1 := add_le_add hpart1 (sum_inv_higher_primePowers_le N)
      _ = 5 := by norm_num

lemma sum_small_primePowers_le (N : ℕ) :
    ∑ pk ∈ (primePowers N).filter (fun pk => (pk.1 ^ pk.2) ^ 2 ≤ N),
      ((pk.1 : ℝ) ^ pk.2) ≤ (N : ℝ) := by
  set S₁ := (primePowers N).filter (fun pk => (pk.1 ^ pk.2) ^ 2 ≤ N)
  set M := Nat.sqrt N
  have hmaps : S₁.image (fun pk : ℕ × ℕ => pk.1 ^ pk.2) ⊆ Finset.Icc 1 M := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨⟨p, k⟩, hpk, rfl⟩
    simp only [S₁, Finset.mem_filter, mem_primePowers] at hpk
    have hpos : 1 ≤ p ^ k := Nat.one_le_pow k p hpk.1.1.pos
    have hle : p ^ k ≤ M := Nat.le_sqrt.mpr (by simpa [sq] using hpk.2)
    exact Finset.mem_Icc.mpr ⟨hpos, hle⟩
  have hinj : Set.InjOn (fun pk : ℕ × ℕ => pk.1 ^ pk.2) ↑S₁ :=
    (primePower_val_injOn N).mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
  have hsum_nat : ∑ pk ∈ S₁, (pk.1 ^ pk.2) ≤ M ^ 2 := by
    calc ∑ pk ∈ S₁, (pk.1 ^ pk.2)
        = ∑ m ∈ S₁.image (fun pk : ℕ × ℕ => pk.1 ^ pk.2), m :=
          (Finset.sum_image (f := id) hinj).symm
      _ ≤ ∑ m ∈ Finset.Icc 1 M, m := Finset.sum_le_sum_of_subset hmaps
      _ ≤ ∑ _m ∈ Finset.Icc 1 M, M := Finset.sum_le_sum fun m hm => (Finset.mem_Icc.mp hm).2
      _ = M ^ 2 := by simp [sq]
  have hM2 : M ^ 2 ≤ N := by
    simpa [sq] using Nat.sqrt_le N
  have hcast : (∑ pk ∈ S₁, ((pk.1 : ℝ) ^ pk.2)) = ((∑ pk ∈ S₁, (pk.1 ^ pk.2) : ℕ) : ℝ) := by
    push_cast; rfl
  rw [hcast]
  exact_mod_cast hsum_nat.trans hM2

lemma sum_inv_small_primePowers_le (N : ℕ) :
    ∑ pk ∈ (primePowers N).filter (fun pk => (pk.1 ^ pk.2) ^ 2 ≤ N),
      ((pk.1 : ℝ) ^ pk.2)⁻¹ ≤ (N : ℝ) := by
  have hle : ∑ pk ∈ (primePowers N).filter (fun pk => (pk.1 ^ pk.2) ^ 2 ≤ N),
        ((pk.1 : ℝ) ^ pk.2)⁻¹ ≤
      ∑ pk ∈ (primePowers N).filter (fun pk => (pk.1 ^ pk.2) ^ 2 ≤ N),
        ((pk.1 : ℝ) ^ pk.2) := by
    refine Finset.sum_le_sum fun pk hpk => ?_
    have hm := mem_primePowers.mp (Finset.mem_filter.mp hpk).1
    have hge1 : (1 : ℝ) ≤ (pk.1 : ℝ) ^ pk.2 := by
      exact_mod_cast Nat.one_le_pow pk.2 pk.1 hm.1.pos
    exact (inv_le_one_of_one_le₀ hge1).trans hge1
  exact hle.trans (sum_small_primePowers_le N)

lemma card_multiples_Icc_one (N d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Icc 1 N).filter (d ∣ ·)).card = N / d := by
  have h := card_multiples_Icc_eq 0 N d hd
  simpa using h

lemma card_exactPowDvd (p k N : ℕ) (hp : Nat.Prime p) :
    ((Finset.Icc 1 N).filter (exactPowDvd p k)).card = N / p ^ k - N / p ^ (k + 1) := by
  have hsub : (Finset.Icc 1 N).filter (p ^ (k + 1) ∣ ·) ⊆ (Finset.Icc 1 N).filter (p ^ k ∣ ·) := by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, (pow_dvd_pow p (Nat.le_succ k)).trans hn.2⟩
  have hsdiff : (Finset.Icc 1 N).filter (exactPowDvd p k) =
      (Finset.Icc 1 N).filter (p ^ k ∣ ·) \ (Finset.Icc 1 N).filter (p ^ (k + 1) ∣ ·) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_sdiff, exactPowDvd]
    tauto
  rw [hsdiff, Finset.card_sdiff_of_subset hsub,
    card_multiples_Icc_one N (p ^ k) (Nat.one_le_pow k p hp.pos),
    card_multiples_Icc_one N (p ^ (k + 1)) (Nat.one_le_pow (k + 1) p hp.pos)]

lemma abs_div_sub_real_div_le (N d : ℕ) (hd : 1 ≤ d) :
    0 ≤ (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) ∧ (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) < 1 := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  constructor
  · have hle : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hd_pos]
      exact_mod_cast Nat.div_mul_le_self N d
    linarith
  · have hlt : (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hd_pos]
      have h := Nat.lt_div_mul_add (a := N) (b := d) (by omega)
      have h' : N < (N / d + 1) * d := by linarith
      exact_mod_cast h'
    linarith

lemma abs_card_exactPowDvd_sub (p k N : ℕ) (hp : Nat.Prime p) :
    |(((Finset.Icc 1 N).filter (exactPowDvd p k)).card : ℝ) -
      (N : ℝ) * tkExactDensity (p, k)| ≤ 1 := by
  rw [card_exactPowDvd p k N hp]
  have hle : N / p ^ (k + 1) ≤ N / p ^ k :=
    Nat.div_le_div_left (Nat.pow_le_pow_right hp.pos (Nat.le_succ k)) (pow_pos hp.pos k)
  rw [Nat.cast_sub hle]
  have h1 := abs_div_sub_real_div_le N (p ^ k) (Nat.one_le_pow k p hp.pos)
  have h2 := abs_div_sub_real_div_le N (p ^ (k + 1)) (Nat.one_le_pow (k + 1) p hp.pos)
  have hdens : (N : ℝ) * tkExactDensity (p, k) =
      (N : ℝ) / ((p ^ k : ℕ) : ℝ) - (N : ℝ) / ((p ^ (k + 1) : ℕ) : ℝ) := by
    unfold tkExactDensity
    push_cast
    rw [pow_succ]
    have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    field_simp [hp_ne]
  rw [hdens, abs_le]
  constructor <;> linarith

lemma card_exactPowDvd_pair_sub (p k q j N : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) :
    |(((Finset.Icc 1 N).filter (fun n => exactPowDvd p k n ∧ exactPowDvd q j n)).card : ℝ) -
      (N : ℝ) * tkExactDensity (p, k) * tkExactDensity (q, j)| ≤ 2 := by
  -- Inclusion-exclusion on `A = {n ≤ N | p^k q^j ∣ n}`, `B = {p^{k+1} q^j ∣ n}`, `C = {p^k q^{j+1} ∣ n}`
  set A := (Finset.Icc 1 N).filter (fun n => p ^ k * q ^ j ∣ n)
  set B := (Finset.Icc 1 N).filter (fun n => p ^ (k + 1) * q ^ j ∣ n)
  set C := (Finset.Icc 1 N).filter (fun n => p ^ k * q ^ (j + 1) ∣ n)
  set BC := (Finset.Icc 1 N).filter (fun n => p ^ (k + 1) * q ^ (j + 1) ∣ n)
  have hcop : ∀ a b, Nat.Coprime (p ^ a) (q ^ b) := fun a b =>
    ((Nat.coprime_primes hp hq).mpr hpq).pow a b
  have hB_sub : B ⊆ A := by
    intro n hn
    simp only [A, B, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, (mul_dvd_mul_right (pow_dvd_pow p (Nat.le_succ k)) (q ^ j)).trans hn.2⟩
  have hC_sub : C ⊆ A := by
    intro n hn
    simp only [A, C, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, (mul_dvd_mul_left (p ^ k) (pow_dvd_pow q (Nat.le_succ j))).trans hn.2⟩
  have hBC_eq : B ∩ C = BC := by
    ext n
    simp only [B, C, BC, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn, h1⟩, ⟨_, h2⟩⟩
      refine ⟨hn, (hcop (k + 1) (j + 1)).mul_dvd_of_dvd_of_dvd ?_ ?_⟩
      · exact (dvd_mul_right _ _).trans h1
      · exact (dvd_mul_left _ _).trans h2
    · rintro ⟨hn, h⟩
      refine ⟨⟨hn, (mul_dvd_mul_left (p ^ (k + 1)) (pow_dvd_pow q (Nat.le_succ j))).trans h⟩,
        ⟨hn, (mul_dvd_mul_right (pow_dvd_pow p (Nat.le_succ k)) (q ^ (j + 1))).trans h⟩⟩
  have hF_eq : (Finset.Icc 1 N).filter (fun n => exactPowDvd p k n ∧ exactPowDvd q j n) =
      A \ (B ∪ C) := by
    ext n
    rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union]
    simp only [A, B, C, Finset.mem_filter, exactPowDvd]
    constructor
    · rintro ⟨hn, ⟨hpk, hnpk⟩, ⟨hqj, hnqj⟩⟩
      refine ⟨⟨hn, (hcop k j).mul_dvd_of_dvd_of_dvd hpk hqj⟩, ?_⟩
      rintro (⟨_, h1⟩ | ⟨_, h2⟩)
      · exact hnpk ((dvd_mul_right _ _).trans h1)
      · exact hnqj ((dvd_mul_left _ _).trans h2)
    · rintro ⟨⟨hn, hA⟩, hnot⟩
      have hpk : p ^ k ∣ n := (dvd_mul_right _ _).trans hA
      have hqj : q ^ j ∣ n := (dvd_mul_left _ _).trans hA
      refine ⟨hn, ⟨hpk, fun hpk1 => hnot (Or.inl ⟨hn, (hcop (k + 1) j).mul_dvd_of_dvd_of_dvd hpk1 hqj⟩)⟩,
        ⟨hqj, fun hqj1 => hnot (Or.inr ⟨hn, (hcop k (j + 1)).mul_dvd_of_dvd_of_dvd hpk hqj1⟩)⟩⟩
  have hcard_r : (((Finset.Icc 1 N).filter (fun n => exactPowDvd p k n ∧ exactPowDvd q j n)).card : ℝ) =
      (A.card : ℝ) - (B.card : ℝ) - (C.card : ℝ) + (BC.card : ℝ) := by
    rw [hF_eq, Finset.card_sdiff_of_subset (Finset.union_subset hB_sub hC_sub)]
    have hu_le : (B ∪ C).card ≤ A.card := Finset.card_le_card (Finset.union_subset hB_sub hC_sub)
    rw [Nat.cast_sub hu_le]
    have hie := Finset.card_union_add_card_inter B C
    rw [hBC_eq] at hie
    have hie_r : ((B ∪ C).card : ℝ) + (BC.card : ℝ) = (B.card : ℝ) + (C.card : ℝ) := by
      exact_mod_cast hie
    linarith
  rw [hcard_r]
  have hA : A.card = N / (p ^ k * q ^ j) :=
    card_multiples_Icc_one N _ (Nat.mul_pos (pow_pos hp.pos k) (pow_pos hq.pos j))
  have hB : B.card = N / (p ^ (k + 1) * q ^ j) :=
    card_multiples_Icc_one N _ (Nat.mul_pos (pow_pos hp.pos (k + 1)) (pow_pos hq.pos j))
  have hC : C.card = N / (p ^ k * q ^ (j + 1)) :=
    card_multiples_Icc_one N _ (Nat.mul_pos (pow_pos hp.pos k) (pow_pos hq.pos (j + 1)))
  have hBC : BC.card = N / (p ^ (k + 1) * q ^ (j + 1)) :=
    card_multiples_Icc_one N _ (Nat.mul_pos (pow_pos hp.pos (k + 1)) (pow_pos hq.pos (j + 1)))
  rw [hA, hB, hC, hBC]
  have eA := abs_div_sub_real_div_le N (p ^ k * q ^ j)
    (Nat.mul_pos (pow_pos hp.pos k) (pow_pos hq.pos j))
  have eB := abs_div_sub_real_div_le N (p ^ (k + 1) * q ^ j)
    (Nat.mul_pos (pow_pos hp.pos (k + 1)) (pow_pos hq.pos j))
  have eC := abs_div_sub_real_div_le N (p ^ k * q ^ (j + 1))
    (Nat.mul_pos (pow_pos hp.pos k) (pow_pos hq.pos (j + 1)))
  have eBC := abs_div_sub_real_div_le N (p ^ (k + 1) * q ^ (j + 1))
    (Nat.mul_pos (pow_pos hp.pos (k + 1)) (pow_pos hq.pos (j + 1)))
  have hdens : (N : ℝ) * tkExactDensity (p, k) * tkExactDensity (q, j) =
      (N : ℝ) / ((p ^ k * q ^ j : ℕ) : ℝ) -
      (N : ℝ) / ((p ^ (k + 1) * q ^ j : ℕ) : ℝ) -
      (N : ℝ) / ((p ^ k * q ^ (j + 1) : ℕ) : ℝ) +
      (N : ℝ) / ((p ^ (k + 1) * q ^ (j + 1) : ℕ) : ℝ) := by
    unfold tkExactDensity
    push_cast
    rw [pow_succ, pow_succ]
    have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hq_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
    field_simp [hp_ne, hq_ne]
    ring
  rw [hdens, abs_le]
  constructor <;> linarith

lemma tk_piece1_bound (f : ℕ → ℂ) (N : ℕ) :
    let S₁ := (primePowers N).filter (fun pk => (pk.1 ^ pk.2) ^ 2 ≤ N)
    let f₁ : ℕ → ℂ := fun n =>
      ∑ pk ∈ S₁.filter (fun pk => exactPowDvd pk.1 pk.2 n), f (pk.1 ^ pk.2)
    let A₁ : ℂ := ∑ pk ∈ S₁, f (pk.1 ^ pk.2) * (tkExactDensity pk : ℂ)
    ∑ n ∈ Finset.Icc 1 N, ‖f₁ n - A₁‖ ^ 2 ≤ 5 * (N : ℝ) * tkVarSq f N := by
  intro S₁ f₁ A₁
  set Bsq : ℝ := tkVarSq f N
  have hBsq_nonneg : 0 ≤ Bsq := tkVarSq_nonneg f N
  have hB₁_le : ∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖ ^ 2 / ((pk.1 : ℝ) ^ pk.2) ≤ Bsq :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ => div_nonneg (sq_nonneg _) (by positivity)
  -- Key Cauchy–Schwarz bound: `(∑_{pk ∈ S₁} ‖f(p^k)‖)^2 ≤ N * Bsq`
  have hsum_norm_sq : (∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖) ^ 2 ≤ (N : ℝ) * Bsq := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S₁
      (fun pk => Real.sqrt ((pk.1 : ℝ) ^ pk.2))
      (fun pk => ‖f (pk.1 ^ pk.2)‖ / Real.sqrt ((pk.1 : ℝ) ^ pk.2))
    have hlhs : ∑ pk ∈ S₁, Real.sqrt ((pk.1 : ℝ) ^ pk.2) *
        (‖f (pk.1 ^ pk.2)‖ / Real.sqrt ((pk.1 : ℝ) ^ pk.2)) =
        ∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖ := by
      refine Finset.sum_congr rfl fun pk hpk => ?_
      have hp_pos : (0 : ℝ) < (pk.1 : ℝ) ^ pk.2 := by
        have hm := mem_primePowers.mp (Finset.mem_filter.mp hpk).1
        exact_mod_cast pow_pos hm.1.pos pk.2
      field_simp [(Real.sqrt_pos.mpr hp_pos).ne']
    have hr1 : ∑ pk ∈ S₁, (Real.sqrt ((pk.1 : ℝ) ^ pk.2)) ^ 2 =
        ∑ pk ∈ S₁, ((pk.1 : ℝ) ^ pk.2) :=
      Finset.sum_congr rfl fun pk _ => Real.sq_sqrt (by positivity)
    have hr2 : ∑ pk ∈ S₁, (‖f (pk.1 ^ pk.2)‖ / Real.sqrt ((pk.1 : ℝ) ^ pk.2)) ^ 2 =
        ∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖ ^ 2 / ((pk.1 : ℝ) ^ pk.2) := by
      refine Finset.sum_congr rfl fun pk _ => ?_
      rw [div_pow, Real.sq_sqrt (by positivity)]
    rw [hlhs, hr1, hr2] at hcs
    calc (∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖) ^ 2
        ≤ (∑ pk ∈ S₁, ((pk.1 : ℝ) ^ pk.2)) *
            (∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖ ^ 2 / ((pk.1 : ℝ) ^ pk.2)) := hcs
      _ ≤ (N : ℝ) * Bsq := mul_le_mul (sum_small_primePowers_le N) hB₁_le
            (Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (by positivity))
            (Nat.cast_nonneg N)
  -- Key Cauchy–Schwarz bound on `‖A₁‖^2 ≤ N * Bsq`
  have hA₁_sq : ‖A₁‖ ^ 2 ≤ (N : ℝ) * Bsq := by
    have hA₁_le : ‖A₁‖ ≤ ∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖ / ((pk.1 : ℝ) ^ pk.2) := by
      calc ‖A₁‖ ≤ ∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2) * (tkExactDensity pk : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖ / ((pk.1 : ℝ) ^ pk.2) := by
            refine Finset.sum_le_sum fun pk hpk => ?_
            have hm := mem_primePowers.mp (Finset.mem_filter.mp hpk).1
            have hp_gt1 : (1 : ℝ) < (pk.1 : ℝ) := by exact_mod_cast hm.1.one_lt
            have h01 : 0 ≤ 1 - (pk.1 : ℝ)⁻¹ ∧ 1 - (pk.1 : ℝ)⁻¹ ≤ 1 :=
              ⟨by linarith [inv_lt_one_of_one_lt₀ hp_gt1], by linarith [inv_pos.mpr (by linarith : (0 : ℝ) < (pk.1 : ℝ))]⟩
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            unfold tkExactDensity
            rw [abs_of_nonneg (mul_nonneg (by positivity) h01.1), div_eq_mul_inv]
            calc ‖f (pk.1 ^ pk.2)‖ * (((pk.1 : ℝ) ^ pk.2)⁻¹ * (1 - (pk.1 : ℝ)⁻¹))
                ≤ ‖f (pk.1 ^ pk.2)‖ * (((pk.1 : ℝ) ^ pk.2)⁻¹ * 1) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h01.2 (by positivity)) (norm_nonneg _)
              _ = ‖f (pk.1 ^ pk.2)‖ * ((pk.1 : ℝ) ^ pk.2)⁻¹ := by ring
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S₁
      (fun pk => 1 / Real.sqrt ((pk.1 : ℝ) ^ pk.2))
      (fun pk => ‖f (pk.1 ^ pk.2)‖ / Real.sqrt ((pk.1 : ℝ) ^ pk.2))
    have hlhs : ∑ pk ∈ S₁, (1 / Real.sqrt ((pk.1 : ℝ) ^ pk.2)) *
        (‖f (pk.1 ^ pk.2)‖ / Real.sqrt ((pk.1 : ℝ) ^ pk.2)) =
        ∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖ / ((pk.1 : ℝ) ^ pk.2) := by
      refine Finset.sum_congr rfl fun pk _ => ?_
      rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by positivity)]
    have hr1 : ∑ pk ∈ S₁, (1 / Real.sqrt ((pk.1 : ℝ) ^ pk.2)) ^ 2 =
        ∑ pk ∈ S₁, ((pk.1 : ℝ) ^ pk.2)⁻¹ := by
      refine Finset.sum_congr rfl fun pk _ => ?_
      rw [div_pow, one_pow, Real.sq_sqrt (by positivity), one_div]
    have hr2 : ∑ pk ∈ S₁, (‖f (pk.1 ^ pk.2)‖ / Real.sqrt ((pk.1 : ℝ) ^ pk.2)) ^ 2 =
        ∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖ ^ 2 / ((pk.1 : ℝ) ^ pk.2) := by
      refine Finset.sum_congr rfl fun pk _ => ?_
      rw [div_pow, Real.sq_sqrt (by positivity)]
    rw [hlhs, hr1, hr2] at hcs
    calc ‖A₁‖ ^ 2 ≤ (∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖ / ((pk.1 : ℝ) ^ pk.2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hA₁_le 2
      _ ≤ (∑ pk ∈ S₁, ((pk.1 : ℝ) ^ pk.2)⁻¹) *
            (∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖ ^ 2 / ((pk.1 : ℝ) ^ pk.2)) := hcs
      _ ≤ (N : ℝ) * Bsq := mul_le_mul (sum_inv_small_primePowers_le N) hB₁_le
            (Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (by positivity))
            (Nat.cast_nonneg N)
  -- Expand `∑_{n=1}^N ‖f₁ n - A₁‖^2`
  have hexpand_C : (∑ n ∈ Finset.Icc 1 N, ((‖f₁ n - A₁‖ ^ 2 : ℝ) : ℂ)) =
      (∑ n ∈ Finset.Icc 1 N, ((‖f₁ n‖ ^ 2 : ℝ) : ℂ)) -
      2 * ((star A₁ * ∑ n ∈ Finset.Icc 1 N, f₁ n).re : ℂ) +
      (N : ℂ) * ((‖A₁‖ ^ 2 : ℝ) : ℂ) := by
    have hpt : ∀ z w : ℂ, ((‖z - w‖ ^ 2 : ℝ) : ℂ) =
        ((‖z‖ ^ 2 : ℝ) : ℂ) - 2 * ((star w * z).re : ℂ) + ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      intro z w
      push_cast
      rw [← Complex.mul_conj', ← Complex.mul_conj', ← Complex.mul_conj']
      have hre : 2 * ((starRingEnd ℂ w * z).re : ℂ) =
          starRingEnd ℂ w * z + w * starRingEnd ℂ z := by
        have h1 := Complex.add_conj (starRingEnd ℂ w * z)
        rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply] at h1
        push_cast at h1
        linear_combination -h1
      rw [map_sub]
      change (z - w) * (starRingEnd ℂ z - starRingEnd ℂ w) =
        z * starRingEnd ℂ z - 2 * ((starRingEnd ℂ w * z).re : ℂ) + w * starRingEnd ℂ w
      rw [hre]
      ring
    simp_rw [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hre_sum : (∑ n ∈ Finset.Icc 1 N, ((star A₁ * f₁ n).re : ℂ)) =
        ((star A₁ * ∑ n ∈ Finset.Icc 1 N, f₁ n).re : ℂ) := by
      rw [← Complex.ofReal_sum, ← Complex.re_sum, ← Finset.mul_sum]
    rw [hre_sum]
    simp
  have hexpand : ∑ n ∈ Finset.Icc 1 N, ‖f₁ n - A₁‖ ^ 2 =
      (∑ n ∈ Finset.Icc 1 N, ‖f₁ n‖ ^ 2) -
      2 * (star A₁ * ∑ n ∈ Finset.Icc 1 N, f₁ n).re +
      (N : ℝ) * ‖A₁‖ ^ 2 := by
    have h := congr_arg Complex.re hexpand_C
    simp only [← Complex.ofReal_sum, Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      mul_zero, sub_zero, Complex.re_ofNat, Complex.im_ofNat] at h
    exact h
  -- Evaluate `∑ n, f₁ n = N * A₁ + R₁` with `‖R₁‖ ≤ ∑_{pk ∈ S₁} ‖f(p^k)‖`
  set R₁ : ℂ := ∑ pk ∈ S₁, f (pk.1 ^ pk.2) *
    ((((Finset.Icc 1 N).filter (exactPowDvd pk.1 pk.2)).card : ℝ) -
      (N : ℝ) * tkExactDensity pk : ℂ)
  have hsum_f1 : ∑ n ∈ Finset.Icc 1 N, f₁ n = (N : ℂ) * A₁ + R₁ := by
    have hswap : ∑ n ∈ Finset.Icc 1 N, f₁ n =
        ∑ pk ∈ S₁, f (pk.1 ^ pk.2) *
          (((Finset.Icc 1 N).filter (exactPowDvd pk.1 pk.2)).card : ℂ) := by
      dsimp [f₁]
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun pk _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hswap]
    dsimp [A₁, R₁]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun pk _ => ?_
    ring
  have hR1_norm : ‖R₁‖ ≤ ∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖ := by
    dsimp [R₁]
    calc ‖∑ pk ∈ S₁, f (pk.1 ^ pk.2) *
            ((((Finset.Icc 1 N).filter (exactPowDvd pk.1 pk.2)).card : ℝ) -
              (N : ℝ) * tkExactDensity pk : ℂ)‖
        ≤ ∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2) *
            ((((Finset.Icc 1 N).filter (exactPowDvd pk.1 pk.2)).card : ℝ) -
              (N : ℝ) * tkExactDensity pk : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖ := by
          refine Finset.sum_le_sum fun pk hpk => ?_
          have hm := mem_primePowers.mp (Finset.mem_filter.mp hpk).1
          rw [norm_mul, show ‖((((Finset.Icc 1 N).filter (exactPowDvd pk.1 pk.2)).card : ℝ) -
              (N : ℝ) * tkExactDensity pk : ℂ)‖ =
              |(((Finset.Icc 1 N).filter (exactPowDvd pk.1 pk.2)).card : ℝ) -
              (N : ℝ) * tkExactDensity pk| by
              have hc : ((((Finset.Icc 1 N).filter (exactPowDvd pk.1 pk.2)).card : ℝ) -
                  (N : ℝ) * tkExactDensity pk : ℂ) =
                  (((((Finset.Icc 1 N).filter (exactPowDvd pk.1 pk.2)).card : ℝ) -
                  (N : ℝ) * tkExactDensity pk : ℝ) : ℂ) := by push_cast; rfl
              rw [hc, Complex.norm_real, Real.norm_eq_abs]]
          have habs := abs_card_exactPowDvd_sub pk.1 pk.2 N hm.1
          calc ‖f (pk.1 ^ pk.2)‖ * |(((Finset.Icc 1 N).filter (exactPowDvd pk.1 pk.2)).card : ℝ) -
                  (N : ℝ) * tkExactDensity pk|
              ≤ ‖f (pk.1 ^ pk.2)‖ * 1 := mul_le_mul_of_nonneg_left habs (norm_nonneg _)
            _ = ‖f (pk.1 ^ pk.2)‖ := mul_one _
  have hcross_bound : |2 * (star A₁ * R₁).re| ≤ 2 * (N : ℝ) * Bsq := by
    have hre_le : |(star A₁ * R₁).re| ≤ ‖A₁‖ * ‖R₁‖ := by
      calc |(star A₁ * R₁).re| ≤ ‖star A₁ * R₁‖ := Complex.abs_re_le_norm _
        _ = ‖A₁‖ * ‖R₁‖ := by rw [norm_mul, norm_star]
    have hprod_le : ‖A₁‖ * ‖R₁‖ ≤ (N : ℝ) * Bsq := by
      have hR1_sq : ‖R₁‖ ^ 2 ≤ (N : ℝ) * Bsq :=
        (pow_le_pow_left₀ (norm_nonneg _) hR1_norm 2).trans hsum_norm_sq
      have hsq : (‖A₁‖ * ‖R₁‖) ^ 2 ≤ ((N : ℝ) * Bsq) ^ 2 := by
        rw [mul_pow, sq ((N : ℝ) * Bsq)]
        exact mul_le_mul hA₁_sq hR1_sq (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg N) hBsq_nonneg)
      have h1 := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
        Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg N) hBsq_nonneg)] at h1
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  -- Expand `∑ n, ‖f₁ n‖^2 - N * ‖A₁‖^2` into diagonal + distinct-prime off-diagonal - same-prime square
  have hL2_C : (∑ n ∈ Finset.Icc 1 N, ((‖f₁ n‖ ^ 2 : ℝ) : ℂ)) =
      ∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
        f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
          (((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
            exactPowDvd pk₂.1 pk₂.2 n)).card : ℂ) := by
    have hpt : ∀ n ∈ Finset.Icc 1 N, ((‖f₁ n‖ ^ 2 : ℝ) : ℂ) =
        ∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
          if exactPowDvd pk₁.1 pk₁.2 n ∧ exactPowDvd pk₂.1 pk₂.2 n then
            f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2))
          else 0 := by
      intro n _
      push_cast
      rw [← Complex.mul_conj']
      dsimp [f₁]
      rw [map_sum, Finset.sum_mul_sum]
      simp_rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun pk₁ _ => ?_
      by_cases h1 : exactPowDvd pk₁.1 pk₁.2 n
      · simp only [h1, true_and, ↓reduceIte]
      · simp [h1]
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun pk₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun pk₂ _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hA1_C : (N : ℂ) * ((‖A₁‖ ^ 2 : ℝ) : ℂ) =
      ∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
        f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
          (((N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂ : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.mul_conj']
    dsimp [A₁]
    rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun pk₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun pk₂ _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    ring
  -- Subtract and split into `pk₁.1 = pk₂.1` vs `pk₁.1 ≠ pk₂.1`
  have hdiff_bound : (∑ n ∈ Finset.Icc 1 N, ‖f₁ n‖ ^ 2) - (N : ℝ) * ‖A₁‖ ^ 2 ≤
      3 * (N : ℝ) * Bsq := by
    have hdiff_C : (∑ n ∈ Finset.Icc 1 N, ((‖f₁ n‖ ^ 2 : ℝ) : ℂ)) - (N : ℂ) * ((‖A₁‖ ^ 2 : ℝ) : ℂ) =
        (∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
          if pk₁.1 = pk₂.1 then
            f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
              (((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                exactPowDvd pk₂.1 pk₂.2 n)).card : ℂ) -
            f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
              (((N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂ : ℝ) : ℂ)
          else 0) +
        (∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
          if pk₁.1 ≠ pk₂.1 then
            f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
              ((((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                exactPowDvd pk₂.1 pk₂.2 n)).card : ℝ) -
                (N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂ : ℂ)
          else 0) := by
      rw [hL2_C, hA1_C, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun pk₁ _ => ?_
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun pk₂ _ => ?_
      by_cases h : pk₁.1 = pk₂.1
      · simp [h]
      · simp [h]
        ring
    -- Same-prime part: diagonal is `≤ N * Bsq`, minus `- N * ∑_p ‖∑_k f(p^k) c_{p,k}‖^2 ≤ 0`
    have hsame_re : (∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
          if pk₁.1 = pk₂.1 then
            f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
              (((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                exactPowDvd pk₂.1 pk₂.2 n)).card : ℂ) -
            f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
              (((N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂ : ℝ) : ℂ)
          else 0).re ≤ (N : ℝ) * Bsq := by
      -- First piece (actual counts): vanishes unless `pk₁ = pk₂`!
      have hactual : (∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
            if pk₁.1 = pk₂.1 then
              f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
                (((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                  exactPowDvd pk₂.1 pk₂.2 n)).card : ℂ)
            else 0).re ≤ (N : ℝ) * Bsq := by
        have hdiag : ∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
              (if pk₁.1 = pk₂.1 then
                f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
                  (((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                    exactPowDvd pk₂.1 pk₂.2 n)).card : ℂ)
              else 0) =
            ∑ pk ∈ S₁, ((‖f (pk.1 ^ pk.2)‖ ^ 2 *
              (((Finset.Icc 1 N).filter (exactPowDvd pk.1 pk.2)).card : ℝ) : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun pk₁ hpk₁ => ?_
          have hinner : ∀ pk₂ ∈ S₁,
              (if pk₁.1 = pk₂.1 then
                f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
                  (((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                    exactPowDvd pk₂.1 pk₂.2 n)).card : ℂ)
              else 0) =
              if pk₂ = pk₁ then
                ((‖f (pk₁.1 ^ pk₁.2)‖ ^ 2 *
                  (((Finset.Icc 1 N).filter (exactPowDvd pk₁.1 pk₁.2)).card : ℝ) : ℝ) : ℂ)
              else 0 := by
            intro pk₂ hpk₂
            by_cases heq : pk₂ = pk₁
            · subst heq
              simp only [↓reduceIte, and_self]
              have hmc : f (pk₂.1 ^ pk₂.2) * star (f (pk₂.1 ^ pk₂.2)) =
                  ((‖f (pk₂.1 ^ pk₂.2)‖ ^ 2 : ℝ) : ℂ) := by
                push_cast; exact Complex.mul_conj' _
              rw [hmc]
              push_cast; rfl
            · simp only [heq, ↓reduceIte]
              split_ifs with hp_eq
              · -- Same prime, different exponents ⇒ filter is empty!
                have hemp : (Finset.Icc 1 N).filter
                    (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧ exactPowDvd pk₂.1 pk₂.2 n) = ∅ := by
                  ext n
                  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]
                  rintro ⟨hn, he1, he2⟩
                  have hm1 := mem_primePowers.mp (Finset.mem_filter.mp hpk₁).1
                  have hm2 := mem_primePowers.mp (Finset.mem_filter.mp hpk₂).1
                  have hn0 : n ≠ 0 := by omega
                  have hf1 := (exactPowDvd_iff_factorization hm1.1 hm1.2.1 hn0).mp he1
                  have hf2 := (exactPowDvd_iff_factorization hm2.1 hm2.2.1 hn0).mp he2
                  rw [hp_eq] at hf1
                  exact heq (Prod.ext hp_eq.symm (hf2.2.symm.trans hf1.2))
                simp [hemp]
              · rfl
          rw [Finset.sum_congr rfl hinner]
          simp [hpk₁]
        rw [hdiag, ← Complex.ofReal_sum, Complex.ofReal_re]
        calc ∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖ ^ 2 *
              (((Finset.Icc 1 N).filter (exactPowDvd pk.1 pk.2)).card : ℝ)
            ≤ ∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖ ^ 2 * ((N : ℝ) / ((pk.1 : ℝ) ^ pk.2)) := by
              refine Finset.sum_le_sum fun pk hpk => ?_
              refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
              have hm := mem_primePowers.mp (Finset.mem_filter.mp hpk).1
              rw [card_exactPowDvd pk.1 pk.2 N hm.1]
              have hle1 : ((N / pk.1 ^ pk.2 - N / pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) ≤
                  ((N / pk.1 ^ pk.2 : ℕ) : ℝ) := by
                exact_mod_cast Nat.sub_le _ _
              have hle2 : ((N / pk.1 ^ pk.2 : ℕ) : ℝ) ≤ (N : ℝ) / ((pk.1 : ℝ) ^ pk.2) := by
                have h := (abs_div_sub_real_div_le N (pk.1 ^ pk.2)
                  (Nat.one_le_pow pk.2 pk.1 hm.1.pos)).1
                push_cast at h
                linarith
              exact hle1.trans hle2
          _ = (N : ℝ) * ∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖ ^ 2 / ((pk.1 : ℝ) ^ pk.2) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun pk _ => by ring
          _ ≤ (N : ℝ) * Bsq := mul_le_mul_of_nonneg_left hB₁_le (Nat.cast_nonneg N)
      -- Second piece (same-prime density square): `≥ 0`!
      have hdens_sq_nonneg : 0 ≤ (∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
            if pk₁.1 = pk₂.1 then
              f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
                (((N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂ : ℝ) : ℂ)
            else 0).re := by
        have hgroup : (∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
              if pk₁.1 = pk₂.1 then
                f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
                  (((N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂ : ℝ) : ℂ)
              else 0) =
            ((N : ℝ) * ∑ p ∈ S₁.image Prod.fst,
              ‖∑ pk ∈ S₁.filter (fun pk => pk.1 = p),
                f (pk.1 ^ pk.2) * (tkExactDensity pk : ℂ)‖ ^ 2 : ℂ) := by
          have hfiber : ∀ p ∈ S₁.image Prod.fst,
              ((‖∑ pk ∈ S₁.filter (fun pk => pk.1 = p),
                f (pk.1 ^ pk.2) * (tkExactDensity pk : ℂ)‖ ^ 2 : ℝ) : ℂ) =
              ∑ pk₁ ∈ S₁.filter (fun pk => pk.1 = p), ∑ pk₂ ∈ S₁.filter (fun pk => pk.1 = p),
                f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
                  ((tkExactDensity pk₁ * tkExactDensity pk₂ : ℝ) : ℂ) := by
            intro p _
            push_cast
            rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun pk₁ _ => Finset.sum_congr rfl fun pk₂ _ => ?_
            rw [map_mul, Complex.conj_ofReal]
            change f (pk₁.1 ^ pk₁.2) * (tkExactDensity pk₁ : ℂ) *
                (star (f (pk₂.1 ^ pk₂.2)) * (tkExactDensity pk₂ : ℂ)) =
              f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
                ((tkExactDensity pk₁ : ℂ) * (tkExactDensity pk₂ : ℂ))
            ring
          rw [Complex.ofReal_sum, Finset.mul_sum]
          have hrhs : ∑ p ∈ S₁.image Prod.fst,
                ((N : ℝ) : ℂ) * ((‖∑ pk ∈ S₁.filter (fun pk => pk.1 = p),
                  f (pk.1 ^ pk.2) * (tkExactDensity pk : ℂ)‖ ^ 2 : ℝ) : ℂ) =
              ∑ p ∈ S₁.image Prod.fst,
                ((N : ℝ) : ℂ) * ∑ pk₁ ∈ S₁.filter (fun pk => pk.1 = p),
                  ∑ pk₂ ∈ S₁.filter (fun pk => pk.1 = p),
                    f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
                      ((tkExactDensity pk₁ * tkExactDensity pk₂ : ℝ) : ℂ) :=
            Finset.sum_congr rfl fun p hp => by rw [hfiber p hp]
          rw [hrhs]
          rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := S₁.image Prod.fst)
            (fun pk hpk => Finset.mem_image_of_mem _ hpk)]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun pk₁ hpk₁ => ?_
          have hp1 : pk₁.1 = p := (Finset.mem_filter.mp hpk₁).2
          rw [Finset.mul_sum, Finset.sum_filter (s := S₁) (p := fun pk => pk.1 = p)]
          refine Finset.sum_congr rfl fun pk₂ _ => ?_
          by_cases h2 : pk₂.1 = p
          · have h12 : pk₁.1 = pk₂.1 := hp1.trans h2.symm
            simp only [h12, h2, ↓reduceIte]
            push_cast
            ring
          · have h12 : pk₁.1 ≠ pk₂.1 := fun h => h2 (h.symm.trans hp1)
            simp only [h12, h2, ↓reduceIte]
        rw [hgroup, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.ofReal_im, mul_zero, sub_zero]
        exact mul_nonneg (Nat.cast_nonneg N) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      have hsplit_same : (∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
            if pk₁.1 = pk₂.1 then
              f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
                (((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                  exactPowDvd pk₂.1 pk₂.2 n)).card : ℂ) -
              f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
                (((N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂ : ℝ) : ℂ)
            else 0) =
          (∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
            if pk₁.1 = pk₂.1 then
              f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
                (((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                  exactPowDvd pk₂.1 pk₂.2 n)).card : ℂ)
            else 0) -
          (∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
            if pk₁.1 = pk₂.1 then
              f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
                (((N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂ : ℝ) : ℂ)
            else 0) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun pk₁ _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun pk₂ _ => ?_
        split_ifs <;> ring
      rw [hsplit_same, Complex.sub_re]
      linarith
    -- Distinct-prime off-diagonal part: `≤ 2 * (∑_{pk ∈ S₁} ‖f(p^k)‖)^2 ≤ 2 * N * Bsq`
    have hoff_re : (∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
          if pk₁.1 ≠ pk₂.1 then
            f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
              ((((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                exactPowDvd pk₂.1 pk₂.2 n)).card : ℝ) -
                (N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂ : ℂ)
          else 0).re ≤ 2 * (N : ℝ) * Bsq := by
      calc (∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
              if pk₁.1 ≠ pk₂.1 then
                f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
                  ((((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                    exactPowDvd pk₂.1 pk₂.2 n)).card : ℝ) -
                    (N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂ : ℂ)
              else 0).re
          ≤ ‖∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
              if pk₁.1 ≠ pk₂.1 then
                f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
                  ((((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                    exactPowDvd pk₂.1 pk₂.2 n)).card : ℝ) -
                    (N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂ : ℂ)
              else 0‖ := Complex.re_le_norm _
        _ ≤ ∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁,
              ‖if pk₁.1 ≠ pk₂.1 then
                f (pk₁.1 ^ pk₁.2) * star (f (pk₂.1 ^ pk₂.2)) *
                  ((((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                    exactPowDvd pk₂.1 pk₂.2 n)).card : ℝ) -
                    (N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂ : ℂ)
              else 0‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
        _ ≤ ∑ pk₁ ∈ S₁, ∑ pk₂ ∈ S₁, 2 * (‖f (pk₁.1 ^ pk₁.2)‖ * ‖f (pk₂.1 ^ pk₂.2)‖) := by
            refine Finset.sum_le_sum fun pk₁ hpk₁ => Finset.sum_le_sum fun pk₂ hpk₂ => ?_
            by_cases hne : pk₁.1 ≠ pk₂.1
            · rw [if_pos hne, norm_mul, norm_mul, norm_star]
              have hm1 := mem_primePowers.mp (Finset.mem_filter.mp hpk₁).1
              have hm2 := mem_primePowers.mp (Finset.mem_filter.mp hpk₂).1
              have habs := card_exactPowDvd_pair_sub pk₁.1 pk₁.2 pk₂.1 pk₂.2 N hm1.1 hm2.1 hne
              rw [show ‖((((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                    exactPowDvd pk₂.1 pk₂.2 n)).card : ℝ) -
                    (N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂ : ℂ)‖ =
                  |(((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                    exactPowDvd pk₂.1 pk₂.2 n)).card : ℝ) -
                    (N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂| by
                have hc : ((((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                    exactPowDvd pk₂.1 pk₂.2 n)).card : ℝ) -
                    (N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂ : ℂ) =
                    (((((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                    exactPowDvd pk₂.1 pk₂.2 n)).card : ℝ) -
                    (N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂ : ℝ) : ℂ) := by push_cast; rfl
                rw [hc, Complex.norm_real, Real.norm_eq_abs]]
              calc ‖f (pk₁.1 ^ pk₁.2)‖ * ‖f (pk₂.1 ^ pk₂.2)‖ *
                    |(((Finset.Icc 1 N).filter (fun n => exactPowDvd pk₁.1 pk₁.2 n ∧
                      exactPowDvd pk₂.1 pk₂.2 n)).card : ℝ) -
                      (N : ℝ) * tkExactDensity pk₁ * tkExactDensity pk₂|
                  ≤ ‖f (pk₁.1 ^ pk₁.2)‖ * ‖f (pk₂.1 ^ pk₂.2)‖ * 2 :=
                    mul_le_mul_of_nonneg_left habs (mul_nonneg (norm_nonneg _) (norm_nonneg _))
                _ = 2 * (‖f (pk₁.1 ^ pk₁.2)‖ * ‖f (pk₂.1 ^ pk₂.2)‖) := by ring
            · simp only [hne, ↓reduceIte, norm_zero]
              positivity
        _ = 2 * (∑ pk ∈ S₁, ‖f (pk.1 ^ pk.2)‖) ^ 2 := by
            rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun pk₁ _ => (Finset.mul_sum _ _ _).symm
        _ ≤ 2 * ((N : ℝ) * Bsq) := mul_le_mul_of_nonneg_left hsum_norm_sq (by norm_num)
        _ = 2 * (N : ℝ) * Bsq := by ring
    have hre_diff := congr_arg Complex.re hdiff_C
    simp only [Complex.sub_re, Complex.add_re, ← Complex.ofReal_sum, Complex.ofReal_re,
      Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_im,
      mul_zero, sub_zero] at hre_diff
    linarith
  -- Assemble `hexpand` + `hsum_f1` + `hdiff_bound` + `hcross_bound`
  have hre_f1 : (star A₁ * ∑ n ∈ Finset.Icc 1 N, f₁ n).re =
      (N : ℝ) * ‖A₁‖ ^ 2 + (star A₁ * R₁).re := by
    rw [hsum_f1, mul_add, Complex.add_re]
    have h1 : (star A₁ * ((N : ℂ) * A₁)).re = (N : ℝ) * ‖A₁‖ ^ 2 := by
      have hmc : star A₁ * ((N : ℂ) * A₁) = (((N : ℝ) * ‖A₁‖ ^ 2 : ℝ) : ℂ) := by
        have h : A₁ * star A₁ = (‖A₁‖ : ℂ) ^ 2 := Complex.mul_conj' A₁
        push_cast
        linear_combination (N : ℂ) * h
      rw [hmc, Complex.ofReal_re]
    rw [h1]
  rw [hexpand, hre_f1]
  have habs_le := abs_le.mp hcross_bound
  linarith

lemma tk_piece2_bound (f : ℕ → ℂ) (N : ℕ) :
    let S₂ := (primePowers N).filter (fun pk => N < (pk.1 ^ pk.2) ^ 2)
    let f₂ : ℕ → ℂ := fun n =>
      ∑ pk ∈ S₂.filter (fun pk => exactPowDvd pk.1 pk.2 n), f (pk.1 ^ pk.2)
    let A₂ : ℂ := ∑ pk ∈ S₂, f (pk.1 ^ pk.2) * (tkExactDensity pk : ℂ)
    ∑ n ∈ Finset.Icc 1 N, ‖f₂ n - A₂‖ ^ 2 ≤ 12 * (N : ℝ) * tkVarSq f N := by
  intro S₂ f₂ A₂
  set Bsq : ℝ := tkVarSq f N
  have hBsq_nonneg : 0 ≤ Bsq := tkVarSq_nonneg f N
  -- For each `n ∈ Icc 1 N`, at most one `pk ∈ S₂` has `exactPowDvd pk.1 pk.2 n`!
  have hf2_card_le1 : ∀ n ∈ Finset.Icc 1 N,
      (S₂.filter (fun pk => exactPowDvd pk.1 pk.2 n)).card ≤ 1 := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [Finset.card_le_one]
    rintro ⟨p₁, k₁⟩ h1 ⟨p₂, k₂⟩ h2
    simp only [S₂, Finset.mem_filter, mem_primePowers] at h1 h2
    by_cases hp_eq : p₁ = p₂
    · have hf1 := (exactPowDvd_iff_factorization h1.1.1.1 h1.1.1.2.1 (by omega)).mp h1.2
      have hf2 := (exactPowDvd_iff_factorization h2.1.1.1 h2.1.1.2.1 (by omega)).mp h2.2
      rw [hp_eq] at hf1
      exact Prod.ext hp_eq (hf1.2.symm.trans hf2.2)
    · exfalso
      have hcop : Nat.Coprime (p₁ ^ k₁) (p₂ ^ k₂) :=
        ((Nat.coprime_primes h1.1.1.1 h2.1.1.1).mpr hp_eq).pow _ _
      have hmul_dvd : p₁ ^ k₁ * p₂ ^ k₂ ∣ n :=
        hcop.mul_dvd_of_dvd_of_dvd h1.2.1 h2.2.1
      have hmul_le : p₁ ^ k₁ * p₂ ^ k₂ ≤ N :=
        (Nat.le_of_dvd (by omega) hmul_dvd).trans hn.2
      have hsq_le : (p₁ ^ k₁ * p₂ ^ k₂) ^ 2 ≤ N ^ 2 :=
        Nat.pow_le_pow_left hmul_le 2
      have hgt : N * N < (p₁ ^ k₁) ^ 2 * (p₂ ^ k₂) ^ 2 :=
        Nat.mul_lt_mul'' h1.1.2 h2.1.2
      rw [← mul_pow, ← sq] at hgt
      omega
  have hf2_L2 : ∑ n ∈ Finset.Icc 1 N, ‖f₂ n‖ ^ 2 ≤ (N : ℝ) * Bsq := by
    have hpt : ∀ n ∈ Finset.Icc 1 N,
        ‖f₂ n‖ ^ 2 = ∑ pk ∈ S₂.filter (fun pk => exactPowDvd pk.1 pk.2 n),
          ‖f (pk.1 ^ pk.2)‖ ^ 2 := by
      intro n hn
      have hc := hf2_card_le1 n hn
      rcases Finset.card_le_one_iff_subset_singleton.mp hc with ⟨pk0, hsub⟩
      by_cases hmem : pk0 ∈ S₂.filter (fun pk => exactPowDvd pk.1 pk.2 n)
      · have heq : S₂.filter (fun pk => exactPowDvd pk.1 pk.2 n) = {pk0} :=
          Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hmem)
        simp [f₂, heq]
      · have hemp : S₂.filter (fun pk => exactPowDvd pk.1 pk.2 n) = ∅ := by
          ext x
          simp only [Finset.notMem_empty, iff_false]
          intro hx
          exact hmem (Finset.mem_singleton.mp (hsub hx) ▸ hx)
        simp [f₂, hemp]
    rw [Finset.sum_congr rfl hpt]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    calc (∑ pk ∈ S₂, ∑ n ∈ Finset.Icc 1 N,
            if exactPowDvd pk.1 pk.2 n then ‖f (pk.1 ^ pk.2)‖ ^ 2 else 0)
        = ∑ pk ∈ S₂, (((Finset.Icc 1 N).filter (exactPowDvd pk.1 pk.2)).card : ℝ) *
            ‖f (pk.1 ^ pk.2)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun pk _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ pk ∈ S₂, ((N : ℝ) / ((pk.1 : ℝ) ^ pk.2)) * ‖f (pk.1 ^ pk.2)‖ ^ 2 := by
          refine Finset.sum_le_sum fun pk hpk => ?_
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have hm := mem_primePowers.mp (Finset.mem_filter.mp hpk).1
          rw [card_exactPowDvd pk.1 pk.2 N hm.1]
          have h1 : ((N / pk.1 ^ pk.2 - N / pk.1 ^ (pk.2 + 1) : ℕ) : ℝ) ≤
              ((N / pk.1 ^ pk.2 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
          have h2 : ((N / pk.1 ^ pk.2 : ℕ) : ℝ) ≤ (N : ℝ) / ((pk.1 : ℝ) ^ pk.2) := by
            have h := (abs_div_sub_real_div_le N (pk.1 ^ pk.2)
              (Nat.one_le_pow pk.2 pk.1 hm.1.pos)).1
            push_cast at h
            linarith
          exact h1.trans h2
      _ = (N : ℝ) * ∑ pk ∈ S₂, ‖f (pk.1 ^ pk.2)‖ ^ 2 / ((pk.1 : ℝ) ^ pk.2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ (N : ℝ) * Bsq :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun _ _ _ => div_nonneg (sq_nonneg _) (by positivity))
            (Nat.cast_nonneg N)
  have hA2_sq : ‖A₂‖ ^ 2 ≤ 5 * Bsq := by
    have hA2_le : ‖A₂‖ ≤ ∑ pk ∈ S₂, ‖f (pk.1 ^ pk.2)‖ / ((pk.1 : ℝ) ^ pk.2) := by
      calc ‖A₂‖ ≤ ∑ pk ∈ S₂, ‖f (pk.1 ^ pk.2) * (tkExactDensity pk : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ pk ∈ S₂, ‖f (pk.1 ^ pk.2)‖ / ((pk.1 : ℝ) ^ pk.2) := by
            refine Finset.sum_le_sum fun pk hpk => ?_
            have hm := mem_primePowers.mp (Finset.mem_filter.mp hpk).1
            have hp_gt1 : (1 : ℝ) < (pk.1 : ℝ) := by exact_mod_cast hm.1.one_lt
            have h01 : 0 ≤ 1 - (pk.1 : ℝ)⁻¹ ∧ 1 - (pk.1 : ℝ)⁻¹ ≤ 1 :=
              ⟨by linarith [inv_lt_one_of_one_lt₀ hp_gt1],
                by linarith [inv_pos.mpr (by linarith : (0 : ℝ) < (pk.1 : ℝ))]⟩
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            unfold tkExactDensity
            rw [abs_of_nonneg (mul_nonneg (by positivity) h01.1), div_eq_mul_inv]
            calc ‖f (pk.1 ^ pk.2)‖ * (((pk.1 : ℝ) ^ pk.2)⁻¹ * (1 - (pk.1 : ℝ)⁻¹))
                ≤ ‖f (pk.1 ^ pk.2)‖ * (((pk.1 : ℝ) ^ pk.2)⁻¹ * 1) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h01.2 (by positivity)) (norm_nonneg _)
              _ = ‖f (pk.1 ^ pk.2)‖ * ((pk.1 : ℝ) ^ pk.2)⁻¹ := by ring
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S₂
      (fun pk => 1 / Real.sqrt ((pk.1 : ℝ) ^ pk.2))
      (fun pk => ‖f (pk.1 ^ pk.2)‖ / Real.sqrt ((pk.1 : ℝ) ^ pk.2))
    have hlhs : ∑ pk ∈ S₂, (1 / Real.sqrt ((pk.1 : ℝ) ^ pk.2)) *
        (‖f (pk.1 ^ pk.2)‖ / Real.sqrt ((pk.1 : ℝ) ^ pk.2)) =
        ∑ pk ∈ S₂, ‖f (pk.1 ^ pk.2)‖ / ((pk.1 : ℝ) ^ pk.2) := by
      refine Finset.sum_congr rfl fun pk _ => ?_
      rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by positivity)]
    have hr1 : ∑ pk ∈ S₂, (1 / Real.sqrt ((pk.1 : ℝ) ^ pk.2)) ^ 2 =
        ∑ pk ∈ S₂, ((pk.1 : ℝ) ^ pk.2)⁻¹ := by
      refine Finset.sum_congr rfl fun pk _ => ?_
      rw [div_pow, one_pow, Real.sq_sqrt (by positivity), one_div]
    have hr2 : ∑ pk ∈ S₂, (‖f (pk.1 ^ pk.2)‖ / Real.sqrt ((pk.1 : ℝ) ^ pk.2)) ^ 2 =
        ∑ pk ∈ S₂, ‖f (pk.1 ^ pk.2)‖ ^ 2 / ((pk.1 : ℝ) ^ pk.2) := by
      refine Finset.sum_congr rfl fun pk _ => ?_
      rw [div_pow, Real.sq_sqrt (by positivity)]
    rw [hlhs, hr1, hr2] at hcs
    have hB2_le : ∑ pk ∈ S₂, ‖f (pk.1 ^ pk.2)‖ ^ 2 / ((pk.1 : ℝ) ^ pk.2) ≤ Bsq :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ => div_nonneg (sq_nonneg _) (by positivity)
    calc ‖A₂‖ ^ 2 ≤ (∑ pk ∈ S₂, ‖f (pk.1 ^ pk.2)‖ / ((pk.1 : ℝ) ^ pk.2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hA2_le 2
      _ ≤ (∑ pk ∈ S₂, ((pk.1 : ℝ) ^ pk.2)⁻¹) *
            (∑ pk ∈ S₂, ‖f (pk.1 ^ pk.2)‖ ^ 2 / ((pk.1 : ℝ) ^ pk.2)) := hcs
      _ ≤ 5 * Bsq := mul_le_mul (sum_inv_large_primePowers_le N) hB2_le
            (Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (by positivity))
            (by norm_num)
  calc ∑ n ∈ Finset.Icc 1 N, ‖f₂ n - A₂‖ ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 N, (2 * ‖f₂ n‖ ^ 2 + 2 * ‖A₂‖ ^ 2) := by
        refine Finset.sum_le_sum fun n _ => ?_
        have htri : ‖f₂ n - A₂‖ ≤ ‖f₂ n‖ + ‖A₂‖ := norm_sub_le _ _
        have hsq : ‖f₂ n - A₂‖ ^ 2 ≤ (‖f₂ n‖ + ‖A₂‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖f₂ n‖ - ‖A₂‖)]
    _ = 2 * (∑ n ∈ Finset.Icc 1 N, ‖f₂ n‖ ^ 2) + 2 * (N : ℝ) * ‖A₂‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc]
        simp
        ring
    _ ≤ 2 * ((N : ℝ) * Bsq) + 2 * (N : ℝ) * (5 * Bsq) := by
        have h1 : 2 * (∑ n ∈ Finset.Icc 1 N, ‖f₂ n‖ ^ 2) ≤ 2 * ((N : ℝ) * Bsq) :=
          mul_le_mul_of_nonneg_left hf2_L2 (by norm_num)
        have h2 : 2 * (N : ℝ) * ‖A₂‖ ^ 2 ≤ 2 * (N : ℝ) * (5 * Bsq) :=
          mul_le_mul_of_nonneg_left hA2_sq (by positivity)
        linarith
    _ = 12 * (N : ℝ) * Bsq := by ring

/-- **Turán–Kubilius Inequality (General Additive Functions, Exact Mean)**:
For every additive function `f : ℕ → ℂ` and every `N : ℕ`,
`∑_{n=1}^N ‖f(n) - A(N)‖^2 ≤ 34 * N * B(N)^2`. -/
theorem turan_kubilius_additive {f : ℕ → ℂ} (hf : IsAdditive f) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖f n - tkMean f N‖ ^ 2 ≤
      34 * (N : ℝ) * (tkVar f N) ^ 2 := by
  rw [tkVar_sq]
  set S₁ := (primePowers N).filter (fun pk => (pk.1 ^ pk.2) ^ 2 ≤ N)
  set S₂ := (primePowers N).filter (fun pk => N < (pk.1 ^ pk.2) ^ 2)
  set f₁ : ℕ → ℂ := fun n =>
    ∑ pk ∈ S₁.filter (fun pk => exactPowDvd pk.1 pk.2 n), f (pk.1 ^ pk.2)
  set f₂ : ℕ → ℂ := fun n =>
    ∑ pk ∈ S₂.filter (fun pk => exactPowDvd pk.1 pk.2 n), f (pk.1 ^ pk.2)
  set A₁ : ℂ := ∑ pk ∈ S₁, f (pk.1 ^ pk.2) * (tkExactDensity pk : ℂ)
  set A₂ : ℂ := ∑ pk ∈ S₂, f (pk.1 ^ pk.2) * (tkExactDensity pk : ℂ)
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro pk h1 h2
    simp only [S₁, S₂, Finset.mem_filter] at h1 h2
    omega
  have hunion : S₁ ∪ S₂ = primePowers N := by
    ext pk
    simp only [S₁, S₂, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hle : (pk.1 ^ pk.2) ^ 2 ≤ N
      · left; exact ⟨h, hle⟩
      · right; exact ⟨h, by omega⟩
  have hA_eq : tkMean f N = A₁ + A₂ := by
    unfold tkMean
    rw [← hunion, Finset.sum_union hdisj]
  have hf_eq : ∀ n ∈ Finset.Icc 1 N, f n = f₁ n + f₂ n := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [additive_eq_sum_primePowers hf hn.1 hn.2]
    have hfilt_union : (primePowers N).filter (fun pk => exactPowDvd pk.1 pk.2 n) =
        S₁.filter (fun pk => exactPowDvd pk.1 pk.2 n) ∪
        S₂.filter (fun pk => exactPowDvd pk.1 pk.2 n) := by
      rw [← Finset.filter_union, hunion]
    have hfilt_disj : Disjoint (S₁.filter (fun pk => exactPowDvd pk.1 pk.2 n))
        (S₂.filter (fun pk => exactPowDvd pk.1 pk.2 n)) :=
      hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [hfilt_union, Finset.sum_union hfilt_disj]
  have h1 := tk_piece1_bound f N
  have h2 := tk_piece2_bound f N
  calc ∑ n ∈ Finset.Icc 1 N, ‖f n - tkMean f N‖ ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 N, (2 * ‖f₁ n - A₁‖ ^ 2 + 2 * ‖f₂ n - A₂‖ ^ 2) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [hf_eq n hn, hA_eq, show f₁ n + f₂ n - (A₁ + A₂) = (f₁ n - A₁) + (f₂ n - A₂) by ring]
        have htri : ‖(f₁ n - A₁) + (f₂ n - A₂)‖ ≤ ‖f₁ n - A₁‖ + ‖f₂ n - A₂‖ := norm_add_le _ _
        have hsq : ‖(f₁ n - A₁) + (f₂ n - A₂)‖ ^ 2 ≤ (‖f₁ n - A₁‖ + ‖f₂ n - A₂‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖f₁ n - A₁‖ - ‖f₂ n - A₂‖)]
    _ = 2 * (∑ n ∈ Finset.Icc 1 N, ‖f₁ n - A₁‖ ^ 2) +
        2 * (∑ n ∈ Finset.Icc 1 N, ‖f₂ n - A₂‖ ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (5 * (N : ℝ) * tkVarSq f N) + 2 * (12 * (N : ℝ) * tkVarSq f N) := by linarith
    _ = 34 * (N : ℝ) * tkVarSq f N := by ring

/-- **Turán–Kubilius Inequality (General Additive Functions, Simplified Mean `Ã(N) = ∑_{p^k ≤ N} f(p^k)/p^k`)**:
`∑_{n=1}^N ‖f(n) - Ã(N)‖^2 ≤ 70 * N * B(N)^2`. -/
theorem turan_kubilius_additive_simple {f : ℕ → ℂ} (hf : IsAdditive f) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖f n - tkMeanSimple f N‖ ^ 2 ≤
      70 * (N : ℝ) * (tkVar f N) ^ 2 := by
  have hmain := turan_kubilius_additive hf N
  rw [tkVar_sq] at hmain ⊢
  have hdiff_sq : ‖tkMean f N - tkMeanSimple f N‖ ^ 2 ≤ tkVarSq f N := by
    have hdiff_eq : tkMean f N - tkMeanSimple f N =
        -∑ pk ∈ primePowers N, f (pk.1 ^ pk.2) * (((pk.1 : ℝ) ^ (pk.2 + 1))⁻¹ : ℂ) := by
      unfold tkMean tkMeanSimple tkExactDensity
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun pk _ => ?_
      push_cast
      rw [pow_succ, mul_inv]
      ring
    have hnorm_le : ‖tkMean f N - tkMeanSimple f N‖ ≤
        ∑ pk ∈ primePowers N, ‖f (pk.1 ^ pk.2)‖ / ((pk.1 : ℝ) ^ (pk.2 + 1)) := by
      rw [hdiff_eq, norm_neg]
      calc ‖∑ pk ∈ primePowers N, f (pk.1 ^ pk.2) * (((pk.1 : ℝ) ^ (pk.2 + 1))⁻¹ : ℂ)‖
          ≤ ∑ pk ∈ primePowers N, ‖f (pk.1 ^ pk.2) * (((pk.1 : ℝ) ^ (pk.2 + 1))⁻¹ : ℂ)‖ :=
            norm_sum_le _ _
        _ = ∑ pk ∈ primePowers N, ‖f (pk.1 ^ pk.2)‖ / ((pk.1 : ℝ) ^ (pk.2 + 1)) := by
            refine Finset.sum_congr rfl fun pk _ => ?_
            rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Nat.cast_nonneg _), div_eq_mul_inv]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (primePowers N)
      (fun pk => 1 / ((pk.1 : ℝ) * Real.sqrt ((pk.1 : ℝ) ^ pk.2)))
      (fun pk => ‖f (pk.1 ^ pk.2)‖ / Real.sqrt ((pk.1 : ℝ) ^ pk.2))
    have hlhs : ∑ pk ∈ primePowers N,
        (1 / ((pk.1 : ℝ) * Real.sqrt ((pk.1 : ℝ) ^ pk.2))) *
          (‖f (pk.1 ^ pk.2)‖ / Real.sqrt ((pk.1 : ℝ) ^ pk.2)) =
        ∑ pk ∈ primePowers N, ‖f (pk.1 ^ pk.2)‖ / ((pk.1 : ℝ) ^ (pk.2 + 1)) := by
      refine Finset.sum_congr rfl fun pk _ => ?_
      rw [div_mul_div_comm, one_mul, mul_assoc, Real.mul_self_sqrt (by positivity), pow_succ']
    have hr1 : ∑ pk ∈ primePowers N,
        (1 / ((pk.1 : ℝ) * Real.sqrt ((pk.1 : ℝ) ^ pk.2))) ^ 2 =
        ∑ pk ∈ primePowers N, ((pk.1 : ℝ) ^ (pk.2 + 2))⁻¹ := by
      refine Finset.sum_congr rfl fun pk _ => ?_
      rw [div_pow, one_pow, mul_pow, Real.sq_sqrt (by positivity), one_div,
        show (pk.1 : ℝ) ^ (pk.2 + 2) = (pk.1 : ℝ) ^ 2 * (pk.1 : ℝ) ^ pk.2 by
          rw [pow_add]; ring]
    have hr2 : ∑ pk ∈ primePowers N, (‖f (pk.1 ^ pk.2)‖ / Real.sqrt ((pk.1 : ℝ) ^ pk.2)) ^ 2 =
        tkVarSq f N := by
      unfold tkVarSq
      refine Finset.sum_congr rfl fun pk _ => by rw [div_pow, Real.sq_sqrt (by positivity)]
    rw [hlhs, hr1, hr2] at hcs
    -- Bound `∑_{pk ∈ primePowers N} p^{-(k+2)} ≤ 1`
    have hinv_le1 : ∑ pk ∈ primePowers N, ((pk.1 : ℝ) ^ (pk.2 + 2))⁻¹ ≤ 1 := by
      have hreidx : ∑ pk ∈ primePowers N, ((pk.1 : ℝ) ^ (pk.2 + 2))⁻¹ ≤
          ∑ pk ∈ (primePowers (N ^ 3)).filter (fun pk => 2 ≤ pk.2), ((pk.1 : ℝ) ^ pk.2)⁻¹ := by
        set ψ : ℕ × ℕ → ℕ × ℕ := fun pk => (pk.1, pk.2 + 2)
        have hψ_inj : Set.InjOn ψ ↑(primePowers N) := by
          intro ⟨p₁, k₁⟩ _ ⟨p₂, k₂⟩ _ heq
          dsimp [ψ] at heq
          rcases Prod.mk.inj heq with ⟨hp, hk⟩
          exact Prod.ext hp (by omega)
        have hψ_sub : (primePowers N).image ψ ⊆
            (primePowers (N ^ 3)).filter (fun pk => 2 ≤ pk.2) := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨⟨p, k⟩, hpk, rfl⟩
          have hm := mem_primePowers.mp hpk
          have hp_le : p ≤ N := (Nat.le_self_pow (by omega : k ≠ 0) p).trans hm.2.2
          have hpk3 : p ^ (k + 2) ≤ N ^ 3 := by
            rw [pow_add]
            calc p ^ k * p ^ 2 ≤ N * N ^ 2 := Nat.mul_le_mul hm.2.2 (Nat.pow_le_pow_left hp_le 2)
              _ = N ^ 3 := by ring
          exact Finset.mem_filter.mpr ⟨mem_primePowers.mpr ⟨hm.1, by omega, hpk3⟩, by dsimp [ψ]; omega⟩
        calc ∑ pk ∈ primePowers N, ((pk.1 : ℝ) ^ (pk.2 + 2))⁻¹
            = ∑ pk ∈ (primePowers N).image ψ, ((pk.1 : ℝ) ^ pk.2)⁻¹ :=
              (Finset.sum_image (f := fun pk : ℕ × ℕ => ((pk.1 : ℝ) ^ pk.2)⁻¹) hψ_inj).symm
          _ ≤ ∑ pk ∈ (primePowers (N ^ 3)).filter (fun pk => 2 ≤ pk.2), ((pk.1 : ℝ) ^ pk.2)⁻¹ :=
              Finset.sum_le_sum_of_subset_of_nonneg hψ_sub fun _ _ _ => by positivity
      exact hreidx.trans (sum_inv_higher_primePowers_le (N ^ 3))
    calc ‖tkMean f N - tkMeanSimple f N‖ ^ 2
        ≤ (∑ pk ∈ primePowers N, ‖f (pk.1 ^ pk.2)‖ / ((pk.1 : ℝ) ^ (pk.2 + 1))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
      _ ≤ (∑ pk ∈ primePowers N, ((pk.1 : ℝ) ^ (pk.2 + 2))⁻¹) * tkVarSq f N := hcs
      _ ≤ 1 * tkVarSq f N := mul_le_mul_of_nonneg_right hinv_le1 (tkVarSq_nonneg f N)
      _ = tkVarSq f N := one_mul _
  calc ∑ n ∈ Finset.Icc 1 N, ‖f n - tkMeanSimple f N‖ ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 N,
          (2 * ‖f n - tkMean f N‖ ^ 2 + 2 * ‖tkMean f N - tkMeanSimple f N‖ ^ 2) := by
        refine Finset.sum_le_sum fun n _ => ?_
        have htri : ‖f n - tkMeanSimple f N‖ ≤
            ‖f n - tkMean f N‖ + ‖tkMean f N - tkMeanSimple f N‖ := by
          rw [show f n - tkMeanSimple f N =
            (f n - tkMean f N) + (tkMean f N - tkMeanSimple f N) by ring]
          exact norm_add_le _ _
        have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖f n - tkMean f N‖ - ‖tkMean f N - tkMeanSimple f N‖)]
    _ = 2 * (∑ n ∈ Finset.Icc 1 N, ‖f n - tkMean f N‖ ^ 2) +
        2 * (N : ℝ) * ‖tkMean f N - tkMeanSimple f N‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc]
        simp
        ring
    _ ≤ 2 * (34 * (N : ℝ) * tkVarSq f N) + 2 * (N : ℝ) * tkVarSq f N := by
        have h1 : 2 * (∑ n ∈ Finset.Icc 1 N, ‖f n - tkMean f N‖ ^ 2) ≤
            2 * (34 * (N : ℝ) * tkVarSq f N) := mul_le_mul_of_nonneg_left hmain (by norm_num)
        have h2 : 2 * (N : ℝ) * ‖tkMean f N - tkMeanSimple f N‖ ^ 2 ≤
            2 * (N : ℝ) * tkVarSq f N := mul_le_mul_of_nonneg_left hdiff_sq (by positivity)
        linarith
    _ = 70 * (N : ℝ) * tkVarSq f N := by ring

/-- **Turán–Kubilius Inequality (Strongly Additive Functions)**:
For every strongly additive function `f : ℕ → ℂ` and every `N : ℕ`,
`∑_{n=1}^N ‖f(n) - ∑_{p ≤ N} f(p)/p‖^2 ≤ 138 * N * ∑_{p ≤ N} ‖f(p)‖^2 / p`. -/
theorem turan_kubilius_strongly_additive {f : ℕ → ℂ} (hf : IsStronglyAdditive f) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖f n - tkStrongMean f N‖ ^ 2 ≤
      138 * (N : ℝ) * (tkStrongVar f N) ^ 2 := by
  rw [tkStrongVar_sq]
  have hmain := turan_kubilius_additive hf.1 N
  rw [tkVar_sq] at hmain
  set P := (Finset.Icc 1 N).filter Nat.Prime
  have hdisj : Set.PairwiseDisjoint (↑P : Set ℕ)
      (fun p => ((Finset.Icc 1 N).filter (fun k => p ^ k ≤ N)).image (p, ·)) := by
    intro p₁ _ p₂ _ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro x h1 h2
    rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨_, _, heq⟩
    exact hne (congr_arg Prod.fst heq).symm
  -- Step 1: `tkVarSq f N ≤ 2 * tkStrongVarSq f N`
  have hB_le : tkVarSq f N ≤ 2 * tkStrongVarSq f N := by
    unfold tkVarSq tkStrongVarSq primePowers
    rw [Finset.sum_biUnion hdisj, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp_prime := (Finset.mem_filter.mp hp).2
    rw [Finset.sum_image (fun _ _ _ _ h => congr_arg Prod.snd h)]
    have hsum_k : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => p ^ k ≤ N),
          ‖f (p ^ k)‖ ^ 2 / ((p : ℝ) ^ k) =
        ‖f p‖ ^ 2 * ∑ k ∈ (Finset.Icc 1 N).filter (fun k => p ^ k ≤ N), ((p : ℝ) ^ k)⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
      rw [hf.2 p k hp_prime hk1, div_eq_mul_inv]
    rw [hsum_k]
    have hgeom_le : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => p ^ k ≤ N), ((p : ℝ) ^ k)⁻¹ ≤
        2 / (p : ℝ) := by
      have h1 : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => p ^ k ≤ N), ((p : ℝ) ^ k)⁻¹ ≤
          ∑ k ∈ Finset.Icc 1 N, ((p : ℝ) ^ k)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
      have h2 := sum_inv_pow_Icc_le (D := N) hp_prime
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
      have h3 : ((p : ℝ) - 1)⁻¹ ≤ 2 / (p : ℝ) := by
        rw [← one_div, div_le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1) (by linarith)]
        linarith
      exact (h1.trans h2).trans h3
    calc ‖f p‖ ^ 2 * ∑ k ∈ (Finset.Icc 1 N).filter (fun k => p ^ k ≤ N), ((p : ℝ) ^ k)⁻¹
        ≤ ‖f p‖ ^ 2 * (2 / (p : ℝ)) := mul_le_mul_of_nonneg_left hgeom_le (sq_nonneg _)
      _ = 2 * (‖f p‖ ^ 2 / (p : ℝ)) := by ring
  -- Step 2: `‖tkMean f N - tkStrongMean f N‖^2 ≤ tkStrongVarSq f N` (by telescoping!)
  have hmean_diff_sq : ‖tkMean f N - tkStrongMean f N‖ ^ 2 ≤ tkStrongVarSq f N := by
    by_cases hN0 : N = 0
    · subst hN0
      have hemp1 : primePowers 0 = ∅ := by
        ext ⟨p, k⟩
        simp only [mem_primePowers, Finset.notMem_empty, iff_false, not_and]
        intro hp hk h0
        have := Nat.one_le_pow k p hp.pos
        omega
      simp [tkMean, tkStrongMean, tkStrongVarSq, hemp1]
    · have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN0)
      have htkMean_eq : tkMean f N =
          ∑ p ∈ P, f p * (∑ k ∈ (Finset.Icc 1 N).filter (fun k => p ^ k ≤ N),
            (tkExactDensity (p, k) : ℂ)) := by
        unfold tkMean primePowers
        rw [Finset.sum_biUnion hdisj]
        refine Finset.sum_congr rfl fun p hp => ?_
        have hp_prime := (Finset.mem_filter.mp hp).2
        rw [Finset.sum_image (fun _ _ _ _ h => congr_arg Prod.snd h), Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
        rw [hf.2 p k hp_prime hk1]
      have hdiff_le : ‖tkMean f N - tkStrongMean f N‖ ≤
          (N : ℝ)⁻¹ * ∑ p ∈ P, ‖f p‖ := by
        rw [htkMean_eq]
        unfold tkStrongMean
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
        have hp_mem := Finset.mem_filter.mp hp
        have hp_prime := hp_mem.2
        have hp_le : p ≤ N := (Finset.mem_Icc.mp hp_mem.1).2
        -- Compute the telescoping sum `∑_{1 ≤ k, p^k ≤ N} (p^{-k} - p^{-(k+1)}) = p^{-1} - p^{-(K+1)}`
        set Kp := Nat.log p N
        have hKp_ge1 : 1 ≤ Kp := Nat.le_log_of_pow_le hp_prime.one_lt (by simpa using hp_le)
        have hfilt_eq : (Finset.Icc 1 N).filter (fun k => p ^ k ≤ N) = Finset.Icc 1 Kp := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · intro ⟨⟨hk1, _⟩, hpk⟩
            exact ⟨hk1, Nat.le_log_of_pow_le hp_prime.one_lt hpk⟩
          · intro ⟨hk1, hkKp⟩
            have hpk : p ^ k ≤ N :=
              (Nat.pow_le_pow_right hp_prime.pos hkKp).trans
                (Nat.pow_log_le_self p hN0)
            have hkN : k ≤ N := (Nat.lt_pow_self hp_prime.one_lt).le.trans hpk
            exact ⟨⟨hk1, hkN⟩, hpk⟩
        have htele : ∑ k ∈ Finset.Icc 1 Kp, tkExactDensity (p, k) =
            (p : ℝ)⁻¹ - ((p : ℝ) ^ (Kp + 1))⁻¹ := by
          have htele_gen : ∀ M : ℕ, 1 ≤ M →
              ∑ k ∈ Finset.Icc 1 M, tkExactDensity (p, k) = (p : ℝ)⁻¹ - ((p : ℝ) ^ (M + 1))⁻¹ := by
            intro M hM
            induction M, hM using Nat.le_induction with
            | base =>
              simp only [Finset.Icc_self, Finset.sum_singleton, tkExactDensity, pow_one]
              have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp_prime.ne_zero
              field_simp [hp_ne]
              ring
            | succ m hm ih =>
              have hI : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
                ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
              rw [hI, Finset.sum_insert (by simp), ih]
              unfold tkExactDensity
              have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp_prime.ne_zero
              rw [pow_succ]
              field_simp [hp_ne]
              ring
          exact htele_gen Kp hKp_ge1
        have hsub_eq : f p * (∑ k ∈ (Finset.Icc 1 N).filter (fun k => p ^ k ≤ N),
              (tkExactDensity (p, k) : ℂ)) - f p / (p : ℂ) =
            -f p * (((p : ℝ) ^ (Kp + 1))⁻¹ : ℂ) := by
          rw [hfilt_eq, ← Complex.ofReal_sum, htele]
          push_cast
          ring
        rw [hsub_eq, norm_mul, norm_neg, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Nat.cast_nonneg _)]
        have hpow_gt : (N : ℝ) < (p : ℝ) ^ (Kp + 1) := by
          exact_mod_cast Nat.lt_pow_succ_log_self hp_prime.one_lt N
        have hinv_le : ((p : ℝ) ^ (Kp + 1))⁻¹ ≤ (N : ℝ)⁻¹ :=
          inv_anti₀ hN_pos hpow_gt.le
        calc ‖f p‖ * ((p : ℝ) ^ (Kp + 1))⁻¹ ≤ ‖f p‖ * (N : ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_left hinv_le (norm_nonneg _)
          _ = (N : ℝ)⁻¹ * ‖f p‖ := mul_comm _ _
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq P
        (fun p => Real.sqrt (p : ℝ))
        (fun p => ‖f p‖ / Real.sqrt (p : ℝ))
      have hlhs : ∑ p ∈ P, Real.sqrt (p : ℝ) * (‖f p‖ / Real.sqrt (p : ℝ)) = ∑ p ∈ P, ‖f p‖ := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Finset.mem_filter.mp hp).2.pos
        field_simp [(Real.sqrt_pos.mpr hp_pos).ne']
      have hr1 : ∑ p ∈ P, (Real.sqrt (p : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 := by
        have h1 : ∑ p ∈ P, (Real.sqrt (p : ℝ)) ^ 2 = ∑ p ∈ P, (p : ℝ) :=
          Finset.sum_congr rfl fun p _ => Real.sq_sqrt (Nat.cast_nonneg p)
        rw [h1]
        calc ∑ p ∈ P, (p : ℝ) ≤ ∑ p ∈ Finset.Icc 1 N, (p : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                fun _ _ _ => Nat.cast_nonneg _
          _ ≤ ∑ _p ∈ Finset.Icc 1 N, (N : ℝ) :=
              Finset.sum_le_sum fun p hp => Nat.cast_le.mpr (Finset.mem_Icc.mp hp).2
          _ = (N : ℝ) ^ 2 := by simp [sq]
      have hr2 : ∑ p ∈ P, (‖f p‖ / Real.sqrt (p : ℝ)) ^ 2 = tkStrongVarSq f N := by
        unfold tkStrongVarSq
        refine Finset.sum_congr rfl fun p _ => by rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
      rw [hlhs, hr2] at hcs
      calc ‖tkMean f N - tkStrongMean f N‖ ^ 2
          ≤ ((N : ℝ)⁻¹ * ∑ p ∈ P, ‖f p‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hdiff_le 2
        _ = ((N : ℝ) ^ 2)⁻¹ * (∑ p ∈ P, ‖f p‖) ^ 2 := by rw [mul_pow, inv_pow]
        _ ≤ ((N : ℝ) ^ 2)⁻¹ * ((∑ p ∈ P, (Real.sqrt (p : ℝ)) ^ 2) * tkStrongVarSq f N) :=
            mul_le_mul_of_nonneg_left hcs (by positivity)
        _ ≤ ((N : ℝ) ^ 2)⁻¹ * ((N : ℝ) ^ 2 * tkStrongVarSq f N) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hr1 (tkStrongVarSq_nonneg f N)) (by positivity)
        _ = tkStrongVarSq f N := by field_simp [hN_pos.ne']
  -- Combine Step 1 and Step 2
  calc ∑ n ∈ Finset.Icc 1 N, ‖f n - tkStrongMean f N‖ ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 N,
          (2 * ‖f n - tkMean f N‖ ^ 2 + 2 * ‖tkMean f N - tkStrongMean f N‖ ^ 2) := by
        refine Finset.sum_le_sum fun n _ => ?_
        have htri : ‖f n - tkStrongMean f N‖ ≤
            ‖f n - tkMean f N‖ + ‖tkMean f N - tkStrongMean f N‖ := by
          rw [show f n - tkStrongMean f N =
            (f n - tkMean f N) + (tkMean f N - tkStrongMean f N) by ring]
          exact norm_add_le _ _
        have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖f n - tkMean f N‖ - ‖tkMean f N - tkStrongMean f N‖)]
    _ = 2 * (∑ n ∈ Finset.Icc 1 N, ‖f n - tkMean f N‖ ^ 2) +
        2 * (N : ℝ) * ‖tkMean f N - tkStrongMean f N‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc]
        simp
        ring
    _ ≤ 2 * (34 * (N : ℝ) * (2 * tkStrongVarSq f N)) + 2 * (N : ℝ) * tkStrongVarSq f N := by
        have h1 : 2 * (∑ n ∈ Finset.Icc 1 N, ‖f n - tkMean f N‖ ^ 2) ≤
            2 * (34 * (N : ℝ) * (2 * tkStrongVarSq f N)) := by
          have := hmain.trans (mul_le_mul_of_nonneg_left hB_le (by positivity))
          linarith
        have h2 : 2 * (N : ℝ) * ‖tkMean f N - tkStrongMean f N‖ ^ 2 ≤
            2 * (N : ℝ) * tkStrongVarSq f N :=
          mul_le_mul_of_nonneg_left hmean_diff_sq (by positivity)
        linarith
    _ = 138 * (N : ℝ) * tkStrongVarSq f N := by ring

lemma cardDistinctFactors_isStronglyAdditive :
    IsStronglyAdditive (fun n : ℕ => (ArithmeticFunction.cardDistinctFactors n : ℂ)) := by
  refine ⟨⟨by simp, fun m n _ _ hcop => ?_⟩, fun p k hp hk => ?_⟩
  · dsimp only
    exact_mod_cast ArithmeticFunction.cardDistinctFactors_mul hcop
  · dsimp only
    rw [ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp (by omega),
      ArithmeticFunction.cardDistinctFactors_apply_prime hp]

/-- **Hardy–Ramanujan Normal Order Variance Bound (Turán 1934)**:
For all `N : ℕ`,
`∑_{n=1}^N (ω(n) - ∑_{p ≤ N} 1/p)^2 ≤ 138 * N * ∑_{p ≤ N} 1/p`. -/
theorem hardy_ramanujan_omega_variance (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.cardDistinctFactors n : ℝ) -
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) ^ 2 ≤
      138 * (N : ℝ) * ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹ := by
  have htk := turan_kubilius_strongly_additive cardDistinctFactors_isStronglyAdditive N
  rw [tkStrongVar_sq] at htk
  have hmean : tkStrongMean (fun n => (ArithmeticFunction.cardDistinctFactors n : ℂ)) N =
      ((∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹ : ℝ) : ℂ) := by
    unfold tkStrongMean
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    dsimp only
    have hp_prime := (Finset.mem_filter.mp hp).2
    rw [ArithmeticFunction.cardDistinctFactors_apply_prime hp_prime]
    simp [div_eq_mul_inv]
  have hvar : tkStrongVarSq (fun n => (ArithmeticFunction.cardDistinctFactors n : ℂ)) N =
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹ := by
    unfold tkStrongVarSq
    refine Finset.sum_congr rfl fun p hp => ?_
    dsimp only
    have hp_prime := (Finset.mem_filter.mp hp).2
    rw [ArithmeticFunction.cardDistinctFactors_apply_prime hp_prime]
    simp [div_eq_mul_inv]
  rw [hmean, hvar] at htk
  have hlhs : ∑ n ∈ Finset.Icc 1 N,
        ‖(ArithmeticFunction.cardDistinctFactors n : ℂ) -
          ((∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹ : ℝ) : ℂ)‖ ^ 2 =
      ∑ n ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.cardDistinctFactors n : ℝ) -
          ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) ^ 2 := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (ArithmeticFunction.cardDistinctFactors n : ℂ) -
          ((∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹ : ℝ) : ℂ) =
        (((ArithmeticFunction.cardDistinctFactors n : ℝ) -
          ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rwa [hlhs] at htk

/-- **Hardy–Ramanujan Normal Order Chebyshev Tail Bound**:
For every `N : ℕ` and every `ε > 0`, the number of `n ∈ {1, ..., N}` deviating from
`∑_{p ≤ N} 1/p` by at least `ε` is at most `(138 * N * ∑_{p ≤ N} 1/p) / ε^2`. -/
theorem hardy_ramanujan_normal_order_tail (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (((Finset.Icc 1 N).filter (fun n =>
        ε ≤ |(ArithmeticFunction.cardDistinctFactors n : ℝ) -
          ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹|)).card : ℝ) ≤
      138 * (N : ℝ) * (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) / ε ^ 2 := by
  set S := (Finset.Icc 1 N).filter (fun n =>
    ε ≤ |(ArithmeticFunction.cardDistinctFactors n : ℝ) -
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹|)
  have hcheb : (S.card : ℝ) * ε ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.cardDistinctFactors n : ℝ) -
          ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) ^ 2 := by
    calc (S.card : ℝ) * ε ^ 2
        = ∑ _n ∈ S, ε ^ 2 := by simp
      _ ≤ ∑ n ∈ S, ((ArithmeticFunction.cardDistinctFactors n : ℝ) -
            ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) ^ 2 := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hge := (Finset.mem_filter.mp hn).2
          conv_rhs => rw [← sq_abs]
          exact pow_le_pow_left₀ hε.le hge 2
      _ ≤ ∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.cardDistinctFactors n : ℝ) -
            ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => sq_nonneg _
  rw [le_div_iff₀ (sq_pos_of_pos hε)]
  exact hcheb.trans (hardy_ramanujan_omega_variance N)

/-! ## Section 4: Vaughan's Identity (Exact Bilinear Decomposition of `Λ(n)`) -/

/-- Truncation of `ArithmeticFunction.vonMangoldt` to `n ≤ U`. -/
def vonMangoldtLe (U : ℕ) : ArithmeticFunction ℝ where
  toFun n := if n ≤ U then Λ n else 0
  map_zero' := by simp

/-- Truncation of `ArithmeticFunction.vonMangoldt` to `n > U`. -/
def vonMangoldtGt (U : ℕ) : ArithmeticFunction ℝ where
  toFun n := if U < n then Λ n else 0
  map_zero' := by simp

/-- Real-valued Möbius function truncated to `n ≤ V`. -/
def moebiusLe (V : ℕ) : ArithmeticFunction ℝ where
  toFun n := if n ≤ V then (ArithmeticFunction.moebius n : ℝ) else 0
  map_zero' := by simp

/-- Real-valued Möbius function truncated to `n > V`. -/
def moebiusGt (V : ℕ) : ArithmeticFunction ℝ where
  toFun n := if V < n then (ArithmeticFunction.moebius n : ℝ) else 0
  map_zero' := by simp

lemma vonMangoldtLe_add_vonMangoldtGt (U : ℕ) :
    vonMangoldtLe U + vonMangoldtGt U = ArithmeticFunction.vonMangoldt := by
  ext n
  rw [ArithmeticFunction.add_apply]
  change (if n ≤ U then Λ n else 0) + (if U < n then Λ n else 0) = Λ n
  by_cases h : n ≤ U
  · have hnot : ¬ U < n := by omega
    simp [h, hnot]
  · have hgt : U < n := by omega
    simp [h, hgt]

lemma moebiusLe_add_moebiusGt (V : ℕ) :
    moebiusLe V + moebiusGt V = (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
  ext n
  rw [ArithmeticFunction.add_apply]
  change (if n ≤ V then (ArithmeticFunction.moebius n : ℝ) else 0) +
      (if V < n then (ArithmeticFunction.moebius n : ℝ) else 0) =
    (ArithmeticFunction.moebius n : ℝ)
  by_cases h : n ≤ V
  · have hnot : ¬ V < n := by omega
    simp [h, hnot]
  · have hgt : V < n := by omega
    simp [h, hgt]

lemma moebius_real_mul_zeta :
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = 1 := by
  have h := ArithmeticFunction.moebius_mul_coe_zeta
  ext n
  have hn := congr_arg (fun f : ArithmeticFunction ℤ => ((f n : ℤ) : ℝ)) h
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.natCoe_apply] at hn ⊢
  push_cast at hn
  simpa using hn

/-- **Vaughan's Identity (Ring-Level Dirichlet Convolution Form)**:
For all `U, V : ℕ`,
`Λ = Λ_{≤ U} + μ_{≤ V} * log - (Λ_{≤ U} * μ_{≤ V}) * ζ + Λ_{> U} * (ζ * μ_{> V})`. -/
theorem vaughan_convolution_identity (U V : ℕ) :
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      vonMangoldtLe U +
      moebiusLe V * ArithmeticFunction.log -
      (vonMangoldtLe U * moebiusLe V) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) +
      vonMangoldtGt U * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * moebiusGt V) := by
  set ζR : ArithmeticFunction ℝ := (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  set μR : ArithmeticFunction ℝ := (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
  have hlog : ArithmeticFunction.log = ArithmeticFunction.vonMangoldt * ζR :=
    ArithmeticFunction.vonMangoldt_mul_zeta.symm
  have hL : ArithmeticFunction.vonMangoldt = vonMangoldtLe U + vonMangoldtGt U :=
    (vonMangoldtLe_add_vonMangoldtGt U).symm
  have hM : moebiusGt V = μR - moebiusLe V :=
    eq_sub_of_add_eq' (moebiusLe_add_moebiusGt V)
  have hmz : μR * ζR = 1 := moebius_real_mul_zeta
  rw [hlog, hM]
  calc ArithmeticFunction.vonMangoldt
      = vonMangoldtLe U + vonMangoldtGt U * 1 := by rw [mul_one, ← hL]
    _ = vonMangoldtLe U + vonMangoldtGt U * (μR * ζR) := by rw [hmz]
    _ = vonMangoldtLe U +
          moebiusLe V * ((vonMangoldtLe U + vonMangoldtGt U) * ζR) -
          vonMangoldtLe U * moebiusLe V * ζR +
          vonMangoldtGt U * (ζR * (μR - moebiusLe V)) := by ring
    _ = vonMangoldtLe U +
          moebiusLe V * (ArithmeticFunction.vonMangoldt * ζR) -
          vonMangoldtLe U * moebiusLe V * ζR +
          vonMangoldtGt U * (ζR * (μR - moebiusLe V)) := by rw [← hL]

/-- Vaughan Type I_2 coefficient `c₁(d) = ∑_{ab = d, a ≤ U, b ≤ V} Λ(a) μ(b)`. -/
def vaughanCoeffI (U V d : ℕ) : ℝ :=
  (vonMangoldtLe U * moebiusLe V) d

/-- Vaughan Type II coefficient `c₂(k) = ∑_{d ∣ k, d ≤ V} μ(d)`. -/
def vaughanCoeffII (V k : ℕ) : ℝ :=
  ∑ d ∈ k.divisors.filter (· ≤ V), (ArithmeticFunction.moebius d : ℝ)

lemma zeta_mul_moebiusGt_apply (V k : ℕ) (hV : 1 ≤ V) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * moebiusGt V) k =
      if V < k then -vaughanCoeffII V k else 0 := by
  rw [ArithmeticFunction.mul_apply]
  have hsum_eq : ∑ x ∈ k.divisorsAntidiagonal,
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) x.1 * moebiusGt V x.2 =
      ∑ d ∈ k.divisors.filter (V < ·), (ArithmeticFunction.moebius d : ℝ) := by
    rw [Nat.sum_divisorsAntidiagonal' (f := fun a b =>
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) a * moebiusGt V b)]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hk0 : k ≠ 0 := (Nat.mem_divisors.mp hd).2
    have hd_dvd : d ∣ k := Nat.dvd_of_mem_divisors hd
    have hdiv_ne : k / d ≠ 0 := by
      intro h0
      have := Nat.mul_div_cancel' hd_dvd
      rw [h0, mul_zero] at this
      exact hk0 this.symm
    simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hdiv_ne,
      ↓reduceIte, Nat.cast_one, one_mul, moebiusGt, ArithmeticFunction.coe_mk]
  rw [hsum_eq]
  by_cases hVk : V < k
  · simp only [hVk, ↓reduceIte]
    have hpart : ∑ d ∈ k.divisors.filter (· ≤ V), (ArithmeticFunction.moebius d : ℝ) +
        ∑ d ∈ k.divisors.filter (V < ·), (ArithmeticFunction.moebius d : ℝ) =
        ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) := by
      rw [← Finset.sum_union]
      · refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext d
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          by_cases hle : d ≤ V
          · left; exact ⟨h, hle⟩
          · right; exact ⟨h, by omega⟩
      · rw [Finset.disjoint_left]
        intro d h1 h2
        simp only [Finset.mem_filter] at h1 h2
        omega
    have hk_ne1 : k ≠ 1 := by omega
    rw [sum_moebius_divisors_eq k, if_neg hk_ne1] at hpart
    unfold vaughanCoeffII
    linarith
  · simp only [hVk, ↓reduceIte]
    refine Finset.sum_eq_zero fun d hd => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    have hd_le : d ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hd.1.2) hd.1.1
    omega

lemma vaughanCoeffI_eq_zero_of_gt {U V d : ℕ} (hd : U * V < d) :
    vaughanCoeffI U V d = 0 := by
  unfold vaughanCoeffI
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hmul : x.1 * x.2 = d := (Nat.mem_divisorsAntidiagonal.mp hx).1
  simp only [vonMangoldtLe, moebiusLe, ArithmeticFunction.coe_mk]
  by_cases h1 : x.1 ≤ U
  · by_cases h2 : x.2 ≤ V
    · have : x.1 * x.2 ≤ U * V := Nat.mul_le_mul h1 h2
      omega
    · simp [h2]
  · simp [h1]

lemma abs_vaughanCoeffI_le_log (U V d : ℕ) :
    |vaughanCoeffI U V d| ≤ Real.log (d : ℝ) := by
  by_cases hd0 : d = 0
  · subst hd0; simp [vaughanCoeffI]
  · unfold vaughanCoeffI
    rw [ArithmeticFunction.mul_apply]
    calc |∑ x ∈ d.divisorsAntidiagonal, vonMangoldtLe U x.1 * moebiusLe V x.2|
        ≤ ∑ x ∈ d.divisorsAntidiagonal, |vonMangoldtLe U x.1 * moebiusLe V x.2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ d.divisorsAntidiagonal, Λ x.1 := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [abs_mul]
          have h1 : |vonMangoldtLe U x.1| ≤ Λ x.1 := by
            simp only [vonMangoldtLe, ArithmeticFunction.coe_mk]
            split_ifs
            · exact le_of_eq (abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg)
            · simp [ArithmeticFunction.vonMangoldt_nonneg]
          have h2 : |moebiusLe V x.2| ≤ 1 := by
            simp only [moebiusLe, ArithmeticFunction.coe_mk]
            split_ifs
            · exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := x.2)
            · norm_num
          calc |vonMangoldtLe U x.1| * |moebiusLe V x.2|
              ≤ Λ x.1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
            _ = Λ x.1 := mul_one _
      _ = ∑ k ∈ d.divisors, Λ k := Nat.sum_divisorsAntidiagonal (f := fun a _ => Λ a)
      _ = Real.log (d : ℝ) := ArithmeticFunction.vonMangoldt_sum

lemma abs_vaughanCoeffII_le_divisors (V k : ℕ) :
    |vaughanCoeffII V k| ≤ (k.divisors.card : ℝ) := by
  unfold vaughanCoeffII
  calc |∑ d ∈ k.divisors.filter (· ≤ V), (ArithmeticFunction.moebius d : ℝ)|
      ≤ ∑ d ∈ k.divisors.filter (· ≤ V), |(ArithmeticFunction.moebius d : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ k.divisors.filter (· ≤ V), (1 : ℝ) :=
        Finset.sum_le_sum fun d _ => by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    _ = ((k.divisors.filter (· ≤ V)).card : ℝ) := by simp
    _ ≤ (k.divisors.card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _

/-- **Vaughan's Identity (Pointwise Exact Arithmetic Decomposition for `n > U`)**:
For all `U, V ≥ 1` and every `n > U`:
`Λ(n) = ∑_{d ∣ n, d ≤ V} μ(d) log(n / d) - ∑_{d ∣ n, d ≤ U V} c₁(d) - ∑_{m k = n, m > U, k > V} Λ(m) c₂(k)`. -/
theorem vaughan_identity_pointwise {U V n : ℕ} (_hU : 1 ≤ U) (hV : 1 ≤ V) (hn : U < n) :
    Λ n =
      (∑ d ∈ n.divisors.filter (· ≤ V),
          (ArithmeticFunction.moebius d : ℝ) * Real.log ((n / d : ℕ) : ℝ)) -
      (∑ d ∈ n.divisors.filter (· ≤ U * V), vaughanCoeffI U V d) -
      (∑ x ∈ n.divisorsAntidiagonal.filter (fun x => U < x.1 ∧ V < x.2),
          Λ x.1 * vaughanCoeffII V x.2) := by
  have hconv := congr_arg (fun f : ArithmeticFunction ℝ => f n) (vaughan_convolution_identity U V)
  change Λ n =
      vonMangoldtLe U n + (moebiusLe V * ArithmeticFunction.log) n -
        ((vonMangoldtLe U * moebiusLe V) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n +
        (vonMangoldtGt U * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * moebiusGt V)) n at hconv
  have hn0 : n ≠ 0 := by omega
  have hLe0 : vonMangoldtLe U n = 0 := by
    simp [vonMangoldtLe, show ¬ n ≤ U by omega]
  have hT1 : (moebiusLe V * ArithmeticFunction.log) n =
      ∑ d ∈ n.divisors.filter (· ≤ V),
        (ArithmeticFunction.moebius d : ℝ) * Real.log ((n / d : ℕ) : ℝ) := by
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (f := fun a b => moebiusLe V a * ArithmeticFunction.log b),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [moebiusLe, ArithmeticFunction.coe_mk, ArithmeticFunction.log_apply]
    split_ifs <;> ring
  have hT2 : ((vonMangoldtLe U * moebiusLe V) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n =
      ∑ d ∈ n.divisors.filter (· ≤ U * V), vaughanCoeffI U V d := by
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (f := fun a b =>
        (vonMangoldtLe U * moebiusLe V) a * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) b),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd_dvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hdiv_ne : n / d ≠ 0 := by
      intro h0
      have := Nat.mul_div_cancel' hd_dvd
      rw [h0, mul_zero] at this
      exact hn0 this.symm
    simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hdiv_ne,
      ↓reduceIte, Nat.cast_one, mul_one]
    change vaughanCoeffI U V d = if d ≤ U * V then vaughanCoeffI U V d else 0
    split_ifs with hle
    · rfl
    · exact vaughanCoeffI_eq_zero_of_gt (by omega)
  have hT3 : (vonMangoldtGt U * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * moebiusGt V)) n =
      -(∑ x ∈ n.divisorsAntidiagonal.filter (fun x => U < x.1 ∧ V < x.2),
          Λ x.1 * vaughanCoeffII V x.2) := by
    rw [ArithmeticFunction.mul_apply, ← Finset.sum_neg_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [zeta_mul_moebiusGt_apply V x.2 hV]
    simp only [vonMangoldtGt, ArithmeticFunction.coe_mk]
    by_cases h1 : U < x.1 <;> by_cases h2 : V < x.2 <;> simp [h1, h2]
  rw [hLe0, zero_add, hT1, hT2, hT3] at hconv
  linarith

/-- **Vaughan's Bilinear Sum Decomposition** for an arbitrary complex weight `f : ℕ → ℂ`:
Decomposes `∑_{U < n ≤ N} Λ(n) f(n)` into explicit Type I_1, Type I_2, and Type II bilinear sums. -/
theorem vaughan_bilinear_sum (f : ℕ → ℂ) {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (N : ℕ) :
    ∑ n ∈ Finset.Ioc U N, (Λ n : ℂ) * f n =
      (∑ d ∈ Finset.Icc 1 V, (ArithmeticFunction.moebius d : ℂ) *
          ∑ m ∈ (Finset.Icc 1 (N / d)).filter (fun m => U < d * m),
            (Real.log (m : ℝ) : ℂ) * f (d * m)) -
      (∑ d ∈ Finset.Icc 1 (U * V), (vaughanCoeffI U V d : ℂ) *
          ∑ m ∈ (Finset.Icc 1 (N / d)).filter (fun m => U < d * m), f (d * m)) -
      (∑ m ∈ Finset.Ioc U (N / V), (Λ m : ℂ) *
          ∑ k ∈ Finset.Ioc V (N / m), (vaughanCoeffII V k : ℂ) * f (m * k)) := by
  have hpt : ∀ n ∈ Finset.Ioc U N,
      (Λ n : ℂ) * f n =
        (∑ d ∈ n.divisors.filter (· ≤ V),
            (ArithmeticFunction.moebius d : ℂ) * (Real.log ((n / d : ℕ) : ℝ) : ℂ) * f n) -
        (∑ d ∈ n.divisors.filter (· ≤ U * V), (vaughanCoeffI U V d : ℂ) * f n) -
        (∑ x ∈ n.divisorsAntidiagonal.filter (fun x => U < x.1 ∧ V < x.2),
            (Λ x.1 : ℂ) * (vaughanCoeffII V x.2 : ℂ) * f n) := by
    intro n hn
    have hUn : U < n := (Finset.mem_Ioc.mp hn).1
    have hv := vaughan_identity_pointwise hU hV hUn
    have hvC : (Λ n : ℂ) =
        (∑ d ∈ n.divisors.filter (· ≤ V),
            (ArithmeticFunction.moebius d : ℂ) * (Real.log ((n / d : ℕ) : ℝ) : ℂ)) -
        (∑ d ∈ n.divisors.filter (· ≤ U * V), (vaughanCoeffI U V d : ℂ)) -
        (∑ x ∈ n.divisorsAntidiagonal.filter (fun x => U < x.1 ∧ V < x.2),
            (Λ x.1 : ℂ) * (vaughanCoeffII V x.2 : ℂ)) := by
      exact_mod_cast hv
    rw [hvC, sub_mul, sub_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  · congr 1
    · -- Type I_1: swap `(n, d)` to `(d, m = n / d)`
      have hswap1 : ∀ n ∈ Finset.Ioc U N,
          ∑ d ∈ n.divisors.filter (· ≤ V),
              (ArithmeticFunction.moebius d : ℂ) * (Real.log ((n / d : ℕ) : ℝ) : ℂ) * f n =
          ∑ d ∈ Finset.Icc 1 V,
            if d ∣ n then (ArithmeticFunction.moebius d : ℂ) *
              (Real.log ((n / d : ℕ) : ℝ) : ℂ) * f n else 0 := by
        intro n hn
        have hn0 : n ≠ 0 := by have := (Finset.mem_Ioc.mp hn).1; omega
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hdn, _⟩, hdV⟩
          exact ⟨⟨Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn0), hdV⟩, hdn⟩
        · rintro ⟨⟨_, hdV⟩, hdn⟩
          exact ⟨⟨hdn, hn0⟩, hdV⟩
      rw [Finset.sum_congr rfl hswap1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd_pos : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      rw [← Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_bij (fun n _ => n / d) ?_ ?_ ?_ ?_
      · intro n hn
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
        have hdm : d * (n / d) = n := Nat.mul_div_cancel' hn.2
        have hm_pos : 1 ≤ n / d := by
          by_contra h0
          have h0' : n / d = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp h0)
          rw [h0', mul_zero] at hdm
          omega
        have hm_le : n / d ≤ N / d := Nat.div_le_div_right hn.1.2
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm_pos, hm_le⟩, by omega⟩
      · intro n₁ h1 n₂ h2 heq
        simp only [Finset.mem_filter] at h1 h2
        rw [← Nat.mul_div_cancel' h1.2, ← Nat.mul_div_cancel' h2.2, heq]
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_Icc] at hm
        have hdm_le : d * m ≤ N := by
          have := Nat.mul_le_mul_left d hm.1.2
          exact this.trans (Nat.mul_div_le N d)
        refine ⟨d * m, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hm.2, hdm_le⟩,
          dvd_mul_right d m⟩, Nat.mul_div_cancel_left m (by omega)⟩
      · intro n hn
        simp only [Finset.mem_filter] at hn
        rw [Nat.mul_div_cancel' hn.2]
        ring
    · -- Type I_2: swap `(n, d)` to `(d, m = n / d)`
      have hswap2 : ∀ n ∈ Finset.Ioc U N,
          ∑ d ∈ n.divisors.filter (· ≤ U * V), (vaughanCoeffI U V d : ℂ) * f n =
          ∑ d ∈ Finset.Icc 1 (U * V),
            if d ∣ n then (vaughanCoeffI U V d : ℂ) * f n else 0 := by
        intro n hn
        have hn0 : n ≠ 0 := by have := (Finset.mem_Ioc.mp hn).1; omega
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hdn, _⟩, hdUV⟩
          exact ⟨⟨Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn0), hdUV⟩, hdn⟩
        · rintro ⟨⟨_, hdUV⟩, hdn⟩
          exact ⟨⟨hdn, hn0⟩, hdUV⟩
      rw [Finset.sum_congr rfl hswap2, Finset.sum_comm]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd_pos : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      rw [← Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_bij (fun n _ => n / d) ?_ ?_ ?_ ?_
      · intro n hn
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
        have hdm : d * (n / d) = n := Nat.mul_div_cancel' hn.2
        have hm_pos : 1 ≤ n / d := by
          by_contra h0
          have h0' : n / d = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp h0)
          rw [h0', mul_zero] at hdm
          omega
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm_pos, Nat.div_le_div_right hn.1.2⟩,
          by omega⟩
      · intro n₁ h1 n₂ h2 heq
        simp only [Finset.mem_filter] at h1 h2
        rw [← Nat.mul_div_cancel' h1.2, ← Nat.mul_div_cancel' h2.2, heq]
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_Icc] at hm
        have hdm_le : d * m ≤ N :=
          (Nat.mul_le_mul_left d hm.1.2).trans (Nat.mul_div_le N d)
        refine ⟨d * m, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hm.2, hdm_le⟩,
          dvd_mul_right d m⟩, Nat.mul_div_cancel_left m (by omega)⟩
      · intro n hn
        simp only [Finset.mem_filter] at hn
        rw [Nat.mul_div_cancel' hn.2]
  · -- Type II: reindex `(n, (m, k))` to `(m, k)`
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij
      (fun p _ => (⟨p.2.1, p.2.2⟩ : (m : ℕ) × ℕ)) ?_ ?_ ?_ ?_
    · intro ⟨n, ⟨m, k⟩⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_filter,
        Nat.mem_divisorsAntidiagonal] at hp ⊢
      have hmk : m * k = n := hp.2.1.1
      have hm_le : m ≤ N / V := (Nat.le_div_iff_mul_le (by omega)).mpr (by
        have h1 : m * V ≤ m * k := Nat.mul_le_mul_left m (by omega)
        omega)
      have hk_le : k ≤ N / m := (Nat.le_div_iff_mul_le (by omega)).mpr (by
        rw [mul_comm]; omega)
      exact ⟨⟨hp.2.2.1, hm_le⟩, ⟨hp.2.2.2, hk_le⟩⟩
    · intro ⟨n₁, ⟨m₁, k₁⟩⟩ h1 ⟨n₂, ⟨m₂, k₂⟩⟩ h2 heq
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
      rcases heq with ⟨rfl, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at h1 h2
      have hn : n₁ = n₂ := h1.2.1.1.symm.trans h2.2.1.1
      subst hn
      rfl
    · intro ⟨m, k⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_Ioc] at hp
      have hmk_gt_U : U < m * k := by
        have hk1 : 1 ≤ k := by omega
        have : m ≤ m * k := Nat.le_mul_of_pos_right m (by omega)
        omega
      have hmk_le_N : m * k ≤ N := by
        have := Nat.mul_le_mul_left m hp.2.2
        exact this.trans (Nat.mul_div_le N m)
      have hmk_ne : m * k ≠ 0 := by omega
      refine ⟨⟨m * k, (m, k)⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_filter,
        Nat.mem_divisorsAntidiagonal]
      exact ⟨⟨hmk_gt_U, hmk_le_N⟩, ⟨⟨trivial, hmk_ne⟩, hp.1.1, hp.2.1⟩⟩
    · intro ⟨n, ⟨m, k⟩⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp
      rw [hp.2.1.1]
      ring

end
end Arith4Ext.SieveCharacters
