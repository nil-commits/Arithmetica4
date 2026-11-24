import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# RHDirect.ChenDefs

Shared, lightweight native-Mathlib definitions and interfaces for our formalization of
**Chen's Theorem (1973)**: every sufficiently large even integer is the sum of a prime
and an integer with at most two prime factors (`p + P₂`).

Zero `sorry`, zero custom `axiom`s, zero `opaque`, zero `native_decide`.
-/

noncomputable section

open Finset Classical

namespace RHDirect.Chen

/-- An integer `q : ℕ` is a `P₂`-number (an almost-prime with at most two prime factors,
counted with multiplicity) if it is prime or the product of two primes. -/
def IsP2 (q : ℕ) : Prop :=
  Nat.Prime q ∨ ∃ r s : ℕ, Nat.Prime r ∧ Nat.Prime s ∧ q = r * s

/-- The multiplicative linear-sieve density for the Goldbach shifted-prime sequence
`A = {N - p : p prime, p < N}`: `g(p) = 0` for `p = 2` or `p ∣ N`, and `g(p) = 1 / (p - 1)`
for odd primes `p ∤ N`. Extended multiplicatively to squarefree `d` via `∏_{p ∈ d.primeFactors}`. -/
def chenPrimeDensity (N p : ℕ) : ℝ :=
  if p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ N then 1 / ((p : ℝ) - 1) else 0

/-- Multiplicative extension of a prime density `ω : ℕ → ℝ` to all natural numbers
(supported on squarefree numbers). -/
def multDensity (ω : ℕ → ℝ) (d : ℕ) : ℝ :=
  if Squarefree d then ∏ p ∈ d.primeFactors, ω p else 0

/-- The sifting product `V(ω, z) = ∏_{p < z, p prime} (1 - ω(p))`. -/
def siftProd (ω : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < z), (1 - ω p)

/-- The sifted count `S(A, P(z))` of elements `a ∈ A` having no prime divisor `< z`. -/
def siftedCard (A : Finset ℕ) (z : ℝ) : ℕ :=
  (A.filter (fun a => ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ a)).card

/-- Linear-sieve (`κ = 1`) Mertens-ratio hypothesis on a prime density `ω : ℕ → ℝ` with
constant `K ≥ 1`:
1. `0 ≤ ω(p) < 1` for every prime `p`, and `ω(n) = 0` for non-primes;
2. For all `2 ≤ w ≤ z`:
   `∏_{w ≤ p < z, p prime} (1 - ω(p))⁻¹ ≤ (log z / log w) * (1 + K / log w)`. -/
structure LinearSieveDensity (ω : ℕ → ℝ) (K : ℝ) : Prop where
  K_ge_one : 1 ≤ K
  nonneg : ∀ p : ℕ, 0 ≤ ω p
  lt_one : ∀ p : ℕ, ω p < 1
  support_prime : ∀ n : ℕ, ¬ n.Prime → ω n = 0
  mertens_ratio : ∀ w z : ℝ, 2 ≤ w → w ≤ z →
    ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - ω p)⁻¹ ≤
      (Real.log z / Real.log w) * (1 + K / Real.log w)

/-- Admissible pair of continuous linear-sieve limit functions `(F, f)` satisfying
the Rosser–Iwaniec (`β = 2`) delay-differential integral equations and limits `F, f → 1`. -/
structure LinearSievePair (F f : ℝ → ℝ) : Prop where
  F_cont : ContinuousOn F (Set.Ioi 0)
  f_cont : ContinuousOn f (Set.Ioi 0)
  F_antitone : AntitoneOn F (Set.Ioi 0)
  f_monotone : MonotoneOn f (Set.Ioi 0)
  f_nonneg : ∀ s : ℝ, 0 < s → 0 ≤ f s
  f_le_one : ∀ s : ℝ, 0 < s → f s ≤ 1
  one_le_F : ∀ s : ℝ, 0 < s → 1 ≤ F s
  F_tendsto_one : Filter.Tendsto F Filter.atTop (nhds 1)
  f_tendsto_one : Filter.Tendsto f Filter.atTop (nhds 1)
  F_const_le_three : ∀ s : ℝ, 0 < s → s ≤ 3 → s * F s = 3 * F 3
  f_zero_le_two : ∀ s : ℝ, 0 < s → s ≤ 2 → f s = 0
  F_buchstab : ∀ a b : ℝ, 3 ≤ a → a ≤ b →
    b * F b - a * F a = ∫ u in a..b, f (u - 1)
  f_buchstab : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
    b * f b - a * f a = ∫ u in a..b, F (u - 1)

/-- The exact Chen triple-prime constant
`I_B = ∫_{1/8}^{1/3} log(2 - 3u) / (u * (1 - u)) du ≈ 0.363084`. -/
def chenIB : ℝ :=
  ∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), Real.log (2 - 3 * u) / (u * (1 - u))

/-- Chen's triple-prime set `M(N)` for `z = N^{1/8}` and `y = N^{1/3}`:
triples `(q₁, q₂, q₃)` of primes coprime to `N` with
`N^{1/8} ≤ q₁ < N^{1/3} ≤ q₂ ≤ q₃` and `q₁ * q₂ * q₃ < N`. -/
def chenM (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range N).product ((Finset.range N).product (Finset.range N))).filter fun t =>
    let q₁ := t.1
    let q₂ := t.2.1
    let q₃ := t.2.2
    q₁.Prime ∧ q₂.Prime ∧ q₃.Prime ∧
    ¬ q₁ ∣ N ∧ ¬ q₂ ∣ N ∧ ¬ q₃ ∣ N ∧
    (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (q₁ : ℝ) ∧
    (q₁ : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3) ∧
    (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (q₂ : ℝ) ∧
    q₂ ≤ q₃ ∧
    q₁ * q₂ * q₃ < N

/-- The shifted odd-prime set `A(N) = {N - p : p prime, 2 < p < N, ¬ p ∣ N}`
represented via the prime `p` (since `p ↦ N - p` is injective on `p < N`). -/
def chenGoldbachSet (N : ℕ) : Finset ℕ :=
  ((Finset.range N).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)).image (fun p => N - p)

/-- The subset `B_prod(N)` of distinct products `q₁ * q₂ * q₃` arising from `chenM N`,
with `N - m` prime (counted via `m ∈ M_prod(N)`). -/
def chenMProd (N : ℕ) : Finset ℕ :=
  (chenM N).image (fun t => t.1 * t.2.1 * t.2.2)

end RHDirect.Chen
