import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ModularForms.Basic

open scoped TensorProduct

/-!
# Arithmetica4 — Trustless Unconditional Landmark Challenge Specification

This file imports **only upstream Mathlib** (`0` `RHDirect` imports, `0` `PrimeGaps` imports,
`0` `MaynardDock` imports) and introduces **zero custom definitions**. Every mathematical
symbol in every theorem below comes directly from Mathlib.

To verify `Solution.lean` against this file without trusting any intermediate module, run:
```sh
lake env lean --run scripts/verify_challenge.lean
```
This checks that every theorem below is proved in `Solution.lean` with identical universe
parameters and `Expr` type, using only `{propext, Classical.choice, Quot.sound}`.
-/

/-! ## 1. Vinogradov's Three-Primes Theorem (1937) -/

/-- Every sufficiently large odd natural number is the sum of three primes. -/
theorem vinogradov_three_primes :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Odd n →
      ∃ p₁ p₂ p₃ : ℕ, Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ Nat.Prime p₃ ∧ p₁ + p₂ + p₃ = n :=
  sorry

/-! ## 2. Chen's Theorem (1973) -/

/-- Every sufficiently large even natural number is `p + q` with `p` prime and `q` prime or
a product of two primes (`P₂`). -/
theorem chen_theorem :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧
        (Nat.Prime q ∨ ∃ r s : ℕ, Nat.Prime r ∧ Nat.Prime s ∧ q = r * s) ∧
        p + q = n :=
  sorry

/-! ## 3. Linnik's Least Prime in an Arithmetic Progression (1944) -/

/-- There exist absolute constants `L, C > 0` such that for every `m ≥ 2` and every residue
`a` coprime to `m`, there is a prime `p ≡ a [MOD m]` with `p ≤ C * m ^ L`. -/
theorem linnik_theorem :
    ∃ L : ℝ, 0 < L ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (m a : ℕ), 2 ≤ m → Nat.Coprime a m →
        ∃ p : ℕ, Nat.Prime p ∧ p ≡ a [MOD m] ∧ (p : ℝ) ≤ C * (m : ℝ) ^ L :=
  sorry

/-! ## 4–6. Unconditional Bounded Prime Gaps (Polymath8b, H = 246) -/

/-- For every `N`, there exist primes `N < p < q` with `q - p ≤ 246`. -/
theorem unconditional_prime_gap_le_246 :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ 246 :=
  sorry

/-- There exists `0 < H ≤ 246` such that arbitrarily large prime pairs differ by at most `H`. -/
theorem bounded_prime_gaps_246_unconditional :
    ∃ H : ℕ, 0 < H ∧ H ≤ 246 ∧
      ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ H :=
  sorry

/-- Consecutive prime gaps are at most `246` infinitely often (`Nat.nth Nat.Prime` form). -/
theorem frequently_consecutive_prime_gap_le_246 :
    Filter.Frequently (fun m : ℕ => Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ 246)
      Filter.atTop :=
  sorry

/-! ## 6b. Maynard–Tao Arbitrary `m`-Tuples of Bounded Primes (2015) -/

/-- For every `m ≥ 1`, there exists `H : ℕ` such that arbitrarily large intervals of width `H`
contain at least `m` primes (`m`-tuples of primes in bounded intervals). -/
theorem maynard_tao_m_tuples :
    ∀ m : ℕ, 1 ≤ m → ∃ H : ℕ, ∀ N : ℕ, ∃ S : Finset ℕ, S.card = m ∧
      (∀ p ∈ S, N ≤ p ∧ Nat.Prime p) ∧ ∀ p ∈ S, ∀ q ∈ S, p ≤ q + H :=
  sorry

/-! ## 7. Dwork's Rationality Theorem (Weil Conjecture I, 1960) -/

/-- For any prime `p`, any `r > 0` (`q = p ^ r`), any dimension `n`, and any finite system of
polynomials `fs : Finset (MvPolynomial (Fin n) (GaloisField p r))`, the Hasse–Weil zeta
function `exp(∑_{m ≥ 1} #V(𝔽_{q^m}) T^m / m) ∈ ℚ[[T]]` is a rational function `P(T) / Q(T)`
over `ℚ` with `Q(0) = 1`. -/
theorem dwork_rationality
    (p r n : ℕ) [Fact p.Prime] (hr : 0 < r)
    (fs : Finset (MvPolynomial (Fin n) (GaloisField p r)))
    (φ : ∀ m : ℕ, 1 ≤ m → (GaloisField p r →+* GaloisField p (r * m))) :
    ∃ P Q : Polynomial ℚ, Q.coeff 0 = 1 ∧
      PowerSeries.subst
        (PowerSeries.mk fun m =>
          if hm : 1 ≤ m then
            (Nat.card {x : Fin n → GaloisField p (r * m) //
              ∀ f ∈ fs, MvPolynomial.eval₂ (φ m hm) x f = 0} : ℚ) / (m : ℚ)
          else 0)
        (PowerSeries.exp ℚ) * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ) :=
  sorry

/-! ## 8. Gauss Class Number Problem (Heilbronn–Siegel, `h(ℚ(√(-d))) → ∞`) -/

/-- For every `M : ℕ`, there exists `D₀ : ℕ` such that every squarefree `d ≥ D₀` satisfies
`M ≤ NumberField.classNumber (AdjoinRoot (X ^ 2 + d))`. -/
theorem gauss_class_number_problem :
    ∀ M : ℕ, ∃ D₀ : ℕ, ∀ (d : ℕ)
      [Fact (Irreducible (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)))],
      D₀ ≤ d → Squarefree d →
      M ≤ NumberField.classNumber (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (d : ℚ))) :=
  sorry

/-! ## 9. General `n`-Variable Hasse–Minkowski Theorem over `ℚ` -/

/-- For every `n : ℕ` and every nondegenerate `QuadraticForm ℚ (Fin n → ℚ)`, `Q` is isotropic
over `ℚ` iff `Q` is isotropic over `ℝ` and over `ℚ_[p]` for every prime `p`. -/
theorem hasse_minkowski_general {n : ℕ} (Q : QuadraticForm ℚ (Fin n → ℚ))
    (hnd : Q.Nondegenerate) :
    (∃ v : Fin n → ℚ, v ≠ 0 ∧ Q v = 0) ↔
      (∃ v : ℝ ⊗[ℚ] (Fin n → ℚ), v ≠ 0 ∧ Q.baseChange ℝ v = 0) ∧
      (∀ p : ℕ, [Fact p.Prime] →
        ∃ v : ℚ_[p] ⊗[ℚ] (Fin n → ℚ), v ≠ 0 ∧ Q.baseChange ℚ_[p] v = 0) :=
  sorry

/-! ## 10. Hilbert Class Field & Artin Reciprocity Isomorphism -/

section HilbertClassField
universe u

/-- For every number field `K` and algebraically closed field `Ω / K`, there exists a finite
abelian Galois extension `H / K` inside `Ω` whose Galois group is isomorphic to the ideal
class group `ClassGroup (𝓞 K)`. -/
theorem hilbert_class_field_artin
    (K : Type u) [Field K] [NumberField K]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] :
    ∃ H : IntermediateField K Ω,
      FiniteDimensional K H ∧ IsGalois K H ∧
      (∀ σ τ : H ≃ₐ[K] H, σ * τ = τ * σ) ∧
      Nonempty (ClassGroup (NumberField.RingOfIntegers K) ≃* (H ≃ₐ[K] H)) :=
  sorry

end HilbertClassField

/-! ## 11. Siegel's `L(1, χ)` Lower Bound (`0` Exceptions) -/

/-- For every `ε > 0`, there exists `C > 0` such that every primitive real non-principal
Dirichlet character `χ` modulo `q` satisfies `C / q ^ ε ≤ (DirichletCharacter.LFunction χ 1).re`. -/
theorem siegel_l1_lower_bound :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
          C / (q : ℝ) ^ ε ≤ (DirichletCharacter.LFunction χ 1).re :=
  sorry

/-! ## 12. Bochner–Kodaira–Nakano Negative-Weight Vanishing -/

/-- Every level-1 modular form and cusp form of strictly negative weight `k < 0` is zero. -/
theorem bochner_negative_weight_vanishing :
    (∀ {k : ℤ}, k < 0 →
      ∀ f : ModularForm (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ).range k, f = 0) ∧
    (∀ {k : ℤ}, k < 0 →
      ∀ f : CuspForm (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ).range k, f = 0) :=
  sorry
