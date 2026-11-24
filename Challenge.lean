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
import Mathlib.Computability.NFA
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Antichain
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Topology.ContinuousOn

open scoped TensorProduct

/-!
# Arithmetica4 — Trustless Unconditional Landmark Challenge Specification

This file imports **only upstream Mathlib** (`0` `RHDirect` imports, `0` `Prize` imports,
`0` `PrimeGaps` imports, `0` `MaynardDock` imports) and introduces **zero custom definitions**.
Every mathematical symbol in every theorem below comes directly from Mathlib.

To verify `Solution.lean` against this file without trusting any intermediate module, run:
```sh
lake env lean --run scripts/verify_challenge.lean
```
This checks that all **46** theorems below are proved in `Solution.lean` with identical universe
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

/-! ## 13. Zhi-Wei Sun's Prime-Shifted Unit Fractions Conjecture (PPL 024, Bloom) -/

/-- Every positive rational number is a finite sum of `1 / (p + d)` over distinct primes `p`,
for both `d = -1` and `d = +1`. -/
theorem sun_prime_shifted_unit_fractions (r : ℚ) (hr : 0 < r) (d : ℤ)
    (hd : d ∈ ({-1, 1} : Set ℤ)) :
    ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧
      r = ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) + (d : ℚ)) :=
  sorry

/-! ## 14. Benkoski–Erdős (1974) Positive Lower Density of Weird Numbers (PPL 086) -/

open Classical in
/-- Weird numbers (abundant, non-pseudoperfect integers) have positive lower asymptotic density. -/
theorem weird_positive_lower_density :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ≤ (((Finset.Icc 1 N).filter (fun n =>
        (0 < n ∧ 2 * n ≤ ∑ d ∈ n.divisors, d) ∧
        ¬ (0 < n ∧ ∃ S : Finset ℕ, S ⊆ n.properDivisors ∧ ∑ d ∈ S, d = n))).card : ℝ) :=
  sorry

/-! ## 15. Erdős #708 Split-Clique Lower Bound (PPL 176) -/

/-- Sharper Erdős–Surányi divisibility-matching lower bound `g(n) ≥ 2n - √(6n) - 2`. -/
theorem erdos_708_split_clique_lower (n : ℕ) (hn : 1 ≤ n) :
    ∀ k : ℕ, (k : ℝ) < 2 * (n : ℝ) - Real.sqrt (6 * (n : ℝ)) - 2 →
      ¬ (∀ (A : Finset ℕ) (hA : A.Nonempty), (A.card = n ∧ ∀ a ∈ A, 2 ≤ a) →
        ∀ x : ℕ, ∃ B ⊆ Finset.Icc (x + 1) (x + A.max' hA),
          B.card ≤ k ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b)) :=
  sorry

/-! ## 16–17. Hager's Sharper Gauss–Legendre & Radau Reverse-Markov Inequalities (PPL 031) -/

/-- Hager's unproved 2015 sharper Gauss–Legendre reverse-Markov bound `|p(τᵢ)| ≤ 1 + τ_{n-1}`. -/
theorem hager_gauss_legendre_sharp
    (n : ℕ) (hn : 1 ≤ n)
    (P : Polynomial ℝ) (hPdeg : P.natDegree = n)
    (hPorth : ∀ q : Polynomial ℝ, q.natDegree < n →
      ∫ t in (-1 : ℝ)..1, P.eval t * q.eval t = 0)
    (τ : Fin n → ℝ) (hτmono : StrictMono τ) (hτroots : ∀ i : Fin n, P.eval (τ i) = 0)
    (p : Polynomial ℝ) (hpdeg : p.natDegree ≤ n) (hp_m1 : p.eval (-1) = 0)
    (hderiv : ∀ i : Fin n, |p.derivative.eval (τ i)| ≤ 1) :
    ∀ i : Fin n, |p.eval (τ i)| ≤ 1 + τ ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ :=
  sorry

/-- Hager's companion Radau reverse-Markov bound `|p(τᵢ)| ≤ 2`. -/
theorem hager_radau_bound
    (n : ℕ) (hn : 1 ≤ n)
    (R : Polynomial ℝ) (hRdeg : R.natDegree = n) (hR1 : R.eval 1 = 0)
    (hRorth : ∀ q : Polynomial ℝ, q.natDegree < n - 1 →
      ∫ t in (-1 : ℝ)..1, R.eval t * q.eval t = 0)
    (τ : Fin n → ℝ) (hτmono : StrictMono τ) (hτroots : ∀ i : Fin n, R.eval (τ i) = 0)
    (p : Polynomial ℝ) (hpdeg : p.natDegree ≤ n) (hp_m1 : p.eval (-1) = 0)
    (hderiv : ∀ i : Fin n, |p.derivative.eval (τ i)| ≤ 1) :
    ∀ i : Fin n, |p.eval (τ i)| ≤ 2 :=
  sorry

/-! ## 18–25. World-Record & Classical Quantitative Bounds (`PPL*` Milestones) -/

/-- Erdős #711 (PPL 173): `max_m f(n, m) ≤ 13 n^{10/7} + 2`, breaking `O(n^{3/2})`. -/
theorem erdos_711_upper_bound (n m : ℕ) (hn : 1 ≤ n) :
    ((sInf ({ L : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k < m + L ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ)
      ≤ 13 * (n : ℝ) ^ ((10 : ℝ) / 7) + 2 :=
  sorry

/-- Shallit #3 (PPL 090 / 121): NFA separating words upper bound `m ≤ 128 n^{1/3} (log n)^{2/3}`. -/
theorem nfa_separating_words_bound {α : Type*} (w x : List α)
    (hlen : w.length = x.length) (hne : w ≠ x) (hn : 2 ≤ w.length) :
    ∃ (m : ℕ) (M : NFA α (Fin m)),
      ((w ∈ M.accepts ∧ x ∉ M.accepts) ∨ (x ∈ M.accepts ∧ w ∉ M.accepts)) ∧
      (m : ℝ) ≤ 128 * (w.length : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (w.length : ℝ)) ^ ((2 : ℝ) / 3) :=
  sorry

/-- Diagonal Ramsey exponential improvement `R(k, k) ≤ (399 / 100)^k` for large `k` (PPL 042). -/
theorem ramsey_diagonal_exponential_improvement :
    ∃ L₀ : ℕ, ∀ k ≥ L₀,
      ((sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree k ∧ Gᶜ.CliqueFree k)} : ℕ) : ℝ) ≤
        (399 / 100 : ℝ) ^ k :=
  sorry

/-- Quantitative Roth (1953) theorem: `r₃(N) ≤ 100 N / log(log N)` for large `N` (PPL 123). -/
theorem roth_three_ap_quantitative :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ((sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
        (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} : ℕ) : ℝ) ≤
        100 * (N : ℝ) / Real.log (Real.log (N : ℝ)) :=
  sorry

/-- Rankin (1961) general-`k` progression-free lower bound (PPL 123). -/
theorem rankin_general_k_ap_free_lower (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) * Real.exp (-C * (Real.log (N : ℝ)) ^ ((1 : ℝ) / (Nat.clog 2 k : ℝ))) ≤
        (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
          (∀ a d : ℕ, 0 < d → ¬ ∀ i < k, a + i * d ∈ A) ∧ A.card = m} : ℕ) :=
  sorry

/-- Ruzsa (1998) infinite Sidon set achieving `|A ∩ [1, N]| ≥ N^{√2 - 1 - ε}` (PPL 124). -/
theorem ruzsa_1998_infinite_sidon :
    ∃ A : Set ℕ, A.Infinite ∧
      (∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ A, ∀ b₂ ∈ A,
        a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (N : ℝ) ^ (Real.sqrt 2 - 1 - ε) ≤ ((A ∩ Set.Icc 1 N).ncard : ℝ) :=
  sorry

/-- Sidon `B₃` upper bound strictly improving Green (2001)'s `(7/2)^{1/3}` to `(699/200)^{1/3}` (PPL 088). -/
theorem sidon_b3_upper_bound_beats_green :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
        (∀ m₁ m₂ : Multiset ℕ,
          m₁.card = 3 → m₂.card = 3 →
          (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
          m₁.sum = m₂.sum → m₁ = m₂) →
        (A.card : ℝ) ≤ (((699 / 200 : ℝ) ^ ((1 : ℝ) / 3)) + ε) * (N : ℝ) ^ ((1 : ℝ) / 3) :=
  sorry

/-- Unitary perfect numbers: sharper double-exponential bound `n < 3^{2^{ω(n)-1}}` for `n ≠ 90` (PPL 133). -/
theorem unitary_perfect_sharper_upper_bound (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n)
    (hne90 : n ≠ 90) :
    n < 3 ^ (2 ^ (n.primeFactors.card - 1)) :=
  sorry

/-! ## 26–45. `Arith4Ext_*` Tier A Combinatorial, Analytic & Topological Landmarks -/

/-- Alon's Combinatorial Nullstellensatz (`Arith4Ext_AlgebraicMethod`). -/
theorem combinatorial_nullstellensatz {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [IsDomain R] [DecidableEq R]
    (f : MvPolynomial ι R) (t : ι → ℕ) (S : ι → Finset R)
    (hdeg : f.totalDegree ≤ ∑ i : ι, t i)
    (hcoeff : f.coeff (∑ i : ι, t i • Finsupp.single i 1) ≠ 0)
    (hcard : ∀ i : ι, t i < (S i).card) :
    ∃ x : ι → R, (∀ i : ι, x i ∈ S i) ∧ MvPolynomial.eval x f ≠ 0 :=
  sorry

/-- Cauchy–Davenport theorem over `ℤ / pℤ` (`Arith4Ext_AlgebraicMethod`). -/
theorem cauchy_davenport {p : ℕ} [Fact p.Prime] (A B : Finset (ZMod p))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.card + B.card - 1) ≤ ((A ×ˢ B).image (fun x => x.1 + x.2)).card :=
  sorry

/-- Chevalley–Warning theorem over `ℤ / pℤ` (`Arith4Ext_AlgebraicMethod`). -/
theorem chevalley_warning {p : ℕ} [Fact p.Prime] {n : ℕ}
    (fs : List (MvPolynomial (Fin n) (ZMod p)))
    (hdeg : (fs.map MvPolynomial.totalDegree).sum < n) :
    p ∣ (Finset.univ.filter (fun x : Fin n → ZMod p => ∀ f ∈ fs, MvPolynomial.eval x f = 0)).card :=
  sorry

/-- Pólya–Vinogradov character sum inequality (`Arith4Ext_SieveCharacters`). -/
theorem polya_vinogradov {q : ℕ} (hq : 2 ≤ q) [NeZero q]
    (χ : MulChar (ZMod q) ℂ) (hχ : DirichletCharacter.IsPrimitive χ) (M N : ℕ) :
    ‖∑ n ∈ Finset.Icc M (M + N - 1), χ (n : ZMod q)‖ ≤
      Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 1) :=
  sorry

/-- Brun–Titchmarsh interval upper bound (`Arith4Ext_SieveCharacters`). -/
theorem brun_titchmarsh_interval (M N : ℕ) (hN : 2 ≤ N) :
    (((Finset.Icc (M + 1) (M + N)).filter Nat.Prime).card : ℝ) ≤
      9 * (N : ℝ) / Real.log (N : ℝ) :=
  sorry

/-- Ajtai–Szemerédi Corners Theorem via triangle removal (`Arith4Ext_SzemerediRegularity`). -/
theorem corners_theorem (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset (ℕ × ℕ),
      A ⊆ Finset.range N ×ˢ Finset.range N →
      δ * (N : ℝ) ^ 2 ≤ (A.card : ℝ) →
      ∃ (x y x' y' : ℕ), (x, y) ∈ A ∧ (x', y) ∈ A ∧ (x, y') ∈ A ∧
        x' ≠ x ∧ (x' : ℤ) - (x : ℤ) = (y' : ℤ) - (y : ℤ) :=
  sorry

section ConvexOpt
open scoped Matrix

/-- Farkas' Lemma (`Arith4Ext_ConvexOptDuality`). -/
theorem farkas_lemma {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ A.mulVec x = b) ↔
      ¬ (∃ y : Fin m → ℝ, (∀ j, 0 ≤ (Aᵀ.mulVec y) j) ∧ y ⬝ᵥ b < 0) :=
  sorry

/-- Von Neumann Minimax Theorem (1928) (`Arith4Ext_ConvexOptDuality`). -/
theorem von_neumann_minimax {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ vStar : ℝ,
      (∃ pStar : Fin m → ℝ, (∀ i, 0 ≤ pStar i) ∧ ∑ i, pStar i = 1 ∧
        ∀ q : Fin n → ℝ, (∀ j, 0 ≤ q j) → ∑ j, q j = 1 → vStar ≤ pStar ⬝ᵥ A.mulVec q) ∧
      (∃ qStar : Fin n → ℝ, (∀ j, 0 ≤ qStar j) ∧ ∑ j, qStar j = 1 ∧
        ∀ p : Fin m → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → p ⬝ᵥ A.mulVec qStar ≤ vStar) :=
  sorry

/-- Birkhoff–von Neumann doubly-stochastic matrix decomposition (`Arith4Ext_ConvexOptDuality`). -/
theorem birkhoff_von_neumann {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hnonneg : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, ∑ j : Fin n, M i j = 1)
    (hcol : ∀ j, ∑ i : Fin n, M i j = 1) :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧ (∑ σ : Equiv.Perm (Fin n), w σ = 1) ∧
        M = ∑ σ : Equiv.Perm (Fin n), w σ • Matrix.of (fun i j => if σ i = j then (1 : ℝ) else 0) :=
  sorry

end ConvexOpt

/-- Dilworth's Poset Chain Decomposition Theorem (`Arith4Ext_ConvexOptDuality`). -/
theorem dilworth_theorem {P : Type*} [PartialOrder P] [DecidableEq P] (S : Finset P) :
    ∃ k : ℕ,
      (∃ U ⊆ S, IsAntichain (· ≤ ·) (U : Set P) ∧ U.card = k) ∧
      (∀ U ⊆ S, IsAntichain (· ≤ ·) (U : Set P) → U.card ≤ k) ∧
      (∃ 𝒞 : Finset (Finset P), 𝒞.card ≤ k ∧
        (∀ C ∈ 𝒞, IsChain (· ≤ ·) (C : Set P)) ∧ S ⊆ 𝒞.biUnion id) :=
  sorry

/-- Sperner's Antichain Theorem (`Arith4Ext_SetSystemsCorrelation`). -/
theorem sperner_theorem {n : ℕ} (ℱ : Finset (Finset (Fin n)))
    (hAnti : ∀ A ∈ ℱ, ∀ B ∈ ℱ, A ⊆ B → A = B) :
    ℱ.card ≤ Nat.choose n (n / 2) :=
  sorry

/-- Erdős–Ko–Rado Theorem (`Arith4Ext_SetSystemsCorrelation`). -/
theorem erdos_ko_rado {n k : ℕ} (hk : 1 ≤ k) (hkn : 2 * k ≤ n)
    (ℱ : Finset (Finset (Fin n)))
    (hunif : ∀ A ∈ ℱ, A.card = k)
    (hinter : ∀ A ∈ ℱ, ∀ B ∈ ℱ, ¬ Disjoint A B) :
    ℱ.card ≤ Nat.choose (n - 1) (k - 1) :=
  sorry

/-- Sauer–Shelah VC-Dimension Lemma (`Arith4Ext_SetSystemsCorrelation`). -/
theorem sauer_shelah {n d : ℕ} (ℱ : Finset (Finset (Fin n)))
    (hno : ∀ S : Finset (Fin n), d < S.card →
      ¬ (∀ T ⊆ S, ∃ A ∈ ℱ, A ∩ S = T)) :
    ℱ.card ≤ ∑ k ∈ Finset.range (d + 1), Nat.choose n k :=
  sorry

open scoped Pointwise in
/-- 1D Brunn–Minkowski Inequality (`Arith4Ext_MeasureConvex`). -/
theorem brunn_minkowski_1d {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hneA : A.Nonempty) (hneB : B.Nonempty) :
    MeasureTheory.volume A + MeasureTheory.volume B ≤ MeasureTheory.volume (A + B) :=
  sorry

/-- Van der Waerden's Theorem (`Arith4Ext_RamseyCombinatorics`). -/
theorem van_der_waerden_theorem (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    ∃ N : ℕ, ∀ (c : ℕ → Fin r),
      ∃ (a d : ℕ), 0 < d ∧ a + (k - 1) * d < N ∧
        ∃ col : Fin r, ∀ j : Fin k, c (a + j.1 * d) = col :=
  sorry

/-- Schur's Ramsey Theorem (`Arith4Ext_RamseyCombinatorics`). -/
theorem schur_theorem {r N : ℕ} (hr : 1 ≤ r) (hN : 3 * Nat.factorial r - 1 ≤ N)
    (c : ℕ → Fin r) :
    ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ y ∧ z ≤ N ∧ x + y = z ∧ c x = c y ∧ c y = c z :=
  sorry

/-- Brouwer Fixed Point Theorem on the standard `d`-simplex (`Arith4Ext_TopologicalComb`). -/
theorem brouwer_fixed_point_simplex (d : ℕ)
    (f : (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ))
    (hf_cont : ContinuousOn f {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1})
    (hf_maps : Set.MapsTo f {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}
      {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}) :
    ∃ x : Fin (d + 1) → ℝ, (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧ f x = x :=
  sorry

/-- Lovász's Kneser Graph Chromatic Number Lower Bound (`Arith4Ext_TopologicalComb`). -/
theorem kneser_no_coloring_lt (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (col : Finset (Fin n) → Fin (n - 2 * k + 1)) :
    ¬ ∀ A B : Finset (Fin n), A.card = k → B.card = k → Disjoint A B → col A ≠ col B :=
  sorry

/-- Two-sided non-asymptotic Stirling–Robbins factorial bounds (`Arith4Ext_GeneratingFunctions`). -/
theorem stirling_factorial_bounds (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (2 * Real.pi * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n *
        Real.exp (1 / (12 * (n : ℝ) + 1)) ≤ (n.factorial : ℝ) ∧
      (n.factorial : ℝ) ≤
        Real.sqrt (2 * Real.pi * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n *
          Real.exp (1 / (12 * (n : ℝ))) :=
  sorry

/-- Non-vanishing of `ζ(1 + it)` on the 1-line (`Arith4Ext_ZetaLFunctions`). -/
theorem riemannZeta_ne_zero_on_re_one (t : ℝ) :
    riemannZeta (1 + (t : ℂ) * Complex.I) ≠ 0 :=
  sorry
