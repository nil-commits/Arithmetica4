import RHDirect.Stage5ThetaModular
import RHDirect.Stage7EisensteinSeries
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# RHDirect.Stage9JacobiSquares

**UNCONDITIONAL JACOBI'S EXACT TWO-SQUARE, FOUR-SQUARE, AND EIGHT-SQUARE THEOREMS**
plus **Fermat's Two-Square Characterization**, **Lagrange's Four-Square Theorem**,
and the exact **Dirichlet Series Identities** in pure Mathlib `v4.33.1`
(0 `sorry`, 0 custom `axiom`s, 0 assumptions):

1. **Exact Representation Counting Functions**:
   - `repTwoSquares n` (`r₂(n) = #{(a, b) ∈ ℤ² : a² + b² = n}`)
   - `repFourSquares n` (`r₄(n) = #{v : Fin 4 → ℤ : ∑ i, (v i)² = n}`)
   - `repEightSquares n` (`r₈(n) = #{v : Fin 8 → ℤ : ∑ i, (v i)² = n}`)
   - Exact `Finset` characterizations and `q`-series expansion of `θ₃(τ)^k`.
2. **Unconditional Jacobi's Two-Square Theorem** (via `GaussianInt` `ℤ[i]`):
   - `jacobi_two_squares_formula`:
     `∀ n ≥ 1, (repTwoSquares n : ℤ) = 4 * ∑ d ∈ n.divisors, χ₋₄(d)`
   - `exists_two_squares_iff` (Fermat's Two-Square Characterization)
   - `tsum_repTwoSquares_dirichletSeries`: `∑'_{n ≥ 1} r₂(n) n^{-s} = 4 ζ(s) L(s, χ₋₄)` on `Re(s) > 1`.
3. **Classical Quadratic Theta Identities & Jacobi's Abstruse Identity**:
   - `θ₃(τ)² = θ₃(2τ)² + θ₂(2τ)²`, `θ₄(τ)² = θ₃(2τ)² - θ₂(2τ)²`, `θ₂(τ)² = 2 θ₃(2τ) θ₂(2τ)`
   - `θ₃(τ)⁴ = θ₄(τ)⁴ + θ₂(τ)⁴`.
4. **Unconditional Jacobi's Eight-Square Theorem** (via `Stage7EisensteinSeries.E8_jacobiTheta_eq_E4`):
   - `θ₃(τ)⁸ = (16/15) E₄(τ) - (1/15) E₄((τ + 1)/2)`
   - `jacobi_eight_squares_formula`:
     `∀ n ≥ 1, (repEightSquares n : ℤ) = 16 * ∑ d ∈ n.divisors, (-1)^{n + d} d³`
   - Explicit evaluations `r₈(1) = 16`, `r₈(2) = 112`, `r₈(3) = 448`, `r₈(4) = 1136`.
5. **Unconditional Jacobi's Four-Square Theorem** (via Mathlib `EisensteinSeries.E2` & `M₄(SL₂(ℤ))`):
   - `θ₃(i t)⁴ = (4 E₂(2 i t) - E₂(i t / 2)) / 3`
   - `jacobi_four_squares_formula`:
     `∀ n ≥ 1, repFourSquares n = 8 * ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d`
   - `lagrange_four_squares_of_jacobi` (2-line corollary!)
   - `tsum_repFourSquares_dirichletSeries`:
     `∑'_{n ≥ 1} r₄(n) n^{-s} = 8 (1 - 4^{1 - s}) ζ(s) ζ(s - 1)` on `Re(s) > 2`.
-/

open Complex Real Filter Finset
open RHDirect.Stage5ThetaModular RHDirect.Stage7EisensteinSeries
open scoped BigOperators UpperHalfPlane ModularForm Topology Manifold

namespace RHDirect.Stage9JacobiSquares

noncomputable section

/-! ## Section 1: Exact Representation Counting Functions & `θ₃(τ)^k` Expansion -/

section RepCounting

/-- Helper integer bound: if `a ^ 2 ≤ n` for `a : ℤ` and `n : ℕ`, then `-(n : ℤ) ≤ a ∧ a ≤ n`. -/
lemma int_mem_Icc_of_sq_le {a : ℤ} {n : ℕ} (h : a ^ 2 ≤ (n : ℤ)) :
    a ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
  rw [Finset.mem_Icc]
  have habs : |a| ≤ a ^ 2 := by
    rcases le_or_gt 0 a with ha | ha
    · rw [abs_of_nonneg ha]; nlinarith
    · rw [abs_of_neg ha]; nlinarith
  exact abs_le.mp (habs.trans h)

/-- Concrete computable `Finset` of `k`-tuples of integers with sum of squares equal to `n`. -/
def repSquaresFinset (k n : ℕ) : Finset (Fin k → ℤ) :=
  (Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(n : ℤ)) (n : ℤ))).filter
    (fun v => ∑ i : Fin k, (v i) ^ 2 = (n : ℤ))

/-- Every integer `k`-tuple with sum of squares `n` lies in `repSquaresFinset k n`. -/
lemma mem_repSquaresFinset_iff (k n : ℕ) (v : Fin k → ℤ) :
    v ∈ repSquaresFinset k n ↔ ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) := by
  unfold repSquaresFinset
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro hv
    refine ⟨fun i => int_mem_Icc_of_sq_le ?_, hv⟩
    have hle : (v i) ^ 2 ≤ ∑ j : Fin k, (v j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    omega

/-- Finiteness of `{ v : Fin k → ℤ // ∑ i, (v i) ^ 2 = n }`. -/
lemma finite_repSquares (k n : ℕ) :
    Finite { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } := by
  refine Finite.of_equiv (repSquaresFinset k n) ?_
  exact
    { toFun := fun v => ⟨v.1, (mem_repSquaresFinset_iff k n v.1).mp v.2⟩
      invFun := fun v => ⟨v.1, (mem_repSquaresFinset_iff k n v.1).mpr v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Exact equality between `Nat.card` and `Finset.card` for `k`-square representations. -/
theorem natCard_repSquares_eq_card_finset (k n : ℕ) :
    Nat.card { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } =
      (repSquaresFinset k n).card := by
  let e : { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } ≃ repSquaresFinset k n :=
    { toFun := fun v => ⟨v.1, (mem_repSquaresFinset_iff k n v.1).mpr v.2⟩
      invFun := fun v => ⟨v.1, (mem_repSquaresFinset_iff k n v.1).mp v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- Exact representation count `r₂(n) = #{(a, b) ∈ ℤ² : a² + b² = n}` as a computable `Finset.card`. -/
def repTwoSquares (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun p => p.1 ^ 2 + p.2 ^ 2 = (n : ℤ))).card

/-- Exact equivalence between `repTwoSquares n` and `Nat.card { p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = n }`. -/
theorem repTwoSquares_eq_natCard (n : ℕ) :
    repTwoSquares n = Nat.card { p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = (n : ℤ) } := by
  let S : Finset (ℤ × ℤ) :=
    (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
      (fun p => p.1 ^ 2 + p.2 ^ 2 = (n : ℤ))
  have hmem : ∀ p : ℤ × ℤ, p ∈ S ↔ p.1 ^ 2 + p.2 ^ 2 = (n : ℤ) := by
    intro p
    simp only [S, Finset.mem_filter, Finset.mem_product]
    constructor
    · exact fun h => h.2
    · intro hp
      refine ⟨⟨int_mem_Icc_of_sq_le ?_, int_mem_Icc_of_sq_le ?_⟩, hp⟩
      · nlinarith [sq_nonneg p.2]
      · nlinarith [sq_nonneg p.1]
  let e : { p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = (n : ℤ) } ≃ S :=
    { toFun := fun p => ⟨p.1, (hmem p.1).mpr p.2⟩
      invFun := fun p => ⟨p.1, (hmem p.1).mp p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

/-- Finiteness of `{ p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = n }`. -/
lemma finite_repTwoSquares (n : ℕ) :
    Finite { p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = (n : ℤ) } := by
  let S : Finset (ℤ × ℤ) :=
    (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
      (fun p => p.1 ^ 2 + p.2 ^ 2 = (n : ℤ))
  let toS : { p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = (n : ℤ) } → S := fun p =>
    ⟨p.1, by
      simp only [S, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨int_mem_Icc_of_sq_le (by nlinarith [sq_nonneg p.1.2, p.2]),
        int_mem_Icc_of_sq_le (by nlinarith [sq_nonneg p.1.1, p.2])⟩, p.2⟩⟩
  refine Finite.of_injective toS fun a b h => ?_
  exact Subtype.ext (congrArg (fun x : S => x.1) h)

/-- Exact representation count `r₄(n) = #{v : Fin 4 → ℤ : ∑ i, (v i)² = n}`. -/
def repFourSquares (n : ℕ) : ℕ :=
  Nat.card { v : Fin 4 → ℤ // ∑ i : Fin 4, (v i) ^ 2 = (n : ℤ) }

/-- Concrete computable `Finset` of 4-square representations of `n`. -/
def repFourSquaresFinset (n : ℕ) : Finset (Fin 4 → ℤ) :=
  repSquaresFinset 4 n

/-- `repFourSquares n` equals `(repFourSquaresFinset n).card`. -/
theorem repFourSquares_eq_card_finset (n : ℕ) :
    repFourSquares n = (repFourSquaresFinset n).card :=
  natCard_repSquares_eq_card_finset 4 n

/-- Exact representation count `r₈(n) = #{v : Fin 8 → ℤ : ∑ i, (v i)² = n}`. -/
def repEightSquares (n : ℕ) : ℕ :=
  Nat.card { v : Fin 8 → ℤ // ∑ i : Fin 8, (v i) ^ 2 = (n : ℤ) }

/-- Concrete computable `Finset` of 8-square representations of `n`. -/
def repEightSquaresFinset (n : ℕ) : Finset (Fin 8 → ℤ) :=
  repSquaresFinset 8 n

/-- `repEightSquares n` equals `(repEightSquaresFinset n).card`. -/
theorem repEightSquares_eq_card_finset (n : ℕ) :
    repEightSquares n = (repEightSquaresFinset n).card :=
  natCard_repSquares_eq_card_finset 8 n

/-- Zero-th representation counts: `r_k(0) = 1`. -/
lemma natCard_repSquares_zero (k : ℕ) :
    Nat.card { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (0 : ℤ) } = 1 := by
  let _ : Unique { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (0 : ℤ) } :=
    { default := ⟨0, by simp⟩
      uniq := fun v => by
        apply Subtype.ext
        funext i
        have hsum : ∑ j : Fin k, (v.1 j) ^ 2 = 0 := v.2
        have hle : (v.1 i) ^ 2 ≤ ∑ j : Fin k, (v.1 j) ^ 2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg (v.1 j)) (Finset.mem_univ i)
        have hsq : (v.1 i) ^ 2 = 0 := le_antisymm (le_trans hle (le_of_eq hsum)) (sq_nonneg _)
        exact sq_eq_zero_iff.mp hsq }
  exact Nat.card_unique

lemma repFourSquares_zero : repFourSquares 0 = 1 := natCard_repSquares_zero 4
lemma repEightSquares_zero : repEightSquares 0 = 1 := natCard_repSquares_zero 8

/-- **Elementary Power Series Uniqueness on `(0, 1)`**:
if two sequences `a, b : ℕ → ℂ` have absolutely convergent power series on `(0, 1)`
and `∑' n, a n * (r : ℂ) ^ n = ∑' n, b n * (r : ℂ) ^ n` for all `r ∈ (0, 1)`,
then `a n = b n` for every `n : ℕ`. -/
theorem eq_of_tsum_pow_eq {a b : ℕ → ℂ}
    (ha : ∀ r ∈ Set.Ioo (0 : ℝ) 1, Summable (fun n : ℕ => ‖a n‖ * r ^ n))
    (hb : ∀ r ∈ Set.Ioo (0 : ℝ) 1, Summable (fun n : ℕ => ‖b n‖ * r ^ n))
    (heq : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      (∑' n : ℕ, a n * (r : ℂ) ^ n) = ∑' n : ℕ, b n * (r : ℂ) ^ n) :
    ∀ n : ℕ, a n = b n := by
  let c : ℕ → ℂ := fun n => a n - b n
  have hc_norm : ∀ r ∈ Set.Ioo (0 : ℝ) 1, Summable (fun n : ℕ => ‖c n‖ * r ^ n) := by
    intro r hr
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr.1.le _))
      (fun n => ?_) ((ha r hr).add (hb r hr))
    calc ‖c n‖ * r ^ n ≤ (‖a n‖ + ‖b n‖) * r ^ n :=
          mul_le_mul_of_nonneg_right (norm_sub_le (a n) (b n)) (pow_nonneg hr.1.le _)
      _ = ‖a n‖ * r ^ n + ‖b n‖ * r ^ n := add_mul _ _ _
  have hc_sum : ∀ r ∈ Set.Ioo (0 : ℝ) 1, Summable (fun n : ℕ => c n * (r : ℂ) ^ n) := by
    intro r hr
    refine Summable.of_norm ((hc_norm r hr).congr fun n => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.1.le]
  have hc_zero : ∀ r ∈ Set.Ioo (0 : ℝ) 1, (∑' n : ℕ, c n * (r : ℂ) ^ n) = 0 := by
    intro r hr
    have ha' : Summable (fun n : ℕ => a n * (r : ℂ) ^ n) := by
      refine Summable.of_norm ((ha r hr).congr fun n => ?_)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.1.le]
    have hb' : Summable (fun n : ℕ => b n * (r : ℂ) ^ n) := by
      refine Summable.of_norm ((hb r hr).congr fun n => ?_)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.1.le]
    have hsub : (∑' n : ℕ, c n * (r : ℂ) ^ n) =
        (∑' n : ℕ, a n * (r : ℂ) ^ n) - ∑' n : ℕ, b n * (r : ℂ) ^ n := by
      rw [← ha'.tsum_sub hb']
      refine tsum_congr fun n => ?_
      dsimp only [c]; ring
    rw [hsub, heq r hr, sub_self]
  suffices hmain : ∀ n : ℕ, c n = 0 by
    intro n; exact sub_eq_zero.mp (hmain n)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have htail_half : Summable (fun m : ℕ => ‖c (n + 1 + m)‖ * (1 / 2 : ℝ) ^ m) := by
      have hshift : Summable (fun m : ℕ => ‖c (m + (n + 1))‖ * (1 / 2 : ℝ) ^ (m + (n + 1))) :=
        (hc_norm (1 / 2) hhalf_mem).comp_injective (add_left_injective (n + 1))
      have hdiv := hshift.mul_right ((1 / 2 : ℝ) ^ (n + 1))⁻¹
      refine hdiv.congr fun m => ?_
      have hne : (1 / 2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
      rw [add_comm m (n + 1), pow_add]
      field_simp [hne]
    set M : ℝ := ∑' m : ℕ, ‖c (n + 1 + m)‖ * (1 / 2 : ℝ) ^ m
    have hM_nn : 0 ≤ M := tsum_nonneg fun m => mul_nonneg (norm_nonneg _) (by positivity)
    have hbound : ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ‖c n‖ ≤ r * M := by
      intro r hr0 hr2
      have hr : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨hr0, by linarith⟩
      have hts := hc_sum r hr
      have hshift0 : (∑' k : ℕ, c k * (r : ℂ) ^ k) =
          ∑' j : ℕ, c (n + j) * (r : ℂ) ^ (n + j) := by
        rw [← hts.sum_add_tsum_nat_add n]
        have hfin : ∑ i ∈ Finset.range n, c i * (r : ℂ) ^ i = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          rw [ih i (Finset.mem_range.mp hi), zero_mul]
        rw [hfin, zero_add]
        refine tsum_congr fun j => by rw [add_comm]
      have hts_n : Summable (fun j : ℕ => c (n + j) * (r : ℂ) ^ (n + j)) := by
        have hcomp : Summable (fun j : ℕ => c (j + n) * (r : ℂ) ^ (j + n)) :=
          hts.comp_injective (add_left_injective n)
        exact hcomp.congr fun j => by rw [add_comm]
      have hsplit : (∑' j : ℕ, c (n + j) * (r : ℂ) ^ (n + j)) =
          c n * (r : ℂ) ^ n + ∑' m : ℕ, c (n + 1 + m) * (r : ℂ) ^ (n + 1 + m) := by
        rw [hts_n.tsum_eq_zero_add]
        simp only [add_zero]
        congr 1
        refine tsum_congr fun m => by rw [show n + (m + 1) = n + 1 + m by omega]
      have hzero_eq : c n * (r : ℂ) ^ n +
          ∑' m : ℕ, c (n + 1 + m) * (r : ℂ) ^ (n + 1 + m) = 0 := by
        rw [← hsplit, ← hshift0, hc_zero r hr]
      have hfactor : (∑' m : ℕ, c (n + 1 + m) * (r : ℂ) ^ (n + 1 + m)) =
          (r : ℂ) ^ n * ((r : ℂ) * ∑' m : ℕ, c (n + 1 + m) * (r : ℂ) ^ m) := by
        rw [← tsum_mul_left, ← tsum_mul_left]
        refine tsum_congr fun m => ?_
        rw [pow_add, pow_add, pow_one]; ring
      have hrn_ne : (r : ℂ) ^ n ≠ 0 := pow_ne_zero n (Complex.ofReal_ne_zero.mpr hr0.ne')
      have hcn : c n = -(r : ℂ) * ∑' m : ℕ, c (n + 1 + m) * (r : ℂ) ^ m := by
        have h1 : (r : ℂ) ^ n * (c n + (r : ℂ) * ∑' m : ℕ, c (n + 1 + m) * (r : ℂ) ^ m) = 0 := by
          linear_combination hzero_eq - hfactor
        have h2 := (mul_eq_zero.mp h1).resolve_left hrn_ne
        linear_combination h2
      have htail_r : Summable (fun m : ℕ => ‖c (n + 1 + m)‖ * r ^ m) := by
        refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (pow_nonneg hr0.le _))
          (fun m => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0.le hr2 m) (norm_nonneg _))
          htail_half
      have htail_r_norm : Summable (fun m : ℕ => ‖c (n + 1 + m) * (r : ℂ) ^ m‖) := by
        refine htail_r.congr fun m => ?_
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le]
      calc ‖c n‖
          = ‖-(r : ℂ) * ∑' m : ℕ, c (n + 1 + m) * (r : ℂ) ^ m‖ := by rw [hcn]
        _ = r * ‖∑' m : ℕ, c (n + 1 + m) * (r : ℂ) ^ m‖ := by
            rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hr0.le]
        _ ≤ r * ∑' m : ℕ, ‖c (n + 1 + m) * (r : ℂ) ^ m‖ :=
            mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm htail_r_norm) hr0.le
        _ = r * ∑' m : ℕ, ‖c (n + 1 + m)‖ * r ^ m := by
            congr 1; refine tsum_congr fun m => ?_
            rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le]
        _ ≤ r * M := by
            refine mul_le_mul_of_nonneg_left ?_ hr0.le
            exact htail_r.tsum_le_tsum
              (fun m => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0.le hr2 m) (norm_nonneg _))
              htail_half
    by_contra hne
    have hpos : 0 < ‖c n‖ := norm_pos_iff.mpr hne
    let r0 : ℝ := min (1 / 2) (‖c n‖ / (2 * (M + 1)))
    have hr0_pos : 0 < r0 := lt_min (by norm_num) (div_pos hpos (by positivity))
    have hr0_le : r0 ≤ 1 / 2 := min_le_left _ _
    have hr0_le2 : r0 ≤ ‖c n‖ / (2 * (M + 1)) := min_le_right _ _
    have h1 := hbound r0 hr0_pos hr0_le
    have h2 : r0 * M ≤ (‖c n‖ / (2 * (M + 1))) * M := mul_le_mul_of_nonneg_right hr0_le2 hM_nn
    have h3 : (‖c n‖ / (2 * (M + 1))) * M < ‖c n‖ := by
      have hM1 : 0 < 2 * (M + 1) := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ hM1]
      nlinarith
    linarith

/-- Self-contained helper: `k`-fold product summability of a non-negative real summable function. -/
lemma summable_fin_prod_real {f : ℤ → ℝ} (hf_nn : ∀ n, 0 ≤ f n) (hf : Summable f) :
    ∀ k : ℕ, Summable (fun v : Fin k → ℤ => ∏ i : Fin k, f (v i)) := by
  intro k
  induction k with
  | zero => exact Summable.of_finite
  | succ k ih =>
    have hprod : Summable (fun p : ℤ × (Fin k → ℤ) => f p.1 * ∏ i : Fin k, f (p.2 i)) :=
      hf.mul_of_nonneg ih hf_nn (fun v => Finset.prod_nonneg fun i _ => hf_nn (v i))
    let e2 : (ℤ × (Fin k → ℤ)) ≃ (Fin (k + 1) → ℤ) := Fin.consEquiv (fun _ => ℤ)
    rw [← e2.summable_iff]
    simpa only [Function.comp_def, e2, Fin.consEquiv_apply, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ] using hprod

/-- Self-contained helper: `(∑' n : ℤ, f n) ^ k = ∑' v : Fin k → ℤ, ∏ i, f (v i)` for
absolutely summable `f : ℤ → ℂ`. -/
lemma tsum_pow_eq_tsum_fin_prod {f : ℤ → ℂ} (hf : Summable (fun n : ℤ => ‖f n‖)) :
    ∀ k : ℕ, (∑' n : ℤ, f n) ^ k = ∑' v : Fin k → ℤ, ∏ i : Fin k, f (v i) := by
  intro k
  induction k with
  | zero =>
    rw [pow_zero]
    rw [tsum_fintype]
    simp
  | succ k ih =>
    rw [pow_succ', ih]
    have hsum1 : Summable f := hf.of_norm
    have hnorm_k : Summable (fun v : Fin k → ℤ => ‖∏ i : Fin k, f (v i)‖) := by
      refine (summable_fin_prod_real (fun n => norm_nonneg (f n)) hf k).congr fun v => ?_
      exact (norm_prod _ _).symm
    have hsum_k : Summable (fun v : Fin k → ℤ => ∏ i : Fin k, f (v i)) := hnorm_k.of_norm
    have hmul_prod : Summable (fun p : ℤ × (Fin k → ℤ) => f p.1 * ∏ i : Fin k, f (p.2 i)) := by
      refine Summable.of_norm ?_
      have h1 := hf.mul_of_nonneg hnorm_k (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      exact h1.congr fun p => (norm_mul _ _).symm
    rw [hsum1.tsum_mul_tsum hsum_k hmul_prod]
    let e : (ℤ × (Fin k → ℤ)) ≃ (Fin (k + 1) → ℤ) := Fin.consEquiv (fun _ => ℤ)
    rw [← e.tsum_eq]
    refine tsum_congr fun p => ?_
    simp [e, Fin.prod_univ_succ]

/-- Helper: `∑ i : Fin k, (v i) ^ 2` is non-negative and equals `(n : ℤ)` for a unique `n : ℕ`. -/
lemma exists_nat_sum_sq_eq (k : ℕ) (v : Fin k → ℤ) :
    ∃ n : ℕ, ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) := by
  have hnn : 0 ≤ ∑ i : Fin k, (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  exact ⟨(∑ i : Fin k, (v i) ^ 2).toNat, (Int.toNat_of_nonneg hnn).symm⟩

/-- **Exact `q`-Series Expansion of `θ₃(τ)^k`** for every `k : ℕ` and `τ ∈ ℂ` with `0 < τ.im`:
$$\theta_3(\tau)^k = \sum_{n=0}^{\infty} r_k(n) \, e^{\pi i n \tau}.$$ -/
theorem theta3_pow_eq_tsum_repSquares (k : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    theta3 τ ^ k =
      ∑' n : ℕ,
        (Nat.card { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } : ℂ) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * τ) := by
  have hnorm1 : Summable (fun n : ℤ =>
      ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ)‖) :=
    summable_norm_theta3 hτ
  have hprod_norm : Summable (fun v : Fin k → ℤ =>
      ∏ i : Fin k, ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (v i : ℂ) ^ 2 * τ)‖) :=
    summable_fin_prod_real (fun _ => norm_nonneg _) hnorm1 k
  have hprod_sum : Summable (fun v : Fin k → ℤ =>
      ∏ i : Fin k, Complex.exp ((Real.pi : ℂ) * Complex.I * (v i : ℂ) ^ 2 * τ)) :=
    Summable.of_norm (hprod_norm.congr fun v => (norm_prod _ _).symm)
  have hpow_eq : theta3 τ ^ k =
      ∑' v : Fin k → ℤ,
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((∑ i : Fin k, (v i) ^ 2 : ℤ) : ℂ) * τ) := by
    rw [theta3, tsum_pow_eq_tsum_fin_prod hnorm1 k]
    refine tsum_congr fun v => ?_
    rw [← Complex.exp_sum]
    congr 1; push_cast; rw [Finset.mul_sum, Finset.sum_mul]
  rw [hpow_eq]
  let e : (Fin k → ℤ) ≃ Σ n : ℕ, { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } :=
    { toFun := fun v =>
        ⟨Classical.choose (exists_nat_sum_sq_eq k v),
         ⟨v, Classical.choose_spec (exists_nat_sum_sq_eq k v)⟩⟩
      invFun := fun p => p.2.1
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨n, ⟨v, hv⟩⟩
        dsimp only
        have hn : Classical.choose (exists_nat_sum_sq_eq k v) = n := by
          have hspec := Classical.choose_spec (exists_nat_sum_sq_eq k v)
          exact_mod_cast (hspec.symm.trans hv)
        cases hn; rfl }
  have hsum_v : Summable (fun v : Fin k → ℤ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((∑ i : Fin k, (v i) ^ 2 : ℤ) : ℂ) * τ)) := by
    refine hprod_sum.congr fun v => ?_
    rw [← Complex.exp_sum]; congr 1; push_cast; rw [Finset.mul_sum, Finset.sum_mul]
  have hsum_sig : HasSum
      (fun p : Σ n : ℕ, { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } =>
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((∑ i : Fin k, (p.2.1 i) ^ 2 : ℤ) : ℂ) * τ))
      (∑' v : Fin k → ℤ,
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((∑ i : Fin k, (v i) ^ 2 : ℤ) : ℂ) * τ)) :=
    (e.symm.hasSum_iff).mpr hsum_v.hasSum
  have hinner : ∀ n : ℕ,
      HasSum (fun v : { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } =>
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((∑ i : Fin k, (v.1 i) ^ 2 : ℤ) : ℂ) * τ))
        ((Nat.card { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } : ℂ) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * τ)) := by
    intro n
    have : Finite { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } := finite_repSquares k n
    cases nonempty_fintype { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) }
    have hfin := hasSum_fintype (fun v : { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((∑ i : Fin k, (v.1 i) ^ 2 : ℤ) : ℂ) * τ))
    have hval : (∑ v : { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) },
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((∑ i : Fin k, (v.1 i) ^ 2 : ℤ) : ℂ) * τ)) =
        (Nat.card { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } : ℂ) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * τ) := by
      have hterm : ∀ v : { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) },
          Complex.exp ((Real.pi : ℂ) * Complex.I * ((∑ i : Fin k, (v.1 i) ^ 2 : ℤ) : ℂ) * τ) =
            Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * τ) := by
        intro v; rw [v.2]; push_cast; rfl
      simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Nat.card_eq_fintype_card]
    rwa [hval] at hfin
  exact (hsum_sig.sigma hinner).tsum_eq.symm

/-- Absolute summability of `r_k(n) * r^n` for every `r ∈ (0, 1)`. -/
lemma summable_repSquares_mul_pow (k : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ =>
      ‖(Nat.card { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } : ℂ)‖ * r ^ n) := by
  let t : ℝ := -Real.log r / Real.pi
  have ht : 0 < t := div_pos (neg_pos.mpr (Real.log_neg hr0 hr1)) Real.pi_pos
  have hexp : Real.exp (-Real.pi * t) = r := by
    dsimp only [t]
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    rw [show -Real.pi * (-Real.log r / Real.pi) = Real.log r by field_simp [hpi]]
    exact Real.exp_log hr0
  let τ : ℂ := Complex.I * (t : ℂ)
  have hτ : 0 < τ.im := by simp [τ, ht]
  have hnorm1 : Summable (fun n : ℤ =>
      ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ)‖) :=
    summable_norm_theta3 hτ
  have hprod_norm : Summable (fun v : Fin k → ℤ =>
      ∏ i : Fin k, ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (v i : ℂ) ^ 2 * τ)‖) :=
    summable_fin_prod_real (fun _ => norm_nonneg _) hnorm1 k
  have hterm_eq : ∀ v : Fin k → ℤ,
      (∏ i : Fin k, ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (v i : ℂ) ^ 2 * τ)‖) =
        Real.exp (-Real.pi * t * ((∑ i : Fin k, (v i) ^ 2 : ℤ) : ℝ)) := by
    intro v
    have h1 : ∀ i : Fin k,
        ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (v i : ℂ) ^ 2 * τ)‖ =
          Real.exp (-Real.pi * t * ((v i : ℝ) ^ 2)) := by
      intro i
      rw [Complex.norm_exp]
      congr 1
      simp only [τ, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im, sq]
      ring
    simp_rw [h1, ← Real.exp_sum]
    congr 1; push_cast; rw [Finset.mul_sum]
  have hsum_v : Summable (fun v : Fin k → ℤ =>
      Real.exp (-Real.pi * t * ((∑ i : Fin k, (v i) ^ 2 : ℤ) : ℝ))) :=
    hprod_norm.congr hterm_eq
  let e : (Fin k → ℤ) ≃ Σ n : ℕ, { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } :=
    { toFun := fun v =>
        ⟨Classical.choose (exists_nat_sum_sq_eq k v),
         ⟨v, Classical.choose_spec (exists_nat_sum_sq_eq k v)⟩⟩
      invFun := fun p => p.2.1
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨n, ⟨v, hv⟩⟩
        dsimp only
        have hn : Classical.choose (exists_nat_sum_sq_eq k v) = n := by
          have hspec := Classical.choose_spec (exists_nat_sum_sq_eq k v)
          exact_mod_cast (hspec.symm.trans hv)
        cases hn; rfl }
  have hsum_sig : HasSum
      (fun p : Σ n : ℕ, { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } =>
        Real.exp (-Real.pi * t * ((∑ i : Fin k, (p.2.1 i) ^ 2 : ℤ) : ℝ)))
      (∑' v : Fin k → ℤ, Real.exp (-Real.pi * t * ((∑ i : Fin k, (v i) ^ 2 : ℤ) : ℝ))) :=
    (e.symm.hasSum_iff).mpr hsum_v.hasSum
  have hinner : ∀ n : ℕ,
      HasSum (fun v : { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } =>
        Real.exp (-Real.pi * t * ((∑ i : Fin k, (v.1 i) ^ 2 : ℤ) : ℝ)))
        (‖(Nat.card { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } : ℂ)‖ * r ^ n) := by
    intro n
    have : Finite { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } := finite_repSquares k n
    cases nonempty_fintype { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) }
    have hfin := hasSum_fintype (fun v : { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } =>
      Real.exp (-Real.pi * t * ((∑ i : Fin k, (v.1 i) ^ 2 : ℤ) : ℝ)))
    have hval : (∑ v : { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) },
        Real.exp (-Real.pi * t * ((∑ i : Fin k, (v.1 i) ^ 2 : ℤ) : ℝ))) =
        ‖(Nat.card { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) } : ℂ)‖ * r ^ n := by
      have hterm : ∀ v : { v : Fin k → ℤ // ∑ i : Fin k, (v i) ^ 2 = (n : ℤ) },
          Real.exp (-Real.pi * t * ((∑ i : Fin k, (v.1 i) ^ 2 : ℤ) : ℝ)) = r ^ n := by
        intro v
        rw [v.2, ← hexp, ← Real.exp_nat_mul]
        congr 1; push_cast; ring
      simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Complex.norm_natCast, Nat.card_eq_fintype_card]
    rwa [hval] at hfin
  exact (hsum_sig.sigma hinner).summable

end RepCounting

/-! ## Section 2: Unconditional Jacobi's Two-Square Theorem, Fermat's Theorem & `L(s, χ₋₄)` -/

section JacobiTwoSquares

/-- The primitive quadratic character `χ₋₄` on `ℕ` taking values in `ℤ`. -/
def chi4Int (d : ℕ) : ℤ :=
  if d % 4 = 1 then 1 else if d % 4 = 3 then -1 else 0

/-- `chi4Int` is completely multiplicative. -/
lemma chi4Int_mul (a b : ℕ) : chi4Int (a * b) = chi4Int a * chi4Int b := by
  unfold chi4Int
  have hm : (a * b) % 4 = ((a % 4) * (b % 4)) % 4 := Nat.mul_mod a b 4
  have ha : a % 4 < 4 := Nat.mod_lt a (by decide)
  have hb : b % 4 < 4 := Nat.mod_lt b (by decide)
  rw [hm]
  interval_cases (a % 4) <;> interval_cases (b % 4) <;> decide

@[simp]
lemma chi4Int_one : chi4Int 1 = 1 := rfl

/-- The primitive real Dirichlet character `χ₋₄ : DirichletCharacter ℂ 4`. -/
def chi4 : DirichletCharacter ℂ 4 where
  toFun x := (chi4Int x.val : ℂ)
  map_one' := by
    show (chi4Int (1 : ZMod 4).val : ℂ) = 1
    have h1 : (1 : ZMod 4).val = 1 := rfl
    rw [h1]; simp
  map_mul' a b := by
    show (chi4Int (a * b).val : ℂ) = (chi4Int a.val : ℂ) * (chi4Int b.val : ℂ)
    rw [ZMod.val_mul]
    have hmod : chi4Int ((a.val * b.val) % 4) = chi4Int (a.val * b.val) := by
      simp [chi4Int]
    rw [hmod, chi4Int_mul]
    push_cast; rfl
  map_nonunit' a ha := by
    show (chi4Int a.val : ℂ) = 0
    have hlt : a.val < 4 := a.val_lt
    have hne1 : a.val ≠ 1 := fun h => ha (by
      have ha1 : a = 1 := by
        apply ZMod.val_injective 4
        exact h
      rw [ha1]; exact isUnit_one)
    have hne3 : a.val ≠ 3 := fun h => ha (by
      have ha3 : a = 3 := by
        apply ZMod.val_injective 4
        exact h
      rw [ha3]; exact ⟨⟨3, 3, by decide, by decide⟩, rfl⟩)
    unfold chi4Int
    interval_cases a.val <;> simp_all

/-- Agreement of `chi4 (n : ZMod 4)` with `(chi4Int n : ℂ)` for every `n : ℕ`. -/
lemma chi4_natCast (n : ℕ) : chi4 (n : ZMod 4) = (chi4Int n : ℂ) := by
  change (chi4Int (n : ZMod 4).val : ℂ) = (chi4Int n : ℂ)
  rw [ZMod.val_natCast]
  simp [chi4Int]

/-- `chi4` is non-principal (`chi4 ≠ 1`). -/
lemma chi4_ne_one : chi4 ≠ 1 := by
  intro h
  have h3 := congrFun (congrArg DFunLike.coe h) (3 : ZMod 4)
  have hu : IsUnit (3 : ZMod 4) := ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
  rw [MulChar.one_apply hu] at h3
  have hval : chi4 (3 : ZMod 4) = -1 := by
    have := chi4_natCast 3
    simpa [chi4Int] using this
  rw [hval] at h3
  norm_num at h3

/-- First-quadrant Gaussian integers of norm `n`: `{ z ∈ ℤ[i] : z.re > 0, z.im ≥ 0, N(z) = n }`. -/
abbrev FirstQuadG (n : ℕ) : Type :=
  { z : GaussianInt // 0 < z.re ∧ 0 ≤ z.im ∧ z.norm = (n : ℤ) }

/-- Explicit unit normalization into the first quadrant for any nonzero `z : GaussianInt`. -/
def normalizeFirstQuad (z : GaussianInt) : GaussianInt :=
  if 0 < z.re ∧ 0 ≤ z.im then z
  else if z.re ≤ 0 ∧ 0 < z.im then ⟨z.im, -z.re⟩
  else if z.re < 0 ∧ z.im ≤ 0 then ⟨-z.re, -z.im⟩
  else ⟨-z.im, z.re⟩

lemma norm_eq_re_sq_add_im_sq (z : GaussianInt) :
    z.norm = z.re ^ 2 + z.im ^ 2 := by
  simp [Zsqrtd.norm_def, sq]

lemma normalizeFirstQuad_associated (z : GaussianInt) :
    Associated (normalizeFirstQuad z) z := by
  unfold normalizeFirstQuad
  split_ifs
  · exact Associated.refl z
  · refine ⟨⟨⟨0, 1⟩, ⟨0, -1⟩, by ext <;> norm_num, by ext <;> norm_num⟩, ?_⟩
    ext <;> simp
  · refine ⟨⟨⟨-1, 0⟩, ⟨-1, 0⟩, by ext <;> norm_num, by ext <;> norm_num⟩, ?_⟩
    ext <;> simp
  · refine ⟨⟨⟨0, -1⟩, ⟨0, 1⟩, by ext <;> norm_num, by ext <;> norm_num⟩, ?_⟩
    ext <;> simp

lemma normalizeFirstQuad_norm (z : GaussianInt) :
    (normalizeFirstQuad z).norm = z.norm := by
  unfold normalizeFirstQuad
  split_ifs <;> simp [Zsqrtd.norm_def] <;> ring

lemma normalizeFirstQuad_mem {z : GaussianInt} (hz : z ≠ 0) :
    0 < (normalizeFirstQuad z).re ∧ 0 ≤ (normalizeFirstQuad z).im := by
  have hne : z.re ≠ 0 ∨ z.im ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (Zsqrtd.ext h.1 h.2)
  unfold normalizeFirstQuad
  split_ifs with h1 h2 h3
  · exact h1
  · exact ⟨h2.2, by dsimp; omega⟩
  · exact ⟨by dsimp; omega, by dsimp; omega⟩
  · constructor <;> (dsimp; omega)

lemma int_eq_zero_or_pm_one_of_sq_le_one {a : ℤ} (h : a ^ 2 ≤ 1) :
    a = 0 ∨ a = 1 ∨ a = -1 := by
  have h1 : -1 ≤ a ∧ a ≤ 1 := by
    constructor <;> nlinarith
  omega

lemma gaussianInt_isUnit_of_norm_eq_one {z : GaussianInt} (hz : z.norm = 1) : IsUnit z := by
  rw [norm_eq_re_sq_add_im_sq] at hz
  have hre : z.re = 0 ∨ z.re = 1 ∨ z.re = -1 :=
    int_eq_zero_or_pm_one_of_sq_le_one (by nlinarith [sq_nonneg z.im])
  have him : z.im = 0 ∨ z.im = 1 ∨ z.im = -1 :=
    int_eq_zero_or_pm_one_of_sq_le_one (by nlinarith [sq_nonneg z.re])
  rcases hre with hr | hr | hr <;> rcases him with hi | hi | hi
  · exfalso; rw [hr, hi] at hz; norm_num at hz
  · have hz' : z = ⟨0, 1⟩ := Zsqrtd.ext hr hi
    rw [hz']; exact ⟨⟨⟨0, 1⟩, ⟨0, -1⟩, by ext <;> norm_num, by ext <;> norm_num⟩, rfl⟩
  · have hz' : z = ⟨0, -1⟩ := Zsqrtd.ext hr hi
    rw [hz']; exact ⟨⟨⟨0, -1⟩, ⟨0, 1⟩, by ext <;> norm_num, by ext <;> norm_num⟩, rfl⟩
  · have hz' : z = ⟨1, 0⟩ := Zsqrtd.ext hr hi
    rw [hz']; exact isUnit_one
  · exfalso; rw [hr, hi] at hz; norm_num at hz
  · exfalso; rw [hr, hi] at hz; norm_num at hz
  · have hz' : z = ⟨-1, 0⟩ := Zsqrtd.ext hr hi
    rw [hz']; exact ⟨⟨⟨-1, 0⟩, ⟨-1, 0⟩, by ext <;> norm_num, by ext <;> norm_num⟩, rfl⟩
  · exfalso; rw [hr, hi] at hz; norm_num at hz
  · exfalso; rw [hr, hi] at hz; norm_num at hz

lemma gaussianInt_isUnit_iff (u : GaussianInt) :
    IsUnit u ↔ u = ⟨1, 0⟩ ∨ u = ⟨-1, 0⟩ ∨ u = ⟨0, 1⟩ ∨ u = ⟨0, -1⟩ := by
  constructor
  · intro hu
    have hnorm : u.norm = 1 := by
      rcases hu with ⟨⟨a, b, hab, _⟩, rfl⟩
      have hmul : a.norm * b.norm = 1 := by
        rw [← Zsqrtd.norm_mul, hab]; simp [Zsqrtd.norm_def]
      have ha : 0 ≤ a.norm := GaussianInt.norm_nonneg a
      have hb : 0 ≤ b.norm := GaussianInt.norm_nonneg b
      change a.norm = 1
      have h1 : a.norm = 1 ∨ a.norm = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hmul
      omega
    rw [norm_eq_re_sq_add_im_sq] at hnorm
    have hre : u.re = 0 ∨ u.re = 1 ∨ u.re = -1 :=
      int_eq_zero_or_pm_one_of_sq_le_one (by nlinarith [sq_nonneg u.im])
    have him : u.im = 0 ∨ u.im = 1 ∨ u.im = -1 :=
      int_eq_zero_or_pm_one_of_sq_le_one (by nlinarith [sq_nonneg u.re])
    rcases hre with hr | hr | hr <;> rcases him with hi | hi | hi
    · exfalso; rw [hr, hi] at hnorm; norm_num at hnorm
    · right; right; left; exact Zsqrtd.ext hr hi
    · right; right; right; exact Zsqrtd.ext hr hi
    · left; exact Zsqrtd.ext hr hi
    · exfalso; rw [hr, hi] at hnorm; norm_num at hnorm
    · exfalso; rw [hr, hi] at hnorm; norm_num at hnorm
    · right; left; exact Zsqrtd.ext hr hi
    · exfalso; rw [hr, hi] at hnorm; norm_num at hnorm
    · exfalso; rw [hr, hi] at hnorm; norm_num at hnorm
  · rintro (rfl | rfl | rfl | rfl)
    · exact isUnit_one
    · exact ⟨⟨⟨-1, 0⟩, ⟨-1, 0⟩, by ext <;> norm_num, by ext <;> norm_num⟩, rfl⟩
    · exact ⟨⟨⟨0, 1⟩, ⟨0, -1⟩, by ext <;> norm_num, by ext <;> norm_num⟩, rfl⟩
    · exact ⟨⟨⟨0, -1⟩, ⟨0, 1⟩, by ext <;> norm_num, by ext <;> norm_num⟩, rfl⟩

lemma eq_of_associated_firstQuad {z w : GaussianInt}
    (hz : 0 < z.re ∧ 0 ≤ z.im) (hw : 0 < w.re ∧ 0 ≤ w.im) (hass : Associated z w) :
    z = w := by
  rcases hass with ⟨u, hu⟩
  have hu4 := (gaussianInt_isUnit_iff (u : GaussianInt)).mp u.isUnit
  rcases hu4 with h | h | h | h
  · rw [h] at hu
    have : z * 1 = w := hu
    simpa using this
  · rw [h] at hu
    have hre : w.re = -z.re := by simpa using (congrArg Zsqrtd.re hu).symm
    omega
  · rw [h] at hu
    have hre : w.re = -z.im := by simpa using (congrArg Zsqrtd.re hu).symm
    omega
  · rw [h] at hu
    have him : w.im = -z.re := by simpa using (congrArg Zsqrtd.im hu).symm
    omega

/-- Exact 4-to-1 bijection: `repTwoSquares n = 4 * Nat.card (FirstQuadG n)` for all `n ≥ 1`. -/
theorem repTwoSquares_eq_four_mul_card_firstQuadG {n : ℕ} (hn : 1 ≤ n) :
    repTwoSquares n = 4 * Nat.card (FirstQuadG n) := by
  rw [repTwoSquares_eq_natCard]
  let unitVec : Fin 4 → GaussianInt := fun i =>
    match i with
    | ⟨0, _⟩ => ⟨1, 0⟩
    | ⟨1, _⟩ => ⟨-1, 0⟩
    | ⟨2, _⟩ => ⟨0, 1⟩
    | ⟨3, _⟩ => ⟨0, -1⟩
  have hnorm_u : ∀ i : Fin 4, (unitVec i).norm = 1 := by
    intro i; fin_cases i <;> decide
  let fwd : Fin 4 × FirstQuadG n → { p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = (n : ℤ) } :=
    fun ⟨i, z⟩ =>
      let w : GaussianInt := unitVec i * z.1
      ⟨(w.re, w.im), by
        have hw : w.norm = (n : ℤ) := by
          rw [Zsqrtd.norm_mul, hnorm_u i, one_mul, z.2.2.2]
        simpa [norm_eq_re_sq_add_im_sq] using hw⟩
  have hbij : Function.Bijective fwd := by
    constructor
    · rintro ⟨i₁, z₁⟩ ⟨i₂, z₂⟩ h
      have hpair : (unitVec i₁ * z₁.1).re = (unitVec i₂ * z₂.1).re ∧
          (unitVec i₁ * z₁.1).im = (unitVec i₂ * z₂.1).im := by
        have h1 := congrArg Subtype.val h
        exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
      have hmul : unitVec i₁ * z₁.1 = unitVec i₂ * z₂.1 := Zsqrtd.ext hpair.1 hpair.2
      have hu1 : IsUnit (unitVec i₁) :=
        (gaussianInt_isUnit_iff _).mpr (by fin_cases i₁ <;> simp [unitVec])
      have hu2 : IsUnit (unitVec i₂) :=
        (gaussianInt_isUnit_iff _).mpr (by fin_cases i₂ <;> simp [unitVec])
      have hass : Associated z₁.1 z₂.1 := by
        obtain ⟨u₁, hu₁⟩ := hu1
        obtain ⟨u₂, hu₂⟩ := hu2
        refine ⟨u₁ * u₂⁻¹, ?_⟩
        rw [Units.val_mul]
        have h' : (u₁ : GaussianInt) * z₁.1 = (u₂ : GaussianInt) * z₂.1 := by
          simpa [hu₁, hu₂] using hmul
        calc z₁.1 * ((u₁ : GaussianInt) * ((u₂⁻¹ : GaussianIntˣ) : GaussianInt))
            = ((u₂⁻¹ : GaussianIntˣ) : GaussianInt) * ((u₁ : GaussianInt) * z₁.1) := by ring
          _ = ((u₂⁻¹ : GaussianIntˣ) : GaussianInt) * ((u₂ : GaussianInt) * z₂.1) := by rw [h']
          _ = (((u₂⁻¹ : GaussianIntˣ) : GaussianInt) * (u₂ : GaussianInt)) * z₂.1 := by ring
          _ = z₂.1 := by simp
      have hz_eq : z₁ = z₂ :=
        Subtype.ext (eq_of_associated_firstQuad ⟨z₁.2.1, z₁.2.2.1⟩ ⟨z₂.2.1, z₂.2.2.1⟩ hass)
      subst hz_eq
      have hz_ne : z₁.1 ≠ 0 := by
        intro h0
        have := z₁.2.2.2
        rw [h0] at this; simp [Zsqrtd.norm_def] at this; omega
      have hu_eq : unitVec i₁ = unitVec i₂ := mul_right_cancel₀ hz_ne hmul
      have hi_eq : i₁ = i₂ := by
        fin_cases i₁ <;> fin_cases i₂ <;> simp [unitVec] at hu_eq ⊢
      exact Prod.ext hi_eq rfl
    · rintro ⟨⟨a, b⟩, hab⟩
      let w : GaussianInt := ⟨a, b⟩
      have hw_norm : w.norm = (n : ℤ) := by simpa [norm_eq_re_sq_add_im_sq] using hab
      have hw_ne : w ≠ 0 := by
        intro h0
        rw [h0] at hw_norm; simp [Zsqrtd.norm_def] at hw_norm; omega
      let z : FirstQuadG n :=
        ⟨normalizeFirstQuad w,
          (normalizeFirstQuad_mem hw_ne).1,
          (normalizeFirstQuad_mem hw_ne).2,
          (normalizeFirstQuad_norm w).trans hw_norm⟩
      rcases normalizeFirstQuad_associated w with ⟨u, hu⟩
      have hu4 := (gaussianInt_isUnit_iff (u : GaussianInt)).mp u.isUnit
      have hex : ∃ i : Fin 4, unitVec i = (u : GaussianInt) := by
        rcases hu4 with h | h | h | h
        · exact ⟨⟨0, by decide⟩, h.symm⟩
        · exact ⟨⟨1, by decide⟩, h.symm⟩
        · exact ⟨⟨2, by decide⟩, h.symm⟩
        · exact ⟨⟨3, by decide⟩, h.symm⟩
      rcases hex with ⟨i, hi⟩
      refine ⟨(i, z), ?_⟩
      apply Subtype.ext
      have hmul : unitVec i * z.1 = w := by rw [hi, mul_comm]; exact hu
      exact Prod.ext (congrArg Zsqrtd.re hmul) (congrArg Zsqrtd.im hmul)
  have hcard := Nat.card_congr (Equiv.ofBijective fwd hbij)
  rw [← hcard, Nat.card_prod, Nat.card_fin]

/-- Count of first-quadrant Gaussian integers of norm `n`. -/
def gCount (n : ℕ) : ℕ := Nat.card (FirstQuadG n)

lemma gCount_one : gCount 1 = 1 := by
  let _ : Unique (FirstQuadG 1) :=
    { default := ⟨⟨1, 0⟩, by decide, by decide, by decide⟩
      uniq := fun z => by
        apply Subtype.ext
        have hsq : z.1.re ^ 2 + z.1.im ^ 2 = 1 := by
          simpa [norm_eq_re_sq_add_im_sq] using z.2.2.2
        have hre : z.1.re = 1 := by nlinarith [z.2.1, sq_nonneg z.1.im]
        have him : z.1.im = 0 := by nlinarith [z.2.2.1, hre, hsq]
        exact Zsqrtd.ext hre him }
  exact Nat.card_unique

lemma zsqrtd_norm_pow (z : GaussianInt) (n : ℕ) : (z ^ n).norm = z.norm ^ n := by
  induction n with
  | zero => simp [Zsqrtd.norm_def]
  | succ n ih => rw [pow_succ, Zsqrtd.norm_mul, ih, pow_succ]

lemma gaussianInt_associated_of_dvd_of_norm_eq {z w : GaussianInt}
    (hdvd : z ∣ w) (hnorm : z.norm = w.norm) (hz : 0 < z.norm) : Associated z w := by
  rcases hdvd with ⟨q, rfl⟩
  rw [Zsqrtd.norm_mul] at hnorm
  have hq : q.norm = 1 := by nlinarith
  obtain ⟨u, hu⟩ := gaussianInt_isUnit_of_norm_eq_one hq
  exact ⟨u, by rw [hu]⟩

lemma gaussianInt_norm_dvd_of_dvd {z w : GaussianInt} (h : z ∣ w) : z.norm ∣ w.norm := by
  rcases h with ⟨q, rfl⟩
  exact ⟨q.norm, Zsqrtd.norm_mul z q⟩

lemma gaussianInt_isCoprime_of_norm_coprime {z w : GaussianInt}
    (hcop : IsCoprime z.norm w.norm) : IsCoprime z w := by
  rcases hcop with ⟨a, b, hab⟩
  refine ⟨(a : GaussianInt) * star z, (b : GaussianInt) * star w, ?_⟩
  have hz : star z * z = (z.norm : GaussianInt) := by
    ext
    · simp [Zsqrtd.norm_def]
    · simp [Zsqrtd.norm_def]; ring
  have hw : star w * w = (w.norm : GaussianInt) := by
    ext
    · simp [Zsqrtd.norm_def]
    · simp [Zsqrtd.norm_def]; ring
  calc ((a : GaussianInt) * star z) * z + ((b : GaussianInt) * star w) * w
      = (a : GaussianInt) * (star z * z) + (b : GaussianInt) * (star w * w) := by ring
    _ = (a : GaussianInt) * (z.norm : GaussianInt) + (b : GaussianInt) * (w.norm : GaussianInt) := by
        rw [hz, hw]
    _ = ((a * z.norm + b * w.norm : ℤ) : GaussianInt) := by push_cast; rfl
    _ = 1 := by rw [hab]; simp

/-- **Multiplicativity of `gCount`**: for coprime positive integers `m, n`,
`gCount (m * n) = gCount m * gCount n` (via `EuclideanDomain.gcd` in `ℤ[i]`). -/
theorem gCount_mul_of_coprime {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n) :
    gCount (m * n) = gCount m * gCount n := by
  let mulMap : FirstQuadG m × FirstQuadG n → FirstQuadG (m * n) := fun ⟨z, w⟩ =>
    have hprod_norm : (z.1 * w.1).norm = ((m * n : ℕ) : ℤ) := by
      rw [Zsqrtd.norm_mul, z.2.2.2, w.2.2.2]; push_cast; rfl
    have hprod_ne : z.1 * w.1 ≠ 0 := by
      intro h0
      rw [h0] at hprod_norm; simp [Zsqrtd.norm_def] at hprod_norm
      have hmn : 0 < m * n := Nat.mul_pos hm hn
      omega
    ⟨normalizeFirstQuad (z.1 * w.1),
      (normalizeFirstQuad_mem hprod_ne).1,
      (normalizeFirstQuad_mem hprod_ne).2,
      (normalizeFirstQuad_norm _).trans hprod_norm⟩
  have hbij : Function.Bijective mulMap := by
    constructor
    · rintro ⟨z₁, w₁⟩ ⟨z₂, w₂⟩ h
      have heq : normalizeFirstQuad (z₁.1 * w₁.1) = normalizeFirstQuad (z₂.1 * w₂.1) :=
        congrArg Subtype.val h
      have hass : Associated (z₁.1 * w₁.1) (z₂.1 * w₂.1) := by
        have h1 := normalizeFirstQuad_associated (z₁.1 * w₁.1)
        have h2 := normalizeFirstQuad_associated (z₂.1 * w₂.1)
        rw [heq] at h1
        exact h1.symm.trans h2
      have hcop_zw : IsCoprime z₁.1 w₂.1 := by
        apply gaussianInt_isCoprime_of_norm_coprime
        rw [z₁.2.2.2, w₂.2.2.2]
        exact Nat.isCoprime_iff_coprime.mpr hcop
      have hdvd12 : z₁.1 ∣ z₂.1 :=
        hcop_zw.dvd_of_dvd_mul_right (dvd_trans (dvd_mul_right z₁.1 w₁.1) hass.dvd)
      have hz_ass : Associated z₁.1 z₂.1 :=
        gaussianInt_associated_of_dvd_of_norm_eq hdvd12
          (z₁.2.2.2.trans z₂.2.2.2.symm) (by rw [z₁.2.2.2]; omega)
      have hz_eq : z₁ = z₂ :=
        Subtype.ext (eq_of_associated_firstQuad ⟨z₁.2.1, z₁.2.2.1⟩ ⟨z₂.2.1, z₂.2.2.1⟩ hz_ass)
      subst hz_eq
      have hz_ne : z₁.1 ≠ 0 := by
        intro h0; have := z₁.2.2.2; rw [h0] at this; simp [Zsqrtd.norm_def] at this; omega
      have hw_ass : Associated w₁.1 w₂.1 := by
        rcases hass with ⟨u, hu⟩
        refine ⟨u, mul_left_cancel₀ hz_ne ?_⟩
        calc z₁.1 * (w₁.1 * (u : GaussianInt)) = (z₁.1 * w₁.1) * (u : GaussianInt) := by ring
          _ = z₁.1 * w₂.1 := hu
      have hw_eq : w₁ = w₂ :=
        Subtype.ext (eq_of_associated_firstQuad ⟨w₁.2.1, w₁.2.2.1⟩ ⟨w₂.2.1, w₂.2.2.1⟩ hw_ass)
      exact Prod.ext rfl hw_eq
    · intro u
      let z0 : GaussianInt := EuclideanDomain.gcd u.1 (m : GaussianInt)
      let w0 : GaussianInt := EuclideanDomain.gcd u.1 (n : GaussianInt)
      have hz0_dvd_u : z0 ∣ u.1 := EuclideanDomain.gcd_dvd_left u.1 (m : GaussianInt)
      have hz0_dvd_m : z0 ∣ (m : GaussianInt) := EuclideanDomain.gcd_dvd_right u.1 (m : GaussianInt)
      have hw0_dvd_u : w0 ∣ u.1 := EuclideanDomain.gcd_dvd_left u.1 (n : GaussianInt)
      have hw0_dvd_n : w0 ∣ (n : GaussianInt) := EuclideanDomain.gcd_dvd_right u.1 (n : GaussianInt)
      have hcop_mn : IsCoprime (m : GaussianInt) (n : GaussianInt) := by
        rcases Nat.isCoprime_iff_coprime.mpr hcop with ⟨a, b, hab⟩
        refine ⟨(a : GaussianInt), (b : GaussianInt), ?_⟩
        calc (a : GaussianInt) * (m : GaussianInt) + (b : GaussianInt) * (n : GaussianInt)
            = ((a * (m : ℤ) + b * (n : ℤ) : ℤ) : GaussianInt) := by push_cast; rfl
          _ = 1 := by rw [hab]; simp
      have hcop_zw : IsCoprime z0 w0 := by
        rcases hcop_mn with ⟨a, b, hab⟩
        rcases hz0_dvd_m with ⟨qm, hqm⟩
        rcases hw0_dvd_n with ⟨qn, hqn⟩
        exact ⟨a * qm, b * qn, by linear_combination hab - a * hqm - b * hqn⟩
      have hzw_dvd_u : z0 * w0 ∣ u.1 := hcop_zw.mul_dvd hz0_dvd_u hw0_dvd_u
      have hu_dvd_mn : u.1 ∣ (m : GaussianInt) * (n : GaussianInt) := by
        refine ⟨star u.1, ?_⟩
        have hst : u.1 * star u.1 = (u.1.norm : GaussianInt) := by
          ext
          · simp [Zsqrtd.norm_def]
          · simp [Zsqrtd.norm_def]; ring
        rw [hst, u.2.2.2]; push_cast; rfl
      have hu_dvd_zw : u.1 ∣ z0 * w0 := by
        have hbez_z : z0 = u.1 * EuclideanDomain.gcdA u.1 (m : GaussianInt) +
            (m : GaussianInt) * EuclideanDomain.gcdB u.1 (m : GaussianInt) :=
          EuclideanDomain.gcd_eq_gcd_ab u.1 (m : GaussianInt)
        have hbez_w : w0 = u.1 * EuclideanDomain.gcdA u.1 (n : GaussianInt) +
            (n : GaussianInt) * EuclideanDomain.gcdB u.1 (n : GaussianInt) :=
          EuclideanDomain.gcd_eq_gcd_ab u.1 (n : GaussianInt)
        set a := EuclideanDomain.gcdA u.1 (m : GaussianInt)
        set b := EuclideanDomain.gcdB u.1 (m : GaussianInt)
        set c := EuclideanDomain.gcdA u.1 (n : GaussianInt)
        set d := EuclideanDomain.gcdB u.1 (n : GaussianInt)
        rcases hu_dvd_mn with ⟨q, hq⟩
        refine ⟨u.1 * a * c + (n : GaussianInt) * a * d + (m : GaussianInt) * b * c + q * b * d, ?_⟩
        rw [hbez_z, hbez_w]
        linear_combination b * d * hq
      have hnorm_eq : z0.norm * w0.norm = ((m * n : ℕ) : ℤ) := by
        rw [← Zsqrtd.norm_mul]
        have hd1 := gaussianInt_norm_dvd_of_dvd hzw_dvd_u
        have hd2 := gaussianInt_norm_dvd_of_dvd hu_dvd_zw
        rw [u.2.2.2] at hd1 hd2
        exact Int.dvd_antisymm (GaussianInt.norm_nonneg _) (Int.natCast_nonneg _) hd1 hd2
      have hz_nat : z0.norm.natAbs ∣ m * m := by
        have h1 := gaussianInt_norm_dvd_of_dvd hz0_dvd_m
        have hm_norm : ((m : GaussianInt)).norm = (m : ℤ) * (m : ℤ) := by simp [Zsqrtd.norm_def]
        rw [hm_norm] at h1
        simpa [Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr h1
      have hw_nat : w0.norm.natAbs ∣ n * n := by
        have h1 := gaussianInt_norm_dvd_of_dvd hw0_dvd_n
        have hn_norm : ((n : GaussianInt)).norm = (n : ℤ) * (n : ℤ) := by simp [Zsqrtd.norm_def]
        rw [hn_norm] at h1
        simpa [Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr h1
      have hprod_nat : z0.norm.natAbs * w0.norm.natAbs = m * n := by
        simpa [Int.natAbs_mul] using congrArg Int.natAbs hnorm_eq
      have hz_dvd_m : z0.norm.natAbs ∣ m := by
        have hcop_zn : Nat.Coprime z0.norm.natAbs n :=
          (hcop.mul_left hcop).coprime_dvd_left hz_nat
        exact hcop_zn.dvd_of_dvd_mul_right ⟨w0.norm.natAbs, hprod_nat.symm⟩
      have hw_dvd_n : w0.norm.natAbs ∣ n := by
        have hcop_wm : Nat.Coprime w0.norm.natAbs m :=
          (hcop.symm.mul_left hcop.symm).coprime_dvd_left hw_nat
        exact hcop_wm.dvd_of_dvd_mul_left ⟨z0.norm.natAbs, by linarith⟩
      have hle1 : z0.norm.natAbs ≤ m := Nat.le_of_dvd hm hz_dvd_m
      have hle2 : w0.norm.natAbs ≤ n := Nat.le_of_dvd hn hw_dvd_n
      have hzn : z0.norm.natAbs = m := by
        by_contra hne
        have hlt : z0.norm.natAbs < m := lt_of_le_of_ne hle1 hne
        have hmul_lt : z0.norm.natAbs * w0.norm.natAbs < m * n :=
          lt_of_le_of_lt (Nat.mul_le_mul_left _ hle2) (Nat.mul_lt_mul_of_pos_right hlt hn)
        omega
      have hwn : w0.norm.natAbs = n := by
        by_contra hne
        have hlt : w0.norm.natAbs < n := lt_of_le_of_ne hle2 hne
        have hmul_lt : z0.norm.natAbs * w0.norm.natAbs < m * n :=
          lt_of_le_of_lt (Nat.mul_le_mul_right _ hle1) (Nat.mul_lt_mul_of_pos_left hlt hm)
        omega
      have hz_eq_m : z0.norm = (m : ℤ) := by
        have hnn := GaussianInt.norm_nonneg z0; omega
      have hw_eq_n : w0.norm = (n : ℤ) := by
        have hnn := GaussianInt.norm_nonneg w0; omega
      have hz0_ne : z0 ≠ 0 := by
        intro h0; rw [h0] at hz_eq_m; simp [Zsqrtd.norm_def] at hz_eq_m; omega
      have hw0_ne : w0 ≠ 0 := by
        intro h0; rw [h0] at hw_eq_n; simp [Zsqrtd.norm_def] at hw_eq_n; omega
      let z : FirstQuadG m :=
        ⟨normalizeFirstQuad z0,
          (normalizeFirstQuad_mem hz0_ne).1,
          (normalizeFirstQuad_mem hz0_ne).2,
          (normalizeFirstQuad_norm z0).trans hz_eq_m⟩
      let w : FirstQuadG n :=
        ⟨normalizeFirstQuad w0,
          (normalizeFirstQuad_mem hw0_ne).1,
          (normalizeFirstQuad_mem hw0_ne).2,
          (normalizeFirstQuad_norm w0).trans hw_eq_n⟩
      refine ⟨(z, w), ?_⟩
      apply Subtype.ext
      have hass1 : Associated (z.1 * w.1) (z0 * w0) :=
        (normalizeFirstQuad_associated z0).mul_mul (normalizeFirstQuad_associated w0)
      have hass2 : Associated (z0 * w0) u.1 :=
        gaussianInt_associated_of_dvd_of_norm_eq hzw_dvd_u
          (by rw [Zsqrtd.norm_mul, hz_eq_m, hw_eq_n, u.2.2.2]; push_cast; rfl)
          (by rw [Zsqrtd.norm_mul, hz_eq_m, hw_eq_n]; nlinarith)
      have hass3 : Associated (normalizeFirstQuad (z.1 * w.1)) u.1 :=
        (normalizeFirstQuad_associated (z.1 * w.1)).trans (hass1.trans hass2)
      exact eq_of_associated_firstQuad
        ⟨(mulMap (z, w)).2.1, (mulMap (z, w)).2.2.1⟩ ⟨u.2.1, u.2.2.1⟩ hass3
  have hcard := Nat.card_congr (Equiv.ofBijective mulMap hbij)
  unfold gCount
  rw [← hcard, Nat.card_prod]

/-- Helper: `1 + i` divides any Gaussian integer of even norm. -/
lemma one_add_i_dvd_of_even_norm {z : GaussianInt} (heven : (2 : ℤ) ∣ z.norm) :
    (⟨1, 1⟩ : GaussianInt) ∣ z := by
  rw [norm_eq_re_sq_add_im_sq] at heven
  have hpar : (2 : ℤ) ∣ z.re + z.im := by
    rcases Int.even_or_odd z.re with ⟨r, hr⟩ | ⟨r, hr⟩ <;>
      rcases Int.even_or_odd z.im with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact ⟨r + s, by omega⟩
    · exfalso; rcases heven with ⟨k, hk⟩
      have : (r + r) ^ 2 + (2 * s + 1) ^ 2 = 2 * k := by rw [← hr, ← hs]; exact hk
      have : 2 * (2 * r ^ 2 + 2 * s ^ 2 + 2 * s) + 1 = 2 * k := by linarith
      omega
    · exfalso; rcases heven with ⟨k, hk⟩
      have : (2 * r + 1) ^ 2 + (s + s) ^ 2 = 2 * k := by rw [← hr, ← hs]; exact hk
      have : 2 * (2 * r ^ 2 + 2 * r + 2 * s ^ 2) + 1 = 2 * k := by linarith
      omega
    · exact ⟨r + s + 1, by omega⟩
  have hpar' : (2 : ℤ) ∣ z.im - z.re := by
    rcases hpar with ⟨t, ht⟩
    exact ⟨t - z.re, by omega⟩
  rcases hpar with ⟨a, ha⟩
  rcases hpar' with ⟨b, hb⟩
  refine ⟨⟨a, b⟩, ?_⟩
  ext <;> simp <;> omega

/-- Prime power `p = 2`: `gCount (2 ^ k) = 1` for every `k : ℕ`. -/
theorem gCount_two_pow (k : ℕ) : gCount (2 ^ k) = 1 := by
  induction k with
  | zero => simpa using gCount_one
  | succ k ih =>
    let pG : GaussianInt := ⟨1, 1⟩
    have hpG_norm : pG.norm = 2 := by decide
    let fwd : FirstQuadG (2 ^ k) → FirstQuadG (2 ^ (k + 1)) := fun z =>
      have hnorm : (pG * z.1).norm = ((2 ^ (k + 1) : ℕ) : ℤ) := by
        rw [Zsqrtd.norm_mul, hpG_norm, z.2.2.2, pow_succ]; push_cast; ring
      have hne : pG * z.1 ≠ 0 := by
        intro h0
        rw [h0] at hnorm; simp [Zsqrtd.norm_def] at hnorm
        have hpos : (0 : ℤ) < (2 : ℤ) ^ (k + 1) := by positivity
        linarith
      ⟨normalizeFirstQuad (pG * z.1),
        (normalizeFirstQuad_mem hne).1,
        (normalizeFirstQuad_mem hne).2,
        (normalizeFirstQuad_norm _).trans hnorm⟩
    have hbij : Function.Bijective fwd := by
      constructor
      · intro z₁ z₂ h
        have heq : normalizeFirstQuad (pG * z₁.1) = normalizeFirstQuad (pG * z₂.1) :=
          congrArg Subtype.val h
        have hass : Associated (pG * z₁.1) (pG * z₂.1) := by
          have h1 := normalizeFirstQuad_associated (pG * z₁.1)
          have h2 := normalizeFirstQuad_associated (pG * z₂.1)
          rw [heq] at h1
          exact h1.symm.trans h2
        have hpG_ne : pG ≠ 0 := by intro h0; rw [h0] at hpG_norm; simp [Zsqrtd.norm_def] at hpG_norm
        have hz_ass : Associated z₁.1 z₂.1 := by
          rcases hass with ⟨u, hu⟩
          refine ⟨u, mul_left_cancel₀ hpG_ne ?_⟩
          calc pG * (z₁.1 * (u : GaussianInt)) = (pG * z₁.1) * (u : GaussianInt) := by ring
            _ = pG * z₂.1 := hu
        exact Subtype.ext (eq_of_associated_firstQuad ⟨z₁.2.1, z₁.2.2.1⟩ ⟨z₂.2.1, z₂.2.2.1⟩ hz_ass)
      · intro w
        have heven : (2 : ℤ) ∣ w.1.norm := by
          rw [w.2.2.2, pow_succ]
          exact ⟨(2 ^ k : ℕ), by push_cast; ring⟩
        rcases one_add_i_dvd_of_even_norm heven with ⟨q, hq⟩
        have hq_norm : q.norm = ((2 ^ k : ℕ) : ℤ) := by
          have h1 := w.2.2.2
          rw [hq, Zsqrtd.norm_mul, hpG_norm, pow_succ] at h1
          push_cast at h1 ⊢
          linarith
        have hq_ne : q ≠ 0 := by
          intro h0; rw [h0] at hq_norm; simp [Zsqrtd.norm_def] at hq_norm
          have hpos : (0 : ℤ) < (2 : ℤ) ^ k := by positivity
          linarith
        let z : FirstQuadG (2 ^ k) :=
          ⟨normalizeFirstQuad q,
            (normalizeFirstQuad_mem hq_ne).1,
            (normalizeFirstQuad_mem hq_ne).2,
            (normalizeFirstQuad_norm q).trans hq_norm⟩
        refine ⟨z, ?_⟩
        apply Subtype.ext
        have hass : Associated (normalizeFirstQuad (pG * z.1)) w.1 := by
          refine (normalizeFirstQuad_associated (pG * z.1)).trans ?_
          rw [hq]
          exact (Associated.refl pG).mul_mul (normalizeFirstQuad_associated q)
        exact eq_of_associated_firstQuad
          ⟨(fwd z).2.1, (fwd z).2.2.1⟩ ⟨w.2.1, w.2.2.1⟩ hass
    rw [gCount, ← Nat.card_congr (Equiv.ofBijective fwd hbij)]
    exact ih

/-- Helper: if `p` is prime with `p % 4 = 3` and `p ∣ a ^ 2 + b ^ 2`, then `p ∣ a` and `p ∣ b`. -/
lemma prime_three_mod_four_dvd_of_dvd_sq_add_sq {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3)
    {a b : ℤ} (h : (p : ℤ) ∣ a ^ 2 + b ^ 2) : (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b := by
  have : Fact p.Prime := ⟨hp⟩
  have hnot_sq : ¬ IsSquare (-1 : ZMod p) := by
    rw [ZMod.exists_sq_eq_neg_one_iff]; omega
  have hz : ((a : ZMod p)) ^ 2 + ((b : ZMod p)) ^ 2 = 0 := by
    have h0 : ((a ^ 2 + b ^ 2 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
    simpa using h0
  have hb0 : (b : ZMod p) = 0 := by
    by_contra hbne
    have hsq : ((a : ZMod p) * (b : ZMod p)⁻¹) ^ 2 = -1 := by
      rw [mul_pow, inv_pow]
      have ha2 : (a : ZMod p) ^ 2 = -((b : ZMod p) ^ 2) := eq_neg_of_add_eq_zero_left hz
      rw [ha2, neg_mul, mul_inv_cancel₀ (pow_ne_zero 2 hbne)]
    exact hnot_sq ⟨(a : ZMod p) * (b : ZMod p)⁻¹, by rw [← sq, hsq]⟩
  have ha0 : (a : ZMod p) = 0 := by
    rw [hb0, zero_pow (by decide : 2 ≠ 0), add_zero] at hz
    exact sq_eq_zero_iff.mp hz
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha0,
    (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hb0⟩

/-- Prime power `p ≡ 3 [MOD 4]`: `gCount (p ^ k) = if Even k then 1 else 0`. -/
theorem gCount_prime_three_mod_four_pow {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) :
    ∀ k : ℕ, gCount (p ^ k) = if Even k then 1 else 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => simp [gCount_one]
    | 1 =>
      rw [if_neg (by decide : ¬ Even 1)]
      have hempty : IsEmpty (FirstQuadG (p ^ 1)) := ⟨fun z => by
        have hsq : z.1.re ^ 2 + z.1.im ^ 2 = (p : ℤ) := by
          simpa [norm_eq_re_sq_add_im_sq] using z.2.2.2
        have hdvd := prime_three_mod_four_dvd_of_dvd_sq_add_sq hp hp3 (a := z.1.re) (b := z.1.im)
          ⟨1, by linarith⟩
        rcases hdvd.1 with ⟨a, ha⟩
        rcases hdvd.2 with ⟨b, hb⟩
        rw [ha, hb] at hsq
        have hp_pos : (0 : ℤ) < p := Nat.cast_pos.mpr hp.pos
        have h1 : (p : ℤ) * (a ^ 2 + b ^ 2) = 1 := by nlinarith
        have hge : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
        have hnn : 0 ≤ a ^ 2 + b ^ 2 := by positivity
        have hpos1 : 1 ≤ a ^ 2 + b ^ 2 := by
          by_contra hc
          have h0 : a ^ 2 + b ^ 2 = 0 := by omega
          rw [h0] at h1; norm_num at h1
        nlinarith⟩
      exact Nat.card_eq_zero.mpr (Or.inl hempty)
    | k + 2 =>
      have hev : Even (k + 2) ↔ Even k := by
        constructor
        · rintro ⟨m, hm⟩; exact ⟨m - 1, by omega⟩
        · rintro ⟨m, hm⟩; exact ⟨m + 1, by omega⟩
      rw [if_congr hev rfl rfl]
      let fwd : FirstQuadG (p ^ k) → FirstQuadG (p ^ (k + 2)) := fun z =>
        ⟨(p : GaussianInt) * z.1,
          by
            have hre : ((p : GaussianInt) * z.1).re = (p : ℤ) * z.1.re := by simp
            rw [hre]; exact mul_pos (Nat.cast_pos.mpr hp.pos) z.2.1,
          by
            have him : ((p : GaussianInt) * z.1).im = (p : ℤ) * z.1.im := by simp
            rw [him]; exact mul_nonneg (Int.natCast_nonneg p) z.2.2.1,
          by
            rw [Zsqrtd.norm_mul, z.2.2.2]
            have hpn : ((p : GaussianInt)).norm = (p : ℤ) ^ 2 := by
              simp [Zsqrtd.norm_def, sq]
            rw [hpn, pow_add]; push_cast; ring⟩
      have hbij : Function.Bijective fwd := by
        constructor
        · intro z₁ z₂ h
          have heq : (p : GaussianInt) * z₁.1 = (p : GaussianInt) * z₂.1 := congrArg Subtype.val h
          have hp_ne : (p : GaussianInt) ≠ 0 := by
            intro h0
            have hre := congrArg Zsqrtd.re h0
            simp at hre
            exact hp.ne_zero hre
          exact Subtype.ext (mul_left_cancel₀ hp_ne heq)
        · intro w
          have hdvd_norm : (p : ℤ) ∣ w.1.re ^ 2 + w.1.im ^ 2 := by
            have hsq : w.1.re ^ 2 + w.1.im ^ 2 = ((p ^ (k + 2) : ℕ) : ℤ) := by
              simpa [norm_eq_re_sq_add_im_sq] using w.2.2.2
            rw [hsq, pow_add]
            exact ⟨((p ^ k * p : ℕ) : ℤ), by push_cast; ring⟩
          have ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := prime_three_mod_four_dvd_of_dvd_sq_add_sq hp hp3 hdvd_norm
          have hp_pos : (0 : ℤ) < p := Nat.cast_pos.mpr hp.pos
          have ha_pos : 0 < a := by nlinarith [w.2.1]
          have hb_nn : 0 ≤ b := by nlinarith [w.2.2.1]
          have hab_norm : (⟨a, b⟩ : GaussianInt).norm = ((p ^ k : ℕ) : ℤ) := by
            have h1 := w.2.2.2
            rw [norm_eq_re_sq_add_im_sq, ha, hb, pow_add] at h1
            rw [norm_eq_re_sq_add_im_sq]
            dsimp only
            push_cast at h1 ⊢
            have hp2 : (0 : ℤ) < (p : ℤ) ^ 2 := by positivity
            nlinarith
          refine ⟨⟨⟨a, b⟩, ha_pos, hb_nn, hab_norm⟩, ?_⟩
          apply Subtype.ext
          ext
          · change ((p : GaussianInt) * ⟨a, b⟩).re = w.1.re; simp [ha]
          · change ((p : GaussianInt) * ⟨a, b⟩).im = w.1.im; simp [hb]
      rw [gCount, ← Nat.card_congr (Equiv.ofBijective fwd hbij)]
      exact ih k (by omega)

/-- Any Gaussian integer whose norm is a rational prime `p` is prime in `ℤ[i]`. -/
lemma gaussianInt_prime_of_norm_prime {pG : GaussianInt} {p : ℕ} (hp : p.Prime)
    (hnorm : pG.norm = (p : ℤ)) : Prime pG := by
  rw [← irreducible_iff_prime]
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have h1 : pG.norm = 1 := by
      rcases hu with ⟨⟨u, v, huv, _⟩, rfl⟩
      have hm : u.norm * v.norm = 1 := by rw [← Zsqrtd.norm_mul, huv]; simp [Zsqrtd.norm_def]
      change u.norm = 1
      have hpm := Int.eq_one_or_neg_one_of_mul_eq_one hm
      have hu_nn := GaussianInt.norm_nonneg u
      omega
    have := hp.ne_one
    omega
  · have hm : a.norm * b.norm = (p : ℤ) := by rw [← Zsqrtd.norm_mul, ← hab, hnorm]
    have ha_nn : 0 ≤ a.norm := GaussianInt.norm_nonneg a
    have hb_nn : 0 ≤ b.norm := GaussianInt.norm_nonneg b
    have hnat : a.norm.natAbs * b.norm.natAbs = p := by
      simpa [Int.natAbs_mul] using congrArg Int.natAbs hm
    rcases (Nat.dvd_prime hp).mp ⟨b.norm.natAbs, hnat.symm⟩ with ha1 | hap
    · left; exact gaussianInt_isUnit_of_norm_eq_one (by omega)
    · right
      have hb1 : b.norm.natAbs = 1 := by
        have hp0 : 0 < p := hp.pos
        rw [hap] at hnat; nlinarith
      exact gaussianInt_isUnit_of_norm_eq_one (by omega)

/-- Prime power `p ≡ 1 [MOD 4]`: `gCount (p ^ k) = k + 1`. -/
theorem gCount_prime_one_mod_four_pow {p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (k : ℕ) :
    gCount (p ^ k) = k + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, y, hxy⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  let pG : GaussianInt := ⟨(x : ℤ), (y : ℤ)⟩
  let pGb : GaussianInt := star pG
  have hpG_norm : pG.norm = (p : ℤ) := by
    rw [norm_eq_re_sq_add_im_sq]
    change (x : ℤ) ^ 2 + (y : ℤ) ^ 2 = (p : ℤ)
    exact_mod_cast hxy
  have hpGb_norm : pGb.norm = (p : ℤ) := by
    rw [norm_eq_re_sq_add_im_sq]
    have h1 : pGb.re = (x : ℤ) := rfl
    have h2 : pGb.im = -(y : ℤ) := rfl
    rw [h1, h2, neg_sq]; exact_mod_cast hxy
  have hpG_prime : Prime pG := gaussianInt_prime_of_norm_prime hp hpG_norm
  have hpGb_prime : Prime pGb := gaussianInt_prime_of_norm_prime hp hpGb_norm
  have hnot_ass : ¬ Associated pG pGb := by
    rintro ⟨u, hu⟩
    have hu4 := (gaussianInt_isUnit_iff (u : GaussianInt)).mp u.isUnit
    rcases hu4 with h | h | h | h
    · rw [h] at hu
      have him : (y : ℤ) = -(y : ℤ) := by simpa [pG, pGb] using congrArg Zsqrtd.im hu
      have hy0 : y = 0 := by omega
      rw [hy0] at hxy
      have hsq : x * x = p := by simpa [sq] using hxy
      rcases (Nat.dvd_prime hp).mp ⟨x, hsq.symm⟩ with hx1 | hxp
      · rw [hx1] at hsq; exact hp.ne_one hsq.symm
      · rw [hxp] at hsq; nlinarith [hp.two_le]
    · rw [h] at hu
      have hre : -(x : ℤ) = (x : ℤ) := by simpa [pG, pGb] using congrArg Zsqrtd.re hu
      have hx0 : x = 0 := by omega
      rw [hx0] at hxy
      have hsq : y * y = p := by simpa [sq] using hxy
      rcases (Nat.dvd_prime hp).mp ⟨y, hsq.symm⟩ with hy1 | hyp
      · rw [hy1] at hsq; exact hp.ne_one hsq.symm
      · rw [hyp] at hsq; nlinarith [hp.two_le]
    · rw [h] at hu
      have hre : -(y : ℤ) = (x : ℤ) := by simpa [pG, pGb] using congrArg Zsqrtd.re hu
      have h2 : 2 * x ^ 2 = p := by
        have hyx : y = x := by omega
        rw [← hxy, hyx]; ring
      omega
    · rw [h] at hu
      have hre : (y : ℤ) = (x : ℤ) := by simpa [pG, pGb] using congrArg Zsqrtd.re hu
      have h2 : 2 * x ^ 2 = p := by
        have hyx : y = x := by omega
        rw [← hxy, hyx]; ring
      omega
  have hpG_not_dvd_pGb : ¬ pG ∣ pGb := fun hdvd =>
    hnot_ass (gaussianInt_associated_of_dvd_of_norm_eq hdvd
      (hpG_norm.trans hpGb_norm.symm) (by rw [hpG_norm]; exact Nat.cast_pos.mpr hp.pos))
  let fwd : Fin (k + 1) → FirstQuadG (p ^ k) := fun j =>
    have hnorm : (pG ^ (j : ℕ) * pGb ^ (k - (j : ℕ))).norm = ((p ^ k : ℕ) : ℤ) := by
      rw [Zsqrtd.norm_mul, zsqrtd_norm_pow, zsqrtd_norm_pow, hpG_norm, hpGb_norm, ← pow_add,
        Nat.add_sub_of_le (Nat.lt_succ_iff.mp j.2)]
      push_cast; rfl
    have hne : pG ^ (j : ℕ) * pGb ^ (k - (j : ℕ)) ≠ 0 := by
      intro h0
      rw [h0] at hnorm; simp [Zsqrtd.norm_def] at hnorm
      have hpos : (0 : ℤ) < (p : ℤ) ^ k := pow_pos (Nat.cast_pos.mpr hp.pos) k
      linarith
    ⟨normalizeFirstQuad (pG ^ (j : ℕ) * pGb ^ (k - (j : ℕ))),
      (normalizeFirstQuad_mem hne).1,
      (normalizeFirstQuad_mem hne).2,
      (normalizeFirstQuad_norm _).trans hnorm⟩
  have hbij : Function.Bijective fwd := by
    constructor
    · intro j₁ j₂ h
      have heq : normalizeFirstQuad (pG ^ (j₁ : ℕ) * pGb ^ (k - (j₁ : ℕ))) =
          normalizeFirstQuad (pG ^ (j₂ : ℕ) * pGb ^ (k - (j₂ : ℕ))) := congrArg Subtype.val h
      have hass : Associated (pG ^ (j₁ : ℕ) * pGb ^ (k - (j₁ : ℕ)))
          (pG ^ (j₂ : ℕ) * pGb ^ (k - (j₂ : ℕ))) := by
        have h1 := normalizeFirstQuad_associated (pG ^ (j₁ : ℕ) * pGb ^ (k - (j₁ : ℕ)))
        have h2 := normalizeFirstQuad_associated (pG ^ (j₂ : ℕ) * pGb ^ (k - (j₂ : ℕ)))
        rw [heq] at h1
        exact h1.symm.trans h2
      by_contra hne
      have hlt_or : (j₁ : ℕ) < (j₂ : ℕ) ∨ (j₂ : ℕ) < (j₁ : ℕ) :=
        lt_or_gt_of_ne (fun hval => hne (Fin.ext hval))
      have hcontra : ∀ a b : Fin (k + 1), (a : ℕ) < (b : ℕ) →
          Associated (pG ^ (a : ℕ) * pGb ^ (k - (a : ℕ)))
            (pG ^ (b : ℕ) * pGb ^ (k - (b : ℕ))) → False := by
        intro a b hab hass'
        have hpG_ne : pG ≠ 0 := hpG_prime.ne_zero
        have hpGb_ne : pGb ≠ 0 := hpGb_prime.ne_zero
        have hdvd : pG ^ ((b : ℕ) - (a : ℕ)) ∣ pGb ^ ((k - (a : ℕ)) - (k - (b : ℕ))) := by
          rcases hass'.symm.dvd with ⟨q, hq⟩
          refine ⟨q, ?_⟩
          have hpow1 : pG ^ (b : ℕ) = pG ^ (a : ℕ) * pG ^ ((b : ℕ) - (a : ℕ)) := by
            rw [← pow_add, Nat.add_sub_of_le hab.le]
          have hpow2 : pGb ^ (k - (a : ℕ)) =
              pGb ^ (k - (b : ℕ)) * pGb ^ ((k - (a : ℕ)) - (k - (b : ℕ))) := by
            rw [← pow_add, Nat.add_sub_of_le (Nat.sub_le_sub_left hab.le k)]
          rw [hpow1, hpow2] at hq
          have hmul_cancel : pG ^ (a : ℕ) * pGb ^ (k - (b : ℕ)) ≠ 0 :=
            mul_ne_zero (pow_ne_zero _ hpG_ne) (pow_ne_zero _ hpGb_ne)
          apply mul_left_cancel₀ hmul_cancel
          linear_combination hq
        have hdvd1 : pG ∣ pGb ^ ((k - (a : ℕ)) - (k - (b : ℕ))) :=
          dvd_trans (dvd_pow_self pG (by omega)) hdvd
        exact hpG_not_dvd_pGb (hpG_prime.dvd_of_dvd_pow hdvd1)
      rcases hlt_or with hlt | hgt
      · exact hcontra j₁ j₂ hlt hass
      · exact hcontra j₂ j₁ hgt hass.symm
    · suffices hsurj : ∀ m : ℕ, ∀ z : GaussianInt, z.norm = ((p ^ m : ℕ) : ℤ) →
          ∃ j : Fin (m + 1), Associated (pG ^ (j : ℕ) * pGb ^ (m - (j : ℕ))) z by
        intro w
        obtain ⟨j, hj⟩ := hsurj k w.1 w.2.2.2
        refine ⟨j, Subtype.ext ?_⟩
        exact eq_of_associated_firstQuad ⟨(fwd j).2.1, (fwd j).2.2.1⟩ ⟨w.2.1, w.2.2.1⟩
          ((normalizeFirstQuad_associated _).trans hj)
      intro m
      induction m with
      | zero =>
        intro z hz
        refine ⟨⟨0, by decide⟩, ?_⟩
        simp only [pow_zero]
        obtain ⟨u, hu⟩ := gaussianInt_isUnit_of_norm_eq_one (by simpa using hz)
        exact ⟨u, by simp [hu]⟩
      | succ m ih =>
        intro z hz
        have hp_dvd : pG ∣ z * star z := by
          have hzz : z * star z = (z.norm : GaussianInt) := by
            ext
            · simp [Zsqrtd.norm_def]
            · simp [Zsqrtd.norm_def]; ring
          have hpGpGb : pG * pGb = (p : GaussianInt) := by
            have h1 : pG * pGb = (pG.norm : GaussianInt) := by
              ext
              · simp [pG, pGb, Zsqrtd.norm_def]
              · simp [pG, pGb, Zsqrtd.norm_def]; ring
            rw [h1, hpG_norm]; rfl
          rw [hzz, hz, pow_succ]
          push_cast
          refine ⟨pGb * (p : GaussianInt) ^ m, ?_⟩
          calc (p : GaussianInt) ^ m * (p : GaussianInt)
              = (pG * pGb) * (p : GaussianInt) ^ m := by rw [hpGpGb, mul_comm]
            _ = pG * (pGb * (p : GaussianInt) ^ m) := by ring
        rcases hpG_prime.dvd_or_dvd hp_dvd with ⟨q, hq⟩ | ⟨q, hq⟩
        · have hq_norm : q.norm = ((p ^ m : ℕ) : ℤ) := by
            rw [hq, Zsqrtd.norm_mul, hpG_norm, pow_succ] at hz
            push_cast at hz ⊢
            have hp_pos : (0 : ℤ) < p := Nat.cast_pos.mpr hp.pos
            nlinarith
          obtain ⟨j, hj⟩ := ih q hq_norm
          refine ⟨⟨(j : ℕ) + 1, Nat.succ_lt_succ j.2⟩, ?_⟩
          have hsub : m + 1 - ((j : ℕ) + 1) = m - (j : ℕ) := by omega
          rw [hsub, pow_succ', mul_assoc, hq]
          exact (Associated.refl pG).mul_mul hj
        · have hqb : pGb ∣ z := by
            refine ⟨star q, ?_⟩
            have := congrArg star hq
            simpa [pGb, star_mul, mul_comm] using this
          rcases hqb with ⟨q', hq'⟩
          have hq'_norm : q'.norm = ((p ^ m : ℕ) : ℤ) := by
            rw [hq', Zsqrtd.norm_mul, hpGb_norm, pow_succ] at hz
            push_cast at hz ⊢
            have hp_pos : (0 : ℤ) < p := Nat.cast_pos.mpr hp.pos
            nlinarith
          obtain ⟨j, hj⟩ := ih q' hq'_norm
          refine ⟨⟨(j : ℕ), Nat.lt_succ_of_lt j.2⟩, ?_⟩
          have hsub : m + 1 - (j : ℕ) = (m - (j : ℕ)) + 1 := by omega
          rw [hsub, pow_succ, hq']
          have hmul_eq : pG ^ (j : ℕ) * (pGb ^ (m - (j : ℕ)) * pGb) =
              pGb * (pG ^ (j : ℕ) * pGb ^ (m - (j : ℕ))) := by ring
          rw [hmul_eq]
          exact (Associated.refl pGb).mul_mul hj
  have hcard := Nat.card_congr (Equiv.ofBijective fwd hbij)
  rw [gCount, ← hcard, Nat.card_fin]

/-- Divisor sum `∑_{d ∣ n} χ₋₄(d)` evaluated at prime powers. -/
lemma sum_divisors_chi4Int_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (∑ d ∈ (p ^ k).divisors, chi4Int d) = (gCount (p ^ k) : ℤ) := by
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hpow : ∀ j : ℕ, chi4Int (p ^ j) = (chi4Int p) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, chi4Int_mul, ih, pow_succ]
  simp_rw [hpow]
  have hp_cases : p = 2 ∨ p % 4 = 1 ∨ p % 4 = 3 := by
    rcases hp.eq_two_or_odd with rfl | hodd
    · left; rfl
    · right; omega
  rcases hp_cases with rfl | hp1 | hp3
  · rw [gCount_two_pow]
    have hchi2 : chi4Int 2 = 0 := rfl
    rw [hchi2, Finset.sum_range_succ']
    simp
  · rw [gCount_prime_one_mod_four_pow hp hp1]
    have hchi : chi4Int p = 1 := by unfold chi4Int; simp [hp1]
    simp [hchi]
  · rw [gCount_prime_three_mod_four_pow hp hp3]
    have hchi : chi4Int p = -1 := by unfold chi4Int; simp [hp3]
    rw [hchi]
    clear hp hp3 hchi
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      rcases Nat.even_or_odd k with hk | hk
      · have hodd : ¬ Even (k + 1) := by rcases hk with ⟨m, rfl⟩; intro ⟨r, hr⟩; omega
        rw [if_pos hk, if_neg hodd]
        rcases hk with ⟨m, rfl⟩
        have h1 : (-1 : ℤ) ^ (m + m + 1) = -1 := by
          rw [show m + m + 1 = 2 * m + 1 by omega, pow_succ, pow_mul]; norm_num
        rw [h1]; norm_num
      · have hev : Even (k + 1) := by rcases hk with ⟨m, rfl⟩; exact ⟨m + 1, by omega⟩
        have hnot : ¬ Even k := Nat.not_even_iff_odd.mpr hk
        rw [if_neg hnot, if_pos hev]
        rcases hk with ⟨m, rfl⟩
        have h1 : (-1 : ℤ) ^ (2 * m + 1 + 1) = 1 := by
          rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, pow_mul]; norm_num
        rw [h1]; norm_num

/-- Multiplicativity of `n ↦ ∑_{d ∣ n} χ₋₄(d)` for coprime `m, n`. -/
lemma sum_divisors_chi4Int_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    (∑ d ∈ (m * n).divisors, chi4Int d) =
      (∑ d ∈ m.divisors, chi4Int d) * (∑ d ∈ n.divisors, chi4Int d) := by
  have hbij : (∑ d ∈ (m * n).divisors, chi4Int d) =
      ∑ p ∈ m.divisors ×ˢ n.divisors, chi4Int (p.1 * p.2) := by
    refine Finset.sum_nbij' (fun d => (Nat.gcd d m, Nat.gcd d n)) (fun p => p.1 * p.2)
      ?_ ?_ ?_ ?_ ?_
    · intro d hd
      rcases Nat.mem_divisors.mp hd with ⟨hdvd, hmn0⟩
      rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors]
      exact ⟨⟨Nat.gcd_dvd_right d m, left_ne_zero_of_mul hmn0⟩,
        ⟨Nat.gcd_dvd_right d n, right_ne_zero_of_mul hmn0⟩⟩
    · intro p hp
      rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hp
      exact Nat.mem_divisors.mpr ⟨mul_dvd_mul hp.1.1 hp.2.1, mul_ne_zero hp.1.2 hp.2.2⟩
    · intro d hd
      rcases Nat.mem_divisors.mp hd with ⟨hdvd, _⟩
      have hmul := hcop.gcd_mul d
      rw [Nat.gcd_eq_left hdvd] at hmul
      exact hmul.symm
    · intro p hp
      rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hp
      have hcop1 : Nat.Coprime p.2 m := hcop.symm.coprime_dvd_left hp.2.1
      have hcop2 : Nat.Coprime p.1 n := hcop.coprime_dvd_left hp.1.1
      ext
      · rw [mul_comm, hcop1.gcd_mul_left_cancel, Nat.gcd_eq_left hp.1.1]
      · rw [hcop2.gcd_mul_left_cancel, Nat.gcd_eq_left hp.2.1]
    · intro d hd
      rcases Nat.mem_divisors.mp hd with ⟨hdvd, _⟩
      have hcop_g : Nat.Coprime (Nat.gcd d m) (Nat.gcd d n) :=
        hcop.coprime_dvd_left (Nat.gcd_dvd_right d m) |>.coprime_dvd_right (Nat.gcd_dvd_right d n)
      have hmul : Nat.gcd d m * Nat.gcd d n = d := by
        have := hcop.gcd_mul d
        rw [Nat.gcd_eq_left hdvd] at this
        exact this.symm
      rw [hmul]
  rw [hbij]
  simp_rw [chi4Int_mul]
  rw [Finset.sum_product, ← Finset.sum_mul_sum]

/-- Exact equality `gCount n = ∑_{d ∣ n} χ₋₄(d)` for every `n ≥ 1`. -/
theorem gCount_eq_sum_divisors_chi4Int {n : ℕ} (hn : 1 ≤ n) :
    (gCount n : ℤ) = ∑ d ∈ n.divisors, chi4Int d := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => omega
  | prime_pow p k hp => exact (sum_divisors_chi4Int_prime_pow hp k).symm
  | coprime a b ha hb hcop iha ihb =>
    have ha1 : 1 ≤ a := by omega
    have hb1 : 1 ≤ b := by omega
    rw [gCount_mul_of_coprime ha1 hb1 hcop, Nat.cast_mul, iha ha1, ihb hb1,
      sum_divisors_chi4Int_mul_of_coprime hcop]

/-- **UNCONDITIONAL JACOBI'S TWO-SQUARE THEOREM (ZERO ASSUMPTIONS!)**:
for EVERY natural number `n ≥ 1`,
$$r_2(n) = 4 \sum_{d \mid n} \chi_{-4}(d).$$ -/
theorem jacobi_two_squares_formula (n : ℕ) (hn : 1 ≤ n) :
    (repTwoSquares n : ℤ) =
      4 * ∑ d ∈ n.divisors, (if d % 4 = 1 then (1 : ℤ) else if d % 4 = 3 then -1 else 0) := by
  rw [repTwoSquares_eq_four_mul_card_firstQuadG hn, Nat.cast_mul, Nat.cast_ofNat]
  change 4 * (gCount n : ℤ) = 4 * ∑ d ∈ n.divisors, chi4Int d
  rw [gCount_eq_sum_divisors_chi4Int hn]

/-- **Fermat's Two-Square Characterization** (immediate corollary of `gCount`):
a positive integer `n ≥ 1` is a sum of two integer squares if and only if every prime
`p ≡ 3 [MOD 4]` divides `n` to an even power. -/
theorem exists_two_squares_iff (n : ℕ) (hn : 1 ≤ n) :
    (∃ a b : ℤ, a ^ 2 + b ^ 2 = (n : ℤ)) ↔
      ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (n.factorization p) := by
  have hpos_iff : (∃ a b : ℤ, a ^ 2 + b ^ 2 = (n : ℤ)) ↔ 0 < gCount n := by
    have hr : (∃ a b : ℤ, a ^ 2 + b ^ 2 = (n : ℤ)) ↔ 0 < repTwoSquares n := by
      rw [repTwoSquares_eq_natCard]
      have : Finite { p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = (n : ℤ) } := finite_repTwoSquares n
      rw [Nat.card_pos_iff]
      constructor
      · rintro ⟨a, b, hab⟩; exact ⟨⟨⟨(a, b), hab⟩⟩, inferInstance⟩
      · rintro ⟨⟨⟨⟨a, b⟩, hab⟩⟩, _⟩; exact ⟨a, b, hab⟩
    rw [hr, repTwoSquares_eq_four_mul_card_firstQuadG hn]
    change 0 < 4 * gCount n ↔ 0 < gCount n
    omega
  rw [hpos_iff]
  clear hpos_iff
  induction n using Nat.recOnPrimeCoprime with
  | zero => omega
  | prime_pow p k hp =>
    have hp_cases : p = 2 ∨ p % 4 = 1 ∨ p % 4 = 3 := by
      rcases hp.eq_two_or_odd with rfl | hodd
      · left; rfl
      · right; omega
    rcases hp_cases with rfl | hp1 | hp3
    · rw [gCount_two_pow]
      simp only [zero_lt_one, true_iff]
      intro q hq hq3
      have hqp : 2 ≠ q := by omega
      rw [Nat.Prime.factorization_pow (by decide : Nat.Prime 2), Finsupp.single_apply, if_neg hqp]
      exact ⟨0, rfl⟩
    · rw [gCount_prime_one_mod_four_pow hp hp1]
      simp only [Nat.succ_pos, true_iff]
      intro q hq hq3
      have hqp : p ≠ q := by omega
      rw [hp.factorization_pow, Finsupp.single_apply, if_neg hqp]
      exact ⟨0, rfl⟩
    · rw [gCount_prime_three_mod_four_pow hp hp3]
      constructor
      · intro hpos q hq hq3
        by_cases hqp : p = q
        · subst hqp
          rw [hp.factorization_pow, Finsupp.single_eq_same]
          by_contra hnot
          rw [if_neg hnot] at hpos
          omega
        · rw [hp.factorization_pow, Finsupp.single_apply, if_neg hqp]
          exact ⟨0, rfl⟩
      · intro hall
        have hk : Even k := by
          have h := hall p hp hp3
          rwa [hp.factorization_pow, Finsupp.single_eq_same] at h
        rw [if_pos hk]; exact zero_lt_one
  | coprime a b ha hb hcop iha ihb =>
    have ha1 : 1 ≤ a := by omega
    have hb1 : 1 ≤ b := by omega
    have hmul_pos : 0 < gCount a * gCount b ↔ 0 < gCount a ∧ 0 < gCount b :=
      ⟨fun h => ⟨Nat.pos_of_mul_pos_right h, Nat.pos_of_mul_pos_left h⟩,
       fun ⟨h1, h2⟩ => Nat.mul_pos h1 h2⟩
    refine (iff_of_eq (congrArg (0 < ·) (gCount_mul_of_coprime ha1 hb1 hcop))).trans
      (hmul_pos.trans ((and_congr (iha ha1) (ihb hb1)).trans ?_))
    constructor
    · rintro ⟨ha', hb'⟩ p hp hp3
      rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply]
      exact (ha' p hp hp3).add (hb' p hp hp3)
    · intro hab
      constructor
      · intro p hp hp3
        by_cases hpa : p ∣ a
        · have hpb : ¬ p ∣ b := fun h => hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hpa h)
          have h0 : b.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpb
          have h := hab p hp hp3
          rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply, h0, add_zero] at h
          exact h
        · rw [Nat.factorization_eq_zero_of_not_dvd hpa]; exact ⟨0, rfl⟩
      · intro p hp hp3
        by_cases hpb : p ∣ b
        · have hpa : ¬ p ∣ a := fun h => hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h hpb)
          have h0 : a.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpa
          have h := hab p hp hp3
          rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply, h0, zero_add] at h
          exact h
        · rw [Nat.factorization_eq_zero_of_not_dvd hpb]; exact ⟨0, rfl⟩

/-- Helper: `LSeriesSummable` for `chi4` on `Re(s) > 1`. -/
lemma lseriesSummable_chi4 {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => chi4 (n : ZMod 4)) s := by
  have hsum1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  refine Summable.of_norm_bounded (g := fun n => ‖LSeries.term (1 : ℕ → ℂ) s n‖) hsum1.norm ?_
  intro n
  by_cases hn : n = 0
  · simp [LSeries.term, hn]
  · simp only [LSeries.term, hn, ↓reduceIte, Pi.one_apply, norm_div, norm_one]
    have hle : ‖chi4 (n : ZMod 4)‖ ≤ 1 := by
      rw [chi4_natCast]; unfold chi4Int; split_ifs <;> norm_num
    exact div_le_div_of_nonneg_right hle (norm_nonneg _)

/-- **Exact `LSeries` Factorization of `r₂(n)`**:
for every `s : ℂ` with `1 < s.re`,
$$L(r_2, s) = 4 \, \zeta(s) \, L(s, \chi_{-4}).$$ -/
theorem LSeries_repTwoSquares_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (repTwoSquares n : ℂ)) s =
      4 * riemannZeta s * DirichletCharacter.LFunction chi4 s := by
  have hsum1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hsumχ : LSeriesSummable (fun n : ℕ => chi4 (n : ZMod 4)) s := lseriesSummable_chi4 hs
  have hconv : LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => chi4 (n : ZMod 4)) =
      fun n : ℕ => if n = 0 then 0 else ((repTwoSquares n : ℂ) / 4) := by
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg hn, LSeries.convolution_def]
      dsimp only
      have hsum_anti :
          (∑ p ∈ n.divisorsAntidiagonal, (1 : ℕ → ℂ) p.1 * chi4 (p.2 : ZMod 4)) =
          ∑ d ∈ n.divisors, chi4 (d : ZMod 4) := by
        refine Finset.sum_nbij' (fun p => p.2) (fun d => (n / d, d)) ?_ ?_ ?_ ?_ ?_
        · intro p hp; exact Nat.snd_mem_divisors_of_mem_antidiagonal hp
        · intro d hd
          exact Nat.mem_divisorsAntidiagonal.mpr
            ⟨Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd), (Nat.mem_divisors.mp hd).2⟩
        · intro p hp
          rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, hn0⟩
          have hp2_pos : 0 < p.2 := Nat.pos_of_ne_zero (fun h0 => hn0 (by simp [← hpmul, h0]))
          ext
          · exact (Nat.eq_div_of_mul_eq_left hp2_pos.ne' hpmul).symm
          · rfl
        · intro _ _; rfl
        · intro p _; simp
      rw [hsum_anti]
      have hjac := congrArg (Int.cast (R := ℂ)) (jacobi_two_squares_formula n (Nat.pos_of_ne_zero hn))
      push_cast at hjac
      have hchi_sum : (∑ d ∈ n.divisors, chi4 (d : ZMod 4)) =
          ∑ d ∈ n.divisors, (chi4Int d : ℂ) :=
        Finset.sum_congr rfl fun d _ => chi4_natCast d
      rw [hchi_sum]
      have hjac' : (repTwoSquares n : ℂ) = 4 * ∑ d ∈ n.divisors, (chi4Int d : ℂ) := by
        simpa [chi4Int] using hjac
      rw [hjac']; ring
  have hL : LSeries (fun n : ℕ => if n = 0 then (0 : ℂ) else (repTwoSquares n : ℂ) / 4) s =
      riemannZeta s * DirichletCharacter.LFunction chi4 s := by
    rw [← hconv, LSeries_convolution' hsum1 hsumχ, LSeries_one_eq_riemannZeta hs,
      DirichletCharacter.LFunction_eq_LSeries chi4 hs]
  have hL4 : LSeries (fun n : ℕ => (repTwoSquares n : ℂ)) s =
      4 * LSeries (fun n : ℕ => if n = 0 then (0 : ℂ) else (repTwoSquares n : ℂ) / 4) s := by
    unfold LSeries
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · simp [LSeries.term, hn]; ring
  rw [hL4, hL]; ring

/-- **`ℕ+`-Indexed Dirichlet Series Identity for `r₂(n)`** on `Re(s) > 1`:
$$\sum_{n=1}^{\infty} r_2(n) \, n^{-s} = 4 \, \zeta(s) \, L(s, \chi_{-4}).$$ -/
theorem tsum_repTwoSquares_dirichletSeries {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ+, (repTwoSquares (n : ℕ) : ℂ) * ((n : ℕ) : ℂ) ^ (-s)) =
      4 * riemannZeta s * DirichletCharacter.LFunction chi4 s := by
  have hsum1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hsumχ : LSeriesSummable (fun n : ℕ => chi4 (n : ZMod 4)) s := lseriesSummable_chi4 hs
  have hsum_r2 : LSeriesSummable (fun n : ℕ => (repTwoSquares n : ℂ)) s := by
    have hconv_sum := (hsum1.convolution hsumχ).mul_left 4
    refine hconv_sum.congr fun n => ?_
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · simp only [LSeries.term, hn, ↓reduceIte]
      rw [LSeries.convolution_def]
      dsimp only
      have hsum_anti :
          (∑ p ∈ n.divisorsAntidiagonal, (1 : ℕ → ℂ) p.1 * chi4 (p.2 : ZMod 4)) =
          ∑ d ∈ n.divisors, (chi4Int d : ℂ) := by
        calc (∑ p ∈ n.divisorsAntidiagonal, (1 : ℕ → ℂ) p.1 * chi4 (p.2 : ZMod 4))
            = ∑ d ∈ n.divisors, chi4 (d : ZMod 4) := by
              refine Finset.sum_nbij' (fun p => p.2) (fun d => (n / d, d)) ?_ ?_ ?_ ?_ ?_
              · intro p hp; exact Nat.snd_mem_divisors_of_mem_antidiagonal hp
              · intro d hd
                exact Nat.mem_divisorsAntidiagonal.mpr
                  ⟨Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd), (Nat.mem_divisors.mp hd).2⟩
              · intro p hp
                rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, hn0⟩
                have hp2_pos : 0 < p.2 := Nat.pos_of_ne_zero (fun h0 => hn0 (by simp [← hpmul, h0]))
                ext
                · exact (Nat.eq_div_of_mul_eq_left hp2_pos.ne' hpmul).symm
                · rfl
              · intro _ _; rfl
              · intro p _; simp
          _ = ∑ d ∈ n.divisors, (chi4Int d : ℂ) := Finset.sum_congr rfl fun d _ => chi4_natCast d
      have hjac := congrArg (Int.cast (R := ℂ)) (jacobi_two_squares_formula n (Nat.pos_of_ne_zero hn))
      push_cast at hjac
      rw [hsum_anti]
      have hjac' : (repTwoSquares n : ℂ) = 4 * ∑ d ∈ n.divisors, (chi4Int d : ℂ) := by
        simpa [chi4Int] using hjac
      rw [hjac']; ring
  rw [← LSeries_repTwoSquares_eq hs]
  unfold LSeries
  rw [hsum_r2.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  let e : ℕ+ ≃ ℕ :=
    { toFun := fun n => (n : ℕ) - 1
      invFun := fun m => ⟨m + 1, Nat.succ_pos m⟩
      left_inv := fun n => Subtype.ext (Nat.sub_add_cancel n.pos)
      right_inv := fun m => Nat.add_sub_cancel m 1 }
  rw [← e.tsum_eq]
  refine tsum_congr fun n => ?_
  have hsucc : e n + 1 = (n : ℕ) := Nat.sub_add_cancel n.pos
  rw [hsucc]
  unfold LSeries.term
  rw [if_neg n.ne_zero, div_eq_mul_inv, Complex.cpow_neg]

/-- Explicit verification: `r₂(1) = 4`. -/
theorem repTwoSquares_one : repTwoSquares 1 = 4 := by
  have h := jacobi_two_squares_formula 1 (by decide)
  norm_num at h; exact_mod_cast h

/-- Explicit verification: `r₂(2) = 4`. -/
theorem repTwoSquares_two : repTwoSquares 2 = 4 := by
  have h := jacobi_two_squares_formula 2 (by decide)
  have hdiv : (2 : ℕ).divisors = {1, 2} := by decide
  rw [hdiv] at h; norm_num at h; exact_mod_cast h

/-- Explicit verification: `r₂(3) = 0`. -/
theorem repTwoSquares_three : repTwoSquares 3 = 0 := by
  have h := jacobi_two_squares_formula 3 (by decide)
  have hdiv : (3 : ℕ).divisors = {1, 3} := by decide
  rw [hdiv] at h; norm_num at h; exact_mod_cast h

/-- Explicit verification: `r₂(5) = 8`. -/
theorem repTwoSquares_five : repTwoSquares 5 = 8 := by
  have h := jacobi_two_squares_formula 5 (by decide)
  have hdiv : (5 : ℕ).divisors = {1, 5} := by decide
  rw [hdiv] at h; norm_num at h; exact_mod_cast h

end JacobiTwoSquares

/-! ## Section 3: Classical Quadratic Theta Identities & Jacobi's Abstruse Identity -/

section QuadraticThetaIdentities

/-- Canonical parity-splitting equivalence `(ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ`:
- `inl (u, v) ↦ (u + v, u - v)` (same parity: `x ≡ y [MOD 2]`)
- `inr (u, v) ↦ (u + v + 1, u - v)` (opposite parity: `x ≢ y [MOD 2]`). -/
def intProdParityEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun
    | Sum.inl (u, v) => (u + v, u - v)
    | Sum.inr (u, v) => (u + v + 1, u - v)
  invFun p :=
    if (2 : ℤ) ∣ p.1 + p.2 then
      Sum.inl ((p.1 + p.2) / 2, (p.1 - p.2) / 2)
    else
      Sum.inr ((p.1 + p.2 - 1) / 2, (p.1 - p.2 - 1) / 2)
  left_inv x := by
    rcases x with ⟨u, v⟩ | ⟨u, v⟩
    · have h : (2 : ℤ) ∣ (u + v) + (u - v) := ⟨u, by ring⟩
      simp only [h, ↓reduceIte]
      congr 1; ext <;> omega
    · have h : ¬ (2 : ℤ) ∣ (u + v + 1) + (u - v) := by
        rintro ⟨k, hk⟩; omega
      simp only [h, ↓reduceIte]
      congr 1; ext <;> omega
  right_inv p := by
    dsimp only
    split_ifs with h
    · dsimp only; ext <;> dsimp <;> omega
    · dsimp only; ext <;> dsimp <;> omega

/-- **First Quadratic Theta Identity**: `θ₃(τ)² = θ₃(2τ)² + θ₂(2τ)²`. -/
theorem theta3_sq_eq {τ : ℂ} (hτ : 0 < τ.im) :
    theta3 τ ^ 2 = theta3 (2 * τ) ^ 2 + theta2 (2 * τ) ^ 2 := by
  have h2τ : 0 < (2 * τ).im := by simp [hτ]
  have hn3 := summable_norm_theta3 hτ
  have hn3_2 := summable_norm_theta3 h2τ
  have hn2_2 := summable_norm_theta2 h2τ
  have hprod : Summable (fun p : ℤ × ℤ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * (p.1 : ℂ) ^ 2 * τ) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * (p.2 : ℂ) ^ 2 * τ)) :=
    Summable.of_norm ((hn3.mul_of_nonneg hn3 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
      fun p => (norm_mul _ _).symm)
  have hsq : theta3 τ ^ 2 =
      ∑' p : ℤ × ℤ,
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((p.1 : ℂ) ^ 2 + (p.2 : ℂ) ^ 2) * τ) := by
    rw [sq, theta3, hn3.of_norm.tsum_mul_tsum hn3.of_norm hprod]
    refine tsum_congr fun p => ?_
    rw [← Complex.exp_add]; congr 1; ring
  have hsum_p : Summable (fun p : ℤ × ℤ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((p.1 : ℂ) ^ 2 + (p.2 : ℂ) ^ 2) * τ)) :=
    hprod.congr fun p => by rw [← Complex.exp_add]; congr 1; ring
  rw [hsq, ← intProdParityEquiv.tsum_eq]
  have hsum_s : Summable (fun x : (ℤ × ℤ) ⊕ (ℤ × ℤ) =>
      Complex.exp ((Real.pi : ℂ) * Complex.I *
        (((intProdParityEquiv x).1 : ℂ) ^ 2 + ((intProdParityEquiv x).2 : ℂ) ^ 2) * τ)) :=
    intProdParityEquiv.summable_iff.mpr hsum_p
  rw [(hsum_s.comp_injective Sum.inl_injective).tsum_sum (hsum_s.comp_injective Sum.inr_injective)]
  congr 1
  · have hprod3 : Summable (fun p : ℤ × ℤ =>
        Complex.exp ((Real.pi : ℂ) * Complex.I * (p.1 : ℂ) ^ 2 * (2 * τ)) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * (p.2 : ℂ) ^ 2 * (2 * τ))) :=
      Summable.of_norm ((hn3_2.mul_of_nonneg hn3_2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
        fun p => (norm_mul _ _).symm)
    rw [sq, theta3, hn3_2.of_norm.tsum_mul_tsum hn3_2.of_norm hprod3]
    refine tsum_congr fun p => ?_
    rw [← Complex.exp_add]; congr 1
    simp only [intProdParityEquiv, Equiv.coe_fn_mk, Int.cast_add, Int.cast_sub]
    ring
  · have hprod2 : Summable (fun p : ℤ × ℤ =>
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((p.1 : ℂ) + 1 / 2) ^ 2 * (2 * τ)) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * ((p.2 : ℂ) + 1 / 2) ^ 2 * (2 * τ))) :=
      Summable.of_norm ((hn2_2.mul_of_nonneg hn2_2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
        fun p => (norm_mul _ _).symm)
    rw [sq, theta2, hn2_2.of_norm.tsum_mul_tsum hn2_2.of_norm hprod2]
    refine tsum_congr fun p => ?_
    rw [← Complex.exp_add]; congr 1
    simp only [intProdParityEquiv, Equiv.coe_fn_mk, Int.cast_add, Int.cast_sub, Int.cast_one]
    ring

/-- **Second Quadratic Theta Identity**: `θ₄(τ)² = θ₃(2τ)² - θ₂(2τ)²`. -/
theorem theta4_sq_eq {τ : ℂ} (hτ : 0 < τ.im) :
    theta4 τ ^ 2 = theta3 (2 * τ) ^ 2 - theta2 (2 * τ) ^ 2 := by
  have h2τ : 0 < (2 * τ).im := by simp [hτ]
  have hn4 := summable_norm_theta4 hτ
  have hn3_2 := summable_norm_theta3 h2τ
  have hn2_2 := summable_norm_theta2 h2τ
  have hprod : Summable (fun p : ℤ × ℤ =>
      ((-1 : ℂ) ^ p.1 * Complex.exp ((Real.pi : ℂ) * Complex.I * (p.1 : ℂ) ^ 2 * τ)) *
        ((-1 : ℂ) ^ p.2 * Complex.exp ((Real.pi : ℂ) * Complex.I * (p.2 : ℂ) ^ 2 * τ))) :=
    Summable.of_norm ((hn4.mul_of_nonneg hn4 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
      fun p => (norm_mul _ _).symm)
  have hsq : theta4 τ ^ 2 =
      ∑' p : ℤ × ℤ,
        (-1 : ℂ) ^ (p.1 + p.2) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * ((p.1 : ℂ) ^ 2 + (p.2 : ℂ) ^ 2) * τ) := by
    rw [sq, theta4, hn4.of_norm.tsum_mul_tsum hn4.of_norm hprod]
    refine tsum_congr fun p => ?_
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    have hexp : Complex.exp ((Real.pi : ℂ) * Complex.I * (p.1 : ℂ) ^ 2 * τ) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * (p.2 : ℂ) ^ 2 * τ) =
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((p.1 : ℂ) ^ 2 + (p.2 : ℂ) ^ 2) * τ) := by
      rw [← Complex.exp_add]; congr 1; ring
    linear_combination (-1 : ℂ) ^ p.1 * (-1 : ℂ) ^ p.2 * hexp
  have hsum_p : Summable (fun p : ℤ × ℤ =>
      (-1 : ℂ) ^ (p.1 + p.2) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((p.1 : ℂ) ^ 2 + (p.2 : ℂ) ^ 2) * τ)) :=
    hprod.congr fun p => by
      rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      have hexp : Complex.exp ((Real.pi : ℂ) * Complex.I * (p.1 : ℂ) ^ 2 * τ) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * (p.2 : ℂ) ^ 2 * τ) =
          Complex.exp ((Real.pi : ℂ) * Complex.I * ((p.1 : ℂ) ^ 2 + (p.2 : ℂ) ^ 2) * τ) := by
        rw [← Complex.exp_add]; congr 1; ring
      linear_combination (-1 : ℂ) ^ p.1 * (-1 : ℂ) ^ p.2 * hexp
  rw [hsq, ← intProdParityEquiv.tsum_eq]
  have hsum_s : Summable (fun x : (ℤ × ℤ) ⊕ (ℤ × ℤ) =>
      (-1 : ℂ) ^ ((intProdParityEquiv x).1 + (intProdParityEquiv x).2) *
        Complex.exp ((Real.pi : ℂ) * Complex.I *
          (((intProdParityEquiv x).1 : ℂ) ^ 2 + ((intProdParityEquiv x).2 : ℂ) ^ 2) * τ)) :=
    intProdParityEquiv.summable_iff.mpr hsum_p
  rw [(hsum_s.comp_injective Sum.inl_injective).tsum_sum (hsum_s.comp_injective Sum.inr_injective),
    sub_eq_add_neg]
  congr 1
  · have hprod3 : Summable (fun p : ℤ × ℤ =>
        Complex.exp ((Real.pi : ℂ) * Complex.I * (p.1 : ℂ) ^ 2 * (2 * τ)) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * (p.2 : ℂ) ^ 2 * (2 * τ))) :=
      Summable.of_norm ((hn3_2.mul_of_nonneg hn3_2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
        fun p => (norm_mul _ _).symm)
    rw [sq, theta3, hn3_2.of_norm.tsum_mul_tsum hn3_2.of_norm hprod3]
    refine tsum_congr fun p => ?_
    have hsign : (-1 : ℂ) ^ ((p.1 + p.2) + (p.1 - p.2)) = 1 := by
      rw [show (p.1 + p.2) + (p.1 - p.2) = 2 * p.1 by ring, zpow_mul]; norm_num
    simp only [intProdParityEquiv, Equiv.coe_fn_mk, hsign, one_mul]
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  · have hprod2 : Summable (fun p : ℤ × ℤ =>
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((p.1 : ℂ) + 1 / 2) ^ 2 * (2 * τ)) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * ((p.2 : ℂ) + 1 / 2) ^ 2 * (2 * τ))) :=
      Summable.of_norm ((hn2_2.mul_of_nonneg hn2_2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
        fun p => (norm_mul _ _).symm)
    rw [sq, theta2, hn2_2.of_norm.tsum_mul_tsum hn2_2.of_norm hprod2, ← tsum_neg]
    refine tsum_congr fun p => ?_
    have hsign : (-1 : ℂ) ^ ((p.1 + p.2 + 1) + (p.1 - p.2)) = -1 := by
      rw [show (p.1 + p.2 + 1) + (p.1 - p.2) = 2 * p.1 + 1 by ring,
        zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]; norm_num
    simp only [intProdParityEquiv, Equiv.coe_fn_mk, hsign, neg_one_mul]
    congr 1
    rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- **Third Quadratic Theta Identity**: `θ₂(τ)² = 2 θ₃(2τ) θ₂(2τ)`. -/
theorem theta2_sq_eq {τ : ℂ} (hτ : 0 < τ.im) :
    theta2 τ ^ 2 = 2 * theta3 (2 * τ) * theta2 (2 * τ) := by
  have h2τ : 0 < (2 * τ).im := by simp [hτ]
  have hn2 := summable_norm_theta2 hτ
  have hn3_2 := summable_norm_theta3 h2τ
  have hn2_2 := summable_norm_theta2 h2τ
  have hprod : Summable (fun p : ℤ × ℤ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((p.1 : ℂ) + 1 / 2) ^ 2 * τ) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((p.2 : ℂ) + 1 / 2) ^ 2 * τ)) :=
    Summable.of_norm ((hn2.mul_of_nonneg hn2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
      fun p => (norm_mul _ _).symm)
  have hsq : theta2 τ ^ 2 =
      ∑' p : ℤ × ℤ,
        Complex.exp ((Real.pi : ℂ) * Complex.I *
          (((p.1 : ℂ) + 1 / 2) ^ 2 + ((p.2 : ℂ) + 1 / 2) ^ 2) * τ) := by
    rw [sq, theta2, hn2.of_norm.tsum_mul_tsum hn2.of_norm hprod]
    refine tsum_congr fun p => ?_
    rw [← Complex.exp_add]; congr 1; ring
  have hsum_p : Summable (fun p : ℤ × ℤ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I *
        (((p.1 : ℂ) + 1 / 2) ^ 2 + ((p.2 : ℂ) + 1 / 2) ^ 2) * τ)) :=
    hprod.congr fun p => by rw [← Complex.exp_add]; congr 1; ring
  rw [hsq, ← intProdParityEquiv.tsum_eq]
  have hsum_s : Summable (fun x : (ℤ × ℤ) ⊕ (ℤ × ℤ) =>
      Complex.exp ((Real.pi : ℂ) * Complex.I *
        ((((intProdParityEquiv x).1 : ℂ) + 1 / 2) ^ 2 +
          (((intProdParityEquiv x).2 : ℂ) + 1 / 2) ^ 2) * τ)) :=
    intProdParityEquiv.summable_iff.mpr hsum_p
  rw [(hsum_s.comp_injective Sum.inl_injective).tsum_sum (hsum_s.comp_injective Sum.inr_injective),
    two_mul, add_mul]
  have hprod32 : Summable (fun p : ℤ × ℤ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * (p.1 : ℂ) ^ 2 * (2 * τ)) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((p.2 : ℂ) + 1 / 2) ^ 2 * (2 * τ))) :=
    Summable.of_norm ((hn3_2.mul_of_nonneg hn2_2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
      fun p => (norm_mul _ _).symm)
  have hprod23 : Summable (fun p : ℤ × ℤ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((p.1 : ℂ) + 1 / 2) ^ 2 * (2 * τ)) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * (p.2 : ℂ) ^ 2 * (2 * τ))) :=
    Summable.of_norm ((hn2_2.mul_of_nonneg hn3_2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
      fun p => (norm_mul _ _).symm)
  congr 1
  · rw [mul_comm (theta3 (2 * τ)), theta2, theta3, hn2_2.of_norm.tsum_mul_tsum hn3_2.of_norm hprod23]
    refine tsum_congr fun ⟨u, v⟩ => ?_
    rw [← Complex.exp_add]; congr 1
    simp only [intProdParityEquiv, Equiv.coe_fn_mk, Int.cast_add, Int.cast_sub]
    ring
  · rw [theta3, theta2, hn3_2.of_norm.tsum_mul_tsum hn2_2.of_norm hprod32]
    let eShift : ℤ × ℤ ≃ ℤ × ℤ :=
      { toFun := fun p => (p.1 - 1, p.2)
        invFun := fun p => (p.1 + 1, p.2)
        left_inv := fun p => Prod.ext (by dsimp; ring) rfl
        right_inv := fun p => Prod.ext (by dsimp; ring) rfl }
    rw [← eShift.tsum_eq]
    refine tsum_congr fun ⟨u, v⟩ => ?_
    rw [← Complex.exp_add]; congr 1
    simp only [intProdParityEquiv, eShift, Equiv.coe_fn_mk, Int.cast_add, Int.cast_sub, Int.cast_one]
    ring

/-- **Jacobi's Abstruse Identity (`Aequatio Identica Satis Abstrusa`)**:
for every `τ ∈ ℂ` with `0 < τ.im`,
$$\theta_3(\tau)^4 = \theta_4(\tau)^4 + \theta_2(\tau)^4.$$ -/
theorem jacobi_abstruse_identity {τ : ℂ} (hτ : 0 < τ.im) :
    theta3 τ ^ 4 = theta4 τ ^ 4 + theta2 τ ^ 4 := by
  calc theta3 τ ^ 4
      = (theta3 τ ^ 2) ^ 2 := by ring
    _ = (theta3 (2 * τ) ^ 2 + theta2 (2 * τ) ^ 2) ^ 2 := by rw [theta3_sq_eq hτ]
    _ = (theta3 (2 * τ) ^ 2 - theta2 (2 * τ) ^ 2) ^ 2 +
          (2 * theta3 (2 * τ) * theta2 (2 * τ)) ^ 2 := by ring
    _ = (theta4 τ ^ 2) ^ 2 + (theta2 τ ^ 2) ^ 2 := by rw [← theta4_sq_eq hτ, ← theta2_sq_eq hτ]
    _ = theta4 τ ^ 4 + theta2 τ ^ 4 := by ring

/-- `T`-shift of `θ₃`: `θ₃(τ + 1) = θ₄(τ)`. -/
theorem theta3_add_one (τ : ℂ) : theta3 (τ + 1) = theta4 τ := by
  unfold theta3 theta4
  refine tsum_congr fun n => ?_
  have hexp : (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ + 1) =
      (n ^ 2 : ℤ) * ((Real.pi : ℂ) * Complex.I) +
        (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ := by
    push_cast; ring
  rw [hexp, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  congr 1
  rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h1 : (-1 : ℂ) ^ ((k + k) ^ 2) = 1 := by
      rw [show (k + k) ^ 2 = 2 * (2 * k ^ 2) by ring, zpow_mul]; norm_num
    have h2 : (-1 : ℂ) ^ (k + k) = 1 := by
      rw [show k + k = 2 * k by ring, zpow_mul]; norm_num
    rw [h1, h2]
  · have h1 : (-1 : ℂ) ^ ((2 * k + 1) ^ 2) = -1 := by
      rw [show (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 by ring,
        zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]; norm_num
    have h2 : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
      rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]; norm_num
    rw [h1, h2]

/-- `T`-shift of `θ₄`: `θ₄(τ + 1) = θ₃(τ)`. -/
theorem theta4_add_one (τ : ℂ) : theta4 (τ + 1) = theta3 τ := by
  unfold theta3 theta4
  refine tsum_congr fun n => ?_
  have hexp : (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ + 1) =
      (n ^ 2 : ℤ) * ((Real.pi : ℂ) * Complex.I) +
        (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ := by
    push_cast; ring
  rw [hexp, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I, ← mul_assoc]
  have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ (n ^ 2) = 1 := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [show (k + k) + (k + k) ^ 2 = 2 * (k + 2 * k ^ 2) by ring, zpow_mul]; norm_num
    · rw [show (2 * k + 1) + (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 3 * k + 1) by ring, zpow_mul]
      norm_num
  rw [hsign, one_mul]

/-- `T`-shift of `θ₂`: `θ₂(τ + 1) = exp(π i / 4) * θ₂(τ)`. -/
theorem theta2_add_one (τ : ℂ) :
    theta2 (τ + 1) = Complex.exp ((Real.pi : ℂ) * Complex.I / 4) * theta2 τ := by
  unfold theta2
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have heven : ∃ m : ℤ, n ^ 2 + n = 2 * m := by
    rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨2 * k ^ 2 + k, by ring⟩
    · exact ⟨2 * k ^ 2 + 3 * k + 1, by ring⟩
  rcases heven with ⟨m, hm⟩
  have hexp : (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * (τ + 1) =
      (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
        ((Real.pi : ℂ) * Complex.I / 4 +
          (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * τ) := by
    have hmC : (n : ℂ) ^ 2 + (n : ℂ) = 2 * (m : ℂ) := by exact_mod_cast hm
    linear_combination (Real.pi : ℂ) * Complex.I * hmC
  rw [hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_add]

/-- `T`-shift of `θ₂⁴`: `θ₂(τ + 1)⁴ = -θ₂(τ)⁴`. -/
theorem theta2_add_one_pow_four (τ : ℂ) : theta2 (τ + 1) ^ 4 = -(theta2 τ ^ 4) := by
  rw [theta2_add_one, mul_pow, ← Complex.exp_nat_mul]
  have h4 : (4 : ℕ) * ((Real.pi : ℂ) * Complex.I / 4) = (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [h4, Complex.exp_pi_mul_I]; ring

end QuadraticThetaIdentities

/-! ## Section 4: Unconditional Jacobi's Eight-Square Theorem (`jacobi_eight_squares_formula`) -/

section JacobiEightSquares

/-- Upper half-plane scaling `τ ↦ 2τ`. -/
def mulTwoUHP (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨2 * (τ : ℂ), by simp [τ.im_pos]⟩

/-- Upper half-plane scaling `τ ↦ τ / 2`. -/
def divTwoUHP (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(τ : ℂ) / 2, by simp [τ.im_pos]⟩

/-- Upper half-plane affine map `τ ↦ (τ + 1) / 2`. -/
def addOneDivTwoUHP (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨((τ : ℂ) + 1) / 2, by simp [τ.im_pos]⟩

/-- **Exact `θ₂(τ)⁸` Eisenstein Identity**:
$$\theta_2(\tau)^8 = \frac{16}{15}\left(E_4(\tau) - E_4(2\tau)\right).$$ -/
theorem theta2_pow_eight_eq (τ : UpperHalfPlane) :
    theta2 (τ : ℂ) ^ 8 = (16 / 15 : ℂ) * (E4 τ - E4 (mulTwoUHP τ)) := by
  have hE1 := E8_jacobiTheta_eq_E4 τ
  have hE2 := E8_jacobiTheta_eq_E4 (mulTwoUHP τ)
  have hτ : 0 < (τ : ℂ).im := τ.im_pos
  have h2τ : 0 < (2 * (τ : ℂ)).im := by simpa using τ.im_pos
  have h3 := theta3_sq_eq hτ
  have h4 := theta4_sq_eq hτ
  have h2 := theta2_sq_eq hτ
  have hab2 := jacobi_abstruse_identity h2τ
  change (1 / 2 : ℂ) * (theta3 (2 * (τ : ℂ)) ^ 8 + theta4 (2 * (τ : ℂ)) ^ 8 +
      theta2 (2 * (τ : ℂ)) ^ 8) = E4 (mulTwoUHP τ) at hE2
  set A : ℂ := theta3 (2 * (τ : ℂ)) ^ 2
  set B : ℂ := theta2 (2 * (τ : ℂ)) ^ 2
  have hth3_8 : theta3 (τ : ℂ) ^ 8 = (A + B) ^ 4 := by
    calc theta3 (τ : ℂ) ^ 8 = (theta3 (τ : ℂ) ^ 2) ^ 4 := by ring
      _ = (A + B) ^ 4 := by rw [h3]
  have hth4_8 : theta4 (τ : ℂ) ^ 8 = (A - B) ^ 4 := by
    calc theta4 (τ : ℂ) ^ 8 = (theta4 (τ : ℂ) ^ 2) ^ 4 := by ring
      _ = (A - B) ^ 4 := by rw [h4]
  have hth2_4 : theta2 (τ : ℂ) ^ 4 = 4 * A * B := by
    calc theta2 (τ : ℂ) ^ 4 = (theta2 (τ : ℂ) ^ 2) ^ 2 := by ring
      _ = (2 * theta3 (2 * (τ : ℂ)) * theta2 (2 * (τ : ℂ))) ^ 2 := by rw [h2]
      _ = 4 * A * B := by simp only [A, B]; ring
  have hth2_8 : theta2 (τ : ℂ) ^ 8 = 16 * A ^ 2 * B ^ 2 := by
    calc theta2 (τ : ℂ) ^ 8 = (theta2 (τ : ℂ) ^ 4) ^ 2 := by ring
      _ = (4 * A * B) ^ 2 := by rw [hth2_4]
      _ = 16 * A ^ 2 * B ^ 2 := by ring
  have hth4_2_8 : theta4 (2 * (τ : ℂ)) ^ 8 = (A ^ 2 - B ^ 2) ^ 2 := by
    have hsub : theta4 (2 * (τ : ℂ)) ^ 4 = A ^ 2 - B ^ 2 := by
      simp only [A, B]; linear_combination -hab2
    calc theta4 (2 * (τ : ℂ)) ^ 8 = (theta4 (2 * (τ : ℂ)) ^ 4) ^ 2 := by ring
      _ = (A ^ 2 - B ^ 2) ^ 2 := by rw [hsub]
  have hth3_2_8 : theta3 (2 * (τ : ℂ)) ^ 8 = A ^ 4 := by simp only [A]; ring
  have hth2_2_8 : theta2 (2 * (τ : ℂ)) ^ 8 = B ^ 4 := by simp only [B]; ring
  rw [hth3_8, hth4_8, hth2_8] at hE1
  rw [hth3_2_8, hth4_2_8, hth2_2_8] at hE2
  rw [hth2_8]
  linear_combination (16 / 15 : ℂ) * (hE1 - hE2)

/-- **Exact `θ₄(τ)⁸` Eisenstein Identity** (by applying `S` to `theta2_pow_eight_eq`):
$$\theta_4(\tau)^8 = \frac{16}{15} E_4(\tau) - \frac{1}{15} E_4(\tau/2).$$ -/
theorem theta4_pow_eight_eq (τ : UpperHalfPlane) :
    theta4 (τ : ℂ) ^ 8 = (16 / 15 : ℂ) * E4 τ - (1 / 15 : ℂ) * E4 (divTwoUHP τ) := by
  have h := theta2_pow_eight_eq (ModularGroup.S • τ)
  rw [theta2_S_smul τ, mul_pow] at h
  have hpow8 : ((-Complex.I * (τ : ℂ)) ^ ((1 : ℂ) / 2)) ^ 8 = (τ : ℂ) ^ 4 := by
    rw [← Complex.cpow_nat_mul]
    have h1 : (8 : ℕ) * ((1 : ℂ) / 2) = (4 : ℕ) := by push_cast; ring
    rw [h1, Complex.cpow_natCast, mul_pow]
    have hI4 : (-Complex.I) ^ 4 = 1 := by
      calc (-Complex.I) ^ 4 = ((-Complex.I) ^ 2) ^ 2 := by ring
        _ = (-1) ^ 2 := by simp [Complex.I_sq]
        _ = 1 := by norm_num
    rw [hI4, one_mul]
  rw [hpow8, E4_S_smul τ] at h
  have hmulS : mulTwoUHP (ModularGroup.S • τ) = ModularGroup.S • (divTwoUHP τ) := by
    apply UpperHalfPlane.ext
    change 2 * ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) =
      ((ModularGroup.S • divTwoUHP τ : UpperHalfPlane) : ℂ)
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_S_smul]
    change 2 * (-(τ : ℂ))⁻¹ = (-((τ : ℂ) / 2))⁻¹
    field_simp [τ.ne_zero]
  rw [hmulS, E4_S_smul (divTwoUHP τ)] at h
  have hdiv4 : ((divTwoUHP τ : ℂ)) ^ 4 = (τ : ℂ) ^ 4 / 16 := by
    change ((τ : ℂ) / 2) ^ 4 = (τ : ℂ) ^ 4 / 16; ring
  rw [hdiv4] at h
  have hτ4_ne : (τ : ℂ) ^ 4 ≠ 0 := pow_ne_zero 4 τ.ne_zero
  apply mul_left_cancel₀ hτ4_ne
  linear_combination h

/-- **Exact `θ₃(τ)⁸` Eisenstein Identity** (by applying `T` to `theta4_pow_eight_eq`):
$$\theta_3(\tau)^8 = \frac{16}{15} E_4(\tau) - \frac{1}{15} E_4\left(\frac{\tau + 1}{2}\right).$$ -/
theorem theta3_pow_eight_eq (τ : UpperHalfPlane) :
    theta3 (τ : ℂ) ^ 8 = (16 / 15 : ℂ) * E4 τ - (1 / 15 : ℂ) * E4 (addOneDivTwoUHP τ) := by
  have h := theta4_pow_eight_eq (ModularGroup.T • τ)
  have hT_coe : ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.modular_T_smul]
    simp [UpperHalfPlane.coe_vadd, add_comm]
  rw [hT_coe, theta4_add_one, E4_T_smul τ] at h
  have hdivT : divTwoUHP (ModularGroup.T • τ) = addOneDivTwoUHP τ := by
    apply UpperHalfPlane.ext
    change ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) / 2 = ((τ : ℂ) + 1) / 2
    rw [hT_coe]
  rwa [hdivT] at h

/-- Elementary divisor identity for Jacobi's eight-square arithmetic function:
for every `n ≥ 1`,
$$16 \sum_{d \mid n} (-1)^{n + d} d^3 =
  \begin{cases} 16 \sigma_3(n) & \text{if } 2 \nmid n, \\ 256 \sigma_3(n/2) - 16 \sigma_3(n) & \text{if } 2 \mid n. \end{cases}$$ -/
lemma jacobi_eight_divisor_identity (n : ℕ) :
    (16 : ℤ) * (∑ d ∈ n.divisors, (-1 : ℤ) ^ (n + d) * (d : ℤ) ^ 3) =
      (if 2 ∣ n then (256 : ℤ) * (ArithmeticFunction.sigma 3 (n / 2) : ℤ) else 0) -
        (16 : ℤ) * (-1 : ℤ) ^ n * (ArithmeticFunction.sigma 3 n : ℤ) := by
  by_cases hn0 : n = 0
  · subst hn0; simp
  · by_cases hev : 2 ∣ n
    · rcases hev with ⟨m, rfl⟩
      rw [if_pos ⟨m, rfl⟩]
      have hdiv2 : 2 * m / 2 = m := Nat.mul_div_cancel_left m (by decide)
      rw [hdiv2]
      have hneg2m : (-1 : ℤ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
      rw [hneg2m, mul_one]
      -- Split `(2 * m).divisors` into even divisors `d = 2e` (`e ∣ m`) and odd divisors
      have hsplit := (Finset.sum_filter_add_sum_filter_not (2 * m).divisors (fun d => 2 ∣ d)
        (fun d => (-1 : ℤ) ^ (2 * m + d) * (d : ℤ) ^ 3)).symm
      have hsplit_all := (Finset.sum_filter_add_sum_filter_not (2 * m).divisors (fun d => 2 ∣ d)
        (fun d => (d : ℤ) ^ 3)).symm
      have heven_part : (∑ d ∈ (2 * m).divisors.filter (fun d => 2 ∣ d),
          (-1 : ℤ) ^ (2 * m + d) * (d : ℤ) ^ 3) =
          8 * (ArithmeticFunction.sigma 3 m : ℤ) := by
        rw [ArithmeticFunction.sigma_apply]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_nbij' (fun d => d / 2) (fun e => 2 * e) ?_ ?_ ?_ ?_ ?_
        · intro d hd
          rw [Finset.mem_filter, Nat.mem_divisors] at hd
          rcases hd.2 with ⟨e, rfl⟩
          rw [Nat.mul_div_cancel_left e (by decide)]
          exact Nat.mem_divisors.mpr
            ⟨(Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hd.1.1, right_ne_zero_of_mul hd.1.2⟩
        · intro e he
          rcases Nat.mem_divisors.mp he with ⟨he_dvd, hm0⟩
          rw [Finset.mem_filter, Nat.mem_divisors]
          exact ⟨⟨Nat.mul_dvd_mul_left 2 he_dvd, mul_ne_zero (by decide) hm0⟩, ⟨e, rfl⟩⟩
        · intro d hd
          rw [Finset.mem_filter] at hd
          exact Nat.mul_div_cancel' hd.2
        · intro e _
          exact Nat.mul_div_cancel_left e (by decide)
        · intro d hd
          rw [Finset.mem_filter] at hd
          rcases hd.2 with ⟨e, rfl⟩
          rw [Nat.mul_div_cancel_left e (by decide)]
          have h1 : (-1 : ℤ) ^ (2 * m + 2 * e) = 1 := by
            rw [show 2 * m + 2 * e = 2 * (m + e) by omega, pow_mul]; norm_num
          rw [h1, one_mul]; push_cast; ring
      have heven_part2 : (∑ d ∈ (2 * m).divisors.filter (fun d => 2 ∣ d), (d : ℤ) ^ 3) =
          8 * (ArithmeticFunction.sigma 3 m : ℤ) := by
        rw [← heven_part]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [Finset.mem_filter] at hd
        rcases hd.2 with ⟨e, rfl⟩
        have h1 : (-1 : ℤ) ^ (2 * m + 2 * e) = 1 := by
          rw [show 2 * m + 2 * e = 2 * (m + e) by omega, pow_mul]; norm_num
        rw [h1, one_mul]
      have hodd_part : (∑ d ∈ (2 * m).divisors.filter (fun d => ¬ 2 ∣ d),
          (-1 : ℤ) ^ (2 * m + d) * (d : ℤ) ^ 3) =
          -(∑ d ∈ (2 * m).divisors.filter (fun d => ¬ 2 ∣ d), (d : ℤ) ^ 3) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [Finset.mem_filter] at hd
        have hodd : ∃ k, d = 2 * k + 1 := by
          rcases Nat.even_or_odd d with ⟨k, rfl⟩ | ⟨k, rfl⟩
          · exfalso; exact hd.2 ⟨k, by omega⟩
          · exact ⟨k, rfl⟩
        rcases hodd with ⟨k, rfl⟩
        have h1 : (-1 : ℤ) ^ (2 * m + (2 * k + 1)) = -1 := by
          rw [show 2 * m + (2 * k + 1) = 2 * (m + k) + 1 by omega, pow_succ, pow_mul]; norm_num
        rw [h1, neg_one_mul]
      have hsig_all : (ArithmeticFunction.sigma 3 (2 * m) : ℤ) =
          ∑ d ∈ (2 * m).divisors, (d : ℤ) ^ 3 := by
        rw [ArithmeticFunction.sigma_apply]; push_cast; rfl
      rw [hsplit, heven_part, hodd_part]
      rw [hsig_all, hsplit_all, heven_part2]
      ring
    · rw [if_neg hev, zero_sub]
      have hodd_n : ∃ k, n = 2 * k + 1 := by
        rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · exfalso; exact hev ⟨k, by omega⟩
        · exact ⟨k, rfl⟩
      rcases hodd_n with ⟨k, rfl⟩
      have hneg_n : (-1 : ℤ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
      rw [hneg_n]
      have hsum_eq : (∑ d ∈ (2 * k + 1).divisors, (-1 : ℤ) ^ (2 * k + 1 + d) * (d : ℤ) ^ 3) =
          (ArithmeticFunction.sigma 3 (2 * k + 1) : ℤ) := by
        rw [ArithmeticFunction.sigma_apply]; push_cast
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd_odd : ¬ 2 ∣ d := fun h2d => hev (dvd_trans h2d (Nat.dvd_of_mem_divisors hd))
        rcases Nat.even_or_odd d with ⟨r, rfl⟩ | ⟨r, rfl⟩
        · exfalso; exact hd_odd ⟨r, by omega⟩
        · have h1 : (-1 : ℤ) ^ (2 * k + 1 + (2 * r + 1)) = 1 := by
            rw [show 2 * k + 1 + (2 * r + 1) = 2 * (k + r + 1) by omega, pow_mul]; norm_num
          rw [h1, one_mul]
      rw [hsum_eq]; ring

/-- Helper: summability of `σ_k(n) * r^n` for `r ∈ (0, 1)`. -/
lemma summable_sigma_mul_pow (k : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (ArithmeticFunction.sigma k n : ℝ) * r ^ n) := by
  have hle : ∀ n : ℕ, (ArithmeticFunction.sigma k n : ℝ) ≤ (n : ℝ) ^ (k + 1) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp
    · rw [ArithmeticFunction.sigma_apply]
      push_cast
      calc (∑ d ∈ n.divisors, (d : ℝ) ^ k)
          ≤ ∑ _d ∈ n.divisors, (n : ℝ) ^ k := by
            refine Finset.sum_le_sum fun d hd => ?_
            have hd_le : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hd)
            exact pow_le_pow_left₀ (Nat.cast_nonneg d) (by exact_mod_cast hd_le) k
        _ = (n.divisors.card : ℝ) * (n : ℝ) ^ k := by simp
        _ ≤ (n : ℝ) * (n : ℝ) ^ k := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have hcard : n.divisors.card ≤ n := by
              have hsub : n.divisors ⊆ Finset.Icc 1 n := fun d hd => by
                rw [Finset.mem_Icc]
                exact ⟨Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) (Nat.pos_of_ne_zero hn),
                  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hd)⟩
              exact (Finset.card_le_card hsub).trans (by simp)
            exact_mod_cast hcard
        _ = (n : ℝ) ^ (k + 1) := by rw [pow_succ']
  have hpoly : Summable (fun n : ℕ => (n : ℝ) ^ (k + 1) * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (k + 1) (by rw [Real.norm_of_nonneg hr0.le]; exact hr1)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hpoly
  exact mul_le_mul_of_nonneg_right (hle n) (pow_nonneg hr0.le n)

/-- **UNCONDITIONAL JACOBI'S EIGHT-SQUARE THEOREM (ZERO ASSUMPTIONS!)**:
for EVERY natural number `n ≥ 1`,
$$r_8(n) = 16 \sum_{d \mid n} (-1)^{n + d} d^3.$$ -/
theorem jacobi_eight_squares_formula (n : ℕ) (hn : 1 ≤ n) :
    (repEightSquares n : ℤ) =
      16 * ∑ d ∈ n.divisors, (-1 : ℤ) ^ (n + d) * (d : ℤ) ^ 3 := by
  let a : ℕ → ℂ := fun m => (repEightSquares m : ℂ)
  let b : ℕ → ℂ := fun m =>
    if m = 0 then 1
    else (16 : ℂ) * ∑ d ∈ m.divisors, (-1 : ℂ) ^ (m + d) * (d : ℂ) ^ 3
  have ha : ∀ r ∈ Set.Ioo (0 : ℝ) 1, Summable (fun m : ℕ => ‖a m‖ * r ^ m) := fun r hr =>
    summable_repSquares_mul_pow 8 hr.1 hr.2
  have hb_formula : ∀ m : ℕ, 1 ≤ m →
      b m = (if 2 ∣ m then (256 : ℂ) * (ArithmeticFunction.sigma 3 (m / 2) : ℂ) else 0) -
        (16 : ℂ) * (-1 : ℂ) ^ m * (ArithmeticFunction.sigma 3 m : ℂ) := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    simp only [b, hm0, ↓reduceIte]
    have h := congrArg (Int.cast (R := ℂ)) (jacobi_eight_divisor_identity m)
    push_cast at h
    exact h
  have hb : ∀ r ∈ Set.Ioo (0 : ℝ) 1, Summable (fun m : ℕ => ‖b m‖ * r ^ m) := by
    intro r hr
    have hsig1 := summable_sigma_mul_pow 3 hr.1 hr.2
    have hsig2 : Summable (fun m : ℕ => (ArithmeticFunction.sigma 3 (m / 2) : ℝ) * r ^ m) := by
      have hpoly : Summable (fun m : ℕ => (m : ℝ) ^ 4 * r ^ m) :=
        summable_pow_mul_geometric_of_norm_lt_one 4 (by rw [Real.norm_of_nonneg hr.1.le]; exact hr.2)
      refine Summable.of_nonneg_of_le (fun m => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr.1.le m))
        (fun m => ?_) hpoly
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr.1.le m)
      have hle : (ArithmeticFunction.sigma 3 (m / 2) : ℝ) ≤ ((m / 2 : ℕ) : ℝ) ^ 4 := by
        by_cases hm2 : m / 2 = 0
        · rw [hm2]; simp
        · rw [ArithmeticFunction.sigma_apply]; push_cast
          calc (∑ d ∈ (m / 2).divisors, (d : ℝ) ^ 3)
              ≤ ∑ _d ∈ (m / 2).divisors, ((m / 2 : ℕ) : ℝ) ^ 3 := by
                refine Finset.sum_le_sum fun d hd => ?_
                have hd_le := Nat.le_of_dvd (Nat.pos_of_ne_zero hm2) (Nat.dvd_of_mem_divisors hd)
                exact pow_le_pow_left₀ (Nat.cast_nonneg d) (by exact_mod_cast hd_le) 3
            _ = ((m / 2).divisors.card : ℝ) * ((m / 2 : ℕ) : ℝ) ^ 3 := by simp
            _ ≤ ((m / 2 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) ^ 3 := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                have hcard : (m / 2).divisors.card ≤ m / 2 := by
                  have hsub : (m / 2).divisors ⊆ Finset.Icc 1 (m / 2) := fun d hd => by
                    rw [Finset.mem_Icc]
                    exact ⟨Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd)
                      (Nat.pos_of_ne_zero hm2),
                      Nat.le_of_dvd (Nat.pos_of_ne_zero hm2) (Nat.dvd_of_mem_divisors hd)⟩
                  exact (Finset.card_le_card hsub).trans (by simp)
                exact_mod_cast hcard
            _ = ((m / 2 : ℕ) : ℝ) ^ 4 := by ring
      exact hle.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self m 2) 4)
    have hdom : Summable (fun m : ℕ =>
        (1 : ℝ) * r ^ m + 256 * ((ArithmeticFunction.sigma 3 (m / 2) : ℝ) * r ^ m) +
          16 * ((ArithmeticFunction.sigma 3 m : ℝ) * r ^ m)) :=
      (((summable_geometric_of_lt_one hr.1.le hr.2).mul_left 1).add (hsig2.mul_left 256)).add
        (hsig1.mul_left 16)
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (pow_nonneg hr.1.le m))
      (fun m => ?_) hdom
    by_cases hm0 : m = 0
    · subst hm0; simp [b]
    · rw [hb_formula m (Nat.pos_of_ne_zero hm0)]
      have hnb : ‖(if 2 ∣ m then (256 : ℂ) * (ArithmeticFunction.sigma 3 (m / 2) : ℂ) else 0) -
          (16 : ℂ) * (-1 : ℂ) ^ m * (ArithmeticFunction.sigma 3 m : ℂ)‖ ≤
          256 * (ArithmeticFunction.sigma 3 (m / 2) : ℝ) +
            16 * (ArithmeticFunction.sigma 3 m : ℝ) := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · split_ifs
          · rw [norm_mul, Complex.norm_natCast, Complex.norm_ofNat]
          · simp
        · rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one,
            Complex.norm_ofNat, Complex.norm_natCast]
      have h1 : ‖(if 2 ∣ m then (256 : ℂ) * (ArithmeticFunction.sigma 3 (m / 2) : ℂ) else 0) -
          (16 : ℂ) * (-1 : ℂ) ^ m * (ArithmeticFunction.sigma 3 m : ℂ)‖ * r ^ m ≤
          (256 * (ArithmeticFunction.sigma 3 (m / 2) : ℝ) +
            16 * (ArithmeticFunction.sigma 3 m : ℝ)) * r ^ m :=
        mul_le_mul_of_nonneg_right hnb (pow_nonneg hr.1.le m)
      have h2 : (0 : ℝ) ≤ 1 * r ^ m := mul_nonneg zero_le_one (pow_nonneg hr.1.le m)
      linarith
  have heq : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      (∑' m : ℕ, a m * (r : ℂ) ^ m) = ∑' m : ℕ, b m * (r : ℂ) ^ m := by
    intro r hr
    let t : ℝ := -Real.log r / Real.pi
    have ht : 0 < t := div_pos (neg_pos.mpr (Real.log_neg hr.1 hr.2)) Real.pi_pos
    have hexp : Real.exp (-Real.pi * t) = r := by
      dsimp only [t]
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      rw [show -Real.pi * (-Real.log r / Real.pi) = Real.log r by field_simp [hpi]]
      exact Real.exp_log hr.1
    let τ : UpperHalfPlane := ⟨Complex.I * (t : ℂ), by simp [ht]⟩
    have hid := theta3_pow_eight_eq τ
    -- Evaluate LHS = ∑' m, a m * r^m
    have hlhs : theta3 (τ : ℂ) ^ 8 = ∑' m : ℕ, a m * (r : ℂ) ^ m := by
      rw [theta3_pow_eq_tsum_repSquares 8 τ.im_pos]
      refine tsum_congr fun m => ?_
      congr 1
      have harg : (Real.pi : ℂ) * Complex.I * (m : ℂ) * (τ : ℂ) =
          (m : ℕ) * ((-Real.pi * t : ℝ) : ℂ) := by
        change (Real.pi : ℂ) * Complex.I * (m : ℂ) * (Complex.I * (t : ℂ)) = _
        push_cast
        linear_combination (Real.pi : ℂ) * (m : ℂ) * (t : ℂ) * Complex.I_mul_I
      rw [harg, Complex.exp_nat_mul, ← Complex.ofReal_exp, hexp]
    -- Evaluate E4 τ and E4 (addOneDivTwoUHP τ)
    have hE4_1 : E4 τ = 1 + 240 * ∑' m : ℕ+, (ArithmeticFunction.sigma 3 (m : ℕ) : ℂ) *
        ((r : ℂ) ^ 2) ^ (m : ℕ) := by
      unfold E4
      congr 2; refine tsum_congr fun m => ?_; congr 1
      have harg : 2 * (Real.pi : ℂ) * Complex.I * ((m : ℕ) : ℂ) * (τ : ℂ) =
          (m : ℕ) * (2 * ((-Real.pi * t : ℝ) : ℂ)) := by
        change 2 * (Real.pi : ℂ) * Complex.I * ((m : ℕ) : ℂ) * (Complex.I * (t : ℂ)) = _
        push_cast
        linear_combination 2 * (Real.pi : ℂ) * ((m : ℕ) : ℂ) * (t : ℂ) * Complex.I_mul_I
      rw [harg, Complex.exp_nat_mul, show 2 * ((-Real.pi * t : ℝ) : ℂ) =
        ((2 : ℕ) : ℂ) * ((-Real.pi * t : ℝ) : ℂ) by norm_num, Complex.exp_nat_mul,
        ← Complex.ofReal_exp, hexp]
    have hE4_2 : E4 (addOneDivTwoUHP τ) =
        1 + 240 * ∑' m : ℕ+, (ArithmeticFunction.sigma 3 (m : ℕ) : ℂ) *
          (-(r : ℂ)) ^ (m : ℕ) := by
      unfold E4
      congr 2; refine tsum_congr fun m => ?_; congr 1
      have harg : 2 * (Real.pi : ℂ) * Complex.I * ((m : ℕ) : ℂ) * ((addOneDivTwoUHP τ : ℂ)) =
          (m : ℕ) * ((Real.pi : ℂ) * Complex.I + ((-Real.pi * t : ℝ) : ℂ)) := by
        change 2 * (Real.pi : ℂ) * Complex.I * ((m : ℕ) : ℂ) *
          ((Complex.I * (t : ℂ) + 1) / 2) = _
        push_cast
        linear_combination (Real.pi : ℂ) * ((m : ℕ) : ℂ) * (t : ℂ) * Complex.I_mul_I
      rw [harg, Complex.exp_nat_mul, Complex.exp_add, Complex.exp_pi_mul_I,
        ← Complex.ofReal_exp, hexp, neg_one_mul]
    -- Evaluate RHS = ∑' m, b m * r^m
    have hb_sum : Summable (fun m : ℕ => b m * (r : ℂ) ^ m) :=
      Summable.of_norm ((hb r hr).congr fun m => by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.1.le])
    have hrhs : (16 / 15 : ℂ) * E4 τ - (1 / 15 : ℂ) * E4 (addOneDivTwoUHP τ) =
        ∑' m : ℕ, b m * (r : ℂ) ^ m := by
      rw [hb_sum.tsum_eq_zero_add]
      have hb0 : b 0 * (r : ℂ) ^ 0 = 1 := by simp [b]
      rw [hb0, hE4_1, hE4_2]
      -- Convert `∑' m : ℕ+, ...` to `∑' m : ℕ, ... (m + 1)`
      have hsum_s1 : Summable (fun m : ℕ =>
          (if 2 ∣ (m + 1) then (256 : ℂ) * (ArithmeticFunction.sigma 3 ((m + 1) / 2) : ℂ) else 0) *
            (r : ℂ) ^ (m + 1)) := by
        have hcomp : Summable (fun m : ℕ =>
            ‖(if 2 ∣ (m + 1) then (256 : ℂ) * (ArithmeticFunction.sigma 3 ((m + 1) / 2) : ℂ) else 0) *
              (r : ℂ) ^ (m + 1)‖) := by
          have hpoly : Summable (fun m : ℕ => 256 * ((m + 1 : ℕ) : ℝ) ^ 4 * r ^ (m + 1)) := by
            have hp0 := summable_pow_mul_geometric_of_norm_lt_one 4
              (by rw [Real.norm_of_nonneg hr.1.le]; exact hr.2)
            have hp := hp0.comp_injective Nat.succ_injective
            refine (hp.mul_left 256).congr fun m => ?_
            simp only [Function.comp_apply, Nat.succ_eq_add_one]
            ring
          refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hpoly
          split_ifs with hev
          · rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_natCast, norm_pow,
              Complex.norm_real, Real.norm_of_nonneg hr.1.le, mul_assoc]
            have hle : (ArithmeticFunction.sigma 3 ((m + 1) / 2) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 4 := by
              by_cases hm2 : (m + 1) / 2 = 0
              · rw [hm2]; simp; positivity
              · rw [ArithmeticFunction.sigma_apply]; push_cast
                have hle1 : (∑ d ∈ ((m + 1) / 2).divisors, (d : ℝ) ^ 3) ≤
                    (((m + 1) / 2 : ℕ) : ℝ) ^ 4 := by
                  calc (∑ d ∈ ((m + 1) / 2).divisors, (d : ℝ) ^ 3)
                      ≤ ∑ _d ∈ ((m + 1) / 2).divisors, (((m + 1) / 2 : ℕ) : ℝ) ^ 3 := by
                        refine Finset.sum_le_sum fun d hd => ?_
                        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm2) (Nat.dvd_of_mem_divisors hd)
                        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast this) 3
                    _ = (((m + 1) / 2).divisors.card : ℝ) * (((m + 1) / 2 : ℕ) : ℝ) ^ 3 := by simp
                    _ ≤ (((m + 1) / 2 : ℕ) : ℝ) * (((m + 1) / 2 : ℕ) : ℝ) ^ 3 := by
                        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                        have hsub : ((m + 1) / 2).divisors ⊆ Finset.Icc 1 ((m + 1) / 2) := fun d hd => by
                          rw [Finset.mem_Icc]
                          exact ⟨Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) (Nat.pos_of_ne_zero hm2),
                            Nat.le_of_dvd (Nat.pos_of_ne_zero hm2) (Nat.dvd_of_mem_divisors hd)⟩
                        exact_mod_cast (Finset.card_le_card hsub).trans (by simp)
                    _ = (((m + 1) / 2 : ℕ) : ℝ) ^ 4 := by ring
                exact hle1.trans (pow_le_pow_left₀ (Nat.cast_nonneg _)
                  (by exact_mod_cast Nat.div_le_self (m + 1) 2) 4)
            have hmul1 : (ArithmeticFunction.sigma 3 ((m + 1) / 2) : ℝ) * r ^ (m + 1) ≤
                ((m + 1 : ℕ) : ℝ) ^ 4 * r ^ (m + 1) :=
              mul_le_mul_of_nonneg_right hle (pow_nonneg hr.1.le _)
            linarith
          · simp only [zero_mul, norm_zero]
            exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) 4))
              (pow_nonneg hr.1.le _)
        exact hcomp.of_norm
      have hsum_s2 : Summable (fun m : ℕ =>
          (16 : ℂ) * (-1 : ℂ) ^ (m + 1) * (ArithmeticFunction.sigma 3 (m + 1) : ℂ) *
            (r : ℂ) ^ (m + 1)) := by
        have hs : Summable (fun m : ℕ =>
            (ArithmeticFunction.sigma 3 (m + 1) : ℝ) * r ^ (m + 1)) :=
          (summable_sigma_mul_pow 3 hr.1 hr.2).comp_injective Nat.succ_injective
        refine Summable.of_norm ((hs.mul_left 16).congr fun m => ?_)
        rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one,
          Complex.norm_ofNat, Complex.norm_natCast, norm_pow, Complex.norm_real,
          Real.norm_of_nonneg hr.1.le, mul_assoc]
      have hterm_b : (∑' m : ℕ, b (m + 1) * (r : ℂ) ^ (m + 1)) =
          (∑' m : ℕ, (if 2 ∣ (m + 1) then (256 : ℂ) * (ArithmeticFunction.sigma 3 ((m + 1) / 2) : ℂ) else 0) *
            (r : ℂ) ^ (m + 1)) -
          (∑' m : ℕ, (16 : ℂ) * (-1 : ℂ) ^ (m + 1) * (ArithmeticFunction.sigma 3 (m + 1) : ℂ) *
            (r : ℂ) ^ (m + 1)) := by
        rw [← hsum_s1.tsum_sub hsum_s2]
        refine tsum_congr fun m => ?_
        rw [hb_formula (m + 1) (Nat.succ_pos m)]
        ring
      rw [hterm_b]
      -- Identify the first sum with `256 * ∑' k : ℕ+, σ_3(k) * (r^2)^k`
      have hpart1 : (∑' m : ℕ,
          (if 2 ∣ (m + 1) then (256 : ℂ) * (ArithmeticFunction.sigma 3 ((m + 1) / 2) : ℂ) else 0) *
            (r : ℂ) ^ (m + 1)) =
          256 * ∑' k : ℕ+, (ArithmeticFunction.sigma 3 (k : ℕ) : ℂ) * ((r : ℂ) ^ 2) ^ (k : ℕ) := by
        -- Split `m : ℕ` into even `2j` (where `2 ∤ 2j+1`, term 0) and odd `2j+1` (where `(2j+2)/2 = j+1`)
        let ePar : ℕ ⊕ ℕ ≃ ℕ :=
          { toFun := fun x => match x with | Sum.inl j => 2 * j | Sum.inr j => 2 * j + 1
            invFun := fun m => if Even m then Sum.inl (m / 2) else Sum.inr (m / 2)
            left_inv := fun x => by
              rcases x with j | j
              · have hev : Even (2 * j) := ⟨j, by omega⟩
                simp [hev]
              · have hodd : ¬ Even (2 * j + 1) := by rintro ⟨k, hk⟩; omega
                simp [hodd]; omega
            right_inv := fun m => by
              dsimp only
              split_ifs with h
              · rcases h with ⟨k, rfl⟩; dsimp only; omega
              · rcases Nat.even_or_odd m with hm | ⟨k, rfl⟩
                · exact absurd hm h
                · dsimp only; omega }
        rw [← ePar.tsum_eq]
        have hs_par := ePar.summable_iff.mpr hsum_s1
        change (∑' x : ℕ ⊕ ℕ,
            ((fun m : ℕ =>
              (if 2 ∣ (m + 1) then (256 : ℂ) * (ArithmeticFunction.sigma 3 ((m + 1) / 2) : ℂ)
                else 0) * (r : ℂ) ^ (m + 1)) ∘ ePar) x) = _
        rw [(hs_par.comp_injective Sum.inl_injective).tsum_sum
          (hs_par.comp_injective Sum.inr_injective)]
        have hzero_l : (∑' j : ℕ,
            (if 2 ∣ (2 * j + 1) then (256 : ℂ) * (ArithmeticFunction.sigma 3 ((2 * j + 1) / 2) : ℂ)
              else 0) * (r : ℂ) ^ (2 * j + 1)) = 0 := by
          have hz : (fun j : ℕ =>
              (if 2 ∣ (2 * j + 1) then (256 : ℂ) * (ArithmeticFunction.sigma 3 ((2 * j + 1) / 2) : ℂ)
                else 0) * (r : ℂ) ^ (2 * j + 1)) = fun _ => (0 : ℂ) := by
            funext j
            have hnot : ¬ 2 ∣ (2 * j + 1) := by rintro ⟨k, hk⟩; omega
            simp [hnot]
          rw [hz, tsum_zero]
        change (∑' j : ℕ,
            (if 2 ∣ (2 * j + 1) then (256 : ℂ) * (ArithmeticFunction.sigma 3 ((2 * j + 1) / 2) : ℂ)
              else 0) * (r : ℂ) ^ (2 * j + 1)) +
          (∑' j : ℕ,
            (if 2 ∣ (2 * j + 1 + 1) then (256 : ℂ) * (ArithmeticFunction.sigma 3 ((2 * j + 1 + 1) / 2) : ℂ)
              else 0) * (r : ℂ) ^ (2 * j + 1 + 1)) = _
        rw [hzero_l, zero_add, ← tsum_mul_left]
        let eP : ℕ+ ≃ ℕ :=
          { toFun := fun k => (k : ℕ) - 1
            invFun := fun j => ⟨j + 1, Nat.succ_pos j⟩
            left_inv := fun k => Subtype.ext (Nat.sub_add_cancel k.pos)
            right_inv := fun j => Nat.add_sub_cancel j 1 }
        rw [← eP.tsum_eq]
        refine tsum_congr fun k => ?_
        have hk : 2 * eP k + 1 + 1 = 2 * (k : ℕ) := by
          change 2 * ((k : ℕ) - 1) + 1 + 1 = 2 * (k : ℕ)
          have := k.pos; omega
        rw [hk, if_pos ⟨(k : ℕ), rfl⟩, Nat.mul_div_cancel_left (k : ℕ) (by decide), pow_mul]
        ring
      -- Identify the second sum with `16 * ∑' k : ℕ+, σ_3(k) * (-r)^k`
      have hpart2 : (∑' m : ℕ,
          (16 : ℂ) * (-1 : ℂ) ^ (m + 1) * (ArithmeticFunction.sigma 3 (m + 1) : ℂ) *
            (r : ℂ) ^ (m + 1)) =
          16 * ∑' k : ℕ+, (ArithmeticFunction.sigma 3 (k : ℕ) : ℂ) * (-(r : ℂ)) ^ (k : ℕ) := by
        rw [← tsum_mul_left]
        let e : ℕ+ ≃ ℕ :=
          { toFun := fun k => (k : ℕ) - 1
            invFun := fun m => ⟨m + 1, Nat.succ_pos m⟩
            left_inv := fun k => Subtype.ext (Nat.sub_add_cancel k.pos)
            right_inv := fun m => Nat.add_sub_cancel m 1 }
        rw [← e.tsum_eq]
        refine tsum_congr fun k => ?_
        have hsucc : e k + 1 = (k : ℕ) := Nat.sub_add_cancel k.pos
        rw [hsucc, show (-(r : ℂ)) = (-1 : ℂ) * (r : ℂ) by ring, mul_pow]
        ring
      rw [hpart1, hpart2]
      ring
    rw [← hlhs, hid, hrhs]
  have hn_eq := eq_of_tsum_pow_eq ha hb heq n
  have hn0 : n ≠ 0 := by omega
  simp only [a, b, hn0, ↓reduceIte] at hn_eq
  exact_mod_cast hn_eq

/-- Odd `n` corollary of Jacobi's Eight-Square Theorem: `r₈(n) = 16 σ₃(n)`. -/
theorem jacobi_eight_squares_odd {n : ℕ} (hodd : Odd n) :
    repEightSquares n = 16 * ArithmeticFunction.sigma 3 n := by
  have hn1 : 1 ≤ n := by rcases hodd with ⟨k, rfl⟩; omega
  have h := jacobi_eight_squares_formula n hn1
  rw [jacobi_eight_divisor_identity n] at h
  have hnot2 : ¬ 2 ∣ n := by rcases hodd with ⟨k, rfl⟩; omega
  rw [if_neg hnot2, zero_sub] at h
  have hneg : (-1 : ℤ) ^ n = -1 := by
    rcases hodd with ⟨k, rfl⟩; rw [pow_succ, pow_mul]; norm_num
  rw [hneg] at h
  have hZ : (repEightSquares n : ℤ) = ((16 * ArithmeticFunction.sigma 3 n : ℕ) : ℤ) := by
    push_cast; linarith
  exact Int.ofNat.inj hZ

/-- Even `n` corollary of Jacobi's Eight-Square Theorem:
`r₈(2m) = 16 (σ₃^{even}(2m) - σ₃^{odd}(2m)) = 256 σ₃(m) - 16 σ₃(2m)` for every `m ≥ 1`. -/
theorem jacobi_eight_squares_even {m : ℕ} (hm : 1 ≤ m) :
    (repEightSquares (2 * m) : ℤ) =
      16 * ((∑ d ∈ (2 * m).divisors.filter Even, (d : ℤ) ^ 3) -
        ∑ d ∈ (2 * m).divisors.filter Odd, (d : ℤ) ^ 3) := by
  have h := jacobi_eight_squares_formula (2 * m) (by omega)
  rw [h]
  congr 1
  have hsplit := (Finset.sum_filter_add_sum_filter_not (2 * m).divisors Even
    (fun d => (-1 : ℤ) ^ (2 * m + d) * (d : ℤ) ^ 3)).symm
  rw [hsplit]
  have hev : (∑ d ∈ (2 * m).divisors.filter Even, (-1 : ℤ) ^ (2 * m + d) * (d : ℤ) ^ 3) =
      ∑ d ∈ (2 * m).divisors.filter Even, (d : ℤ) ^ 3 := by
    refine Finset.sum_congr rfl fun d hd => ?_
    rcases (Finset.mem_filter.mp hd).2 with ⟨k, rfl⟩
    have h1 : (-1 : ℤ) ^ (2 * m + (k + k)) = 1 := by
      rw [show 2 * m + (k + k) = 2 * (m + k) by omega, pow_mul]; norm_num
    rw [h1, one_mul]
  have hodd_filter : (2 * m).divisors.filter (fun d => ¬ Even d) = (2 * m).divisors.filter Odd := by
    ext d; simp [Nat.not_even_iff_odd]
  have hodd : (∑ d ∈ (2 * m).divisors.filter (fun d => ¬ Even d),
      (-1 : ℤ) ^ (2 * m + d) * (d : ℤ) ^ 3) =
      -(∑ d ∈ (2 * m).divisors.filter Odd, (d : ℤ) ^ 3) := by
    rw [hodd_filter, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    rcases (Finset.mem_filter.mp hd).2 with ⟨k, rfl⟩
    have h1 : (-1 : ℤ) ^ (2 * m + (2 * k + 1)) = -1 := by
      rw [show 2 * m + (2 * k + 1) = 2 * (m + k) + 1 by omega, pow_succ, pow_mul]; norm_num
    rw [h1, neg_one_mul]
  rw [hev, hodd]; ring

/-- Explicit verification: `r₈(1) = 16`. -/
theorem repEightSquares_one : repEightSquares 1 = 16 := by
  have h := jacobi_eight_squares_odd (by decide : Odd 1)
  simpa using h

/-- Explicit verification: `r₈(2) = 112`. -/
theorem repEightSquares_two : repEightSquares 2 = 112 := by
  have h := jacobi_eight_squares_formula 2 (by decide)
  have hdiv : (2 : ℕ).divisors = {1, 2} := by decide
  rw [hdiv] at h
  norm_num at h
  exact_mod_cast h

/-- Explicit verification: `r₈(3) = 448`. -/
theorem repEightSquares_three : repEightSquares 3 = 448 := by
  have h := jacobi_eight_squares_odd (by decide : Odd 3)
  have hsig : ArithmeticFunction.sigma 3 3 = 28 := by
    rw [ArithmeticFunction.sigma_apply]
    have hdiv : (3 : ℕ).divisors = {1, 3} := by decide
    rw [hdiv]; norm_num
  rw [hsig] at h; exact h

/-- Explicit verification: `r₈(4) = 1136`. -/
theorem repEightSquares_four : repEightSquares 4 = 1136 := by
  have h := jacobi_eight_squares_formula 4 (by decide)
  have hdiv : (4 : ℕ).divisors = {1, 2, 4} := by decide
  rw [hdiv] at h
  norm_num at h
  exact_mod_cast h

end JacobiEightSquares

/-! ## Section 5: Unconditional Jacobi's Four-Square Theorem, Lagrange Corollary & Dirichlet Series -/

section JacobiFourSquares

/-! ### Part 5A: Holomorphicity (`MDiff`) and `i∞`-Boundedness / Limits of `θ₃, θ₄, θ₂, E₂` -/

lemma differentiableOn_theta3 : DifferentiableOn ℂ theta3 {z : ℂ | 0 < z.im} := by
  intro z₀ hz₀
  have hδ : 0 < z₀.im / 2 := half_pos hz₀
  let U : Set ℂ := {z : ℂ | z₀.im / 2 < z.im}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hz₀U : z₀ ∈ U := by change z₀.im / 2 < z₀.im; linarith
  have hdiffU : DifferentiableOn ℂ theta3 U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun n : ℤ => ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 *
        (Complex.I * ((z₀.im / 2 : ℝ) : ℂ)))‖)
      (summable_norm_theta3 (by simp [hδ])) ?_ hU_open ?_
    · intro n
      refine (Differentiable.cexp ?_).differentiableOn
      fun_prop
    · intro n w hw
      have hw' : z₀.im / 2 < w.im := hw
      rw [Complex.norm_exp, Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im, sq]
      have hnn : 0 ≤ Real.pi * ((n : ℝ) * (n : ℝ)) := mul_nonneg Real.pi_pos.le (mul_self_nonneg _)
      nlinarith
  exact (hdiffU.differentiableAt (hU_open.mem_nhds hz₀U)).differentiableWithinAt

lemma differentiableOn_theta4 : DifferentiableOn ℂ theta4 {z : ℂ | 0 < z.im} := by
  intro z₀ hz₀
  have hδ : 0 < z₀.im / 2 := half_pos hz₀
  let U : Set ℂ := {z : ℂ | z₀.im / 2 < z.im}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hz₀U : z₀ ∈ U := by change z₀.im / 2 < z₀.im; linarith
  have hdiffU : DifferentiableOn ℂ theta4 U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun n : ℤ => ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 *
        (Complex.I * ((z₀.im / 2 : ℝ) : ℂ)))‖)
      (summable_norm_theta3 (by simp [hδ])) ?_ hU_open ?_
    · intro n
      refine (Differentiable.const_mul (Differentiable.cexp (by fun_prop)) _).differentiableOn
    · intro n w hw
      have hw' : z₀.im / 2 < w.im := hw
      rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
        Complex.norm_exp, Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im, sq]
      have hnn : 0 ≤ Real.pi * ((n : ℝ) * (n : ℝ)) := mul_nonneg Real.pi_pos.le (mul_self_nonneg _)
      nlinarith
  exact (hdiffU.differentiableAt (hU_open.mem_nhds hz₀U)).differentiableWithinAt

lemma differentiableOn_theta2 : DifferentiableOn ℂ theta2 {z : ℂ | 0 < z.im} := by
  intro z₀ hz₀
  have hδ : 0 < z₀.im / 2 := half_pos hz₀
  let U : Set ℂ := {z : ℂ | z₀.im / 2 < z.im}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hz₀U : z₀ ∈ U := by change z₀.im / 2 < z₀.im; linarith
  have hdiffU : DifferentiableOn ℂ theta2 U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun n : ℤ => ‖Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 *
        (Complex.I * ((z₀.im / 2 : ℝ) : ℂ)))‖)
      (summable_norm_theta2 (by simp [hδ])) ?_ hU_open ?_
    · intro n
      refine (Differentiable.cexp ?_).differentiableOn
      fun_prop
    · intro n w hw
      have hw' : z₀.im / 2 < w.im := hw
      rw [Complex.norm_exp, Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hsq : (((n : ℂ) + 1 / 2) ^ 2) = ((((n : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [hsq]
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      have hnn : 0 ≤ Real.pi * ((n : ℝ) + 1 / 2) ^ 2 := mul_nonneg Real.pi_pos.le (sq_nonneg _)
      nlinarith
  exact (hdiffU.differentiableAt (hU_open.mem_nhds hz₀U)).differentiableWithinAt

lemma mdifferentiable_theta3 : MDiff (fun τ : UpperHalfPlane => theta3 (τ : ℂ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine differentiableOn_theta3.congr fun z hz => ?_
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

lemma mdifferentiable_theta4 : MDiff (fun τ : UpperHalfPlane => theta4 (τ : ℂ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine differentiableOn_theta4.congr fun z hz => ?_
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

lemma mdifferentiable_theta2 : MDiff (fun τ : UpperHalfPlane => theta2 (τ : ℂ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine differentiableOn_theta2.congr fun z hz => ?_
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

lemma mdifferentiable_E2_mulTwo :
    MDiff (fun τ : UpperHalfPlane => EisensteinSeries.E2 (mulTwoUHP τ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hE2 := UpperHalfPlane.mdifferentiable_iff.mp E2_mdifferentiable
  have hcomp : DifferentiableOn ℂ ((EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) ∘
      (fun z : ℂ => 2 * z)) {z : ℂ | 0 < z.im} := by
    refine hE2.comp (Differentiable.differentiableOn (by fun_prop)) ?_
    intro z hz; change 0 < z.im at hz; change 0 < (2 * z).im; simp [hz]
  refine hcomp.congr fun z hz => ?_
  change 0 < z.im at hz
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have h2z : 0 < (2 * z).im := by simp [hz]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos h2z]
  rfl

lemma mdifferentiable_E2_divTwo :
    MDiff (fun τ : UpperHalfPlane => EisensteinSeries.E2 (divTwoUHP τ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hE2 := UpperHalfPlane.mdifferentiable_iff.mp E2_mdifferentiable
  have hcomp : DifferentiableOn ℂ ((EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) ∘
      (fun z : ℂ => z / 2)) {z : ℂ | 0 < z.im} := by
    refine hE2.comp (Differentiable.differentiableOn (by fun_prop)) ?_
    intro z hz; change 0 < z.im at hz; change 0 < (z / 2).im; simp [hz]
  refine hcomp.congr fun z hz => ?_
  change 0 < z.im at hz
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hz2 : 0 < (z / 2).im := by simp [hz]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz2]
  rfl

lemma mdifferentiable_E2_addOneDivTwo :
    MDiff (fun τ : UpperHalfPlane => EisensteinSeries.E2 (addOneDivTwoUHP τ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hE2 := UpperHalfPlane.mdifferentiable_iff.mp E2_mdifferentiable
  have hcomp : DifferentiableOn ℂ ((EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) ∘
      (fun z : ℂ => (z + 1) / 2)) {z : ℂ | 0 < z.im} := by
    refine hE2.comp (Differentiable.differentiableOn (by fun_prop)) ?_
    intro z hz; change 0 < z.im at hz; change 0 < ((z + 1) / 2).im; simp [hz]
  refine hcomp.congr fun z hz => ?_
  change 0 < z.im at hz
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hz2 : 0 < ((z + 1) / 2).im := by simp [hz]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz2]
  rfl

/-- Explicit norm decay of `E₂(τ) - 1` as `Im(τ) → ∞`. -/
lemma norm_E2_sub_one_le {τ : UpperHalfPlane} (hτ : 1 / 2 ≤ τ.im) :
    ‖EisensteinSeries.E2 τ - 1‖ ≤
      (24 * ∑' m : ℕ, (ArithmeticFunction.sigma 1 (m + 1) : ℝ) *
        Real.exp (-Real.pi) ^ m) * Real.exp (-2 * Real.pi * τ.im) := by
  rw [EisensteinSeries.E2_eq_tsum_cexp]
  have hdiff : (1 - 24 * ∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ (n : ℕ)) - 1 =
      -(24 * ∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ (n : ℕ)) := by ring
  rw [hdiff, norm_neg, norm_mul, Complex.norm_ofNat]
  have hnorm_q : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ))‖ =
      Real.exp (-2 * Real.pi * τ.im) := by
    rw [Complex.norm_exp]; congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, UpperHalfPlane.coe_im]
    ring
  have hq_pos : 0 < Real.exp (-2 * Real.pi * τ.im) := Real.exp_pos _
  have hq_le : Real.exp (-2 * Real.pi * τ.im) ≤ Real.exp (-Real.pi) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hpi_lt : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  have hsum_dom : Summable (fun m : ℕ =>
      (ArithmeticFunction.sigma 1 (m + 1) : ℝ) * Real.exp (-Real.pi) ^ m) := by
    have hs := (summable_sigma_mul_pow 1 (Real.exp_pos (-Real.pi)) hpi_lt).comp_injective
      Nat.succ_injective
    have hdiv := hs.mul_right (Real.exp (-Real.pi))⁻¹
    refine hdiv.congr fun m => ?_
    have hne : Real.exp (-Real.pi) ≠ 0 := (Real.exp_pos _).ne'
    change (ArithmeticFunction.sigma 1 (m + 1) : ℝ) * Real.exp (-Real.pi) ^ (m + 1) *
        (Real.exp (-Real.pi))⁻¹ = _
    rw [pow_succ]; field_simp [hne]
  let e : ℕ+ ≃ ℕ :=
    { toFun := fun n => (n : ℕ) - 1
      invFun := fun m => ⟨m + 1, Nat.succ_pos m⟩
      left_inv := fun n => Subtype.ext (Nat.sub_add_cancel n.pos)
      right_inv := fun m => Nat.add_sub_cancel m 1 }
  have htsum_eq : (∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ (n : ℕ)) =
      ∑' m : ℕ, (ArithmeticFunction.sigma 1 (m + 1) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ (m + 1) := by
    rw [← e.symm.tsum_eq]
    rfl
  rw [htsum_eq]
  have hsum_norm : Summable (fun m : ℕ =>
      ‖(ArithmeticFunction.sigma 1 (m + 1) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ (m + 1)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      (hsum_dom.mul_right (Real.exp (-2 * Real.pi * τ.im)))
    rw [norm_mul, Complex.norm_natCast, norm_pow, hnorm_q, pow_succ, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hq_pos.le
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq_pos.le hq_le m) (Nat.cast_nonneg _)
  have h1 : ‖∑' m : ℕ, (ArithmeticFunction.sigma 1 (m + 1) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ (m + 1)‖ ≤
      (∑' m : ℕ, (ArithmeticFunction.sigma 1 (m + 1) : ℝ) * Real.exp (-Real.pi) ^ m) *
        Real.exp (-2 * Real.pi * τ.im) := by
    refine (norm_tsum_le_tsum_norm hsum_norm).trans ?_
    rw [← tsum_mul_right]
    refine hsum_norm.tsum_le_tsum (fun m => ?_) (hsum_dom.mul_right _)
    rw [norm_mul, Complex.norm_natCast, norm_pow, hnorm_q, pow_succ, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hq_pos.le
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq_pos.le hq_le m) (Nat.cast_nonneg _)
  linarith

/-- Explicit norm decay of `θ₃(τ) - 1` for `1 ≤ Im(τ)`. -/
lemma norm_theta3_sub_one_le {τ : UpperHalfPlane} (hτ : 1 ≤ τ.im) :
    ‖theta3 (τ : ℂ) - 1‖ ≤
      (∑' n : ℤ, if n = 0 then (0 : ℝ) else
        Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))) * Real.exp (-Real.pi * τ.im) := by
  have hsum3 : Summable (fun n : ℤ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ))) :=
    (summable_norm_theta3 τ.im_pos).of_norm
  have hsub : theta3 (τ : ℂ) - 1 =
      ∑' n : ℤ, if n = 0 then (0 : ℂ) else
        Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ)) := by
    have hsplit := hsum3.tsum_eq_add_tsum_ite (0 : ℤ)
    simp only [Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, Complex.exp_zero] at hsplit
    unfold theta3
    rw [hsplit]
    ring
  rw [hsub]
  have hdom : Summable (fun n : ℤ =>
      (if n = 0 then (0 : ℝ) else Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))) *
        Real.exp (-Real.pi * τ.im)) := by
    have h1 := summable_norm_theta3 (τ := Complex.I) (by simp)
    refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_)
      (h1.mul_right (Real.exp Real.pi * Real.exp (-Real.pi * τ.im)))
    split_ifs with hn
    · simp; positivity
    · rw [Complex.norm_exp]
      have hre : ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * Complex.I).re =
          -Real.pi * (n : ℝ) ^ 2 := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im, sq]
        ring
      rw [hre, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
  have hterm_le : ∀ n : ℤ,
      ‖if n = 0 then (0 : ℂ) else
        Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ))‖ ≤
      (if n = 0 then (0 : ℝ) else Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))) *
        Real.exp (-Real.pi * τ.im) := by
    intro n
    split_ifs with hn
    · simp
    · rw [Complex.norm_exp, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hre : ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ)).re =
          -Real.pi * (n : ℝ) ^ 2 * τ.im := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
          UpperHalfPlane.coe_im, sq]
        ring
      rw [hre]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have h1 : (1 : ℤ) ≤ n ^ 2 := by rcases lt_or_gt_of_ne hn with hlt | hgt <;> nlinarith
        exact_mod_cast h1
      have hprod : 0 ≤ ((n : ℝ) ^ 2 - 1) * (τ.im - 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [Real.pi_pos]
  have hnorm_sum : Summable (fun n : ℤ =>
      ‖if n = 0 then (0 : ℂ) else
        Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le hdom
  refine (norm_tsum_le_tsum_norm hnorm_sum).trans ?_
  rw [← tsum_mul_right]
  exact hnorm_sum.tsum_le_tsum hterm_le hdom

/-- Explicit norm decay of `θ₄(τ) - 1` for `1 ≤ Im(τ)`. -/
lemma norm_theta4_sub_one_le {τ : UpperHalfPlane} (hτ : 1 ≤ τ.im) :
    ‖theta4 (τ : ℂ) - 1‖ ≤
      (∑' n : ℤ, if n = 0 then (0 : ℝ) else
        Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))) * Real.exp (-Real.pi * τ.im) := by
  have hsum4 : Summable (fun n : ℤ =>
      (-1 : ℂ) ^ n * Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ))) :=
    (summable_norm_theta4 τ.im_pos).of_norm
  have hsub : theta4 (τ : ℂ) - 1 =
      ∑' n : ℤ, if n = 0 then (0 : ℂ) else
        (-1 : ℂ) ^ n * Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ)) := by
    have hsplit := hsum4.tsum_eq_add_tsum_ite (0 : ℤ)
    simp only [zpow_zero, one_mul, Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      zero_mul, Complex.exp_zero] at hsplit
    unfold theta4
    rw [hsplit]
    ring
  rw [hsub]
  have hdom : Summable (fun n : ℤ =>
      (if n = 0 then (0 : ℝ) else Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))) *
        Real.exp (-Real.pi * τ.im)) := by
    have h1 := summable_norm_theta3 (τ := Complex.I) (by simp)
    refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_)
      (h1.mul_right (Real.exp Real.pi * Real.exp (-Real.pi * τ.im)))
    split_ifs with hn
    · simp; positivity
    · rw [Complex.norm_exp]
      have hre : ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * Complex.I).re =
          -Real.pi * (n : ℝ) ^ 2 := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im, sq]
        ring
      rw [hre, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
  have hterm_le : ∀ n : ℤ,
      ‖if n = 0 then (0 : ℂ) else
        (-1 : ℂ) ^ n * Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ))‖ ≤
      (if n = 0 then (0 : ℝ) else Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))) *
        Real.exp (-Real.pi * τ.im) := by
    intro n
    split_ifs with hn
    · simp
    · rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
        Complex.norm_exp, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hre : ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ)).re =
          -Real.pi * (n : ℝ) ^ 2 * τ.im := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
          UpperHalfPlane.coe_im, sq]
        ring
      rw [hre]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have h1 : (1 : ℤ) ≤ n ^ 2 := by rcases lt_or_gt_of_ne hn with hlt | hgt <;> nlinarith
        exact_mod_cast h1
      have hprod : 0 ≤ ((n : ℝ) ^ 2 - 1) * (τ.im - 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [Real.pi_pos]
  have hnorm_sum : Summable (fun n : ℤ =>
      ‖if n = 0 then (0 : ℂ) else
        (-1 : ℂ) ^ n * Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le hdom
  refine (norm_tsum_le_tsum_norm hnorm_sum).trans ?_
  rw [← tsum_mul_right]
  exact hnorm_sum.tsum_le_tsum hterm_le hdom

/-- Explicit norm decay of `θ₂(τ)` for `1 ≤ Im(τ)`. -/
lemma norm_theta2_le {τ : UpperHalfPlane} (hτ : 1 ≤ τ.im) :
    ‖theta2 (τ : ℂ)‖ ≤
      (∑' n : ℤ, Real.exp (-Real.pi * (((n : ℝ) + 1 / 2) ^ 2 - 1 / 4))) *
        Real.exp (-Real.pi / 4 * τ.im) := by
  have hdom : Summable (fun n : ℤ =>
      Real.exp (-Real.pi * (((n : ℝ) + 1 / 2) ^ 2 - 1 / 4)) * Real.exp (-Real.pi / 4 * τ.im)) := by
    have h1 := summable_norm_theta2 (τ := Complex.I) (by simp)
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
      (h1.mul_right (Real.exp (Real.pi / 4) * Real.exp (-Real.pi / 4 * τ.im)))
    rw [Complex.norm_exp]
    have hsq : (((n : ℂ) + 1 / 2) ^ 2) = ((((n : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hsq]
    have hre : ((Real.pi : ℂ) * Complex.I * ((((n : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ) * Complex.I).re =
        -Real.pi * ((n : ℝ) + 1 / 2) ^ 2 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    rw [hre, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hnorm_sum := summable_norm_theta2 τ.im_pos
  refine (norm_tsum_le_tsum_norm hnorm_sum).trans ?_
  rw [← tsum_mul_right]
  refine hnorm_sum.tsum_le_tsum (fun n => ?_) hdom
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq : (((n : ℂ) + 1 / 2) ^ 2) = ((((n : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hsq]
  have hre : ((Real.pi : ℂ) * Complex.I * ((((n : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ) * (τ : ℂ)).re =
      -Real.pi * ((n : ℝ) + 1 / 2) ^ 2 * τ.im := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, UpperHalfPlane.coe_im]
    ring
  rw [hre]
  have hn4 : (1 / 4 : ℝ) ≤ ((n : ℝ) + 1 / 2) ^ 2 := by
    have h1 : (1 : ℤ) ≤ (2 * n + 1) ^ 2 := by
      have hne : 2 * n + 1 ≠ 0 := by omega
      rcases lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith
    have h1R : (1 : ℝ) ≤ (2 * (n : ℝ) + 1) ^ 2 := by exact_mod_cast h1
    nlinarith
  have hprod : 0 ≤ (((n : ℝ) + 1 / 2) ^ 2 - 1 / 4) * (τ.im - 1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [Real.pi_pos]

/-! ### Part 5B: The Three `Γ₀(2)`-Conjugate Weight-2 Forms `(H₀, H₁, H₂)` and `(T₀, T₁, T₂)` -/

/-- Eisenstein `E₂` combinations `H₀, H₁, H₂` forming a weight-2 `SL₂(ℤ)` permutation triple. -/
def H0 (τ : UpperHalfPlane) : ℂ :=
  2 * EisensteinSeries.E2 (mulTwoUHP τ) - EisensteinSeries.E2 τ

def H1 (τ : UpperHalfPlane) : ℂ :=
  (1 / 2 : ℂ) * EisensteinSeries.E2 (divTwoUHP τ) - EisensteinSeries.E2 τ

def H2 (τ : UpperHalfPlane) : ℂ :=
  (1 / 2 : ℂ) * EisensteinSeries.E2 (addOneDivTwoUHP τ) - EisensteinSeries.E2 τ

/-- Theta fourth-power combinations `T₀, T₁, T₂` forming the matching weight-2 `SL₂(ℤ)` triple. -/
def T0 (τ : UpperHalfPlane) : ℂ :=
  (1 / 2 : ℂ) * (theta3 (τ : ℂ) ^ 4 + theta4 (τ : ℂ) ^ 4)

def T1 (τ : UpperHalfPlane) : ℂ :=
  -(1 / 2 : ℂ) * (theta3 (τ : ℂ) ^ 4 + theta2 (τ : ℂ) ^ 4)

def T2 (τ : UpperHalfPlane) : ℂ :=
  (1 / 2 : ℂ) * (theta2 (τ : ℂ) ^ 4 - theta4 (τ : ℂ) ^ 4)

/-- Weight-2 `T`-periodicity of `EisensteinSeries.E2`: `E₂(T • τ) = E₂(τ)`. -/
lemma E2_T_smul (τ : UpperHalfPlane) :
    EisensteinSeries.E2 (ModularGroup.T • τ) = EisensteinSeries.E2 τ := by
  have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.T) τ
  rw [EisensteinSeries.D2_T, smul_zero, sub_zero] at h
  have hT : SlashAction.map (2 : ℤ) ModularGroup.T EisensteinSeries.E2 τ =
      EisensteinSeries.E2 (ModularGroup.T • τ) := by
    rw [ModularForm.SL_slash]
    exact slash_T_apply 2 EisensteinSeries.E2 τ
  rwa [hT] at h

/-- Weight-2 `S`-quasimodular transformation of `EisensteinSeries.E2`. -/
lemma E2_S_smul (τ : UpperHalfPlane) :
    EisensteinSeries.E2 (ModularGroup.S • τ) =
      (τ : ℂ) ^ 2 * EisensteinSeries.E2 τ -
        (1 / (2 * riemannZeta 2)) * (2 * (Real.pi : ℂ) * Complex.I) * (τ : ℂ) := by
  have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.S) τ
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, EisensteinSeries.D2_S] at h
  have hS : SlashAction.map (2 : ℤ) ModularGroup.S EisensteinSeries.E2 τ =
      EisensteinSeries.E2 (ModularGroup.S • τ) * (τ : ℂ) ^ (-(2 : ℤ)) := by
    rw [ModularForm.SL_slash]
    exact slash_S_apply 2 EisensteinSeries.E2 τ
  rw [hS] at h
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hmul := congrArg (· * (τ : ℂ) ^ (2 : ℤ)) h
  rw [mul_assoc, ← zpow_add₀ hτ, neg_add_cancel, zpow_zero, mul_one] at hmul
  rw [hmul]
  have hpow2 : (τ : ℂ) ^ (2 : ℤ) = (τ : ℂ) ^ 2 := by norm_cast
  rw [hpow2]
  field_simp [hτ]

/-- Special matrix `γH = !![1, -1; 2, -1] ∈ SL₂(ℤ)` mapping `(τ + 1)/2 ↦ (-1/τ + 1)/2`. -/
def gammaH2 : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, -1; 2, -1], by decide⟩

lemma gammaH2_smul_addOneDivTwo (τ : UpperHalfPlane) :
    gammaH2 • (addOneDivTwoUHP τ) = addOneDivTwoUHP (ModularGroup.S • τ) := by
  apply UpperHalfPlane.ext
  have hnum_den : ((gammaH2 • addOneDivTwoUHP τ : UpperHalfPlane) : ℂ) =
      ((1 : ℂ) * ((addOneDivTwoUHP τ : ℂ)) + (-1 : ℂ)) /
        ((2 : ℂ) * ((addOneDivTwoUHP τ : ℂ)) + (-1 : ℂ)) := by
    rw [UpperHalfPlane.specialLinearGroup_apply]
    simp [gammaH2]
  rw [hnum_den]
  change (1 * (((τ : ℂ) + 1) / 2) + -1) / (2 * (((τ : ℂ) + 1) / 2) + -1) =
    (((ModularGroup.S • τ : UpperHalfPlane) : ℂ) + 1) / 2
  rw [UpperHalfPlane.modular_S_smul]
  change (1 * (((τ : ℂ) + 1) / 2) + -1) / (2 * (((τ : ℂ) + 1) / 2) + -1) =
    ((-(τ : ℂ))⁻¹ + 1) / 2
  field_simp [τ.ne_zero]
  ring

lemma E2_addOneDivTwo_S_smul (τ : UpperHalfPlane) :
    EisensteinSeries.E2 (addOneDivTwoUHP (ModularGroup.S • τ)) =
      (τ : ℂ) ^ 2 * EisensteinSeries.E2 (addOneDivTwoUHP τ) -
        (1 / (2 * riemannZeta 2)) * (4 * (Real.pi : ℂ) * Complex.I) * (τ : ℂ) := by
  have h := congrFun (EisensteinSeries.E2_slash_action gammaH2) (addOneDivTwoUHP τ)
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
  have hden : UpperHalfPlane.denom
      (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) gammaH2))
      (addOneDivTwoUHP τ) = (τ : ℂ) := by
    have h10 : ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) gammaH2 :
        Matrix (Fin 2) (Fin 2) ℝ) 1 0) = 2 := by
      change ((gammaH2 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) = 2
      have : (gammaH2 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 2 := rfl
      rw [this]; norm_num
    have h11 : ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) gammaH2 :
        Matrix (Fin 2) (Fin 2) ℝ) 1 1) = -1 := by
      change ((gammaH2 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) = -1
      have : (gammaH2 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -1 := rfl
      rw [this]; norm_num
    rw [UpperHalfPlane.denom]
    change (((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) gammaH2 :
        Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * (((τ : ℂ) + 1) / 2) +
      (((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) gammaH2 :
        Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ) : ℂ) = (τ : ℂ)
    rw [h10, h11]; push_cast; ring
  have hD2 : EisensteinSeries.D2 gammaH2 (addOneDivTwoUHP τ) =
      4 * (Real.pi : ℂ) * Complex.I / (τ : ℂ) := by
    unfold EisensteinSeries.D2
    rw [hden]
    have hc : (gammaH2 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 2 := rfl
    rw [hc]; push_cast; ring
  have hslash : SlashAction.map (2 : ℤ) gammaH2 EisensteinSeries.E2 (addOneDivTwoUHP τ) =
      EisensteinSeries.E2 (addOneDivTwoUHP (ModularGroup.S • τ)) * (τ : ℂ) ^ (-(2 : ℤ)) := by
    rw [ModularForm.SL_slash_apply, gammaH2_smul_addOneDivTwo τ]
    congr 2
  rw [hslash, hD2] at h
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hmul := congrArg (· * (τ : ℂ) ^ (2 : ℤ)) h
  rw [mul_assoc, ← zpow_add₀ hτ, neg_add_cancel, zpow_zero, mul_one] at hmul
  rw [hmul]
  have hpow2 : (τ : ℂ) ^ (2 : ℤ) = (τ : ℂ) ^ 2 := by norm_cast
  rw [hpow2]
  field_simp [hτ]

lemma H0_S_smul (τ : UpperHalfPlane) : H0 (ModularGroup.S • τ) = (τ : ℂ) ^ 2 * H1 τ := by
  unfold H0 H1
  have hmulS : mulTwoUHP (ModularGroup.S • τ) = ModularGroup.S • (divTwoUHP τ) := by
    apply UpperHalfPlane.ext
    change 2 * ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) =
      ((ModularGroup.S • divTwoUHP τ : UpperHalfPlane) : ℂ)
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_S_smul]
    change 2 * (-(τ : ℂ))⁻¹ = (-((τ : ℂ) / 2))⁻¹
    field_simp [τ.ne_zero]
  rw [hmulS, E2_S_smul (divTwoUHP τ), E2_S_smul τ]
  change 2 * (((τ : ℂ) / 2) ^ 2 * EisensteinSeries.E2 (divTwoUHP τ) -
      1 / (2 * riemannZeta 2) * (2 * (Real.pi : ℂ) * Complex.I) * ((τ : ℂ) / 2)) - _ = _
  ring

lemma H1_S_smul (τ : UpperHalfPlane) : H1 (ModularGroup.S • τ) = (τ : ℂ) ^ 2 * H0 τ := by
  have h := H0_S_smul (ModularGroup.S • τ)
  have hSS_mat : ModularGroup.S * ModularGroup.S = -1 := Subtype.ext ModularGroup.S_mul_S_eq
  have hSS : ModularGroup.S • (ModularGroup.S • τ) = τ := by
    rw [← mul_smul, hSS_mat, ModularGroup.SL_neg_smul, one_smul]
  rw [hSS] at h
  have hS_sq : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) ^ 2 = ((τ : ℂ) ^ 2)⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
    change (-(τ : ℂ))⁻¹ ^ 2 = ((τ : ℂ) ^ 2)⁻¹
    field_simp [τ.ne_zero]
  rw [hS_sq] at h
  have hτ2 : (τ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 τ.ne_zero
  calc H1 (ModularGroup.S • τ)
      = (τ : ℂ) ^ 2 * (((τ : ℂ) ^ 2)⁻¹ * H1 (ModularGroup.S • τ)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hτ2, one_mul]
    _ = (τ : ℂ) ^ 2 * H0 τ := by rw [← h]

lemma H2_S_smul (τ : UpperHalfPlane) : H2 (ModularGroup.S • τ) = (τ : ℂ) ^ 2 * H2 τ := by
  unfold H2
  rw [E2_addOneDivTwo_S_smul τ, E2_S_smul τ]
  ring

lemma H0_T_smul (τ : UpperHalfPlane) : H0 (ModularGroup.T • τ) = H0 τ := by
  unfold H0
  have hT_coe : ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.modular_T_smul]; simp [UpperHalfPlane.coe_vadd, add_comm]
  have hmulT : mulTwoUHP (ModularGroup.T • τ) =
      ModularGroup.T • (ModularGroup.T • mulTwoUHP τ) := by
    apply UpperHalfPlane.ext
    change 2 * ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) = _
    rw [hT_coe, UpperHalfPlane.modular_T_smul, UpperHalfPlane.modular_T_smul]
    simp [UpperHalfPlane.coe_vadd, mulTwoUHP]; ring
  rw [hmulT, E2_T_smul, E2_T_smul, E2_T_smul]

lemma H1_T_smul (τ : UpperHalfPlane) : H1 (ModularGroup.T • τ) = H2 τ := by
  unfold H1 H2
  have hT_coe : ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.modular_T_smul]; simp [UpperHalfPlane.coe_vadd, add_comm]
  have hdivT : divTwoUHP (ModularGroup.T • τ) = addOneDivTwoUHP τ := by
    apply UpperHalfPlane.ext
    change ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) / 2 = ((τ : ℂ) + 1) / 2
    rw [hT_coe]
  rw [hdivT, E2_T_smul]

lemma H2_T_smul (τ : UpperHalfPlane) : H2 (ModularGroup.T • τ) = H1 τ := by
  unfold H1 H2
  have hT_coe : ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.modular_T_smul]; simp [UpperHalfPlane.coe_vadd, add_comm]
  have haddT : addOneDivTwoUHP (ModularGroup.T • τ) = ModularGroup.T • (divTwoUHP τ) := by
    apply UpperHalfPlane.ext
    change (((ModularGroup.T • τ : UpperHalfPlane) : ℂ) + 1) / 2 = _
    rw [hT_coe, UpperHalfPlane.modular_T_smul]
    simp [UpperHalfPlane.coe_vadd, divTwoUHP]; ring
  rw [haddT, E2_T_smul, E2_T_smul]

private lemma neg_I_mul_cpow_half_pow_four (τ : UpperHalfPlane) :
    ((-Complex.I * (τ : ℂ)) ^ ((1 : ℂ) / 2)) ^ 4 = -((τ : ℂ) ^ 2) := by
  rw [← Complex.cpow_nat_mul]
  have h1 : (4 : ℕ) * ((1 : ℂ) / 2) = (2 : ℕ) := by push_cast; ring
  rw [h1, Complex.cpow_natCast, mul_pow]
  have hI2 : (-Complex.I) ^ 2 = -1 := by simp [Complex.I_sq]
  rw [hI2]; ring

lemma T0_S_smul (τ : UpperHalfPlane) : T0 (ModularGroup.S • τ) = (τ : ℂ) ^ 2 * T1 τ := by
  unfold T0 T1
  rw [theta3_S_smul, theta4_S_smul, mul_pow, mul_pow, neg_I_mul_cpow_half_pow_four]
  ring

lemma T1_S_smul (τ : UpperHalfPlane) : T1 (ModularGroup.S • τ) = (τ : ℂ) ^ 2 * T0 τ := by
  unfold T0 T1
  rw [theta3_S_smul, theta2_S_smul, mul_pow, mul_pow, neg_I_mul_cpow_half_pow_four]
  ring

lemma T2_S_smul (τ : UpperHalfPlane) : T2 (ModularGroup.S • τ) = (τ : ℂ) ^ 2 * T2 τ := by
  unfold T2
  rw [theta2_S_smul, theta4_S_smul, mul_pow, mul_pow, neg_I_mul_cpow_half_pow_four]
  ring

lemma T0_T_smul (τ : UpperHalfPlane) : T0 (ModularGroup.T • τ) = T0 τ := by
  unfold T0
  have hT_coe : ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.modular_T_smul]; simp [UpperHalfPlane.coe_vadd, add_comm]
  rw [hT_coe, theta3_add_one, theta4_add_one]; ring

lemma T1_T_smul (τ : UpperHalfPlane) : T1 (ModularGroup.T • τ) = T2 τ := by
  unfold T1 T2
  have hT_coe : ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.modular_T_smul]; simp [UpperHalfPlane.coe_vadd, add_comm]
  rw [hT_coe, theta3_add_one, theta2_add_one_pow_four]; ring

lemma T2_T_smul (τ : UpperHalfPlane) : T2 (ModularGroup.T • τ) = T1 τ := by
  unfold T1 T2
  have hT_coe : ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.modular_T_smul]; simp [UpperHalfPlane.coe_vadd, add_comm]
  rw [hT_coe, theta4_add_one, theta2_add_one_pow_four]; ring

/-! ### Part 5C: Level-1 Weight-4 Vanishing of `P = (H₀ - T₀)² + (H₁ - T₁)² + (H₂ - T₂)²` -/

/-- Level-1 weight-4 modular form measuring the squared defect between `(H₀, H₁, H₂)` and `(T₀, T₁, T₂)`. -/
def defectWeight4Fun (τ : UpperHalfPlane) : ℂ :=
  (H0 τ - T0 τ) ^ 2 + (H1 τ - T1 τ) ^ 2 + (H2 τ - T2 τ) ^ 2

lemma defectWeight4Fun_S_smul (τ : UpperHalfPlane) :
    defectWeight4Fun (ModularGroup.S • τ) = (τ : ℂ) ^ 4 * defectWeight4Fun τ := by
  unfold defectWeight4Fun
  rw [H0_S_smul, H1_S_smul, H2_S_smul, T0_S_smul, T1_S_smul, T2_S_smul]
  ring

lemma defectWeight4Fun_T_smul (τ : UpperHalfPlane) :
    defectWeight4Fun (ModularGroup.T • τ) = defectWeight4Fun τ := by
  unfold defectWeight4Fun
  rw [H0_T_smul, H1_T_smul, H2_T_smul, T0_T_smul, T1_T_smul, T2_T_smul]
  ring

lemma defectWeight4Fun_slash_SL2Z_invariant (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    SlashAction.map (4 : ℤ) (sl2ZToGL2R γ) defectWeight4Fun = defectWeight4Fun :=
  slash_SL2Z_invariant_of_S_T 4 defectWeight4Fun
    (fun τ => by simpa using defectWeight4Fun_S_smul τ)
    defectWeight4Fun_T_smul γ

lemma mdifferentiable_defectWeight4Fun : MDiff defectWeight4Fun := by
  have hE2 := E2_mdifferentiable
  have hE2_2 := mdifferentiable_E2_mulTwo
  have hE2_h := mdifferentiable_E2_divTwo
  have hE2_a := mdifferentiable_E2_addOneDivTwo
  have ht3 := mdifferentiable_theta3
  have ht4 := mdifferentiable_theta4
  have ht2 := mdifferentiable_theta2
  have hH0 : MDiff H0 := ((mdifferentiable_const.mul hE2_2).sub hE2)
  have hH1 : MDiff H1 := ((mdifferentiable_const.mul hE2_h).sub hE2)
  have hH2 : MDiff H2 := ((mdifferentiable_const.mul hE2_a).sub hE2)
  have hT0 : MDiff T0 := mdifferentiable_const.mul ((ht3.pow 4).add (ht4.pow 4))
  have hT1 : MDiff T1 := mdifferentiable_const.mul ((ht3.pow 4).add (ht2.pow 4))
  have hT2 : MDiff T2 := mdifferentiable_const.mul ((ht2.pow 4).sub (ht4.pow 4))
  exact (((hH0.sub hT0).pow 2).add ((hH1.sub hT1).pow 2)).add ((hH2.sub hT2).pow 2)

lemma isBoundedAtImInfty_defectWeight4Fun :
    UpperHalfPlane.IsBoundedAtImInfty defectWeight4Fun := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  set CE2 : ℝ := 24 * ∑' m : ℕ, (ArithmeticFunction.sigma 1 (m + 1) : ℝ) *
    Real.exp (-Real.pi) ^ m
  set C3 : ℝ := ∑' n : ℤ, if n = 0 then (0 : ℝ) else Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))
  set C2 : ℝ := ∑' n : ℤ, Real.exp (-Real.pi * (((n : ℝ) + 1 / 2) ^ 2 - 1 / 4))
  have hCE2_nn : 0 ≤ CE2 := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  have hC3_nn : 0 ≤ C3 := tsum_nonneg fun _ => by split_ifs <;> positivity
  have hC2_nn : 0 ≤ C2 := tsum_nonneg fun _ => (Real.exp_pos _).le
  set BE2 : ℝ := 1 + CE2
  set Bt3 : ℝ := 1 + C3
  set Bt2 : ℝ := C2
  set M : ℝ := 3 * ((3 * BE2 + (Bt3 ^ 4 + Bt3 ^ 4 + Bt2 ^ 4)) ^ 2)
  refine ⟨M, 1, fun τ hτ => ?_⟩
  have hE2_bd : ∀ z : UpperHalfPlane, 1 / 2 ≤ z.im → ‖EisensteinSeries.E2 z‖ ≤ BE2 := by
    intro z hz
    have h1 := norm_E2_sub_one_le hz
    have hexp1 : Real.exp (-2 * Real.pi * z.im) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    have h2 : ‖EisensteinSeries.E2 z - 1‖ ≤ CE2 :=
      h1.trans (mul_le_of_le_one_right hCE2_nn hexp1)
    have h3 : ‖EisensteinSeries.E2 z‖ ≤ ‖(1 : ℂ)‖ + ‖EisensteinSeries.E2 z - 1‖ := by
      simpa using norm_add_le (1 : ℂ) (EisensteinSeries.E2 z - 1)
    rw [norm_one] at h3
    linarith
  have ht3_bd : ‖theta3 (τ : ℂ)‖ ≤ Bt3 := by
    have h1 := norm_theta3_sub_one_le hτ
    have hexp1 : Real.exp (-Real.pi * τ.im) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    have h2 : ‖theta3 (τ : ℂ) - 1‖ ≤ C3 := h1.trans (mul_le_of_le_one_right hC3_nn hexp1)
    have h3 : ‖theta3 (τ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖theta3 (τ : ℂ) - 1‖ := by
      simpa using norm_add_le (1 : ℂ) (theta3 (τ : ℂ) - 1)
    rw [norm_one] at h3; linarith
  have ht4_bd : ‖theta4 (τ : ℂ)‖ ≤ Bt3 := by
    have h1 := norm_theta4_sub_one_le hτ
    have hexp1 : Real.exp (-Real.pi * τ.im) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    have h2 : ‖theta4 (τ : ℂ) - 1‖ ≤ C3 := h1.trans (mul_le_of_le_one_right hC3_nn hexp1)
    have h3 : ‖theta4 (τ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖theta4 (τ : ℂ) - 1‖ := by
      simpa using norm_add_le (1 : ℂ) (theta4 (τ : ℂ) - 1)
    rw [norm_one] at h3; linarith
  have ht2_bd : ‖theta2 (τ : ℂ)‖ ≤ Bt2 := by
    have h1 := norm_theta2_le hτ
    have hexp1 : Real.exp (-Real.pi / 4 * τ.im) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    exact h1.trans (mul_le_of_le_one_right hC2_nn hexp1)
  have hE0 := hE2_bd τ (by linarith)
  have hE2 := hE2_bd (mulTwoUHP τ) (by change 1 / 2 ≤ (2 * (τ : ℂ)).im; simp; linarith)
  have hEh := hE2_bd (divTwoUHP τ) (by change 1 / 2 ≤ ((τ : ℂ) / 2).im; simp; linarith)
  have hEa := hE2_bd (addOneDivTwoUHP τ) (by change 1 / 2 ≤ (((τ : ℂ) + 1) / 2).im; simp; linarith)
  have hBE2_nn : 0 ≤ BE2 := by linarith
  have hBt3_nn : 0 ≤ Bt3 := by linarith
  have hBt2_nn : 0 ≤ Bt2 := hC2_nn
  set B : ℝ := 3 * BE2 + (Bt3 ^ 4 + Bt3 ^ 4 + Bt2 ^ 4)
  have hB_nn : 0 ≤ B := by positivity
  have hD0 : ‖H0 τ - T0 τ‖ ≤ B := by
    have hH0 : ‖H0 τ‖ ≤ 3 * BE2 := by
      unfold H0
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_ofNat]; linarith
    have hT0 : ‖T0 τ‖ ≤ Bt3 ^ 4 + Bt3 ^ 4 + Bt2 ^ 4 := by
      unfold T0
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
      have hsum : ‖theta3 (τ : ℂ) ^ 4 + theta4 (τ : ℂ) ^ 4‖ ≤ Bt3 ^ 4 + Bt3 ^ 4 := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ht3_bd 4
        · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ht4_bd 4
      have hnn1 : 0 ≤ Bt3 ^ 4 := by positivity
      have hnn2 : 0 ≤ Bt2 ^ 4 := by positivity
      linarith
    exact (norm_sub_le _ _).trans (add_le_add hH0 hT0)
  have hD1 : ‖H1 τ - T1 τ‖ ≤ B := by
    have hH1 : ‖H1 τ‖ ≤ 3 * BE2 := by
      unfold H1
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]; linarith
    have hT1 : ‖T1 τ‖ ≤ Bt3 ^ 4 + Bt3 ^ 4 + Bt2 ^ 4 := by
      unfold T1
      rw [norm_mul, norm_neg, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
      have hsum : ‖theta3 (τ : ℂ) ^ 4 + theta2 (τ : ℂ) ^ 4‖ ≤ Bt3 ^ 4 + Bt2 ^ 4 := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ht3_bd 4
        · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ht2_bd 4
      have hnn1 : 0 ≤ Bt3 ^ 4 := by positivity
      have hnn2 : 0 ≤ Bt2 ^ 4 := by positivity
      linarith
    exact (norm_sub_le _ _).trans (add_le_add hH1 hT1)
  have hD2 : ‖H2 τ - T2 τ‖ ≤ B := by
    have hH2 : ‖H2 τ‖ ≤ 3 * BE2 := by
      unfold H2
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]; linarith
    have hT2 : ‖T2 τ‖ ≤ Bt3 ^ 4 + Bt3 ^ 4 + Bt2 ^ 4 := by
      unfold T2
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
      have hsum : ‖theta2 (τ : ℂ) ^ 4 - theta4 (τ : ℂ) ^ 4‖ ≤ Bt2 ^ 4 + Bt3 ^ 4 := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ht2_bd 4
        · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ht4_bd 4
      have hnn1 : 0 ≤ Bt3 ^ 4 := by positivity
      have hnn2 : 0 ≤ Bt2 ^ 4 := by positivity
      linarith
    exact (norm_sub_le _ _).trans (add_le_add hH2 hT2)
  have hsq0 : ‖(H0 τ - T0 τ) ^ 2‖ ≤ B ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hD0 2
  have hsq1 : ‖(H1 τ - T1 τ) ^ 2‖ ≤ B ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hD1 2
  have hsq2 : ‖(H2 τ - T2 τ) ^ 2‖ ≤ B ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hD2 2
  unfold defectWeight4Fun
  calc ‖(H0 τ - T0 τ) ^ 2 + (H1 τ - T1 τ) ^ 2 + (H2 τ - T2 τ) ^ 2‖
      ≤ ‖(H0 τ - T0 τ) ^ 2 + (H1 τ - T1 τ) ^ 2‖ + ‖(H2 τ - T2 τ) ^ 2‖ := norm_add_le _ _
    _ ≤ (‖(H0 τ - T0 τ) ^ 2‖ + ‖(H1 τ - T1 τ) ^ 2‖) + ‖(H2 τ - T2 τ) ^ 2‖ :=
        add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ (B ^ 2 + B ^ 2) + B ^ 2 := by linarith
    _ = M := by simp only [M, B]; ring

/-- The weight-4 level-1 modular form `PMod ∈ M₄(SL₂(ℤ))`. -/
def defectWeight4Form : ModularForm SL2ZRange 4 where
  toFun := defectWeight4Fun
  slash_action_eq' := by
    rintro _ ⟨γ, rfl⟩
    simpa [sl2ZToGL2R_eq_mapGL] using defectWeight4Fun_slash_SL2Z_invariant γ
  holo' := mdifferentiable_defectWeight4Fun
  bdd_at_cusps' := by
    intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    have hinv : SlashAction.map (4 : ℤ) γ defectWeight4Fun = defectWeight4Fun := by
      rw [ModularForm.SL_slash]
      exact defectWeight4Fun_slash_SL2Z_invariant γ
    rw [hinv]
    exact isBoundedAtImInfty_defectWeight4Fun

/-- **Identical Vanishing of the Level-1 Weight-4 Defect Form**:
`∀ τ : UpperHalfPlane, (H₀ τ - T₀ τ)² + (H₁ τ - T₁ τ)² + (H₂ τ - T₂ τ)² = 0`! -/
theorem defectWeight4Fun_eq_zero (τ : UpperHalfPlane) : defectWeight4Fun τ = 0 := by
  have hsmul := modularForm_SL2Z_weight_four_eq_smul_E4 defectWeight4Form
  set c : ℂ := PowerSeries.coeff 0
    (UpperHalfPlane.qExpansion 1 (defectWeight4Form : UpperHalfPlane → ℂ))
  have hval : ∀ z : UpperHalfPlane, defectWeight4Fun z = c * E4 z := by
    intro z
    have hz := congrArg (fun f : ModularForm SL2ZRange 4 => f z) hsmul
    rw [E4_eq_modularForm_E4 z]
    exact hz
  -- Show `c = 0` by taking `z = I * t` as `t → ∞`
  have hc0 : c = 0 := by
    let imgPt : ℝ → UpperHalfPlane := fun t =>
      ⟨Complex.I * ((max t 1 : ℝ) : ℂ), by simp [lt_of_lt_of_le zero_lt_one (le_max_right t 1)]⟩
    have hE2_lim : ∀ (f : UpperHalfPlane → UpperHalfPlane) (a : ℝ), 0 < a →
        (∀ t : ℝ, 1 ≤ t → a * t ≤ (f (imgPt t)).im) →
        Tendsto (fun t : ℝ => EisensteinSeries.E2 (f (imgPt t))) atTop (nhds 1) := by
      intro f a ha hfim
      rw [tendsto_iff_norm_sub_tendsto_zero]
      set CE2 : ℝ := 24 * ∑' m : ℕ, (ArithmeticFunction.sigma 1 (m + 1) : ℝ) *
        Real.exp (-Real.pi) ^ m
      have hzero : Tendsto (fun t : ℝ => CE2 * Real.exp (-2 * Real.pi * a * t)) atTop (nhds 0) := by
        have hlin : Tendsto (fun t : ℝ => -2 * Real.pi * a * t) atTop atBot := by
          have hneg : -2 * Real.pi * a < 0 := by nlinarith [Real.pi_pos]
          exact Filter.Tendsto.const_mul_atTop_of_neg hneg tendsto_id
        simpa using (Real.tendsto_exp_atBot.comp hlin).const_mul CE2
      refine squeeze_zero_norm' ?_ hzero
      filter_upwards [eventually_ge_atTop (max 1 (1 / (2 * a)))] with t ht
      have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
      have hta : 1 / (2 * a) ≤ t := (le_max_right _ _).trans ht
      have him_half : 1 / 2 ≤ (f (imgPt t)).im := by
        have h1 := hfim t ht1
        have h2 : 1 / 2 ≤ a * t := by
          have h2a : 0 < 2 * a := by positivity
          have hmul := (div_le_iff₀ h2a).mp hta
          linarith
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      refine (norm_E2_sub_one_le him_half).trans ?_
      have hCE2_nn : 0 ≤ CE2 := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCE2_nn
      have := hfim t ht1
      nlinarith [Real.pi_pos]
    have hE2_1 : Tendsto (fun t : ℝ => EisensteinSeries.E2 (imgPt t)) atTop (nhds 1) :=
      hE2_lim id 1 one_pos (fun t ht => by
        change 1 * t ≤ (Complex.I * ((max t 1 : ℝ) : ℂ)).im
        simp [max_eq_left ht])
    have hE2_2 : Tendsto (fun t : ℝ => EisensteinSeries.E2 (mulTwoUHP (imgPt t))) atTop (nhds 1) :=
      hE2_lim mulTwoUHP 2 (by norm_num) (fun t ht => by
        change 2 * t ≤ (2 * (Complex.I * ((max t 1 : ℝ) : ℂ))).im
        simp [max_eq_left ht])
    have hE2_h : Tendsto (fun t : ℝ => EisensteinSeries.E2 (divTwoUHP (imgPt t))) atTop (nhds 1) :=
      hE2_lim divTwoUHP (1 / 2) (by norm_num) (fun t ht => by
        change 1 / 2 * t ≤ (Complex.I * ((max t 1 : ℝ) : ℂ) / 2).im
        simp [max_eq_left ht]; linarith)
    have hE2_a : Tendsto (fun t : ℝ => EisensteinSeries.E2 (addOneDivTwoUHP (imgPt t))) atTop (nhds 1) :=
      hE2_lim addOneDivTwoUHP (1 / 2) (by norm_num) (fun t ht => by
        change 1 / 2 * t ≤ ((Complex.I * ((max t 1 : ℝ) : ℂ) + 1) / 2).im
        simp [max_eq_left ht]; linarith)
    have ht3_lim : Tendsto (fun t : ℝ => theta3 (imgPt t : ℂ)) atTop (nhds 1) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      set C3 : ℝ := ∑' n : ℤ, if n = 0 then (0 : ℝ) else Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))
      have hzero : Tendsto (fun t : ℝ => C3 * Real.exp (-Real.pi * t)) atTop (nhds 0) := by
        have hlin : Tendsto (fun t : ℝ => -Real.pi * t) atTop atBot :=
          Filter.Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos) tendsto_id
        simpa using (Real.tendsto_exp_atBot.comp hlin).const_mul C3
      refine squeeze_zero_norm' ?_ hzero
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      have him : (imgPt t).im = t := by
        change (Complex.I * ((max t 1 : ℝ) : ℂ)).im = t
        simp [max_eq_left ht]
      have h := norm_theta3_sub_one_le (τ := imgPt t) (by linarith)
      rw [him] at h
      exact h
    have ht4_lim : Tendsto (fun t : ℝ => theta4 (imgPt t : ℂ)) atTop (nhds 1) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      set C3 : ℝ := ∑' n : ℤ, if n = 0 then (0 : ℝ) else Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))
      have hzero : Tendsto (fun t : ℝ => C3 * Real.exp (-Real.pi * t)) atTop (nhds 0) := by
        have hlin : Tendsto (fun t : ℝ => -Real.pi * t) atTop atBot :=
          Filter.Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos) tendsto_id
        simpa using (Real.tendsto_exp_atBot.comp hlin).const_mul C3
      refine squeeze_zero_norm' ?_ hzero
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      have him : (imgPt t).im = t := by
        change (Complex.I * ((max t 1 : ℝ) : ℂ)).im = t
        simp [max_eq_left ht]
      have h := norm_theta4_sub_one_le (τ := imgPt t) (by linarith)
      rw [him] at h
      exact h
    have ht2_lim : Tendsto (fun t : ℝ => theta2 (imgPt t : ℂ)) atTop (nhds 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      set C2 : ℝ := ∑' n : ℤ, Real.exp (-Real.pi * (((n : ℝ) + 1 / 2) ^ 2 - 1 / 4))
      have hzero : Tendsto (fun t : ℝ => C2 * Real.exp (-Real.pi / 4 * t)) atTop (nhds 0) := by
        have hlin : Tendsto (fun t : ℝ => -Real.pi / 4 * t) atTop atBot :=
          Filter.Tendsto.const_mul_atTop_of_neg (by linarith [Real.pi_pos]) tendsto_id
        simpa using (Real.tendsto_exp_atBot.comp hlin).const_mul C2
      refine squeeze_zero_norm' ?_ hzero
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      have him : (imgPt t).im = t := by
        change (Complex.I * ((max t 1 : ℝ) : ℂ)).im = t
        simp [max_eq_left ht]
      have h := norm_theta2_le (τ := imgPt t) (by linarith)
      rw [him] at h
      exact h
    have hP_lim : Tendsto (fun t : ℝ => defectWeight4Fun (imgPt t)) atTop (nhds 0) := by
      have hH0_lim : Tendsto (fun t : ℝ => H0 (imgPt t)) atTop (nhds 1) := by
        have h := (hE2_2.const_mul (2 : ℂ)).sub hE2_1
        rwa [show (2 : ℂ) * 1 - 1 = 1 by ring] at h
      have hH1_lim : Tendsto (fun t : ℝ => H1 (imgPt t)) atTop (nhds (-1 / 2 : ℂ)) := by
        have h := (hE2_h.const_mul (1 / 2 : ℂ)).sub hE2_1
        rwa [show (1 / 2 : ℂ) * 1 - 1 = -1 / 2 by ring] at h
      have hH2_lim : Tendsto (fun t : ℝ => H2 (imgPt t)) atTop (nhds (-1 / 2 : ℂ)) := by
        have h := (hE2_a.const_mul (1 / 2 : ℂ)).sub hE2_1
        rwa [show (1 / 2 : ℂ) * 1 - 1 = -1 / 2 by ring] at h
      have hT0_lim : Tendsto (fun t : ℝ => T0 (imgPt t)) atTop (nhds 1) := by
        have h := ((ht3_lim.pow 4).add (ht4_lim.pow 4)).const_mul (1 / 2 : ℂ)
        rwa [show (1 / 2 : ℂ) * (1 ^ 4 + 1 ^ 4) = 1 by ring] at h
      have hT1_lim : Tendsto (fun t : ℝ => T1 (imgPt t)) atTop (nhds (-1 / 2 : ℂ)) := by
        have h := ((ht3_lim.pow 4).add (ht2_lim.pow 4)).const_mul (-(1 / 2 : ℂ))
        rwa [show -(1 / 2 : ℂ) * (1 ^ 4 + 0 ^ 4) = -1 / 2 by ring] at h
      have hT2_lim : Tendsto (fun t : ℝ => T2 (imgPt t)) atTop (nhds (-1 / 2 : ℂ)) := by
        have h := ((ht2_lim.pow 4).sub (ht4_lim.pow 4)).const_mul (1 / 2 : ℂ)
        rwa [show (1 / 2 : ℂ) * (0 ^ 4 - 1 ^ 4) = -1 / 2 by ring] at h
      have h := (((hH0_lim.sub hT0_lim).pow 2).add ((hH1_lim.sub hT1_lim).pow 2)).add
        ((hH2_lim.sub hT2_lim).pow 2)
      rwa [show ((1 : ℂ) - 1) ^ 2 + (-1 / 2 - -1 / 2) ^ 2 + (-1 / 2 - -1 / 2) ^ 2 = 0 by ring] at h
    have hE4_lim : Tendsto (fun t : ℝ => E4 (imgPt t)) atTop (nhds 1) := by
      have h := (((ht3_lim.pow 8).add (ht4_lim.pow 8)).add (ht2_lim.pow 8)).const_mul (1 / 2 : ℂ)
      have h1 : (1 / 2 : ℂ) * (1 ^ 8 + 1 ^ 8 + 0 ^ 8) = 1 := by ring
      rw [h1] at h
      exact h.congr fun t => E8_jacobiTheta_eq_E4 (imgPt t)
    have hP_lim2 : Tendsto (fun t : ℝ => defectWeight4Fun (imgPt t)) atTop (nhds c) := by
      simpa [hval] using hE4_lim.const_mul c
    exact tendsto_nhds_unique hP_lim2 hP_lim
  rw [hval τ, hc0, zero_mul]

/-! ### Part 5D: Reality on the Imaginary Axis & Exact `θ₃(i t)⁴` Identity -/

private lemma E2_imaginary_axis_im_eq_zero {s : ℝ} (hs : 0 < s) :
    (EisensteinSeries.E2 ⟨Complex.I * (s : ℂ), by simp [hs]⟩).im = 0 := by
  rw [EisensteinSeries.E2_eq_tsum_cexp]
  have hreal : (∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (Complex.I * (s : ℂ))) ^ (n : ℕ)) =
      ((∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) *
        Real.exp (-2 * Real.pi * s) ^ (n : ℕ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (Complex.I * (s : ℂ))) =
        ((Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1; push_cast
      linear_combination 2 * (Real.pi : ℂ) * (s : ℂ) * Complex.I_mul_I
    rw [hexp]; push_cast; rfl
  change (1 - 24 * ∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (Complex.I * (s : ℂ))) ^ (n : ℕ)).im = 0
  rw [hreal]
  simp

private lemma E2_addOneDivTwo_imaginary_axis_im_eq_zero {t : ℝ} (ht : 0 < t) :
    (EisensteinSeries.E2 (addOneDivTwoUHP ⟨Complex.I * (t : ℂ), by simp [ht]⟩)).im = 0 := by
  rw [EisensteinSeries.E2_eq_tsum_cexp]
  have hreal : (∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((Complex.I * (t : ℂ) + 1) / 2)) ^ (n : ℕ)) =
      ((∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) *
        (-Real.exp (-Real.pi * t)) ^ (n : ℕ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((Complex.I * (t : ℂ) + 1) / 2)) =
        ((-Real.exp (-Real.pi * t) : ℝ) : ℂ) := by
      have harg : 2 * (Real.pi : ℂ) * Complex.I * ((Complex.I * (t : ℂ) + 1) / 2) =
          (Real.pi : ℂ) * Complex.I + ((-Real.pi * t : ℝ) : ℂ) := by
        push_cast
        linear_combination (Real.pi : ℂ) * (t : ℂ) * Complex.I_mul_I
      rw [harg, Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp]
      push_cast; ring
    rw [hexp]; push_cast; rfl
  change (1 - 24 * ∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((Complex.I * (t : ℂ) + 1) / 2)) ^ (n : ℕ)).im = 0
  rw [hreal]; simp

private lemma theta3_imaginary_axis_im_eq_zero (t : ℝ) :
    (theta3 (Complex.I * (t : ℂ))).im = 0 := by
  have hreal : theta3 (Complex.I * (t : ℂ)) =
      ((∑' n : ℤ, Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) : ℝ) : ℂ) := by
    unfold theta3; rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [Complex.ofReal_exp]; congr 1; push_cast
    linear_combination (Real.pi : ℂ) * (n : ℂ) ^ 2 * (t : ℂ) * Complex.I_mul_I
  rw [hreal]; exact Complex.ofReal_im _

private lemma theta4_imaginary_axis_im_eq_zero (t : ℝ) :
    (theta4 (Complex.I * (t : ℂ))).im = 0 := by
  have hreal : theta4 (Complex.I * (t : ℂ)) =
      ((∑' n : ℤ, (-1 : ℝ) ^ n * Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) : ℝ) : ℂ) := by
    unfold theta4; rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_neg, Complex.ofReal_one,
      Complex.ofReal_exp]
    congr 2; push_cast
    linear_combination (Real.pi : ℂ) * (n : ℂ) ^ 2 * (t : ℂ) * Complex.I_mul_I
  rw [hreal]; exact Complex.ofReal_im _

private lemma theta2_imaginary_axis_im_eq_zero (t : ℝ) :
    (theta2 (Complex.I * (t : ℂ))).im = 0 := by
  have hreal : theta2 (Complex.I * (t : ℂ)) =
      ((∑' n : ℤ, Real.exp (-Real.pi * ((n : ℝ) + 1 / 2) ^ 2 * t) : ℝ) : ℂ) := by
    unfold theta2; rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [Complex.ofReal_exp]; congr 1; push_cast
    linear_combination (Real.pi : ℂ) * ((n : ℂ) + 1 / 2) ^ 2 * (t : ℂ) * Complex.I_mul_I
  rw [hreal]; exact Complex.ofReal_im _

private lemma eq_zero_of_im_zero_sum_three_sq {z₀ z₁ z₂ : ℂ}
    (h0 : z₀.im = 0) (h1 : z₁.im = 0) (h2 : z₂.im = 0)
    (hsum : z₀ ^ 2 + z₁ ^ 2 + z₂ ^ 2 = 0) :
    z₀ = 0 ∧ z₁ = 0 ∧ z₂ = 0 := by
  have hre : z₀.re ^ 2 + z₁.re ^ 2 + z₂.re ^ 2 = 0 := by
    have := congrArg Complex.re hsum
    simp only [Complex.add_re, Complex.zero_re, sq, Complex.mul_re, h0, h1, h2, mul_zero,
      sub_zero] at this
    linarith
  have hr0 : z₀.re = 0 := by nlinarith [sq_nonneg z₀.re, sq_nonneg z₁.re, sq_nonneg z₂.re]
  have hr1 : z₁.re = 0 := by nlinarith [sq_nonneg z₀.re, sq_nonneg z₁.re, sq_nonneg z₂.re]
  have hr2 : z₂.re = 0 := by nlinarith [sq_nonneg z₀.re, sq_nonneg z₁.re, sq_nonneg z₂.re]
  exact ⟨Complex.ext hr0 h0, Complex.ext hr1 h1, Complex.ext hr2 h2⟩

/-- **Exact Imaginary-Axis Identity for `θ₃(i t)⁴`**:
for every `t > 0` (`τ = i t`),
$$\theta_3(i t)^4 = \frac{4 E_2(2 i t) - E_2(i t / 2)}{3}.$$ -/
theorem theta3_pow_four_imaginary_axis {t : ℝ} (ht : 0 < t) :
    let τ : UpperHalfPlane := ⟨Complex.I * (t : ℂ), by simp [ht]⟩
    theta3 (τ : ℂ) ^ 4 =
      (4 * EisensteinSeries.E2 (mulTwoUHP τ) - EisensteinSeries.E2 (divTwoUHP τ)) / 3 := by
  intro τ
  have hdef := defectWeight4Fun_eq_zero τ
  have hE_im : (EisensteinSeries.E2 τ).im = 0 := E2_imaginary_axis_im_eq_zero ht
  have hE2_im : (EisensteinSeries.E2 (mulTwoUHP τ)).im = 0 := by
    have hEq : mulTwoUHP τ = ⟨Complex.I * ((2 * t : ℝ) : ℂ), by simp [ht]⟩ := by
      apply UpperHalfPlane.ext
      change 2 * (Complex.I * (t : ℂ)) = Complex.I * ((2 * t : ℝ) : ℂ)
      push_cast; ring
    rw [hEq]
    exact E2_imaginary_axis_im_eq_zero (by linarith)
  have hEh_im : (EisensteinSeries.E2 (divTwoUHP τ)).im = 0 := by
    have hEq : divTwoUHP τ = ⟨Complex.I * ((t / 2 : ℝ) : ℂ), by simp [ht]⟩ := by
      apply UpperHalfPlane.ext
      change (Complex.I * (t : ℂ)) / 2 = Complex.I * ((t / 2 : ℝ) : ℂ)
      push_cast; ring
    rw [hEq]
    exact E2_imaginary_axis_im_eq_zero (by linarith)
  have hEa_im : (EisensteinSeries.E2 (addOneDivTwoUHP τ)).im = 0 :=
    E2_addOneDivTwo_imaginary_axis_im_eq_zero ht
  have ht3_im : (theta3 (τ : ℂ)).im = 0 := theta3_imaginary_axis_im_eq_zero t
  have ht4_im : (theta4 (τ : ℂ)).im = 0 := theta4_imaginary_axis_im_eq_zero t
  have ht2_im : (theta2 (τ : ℂ)).im = 0 := theta2_imaginary_axis_im_eq_zero t
  have him_pow4 : ∀ z : ℂ, z.im = 0 → (z ^ 4).im = 0 := by
    intro z hz
    have : z = (z.re : ℂ) := Complex.ext rfl (by simp [hz])
    rw [this, ← Complex.ofReal_pow]; exact Complex.ofReal_im _
  have hD0_im : (H0 τ - T0 τ).im = 0 := by
    simp [H0, T0, hE2_im, hE_im, him_pow4 _ ht3_im, him_pow4 _ ht4_im]
  have hD1_im : (H1 τ - T1 τ).im = 0 := by
    simp [H1, T1, hEh_im, hE_im, him_pow4 _ ht3_im, him_pow4 _ ht2_im]
  have hD2_im : (H2 τ - T2 τ).im = 0 := by
    simp [H2, T2, hEa_im, hE_im, him_pow4 _ ht2_im, him_pow4 _ ht4_im]
  have ⟨h0, h1, _⟩ := eq_zero_of_im_zero_sum_three_sq hD0_im hD1_im hD2_im hdef
  have hH0 : H0 τ = T0 τ := sub_eq_zero.mp h0
  have hH1 : H1 τ = T1 τ := sub_eq_zero.mp h1
  have hab := jacobi_abstruse_identity τ.im_pos
  have hT_sub : T0 τ - T1 τ = (3 / 2 : ℂ) * theta3 (τ : ℂ) ^ 4 := by
    unfold T0 T1
    linear_combination (1 / 2 : ℂ) * hab.symm
  have hH_sub : H0 τ - H1 τ =
      2 * EisensteinSeries.E2 (mulTwoUHP τ) - (1 / 2 : ℂ) * EisensteinSeries.E2 (divTwoUHP τ) := by
    unfold H0 H1; ring
  have heq : (3 / 2 : ℂ) * theta3 (τ : ℂ) ^ 4 =
      2 * EisensteinSeries.E2 (mulTwoUHP τ) - (1 / 2 : ℂ) * EisensteinSeries.E2 (divTwoUHP τ) := by
    rw [← hT_sub, ← hH0, ← hH1, hH_sub]
  linear_combination (2 / 3 : ℂ) * heq

/-! ### Part 5E: Unconditional Jacobi's Four-Square Theorem, Lagrange Corollary & Dirichlet Series -/

/-- Elementary divisor identity for Jacobi's four-square arithmetic function:
for every `n : ℕ`,
$$\sum_{\substack{d \mid n \\ 4 \nmid d}} d = \sigma_1(n) - \mathbf{1}_{4 \mid n} \cdot 4 \sigma_1(n/4).$$ -/
lemma jacobi_four_divisor_identity (n : ℕ) :
    ((∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d : ℕ) : ℤ) =
      (ArithmeticFunction.sigma 1 n : ℤ) -
        (if 4 ∣ n then (4 : ℤ) * (ArithmeticFunction.sigma 1 (n / 4) : ℤ) else 0) := by
  by_cases hn0 : n = 0
  · subst hn0; simp
  · have hsplit := (Finset.sum_filter_add_sum_filter_not n.divisors (fun d => 4 ∣ d) (fun d => d)).symm
    have hsig : ArithmeticFunction.sigma 1 n = ∑ d ∈ n.divisors, d := by
      rw [ArithmeticFunction.sigma_apply]; simp
    by_cases h4 : 4 ∣ n
    · rcases h4 with ⟨m, rfl⟩
      rw [if_pos ⟨m, rfl⟩, Nat.mul_div_cancel_left m (by decide)]
      have hdiv4 : (∑ d ∈ (4 * m).divisors.filter (fun d => 4 ∣ d), d) =
          4 * ArithmeticFunction.sigma 1 m := by
        rw [ArithmeticFunction.sigma_apply]
        simp only [pow_one]
        rw [Finset.mul_sum]
        refine Finset.sum_nbij' (fun d => d / 4) (fun e => 4 * e) ?_ ?_ ?_ ?_ ?_
        · intro d hd
          rw [Finset.mem_filter, Nat.mem_divisors] at hd
          rcases hd.2 with ⟨e, rfl⟩
          rw [Nat.mul_div_cancel_left e (by decide)]
          exact Nat.mem_divisors.mpr
            ⟨(Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)).mp hd.1.1, right_ne_zero_of_mul hd.1.2⟩
        · intro e he
          rcases Nat.mem_divisors.mp he with ⟨he_dvd, hm0⟩
          rw [Finset.mem_filter, Nat.mem_divisors]
          exact ⟨⟨Nat.mul_dvd_mul_left 4 he_dvd, mul_ne_zero (by decide) hm0⟩, ⟨e, rfl⟩⟩
        · intro d hd
          rw [Finset.mem_filter] at hd; exact Nat.mul_div_cancel' hd.2
        · intro e _; exact Nat.mul_div_cancel_left e (by decide)
        · intro d hd
          rw [Finset.mem_filter] at hd; exact (Nat.mul_div_cancel' hd.2).symm
      have hnat : ArithmeticFunction.sigma 1 (4 * m) =
          4 * ArithmeticFunction.sigma 1 m +
            ∑ d ∈ (4 * m).divisors.filter (fun d => ¬ 4 ∣ d), d := by
        rw [hsig, hsplit, hdiv4]
      omega
    · rw [if_neg h4, sub_zero]
      have hempty : (n.divisors.filter (fun d => 4 ∣ d)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro d hd h4d
        exact h4 (dvd_trans h4d (Nat.dvd_of_mem_divisors hd))
      rw [hempty, Finset.sum_empty, zero_add] at hsplit
      rw [hsig, hsplit]

/-- **UNCONDITIONAL JACOBI'S FOUR-SQUARE THEOREM (ZERO ASSUMPTIONS!)**:
for EVERY natural number `n ≥ 1`,
$$r_4(n) = 8 \sum_{\substack{d \mid n \\ 4 \nmid d}} d.$$ -/
theorem jacobi_four_squares_formula (n : ℕ) (hn : 1 ≤ n) :
    repFourSquares n = 8 * ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d := by
  let a : ℕ → ℂ := fun m => (repFourSquares m : ℂ)
  let b : ℕ → ℂ := fun m =>
    if m = 0 then 1
    else (8 : ℂ) * ((∑ d ∈ m.divisors.filter (fun d => ¬ 4 ∣ d), d : ℕ) : ℂ)
  have ha : ∀ r ∈ Set.Ioo (0 : ℝ) 1, Summable (fun m : ℕ => ‖a m‖ * r ^ m) := fun r hr =>
    summable_repSquares_mul_pow 4 hr.1 hr.2
  have hb_formula : ∀ m : ℕ, 1 ≤ m →
      b m = (8 : ℂ) * (ArithmeticFunction.sigma 1 m : ℂ) -
        (if 4 ∣ m then (32 : ℂ) * (ArithmeticFunction.sigma 1 (m / 4) : ℂ) else 0) := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    simp only [b, hm0, ↓reduceIte]
    have h := congrArg (Int.cast (R := ℂ)) (jacobi_four_divisor_identity m)
    push_cast at h ⊢
    rw [h]
    split_ifs <;> ring
  have hb : ∀ r ∈ Set.Ioo (0 : ℝ) 1, Summable (fun m : ℕ => ‖b m‖ * r ^ m) := by
    intro r hr
    have hsig1 := summable_sigma_mul_pow 1 hr.1 hr.2
    have hdom : Summable (fun m : ℕ =>
        (1 : ℝ) * r ^ m + 8 * ((ArithmeticFunction.sigma 1 m : ℝ) * r ^ m)) :=
      ((summable_geometric_of_lt_one hr.1.le hr.2).mul_left 1).add (hsig1.mul_left 8)
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (pow_nonneg hr.1.le m))
      (fun m => ?_) hdom
    by_cases hm0 : m = 0
    · subst hm0; simp [b]
    · simp only [b, hm0, ↓reduceIte, norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
      have hle : (∑ d ∈ m.divisors.filter (fun d => ¬ 4 ∣ d), d) ≤ ArithmeticFunction.sigma 1 m := by
        rw [ArithmeticFunction.sigma_apply]
        simp only [pow_one]
        exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have hleR : ((∑ d ∈ m.divisors.filter (fun d => ¬ 4 ∣ d), d : ℕ) : ℝ) ≤
          (ArithmeticFunction.sigma 1 m : ℝ) := by exact_mod_cast hle
      have h1 : 8 * ((∑ d ∈ m.divisors.filter (fun d => ¬ 4 ∣ d), d : ℕ) : ℝ) * r ^ m ≤
          8 * (ArithmeticFunction.sigma 1 m : ℝ) * r ^ m := by
        nlinarith [pow_nonneg hr.1.le m]
      have h2 : (0 : ℝ) ≤ 1 * r ^ m := mul_nonneg zero_le_one (pow_nonneg hr.1.le m)
      linarith
  have heq : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      (∑' m : ℕ, a m * (r : ℂ) ^ m) = ∑' m : ℕ, b m * (r : ℂ) ^ m := by
    intro r hr
    let t : ℝ := -Real.log r / Real.pi
    have ht : 0 < t := div_pos (neg_pos.mpr (Real.log_neg hr.1 hr.2)) Real.pi_pos
    have hexp : Real.exp (-Real.pi * t) = r := by
      dsimp only [t]
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      rw [show -Real.pi * (-Real.log r / Real.pi) = Real.log r by field_simp [hpi]]
      exact Real.exp_log hr.1
    let τ : UpperHalfPlane := ⟨Complex.I * (t : ℂ), by simp [ht]⟩
    have hid := theta3_pow_four_imaginary_axis ht
    have hlhs : theta3 (τ : ℂ) ^ 4 = ∑' m : ℕ, a m * (r : ℂ) ^ m := by
      rw [theta3_pow_eq_tsum_repSquares 4 τ.im_pos]
      refine tsum_congr fun m => ?_
      congr 1
      have harg : (Real.pi : ℂ) * Complex.I * (m : ℂ) * (τ : ℂ) =
          (m : ℕ) * ((-Real.pi * t : ℝ) : ℂ) := by
        change (Real.pi : ℂ) * Complex.I * (m : ℂ) * (Complex.I * (t : ℂ)) = _
        push_cast
        linear_combination (Real.pi : ℂ) * (m : ℂ) * (t : ℂ) * Complex.I_mul_I
      rw [harg, Complex.exp_nat_mul, ← Complex.ofReal_exp, hexp]
    have hE2_h : EisensteinSeries.E2 (divTwoUHP τ) =
        1 - 24 * ∑' k : ℕ+, (ArithmeticFunction.sigma 1 (k : ℕ) : ℂ) * (r : ℂ) ^ (k : ℕ) := by
      rw [EisensteinSeries.E2_eq_tsum_cexp]
      congr 2; refine tsum_congr fun k => ?_; congr 2
      have harg : 2 * (Real.pi : ℂ) * Complex.I * ((divTwoUHP τ : ℂ)) =
          ((-Real.pi * t : ℝ) : ℂ) := by
        change 2 * (Real.pi : ℂ) * Complex.I * (Complex.I * (t : ℂ) / 2) = _
        push_cast
        linear_combination (Real.pi : ℂ) * (t : ℂ) * Complex.I_mul_I
      rw [harg, ← Complex.ofReal_exp, hexp]
    have hE2_2 : EisensteinSeries.E2 (mulTwoUHP τ) =
        1 - 24 * ∑' k : ℕ+, (ArithmeticFunction.sigma 1 (k : ℕ) : ℂ) *
          ((r : ℂ) ^ 4) ^ (k : ℕ) := by
      rw [EisensteinSeries.E2_eq_tsum_cexp]
      congr 2; refine tsum_congr fun k => ?_; congr 2
      have harg : 2 * (Real.pi : ℂ) * Complex.I * ((mulTwoUHP τ : ℂ)) =
          ((4 : ℕ) : ℂ) * ((-Real.pi * t : ℝ) : ℂ) := by
        change 2 * (Real.pi : ℂ) * Complex.I * (2 * (Complex.I * (t : ℂ))) = _
        push_cast
        linear_combination 4 * (Real.pi : ℂ) * (t : ℂ) * Complex.I_mul_I
      rw [harg, Complex.exp_nat_mul, ← Complex.ofReal_exp, hexp]
    have hb_sum : Summable (fun m : ℕ => b m * (r : ℂ) ^ m) :=
      Summable.of_norm ((hb r hr).congr fun m => by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.1.le])
    have hrhs : (4 * EisensteinSeries.E2 (mulTwoUHP τ) - EisensteinSeries.E2 (divTwoUHP τ)) / 3 =
        ∑' m : ℕ, b m * (r : ℂ) ^ m := by
      rw [hb_sum.tsum_eq_zero_add]
      have hb0 : b 0 * (r : ℂ) ^ 0 = 1 := by simp [b]
      rw [hb0, hE2_2, hE2_h]
      have hsum_s1 : Summable (fun m : ℕ =>
          (8 : ℂ) * (ArithmeticFunction.sigma 1 (m + 1) : ℂ) * (r : ℂ) ^ (m + 1)) := by
        have hs : Summable (fun m : ℕ =>
            (ArithmeticFunction.sigma 1 (m + 1) : ℝ) * r ^ (m + 1)) :=
          (summable_sigma_mul_pow 1 hr.1 hr.2).comp_injective Nat.succ_injective
        refine Summable.of_norm ((hs.mul_left 8).congr fun m => ?_)
        rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_natCast, norm_pow,
          Complex.norm_real, Real.norm_of_nonneg hr.1.le, mul_assoc]
      have hsum_s2 : Summable (fun m : ℕ =>
          (if 4 ∣ (m + 1) then (32 : ℂ) * (ArithmeticFunction.sigma 1 ((m + 1) / 4) : ℂ) else 0) *
            (r : ℂ) ^ (m + 1)) := by
        have hpoly : Summable (fun m : ℕ => 32 * ((m + 1 : ℕ) : ℝ) ^ 2 * r ^ (m + 1)) := by
          have hp0 := summable_pow_mul_geometric_of_norm_lt_one 2
            (by rw [Real.norm_of_nonneg hr.1.le]; exact hr.2)
          have hp := hp0.comp_injective Nat.succ_injective
          refine (hp.mul_left 32).congr fun m => ?_
          simp only [Function.comp_apply, Nat.succ_eq_add_one]
          ring
        refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hpoly)
        split_ifs with h4
        · rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_natCast, norm_pow,
            Complex.norm_real, Real.norm_of_nonneg hr.1.le, mul_assoc]
          have hle : (ArithmeticFunction.sigma 1 ((m + 1) / 4) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
            by_cases hm4 : (m + 1) / 4 = 0
            · rw [hm4]; simp; positivity
            · rw [ArithmeticFunction.sigma_apply]; simp only [pow_one]; push_cast
              have hle1 : (∑ d ∈ ((m + 1) / 4).divisors, (d : ℝ)) ≤
                  (((m + 1) / 4 : ℕ) : ℝ) ^ 2 := by
                calc (∑ d ∈ ((m + 1) / 4).divisors, (d : ℝ))
                    ≤ ∑ _d ∈ ((m + 1) / 4).divisors, (((m + 1) / 4 : ℕ) : ℝ) := by
                      refine Finset.sum_le_sum fun d hd => ?_
                      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hm4)
                        (Nat.dvd_of_mem_divisors hd)
                  _ = (((m + 1) / 4).divisors.card : ℝ) * (((m + 1) / 4 : ℕ) : ℝ) := by simp
                  _ ≤ (((m + 1) / 4 : ℕ) : ℝ) * (((m + 1) / 4 : ℕ) : ℝ) := by
                      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
                      have hsub : ((m + 1) / 4).divisors ⊆ Finset.Icc 1 ((m + 1) / 4) := fun d hd => by
                        rw [Finset.mem_Icc]
                        exact ⟨Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd)
                          (Nat.pos_of_ne_zero hm4),
                          Nat.le_of_dvd (Nat.pos_of_ne_zero hm4) (Nat.dvd_of_mem_divisors hd)⟩
                      exact_mod_cast (Finset.card_le_card hsub).trans (by simp)
                  _ = (((m + 1) / 4 : ℕ) : ℝ) ^ 2 := by ring
              exact hle1.trans (pow_le_pow_left₀ (Nat.cast_nonneg _)
                (by exact_mod_cast Nat.div_le_self (m + 1) 4) 2)
          have hmul1 : (ArithmeticFunction.sigma 1 ((m + 1) / 4) : ℝ) * r ^ (m + 1) ≤
              ((m + 1 : ℕ) : ℝ) ^ 2 * r ^ (m + 1) :=
            mul_le_mul_of_nonneg_right hle (pow_nonneg hr.1.le _)
          linarith
        · simp only [zero_mul, norm_zero]
          exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) 2))
            (pow_nonneg hr.1.le _)
      have hterm_b : (∑' m : ℕ, b (m + 1) * (r : ℂ) ^ (m + 1)) =
          (∑' m : ℕ, (8 : ℂ) * (ArithmeticFunction.sigma 1 (m + 1) : ℂ) * (r : ℂ) ^ (m + 1)) -
          (∑' m : ℕ, (if 4 ∣ (m + 1) then (32 : ℂ) * (ArithmeticFunction.sigma 1 ((m + 1) / 4) : ℂ) else 0) *
            (r : ℂ) ^ (m + 1)) := by
        rw [← hsum_s1.tsum_sub hsum_s2]
        refine tsum_congr fun m => ?_
        rw [hb_formula (m + 1) (Nat.succ_pos m)]; ring
      rw [hterm_b]
      have hpart1 : (∑' m : ℕ, (8 : ℂ) * (ArithmeticFunction.sigma 1 (m + 1) : ℂ) * (r : ℂ) ^ (m + 1)) =
          8 * ∑' k : ℕ+, (ArithmeticFunction.sigma 1 (k : ℕ) : ℂ) * (r : ℂ) ^ (k : ℕ) := by
        rw [← tsum_mul_left]
        let e : ℕ+ ≃ ℕ :=
          { toFun := fun k => (k : ℕ) - 1
            invFun := fun m => ⟨m + 1, Nat.succ_pos m⟩
            left_inv := fun k => Subtype.ext (Nat.sub_add_cancel k.pos)
            right_inv := fun m => Nat.add_sub_cancel m 1 }
        rw [← e.tsum_eq]
        refine tsum_congr fun k => ?_
        have hsucc : e k + 1 = (k : ℕ) := Nat.sub_add_cancel k.pos
        rw [hsucc]; ring
      have hpart2 : (∑' m : ℕ,
          (if 4 ∣ (m + 1) then (32 : ℂ) * (ArithmeticFunction.sigma 1 ((m + 1) / 4) : ℂ) else 0) *
            (r : ℂ) ^ (m + 1)) =
          32 * ∑' k : ℕ+, (ArithmeticFunction.sigma 1 (k : ℕ) : ℂ) * ((r : ℂ) ^ 4) ^ (k : ℕ) := by
        let eMod4 : Fin 4 × ℕ ≃ ℕ :=
          { toFun := fun p => 4 * p.2 + (p.1 : ℕ)
            invFun := fun m => (⟨m % 4, Nat.mod_lt m (by decide)⟩, m / 4)
            left_inv := fun p => by
              ext
              · dsimp; have hp := p.1.2; omega
              · dsimp; have hp := p.1.2; omega
            right_inv := fun m => by dsimp; omega }
        rw [← eMod4.tsum_eq]
        have hs_mod4 := eMod4.summable_iff.mpr hsum_s2
        change (∑' p : Fin 4 × ℕ,
            ((fun m : ℕ =>
              (if 4 ∣ (m + 1) then (32 : ℂ) * (ArithmeticFunction.sigma 1 ((m + 1) / 4) : ℂ)
                else 0) * (r : ℂ) ^ (m + 1)) ∘ eMod4) p) = _
        rw [hs_mod4.tsum_prod']
        · have hfin_sum : ∀ i : Fin 4, i ≠ ⟨3, by decide⟩ →
              (∑' j : ℕ, (if 4 ∣ (4 * j + (i : ℕ) + 1) then
                (32 : ℂ) * (ArithmeticFunction.sigma 1 ((4 * j + (i : ℕ) + 1) / 4) : ℂ) else 0) *
                (r : ℂ) ^ (4 * j + (i : ℕ) + 1)) = 0 := by
            intro i hi
            have hz : (fun j : ℕ => (if 4 ∣ (4 * j + (i : ℕ) + 1) then
                (32 : ℂ) * (ArithmeticFunction.sigma 1 ((4 * j + (i : ℕ) + 1) / 4) : ℂ) else 0) *
                (r : ℂ) ^ (4 * j + (i : ℕ) + 1)) = fun _ => (0 : ℂ) := by
              funext j
              have hi4 := i.2
              have hi3 : (i : ℕ) ≠ 3 := fun h => hi (Fin.ext h)
              have hnot4 : ¬ 4 ∣ (4 * j + (i : ℕ) + 1) := by omega
              simp [hnot4]
            rw [hz, tsum_zero]
          rw [tsum_fintype, Finset.sum_eq_single (⟨3, by decide⟩ : Fin 4)
            (fun i _ hi => by simpa [Function.comp_apply, eMod4] using hfin_sum i hi)
            (fun h => absurd (Finset.mem_univ _) h)]
          rw [← tsum_mul_left]
          let eP : ℕ+ ≃ ℕ :=
            { toFun := fun k => (k : ℕ) - 1
              invFun := fun j => ⟨j + 1, Nat.succ_pos j⟩
              left_inv := fun k => Subtype.ext (Nat.sub_add_cancel k.pos)
              right_inv := fun j => Nat.add_sub_cancel j 1 }
          rw [← eP.tsum_eq]
          refine tsum_congr fun k => ?_
          have hk : 4 * eP k + 3 + 1 = 4 * (k : ℕ) := by
            change 4 * ((k : ℕ) - 1) + 3 + 1 = 4 * (k : ℕ)
            have := k.pos; omega
          change (if 4 ∣ (4 * eP k + 3 + 1) then
              (32 : ℂ) * (ArithmeticFunction.sigma 1 ((4 * eP k + 3 + 1) / 4) : ℂ) else 0) *
            (r : ℂ) ^ (4 * eP k + 3 + 1) = _
          rw [hk, if_pos ⟨(k : ℕ), rfl⟩, Nat.mul_div_cancel_left (k : ℕ) (by decide), pow_mul]
          ring
        · intro i
          exact hs_mod4.comp_injective (fun _ _ h => (Prod.mk.inj h).2)
      rw [hpart1, hpart2]; ring
    rw [← hlhs, hid, hrhs]
  have hn_eq := eq_of_tsum_pow_eq ha hb heq n
  have hn0 : n ≠ 0 := by omega
  simp only [a, b, hn0, ↓reduceIte] at hn_eq
  exact_mod_cast hn_eq

/-- Every positive integer has at least `8` representations as a sum of four squares: `r₄(n) ≥ 8`. -/
theorem repFourSquares_ge_eight (n : ℕ) (hn : 1 ≤ n) : 8 ≤ repFourSquares n := by
  rw [jacobi_four_squares_formula n hn]
  have h1_mem : 1 ∈ n.divisors.filter (fun d => ¬ 4 ∣ d) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd n, by omega⟩, by decide⟩
  have hsum_ge : 1 ≤ ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d :=
    Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) h1_mem
  omega

/-- **Lagrange's Four-Square Theorem** as a 2-line corollary of Jacobi's Four-Square Formula (`r₄(n) ≥ 8 > 0`)! -/
theorem lagrange_four_squares_of_jacobi (n : ℕ) :
    ∃ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = (n : ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, 0, 0, by norm_num⟩
  · have hpos : 0 < repFourSquares n := by have := repFourSquares_ge_eight n hn; omega
    obtain ⟨⟨v, hv⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨v 0, v 1, v 2, v 3, by simpa [Fin.sum_univ_four] using hv⟩

/-- **Exact `LSeries` Identity for `r₄(n)`** on `Re(s) > 2`:
$$L(r_4, s) = 8 \left(1 - 4^{1 - s}\right) \zeta(s) \, \zeta(s - 1).$$ -/
theorem LSeries_repFourSquares_eq {s : ℂ} (hs : 2 < s.re) :
    LSeries (fun n : ℕ => (repFourSquares n : ℂ)) s =
      8 * (1 - (4 : ℂ) ^ (1 - s)) * riemannZeta s * riemannZeta (s - 1) := by
  have hs_sig : ((1 : ℕ) : ℝ) + 1 < s.re := by norm_num; linarith
  have hsum_sig : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.sigma 1 n : ℂ)) s := by
    have hs1 : 1 < s.re := by linarith
    have hs1' : 1 < (s - (1 : ℂ)).re := by simp; linarith
    have hsum1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs1
    have hsum_id : LSeriesSummable (fun n : ℕ => (n : ℂ) ^ 1) s := by
      refine (LSeriesSummable_one_iff.mpr hs1').congr fun n => ?_
      by_cases hn : n = 0
      · simp [LSeries.term, hn]
      · simp only [LSeries.term, hn, ↓reduceIte, Pi.one_apply, pow_one]
        have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        rw [Complex.cpow_sub _ _ hnC, Complex.cpow_one, div_div_eq_mul_div, one_mul]
    have hconv : LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => (n : ℂ) ^ 1) =
        fun n : ℕ => (ArithmeticFunction.sigma 1 n : ℂ) := by
      funext n
      rw [LSeries.convolution_def, ArithmeticFunction.sigma_apply]
      dsimp only
      have hsum_anti :
          (∑ p ∈ n.divisorsAntidiagonal, (1 : ℕ → ℂ) p.1 * (p.2 : ℂ) ^ 1) =
          ∑ d ∈ n.divisors, (d : ℂ) ^ 1 := by
        refine Finset.sum_nbij' (fun p => p.2) (fun d => (n / d, d)) ?_ ?_ ?_ ?_ ?_
        · intro p hp; exact Nat.snd_mem_divisors_of_mem_antidiagonal hp
        · intro d hd
          exact Nat.mem_divisorsAntidiagonal.mpr
            ⟨Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd), (Nat.mem_divisors.mp hd).2⟩
        · intro p hp
          rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, hn0⟩
          have hp2_pos : 0 < p.2 := Nat.pos_of_ne_zero (fun h0 => hn0 (by simp [← hpmul, h0]))
          ext
          · exact (Nat.eq_div_of_mul_eq_left hp2_pos.ne' hpmul).symm
          · rfl
        · intro _ _; rfl
        · intro p _; simp
      rw [hsum_anti]; push_cast; rfl
    rw [← hconv]; exact hsum1.convolution hsum_id
  have hsum_sig4 : Summable (fun n : ℕ =>
      if n = 0 then (0 : ℂ) else
        (if 4 ∣ n then (32 : ℂ) * (ArithmeticFunction.sigma 1 (n / 4) : ℂ) else 0) / (n : ℂ) ^ s) := by
    let eMod4 : Fin 4 × ℕ ≃ ℕ :=
      { toFun := fun p => 4 * p.2 + (p.1 : ℕ)
        invFun := fun m => (⟨m % 4, Nat.mod_lt m (by decide)⟩, m / 4)
        left_inv := fun p => by ext <;> (dsimp; have := p.1.2; omega)
        right_inv := fun m => by dsimp; omega }
    rw [← eMod4.summable_iff]
    refine (summable_prod_of_nonneg (f := fun p : Fin 4 × ℕ =>
        ‖if 4 * p.2 + (p.1 : ℕ) = 0 then (0 : ℂ) else
          (if 4 ∣ (4 * p.2 + (p.1 : ℕ)) then
            (32 : ℂ) * (ArithmeticFunction.sigma 1 ((4 * p.2 + (p.1 : ℕ)) / 4) : ℂ) else 0) /
          ((4 * p.2 + (p.1 : ℕ) : ℕ) : ℂ) ^ s‖) (fun _ => norm_nonneg _)).mpr ?_ |>.of_norm
    refine ⟨fun i => ?_, ?_⟩
    · by_cases hi : (i : ℕ) = 0
      · have hs' : Summable (fun m : ℕ =>
            ‖(32 : ℂ) * (4 : ℂ) ^ (-s) * LSeries.term (fun k => (ArithmeticFunction.sigma 1 k : ℂ)) s m‖) :=
          (hsum_sig.mul_left ((32 : ℂ) * (4 : ℂ) ^ (-s))).norm
        refine hs'.congr fun m => ?_
        rw [hi, add_zero]
        by_cases hm : m = 0
        · simp [hm, LSeries.term]
        · have h4m : 4 * m ≠ 0 := mul_ne_zero (by decide) hm
          simp only [h4m, ↓reduceIte, LSeries.term, hm]
          rw [if_pos ⟨m, rfl⟩, Nat.mul_div_cancel_left m (by decide)]
          have hcpow : ((4 * m : ℕ) : ℂ) ^ s = (4 : ℂ) ^ s * (m : ℂ) ^ s := by
            have h4mC : ((4 * m : ℕ) : ℂ) = ((4 : ℝ) : ℂ) * ((m : ℝ) : ℂ) := by push_cast; rfl
            rw [h4mC, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
            norm_cast
          rw [hcpow, Complex.cpow_neg]
          congr 1; ring
      · have hz : (fun y : ℕ =>
            ‖if 4 * (i, y).2 + ((i, y).1 : ℕ) = 0 then (0 : ℂ) else
              (if 4 ∣ (4 * (i, y).2 + ((i, y).1 : ℕ)) then
                (32 : ℂ) * (ArithmeticFunction.sigma 1 ((4 * (i, y).2 + ((i, y).1 : ℕ)) / 4) : ℂ) else 0) /
              ((4 * (i, y).2 + ((i, y).1 : ℕ) : ℕ) : ℂ) ^ s‖) = fun _ => (0 : ℝ) := by
          funext m
          have hnot4 : ¬ 4 ∣ (4 * m + (i : ℕ)) := by have := i.2; omega
          simp [hnot4]
        rw [hz]; exact summable_zero
    · exact Summable.of_finite
  have hsum_8 : Summable (fun n : ℕ =>
      8 * LSeries.term (fun k => (ArithmeticFunction.sigma 1 k : ℂ)) s n) :=
    hsum_sig.mul_left 8
  have hL_split : LSeries (fun n : ℕ => (repFourSquares n : ℂ)) s =
      (∑' n : ℕ, 8 * LSeries.term (fun k => (ArithmeticFunction.sigma 1 k : ℂ)) s n) -
      (∑' n : ℕ, if n = 0 then (0 : ℂ) else
        (if 4 ∣ n then (32 : ℂ) * (ArithmeticFunction.sigma 1 (n / 4) : ℂ) else 0) / (n : ℂ) ^ s) := by
    rw [← hsum_8.tsum_sub hsum_sig4]
    unfold LSeries
    refine tsum_congr fun n => ?_
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · simp only [LSeries.term, hn, ↓reduceIte]
      have hjac := jacobi_four_squares_formula n (Nat.pos_of_ne_zero hn)
      have hdiv := congrArg (Int.cast (R := ℂ)) (jacobi_four_divisor_identity n)
      push_cast at hdiv
      have hr4C : (repFourSquares n : ℂ) =
          8 * (ArithmeticFunction.sigma 1 n : ℂ) -
            (if 4 ∣ n then (32 : ℂ) * (ArithmeticFunction.sigma 1 (n / 4) : ℂ) else 0) := by
        rw [hjac]
        push_cast
        rw [hdiv]
        split_ifs <;> ring
      rw [hr4C]; ring
  have hpart2 : (∑' n : ℕ, if n = 0 then (0 : ℂ) else
      (if 4 ∣ n then (32 : ℂ) * (ArithmeticFunction.sigma 1 (n / 4) : ℂ) else 0) / (n : ℂ) ^ s) =
      32 * (4 : ℂ) ^ (-s) * LSeries (fun k => (ArithmeticFunction.sigma 1 k : ℂ)) s := by
    let eMod4 : Fin 4 × ℕ ≃ ℕ :=
      { toFun := fun p => 4 * p.2 + (p.1 : ℕ)
        invFun := fun m => (⟨m % 4, Nat.mod_lt m (by decide)⟩, m / 4)
        left_inv := fun p => by ext <;> (dsimp; have := p.1.2; omega)
        right_inv := fun m => by dsimp; omega }
    rw [← eMod4.tsum_eq]
    have hs_mod4 := eMod4.summable_iff.mpr hsum_sig4
    change (∑' p : Fin 4 × ℕ,
        ((fun n : ℕ => if n = 0 then (0 : ℂ) else
          (if 4 ∣ n then (32 : ℂ) * (ArithmeticFunction.sigma 1 (n / 4) : ℂ) else 0) /
            (n : ℂ) ^ s) ∘ eMod4) p) = _
    rw [hs_mod4.tsum_prod']
    · have hzero : ∀ i : Fin 4, i ≠ 0 →
          (∑' m : ℕ, if 4 * m + (i : ℕ) = 0 then (0 : ℂ) else
            (if 4 ∣ (4 * m + (i : ℕ)) then
              (32 : ℂ) * (ArithmeticFunction.sigma 1 ((4 * m + (i : ℕ)) / 4) : ℂ) else 0) /
            ((4 * m + (i : ℕ) : ℕ) : ℂ) ^ s) = 0 := by
        intro i hi
        have hz : (fun m : ℕ => if 4 * m + (i : ℕ) = 0 then (0 : ℂ) else
            (if 4 ∣ (4 * m + (i : ℕ)) then
              (32 : ℂ) * (ArithmeticFunction.sigma 1 ((4 * m + (i : ℕ)) / 4) : ℂ) else 0) /
            ((4 * m + (i : ℕ) : ℕ) : ℂ) ^ s) = fun _ => (0 : ℂ) := by
          funext m
          have hi0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
          have hnot4 : ¬ 4 ∣ (4 * m + (i : ℕ)) := by have := i.2; omega
          simp [hnot4]
        rw [hz, tsum_zero]
      rw [tsum_fintype, Finset.sum_eq_single (0 : Fin 4)
        (fun i _ hi => by simpa [Function.comp_apply, eMod4] using hzero i hi)
        (fun h => absurd (Finset.mem_univ _) h)]
      unfold LSeries
      rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      change (if 4 * m + 0 = 0 then (0 : ℂ) else
          (if 4 ∣ (4 * m + 0) then (32 : ℂ) * (ArithmeticFunction.sigma 1 ((4 * m + 0) / 4) : ℂ)
            else 0) / ((4 * m + 0 : ℕ) : ℂ) ^ s) = _
      rw [add_zero]
      by_cases hm : m = 0
      · simp [hm, LSeries.term]
      · have h4m : 4 * m ≠ 0 := mul_ne_zero (by decide) hm
        simp only [h4m, ↓reduceIte, LSeries.term, hm]
        rw [if_pos ⟨m, rfl⟩, Nat.mul_div_cancel_left m (by decide)]
        have hcpow : ((4 * m : ℕ) : ℂ) ^ s = (4 : ℂ) ^ s * (m : ℂ) ^ s := by
          have h4mC : ((4 * m : ℕ) : ℂ) = ((4 : ℝ) : ℂ) * ((m : ℝ) : ℂ) := by push_cast; rfl
          rw [h4mC, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
          norm_cast
        rw [hcpow, Complex.cpow_neg]
        ring
    · intro i
      exact hs_mod4.comp_injective (fun _ _ h => (Prod.mk.inj h).2)
  rw [hL_split, tsum_mul_left, hpart2]
  have hL_sig := LSeries_sigma_eq_riemannZeta_mul 1 hs_sig
  change 8 * LSeries (fun k => (ArithmeticFunction.sigma 1 k : ℂ)) s -
    32 * (4 : ℂ) ^ (-s) * LSeries (fun k => (ArithmeticFunction.sigma 1 k : ℂ)) s = _
  rw [hL_sig]
  have h4pow : (4 : ℂ) ^ (1 - s) = 4 * (4 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num : (4 : ℂ) ≠ 0), Complex.cpow_one]
  rw [h4pow]
  push_cast
  ring

/-- **`ℕ+`-Indexed Dirichlet Series Identity for `r₄(n)`** on `Re(s) > 2`:
$$\sum_{n=1}^{\infty} r_4(n) \, n^{-s} = 8 \left(1 - 4^{1 - s}\right) \zeta(s) \, \zeta(s - 1).$$ -/
theorem tsum_repFourSquares_dirichletSeries {s : ℂ} (hs : 2 < s.re) :
    (∑' n : ℕ+, (repFourSquares (n : ℕ) : ℂ) * ((n : ℕ) : ℂ) ^ (-s)) =
      8 * (1 - (4 : ℂ) ^ (1 - s)) * riemannZeta s * riemannZeta (s - 1) := by
  have hsum_sig : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.sigma 1 n : ℂ)) s := by
    have hs1 : 1 < s.re := by linarith
    have hs1' : 1 < (s - (1 : ℂ)).re := by simp; linarith
    have hsum1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs1
    have hsum_id : LSeriesSummable (fun n : ℕ => (n : ℂ) ^ 1) s := by
      refine (LSeriesSummable_one_iff.mpr hs1').congr fun n => ?_
      by_cases hn : n = 0
      · simp [LSeries.term, hn]
      · simp only [LSeries.term, hn, ↓reduceIte, Pi.one_apply, pow_one]
        have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        rw [Complex.cpow_sub _ _ hnC, Complex.cpow_one, div_div_eq_mul_div, one_mul]
    have hconv : LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => (n : ℂ) ^ 1) =
        fun n : ℕ => (ArithmeticFunction.sigma 1 n : ℂ) := by
      funext n
      rw [LSeries.convolution_def, ArithmeticFunction.sigma_apply]
      dsimp only
      have hsum_anti :
          (∑ p ∈ n.divisorsAntidiagonal, (1 : ℕ → ℂ) p.1 * (p.2 : ℂ) ^ 1) =
          ∑ d ∈ n.divisors, (d : ℂ) ^ 1 := by
        refine Finset.sum_nbij' (fun p => p.2) (fun d => (n / d, d)) ?_ ?_ ?_ ?_ ?_
        · intro p hp; exact Nat.snd_mem_divisors_of_mem_antidiagonal hp
        · intro d hd
          exact Nat.mem_divisorsAntidiagonal.mpr
            ⟨Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd), (Nat.mem_divisors.mp hd).2⟩
        · intro p hp
          rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, hn0⟩
          have hp2_pos : 0 < p.2 := Nat.pos_of_ne_zero (fun h0 => hn0 (by simp [← hpmul, h0]))
          ext
          · exact (Nat.eq_div_of_mul_eq_left hp2_pos.ne' hpmul).symm
          · rfl
        · intro _ _; rfl
        · intro p _; simp
      rw [hsum_anti]; push_cast; rfl
    rw [← hconv]; exact hsum1.convolution hsum_id
  have hsum_r4 : LSeriesSummable (fun n : ℕ => (repFourSquares n : ℂ)) s := by
    refine Summable.of_norm_bounded
      (g := fun n => 8 * ‖LSeries.term (fun k => (ArithmeticFunction.sigma 1 k : ℂ)) s n‖)
      (hsum_sig.norm.mul_left 8) ?_
    intro n
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · simp only [LSeries.term, hn, ↓reduceIte, norm_div, Complex.norm_natCast]
      have hle : repFourSquares n ≤ 8 * ArithmeticFunction.sigma 1 n := by
        rw [jacobi_four_squares_formula n (Nat.pos_of_ne_zero hn), ArithmeticFunction.sigma_apply]
        simp only [pow_one]
        exact Nat.mul_le_mul_left 8 (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
      have hleR : (repFourSquares n : ℝ) ≤ 8 * (ArithmeticFunction.sigma 1 n : ℝ) := by
        exact_mod_cast hle
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hleR (norm_nonneg _)
  rw [← LSeries_repFourSquares_eq hs]
  unfold LSeries
  rw [hsum_r4.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  let e : ℕ+ ≃ ℕ :=
    { toFun := fun n => (n : ℕ) - 1
      invFun := fun m => ⟨m + 1, Nat.succ_pos m⟩
      left_inv := fun n => Subtype.ext (Nat.sub_add_cancel n.pos)
      right_inv := fun m => Nat.add_sub_cancel m 1 }
  rw [← e.tsum_eq]
  refine tsum_congr fun n => ?_
  have hsucc : e n + 1 = (n : ℕ) := Nat.sub_add_cancel n.pos
  rw [hsucc]
  unfold LSeries.term
  rw [if_neg n.ne_zero, div_eq_mul_inv, Complex.cpow_neg]

/-- Explicit verification: `r₄(1) = 8`. -/
theorem repFourSquares_one : repFourSquares 1 = 8 := by
  have h := jacobi_four_squares_formula 1 (by decide)
  have hdiv : (1 : ℕ).divisors = {1} := by decide
  rw [hdiv] at h; exact h.trans (by decide)

/-- Explicit verification: `r₄(2) = 24`. -/
theorem repFourSquares_two : repFourSquares 2 = 24 := by
  have h := jacobi_four_squares_formula 2 (by decide)
  have hdiv : (2 : ℕ).divisors = {1, 2} := by decide
  rw [hdiv] at h; exact h.trans (by decide)

/-- Explicit verification: `r₄(3) = 32`. -/
theorem repFourSquares_three : repFourSquares 3 = 32 := by
  have h := jacobi_four_squares_formula 3 (by decide)
  have hdiv : (3 : ℕ).divisors = {1, 3} := by decide
  rw [hdiv] at h; exact h.trans (by decide)

/-- Explicit verification: `r₄(4) = 24`. -/
theorem repFourSquares_four : repFourSquares 4 = 24 := by
  have h := jacobi_four_squares_formula 4 (by decide)
  have hdiv : (4 : ℕ).divisors = {1, 2, 4} := by decide
  rw [hdiv] at h; exact h.trans (by decide)

end JacobiFourSquares

end
end RHDirect.Stage9JacobiSquares
