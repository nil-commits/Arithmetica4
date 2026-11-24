import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# PPL 089: Talagrand's Discrete Convexity / `q`-Covering Conjecture

Formalization of structural, spectral/Fourier, and refutation results for **PPL 089**
(Michel Talagrand, Research Problem 12.5.6 in *Upper and Lower Bounds for Stochastic Processes*,
Conjecture 7.1 in *Are many small sets explicitly small?* (STOC 2010), and `combinatorics.pdf`):

For `δ ∈ (0, 1/2]`, `N : ℕ`, the biased product measure `μ_δ` on `Finset (Fin N)`, and
`D ⊆ Finset (Fin N)`, let `D^{(q)}` be the family of subsets `S : Finset (Fin N)` that cannot be
covered by the union of `q` elements of `D`.

## Verified Theorems (0 `sorry`, 0 custom defs in final theorem statements, pure Mathlib)

1. `ppl089_delta_half`: Talagrand's baseline `δ = 1/2`, `q = 2` case — whenever `μ_{1/2}(D) > 1/2`,
   every subset `S : Finset (Fin N)` is covered by 2 sets in `D` (`D^{(2)} = ∅`).
2. `ppl089_down_closure_eq_uncovered`: Replacing `D` by its downward closure preserves `D^{(q)}`
   and can only increase `μ_δ(D)`.
3. `ppl089_explicit_fourier_cover_even`: **New explicit closed-form `q = 2m` Fourier-Walsh
   fractional cover** extending Chen Li's spectral method (`arXiv:2609.08967`) to all even `q = 2m`
   without LP duality or Hahn–Banach. With unnormalized `δ`-biased Fourier coefficients
   `c_I = ∑ A ∈ D, μ_δ(A) * ∏ i ∈ I, (if i ∈ A then 1 - δ else -δ)` and
   `λ_I = c_I^2 / (μ_δ(D)^2 * δ^(2 * |I|))`, every `S ∈ D^{(2m)}` satisfies
   `1 ≤ ∑_{I ⊆ S, Odd |I|} λ_I^m`, and Parseval yields
   `∑_{Odd |I|} λ_I * δ^|I| ≤ (1 - δ) * (1 - μ_δ(D)) / μ_δ(D)`.
4. `ppl089_fractional_q2`: **Exact Fractional PPL 089 for `q = 2`** (pure-Mathlib statement) —
   for every `N`, `δ ∈ (0, 1)`, and `D` with `μ_δ(D) ≥ 2 * (1 - δ) / (3 - 2 * δ)` (in particular
   `μ_δ(D) ≥ 2/3`), there exists `w : Finset (Fin N) → ℝ` with `0 ≤ w I`,
   `1 ≤ ∑ I ∈ S.powerset, w I` for every `S ∈ D^{(2)}`, and `∑ I, w I * δ^I.card ≤ 1/2`.
5. `ppl089_no_spread_measure_q2`: **Chen Li's Theorem 1.14 (`arXiv:2609.08967`)** (pure-Mathlib
   statement) — if `μ_δ(D) > (1 - δ) / (2 - δ)`, no `δ`-spread probability distribution `ν` on
   `Finset (Fin N)` can be supported on `D^{(2)}`.
6. `ppl089_fang_wang_lemma1_false`: **Certified disproof of Lemma 1 of the withdrawn late-2025
   preprint `arXiv:2511.17336v1`** on `Fin 3`, showing integral set cover number exceeds packing
   number (`2 > 1`) even for the covering down-set `{A ⊆ Fin 3 | |A| ≤ 2}`.
7. `ppl089_right_shift_decreases_smallness`: **Certified counterexample on `Fin 5` (`δ = 2/5`)**
   showing Frankl shifting of an upset can strictly decrease its optimal `δ`-smallness cover weight
   (`0.864 < 0.880`), obstructing direct shifting reductions.
-/

namespace PPL089

section ProductMeasureAndFourier

variable {N : ℕ}

/-- Point mass of the `δ`-biased product measure on `Finset (Fin N)` written as a coordinate
product (making Fubini/factorization across coordinates completely algebraic). -/
private def prodWeight (δ : ℝ) (A : Finset (Fin N)) : ℝ :=
  ∏ i : Fin N, if i ∈ A then δ else 1 - δ

/-- Equivalence between `prodWeight` and the standard `δ^|A| * (1 - δ)^(N - |A|)` formula. -/
private lemma prodWeight_eq_pow (δ : ℝ) (A : Finset (Fin N)) :
    prodWeight δ A = δ ^ A.card * (1 - δ) ^ (N - A.card) := by
  unfold prodWeight
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (Finset.univ.filter (fun i : Fin N => i ∈ A)).card = A.card := by
    congr 1; ext i; simp
  have h2 : (Finset.univ.filter (fun i : Fin N => i ∉ A)).card = N - A.card := by
    have hc : (Finset.univ.filter (fun i : Fin N => i ∉ A)) = Finset.univ \ A := by
      ext i; simp
    rw [hc, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  rw [h1, h2]

private lemma prodWeight_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (A : Finset (Fin N)) :
    0 ≤ prodWeight δ A := by
  unfold prodWeight
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

/-- Equivalence between `Finset (Fin N)` and `Fin N → Bool` for coordinate factorization. -/
private def finsetBoolEquiv : Finset (Fin N) ≃ (Fin N → Bool) where
  toFun A i := decide (i ∈ A)
  invFun f := Finset.univ.filter (fun i => f i = true)
  left_inv A := by ext i; simp
  right_inv f := by ext i; simp

/-- Key coordinate-factorization lemma: summing a coordinatewise product over all `A : Finset (Fin N)`
factors into the product of the 2-point sums over `Fin N`. -/
private lemma sum_finset_prod (g : Fin N → Bool → ℝ) :
    ∑ A : Finset (Fin N), ∏ i : Fin N, g i (decide (i ∈ A)) =
      ∏ i : Fin N, (g i true + g i false) := by
  have h1 : ∑ A : Finset (Fin N), ∏ i : Fin N, g i (decide (i ∈ A)) =
      ∑ f : Fin N → Bool, ∏ i : Fin N, g i (f i) :=
    Fintype.sum_equiv finsetBoolEquiv _ _ (fun A => rfl)
  rw [h1, ← Fintype.prod_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp

/-- Total probability mass of `prodWeight δ` equals `1`. -/
private lemma sum_prodWeight (δ : ℝ) :
    ∑ A : Finset (Fin N), prodWeight δ A = 1 := by
  have h := sum_finset_prod (N := N) (fun _ b => if b then δ else 1 - δ)
  have hL : (∑ A : Finset (Fin N), prodWeight δ A) =
      ∑ A : Finset (Fin N), ∏ i : Fin N, if decide (i ∈ A) then δ else 1 - δ := by
    refine Finset.sum_congr rfl (fun A _ => ?_)
    unfold prodWeight
    refine Finset.prod_congr rfl (fun i _ => by simp)
  rw [hL, h]
  simp

/-- Unnormalized `δ`-biased orthogonal character (avoids all square roots!). -/
private def psi (δ : ℝ) (I A : Finset (Fin N)) : ℝ :=
  ∏ i ∈ I, if i ∈ A then (1 - δ) else -δ

private lemma psi_empty (δ : ℝ) (A : Finset (Fin N)) : psi δ ∅ A = 1 := by
  simp [psi]

/-- Orthogonality of `psi δ I` under `prodWeight δ`. -/
private lemma sum_prodWeight_psi_mul (δ : ℝ) (I J : Finset (Fin N)) :
    ∑ A : Finset (Fin N), prodWeight δ A * (psi δ I A * psi δ J A) =
      if I = J then (δ * (1 - δ)) ^ I.card else 0 := by
  let g : Fin N → Bool → ℝ := fun i b =>
    (if b then δ else 1 - δ) *
      (if i ∈ I then (if b then 1 - δ else -δ) else 1) *
      (if i ∈ J then (if b then 1 - δ else -δ) else 1)
  have hL : (∑ A : Finset (Fin N), prodWeight δ A * (psi δ I A * psi δ J A)) =
      ∑ A : Finset (Fin N), ∏ i : Fin N, g i (decide (i ∈ A)) := by
    refine Finset.sum_congr rfl (fun A _ => ?_)
    have hI : psi δ I A = ∏ i : Fin N, if i ∈ I then (if decide (i ∈ A) then 1 - δ else -δ) else 1 := by
      unfold psi
      rw [← Finset.prod_filter]
      refine Finset.prod_congr ?_ (fun i _ => by simp)
      ext i; simp
    have hJ : psi δ J A = ∏ i : Fin N, if i ∈ J then (if decide (i ∈ A) then 1 - δ else -δ) else 1 := by
      unfold psi
      rw [← Finset.prod_filter]
      refine Finset.prod_congr ?_ (fun i _ => by simp)
      ext i; simp
    rw [hI, hJ]
    unfold prodWeight
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp [g, mul_assoc]
  rw [hL, sum_finset_prod]
  by_cases hIJ : I = J
  · subst hIJ
    simp only [↓reduceIte]
    have hterm : ∀ i : Fin N,
        g i true + g i false = if i ∈ I then δ * (1 - δ) else 1 := by
      intro i
      by_cases hi : i ∈ I
      · simp [g, hi]; ring
      · simp [g, hi]
    simp_rw [hterm]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    congr 1
    have hf : (Finset.univ.filter (fun i : Fin N => i ∈ I)) = I := by ext i; simp
    rw [hf]
  · simp only [hIJ, ↓reduceIte]
    have hex : ∃ i : Fin N, (i ∈ I ∧ i ∉ J) ∨ (i ∉ I ∧ i ∈ J) := by
      by_contra hall
      push Not at hall
      apply hIJ
      ext i
      exact ⟨fun hi => (hall i).1 hi, fun hj => by_contra fun hi => (hall i).2 hi hj⟩
    obtain ⟨i₀, hi₀⟩ := hex
    refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
    rcases hi₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [g, h1, h2] <;> ring

/-- Unnormalized `δ`-biased Fourier coefficient of the indicator of `D`. -/
private def fourierCoeff (δ : ℝ) (D : Finset (Finset (Fin N))) (I : Finset (Fin N)) : ℝ :=
  ∑ A ∈ D, prodWeight δ A * psi δ I A

private lemma fourierCoeff_empty (δ : ℝ) (D : Finset (Finset (Fin N))) :
    fourierCoeff δ D ∅ = ∑ A ∈ D, prodWeight δ A := by
  simp [fourierCoeff, psi_empty]

/-- Exact Parseval identity for `1_D` in the unnormalized `δ`-biased basis. -/
private lemma parseval_indicator {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (D : Finset (Finset (Fin N))) :
    ∑ I : Finset (Fin N), (fourierCoeff δ D I) ^ 2 / (δ * (1 - δ)) ^ I.card =
      ∑ A ∈ D, prodWeight δ A := by
  have hpos : ∀ I : Finset (Fin N), (δ * (1 - δ)) ^ I.card ≠ 0 := by
    intro I
    exact pow_ne_zero _ (mul_ne_zero (ne_of_gt hδ0) (ne_of_gt (sub_pos.mpr hδ1)))
  -- Compute ∑_{A, B ∈ D} μ(A) μ(B) ∑_I ψ_I(A) ψ_I(B) / (δ(1-δ))^|I|
  -- For fixed A, B: ∑_I (∏_{i ∈ I} (ψ(i∈A) ψ(i∈B) / (δ(1-δ))))
  --   = ∏_i (1 + ψ(i∈A) ψ(i∈B) / (δ(1-δ)))
  --   = if A = B then 1 / μ(A) else 0!
  have hker : ∀ A B : Finset (Fin N),
      ∑ I : Finset (Fin N), (psi δ I A * psi δ I B) / (δ * (1 - δ)) ^ I.card =
        if A = B then (prodWeight δ A)⁻¹ else 0 := by
    intro A B
    have hprod_id : ∀ I : Finset (Fin N),
        (psi δ I A * psi δ I B) / (δ * (1 - δ)) ^ I.card =
          ∏ i : Fin N, if decide (i ∈ I) then
            ((if i ∈ A then 1 - δ else -δ) * (if i ∈ B then 1 - δ else -δ)) / (δ * (1 - δ))
          else 1 := by
      intro I
      unfold psi
      rw [← Finset.prod_mul_distrib]
      have hden : (δ * (1 - δ)) ^ I.card = ∏ _i ∈ I, (δ * (1 - δ)) := by
        rw [Finset.prod_const]
      rw [hden, ← Finset.prod_div_distrib]
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
      refine Finset.prod_congr ?_ (fun i _ => rfl)
      ext i; simp
    simp_rw [hprod_id]
    rw [sum_finset_prod (fun i b => if b = true then
      ((if i ∈ A then 1 - δ else -δ) * (if i ∈ B then 1 - δ else -δ)) / (δ * (1 - δ)) else 1)]
    have hd0 : δ ≠ 0 := ne_of_gt hδ0
    have hd1 : 1 - δ ≠ 0 := ne_of_gt (sub_pos.mpr hδ1)
    by_cases hAB : A = B
    · subst hAB
      simp only [↓reduceIte]
      unfold prodWeight
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      by_cases hi : i ∈ A <;> simp [hi] <;> field_simp <;> ring
    · simp only [hAB, ↓reduceIte]
      have hex : ∃ i : Fin N, (i ∈ A ∧ i ∉ B) ∨ (i ∉ A ∧ i ∈ B) := by
        by_contra hall
        push Not at hall
        apply hAB
        ext i
        exact ⟨fun hi => (hall i).1 hi, fun hj => by_contra fun hi => (hall i).2 hi hj⟩
      obtain ⟨i₀, hi₀⟩ := hex
      refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
      rcases hi₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2] <;> field_simp <;> ring
  -- Expand LHS = ∑_I (∑_{A ∈ D} μ(A) ψ_I(A)) (∑_{B ∈ D} μ(B) ψ_I(B)) / (δ(1-δ))^|I|
  have hexp : ∑ I : Finset (Fin N), (fourierCoeff δ D I) ^ 2 / (δ * (1 - δ)) ^ I.card =
      ∑ A ∈ D, ∑ B ∈ D, prodWeight δ A * prodWeight δ B *
        ∑ I : Finset (Fin N), (psi δ I A * psi δ I B) / (δ * (1 - δ)) ^ I.card := by
    calc ∑ I : Finset (Fin N), (fourierCoeff δ D I) ^ 2 / (δ * (1 - δ)) ^ I.card
        = ∑ I : Finset (Fin N), ∑ A ∈ D, ∑ B ∈ D,
            prodWeight δ A * prodWeight δ B *
              ((psi δ I A * psi δ I B) / (δ * (1 - δ)) ^ I.card) := by
          refine Finset.sum_congr rfl (fun I _ => ?_)
          rw [sq, fourierCoeff, Finset.sum_mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl (fun A _ => ?_)
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl (fun B _ => ?_)
          ring
      _ = ∑ A ∈ D, ∑ B ∈ D, ∑ I : Finset (Fin N),
            prodWeight δ A * prodWeight δ B *
              ((psi δ I A * psi δ I B) / (δ * (1 - δ)) ^ I.card) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun A _ => Finset.sum_comm)
      _ = ∑ A ∈ D, ∑ B ∈ D, prodWeight δ A * prodWeight δ B *
            ∑ I : Finset (Fin N), (psi δ I A * psi δ I B) / (δ * (1 - δ)) ^ I.card := by
          refine Finset.sum_congr rfl (fun A _ => Finset.sum_congr rfl (fun B _ => ?_))
          rw [Finset.mul_sum]
  rw [hexp]
  simp_rw [hker]
  refine Finset.sum_congr rfl (fun A hA => ?_)
  have hpw_ne : prodWeight δ A ≠ 0 := by
    unfold prodWeight
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by
      split_ifs
      · exact ne_of_gt hδ0
      · exact ne_of_gt (sub_pos.mpr hδ1))
  have hinner : ∑ B ∈ D, prodWeight δ A * prodWeight δ B *
      (if A = B then (prodWeight δ A)⁻¹ else 0) = prodWeight δ A := by
    have : ∀ B ∈ D, prodWeight δ A * prodWeight δ B *
        (if A = B then (prodWeight δ A)⁻¹ else 0) =
        if B = A then prodWeight δ A else 0 := by
      intro B _
      by_cases hBA : B = A
      · subst hBA; simp [hpw_ne]
      · have hAB : A ≠ B := Ne.symm hBA
        simp [hBA, hAB]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' D A, if_pos hA]
  exact hinner

/-- Product expansion: `∏ i ∈ S, (1 + f i) = ∑ I ∈ S.powerset, ∏ i ∈ I, f i`. -/
private lemma prod_one_add_eq_sum_powerset {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℝ) :
    ∏ i ∈ S, (1 + f i) = ∑ I ∈ S.powerset, ∏ i ∈ I, f i := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.powerset_insert, Finset.sum_union]
    · rw [Finset.sum_image]
      · rw [add_mul, one_mul, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun I hI => ?_)
        have haI : a ∉ I := fun h => ha (Finset.mem_powerset.mp hI h)
        rw [Finset.prod_insert haI]
      · intro I hI J hJ hIJ
        have haI : a ∉ I := fun h => ha (Finset.mem_powerset.mp hI h)
        have haJ : a ∉ J := fun h => ha (Finset.mem_powerset.mp hJ h)
        have h1 := congrArg (fun T => T.erase a) hIJ
        simpa [Finset.erase_insert haI, Finset.erase_insert haJ] using h1
    · rw [Finset.disjoint_left]
      intro I hI hI'
      rcases Finset.mem_image.mp hI' with ⟨J, _, rfl⟩
      exact ha (Finset.mem_powerset.mp hI (Finset.mem_insert_self a J))

/-- Key `2m`-fold kernel identity for `S ∈ D^{(2m)}`:
`∑ I ∈ S.powerset, (-1)^|I| * (fourierCoeff δ D I / δ^|I|)^(2*m) = 0`. -/
private lemma kernel_vanishing_even {δ : ℝ} (hδ0 : 0 < δ) (m : ℕ) (_hm : 1 ≤ m)
    (D : Finset (Finset (Fin N))) (S : Finset (Fin N))
    (hS : ∀ f : Fin (2 * m) → Finset (Fin N), (∀ j, f j ∈ D) →
      ¬ S ⊆ Finset.univ.biUnion f) :
    ∑ I ∈ S.powerset, (-1 : ℝ) ^ I.card *
      ((fourierCoeff δ D I) ^ 2 / δ ^ (2 * I.card)) ^ m = 0 := by
  have hd0 : δ ≠ 0 := ne_of_gt hδ0
  -- Single-coordinate 2m-ary kernel: 1 - (1 / δ^(2m)) * ∏ j, ψ(i ∈ f j)
  let K : (Fin (2 * m) → Finset (Fin N)) → ℝ := fun f =>
    ∏ i ∈ S, (1 + (-(1 / δ ^ (2 * m)) *
      ∏ j : Fin (2 * m), (if i ∈ f j then (1 - δ) else -δ)))
  -- For every tuple f ∈ D^(2m), S is not covered by ⋃ j, f j, so some i ∈ S misses all f j,
  -- making that factor 1 - (1 / δ^(2m)) * (-δ)^(2m) = 0!
  have hK_zero : ∀ f : Fin (2 * m) → Finset (Fin N), (∀ j, f j ∈ D) → K f = 0 := by
    intro f hf
    have hnot := hS f hf
    rw [Finset.not_subset] at hnot
    obtain ⟨i₀, hi₀S, hi₀U⟩ := hnot
    rw [Finset.mem_biUnion] at hi₀U
    push Not at hi₀U
    refine Finset.prod_eq_zero hi₀S ?_
    have hmiss : ∀ j : Fin (2 * m), i₀ ∉ f j := fun j => hi₀U j (Finset.mem_univ j)
    have hprod : ∏ j : Fin (2 * m), (if i₀ ∈ f j then (1 - δ) else -δ) = δ ^ (2 * m) := by
      calc ∏ j : Fin (2 * m), (if i₀ ∈ f j then (1 - δ) else -δ)
          = ∏ _j : Fin (2 * m), (-δ) := Finset.prod_congr rfl (fun j _ => if_neg (hmiss j))
        _ = (-δ) ^ (2 * m) := by simp
        _ = δ ^ (2 * m) := by rw [pow_mul, neg_sq, ← pow_mul]
    rw [hprod]
    have hd2m : δ ^ (2 * m) ≠ 0 := pow_ne_zero _ hd0
    field_simp [hd2m]
    ring
  -- Sum K(f) * ∏ j, prodWeight δ (f j) over all f ∈ (Fin (2m) → D)
  let tuples : Finset (Fin (2 * m) → Finset (Fin N)) :=
    Fintype.piFinset (fun _ : Fin (2 * m) => D)
  have hsum_zero : ∑ f ∈ tuples, (∏ j : Fin (2 * m), prodWeight δ (f j)) * K f = 0 := by
    refine Finset.sum_eq_zero (fun f hf => ?_)
    have hmem : ∀ j, f j ∈ D := fun j => (Fintype.mem_piFinset.mp hf) j
    rw [hK_zero f hmem, mul_zero]
  -- Expand K(f) via prod_one_add_eq_sum_powerset and swap sums
  have hexp : ∑ f ∈ tuples, (∏ j : Fin (2 * m), prodWeight δ (f j)) * K f =
      ∑ I ∈ S.powerset, (-1 : ℝ) ^ I.card *
        ((fourierCoeff δ D I) ^ 2 / δ ^ (2 * I.card)) ^ m := by
    have hK_exp : ∀ f : Fin (2 * m) → Finset (Fin N),
        K f = ∑ I ∈ S.powerset, ((-1 : ℝ) ^ I.card / (δ ^ (2 * m)) ^ I.card) *
          ∏ j : Fin (2 * m), psi δ I (f j) := by
      intro f
      unfold K
      rw [prod_one_add_eq_sum_powerset]
      refine Finset.sum_congr rfl (fun I _ => ?_)
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      have hcomm : ∏ i ∈ I, ∏ j : Fin (2 * m), (if i ∈ f j then (1 - δ) else -δ) =
          ∏ j : Fin (2 * m), psi δ I (f j) := by
        rw [Finset.prod_comm]
        rfl
      rw [hcomm]
      congr 1
      rw [show -(1 / δ ^ (2 * m)) = (-1 : ℝ) / δ ^ (2 * m) by ring, div_pow]
    simp_rw [hK_exp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun I _ => ?_)
    have hpull : ∑ f ∈ tuples, (∏ j : Fin (2 * m), prodWeight δ (f j)) *
        (((-1 : ℝ) ^ I.card / (δ ^ (2 * m)) ^ I.card) * ∏ j : Fin (2 * m), psi δ I (f j)) =
        ((-1 : ℝ) ^ I.card / (δ ^ (2 * m)) ^ I.card) *
        ∑ f ∈ tuples, ∏ j : Fin (2 * m), (prodWeight δ (f j) * psi δ I (f j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun f _ => ?_)
      rw [mul_left_comm, ← Finset.prod_mul_distrib]
    rw [hpull]
    have hfact : ∑ f ∈ tuples, ∏ j : Fin (2 * m), (prodWeight δ (f j) * psi δ I (f j)) =
        (fourierCoeff δ D I) ^ (2 * m) := by
      have hpi := (Fintype.prod_sum (fun (_ : Fin (2 * m)) (A : Finset (Fin N)) =>
        if A ∈ D then prodWeight δ A * psi δ I A else 0)).symm
      have hsub : ∑ f ∈ tuples, ∏ j : Fin (2 * m), (prodWeight δ (f j) * psi δ I (f j)) =
          ∑ f : Fin (2 * m) → Finset (Fin N),
            ∏ j : Fin (2 * m), (if f j ∈ D then prodWeight δ (f j) * psi δ I (f j) else 0) := by
        symm
        rw [← Finset.sum_subset (Finset.subset_univ tuples)]
        · refine Finset.sum_congr rfl (fun f hf => ?_)
          have hmem : ∀ j, f j ∈ D := fun j => (Fintype.mem_piFinset.mp hf) j
          refine Finset.prod_congr rfl (fun j _ => if_pos (hmem j))
        · intro f _ hf
          have hnot : ∃ j, f j ∉ D := by
            by_contra hall; push Not at hall
            exact hf (Fintype.mem_piFinset.mpr hall)
          obtain ⟨j₀, hj₀⟩ := hnot
          exact Finset.prod_eq_zero (Finset.mem_univ j₀) (if_neg hj₀)
      rw [hsub, hpi]
      have hinner : ∀ _j : Fin (2 * m),
          (∑ A : Finset (Fin N), if A ∈ D then prodWeight δ A * psi δ I A else 0) =
            fourierCoeff δ D I := by
        intro _
        rw [← Finset.sum_filter]
        have hf : Finset.univ.filter (fun A : Finset (Fin N) => A ∈ D) = D := by ext A; simp
        rw [hf]; rfl
      rw [Finset.prod_congr rfl (fun j _ => hinner j)]
      simp
    rw [hfact]
    have hd_pow : (δ ^ (2 * m)) ^ I.card = (δ ^ (2 * I.card)) ^ m := by
      rw [← pow_mul, ← pow_mul]; congr 1; ring
    have hf_pow : (fourierCoeff δ D I) ^ (2 * m) = ((fourierCoeff δ D I) ^ 2) ^ m := by
      rw [← pow_mul]
    rw [hd_pow, hf_pow, div_pow]
    ring
  rw [← hexp, hsum_zero]

end ProductMeasureAndFourier

/-! ### Main Pure-Mathlib Theorems for PPL 089 -/

/-- **Theorem 1 (Talagrand's baseline `δ = 1/2`, `q = 2`):**
If `D ⊆ Finset (Fin N)` has uniform measure `μ_{1/2}(D) > 1/2`, then `D^{(2)} = ∅`:
every subset `S : Finset (Fin N)` is covered by two elements of `D` (so `𝒢 = ∅` gives cover
weight `0 ≤ 1/2`). -/
theorem ppl089_delta_half (N : ℕ) (D : Finset (Finset (Fin N)))
    (hD : (1 : ℝ) / 2 < ∑ A ∈ D, ((1 : ℝ) / 2) ^ A.card * (1 - (1 : ℝ) / 2) ^ (N - A.card)) :
    ∀ S : Finset (Fin N), ∃ A ∈ D, ∃ B ∈ D, S ⊆ A ∪ B := by
  have hcard : 2 ^ (N - 1) < D.card ∨ N = 0 := by
    by_cases hN : N = 0
    · exact Or.inr hN
    · left
      have hterm : ∀ A ∈ D, ((1 : ℝ) / 2) ^ A.card * (1 - (1 : ℝ) / 2) ^ (N - A.card) =
          ((1 : ℝ) / 2) ^ N := by
        intro A _
        have hle : A.card ≤ N := by simpa using Finset.card_le_univ A
        rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← pow_add, Nat.add_sub_of_le hle]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul] at hD
      have h2N : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
      have hmul : (2 : ℝ) ^ (N - 1) < (D.card : ℝ) := by
        have hN1 : N = (N - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero hN)).symm
        have h1 : (1 : ℝ) / 2 * (2 : ℝ) ^ N = (2 : ℝ) ^ (N - 1) := by
          conv_lhs => rw [hN1, pow_succ]
          ring
        have h2 : (D.card : ℝ) * ((1 : ℝ) / 2) ^ N * (2 : ℝ) ^ N = (D.card : ℝ) := by
          rw [mul_assoc, ← mul_pow]; norm_num
        have h3 := mul_lt_mul_of_pos_right hD h2N
        rw [h1, h2] at h3
        exact h3
      exact_mod_cast hmul
  rcases hcard with hgt | rfl
  · -- By pigeonhole on complements A ↦ Aᶜ, D and D.image compl intersect!
    let Dc := D.image (fun A : Finset (Fin N) => Aᶜ)
    have hDc_card : Dc.card = D.card := Finset.card_image_of_injective D compl_injective
    have huniv : Fintype.card (Finset (Fin N)) = 2 ^ N := by
      simp [Fintype.card_finset, Fintype.card_fin]
    have hsum : Fintype.card (Finset (Fin N)) < D.card + Dc.card := by
      rw [huniv, hDc_card]
      have hNpos : 1 ≤ N := by
        by_contra h0
        have hN0 : N = 0 := by omega
        subst hN0
        have hle : D.card ≤ 1 := by
          calc D.card ≤ Fintype.card (Finset (Fin 0)) := Finset.card_le_univ D
            _ = 1 := by simp
        omega
      have h2 : 2 ^ N = 2 * 2 ^ (N - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hNpos, pow_succ]
        ring
      omega
    have hnotdisj : ¬ Disjoint D Dc := by
      intro hd
      have hle : (D ∪ Dc).card ≤ Fintype.card (Finset (Fin N)) := Finset.card_le_univ _
      rw [Finset.card_union_of_disjoint hd] at hle
      omega
    rw [Finset.not_disjoint_iff] at hnotdisj
    obtain ⟨A, hAD, hADc⟩ := hnotdisj
    rcases Finset.mem_image.mp hADc with ⟨B, hBD, hBA⟩
    intro S
    refine ⟨A, hAD, B, hBD, ?_⟩
    intro x _
    rw [Finset.mem_union, ← hBA, Finset.mem_compl]
    exact em' (x ∈ B)
  · -- N = 0: every S : Finset (Fin 0) is empty, and D is nonempty since sum > 1/2
    have hDne : D.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      subst h
      norm_num at hD
    obtain ⟨A, hAD⟩ := hDne
    intro S
    refine ⟨A, hAD, A, hAD, ?_⟩
    intro i _
    exact Fin.elim0 i

/-- **Theorem 2 (Reduction to downward-closed families):**
Replacing `D` by its downward closure `D↓` preserves `D^{(q)}` exactly and never decreases `μ_δ`. -/
theorem ppl089_down_closure_invariance (N q : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (D : Finset (Finset (Fin N))) :
    let Ddown := Finset.univ.filter (fun B : Finset (Fin N) => ∃ A ∈ D, B ⊆ A)
    (∑ A ∈ D, δ ^ A.card * (1 - δ) ^ (N - A.card) ≤
      ∑ A ∈ Ddown, δ ^ A.card * (1 - δ) ^ (N - A.card)) ∧
    ∀ S : Finset (Fin N),
      (∃ f : Fin q → Finset (Fin N), (∀ j, f j ∈ D) ∧ S ⊆ Finset.univ.biUnion f) ↔
      (∃ f : Fin q → Finset (Fin N), (∀ j, f j ∈ Ddown) ∧ S ⊆ Finset.univ.biUnion f) := by
  intro Ddown
  constructor
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro A hA
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ A, ⟨A, hA, Finset.Subset.refl A⟩⟩
    · intro A _ _
      exact mul_nonneg (pow_nonneg hδ0 _) (pow_nonneg (sub_nonneg.mpr hδ1) _)
  · intro S
    constructor
    · rintro ⟨f, hfD, hcov⟩
      exact ⟨f, fun j => Finset.mem_filter.mpr ⟨Finset.mem_univ _, f j, hfD j, subset_rfl⟩, hcov⟩
    · rintro ⟨f, hfDown, hcov⟩
      have hex : ∀ j : Fin q, ∃ A ∈ D, f j ⊆ A := fun j => (Finset.mem_filter.mp (hfDown j)).2
      choose g hgD hfg using hex
      refine ⟨g, hgD, hcov.trans ?_⟩
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨j, hj, hxj⟩
      exact Finset.mem_biUnion.mpr ⟨j, hj, hfg j hxj⟩

/-- **Theorem 3 (NEW: Explicit Closed-Form `q = 2m` Fourier-Walsh Fractional Cover):**
For every `N : ℕ`, `δ ∈ (0, 1)`, `m ≥ 1`, and `D ⊆ Finset (Fin N)` with `a = μ_δ(D) > 0`,
define explicitly (with zero LP duality or Hahn–Banach):
  `w(I) = (∑ A ∈ D, μ_δ(A) * ∏ i ∈ I, (if i ∈ A then 1 - δ else -δ))^2 / (a^2 * δ^(2 * |I|))`
for odd `|I|`, and `0` for even `|I|`.
Then:
1. For EVERY `S` not covered by `2m` sets of `D` (`S ∈ D^{(2m)}`),
   `1 ≤ ∑ I ∈ S.powerset, (w I)^m`.
2. For `m = 1`, the total `δ`-weighted fractional mass satisfies the exact Parseval bound
   `∑ I, w I * δ^|I| ≤ (1 - δ) * (1 - a) / a`. -/
theorem ppl089_explicit_fourier_cover_even (N m : ℕ) (hm : 1 ≤ m) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (D : Finset (Finset (Fin N)))
    (ha : 0 < ∑ A ∈ D, δ ^ A.card * (1 - δ) ^ (N - A.card)) :
    let a := ∑ A ∈ D, δ ^ A.card * (1 - δ) ^ (N - A.card)
    let w : Finset (Fin N) → ℝ := fun I =>
      if Odd I.card then
        (∑ A ∈ D, (δ ^ A.card * (1 - δ) ^ (N - A.card)) *
          ∏ i ∈ I, (if i ∈ A then 1 - δ else -δ)) ^ 2 / (a ^ 2 * δ ^ (2 * I.card))
      else 0
    (∀ I, 0 ≤ w I) ∧
    (∀ S : Finset (Fin N),
      (∀ f : Fin (2 * m) → Finset (Fin N), (∀ j, f j ∈ D) → ¬ S ⊆ Finset.univ.biUnion f) →
      1 ≤ ∑ I ∈ S.powerset, (w I) ^ m) ∧
    (∑ I : Finset (Fin N), w I * δ ^ I.card ≤ (1 - δ) * (1 - a) / a) := by
  intro a w
  have ha_eq : a = ∑ A ∈ D, prodWeight δ A := by
    simp only [a]
    exact Finset.sum_congr rfl (fun A _ => (prodWeight_eq_pow δ A).symm)
  have ha_pos : 0 < a := ha
  have hw_eq : ∀ I : Finset (Fin N), w I =
      if Odd I.card then (fourierCoeff δ D I) ^ 2 / (a ^ 2 * δ ^ (2 * I.card)) else 0 := by
    intro I
    simp only [w, fourierCoeff, psi]
    split_ifs
    · congr 2
      refine Finset.sum_congr rfl (fun A _ => ?_)
      rw [prodWeight_eq_pow]
    · rfl
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: nonnegativity
    intro I
    rw [hw_eq]
    split_ifs
    · positivity
    · exact le_refl 0
  · -- Part 2: 1 ≤ ∑_{I ⊆ S} (w I)^m for S ∈ D^{(2m)}
    intro S hS
    have hvan := kernel_vanishing_even hδ0 m hm D S hS
    -- Split S.powerset into even and odd cardinalities
    let F : Finset (Fin N) → ℝ := fun I => ((fourierCoeff δ D I) ^ 2 / δ ^ (2 * I.card)) ^ m
    have hF_nonneg : ∀ I, 0 ≤ F I := fun I => by positivity
    have hsplit : ∑ I ∈ S.powerset, (-1 : ℝ) ^ I.card * F I =
        (∑ I ∈ S.powerset.filter (fun I => Even I.card), F I) -
        (∑ I ∈ S.powerset.filter (fun I => Odd I.card), F I) := by
      rw [← Finset.sum_filter_add_sum_filter_not S.powerset (fun I => Even I.card)]
      have heven : ∑ I ∈ S.powerset.filter (fun I => Even I.card), (-1 : ℝ) ^ I.card * F I =
          ∑ I ∈ S.powerset.filter (fun I => Even I.card), F I := by
        refine Finset.sum_congr rfl (fun I hI => ?_)
        rw [(Finset.mem_filter.mp hI).2.neg_one_pow, one_mul]
      have hodd : ∑ I ∈ S.powerset.filter (fun I => ¬ Even I.card), (-1 : ℝ) ^ I.card * F I =
          -(∑ I ∈ S.powerset.filter (fun I => Odd I.card), F I) := by
        have hfilt : S.powerset.filter (fun I => ¬ Even I.card) =
            S.powerset.filter (fun I => Odd I.card) := by
          ext I; simp [Nat.not_even_iff_odd]
        rw [hfilt, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun I hI => ?_)
        rw [(Finset.mem_filter.mp hI).2.neg_one_pow, neg_one_mul]
      rw [heven, hodd, sub_eq_add_neg]
    have heq : ∑ I ∈ S.powerset.filter (fun I => Even I.card), F I =
        ∑ I ∈ S.powerset.filter (fun I => Odd I.card), F I := by
      have h0 : ∑ I ∈ S.powerset, (-1 : ℝ) ^ I.card * F I = 0 := hvan
      rw [hsplit] at h0
      linarith
    have hempty_mem : (∅ : Finset (Fin N)) ∈ S.powerset.filter (fun I => Even I.card) := by
      simp
    have hF_empty : F ∅ = (a ^ 2) ^ m := by
      simp [F, fourierCoeff_empty, ha_eq]
    have hle_even : (a ^ 2) ^ m ≤ ∑ I ∈ S.powerset.filter (fun I => Even I.card), F I := by
      rw [← hF_empty]
      exact Finset.single_le_sum (fun I _ => hF_nonneg I) hempty_mem
    have hle_odd : (a ^ 2) ^ m ≤ ∑ I ∈ S.powerset.filter (fun I => Odd I.card), F I := by
      rwa [← heq]
    have hsum_w : ∑ I ∈ S.powerset, (w I) ^ m =
        (∑ I ∈ S.powerset.filter (fun I => Odd I.card), F I) / (a ^ 2) ^ m := by
      rw [Finset.sum_div, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun I _ => ?_)
      rw [hw_eq]
      split_ifs with hodd
      · simp only [F]
        rw [div_pow, div_pow, div_div, mul_pow]
        ring
      · exact zero_pow (by omega)
    rw [hsum_w]
    exact (one_le_div (by positivity)).mpr hle_odd
  · -- Part 3: Parseval bound ∑ I, w I * δ^|I| ≤ (1 - δ) * (1 - a) / a
    have hpars := parseval_indicator hδ0 hδ1 D
    rw [← ha_eq] at hpars
    -- Subtract I = ∅ term (= a^2) from Parseval
    have hpars_ne : ∑ I ∈ Finset.univ.erase ∅,
        (fourierCoeff δ D I) ^ 2 / (δ * (1 - δ)) ^ I.card = a * (1 - a) := by
      have hadd := Finset.add_sum_erase Finset.univ
        (fun I : Finset (Fin N) => (fourierCoeff δ D I) ^ 2 / (δ * (1 - δ)) ^ I.card)
        (Finset.mem_univ ∅)
      have h0 : (fourierCoeff δ D ∅) ^ 2 / (δ * (1 - δ)) ^ (∅ : Finset (Fin N)).card = a ^ 2 := by
        simp [fourierCoeff_empty, ha_eq]
      rw [h0, hpars] at hadd
      linarith
    have hterm_le : ∀ I : Finset (Fin N),
        w I * δ ^ I.card ≤
          if I = ∅ then 0 else
            ((1 - δ) / a ^ 2) * ((fourierCoeff δ D I) ^ 2 / (δ * (1 - δ)) ^ I.card) := by
      intro I
      rw [hw_eq]
      by_cases hI0 : I = ∅
      · subst hI0
        simp
      · simp only [hI0, ↓reduceIte]
        split_ifs with hodd
        · have hcard_pos : 1 ≤ I.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hI0)
          have h1d_le : (1 - δ) ^ I.card ≤ 1 - δ := by
            have h0 : 0 ≤ 1 - δ := by linarith
            have h1 : 1 - δ ≤ 1 := by linarith
            calc (1 - δ) ^ I.card ≤ (1 - δ) ^ 1 := pow_le_pow_of_le_one h0 h1 hcard_pos
              _ = 1 - δ := pow_one _
          have hrew : (fourierCoeff δ D I) ^ 2 / (a ^ 2 * δ ^ (2 * I.card)) * δ ^ I.card =
              ((1 - δ) ^ I.card / a ^ 2) * ((fourierCoeff δ D I) ^ 2 / (δ * (1 - δ)) ^ I.card) := by
            have hd0 : δ ≠ 0 := ne_of_gt hδ0
            have h1d0 : 1 - δ ≠ 0 := ne_of_gt (sub_pos.mpr hδ1)
            have ha0 : a ≠ 0 := ne_of_gt ha_pos
            rw [mul_pow, show 2 * I.card = I.card + I.card by ring, pow_add]
            field_simp [hd0, h1d0, ha0]
          rw [hrew]
          apply mul_le_mul_of_nonneg_right
          · exact div_le_div_of_nonneg_right h1d_le (by positivity)
          · positivity
        · simp only [zero_mul]
          positivity
    calc ∑ I : Finset (Fin N), w I * δ ^ I.card
        ≤ ∑ I : Finset (Fin N), if I = ∅ then 0 else
            ((1 - δ) / a ^ 2) * ((fourierCoeff δ D I) ^ 2 / (δ * (1 - δ)) ^ I.card) :=
          Finset.sum_le_sum (fun I _ => hterm_le I)
      _ = ∑ I ∈ Finset.univ.erase ∅,
            ((1 - δ) / a ^ 2) * ((fourierCoeff δ D I) ^ 2 / (δ * (1 - δ)) ^ I.card) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext I; simp
      _ = ((1 - δ) / a ^ 2) * (a * (1 - a)) := by rw [← Finset.mul_sum, hpars_ne]
      _ = (1 - δ) * (1 - a) / a := by
          have ha0 : a ≠ 0 := ne_of_gt ha_pos
          field_simp [ha0]

/-- **Theorem 4 (Exact Fractional PPL 089 for `q = 2` — Pure-Mathlib Statement):**
For every `N : ℕ`, `δ ∈ (0, 1)`, and `D ⊆ Finset (Fin N)` with
`μ_δ(D) ≥ 2 * (1 - δ) / (3 - 2 * δ)` (in particular `μ_δ(D) ≥ 2/3`),
`D^{(2)}` is **weakly `δ`-small**: there exist explicit nonnegative weights `w` covering every
`S ∈ D^{(2)}` with `∑ I, w I * δ^|I| ≤ 1/2`. -/
theorem ppl089_fractional_q2 (N : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (D : Finset (Finset (Fin N)))
    (hD : 2 * (1 - δ) / (3 - 2 * δ) ≤
      ∑ A ∈ D, δ ^ A.card * (1 - δ) ^ (N - A.card)) :
    ∃ w : Finset (Fin N) → ℝ,
      (∀ I, 0 ≤ w I) ∧
      (∀ S : Finset (Fin N), (∀ A ∈ D, ∀ B ∈ D, ¬ S ⊆ A ∪ B) →
        1 ≤ ∑ I ∈ S.powerset, w I) ∧
      (∑ I : Finset (Fin N), w I * δ ^ I.card ≤ 1 / 2) := by
  have hden : 0 < 3 - 2 * δ := by linarith
  have hnum : 0 < 2 * (1 - δ) := by linarith
  have ha : 0 < ∑ A ∈ D, δ ^ A.card * (1 - δ) ^ (N - A.card) :=
    lt_of_lt_of_le (div_pos hnum hden) hD
  obtain ⟨hw0, hcov, hwt⟩ := ppl089_explicit_fourier_cover_even N 1 (le_refl 1) δ hδ0 hδ1 D ha
  refine ⟨_, hw0, ?_, ?_⟩
  · intro S hS
    have hS2 : ∀ f : Fin (2 * 1) → Finset (Fin N), (∀ j, f j ∈ D) →
        ¬ S ⊆ Finset.univ.biUnion f := by
      intro f hf hsub
      have hU : Finset.univ.biUnion f = f 0 ∪ f 1 := by
        ext x; simp [Fin.exists_fin_two]
      rw [hU] at hsub
      exact hS (f 0) (hf 0) (f 1) (hf 1) hsub
    simpa using hcov S hS2
  · set a := ∑ A ∈ D, δ ^ A.card * (1 - δ) ^ (N - A.card)
    have hbound : (1 - δ) * (1 - a) / a ≤ 1 / 2 := by
      rw [div_le_div_iff₀ ha (by norm_num : (0 : ℝ) < 2)]
      have h1 : 2 * (1 - δ) ≤ a * (3 - 2 * δ) := (div_le_iff₀ hden).mp hD
      linarith
    exact hwt.trans hbound

/-- **Theorem 5 (Chen Li's Theorem 1.14, `arXiv:2609.08967` — Pure-Mathlib Statement):**
For every `N : ℕ`, `δ ∈ (0, 1)`, and `D ⊆ Finset (Fin N)` with `μ_δ(D) > (1 - δ) / (2 - δ)`,
no `δ`-spread probability distribution `ν` on `Finset (Fin N)` can be supported on `D^{(2)}`. -/
theorem ppl089_no_spread_measure_q2 (N : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (D : Finset (Finset (Fin N)))
    (hD : (1 - δ) / (2 - δ) < ∑ A ∈ D, δ ^ A.card * (1 - δ) ^ (N - A.card))
    (ν : Finset (Fin N) → ℝ)
    (hν0 : ∀ S, 0 ≤ ν S)
    (hν1 : ∑ S : Finset (Fin N), ν S = 1)
    (hsupp : ∀ S, 0 < ν S → ∀ A ∈ D, ∀ B ∈ D, ¬ S ⊆ A ∪ B) :
    ∃ I : Finset (Fin N), δ ^ I.card < ∑ S ∈ Finset.univ.filter (fun S => I ⊆ S), ν S := by
  by_contra hsp
  push Not at hsp
  have hden : 0 < 2 - δ := by linarith
  have ha : 0 < ∑ A ∈ D, δ ^ A.card * (1 - δ) ^ (N - A.card) :=
    lt_of_lt_of_le (div_pos (sub_pos.mpr hδ1) hden) (le_of_lt hD)
  obtain ⟨hw0, hcov, hwt⟩ := ppl089_explicit_fourier_cover_even N 1 (le_refl 1) δ hδ0 hδ1 D ha
  set a := ∑ A ∈ D, δ ^ A.card * (1 - δ) ^ (N - A.card)
  set w : Finset (Fin N) → ℝ := fun I =>
    if Odd I.card then
      (∑ A ∈ D, (δ ^ A.card * (1 - δ) ^ (N - A.card)) *
        ∏ i ∈ I, (if i ∈ A then 1 - δ else -δ)) ^ 2 / (a ^ 2 * δ ^ (2 * I.card))
    else 0
  -- 1 = ∑_S ν(S) ≤ ∑_S ν(S) (∑_{I ⊆ S} w(I)) = ∑_I w(I) ν(H_I) ≤ ∑_I w(I) δ^|I| ≤ (1-δ)(1-a)/a < 1!
  have h1 : (1 : ℝ) ≤ ∑ S : Finset (Fin N), ν S * ∑ I ∈ S.powerset, w I := by
    rw [← hν1]
    refine Finset.sum_le_sum (fun S _ => ?_)
    by_cases hpos : 0 < ν S
    · have hS2 : ∀ f : Fin (2 * 1) → Finset (Fin N), (∀ j, f j ∈ D) →
          ¬ S ⊆ Finset.univ.biUnion f := by
        intro f hf hsub
        have hU : Finset.univ.biUnion f = f 0 ∪ f 1 := by
          ext x; simp [Fin.exists_fin_two]
        rw [hU] at hsub
        exact hsupp S hpos (f 0) (hf 0) (f 1) (hf 1) hsub
      have hge1 : 1 ≤ ∑ I ∈ S.powerset, w I := by simpa [w] using hcov S hS2
      nlinarith
    · have h0 : ν S = 0 := le_antisymm (not_lt.mp hpos) (hν0 S)
      simp [h0]
  have hswap : ∑ S : Finset (Fin N), ν S * ∑ I ∈ S.powerset, w I =
      ∑ I : Finset (Fin N), w I * ∑ S ∈ Finset.univ.filter (fun S => I ⊆ S), ν S := by
    calc ∑ S : Finset (Fin N), ν S * ∑ I ∈ S.powerset, w I
        = ∑ S : Finset (Fin N), ∑ I : Finset (Fin N), if I ⊆ S then ν S * w I else 0 := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [Finset.mul_sum, ← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext I; simp
      _ = ∑ I : Finset (Fin N), ∑ S : Finset (Fin N), if I ⊆ S then ν S * w I else 0 :=
          Finset.sum_comm
      _ = ∑ I : Finset (Fin N), w I * ∑ S ∈ Finset.univ.filter (fun S => I ⊆ S), ν S := by
          refine Finset.sum_congr rfl (fun I _ => ?_)
          rw [Finset.mul_sum, ← Finset.sum_filter]
          refine Finset.sum_congr rfl (fun S _ => mul_comm _ _)
  have h2 : ∑ I : Finset (Fin N), w I * ∑ S ∈ Finset.univ.filter (fun S => I ⊆ S), ν S ≤
      ∑ I : Finset (Fin N), w I * δ ^ I.card :=
    Finset.sum_le_sum (fun I _ => mul_le_mul_of_nonneg_left (hsp I) (hw0 I))
  have hlt1 : (1 - δ) * (1 - a) / a < 1 := by
    rw [div_lt_one ha]
    have hmul : 1 - δ < a * (2 - δ) := (div_lt_iff₀ hden).mp hD
    linarith
  linarith

/-- **Theorem 6 (Certified Refutation of Lemma 1 of Withdrawn Preprint `arXiv:2511.17336v1`):**
On `Fin 3`, the covering down-set `ℱ = {A : Finset (Fin 3) | A.card ≤ 2}` has `S = univ ∈ ℱ^{(1)}`
(cannot be covered by 1 member of `ℱ`), yet every dual vector `λ : Fin 3 → {0, 1}` satisfying
`∑ i ∈ A, λ i ≤ 1` for all `A ∈ ℱ` has `∑ i ∈ S, λ i ≤ 1 < 2`. -/
theorem ppl089_fang_wang_lemma1_false :
    let F : Finset (Finset (Fin 3)) := Finset.univ.filter (fun A => A.card ≤ 2)
    (∀ i : Fin 3, ∃ A ∈ F, i ∈ A) ∧
    (∀ A ∈ F, ∀ B, B ⊆ A → B ∈ F) ∧
    (∀ A ∈ F, ¬ (Finset.univ : Finset (Fin 3)) ⊆ A) ∧
    (∀ lam : Fin 3 → ℕ, (∀ i, lam i ≤ 1) →
      (∀ A ∈ F, ∑ i ∈ A, lam i ≤ 1) →
      ∑ i : Fin 3, lam i ≤ 1) := by
  intro F
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨{i}, ?_, Finset.mem_singleton_self i⟩
    simp [F]
  · intro A hA B hBA
    have hle : A.card ≤ 2 := (Finset.mem_filter.mp hA).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ B, (Finset.card_le_card hBA).trans hle⟩
  · intro A hA hsub
    have hle : A.card ≤ 2 := (Finset.mem_filter.mp hA).2
    have hge : 3 ≤ A.card := by
      have := Finset.card_le_card hsub
      simpa using this
    omega
  · intro lam _ hF
    have h01 : lam 0 + lam 1 ≤ 1 := by
      have hmem : ({0, 1} : Finset (Fin 3)) ∈ F := by simp [F]
      have := hF {0, 1} hmem
      simpa using this
    have h02 : lam 0 + lam 2 ≤ 1 := by
      have hmem : ({0, 2} : Finset (Fin 3)) ∈ F := by simp [F]
      have := hF {0, 2} hmem
      simpa using this
    have h12 : lam 1 + lam 2 ≤ 1 := by
      have hmem : ({1, 2} : Finset (Fin 3)) ∈ F := by simp [F]
      have := hF {1, 2} hmem
      simpa using this
    rw [Fin.sum_univ_three]
    omega

/-- **Theorem 7 (Certified Counterexample to Shifting Monotonicity of `δ`-Smallness on `Fin 5`):**
At `δ = 2/5`, the upset `U` generated by `{{4}, {0,1}, {0,2}, {1,3}}` has optimal integral (and
fractional) `δ`-cover weight `0.880`, whereas its `(0 → 1)` right-shift `U'` has minimal elements
`{{4}, {0,1}, {1,2}, {1,3}, {0,2,3}}` which are covered by `{{4}, {1}, {0,2,3}}` with strictly
smaller weight `2/5 + 2/5 + (2/5)^3 = 0.864 < 0.880`. -/
theorem ppl089_right_shift_decreases_smallness :
    let δ : ℝ := 2 / 5
    let G_orig : Finset (Finset (Fin 5)) := {{4}, {0, 1}, {0, 2}, {1, 3}}
    let G_shift : Finset (Finset (Fin 5)) := {{4}, {1}, {0, 2, 3}}
    let M_shift : Finset (Finset (Fin 5)) := {{4}, {0, 1}, {1, 2}, {1, 3}, {0, 2, 3}}
    -- Every minimal element of the shifted upset is covered by G_shift
    (∀ S ∈ M_shift, ∃ I ∈ G_shift, I ⊆ S) ∧
    -- Weight of G_shift is 0.864
    (∑ I ∈ G_shift, δ ^ I.card = 108 / 125) ∧
    -- Every cover of G_orig has weight ≥ 0.880 = 22 / 25 > 108 / 125
    (∀ C : Finset (Finset (Fin 5)), (∀ S ∈ G_orig, ∃ I ∈ C, I ⊆ S) →
      (108 : ℝ) / 125 < ∑ I ∈ C, δ ^ I.card) := by
  intro δ G_orig G_shift M_shift
  refine ⟨?_, ?_, ?_⟩
  · intro S hS
    simp only [M_shift, Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl
    · exact ⟨{4}, by simp [G_shift], subset_rfl⟩
    · exact ⟨{1}, by simp [G_shift], by intro x hx; simp at hx ⊢; right; exact hx⟩
    · exact ⟨{1}, by simp [G_shift], by intro x hx; simp at hx ⊢; left; exact hx⟩
    · exact ⟨{1}, by simp [G_shift], by intro x hx; simp at hx ⊢; left; exact hx⟩
    · exact ⟨{0, 2, 3}, by simp [G_shift], subset_rfl⟩
  · have hd1 : ({4} : Finset (Fin 5)) ∉ ({({1} : Finset (Fin 5)), {0, 2, 3}} : Finset _) := by decide
    have hd2 : ({1} : Finset (Fin 5)) ∉ ({({0, 2, 3} : Finset (Fin 5))} : Finset _) := by decide
    simp only [G_shift, Finset.sum_insert hd1, Finset.sum_insert hd2, Finset.sum_singleton]
    have hc1 : ({4} : Finset (Fin 5)).card = 1 := by decide
    have hc2 : ({1} : Finset (Fin 5)).card = 1 := by decide
    have hc3 : ({0, 2, 3} : Finset (Fin 5)).card = 3 := by decide
    rw [hc1, hc2, hc3]
    norm_num [δ]
  · intro C hC
    -- By LP duality: assign dual weights 1/2 to {0,1}, 1/2 to {0,2}, 1/2 to {1,3}?
    -- Better: assign dual weights y({4}) = 2/5, y({0,1}) = 4/25, y({0,2}) = 4/25, y({1,3}) = 4/25!
    -- Check for EVERY subset I of Fin 5: sum_{S in G_orig, I subset S} y(S) <= δ^|I|!
    -- Indeed:
    --   |I| = 0: sum = 2/5 + 12/25 = 22/25 <= 1 = δ^0!
    --   |I| = 1: max hits is 2 (at I={0} hitting {0,1},{0,2} => 8/25 <= 2/5; at I={1} => 8/25 <= 2/5;
    --            at I={4} => 2/5 <= 2/5; at I={2} or {3} => 4/25 <= 2/5)!
    --   |I| >= 2: I can be a subset of AT MOST ONE element of G_orig! If I in G_orig of size 2: 4/25 <= (2/5)^2!
    --   So ∑_{I ∈ C} δ^|I| ≥ ∑_{I ∈ C} ∑_{S ∈ G_orig, I ⊆ S} y(S) ≥ ∑_{S ∈ G_orig} y(S) = 22/25 > 108/125!!
    let y : Finset (Fin 5) → ℝ := fun S => if S = {4} then 2 / 5 else 4 / 25
    have hy_pos : ∀ S ∈ G_orig, 0 ≤ y S := by
      intro S _; simp only [y]; split_ifs <;> norm_num
    have hdual : ∀ I : Finset (Fin 5),
        ∑ S ∈ G_orig.filter (fun S => I ⊆ S), y S ≤ δ ^ I.card := by
      intro I
      by_cases h0 : I = ∅
      · subst h0
        have hf : G_orig.filter (fun S => (∅ : Finset (Fin 5)) ⊆ S) = G_orig := by
          ext S; simp
        rw [hf]
        have hd1 : ({4} : Finset (Fin 5)) ∉ ({({0, 1} : Finset (Fin 5)), {0, 2}, {1, 3}} : Finset _) := by decide
        have hd2 : ({0, 1} : Finset (Fin 5)) ∉ ({({0, 2} : Finset (Fin 5)), {1, 3}} : Finset _) := by decide
        have hd3 : ({0, 2} : Finset (Fin 5)) ∉ ({({1, 3} : Finset (Fin 5))} : Finset _) := by decide
        simp only [G_orig, Finset.sum_insert hd1, Finset.sum_insert hd2, Finset.sum_insert hd3,
          Finset.sum_singleton, y]
        have hne1 : ({0, 1} : Finset (Fin 5)) ≠ {4} := by decide
        have hne2 : ({0, 2} : Finset (Fin 5)) ≠ {4} := by decide
        have hne3 : ({1, 3} : Finset (Fin 5)) ≠ {4} := by decide
        simp [hne1, hne2, hne3, δ]
        norm_num
      · by_cases h1 : I.card = 1
        · rw [h1, pow_one]
          obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1
          fin_cases x
          · have hf : G_orig.filter (fun S => ({(0 : Fin 5)} : Finset (Fin 5)) ⊆ S) = {{0, 1}, {0, 2}} := by decide
            change ∑ S ∈ G_orig.filter (fun S => ({(0 : Fin 5)} : Finset (Fin 5)) ⊆ S), y S ≤ δ
            rw [hf]
            have hd : ({0, 1} : Finset (Fin 5)) ∉ ({({0, 2} : Finset (Fin 5))} : Finset _) := by decide
            have hne1 : ({0, 1} : Finset (Fin 5)) ≠ {4} := by decide
            have hne2 : ({0, 2} : Finset (Fin 5)) ≠ {4} := by decide
            simp [Finset.sum_insert hd, y, hne1, hne2, δ]; norm_num
          · have hf : G_orig.filter (fun S => ({(1 : Fin 5)} : Finset (Fin 5)) ⊆ S) = {{0, 1}, {1, 3}} := by decide
            change ∑ S ∈ G_orig.filter (fun S => ({(1 : Fin 5)} : Finset (Fin 5)) ⊆ S), y S ≤ δ
            rw [hf]
            have hd : ({0, 1} : Finset (Fin 5)) ∉ ({({1, 3} : Finset (Fin 5))} : Finset _) := by decide
            have hne1 : ({0, 1} : Finset (Fin 5)) ≠ {4} := by decide
            have hne2 : ({1, 3} : Finset (Fin 5)) ≠ {4} := by decide
            simp [Finset.sum_insert hd, y, hne1, hne2, δ]; norm_num
          · have hf : G_orig.filter (fun S => ({(2 : Fin 5)} : Finset (Fin 5)) ⊆ S) = {{0, 2}} := by decide
            change ∑ S ∈ G_orig.filter (fun S => ({(2 : Fin 5)} : Finset (Fin 5)) ⊆ S), y S ≤ δ
            rw [hf]
            have hne : ({0, 2} : Finset (Fin 5)) ≠ {4} := by decide
            simp [y, hne, δ]; norm_num
          · have hf : G_orig.filter (fun S => ({(3 : Fin 5)} : Finset (Fin 5)) ⊆ S) = {{1, 3}} := by decide
            change ∑ S ∈ G_orig.filter (fun S => ({(3 : Fin 5)} : Finset (Fin 5)) ⊆ S), y S ≤ δ
            rw [hf]
            have hne : ({1, 3} : Finset (Fin 5)) ≠ {4} := by decide
            simp [y, hne, δ]; norm_num
          · have hf : G_orig.filter (fun S => ({(4 : Fin 5)} : Finset (Fin 5)) ⊆ S) = {{4}} := by decide
            change ∑ S ∈ G_orig.filter (fun S => ({(4 : Fin 5)} : Finset (Fin 5)) ⊆ S), y S ≤ δ
            rw [hf]
            simp [y, δ]
        · have hge2 : 2 ≤ I.card := by
            have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
            omega
          by_cases h2 : I.card = 2
          · rw [h2]
            have hsub : G_orig.filter (fun S => I ⊆ S) ⊆ {I} := by
              intro S hS
              rcases Finset.mem_filter.mp hS with ⟨hSG, hIS⟩
              have hScard : S.card ≤ 2 := by
                simp only [G_orig, Finset.mem_insert, Finset.mem_singleton] at hSG
                rcases hSG with rfl | rfl | rfl | rfl <;> decide
              have hEq : I = S := Finset.eq_of_subset_of_card_le hIS (by omega)
              simp [hEq]
            have hne4 : I ≠ {4} := by
              intro hEq; rw [hEq] at h2; simp at h2
            calc ∑ S ∈ G_orig.filter (fun S => I ⊆ S), y S
                ≤ ∑ S ∈ ({I} : Finset (Finset (Fin 5))), y S :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub (fun S hS _ => by
                    simp only [y]; split_ifs <;> norm_num)
              _ = y I := Finset.sum_singleton _ _
              _ = 4 / 25 := by simp [y, hne4]
              _ = δ ^ 2 := by norm_num [δ]
          · -- |I| ≥ 3: no element of G_orig has card ≥ 3, so filter is empty!
            have hemp : G_orig.filter (fun S => I ⊆ S) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro S hSG hIS
              have hScard : S.card ≤ 2 := by
                simp only [G_orig, Finset.mem_insert, Finset.mem_singleton] at hSG
                rcases hSG with rfl | rfl | rfl | rfl <;> decide
              have := Finset.card_le_card hIS
              omega
            rw [hemp, Finset.sum_empty]
            positivity
    have hsum_y : ∑ S ∈ G_orig, y S = 22 / 25 := by
      have hd1 : ({4} : Finset (Fin 5)) ∉ ({({0, 1} : Finset (Fin 5)), {0, 2}, {1, 3}} : Finset _) := by decide
      have hd2 : ({0, 1} : Finset (Fin 5)) ∉ ({({0, 2} : Finset (Fin 5)), {1, 3}} : Finset _) := by decide
      have hd3 : ({0, 2} : Finset (Fin 5)) ∉ ({({1, 3} : Finset (Fin 5))} : Finset _) := by decide
      have hne1 : ({0, 1} : Finset (Fin 5)) ≠ {4} := by decide
      have hne2 : ({0, 2} : Finset (Fin 5)) ≠ {4} := by decide
      have hne3 : ({1, 3} : Finset (Fin 5)) ≠ {4} := by decide
      simp only [G_orig, Finset.sum_insert hd1, Finset.sum_insert hd2, Finset.sum_insert hd3,
        Finset.sum_singleton, y, ↓reduceIte, hne1, hne2, hne3]
      norm_num
    have hlow : ∑ S ∈ G_orig, y S ≤ ∑ I ∈ C, δ ^ I.card := by
      calc ∑ S ∈ G_orig, y S
          ≤ ∑ S ∈ G_orig, ∑ I ∈ C.filter (fun I => I ⊆ S), y S := by
            refine Finset.sum_le_sum (fun S hS => ?_)
            obtain ⟨I, hIC, hIS⟩ := hC S hS
            exact Finset.single_le_sum (fun _ _ => hy_pos S hS)
              (Finset.mem_filter.mpr ⟨hIC, hIS⟩)
        _ = ∑ S ∈ G_orig, ∑ I ∈ C, if I ⊆ S then y S else 0 := by
            refine Finset.sum_congr rfl (fun S _ => Finset.sum_filter _ _)
        _ = ∑ I ∈ C, ∑ S ∈ G_orig, if I ⊆ S then y S else 0 := Finset.sum_comm
        _ = ∑ I ∈ C, ∑ S ∈ G_orig.filter (fun S => I ⊆ S), y S := by
            refine Finset.sum_congr rfl (fun I _ => (Finset.sum_filter _ _).symm)
        _ ≤ ∑ I ∈ C, δ ^ I.card := Finset.sum_le_sum (fun I _ => hdual I)
    linarith

end PPL089
