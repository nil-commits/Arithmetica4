/-
Copyright (c) 2026 Arithmetica4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Arithmetica4 Tier A Extension: Discrete Information Theory, Shearer's Entropy Lemma & Classical Coding Theory

A 100% self-contained, targeted-import Tier A Lean 4 formalization covering:
1. **Discrete Shannon Entropy, Conditional Entropy, Mutual Information, Gibbs & Pinsker's Inequality:**
   - `IsProbDist`, `shannonEntropy`, `marginalLeft`, `marginalRight`, `condEntropy`, `mutualInfo`,
     `klDiv`, `tvDist`
   - `shannonEntropy_nonneg`, `shannonEntropy_le_log_card`, `shannonEntropy_uniform`
   - `gibbs_inequality`, `log_sum_inequality`, `pinsker_inequality` (`2 * TV(P, Q)^2 ≤ D_KL(P ‖ Q)`)
   - `shannonEntropy_chain_rule` (`H(X, Y) = H(X) + H(Y | X)`),
     `mutualInfo_eq_klDiv`, `condEntropy_le_marginalRight` (`H(Y | X) ≤ H(Y)`),
     `shannonEntropy_subadditive`, `condEntropy_pair_le` (`H(Z | X, Y) ≤ H(Z | X)`)
2. **Shearer's Entropy Lemma, Han's Inequality & Bollobás–Thomason / Loomis–Whitney Projections:**
   - `restrictTuple`, `projDist`, `condCoordEntropy`
   - `shannonEntropy_projDist_chain_rule`, `condCoordEntropy_antitone`, `condCoordEntropy_nonneg`
   - `shearer_entropy_lemma`, `hans_inequality`, `shearer_projection_card`,
     `loomis_whitney_inequality`
3. **Kraft–McMillan Inequality, Kraft Converse, Shannon Source Coding & Binary Entropy Tail Bounds:**
   - `IsPrefixFree`, `IsUniquelyDecodable`, `isUniquelyDecodable_of_isPrefixFree`
   - `kraft_mcmillan_inequality`, `kraft_mcmillan_binary`, `kraft_prefix_free`,
     `kraft_exists_prefix_free`, `shannon_source_coding_lower_bound`
   - `binEntropyNat`, `binEntropy2`, `sum_choose_le_two_rpow_binEntropy2`,
     `choose_le_two_rpow_binEntropy2`
4. **Classical Coding-Theory Bounds & General `F_p` MacWilliams Weight-Enumerator Identity:**
   - `hammingDist`, `hammingWeight`, `hammingBall`, `card_hammingBall`
   - `singleton_bound`, `hamming_sphere_packing_bound`, `gilbert_varshamov_bound`,
     `plotkin_bound`, `plotkin_bound_binary`
   - `dualCode`, `weightEnum`, `card_mul_card_dualCode`, `macwilliams_identity`,
     `macwilliams_identity_binary`
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

namespace Arith4Ext.EntropyCoding

open scoped BigOperators Classical

noncomputable section

/-! ## Section 1: Discrete Shannon Entropy, Conditional Entropy, KL Divergence & Pinsker -/

section DiscreteEntropy

/-- A discrete probability distribution on a finite type `α`. -/
def IsProbDist {α : Type*} [Fintype α] (P : α → ℝ) : Prop :=
  (∀ x : α, 0 ≤ P x) ∧ ∑ x : α, P x = 1

/-- Discrete Shannon entropy (in nats): `H(P) = ∑ x, -(P x * log (P x))`.
Since `Real.log 0 = 0`, zero-probability atoms contribute `0` automatically. -/
def shannonEntropy {α : Type*} [Fintype α] (P : α → ℝ) : ℝ :=
  ∑ x : α, -(P x * Real.log (P x))

/-- Kullback–Leibler divergence (in nats): `D_KL(P ‖ Q) = ∑ x, P x * log (P x / Q x)`. -/
def klDiv {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ :=
  ∑ x : α, P x * Real.log (P x / Q x)

/-- Total variation distance: `TV(P, Q) = (1 / 2) * ∑ x, |P x - Q x|`. -/
def tvDist {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ :=
  (1 / 2) * ∑ x : α, |P x - Q x|

/-- Left marginal of a joint distribution `P : α × β → ℝ`. -/
def marginalLeft {α β : Type*} [Fintype β] (P : α × β → ℝ) (x : α) : ℝ :=
  ∑ y : β, P (x, y)

/-- Right marginal of a joint distribution `P : α × β → ℝ`. -/
def marginalRight {α β : Type*} [Fintype α] (P : α × β → ℝ) (y : β) : ℝ :=
  ∑ x : α, P (x, y)

/-- Conditional Shannon entropy `H(Y | X)` of a joint distribution `P : α × β → ℝ`. -/
def condEntropy {α β : Type*} [Fintype α] [Fintype β] (P : α × β → ℝ) : ℝ :=
  ∑ x : α, ∑ y : β, -(P (x, y) * Real.log (P (x, y) / marginalLeft P x))

/-- Mutual information `I(X; Y) = H(X) + H(Y) - H(X, Y)` of a joint distribution `P : α × β → ℝ`. -/
def mutualInfo {α β : Type*} [Fintype α] [Fintype β] (P : α × β → ℝ) : ℝ :=
  shannonEntropy (marginalLeft P) + shannonEntropy (marginalRight P) - shannonEntropy P

lemma isProbDist_le_one {α : Type*} [Fintype α] {P : α → ℝ} (hP : IsProbDist P) (x : α) :
    P x ≤ 1 := by
  calc P x ≤ ∑ y : α, P y := Finset.single_le_sum (fun y _ => hP.1 y) (Finset.mem_univ x)
    _ = 1 := hP.2

lemma isProbDist_card_pos {α : Type*} [Fintype α] {P : α → ℝ} (hP : IsProbDist P) :
    0 < Fintype.card α := by
  by_contra h
  have h0 : Fintype.card α = 0 := by omega
  have : IsEmpty α := Fintype.card_eq_zero_iff.mp h0
  have hsum : ∑ x : α, P x = 0 := by simp
  linarith [hP.2]

lemma isProbDist_marginalLeft {α β : Type*} [Fintype α] [Fintype β] {P : α × β → ℝ}
    (hP : IsProbDist P) : IsProbDist (marginalLeft P) := by
  refine ⟨fun x => Finset.sum_nonneg fun y _ => hP.1 (x, y), ?_⟩
  simpa [marginalLeft, Fintype.sum_prod_type] using hP.2

lemma isProbDist_marginalRight {α β : Type*} [Fintype α] [Fintype β] {P : α × β → ℝ}
    (hP : IsProbDist P) : IsProbDist (marginalRight P) := by
  refine ⟨fun y => Finset.sum_nonneg fun x _ => hP.1 (x, y), ?_⟩
  simpa [marginalRight, Fintype.sum_prod_type_right] using hP.2

lemma isProbDist_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    {P : β → ℝ} (hP : IsProbDist P) : IsProbDist (P ∘ e) := by
  refine ⟨fun x => hP.1 (e x), ?_⟩
  simpa [Function.comp] using (Equiv.sum_comp e P).trans hP.2

lemma shannonEntropy_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (P : β → ℝ) :
    shannonEntropy (P ∘ e) = shannonEntropy P := by
  unfold shannonEntropy
  exact Equiv.sum_comp e (fun y => -(P y * Real.log (P y)))

/-- Non-negativity of Shannon entropy: `0 ≤ H(P)` for every probability distribution `P`. -/
theorem shannonEntropy_nonneg {α : Type*} [Fintype α] {P : α → ℝ} (hP : IsProbDist P) :
    0 ≤ shannonEntropy P := by
  apply Finset.sum_nonneg
  intro x _
  by_cases hx : P x = 0
  · simp [hx]
  · have hpos : 0 < P x := lt_of_le_of_ne (hP.1 x) (Ne.symm hx)
    have hlog : Real.log (P x) ≤ 0 := Real.log_nonpos hpos.le (isProbDist_le_one hP x)
    nlinarith

/-- Shannon entropy of the uniform distribution on a nonempty `Fintype α` equals `log |α|`. -/
theorem shannonEntropy_uniform {α : Type*} [Fintype α] [Nonempty α] :
    shannonEntropy (fun _ : α => (1 : ℝ) / (Fintype.card α : ℝ)) = Real.log (Fintype.card α : ℝ) := by
  have hpos : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos (α := α)
  unfold shannonEntropy
  simp only [one_div, Real.log_inv, mul_neg, neg_neg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hpos.ne']

/-- **Elementary Log-Sum Inequality (on any finite set `S`):**
For nonnegative `a, b : α → ℝ` with `∀ x ∈ S, a x ≠ 0 → 0 < b x`,
`(∑ x ∈ S, a x) * log ((∑ x ∈ S, a x) / (∑ x ∈ S, b x)) ≤ ∑ x ∈ S, a x * log (a x / b x)`. -/
theorem log_sum_inequality {α : Type*} (S : Finset α) (a b : α → ℝ)
    (ha : ∀ x ∈ S, 0 ≤ a x) (hb : ∀ x ∈ S, 0 ≤ b x)
    (hab : ∀ x ∈ S, a x ≠ 0 → 0 < b x) :
    (∑ x ∈ S, a x) * Real.log ((∑ x ∈ S, a x) / (∑ x ∈ S, b x)) ≤
      ∑ x ∈ S, a x * Real.log (a x / b x) := by
  set A : ℝ := ∑ x ∈ S, a x
  set B : ℝ := ∑ x ∈ S, b x
  have hA_nn : 0 ≤ A := Finset.sum_nonneg ha
  have hB_nn : 0 ≤ B := Finset.sum_nonneg hb
  by_cases hA0 : A = 0
  · have ha0 : ∀ x ∈ S, a x = 0 := (Finset.sum_eq_zero_iff_of_nonneg ha).mp hA0
    have hRHS : ∑ x ∈ S, a x * Real.log (a x / b x) = 0 :=
      Finset.sum_eq_zero fun x hx => by simp [ha0 x hx]
    simp [hA0, hRHS]
  · have hA_pos : 0 < A := lt_of_le_of_ne hA_nn (Ne.symm hA0)
    have hB_pos : 0 < B := by
      have hex : ∃ x ∈ S, a x ≠ 0 := by
        by_contra h
        push Not at h
        exact hA0 (Finset.sum_eq_zero h)
      rcases hex with ⟨x₀, hx₀, ha₀⟩
      exact lt_of_lt_of_le (hab x₀ hx₀ ha₀) (Finset.single_le_sum hb hx₀)
    -- Pointwise: `a x * (A / B) - b x * (A / B)` via `log t ≤ t - 1`
    have hpt : ∀ x ∈ S, (A / B) * (a x * (B / A) - b x) ≤
        a x * Real.log (a x / b x) - a x * Real.log (A / B) := by
      intro x hx
      by_cases hax : a x = 0
      · simp only [hax, zero_mul, zero_sub, sub_zero]
        have h1 : 0 ≤ (A / B) * b x := mul_nonneg (div_nonneg hA_pos.le hB_pos.le) (hb x hx)
        linarith
      · have hax_pos : 0 < a x := lt_of_le_of_ne (ha x hx) (Ne.symm hax)
        have hbx_pos : 0 < b x := hab x hx hax
        have ht_pos : 0 < (b x * A) / (a x * B) := by positivity
        have hlog := Real.log_le_sub_one_of_pos ht_pos
        have hlog_eq : Real.log ((b x * A) / (a x * B)) =
            Real.log (A / B) - Real.log (a x / b x) := by
          rw [Real.log_div (by positivity) (by positivity),
              Real.log_mul hbx_pos.ne' hA_pos.ne', Real.log_mul hax_pos.ne' hB_pos.ne',
              Real.log_div hA_pos.ne' hB_pos.ne', Real.log_div hax_pos.ne' hbx_pos.ne']
          ring
        rw [hlog_eq] at hlog
        have hmul := mul_le_mul_of_nonneg_left hlog hax_pos.le
        have hsimp : a x * ((b x * A) / (a x * B) - 1) = (A / B) * b x - a x := by
          field_simp [hax_pos.ne', hB_pos.ne']
        have hLHS_eq : (A / B) * (a x * (B / A) - b x) = a x - (A / B) * b x := by
          field_simp [hA_pos.ne', hB_pos.ne']
        linarith
    have hsum := Finset.sum_le_sum hpt
    have hLHS_zero : ∑ x ∈ S, (A / B) * (a x * (B / A) - b x) = 0 := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]
      change (A / B) * (A * (B / A) - B) = 0
      field_simp [hA_pos.ne', hB_pos.ne']
      ring
    rw [hLHS_zero, Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
    linarith

/-- **Gibbs' Inequality (`D_KL(P ‖ Q) ≥ 0`):**
For discrete probability distributions `P, Q` with `P ≪ Q`, the KL divergence is nonnegative. -/
theorem gibbs_inequality {α : Type*} [Fintype α] {P Q : α → ℝ}
    (hP : IsProbDist P) (hQ : IsProbDist Q) (hac : ∀ x : α, P x ≠ 0 → 0 < Q x) :
    0 ≤ klDiv P Q := by
  have h := log_sum_inequality Finset.univ P Q (fun x _ => hP.1 x) (fun x _ => hQ.1 x)
    (fun x _ hx => hac x hx)
  rw [hP.2, hQ.2, div_one, Real.log_one, mul_zero] at h
  exact h

/-- **Maximum Entropy Bound:** `H(P) ≤ log |α|` for every probability distribution `P` on `α`. -/
theorem shannonEntropy_le_log_card {α : Type*} [Fintype α] {P : α → ℝ} (hP : IsProbDist P) :
    shannonEntropy P ≤ Real.log (Fintype.card α : ℝ) := by
  have hcard_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast isProbDist_card_pos hP
  let U : α → ℝ := fun _ => 1 / (Fintype.card α : ℝ)
  have hU : IsProbDist U := by
    refine ⟨fun _ => by positivity, ?_⟩
    simp only [U, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hcard_pos.ne']
  have hkl : 0 ≤ klDiv P U := gibbs_inequality hP hU (fun _ _ => by positivity)
  have hkl_eq : klDiv P U = Real.log (Fintype.card α : ℝ) - shannonEntropy P := by
    unfold klDiv shannonEntropy U
    have hterm : ∀ x : α, P x * Real.log (P x / (1 / (Fintype.card α : ℝ))) =
        P x * Real.log (Fintype.card α : ℝ) - (-(P x * Real.log (P x))) := by
      intro x
      by_cases hx : P x = 0
      · simp [hx]
      · have hpx : 0 < P x := lt_of_le_of_ne (hP.1 x) (Ne.symm hx)
        rw [div_div_eq_mul_div, div_one, Real.log_mul hpx.ne' hcard_pos.ne']
        ring
    simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, hP.2, one_mul]
  linarith

/-- Binary Pinsker inequality for `0 < q ≤ p < 1`:
`2 * (p - q)^2 ≤ p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))`. -/
private lemma binary_pinsker_interior {p q : ℝ} (hq0 : 0 < q) (hqp : q ≤ p) (hp1 : p < 1) :
    2 * (p - q) ^ 2 ≤ p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  have hp0 : 0 < p := lt_of_lt_of_le hq0 hqp
  have h1p : 0 < 1 - p := by linarith
  have h1q : 0 < 1 - q := by linarith
  let f : ℝ → ℝ := fun t =>
    p * (Real.log p - Real.log t) + (1 - p) * (Real.log (1 - p) - Real.log (1 - t)) -
      2 * (p - t) ^ 2
  have hderiv : ∀ t ∈ Set.Icc q p,
      HasDerivAt f (-(p - t) * (2 * t - 1) ^ 2 / (t * (1 - t))) t := by
    intro t ⟨hqt, htp⟩
    have ht0 : 0 < t := lt_of_lt_of_le hq0 hqt
    have h1t : 0 < 1 - t := by linarith
    have h1 : HasDerivAt (fun t : ℝ => Real.log p - Real.log t) (0 - t⁻¹) t :=
      (hasDerivAt_const t (Real.log p)).sub (Real.hasDerivAt_log ht0.ne')
    have h2 : HasDerivAt (fun t : ℝ => Real.log (1 - p) - Real.log (1 - t)) (0 - (0 - 1) / (1 - t)) t := by
      have hsub : HasDerivAt (fun t : ℝ => 1 - t) (0 - 1) t :=
        (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
      exact (hasDerivAt_const t (Real.log (1 - p))).sub (hsub.log h1t.ne')
    have h3 : HasDerivAt (fun t : ℝ => (p - t) ^ 2) (2 * (p - t) ^ 1 * (0 - 1)) t := by
      have hsub : HasDerivAt (fun t : ℝ => p - t) (0 - 1) t :=
        (hasDerivAt_const t p).sub (hasDerivAt_id t)
      exact hsub.pow 2
    have hval : p * (0 - t⁻¹) + (1 - p) * (0 - (0 - 1) / (1 - t)) - 2 * (2 * (p - t) ^ 1 * (0 - 1)) =
        -(p - t) * (2 * t - 1) ^ 2 / (t * (1 - t)) := by
      field_simp [ht0.ne', h1t.ne']
      ring
    rw [← hval]
    exact ((h1.const_mul p).add (h2.const_mul (1 - p))).sub (h3.const_mul 2)
  have hanti : AntitoneOn f (Set.Icc q p) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc q p)
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have htIcc : t ∈ Set.Icc q p := interior_subset ht
      rw [(hderiv t htIcc).deriv]
      have ht0 : 0 < t := lt_of_lt_of_le hq0 htIcc.1
      have h1t : 0 < 1 - t := by linarith [htIcc.2]
      have hnum : 0 ≤ (p - t) * (2 * t - 1) ^ 2 := mul_nonneg (by linarith [htIcc.2]) (sq_nonneg _)
      have hden : 0 < t * (1 - t) := mul_pos ht0 h1t
      have : 0 ≤ (p - t) * (2 * t - 1) ^ 2 / (t * (1 - t)) := div_nonneg hnum hden.le
      rw [neg_mul, neg_div]
      linarith
  have hfp : f p = 0 := by simp [f]
  have hfq_ge : f p ≤ f q := hanti ⟨le_rfl, hqp⟩ ⟨hqp, le_rfl⟩ hqp
  rw [hfp] at hfq_ge
  have hfq_eq : f q = p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) - 2 * (p - q) ^ 2 := by
    simp only [f]
    rw [Real.log_div hp0.ne' hq0.ne', Real.log_div h1p.ne' h1q.ne']
  linarith

/-- Binary Pinsker boundary case `p = 1, 0 < q ≤ 1`: `2 * (1 - q)^2 ≤ -log q`. -/
private lemma binary_pinsker_one {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    2 * (1 - q) ^ 2 ≤ -Real.log q := by
  let g : ℝ → ℝ := fun t => -Real.log t - 2 * (1 - t) ^ 2
  have hderiv : ∀ t ∈ Set.Icc q 1, HasDerivAt g (-(2 * t - 1) ^ 2 / t) t := by
    intro t ⟨hqt, _⟩
    have ht0 : 0 < t := lt_of_lt_of_le hq0 hqt
    have h1 : HasDerivAt (fun t : ℝ => -Real.log t) (-(t⁻¹)) t := (Real.hasDerivAt_log ht0.ne').neg
    have h2 : HasDerivAt (fun t : ℝ => (1 - t) ^ 2) (2 * (1 - t) ^ 1 * (0 - 1)) t := by
      have hsub : HasDerivAt (fun t : ℝ => 1 - t) (0 - 1) t :=
        (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
      exact hsub.pow 2
    have hval : -t⁻¹ - 2 * (2 * (1 - t) ^ 1 * (0 - 1)) = -(2 * t - 1) ^ 2 / t := by
      field_simp [ht0.ne']
      ring
    rw [← hval]
    exact h1.sub (h2.const_mul 2)
  have hanti : AntitoneOn g (Set.Icc q 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc q 1)
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have htIcc : t ∈ Set.Icc q 1 := interior_subset ht
      rw [(hderiv t htIcc).deriv]
      have ht0 : 0 < t := lt_of_lt_of_le hq0 htIcc.1
      have : 0 ≤ (2 * t - 1) ^ 2 / t := div_nonneg (sq_nonneg _) ht0.le
      rw [neg_div]
      linarith
  have hg1 : g 1 = 0 := by simp [g]
  have hgq : g 1 ≤ g q := hanti ⟨le_rfl, hq1⟩ ⟨hq1, le_rfl⟩ hq1
  rw [hg1] at hgq
  dsimp only [g] at hgq
  linarith

/-- **Pinsker's Inequality:**
For any discrete probability distributions `P, Q` on a finite type `α` with `P ≪ Q`,
`2 * TV(P, Q)^2 ≤ D_KL(P ‖ Q)`. -/
theorem pinsker_inequality {α : Type*} [Fintype α] {P Q : α → ℝ}
    (hP : IsProbDist P) (hQ : IsProbDist Q) (hac : ∀ x : α, P x ≠ 0 → 0 < Q x) :
    2 * (tvDist P Q) ^ 2 ≤ klDiv P Q := by
  let A : Finset α := Finset.univ.filter (fun x => Q x ≤ P x)
  let p : ℝ := ∑ x ∈ A, P x
  let q : ℝ := ∑ x ∈ A, Q x
  have hP_compl : ∑ x ∈ Aᶜ, P x = 1 - p := by
    have hsum : ∑ x ∈ A, P x + ∑ x ∈ Aᶜ, P x = ∑ x : α, P x := Finset.sum_add_sum_compl A P
    linarith [hP.2]
  have hQ_compl : ∑ x ∈ Aᶜ, Q x = 1 - q := by
    have hsum : ∑ x ∈ A, Q x + ∑ x ∈ Aᶜ, Q x = ∑ x : α, Q x := Finset.sum_add_sum_compl A Q
    linarith [hQ.2]
  have htv_eq : tvDist P Q = p - q := by
    unfold tvDist
    have hsplit : ∑ x : α, |P x - Q x| =
        (∑ x ∈ A, |P x - Q x|) + (∑ x ∈ Aᶜ, |P x - Q x|) :=
      (Finset.sum_add_sum_compl A (fun x => |P x - Q x|)).symm
    have hA_eq : ∑ x ∈ A, |P x - Q x| = p - q := by
      have : ∀ x ∈ A, |P x - Q x| = P x - Q x := fun x hx =>
        abs_of_nonneg (sub_nonneg.mpr (Finset.mem_filter.mp hx).2)
      rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
    have hAc_eq : ∑ x ∈ Aᶜ, |P x - Q x| = (1 - q) - (1 - p) := by
      have : ∀ x ∈ Aᶜ, |P x - Q x| = Q x - P x := by
        intro x hx
        have hlt : P x < Q x := not_le.mp (fun hle =>
          (Finset.mem_compl.mp hx) (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hle⟩))
        rw [abs_of_neg (sub_neg.mpr hlt), neg_sub]
      rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, hP_compl, hQ_compl]
    rw [hsplit, hA_eq, hAc_eq]
    ring
  -- Log-sum inequality on `A` and `Aᶜ` reduces `klDiv P Q` to binary KL divergence
  have hlsA := log_sum_inequality A P Q (fun x _ => hP.1 x) (fun x _ => hQ.1 x)
    (fun x _ hx => hac x hx)
  have hlsAc := log_sum_inequality Aᶜ P Q (fun x _ => hP.1 x) (fun x _ => hQ.1 x)
    (fun x _ hx => hac x hx)
  rw [hP_compl, hQ_compl] at hlsAc
  have hkl_ge : p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤ klDiv P Q := by
    unfold klDiv
    rw [← Finset.sum_add_sum_compl A (fun x => P x * Real.log (P x / Q x))]
    exact add_le_add hlsA hlsAc
  rw [htv_eq]
  -- Now establish `2 * (p - q)^2 ≤ p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))`
  have hqp : q ≤ p := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
  have hq_nn : 0 ≤ q := Finset.sum_nonneg fun x _ => hQ.1 x
  have hp_le1 : p ≤ 1 := by
    have : 0 ≤ 1 - p := hP_compl ▸ Finset.sum_nonneg fun x _ => hP.1 x
    linarith
  by_cases hp0 : p = 0
  · have hq0 : q = 0 := by linarith
    simp only [hp0, hq0, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero]
    exact gibbs_inequality hP hQ hac
  · have hp_pos : 0 < p := lt_of_le_of_ne (hq_nn.trans hqp) (Ne.symm hp0)
    have hq_pos : 0 < q := by
      have hex : ∃ x ∈ A, P x ≠ 0 := by
        by_contra h
        push Not at h
        exact hp0 (Finset.sum_eq_zero h)
      rcases hex with ⟨x₀, hx₀, hPx₀⟩
      exact lt_of_lt_of_le (hac x₀ hPx₀) (Finset.single_le_sum (fun x _ => hQ.1 x) hx₀)
    by_cases hp1 : p = 1
    · have hq1 : q ≤ 1 := hp1 ▸ hqp
      have hbin := binary_pinsker_one hq_pos hq1
      have hterm : p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) = -Real.log q := by
        rw [hp1]; simp [one_div, Real.log_inv]
      rw [hp1]
      linarith
    · have hp_lt1 : p < 1 := lt_of_le_of_ne hp_le1 hp1
      exact (binary_pinsker_interior hq_pos hqp hp_lt1).trans hkl_ge

/-- **Chain Rule for Discrete Shannon Entropy:** `H(X, Y) = H(X) + H(Y | X)`. -/
theorem shannonEntropy_chain_rule {α β : Type*} [Fintype α] [Fintype β] {P : α × β → ℝ}
    (hP : IsProbDist P) :
    shannonEntropy P = shannonEntropy (marginalLeft P) + condEntropy P := by
  unfold shannonEntropy condEntropy
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hmx : marginalLeft P x = 0
  · have hxy0 : ∀ y : β, P (x, y) = 0 := fun y =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun y' _ => hP.1 (x, y'))).mp hmx y (Finset.mem_univ y)
    simp [hmx, hxy0]
  · have hmx_pos : 0 < marginalLeft P x :=
      lt_of_le_of_ne (Finset.sum_nonneg fun y _ => hP.1 (x, y)) (Ne.symm hmx)
    have hinner : ∑ y : β, -(P (x, y) * Real.log (P (x, y) / marginalLeft P x)) =
        (∑ y : β, -(P (x, y) * Real.log (P (x, y)))) + marginalLeft P x * Real.log (marginalLeft P x) := by
      have hterm : ∀ y : β, -(P (x, y) * Real.log (P (x, y) / marginalLeft P x)) =
          -(P (x, y) * Real.log (P (x, y))) + P (x, y) * Real.log (marginalLeft P x) := by
        intro y
        by_cases hxy : P (x, y) = 0
        · simp [hxy]
        · have hxy_pos : 0 < P (x, y) := lt_of_le_of_ne (hP.1 (x, y)) (Ne.symm hxy)
          rw [Real.log_div hxy_pos.ne' hmx_pos.ne']
          ring
      simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
      rfl
    linarith

/-- **Mutual Information as KL Divergence:**
`I(X; Y) = D_KL(P_{X,Y} ‖ P_X ⊗ P_Y)`. -/
theorem mutualInfo_eq_klDiv {α β : Type*} [Fintype α] [Fintype β] {P : α × β → ℝ}
    (hP : IsProbDist P) :
    mutualInfo P = klDiv P (fun p => marginalLeft P p.1 * marginalRight P p.2) := by
  unfold mutualInfo shannonEntropy klDiv
  have hL : ∑ x : α, -(marginalLeft P x * Real.log (marginalLeft P x)) =
      ∑ p : α × β, -(P p * Real.log (marginalLeft P p.1)) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    dsimp only
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
    rfl
  have hR : ∑ y : β, -(marginalRight P y * Real.log (marginalRight P y)) =
      ∑ p : α × β, -(P p * Real.log (marginalRight P p.2)) := by
    rw [Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro y _
    dsimp only
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
    rfl
  rw [hL, hR, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ⟨x, y⟩ _
  by_cases hxy : P (x, y) = 0
  · simp [hxy]
  · have hxy_pos : 0 < P (x, y) := lt_of_le_of_ne (hP.1 (x, y)) (Ne.symm hxy)
    have hmx_pos : 0 < marginalLeft P x :=
      lt_of_lt_of_le hxy_pos (Finset.single_le_sum (fun y' _ => hP.1 (x, y')) (Finset.mem_univ y))
    have hmy_pos : 0 < marginalRight P y :=
      lt_of_lt_of_le hxy_pos (Finset.single_le_sum (fun x' _ => hP.1 (x', y)) (Finset.mem_univ x))
    rw [Real.log_div hxy_pos.ne' (mul_pos hmx_pos hmy_pos).ne',
        Real.log_mul hmx_pos.ne' hmy_pos.ne']
    ring

/-- Non-negativity of mutual information: `0 ≤ I(X; Y)`. -/
theorem mutualInfo_nonneg {α β : Type*} [Fintype α] [Fintype β] {P : α × β → ℝ}
    (hP : IsProbDist P) : 0 ≤ mutualInfo P := by
  rw [mutualInfo_eq_klDiv hP]
  let Q : α × β → ℝ := fun p => marginalLeft P p.1 * marginalRight P p.2
  have hL := isProbDist_marginalLeft hP
  have hR := isProbDist_marginalRight hP
  have hQ : IsProbDist Q := by
    refine ⟨fun p => mul_nonneg (hL.1 p.1) (hR.1 p.2), ?_⟩
    simp only [Q, Fintype.sum_prod_type, ← Finset.mul_sum, hR.2, mul_one, hL.2]
  refine gibbs_inequality hP hQ ?_
  intro ⟨x, y⟩ hxy
  have hxy_pos : 0 < P (x, y) := lt_of_le_of_ne (hP.1 (x, y)) (Ne.symm hxy)
  have hmx_pos : 0 < marginalLeft P x :=
    lt_of_lt_of_le hxy_pos (Finset.single_le_sum (fun y' _ => hP.1 (x, y')) (Finset.mem_univ y))
  have hmy_pos : 0 < marginalRight P y :=
    lt_of_lt_of_le hxy_pos (Finset.single_le_sum (fun x' _ => hP.1 (x', y)) (Finset.mem_univ x))
  exact mul_pos hmx_pos hmy_pos

/-- **Subadditivity of Shannon Entropy:** `H(X, Y) ≤ H(X) + H(Y)`. -/
theorem shannonEntropy_subadditive {α β : Type*} [Fintype α] [Fintype β] {P : α × β → ℝ}
    (hP : IsProbDist P) :
    shannonEntropy P ≤ shannonEntropy (marginalLeft P) + shannonEntropy (marginalRight P) := by
  have := mutualInfo_nonneg hP
  unfold mutualInfo at this
  linarith

/-- **Conditioning Reduces Entropy:** `H(Y | X) ≤ H(Y)`. -/
theorem condEntropy_le_marginalRight {α β : Type*} [Fintype α] [Fintype β] {P : α × β → ℝ}
    (hP : IsProbDist P) :
    condEntropy P ≤ shannonEntropy (marginalRight P) := by
  have hchain := shannonEntropy_chain_rule hP
  have hsub := shannonEntropy_subadditive hP
  linarith

/-- Non-negativity of conditional entropy: `0 ≤ H(Y | X)`. -/
theorem condEntropy_nonneg {α β : Type*} [Fintype α] [Fintype β] {P : α × β → ℝ}
    (hP : IsProbDist P) : 0 ≤ condEntropy P := by
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  by_cases hxy : P (x, y) = 0
  · simp [hxy]
  · have hxy_pos : 0 < P (x, y) := lt_of_le_of_ne (hP.1 (x, y)) (Ne.symm hxy)
    have hle : P (x, y) ≤ marginalLeft P x :=
      Finset.single_le_sum (fun y' _ => hP.1 (x, y')) (Finset.mem_univ y)
    have hmx_pos : 0 < marginalLeft P x := lt_of_lt_of_le hxy_pos hle
    have hdiv_le : P (x, y) / marginalLeft P x ≤ 1 := (div_le_one hmx_pos).mpr hle
    have hlog : Real.log (P (x, y) / marginalLeft P x) ≤ 0 :=
      Real.log_nonpos (div_nonneg hxy_pos.le hmx_pos.le) hdiv_le
    nlinarith

/-- **Strong Subadditivity / Conditioning on Extra Information Reduces Entropy:**
For any joint distribution `P : (α × β) × γ → ℝ`, `H(Z | X, Y) ≤ H(Z | X)`. -/
theorem condEntropy_pair_le {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {P : (α × β) × γ → ℝ} (hP : IsProbDist P) :
    condEntropy P ≤
      condEntropy (fun p : α × γ => ∑ y : β, P ((p.1, y), p.2)) := by
  let P_XZ : α × γ → ℝ := fun p => ∑ y : β, P ((p.1, y), p.2)
  have hP_XZ_nn : ∀ x z, 0 ≤ P_XZ (x, z) := fun x z =>
    Finset.sum_nonneg fun y _ => hP.1 ((x, y), z)
  have hmargX : ∀ x : α, marginalLeft P_XZ x = ∑ y : β, marginalLeft P (x, y) := by
    intro x
    simp only [marginalLeft, P_XZ]
    exact Finset.sum_comm
  -- Decompose both sides as a weighted sum over `x : α` of conditional distributions on `β × γ`
  have hLHS : condEntropy P =
      ∑ x : α, if hmx : marginalLeft P_XZ x = 0 then 0 else
        marginalLeft P_XZ x * condEntropy (fun p : β × γ => P ((x, p.1), p.2) / marginalLeft P_XZ x) := by
    unfold condEntropy
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hmx : marginalLeft P_XZ x = 0
    · rw [dif_pos hmx]
      have hy0 : ∀ y : β, marginalLeft P (x, y) = 0 := fun y =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun y' _ =>
          Finset.sum_nonneg fun z _ => hP.1 ((x, y'), z))).mp ((hmargX x).symm.trans hmx) y (Finset.mem_univ y)
      apply Finset.sum_eq_zero; intro y _
      apply Finset.sum_eq_zero; intro z _
      have hz0 : P ((x, y), z) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun z' _ => hP.1 ((x, y), z'))).mp (hy0 y) z (Finset.mem_univ z)
      simp [hz0]
    · rw [dif_neg hmx]
      have hmx_pos : 0 < marginalLeft P_XZ x :=
        lt_of_le_of_ne (Finset.sum_nonneg fun z _ => hP_XZ_nn x z) (Ne.symm hmx)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      have hml_eq : marginalLeft (fun p : β × γ => P ((x, p.1), p.2) / marginalLeft P_XZ x) y =
          marginalLeft P (x, y) / marginalLeft P_XZ x := by
        simp only [marginalLeft, ← Finset.sum_div]
      rw [hml_eq]
      have hdiv_eq : (P ((x, y), z) / marginalLeft P_XZ x) / (marginalLeft P (x, y) / marginalLeft P_XZ x) =
          P ((x, y), z) / marginalLeft P (x, y) := div_div_div_cancel_right₀ hmx_pos.ne' _ _
      rw [hdiv_eq]
      field_simp [hmx_pos.ne']
  have hRHS : condEntropy P_XZ =
      ∑ x : α, if hmx : marginalLeft P_XZ x = 0 then 0 else
        marginalLeft P_XZ x *
          shannonEntropy (marginalRight (fun p : β × γ => P ((x, p.1), p.2) / marginalLeft P_XZ x)) := by
    unfold condEntropy shannonEntropy
    apply Finset.sum_congr rfl
    intro x _
    by_cases hmx : marginalLeft P_XZ x = 0
    · rw [dif_pos hmx]
      apply Finset.sum_eq_zero; intro z _
      have hz0 : P_XZ (x, z) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun z' _ => hP_XZ_nn x z')).mp hmx z (Finset.mem_univ z)
      simp [hz0]
    · rw [dif_neg hmx]
      have hmx_pos : 0 < marginalLeft P_XZ x :=
        lt_of_le_of_ne (Finset.sum_nonneg fun z _ => hP_XZ_nn x z) (Ne.symm hmx)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      have hmr_eq : marginalRight (fun p : β × γ => P ((x, p.1), p.2) / marginalLeft P_XZ x) z =
          P_XZ (x, z) / marginalLeft P_XZ x := by
        simp only [marginalRight, P_XZ, ← Finset.sum_div]
      rw [hmr_eq]
      field_simp [hmx_pos.ne']
  rw [hLHS, hRHS]
  apply Finset.sum_le_sum
  intro x _
  by_cases hmx : marginalLeft P_XZ x = 0
  · simp [hmx]
  · rw [dif_neg hmx, dif_neg hmx]
    have hmx_pos : 0 < marginalLeft P_XZ x :=
      lt_of_le_of_ne (Finset.sum_nonneg fun z _ => hP_XZ_nn x z) (Ne.symm hmx)
    apply mul_le_mul_of_nonneg_left _ hmx_pos.le
    have hQx : IsProbDist (fun p : β × γ => P ((x, p.1), p.2) / marginalLeft P_XZ x) := by
      refine ⟨fun p => div_nonneg (hP.1 ((x, p.1), p.2)) hmx_pos.le, ?_⟩
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.sum_div]
      change (∑ y : β, marginalLeft P (x, y)) / marginalLeft P_XZ x = 1
      rw [← hmargX x, div_self hmx_pos.ne']
    exact condEntropy_le_marginalRight hQx

end DiscreteEntropy

/-! ## Section 2: Shearer's Entropy Lemma, Han's Inequality & Projection Corollaries -/

section ShearerAndHan

/-- Restrict a `d`-tuple `x : ∀ i : Fin d, α i` to a coordinate subset `S : Finset (Fin d)`. -/
def restrictTuple {d : ℕ} {α : Fin d → Type*} (S : Finset (Fin d))
    (x : ∀ i : Fin d, α i) : ∀ i : S, α i :=
  fun i => x i.1

/-- Marginal (projected) distribution of `P : (∀ i : Fin d, α i) → ℝ` onto coordinate subset `S`. -/
def projDist {d : ℕ} {α : Fin d → Type*} [∀ i, Fintype (α i)]
    (P : (∀ i : Fin d, α i) → ℝ) (S : Finset (Fin d)) (u : ∀ i : S, α i) : ℝ :=
  ∑ x : ∀ i : Fin d, α i, if restrictTuple S x = u then P x else 0

/-- Conditional entropy `H(X_j | X_S) = H(X_{S ∪ {j}}) - H(X_S)` of coordinate `j` given `S`. -/
def condCoordEntropy {d : ℕ} {α : Fin d → Type*} [∀ i, Fintype (α i)]
    (P : (∀ i : Fin d, α i) → ℝ) (j : Fin d) (S : Finset (Fin d)) : ℝ :=
  shannonEntropy (projDist P (insert j S)) - shannonEntropy (projDist P S)

lemma isProbDist_projDist {d : ℕ} {α : Fin d → Type*} [∀ i, Fintype (α i)]
    {P : (∀ i : Fin d, α i) → ℝ} (hP : IsProbDist P) (S : Finset (Fin d)) :
    IsProbDist (projDist P S) := by
  refine ⟨fun u => Finset.sum_nonneg fun x _ => by split_ifs; exacts [hP.1 x, le_refl 0], ?_⟩
  unfold projDist
  rw [Finset.sum_comm]
  have h1 : ∀ x : ∀ i : Fin d, α i,
      (∑ u : ∀ i : S, α i, if restrictTuple S x = u then P x else 0) = P x := by
    intro x
    simp
  simp_rw [h1]
  exact hP.2

lemma shannonEntropy_projDist_empty {d : ℕ} {α : Fin d → Type*} [∀ i, Fintype (α i)]
    {P : (∀ i : Fin d, α i) → ℝ} (hP : IsProbDist P) :
    shannonEntropy (projDist P ∅) = 0 := by
  unfold shannonEntropy
  have huniq : Unique (∀ i : (∅ : Finset (Fin d)), α i) :=
    { default := fun i => absurd i.2 (Finset.notMem_empty _)
      uniq := fun u => funext fun i => absurd i.2 (Finset.notMem_empty _) }
  have hval : projDist P ∅ huniq.default = 1 := by
    unfold projDist
    have hall : ∀ x : ∀ i : Fin d, α i, restrictTuple ∅ x = huniq.default :=
      fun x => huniq.uniq _
    simp_rw [hall, ite_true]
    exact hP.2
  rw [Finset.univ_unique, Finset.sum_singleton]
  have heq : (default : ∀ i : (∅ : Finset (Fin d)), α i) = huniq.default := huniq.uniq _
  rw [heq, hval, Real.log_one, mul_zero, neg_zero]

lemma shannonEntropy_projDist_univ {d : ℕ} {α : Fin d → Type*} [∀ i, Fintype (α i)]
    (P : (∀ i : Fin d, α i) → ℝ) :
    shannonEntropy (projDist P Finset.univ) = shannonEntropy P := by
  let e : (∀ i : Fin d, α i) ≃ (∀ i : (Finset.univ : Finset (Fin d)), α i) :=
    { toFun := restrictTuple Finset.univ
      invFun := fun u i => u ⟨i, Finset.mem_univ i⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcomp : projDist P Finset.univ ∘ e = P := by
    funext x
    have hiff : ∀ y : ∀ i : Fin d, α i, restrictTuple Finset.univ y = restrictTuple Finset.univ x ↔ y = x := by
      intro y
      constructor
      · intro h; funext i; exact congrFun h ⟨i, Finset.mem_univ i⟩
      · intro h; rw [h]
    change (∑ y : ∀ i : Fin d, α i,
      if restrictTuple Finset.univ y = restrictTuple Finset.univ x then P y else 0) = P x
    simp [hiff]
  conv_rhs => rw [← hcomp]
  exact (shannonEntropy_equiv e (projDist P Finset.univ)).symm

/-- Equivalence splitting `insert j S` (for `j ∉ S`) into `S` and `{j}`. -/
private def insertTupleEquiv {d : ℕ} {α : Fin d → Type*} {j : Fin d} {S : Finset (Fin d)}
    (hj : j ∉ S) :
    ((∀ i : S, α i) × α j) ≃ (∀ i : (insert j S : Finset (Fin d)), α i) where
  toFun p i :=
    if h : i.1 = j then cast (congrArg α h.symm) p.2
    else p.1 ⟨i.1, (Finset.mem_insert.mp i.2).resolve_left h⟩
  invFun u := (fun i => u ⟨i.1, Finset.mem_insert_of_mem i.2⟩, u ⟨j, Finset.mem_insert_self j S⟩)
  left_inv := by
    rintro ⟨u, a⟩
    ext i
    · have hne : i.1 ≠ j := fun h => hj (h ▸ i.2)
      simp [hne]
    · simp
  right_inv := by
    intro u
    funext ⟨i, hi⟩
    by_cases h : i = j
    · subst h; simp
    · simp [h]

/-- Equivalence splitting a disjoint union `A ∪ B` into `A` and `B`. -/
private def disjointUnionTupleEquiv {d : ℕ} {α : Fin d → Type*} {A B : Finset (Fin d)}
    (hdisj : Disjoint A B) :
    ((∀ i : A, α i) × (∀ i : B, α i)) ≃ (∀ i : (A ∪ B : Finset (Fin d)), α i) where
  toFun p i :=
    if h : i.1 ∈ A then p.1 ⟨i.1, h⟩
    else p.2 ⟨i.1, (Finset.mem_union.mp i.2).resolve_left h⟩
  invFun u :=
    (fun i => u ⟨i.1, Finset.mem_union_left B i.2⟩,
     fun i => u ⟨i.1, Finset.mem_union_right A i.2⟩)
  left_inv := by
    rintro ⟨u, v⟩
    ext i
    · simp [i.2]
    · have hnotA : i.1 ∉ A := Finset.disjoint_right.mp hdisj i.2
      simp [hnotA]
  right_inv := by
    intro u
    funext ⟨i, hi⟩
    by_cases h : i ∈ A <;> simp [h]

lemma marginalLeft_projDist_insert {d : ℕ} {α : Fin d → Type*} [∀ i, Fintype (α i)]
    (P : (∀ i : Fin d, α i) → ℝ) {j : Fin d} {S : Finset (Fin d)} (hj : j ∉ S) :
    marginalLeft (projDist P (insert j S) ∘ insertTupleEquiv hj) = projDist P S := by
  funext u
  unfold marginalLeft projDist
  simp only [Function.comp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hres : restrictTuple S x = u
  · rw [if_pos hres]
    have hiff : ∀ a : α j,
        restrictTuple (insert j S) x = insertTupleEquiv hj (u, a) ↔ a = x j := by
      intro a
      constructor
      · intro h
        have hj_eq := congrFun h ⟨j, Finset.mem_insert_self j S⟩
        simpa [restrictTuple, insertTupleEquiv] using hj_eq.symm
      · intro h
        funext ⟨i, hi⟩
        by_cases hij : i = j
        · subst hij; simp [restrictTuple, insertTupleEquiv, h]
        · have hiS : i ∈ S := (Finset.mem_insert.mp hi).resolve_left hij
          have hu := congrFun hres ⟨i, hiS⟩
          simpa [restrictTuple, insertTupleEquiv, hij] using hu
    simp [hiff]
  · rw [if_neg hres]
    apply Finset.sum_eq_zero
    intro a _
    rw [if_neg]
    intro heq
    apply hres
    funext ⟨i, hi⟩
    have hne : i ≠ j := fun h => hj (h ▸ hi)
    have hi_eq := congrFun heq ⟨i, Finset.mem_insert_of_mem hi⟩
    simpa [restrictTuple, insertTupleEquiv, hne] using hi_eq

lemma condCoordEntropy_eq_condEntropy {d : ℕ} {α : Fin d → Type*} [∀ i, Fintype (α i)]
    {P : (∀ i : Fin d, α i) → ℝ} (hP : IsProbDist P) {j : Fin d} {S : Finset (Fin d)} (hj : j ∉ S) :
    condCoordEntropy P j S = condEntropy (projDist P (insert j S) ∘ insertTupleEquiv hj) := by
  unfold condCoordEntropy
  have hQ : IsProbDist (projDist P (insert j S) ∘ insertTupleEquiv hj) :=
    isProbDist_equiv (insertTupleEquiv hj) (isProbDist_projDist hP (insert j S))
  have hchain := shannonEntropy_chain_rule hQ
  rw [shannonEntropy_equiv (insertTupleEquiv hj), marginalLeft_projDist_insert P hj] at hchain
  linarith

lemma condCoordEntropy_nonneg {d : ℕ} {α : Fin d → Type*} [∀ i, Fintype (α i)]
    {P : (∀ i : Fin d, α i) → ℝ} (hP : IsProbDist P) (j : Fin d) (S : Finset (Fin d)) :
    0 ≤ condCoordEntropy P j S := by
  by_cases hj : j ∈ S
  · rw [condCoordEntropy, Finset.insert_eq_of_mem hj, sub_self]
  · rw [condCoordEntropy_eq_condEntropy hP hj]
    exact condEntropy_nonneg (isProbDist_equiv (insertTupleEquiv hj) (isProbDist_projDist hP (insert j S)))

/-- **Monotonicity of Conditioning on Coordinate Subsets:**
If `A ⊆ B` and `j ∉ B`, then `H(X_j | X_B) ≤ H(X_j | X_A)`. -/
theorem condCoordEntropy_antitone {d : ℕ} {α : Fin d → Type*} [∀ i, Fintype (α i)]
    {P : (∀ i : Fin d, α i) → ℝ} (hP : IsProbDist P) {j : Fin d} {A B : Finset (Fin d)}
    (hAB : A ⊆ B) (hjB : j ∉ B) :
    condCoordEntropy P j B ≤ condCoordEntropy P j A := by
  have hjA : j ∉ A := fun h => hjB (hAB h)
  rw [condCoordEntropy_eq_condEntropy hP hjB, condCoordEntropy_eq_condEntropy hP hjA]
  let D : Finset (Fin d) := B \ A
  have hdisj : Disjoint A D := Finset.disjoint_sdiff
  have hunion : A ∪ D = B := Finset.union_sdiff_of_subset hAB
  let eAB : (∀ i : (A ∪ D : Finset (Fin d)), α i) ≃ (∀ i : B, α i) :=
    { toFun := fun w i => w ⟨i.1, hunion.symm ▸ i.2⟩
      invFun := fun w i => w ⟨i.1, hunion ▸ i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eB : ((∀ i : A, α i) × (∀ i : D, α i)) ≃ (∀ i : B, α i) :=
    (disjointUnionTupleEquiv hdisj).trans eAB
  let Q : ((∀ i : A, α i) × (∀ i : D, α i)) × α j → ℝ :=
    fun p => (projDist P (insert j B) ∘ insertTupleEquiv hjB) (eB p.1, p.2)
  have hQ_dist : IsProbDist Q := by
    let eAll : (((∀ i : A, α i) × (∀ i : D, α i)) × α j) ≃ ((∀ i : B, α i) × α j) :=
      Equiv.prodCongr eB (Equiv.refl (α j))
    exact isProbDist_equiv (eAll.trans (insertTupleEquiv hjB)) (isProbDist_projDist hP (insert j B))
  have hcond_eq : condEntropy (projDist P (insert j B) ∘ insertTupleEquiv hjB) = condEntropy Q := by
    unfold condEntropy
    rw [← Equiv.sum_comp eB]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro a _
    rfl
  have hmarg_Q : (fun p : (∀ i : A, α i) × α j => ∑ v : ∀ i : D, α i, Q ((p.1, v), p.2)) =
      projDist P (insert j A) ∘ insertTupleEquiv hjA := by
    funext ⟨u, a⟩
    simp only [Q, Function.comp, projDist]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hres : restrictTuple (insert j A) x = insertTupleEquiv hjA (u, a)
    · rw [if_pos hres]
      have hiff : ∀ v : ∀ i : D, α i,
          restrictTuple (insert j B) x = insertTupleEquiv hjB (eB (u, v), a) ↔
          v = restrictTuple D x := by
        intro v
        constructor
        · intro h
          funext ⟨i, hiD⟩
          have hiB : i ∈ B := (Finset.mem_sdiff.mp hiD).1
          have hiA : i ∉ A := (Finset.mem_sdiff.mp hiD).2
          have hne : i ≠ j := fun hij => hjB (hij ▸ hiB)
          have hval := congrFun h ⟨i, Finset.mem_insert_of_mem hiB⟩
          simpa [restrictTuple, insertTupleEquiv, eB, eAB, disjointUnionTupleEquiv, hne, hiA] using hval.symm
        · intro hv
          subst hv
          funext ⟨i, hi⟩
          by_cases hij : i = j
          · subst i
            have hja := congrFun hres ⟨j, Finset.mem_insert_self j A⟩
            simpa [restrictTuple, insertTupleEquiv] using hja
          · have hiB : i ∈ B := (Finset.mem_insert.mp hi).resolve_left hij
            by_cases hiA : i ∈ A
            · have hia := congrFun hres ⟨i, Finset.mem_insert_of_mem hiA⟩
              simpa [restrictTuple, insertTupleEquiv, eB, eAB, disjointUnionTupleEquiv, hij, hiA] using hia
            · simp [restrictTuple, insertTupleEquiv, eB, eAB, disjointUnionTupleEquiv, hij, hiA]
      simp [hiff]
    · rw [if_neg hres]
      apply Finset.sum_eq_zero
      intro v _
      rw [if_neg]
      intro heq
      apply hres
      funext ⟨i, hi⟩
      by_cases hij : i = j
      · subst i
        have hja := congrFun heq ⟨j, Finset.mem_insert_self j B⟩
        simpa [restrictTuple, insertTupleEquiv] using hja
      · have hiA : i ∈ A := (Finset.mem_insert.mp hi).resolve_left hij
        have hiB : i ∈ B := hAB hiA
        have hia := congrFun heq ⟨i, Finset.mem_insert_of_mem hiB⟩
        simpa [restrictTuple, insertTupleEquiv, eB, eAB, disjointUnionTupleEquiv, hij, hiA] using hia
  rw [hcond_eq, ← hmarg_Q]
  exact condEntropy_pair_le hQ_dist

/-- **Subset Chain Rule:** For any coordinate subset `S : Finset (Fin d)`,
`H(X_S) = ∑ j ∈ S, H(X_j | X_{S ∩ {i | i < j}})`. -/
theorem shannonEntropy_projDist_chain_rule {d : ℕ} {α : Fin d → Type*} [∀ i, Fintype (α i)]
    {P : (∀ i : Fin d, α i) → ℝ} (hP : IsProbDist P) (S : Finset (Fin d)) :
    shannonEntropy (projDist P S) =
      ∑ j ∈ S, condCoordEntropy P j (S.filter (fun i => i < j)) := by
  have hind : ∀ m : ℕ, m ≤ d →
      shannonEntropy (projDist P (S.filter (fun i : Fin d => i.val < m))) =
        ∑ j ∈ S.filter (fun i : Fin d => i.val < m),
          condCoordEntropy P j (S.filter (fun i => i < j)) := by
    intro m hm
    induction m with
    | zero =>
      have hemp : S.filter (fun i : Fin d => i.val < 0) = ∅ := by
        ext i; simp
      rw [hemp, Finset.sum_empty, shannonEntropy_projDist_empty hP]
    | succ m ih =>
      have hm_lt : m < d := by omega
      let jm : Fin d := ⟨m, hm_lt⟩
      have hstep := ih (by omega)
      by_cases hjm : jm ∈ S
      · have hflt : S.filter (fun i : Fin d => i.val < m + 1) =
            insert jm (S.filter (fun i : Fin d => i.val < m)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_insert, jm, Fin.ext_iff]
          constructor
          · rintro ⟨hiS, hilt⟩
            by_cases heq : i.val = m
            · left; exact heq
            · right; exact ⟨hiS, by omega⟩
          · rintro (heq | ⟨hiS, hilt⟩)
            · have hi_eq : i = jm := Fin.ext heq
              exact ⟨hi_eq ▸ hjm, by omega⟩
            · exact ⟨hiS, by omega⟩
        have hnotmem : jm ∉ S.filter (fun i : Fin d => i.val < m) := by
          simp [jm]
        have hlt_eq : S.filter (fun i : Fin d => i < jm) = S.filter (fun i : Fin d => i.val < m) := by
          ext i; simp [jm, Fin.lt_def]
        rw [hflt, Finset.sum_insert hnotmem, hlt_eq, ← hstep]
        unfold condCoordEntropy
        ring
      · have hflt : S.filter (fun i : Fin d => i.val < m + 1) =
            S.filter (fun i : Fin d => i.val < m) := by
          ext i
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hiS, hilt⟩
            refine ⟨hiS, ?_⟩
            by_contra hge
            have hi_eq : i = jm := Fin.ext (by dsimp [jm]; omega)
            exact hjm (hi_eq ▸ hiS)
          · rintro ⟨hiS, hilt⟩
            exact ⟨hiS, by omega⟩
        rw [hflt]
        exact hstep
  have hfull : S.filter (fun i : Fin d => i.val < d) = S := by
    ext i
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro _
    exact i.isLt
  have hres := hind d le_rfl
  rw [hfull] at hres
  exact hres

/-- **Shearer's Entropy Lemma:**
If a finite family `(ℱ r)_{r ∈ ι}` of subsets of `Fin d` covers every coordinate `j : Fin d`
at least `k` times (`∀ j, k ≤ #{r | j ∈ ℱ r}`), then for every probability distribution `P`
on `∀ i : Fin d, α i`,
`k * H(X) ≤ ∑ r : ι, H(X_{ℱ r})`. -/
theorem shearer_entropy_lemma {d : ℕ} {α : Fin d → Type*} [∀ i, Fintype (α i)]
    {ι : Type*} [Fintype ι] (ℱ : ι → Finset (Fin d)) (k : ℕ)
    (hcov : ∀ j : Fin d, k ≤ (Finset.univ.filter (fun r : ι => j ∈ ℱ r)).card)
    {P : (∀ i : Fin d, α i) → ℝ} (hP : IsProbDist P) :
    (k : ℝ) * shannonEntropy P ≤ ∑ r : ι, shannonEntropy (projDist P (ℱ r)) := by
  have hchain_all : shannonEntropy P =
      ∑ j : Fin d, condCoordEntropy P j (Finset.univ.filter (fun i => i < j)) := by
    rw [← shannonEntropy_projDist_univ P]
    exact shannonEntropy_projDist_chain_rule hP Finset.univ
  have hstep1 : ∑ r : ι, shannonEntropy (projDist P (ℱ r)) ≥
      ∑ r : ι, ∑ j ∈ ℱ r, condCoordEntropy P j (Finset.univ.filter (fun i => i < j)) := by
    apply Finset.sum_le_sum
    intro r _
    rw [shannonEntropy_projDist_chain_rule hP (ℱ r)]
    apply Finset.sum_le_sum
    intro j _
    apply condCoordEntropy_antitone hP
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
    · simp
  have hswap : (∑ r : ι, ∑ j ∈ ℱ r, condCoordEntropy P j (Finset.univ.filter (fun i => i < j))) =
      ∑ j : Fin d, ((Finset.univ.filter (fun r : ι => j ∈ ℱ r)).card : ℝ) *
        condCoordEntropy P j (Finset.univ.filter (fun i => i < j)) := by
    calc ∑ r : ι, ∑ j ∈ ℱ r, condCoordEntropy P j (Finset.univ.filter (fun i => i < j))
        = ∑ r : ι, ∑ j : Fin d,
            if j ∈ ℱ r then condCoordEntropy P j (Finset.univ.filter (fun i => i < j)) else 0 := by
          apply Finset.sum_congr rfl; intro r _
          rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = ∑ j : Fin d, ∑ r : ι,
            if j ∈ ℱ r then condCoordEntropy P j (Finset.univ.filter (fun i => i < j)) else 0 :=
          Finset.sum_comm
      _ = ∑ j : Fin d, ((Finset.univ.filter (fun r : ι => j ∈ ℱ r)).card : ℝ) *
            condCoordEntropy P j (Finset.univ.filter (fun i => i < j)) := by
          apply Finset.sum_congr rfl; intro j _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hstep2 : (k : ℝ) * shannonEntropy P ≤
      ∑ j : Fin d, ((Finset.univ.filter (fun r : ι => j ∈ ℱ r)).card : ℝ) *
        condCoordEntropy P j (Finset.univ.filter (fun i => i < j)) := by
    rw [hchain_all, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcov j))
      (condCoordEntropy_nonneg hP j _)
  linarith

/-- **Han's Inequality:**
For any `d ≥ 1` and any probability distribution `P` on `∀ i : Fin d, α i`,
`((d - 1 : ℕ) : ℝ) * H(X) ≤ ∑ i : Fin d, H(X_{-i})`, where `X_{-i}` drops coordinate `i`. -/
theorem hans_inequality {d : ℕ} {α : Fin d → Type*} [∀ i, Fintype (α i)]
    {P : (∀ i : Fin d, α i) → ℝ} (hP : IsProbDist P) :
    ((d - 1 : ℕ) : ℝ) * shannonEntropy P ≤
      ∑ i : Fin d, shannonEntropy (projDist P (Finset.univ.erase i)) := by
  refine shearer_entropy_lemma (fun i : Fin d => Finset.univ.erase i) (d - 1) ?_ hP
  intro j
  have hfilt : Finset.univ.filter (fun r : Fin d => j ∈ Finset.univ.erase r) =
      Finset.univ.erase j := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    exact ne_comm
  rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]

/-- **Combinatorial Shearer Projection Inequality (Bollobás–Thomason Box Theorem):**
If `(ℱ r)_{r ∈ ι}` covers every coordinate `j : Fin d` at least `k` times (`1 ≤ k`),
then for every finite set `A : Finset (∀ i : Fin d, α i)`,
`|A|^k ≤ ∏ r : ι, |π_{ℱ r}(A)|`. -/
theorem shearer_projection_card {d : ℕ} {α : Fin d → Type*} [∀ i, Fintype (α i)]
    {ι : Type*} [Fintype ι] (ℱ : ι → Finset (Fin d)) (k : ℕ) (hk : 1 ≤ k)
    (hcov : ∀ j : Fin d, k ≤ (Finset.univ.filter (fun r : ι => j ∈ ℱ r)).card)
    (A : Finset (∀ i : Fin d, α i)) :
    A.card ^ k ≤ ∏ r : ι, (A.image (restrictTuple (ℱ r))).card := by
  by_cases hA : A = ∅
  · subst hA
    simp only [Finset.card_empty, zero_pow (by omega : k ≠ 0), Nat.zero_le]
  · have hA_pos : (0 : ℝ) < (A.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hA)
    let P : (∀ i : Fin d, α i) → ℝ := fun x => if x ∈ A then 1 / (A.card : ℝ) else 0
    have hP : IsProbDist P := by
      refine ⟨fun x => by dsimp only [P]; split_ifs <;> positivity, ?_⟩
      simp only [P, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      field_simp [hA_pos.ne']
    have hHP : shannonEntropy P = Real.log (A.card : ℝ) := by
      unfold shannonEntropy
      have hterm : ∀ x : ∀ i : Fin d, α i,
          -(P x * Real.log (P x)) = if x ∈ A then (1 / (A.card : ℝ)) * Real.log (A.card : ℝ) else 0 := by
        intro x
        dsimp only [P]
        split_ifs
        · rw [one_div, Real.log_inv]; ring
        · simp
      simp_rw [hterm, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      field_simp [hA_pos.ne']
    -- For each `r`, `projDist P (ℱ r)` is supported on `A.image (restrictTuple (ℱ r))`, so `H ≤ log |π_{ℱ r}(A)|`
    have hproj_le : ∀ r : ι,
        shannonEntropy (projDist P (ℱ r)) ≤ Real.log ((A.image (restrictTuple (ℱ r))).card : ℝ) := by
      intro r
      let B := A.image (restrictTuple (ℱ r))
      have hB_pos : (0 : ℝ) < (B.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ((Finset.nonempty_iff_ne_empty.mpr hA).image _)
      have hsupp : ∀ u : ∀ i : ℱ r, α i, u ∉ B → projDist P (ℱ r) u = 0 := by
        intro u hu
        unfold projDist
        apply Finset.sum_eq_zero
        intro x _
        split_ifs with hres
        · dsimp only [P]
          rw [if_neg]
          intro hxA
          exact hu (Finset.mem_image.mpr ⟨x, hxA, hres⟩)
        · rfl
      let Q : B → ℝ := fun u => projDist P (ℱ r) u.1
      have hQ : IsProbDist Q := by
        have hprojP := isProbDist_projDist hP (ℱ r)
        refine ⟨fun u => hprojP.1 u.1, ?_⟩
        rw [Finset.univ_eq_attach]
        have hsum_eq : ∑ u ∈ B.attach, projDist P (ℱ r) u.1 = ∑ u ∈ B, projDist P (ℱ r) u :=
          Finset.sum_attach B (fun u => projDist P (ℱ r) u)
        rw [hsum_eq]
        have hfull : (∑ u ∈ B, projDist P (ℱ r) u) + (∑ u ∈ Bᶜ, projDist P (ℱ r) u) = 1 :=
          (Finset.sum_add_sum_compl B (projDist P (ℱ r))).trans hprojP.2
        have hzero : ∑ u ∈ Bᶜ, projDist P (ℱ r) u = 0 :=
          Finset.sum_eq_zero fun u hu => hsupp u (Finset.mem_compl.mp hu)
        linarith
      have hHQ_eq : shannonEntropy (projDist P (ℱ r)) = shannonEntropy Q := by
        unfold shannonEntropy
        rw [← Finset.sum_add_sum_compl B (fun u => -(projDist P (ℱ r) u * Real.log (projDist P (ℱ r) u)))]
        have hzero : ∑ u ∈ Bᶜ, -(projDist P (ℱ r) u * Real.log (projDist P (ℱ r) u)) = 0 :=
          Finset.sum_eq_zero fun u hu => by simp [hsupp u (Finset.mem_compl.mp hu)]
        rw [hzero, add_zero, Finset.univ_eq_attach]
        exact (Finset.sum_attach B (fun u => -(projDist P (ℱ r) u * Real.log (projDist P (ℱ r) u)))).symm
      rw [hHQ_eq]
      have hle := shannonEntropy_le_log_card hQ
      simpa [Fintype.card_coe] using hle
    have hshearer := shearer_entropy_lemma ℱ k hcov hP
    rw [hHP] at hshearer
    have hlog_le : (k : ℝ) * Real.log (A.card : ℝ) ≤
        ∑ r : ι, Real.log ((A.image (restrictTuple (ℱ r))).card : ℝ) :=
      hshearer.trans (Finset.sum_le_sum fun r _ => hproj_le r)
    have hprod_pos : ∀ r : ι, ((A.image (restrictTuple (ℱ r))).card : ℝ) ≠ 0 := by
      intro r
      have : 0 < (A.image (restrictTuple (ℱ r))).card :=
        Finset.card_pos.mpr ((Finset.nonempty_iff_ne_empty.mpr hA).image _)
      exact_mod_cast this.ne'
    have hlog_prod : ∑ r : ι, Real.log ((A.image (restrictTuple (ℱ r))).card : ℝ) =
        Real.log (∏ r : ι, ((A.image (restrictTuple (ℱ r))).card : ℝ)) :=
      (Real.log_prod fun r _ => hprod_pos r).symm
    have hlog_pow : (k : ℝ) * Real.log (A.card : ℝ) = Real.log ((A.card : ℝ) ^ k) :=
      (Real.log_pow (A.card : ℝ) k).symm
    rw [hlog_pow, hlog_prod] at hlog_le
    have hreal : (A.card : ℝ) ^ k ≤ ∏ r : ι, ((A.image (restrictTuple (ℱ r))).card : ℝ) := by
      have h1 := Real.exp_le_exp.mpr hlog_le
      rw [Real.exp_log (pow_pos hA_pos k),
          Real.exp_log (Finset.prod_pos fun r _ => by
            exact_mod_cast Finset.card_pos.mpr ((Finset.nonempty_iff_ne_empty.mpr hA).image _))] at h1
      exact h1
    exact_mod_cast hreal

/-- **Loomis–Whitney Inequality (`d ≥ 2`):**
For any finite set `A ⊆ ∀ i : Fin d, α i`,
`|A|^{d - 1} ≤ ∏ i : Fin d, |π_{-i}(A)|`. -/
theorem loomis_whitney_inequality {d : ℕ} (hd : 2 ≤ d) {α : Fin d → Type*} [∀ i, Fintype (α i)]
    (A : Finset (∀ i : Fin d, α i)) :
    A.card ^ (d - 1) ≤ ∏ i : Fin d, (A.image (restrictTuple (Finset.univ.erase i))).card := by
  refine shearer_projection_card (fun i : Fin d => Finset.univ.erase i) (d - 1) (by omega) ?_ A
  intro j
  have hfilt : Finset.univ.filter (fun r : Fin d => j ∈ Finset.univ.erase r) =
      Finset.univ.erase j := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    exact ne_comm
  rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]

end ShearerAndHan

/-! ## Section 3: Kraft–McMillan Inequality, Kraft Converse, Shannon Source Coding & Binary Entropy -/

section KraftAndBinaryEntropy

/-- A code `f : ι → List α` is **prefix-free** (instantaneous) if no codeword is a prefix of
any other codeword. -/
def IsPrefixFree {ι α : Type*} (f : ι → List α) : Prop :=
  ∀ i j : ι, i ≠ j → ¬ (f i <+: f j)

/-- A code `f : ι → List α` is **uniquely decodable** if concatenation of codewords is injective
on finite symbol sequences `List ι`. -/
def IsUniquelyDecodable {ι α : Type*} (f : ι → List α) : Prop :=
  Function.Injective (fun w : List ι => (w.map f).flatten)

/-- Every prefix-free code with nonempty codewords is uniquely decodable. -/
theorem isUniquelyDecodable_of_isPrefixFree {ι α : Type*} {f : ι → List α}
    (hf : IsPrefixFree f) (hne : ∀ i : ι, f i ≠ []) :
    IsUniquelyDecodable f := by
  intro w₁
  induction w₁ with
  | nil =>
    intro w₂ heq
    cases w₂ with
    | nil => rfl
    | cons j t₂ =>
      simp only [List.map_nil, List.flatten_nil, List.map_cons, List.flatten_cons] at heq
      have hj : f j = [] := (List.append_eq_nil_iff.mp heq.symm).1
      exact absurd hj (hne j)
  | cons i t₁ ih =>
    intro w₂ heq
    cases w₂ with
    | nil =>
      simp only [List.map_nil, List.flatten_nil, List.map_cons, List.flatten_cons] at heq
      have hi : f i = [] := (List.append_eq_nil_iff.mp heq).1
      exact absurd hi (hne i)
    | cons j t₂ =>
      simp only [List.map_cons, List.flatten_cons] at heq
      have hij : i = j := by
        rcases List.append_eq_append_iff.mp heq with ⟨s, hs, _⟩ | ⟨s, hs, _⟩
        · by_contra hne_ij
          exact hf i j hne_ij ⟨s, hs.symm⟩
        · by_contra hne_ij
          exact hf j i (Ne.symm hne_ij) ⟨s, hs.symm⟩
      subst hij
      have ht : (t₁.map f).flatten = (t₂.map f).flatten := List.append_cancel_left heq
      rw [ih ht]

/-- Elementary quadratic lower bound `(1 + δ)^m ≥ 1 + m * δ + (m * (m - 1) / 2) * δ^2` for `δ ≥ 0`. -/
private lemma one_add_pow_ge_quad {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ m : ℕ, 1 + (m : ℝ) * δ + ((m : ℝ) * ((m : ℝ) - 1) / 2) * δ ^ 2 ≤ (1 + δ) ^ m
  | 0 => by simp
  | m + 1 => by
    have ih := one_add_pow_ge_quad hδ m
    have hmul : (1 + (m : ℝ) * δ + ((m : ℝ) * ((m : ℝ) - 1) / 2) * δ ^ 2) * (1 + δ) ≤
        (1 + δ) ^ m * (1 + δ) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    rw [pow_succ (1 + δ) m]
    have hnonneg : 0 ≤ ((m : ℝ) * ((m : ℝ) - 1) / 2) * δ ^ 3 := by
      cases m with
      | zero => simp
      | succ k =>
        have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have hm1 : ((k + 1 : ℕ) : ℝ) - 1 = (k : ℝ) := by push_cast; ring
        rw [hm1]
        positivity
    have hexp : (1 + (m : ℝ) * δ + ((m : ℝ) * ((m : ℝ) - 1) / 2) * δ ^ 2) * (1 + δ) =
        1 + ((m : ℝ) + 1) * δ + (((m : ℝ) + 1) * (((m : ℝ) + 1) - 1) / 2) * δ ^ 2 +
          ((m : ℝ) * ((m : ℝ) - 1) / 2) * δ ^ 3 := by ring
    push_cast
    linarith

/-- **Kraft–McMillan Inequality (general `q`-ary uniquely decodable codes):**
For any `q ≥ 2` and any uniquely decodable code `f : ι → List (Fin q)` on a finite alphabet `ι`,
`∑ i : ι, 1 / q ^ (f i).length ≤ 1`. -/
theorem kraft_mcmillan_inequality {ι : Type*} [Fintype ι] {q : ℕ} (hq : 2 ≤ q)
    (f : ι → List (Fin q)) (hf : IsUniquelyDecodable f) :
    ∑ i : ι, (1 : ℝ) / (q : ℝ) ^ (f i).length ≤ 1 := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  set S : ℝ := ∑ i : ι, (1 : ℝ) / (q : ℝ) ^ (f i).length
  set L : ℕ := Finset.univ.sup (fun i : ι => (f i).length)
  -- Key polynomial-growth bound: `S^m ≤ m * L + 1` for every `m : ℕ`
  have hpow_le : ∀ m : ℕ, S ^ m ≤ (m * L + 1 : ℝ) := by
    intro m
    have hexpand : S ^ m = ∑ w : Fin m → ι, (1 : ℝ) / (q : ℝ) ^ (∑ j : Fin m, (f (w j)).length) := by
      dsimp only [S]
      rw [Fintype.sum_pow]
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.prod_div_distrib, Finset.prod_const_one, ← Finset.prod_pow_eq_pow_sum]
    have hlen_le : ∀ w : Fin m → ι, (∑ j : Fin m, (f (w j)).length) ≤ m * L := by
      intro w
      calc ∑ j : Fin m, (f (w j)).length
          ≤ ∑ _j : Fin m, L := Finset.sum_le_sum fun j _ =>
            Finset.le_sup (f := fun i : ι => (f i).length) (Finset.mem_univ (w j))
        _ = m * L := by simp
    -- Group `w : Fin m → ι` by total codeword length `ℓ ∈ Finset.range (m * L + 1)`
    have hgroup : ∑ w : Fin m → ι, (1 : ℝ) / (q : ℝ) ^ (∑ j : Fin m, (f (w j)).length) =
        ∑ ℓ ∈ Finset.range (m * L + 1),
          ((Finset.univ.filter (fun w : Fin m → ι => (∑ j : Fin m, (f (w j)).length) = ℓ)).card : ℝ) *
            ((1 : ℝ) / (q : ℝ) ^ ℓ) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun w : Fin m → ι => ∑ j : Fin m, (f (w j)).length)
        (t := Finset.range (m * L + 1)) (fun w _ => Finset.mem_range.mpr (by have := hlen_le w; omega))]
      apply Finset.sum_congr rfl
      intro ℓ _
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro w hw
      rw [(Finset.mem_filter.mp hw).2]
    -- Each length-`ℓ` bucket injects into `Fin ℓ → Fin q` by unique decodability, so has size `≤ q ^ ℓ`
    have hbucket : ∀ ℓ : ℕ,
        (Finset.univ.filter (fun w : Fin m → ι => (∑ j : Fin m, (f (w j)).length) = ℓ)).card ≤ q ^ ℓ := by
      intro ℓ
      let B := Finset.univ.filter (fun w : Fin m → ι => (∑ j : Fin m, (f (w j)).length) = ℓ)
      let encode : (Fin m → ι) → List (Fin q) := fun w => ((List.ofFn w).map f).flatten
      have henc_len : ∀ w ∈ B, (encode w).length = ℓ := by
        intro w hw
        dsimp only [encode]
        rw [List.length_flatten, List.map_map, List.map_ofFn, List.sum_ofFn]
        exact (Finset.mem_filter.mp hw).2
      let toVec : (Fin m → ι) → (Fin ℓ → Fin q) := fun w k =>
        if h : k.1 < (encode w).length then (encode w)[k.1]'h else ⟨0, by omega⟩
      have hinj : Set.InjOn toVec (B : Set (Fin m → ι)) := by
        intro w₁ hw₁ w₂ hw₂ hvec
        have hlen₁ : (encode w₁).length = ℓ := henc_len w₁ hw₁
        have hlen₂ : (encode w₂).length = ℓ := henc_len w₂ hw₂
        have henc_eq : encode w₁ = encode w₂ := by
          apply List.ext_getElem (hlen₁.trans hlen₂.symm)
          intro k hk₁ hk₂
          have hkℓ : k < ℓ := hlen₁ ▸ hk₁
          have hkv := congrFun hvec ⟨k, hkℓ⟩
          simpa [toVec, hk₁, hk₂] using hkv
        exact List.ofFn_injective (hf henc_eq)
      calc B.card = (B.image toVec).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ : Finset (Fin ℓ → Fin q)).card := Finset.card_le_card (Finset.subset_univ _)
        _ = q ^ ℓ := by simp
    rw [hexpand, hgroup]
    calc ∑ ℓ ∈ Finset.range (m * L + 1),
            ((Finset.univ.filter (fun w : Fin m → ι => (∑ j : Fin m, (f (w j)).length) = ℓ)).card : ℝ) *
              ((1 : ℝ) / (q : ℝ) ^ ℓ)
        ≤ ∑ _ℓ ∈ Finset.range (m * L + 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro ℓ _
          have hbR : ((Finset.univ.filter (fun w : Fin m → ι => (∑ j : Fin m, (f (w j)).length) = ℓ)).card : ℝ) ≤
              (q : ℝ) ^ ℓ := by exact_mod_cast hbucket ℓ
          have hqℓ : (0 : ℝ) < (q : ℝ) ^ ℓ := pow_pos hq_pos ℓ
          calc ((Finset.univ.filter (fun w : Fin m → ι => (∑ j : Fin m, (f (w j)).length) = ℓ)).card : ℝ) *
                ((1 : ℝ) / (q : ℝ) ^ ℓ)
              ≤ (q : ℝ) ^ ℓ * ((1 : ℝ) / (q : ℝ) ^ ℓ) :=
                mul_le_mul_of_nonneg_right hbR (by positivity)
            _ = 1 := by field_simp [hqℓ.ne']
      _ = (m * L + 1 : ℝ) := by simp [Finset.sum_const, Finset.card_range]
  -- If `S > 1`, quadratic growth of `(1 + δ)^m` beats linear `m * L + 1`
  by_contra hgt
  push Not at hgt
  set δ : ℝ := S - 1
  have hδ : 0 < δ := by linarith
  set m : ℕ := max 2 (⌈2 * ((L : ℝ) + 1) / δ ^ 2⌉₊ + 2)
  have hm2 : 2 ≤ m := le_max_left _ _
  have hm_big : 2 * ((L : ℝ) + 1) / δ ^ 2 + 1 < (m : ℝ) := by
    have h1 : 2 * ((L : ℝ) + 1) / δ ^ 2 ≤ (⌈2 * ((L : ℝ) + 1) / δ ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈2 * ((L : ℝ) + 1) / δ ^ 2⌉₊ + 2 ≤ m := le_max_right _ _
    have h3 : ((⌈2 * ((L : ℝ) + 1) / δ ^ 2⌉₊ + 2 : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr h2
    rw [Nat.cast_add, Nat.cast_ofNat] at h3
    linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hquad := one_add_pow_ge_quad hδ.le m
  have hS_eq : 1 + δ = S := by ring
  rw [hS_eq] at hquad
  have hbound := hpow_le m
  have hL_lt : (L : ℝ) + 1 < (((m : ℝ) - 1) / 2) * δ ^ 2 := by
    have hsub : 2 * ((L : ℝ) + 1) / δ ^ 2 < (m : ℝ) - 1 := by linarith
    have hmul := mul_lt_mul_of_pos_right hsub (sq_pos_of_pos hδ)
    have hcancel : (2 * ((L : ℝ) + 1) / δ ^ 2) * δ ^ 2 = 2 * ((L : ℝ) + 1) := by
      field_simp [hδ.ne']
    linarith
  have hmul_m : (m : ℝ) * ((L : ℝ) + 1) < (m : ℝ) * ((((m : ℝ) - 1) / 2) * δ ^ 2) :=
    mul_lt_mul_of_pos_left hL_lt hm_pos
  have hquad_gt : (m : ℝ) * (L : ℝ) + 1 < ((m : ℝ) * ((m : ℝ) - 1) / 2) * δ ^ 2 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
    nlinarith
  nlinarith

/-- Binary specialization of the Kraft–McMillan inequality (`q = 2`). -/
theorem kraft_mcmillan_binary {ι : Type*} [Fintype ι] (f : ι → List (Fin 2))
    (hf : IsUniquelyDecodable f) :
    ∑ i : ι, (1 : ℝ) / (2 : ℝ) ^ (f i).length ≤ 1 := by
  simpa using kraft_mcmillan_inequality (q := 2) (by omega) f hf

/-- Kraft inequality for prefix-free `q`-ary codes with nonempty codewords. -/
theorem kraft_prefix_free {ι : Type*} [Fintype ι] {q : ℕ} (hq : 2 ≤ q)
    (f : ι → List (Fin q)) (hf : IsPrefixFree f) (hne : ∀ i : ι, f i ≠ []) :
    ∑ i : ι, (1 : ℝ) / (q : ℝ) ^ (f i).length ≤ 1 :=
  kraft_mcmillan_inequality hq f (isUniquelyDecodable_of_isPrefixFree hf hne)

/-- Base-`q` MSB-first digit expansion of length `L` for `a : ℕ`. -/
private def toBaseQ (q : ℕ) (hq : 2 ≤ q) (L a : ℕ) : List (Fin q) :=
  List.ofFn (fun k : Fin L => ⟨(a / q ^ (L - 1 - k.1)) % q, Nat.mod_lt _ (by omega)⟩)

private lemma toBaseQ_length (q : ℕ) (hq : 2 ≤ q) (L a : ℕ) :
    (toBaseQ q hq L a).length = L := by
  simp [toBaseQ]

private lemma eq_of_toBaseQ_eq (q : ℕ) (hq : 2 ≤ q) :
    ∀ L a b : ℕ, a < q ^ L → b < q ^ L → toBaseQ q hq L a = toBaseQ q hq L b → a = b
  | 0, a, b, ha, hb, _ => by simp only [pow_zero] at ha hb; omega
  | L + 1, a, b, ha, hb, heq => by
    have hq0 : 0 < q := by omega
    have hdiv_lt_a : a / q < q ^ L := by
      rw [Nat.div_lt_iff_lt_mul hq0]
      simpa [pow_succ] using ha
    have hdiv_lt_b : b / q < q ^ L := by
      rw [Nat.div_lt_iff_lt_mul hq0]
      simpa [pow_succ] using hb
    have hmod : a % q = b % q := by
      have hget := congrArg (fun l => l[L]?) heq
      simp only [toBaseQ, List.getElem?_ofFn, lt_add_iff_pos_right, zero_lt_one, ↓reduceDIte,
        Nat.add_sub_cancel, Nat.sub_self, pow_zero, Nat.div_one, Option.some.injEq,
        Fin.mk.injEq] at hget
      exact hget
    have hdiv_eq : a / q = b / q := by
      apply eq_of_toBaseQ_eq q hq L (a / q) (b / q) hdiv_lt_a hdiv_lt_b
      apply List.ext_getElem (by simp [toBaseQ])
      intro k hk₁ hk₂
      simp only [toBaseQ, List.length_ofFn] at hk₁
      have hget := congrArg (fun l => l[k]?) heq
      have hk' : k < L + 1 := by omega
      simp only [toBaseQ, List.getElem?_ofFn, hk', ↓reduceDIte, Option.some.injEq,
        Fin.mk.injEq] at hget
      have hexp : L + 1 - 1 - k = (L - 1 - k) + 1 := by omega
      rw [hexp, pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at hget
      simp only [toBaseQ, List.getElem_ofFn, Fin.mk.injEq]
      exact hget
    have ha_rec := Nat.div_add_mod a q
    have hb_rec := Nat.div_add_mod b q
    rw [← ha_rec, ← hb_rec, hdiv_eq, hmod]

private lemma div_eq_of_toBaseQ_prefix (q : ℕ) (hq : 2 ≤ q) {L₁ L₂ a₁ a₂ : ℕ}
    (hL : L₁ ≤ L₂) (ha₁ : a₁ < q ^ L₁) (ha₂ : a₂ < q ^ L₂)
    (hpre : toBaseQ q hq L₁ a₁ <+: toBaseQ q hq L₂ a₂) :
    a₁ = a₂ / q ^ (L₂ - L₁) := by
  have hq0 : 0 < q := by omega
  have hdiv_lt : a₂ / q ^ (L₂ - L₁) < q ^ L₁ := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hq0 _), ← pow_add]
    have hadd : L₁ + (L₂ - L₁) = L₂ := by omega
    rwa [hadd]
  apply eq_of_toBaseQ_eq q hq L₁ a₁ (a₂ / q ^ (L₂ - L₁)) ha₁ hdiv_lt
  apply List.ext_getElem (by simp [toBaseQ])
  intro k hk₁ _
  simp only [toBaseQ, List.length_ofFn] at hk₁
  rcases hpre with ⟨s, hs⟩
  have hget := congrArg (fun l => l[k]?) hs
  have hk₂ : k < L₂ := by omega
  rw [List.getElem?_append_left (by simp [toBaseQ]; omega)] at hget
  simp only [toBaseQ, List.getElem?_ofFn, hk₁, hk₂, ↓reduceDIte, Option.some.injEq,
    Fin.mk.injEq] at hget
  have hexp : L₂ - 1 - k = (L₂ - L₁) + (L₁ - 1 - k) := by omega
  rw [hexp, pow_add, ← Nat.div_div_eq_div_mul] at hget
  simp only [toBaseQ, List.getElem_ofFn, Fin.mk.injEq]
  exact hget

/-- Existence of a sorting permutation `σ : Equiv.Perm (Fin n)` for any function `ℓ : Fin n → ℕ`. -/
private lemma exists_sort_perm : ∀ (n : ℕ) (ℓ : Fin n → ℕ),
    ∃ σ : Equiv.Perm (Fin n), Monotone (ℓ ∘ σ)
  | 0, _ => ⟨Equiv.refl _, fun i => Fin.elim0 i⟩
  | n + 1, ℓ => by
    -- Pick an index `i₀` achieving the minimum of `ℓ`
    obtain ⟨i₀, _, hi₀_min⟩ := Finset.exists_min_image Finset.univ ℓ Finset.univ_nonempty
    let τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i₀
    let ℓ' : Fin n → ℕ := fun k => ℓ (τ k.succ)
    obtain ⟨σ', hσ'_mono⟩ := exists_sort_perm n ℓ'
    -- Lift `σ' : Equiv.Perm (Fin n)` to fix `0` and permute `k.succ`
    let σLift : Equiv.Perm (Fin (n + 1)) :=
      { toFun := Fin.cases 0 (fun k => (σ' k).succ)
        invFun := Fin.cases 0 (fun k => (σ'.symm k).succ)
        left_inv := fun i => Fin.cases rfl (fun k => by simp) i
        right_inv := fun i => Fin.cases rfl (fun k => by simp) i }
    refine ⟨σLift.trans τ, ?_⟩
    intro a b hab
    cases a using Fin.cases with
    | zero =>
      simp only [Function.comp, Equiv.trans_apply, σLift, Equiv.coe_fn_mk, Fin.cases_zero,
        τ, Equiv.swap_apply_left]
      exact hi₀_min _ (Finset.mem_univ _)
    | succ a' =>
      cases b using Fin.cases with
      | zero => exact absurd hab (by simp)
      | succ b' =>
        have hle : a' ≤ b' := Fin.succ_le_succ_iff.mp hab
        simpa [Function.comp, Equiv.trans_apply, σLift, ℓ'] using hσ'_mono hle

/-- **Kraft's Converse (Constructive Existence of Prefix-Free Codes):**
Given `q ≥ 2` and target lengths `ℓ : Fin n → ℕ` satisfying Kraft's inequality
`∑ i, 1 / q ^ (ℓ i) ≤ 1`, there exists a prefix-free `q`-ary code `f : Fin n → List (Fin q)`
with `(f i).length = ℓ i` for every `i`. -/
theorem kraft_exists_prefix_free {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (ℓ : Fin n → ℕ)
    (hkraft : ∑ i : Fin n, (1 : ℝ) / (q : ℝ) ^ (ℓ i) ≤ 1) :
    ∃ f : Fin n → List (Fin q), IsPrefixFree f ∧ ∀ i : Fin n, (f i).length = ℓ i := by
  obtain ⟨σ, hmono⟩ := exists_sort_perm n ℓ
  let L : Fin n → ℕ := ℓ ∘ σ
  have hkraftL : ∑ i : Fin n, (1 : ℝ) / (q : ℝ) ^ (L i) ≤ 1 := by
    have heq : ∑ i : Fin n, (1 : ℝ) / (q : ℝ) ^ (L i) =
        ∑ i : Fin n, (1 : ℝ) / (q : ℝ) ^ (ℓ i) :=
      Equiv.sum_comp σ (fun i => (1 : ℝ) / (q : ℝ) ^ (ℓ i))
    linarith
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  let a : Fin n → ℕ := fun i => ∑ j ∈ Finset.univ.filter (· < i), q ^ (L i - L j)
  have ha_lt : ∀ i : Fin n, a i < q ^ (L i) := by
    intro i
    have hdiv : (a i : ℝ) / (q : ℝ) ^ (L i) =
        ∑ j ∈ Finset.univ.filter (· < i), (1 : ℝ) / (q : ℝ) ^ (L j) := by
      dsimp only [a]
      rw [Nat.cast_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < i := (Finset.mem_filter.mp hj).2
      have hLj : L j ≤ L i := hmono hjlt.le
      rw [Nat.cast_pow]
      have hqLj : (0 : ℝ) < (q : ℝ) ^ (L j) := pow_pos hq_pos _
      have hqLi : (0 : ℝ) < (q : ℝ) ^ (L i) := pow_pos hq_pos _
      rw [div_eq_div_iff hqLi.ne' hqLj.ne', one_mul, ← pow_add]
      have hadd : L i - L j + L j = L i := by omega
      rw [hadd]
    have hsum_lt : (∑ j ∈ Finset.univ.filter (· < i), (1 : ℝ) / (q : ℝ) ^ (L j)) < 1 := by
      have hle_sub : (∑ j ∈ Finset.univ.filter (· < i), (1 : ℝ) / (q : ℝ) ^ (L j)) +
          (1 : ℝ) / (q : ℝ) ^ (L i) ≤ ∑ j : Fin n, (1 : ℝ) / (q : ℝ) ^ (L j) := by
        have hnot : i ∉ Finset.univ.filter (· < i) := by simp
        rw [add_comm, ← Finset.sum_insert (f := fun j : Fin n => (1 : ℝ) / (q : ℝ) ^ (L j)) hnot]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
      have hterm_pos : (0 : ℝ) < (1 : ℝ) / (q : ℝ) ^ (L i) := by positivity
      linarith
    have ha_ltR : (a i : ℝ) < (q : ℝ) ^ (L i) := by
      have h1 : (a i : ℝ) / (q : ℝ) ^ (L i) < 1 := hdiv.symm ▸ hsum_lt
      exact (div_lt_one (pow_pos hq_pos _)).mp h1
    exact_mod_cast ha_ltR
  have ha_step : ∀ {i k : Fin n}, i < k → (a i + 1) * q ^ (L k - L i) ≤ a k := by
    intro i k hik
    have hsub : insert i (Finset.univ.filter (· < i)) ⊆ Finset.univ.filter (· < k) := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjlt
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hik⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hjlt).2 hik⟩
    have hnot : i ∉ Finset.univ.filter (· < i) := by simp
    calc (a i + 1) * q ^ (L k - L i)
        = (∑ j ∈ Finset.univ.filter (· < i), q ^ (L i - L j) * q ^ (L k - L i)) + q ^ (L k - L i) := by
          rw [add_mul, one_mul, Finset.sum_mul]
      _ = (∑ j ∈ Finset.univ.filter (· < i), q ^ (L k - L j)) + q ^ (L k - L i) := by
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < i := (Finset.mem_filter.mp hj).2
          have h1 : L j ≤ L i := hmono hjlt.le
          have h2 : L i ≤ L k := hmono hik.le
          rw [← pow_add]
          congr 1
          omega
      _ = ∑ j ∈ insert i (Finset.univ.filter (· < i)), q ^ (L k - L j) := by
          rw [Finset.sum_insert hnot, add_comm]
      _ ≤ a k := Finset.sum_le_sum_of_subset hsub
  let g : Fin n → List (Fin q) := fun i => toBaseQ q hq (L i) (a i)
  have hg_pre : IsPrefixFree g := by
    intro i k hik hpre
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · have hdiv_eq := div_eq_of_toBaseQ_prefix q hq (hmono hlt.le) (ha_lt i) (ha_lt k) hpre
      have hge := ha_step hlt
      have hdiv_ge : a i + 1 ≤ a k / q ^ (L k - L i) :=
        (Nat.le_div_iff_mul_le (pow_pos (by omega : 0 < q) _)).mpr hge
      dsimp only [L] at hdiv_ge
      omega
    · have hlen_le : L i ≤ L k := by
        have := hpre.length_le
        simpa [g, toBaseQ_length] using this
      have hLk_le : L k ≤ L i := hmono hgt.le
      have hLeq : L i = L k := le_antisymm hlen_le hLk_le
      have hdiv_eq := div_eq_of_toBaseQ_prefix q hq hlen_le (ha_lt i) (ha_lt k) hpre
      have hge := ha_step hgt
      rw [hLeq, Nat.sub_self, pow_zero, Nat.div_one] at hdiv_eq
      rw [hLeq, Nat.sub_self, pow_zero, mul_one] at hge
      omega
  refine ⟨fun i => g (σ.symm i), ?_, ?_⟩
  · intro i j hij
    exact hg_pre (σ.symm i) (σ.symm j) (fun h => hij (σ.symm.injective h))
  · intro i
    simp [g, toBaseQ_length, L]

/-- **Shannon Source Coding Lower Bound:**
For any probability distribution `P : ι → ℝ` and any uniquely decodable `q`-ary code
`f : ι → List (Fin q)` (`q ≥ 2`), the expected codeword length is at least `H(P) / log q`. -/
theorem shannon_source_coding_lower_bound {ι : Type*} [Fintype ι] {q : ℕ} (hq : 2 ≤ q)
    {P : ι → ℝ} (hP : IsProbDist P) (f : ι → List (Fin q)) (hf : IsUniquelyDecodable f) :
    shannonEntropy P / Real.log (q : ℝ) ≤ ∑ i : ι, P i * ((f i).length : ℝ) := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hkraft := kraft_mcmillan_inequality hq f hf
  set Z : ℝ := ∑ i : ι, (1 : ℝ) / (q : ℝ) ^ (f i).length
  have hZ_pos : 0 < Z := by
    have hcard : 0 < Fintype.card ι := isProbDist_card_pos hP
    obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp hcard
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (q : ℝ) ^ (f i₀).length)
      (Finset.single_le_sum (f := fun i : ι => (1 : ℝ) / (q : ℝ) ^ (f i).length)
        (fun i _ => by positivity) (Finset.mem_univ i₀))
  let Q : ι → ℝ := fun i => ((1 : ℝ) / (q : ℝ) ^ (f i).length) / Z
  have hQ : IsProbDist Q := by
    refine ⟨fun i => by dsimp only [Q]; positivity, ?_⟩
    simp only [Q, ← Finset.sum_div]
    exact div_self hZ_pos.ne'
  have hkl : 0 ≤ klDiv P Q := gibbs_inequality hP hQ (fun i _ => by dsimp only [Q]; positivity)
  have hkl_eq : klDiv P Q =
      -shannonEntropy P + (∑ i : ι, P i * ((f i).length : ℝ)) * Real.log (q : ℝ) + Real.log Z := by
    unfold klDiv shannonEntropy
    have hterm : ∀ i : ι, P i * Real.log (P i / Q i) =
        P i * Real.log (P i) + P i * ((f i).length : ℝ) * Real.log (q : ℝ) + P i * Real.log Z := by
      intro i
      by_cases hpi : P i = 0
      · simp [hpi]
      · have hpi_pos : 0 < P i := lt_of_le_of_ne (hP.1 i) (Ne.symm hpi)
        have hqi_pos : 0 < Q i := by dsimp only [Q]; positivity
        have hdiv : P i / Q i = P i * ((q : ℝ) ^ (f i).length * Z) := by
          dsimp only [Q]; field_simp [hZ_pos.ne', (pow_pos hq_pos (f i).length).ne']
        rw [hdiv, Real.log_mul hpi_pos.ne' (by positivity),
            Real.log_mul (pow_pos hq_pos (f i).length).ne' hZ_pos.ne', Real.log_pow]
        ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, hP.2, one_mul, Finset.sum_neg_distrib]
    ring
  have hlogZ : Real.log Z ≤ 0 := Real.log_nonpos hZ_pos.le hkraft
  rw [div_le_iff₀ hlogq]
  linarith

/-- Binary entropy function in nats: `h(p) = -(p log p + (1 - p) log (1 - p))`. -/
def binEntropyNat (p : ℝ) : ℝ :=
  -(p * Real.log p + (1 - p) * Real.log (1 - p))

/-- Binary entropy function in bits: `H_2(p) = h(p) / log 2`. -/
def binEntropy2 (p : ℝ) : ℝ :=
  binEntropyNat p / Real.log 2

lemma binEntropy2_symm (p : ℝ) : binEntropy2 (1 - p) = binEntropy2 p := by
  unfold binEntropy2 binEntropyNat
  ring_nf

lemma binEntropy2_half : binEntropy2 (1 / 2) = 1 := by
  unfold binEntropy2 binEntropyNat
  have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h1, one_div, Real.log_inv]
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp [hlog2]
  ring

lemma binEntropy2_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ binEntropy2 p := by
  unfold binEntropy2 binEntropyNat
  apply div_nonneg _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have h1 : p * Real.log p ≤ 0 := by
    by_cases h : p = 0
    · simp [h]
    · exact mul_nonpos_of_nonneg_of_nonpos hp0 (Real.log_nonpos hp0 hp1)
  have h2 : (1 - p) * Real.log (1 - p) ≤ 0 := by
    by_cases h : 1 - p = 0
    · simp [h]
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (Real.log_nonpos (by linarith) (by linarith))
  linarith

lemma binEntropy2_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : binEntropy2 p ≤ 1 := by
  let P : Bool → ℝ := fun b => if b then p else 1 - p
  have hP : IsProbDist P := by
    refine ⟨fun b => by cases b <;> simp [P] <;> linarith, ?_⟩
    simp [P]
  have hHP : shannonEntropy P = binEntropyNat p := by
    unfold shannonEntropy binEntropyNat
    simp [P]
  have hle := shannonEntropy_le_log_card hP
  rw [hHP, Fintype.card_bool, Nat.cast_ofNat] at hle
  unfold binEntropy2
  exact (div_le_one (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hle

lemma two_rpow_binEntropy2_eq_exp (n : ℕ) (p : ℝ) :
    (2 : ℝ) ^ ((n : ℝ) * binEntropy2 p) = Real.exp ((n : ℝ) * binEntropyNat p) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  unfold binEntropy2
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp [hlog2]

/-- **Binary Entropy Bound on Binomial Tails:**
For every `n : ℕ` and every `p ∈ [0, 1/2]`,
`∑_{k ≤ p n} C(n, k) ≤ 2^{n H_2(p)}`. -/
theorem sum_choose_le_two_rpow_binEntropy2 (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp_half : p ≤ 1 / 2) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ p * (n : ℝ)), (Nat.choose n k : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) * binEntropy2 p) := by
  rw [two_rpow_binEntropy2_eq_exp]
  by_cases h0 : p = 0
  · subst h0
    have hflt : (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ 0 * (n : ℝ)) = {0} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, zero_mul]
      constructor
      · rintro ⟨_, hk⟩
        have : k ≤ 0 := by exact_mod_cast hk
        omega
      · rintro rfl
        exact ⟨by omega, by simp⟩
    rw [hflt, Finset.sum_singleton, Nat.choose_zero_right, Nat.cast_one]
    simp [binEntropyNat]
  · have hp_pos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm h0)
    have h1p_pos : 0 < 1 - p := by linarith
    have hratio_pos : 0 < p / (1 - p) := div_pos hp_pos h1p_pos
    have hratio_le1 : p / (1 - p) ≤ 1 := (div_le_one h1p_pos).mpr (by linarith)
    -- `1 = (p + (1 - p))^n = ∑ C(n, k) p^k (1 - p)^{n - k}`
    have hbinom : (1 : ℝ) = ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
      have h1 : (p + (1 - p)) ^ n = 1 := by rw [add_sub_cancel, one_pow]
      conv_lhs => rw [← h1, add_pow]
      apply Finset.sum_congr rfl
      intro k _
      ring
    -- Every term with `k ≤ p n` satisfies `p^k (1 - p)^{n - k} ≥ exp (-n h(p))`
    have hterm_ge : ∀ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ p * (n : ℝ)),
        (Nat.choose n k : ℝ) * Real.exp (-((n : ℝ) * binEntropyNat p)) ≤
          (Nat.choose n k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
      intro k hk
      have hk_le_n : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
      have hk_le_pn : (k : ℝ) ≤ p * (n : ℝ) := (Finset.mem_filter.mp hk).2
      have hpow_eq : p ^ k * (1 - p) ^ (n - k) = (1 - p) ^ n * (p / (1 - p)) ^ k := by
        rw [div_pow]
        have hsplit : (1 - p) ^ n = (1 - p) ^ (n - k) * (1 - p) ^ k := by
          rw [← pow_add]; congr 1; omega
        rw [hsplit]
        field_simp [(pow_pos h1p_pos k).ne']
      have hexp_eq : Real.exp (-((n : ℝ) * binEntropyNat p)) =
          (1 - p) ^ n * (p / (1 - p)) ^ (p * (n : ℝ)) := by
        unfold binEntropyNat
        rw [Real.rpow_def_of_pos hratio_pos, Real.log_div hp_pos.ne' h1p_pos.ne',
            ← Real.exp_log (pow_pos h1p_pos n), Real.log_pow, ← Real.exp_add]
        congr 1
        ring
      have hrpow_le : (p / (1 - p)) ^ (p * (n : ℝ)) ≤ (p / (1 - p)) ^ k := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge hratio_pos hratio_le1 hk_le_pn
      rw [hexp_eq, mul_assoc, hpow_eq]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hrpow_le (pow_nonneg h1p_pos.le n)) (Nat.cast_nonneg _)
    have hsum_le : (∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ p * (n : ℝ)),
          (Nat.choose n k : ℝ)) * Real.exp (-((n : ℝ) * binEntropyNat p)) ≤ 1 := by
      rw [Finset.sum_mul, hbinom]
      exact (Finset.sum_le_sum hterm_ge).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => by positivity))
    have hexp_pos : 0 < Real.exp ((n : ℝ) * binEntropyNat p) := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_right hsum_le hexp_pos.le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul] at hmul
    exact hmul

/-- Single binomial coefficient upper bound via binary entropy:
for all `n ≥ 1` and `k ≤ n`, `C(n, k) ≤ 2^{n H_2(k / n)}`. -/
theorem choose_le_two_rpow_binEntropy2 {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    (Nat.choose n k : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * binEntropy2 ((k : ℝ) / (n : ℝ))) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  by_cases hhalf : (k : ℝ) / (n : ℝ) ≤ 1 / 2
  · have hmem : k ∈ (Finset.range (n + 1)).filter (fun j : ℕ => (j : ℝ) ≤ ((k : ℝ) / (n : ℝ)) * (n : ℝ)) := by
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [div_mul_cancel₀ _ hn_pos.ne']
    exact (Finset.single_le_sum (fun j _ => Nat.cast_nonneg (Nat.choose n j)) hmem).trans
      (sum_choose_le_two_rpow_binEntropy2 n (by positivity) hhalf)
  · push Not at hhalf
    have hkn_le : ((n - k : ℕ) : ℝ) / (n : ℝ) ≤ 1 / 2 := by
      rw [Nat.cast_sub hk, sub_div, div_self hn_pos.ne']
      linarith
    have hsymm : binEntropy2 ((k : ℝ) / (n : ℝ)) = binEntropy2 (((n - k : ℕ) : ℝ) / (n : ℝ)) := by
      rw [Nat.cast_sub hk, sub_div, div_self hn_pos.ne', binEntropy2_symm]
    rw [hsymm, ← Nat.choose_symm hk]
    have hmem : n - k ∈ (Finset.range (n + 1)).filter
        (fun j : ℕ => (j : ℝ) ≤ (((n - k : ℕ) : ℝ) / (n : ℝ)) * (n : ℝ)) := by
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [div_mul_cancel₀ _ hn_pos.ne']
    exact (Finset.single_le_sum (fun j _ => Nat.cast_nonneg (Nat.choose n j)) hmem).trans
      (sum_choose_le_two_rpow_binEntropy2 n (by positivity) hkn_le)

end KraftAndBinaryEntropy

/-! ## Section 4: Classical Coding-Theory Bounds & General `F_p` MacWilliams Identity -/

section CodingTheory

/-- Hamming distance between two codewords `x, y : Fin n → α`. -/
def hammingDist {n : ℕ} {α : Type*} [DecidableEq α] (x y : Fin n → α) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card

/-- Hamming weight of a codeword `x : Fin n → α` (number of nonzero coordinates). -/
def hammingWeight {n : ℕ} {α : Type*} [Zero α] [DecidableEq α] (x : Fin n → α) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).card

/-- Closed Hamming ball of radius `r` centered at `x : Fin n → α`. -/
def hammingBall {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (x : Fin n → α) (r : ℕ) : Finset (Fin n → α) :=
  Finset.univ.filter (fun y => hammingDist x y ≤ r)

lemma hammingDist_self {n : ℕ} {α : Type*} [DecidableEq α] (x : Fin n → α) :
    hammingDist x x = 0 := by
  simp [hammingDist]

lemma hammingDist_comm {n : ℕ} {α : Type*} [DecidableEq α] (x y : Fin n → α) :
    hammingDist x y = hammingDist y x := by
  unfold hammingDist
  congr 1; ext i; simp [ne_comm]

lemma hammingDist_eq_zero {n : ℕ} {α : Type*} [DecidableEq α] {x y : Fin n → α} :
    hammingDist x y = 0 ↔ x = y := by
  unfold hammingDist
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h; funext i; by_contra hne; exact h (Finset.mem_univ i) hne
  · rintro rfl i _; simp

lemma hammingDist_triangle {n : ℕ} {α : Type*} [DecidableEq α] (x y z : Fin n → α) :
    hammingDist x z ≤ hammingDist x y + hammingDist y z := by
  unfold hammingDist
  have hsub : Finset.univ.filter (fun i : Fin n => x i ≠ z i) ⊆
      Finset.univ.filter (fun i : Fin n => x i ≠ y i) ∪
      Finset.univ.filter (fun i : Fin n => y i ≠ z i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
    by_cases hxy : x i = y i
    · right; exact hxy ▸ hi
    · left; exact hxy
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

lemma hammingDist_le_length {n : ℕ} {α : Type*} [DecidableEq α] (x y : Fin n → α) :
    hammingDist x y ≤ n := by
  calc hammingDist x y ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-- Exact cardinality of a Hamming ball of radius `r` in `(Fin n → α)`:
`|B(x, r)| = ∑_{k=0}^r C(n, k) (|α| - 1)^k`. -/
theorem card_hammingBall {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (x : Fin n → α) (r : ℕ) :
    (hammingBall x r).card =
      ∑ k ∈ Finset.range (r + 1), Nat.choose n k * (Fintype.card α - 1) ^ k := by
  -- Fiber `hammingBall x r` by the exact support set `S = {i | x i ≠ y i}`
  let supp : (Fin n → α) → Finset (Fin n) := fun y => Finset.univ.filter (fun i => x i ≠ y i)
  have hfiber_card : ∀ S : Finset (Fin n),
      ((hammingBall x r).filter (fun y => supp y = S)).card =
        if S.card ≤ r then (Fintype.card α - 1) ^ S.card else 0 := by
    intro S
    split_ifs with hSr
    · -- Explicit bijection with `∀ i : S, {a : α // a ≠ x i.1}`
      let T := (hammingBall x r).filter (fun y => supp y = S)
      let e : T ≃ (∀ i : S, {a : α // a ≠ x i.1}) :=
        { toFun := fun y i =>
            ⟨y.1 i.1, by
              have hsupp := (Finset.mem_filter.mp y.2).2
              have hi : i.1 ∈ supp y.1 := hsupp.symm ▸ i.2
              exact (Finset.mem_filter.mp hi).2.symm⟩
          invFun := fun f =>
            ⟨fun i => if hi : i ∈ S then (f ⟨i, hi⟩).1 else x i, by
              have hsupp : supp (fun i => if hi : i ∈ S then (f ⟨i, hi⟩).1 else x i) = S := by
                ext i
                simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
                by_cases hi : i ∈ S
                · simp [hi, (f ⟨i, hi⟩).2.symm]
                · simp [hi]
              exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                by change (supp _).card ≤ r; rw [hsupp]; exact hSr⟩, hsupp⟩⟩
          left_inv := by
            intro ⟨y, hy⟩
            ext i
            have hsupp := (Finset.mem_filter.mp hy).2
            by_cases hi : i ∈ S
            · simp [hi]
            · simp only [dif_neg hi]
              have hnot : i ∉ supp y := hsupp.symm ▸ hi
              simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnot
              exact hnot
          right_inv := by
            intro f
            funext ⟨i, hi⟩
            ext
            simp [hi] }
      have hcard_T : T.card = Fintype.card (∀ i : S, {a : α // a ≠ x i.1}) := by
        rw [← Fintype.card_coe]; exact Fintype.card_congr e
      rw [hcard_T, Fintype.card_pi]
      have hsub_card : ∀ i : S, Fintype.card {a : α // a ≠ x i.1} = Fintype.card α - 1 := by
        intro i
        rw [Fintype.card_subtype_compl]
        simp
      simp_rw [hsub_card, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y hy hsupp
      have hle : (supp y).card ≤ r := (Finset.mem_filter.mp hy).2
      rw [hsupp] at hle
      exact hSr hle
  have hsum_powerset : (hammingBall x r).card =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((hammingBall x r).filter (fun y => supp y = S)).card := by
    conv_lhs => rw [Finset.card_eq_sum_ones]
    rw [← Finset.sum_fiberwise_of_maps_to (g := supp)
          (t := (Finset.univ : Finset (Fin n)).powerset)
          (fun _ _ => Finset.mem_powerset.mpr (Finset.subset_univ _))]
    apply Finset.sum_congr rfl
    intro S _
    rw [Finset.card_eq_sum_ones]
  rw [hsum_powerset]
  simp_rw [hfiber_card]
  rw [← Finset.sum_filter]
  -- Group `S` with `S.card ≤ r` by `k = S.card ∈ Finset.range (r + 1)`
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.range (r + 1))
    (fun S hS => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hS).2))]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hflt_eq : (((Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ r)).filter
      (fun S => S.card = k)) = (Finset.univ : Finset (Fin n)).powersetCard k := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.mem_powersetCard]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h ▸ hk_le, h⟩⟩
  rw [hflt_eq]
  calc ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (Fintype.card α - 1) ^ S.card
      = ∑ _S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (Fintype.card α - 1) ^ k :=
        Finset.sum_congr rfl fun S hS => by rw [(Finset.mem_powersetCard.mp hS).2]
    _ = Nat.choose n k * (Fintype.card α - 1) ^ k := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

private lemma card_filter_add_not {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  calc ∑ x ∈ s, ((if p x then 1 else 0) + (if ¬ p x then 1 else 0))
      = ∑ _x ∈ s, 1 := Finset.sum_congr rfl fun x _ => by by_cases h : p x <;> simp [h]
    _ = s.card := by simp

/-- **Singleton Bound:**
Any `q`-ary code `C ⊆ α^n` with minimum distance `d` (`1 ≤ d ≤ n`) satisfies
`|C| ≤ |α|^{n - d + 1}`. -/
theorem singleton_bound {n d : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hd1 : 1 ≤ d) (hdn : d ≤ n) (C : Finset (Fin n → α))
    (hdist : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) :
    C.card ≤ (Fintype.card α) ^ (n - d + 1) := by
  let m : ℕ := n - d + 1
  let proj : (Fin n → α) → (Fin m → α) := fun x i => x ⟨i.1, by omega⟩
  have hinj : Set.InjOn proj (C : Set (Fin n → α)) := by
    intro x hx y hy hxy
    by_contra hne
    have hge := hdist x hx y hy hne
    have hsub : Finset.univ.filter (fun i : Fin n => x i ≠ y i) ⊆
        Finset.univ.filter (fun i : Fin n => m ≤ i.1) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_contra hlt
      push Not at hlt
      have heq := congrFun hxy ⟨i.1, hlt⟩
      exact hi heq
    have hcard_le : (Finset.univ.filter (fun i : Fin n => m ≤ i.1)).card ≤ d - 1 := by
      have hcompl : (Finset.univ.filter (fun i : Fin n => i.1 < m)).card = m := by
        let e : Fin m ↪ Fin n := ⟨fun i => ⟨i.1, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
        have himg : Finset.univ.filter (fun i : Fin n => i.1 < m) = Finset.univ.map e := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, e]
          constructor
          · intro hi; exact ⟨⟨i.1, hi⟩, Fin.ext rfl⟩
          · rintro ⟨j, rfl⟩; exact j.isLt
        rw [himg, Finset.card_map, Finset.card_univ, Fintype.card_fin]
      have htot := card_filter_add_not (Finset.univ : Finset (Fin n)) (fun i : Fin n => i.1 < m)
      have hneg : (Finset.univ.filter (fun i : Fin n => ¬ i.1 < m)) =
          Finset.univ.filter (fun i : Fin n => m ≤ i.1) := by
        ext i; simp [not_lt]
      rw [hcompl, hneg, Finset.card_univ, Fintype.card_fin] at htot
      omega
    have hlt_d : hammingDist x y ≤ d - 1 := (Finset.card_le_card hsub).trans hcard_le
    omega
  calc C.card = (C.image proj).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Fin m → α)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = (Fintype.card α) ^ m := by simp

/-- **Hamming Sphere-Packing Bound:**
If `C ⊆ α^n` has minimum distance `d ≥ 2 t + 1`, then Hamming balls of radius `t` around
codewords are pairwise disjoint, giving
`|C| * (∑_{k=0}^t C(n, k) (|α| - 1)^k) ≤ |α|^n`. -/
theorem hamming_sphere_packing_bound {n d t : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (ht : 2 * t + 1 ≤ d) (C : Finset (Fin n → α))
    (hdist : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) :
    C.card * (∑ k ∈ Finset.range (t + 1), Nat.choose n k * (Fintype.card α - 1) ^ k) ≤
      (Fintype.card α) ^ n := by
  have hdisj : Set.PairwiseDisjoint (C : Set (Fin n → α)) (fun c => hammingBall c t) := by
    intro c₁ hc₁ c₂ hc₂ hne
    change Disjoint (hammingBall c₁ t) (hammingBall c₂ t)
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    have h1 : hammingDist c₁ z ≤ t := (Finset.mem_filter.mp hz₁).2
    have h2 : hammingDist c₂ z ≤ t := (Finset.mem_filter.mp hz₂).2
    have htri := hammingDist_triangle c₁ z c₂
    rw [hammingDist_comm z c₂] at htri
    have hge := hdist c₁ hc₁ c₂ hc₂ hne
    omega
  calc C.card * (∑ k ∈ Finset.range (t + 1), Nat.choose n k * (Fintype.card α - 1) ^ k)
      = ∑ c ∈ C, (hammingBall c t).card := by
        rw [← smul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_congr rfl fun c _ => (card_hammingBall c t).symm
    _ = (C.biUnion (fun c => hammingBall c t)).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset (Fin n → α)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = (Fintype.card α) ^ n := by simp

/-- **Gilbert–Varshamov Lower Bound:**
For every finite alphabet `α`, block length `n`, and minimum distance `d ≥ 1`, there exists
a code `C ⊆ α^n` of minimum distance `≥ d` satisfying
`|α|^n ≤ |C| * (∑_{k=0}^{d-1} C(n, k) (|α| - 1)^k)`. -/
theorem gilbert_varshamov_bound {n d : ℕ} (hd : 1 ≤ d) {α : Type*} [Fintype α] [DecidableEq α] :
    ∃ C : Finset (Fin n → α),
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) ∧
      (Fintype.card α) ^ n ≤
        C.card * (∑ k ∈ Finset.range d, Nat.choose n k * (Fintype.card α - 1) ^ k) := by
  let validCodes : Finset (Finset (Fin n → α)) :=
    Finset.univ.filter (fun C => ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y)
  have hne : validCodes.Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ hx => absurd hx (Finset.notMem_empty _)⟩⟩
  obtain ⟨C, hC_mem, hC_max⟩ := Finset.exists_max_image validCodes Finset.card hne
  have hC_dist : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := (Finset.mem_filter.mp hC_mem).2
  -- Maximality implies the balls of radius `d - 1` around `C` cover the entire space `α^n`
  have hcover : (Finset.univ : Finset (Fin n → α)) ⊆ C.biUnion (fun c => hammingBall c (d - 1)) := by
    intro y _
    by_contra hnot
    have hfar : ∀ c ∈ C, d ≤ hammingDist c y := by
      intro c hc
      by_contra hlt
      push Not at hlt
      exact hnot (Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)
    have hy_notC : y ∉ C := by
      intro hyC
      have := hfar y hyC
      rw [hammingDist_self] at this
      omega
    have hins_valid : insert y C ∈ validCodes := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro u hu v hv huv
      rcases Finset.mem_insert.mp hu with rfl | huC <;> rcases Finset.mem_insert.mp hv with rfl | hvC
      · exact absurd rfl huv
      · rw [hammingDist_comm]; exact hfar v hvC
      · exact hfar u huC
      · exact hC_dist u huC v hvC huv
    have hle := hC_max (insert y C) hins_valid
    rw [Finset.card_insert_of_notMem hy_notC] at hle
    omega
  refine ⟨C, hC_dist, ?_⟩
  have hrange : d - 1 + 1 = d := by omega
  calc (Fintype.card α) ^ n
      = (Finset.univ : Finset (Fin n → α)).card := by simp
    _ ≤ (C.biUnion (fun c => hammingBall c (d - 1))).card := Finset.card_le_card hcover
    _ ≤ ∑ c ∈ C, (hammingBall c (d - 1)).card := Finset.card_biUnion_le
    _ = ∑ _c ∈ C, (∑ k ∈ Finset.range d, Nat.choose n k * (Fintype.card α - 1) ^ k) :=
        Finset.sum_congr rfl fun c _ => by rw [card_hammingBall, hrange]
    _ = C.card * (∑ k ∈ Finset.range d, Nat.choose n k * (Fintype.card α - 1) ^ k) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- **Plotkin Bound (general `q`-ary alphabets):**
If `C ⊆ α^n` (`q = |α|`) has minimum distance `d` satisfying `(q - 1) * n < q * d`, then
`|C| ≤ q * d / (q * d - (q - 1) * n)`. -/
theorem plotkin_bound {n d : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hplot : ((Fintype.card α : ℝ) - 1) * (n : ℝ) < (Fintype.card α : ℝ) * (d : ℝ))
    (C : Finset (Fin n → α))
    (hdist : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) :
    (C.card : ℝ) ≤ (Fintype.card α : ℝ) * (d : ℝ) /
      ((Fintype.card α : ℝ) * (d : ℝ) - ((Fintype.card α : ℝ) - 1) * (n : ℝ)) := by
  set q : ℕ := Fintype.card α
  have hden : 0 < (q : ℝ) * (d : ℝ) - ((q : ℝ) - 1) * (n : ℝ) := by linarith
  rw [le_div_iff₀ hden]
  by_cases hC0 : C.card = 0
  · rw [hC0]; simp only [Nat.cast_zero, zero_mul]; positivity
  · have hq_pos : 0 < q := by
      obtain ⟨c, _⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hC0)
      by_cases hn0 : n = 0
      · subst hn0
        by_contra hq0
        have : q = 0 := by omega
        simp [this] at hplot
      · exact Fintype.card_pos_iff.mpr ⟨c ⟨0, Nat.pos_of_ne_zero hn0⟩⟩
    have hq_posR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
    -- Double-count `S := ∑ c₁ ∈ C, ∑ c₂ ∈ C, hammingDist c₁ c₂`
    let S : ℕ := ∑ c₁ ∈ C, ∑ c₂ ∈ C, hammingDist c₁ c₂
    -- Lower bound: `|C| * (|C| - 1) * d ≤ S`
    have hS_lower : C.card * (C.card - 1) * d ≤ S := by
      dsimp only [S]
      have hrow : ∀ c₁ ∈ C, (C.card - 1) * d ≤ ∑ c₂ ∈ C, hammingDist c₁ c₂ := by
        intro c₁ hc₁
        calc (C.card - 1) * d
            = ∑ _c₂ ∈ C.erase c₁, d := by
              rw [Finset.sum_const, Finset.card_erase_of_mem hc₁, smul_eq_mul]
          _ ≤ ∑ c₂ ∈ C.erase c₁, hammingDist c₁ c₂ :=
              Finset.sum_le_sum fun c₂ hc₂ =>
                hdist c₁ hc₁ c₂ (Finset.mem_of_mem_erase hc₂) (Finset.ne_of_mem_erase hc₂).symm
          _ ≤ ∑ c₂ ∈ C, hammingDist c₁ c₂ :=
              Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
      calc C.card * (C.card - 1) * d = ∑ _c₁ ∈ C, (C.card - 1) * d := by
            rw [Finset.sum_const, smul_eq_mul, mul_assoc]
        _ ≤ ∑ c₁ ∈ C, ∑ c₂ ∈ C, hammingDist c₁ c₂ := Finset.sum_le_sum hrow
    -- Upper bound: `q * S ≤ (q - 1) * n * |C|^2` via coordinate Cauchy–Schwarz
    have hS_eq : S = ∑ i : Fin n, (C.card ^ 2 - ∑ a : α, (C.filter (fun c => c i = a)).card ^ 2) := by
      have hcoord : ∀ i : Fin n,
          (∑ c₁ ∈ C, ∑ c₂ ∈ C, if c₁ i ≠ c₂ i then 1 else 0) =
            C.card ^ 2 - ∑ a : α, (C.filter (fun c => c i = a)).card ^ 2 := by
        intro i
        have htot : (∑ c₁ ∈ C, ∑ c₂ ∈ C, ((if c₁ i ≠ c₂ i then 1 else 0) +
              (if c₁ i = c₂ i then 1 else 0))) = C.card ^ 2 := by
          have h1 : ∀ c₁ c₂ : Fin n → α,
              (if c₁ i ≠ c₂ i then 1 else 0) + (if c₁ i = c₂ i then 1 else 0) = 1 := by
            intro c₁ c₂; by_cases h : c₁ i = c₂ i <;> simp [h]
          simp_rw [h1, Finset.sum_const, smul_eq_mul, mul_one, sq]
        have heq_cnt : (∑ c₁ ∈ C, ∑ c₂ ∈ C, if c₁ i = c₂ i then 1 else 0) =
            ∑ a : α, (C.filter (fun c => c i = a)).card ^ 2 := by
          calc ∑ c₁ ∈ C, ∑ c₂ ∈ C, (if c₁ i = c₂ i then 1 else 0)
              = ∑ c₁ ∈ C, (C.filter (fun c₂ => c₂ i = c₁ i)).card := by
                apply Finset.sum_congr rfl; intro c₁ _
                rw [Finset.card_filter]
                apply Finset.sum_congr rfl; intro c₂ _
                by_cases h : c₁ i = c₂ i <;> simp [h, eq_comm]
            _ = ∑ a : α, ∑ _c₁ ∈ C.filter (fun c => c i = a), (C.filter (fun c₂ => c₂ i = a)).card := by
                rw [← Finset.sum_fiberwise_of_maps_to (g := fun c : Fin n → α => c i)
                  (t := (Finset.univ : Finset α)) (fun _ _ => Finset.mem_univ _)]
                apply Finset.sum_congr rfl; intro a _
                apply Finset.sum_congr rfl; intro c₁ hc₁
                rw [(Finset.mem_filter.mp hc₁).2]
            _ = ∑ a : α, (C.filter (fun c => c i = a)).card ^ 2 := by
                apply Finset.sum_congr rfl; intro a _
                rw [Finset.sum_const, smul_eq_mul, sq]
        have hsum_add : (∑ c₁ ∈ C, ∑ c₂ ∈ C, if c₁ i ≠ c₂ i then 1 else 0) +
            (∑ c₁ ∈ C, ∑ c₂ ∈ C, if c₁ i = c₂ i then 1 else 0) = C.card ^ 2 := by
          simpa [Finset.sum_add_distrib] using htot
        omega
      calc S = ∑ c₁ ∈ C, ∑ c₂ ∈ C, ∑ i : Fin n, if c₁ i ≠ c₂ i then 1 else 0 := by
            dsimp only [S, hammingDist]
            apply Finset.sum_congr rfl; intro c₁ _
            apply Finset.sum_congr rfl; intro c₂ _
            rw [Finset.card_filter]
        _ = ∑ c₁ ∈ C, ∑ i : Fin n, ∑ c₂ ∈ C, if c₁ i ≠ c₂ i then 1 else 0 :=
            Finset.sum_congr rfl fun c₁ _ => Finset.sum_comm
        _ = ∑ i : Fin n, ∑ c₁ ∈ C, ∑ c₂ ∈ C, if c₁ i ≠ c₂ i then 1 else 0 :=
            Finset.sum_comm
        _ = ∑ i : Fin n, (C.card ^ 2 - ∑ a : α, (C.filter (fun c => c i = a)).card ^ 2) :=
            Finset.sum_congr rfl fun i _ => hcoord i
    have hS_upperR : (q : ℝ) * (S : ℝ) ≤ ((q : ℝ) - 1) * (n : ℝ) * (C.card : ℝ) ^ 2 := by
      have hcoord_le : ∀ i : Fin n,
          ((C.card ^ 2 - ∑ a : α, (C.filter (fun c => c i = a)).card ^ 2 : ℕ) : ℝ) ≤
            ((q : ℝ) - 1) / (q : ℝ) * (C.card : ℝ) ^ 2 := by
        intro i
        have hsum_m : (∑ a : α, ((C.filter (fun c => c i = a)).card : ℝ)) = (C.card : ℝ) := by
          have hnat : (∑ a : α, (C.filter (fun c => c i = a)).card) = C.card := by
            conv_rhs => rw [Finset.card_eq_sum_ones]
            rw [← Finset.sum_fiberwise_of_maps_to (g := fun c : Fin n → α => c i)
                  (t := (Finset.univ : Finset α)) (fun _ _ => Finset.mem_univ _)]
            apply Finset.sum_congr rfl; intro a _; rw [Finset.card_eq_sum_ones]
          exact_mod_cast hnat
        have hcs : (C.card : ℝ) ^ 2 ≤
            (q : ℝ) * ∑ a : α, ((C.filter (fun c => c i = a)).card : ℝ) ^ 2 := by
          let f : α → ℝ := fun a => ((C.filter (fun c => c i = a)).card : ℝ)
          have hnonneg : 0 ≤ ∑ a : α, ∑ b : α, (f a - f b) ^ 2 :=
            Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
          have hexp : ∑ a : α, ∑ b : α, (f a - f b) ^ 2 =
              2 * (q : ℝ) * (∑ a : α, f a ^ 2) - 2 * (∑ a : α, f a) ^ 2 := by
            have h1 : ∀ a b : α, (f a - f b) ^ 2 = f a ^ 2 + f b ^ 2 - 2 * (f a * f b) := fun a b => by ring
            simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul, sq]
            change (q : ℝ) * (∑ a : α, f a * f a) + (q : ℝ) * (∑ b : α, f b * f b) -
              2 * ((∑ a : α, f a) * (∑ b : α, f b)) = _
            ring
          have hfa : ∑ a : α, f a = (C.card : ℝ) := hsum_m
          rw [hexp, hfa] at hnonneg
          linarith
        have hle_sq : ∑ a : α, (C.filter (fun c => c i = a)).card ^ 2 ≤ C.card ^ 2 := by
          have hnat : (∑ a : α, (C.filter (fun c => c i = a)).card) = C.card := by
            exact_mod_cast hsum_m
          have hsq : ∑ a : α, (C.filter (fun c => c i = a)).card ^ 2 ≤
              (∑ a : α, (C.filter (fun c => c i = a)).card) ^ 2 := by
            calc ∑ a : α, (C.filter (fun c => c i = a)).card ^ 2
                ≤ ∑ a : α, (C.filter (fun c => c i = a)).card * C.card :=
                  Finset.sum_le_sum fun a _ => by
                    rw [sq]; exact Nat.mul_le_mul_left _ (Finset.card_filter_le _ _)
              _ = (∑ a : α, (C.filter (fun c => c i = a)).card) * C.card := (Finset.sum_mul ..).symm
              _ = (∑ a : α, (C.filter (fun c => c i = a)).card) ^ 2 := by rw [hnat, sq]
          rwa [hnat] at hsq
        rw [Nat.cast_sub hle_sq, Nat.cast_pow, Nat.cast_sum]
        simp_rw [Nat.cast_pow]
        have hdiv : (C.card : ℝ) ^ 2 / (q : ℝ) ≤ ∑ a : α, ((C.filter (fun c => c i = a)).card : ℝ) ^ 2 :=
          (div_le_iff₀ hq_posR).mpr (by linarith)
        have hring : (C.card : ℝ) ^ 2 - (C.card : ℝ) ^ 2 / (q : ℝ) =
            ((q : ℝ) - 1) / (q : ℝ) * (C.card : ℝ) ^ 2 := by
          field_simp [hq_posR.ne']
        linarith
      have hSR : (S : ℝ) ≤ (n : ℝ) * (((q : ℝ) - 1) / (q : ℝ) * (C.card : ℝ) ^ 2) := by
        rw [hS_eq, Nat.cast_sum]
        calc ∑ i : Fin n, ((C.card ^ 2 - ∑ a : α, (C.filter (fun c => c i = a)).card ^ 2 : ℕ) : ℝ)
            ≤ ∑ _i : Fin n, (((q : ℝ) - 1) / (q : ℝ) * (C.card : ℝ) ^ 2) :=
              Finset.sum_le_sum fun i _ => hcoord_le i
          _ = (n : ℝ) * (((q : ℝ) - 1) / (q : ℝ) * (C.card : ℝ) ^ 2) := by
              simp [Finset.sum_const, nsmul_eq_mul]
      have hmul := mul_le_mul_of_nonneg_left hSR hq_posR.le
      have hring : (q : ℝ) * ((n : ℝ) * (((q : ℝ) - 1) / (q : ℝ) * (C.card : ℝ) ^ 2)) =
          ((q : ℝ) - 1) * (n : ℝ) * (C.card : ℝ) ^ 2 := by
        field_simp [hq_posR.ne']
      linarith
    have hC1 : 1 ≤ C.card := Nat.pos_of_ne_zero hC0
    have hC_posR : (0 : ℝ) < (C.card : ℝ) := by exact_mod_cast hC1
    have hS_lowerR : (C.card : ℝ) * ((C.card : ℝ) - 1) * (d : ℝ) ≤ (S : ℝ) := by
      have h := Nat.cast_le (α := ℝ).mpr hS_lower
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hC1, Nat.cast_one] at h
      exact h
    have hcomb : (q : ℝ) * ((C.card : ℝ) * ((C.card : ℝ) - 1) * (d : ℝ)) ≤
        ((q : ℝ) - 1) * (n : ℝ) * (C.card : ℝ) ^ 2 :=
      (mul_le_mul_of_nonneg_left hS_lowerR hq_posR.le).trans hS_upperR
    nlinarith

/-- Binary Plotkin bound (`q = 2`): if `n < 2 * d`, then `|C| ≤ 2 * d / (2 * d - n)`. -/
theorem plotkin_bound_binary {n d : ℕ} (hplot : n < 2 * d)
    (C : Finset (Fin n → Fin 2))
    (hdist : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) :
    (C.card : ℝ) ≤ 2 * (d : ℝ) / (2 * (d : ℝ) - (n : ℝ)) := by
  have hplotR : ((Fintype.card (Fin 2) : ℝ) - 1) * (n : ℝ) < (Fintype.card (Fin 2) : ℝ) * (d : ℝ) := by
    simp only [Fintype.card_fin, Nat.cast_ofNat]
    have : (n : ℝ) < 2 * (d : ℝ) := by exact_mod_cast hplot
    linarith
  have h := plotkin_bound hplotR C hdist
  simpa only [Fintype.card_fin, Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using h

/-! ### General `F_p` (`ZMod p`) MacWilliams Weight-Enumerator Identity -/

/-- Additive character `χ(a) = exp(2πi a / p)` on `ZMod p`. -/
private def zmodChar (p : ℕ) (a : ZMod p) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) / (p : ℂ))

private lemma zmodChar_zero (p : ℕ) [NeZero p] : zmodChar p 0 = 1 := by
  simp [zmodChar, ZMod.val_zero]

private lemma zmodChar_add (p : ℕ) [NeZero p] (a b : ZMod p) :
    zmodChar p (a + b) = zmodChar p a * zmodChar p b := by
  unfold zmodChar
  rw [← Complex.exp_add]
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hmod : ∃ k : ℕ, (a + b).val + p * k = a.val + b.val :=
    ⟨(a.val + b.val) / p, by rw [ZMod.val_add]; exact Nat.mod_add_div (a.val + b.val) p⟩
  rcases hmod with ⟨k, hk⟩
  have hmodC : ((a + b).val : ℂ) = (a.val : ℂ) + (b.val : ℂ) - (k : ℂ) * (p : ℂ) := by
    have h : ((a + b).val : ℂ) + (p : ℂ) * (k : ℂ) = (a.val : ℂ) + (b.val : ℂ) := by
      exact_mod_cast hk
    linear_combination h
  have hkC : ((-((k : ℤ)) : ℤ) : ℂ) = -(k : ℂ) := by push_cast; rfl
  have hexp_eq : 2 * Real.pi * Complex.I * ((a + b).val : ℂ) / (p : ℂ) =
      (2 * Real.pi * Complex.I * (a.val : ℂ) / (p : ℂ) +
      2 * Real.pi * Complex.I * (b.val : ℂ) / (p : ℂ)) +
      (((-((k : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
    rw [hmodC, hkC]
    field_simp [hpC]
    ring
  rw [hexp_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma zmodChar_ne_one {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    zmodChar p a ≠ 1 := by
  intro heq
  rw [zmodChar, Complex.exp_eq_one_iff] at heq
  rcases heq with ⟨k, hk⟩
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp_pos.ne'
  have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hvalC : (a.val : ℂ) = (k : ℂ) * (p : ℂ) := by
    have h1 : (2 * Real.pi * Complex.I) * ((a.val : ℂ) / (p : ℂ)) =
        (2 * Real.pi * Complex.I) * (k : ℂ) := by
      linear_combination hk
    have h2 : (a.val : ℂ) / (p : ℂ) = (k : ℂ) := mul_left_cancel₀ h2piI h1
    exact (div_eq_iff hpC).mp h2
  have hvalR : (a.val : ℝ) = (k : ℝ) * (p : ℝ) := by
    exact_mod_cast congrArg Complex.re hvalC
  have ha_pos : 0 < a.val := Nat.pos_of_ne_zero (fun h => ha ((ZMod.val_eq_zero a).mp h))
  have ha_lt : a.val < p := a.val_lt
  have hk_gt : (0 : ℝ) < (k : ℝ) := by
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
    have haR : (0 : ℝ) < (a.val : ℝ) := by exact_mod_cast ha_pos
    nlinarith
  have hk_lt : (k : ℝ) < 1 := by
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
    have haR : (a.val : ℝ) < (p : ℝ) := by exact_mod_cast ha_lt
    nlinarith
  have hk1 : (1 : ℤ) ≤ k := by
    have : (0 : ℤ) < k := by exact_mod_cast hk_gt
    omega
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  linarith

private lemma sum_zmodChar_mul {p : ℕ} [Fact p.Prime] (c : ZMod p) :
    ∑ a : ZMod p, zmodChar p (c * a) = if c = 0 then (p : ℂ) else 0 := by
  split_ifs with hc
  · subst hc
    simp only [zero_mul, zmodChar_zero, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
      mul_one]
  · have hshift : ∑ a : ZMod p, zmodChar p (c * a) =
        zmodChar p c * ∑ a : ZMod p, zmodChar p (c * a) := by
      rw [Finset.mul_sum]
      refine (Equiv.sum_comp (Equiv.addRight (1 : ZMod p)) (fun a => zmodChar p (c * a))).symm.trans ?_
      apply Finset.sum_congr rfl
      intro a _
      change zmodChar p (c * (a + 1)) = zmodChar p c * zmodChar p (c * a)
      rw [mul_add, mul_one, zmodChar_add, mul_comm]
    have hne : zmodChar p c - 1 ≠ 0 := sub_ne_zero.mpr (zmodChar_ne_one hc)
    have hmul0 : (zmodChar p c - 1) * (∑ a : ZMod p, zmodChar p (c * a)) = 0 := by
      linear_combination -hshift
    exact (mul_eq_zero.mp hmul0).resolve_left hne

/-- The dual (orthogonal complement) linear code `C^⊥ ⊆ (Fin n → ZMod p)` of a linear code `C`
with respect to the standard dot product `∑ i, c i * v i`. -/
def dualCode {p n : ℕ} (C : Submodule (ZMod p) (Fin n → ZMod p)) :
    Submodule (ZMod p) (Fin n → ZMod p) where
  carrier := {v | ∀ c ∈ C, ∑ i : Fin n, c i * v i = 0}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun {u v} hu hv c hc => by
    simp_rw [Pi.add_apply, mul_add, Finset.sum_add_distrib, hu c hc, hv c hc, add_zero]
  smul_mem' := fun a {v} hv c hc => by
    simp_rw [Pi.smul_apply, smul_eq_mul, mul_left_comm (c _), ← Finset.mul_sum, hv c hc, mul_zero]

/-- Homogeneous Hamming weight enumerator polynomial `W_S(X, Y) = ∑_{c ∈ S} X^{n - wt(c)} Y^{wt(c)}`. -/
def weightEnum {n : ℕ} {α : Type*} [Zero α] [DecidableEq α]
    (S : Finset (Fin n → α)) (X Y : ℝ) : ℝ :=
  ∑ c ∈ S, X ^ (n - hammingWeight c) * Y ^ (hammingWeight c)

private lemma sum_zmodChar_dot {p n : ℕ} [Fact p.Prime]
    (C : Submodule (ZMod p) (Fin n → ZMod p)) (v : Fin n → ZMod p) :
    ∑ c ∈ Finset.univ.filter (· ∈ C), zmodChar p (∑ i : Fin n, c i * v i) =
      if v ∈ dualCode C then ((Finset.univ.filter (· ∈ C)).card : ℂ) else 0 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  split_ifs with hv
  · have hall : ∀ c ∈ Finset.univ.filter (· ∈ C), zmodChar p (∑ i : Fin n, c i * v i) = 1 := by
      intro c hc
      rw [hv c (Finset.mem_filter.mp hc).2, zmodChar_zero]
    rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, mul_one]
  · simp only [dualCode, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq, not_forall] at hv
    rcases hv with ⟨c₀, hc₀, hdot_ne⟩
    have hshift : (∑ c ∈ Finset.univ.filter (· ∈ C), zmodChar p (∑ i : Fin n, c i * v i)) =
        zmodChar p (∑ i : Fin n, c₀ i * v i) *
          ∑ c ∈ Finset.univ.filter (· ∈ C), zmodChar p (∑ i : Fin n, c i * v i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun c _ => c - c₀) ?_ ?_ ?_ ?_
      · intro c hc
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.sub_mem (Finset.mem_filter.mp hc).2 hc₀⟩
      · intro c₁ _ c₂ _ h; exact sub_left_injective h
      · intro c hc
        refine ⟨c + c₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          C.add_mem (Finset.mem_filter.mp hc).2 hc₀⟩, add_sub_cancel_right c c₀⟩
      · intro c _
        have hdot_eq : ∑ i : Fin n, c i * v i =
            (∑ i : Fin n, c₀ i * v i) + (∑ i : Fin n, (c - c₀) i * v i) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          simp only [Pi.sub_apply]
          ring
        rw [hdot_eq, zmodChar_add]
    have hne : zmodChar p (∑ i : Fin n, c₀ i * v i) - 1 ≠ 0 :=
      sub_ne_zero.mpr (zmodChar_ne_one hdot_ne)
    have hmul0 : (zmodChar p (∑ i : Fin n, c₀ i * v i) - 1) *
        (∑ c ∈ Finset.univ.filter (· ∈ C), zmodChar p (∑ i : Fin n, c i * v i)) = 0 := by
      linear_combination -hshift
    exact (mul_eq_zero.mp hmul0).resolve_left hne

/-- **Dimension / Cardinality Duality for Linear Codes over `F_p`:**
`|C| * |C^⊥| = p^n`. -/
theorem card_mul_card_dualCode {p n : ℕ} [Fact p.Prime]
    (C : Submodule (ZMod p) (Fin n → ZMod p)) :
    (Finset.univ.filter (· ∈ C)).card * (Finset.univ.filter (· ∈ dualCode C)).card = p ^ n := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hLHS : ∑ v : Fin n → ZMod p, ∑ c ∈ Finset.univ.filter (· ∈ C),
        zmodChar p (∑ i : Fin n, c i * v i) =
      (((Finset.univ.filter (· ∈ C)).card * (Finset.univ.filter (· ∈ dualCode C)).card : ℕ) : ℂ) := by
    simp_rw [sum_zmodChar_dot, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    push_cast; ring
  have hRHS : ∑ v : Fin n → ZMod p, ∑ c ∈ Finset.univ.filter (· ∈ C),
        zmodChar p (∑ i : Fin n, c i * v i) = ((p ^ n : ℕ) : ℂ) := by
    rw [Finset.sum_comm]
    have hinner : ∀ c : Fin n → ZMod p,
        ∑ v : Fin n → ZMod p, zmodChar p (∑ i : Fin n, c i * v i) =
          if c = 0 then ((p ^ n : ℕ) : ℂ) else 0 := by
      intro c
      have hprod : ∑ v : Fin n → ZMod p, zmodChar p (∑ i : Fin n, c i * v i) =
          ∏ i : Fin n, ∑ a : ZMod p, zmodChar p (c i * a) := by
        rw [Fintype.prod_sum]
        apply Finset.sum_congr rfl
        intro v _
        have hsum_char : ∀ s : Finset (Fin n),
            zmodChar p (∑ i ∈ s, c i * v i) = ∏ i ∈ s, zmodChar p (c i * v i) := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp [zmodChar_zero]
          | insert i s hi ih =>
            rw [Finset.sum_insert hi, Finset.prod_insert hi, zmodChar_add, ih]
        exact hsum_char Finset.univ
      rw [hprod]
      simp_rw [sum_zmodChar_mul]
      by_cases hc : c = 0
      · subst hc
        simp only [Pi.zero_apply, ↓reduceIte, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Nat.cast_pow]
      · rw [if_neg hc]
        have hex : ∃ i : Fin n, c i ≠ 0 := by
          by_contra h; push Not at h; exact hc (funext h)
        rcases hex with ⟨i₀, hi₀⟩
        exact Finset.prod_eq_zero (Finset.mem_univ i₀) (if_neg hi₀)
    simp_rw [hinner]
    have h0mem : (0 : Fin n → ZMod p) ∈ Finset.univ.filter (· ∈ C) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.zero_mem⟩
    rw [Finset.sum_ite_eq', if_pos h0mem]
  have heqC : (((Finset.univ.filter (· ∈ C)).card * (Finset.univ.filter (· ∈ dualCode C)).card : ℕ) : ℂ) =
      ((p ^ n : ℕ) : ℂ) := hLHS.symm.trans hRHS
  exact_mod_cast heqC

/-- **General `F_p` MacWilliams Weight-Enumerator Identity:**
For every prime `p`, every linear code `C : Submodule (ZMod p) (Fin n → ZMod p)`, and all `X, Y : ℝ`,
`W_{C^⊥}(X, Y) = (1 / |C|) * W_C(X + (p - 1) Y, X - Y)`. -/
theorem macwilliams_identity {p n : ℕ} [Fact p.Prime]
    (C : Submodule (ZMod p) (Fin n → ZMod p)) (X Y : ℝ) :
    weightEnum (Finset.univ.filter (· ∈ dualCode C)) X Y =
      (1 / ((Finset.univ.filter (· ∈ C)).card : ℝ)) *
        weightEnum (Finset.univ.filter (· ∈ C)) (X + ((p : ℝ) - 1) * Y) (X - Y) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hC_pos : 0 < (Finset.univ.filter (· ∈ C)).card :=
    Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.zero_mem⟩⟩
  have hC_posR : (0 : ℝ) < ((Finset.univ.filter (· ∈ C)).card : ℝ) := by exact_mod_cast hC_pos
  -- Prove the identity in `ℂ`, then cast back to `ℝ` via `Complex.ofReal_injective`
  have hkeyC : ((Finset.univ.filter (· ∈ C)).card : ℂ) *
        (weightEnum (Finset.univ.filter (· ∈ dualCode C)) X Y : ℂ) =
      (weightEnum (Finset.univ.filter (· ∈ C)) (X + ((p : ℝ) - 1) * Y) (X - Y) : ℂ) := by
    let XC : ℂ := (X : ℂ)
    let YC : ℂ := (Y : ℂ)
    -- Step 1: LHS equals `∑ v, (∑ c ∈ C, χ(⟨c, v⟩)) * XC^(n - wt(v)) * YC^(wt(v))`
    have hLHS : ((Finset.univ.filter (· ∈ C)).card : ℂ) *
          (weightEnum (Finset.univ.filter (· ∈ dualCode C)) X Y : ℂ) =
        ∑ v : Fin n → ZMod p,
          (∑ c ∈ Finset.univ.filter (· ∈ C), zmodChar p (∑ i : Fin n, c i * v i)) *
            (XC ^ (n - hammingWeight v) * YC ^ (hammingWeight v)) := by
      unfold weightEnum
      push_cast
      rw [Finset.mul_sum]
      simp_rw [sum_zmodChar_dot]
      have hterm : ∀ v : Fin n → ZMod p,
          (if v ∈ dualCode C then ((Finset.univ.filter (· ∈ C)).card : ℂ) else 0) *
            (XC ^ (n - hammingWeight v) * YC ^ (hammingWeight v)) =
          if v ∈ dualCode C then
            ((Finset.univ.filter (· ∈ C)).card : ℂ) * (XC ^ (n - hammingWeight v) * YC ^ (hammingWeight v))
          else 0 := by
        intro v; split_ifs <;> ring
      simp_rw [hterm, ← Finset.sum_filter]
      rfl
    -- Step 2: Swap sums and factor over coordinates `i : Fin n`
    have hfactor : ∀ c : Fin n → ZMod p,
        ∑ v : Fin n → ZMod p,
          zmodChar p (∑ i : Fin n, c i * v i) * (XC ^ (n - hammingWeight v) * YC ^ (hammingWeight v)) =
        (XC + ((p : ℂ) - 1) * YC) ^ (n - hammingWeight c) * (XC - YC) ^ (hammingWeight c) := by
      intro c
      have hprod_v : ∀ v : Fin n → ZMod p,
          zmodChar p (∑ i : Fin n, c i * v i) * (XC ^ (n - hammingWeight v) * YC ^ (hammingWeight v)) =
            ∏ i : Fin n, zmodChar p (c i * v i) * (if v i = 0 then XC else YC) := by
        intro v
        have hsum_char : ∀ s : Finset (Fin n),
            zmodChar p (∑ i ∈ s, c i * v i) = ∏ i ∈ s, zmodChar p (c i * v i) := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp [zmodChar_zero]
          | insert i s hi ih =>
            rw [Finset.sum_insert hi, Finset.prod_insert hi, zmodChar_add, ih]
        have hwt_prod : ∏ i : Fin n, (if v i = 0 then XC else YC) =
            XC ^ (n - hammingWeight v) * YC ^ (hammingWeight v) := by
          rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
          have hnz : (Finset.univ.filter (fun i : Fin n => ¬ v i = 0)).card = hammingWeight v := rfl
          have hz : (Finset.univ.filter (fun i : Fin n => v i = 0)).card = n - hammingWeight v := by
            have htot := card_filter_add_not (Finset.univ : Finset (Fin n)) (fun i : Fin n => v i = 0)
            rw [hnz, Finset.card_univ, Fintype.card_fin] at htot
            omega
          rw [hz, hnz]
        rw [Finset.prod_mul_distrib, hsum_char Finset.univ, hwt_prod]
      simp_rw [hprod_v]
      rw [← Fintype.prod_sum (fun (i : Fin n) (a : ZMod p) => zmodChar p (c i * a) * if a = 0 then XC else YC)]
      have hcoord_sum : ∀ i : Fin n,
          (∑ a : ZMod p, zmodChar p (c i * a) * (if a = 0 then XC else YC)) =
            if c i = 0 then XC + ((p : ℂ) - 1) * YC else XC - YC := by
        intro i
        have hsplit : ∑ a : ZMod p, zmodChar p (c i * a) * (if a = 0 then XC else YC) =
            XC + YC * ((∑ a : ZMod p, zmodChar p (c i * a)) - 1) := by
          have hterm : ∀ a : ZMod p,
              zmodChar p (c i * a) * (if a = 0 then XC else YC) =
                (if a = 0 then XC - YC else 0) + YC * zmodChar p (c i * a) := by
            intro a
            by_cases ha : a = 0
            · subst ha; simp [zmodChar_zero]
            · simp [ha]; ring
          simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
            ← Finset.mul_sum]
          ring
        rw [hsplit, sum_zmodChar_mul]
        split_ifs <;> ring
      simp_rw [hcoord_sum, Finset.prod_ite, Finset.prod_const]
      have hnz : (Finset.univ.filter (fun i : Fin n => ¬ c i = 0)).card = hammingWeight c := rfl
      have hz : (Finset.univ.filter (fun i : Fin n => c i = 0)).card = n - hammingWeight c := by
        have htot := card_filter_add_not (Finset.univ : Finset (Fin n)) (fun i : Fin n => c i = 0)
        rw [hnz, Finset.card_univ, Fintype.card_fin] at htot
        omega
      rw [hz, hnz]
    rw [hLHS]
    calc ∑ v : Fin n → ZMod p,
            (∑ c ∈ Finset.univ.filter (· ∈ C), zmodChar p (∑ i : Fin n, c i * v i)) *
              (XC ^ (n - hammingWeight v) * YC ^ (hammingWeight v))
        = ∑ c ∈ Finset.univ.filter (· ∈ C), ∑ v : Fin n → ZMod p,
            zmodChar p (∑ i : Fin n, c i * v i) * (XC ^ (n - hammingWeight v) * YC ^ (hammingWeight v)) := by
          simp_rw [Finset.sum_mul]
          exact Finset.sum_comm
      _ = ∑ c ∈ Finset.univ.filter (· ∈ C),
            (XC + ((p : ℂ) - 1) * YC) ^ (n - hammingWeight c) * (XC - YC) ^ (hammingWeight c) :=
          Finset.sum_congr rfl fun c _ => hfactor c
      _ = (weightEnum (Finset.univ.filter (· ∈ C)) (X + ((p : ℝ) - 1) * Y) (X - Y) : ℂ) := by
          unfold weightEnum
          push_cast
          rfl
  have hkeyR : ((Finset.univ.filter (· ∈ C)).card : ℝ) *
        weightEnum (Finset.univ.filter (· ∈ dualCode C)) X Y =
      weightEnum (Finset.univ.filter (· ∈ C)) (X + ((p : ℝ) - 1) * Y) (X - Y) := by
    apply Complex.ofReal_injective
    push_cast
    exact hkeyC
  rw [one_div_mul_eq_div, eq_div_iff hC_posR.ne', mul_comm]
  exact hkeyR

/-- Binary specialization (`p = 2`) of the MacWilliams Weight-Enumerator Identity:
`W_{C^⊥}(X, Y) = (1 / |C|) * W_C(X + Y, X - Y)`. -/
theorem macwilliams_identity_binary {n : ℕ}
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (X Y : ℝ) :
    weightEnum (Finset.univ.filter (· ∈ dualCode C)) X Y =
      (1 / ((Finset.univ.filter (· ∈ C)).card : ℝ)) *
        weightEnum (Finset.univ.filter (· ∈ C)) (X + Y) (X - Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := macwilliams_identity C X Y
  simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using h

end CodingTheory

end
end Arith4Ext.EntropyCoding
