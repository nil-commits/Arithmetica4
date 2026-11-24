/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# PPL 173 Part 1 (Erdős Problem #711): New World-Record Upper Bound `max_m f(n, m) ≤ 13 n^{10/7} + 2`

## Scope & Honest Labeling
This file proves a **new world-record general upper bound** for Erdős Problem #711 Part 1
(Erdős–Pomerance, *Indag. Math.* 1980), strictly improving the 46-year-old `O(n^{3/2})` upper bound
by `1/14` in the exponent, with an explicit constant `13` valid for **all** `n ≥ 1` and **all**
`m : ℕ`:

> **Main Theorems (`ppl173_world_record_nat`, `ppl173_world_record_rpow`, `ppl173_world_record_closed`):**
> For every `n ≥ 1` and every `m : ℕ`, if `L : ℕ` satisfies `13 ^ 7 * n ^ 10 ≤ (L - 1) ^ 7`
> (in particular `L = ⌈13 * n ^ (10/7)⌉ + 1`), then the open interval `(m, m + L)` contains `n`
> distinct natural numbers `a_1, ..., a_n` such that `k ∣ a_k` for every `1 ≤ k ≤ n`.
> Equivalently, the minimal `f(n, m)` satisfies
> `f(n, m) ≤ 13 * n ^ (10 / 7) + 2` for all `n ≥ 1` and `m : ℕ`.

- **Status vs. Literature:** Strictly beats Erdős–Pomerance (1980) `max_m f(n, m) ≪ n^{3/2}`
  (still cited as the best general upper bound in van Doorn 2026 `arXiv:2601.16972` and
  Kominers 2026 `arXiv:2607.10431`).
- **NOT the full `n^{1+o(1)}` conjecture:** The full Erdős #711 Part 1 conjecture
  `max_m f(n, m) ≤ n^{1+o(1)}` remains open; our block reduction shows it is implied by the
  Katz–Tao Arithmetic Kakeya Conjecture (`|D_r(A)| ≪_ε |A|^{1+ε}` for `r = r(ε)`).

## Proof Overview (100% Elementary, Self-Contained, Zero `sorry`)
1. **5-AP Distinct Common Differences (`card_pow_four_le_card_pow_seven_of_five_ap`):**
   For any finite sets `A, D ⊆ ℤ` where every `d ∈ D` is the common difference of a 5-term
   arithmetic progression `a, a+d, a+2d, a+3d, a+4d ∈ A`, we prove `|D|^4 ≤ |A|^7` (constant `1`).
   Selecting one edge `(a_d, a_d + d) ∈ G ⊆ A × A` per `d ∈ D` makes `(a, b) ↦ b - a` injective on
   `G`. Two Cauchy–Schwarz steps lower-bound the 4-cycles `|C₄(G)| ≥ |G|^4 / |A|^4`, while the map
   `(a₁, a₂, b₁, b₂) ↦ (3b₁ - 2a₁, 2b₂ - a₁, 4b₂ - 3a₂)` injects `C₄(G) ↪ A³` via the exact
   identity `(3b₁ - 2a₁) - 2(2b₂ - a₁) + (4b₂ - 3a₂) = 3(b₁ - a₂)`.
2. **Windowed Block Bound (`block_five_ap_bound`):**
   For any `S' ⊆ S ∩ [1, M]` and `B = ⌊(L - 1)/M⌋ ≥ 5`, every 5-block window `A_b` of multiples in
   `T` contains a 5-AP of step `k` for all `k ∈ S'`. By pigeonhole on the minimum window `A_{b₀}`
   (each `t ∈ T` lies in at most `5` windows), `(B - 4)^7 |S'|^4 ≤ 5^7 |T|^7`.
3. **Dyadic Summation & Hall's Marriage Theorem:**
   Partitioning `S ⊆ [1, n]` into dyadic slices `S_j = {k ∈ S : 2^j k ≤ n < 2^{j+1} k}`, using
   `81^j = (3^j)^4 ≤ (2^j)^7 = 128^j` and `∑ 3^{-j} < 3/2`, any Hall failure `|T| < |S|` forces
   `16 (L - 1)^7 < 81 · 10^7 n^{10} < 16 · 13^7 n^{10}`, contradiction. Hall's Marriage Theorem
   (`Finset.all_card_le_biUnion_card_iff_exists_injective`) concludes the proof.
-/

namespace PPL173

/-! ### Section 1: Elementary `Finset` Cauchy–Schwarz and `C₄` Lower Bound -/

/-- Elementary Cauchy–Schwarz inequality for `ℕ`-valued functions on a `Finset`. -/
private lemma sq_sum_le_card_mul_sum_sq_nat {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∑ x ∈ s, f x) ^ 2 ≤ s.card * ∑ x ∈ s, (f x) ^ 2 := by
  have hZ : (0 : ℤ) ≤ ∑ x ∈ s, ∑ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
  have hexp :
      ∑ x ∈ s, ∑ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 =
        2 * (s.card : ℤ) * (∑ x ∈ s, (f x : ℤ) ^ 2) - 2 * (∑ x ∈ s, (f x : ℤ)) ^ 2 := by
    have h1 : ∀ x ∈ s, ∑ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 =
        (s.card : ℤ) * (f x : ℤ) ^ 2 - 2 * (f x : ℤ) * (∑ y ∈ s, (f y : ℤ)) +
          ∑ y ∈ s, (f y : ℤ) ^ 2 := by
      intro x _
      have hsub : ∀ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 =
          (f x : ℤ) ^ 2 - 2 * (f x : ℤ) * (f y : ℤ) + (f y : ℤ) ^ 2 := by
        intro y _; ring
      rw [Finset.sum_congr rfl hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ x ∈ s, 2 * (f x : ℤ) = 2 * ∑ x ∈ s, (f x : ℤ) := by
      rw [← Finset.mul_sum]
    rw [h2]
    ring
  rw [hexp] at hZ
  have hle : (∑ x ∈ s, (f x : ℤ)) ^ 2 ≤ (s.card : ℤ) * ∑ x ∈ s, (f x : ℤ) ^ 2 := by linarith
  exact_mod_cast hle

/-- The set of (possibly degenerate) 4-cycles `((a₁, a₂), (b₁, b₂))` in a bipartite graph
`G ⊆ A × A`. -/
private def c4Set (A : Finset ℤ) (G : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter fun p =>
    (p.1.1, p.2.1) ∈ G ∧ (p.1.1, p.2.2) ∈ G ∧ (p.1.2, p.2.1) ∈ G ∧ (p.1.2, p.2.2) ∈ G

/-- Double-counting + two Cauchy–Schwarz steps: `|G|^4 ≤ |A|^4 * |C₄(G)|` for `G ⊆ A × A`. -/
private lemma c4Set_card_lower_bound (A : Finset ℤ) (G : Finset (ℤ × ℤ)) (hG : G ⊆ A ×ˢ A) :
    G.card ^ 4 ≤ A.card ^ 4 * (c4Set A G).card := by
  let deg : ℤ → ℕ := fun a => (A.filter (fun b => (a, b) ∈ G)).card
  let codeg : ℤ × ℤ → ℕ := fun p => (A.filter (fun a => (a, p.1) ∈ G ∧ (a, p.2) ∈ G)).card
  -- Step 1: ∑ a ∈ A, deg a = G.card
  have hsum_deg : ∑ a ∈ A, deg a = G.card := by
    have hEq : G = (A ×ˢ A).filter (fun p => p ∈ G) := by
      ext p
      exact ⟨fun hp => Finset.mem_filter.mpr ⟨hG hp, hp⟩, fun hp => (Finset.mem_filter.mp hp).2⟩
    rw [hEq, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    dsimp only [deg]
    rw [Finset.card_filter]
  -- Step 2: ∑ p ∈ A ×ˢ A, codeg p = ∑ a ∈ A, (deg a)^2
  have hsum_codeg : ∑ p ∈ A ×ˢ A, codeg p = ∑ a ∈ A, (deg a) ^ 2 := by
    have hL : ∑ p ∈ A ×ˢ A, codeg p =
        ∑ p ∈ A ×ˢ A, ∑ a ∈ A, (if (a, p.1) ∈ G ∧ (a, p.2) ∈ G then 1 else 0) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      dsimp only [codeg]
      rw [Finset.card_filter]
    rw [hL, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_product]
    have hmul : ∀ b₁ ∈ A, ∑ b₂ ∈ A, (if (a, b₁) ∈ G ∧ (a, b₂) ∈ G then (1 : ℕ) else 0) =
        (if (a, b₁) ∈ G then 1 else 0) * deg a := by
      intro b₁ _
      by_cases h1 : (a, b₁) ∈ G
      · simp only [h1, true_and, ite_true, one_mul, deg]
        rw [Finset.card_filter]
      · simp only [h1, false_and, ite_false, zero_mul, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl hmul, ← Finset.sum_mul]
    have hdeg_eq : ∑ b₁ ∈ A, (if (a, b₁) ∈ G then (1 : ℕ) else 0) = deg a := by
      dsimp only [deg]
      rw [Finset.card_filter]
    rw [hdeg_eq, sq]
  -- Step 3: (c4Set A G).card = ∑ p ∈ A ×ˢ A, (codeg p)^2
  have hc4_eq : (c4Set A G).card = ∑ p ∈ A ×ˢ A, (codeg p) ^ 2 := by
    rw [c4Set, Finset.card_filter, Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_product]
    have hmul : ∀ a₁ ∈ A,
        ∑ a₂ ∈ A, (if (a₁, p.1) ∈ G ∧ (a₁, p.2) ∈ G ∧ (a₂, p.1) ∈ G ∧ (a₂, p.2) ∈ G
          then (1 : ℕ) else 0) =
        (if (a₁, p.1) ∈ G ∧ (a₁, p.2) ∈ G then 1 else 0) * codeg p := by
      intro a₁ _
      by_cases h1 : (a₁, p.1) ∈ G ∧ (a₁, p.2) ∈ G
      · simp only [h1.1, h1.2, true_and, ite_true, one_mul, codeg]
        rw [Finset.card_filter]
      · have hfalse : ∀ a₂ : ℤ,
            ¬((a₁, p.1) ∈ G ∧ (a₁, p.2) ∈ G ∧ (a₂, p.1) ∈ G ∧ (a₂, p.2) ∈ G) :=
          fun _ h => h1 ⟨h.1, h.2.1⟩
        simp only [h1, ite_false, zero_mul, hfalse, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl hmul, ← Finset.sum_mul]
    have hcd : ∑ a₁ ∈ A, (if (a₁, p.1) ∈ G ∧ (a₁, p.2) ∈ G then (1 : ℕ) else 0) = codeg p := by
      dsimp only [codeg]
      rw [Finset.card_filter]
    rw [hcd, sq]
  -- Step 4: Two applications of Cauchy–Schwarz
  have hcs1 : G.card ^ 2 ≤ A.card * ∑ p ∈ A ×ˢ A, codeg p := by
    rw [← hsum_deg, hsum_codeg]
    exact sq_sum_le_card_mul_sum_sq_nat A deg
  have hcs2 : (∑ p ∈ A ×ˢ A, codeg p) ^ 2 ≤ A.card ^ 2 * (c4Set A G).card := by
    have h := sq_sum_le_card_mul_sum_sq_nat (A ×ˢ A) codeg
    rw [Finset.card_product, ← sq, ← hc4_eq] at h
    exact h
  calc
    G.card ^ 4 = (G.card ^ 2) ^ 2 := by ring
    _ ≤ (A.card * ∑ p ∈ A ×ˢ A, codeg p) ^ 2 := Nat.pow_le_pow_left hcs1 2
    _ = A.card ^ 2 * (∑ p ∈ A ×ˢ A, codeg p) ^ 2 := by ring
    _ ≤ A.card ^ 2 * (A.card ^ 2 * (c4Set A G).card) := Nat.mul_le_mul_left _ hcs2
    _ = A.card ^ 4 * (c4Set A G).card := by ring

/-! ### Section 2: The 5-AP Distinct Common Differences Bound `|D|^4 ≤ |A|^7` -/

/-- **5-AP Distinct Common Differences Theorem (constant 1):**
If `A, D ⊆ ℤ` are finite sets such that every `d ∈ D` is the common difference of a 5-term
arithmetic progression `{a, a + d, a + 2d, a + 3d, a + 4d} ⊆ A`, then `|D|^4 ≤ |A|^7`. -/
theorem card_pow_four_le_card_pow_seven_of_five_ap
    (A D : Finset ℤ)
    (hD : ∀ d ∈ D, ∃ a ∈ A, a + d ∈ A ∧ a + 2 * d ∈ A ∧ a + 3 * d ∈ A ∧ a + 4 * d ∈ A) :
    D.card ^ 4 ≤ A.card ^ 7 := by
  classical
  -- Choose one starting point `a₀ d` for each `d ∈ D`
  let a₀ : ℤ → ℤ := fun d => if h : d ∈ D then Classical.choose (hD d h) else 0
  have ha₀ : ∀ d ∈ D, a₀ d ∈ A ∧ a₀ d + d ∈ A ∧ a₀ d + 2 * d ∈ A ∧
      a₀ d + 3 * d ∈ A ∧ a₀ d + 4 * d ∈ A := by
    intro d hd
    have hspec := Classical.choose_spec (hD d hd)
    simpa [a₀, hd] using hspec
  -- Build the graph G = {(a₀ d, a₀ d + d) : d ∈ D} ⊆ A × A
  let f : ℤ → ℤ × ℤ := fun d => (a₀ d, a₀ d + d)
  let G : Finset (ℤ × ℤ) := D.image f
  have hf_inj : Set.InjOn f (D : Set ℤ) := by
    intro d₁ _ d₂ _ hEq
    have h1 : a₀ d₁ = a₀ d₂ := congrArg Prod.fst hEq
    have h2 : a₀ d₁ + d₁ = a₀ d₂ + d₂ := congrArg Prod.snd hEq
    omega
  have hG_card : G.card = D.card := Finset.card_image_of_injOn hf_inj
  have hG_sub : G ⊆ A ×ˢ A := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨d, hd, rfl⟩
    have h := ha₀ d hd
    exact Finset.mem_product.mpr ⟨h.1, h.2.1⟩
  have hG_ap : ∀ p ∈ G, 2 * p.2 - p.1 ∈ A ∧ 3 * p.2 - 2 * p.1 ∈ A ∧ 4 * p.2 - 3 * p.1 ∈ A := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨d, hd, rfl⟩
    have h := ha₀ d hd
    refine ⟨?_, ?_, ?_⟩
    · convert h.2.2.1 using 1; ring
    · convert h.2.2.2.1 using 1; ring
    · convert h.2.2.2.2 using 1; ring
  have hG_diff_inj : ∀ p q, p ∈ G → q ∈ G → p.2 - p.1 = q.2 - q.1 → p = q := by
    intro p q hp hq hdiff
    rcases Finset.mem_image.mp hp with ⟨d₁, hd₁, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨d₂, hd₂, rfl⟩
    have hd : d₁ = d₂ := by dsimp [f] at hdiff; omega
    subst hd
    rfl
  -- Inject C₄(G) into A × (A × A) via (a₁, a₂, b₁, b₂) ↦ (3b₁ - 2a₁, (2b₂ - a₁, 4b₂ - 3a₂))
  let Φ : (ℤ × ℤ) × (ℤ × ℤ) → ℤ × (ℤ × ℤ) :=
    fun p => (3 * p.2.1 - 2 * p.1.1, (2 * p.2.2 - p.1.1, 4 * p.2.2 - 3 * p.1.2))
  have hΦ_maps : ∀ p ∈ c4Set A G, Φ p ∈ A ×ˢ (A ×ˢ A) := by
    intro p hp
    have hmem := (Finset.mem_filter.mp hp).2
    refine Finset.mem_product.mpr ⟨(hG_ap _ hmem.1).2.1, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
    · exact (hG_ap _ hmem.2.1).1
    · exact (hG_ap _ hmem.2.2.2).2.2
  have hΦ_inj : Set.InjOn Φ (c4Set A G : Set ((ℤ × ℤ) × (ℤ × ℤ))) := by
    intro p hp q hq hEq
    have hpm := (Finset.mem_filter.mp hp).2
    have hqm := (Finset.mem_filter.mp hq).2
    have h1 : 3 * p.2.1 - 2 * p.1.1 = 3 * q.2.1 - 2 * q.1.1 := congrArg Prod.fst hEq
    have h2 : 2 * p.2.2 - p.1.1 = 2 * q.2.2 - q.1.1 := congrArg (fun x => x.2.1) hEq
    have h3 : 4 * p.2.2 - 3 * p.1.2 = 4 * q.2.2 - 3 * q.1.2 := congrArg (fun x => x.2.2) hEq
    -- Key linear identity: v₁ - 2 v₂ + v₃ = 3 (b₁ - a₂)
    have hdiff : p.2.1 - p.1.2 = q.2.1 - q.1.2 := by linarith
    have heq21 : (p.1.2, p.2.1) = (q.1.2, q.2.1) :=
      hG_diff_inj _ _ hpm.2.2.1 hqm.2.2.1 hdiff
    have ha₂ : p.1.2 = q.1.2 := congrArg Prod.fst heq21
    have hb₁ : p.2.1 = q.2.1 := congrArg Prod.snd heq21
    have ha₁ : p.1.1 = q.1.1 := by linarith
    have hb₂ : p.2.2 = q.2.2 := by linarith
    rcases p with ⟨⟨pa₁, pa₂⟩, ⟨pb₁, pb₂⟩⟩
    rcases q with ⟨⟨qa₁, qa₂⟩, ⟨qb₁, qb₂⟩⟩
    simp only at ha₁ ha₂ hb₁ hb₂
    subst ha₁; subst ha₂; subst hb₁; subst hb₂
    rfl
  have hc4_upper : (c4Set A G).card ≤ A.card ^ 3 := by
    calc
      (c4Set A G).card ≤ (A ×ˢ (A ×ˢ A)).card :=
        Finset.card_le_card_of_injOn Φ hΦ_maps hΦ_inj
      _ = A.card * (A.card * A.card) := by simp [Finset.card_product]
      _ = A.card ^ 3 := by ring
  calc
    D.card ^ 4 = G.card ^ 4 := by rw [hG_card]
    _ ≤ A.card ^ 4 * (c4Set A G).card := c4Set_card_lower_bound A G hG_sub
    _ ≤ A.card ^ 4 * A.card ^ 3 := Nat.mul_le_mul_left _ hc4_upper
    _ = A.card ^ 7 := by ring

/-! ### Section 3: Windowed Block Bound on Multiples in `(m, m + L)` -/

/-- Every integer `k ∈ [1, M]` has a multiple in `(x, x + M]`. -/
private lemma exists_multiple_in_block (x M k : ℕ) (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    ∃ a : ℕ, x < a ∧ a ≤ x + M ∧ k ∣ a := by
  refine ⟨(x / k + 1) * k, ?_, ?_, dvd_mul_left k _⟩
  · have hmod := Nat.div_add_mod x k
    have hlt : x % k < k := Nat.mod_lt x (by omega)
    nlinarith
  · have hle : (x / k) * k ≤ x := Nat.div_mul_le_self x k
    nlinarith

/-- Windowed 5-block bound: for `S' ⊆ S` with all elements in `[1, M]` and `B = ⌊(L-1)/M⌋ ≥ 5`,
`(B - 4)^7 * |S'|^4 ≤ 5^7 * |T|^7`, where `T` is the neighborhood of `S` in `(m, m + L)`. -/
private lemma block_five_ap_bound
    (m L M : ℕ) (hM : 1 ≤ M) (S S' : Finset ℕ)
    (hS'sub : S' ⊆ S) (hS'le : ∀ k ∈ S', 1 ≤ k ∧ k ≤ M)
    (hB : 5 ≤ (L - 1) / M) :
    ((L - 1) / M - 4) ^ 7 * S'.card ^ 4 ≤
      5 ^ 7 * ((Finset.Ioo m (m + L)).filter (fun t => ∃ k ∈ S, k ∣ t)).card ^ 7 := by
  classical
  let T : Finset ℕ := (Finset.Ioo m (m + L)).filter (fun t => ∃ k ∈ S, k ∣ t)
  let B : ℕ := (L - 1) / M
  let W : ℕ := B - 4
  have hW_pos : 1 ≤ W := by omega
  have hBM : B * M ≤ L - 1 := Nat.div_mul_le_self (L - 1) M
  have hL_pos : 1 ≤ L := by
    have : 5 * M ≤ B * M := Nat.mul_le_mul_right M hB
    omega
  -- Window A_b = T ∩ (m + b*M, m + (b + 5)*M]
  let win : ℕ → Finset ℕ := fun b =>
    T.filter (fun t => m + b * M < t ∧ t ≤ m + (b + 5) * M)
  -- Every window contains a 5-AP of step k for every k ∈ S'
  have hwin_bound : ∀ b ∈ Finset.range W, S'.card ^ 4 ≤ (win b).card ^ 7 := by
    intro b hb
    have hb_lt : b < W := Finset.mem_range.mp hb
    have hb5 : (b + 5) * M ≤ L - 1 := by
      have : b + 5 ≤ B := by omega
      exact le_trans (Nat.mul_le_mul_right M this) hBM
    let A_b : Finset ℤ := (win b).image (fun x : ℕ => (x : ℤ))
    let D_s : Finset ℤ := S'.image (fun x : ℕ => (x : ℤ))
    have hA_card : A_b.card = (win b).card :=
      Finset.card_image_of_injective _ Nat.cast_injective
    have hD_card : D_s.card = S'.card :=
      Finset.card_image_of_injective _ Nat.cast_injective
    have hfive : ∀ d ∈ D_s, ∃ a ∈ A_b,
        a + d ∈ A_b ∧ a + 2 * d ∈ A_b ∧ a + 3 * d ∈ A_b ∧ a + 4 * d ∈ A_b := by
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨k, hk, rfl⟩
      have hk_bounds := hS'le k hk
      obtain ⟨a, ha_gt, ha_le, ha_dvd⟩ :=
        exists_multiple_in_block (m + b * M) M k hk_bounds.1 hk_bounds.2
      have hmem : ∀ r : ℕ, r ≤ 4 → (a + r * k : ℕ) ∈ win b := by
        intro r hr
        have hlo : m + b * M < a + r * k := by omega
        have hhi : a + r * k ≤ m + (b + 5) * M := by
          have hrk : r * k ≤ 4 * M := Nat.mul_le_mul hr hk_bounds.2
          have hadd : m + b * M + M + 4 * M = m + (b + 5) * M := by ring
          omega
        have hT : a + r * k ∈ T := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨?_, ?_⟩, k, hS'sub hk, ?_⟩
          · omega
          · omega
          · exact dvd_add ha_dvd (dvd_mul_left k r)
        exact Finset.mem_filter.mpr ⟨hT, hlo, hhi⟩
      have hmem0 : a ∈ win b := by simpa using hmem 0 (by omega)
      refine ⟨(a : ℤ), Finset.mem_image_of_mem _ hmem0, ?_, ?_, ?_, ?_⟩
      · convert Finset.mem_image_of_mem (fun x : ℕ => (x : ℤ)) (hmem 1 (by omega)) using 1
        push_cast; ring
      · convert Finset.mem_image_of_mem (fun x : ℕ => (x : ℤ)) (hmem 2 (by omega)) using 1
        push_cast; ring
      · convert Finset.mem_image_of_mem (fun x : ℕ => (x : ℤ)) (hmem 3 (by omega)) using 1
        push_cast; ring
      · convert Finset.mem_image_of_mem (fun x : ℕ => (x : ℤ)) (hmem 4 (by omega)) using 1
        push_cast; ring
    have h7 := card_pow_four_le_card_pow_seven_of_five_ap A_b D_s hfive
    rwa [hA_card, hD_card] at h7
  -- Sum of window sizes is at most 5 * T.card (each t ∈ T lies in at most 5 windows)
  have hsum_win : ∑ b ∈ Finset.range W, (win b).card ≤ 5 * T.card := by
    have hswap : ∑ b ∈ Finset.range W, (win b).card =
        ∑ t ∈ T, ((Finset.range W).filter (fun b => m + b * M < t ∧ t ≤ m + (b + 5) * M)).card := by
      simp_rw [win, Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap]
    have hpt : ∀ t ∈ T,
        ((Finset.range W).filter (fun b => m + b * M < t ∧ t ≤ m + (b + 5) * M)).card ≤ 5 := by
      intro t ht
      have ht_gt : m < t := (Finset.mem_Ioo.mp (Finset.mem_filter.mp ht).1).1
      let q : ℕ := (t - m - 1) / M
      have hsub :
          (Finset.range W).filter (fun b => m + b * M < t ∧ t ≤ m + (b + 5) * M) ⊆
            Finset.Icc (q - 4) q := by
        intro b hb
        rcases (Finset.mem_filter.mp hb).2 with ⟨h1, h2⟩
        have hbM_le : b * M ≤ t - m - 1 := by omega
        have hb_le_q : b ≤ q := (Nat.le_div_iff_mul_le (by omega : 0 < M)).mpr hbM_le
        have hlt_b5 : t - m - 1 < (b + 5) * M := by omega
        have hq_lt_b5 : q < b + 5 := (Nat.div_lt_iff_lt_mul (by omega : 0 < M)).mpr hlt_b5
        exact Finset.mem_Icc.mpr ⟨by omega, hb_le_q⟩
      calc
        ((Finset.range W).filter (fun b => m + b * M < t ∧ t ≤ m + (b + 5) * M)).card
            ≤ (Finset.Icc (q - 4) q).card := Finset.card_le_card hsub
        _ = q + 1 - (q - 4) := Nat.card_Icc (q - 4) q
        _ ≤ 5 := by omega
    calc
      ∑ t ∈ T, ((Finset.range W).filter (fun b => m + b * M < t ∧ t ≤ m + (b + 5) * M)).card
          ≤ ∑ _t ∈ T, 5 := Finset.sum_le_sum hpt
      _ = 5 * T.card := by simp [mul_comm]
  -- Pick a minimum-size window b₀ ∈ Finset.range W
  have hne : (Finset.range W).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨b₀, hb₀, hmin⟩ := Finset.exists_min_image (Finset.range W) (fun b => (win b).card) hne
  have hW_mul : W * (win b₀).card ≤ 5 * T.card := by
    calc
      W * (win b₀).card = ∑ _b ∈ Finset.range W, (win b₀).card := by simp
      _ ≤ ∑ b ∈ Finset.range W, (win b).card := Finset.sum_le_sum (fun b hb => hmin b hb)
      _ ≤ 5 * T.card := hsum_win
  have hb₀_ap : S'.card ^ 4 ≤ (win b₀).card ^ 7 := hwin_bound b₀ hb₀
  calc
    W ^ 7 * S'.card ^ 4 ≤ W ^ 7 * (win b₀).card ^ 7 := Nat.mul_le_mul_left _ hb₀_ap
    _ = (W * (win b₀).card) ^ 7 := by ring
    _ ≤ (5 * T.card) ^ 7 := Nat.pow_le_pow_left hW_mul 7
    _ = 5 ^ 7 * T.card ^ 7 := by ring

/-! ### Section 4: Dyadic Summation & Hall Condition Verification -/

/-- Every subset `S ⊆ [1, n]` satisfies Hall's condition `|S| ≤ |N(S)|` in `(m, m + L)`
whenever `13 ^ 7 * n ^ 10 ≤ (L - 1) ^ 7`. -/
private lemma hall_condition_world_record
    (n m L : ℕ) (hn : 1 ≤ n) (hL : 13 ^ 7 * n ^ 10 ≤ (L - 1) ^ 7)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 n) :
    S.card ≤ ((Finset.Ioo m (m + L)).filter (fun t => ∃ k ∈ S, k ∣ t)).card := by
  classical
  let T : Finset ℕ := (Finset.Ioo m (m + L)).filter (fun t => ∃ k ∈ S, k ∣ t)
  by_contra hlt
  push Not at hlt
  have hS_pos : 1 ≤ S.card := by omega
  have hS_le_n : S.card ≤ n := by
    calc S.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hS
    _ = n := by simp
  -- Deduce 13 * n ≤ L - 1
  have h13n : 13 * n ≤ L - 1 := by
    by_contra h13
    push Not at h13
    have hpow : (L - 1) ^ 7 < (13 * n) ^ 7 := Nat.pow_lt_pow_left h13 (by norm_num)
    have h10 : (13 * n) ^ 7 ≤ 13 ^ 7 * n ^ 10 := by
      have : n ^ 7 ≤ n ^ 10 := Nat.pow_le_pow_right hn (by norm_num)
      calc (13 * n) ^ 7 = 13 ^ 7 * n ^ 7 := by ring
      _ ≤ 13 ^ 7 * n ^ 10 := Nat.mul_le_mul_left _ this
    omega
  -- Dyadic partition: S_j = {k ∈ S : 2^j * k ≤ n ∧ n < 2^(j+1) * k}
  let slice : ℕ → Finset ℕ := fun j =>
    S.filter (fun k => 2 ^ j * k ≤ n ∧ n < 2 ^ (j + 1) * k)
  -- Partition identity: S.card = ∑ j ∈ range (n + 1), (slice j).card
  have hpart : S.card = ∑ j ∈ Finset.range (n + 1), (slice j).card := by
    have hbi : S = (Finset.range (n + 1)).biUnion slice := by
      ext k
      simp only [Finset.mem_biUnion, Finset.mem_range, slice, Finset.mem_filter]
      constructor
      · intro hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp (hS hk)).1
        have hkn : k ≤ n := (Finset.mem_Icc.mp (hS hk)).2
        have hq_pos : 1 ≤ n / k := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr (by simpa using hkn)
        let j : ℕ := Nat.log 2 (n / k)
        have hj_le : 2 ^ j ≤ n / k := Nat.pow_log_le_self 2 (by omega)
        have hj_lt : n / k < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) (n / k)
        have hj_range : j < n + 1 := by
          have : j ≤ n / k := le_trans (le_of_lt (Nat.lt_two_pow_self)) hj_le
          have : n / k ≤ n := Nat.div_le_self n k
          omega
        refine ⟨j, hj_range, hk, ?_, ?_⟩
        · exact (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hj_le
        · exact (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mp hj_lt
      · rintro ⟨_, _, hk, _, _⟩
        exact hk
    have hdisj : Set.PairwiseDisjoint (Finset.range (n + 1) : Set ℕ) slice := by
      intro i _ j _ hij
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro k hki hkj
      have hi := (Finset.mem_filter.mp hki).2
      have hj := (Finset.mem_filter.mp hkj).2
      rcases lt_or_gt_of_ne hij with hlt_ij | hgt_ij
      · have hle : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hlt_ij
        have : 2 ^ (i + 1) * k ≤ 2 ^ j * k := Nat.mul_le_mul_right k hle
        omega
      · have hle : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hgt_ij
        have : 2 ^ (j + 1) * k ≤ 2 ^ i * k := Nat.mul_le_mul_right k hle
        omega
    conv_lhs => rw [hbi]
    exact Finset.card_biUnion hdisj
  -- Per-slice inequality in ℕ: (3^j * |S_j|)^4 * (L - 1)^7 ≤ (10 * n * |T|)^7
  have hslice_bound : ∀ j ∈ Finset.range (n + 1),
      (3 ^ j * (slice j).card) ^ 4 * (L - 1) ^ 7 ≤ (10 * n * T.card) ^ 7 := by
    intro j _
    by_cases hempty : (slice j).card = 0
    · simp [hempty]
    · obtain ⟨k₀, hk₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hempty)
      have hk₀_in_S : k₀ ∈ S := (Finset.mem_filter.mp hk₀).1
      have hk₀_1 : 1 ≤ k₀ := (Finset.mem_Icc.mp (hS hk₀_in_S)).1
      have hk₀_2j : 2 ^ j * k₀ ≤ n := (Finset.mem_filter.mp hk₀).2.1
      let M : ℕ := n / 2 ^ j
      have h2j_pos : 0 < 2 ^ j := Nat.two_pow_pos j
      have hM_pos : 1 ≤ M := by
        have : 2 ^ j ≤ n := le_trans (by nlinarith) hk₀_2j
        exact (Nat.le_div_iff_mul_le h2j_pos).mpr (by simpa using this)
      have h2jM : 2 ^ j * M ≤ n := by
        rw [mul_comm]; exact Nat.div_mul_le_self n (2 ^ j)
      have hM_le_n : M ≤ n := Nat.div_le_self n (2 ^ j)
      have hslice_sub : slice j ⊆ S := Finset.filter_subset _ _
      have hslice_le : ∀ k ∈ slice j, 1 ≤ k ∧ k ≤ M := by
        intro k hk
        have hkS : k ∈ S := (Finset.mem_filter.mp hk).1
        have hk2 : 2 ^ j * k ≤ n := (Finset.mem_filter.mp hk).2.1
        refine ⟨(Finset.mem_Icc.mp (hS hkS)).1, ?_⟩
        exact (Nat.le_div_iff_mul_le h2j_pos).mpr (by rwa [mul_comm])
      have h13M : 13 * M ≤ L - 1 := le_trans (Nat.mul_le_mul_left 13 hM_le_n) h13n
      have hB5 : 5 ≤ (L - 1) / M := by
        have : 13 ≤ (L - 1) / M := (Nat.le_div_iff_mul_le (by omega : 0 < M)).mpr (by linarith)
        omega
      have hblk := block_five_ap_bound m L M hM_pos S (slice j) hslice_sub hslice_le hB5
      -- Pure ℕ bound: 2^j * (L - 1) ≤ 2 * n * ((L - 1) / M - 4)
      have hB_lb : 2 ^ j * (L - 1) ≤ 2 * n * ((L - 1) / M - 4) := by
        have hrem : L - 1 < ((L - 1) / M + 1) * M := by
          have := Nat.div_add_mod (L - 1) M
          have := Nat.mod_lt (L - 1) (by omega : 0 < M)
          nlinarith
        have hstep : L - 1 ≤ 2 * M * ((L - 1) / M - 4) := by
          have hB_ge : 4 ≤ (L - 1) / M := by omega
          have hsub_mul : ((L - 1) / M - 4) * M + 4 * M = ((L - 1) / M) * M := by
            rw [← Nat.add_mul, Nat.sub_add_cancel hB_ge]
          nlinarith
        calc
          2 ^ j * (L - 1) ≤ 2 ^ j * (2 * M * ((L - 1) / M - 4)) := Nat.mul_le_mul_left _ hstep
          _ = 2 * (2 ^ j * M) * ((L - 1) / M - 4) := by ring
          _ ≤ 2 * n * ((L - 1) / M - 4) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 h2jM)
      have h81_128 : (3 ^ j) ^ 4 ≤ (2 ^ j) ^ 7 := by
        calc
          (3 ^ j) ^ 4 = (3 ^ 4) ^ j := by rw [← pow_mul, mul_comm, pow_mul]
          _ = 81 ^ j := by norm_num
          _ ≤ 128 ^ j := Nat.pow_le_pow_left (by norm_num) j
          _ = (2 ^ 7) ^ j := by norm_num
          _ = (2 ^ j) ^ 7 := by rw [← pow_mul, mul_comm, pow_mul]
      calc
        (3 ^ j * (slice j).card) ^ 4 * (L - 1) ^ 7
            = (3 ^ j) ^ 4 * ((L - 1) ^ 7 * (slice j).card ^ 4) := by ring
        _ ≤ (2 ^ j) ^ 7 * ((L - 1) ^ 7 * (slice j).card ^ 4) := Nat.mul_le_mul_right _ h81_128
        _ = (2 ^ j * (L - 1)) ^ 7 * (slice j).card ^ 4 := by ring
        _ ≤ (2 * n * ((L - 1) / M - 4)) ^ 7 * (slice j).card ^ 4 :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hB_lb 7)
        _ = (2 * n) ^ 7 * (((L - 1) / M - 4) ^ 7 * (slice j).card ^ 4) := by ring
        _ ≤ (2 * n) ^ 7 * (5 ^ 7 * T.card ^ 7) := Nat.mul_le_mul_left _ hblk
        _ = (10 * n * T.card) ^ 7 := by ring
  -- Sum over j ∈ range (n + 1) in ℝ using Real.sqrt twice (avoiding Real.rpow in the core!)
  have hL1_pos_real : (0 : ℝ) < (L - 1 : ℕ) := by
    have : 1 ≤ L - 1 := by omega
    exact_mod_cast this
  let X : ℝ := ((10 * n * T.card : ℕ) : ℝ) ^ 7 / ((L - 1 : ℕ) : ℝ) ^ 7
  have hX_nonneg : 0 ≤ X := div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (le_of_lt hL1_pos_real) _)
  let R : ℝ := Real.sqrt (Real.sqrt X)
  have hR_nonneg : 0 ≤ R := Real.sqrt_nonneg _
  have hR_pow4 : R ^ 4 = X := by
    have h1 : R ^ 2 = Real.sqrt X := Real.sq_sqrt (Real.sqrt_nonneg X)
    calc R ^ 4 = (R ^ 2) ^ 2 := by ring
    _ = (Real.sqrt X) ^ 2 := by rw [h1]
    _ = X := Real.sq_sqrt hX_nonneg
  have hslice_real : ∀ j ∈ Finset.range (n + 1),
      ((slice j).card : ℝ) ≤ R * ((1 : ℝ) / 3) ^ j := by
    intro j hj
    have hnat : ((3 ^ j * (slice j).card : ℕ) : ℝ) ^ 4 * ((L - 1 : ℕ) : ℝ) ^ 7 ≤
        ((10 * n * T.card : ℕ) : ℝ) ^ 7 := by
      exact_mod_cast hslice_bound j hj
    have hdiv : ((3 ^ j * (slice j).card : ℕ) : ℝ) ^ 4 ≤ R ^ 4 := by
      rw [hR_pow4]
      exact (le_div_iff₀ (pow_pos hL1_pos_real 7)).mpr hnat
    have hleR : ((3 ^ j * (slice j).card : ℕ) : ℝ) ≤ R := by
      by_contra hgt
      push Not at hgt
      have : R ^ 4 < ((3 ^ j * (slice j).card : ℕ) : ℝ) ^ 4 :=
        pow_lt_pow_left₀ hgt hR_nonneg (by norm_num)
      linarith
    have h3pos : (0 : ℝ) < (3 : ℝ) ^ j := pow_pos (by norm_num) j
    have hcast : ((3 ^ j * (slice j).card : ℕ) : ℝ) = (3 : ℝ) ^ j * ((slice j).card : ℝ) := by
      push_cast; ring
    rw [hcast] at hleR
    rw [one_div, inv_pow, ← div_eq_mul_inv]
    exact (le_div_iff₀ h3pos).mpr (by linarith)
  have hgeom : ∑ j ∈ Finset.range (n + 1), ((1 : ℝ) / 3) ^ j ≤ 3 / 2 := by
    have haux : ∀ N : ℕ, ∑ j ∈ Finset.range N, ((1 : ℝ) / 3) ^ j =
        (3 / 2 : ℝ) * (1 - ((1 : ℝ) / 3) ^ N) := by
      intro N
      induction N with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    rw [haux (n + 1)]
    have hnonneg : (0 : ℝ) ≤ ((1 : ℝ) / 3) ^ (n + 1) := pow_nonneg (by norm_num) _
    linarith
  have hS_le_R : (S.card : ℝ) ≤ R * (3 / 2) := by
    have hcast_part : (S.card : ℝ) = ∑ j ∈ Finset.range (n + 1), ((slice j).card : ℝ) := by
      exact_mod_cast hpart
    rw [hcast_part]
    calc
      ∑ j ∈ Finset.range (n + 1), ((slice j).card : ℝ)
          ≤ ∑ j ∈ Finset.range (n + 1), R * ((1 : ℝ) / 3) ^ j := Finset.sum_le_sum hslice_real
      _ = R * ∑ j ∈ Finset.range (n + 1), ((1 : ℝ) / 3) ^ j := by rw [← Finset.mul_sum]
      _ ≤ R * (3 / 2) := mul_le_mul_of_nonneg_left hgeom hR_nonneg
  have hS_pow4 : (S.card : ℝ) ^ 4 ≤ (81 / 16 : ℝ) * X := by
    have h1 := pow_le_pow_left₀ (Nat.cast_nonneg S.card) hS_le_R 4
    calc (S.card : ℝ) ^ 4 ≤ (R * (3 / 2)) ^ 4 := h1
    _ = (81 / 16 : ℝ) * R ^ 4 := by ring
    _ = (81 / 16 : ℝ) * X := by rw [hR_pow4]
  have hmain_real :
      16 * (S.card : ℝ) ^ 4 * ((L - 1 : ℕ) : ℝ) ^ 7 ≤
        81 * ((10 * n * T.card : ℕ) : ℝ) ^ 7 := by
    have hpos7 : (0 : ℝ) < ((L - 1 : ℕ) : ℝ) ^ 7 := pow_pos hL1_pos_real 7
    have h2 : (S.card : ℝ) ^ 4 * ((L - 1 : ℕ) : ℝ) ^ 7 ≤
        (81 / 16 : ℝ) * ((10 * n * T.card : ℕ) : ℝ) ^ 7 := by
      have hX_mul : X * ((L - 1 : ℕ) : ℝ) ^ 7 = ((10 * n * T.card : ℕ) : ℝ) ^ 7 :=
        div_mul_cancel₀ _ (ne_of_gt hpos7)
      calc
        (S.card : ℝ) ^ 4 * ((L - 1 : ℕ) : ℝ) ^ 7
            ≤ ((81 / 16 : ℝ) * X) * ((L - 1 : ℕ) : ℝ) ^ 7 :=
              mul_le_mul_of_nonneg_right hS_pow4 (le_of_lt hpos7)
        _ = (81 / 16 : ℝ) * (X * ((L - 1 : ℕ) : ℝ) ^ 7) := by ring
        _ = (81 / 16 : ℝ) * ((10 * n * T.card : ℕ) : ℝ) ^ 7 := by rw [hX_mul]
    linarith
  have hmain_nat : 16 * S.card ^ 4 * (L - 1) ^ 7 ≤ 81 * (10 * n * T.card) ^ 7 := by
    exact_mod_cast hmain_real
  -- Contradict hL using T.card < S.card ≤ n and 16 * 13^7 = 1003976272 > 810000000 = 81 * 10^7
  have hT_pow7 : T.card ^ 7 < S.card ^ 7 := Nat.pow_lt_pow_left hlt (by norm_num)
  have hS_pow3 : S.card ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hS_le_n 3
  have hS4_pos : 0 < S.card ^ 4 := pow_pos (by omega) 4
  have hupper : 81 * (10 * n * T.card) ^ 7 < 81 * 10 ^ 7 * S.card ^ 4 * n ^ 10 := by
    have h1 : 81 * (10 * n * T.card) ^ 7 = 81 * 10 ^ 7 * n ^ 7 * T.card ^ 7 := by ring
    have h2 : 81 * 10 ^ 7 * n ^ 7 * T.card ^ 7 < 81 * 10 ^ 7 * n ^ 7 * S.card ^ 7 :=
      Nat.mul_lt_mul_of_pos_left hT_pow7 (by positivity)
    have h3 : 81 * 10 ^ 7 * n ^ 7 * S.card ^ 7 ≤ 81 * 10 ^ 7 * S.card ^ 4 * n ^ 10 := by
      have : n ^ 7 * S.card ^ 7 = S.card ^ 4 * (n ^ 7 * S.card ^ 3) := by ring
      have h4 : n ^ 7 * S.card ^ 3 ≤ n ^ 7 * n ^ 3 := Nat.mul_le_mul_left _ hS_pow3
      have h5 : n ^ 7 * n ^ 3 = n ^ 10 := by ring
      nlinarith
    omega
  have hlower : 16 * 13 ^ 7 * S.card ^ 4 * n ^ 10 ≤ 16 * S.card ^ 4 * (L - 1) ^ 7 := by
    calc
      16 * 13 ^ 7 * S.card ^ 4 * n ^ 10
          = 16 * S.card ^ 4 * (13 ^ 7 * n ^ 10) := by ring
      _ ≤ 16 * S.card ^ 4 * (L - 1) ^ 7 := Nat.mul_le_mul_left _ hL
  have hconst : 81 * 10 ^ 7 * S.card ^ 4 * n ^ 10 < 16 * 13 ^ 7 * S.card ^ 4 * n ^ 10 := by
    have hpos : 0 < S.card ^ 4 * n ^ 10 := Nat.mul_pos hS4_pos (pow_pos (by omega) 10)
    have hnum : 81 * 10 ^ 7 < 16 * 13 ^ 7 := by norm_num
    calc
      81 * 10 ^ 7 * S.card ^ 4 * n ^ 10 = (81 * 10 ^ 7) * (S.card ^ 4 * n ^ 10) := by ring
      _ < (16 * 13 ^ 7) * (S.card ^ 4 * n ^ 10) := Nat.mul_lt_mul_of_pos_right hnum hpos
      _ = 16 * 13 ^ 7 * S.card ^ 4 * n ^ 10 := by ring
  omega

/-! ### Section 5: Main Pure-Mathlib World-Record Theorems (Zero Custom Definitions) -/

/-- **PPL 173 World-Record Upper Bound (Pure `ℕ` Existence Form):**
For every `n ≥ 1`, every `m : ℕ`, and every `L : ℕ` satisfying `13 ^ 7 * n ^ 10 ≤ (L - 1) ^ 7`,
there exist `n` distinct natural numbers `a 1, ..., a n` in the open interval `(m, m + L)`
such that `k ∣ a k` for all `1 ≤ k ≤ n`. -/
theorem ppl173_world_record_nat (n m L : ℕ) (hn : 1 ≤ n)
    (hL : 13 ^ 7 * n ^ 10 ≤ (L - 1) ^ 7) :
    ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k < m + L ∧ k ∣ a k) := by
  classical
  let t : { k : ℕ // k ∈ Finset.Icc 1 n } → Finset ℕ :=
    fun k => (Finset.Ioo m (m + L)).filter (fun x => k.1 ∣ x)
  have hHall : ∀ s : Finset { k : ℕ // k ∈ Finset.Icc 1 n }, s.card ≤ (s.biUnion t).card := by
    intro s
    let S : Finset ℕ := s.map ⟨Subtype.val, Subtype.val_injective⟩
    have hS_sub : S ⊆ Finset.Icc 1 n := by
      intro k hk
      rcases Finset.mem_map.mp hk with ⟨⟨k', hk'⟩, _, rfl⟩
      exact hk'
    have hEq : s.biUnion t = (Finset.Ioo m (m + L)).filter (fun x => ∃ k ∈ S, k ∣ x) := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_filter, t, S, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨k, hk, hxIoo, hdvd⟩
        exact ⟨hxIoo, k.1, ⟨k, hk, rfl⟩, hdvd⟩
      · rintro ⟨hxIoo, _, ⟨k, hk, rfl⟩, hdvd⟩
        exact ⟨k, hk, hxIoo, hdvd⟩
    rw [hEq, ← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
    exact hall_condition_world_record n m L hn hL S hS_sub
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  refine ⟨fun k => if h : k ∈ Finset.Icc 1 n then f ⟨k, h⟩ else 0, ?_, ?_⟩
  · intro i j hi1 hin hj1 hjn hEq
    have hi : i ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hi1, hin⟩
    have hj : j ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hj1, hjn⟩
    simp only [hi, hj, dite_true] at hEq
    exact congrArg Subtype.val (hf_inj hEq)
  · intro k hk1 hkn
    have hk : k ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hk1, hkn⟩
    simp only [hk, dite_true]
    have hmem := hf_mem ⟨k, hk⟩
    have hflt := Finset.mem_filter.mp hmem
    have hIoo := Finset.mem_Ioo.mp hflt.1
    exact ⟨hIoo.1, hIoo.2, hflt.2⟩

/-- **PPL 173 World-Record Upper Bound (Verbatim Open-Interval `f(n, m) ≤ 13 n^{10/7} + 2`):**
For every `n ≥ 1` and every `m : ℕ`, the minimal `L` such that `(m, m + L)` contains `n` distinct
multiples `a_1, ..., a_n` with `k ∣ a_k` (`1 ≤ k ≤ n`) satisfies
`f(n, m) ≤ 13 * n ^ (10 / 7) + 2`. -/
theorem ppl173_world_record_rpow (n m : ℕ) (hn : 1 ≤ n) :
    ((sInf ({ L : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k < m + L ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ)
      ≤ 13 * (n : ℝ) ^ ((10 : ℝ) / 7) + 2 := by
  let x : ℝ := 13 * (n : ℝ) ^ ((10 : ℝ) / 7)
  let L₀ : ℕ := Nat.ceil x + 1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hx_nonneg : 0 ≤ x := by positivity
  have hceil_ge : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
  have hceil_lt : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx_nonneg
  have hL₀_pow7 : 13 ^ 7 * n ^ 10 ≤ (L₀ - 1) ^ 7 := by
    have hsub : L₀ - 1 = Nat.ceil x := by simp [L₀]
    rw [hsub]
    have hreal : (13 : ℝ) ^ 7 * (n : ℝ) ^ 10 ≤ ((Nat.ceil x : ℕ) : ℝ) ^ 7 := by
      have hx7 : x ^ 7 = (13 : ℝ) ^ 7 * (n : ℝ) ^ 10 := by
        dsimp [x]
        rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((10 : ℝ) / 7)) 7,
          ← Real.rpow_mul (le_of_lt hn_pos)]
        have h10 : ((10 : ℝ) / 7) * ((7 : ℕ) : ℝ) = ((10 : ℕ) : ℝ) := by norm_num
        rw [h10, Real.rpow_natCast]
      rw [← hx7]
      exact pow_le_pow_left₀ hx_nonneg hceil_ge 7
    exact_mod_cast hreal
  have hL₀_mem : L₀ ∈ ({ L : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k < m + L ∧ k ∣ a k) } : Set ℕ) :=
    ppl173_world_record_nat n m L₀ hn hL₀_pow7
  have hsInf_le : sInf ({ L : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k < m + L ∧ k ∣ a k) } : Set ℕ) ≤ L₀ :=
    Nat.sInf_le hL₀_mem
  have hsInf_real : ((sInf ({ L : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k < m + L ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ) ≤ (L₀ : ℝ) := by
    exact_mod_cast hsInf_le
  have hL₀_real : (L₀ : ℝ) ≤ x + 2 := by
    have : (L₀ : ℝ) = (Nat.ceil x : ℝ) + 1 := by simp [L₀]
    linarith
  exact le_trans hsInf_real hL₀_real

/-- **PPL 173 World-Record Upper Bound (Closed-Right Interval `(m, m + h]` Form):**
Matching Erdős–Pomerance (1980), van Doorn (2026), and Kominers (2026), the minimal `h` such that
`(m, m + h]` contains `n` distinct multiples `a_1, ..., a_n` with `k ∣ a_k` (`1 ≤ k ≤ n`)
satisfies `h ≤ 13 * n ^ (10 / 7) + 1` for all `n ≥ 1` and `m : ℕ`. -/
theorem ppl173_world_record_closed (n m : ℕ) (hn : 1 ≤ n) :
    ((sInf ({ h : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k ≤ m + h ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ)
      ≤ 13 * (n : ℝ) ^ ((10 : ℝ) / 7) + 1 := by
  let x : ℝ := 13 * (n : ℝ) ^ ((10 : ℝ) / 7)
  let h₀ : ℕ := Nat.ceil x
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hx_nonneg : 0 ≤ x := by positivity
  have hceil_ge : x ≤ (h₀ : ℝ) := Nat.le_ceil x
  have hceil_lt : (h₀ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx_nonneg
  have hh₀_pow7 : 13 ^ 7 * n ^ 10 ≤ ((h₀ + 1) - 1) ^ 7 := by
    simp only [Nat.add_sub_cancel]
    have hreal : (13 : ℝ) ^ 7 * (n : ℝ) ^ 10 ≤ ((h₀ : ℕ) : ℝ) ^ 7 := by
      have hx7 : x ^ 7 = (13 : ℝ) ^ 7 * (n : ℝ) ^ 10 := by
        dsimp [x]
        rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((10 : ℝ) / 7)) 7,
          ← Real.rpow_mul (le_of_lt hn_pos)]
        have h10 : ((10 : ℝ) / 7) * ((7 : ℕ) : ℝ) = ((10 : ℕ) : ℝ) := by norm_num
        rw [h10, Real.rpow_natCast]
      rw [← hx7]
      exact pow_le_pow_left₀ hx_nonneg hceil_ge 7
    exact_mod_cast hreal
  have hh₀_mem : h₀ ∈ ({ h : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k ≤ m + h ∧ k ∣ a k) } : Set ℕ) := by
    obtain ⟨a, hinj, hprop⟩ := ppl173_world_record_nat n m (h₀ + 1) hn hh₀_pow7
    refine ⟨a, hinj, fun k hk1 hkn => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hprop k hk1 hkn
    exact ⟨h1, by omega, h3⟩
  have hsInf_le : sInf ({ h : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k ≤ m + h ∧ k ∣ a k) } : Set ℕ) ≤ h₀ :=
    Nat.sInf_le hh₀_mem
  have hsInf_real : ((sInf ({ h : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k ≤ m + h ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ) ≤ (h₀ : ℝ) := by
    exact_mod_cast hsInf_le
  exact le_trans hsInf_real (le_of_lt hceil_lt)

/-- **PPL 173 World-Record Upper Bound (`⨆ m, f(n, m) ≤ 13 n^{10/7} + 2` Supremum Form):**
Directly states the uniform upper bound on `max_m f(n, m)` over all `m : ℕ` for every `n ≥ 1`. -/
theorem ppl173_world_record_iSup (n : ℕ) (hn : 1 ≤ n) :
    (⨆ m : ℕ, ((sInf ({ L : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k < m + L ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ))
      ≤ 13 * (n : ℝ) ^ ((10 : ℝ) / 7) + 2 :=
  ciSup_le fun m => ppl173_world_record_rpow n m hn

end PPL173
