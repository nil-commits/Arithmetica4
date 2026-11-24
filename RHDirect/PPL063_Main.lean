/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-!
# PPL 063 (Erdős Problem #161): Hypergraph Discrepancy Jumps `F^{(t)}(n, α)`

## Scope & Honest Labeling
This file is a **partial research & formalization milestone** for Erdős Problem #161 ($500, OPEN),
targeting the corrected **"smallest `m`"** definition (`Hypergraph.balancedColoringThreshold` in
`google-deepmind/formal-conjectures`, `FormalConjectures/ErdosProblems/161.lean`) with its
`α = 0` Ramsey convention. All main theorem signatures are stated **directly** in pure Mathlib
(zero custom definitions in main theorem types).

- **What IS proved in this file (100% pure Mathlib, zero `sorry`):**
  1. **Averaging Monotonicity Lemma & Exact-Size Reduction** for all `t ≥ 1`.
  2. **Ramsey Anchor Lemma** at small `α` (`0 ≤ α ≤ 1 / m.choose t`).
  3. **Universal Probabilistic Upper Bound:** `F^{(t)}(n, α) = O_{t, α}((log n)^{1/(t-1)})`
     for **all** `t ≥ 2` and **all** `α ∈ [0, 1/2)` (pure-`Finset` Hoeffding bound).
  4. **Complete `t = 2` Non-Jump Theorem** (settling the `t = 2` slice of `erdos_161.parts.i`):
     `F^{(2)}(n, α) =Θ[atTop] log n` for all `α ∈ [0, 1/2)`, hence no jumps on `[0, 1/2)`.
  5. **Complete `t = 3` Positive-Density Collapse** (Conlon–Fox–Sudakov [CFS11], settling the
     `t = 3` slice of `erdos_161.parts.ii`): `F^{(3)}(n, α) =Θ[atTop] √(log n)` for all
     `α ∈ (0, 1/2)`.
  6. **General `t ≥ 2` (and `t ≥ 4`) High-Density Collapse:** Via Erdős (1964) multipartite
     hypergraph Turán + an exact Inclusion-Exclusion Discrepancy obstruction,
     `F^{(t)}(n, α) =Θ[atTop] (log n)^{1/(t-1)}` for all `t ≥ 2` and all `α ∈ (α_IE(t), 1/2)`
     where `α_IE(t) = 1/2 - t! / (2 * ∑_{r=1}^t (t.choose r) * r^t)` (e.g. `α_IE(4) = 41 / 85`).
- **What remains OPEN (NOT claimed):**
  - Full `erdos_161.parts.ii` for `t ≥ 4` on `(0, α_IE(t)]` (blocked by Hypergraph Nikiforov).
  - Unconditional separation of `α = 0` from `α > 0` for `t ≥ 3` in `erdos_161.parts.i`
    (equivalent to improving hypergraph Ramsey lower bounds, Erdős–Hajnal–Rado #562).
-/

namespace PPL063

open Filter Asymptotics

/-- Internal shorthand matching `Hypergraph.balancedColoringThreshold` verbatim.
All public main theorems inline this expression directly. -/
private noncomputable abbrev F (n t : ℕ) (α : ℝ) : ℕ :=
  sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
    ∀ b : Bool,
      0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
      α * (X.card.choose t : ℝ) ≤ (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)}

/-- Number of `t`-subsets of `X` assigned color `b` by `c`. -/
private def colorCount {n : ℕ} (c : Finset (Fin n) → Bool) (t : ℕ) (X : Finset (Fin n))
    (b : Bool) : ℕ :=
  ((X.powersetCard t).filter (fun e => c e = b)).card

/-! ### Section 1: Averaging Monotonicity Lemma & Basic Structural Properties -/

/-- Double-counting identity: summing `colorCount c t Y b` over all `m`-subsets `Y ⊆ X`
counts every `t`-subset of `X` of color `b` exactly `(X.card - t).choose (m - t)` times. -/
private lemma sum_colorCount_powersetCard {n : ℕ} (c : Finset (Fin n) → Bool) (t m : ℕ)
    (X : Finset (Fin n)) (htm : t ≤ m) (_hmX : m ≤ X.card) (b : Bool) :
    ∑ Y ∈ X.powersetCard m, colorCount c t Y b =
      (X.card - t).choose (m - t) * colorCount c t X b := by
  classical
  let E : Finset (Finset (Fin n)) := (X.powersetCard t).filter (fun e => c e = b)
  have hL : ∑ Y ∈ X.powersetCard m, colorCount c t Y b =
      ∑ Y ∈ X.powersetCard m, ∑ e ∈ E, (if e ⊆ Y then 1 else 0) := by
    refine Finset.sum_congr rfl fun Y hY => ?_
    have hYX : Y ⊆ X := (Finset.mem_powersetCard.mp hY).1
    dsimp only [colorCount]
    have hEq : (Y.powersetCard t).filter (fun e => c e = b) =
        E.filter (fun e => e ⊆ Y) := by
      ext e
      simp only [E, Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨heY, hecard⟩, hcb⟩
        exact ⟨⟨⟨heY.trans hYX, hecard⟩, hcb⟩, heY⟩
      · rintro ⟨⟨⟨_, hecard⟩, hcb⟩, heY⟩
        exact ⟨⟨heY, hecard⟩, hcb⟩
    rw [hEq, Finset.card_filter]
  rw [hL, Finset.sum_comm]
  have hinner : ∀ e ∈ E,
      (∑ Y ∈ X.powersetCard m, (if e ⊆ Y then (1 : ℕ) else 0)) =
        (X.card - t).choose (m - t) := by
    intro e he
    have heX : e ⊆ X := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).1
    have hecard : e.card = t := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
    rw [← Finset.card_filter]
    have hbij : ((X.powersetCard m).filter (fun Y => e ⊆ Y)).card =
        ((X \ e).powersetCard (m - t)).card := by
      refine Finset.card_bij (fun Y _ => Y \ e) ?_ ?_ ?_
      · intro Y hY
        rcases Finset.mem_filter.mp hY with ⟨hYm, heY⟩
        rcases Finset.mem_powersetCard.mp hYm with ⟨hYX, hYcard⟩
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.sdiff_subset_sdiff hYX (Finset.Subset.refl e), ?_⟩
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr heY, hYcard, hecard]
      · intro Y₁ hY₁ Y₂ hY₂ hEq
        have heY₁ : e ⊆ Y₁ := (Finset.mem_filter.mp hY₁).2
        have heY₂ : e ⊆ Y₂ := (Finset.mem_filter.mp hY₂).2
        have h1 : Y₁ = (Y₁ \ e) ∪ e := (Finset.sdiff_union_of_subset heY₁).symm
        have h2 : Y₂ = (Y₂ \ e) ∪ e := (Finset.sdiff_union_of_subset heY₂).symm
        rw [h1, h2, hEq]
      · intro Z hZ
        rcases Finset.mem_powersetCard.mp hZ with ⟨hZXe, hZcard⟩
        have hdisj : Disjoint Z e := Finset.disjoint_of_subset_left hZXe Finset.sdiff_disjoint
        refine ⟨Z ∪ e, ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_powersetCard]
          refine ⟨⟨Finset.union_subset (hZXe.trans Finset.sdiff_subset) heX, ?_⟩,
            Finset.subset_union_right⟩
          rw [Finset.card_union_of_disjoint hdisj, hZcard, hecard]
          omega
        · exact Finset.union_sdiff_cancel_right hdisj
    rw [hbij, Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_eq_left.mpr heX, hecard]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_comm]
  rfl

/-- **Averaging Monotonicity Lemma (Density Form):**
If every `m`-subset `Y ⊆ X` satisfies `0 < colorCount c t Y b` and
`α * m.choose t ≤ colorCount c t Y b` (with `t ≤ m ≤ X.card`), then `X` satisfies the same bounds
with `X.card.choose t`. -/
theorem averaging_monotonicity {n : ℕ} (c : Finset (Fin n) → Bool) (t m : ℕ) (α : ℝ)
    (X : Finset (Fin n)) (htm : t ≤ m) (hmX : m ≤ X.card) (b : Bool)
    (hY : ∀ Y ∈ X.powersetCard m,
      0 < ((Y.powersetCard t).filter (fun e => c e = b)).card ∧
      α * (m.choose t : ℝ) ≤ (((Y.powersetCard t).filter (fun e => c e = b)).card : ℝ)) :
    0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
    α * (X.card.choose t : ℝ) ≤ (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ) := by
  have hsum := sum_colorCount_powersetCard c t m X htm hmX b
  have hchoose_pos : 0 < (X.card - t).choose (m - t) :=
    Nat.choose_pos (by omega)
  have hXm_pos : 0 < X.card.choose m := Nat.choose_pos hmX
  have hpos_count : 0 < colorCount c t X b := by
    obtain ⟨Y₀, hY₀⟩ : (X.powersetCard m).Nonempty := by
      rw [← Finset.card_pos, Finset.card_powersetCard]
      exact hXm_pos
    have hY₀_pos : 0 < colorCount c t Y₀ b := (hY Y₀ hY₀).1
    have hsum_pos : 0 < ∑ Y ∈ X.powersetCard m, colorCount c t Y b :=
      lt_of_lt_of_le hY₀_pos
        (Finset.single_le_sum (f := fun Y => colorCount c t Y b) (fun _ _ => Nat.zero_le _) hY₀)
    rw [hsum] at hsum_pos
    exact Nat.pos_of_mul_pos_left hsum_pos
  refine ⟨hpos_count, ?_⟩
  have hsum_real :
      (X.card.choose m : ℝ) * (α * (m.choose t : ℝ)) ≤
        ((X.card - t).choose (m - t) : ℝ) * (colorCount c t X b : ℝ) := by
    have h1 : (X.card.choose m : ℝ) * (α * (m.choose t : ℝ)) =
        ∑ _Y ∈ X.powersetCard m, (α * (m.choose t : ℝ)) := by
      rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
    have h2 : ∑ _Y ∈ X.powersetCard m, (α * (m.choose t : ℝ)) ≤
        ∑ Y ∈ X.powersetCard m, (colorCount c t Y b : ℝ) :=
      Finset.sum_le_sum fun Y hYm => (hY Y hYm).2
    have h3 : (∑ Y ∈ X.powersetCard m, (colorCount c t Y b : ℝ)) =
        ((X.card - t).choose (m - t) : ℝ) * (colorCount c t X b : ℝ) := by
      exact_mod_cast hsum
    linarith
  have hident_nat : X.card.choose m * m.choose t = X.card.choose t * (X.card - t).choose (m - t) :=
    Nat.choose_mul (n := X.card) (k := m) (s := t) htm
  have hident : (X.card.choose m : ℝ) * (m.choose t : ℝ) =
      (X.card.choose t : ℝ) * ((X.card - t).choose (m - t) : ℝ) := by
    exact_mod_cast hident_nat
  have hchoose_pos_r : (0 : ℝ) < ((X.card - t).choose (m - t) : ℝ) := by
    exact_mod_cast hchoose_pos
  have hmul : ((X.card - t).choose (m - t) : ℝ) * (α * (X.card.choose t : ℝ)) ≤
      ((X.card - t).choose (m - t) : ℝ) * (colorCount c t X b : ℝ) := by
    calc
      ((X.card - t).choose (m - t) : ℝ) * (α * (X.card.choose t : ℝ))
          = α * ((X.card.choose t : ℝ) * ((X.card - t).choose (m - t) : ℝ)) := by ring
      _ = α * ((X.card.choose m : ℝ) * (m.choose t : ℝ)) := by rw [hident]
      _ = (X.card.choose m : ℝ) * (α * (m.choose t : ℝ)) := by ring
      _ ≤ ((X.card - t).choose (m - t) : ℝ) * (colorCount c t X b : ℝ) := hsum_real
  exact le_of_mul_le_mul_left hmul hchoose_pos_r

/-- **Exact-Size Reduction Lemma:**
For `t ≤ m`, a coloring `c` satisfies the threshold condition on all `X` with `m ≤ X.card`
if and only if it satisfies it on all `X` with `X.card = m`. -/
theorem exact_size_reduction {n t m : ℕ} (htm : t ≤ m) (α : ℝ) (c : Finset (Fin n) → Bool) :
    (∀ X : Finset (Fin n), m ≤ X.card → ∀ b : Bool,
      0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
      α * (X.card.choose t : ℝ) ≤ (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)) ↔
    (∀ X : Finset (Fin n), X.card = m → ∀ b : Bool,
      0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
      α * (m.choose t : ℝ) ≤ (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)) := by
  constructor
  · intro h X hX b
    simpa [hX] using h X (le_of_eq hX.symm) b
  · intro h X hXm b
    refine averaging_monotonicity c t m α X htm hXm b ?_
    intro Y hY
    exact h Y (Finset.mem_powersetCard.mp hY).2 b

/-- The feasible set defining `F n t α` is always nonempty (`n + 1` is vacuously feasible). -/
private lemma feasible_nonempty (n t : ℕ) (α : ℝ) :
    ({m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        α * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)} : Set ℕ).Nonempty := by
  refine ⟨n + 1, fun _ => false, fun X hX => ?_⟩
  have hle : X.card ≤ n := by
    simpa using Finset.card_le_univ X
  omega

/-- Trivial upper bound: `F(n, t, α) ≤ n + 1`. -/
theorem threshold_le_succ (n t : ℕ) (α : ℝ) :
    sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        α * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)} ≤ n + 1 := by
  apply Nat.sInf_le
  refine ⟨fun _ => false, fun X hX => ?_⟩
  have hle : X.card ≤ n := by simpa using Finset.card_le_univ X
  omega

/-- Monotonicity in `α`: if `α ≤ β`, then `F(n, t, α) ≤ F(n, t, β)`. -/
theorem threshold_mono_alpha (n t : ℕ) {α β : ℝ} (hαβ : α ≤ β) :
    sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        α * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)} ≤
    sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        β * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)} := by
  have hmem := Nat.sInf_mem (feasible_nonempty n t β)
  apply Nat.sInf_le
  rcases hmem with ⟨c, hc⟩
  refine ⟨c, fun X hX b => ?_⟩
  obtain ⟨hpos, hcnt⟩ := hc X hX b
  refine ⟨hpos, le_trans ?_ hcnt⟩
  exact mul_le_mul_of_nonneg_right hαβ (Nat.cast_nonneg _)

/-- Monotonicity in `n`: if `n₁ ≤ n₂`, then `F(n₁, t, α) ≤ F(n₂, t, α)`. -/
theorem threshold_mono_n {n₁ n₂ : ℕ} (h12 : n₁ ≤ n₂) (t : ℕ) (α : ℝ) :
    sInf {m : ℕ | ∃ c : Finset (Fin n₁) → Bool, ∀ X : Finset (Fin n₁), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        α * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)} ≤
    sInf {m : ℕ | ∃ c : Finset (Fin n₂) → Bool, ∀ X : Finset (Fin n₂), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        α * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)} := by
  have hmem := Nat.sInf_mem (feasible_nonempty n₂ t α)
  apply Nat.sInf_le
  rcases hmem with ⟨c, hc⟩
  let emb : Fin n₁ ↪ Fin n₂ := Fin.castLEEmb h12
  refine ⟨fun e => c (e.map emb), fun X hX b => ?_⟩
  have hcard : (X.map emb).card = X.card := Finset.card_map emb
  have hres := hc (X.map emb) (by rw [hcard]; exact hX) b
  have hbij : ((X.powersetCard t).filter (fun e => c (e.map emb) = b)).card =
      (((X.map emb).powersetCard t).filter (fun e => c e = b)).card := by
    refine Finset.card_bij (fun e _ => e.map emb) ?_ ?_ ?_
    · intro e he
      rcases Finset.mem_filter.mp he with ⟨heX, hcb⟩
      rcases Finset.mem_powersetCard.mp heX with ⟨heSub, heCard⟩
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.map_subset_map.mpr heSub, by rw [Finset.card_map, heCard]⟩, hcb⟩
    · intro e₁ _ e₂ _ hEq
      exact Finset.map_injective emb hEq
    · intro e' he'
      rcases Finset.mem_filter.mp he' with ⟨he'X, hcb⟩
      rcases Finset.mem_powersetCard.mp he'X with ⟨he'Sub, he'Card⟩
      let e : Finset (Fin n₁) := X.filter (fun x => emb x ∈ e')
      have hemap : e.map emb = e' := by
        ext y
        simp only [e, Finset.mem_map, Finset.mem_filter]
        constructor
        · rintro ⟨x, ⟨_, hx⟩, rfl⟩; exact hx
        · intro hy
          obtain ⟨x, hxX, rfl⟩ := Finset.mem_map.mp (he'Sub hy)
          exact ⟨x, ⟨hxX, hy⟩, rfl⟩
      refine ⟨e, ?_, hemap⟩
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.filter_subset _ _, ?_⟩, by rw [hemap]; exact hcb⟩
      rw [← Finset.card_map emb, hemap, he'Card]
  rw [hbij, ← hcard]
  exact hres

/-- Helper: `F n t α ≤ m` iff there exists a coloring valid on all `X` with `m ≤ X.card`. -/
private lemma F_le_iff {n t m : ℕ} {α : ℝ} :
    F n t α ≤ m ↔ ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        α * (X.card.choose t : ℝ) ≤ (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ) := by
  constructor
  · intro hle
    rcases Nat.sInf_mem (feasible_nonempty n t α) with ⟨c, hc⟩
    exact ⟨c, fun X hX b => hc X (le_trans hle hX) b⟩
  · intro h
    exact Nat.sInf_le h

/-- Helper: if every coloring has a bad set of size `m` (with `m ≤ n`), then `m < F n t α`. -/
private lemma lt_F_of_every_coloring_has_bad {n t m : ℕ} {α : ℝ}
    (hbad : ∀ c : Finset (Fin n) → Bool, ∃ X : Finset (Fin n), m ≤ X.card ∧ ∃ b : Bool,
      ((X.powersetCard t).filter (fun e => c e = b)).card = 0 ∨
      (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ) < α * (X.card.choose t : ℝ)) :
    m < F n t α := by
  by_contra h
  push Not at h
  obtain ⟨c, hc⟩ := F_le_iff.mp h
  obtain ⟨X, hXm, b, hb⟩ := hbad c
  obtain ⟨hpos, hcnt⟩ := hc X hXm b
  rcases hb with h0 | hlt
  · omega
  · linarith

/-! ### Section 2: Ramsey Anchor Lemma at Small `α` -/

/-- **Ramsey Anchor Lemma:**
For any `t ≤ m ≤ n` and `0 ≤ α ≤ 1 / (m.choose t)`, `F(n, t, α) ≤ m` holds if and only if
there exists a 2-coloring of `K_n^{(t)}` containing no monochromatic `K_m^{(t)}`
(equivalently, `n < R_t(m, m)`). -/
theorem ramsey_anchor_lemma {n t m : ℕ} (htm : t ≤ m) {α : ℝ}
    (hα_le : α * (m.choose t : ℝ) ≤ 1) :
    sInf {k : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), k ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        α * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)} ≤ m ↔
    ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), X.card = m →
      ∀ b : Bool, 0 < ((X.powersetCard t).filter (fun e => c e = b)).card := by
  rw [F_le_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun X hX b => (hc X (le_of_eq hX.symm) b).1⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, (exact_size_reduction htm α c).mpr ?_⟩
    intro X hX b
    have hpos : 0 < ((X.powersetCard t).filter (fun e => c e = b)).card := hc X hX b
    refine ⟨hpos, ?_⟩
    have h1 : (1 : ℝ) ≤ (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ) := by
      exact_mod_cast hpos
    exact le_trans hα_le h1

/-- Corollary: `F(n, t, α) = F(n, t, 0)` whenever `t ≤ F(n, t, 0)` and
`0 ≤ α` satisfies `α * (F(n, t, 0).choose t) ≤ 1`. -/
theorem ramsey_anchor_eq_zero {n t : ℕ} {α : ℝ} (hα0 : 0 ≤ α)
    (htF : t ≤ sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        (0 : ℝ) * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)})
    (hα_le : α * ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        (0 : ℝ) * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)}).choose t : ℝ) ≤ 1) :
    sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        α * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)} =
    sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        (0 : ℝ) * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)} := by
  apply le_antisymm
  · rw [ramsey_anchor_lemma htF hα_le]
    obtain ⟨c, hc⟩ := F_le_iff.mp (le_refl (F n t 0))
    exact ⟨c, fun X hX b => (hc X (le_of_eq hX.symm) b).1⟩
  · exact threshold_mono_alpha n t hα0

/-! ### Section 3: Universal Probabilistic Upper Bound (`O_{t, α}((log n)^{1/(t-1)})`) -/

/-- Elementary hyperbolic cosine bound: `exp x + exp (-x) ≤ 2 * exp (x ^ 2 / 2)` for all `x ≥ 0`. -/
private lemma exp_add_exp_neg_le {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x + Real.exp (-x) ≤ 2 * Real.exp (x ^ 2 / 2) := by
  let g : ℝ → ℝ := fun t => (1 + t) - (1 - t) * Real.exp (2 * t)
  let g' : ℝ → ℝ := fun t => 1 - (1 - 2 * t) * Real.exp (2 * t)
  have hg'_deriv : ∀ t : ℝ, HasDerivAt g' (4 * t * Real.exp (2 * t)) t := by
    intro t
    have h1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t (1 : ℝ)
    have h2 : HasDerivAt (fun s : ℝ => 1 - 2 * s) (0 - 2 * 1) t :=
      (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).const_mul 2)
    have h3 : HasDerivAt (fun s : ℝ => Real.exp (2 * s)) (Real.exp (2 * t) * (2 * 1)) t :=
      ((hasDerivAt_id t).const_mul 2).exp
    have hsub := h1.sub (h2.mul h3)
    have heq : (0 : ℝ) - ((0 - 2 * 1) * Real.exp (2 * t) +
        (1 - 2 * t) * (Real.exp (2 * t) * (2 * 1))) = 4 * t * Real.exp (2 * t) := by ring
    rw [heq] at hsub
    exact hsub
  have hg'_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ g' t := by
    intro t ht
    have hmono : MonotoneOn g' (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact fun s _ => (hg'_deriv s).continuousAt.continuousWithinAt
      · exact fun s _ => (hg'_deriv s).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [(hg'_deriv s).deriv]
        have hs0 : 0 ≤ s := le_of_lt (by simpa [interior_Ici] using hs)
        positivity
    have h0 : g' 0 = 0 := by simp [g']
    rw [← h0]
    exact hmono (by simp : (0 : ℝ) ∈ Set.Ici (0 : ℝ)) ht ht
  have hg_deriv : ∀ t : ℝ, HasDerivAt g (g' t) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => 1 + s) (0 + 1) t :=
      (hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)
    have h2 : HasDerivAt (fun s : ℝ => 1 - s) (0 - 1) t :=
      (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    have h3 : HasDerivAt (fun s : ℝ => Real.exp (2 * s)) (Real.exp (2 * t) * (2 * 1)) t :=
      ((hasDerivAt_id t).const_mul 2).exp
    have hsub := h1.sub (h2.mul h3)
    have heq : (0 + 1 : ℝ) - ((0 - 1) * Real.exp (2 * t) +
        (1 - t) * (Real.exp (2 * t) * (2 * 1))) = g' t := by dsimp only [g']; ring
    rw [heq] at hsub
    exact hsub
  have hg_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ g t := by
    intro t ht
    have hmono : MonotoneOn g (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact fun s _ => (hg_deriv s).continuousAt.continuousWithinAt
      · exact fun s _ => (hg_deriv s).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [(hg_deriv s).deriv]
        exact hg'_nonneg s (le_of_lt (by simpa [interior_Ici] using hs))
    have h0 : g 0 = 0 := by simp [g]
    rw [← h0]
    exact hmono (by simp : (0 : ℝ) ∈ Set.Ici (0 : ℝ)) ht ht
  let f : ℝ → ℝ := fun t => Real.exp (-(t ^ 2 / 2)) * (Real.exp t + Real.exp (-t))
  have hf_deriv : ∀ t : ℝ,
      HasDerivAt f (-(Real.exp (-(t ^ 2 / 2)) * Real.exp (-t) * g t)) t := by
    intro t
    have hsq : HasDerivAt (fun s : ℝ => -(s ^ 2 / 2)) (-((2 * t ^ (2 - 1)) / 2)) t :=
      ((hasDerivAt_pow 2 t).div_const 2).neg
    have he1 : HasDerivAt (fun s : ℝ => Real.exp (-(s ^ 2 / 2)))
        (Real.exp (-(t ^ 2 / 2)) * (-((2 * t ^ (2 - 1)) / 2))) t := hsq.exp
    have he2 : HasDerivAt (fun s : ℝ => Real.exp s + Real.exp (-s))
        (Real.exp t + Real.exp (-t) * (-1)) t :=
      (Real.hasDerivAt_exp t).add ((hasDerivAt_neg t).exp)
    have hmul := he1.mul he2
    have heq : Real.exp (-(t ^ 2 / 2)) * -((2 * t ^ (2 - 1)) / 2) * (Real.exp t + Real.exp (-t)) +
        Real.exp (-(t ^ 2 / 2)) * (Real.exp t + Real.exp (-t) * -1) =
        -(Real.exp (-(t ^ 2 / 2)) * Real.exp (-t) * g t) := by
      dsimp only [g]
      have hexp2 : Real.exp (-t) * Real.exp (2 * t) = Real.exp t := by
        rw [← Real.exp_add]; congr 1; ring
      have hpow1 : (2 : ℝ) * t ^ (2 - 1) / 2 = t := by simp
      rw [hpow1]
      calc
        Real.exp (-(t ^ 2 / 2)) * -t * (Real.exp t + Real.exp (-t)) +
            Real.exp (-(t ^ 2 / 2)) * (Real.exp t + Real.exp (-t) * -1)
            = Real.exp (-(t ^ 2 / 2)) * ((1 - t) * Real.exp t - (1 + t) * Real.exp (-t)) := by ring
        _ = Real.exp (-(t ^ 2 / 2)) *
              ((1 - t) * (Real.exp (-t) * Real.exp (2 * t)) - (1 + t) * Real.exp (-t)) := by
              rw [hexp2]
        _ = -(Real.exp (-(t ^ 2 / 2)) * Real.exp (-t) *
              (1 + t - (1 - t) * Real.exp (2 * t))) := by ring
    rw [heq] at hmul
    exact hmul
  have hanti : AntitoneOn f (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun s _ => (hf_deriv s).continuousAt.continuousWithinAt
    · exact fun s _ => (hf_deriv s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hf_deriv s).deriv]
      have hs0 : 0 ≤ s := le_of_lt (by simpa [interior_Ici] using hs)
      have hgs : 0 ≤ g s := hg_nonneg s hs0
      have hp : 0 ≤ Real.exp (-(s ^ 2 / 2)) * Real.exp (-s) * g s := by positivity
      linarith
  have hfx : f x ≤ f 0 := hanti (by simp : (0 : ℝ) ∈ Set.Ici (0 : ℝ)) hx hx
  have hf0 : f 0 = 2 := by simp [f]; ring
  rw [hf0] at hfx
  dsimp only [f] at hfx
  have hmul := mul_le_mul_of_nonneg_left hfx (le_of_lt (Real.exp_pos (x ^ 2 / 2)))
  have hcancel : Real.exp (x ^ 2 / 2) * Real.exp (-(x ^ 2 / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  calc
    Real.exp x + Real.exp (-x)
        = (Real.exp (x ^ 2 / 2) * Real.exp (-(x ^ 2 / 2))) * (Real.exp x + Real.exp (-x)) := by
          rw [hcancel, one_mul]
    _ = Real.exp (x ^ 2 / 2) * (Real.exp (-(x ^ 2 / 2)) * (Real.exp x + Real.exp (-x))) := by ring
    _ ≤ Real.exp (x ^ 2 / 2) * 2 := hmul
    _ = 2 * Real.exp (x ^ 2 / 2) := by ring

/-- Pure-`Finset` exponential-moment identity for Boolean colorings of a finite type `ι`. -/
private lemma sum_exp_bool_coloring {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Bool) (lam : ℝ) :
    ∑ f : ι → Bool,
      Real.exp (lam * ((Fintype.card ι : ℝ) / 2 -
        ((Finset.univ.filter (fun i : ι => f i = b)).card : ℝ))) =
      (Real.exp (lam / 2) + Real.exp (-(lam / 2))) ^ Fintype.card ι := by
  have hterm : ∀ f : ι → Bool,
      Real.exp (lam * ((Fintype.card ι : ℝ) / 2 -
        ((Finset.univ.filter (fun i : ι => f i = b)).card : ℝ))) =
      ∏ i : ι, Real.exp (if f i = b then -(lam / 2) else lam / 2) := by
    intro f
    rw [← Real.exp_sum]
    congr 1
    have hsplit : ∑ i : ι, (if f i = b then -(lam / 2) else lam / 2) =
        ∑ i : ι, (lam / 2 - if f i = b then lam else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    rw [hsplit, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hfilt : (∑ i : ι, if f i = b then lam else (0 : ℝ)) =
        ((Finset.univ.filter (fun i : ι => f i = b)).card : ℝ) * lam := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hfilt]
    ring
  simp_rw [hterm]
  have hpi := (Fintype.prod_sum (fun (_ : ι) (v : Bool) =>
    Real.exp (if v = b then -(lam / 2) else lam / 2))).symm
  rw [hpi]
  have hinner :
      (∑ v : Bool, Real.exp (if v = b then -(lam / 2) else lam / 2)) =
        Real.exp (lam / 2) + Real.exp (-(lam / 2)) := by
    rw [Fintype.sum_bool]
    cases b
    · rw [if_neg (by decide : true ≠ false), if_pos rfl]
    · rw [if_pos rfl, if_neg (by decide : false ≠ true), add_comm]
  rw [Finset.prod_congr rfl (fun _ _ => hinner), Finset.prod_const, Finset.card_univ]

/-- Pure-`Finset` Hoeffding tail bound for Boolean colorings of a finite type `ι`. -/
private lemma hoeffding_finset_bool {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Bool) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((Finset.univ.filter (fun f : ι → Bool =>
      ((Finset.univ.filter (fun i : ι => f i = b)).card : ℝ) ≤
        (1 / 2 - δ) * (Fintype.card ι : ℝ))).card : ℝ) ≤
      (2 : ℝ) ^ Fintype.card ι * Real.exp (-(2 * δ ^ 2 * (Fintype.card ι : ℝ))) := by
  let N : ℕ := Fintype.card ι
  let lam : ℝ := 4 * δ
  let bad : Finset (ι → Bool) :=
    Finset.univ.filter (fun f : ι → Bool =>
      ((Finset.univ.filter (fun i : ι => f i = b)).card : ℝ) ≤ (1 / 2 - δ) * (N : ℝ))
  have hlam : 0 ≤ lam / 2 := by dsimp only [lam]; linarith
  have hmarkov : (bad.card : ℝ) * Real.exp (lam * δ * (N : ℝ)) ≤
      ∑ f : ι → Bool, Real.exp (lam * ((N : ℝ) / 2 -
        ((Finset.univ.filter (fun i : ι => f i = b)).card : ℝ))) := by
    calc
      (bad.card : ℝ) * Real.exp (lam * δ * (N : ℝ))
          = ∑ _f ∈ bad, Real.exp (lam * δ * (N : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ f ∈ bad, Real.exp (lam * ((N : ℝ) / 2 -
            ((Finset.univ.filter (fun i : ι => f i = b)).card : ℝ))) := by
            refine Finset.sum_le_sum fun f hf => Real.exp_le_exp.mpr ?_
            have hle : ((Finset.univ.filter (fun i : ι => f i = b)).card : ℝ) ≤
                (1 / 2 - δ) * (N : ℝ) := (Finset.mem_filter.mp hf).2
            have hdiff : δ * (N : ℝ) ≤ (N : ℝ) / 2 -
                ((Finset.univ.filter (fun i : ι => f i = b)).card : ℝ) := by linarith
            have hlam0 : 0 ≤ lam := by dsimp only [lam]; linarith
            nlinarith
      _ ≤ ∑ f : ι → Bool, Real.exp (lam * ((N : ℝ) / 2 -
            ((Finset.univ.filter (fun i : ι => f i = b)).card : ℝ))) :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => le_of_lt (Real.exp_pos _)
  rw [sum_exp_bool_coloring b lam] at hmarkov
  have hbase : Real.exp (lam / 2) + Real.exp (-(lam / 2)) ≤ 2 * Real.exp ((lam / 2) ^ 2 / 2) :=
    exp_add_exp_neg_le hlam
  have hpow : (Real.exp (lam / 2) + Real.exp (-(lam / 2))) ^ N ≤
      (2 * Real.exp ((lam / 2) ^ 2 / 2)) ^ N :=
    pow_le_pow_left₀ (by positivity) hbase N
  have hrhs : (2 * Real.exp ((lam / 2) ^ 2 / 2)) ^ N =
      (2 : ℝ) ^ N * Real.exp (2 * δ ^ 2 * (N : ℝ)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    dsimp only [lam]
    ring
  have hcomb : (bad.card : ℝ) * Real.exp (4 * δ ^ 2 * (N : ℝ)) ≤
      (2 : ℝ) ^ N * Real.exp (2 * δ ^ 2 * (N : ℝ)) := by
    have h4 : lam * δ * (N : ℝ) = 4 * δ ^ 2 * (N : ℝ) := by dsimp only [lam]; ring
    rw [← h4, ← hrhs]
    exact le_trans hmarkov hpow
  have hmul := mul_le_mul_of_nonneg_right hcomb
    (le_of_lt (Real.exp_pos (-(4 * δ ^ 2 * (N : ℝ)))))
  have hL : (bad.card : ℝ) * Real.exp (4 * δ ^ 2 * (N : ℝ)) *
      Real.exp (-(4 * δ ^ 2 * (N : ℝ))) = (bad.card : ℝ) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  have hR : (2 : ℝ) ^ N * Real.exp (2 * δ ^ 2 * (N : ℝ)) *
      Real.exp (-(4 * δ ^ 2 * (N : ℝ))) =
      (2 : ℝ) ^ N * Real.exp (-(2 * δ ^ 2 * (N : ℝ))) := by
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [hL, hR] at hmul
  exact hmul

/-- Extending a Hoeffding tail bound from `X.powersetCard t` to all colorings of `univ.powersetCard t`. -/
private lemma card_bad_colorings_for_X {n t : ℕ} (X : Finset (Fin n)) (b : Bool)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    let E : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard t
    ((Finset.univ.filter (fun f : E → Bool =>
      (((X.powersetCard t).filter (fun e => ∃ he : e ∈ E, f ⟨e, he⟩ = b)).card : ℝ) ≤
        (1 / 2 - δ) * (X.card.choose t : ℝ))).card : ℝ) ≤
      (2 : ℝ) ^ (n.choose t) * Real.exp (-(2 * δ ^ 2 * (X.card.choose t : ℝ))) := by
  classical
  intro E
  let EX : Finset (Finset (Fin n)) := X.powersetCard t
  have hEX_sub : EX ⊆ E := Finset.powersetCard_mono (Finset.subset_univ X)
  let Ec : Finset (Finset (Fin n)) := E \ EX
  -- Bijection (E → Bool) ≃ (EX → Bool) × (Ec → Bool)
  let split : (E → Bool) → (EX → Bool) × (Ec → Bool) := fun f =>
    (fun x => f ⟨x.1, hEX_sub x.2⟩, fun y => f ⟨y.1, (Finset.mem_sdiff.mp y.2).1⟩)
  have hsplit_inj : Function.Injective split := by
    intro f₁ f₂ hEq
    funext ⟨e, he⟩
    by_cases heX : e ∈ EX
    · have h1 := congrFun (congrArg Prod.fst hEq) ⟨e, heX⟩
      exact h1
    · have hec : e ∈ Ec := Finset.mem_sdiff.mpr ⟨he, heX⟩
      have h2 := congrFun (congrArg Prod.snd hEq) ⟨e, hec⟩
      exact h2
  let badEX : Finset (EX → Bool) :=
    Finset.univ.filter (fun g : EX → Bool =>
      ((Finset.univ.filter (fun i : EX => g i = b)).card : ℝ) ≤
        (1 / 2 - δ) * (Fintype.card EX : ℝ))
  have hcardEX : Fintype.card EX = X.card.choose t := by
    rw [Fintype.card_coe, Finset.card_powersetCard]
  have hcardE : Fintype.card E = n.choose t := by
    rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hcardEc : Fintype.card Ec = n.choose t - X.card.choose t := by
    rw [Fintype.card_coe, Finset.card_sdiff, Finset.inter_eq_left.mpr hEX_sub]
    simp only [E, EX, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hle_choose : X.card.choose t ≤ n.choose t := by
    have : EX.card ≤ E.card := Finset.card_le_card hEX_sub
    simpa [E, EX, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using this
  let badAll := Finset.univ.filter (fun f : E → Bool =>
    (((X.powersetCard t).filter (fun e => ∃ he : e ∈ E, f ⟨e, he⟩ = b)).card : ℝ) ≤
      (1 / 2 - δ) * (X.card.choose t : ℝ))
  have himg : badAll.card ≤ (badEX ×ˢ (Finset.univ : Finset (Ec → Bool))).card := by
    refine Finset.card_le_card_of_injOn split ?_ (fun _ _ _ _ h => hsplit_inj h)
    intro f hf
    rw [Finset.mem_coe, Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hf_le := (Finset.mem_filter.mp (Finset.mem_coe.mp hf)).2
    have hcount_eq : (Finset.univ.filter (fun i : EX => f ⟨i.1, hEX_sub i.2⟩ = b)).card =
        (EX.filter (fun e => ∃ he : e ∈ E, f ⟨e, he⟩ = b)).card := by
      refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
      · intro i hi
        have hfb : f ⟨i.1, hEX_sub i.2⟩ = b := (Finset.mem_filter.mp hi).2
        exact Finset.mem_filter.mpr ⟨i.2, ⟨hEX_sub i.2, hfb⟩⟩
      · intro i₁ _ i₂ _ hEq; exact Subtype.ext hEq
      · intro e he
        rcases Finset.mem_filter.mp he with ⟨heEX, ⟨heE, hfb⟩⟩
        exact ⟨⟨e, heEX⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfb⟩, rfl⟩
    rw [hcount_eq, hcardEX]
    exact hf_le
  have hcard_prod : ((badEX ×ˢ (Finset.univ : Finset (Ec → Bool))).card : ℝ) =
      (badEX.card : ℝ) * (2 : ℝ) ^ (n.choose t - X.card.choose t) := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, hcardEc]
    push_cast
    rfl
  have hhoeff : (badEX.card : ℝ) ≤
      (2 : ℝ) ^ (X.card.choose t) * Real.exp (-(2 * δ ^ 2 * (X.card.choose t : ℝ))) := by
    have h := hoeffding_finset_bool (ι := EX) b hδ
    rw [hcardEX] at h
    simpa [badEX, hcardEX] using h
  calc
    (badAll.card : ℝ) ≤ ((badEX ×ˢ (Finset.univ : Finset (Ec → Bool))).card : ℝ) := by
      exact_mod_cast himg
    _ = (badEX.card : ℝ) * (2 : ℝ) ^ (n.choose t - X.card.choose t) := hcard_prod
    _ ≤ ((2 : ℝ) ^ (X.card.choose t) * Real.exp (-(2 * δ ^ 2 * (X.card.choose t : ℝ)))) *
          (2 : ℝ) ^ (n.choose t - X.card.choose t) :=
        mul_le_mul_of_nonneg_right hhoeff (by positivity)
    _ = ((2 : ℝ) ^ (X.card.choose t) * (2 : ℝ) ^ (n.choose t - X.card.choose t)) *
          Real.exp (-(2 * δ ^ 2 * (X.card.choose t : ℝ))) := by ring
    _ = (2 : ℝ) ^ (n.choose t) * Real.exp (-(2 * δ ^ 2 * (X.card.choose t : ℝ))) := by
        rw [← pow_add, Nat.add_sub_of_le hle_choose]

/-- Probabilistic existence criterion: if `t ≤ m`, `0 ≤ α < 1/2`, `δ = 1/2 - α`, and
`2 * (n.choose m) * exp (-2 * δ^2 * (m.choose t)) < 1` (with `0 < (1/2 - δ) * m.choose t`),
then `F(n, t, α) ≤ m`. -/
private lemma F_le_of_prob_criterion {n t m : ℕ} (htm : t ≤ m) {α : ℝ}
    (hα0 : 0 ≤ α) (hα_lt : α < 1 / 2)
    (hcrit : 2 * (n.choose m : ℝ) *
      Real.exp (-(2 * ((1 / 2 - α) / 2) ^ 2 * (m.choose t : ℝ))) < 1) :
    F n t α ≤ m := by
  classical
  let δ : ℝ := (1 / 2 - α) / 2
  have hδ_pos : 0 < δ := by dsimp only [δ]; linarith
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hα_strict : α < 1 / 2 - δ := by dsimp only [δ]; linarith
  have h0_lt : 0 < 1 / 2 - δ := by dsimp only [δ]; linarith
  let E : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard t
  let badFor (X : Finset (Fin n)) (b : Bool) : Finset (E → Bool) :=
    Finset.univ.filter (fun f : E → Bool =>
      (((X.powersetCard t).filter (fun e => ∃ he : e ∈ E, f ⟨e, he⟩ = b)).card : ℝ) ≤
        (1 / 2 - δ) * (X.card.choose t : ℝ))
  let badUnion : Finset (E → Bool) :=
    ((Finset.univ : Finset (Fin n)).powersetCard m).biUnion fun X =>
      badFor X false ∪ badFor X true
  have hbad_card : (badUnion.card : ℝ) < (2 : ℝ) ^ (n.choose t) := by
    have h1 : badUnion.card ≤
        ∑ X ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
          ((badFor X false).card + (badFor X true).card) := by
      refine le_trans Finset.card_biUnion_le ?_
      refine Finset.sum_le_sum fun X _ => Finset.card_union_le _ _
    have h1r : (badUnion.card : ℝ) ≤
        ∑ X ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
          ((badFor X false).card + (badFor X true).card : ℝ) := by
      exact_mod_cast h1
    have h2 : ∑ X ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        ((badFor X false).card + (badFor X true).card : ℝ) ≤
        ∑ _X ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
          (2 * ((2 : ℝ) ^ (n.choose t) * Real.exp (-(2 * δ ^ 2 * (m.choose t : ℝ))))) := by
      refine Finset.sum_le_sum fun X hX => ?_
      have hXcard : X.card = m := (Finset.mem_powersetCard.mp hX).2
      have hf : ((badFor X false).card : ℝ) ≤
          (2 : ℝ) ^ (n.choose t) * Real.exp (-(2 * δ ^ 2 * (m.choose t : ℝ))) := by
        simpa [badFor, E, hXcard] using card_bad_colorings_for_X (n := n) (t := t) X false hδ_nonneg
      have ht : ((badFor X true).card : ℝ) ≤
          (2 : ℝ) ^ (n.choose t) * Real.exp (-(2 * δ ^ 2 * (m.choose t : ℝ))) := by
        simpa [badFor, E, hXcard] using card_bad_colorings_for_X (n := n) (t := t) X true hδ_nonneg
      linarith
    have h3 : (∑ _X ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        (2 * ((2 : ℝ) ^ (n.choose t) * Real.exp (-(2 * δ ^ 2 * (m.choose t : ℝ)))))) =
        (2 * (n.choose m : ℝ) * Real.exp (-(2 * δ ^ 2 * (m.choose t : ℝ)))) *
          (2 : ℝ) ^ (n.choose t) := by
      rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    have hle := le_trans h1r (le_trans h2 (le_of_eq h3))
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (n.choose t) := by positivity
    calc
      (badUnion.card : ℝ) ≤ (2 * (n.choose m : ℝ) * Real.exp (-(2 * δ ^ 2 * (m.choose t : ℝ)))) *
          (2 : ℝ) ^ (n.choose t) := hle
      _ < 1 * (2 : ℝ) ^ (n.choose t) := mul_lt_mul_of_pos_right hcrit hpow_pos
      _ = (2 : ℝ) ^ (n.choose t) := one_mul _
  have huniv_card : (Finset.univ : Finset (E → Bool)).card = 2 ^ (n.choose t) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hlt_nat : badUnion.card < (Finset.univ : Finset (E → Bool)).card := by
    rw [huniv_card]
    have : (badUnion.card : ℝ) < ((2 ^ (n.choose t) : ℕ) : ℝ) := by simpa using hbad_card
    exact_mod_cast this
  obtain ⟨f, _, hf_not_bad⟩ : ∃ f ∈ (Finset.univ : Finset (E → Bool)), f ∉ badUnion :=
    Finset.exists_mem_notMem_of_card_lt_card hlt_nat
  let c : Finset (Fin n) → Bool := fun e => if he : e ∈ E then f ⟨e, he⟩ else false
  rw [F_le_iff]
  refine ⟨c, (exact_size_reduction htm α c).mpr ?_⟩
  intro X hX b
  have hXmem : X ∈ (Finset.univ : Finset (Fin n)).powersetCard m :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ X, hX⟩
  have hf_not_b : f ∉ badFor X b := by
    intro hmem
    apply hf_not_bad
    rw [Finset.mem_biUnion]
    refine ⟨X, hXmem, ?_⟩
    cases b
    · exact Finset.mem_union_left _ hmem
    · exact Finset.mem_union_right _ hmem
  have hgt : (1 / 2 - δ) * (X.card.choose t : ℝ) <
      (((X.powersetCard t).filter (fun e => ∃ he : e ∈ E, f ⟨e, he⟩ = b)).card : ℝ) := by
    by_contra hle
    push Not at hle
    exact hf_not_b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
  have hcount_eq :
      ((X.powersetCard t).filter (fun e => c e = b)).card =
      ((X.powersetCard t).filter (fun e => ∃ he : e ∈ E, f ⟨e, he⟩ = b)).card := by
    congr 1
    ext e
    simp only [Finset.mem_filter, c]
    constructor
    · rintro ⟨heX, hce⟩
      have heE : e ∈ E := Finset.powersetCard_mono (Finset.subset_univ X) heX
      rw [dif_pos heE] at hce
      exact ⟨heX, ⟨heE, hce⟩⟩
    · rintro ⟨heX, ⟨heE, hfe⟩⟩
      refine ⟨heX, ?_⟩
      rw [dif_pos heE]
      exact hfe
  rw [hX] at hgt
  rw [hcount_eq]
  have hmt_pos : (0 : ℝ) < (m.choose t : ℝ) := by exact_mod_cast Nat.choose_pos htm
  have hpos_real : (0 : ℝ) < (((X.powersetCard t).filter
      (fun e => ∃ he : e ∈ E, f ⟨e, he⟩ = b)).card : ℝ) :=
    lt_trans (mul_pos h0_lt hmt_pos) hgt
  have hpos_nat : 0 < ((X.powersetCard t).filter
      (fun e => ∃ he : e ∈ E, f ⟨e, he⟩ = b)).card := by
    exact_mod_cast hpos_real
  refine ⟨hpos_nat, le_of_lt (lt_trans ?_ hgt)⟩
  exact mul_lt_mul_of_pos_right hα_strict hmt_pos

/-- Elementary binomial lower bound: `t! * (m.choose t) ≥ (m - t + 1)^t` for `t ≤ m`. -/
private lemma factorial_mul_choose_ge_pow {m t : ℕ} (htm : t ≤ m) :
    (m - t + 1) ^ t ≤ t.factorial * m.choose t := by
  have hdesc := Nat.descFactorial_eq_factorial_mul_choose m t
  rw [← hdesc]
  clear hdesc
  induction t generalizing m with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, pow_succ]
    have hkm : k ≤ m := by omega
    have h1 : (m - (k + 1) + 1) ^ k ≤ (m - k + 1) ^ k :=
      Nat.pow_le_pow_left (by omega) k
    have h2 : (m - k + 1) ^ k ≤ m.descFactorial k := ih hkm
    have h3 : m - (k + 1) + 1 = m - k := by omega
    rw [h3]
    calc
      (m - k) ^ k * (m - k) ≤ (m - k + 1) ^ k * (m - k) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) k)
      _ ≤ m.descFactorial k * (m - k) := Nat.mul_le_mul_right _ h2
      _ = (m - k) * m.descFactorial k := mul_comm _ _

/-- **Universal Probabilistic Upper Bound (Explicit Form):**
For every `t ≥ 2`, `α < 1/2`, and `n ≥ 2`,
`F(n, t, α) ≤ ⌈(2 * t! / ((1/2 - α)/2)^2 * log n)^{1/(t-1)}⌉ + t + 2`. -/
theorem threshold_upper_explicit {t : ℕ} (ht : 2 ≤ t) {α : ℝ} (hα0 : 0 ≤ α) (hα_lt : α < 1 / 2)
    {n : ℕ} (hn : 2 ≤ n) :
    let δ : ℝ := (1 / 2 - α) / 2
    let C : ℝ := ((t.factorial : ℝ) / (δ ^ 2)) ^ ((1 : ℝ) / ((t : ℝ) - 1))
    ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        α * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)} : ℕ) : ℝ) ≤
      C * (Real.log (n : ℝ)) ^ ((1 : ℝ) / ((t : ℝ) - 1)) + (t : ℝ) + 2 := by
  intro δ C
  have hδ_pos : 0 < δ := by dsimp only [δ]; linarith
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have ht1_pos : (0 : ℝ) < (t : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  let x : ℝ := C * (Real.log (n : ℝ)) ^ ((1 : ℝ) / ((t : ℝ) - 1))
  have hx_pos : 0 < x := by
    dsimp only [x, C]
    positivity
  let k : ℕ := Nat.ceil x + 1
  let m : ℕ := k + t
  have htm : t ≤ m := by omega
  have hxk : x < (k : ℝ) := by
    have : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
    push_cast [k]
    linarith
  have hk_pos : (0 : ℝ) < (k : ℝ) := lt_trans hx_pos hxk
  have hpow_gt : (t.factorial : ℝ) / (δ ^ 2) * Real.log (n : ℝ) < (k : ℝ) ^ (t - 1) := by
    have hx_pow : x ^ (t - 1) = (t.factorial : ℝ) / (δ ^ 2) * Real.log (n : ℝ) := by
      have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]
      have hC_pow : C ^ (t - 1) = (t.factorial : ℝ) / (δ ^ 2) := by
        dsimp only [C]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hcast,
          one_div_mul_cancel (ne_of_gt ht1_pos), Real.rpow_one]
      have hL_pow : ((Real.log (n : ℝ)) ^ ((1 : ℝ) / ((t : ℝ) - 1))) ^ (t - 1) =
          Real.log (n : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hlog_pos), hcast,
          one_div_mul_cancel (ne_of_gt ht1_pos), Real.rpow_one]
      dsimp only [x]
      rw [mul_pow, hC_pow, hL_pow]
    rw [← hx_pow]
    exact pow_lt_pow_left₀ hxk (le_of_lt hx_pos) (by omega : t - 1 ≠ 0)
  have hchoose_lb : ((k + 1 : ℕ) : ℝ) ^ t / (t.factorial : ℝ) ≤ (m.choose t : ℝ) := by
    have hnat : (m - t + 1) ^ t ≤ t.factorial * m.choose t := factorial_mul_choose_ge_pow htm
    have hmt : m - t + 1 = k + 1 := by omega
    rw [hmt] at hnat
    have hreal : ((k + 1 : ℕ) : ℝ) ^ t ≤ (t.factorial : ℝ) * (m.choose t : ℝ) := by
      exact_mod_cast hnat
    rw [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos t)]
    linarith
  have hbernoulli : (m : ℝ) * (k : ℝ) ^ (t - 1) ≤ ((k + 1 : ℕ) : ℝ) ^ t := by
    have hinv_nonneg : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
    have h1 : (1 : ℝ) + (t : ℝ) * (1 / (k : ℝ)) ≤ (1 + 1 / (k : ℝ)) ^ t :=
      one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ 1 / (k : ℝ)) t
    have hmul := mul_le_mul_of_nonneg_right h1 (pow_nonneg (le_of_lt hk_pos) t)
    have hL : (1 + (t : ℝ) * (1 / (k : ℝ))) * (k : ℝ) ^ t = (m : ℝ) * (k : ℝ) ^ (t - 1) := by
      have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
      have hpow_split : (k : ℝ) ^ t = (k : ℝ) * (k : ℝ) ^ (t - 1) := by
        conv_lhs => rw [show t = (t - 1) + 1 by omega, pow_succ']
      rw [hpow_split]
      push_cast [m]
      field_simp [hk_ne]
    have hR : (1 + 1 / (k : ℝ)) ^ t * (k : ℝ) ^ t = ((k + 1 : ℕ) : ℝ) ^ t := by
      rw [← mul_pow]
      congr 1
      have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
      push_cast
      field_simp [hk_ne]
    linarith
  have hlog2_le : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hexp_gt : (m : ℝ) * Real.log (n : ℝ) + Real.log 2 <
      2 * δ ^ 2 * (m.choose t : ℝ) := by
    have h1 : (m : ℝ) * Real.log (n : ℝ) <
        δ ^ 2 * (((k + 1 : ℕ) : ℝ) ^ t / (t.factorial : ℝ)) := by
      have hfac_pos : (0 : ℝ) < (t.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos t
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hstep1 : (m : ℝ) * ((t.factorial : ℝ) / (δ ^ 2) * Real.log (n : ℝ)) <
          (m : ℝ) * (k : ℝ) ^ (t - 1) :=
        mul_lt_mul_of_pos_left hpow_gt hm_pos
      have hstep2 : (m : ℝ) * ((t.factorial : ℝ) / (δ ^ 2) * Real.log (n : ℝ)) <
          ((k + 1 : ℕ) : ℝ) ^ t := lt_of_lt_of_le hstep1 hbernoulli
      have hstep3 := mul_lt_mul_of_pos_left hstep2 (show 0 < δ ^ 2 / (t.factorial : ℝ) by positivity)
      have hL : δ ^ 2 / (t.factorial : ℝ) *
          ((m : ℝ) * ((t.factorial : ℝ) / δ ^ 2 * Real.log (n : ℝ))) =
          (m : ℝ) * Real.log (n : ℝ) := by
        field_simp [ne_of_gt hδ_pos, ne_of_gt hfac_pos]
      have hR : δ ^ 2 / (t.factorial : ℝ) * ((k + 1 : ℕ) : ℝ) ^ t =
          δ ^ 2 * (((k + 1 : ℕ) : ℝ) ^ t / (t.factorial : ℝ)) := by ring
      linarith
    have h2 : Real.log 2 < δ ^ 2 * (((k + 1 : ℕ) : ℝ) ^ t / (t.factorial : ℝ)) := by
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
      have : Real.log 2 ≤ (m : ℝ) * Real.log (n : ℝ) := by nlinarith
      linarith
    have h3 : 2 * δ ^ 2 * (((k + 1 : ℕ) : ℝ) ^ t / (t.factorial : ℝ)) ≤
        2 * δ ^ 2 * (m.choose t : ℝ) :=
      mul_le_mul_of_nonneg_left hchoose_lb (by positivity)
    linarith
  have hcrit : 2 * (n.choose m : ℝ) *
      Real.exp (-(2 * δ ^ 2 * (m.choose t : ℝ))) < 1 := by
    have hchoose_ub_nat : n.choose m ≤ n ^ m := by
      have h1 : n.choose m ≤ m.factorial * n.choose m :=
        Nat.le_mul_of_pos_left _ (Nat.factorial_pos m)
      rw [← Nat.descFactorial_eq_factorial_mul_choose] at h1
      exact le_trans h1 (Nat.descFactorial_le_pow n m)
    have hchoose_ub : (n.choose m : ℝ) ≤ (n : ℝ) ^ m := by exact_mod_cast hchoose_ub_nat
    have hpow_exp : (n : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log (n : ℝ)) := by
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      rw [mul_comm, Real.exp_mul, Real.exp_log hn_pos, Real.rpow_natCast]
    have h2_exp : (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    calc
      2 * (n.choose m : ℝ) * Real.exp (-(2 * δ ^ 2 * (m.choose t : ℝ)))
          ≤ 2 * (n : ℝ) ^ m * Real.exp (-(2 * δ ^ 2 * (m.choose t : ℝ))) := by
            gcongr
      _ = Real.exp (Real.log 2) * Real.exp ((m : ℝ) * Real.log (n : ℝ)) *
            Real.exp (-(2 * δ ^ 2 * (m.choose t : ℝ))) := by rw [← h2_exp, hpow_exp]
      _ = Real.exp ((m : ℝ) * Real.log (n : ℝ) + Real.log 2 -
            2 * δ ^ 2 * (m.choose t : ℝ)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hFle : F n t α ≤ m := F_le_of_prob_criterion htm hα0 hα_lt hcrit
  have hFle_r : (F n t α : ℝ) ≤ (m : ℝ) := by exact_mod_cast hFle
  have hceil_lt : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one (le_of_lt hx_pos)
  have hm_le : (m : ℝ) ≤ x + (t : ℝ) + 2 := by
    push_cast [m, k]
    linarith
  exact le_trans hFle_r hm_le

/-- **Universal Asymptotic Upper Bound (`IsBigO` Form):**
For every `t ≥ 2` and every `α ∈ [0, 1/2)`,
`F^{(t)}(n, α) = O((log n)^{1/(t-1)})` as `n → ∞`. -/
theorem threshold_isBigO_log_rpow {t : ℕ} (ht : 2 ≤ t) {α : ℝ} (hα0 : 0 ≤ α) (hα_lt : α < 1 / 2) :
    (fun n : ℕ => ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        α * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)} : ℕ) : ℝ))
      =O[atTop] (fun n : ℕ => (Real.log (n : ℝ)) ^ ((1 : ℝ) / ((t : ℝ) - 1))) := by
  let δ : ℝ := (1 / 2 - α) / 2
  let C : ℝ := ((t.factorial : ℝ) / (δ ^ 2)) ^ ((1 : ℝ) / ((t : ℝ) - 1))
  rw [Asymptotics.isBigO_iff]
  refine ⟨C + (t : ℝ) + 2, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨3, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := by omega
  have h1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have he : Real.exp 1 ≤ (n : ℝ) := by
      have : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        linarith
      have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have := Real.log_le_log (Real.exp_pos 1) he
    simpa using this
  have ht1_pos : (0 : ℝ) < (t : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hrpow_ge1 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ ((1 : ℝ) / ((t : ℝ) - 1)) :=
    Real.one_le_rpow h1 (by positivity)
  have hub := threshold_upper_explicit ht hα0 hα_lt hn2
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (le_trans (by norm_num) hrpow_ge1)]
  calc
    (F n t α : ℝ) ≤ C * (Real.log (n : ℝ)) ^ ((1 : ℝ) / ((t : ℝ) - 1)) + (t : ℝ) + 2 := hub
    _ ≤ C * (Real.log (n : ℝ)) ^ ((1 : ℝ) / ((t : ℝ) - 1)) +
        ((t : ℝ) + 2) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / ((t : ℝ) - 1)) := by
          have : (t : ℝ) + 2 ≤ ((t : ℝ) + 2) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / ((t : ℝ) - 1)) := by
            nlinarith
          linarith
    _ = (C + (t : ℝ) + 2) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / ((t : ℝ) - 1)) := by ring

/-! ### Section 4: Classical Graph Ramsey (`R_2(a, b) ≤ (a + b).choose a`) & Full `t = 2` Non-Jump Theorem -/

/-- Classical Erdős–Szekeres 2-color graph Ramsey theorem on finite sets:
if `a + b` chooses `a` ≤ `|V|`, then every 2-coloring of 2-subsets of `V` contains either a
`false`-clique of size `a` or a `true`-clique of size `b`. -/
private lemma erdos_szekeres_ramsey {V : Type*} [DecidableEq V] :
    ∀ s : ℕ, ∀ a b : ℕ, a + b = s → ∀ (U : Finset V) (c : Finset V → Bool),
      (a + b).choose a ≤ U.card →
      (∃ A ⊆ U, A.card = a ∧ ∀ e ∈ A.powersetCard 2, c e = false) ∨
      (∃ B ⊆ U, B.card = b ∧ ∀ e ∈ B.powersetCard 2, c e = true) := by
  intro s
  induction s with
  | zero =>
    intro a b hab U c _
    have ha : a = 0 := by omega
    subst ha
    left
    exact ⟨∅, Finset.empty_subset U, rfl, by simp⟩
  | succ s ih =>
    intro a b hab U c hU
    cases a with
    | zero =>
      left
      exact ⟨∅, Finset.empty_subset U, rfl, by simp⟩
    | succ a' =>
      cases b with
      | zero =>
        right
        exact ⟨∅, Finset.empty_subset U, rfl, by simp⟩
      | succ b' =>
        have hpos : 0 < U.card :=
          lt_of_lt_of_le (Nat.choose_pos (by omega)) hU
        obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
        let U' : Finset V := U.erase v
        let U0 : Finset V := U'.filter (fun u => c {v, u} = false)
        let U1 : Finset V := U'.filter (fun u => c {v, u} = true)
        have hU'_card : U'.card = U.card - 1 := Finset.card_erase_of_mem hv
        have hpart : U0.card + U1.card = U'.card := by
          have hdisj : Disjoint U0 U1 := by
            rw [Finset.disjoint_left]
            intro u hu0 hu1
            have h0 := (Finset.mem_filter.mp hu0).2
            have h1 := (Finset.mem_filter.mp hu1).2
            rw [h0] at h1
            exact Bool.false_ne_true h1
          have hunion : U0 ∪ U1 = U' := by
            ext u
            simp only [U0, U1, Finset.mem_union, Finset.mem_filter]
            constructor
            · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
            · intro h
              by_cases hc : c {v, u} = false
              · exact Or.inl ⟨h, hc⟩
              · exact Or.inr ⟨h, Bool.eq_true_of_not_eq_false hc⟩
          rw [← Finset.card_union_of_disjoint hdisj, hunion]
        have hpascal : (a' + 1 + (b' + 1)).choose (a' + 1) =
            (a' + (b' + 1)).choose a' + (a' + 1 + b').choose (a' + 1) := by
          have h1 : a' + 1 + (b' + 1) = (a' + b' + 1) + 1 := by omega
          have h2 : a' + (b' + 1) = a' + b' + 1 := by omega
          have h3 : a' + 1 + b' = a' + b' + 1 := by omega
          rw [h1, h2, h3, Nat.choose_succ_succ]
        have hU0_or_U1 :
            (a' + (b' + 1)).choose a' ≤ U0.card ∨ (a' + 1 + b').choose (a' + 1) ≤ U1.card := by
          by_contra h
          push Not at h
          rcases h with ⟨h0, h1⟩
          have hU_ge1 : 1 ≤ U.card := hpos
          omega
        rcases hU0_or_U1 with hU0 | hU1
        · rcases ih a' (b' + 1) (by omega) U0 c hU0 with ⟨A, hAU0, hAcard, hAc⟩ | ⟨B, hBU0, hBcard, hBc⟩
          · left
            have hvA : v ∉ A := fun hvA =>
              (Finset.mem_erase.mp (Finset.mem_filter.mp (hAU0 hvA)).1).1 rfl
            refine ⟨insert v A, ?_, ?_, ?_⟩
            · exact Finset.insert_subset hv
                (hAU0.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset v U)))
            · rw [Finset.card_insert_of_notMem hvA, hAcard]
            · intro e he
              rcases Finset.mem_powersetCard.mp he with ⟨heSub, heCard⟩
              by_cases hve : v ∈ e
              · obtain ⟨u, hu, heEq⟩ : ∃ u ∈ A, e = {v, u} := by
                  have h1 : (e.erase v).card = 1 := by
                    rw [Finset.card_erase_of_mem hve, heCard]
                  obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp h1
                  have hue : u ∈ e := Finset.mem_of_mem_erase (hu_eq ▸ Finset.mem_singleton_self u)
                  have huv : u ≠ v := (Finset.mem_erase.mp (hu_eq ▸ Finset.mem_singleton_self u)).1
                  have huA : u ∈ A := by
                    rcases Finset.mem_insert.mp (heSub hue) with rfl | huA
                    · exact absurd rfl huv
                    · exact huA
                  refine ⟨u, huA, ?_⟩
                  ext w
                  simp only [Finset.mem_insert, Finset.mem_singleton]
                  constructor
                  · intro hw
                    by_cases hwv : w = v
                    · exact Or.inl hwv
                    · right
                      have : w ∈ e.erase v := Finset.mem_erase.mpr ⟨hwv, hw⟩
                      rw [hu_eq, Finset.mem_singleton] at this
                      exact this
                  · rintro (rfl | rfl)
                    · exact hve
                    · exact hue
                rw [heEq]
                exact (Finset.mem_filter.mp (hAU0 hu)).2
              · apply hAc e
                rw [Finset.mem_powersetCard]
                refine ⟨fun w hw => ?_, heCard⟩
                rcases Finset.mem_insert.mp (heSub hw) with rfl | hwA
                · exact absurd hw hve
                · exact hwA
          · right
            exact ⟨B, hBU0.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset v U)),
              hBcard, hBc⟩
        · rcases ih (a' + 1) b' (by omega) U1 c hU1 with ⟨A, hAU1, hAcard, hAc⟩ | ⟨B, hBU1, hBcard, hBc⟩
          · left
            exact ⟨A, hAU1.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset v U)),
              hAcard, hAc⟩
          · right
            have hvB : v ∉ B := fun hvB =>
              (Finset.mem_erase.mp (Finset.mem_filter.mp (hBU1 hvB)).1).1 rfl
            refine ⟨insert v B, ?_, ?_, ?_⟩
            · exact Finset.insert_subset hv
                (hBU1.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset v U)))
            · rw [Finset.card_insert_of_notMem hvB, hBcard]
            · intro e he
              rcases Finset.mem_powersetCard.mp he with ⟨heSub, heCard⟩
              by_cases hve : v ∈ e
              · obtain ⟨u, hu, heEq⟩ : ∃ u ∈ B, e = {v, u} := by
                  have h1 : (e.erase v).card = 1 := by
                    rw [Finset.card_erase_of_mem hve, heCard]
                  obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp h1
                  have hue : u ∈ e := Finset.mem_of_mem_erase (hu_eq ▸ Finset.mem_singleton_self u)
                  have huv : u ≠ v := (Finset.mem_erase.mp (hu_eq ▸ Finset.mem_singleton_self u)).1
                  have huB : u ∈ B := by
                    rcases Finset.mem_insert.mp (heSub hue) with rfl | huB
                    · exact absurd rfl huv
                    · exact huB
                  refine ⟨u, huB, ?_⟩
                  ext w
                  simp only [Finset.mem_insert, Finset.mem_singleton]
                  constructor
                  · intro hw
                    by_cases hwv : w = v
                    · exact Or.inl hwv
                    · right
                      have : w ∈ e.erase v := Finset.mem_erase.mpr ⟨hwv, hw⟩
                      rw [hu_eq, Finset.mem_singleton] at this
                      exact this
                  · rintro (rfl | rfl)
                    · exact hve
                    · exact hue
                rw [heEq]
                exact (Finset.mem_filter.mp (hBU1 hu)).2
              · apply hBc e
                rw [Finset.mem_powersetCard]
                refine ⟨fun w hw => ?_, heCard⟩
                rcases Finset.mem_insert.mp (heSub hw) with rfl | hwB
                · exact absurd hw hve
                · exact hwB

/-- Diagonal specialization: if `4 ^ m ≤ U.card`, every 2-coloring of pairs in `U` has a
monochromatic `m`-clique. -/
private lemma erdos_szekeres_diag {V : Type*} [DecidableEq V] {m : ℕ} {U : Finset V}
    (c : Finset V → Bool) (hU : 4 ^ m ≤ U.card) :
    ∃ b : Bool, ∃ A ⊆ U, A.card = m ∧ ∀ e ∈ A.powersetCard 2, c e = b := by
  have hchoose : (m + m).choose m ≤ U.card := by
    have h1 : (m + m).choose m ≤ 2 ^ (m + m) := Nat.choose_le_two_pow (m + m) m
    have h2 : 2 ^ (m + m) = 4 ^ m := by
      rw [show m + m = 2 * m by omega, pow_mul]; norm_num
    omega
  rcases erdos_szekeres_ramsey (m + m) m m rfl U c hchoose with ⟨A, hA⟩ | ⟨B, hB⟩
  · exact ⟨false, A, hA⟩
  · exact ⟨true, B, hB⟩

/-- Explicit `t = 2` lower bound for all `α : ℝ` (including `α = 0`!):
if `4 ^ m ≤ n`, then `m < F(n, 2, α)`. -/
private lemma t2_lower_of_four_pow {n m : ℕ} (h4 : 4 ^ m ≤ n) (α : ℝ) :
    m < F n 2 α := by
  apply lt_F_of_every_coloring_has_bad
  intro c
  have huniv : 4 ^ m ≤ (Finset.univ : Finset (Fin n)).card := by simpa using h4
  obtain ⟨b, A, _, hAcard, hAc⟩ := erdos_szekeres_diag c huniv
  refine ⟨A, le_of_eq hAcard.symm, !b, Or.inl ?_⟩
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he
  rw [hAc e he]
  cases b <;> decide

/-- **Complete `t = 2` Asymptotic Equivalence (`F^{(2)}(n, α) =Θ[atTop] log n`):**
For every `α ∈ [0, 1/2)` (in fact every `α < 1/2`), `F^{(2)}(n, α) = Θ(log n)`. -/
theorem ppl063_t2_isTheta_log {α : ℝ} (hα0 : 0 ≤ α) (hα_lt : α < 1 / 2) :
    (fun n : ℕ => ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard 2).filter (fun e => c e = b)).card ∧
        α * (X.card.choose 2 : ℝ) ≤
          (((X.powersetCard 2).filter (fun e => c e = b)).card : ℝ)} : ℕ) : ℝ))
      =Θ[atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
  constructor
  · have hbigO := threshold_isBigO_log_rpow (t := 2) (by omega) hα0 hα_lt
    have heq : (fun n : ℕ => (Real.log (n : ℝ)) ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) - 1))) =
        (fun n : ℕ => Real.log (n : ℝ)) := by
      funext n
      have h1 : (1 : ℝ) / (((2 : ℕ) : ℝ) - 1) = 1 := by norm_num
      rw [h1, Real.rpow_one]
    rw [heq] at hbigO
    exact hbigO
  · rw [Asymptotics.isBigO_iff]
    refine ⟨Real.log 4, ?_⟩
    rw [Filter.eventually_atTop]
    refine ⟨4, fun n hn => ?_⟩
    let m : ℕ := Nat.log 4 n
    have h4 : 4 ^ m ≤ n := Nat.pow_log_le_self 4 (by omega)
    have hlt : m < F n 2 α := t2_lower_of_four_pow h4 α
    have hm1 : n < 4 ^ (m + 1) := Nat.lt_pow_succ_log_self (by omega) n
    have hlog_le : Real.log (n : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * Real.log 4 := by
      have hnr : (n : ℝ) < ((4 : ℝ) ^ (m + 1)) := by exact_mod_cast hm1
      have h1 := Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (le_of_lt hnr)
      simpa [Real.log_pow] using h1
    have hm1_le_F : ((m + 1 : ℕ) : ℝ) ≤ (F n 2 α : ℝ) := by exact_mod_cast hlt
    have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have hlogn_pos : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    rw [Real.norm_of_nonneg hlogn_pos, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    calc
      Real.log (n : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * Real.log 4 := hlog_le
      _ ≤ (F n 2 α : ℝ) * Real.log 4 := mul_le_mul_of_nonneg_right hm1_le_F (le_of_lt hlog4_pos)
      _ = Real.log 4 * (F n 2 α : ℝ) := mul_comm _ _

/-- **Complete `t = 2` Non-Jump Theorem (Settling the `t = 2` Slice of `erdos_161.parts.i`):**
For all `α, β ∈ [0, 1/2)`, `F^{(2)}(n, α) =Θ[atTop] F^{(2)}(n, β)` — zero asymptotic jumps
occur at `t = 2`. -/
theorem ppl063_t2_no_jumps {α β : ℝ} (hα0 : 0 ≤ α) (hα_lt : α < 1 / 2)
    (hβ0 : 0 ≤ β) (hβ_lt : β < 1 / 2) :
    (fun n : ℕ => ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard 2).filter (fun e => c e = b)).card ∧
        α * (X.card.choose 2 : ℝ) ≤
          (((X.powersetCard 2).filter (fun e => c e = b)).card : ℝ)} : ℕ) : ℝ))
      =Θ[atTop]
    (fun n : ℕ => ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard 2).filter (fun e => c e = b)).card ∧
        β * (X.card.choose 2 : ℝ) ≤
          (((X.powersetCard 2).filter (fun e => c e = b)).card : ℝ)} : ℕ) : ℝ)) :=
  (ppl063_t2_isTheta_log hα0 hα_lt).trans (ppl063_t2_isTheta_log hβ0 hβ_lt).symm

/-! ### Section 5: Conlon–Fox–Sudakov [CFS11] `t = 3` Positive-Density Collapse -/

/-- **Unified KST Power-Mean Lemma (used for both CFS11 `t = 3` and Erdős 1964 general `t`):**
Given a bipartite relation `adj` on `X × Y` with `1 ≤ t ≤ Y.card`, `0 < δ`, `(t : ℝ) ≤ δ * Y.card`,
and at least `2 * δ * |X| * |Y|` edges, there exists a `t`-subset `U ⊆ Y` whose common neighborhood
in `X` has size at least `δ ^ t * |X|`. -/
private lemma kst_bipartite_power_mean {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (adj : α → β → Prop) [DecidableRel adj]
    {t : ℕ} (ht : 1 ≤ t) (htY_nat : t ≤ Y.card) {δ : ℝ} (hδ : 0 < δ)
    (htY : (t : ℝ) ≤ δ * (Y.card : ℝ))
    (hedges : 2 * δ * (X.card : ℝ) * (Y.card : ℝ) ≤
      ((∑ x ∈ X, (Y.filter (fun y => adj x y)).card : ℕ) : ℝ)) :
    ∃ U ∈ Y.powersetCard t,
      δ ^ t * (X.card : ℝ) ≤ ((X.filter (fun x => ∀ u ∈ U, adj x u)).card : ℝ) := by
  by_cases hX0 : X.card = 0
  · obtain ⟨U, hUY, hUcard⟩ := Finset.exists_subset_card_eq htY_nat
    refine ⟨U, Finset.mem_powersetCard.mpr ⟨hUY, hUcard⟩, ?_⟩
    simp [hX0]
  have hXpos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hX0)
  have hYpos : (0 : ℝ) < (Y.card : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) htY_nat)
  let deg : α → ℕ := fun x => (Y.filter (fun y => adj x y)).card
  let yv : α → ℝ := fun x => max 0 ((deg x : ℝ) - (t : ℝ))
  -- Step 1: ∑ x ∈ X, yv x ≥ δ * |X| * |Y|
  have hsum_y : δ * (X.card : ℝ) * (Y.card : ℝ) ≤ ∑ x ∈ X, yv x := by
    have h1 : ∑ x ∈ X, ((deg x : ℝ) - (t : ℝ)) ≤ ∑ x ∈ X, yv x :=
      Finset.sum_le_sum fun x _ => le_max_right 0 _
    have h2 : ∑ x ∈ X, ((deg x : ℝ) - (t : ℝ)) =
        ((∑ x ∈ X, deg x : ℕ) : ℝ) - (X.card : ℝ) * (t : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_sum]
    have h3 : (X.card : ℝ) * (t : ℝ) ≤ (X.card : ℝ) * (δ * (Y.card : ℝ)) :=
      mul_le_mul_of_nonneg_left htY (le_of_lt hXpos)
    linarith
  -- Step 2: Power-mean inequality: (δ * |Y|)^t * |X| ≤ ∑ x ∈ X, (yv x)^t
  have hpow_mean : (X.card : ℝ) * (δ * (Y.card : ℝ)) ^ t ≤ ∑ x ∈ X, (yv x) ^ t := by
    have hw_nonneg : ∀ x ∈ X, (0 : ℝ) ≤ (X.card : ℝ)⁻¹ := fun _ _ => by positivity
    have hw_sum : ∑ _x ∈ X, (X.card : ℝ)⁻¹ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp [ne_of_gt hXpos]
    have hy_nonneg : ∀ x ∈ X, 0 ≤ yv x := fun _ _ => le_max_left 0 _
    have hjensen := Real.pow_arith_mean_le_arith_mean_pow X (fun _ => (X.card : ℝ)⁻¹) yv
      hw_nonneg hw_sum hy_nonneg t
    have hmean_ge : δ * (Y.card : ℝ) ≤ ∑ x ∈ X, (X.card : ℝ)⁻¹ * yv x := by
      rw [← Finset.mul_sum, inv_mul_eq_div, le_div_iff₀ hXpos]
      linarith
    have hpow_le : (δ * (Y.card : ℝ)) ^ t ≤ (∑ x ∈ X, (X.card : ℝ)⁻¹ * yv x) ^ t :=
      pow_le_pow_left₀ (by positivity) hmean_ge t
    have hcomb := le_trans hpow_le hjensen
    rw [← Finset.mul_sum, inv_mul_eq_div, le_div_iff₀ hXpos] at hcomb
    linarith
  -- Step 3: Pointwise (yv x)^t ≤ t! * (deg x).choose t
  have hptwise : ∀ x ∈ X, (yv x) ^ t ≤ (t.factorial : ℝ) * ((deg x).choose t : ℝ) := by
    intro x _
    by_cases hdt : t ≤ deg x
    · have hsub_nonneg : (0 : ℝ) ≤ (deg x : ℝ) - (t : ℝ) :=
        sub_nonneg.mpr (Nat.cast_le.mpr hdt)
      have hy_eq : yv x = (deg x : ℝ) - (t : ℝ) := max_eq_right hsub_nonneg
      rw [hy_eq]
      have h1 : (deg x : ℝ) - (t : ℝ) ≤ ((deg x - t + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_sub hdt, Nat.cast_one]; linarith
      have h2 : ((deg x : ℝ) - (t : ℝ)) ^ t ≤ ((deg x - t + 1 : ℕ) : ℝ) ^ t :=
        pow_le_pow_left₀ hsub_nonneg h1 t
      have h3 : ((deg x - t + 1 : ℕ) : ℝ) ^ t ≤ (t.factorial : ℝ) * ((deg x).choose t : ℝ) := by
        exact_mod_cast factorial_mul_choose_ge_pow hdt
      exact le_trans h2 h3
    · have hsub_nonpos : (deg x : ℝ) - (t : ℝ) ≤ 0 :=
        sub_nonpos.mpr (Nat.cast_le.mpr (by omega))
      have hy_eq : yv x = 0 := max_eq_left hsub_nonpos
      rw [hy_eq, zero_pow (by omega : t ≠ 0)]
      positivity
  -- Step 4: Double-counting ∑ x ∈ X, (deg x).choose t = ∑ U ∈ Y.powersetCard t, commonDeg U
  have hdouble : ∑ x ∈ X, (deg x).choose t =
      ∑ U ∈ Y.powersetCard t, (X.filter (fun x => ∀ u ∈ U, adj x u)).card := by
    have hL : ∑ x ∈ X, (deg x).choose t =
        ∑ x ∈ X, ∑ U ∈ Y.powersetCard t, (if ∀ u ∈ U, adj x u then 1 else 0) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      dsimp only [deg]
      rw [← Finset.card_powersetCard, ← Finset.card_filter]
      congr 1
      ext U
      simp only [Finset.mem_powersetCard, Finset.mem_filter]
      constructor
      · rintro ⟨hUsub, hUcard⟩
        refine ⟨⟨fun u hu => (Finset.mem_filter.mp (hUsub hu)).1, hUcard⟩,
          fun u hu => (Finset.mem_filter.mp (hUsub hu)).2⟩
      · rintro ⟨⟨hUY, hUcard⟩, hadj⟩
        exact ⟨fun u hu => Finset.mem_filter.mpr ⟨hUY hu, hadj u hu⟩, hUcard⟩
    rw [hL, Finset.sum_comm]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [Finset.card_filter]
  -- Step 5: Pigeonhole over U ∈ Y.powersetCard t
  have hsum_common : (X.card : ℝ) * (δ * (Y.card : ℝ)) ^ t ≤
      (t.factorial : ℝ) * ∑ U ∈ Y.powersetCard t,
        ((X.filter (fun x => ∀ u ∈ U, adj x u)).card : ℝ) := by
    calc
      (X.card : ℝ) * (δ * (Y.card : ℝ)) ^ t ≤ ∑ x ∈ X, (yv x) ^ t := hpow_mean
      _ ≤ ∑ x ∈ X, (t.factorial : ℝ) * ((deg x).choose t : ℝ) := Finset.sum_le_sum hptwise
      _ = (t.factorial : ℝ) * ∑ x ∈ X, ((deg x).choose t : ℝ) := (Finset.mul_sum _ _ _).symm
      _ = (t.factorial : ℝ) * ∑ U ∈ Y.powersetCard t,
            ((X.filter (fun x => ∀ u ∈ U, adj x u)).card : ℝ) := by
          congr 1
          exact_mod_cast hdouble
  by_contra hnone
  push Not at hnone
  have hlt_sum : ∑ U ∈ Y.powersetCard t,
      ((X.filter (fun x => ∀ u ∈ U, adj x u)).card : ℝ) <
      ∑ _U ∈ Y.powersetCard t, (δ ^ t * (X.card : ℝ)) := by
    refine Finset.sum_lt_sum_of_nonempty ?_ hnone
    rw [← Finset.card_pos, Finset.card_powersetCard]
    exact Nat.choose_pos htY_nat
  have hrhs_sum : ∑ _U ∈ Y.powersetCard t, (δ ^ t * (X.card : ℝ)) =
      ((Y.card.choose t : ℕ) : ℝ) * (δ ^ t * (X.card : ℝ)) := by
    rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  have hfac_pos : (0 : ℝ) < (t.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos t
  have hstrict : (X.card : ℝ) * (δ * (Y.card : ℝ)) ^ t <
      (t.factorial : ℝ) * (((Y.card.choose t : ℕ) : ℝ) * (δ ^ t * (X.card : ℝ))) := by
    rw [← hrhs_sum]
    exact lt_of_le_of_lt hsum_common (mul_lt_mul_of_pos_left hlt_sum hfac_pos)
  have hchoose_ub : (t.factorial : ℝ) * (Y.card.choose t : ℝ) ≤ (Y.card : ℝ) ^ t := by
    have hnat : t.factorial * Y.card.choose t ≤ Y.card ^ t := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow Y.card t
    exact_mod_cast hnat
  have hupper : (t.factorial : ℝ) * (((Y.card.choose t : ℕ) : ℝ) * (δ ^ t * (X.card : ℝ))) ≤
      (X.card : ℝ) * (δ * (Y.card : ℝ)) ^ t := by
    calc
      (t.factorial : ℝ) * (((Y.card.choose t : ℕ) : ℝ) * (δ ^ t * (X.card : ℝ)))
          = ((t.factorial : ℝ) * (Y.card.choose t : ℝ)) * (δ ^ t * (X.card : ℝ)) := by ring
      _ ≤ (Y.card : ℝ) ^ t * (δ ^ t * (X.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hchoose_ub (by positivity)
      _ = (X.card : ℝ) * (δ * (Y.card : ℝ)) ^ t := by rw [mul_pow]; ring
  linarith

/-- **CFS11 Lemma 1 (Elementary Bipartite Subset-Pigeonhole):**
Any bipartite graph on `A × B` with `|A| = 4 * m` and edge density `≥ 1/2` contains a complete
bipartite subgraph `A' × B'` with `|A'| = m` and `|B| ≤ 2 ^ (4 * m + 2) * |B'|`. -/
private lemma bipartite_dense_complete {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (adj : α → β → Prop) [DecidableRel adj]
    (m : ℕ) (hA : A.card = 4 * m)
    (hdense : A.card * B.card ≤ 2 * ∑ b ∈ B, (A.filter (fun a => adj a b)).card) :
    ∃ A' ⊆ A, A'.card = m ∧ ∃ B' ⊆ B, B.card ≤ 2 ^ (4 * m + 2) * B'.card ∧
      ∀ a ∈ A', ∀ b ∈ B', adj a b := by
  classical
  by_cases hm0 : m = 0
  · subst hm0
    refine ⟨∅, Finset.empty_subset A, rfl, B, Finset.Subset.refl B, ?_, by simp⟩
    have : 1 ≤ 2 ^ (4 * 0 + 2) := by norm_num
    exact Nat.le_mul_of_pos_left B.card (by positivity)
  have hm_pos : 1 ≤ m := Nat.pos_of_ne_zero hm0
  let deg : β → ℕ := fun b => (A.filter (fun a => adj a b)).card
  let Bgood : Finset β := B.filter (fun b => m ≤ deg b)
  let Bbad : Finset β := B.filter (fun b => ¬ (m ≤ deg b))
  have hsum_split : ∑ b ∈ B, deg b = ∑ b ∈ Bgood, deg b + ∑ b ∈ Bbad, deg b :=
    (Finset.sum_filter_add_sum_filter_not B (fun b => m ≤ deg b) deg).symm
  have hgood_ub : ∑ b ∈ Bgood, deg b ≤ Bgood.card * (4 * m) := by
    calc
      ∑ b ∈ Bgood, deg b ≤ ∑ _b ∈ Bgood, (4 * m) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [← hA]
        exact Finset.card_filter_le _ _
      _ = Bgood.card * (4 * m) := by rw [Finset.sum_const, smul_eq_mul]
  have hbad_ub : ∑ b ∈ Bbad, deg b ≤ B.card * m := by
    calc
      ∑ b ∈ Bbad, deg b ≤ ∑ _b ∈ Bbad, m := by
        refine Finset.sum_le_sum fun b hb => ?_
        have hlt := (Finset.mem_filter.mp hb).2
        omega
      _ = Bbad.card * m := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ B.card * m := Nat.mul_le_mul_right m (Finset.card_filter_le _ _)
  have hBgood_ge : B.card ≤ 4 * Bgood.card := by
    rw [hA] at hdense
    have hsum_le : ∑ b ∈ B, deg b ≤ Bgood.card * (4 * m) + B.card * m := by
      rw [hsum_split]; exact Nat.add_le_add hgood_ub hbad_ub
    have h1 : 4 * m * B.card ≤ 2 * (Bgood.card * (4 * m) + B.card * m) :=
      le_trans hdense (Nat.mul_le_mul_left 2 hsum_le)
    have h2 : m * B.card ≤ m * (4 * Bgood.card) := by linarith
    exact Nat.le_of_mul_le_mul_left h2 hm_pos
  -- For each b ∈ Bgood, choose an m-subset of its neighbors in A
  have hex : ∀ b : β, b ∈ Bgood → ∃ S ∈ A.powersetCard m, ∀ a ∈ S, adj a b := by
    intro b hb
    have hdeg : m ≤ (A.filter (fun a => adj a b)).card := (Finset.mem_filter.mp hb).2
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hdeg
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨hSsub.trans (Finset.filter_subset _ _), hScard⟩,
      fun a ha => (Finset.mem_filter.mp (hSsub ha)).2⟩
  let pick : β → Finset α := fun b =>
    if hb : b ∈ Bgood then Classical.choose (hex b hb) else ∅
  have hpick_mem : ∀ b ∈ Bgood, pick b ∈ A.powersetCard m := by
    intro b hb
    dsimp only [pick]
    rw [dif_pos hb]
    exact (Classical.choose_spec (hex b hb)).1
  have hpick_adj : ∀ b ∈ Bgood, ∀ a ∈ pick b, adj a b := by
    intro b hb
    dsimp only [pick]
    rw [dif_pos hb]
    exact (Classical.choose_spec (hex b hb)).2
  -- Pigeonhole over S ∈ A.powersetCard m
  have hsum_fibers : ∑ S ∈ A.powersetCard m, (Bgood.filter (fun b => pick b = S)).card =
      Bgood.card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext b
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨_, _, hb, _⟩; exact hb
      · intro hb; exact ⟨pick b, hpick_mem b hb, hb, rfl⟩
    · intro S₁ _ S₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro b hb₁ hb₂
      have h1 := (Finset.mem_filter.mp hb₁).2
      have h2 := (Finset.mem_filter.mp hb₂).2
      exact hne (h1.symm.trans h2)
  have hcard_pow : (A.powersetCard m).card ≤ 2 ^ (4 * m) := by
    rw [Finset.card_powersetCard, hA]
    exact Nat.choose_le_two_pow (4 * m) m
  have hex_S : ∃ S ∈ A.powersetCard m,
      Bgood.card ≤ 2 ^ (4 * m) * (Bgood.filter (fun b => pick b = S)).card := by
    by_contra hnone
    push Not at hnone
    have hpos_pow : (A.powersetCard m).Nonempty := by
      rw [← Finset.card_pos, Finset.card_powersetCard, hA]
      exact Nat.choose_pos (by omega)
    have hstrict :
        ∑ S ∈ A.powersetCard m, 2 ^ (4 * m) * (Bgood.filter (fun b => pick b = S)).card <
          ∑ _S ∈ A.powersetCard m, Bgood.card :=
      Finset.sum_lt_sum_of_nonempty hpos_pow hnone
    rw [← Finset.mul_sum, hsum_fibers, Finset.sum_const, smul_eq_mul] at hstrict
    have hle : (A.powersetCard m).card * Bgood.card ≤ 2 ^ (4 * m) * Bgood.card :=
      Nat.mul_le_mul_right Bgood.card hcard_pow
    omega
  obtain ⟨A', hA'mem, hA'card⟩ := hex_S
  rcases Finset.mem_powersetCard.mp hA'mem with ⟨hA'sub, hA'c⟩
  refine ⟨A', hA'sub, hA'c, Bgood.filter (fun b => pick b = A'),
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _), ?_, ?_⟩
  · calc
      B.card ≤ 4 * Bgood.card := hBgood_ge
      _ ≤ 4 * (2 ^ (4 * m) * (Bgood.filter (fun b => pick b = A')).card) :=
          Nat.mul_le_mul_left 4 hA'card
      _ = 2 ^ (4 * m + 2) * (Bgood.filter (fun b => pick b = A')).card := by
          rw [pow_add]; ring
  · intro a ha b hb
    rcases Finset.mem_filter.mp hb with ⟨hb_good, hpick_eq⟩
    rw [← hpick_eq] at ha
    exact hpick_adj b hb_good a ha

/-- **CFS11 Lemma 2 (Dense Graph KST Specialization):**
Any graph `G ⊆ S.powersetCard 2` with `ε * |S|^2 ≤ |G|` and `1 ≤ t ≤ ε * |S|` contains disjoint
`U, W ⊆ S` with `|U| = t`, `ε^t * |S| ≤ |W|`, and `{u, w} ∈ G` for all `u ∈ U, w ∈ W`. -/
private lemma kst_dense_graph {V : Type*} [DecidableEq V]
    (S : Finset V) (G : Finset (Finset V)) (hG : G ⊆ S.powersetCard 2)
    {t : ℕ} (ht : 1 ≤ t) (htS_nat : t ≤ S.card) {ε : ℝ} (hε : 0 < ε)
    (htS : (t : ℝ) ≤ ε * (S.card : ℝ))
    (hGcard : ε * (S.card : ℝ) ^ 2 ≤ (G.card : ℝ)) :
    ∃ U ⊆ S, ∃ W ⊆ S, Disjoint U W ∧ U.card = t ∧
      ε ^ t * (S.card : ℝ) ≤ (W.card : ℝ) ∧ ∀ u ∈ U, ∀ w ∈ W, ({u, w} : Finset V) ∈ G := by
  have hhand : ∑ v ∈ S, (S.filter (fun u => ({v, u} : Finset V) ∈ G)).card = 2 * G.card := by
    have hL : ∑ v ∈ S, (S.filter (fun u => ({v, u} : Finset V) ∈ G)).card =
        ∑ v ∈ S, ∑ e ∈ G, (if v ∈ e then 1 else 0) := by
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← Finset.card_filter]
      refine Finset.card_bij (fun u _ => ({v, u} : Finset V)) ?_ ?_ ?_
      · intro u hu
        have hvuG : ({v, u} : Finset V) ∈ G := (Finset.mem_filter.mp hu).2
        exact Finset.mem_filter.mpr ⟨hvuG, Finset.mem_insert_self v {u}⟩
      · intro u₁ hu₁ u₂ hu₂ hEq
        have hvu₁ : ({v, u₁} : Finset V) ∈ G := (Finset.mem_filter.mp hu₁).2
        have hvu₂ : ({v, u₂} : Finset V) ∈ G := (Finset.mem_filter.mp hu₂).2
        have hne₁ : v ≠ u₁ := by
          have hc := (Finset.mem_powersetCard.mp (hG hvu₁)).2
          intro h; subst h; simp at hc
        have hne₂ : v ≠ u₂ := by
          have hc := (Finset.mem_powersetCard.mp (hG hvu₂)).2
          intro h; subst h; simp at hc
        have hmem : u₁ ∈ ({v, u₂} : Finset V) := by
          rw [← hEq]; simp
        rcases Finset.mem_insert.mp hmem with rfl | h2
        · exact absurd rfl hne₁
        · exact Finset.mem_singleton.mp h2
      · intro e he
        rcases Finset.mem_filter.mp he with ⟨heG, hve⟩
        rcases Finset.mem_powersetCard.mp (hG heG) with ⟨heS, hecard⟩
        have h1 : (e.erase v).card = 1 := by rw [Finset.card_erase_of_mem hve, hecard]
        obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp h1
        have hue : u ∈ e := Finset.mem_of_mem_erase (hu_eq ▸ Finset.mem_singleton_self u)
        have huv : u ≠ v := (Finset.mem_erase.mp (hu_eq ▸ Finset.mem_singleton_self u)).1
        have heEq : ({v, u} : Finset V) = e := by
          ext w
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (rfl | rfl) <;> assumption
          · intro hw
            by_cases hwv : w = v
            · exact Or.inl hwv
            · right
              have : w ∈ e.erase v := Finset.mem_erase.mpr ⟨hwv, hw⟩
              rw [hu_eq, Finset.mem_singleton] at this
              exact this
        refine ⟨u, Finset.mem_filter.mpr ⟨heS hue, by rw [heEq]; exact heG⟩, heEq⟩
    rw [hL, Finset.sum_comm]
    have hinner : ∀ e ∈ G, (∑ v ∈ S, if v ∈ e then (1 : ℕ) else 0) = 2 := by
      intro e he
      rcases Finset.mem_powersetCard.mp (hG he) with ⟨heS, hecard⟩
      rw [← Finset.card_filter]
      have hEq : S.filter (fun v => v ∈ e) = e := by
        ext v; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨heS h, h⟩⟩
      rw [hEq, hecard]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_comm]
  have hedges : 2 * ε * (S.card : ℝ) * (S.card : ℝ) ≤
      ((∑ v ∈ S, (S.filter (fun u => ({v, u} : Finset V) ∈ G)).card : ℕ) : ℝ) := by
    rw [hhand]
    push_cast
    nlinarith
  obtain ⟨U, hUmem, hWcard⟩ :=
    kst_bipartite_power_mean S S (fun v u => ({v, u} : Finset V) ∈ G) ht htS_nat hε htS hedges
  rcases Finset.mem_powersetCard.mp hUmem with ⟨hUS, hUcard⟩
  let W : Finset V := S.filter (fun v => ∀ u ∈ U, ({v, u} : Finset V) ∈ G)
  have hdisj : Disjoint U W := by
    rw [Finset.disjoint_left]
    intro u huU huW
    have hmem : ({u, u} : Finset V) ∈ G := (Finset.mem_filter.mp huW).2 u huU
    have hc := (Finset.mem_powersetCard.mp (hG hmem)).2
    simp at hc
  refine ⟨U, hUS, W, Finset.filter_subset _ _, hdisj, hUcard, hWcard, ?_⟩
  intro u hu w hw
  have hwu : ({w, u} : Finset V) ∈ G := (Finset.mem_filter.mp hw).2 u hu
  rwa [Finset.pair_comm] at hwu

/-- Single sub-step inside CFS11 round `i + 1`: refine one previous part `V_h` (size `4 * m'`)
to `V_h'` (size `m'`) and shrink graph `G` by at most `2 ^ (4 * m' + 2)` so all triples in
`V_h' × G'` share a single color `b`. -/
private lemma cfs11_substep {N : ℕ} (c : Finset (Fin N) → Bool)
    (Vh : Finset (Fin N)) (S : Finset (Fin N)) (G : Finset (Finset (Fin N)))
    (_hdisj : Disjoint Vh S) (_hG : G ⊆ S.powersetCard 2)
    (m' : ℕ) (hVh : Vh.card = 4 * m') :
    ∃ b : Bool, ∃ Vh' ⊆ Vh, Vh'.card = m' ∧
      ∃ G' ⊆ G, G.card ≤ 2 ^ (4 * m' + 2) * G'.card ∧
        ∀ v ∈ Vh', ∀ e ∈ G', c (insert v e) = b := by
  let count (b : Bool) : ℕ :=
    ∑ e ∈ G, (Vh.filter (fun v => c (insert v e) = b)).card
  have hsum_colors : count false + count true = Vh.card * G.card := by
    dsimp only [count]
    rw [← Finset.sum_add_distrib]
    have hinner : ∀ e ∈ G,
        (Vh.filter (fun v => c (insert v e) = false)).card +
        (Vh.filter (fun v => c (insert v e) = true)).card = Vh.card := by
      intro e _
      have hdisj_c : Disjoint (Vh.filter (fun v => c (insert v e) = false))
          (Vh.filter (fun v => c (insert v e) = true)) := by
        rw [Finset.disjoint_left]
        intro v h0 h1
        have hc0 := (Finset.mem_filter.mp h0).2
        have hc1 := (Finset.mem_filter.mp h1).2
        rw [hc0] at hc1
        exact Bool.false_ne_true hc1
      have hunion : Vh.filter (fun v => c (insert v e) = false) ∪
          Vh.filter (fun v => c (insert v e) = true) = Vh := by
        ext v
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          by_cases hc : c (insert v e) = false
          · exact Or.inl ⟨h, hc⟩
          · exact Or.inr ⟨h, Bool.eq_true_of_not_eq_false hc⟩
      rw [← Finset.card_union_of_disjoint hdisj_c, hunion]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_comm]
  have hmaj : ∃ b : Bool, Vh.card * G.card ≤ 2 * count b := by
    by_cases h : count false ≤ count true
    · exact ⟨true, by omega⟩
    · exact ⟨false, by omega⟩
  obtain ⟨b, hb⟩ := hmaj
  obtain ⟨Vh', hVh'sub, hVh'card, G', hG'sub, hG'card, hadj⟩ :=
    bipartite_dense_complete Vh G (fun v e => c (insert v e) = b) m' hVh hb
  exact ⟨b, Vh', hVh'sub, hVh'card, G', hG'sub, hG'card, hadj⟩

/-- Inner loop of CFS11 round `i + 1`: refine `j` previous parts `V 0, ..., V (j - 1)`
simultaneously against `G_0 = S.powersetCard 2`. -/
private lemma cfs11_inner_loop {N : ℕ} (c : Finset (Fin N) → Bool)
    (S : Finset (Fin N)) (m' : ℕ) :
    ∀ (j : ℕ) (V : Fin j → Finset (Fin N)),
      (∀ h : Fin j, Disjoint (V h) S) →
      (∀ h : Fin j, (V h).card = 4 * m') →
      ∃ (χ : Fin j → Bool) (V' : Fin j → Finset (Fin N)) (G : Finset (Finset (Fin N))),
        G ⊆ S.powersetCard 2 ∧
        (∀ h : Fin j, V' h ⊆ V h ∧ (V' h).card = m') ∧
        (S.powersetCard 2).card ≤ 2 ^ (j * (4 * m' + 2)) * G.card ∧
        (∀ h : Fin j, ∀ v ∈ V' h, ∀ e ∈ G, c (insert v e) = χ h) := by
  intro j
  induction j with
  | zero =>
    intro V _ _
    refine ⟨Fin.elim0, Fin.elim0, S.powersetCard 2, Finset.Subset.refl _, fun h => h.elim0,
      by simp, fun h => h.elim0⟩
  | succ j ih =>
    intro V hdisj hcard
    obtain ⟨χ_prev, V'_prev, G_prev, hG_prev_sub, hV'_prev, hG_prev_card, hcolor_prev⟩ :=
      ih (fun h => V h.castSucc) (fun h => hdisj h.castSucc) (fun h => hcard h.castSucc)
    obtain ⟨b_last, V_last', hV_last'_sub, hV_last'_card, G_new, hG_new_sub, hG_new_card,
        hcolor_last⟩ :=
      cfs11_substep c (V (Fin.last j)) S G_prev (hdisj (Fin.last j)) hG_prev_sub m'
        (hcard (Fin.last j))
    let χ : Fin (j + 1) → Bool := Fin.snoc χ_prev b_last
    let V' : Fin (j + 1) → Finset (Fin N) := Fin.snoc V'_prev V_last'
    refine ⟨χ, V', G_new, hG_new_sub.trans hG_prev_sub, ?_, ?_, ?_⟩
    · intro h
      refine Fin.lastCases ?_ ?_ h
      · simpa [V'] using ⟨hV_last'_sub, hV_last'_card⟩
      · intro h'
        simpa [V'] using hV'_prev h'
    · calc
        (S.powersetCard 2).card ≤ 2 ^ (j * (4 * m' + 2)) * G_prev.card := hG_prev_card
        _ ≤ 2 ^ (j * (4 * m' + 2)) * (2 ^ (4 * m' + 2) * G_new.card) :=
            Nat.mul_le_mul_left _ hG_new_card
        _ = 2 ^ ((j + 1) * (4 * m' + 2)) * G_new.card := by
            rw [← mul_assoc, ← pow_add, show j * (4 * m' + 2) + (4 * m' + 2) =
              (j + 1) * (4 * m' + 2) by ring]
    · intro h
      refine Fin.lastCases ?_ ?_ h
      · intro v hv e he
        have hv' : v ∈ V_last' := by simpa [V'] using hv
        simpa [χ] using hcolor_last v hv' e he
      · intro h' v hv e he
        have hv' : v ∈ V'_prev h' := by simpa [V'] using hv
        simpa [χ] using hcolor_prev h' v hv' e (hG_new_sub he)

/-- **CFS11 Iterative Construction of `r` Uniform Parts + Reservoir `S`:**
Given `r ≥ 1`, `n ≥ 1`, `M = 4 ^ r * n`, and `2 ^ (8 * M ^ 2) ≤ N`, builds for every `i ≤ r`
disjoint parts `V 0, ..., V (i - 1)` of size `4 ^ (r - i) * n`, a disjoint reservoir `S` of size
`≥ 2 ^ (8 * M ^ 2 - 4 * M * (M - 4 ^ (r - i) * n))`, and pair colors `χ(a, b)` (`a < b < i`)
such that every triple `{x, y, z}` with `x ∈ V a`, `y ∈ V b`, and `z ∈ V c` (`b < c`) or `z ∈ S`
has color `χ(a, b)`. -/
private lemma cfs11_build_parts {N r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n)
    (c : Finset (Fin N) → Bool) (hN : 2 ^ (8 * (4 ^ r * n) ^ 2) ≤ N) :
    let M : ℕ := 4 ^ r * n
    ∀ i : ℕ, i ≤ r →
      ∃ (V : Fin i → Finset (Fin N)) (S : Finset (Fin N)) (χ : Fin i → Fin i → Bool),
        (∀ a : Fin i, (V a).card = 4 ^ (r - i) * n) ∧
        (∀ a b : Fin i, a ≠ b → Disjoint (V a) (V b)) ∧
        (∀ a : Fin i, Disjoint (V a) S) ∧
        2 ^ (8 * M ^ 2 - 4 * M * (M - 4 ^ (r - i) * n)) ≤ S.card ∧
        (∀ a b : Fin i, a < b → ∀ x ∈ V a, ∀ y ∈ V b,
          (∀ d : Fin i, b < d → ∀ z ∈ V d, c {x, y, z} = χ a b) ∧
          (∀ z ∈ S, c {x, y, z} = χ a b)) := by
  intro M i
  induction i with
  | zero =>
    intro _
    refine ⟨Fin.elim0, Finset.univ, fun a => a.elim0,
      fun a => a.elim0, fun a => a.elim0, fun a => a.elim0, ?_, fun a => a.elim0⟩
    dsimp only [M]
    simp only [Nat.sub_zero, Nat.sub_self, mul_zero, Finset.card_univ, Fintype.card_fin]
    exact hN
  | succ i ih =>
    intro hir
    have hi_le : i ≤ r := by omega
    obtain ⟨V, S, χ_prev, hVcard, hVdisj, hVSdisj, hScard, hcolor⟩ := ih hi_le
    let m' : ℕ := 4 ^ (r - (i + 1)) * n
    have h4m' : 4 ^ (r - i) * n = 4 * m' := by
      dsimp only [m']
      have hpow : 4 ^ (r - i) = 4 * 4 ^ (r - (i + 1)) := by
        rw [show r - i = (r - (i + 1)) + 1 by omega, pow_succ']
      rw [hpow, mul_assoc]
    have hVcard' : ∀ h : Fin i, (V h).card = 4 * m' := fun h => (hVcard h).trans h4m'
    -- Run inner loop on V 0, ..., V (i - 1) and S
    obtain ⟨χ_new, V'_prev, G, hGsub, hV'_prop, hGcard_nat, hGcolor⟩ :=
      cfs11_inner_loop c S m' i V hVSdisj hVcard'
    -- Bound exponent: i * (4 * m' + 2) + 2 ≤ 4 * M
    have hM_ge4 : 4 ≤ M := by
      dsimp only [M]
      have h4r : 4 ≤ 4 ^ r := by
        calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ r := Nat.pow_le_pow_right (by norm_num) hr
      nlinarith
    have hm'_le_M : m' ≤ M := by
      dsimp only [m', M]
      exact Nat.mul_le_mul_right n (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hi_le_pow : i ≤ 4 ^ i := by
      have : i < 2 ^ i := Nat.lt_two_pow_self
      have : 2 ^ i ≤ 4 ^ i := Nat.pow_le_pow_left (by norm_num) i
      omega
    have him_le_M : i * (4 * m') ≤ M := by
      rw [← h4m']
      dsimp only [M]
      calc
        i * (4 ^ (r - i) * n) ≤ 4 ^ i * (4 ^ (r - i) * n) := Nat.mul_le_mul_right _ hi_le_pow
        _ = (4 ^ i * 4 ^ (r - i)) * n := by ring
        _ = 4 ^ r * n := by rw [← pow_add, Nat.add_sub_of_le hi_le]
    have hi_le_M : i ≤ M := by
      calc i ≤ 4 ^ i := hi_le_pow
      _ ≤ 4 ^ r := Nat.pow_le_pow_right (by norm_num) hi_le
      _ ≤ 4 ^ r * n := Nat.le_mul_of_pos_right _ hn
    have hexp_le : i * (4 * m' + 2) + 2 ≤ 4 * M := by
      have h1 : i * (4 * m' + 2) = i * (4 * m') + 2 * i := by ring
      omega
    -- Lower bound on S.card: ≥ 2 ^ (4 * M ^ 2)
    have hS_ge_4M2 : 2 ^ (4 * M ^ 2) ≤ S.card := by
      have hexp : 4 * M ^ 2 ≤ 8 * M ^ 2 - 4 * M * (M - 4 ^ (r - i) * n) := by
        have hsub_le : M - 4 ^ (r - i) * n ≤ M := Nat.sub_le _ _
        have hmul_le : 4 * M * (M - 4 ^ (r - i) * n) ≤ 4 * M ^ 2 := by nlinarith
        omega
      exact le_trans (Nat.pow_le_pow_right (by norm_num) hexp) hScard
    have hS_ge2 : 2 ≤ S.card := by
      have : 2 ≤ 2 ^ (4 * M ^ 2) :=
        le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
      omega
    -- Show ε = (2 : ℝ) ^ (-(4 * M : ℤ)) satisfies ε * S.card ^ 2 ≤ G.card
    let ε : ℝ := ((2 : ℝ) ^ (4 * M))⁻¹
    have hε_pos : 0 < ε := by dsimp only [ε]; positivity
    have hchoose2_ge : S.card ^ 2 ≤ 4 * (S.powersetCard 2).card := by
      rw [Finset.card_powersetCard, Nat.choose_two_right]
      have h1 : S.card * (S.card - 1) = 2 * (S.card * (S.card - 1) / 2) :=
        (Nat.mul_div_cancel' (Nat.even_mul_pred_self S.card).two_dvd).symm
      have h2 : S.card ≤ 2 * (S.card - 1) := by omega
      have h3 : S.card ^ 2 ≤ 2 * (S.card * (S.card - 1)) := by
        rw [sq]; nlinarith
      omega
    have hG_dense_nat : S.card ^ 2 ≤ 2 ^ (4 * M) * G.card := by
      calc
        S.card ^ 2 ≤ 4 * (S.powersetCard 2).card := hchoose2_ge
        _ ≤ 4 * (2 ^ (i * (4 * m' + 2)) * G.card) := Nat.mul_le_mul_left 4 hGcard_nat
        _ = 2 ^ (i * (4 * m' + 2) + 2) * G.card := by rw [pow_add]; ring
        _ ≤ 2 ^ (4 * M) * G.card :=
            Nat.mul_le_mul_right G.card (Nat.pow_le_pow_right (by norm_num) hexp_le)
    have hG_dense : ε * (S.card : ℝ) ^ 2 ≤ (G.card : ℝ) := by
      dsimp only [ε]
      rw [inv_mul_eq_div, div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (4 * M))]
      have : ((S.card ^ 2 : ℕ) : ℝ) ≤ ((2 ^ (4 * M) * G.card : ℕ) : ℝ) := by
        exact_mod_cast hG_dense_nat
      push_cast at this
      linarith
    -- Check 1 ≤ m' and m' ≤ ε * S.card
    have hm'_pos : 1 ≤ m' := by
      dsimp only [m']
      exact Nat.mul_pos (Nat.pow_pos (by norm_num)) hn
    have hm'_le_epsS : (m' : ℝ) ≤ ε * (S.card : ℝ) := by
      dsimp only [ε]
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (4 * M))]
      have hnat : m' * 2 ^ (4 * M) ≤ S.card := by
        have h1 : m' ≤ 2 ^ M := le_trans hm'_le_M (le_of_lt Nat.lt_two_pow_self)
        have h2 : m' * 2 ^ (4 * M) ≤ 2 ^ (5 * M) := by
          calc m' * 2 ^ (4 * M) ≤ 2 ^ M * 2 ^ (4 * M) := Nat.mul_le_mul_right _ h1
          _ = 2 ^ (5 * M) := by rw [← pow_add]; congr 1; omega
        have h3 : 5 * M ≤ 4 * M ^ 2 := by nlinarith
        exact le_trans h2 (le_trans (Nat.pow_le_pow_right (by norm_num) h3) hS_ge_4M2)
      exact_mod_cast hnat
    have hm'_le_S : m' ≤ S.card := by
      have h1 : (m' : ℝ) ≤ (S.card : ℝ) := by
        have hε_le1 : ε ≤ 1 := by
          dsimp only [ε]
          exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        nlinarith
      exact_mod_cast h1
    -- Apply KST to G on S!
    obtain ⟨U_new, hU_sub, S_new, hS_new_sub, hUS_disj, hU_card, hS_new_card_r, hUS_edges⟩ :=
      kst_dense_graph S G hGsub hm'_pos hm'_le_S hε_pos hm'_le_epsS hG_dense
    -- Convert S_new.card lower bound to ℕ
    have hS_new_card : 2 ^ (8 * M ^ 2 - 4 * M * (M - m')) ≤ S_new.card := by
      have hmul_r : ((2 ^ (4 * M * m') : ℕ) : ℝ) * (S_new.card : ℝ) ≥ (S.card : ℝ) := by
        have hε_pow : ε ^ m' = (((2 : ℝ) ^ (4 * M * m'))⁻¹) := by
          dsimp only [ε]
          rw [inv_pow, ← pow_mul]
        rw [hε_pow, inv_mul_eq_div, div_le_iff₀ (by positivity)] at hS_new_card_r
        push_cast
        linarith
      have hmul_nat : S.card ≤ 2 ^ (4 * M * m') * S_new.card := by
        have : (S.card : ℝ) ≤ ((2 ^ (4 * M * m') * S_new.card : ℕ) : ℝ) := by
          rw [Nat.cast_mul]; linarith
        exact_mod_cast this
      have hexp_add :
          (8 * M ^ 2 - 4 * M * (M - m')) + 4 * M * m' ≤
            8 * M ^ 2 - 4 * M * (M - 4 ^ (r - i) * n) := by
        have h4m'_le_M : 4 * m' ≤ M := by
          rw [← h4m']
          dsimp only [M]
          exact Nat.mul_le_mul_right n (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hdiff : 4 * M * (M - 4 ^ (r - i) * n) + 4 * M * m' ≤ 4 * M * (M - m') := by
          rw [h4m']
          have hsub1 : (M - 4 * m') + m' ≤ M - m' := by omega
          calc
            4 * M * (M - 4 * m') + 4 * M * m' = 4 * M * ((M - 4 * m') + m') := by ring
            _ ≤ 4 * M * (M - m') := Nat.mul_le_mul_left _ hsub1
        have hle8 : 4 * M * (M - m') ≤ 8 * M ^ 2 := by
          have : M - m' ≤ M := Nat.sub_le _ _
          nlinarith
        omega
      have hpow_le : 2 ^ (8 * M ^ 2 - 4 * M * (M - m')) * 2 ^ (4 * M * m') ≤
          2 ^ (4 * M * m') * S_new.card := by
        rw [← pow_add]
        exact le_trans (Nat.pow_le_pow_right (by norm_num) hexp_add) (le_trans hScard hmul_nat)
      rw [mul_comm (2 ^ (4 * M * m'))] at hpow_le
      exact Nat.le_of_mul_le_mul_right hpow_le (Nat.pow_pos (by norm_num))
    -- Assemble new tuple V_next, S_new, χ_next
    let V_next : Fin (i + 1) → Finset (Fin N) := Fin.snoc V'_prev U_new
    let χ_next : Fin (i + 1) → Fin (i + 1) → Bool := fun a b =>
      Fin.lastCases false (fun a' => Fin.lastCases (χ_new a') (fun b' => χ_prev a' b') b) a
    refine ⟨V_next, S_new, χ_next, ?_, ?_, ?_, hS_new_card, ?_⟩
    · intro a
      refine Fin.lastCases ?_ ?_ a
      · simpa [V_next, m'] using hU_card
      · intro a'
        simpa [V_next, m'] using (hV'_prop a').2
    · intro a b
      refine Fin.lastCases ?_ ?_ a
      · refine Fin.lastCases (fun h => absurd rfl h) ?_ b
        intro b' _
        have h1 : V'_prev b' ⊆ V b' := (hV'_prop b').1
        change Disjoint (Fin.snoc (α := fun _ => Finset (Fin N)) V'_prev U_new (Fin.last i))
          (Fin.snoc (α := fun _ => Finset (Fin N)) V'_prev U_new b'.castSucc)
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact Finset.disjoint_of_subset_right h1
          (Finset.disjoint_of_subset_left hU_sub (hVSdisj b').symm)
      · intro a'
        refine Fin.lastCases ?_ ?_ b
        · intro _
          have h1 : V'_prev a' ⊆ V a' := (hV'_prop a').1
          change Disjoint (Fin.snoc (α := fun _ => Finset (Fin N)) V'_prev U_new a'.castSucc)
            (Fin.snoc (α := fun _ => Finset (Fin N)) V'_prev U_new (Fin.last i))
          rw [Fin.snoc_castSucc, Fin.snoc_last]
          exact Finset.disjoint_of_subset_left h1
            (Finset.disjoint_of_subset_right hU_sub (hVSdisj a'))
        · intro b' hab'
          have hne : a' ≠ b' := fun h => hab' (by subst h; rfl)
          change Disjoint (Fin.snoc (α := fun _ => Finset (Fin N)) V'_prev U_new a'.castSucc)
            (Fin.snoc (α := fun _ => Finset (Fin N)) V'_prev U_new b'.castSucc)
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact Finset.disjoint_of_subset_left (hV'_prop a').1
            (Finset.disjoint_of_subset_right (hV'_prop b').1 (hVdisj a' b' hne))
    · intro a
      refine Fin.lastCases ?_ ?_ a
      · change Disjoint (Fin.snoc (α := fun _ => Finset (Fin N)) V'_prev U_new (Fin.last i)) S_new
        rw [Fin.snoc_last]
        exact hUS_disj
      · intro a'
        change Disjoint (Fin.snoc (α := fun _ => Finset (Fin N)) V'_prev U_new a'.castSucc) S_new
        rw [Fin.snoc_castSucc]
        exact Finset.disjoint_of_subset_left (hV'_prop a').1
          (Finset.disjoint_of_subset_right hS_new_sub (hVSdisj a'))
    · intro a b hab x hx y hy
      -- a < b in Fin (i + 1), so a = a'.castSucc
      have ha_ne : a ≠ Fin.last i := by
        intro h; subst h; exact not_lt_of_ge (Fin.le_last b) hab
      obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.mpr ha_ne
      have hx' : x ∈ V'_prev a' := by simpa [V_next] using hx
      have hxV : x ∈ V a' := (hV'_prop a').1 hx'
      refine Fin.lastCases ?_ ?_ b hab hy
      · -- Case b = Fin.last i: no d > b, and for z ∈ S_new, {y, z} ∈ G so c {x, y, z} = χ_new a'
        intro _ hy_last
        have hyU : y ∈ U_new := by simpa [V_next] using hy_last
        refine ⟨fun d hd => absurd hd (not_lt_of_ge (Fin.le_last d)), fun z hz => ?_⟩
        have hyzG : ({y, z} : Finset (Fin N)) ∈ G := hUS_edges y hyU z hz
        have hcol := hGcolor a' x hx' {y, z} hyzG
        simpa [χ_next] using hcol
      · -- Case b = b'.castSucc with a' < b'
        intro b' hab' hy_prev
        have ha'b' : a' < b' := Fin.castSucc_lt_castSucc_iff.mp hab'
        have hy' : y ∈ V'_prev b' := by simpa [V_next] using hy_prev
        have hyV : y ∈ V b' := (hV'_prop b').1 hy'
        have hcol_prev := hcolor a' b' ha'b' x hxV y hyV
        refine ⟨?_, ?_⟩
        · intro d hbd z hz
          refine Fin.lastCases ?_ ?_ d hbd hz
          · intro _ hz_last
            have hzU : z ∈ U_new := by simpa [V_next] using hz_last
            simpa [χ_next] using hcol_prev.2 z (hU_sub hzU)
          · intro d' hbd' hz_prev
            have hb'd' : b' < d' := Fin.castSucc_lt_castSucc_iff.mp hbd'
            have hz' : z ∈ V'_prev d' := by simpa [V_next] using hz_prev
            simpa [χ_next] using hcol_prev.1 d' hb'd' z ((hV'_prop d').1 hz')
        · intro z hz
          simpa [χ_next] using hcol_prev.2 z (hS_new_sub hz)

/-- **CFS11 Theorem 2 (Multipartite 3-Uniform Hypergraph Ramsey Bound):**
For every `d ≥ 3`, `n ≥ 1`, and `N ≥ 2 ^ (8 * (4 ^ (4 ^ (d - 1)) * n) ^ 2)`, every 2-coloring of
3-subsets of `Fin N` contains a monochromatic complete `d`-partite 3-uniform hypergraph
`K_d^{(3)}(n)`. -/
private lemma cfs11_multipartite_ramsey {d n N : ℕ} (hd : 3 ≤ d) (hn : 1 ≤ n)
    (c : Finset (Fin N) → Bool)
    (hN : 2 ^ (8 * (4 ^ (4 ^ (d - 1)) * n) ^ 2) ≤ N) :
    ∃ (b₀ : Bool) (W : Fin d → Finset (Fin N)),
      (∀ i : Fin d, (W i).card = n) ∧
      (∀ i j : Fin d, i ≠ j → Disjoint (W i) (W j)) ∧
      (∀ i j k : Fin d, i < j → j < k →
        ∀ x ∈ W i, ∀ y ∈ W j, ∀ z ∈ W k, c {x, y, z} = b₀) := by
  let r : ℕ := 4 ^ (d - 1)
  have hr : 1 ≤ r := Nat.one_le_pow _ _ (by norm_num)
  obtain ⟨V, S, χ, hVcard, hVdisj, hVSdisj, hScard, hcolor⟩ :=
    cfs11_build_parts hr hn c hN r (le_refl r)
  -- Pick V_last ⊆ S of size n
  have hn_le_S : n ≤ S.card := by
    let M : ℕ := 4 ^ r * n
    have h1 : 4 * M ^ 2 ≤ 8 * M ^ 2 - 4 * M * (M - 4 ^ (r - r) * n) := by
      have hsub_le : M - 4 ^ (r - r) * n ≤ M := Nat.sub_le _ _
      have hmul_le : 4 * M * (M - 4 ^ (r - r) * n) ≤ 4 * M ^ 2 := by nlinarith
      omega
    have h2 : n ≤ M := Nat.le_mul_of_pos_left n (Nat.pow_pos (by norm_num))
    have h3 : n ≤ 2 ^ (4 * M ^ 2) :=
      le_trans h2 (le_trans (le_of_lt Nat.lt_two_pow_self)
        (Nat.pow_le_pow_right (by norm_num) (by nlinarith)))
    exact le_trans h3 (le_trans (Nat.pow_le_pow_right (by norm_num) h1) hScard)
  obtain ⟨V_last, hV_last_sub, hV_last_card⟩ := Finset.exists_subset_card_eq hn_le_S
  -- Define symmetric 2-coloring on pairs of Fin r using χ
  let c2 : Finset (Fin r) → Bool := fun e =>
    if h : e.card = 2 then
      let a := e.min' (Finset.card_pos.mp (by omega))
      let b := e.max' (Finset.card_pos.mp (by omega))
      χ a b
    else false
  have h4_le_r : 4 ^ (d - 1) ≤ (Finset.univ : Finset (Fin r)).card := by
    simp [r]
  obtain ⟨b₀, I, _, hIcard, hIc2⟩ := erdos_szekeres_diag c2 h4_le_r
  -- Enumerate I in strictly increasing order via Finset.orderEmbOfFin
  let emb : Fin (d - 1) ↪o Fin r := I.orderEmbOfFin hIcard
  -- Build W : Fin d → Finset (Fin N) by appending V_last to V ∘ emb
  let W : Fin d → Finset (Fin N) := fun i =>
    if h : i.1 < d - 1 then V (emb ⟨i.1, h⟩) else V_last
  refine ⟨b₀, W, ?_, ?_, ?_⟩
  · intro i
    dsimp only [W]
    split_ifs with h
    · simpa using hVcard (emb ⟨i.1, h⟩)
    · exact hV_last_card
  · intro i j hij
    dsimp only [W]
    split_ifs with hi hj
    · apply hVdisj
      intro hEq
      have hfin := emb.injective hEq
      exact hij (Fin.ext (by simpa using congrArg Fin.val hfin))
    · exact Finset.disjoint_of_subset_right hV_last_sub (hVSdisj _)
    · exact (Finset.disjoint_of_subset_right hV_last_sub (hVSdisj _)).symm
    · exfalso; exact hij (Fin.ext (by omega))
  · intro i j k hij hjk x hx y hy z hz
    have hi : i.1 < d - 1 := by omega
    have hj : j.1 < d - 1 := by omega
    have hx' : x ∈ V (emb ⟨i.1, hi⟩) := by simpa [W, hi] using hx
    have hy' : y ∈ V (emb ⟨j.1, hj⟩) := by simpa [W, hj] using hy
    have hlt_ij : emb ⟨i.1, hi⟩ < emb ⟨j.1, hj⟩ :=
      emb.strictMono (by exact Fin.mk_lt_mk.mpr hij)
    -- Compute χ (emb i) (emb j) = b₀ from hIc2 on {emb i, emb j}
    have hpair_mem : ({emb ⟨i.1, hi⟩, emb ⟨j.1, hj⟩} : Finset (Fin r)) ∈ I.powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair (ne_of_lt hlt_ij)⟩
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu2
      · exact Finset.orderEmbOfFin_mem I hIcard ⟨i.1, hi⟩
      · rw [Finset.mem_singleton.mp hu2]
        exact Finset.orderEmbOfFin_mem I hIcard ⟨j.1, hj⟩
    have hchi_eq : χ (emb ⟨i.1, hi⟩) (emb ⟨j.1, hj⟩) = b₀ := by
      have h := hIc2 _ hpair_mem
      dsimp only [c2] at h
      have hcard2 : ({emb ⟨i.1, hi⟩, emb ⟨j.1, hj⟩} : Finset (Fin r)).card = 2 :=
        Finset.card_pair (ne_of_lt hlt_ij)
      rw [dif_pos hcard2] at h
      have hmin : ({emb ⟨i.1, hi⟩, emb ⟨j.1, hj⟩} : Finset (Fin r)).min'
          (by simp) = emb ⟨i.1, hi⟩ := by
        apply le_antisymm
        · exact Finset.min'_le _ _ (by simp)
        · exact Finset.le_min' _ _ _ (by
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hu2
            · exact le_rfl
            · rw [Finset.mem_singleton.mp hu2]; exact le_of_lt hlt_ij)
      have hmax : ({emb ⟨i.1, hi⟩, emb ⟨j.1, hj⟩} : Finset (Fin r)).max'
          (by simp) = emb ⟨j.1, hj⟩ := by
        apply le_antisymm
        · exact Finset.max'_le _ _ _ (by
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hu2
            · exact le_of_lt hlt_ij
            · rw [Finset.mem_singleton.mp hu2])
        · exact Finset.le_max' _ _ (by simp)
      rwa [hmin, hmax] at h
    have hcol := hcolor (emb ⟨i.1, hi⟩) (emb ⟨j.1, hj⟩) hlt_ij x hx' y hy'
    rw [hchi_eq] at hcol
    by_cases hk : k.1 < d - 1
    · have hz' : z ∈ V (emb ⟨k.1, hk⟩) := by simpa [W, hk] using hz
      have hlt_jk : emb ⟨j.1, hj⟩ < emb ⟨k.1, hk⟩ :=
        emb.strictMono (by exact Fin.mk_lt_mk.mpr hjk)
      exact hcol.1 (emb ⟨k.1, hk⟩) hlt_jk z hz'
    · have hz' : z ∈ V_last := by simpa [W, hk] using hz
      exact hcol.2 z (hV_last_sub hz')

/-- Crossing triples in a `d`-partite family `W : Fin d → Finset (Fin N)` of size `n` have
cardinality `d.choose 3 * n ^ 3` and satisfy `(1 - 3 / d) * (d * n).choose 3 < d.choose 3 * n ^ 3`. -/
private lemma cfs11_almost_mono_of_multipartite {N d n : ℕ} (hd : 4 ≤ d) (hn : 1 ≤ n)
    (c : Finset (Fin N) → Bool) (b₀ : Bool) (W : Fin d → Finset (Fin N))
    (hWcard : ∀ i : Fin d, (W i).card = n)
    (hWdisj : ∀ i j : Fin d, i ≠ j → Disjoint (W i) (W j))
    (hWcol : ∀ i j k : Fin d, i < j → j < k →
      ∀ x ∈ W i, ∀ y ∈ W j, ∀ z ∈ W k, c {x, y, z} = b₀) :
    let X : Finset (Fin N) := Finset.univ.biUnion W
    X.card = d * n ∧
    (((X.powersetCard 3).filter (fun e => c e = !b₀)).card : ℝ) <
      (3 / (d : ℝ)) * ((X.card.choose 3 : ℕ) : ℝ) := by
  intro X
  have hXcard : X.card = d * n := by
    dsimp only [X]
    rw [Finset.card_biUnion (fun i _ j _ hij => hWdisj i j hij)]
    simp [hWcard]
  refine ⟨hXcard, ?_⟩
  -- Build injection from triples (i < j < k) × (x ∈ W i, y ∈ W j, z ∈ W k) into b₀-colored edges
  let T : Finset (Fin d × Fin d × Fin d) :=
    (Finset.univ ×ˢ (Finset.univ ×ˢ Finset.univ)).filter (fun p => p.1 < p.2.1 ∧ p.2.1 < p.2.2)
  let crossTriples : Finset (Finset (Fin N)) :=
    T.biUnion fun p =>
      (W p.1 ×ˢ (W p.2.1 ×ˢ W p.2.2)).image fun q => ({q.1, q.2.1, q.2.2} : Finset (Fin N))
  have hcross_sub : crossTriples ⊆ (X.powersetCard 3).filter (fun e => c e = b₀) := by
    intro e he
    rcases Finset.mem_biUnion.mp he with ⟨⟨i, j, k⟩, hp, hqmem⟩
    rcases Finset.mem_filter.mp hp with ⟨_, hij, hjk⟩
    rcases Finset.mem_image.mp hqmem with ⟨⟨x, y, z⟩, hxyz, rfl⟩
    rcases Finset.mem_product.mp hxyz with ⟨hx, hyz⟩
    rcases Finset.mem_product.mp hyz with ⟨hy, hz⟩
    have hxy : x ≠ y := fun h => Finset.disjoint_left.mp (hWdisj i j (ne_of_lt hij)) hx (h ▸ hy)
    have hxz : x ≠ z := fun h =>
      Finset.disjoint_left.mp (hWdisj i k (ne_of_lt (lt_trans hij hjk))) hx (h ▸ hz)
    have hyz_ne : y ≠ z := fun h => Finset.disjoint_left.mp (hWdisj j k (ne_of_lt hjk)) hy (h ▸ hz)
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, hWcol i j k hij hjk x hx y hy z hz⟩
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
      · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hy⟩
      · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hz⟩
    · rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
        Finset.card_insert_of_notMem (by simp [hyz_ne]), Finset.card_singleton]
  have hcross_card : crossTriples.card = d.choose 3 * n ^ 3 := by
    have hTcard : T.card = d.choose 3 := by
      have hcard_d : ((Finset.univ : Finset (Fin d)).powersetCard 3).card = d.choose 3 := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      rw [← hcard_d]
      refine Finset.card_bij (fun p _ => ({p.1, p.2.1, p.2.2} : Finset (Fin d))) ?_ ?_ ?_
      · intro ⟨i, j, k⟩ hp
        rcases Finset.mem_filter.mp hp with ⟨_, hij, hjk⟩
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.subset_univ _, ?_⟩
        rw [Finset.card_insert_of_notMem (by simp [ne_of_lt hij, ne_of_lt (lt_trans hij hjk)]),
          Finset.card_insert_of_notMem (by simp [ne_of_lt hjk]), Finset.card_singleton]
      · intro ⟨i₁, j₁, k₁⟩ hp₁ ⟨i₂, j₂, k₂⟩ hp₂ hEq
        rcases Finset.mem_filter.mp hp₁ with ⟨_, hij₁, hjk₁⟩
        rcases Finset.mem_filter.mp hp₂ with ⟨_, hij₂, hjk₂⟩
        -- Sorted triple is uniquely recovered from its 3-element Finset
        have hi : i₁ = i₂ := by
          have hm₁ : ({i₁, j₁, k₁} : Finset (Fin d)).min' (by simp) = i₁ := by
            apply le_antisymm (Finset.min'_le _ _ (by simp))
            refine Finset.le_min' _ _ _ fun u hu => ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl | rfl
            · exact le_rfl
            · exact le_of_lt hij₁
            · exact le_of_lt (lt_trans hij₁ hjk₁)
          have hm₂ : ({i₂, j₂, k₂} : Finset (Fin d)).min' (by simp) = i₂ := by
            apply le_antisymm (Finset.min'_le _ _ (by simp))
            refine Finset.le_min' _ _ _ fun u hu => ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl | rfl
            · exact le_rfl
            · exact le_of_lt hij₂
            · exact le_of_lt (lt_trans hij₂ hjk₂)
          rw [← hm₁, ← hm₂]; congr 1
        have hk : k₁ = k₂ := by
          have hm₁ : ({i₁, j₁, k₁} : Finset (Fin d)).max' (by simp) = k₁ := by
            apply le_antisymm _ (Finset.le_max' _ _ (by simp))
            refine Finset.max'_le _ _ _ fun u hu => ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl | rfl
            · exact le_of_lt (lt_trans hij₁ hjk₁)
            · exact le_of_lt hjk₁
            · exact le_rfl
          have hm₂ : ({i₂, j₂, k₂} : Finset (Fin d)).max' (by simp) = k₂ := by
            apply le_antisymm _ (Finset.le_max' _ _ (by simp))
            refine Finset.max'_le _ _ _ fun u hu => ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl | rfl
            · exact le_of_lt (lt_trans hij₂ hjk₂)
            · exact le_of_lt hjk₂
            · exact le_rfl
          rw [← hm₁, ← hm₂]; congr 1
        subst hi; subst hk
        have hj_mem : j₁ ∈ ({i₁, j₂, k₁} : Finset (Fin d)) := by rw [← hEq]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj_mem
        rcases hj_mem with h1 | rfl | h3
        · exact absurd h1 (ne_of_gt hij₁)
        · rfl
        · exact absurd h3 (ne_of_lt hjk₁)
      · intro s hs
        have hscard : s.card = 3 := (Finset.mem_powersetCard.mp hs).2
        let emb := s.orderEmbOfFin hscard
        refine ⟨(emb 0, emb 1, emb 2), ?_, ?_⟩
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, emb.strictMono (by decide), emb.strictMono (by decide)⟩
        · ext u
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (rfl | rfl | rfl) <;> exact Finset.orderEmbOfFin_mem s hscard _
          · intro hu
            obtain ⟨idx, hidx⟩ : ∃ idx : Fin 3, emb idx = u := by
              have hrange : Set.range emb = (s : Set (Fin d)) := Finset.range_orderEmbOfFin s hscard
              have : u ∈ Set.range emb := by rw [hrange]; exact hu
              exact this
            fin_cases idx <;> simp [← hidx]
    -- Each fiber over p ∈ T is disjoint and has size n^3
    have hbiUnion_disj : Set.PairwiseDisjoint (T : Set (Fin d × Fin d × Fin d))
        (fun p => (W p.1 ×ˢ (W p.2.1 ×ˢ W p.2.2)).image
          fun q => ({q.1, q.2.1, q.2.2} : Finset (Fin N))) := by
      intro ⟨i₁, j₁, k₁⟩ hp₁ ⟨i₂, j₂, k₂⟩ hp₂ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e he₁ he₂
      rcases Finset.mem_image.mp he₁ with ⟨⟨x₁, y₁, z₁⟩, hxyz₁, rfl⟩
      rcases Finset.mem_image.mp he₂ with ⟨⟨x₂, y₂, z₂⟩, hxyz₂, hEq⟩
      rcases Finset.mem_product.mp hxyz₁ with ⟨hx₁, hyz₁⟩
      rcases Finset.mem_product.mp hyz₁ with ⟨hy₁, hz₁⟩
      rcases Finset.mem_product.mp hxyz₂ with ⟨hx₂, hyz₂⟩
      rcases Finset.mem_product.mp hyz₂ with ⟨hy₂, hz₂⟩
      rcases Finset.mem_filter.mp hp₁ with ⟨_, hij₁, hjk₁⟩
      rcases Finset.mem_filter.mp hp₂ with ⟨_, hij₂, hjk₂⟩
      -- The set of part indices hit by {x₁, y₁, z₁} is {i₁, j₁, k₁} and equals {i₂, j₂, k₂}
      have hset_eq : ({i₁, j₁, k₁} : Finset (Fin d)) = {i₂, j₂, k₂} := by
        have hpart : ∀ u : Fin N, ∀ a b : Fin d, u ∈ W a → u ∈ W b → a = b := by
          intro u a b ha hb
          by_contra hab
          exact Finset.disjoint_left.mp (hWdisj a b hab) ha hb
        ext r
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl | rfl)
          · have hmem : x₁ ∈ ({x₂, y₂, z₂} : Finset (Fin N)) := by rw [hEq]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with rfl | rfl | rfl
            · exact Or.inl (hpart _ _ _ hx₁ hx₂)
            · exact Or.inr (Or.inl (hpart _ _ _ hx₁ hy₂))
            · exact Or.inr (Or.inr (hpart _ _ _ hx₁ hz₂))
          · have hmem : y₁ ∈ ({x₂, y₂, z₂} : Finset (Fin N)) := by rw [hEq]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with rfl | rfl | rfl
            · exact Or.inl (hpart _ _ _ hy₁ hx₂)
            · exact Or.inr (Or.inl (hpart _ _ _ hy₁ hy₂))
            · exact Or.inr (Or.inr (hpart _ _ _ hy₁ hz₂))
          · have hmem : z₁ ∈ ({x₂, y₂, z₂} : Finset (Fin N)) := by rw [hEq]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with rfl | rfl | rfl
            · exact Or.inl (hpart _ _ _ hz₁ hx₂)
            · exact Or.inr (Or.inl (hpart _ _ _ hz₁ hy₂))
            · exact Or.inr (Or.inr (hpart _ _ _ hz₁ hz₂))
        · rintro (rfl | rfl | rfl)
          · have hmem : x₂ ∈ ({x₁, y₁, z₁} : Finset (Fin N)) := by rw [← hEq]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with rfl | rfl | rfl
            · exact Or.inl (hpart _ _ _ hx₂ hx₁)
            · exact Or.inr (Or.inl (hpart _ _ _ hx₂ hy₁))
            · exact Or.inr (Or.inr (hpart _ _ _ hx₂ hz₁))
          · have hmem : y₂ ∈ ({x₁, y₁, z₁} : Finset (Fin N)) := by rw [← hEq]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with rfl | rfl | rfl
            · exact Or.inl (hpart _ _ _ hy₂ hx₁)
            · exact Or.inr (Or.inl (hpart _ _ _ hy₂ hy₁))
            · exact Or.inr (Or.inr (hpart _ _ _ hy₂ hz₁))
          · have hmem : z₂ ∈ ({x₁, y₁, z₁} : Finset (Fin N)) := by rw [← hEq]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with rfl | rfl | rfl
            · exact Or.inl (hpart _ _ _ hz₂ hx₁)
            · exact Or.inr (Or.inl (hpart _ _ _ hz₂ hy₁))
            · exact Or.inr (Or.inr (hpart _ _ _ hz₂ hz₁))
      -- Same sorted-triple uniqueness gives (i₁, j₁, k₁) = (i₂, j₂, k₂)
      have hi : i₁ = i₂ := by
        have hm₁ : ({i₁, j₁, k₁} : Finset (Fin d)).min' (by simp) = i₁ := by
          apply le_antisymm (Finset.min'_le _ _ (by simp))
          refine Finset.le_min' _ _ _ fun u hu => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact le_rfl
          · exact le_of_lt hij₁
          · exact le_of_lt (lt_trans hij₁ hjk₁)
        have hm₂ : ({i₂, j₂, k₂} : Finset (Fin d)).min' (by simp) = i₂ := by
          apply le_antisymm (Finset.min'_le _ _ (by simp))
          refine Finset.le_min' _ _ _ fun u hu => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact le_rfl
          · exact le_of_lt hij₂
          · exact le_of_lt (lt_trans hij₂ hjk₂)
        rw [← hm₁, ← hm₂]; congr 1
      have hk : k₁ = k₂ := by
        have hm₁ : ({i₁, j₁, k₁} : Finset (Fin d)).max' (by simp) = k₁ := by
          apply le_antisymm _ (Finset.le_max' _ _ (by simp))
          refine Finset.max'_le _ _ _ fun u hu => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact le_of_lt (lt_trans hij₁ hjk₁)
          · exact le_of_lt hjk₁
          · exact le_rfl
        have hm₂ : ({i₂, j₂, k₂} : Finset (Fin d)).max' (by simp) = k₂ := by
          apply le_antisymm _ (Finset.le_max' _ _ (by simp))
          refine Finset.max'_le _ _ _ fun u hu => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact le_of_lt (lt_trans hij₂ hjk₂)
          · exact le_of_lt hjk₂
          · exact le_rfl
        rw [← hm₁, ← hm₂]; congr 1
      subst hi; subst hk
      have hj_mem : j₁ ∈ ({i₁, j₂, k₁} : Finset (Fin d)) := by rw [← hset_eq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj_mem
      rcases hj_mem with h1 | rfl | h3
      · exact absurd h1 (ne_of_gt hij₁)
      · exact hne rfl
      · exact absurd h3 (ne_of_lt hjk₁)
    rw [Finset.card_biUnion hbiUnion_disj]
    have hfiber_card : ∀ p ∈ T,
        ((W p.1 ×ˢ (W p.2.1 ×ˢ W p.2.2)).image
          fun q => ({q.1, q.2.1, q.2.2} : Finset (Fin N))).card = n ^ 3 := by
      intro ⟨i, j, k⟩ hp
      rcases Finset.mem_filter.mp hp with ⟨_, hij, hjk⟩
      rw [Finset.card_image_of_injOn]
      · simp [hWcard, pow_succ]; ring
      · intro ⟨x₁, y₁, z₁⟩ h1 ⟨x₂, y₂, z₂⟩ h2 hEq
        dsimp only at hEq
        rcases Finset.mem_product.mp h1 with ⟨hx₁, hyz₁⟩
        rcases Finset.mem_product.mp hyz₁ with ⟨hy₁, hz₁⟩
        rcases Finset.mem_product.mp h2 with ⟨hx₂, hyz₂⟩
        rcases Finset.mem_product.mp hyz₂ with ⟨hy₂, hz₂⟩
        have hx : x₁ = x₂ := by
          have hmem : x₁ ∈ ({x₂, y₂, z₂} : Finset (Fin N)) := by rw [← hEq]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl | rfl
          · rfl
          · exact absurd hy₂ (Finset.disjoint_left.mp (hWdisj i j (ne_of_lt hij)) hx₁)
          · exact absurd hz₂ (Finset.disjoint_left.mp (hWdisj i k (ne_of_lt (lt_trans hij hjk))) hx₁)
        have hy : y₁ = y₂ := by
          have hmem : y₁ ∈ ({x₂, y₂, z₂} : Finset (Fin N)) := by rw [← hEq]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl | rfl
          · exact absurd hx₂ (Finset.disjoint_left.mp (hWdisj j i (ne_of_gt hij)) hy₁)
          · rfl
          · exact absurd hz₂ (Finset.disjoint_left.mp (hWdisj j k (ne_of_lt hjk)) hy₁)
        have hz : z₁ = z₂ := by
          have hmem : z₁ ∈ ({x₂, y₂, z₂} : Finset (Fin N)) := by rw [← hEq]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl | rfl
          · exact absurd hx₂ (Finset.disjoint_left.mp (hWdisj k i (ne_of_gt (lt_trans hij hjk))) hz₁)
          · exact absurd hy₂ (Finset.disjoint_left.mp (hWdisj k j (ne_of_gt hjk)) hz₁)
          · rfl
        simp [hx, hy, hz]
    rw [Finset.sum_congr rfl hfiber_card, Finset.sum_const, smul_eq_mul, hTcard]
  -- Count !b₀ edges = total - b₀ edges ≤ (d*n).choose 3 - d.choose 3 * n^3 < (3 / d) * (d*n).choose 3
  have hpart : ((X.powersetCard 3).filter (fun e => c e = b₀)).card +
      ((X.powersetCard 3).filter (fun e => c e = !b₀)).card = X.card.choose 3 := by
    have hdisj_c : Disjoint ((X.powersetCard 3).filter (fun e => c e = b₀))
        ((X.powersetCard 3).filter (fun e => c e = !b₀)) := by
      rw [Finset.disjoint_left]
      intro e h0 h1
      have hc0 := (Finset.mem_filter.mp h0).2
      have hc1 := (Finset.mem_filter.mp h1).2
      rw [hc0] at hc1
      cases b₀ <;> simp at hc1
    have hunion : (X.powersetCard 3).filter (fun e => c e = b₀) ∪
        (X.powersetCard 3).filter (fun e => c e = !b₀) = X.powersetCard 3 := by
      ext e
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases hc : c e = b₀
        · exact Or.inl ⟨h, hc⟩
        · refine Or.inr ⟨h, ?_⟩
          cases hce : c e <;> cases b₀ <;> simp_all
    rw [← Finset.card_union_of_disjoint hdisj_c, hunion, Finset.card_powersetCard]
  have hb0_ge : d.choose 3 * n ^ 3 ≤ ((X.powersetCard 3).filter (fun e => c e = b₀)).card := by
    rw [← hcross_card]
    exact Finset.card_le_card hcross_sub
  -- Algebraic inequality: (1 - 3/d) * (d*n).choose 3 < d.choose 3 * n^3
  -- Multiply by 6 * d: (d - 3) * (d*n)*(d*n-1)*(d*n-2) < d * d*(d-1)*(d-2) * n^3
  have hchoose3_dn : 6 * (d * n).choose 3 = d * n * (d * n - 1) * (d * n - 2) := by
    have h := (Nat.descFactorial_eq_factorial_mul_choose (d * n) 3).symm
    simp only [Nat.factorial, Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
      mul_one] at h
    calc
      6 * (d * n).choose 3 = Nat.succ 2 * (Nat.succ 1 * Nat.succ 0) * (d * n).choose 3 := rfl
      _ = (d * n - 2) * ((d * n - 1) * (d * n)) := h
      _ = d * n * (d * n - 1) * (d * n - 2) := by ring
  have hchoose3_d : 6 * d.choose 3 = d * (d - 1) * (d - 2) := by
    have h := (Nat.descFactorial_eq_factorial_mul_choose d 3).symm
    simp only [Nat.factorial, Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
      mul_one] at h
    calc
      6 * d.choose 3 = Nat.succ 2 * (Nat.succ 1 * Nat.succ 0) * d.choose 3 := rfl
      _ = (d - 2) * ((d - 1) * d) := h
      _ = d * (d - 1) * (d - 2) := by ring
  have halg_nat : (d - 3) * (d * n).choose 3 < d * (d.choose 3 * n ^ 3) := by
    have h6 : 6 * ((d - 3) * (d * n).choose 3) < 6 * (d * (d.choose 3 * n ^ 3)) := by
      have hL : 6 * ((d - 3) * (d * n).choose 3) = (d - 3) * (d * n * (d * n - 1) * (d * n - 2)) := by
        rw [← hchoose3_dn]; ring
      have hR : 6 * (d * (d.choose 3 * n ^ 3)) = d * (d * (d - 1) * (d - 2) * n ^ 3) := by
        rw [← hchoose3_d]; ring
      rw [hL, hR]
      -- Note (d - 3) * (d * n - 1) * (d * n - 2) < d * (d - 1) * (d - 2) * n ^ 2
      -- Even simpler: (d*n - 1) < d*n and (d*n - 2) < d*n, and (d-3)*d < (d-1)*(d-2) since d^2-3d < d^2-3d+2!
      have h1 : (d - 3) * d < (d - 1) * (d - 2) := by
        have hd3 : 3 ≤ d := by omega
        zify [hd3, (by omega : 1 ≤ d), (by omega : 2 ≤ d)]
        nlinarith
      have h2 : d * n - 1 ≤ d * n := Nat.sub_le _ _
      have h3 : d * n - 2 ≤ d * n := Nat.sub_le _ _
      have hdn_pos : 0 < d * n := Nat.mul_pos (by omega) hn
      have hprod1 : (d * n - 1) * (d * n - 2) ≤ (d * n) * (d * n) :=
        Nat.mul_le_mul h2 h3
      calc
        (d - 3) * (d * n * (d * n - 1) * (d * n - 2))
            = ((d - 3) * d) * (n * ((d * n - 1) * (d * n - 2))) := by ring
        _ < ((d - 1) * (d - 2)) * (n * ((d * n) * (d * n))) := by
            refine lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left n hprod1)) ?_
            exact Nat.mul_lt_mul_of_pos_right h1 (by positivity)
        _ = d * (d * (d - 1) * (d - 2) * n ^ 3) := by ring
    omega
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have halg_r : ((d : ℝ) - 3) * ((X.card.choose 3 : ℕ) : ℝ) <
      (d : ℝ) * ((d.choose 3 * n ^ 3 : ℕ) : ℝ) := by
    rw [hXcard]
    have : (((d - 3) * (d * n).choose 3 : ℕ) : ℝ) < ((d * (d.choose 3 * n ^ 3) : ℕ) : ℝ) := by
      exact_mod_cast halg_nat
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 3 ≤ d), Nat.cast_mul] at this
    simpa using this
  have hnotb0_le : (((X.powersetCard 3).filter (fun e => c e = !b₀)).card : ℝ) ≤
      ((X.card.choose 3 : ℕ) : ℝ) - ((d.choose 3 * n ^ 3 : ℕ) : ℝ) := by
    have hnat : ((X.powersetCard 3).filter (fun e => c e = !b₀)).card + d.choose 3 * n ^ 3 ≤
        X.card.choose 3 := by omega
    have hr : (((X.powersetCard 3).filter (fun e => c e = !b₀)).card : ℝ) +
        ((d.choose 3 * n ^ 3 : ℕ) : ℝ) ≤ ((X.card.choose 3 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hmul_lt : (d : ℝ) * (((X.powersetCard 3).filter (fun e => c e = !b₀)).card : ℝ) <
      3 * ((X.card.choose 3 : ℕ) : ℝ) := by
    nlinarith
  rw [div_mul_eq_mul_div, lt_div_iff₀ hd_pos]
  linarith

/-- **Conlon–Fox–Sudakov [CFS11] Complete `t = 3` Asymptotic Equivalence:**
For every `α ∈ (0, 1/2)`, `F^{(3)}(n, α) =Θ[atTop] √(log n)`. -/
theorem ppl063_t3_isTheta_sqrt_log {α : ℝ} (hα_pos : 0 < α) (hα_lt : α < 1 / 2) :
    (fun n : ℕ => ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard 3).filter (fun e => c e = b)).card ∧
        α * (X.card.choose 3 : ℝ) ≤
          (((X.powersetCard 3).filter (fun e => c e = b)).card : ℝ)} : ℕ) : ℝ))
      =Θ[atTop] (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) := by
  constructor
  · have hbigO := threshold_isBigO_log_rpow (t := 3) (by omega) (le_of_lt hα_pos) hα_lt
    have heq : (fun n : ℕ => (Real.log (n : ℝ)) ^ ((1 : ℝ) / (((3 : ℕ) : ℝ) - 1))) =
        (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) := by
      funext n
      rw [Real.sqrt_eq_rpow]
      congr 1
      norm_num
    rw [heq] at hbigO
    exact hbigO
  · -- Lower bound: √(log N) = O(F(N, 3, α))
    let d : ℕ := max 4 (Nat.ceil (3 / α))
    have hd4 : 4 ≤ d := le_max_left 4 _
    have h3d_le_α : 3 / (d : ℝ) ≤ α := by
      have hd_ge : 3 / α ≤ (d : ℝ) := le_trans (Nat.le_ceil (3 / α)) (by exact_mod_cast le_max_right 4 _)
      have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      rw [div_le_iff₀ hd_pos]
      rw [div_le_iff₀ hα_pos] at hd_ge
      linarith
    let K : ℕ := 8 * (4 ^ (4 ^ (d - 1))) ^ 2
    have hK_pos : 0 < K := by positivity
    rw [Asymptotics.isBigO_iff]
    refine ⟨Real.sqrt ((K : ℝ) * Real.log 2) * 2, ?_⟩
    rw [Filter.eventually_atTop]
    refine ⟨2 ^ K, fun N hN => ?_⟩
    have hN_pos : 0 < N := lt_of_lt_of_le (Nat.pow_pos (by norm_num)) hN
    let q : ℕ := Nat.log 2 N / K
    let m : ℕ := Nat.sqrt q
    have hq_pos : 1 ≤ q := by
      have hlog_ge : K ≤ Nat.log 2 N := by
        rw [Nat.le_log_iff_pow_le (by norm_num) (ne_of_gt hN_pos)]
        exact hN
      exact Nat.div_pos hlog_ge hK_pos
    have hm_pos : 1 ≤ m := by
      dsimp only [m]
      rw [Nat.le_sqrt]
      omega
    have hpow_le_N : 2 ^ (8 * (4 ^ (4 ^ (d - 1)) * m) ^ 2) ≤ N := by
      have hexp : 8 * (4 ^ (4 ^ (d - 1)) * m) ^ 2 = K * m ^ 2 := by dsimp only [K]; ring
      rw [hexp]
      have hm2 : m ^ 2 ≤ q := by rw [sq]; exact Nat.sqrt_le q
      have hKm2 : K * m ^ 2 ≤ Nat.log 2 N :=
        le_trans (Nat.mul_le_mul_left K hm2) (Nat.mul_div_le (Nat.log 2 N) K)
      exact le_trans (Nat.pow_le_pow_right (by norm_num) hKm2)
        (Nat.pow_log_le_self 2 (ne_of_gt hN_pos))
    -- Apply CFS11 to show d * m < F N 3 α
    have hdm_lt_F : d * m < F N 3 α := by
      apply lt_F_of_every_coloring_has_bad
      intro c
      obtain ⟨b₀, W, hWcard, hWdisj, hWcol⟩ :=
        cfs11_multipartite_ramsey (by omega : 3 ≤ d) hm_pos c hpow_le_N
      obtain ⟨hXcard, hXlt⟩ := cfs11_almost_mono_of_multipartite hd4 hm_pos c b₀ W hWcard hWdisj hWcol
      refine ⟨Finset.univ.biUnion W, le_of_eq hXcard.symm, !b₀, Or.inr ?_⟩
      refine lt_of_lt_of_le hXlt ?_
      exact mul_le_mul_of_nonneg_right h3d_le_α (Nat.cast_nonneg _)
    -- Relate log N to (2 * m)^2 and hence √(log N) ≤ C * F N 3 α
    have hsqrt_le : Real.sqrt (Real.log (N : ℝ)) ≤
        Real.sqrt ((K : ℝ) * Real.log 2) * (2 * (m : ℝ)) := by
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hK_rpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
      have hlogN_clean : Real.log (N : ℝ) ≤ (K : ℝ) * Real.log 2 * (2 * (m : ℝ)) ^ 2 := by
        have hN_lt : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
        have hlog_step : Nat.log 2 N + 1 ≤ K * (m + 1) ^ 2 := by
          have hq_lt : q < (m + 1) * (m + 1) := Nat.lt_succ_sqrt q
          have hdiv : Nat.log 2 N < K * (q + 1) := Nat.lt_mul_div_succ (Nat.log 2 N) hK_pos
          have hq1 : q + 1 ≤ (m + 1) ^ 2 := by rw [sq]; omega
          have := lt_of_lt_of_le hdiv (Nat.mul_le_mul_left K hq1)
          omega
        have hN_lt2 : N < 2 ^ (K * (m + 1) ^ 2) :=
          lt_of_lt_of_le hN_lt (Nat.pow_le_pow_right (by norm_num) hlog_step)
        have hNr : (N : ℝ) < (2 : ℝ) ^ (K * (m + 1) ^ 2) := by exact_mod_cast hN_lt2
        have h1 := Real.log_le_log (by exact_mod_cast hN_pos) (le_of_lt hNr)
        rw [Real.log_pow] at h1
        have hm1_sq : ((m + 1 : ℕ) : ℝ) ^ 2 ≤ (2 * (m : ℝ)) ^ 2 := by
          push_cast; nlinarith
        have h2 : ((K * (m + 1) ^ 2 : ℕ) : ℝ) * Real.log 2 ≤
            (K : ℝ) * Real.log 2 * (2 * (m : ℝ)) ^ 2 := by
          rw [Nat.cast_mul, Nat.cast_pow]
          have h3 : (K : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 ≤ (K : ℝ) * (2 * (m : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_left hm1_sq (le_of_lt hK_rpos)
          have h4 := mul_le_mul_of_nonneg_right h3 (le_of_lt hlog2_pos)
          linarith
        exact le_trans h1 h2
      calc
        Real.sqrt (Real.log (N : ℝ)) ≤ Real.sqrt ((K : ℝ) * Real.log 2 * (2 * (m : ℝ)) ^ 2) :=
          Real.sqrt_le_sqrt hlogN_clean
        _ = Real.sqrt ((K : ℝ) * Real.log 2) * Real.sqrt ((2 * (m : ℝ)) ^ 2) :=
          Real.sqrt_mul (by positivity) _
        _ = Real.sqrt ((K : ℝ) * Real.log 2) * (2 * (m : ℝ)) := by
          rw [Real.sqrt_sq (by positivity)]
    have hm_le_F : (m : ℝ) ≤ (F N 3 α : ℝ) := by
      have : m ≤ F N 3 α := le_trans (Nat.le_mul_of_pos_left m (by omega : 0 < d)) (le_of_lt hdm_lt_F)
      exact_mod_cast this
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    calc
      Real.sqrt (Real.log (N : ℝ)) ≤ Real.sqrt ((K : ℝ) * Real.log 2) * (2 * (m : ℝ)) := hsqrt_le
      _ ≤ Real.sqrt ((K : ℝ) * Real.log 2) * (2 * (F N 3 α : ℝ)) := by
          gcongr
      _ = Real.sqrt ((K : ℝ) * Real.log 2) * 2 * (F N 3 α : ℝ) := by ring

/-- **Conlon–Fox–Sudakov [CFS11] Complete `t = 3` Positive-Density Collapse
(Settling the `t = 3` Slice of `erdos_161.parts.ii`):**
For all `α, β ∈ (0, 1/2)`, `F^{(3)}(n, α) =Θ[atTop] F^{(3)}(n, β)`. -/
theorem ppl063_t3_positive_density_collapse {α β : ℝ}
    (hα_pos : 0 < α) (hα_lt : α < 1 / 2) (hβ_pos : 0 < β) (hβ_lt : β < 1 / 2) :
    (fun n : ℕ => ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard 3).filter (fun e => c e = b)).card ∧
        α * (X.card.choose 3 : ℝ) ≤
          (((X.powersetCard 3).filter (fun e => c e = b)).card : ℝ)} : ℕ) : ℝ))
      =Θ[atTop]
    (fun n : ℕ => ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard 3).filter (fun e => c e = b)).card ∧
        β * (X.card.choose 3 : ℝ) ≤
          (((X.powersetCard 3).filter (fun e => c e = b)).card : ℝ)} : ℕ) : ℝ)) :=
  (ppl063_t3_isTheta_sqrt_log hα_pos hα_lt).trans (ppl063_t3_isTheta_sqrt_log hβ_pos hβ_lt).symm

/-! ### Section 6: General `t ≥ 2` (and `t ≥ 4`) High-Density Collapse on `(α_IE(t), 1/2)` -/

/-- **Erdős (1964) Multipartite Product Turán Lemma:**
Any subset `E ⊆ V_0 × ... × V_{r-1}` (with `|V_i| = N`) of density `δ ∈ (0, 1]` contains a
complete `r`-partite blowup `U_0 × ... × U_{r-1} ⊆ E` with `|U_i| = m` whenever
`2 * m ≤ (δ / 2) ^ ((m + 1) ^ (r - 1)) * N`. -/
private lemma erdos1964_product {α : Type*} [DecidableEq α] :
    ∀ (r : ℕ), 1 ≤ r → ∀ (m N : ℕ), 1 ≤ m → 1 ≤ N →
      ∀ (V : Fin r → Finset α) (E : Finset (Fin r → α)) (δ : ℝ),
        (∀ i : Fin r, (V i).card = N) →
        E ⊆ Fintype.piFinset V →
        0 < δ → δ ≤ 1 →
        δ * (N : ℝ) ^ r ≤ (E.card : ℝ) →
        2 * (m : ℝ) ≤ (δ / 2) ^ ((m + 1) ^ (r - 1)) * (N : ℝ) →
        ∃ U : Fin r → Finset α,
          (∀ i : Fin r, U i ⊆ V i ∧ (U i).card = m) ∧ Fintype.piFinset U ⊆ E := by
  intro r
  induction r with
  | zero => intro h0; omega
  | succ r ih =>
    intro _ m N hm hN V E δ hVcard hEsub hδ0 hδ1 hEcard hNlb
    by_cases hr0 : r = 0
    · subst hr0
      -- Base case r = 1: project E ⊆ (Fin 1 → α) to V 0
      let E0 : Finset α := (V 0).filter (fun x => (fun _ : Fin 1 => x) ∈ E)
      have hE0_card : E0.card = E.card := by
        refine Finset.card_bij (fun x _ => (fun _ : Fin 1 => x)) ?_ ?_ ?_
        · intro x hx; exact (Finset.mem_filter.mp hx).2
        · intro x₁ _ x₂ _ hEq; exact congrFun hEq 0
        · intro f hf
          have hf0 : f 0 ∈ V 0 := (Fintype.mem_piFinset.mp (hEsub hf)) 0
          have hfeq : (fun _ : Fin 1 => f 0) = f := by
            funext i; rw [Fin.eq_zero i]
          refine ⟨f 0, Finset.mem_filter.mpr ⟨hf0, by rw [hfeq]; exact hf⟩, hfeq⟩
      have hm_le_E0 : m ≤ E0.card := by
        have h1 : (m : ℝ) ≤ (E0.card : ℝ) := by
          rw [hE0_card]
          simp only [zero_add, Nat.sub_self, pow_zero, pow_one] at hNlb hEcard
          have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          nlinarith
        exact_mod_cast h1
      obtain ⟨U0, hU0sub, hU0card⟩ := Finset.exists_subset_card_eq hm_le_E0
      refine ⟨fun _ => U0, fun i => ?_, fun f hf => ?_⟩
      · rw [Fin.eq_zero i]
        exact ⟨hU0sub.trans (Finset.filter_subset _ _), hU0card⟩
      · have hf0 : f 0 ∈ U0 := Fintype.mem_piFinset.mp hf 0
        have hmem : (fun _ : Fin 1 => f 0) ∈ E := (Finset.mem_filter.mp (hU0sub hf0)).2
        have hfeq : (fun _ : Fin 1 => f 0) = f := by funext i; rw [Fin.eq_zero i]
        rwa [← hfeq]
    · have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr0
      let Vprev : Fin r → Finset α := fun i => V i.castSucc
      let X : Finset (Fin r → α) := Fintype.piFinset Vprev
      let Y : Finset α := V (Fin.last r)
      let adj : (Fin r → α) → α → Prop := fun x y => Fin.snoc (α := fun _ => α) x y ∈ E
      have hXcard : X.card = N ^ r := by
        dsimp only [X, Vprev]
        rw [Fintype.card_piFinset]
        simp [hVcard]
      have hYcard : Y.card = N := hVcard (Fin.last r)
      -- Sum of degrees ∑ x ∈ X, |(Y.filter (adj x))| = E.card
      have hsum_deg : ∑ x ∈ X, (Y.filter (fun y => adj x y)).card = E.card := by
        have h1 : ∑ x ∈ X, (Y.filter (fun y => adj x y)).card =
            ((X ×ˢ Y).filter (fun p => adj p.1 p.2)).card := by
          rw [Finset.card_filter, Finset.sum_product]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.card_filter]
        rw [h1]
        refine Finset.card_bij (fun p _ => Fin.snoc (α := fun _ => α) p.1 p.2) ?_ ?_ ?_
        · intro p hp; exact (Finset.mem_filter.mp hp).2
        · intro ⟨x₁, y₁⟩ _ ⟨x₂, y₂⟩ _ hEq
          have hx : x₁ = x₂ := by
            funext i
            have := congrFun hEq i.castSucc
            simpa using this
          have hy : y₁ = y₂ := by
            have := congrFun hEq (Fin.last r)
            simpa using this
          simp [hx, hy]
        · intro f hf
          let x : Fin r → α := fun i => f i.castSucc
          let y : α := f (Fin.last r)
          have hsnoc : Fin.snoc (α := fun _ => α) x y = f := by
            funext i
            refine Fin.lastCases ?_ ?_ i
            · simp [y]
            · intro j; simp [x]
          refine ⟨(x, y), ?_, hsnoc⟩
          rw [Finset.mem_filter, Finset.mem_product]
          refine ⟨⟨Fintype.mem_piFinset.mpr fun i => (Fintype.mem_piFinset.mp (hEsub hf)) i.castSucc,
            (Fintype.mem_piFinset.mp (hEsub hf)) (Fin.last r)⟩, ?_⟩
          dsimp only [adj]
          rwa [hsnoc]
      -- Verify hypotheses of kst_bipartite_power_mean with δ' = δ / 2 and t = m
      have hδ2_pos : 0 < δ / 2 := by linarith
      have hδ2_le1 : δ / 2 ≤ 1 := by linarith
      have hm_le_δ2N : (m : ℝ) ≤ (δ / 2) * (Y.card : ℝ) := by
        rw [hYcard]
        have hpow_le : (δ / 2) ^ ((m + 1) ^ r) ≤ δ / 2 := by
          have hexp1 : 1 ≤ (m + 1) ^ r := Nat.one_le_pow _ _ (by omega)
          calc
            (δ / 2) ^ ((m + 1) ^ r) ≤ (δ / 2) ^ 1 := pow_le_pow_of_le_one (le_of_lt hδ2_pos) hδ2_le1 hexp1
            _ = δ / 2 := pow_one _
        have h1 : (δ / 2) ^ ((m + 1) ^ r) * (N : ℝ) ≤ (δ / 2) * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hpow_le (Nat.cast_nonneg N)
        have h2 : (m : ℝ) ≤ 2 * (m : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) m]
        have hsub : r + 1 - 1 = r := by omega
        rw [hsub] at hNlb
        linarith
      have hm_le_Y : m ≤ Y.card := by
        have h1 : (m : ℝ) ≤ (Y.card : ℝ) := by
          have hY0 : (0 : ℝ) ≤ (Y.card : ℝ) := Nat.cast_nonneg _
          nlinarith
        exact_mod_cast h1
      have hedges : 2 * (δ / 2) * (X.card : ℝ) * (Y.card : ℝ) ≤
          ((∑ x ∈ X, (Y.filter (fun y => adj x y)).card : ℕ) : ℝ) := by
        rw [hsum_deg, hXcard, hYcard]
        push_cast
        rw [pow_succ] at hEcard
        linarith
      obtain ⟨Ulast, hUlast_mem, hE'_card⟩ :=
        kst_bipartite_power_mean X Y adj hm hm_le_Y hδ2_pos hm_le_δ2N hedges
      rcases Finset.mem_powersetCard.mp hUlast_mem with ⟨hUlast_sub, hUlast_card⟩
      let E' : Finset (Fin r → α) := X.filter (fun x => ∀ y ∈ Ulast, adj x y)
      let δ' : ℝ := (δ / 2) ^ m
      have hδ'_pos : 0 < δ' := by dsimp only [δ']; positivity
      have hδ'_le1 : δ' ≤ 1 := by dsimp only [δ']; exact pow_le_one₀ (le_of_lt hδ2_pos) hδ2_le1
      have hE'_lb : δ' * (N : ℝ) ^ r ≤ (E'.card : ℝ) := by
        dsimp only [δ', E']
        rw [hXcard] at hE'_card
        push_cast at hE'_card
        exact hE'_card
      have hNlb' : 2 * (m : ℝ) ≤ (δ' / 2) ^ ((m + 1) ^ (r - 1)) * (N : ℝ) := by
        have hstep : (δ / 2) ^ (m + 1) ≤ δ' / 2 := by
          dsimp only [δ']
          rw [pow_succ]
          have : δ / 2 ≤ 1 / 2 := by linarith
          have hp0 : 0 ≤ (δ / 2) ^ m := by positivity
          nlinarith
        have hpow_step : (δ / 2) ^ ((m + 1) ^ r) ≤ (δ' / 2) ^ ((m + 1) ^ (r - 1)) := by
          have hr_eq : (m + 1) ^ r = (m + 1) * (m + 1) ^ (r - 1) := by
            conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ']
          rw [hr_eq, pow_mul]
          exact pow_le_pow_left₀ (by positivity) hstep _
        have hsub : r + 1 - 1 = r := by omega
        rw [hsub] at hNlb
        exact le_trans hNlb (mul_le_mul_of_nonneg_right hpow_step (Nat.cast_nonneg N))
      obtain ⟨Uprev, hUprev_prop, hUprev_sub⟩ :=
        ih hr1 m N hm hN Vprev E' δ' (fun i => hVcard i.castSucc)
          (Finset.filter_subset _ _) hδ'_pos hδ'_le1 hE'_lb hNlb'
      let U : Fin (r + 1) → Finset α := Fin.snoc (α := fun _ => Finset α) Uprev Ulast
      refine ⟨U, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa [U, Y] using ⟨hUlast_sub, hUlast_card⟩
        · intro j
          simpa [U, Vprev] using hUprev_prop j
      · intro f hf
        let x : Fin r → α := fun i => f i.castSucc
        let y : α := f (Fin.last r)
        have hx : x ∈ Fintype.piFinset Uprev := by
          rw [Fintype.mem_piFinset]
          intro j
          have := (Fintype.mem_piFinset.mp hf) j.castSucc
          simpa [U] using this
        have hy : y ∈ Ulast := by
          have := (Fintype.mem_piFinset.mp hf) (Fin.last r)
          simpa [U] using this
        have hxE' : x ∈ E' := hUprev_sub hx
        have hadj : adj x y := (Finset.mem_filter.mp hxE').2 y hy
        have hsnoc : Fin.snoc (α := fun _ => α) x y = f := by
          funext i
          refine Fin.lastCases ?_ ?_ i
          · simp [y]
          · intro j; simp [x]
        dsimp only [adj] at hadj
        rwa [hsnoc] at hadj

/-- Two finite subsets of `Fin n` of the same cardinality are related by a permutation of `Fin n`. -/
private lemma exists_perm_image_eq {n : ℕ} (s t : Finset (Fin n)) (hcard : s.card = t.card) :
    ∃ τ : Equiv.Perm (Fin n), s.image τ = t := by
  classical
  have hcomp_card : (Finset.univ \ s).card = (Finset.univ \ t).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ s),
      Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ t), hcard]
  have he1 : Fintype.card {x : Fin n // x ∈ s} = Fintype.card {x : Fin n // x ∈ t} := by
    simpa [Fintype.card_coe] using hcard
  have he2 : Fintype.card {x : Fin n // x ∉ s} = Fintype.card {x : Fin n // x ∉ t} := by
    have hs : Fintype.card {x : Fin n // x ∉ s} = (Finset.univ \ s).card := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr ?_
      exact
        { toFun := fun x => ⟨x.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, x.2⟩⟩
          invFun := fun x => ⟨x.1, (Finset.mem_sdiff.mp x.2).2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have ht : Fintype.card {x : Fin n // x ∉ t} = (Finset.univ \ t).card := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr ?_
      exact
        { toFun := fun x => ⟨x.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, x.2⟩⟩
          invFun := fun x => ⟨x.1, (Finset.mem_sdiff.mp x.2).2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [hs, ht, hcomp_card]
  let e1 : {x : Fin n // x ∈ s} ≃ {x : Fin n // x ∈ t} := Fintype.equivOfCardEq he1
  let e2 : {x : Fin n // x ∉ s} ≃ {x : Fin n // x ∉ t} := Fintype.equivOfCardEq he2
  let τ : Equiv.Perm (Fin n) :=
    { toFun := fun x => if hx : x ∈ s then (e1 ⟨x, hx⟩).1 else (e2 ⟨x, hx⟩).1
      invFun := fun y => if hy : y ∈ t then (e1.symm ⟨y, hy⟩).1 else (e2.symm ⟨y, hy⟩).1
      left_inv := fun x => by
        by_cases hx : x ∈ s
        · simp only [dif_pos hx, dif_pos (e1 ⟨x, hx⟩).2]
          exact congrArg Subtype.val (e1.symm_apply_apply ⟨x, hx⟩)
        · simp only [dif_neg hx, dif_neg (e2 ⟨x, hx⟩).2]
          exact congrArg Subtype.val (e2.symm_apply_apply ⟨x, hx⟩)
      right_inv := fun y => by
        by_cases hy : y ∈ t
        · simp only [dif_pos hy, dif_pos (e1.symm ⟨y, hy⟩).2]
          exact congrArg Subtype.val (e1.apply_symm_apply ⟨y, hy⟩)
        · simp only [dif_neg hy, dif_neg (e2.symm ⟨y, hy⟩).2]
          exact congrArg Subtype.val (e2.apply_symm_apply ⟨y, hy⟩) }
  refine ⟨τ, ?_⟩
  ext y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [τ, Equiv.coe_fn_mk, dif_pos hx]
    exact (e1 ⟨x, hx⟩).2
  · intro hy
    refine ⟨(e1.symm ⟨y, hy⟩).1, (e1.symm ⟨y, hy⟩).2, ?_⟩
    simp only [τ, Equiv.coe_fn_mk, dif_pos (e1.symm ⟨y, hy⟩).2]
    exact congrArg Subtype.val (e1.apply_symm_apply ⟨y, hy⟩)

/-- **Exact Permutation-Averaging Multipartite Extraction (Zero Density Loss):**
Given any `t`-uniform hypergraph `H` on `Fin n` with `n.choose t ≤ 2 * |H|` and `N = n / t ≥ 1`,
there exist `t` pairwise disjoint `N`-subsets `V 0, ..., V (t - 1) ⊆ Fin n` such that at least
half of all `N ^ t` crossing tuples lie in `H`. -/
private lemma exists_disjoint_dense_parts {n t : ℕ} (ht : 1 ≤ t) (hnt : t ≤ n)
    (H : Finset (Finset (Fin n))) (hHsub : H ⊆ (Finset.univ : Finset (Fin n)).powersetCard t)
    (hHcard : n.choose t ≤ 2 * H.card) :
    let N : ℕ := n / t
    ∃ V : Fin t → Finset (Fin n),
      (∀ i : Fin t, (V i).card = N) ∧
      (∀ i j : Fin t, i ≠ j → Disjoint (V i) (V j)) ∧
      N ^ t ≤ 2 * ((Fintype.piFinset V).filter (fun f => (Finset.univ.image f) ∈ H)).card := by
  classical
  intro N
  have hN_pos : 1 ≤ N := Nat.div_pos hnt (by omega)
  have htN_le : t * N ≤ n := Nat.mul_div_le n t
  let idx : Fin t → Fin N → Fin n := fun i j =>
    ⟨i.1 * N + j.1, by
      have hi : i.1 + 1 ≤ t := i.2
      have h1 : (i.1 + 1) * N ≤ t * N := Nat.mul_le_mul_right N hi
      have h2 : i.1 * N + j.1 < i.1 * N + N := Nat.add_lt_add_left j.2 _
      have h3 : i.1 * N + N = (i.1 + 1) * N := by ring
      omega⟩
  have hidx_inj : ∀ i₁ j₁ i₂ j₂, idx i₁ j₁ = idx i₂ j₂ → i₁ = i₂ ∧ j₁ = j₂ := by
    intro i₁ j₁ i₂ j₂ hEq
    have hval : i₁.1 * N + j₁.1 = i₂.1 * N + j₂.1 := congrArg Fin.val hEq
    have hdiv : i₁.1 = i₂.1 := by
      have h1 : (i₁.1 * N + j₁.1) / N = i₁.1 := by
        rw [mul_comm i₁.1 N, Nat.mul_add_div (by omega : 0 < N), Nat.div_eq_of_lt j₁.2, add_zero]
      have h2 : (i₂.1 * N + j₂.1) / N = i₂.1 := by
        rw [mul_comm i₂.1 N, Nat.mul_add_div (by omega : 0 < N), Nat.div_eq_of_lt j₂.2, add_zero]
      rw [← h1, hval, h2]
    have hmod : j₁.1 = j₂.1 := by nlinarith
    exact ⟨Fin.ext hdiv, Fin.ext hmod⟩
  -- For any fixed g : Fin t → Fin N, by permutation symmetry,
  -- #{σ : Perm (Fin n) | image (σ ∘ a_g) = e} is constant over all e ∈ univ.powersetCard t!
  have hfixed_g : ∀ g : Fin t → Fin N,
      Fintype.card (Equiv.Perm (Fin n)) ≤
        2 * (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (Finset.univ.image (fun i : Fin t => σ (idx i (g i)))) ∈ H)).card := by
    intro g
    let a : Fin t → Fin n := fun i => idx i (g i)
    have ha_inj : Function.Injective a := fun i₁ i₂ h => (hidx_inj i₁ (g i₁) i₂ (g i₂) h).1
    let img (σ : Equiv.Perm (Fin n)) : Finset (Fin n) := Finset.univ.image (fun i => σ (a i))
    have himg_mem : ∀ σ : Equiv.Perm (Fin n),
        img σ ∈ (Finset.univ : Finset (Fin n)).powersetCard t := by
      intro σ
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      change (Finset.univ.image (σ ∘ a)).card = t
      rw [Finset.card_image_of_injective _ (σ.injective.comp ha_inj), Finset.card_univ,
        Fintype.card_fin]
    -- Fiber cardinality is invariant under e₁, e₂ ∈ univ.powersetCard t
    have hfiber_eq : ∀ e₁ e₂ : Finset (Fin n),
        e₁ ∈ (Finset.univ : Finset (Fin n)).powersetCard t →
        e₂ ∈ (Finset.univ : Finset (Fin n)).powersetCard t →
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => img σ = e₁)).card =
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => img σ = e₂)).card := by
      intro e₁ e₂ he₁ he₂
      have hcard_eq : e₁.card = e₂.card := by
        rw [(Finset.mem_powersetCard.mp he₁).2, (Finset.mem_powersetCard.mp he₂).2]
      obtain ⟨τ, hτ⟩ := exists_perm_image_eq e₁ e₂ hcard_eq
      refine Finset.card_bij (fun σ _ => τ * σ) ?_ ?_ ?_
      · intro σ hσ
        have hσe : img σ = e₁ := (Finset.mem_filter.mp hσ).2
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        dsimp only [img] at hσe ⊢
        calc
          Finset.univ.image (fun i => (τ * σ) (a i))
              = (Finset.univ.image (fun i => σ (a i))).image τ := by
                rw [Finset.image_image]; rfl
          _ = e₁.image τ := by rw [hσe]
          _ = e₂ := hτ
      · intro σ₁ _ σ₂ _ hEq; exact mul_left_cancel hEq
      · intro σ₂ hσ₂
        have hσe : img σ₂ = e₂ := (Finset.mem_filter.mp hσ₂).2
        refine ⟨τ⁻¹ * σ₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, mul_inv_cancel_left τ σ₂⟩
        dsimp only [img] at hσe ⊢
        calc
          Finset.univ.image (fun i => (τ⁻¹ * σ₂) (a i))
              = (Finset.univ.image (fun i => σ₂ (a i))).image (τ⁻¹ : Equiv.Perm (Fin n)) := by
                rw [Finset.image_image]; rfl
          _ = e₂.image (τ⁻¹ : Equiv.Perm (Fin n)) := by rw [hσe]
          _ = (e₁.image τ).image (τ⁻¹ : Equiv.Perm (Fin n)) := by rw [← hτ]
          _ = e₁ := by
              rw [Finset.image_image]
              have : ((τ⁻¹ : Equiv.Perm (Fin n)) ∘ (τ : Equiv.Perm (Fin n))) = id := by
                funext x; simp
              rw [this, Finset.image_id]
    -- Pick a reference e₀ = img 1
    let e₀ : Finset (Fin n) := img 1
    have he₀ : e₀ ∈ (Finset.univ : Finset (Fin n)).powersetCard t := himg_mem 1
    let c0 : ℕ := (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => img σ = e₀)).card
    have htotal : Fintype.card (Equiv.Perm (Fin n)) = n.choose t * c0 := by
      have hsum : ∑ e ∈ (Finset.univ : Finset (Fin n)).powersetCard t,
          (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => img σ = e)).card =
          Fintype.card (Equiv.Perm (Fin n)) := by
        rw [← Finset.card_biUnion]
        · rw [← Finset.card_univ]
          congr 1
          ext σ
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          exact ⟨img σ, himg_mem σ, rfl⟩
        · intro e₁ _ e₂ _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro σ h1 h2
          exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      rw [← hsum]
      have hcongr : ∑ e ∈ (Finset.univ : Finset (Fin n)).powersetCard t,
          (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => img σ = e)).card =
          ∑ _e ∈ (Finset.univ : Finset (Fin n)).powersetCard t, c0 :=
        Finset.sum_congr rfl fun e he => hfiber_eq e e₀ he he₀
      rw [hcongr, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul]
    have hH_sum : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => img σ ∈ H)).card =
        H.card * c0 := by
      have hsum : ∑ e ∈ H,
          (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => img σ = e)).card =
          (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => img σ ∈ H)).card := by
        rw [← Finset.card_biUnion]
        · congr 1
          ext σ
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun ⟨e, heH, hEq⟩ => hEq ▸ heH, fun h => ⟨img σ, h, rfl⟩⟩
        · intro e₁ _ e₂ _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro σ h1 h2
          exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      rw [← hsum]
      have hcongr : ∑ e ∈ H,
          (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => img σ = e)).card =
          ∑ _e ∈ H, c0 :=
        Finset.sum_congr rfl fun e he => hfiber_eq e e₀ (hHsub he) he₀
      rw [hcongr, Finset.sum_const, smul_eq_mul]
    rw [htotal, hH_sum]
    calc
      n.choose t * c0 ≤ (2 * H.card) * c0 := Nat.mul_le_mul_right c0 hHcard
      _ = 2 * (H.card * c0) := by ring
  -- Sum over all g : Fin t → Fin N and swap sums to find a good σ : Equiv.Perm (Fin n)
  let score (σ : Equiv.Perm (Fin n)) : ℕ :=
    (Finset.univ.filter (fun g : Fin t → Fin N =>
      (Finset.univ.image (fun i : Fin t => σ (idx i (g i)))) ∈ H)).card
  have hsum_ge : Fintype.card (Equiv.Perm (Fin n)) * N ^ t ≤
      2 * ∑ σ : Equiv.Perm (Fin n), score σ := by
    have hswap : ∑ σ : Equiv.Perm (Fin n), score σ =
        ∑ g : Fin t → Fin N,
          (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
            (Finset.univ.image (fun i : Fin t => σ (idx i (g i)))) ∈ H)).card := by
      simp only [score, Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap, Finset.mul_sum]
    calc
      Fintype.card (Equiv.Perm (Fin n)) * N ^ t
          = ∑ _g : Fin t → Fin N, Fintype.card (Equiv.Perm (Fin n)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              Fintype.card_fin, smul_eq_mul, mul_comm]
      _ ≤ ∑ g : Fin t → Fin N,
            2 * (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
              (Finset.univ.image (fun i : Fin t => σ (idx i (g i)))) ∈ H)).card :=
            Finset.sum_le_sum fun g _ => hfixed_g g
  have hex_σ : ∃ σ : Equiv.Perm (Fin n), N ^ t ≤ 2 * score σ := by
    by_contra hnone
    push Not at hnone
    have hstrict : ∑ σ : Equiv.Perm (Fin n), 2 * score σ <
        ∑ _σ : Equiv.Perm (Fin n), N ^ t :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun σ _ => hnone σ)
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hstrict
    omega
  obtain ⟨σ, hσ⟩ := hex_σ
  let V : Fin t → Finset (Fin n) := fun i =>
    (Finset.univ : Finset (Fin N)).image (fun j => σ (idx i j))
  refine ⟨V, ?_, ?_, ?_⟩
  · intro i
    dsimp only [V]
    rw [Finset.card_image_of_injective _ (fun j₁ j₂ h => (hidx_inj i j₁ i j₂ (σ.injective h)).2),
      Finset.card_univ, Fintype.card_fin]
  · intro i₁ i₂ hne
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rcases Finset.mem_image.mp hx₁ with ⟨j₁, _, rfl⟩
    rcases Finset.mem_image.mp hx₂ with ⟨j₂, _, hEq⟩
    exact hne (hidx_inj i₂ j₂ i₁ j₁ (σ.injective hEq)).1.symm
  · have hscore_eq : score σ =
        ((Fintype.piFinset V).filter (fun f => (Finset.univ.image f) ∈ H)).card := by
      refine Finset.card_bij (fun g _ i => σ (idx i (g i))) ?_ ?_ ?_
      · intro g hg
        rw [Finset.mem_filter]
        refine ⟨Fintype.mem_piFinset.mpr fun i => Finset.mem_image.mpr ⟨g i, Finset.mem_univ _, rfl⟩,
          (Finset.mem_filter.mp hg).2⟩
      · intro g₁ _ g₂ _ hEq
        funext i
        exact (hidx_inj i (g₁ i) i (g₂ i) (σ.injective (congrFun hEq i))).2
      · intro f hf
        rcases Finset.mem_filter.mp hf with ⟨hfpi, hfH⟩
        have hex_j : ∀ i : Fin t, ∃ j : Fin N, σ (idx i j) = f i := by
          intro i
          obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Fintype.mem_piFinset.mp hfpi i)
          exact ⟨j, hj⟩
        let g : Fin t → Fin N := fun i => Classical.choose (hex_j i)
        have hgeq : (fun i => σ (idx i (g i))) = f := by
          funext i; exact Classical.choose_spec (hex_j i)
        refine ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hgeq]⟩, hgeq⟩
    rw [← hscore_eq]
    exact hσ

/-- **Erdős (1964) Complete `t`-Partite Monochromatic Hypergraph Theorem:**
In any 2-coloring of `K_n^{(t)}` (`t ≥ 2`), if `2 * m ≤ (1 / 4) ^ ((m + 1) ^ (t - 1)) * (n / t)`,
there exists a monochromatic complete `t`-partite `t`-uniform subhypergraph `K^{(t)}(m, ..., m)`. -/
private lemma erdos1964_mono_multipartite {n t m : ℕ} (ht : 2 ≤ t) (hm : 1 ≤ m) (hnt : t ≤ n)
    (c : Finset (Fin n) → Bool)
    (hlb : 2 * (m : ℝ) ≤ (1 / 4 : ℝ) ^ ((m + 1) ^ (t - 1)) * ((n / t : ℕ) : ℝ)) :
    ∃ (b₀ : Bool) (U : Fin t → Finset (Fin n)),
      (∀ i : Fin t, (U i).card = m) ∧
      (∀ i j : Fin t, i ≠ j → Disjoint (U i) (U j)) ∧
      (∀ f ∈ Fintype.piFinset U, c (Finset.univ.image f) = b₀) := by
  let allE : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard t
  let H0 : Finset (Finset (Fin n)) := allE.filter (fun e => c e = false)
  let H1 : Finset (Finset (Fin n)) := allE.filter (fun e => c e = true)
  have hsum_H : H0.card + H1.card = n.choose t := by
    have hdisj : Disjoint H0 H1 := by
      rw [Finset.disjoint_left]
      intro e h0 h1
      have hc0 := (Finset.mem_filter.mp h0).2
      have hc1 := (Finset.mem_filter.mp h1).2
      rw [hc0] at hc1
      exact Bool.false_ne_true hc1
    have hunion : H0 ∪ H1 = allE := by
      ext e
      simp only [H0, H1, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases hc : c e = false
        · exact Or.inl ⟨h, hc⟩
        · exact Or.inr ⟨h, Bool.eq_true_of_not_eq_false hc⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
    simp [allE]
  have hmaj : ∃ b₀ : Bool, n.choose t ≤ 2 * (allE.filter (fun e => c e = b₀)).card := by
    by_cases h : H0.card ≤ H1.card
    · exact ⟨true, by dsimp only [H0, H1] at h hsum_H; omega⟩
    · exact ⟨false, by dsimp only [H0, H1] at h hsum_H; omega⟩
  obtain ⟨b₀, hb₀⟩ := hmaj
  let H : Finset (Finset (Fin n)) := allE.filter (fun e => c e = b₀)
  obtain ⟨V, hVcard, hVdisj, hVdense⟩ :=
    exists_disjoint_dense_parts (by omega : 1 ≤ t) hnt H (Finset.filter_subset _ _) hb₀
  let E : Finset (Fin t → Fin n) :=
    (Fintype.piFinset V).filter (fun f => (Finset.univ.image f) ∈ H)
  have hN_pos : 1 ≤ n / t := Nat.div_pos hnt (by omega)
  have hEdense_r : (1 / 2 : ℝ) * ((n / t : ℕ) : ℝ) ^ t ≤ (E.card : ℝ) := by
    have hnat : (n / t) ^ t ≤ 2 * E.card := hVdense
    have hr : (((n / t) ^ t : ℕ) : ℝ) ≤ ((2 * E.card : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hr
    linarith
  have hlb' : 2 * (m : ℝ) ≤ ((1 / 2 : ℝ) / 2) ^ ((m + 1) ^ (t - 1)) * ((n / t : ℕ) : ℝ) := by
    have : ((1 / 2 : ℝ) / 2) = 1 / 4 := by norm_num
    rwa [this]
  obtain ⟨U, hUprop, hUsub⟩ :=
    erdos1964_product t (by omega : 1 ≤ t) m (n / t) hm hN_pos V E (1 / 2)
      hVcard (Finset.filter_subset _ _) (by norm_num) (by norm_num) hEdense_r hlb'
  refine ⟨b₀, U, fun i => (hUprop i).2, ?_, ?_⟩
  · intro i j hij
    exact Finset.disjoint_of_subset_left (hUprop i).1
      (Finset.disjoint_of_subset_right (hUprop j).1 (hVdisj i j hij))
  · intro f hf
    have hfH : Finset.univ.image f ∈ H := (Finset.mem_filter.mp (hUsub hf)).2
    exact (Finset.mem_filter.mp hfH).2

/-- Alternating-sum identity on `Finset (Fin t)`:
`∑ I ⊇ J, (-1)^(t - I.card) = if J = univ then 1 else 0`. -/
private lemma alternating_sum_supsets {t : ℕ} (J : Finset (Fin t)) :
    ∑ I ∈ (Finset.univ : Finset (Finset (Fin t))).filter (fun I => J ⊆ I),
      (-1 : ℤ) ^ (t - I.card) =
      if J = Finset.univ then 1 else 0 := by
  let K : Finset (Fin t) := Finset.univ \ J
  have hdisj : Disjoint J K := Finset.disjoint_sdiff
  have hKcard : K.card = t - J.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ J),
      Finset.card_univ, Fintype.card_fin]
  have hbij : ∑ I ∈ (Finset.univ : Finset (Finset (Fin t))).filter (fun I => J ⊆ I),
      (-1 : ℤ) ^ (t - I.card) =
      ∑ A ∈ K.powerset, (-1 : ℤ) ^ (K.card - A.card) := by
    refine Finset.sum_bij (fun I _ => I \ J) ?_ ?_ ?_ ?_
    · intro I _
      rw [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff (Finset.subset_univ I) (Finset.Subset.refl J)
    · intro I₁ hI₁ I₂ hI₂ hEq
      have hJ₁ : J ⊆ I₁ := (Finset.mem_filter.mp hI₁).2
      have hJ₂ : J ⊆ I₂ := (Finset.mem_filter.mp hI₂).2
      rw [← Finset.sdiff_union_of_subset hJ₁, ← Finset.sdiff_union_of_subset hJ₂, hEq]
    · intro A hA
      have hAK : A ⊆ K := Finset.mem_powerset.mp hA
      have hdisjA : Disjoint J A := Finset.disjoint_of_subset_right hAK hdisj
      refine ⟨J ∪ A, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_union_left⟩, ?_⟩
      exact Finset.union_sdiff_cancel_left hdisjA
    · intro I hI
      have hJI : J ⊆ I := (Finset.mem_filter.mp hI).2
      have hIcard : (I \ J).card = I.card - J.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hJI]
      have hJleI : J.card ≤ I.card := Finset.card_le_card hJI
      have hIle_t : I.card ≤ t := by
        simpa using Finset.card_le_univ I
      rw [hKcard, hIcard]
      congr 1
      omega
  rw [hbij]
  have hbinom : ∑ A ∈ K.powerset, (-1 : ℤ) ^ (K.card - A.card) = (1 + (-1 : ℤ)) ^ K.card := by
    rw [add_pow]
    have hgroup : ∑ A ∈ K.powerset, (-1 : ℤ) ^ (K.card - A.card) =
        ∑ r ∈ Finset.range (K.card + 1),
          ∑ _A ∈ K.powersetCard r, (-1 : ℤ) ^ (K.card - r) := by
      have hbi : K.powerset = (Finset.range (K.card + 1)).biUnion (fun r => K.powersetCard r) := by
        ext A
        simp only [Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
        constructor
        · intro hAK
          exact ⟨A.card, Nat.lt_succ_of_le (Finset.card_le_card hAK), hAK, rfl⟩
        · rintro ⟨_, _, hAK, _⟩; exact hAK
      conv_lhs => rw [hbi]
      rw [Finset.sum_biUnion]
      · refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun A hA => ?_
        rw [(Finset.mem_powersetCard.mp hA).2]
      · intro r₁ _ r₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro A h1 h2
        exact hne ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)
    rw [hgroup]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, one_pow]
    ring
  rw [hbinom]
  by_cases hJ : J = Finset.univ
  · subst hJ
    have hK0 : K.card = 0 := by simp [K]
    rw [hK0, pow_zero, if_pos rfl]
  · have hKpos : 0 < K.card := by
      rw [Finset.card_pos]
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hJ
      ext i
      simp only [Finset.mem_univ, iff_true]
      by_contra hi
      have : i ∈ K := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
      rw [hempty] at this
      exact Finset.notMem_empty i this
    rw [if_neg hJ]
    have : (1 + (-1 : ℤ)) = 0 := by ring
    rw [this, zero_pow (ne_of_gt hKpos)]

/-- General Inclusion-Exclusion Identity on a `t`-partite family `V : Fin t → Finset (Fin n)`:
for any subset `E ⊆ (univ.biUnion V).powersetCard t`, the alternating sum of `|(Y_I.powersetCard t) ∩ E|`
equals the number of crossing edges in `E`. -/
private lemma inclusion_exclusion_partite {n t : ℕ} (V : Fin t → Finset (Fin n))
    (hVdisj : ∀ i j : Fin t, i ≠ j → Disjoint (V i) (V j))
    (E : Finset (Finset (Fin n))) (hEsub : E ⊆ (Finset.univ.biUnion V).powersetCard t) :
    ∑ I : Finset (Fin t),
      (-1 : ℤ) ^ (t - I.card) *
        ((E.filter (fun e => e ⊆ I.biUnion V)).card : ℤ) =
      ((E.filter (fun e => ∀ i : Fin t, (e ∩ V i).Nonempty)).card : ℤ) := by
  have hL : ∑ I : Finset (Fin t),
      (-1 : ℤ) ^ (t - I.card) * ((E.filter (fun e => e ⊆ I.biUnion V)).card : ℤ) =
      ∑ I : Finset (Fin t), ∑ e ∈ E,
        (if e ⊆ I.biUnion V then (-1 : ℤ) ^ (t - I.card) else 0) := by
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hL, Finset.sum_comm]
  have hinner : ∀ e ∈ E,
      (∑ I : Finset (Fin t), if e ⊆ I.biUnion V then (-1 : ℤ) ^ (t - I.card) else 0) =
        if ∀ i : Fin t, (e ∩ V i).Nonempty then 1 else 0 := by
    intro e he
    let J : Finset (Fin t) := Finset.univ.filter (fun i => (e ∩ V i).Nonempty)
    have hiff : ∀ I : Finset (Fin t), e ⊆ I.biUnion V ↔ J ⊆ I := by
      intro I
      constructor
      · intro heI i hiJ
        obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hiJ).2
        rcases Finset.mem_inter.mp hx with ⟨hxe, hxVi⟩
        obtain ⟨j, hjI, hxVj⟩ := Finset.mem_biUnion.mp (heI hxe)
        have hij : i = j := by
          by_contra hne
          exact Finset.disjoint_left.mp (hVdisj i j hne) hxVi hxVj
        rwa [hij]
      · intro hJI x hxe
        have hxU : x ∈ Finset.univ.biUnion V := (Finset.mem_powersetCard.mp (hEsub he)).1 hxe
        obtain ⟨i, _, hxVi⟩ := Finset.mem_biUnion.mp hxU
        have hiJ : i ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, Finset.mem_inter.mpr ⟨hxe, hxVi⟩⟩⟩
        exact Finset.mem_biUnion.mpr ⟨i, hJI hiJ, hxVi⟩
    have hsum_eq : (∑ I : Finset (Fin t), if e ⊆ I.biUnion V then (-1 : ℤ) ^ (t - I.card) else 0) =
        ∑ I ∈ (Finset.univ : Finset (Finset (Fin t))).filter (fun I => J ⊆ I),
          (-1 : ℤ) ^ (t - I.card) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun I _ => ?_
      by_cases h : e ⊆ I.biUnion V
      · rw [if_pos h, if_pos ((hiff I).mp h)]
      · rw [if_neg h, if_neg (fun h' => h ((hiff I).mpr h'))]
    rw [hsum_eq, alternating_sum_supsets J]
    have hJuniv : J = Finset.univ ↔ ∀ i : Fin t, (e ∩ V i).Nonempty := by
      constructor
      · intro h i
        have : i ∈ J := by rw [h]; exact Finset.mem_univ i
        exact (Finset.mem_filter.mp this).2
      · intro h
        ext i
        simp [J, h i]
    by_cases hc : ∀ i : Fin t, (e ∩ V i).Nonempty
    · rw [if_pos (hJuniv.mpr hc), if_pos hc]
    · rw [if_neg (fun h => hc (hJuniv.mp h)), if_neg hc]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Exact Inclusion-Exclusion Discrepancy Obstruction (Finite for ALL `m ≥ t`):**
If `V : Fin t → Finset (Fin n)` (`t ≥ 2`) are pairwise disjoint sets of size `m ≥ t` whose crossing
`t`-edges are all color `b₀`, and
`α > 1/2 - t! / (2 * ∑_{r=1}^t (t.choose r) * r^t)`,
then some nonempty union `Y = I.biUnion V` (of size `≥ m`) violates `α`-balance. -/
private lemma inclusion_exclusion_discrepancy {n t m : ℕ} (ht : 2 ≤ t) (htm : t ≤ m)
    (V : Fin t → Finset (Fin n)) (hVcard : ∀ i : Fin t, (V i).card = m)
    (hVdisj : ∀ i j : Fin t, i ≠ j → Disjoint (V i) (V j))
    (c : Finset (Fin n) → Bool) (b₀ : Bool)
    (hcross : ∀ f ∈ Fintype.piFinset V, c (Finset.univ.image f) = b₀)
    {α : ℝ}
    (hα_gt : 1 / 2 - (t.factorial : ℝ) /
      (2 * ∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t) < α) :
    ∃ X : Finset (Fin n), m ≤ X.card ∧ ∃ b : Bool,
      (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ) < α * (X.card.choose t : ℝ) := by
  let U : Finset (Fin n) := Finset.univ.biUnion V
  let allE : Finset (Finset (Fin n)) := U.powersetCard t
  let b₁ : Bool := !b₀
  let E₁ : Finset (Finset (Fin n)) := allE.filter (fun e => c e = b₁)
  -- Helper: every crossing edge e ∈ allE has e = univ.image f for a unique f ∈ piFinset V
  have hcross_eq_image : ∀ e ∈ allE, (∀ i : Fin t, (e ∩ V i).Nonempty) →
      ∃ f ∈ Fintype.piFinset V, Finset.univ.image f = e := by
    intro e he hhit
    have hex : ∀ i : Fin t, ∃ x ∈ V i, x ∈ e := fun i => by
      obtain ⟨x, hx⟩ := hhit i
      exact ⟨x, (Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx).1⟩
    let f : Fin t → Fin n := fun i => Classical.choose (hex i)
    have hfV : ∀ i : Fin t, f i ∈ V i := fun i => (Classical.choose_spec (hex i)).1
    have hfe : ∀ i : Fin t, f i ∈ e := fun i => (Classical.choose_spec (hex i)).2
    have hfinj : Function.Injective f := by
      intro i j hEq
      by_contra hne
      exact Finset.disjoint_left.mp (hVdisj i j hne) (hfV i) (hEq ▸ hfV j)
    refine ⟨f, Fintype.mem_piFinset.mpr hfV, ?_⟩
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hfe i
    · rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin,
        (Finset.mem_powersetCard.mp he).2]
  -- Identity 1: alternating sum of E₁ is 0
  have hIE1 : ∑ I : Finset (Fin t),
      (-1 : ℤ) ^ (t - I.card) * (((I.biUnion V).powersetCard t |>.filter (fun e => c e = b₁)).card : ℤ) = 0 := by
    have hfilt_eq : ∀ I : Finset (Fin t),
        (E₁.filter (fun e => e ⊆ I.biUnion V)) =
          ((I.biUnion V).powersetCard t).filter (fun e => c e = b₁) := by
      intro I
      ext e
      simp only [E₁, allE, U, Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨⟨_, hcard⟩, hc⟩, heI⟩; exact ⟨⟨heI, hcard⟩, hc⟩
      · rintro ⟨⟨heI, hcard⟩, hc⟩
        exact ⟨⟨⟨heI.trans (Finset.biUnion_subset_biUnion_of_subset_left V (Finset.subset_univ I)),
          hcard⟩, hc⟩, heI⟩
    have h1 := inclusion_exclusion_partite V hVdisj E₁ (Finset.filter_subset _ _)
    simp_rw [hfilt_eq] at h1
    rw [h1]
    have hempty : E₁.filter (fun e => ∀ i : Fin t, (e ∩ V i).Nonempty) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he hhit
      rcases Finset.mem_filter.mp he with ⟨heall, hcb1⟩
      obtain ⟨f, hfpi, rfl⟩ := hcross_eq_image e heall hhit
      have hcb0 := hcross f hfpi
      rw [hcb0] at hcb1
      cases b₀ <;> simp [b₁] at hcb1
    rw [hempty, Finset.card_empty, Nat.cast_zero]
  -- Identity 2: alternating sum of allE is m ^ t
  have hIE2 : ∑ I : Finset (Fin t),
      (-1 : ℤ) ^ (t - I.card) * (((I.card * m).choose t : ℕ) : ℤ) = (m : ℤ) ^ t := by
    have hfilt_eq : ∀ I : Finset (Fin t),
        (allE.filter (fun e => e ⊆ I.biUnion V)).card = (I.card * m).choose t := by
      intro I
      have hEq : allE.filter (fun e => e ⊆ I.biUnion V) = (I.biUnion V).powersetCard t := by
        ext e
        simp only [allE, U, Finset.mem_filter, Finset.mem_powersetCard]
        exact ⟨fun ⟨⟨_, hc⟩, hI⟩ => ⟨hI, hc⟩,
          fun ⟨hI, hc⟩ => ⟨⟨hI.trans (Finset.biUnion_subset_biUnion_of_subset_left V (Finset.subset_univ I)),
            hc⟩, hI⟩⟩
      rw [hEq, Finset.card_powersetCard,
        Finset.card_biUnion (fun i _ j _ hij => hVdisj i j hij)]
      simp [hVcard]
    have h2 := inclusion_exclusion_partite V hVdisj allE (Finset.Subset.refl _)
    simp_rw [hfilt_eq] at h2
    rw [h2]
    have hcard_cross : (allE.filter (fun e => ∀ i : Fin t, (e ∩ V i).Nonempty)).card = m ^ t := by
      have hpi_card : (Fintype.piFinset V).card = m ^ t := by
        rw [Fintype.card_piFinset]; simp [hVcard]
      rw [← hpi_card]
      symm
      refine Finset.card_bij (fun f _ => Finset.univ.image f) ?_ ?_ ?_
      · intro f hf
        have hfinj : Function.Injective f := by
          intro i j hEq
          by_contra hne
          exact Finset.disjoint_left.mp (hVdisj i j hne)
            (Fintype.mem_piFinset.mp hf i) (hEq ▸ Fintype.mem_piFinset.mp hf j)
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
        · intro x hx
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Fintype.mem_piFinset.mp hf i⟩
        · rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
        · intro i
          exact ⟨f i, Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
            Fintype.mem_piFinset.mp hf i⟩⟩
      · intro f₁ hf₁ f₂ hf₂ hEq
        funext i
        have hmem : f₁ i ∈ Finset.univ.image f₂ := by
          rw [← hEq]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
        have hij : j = i := by
          by_contra hne
          exact Finset.disjoint_left.mp (hVdisj j i hne)
            (Fintype.mem_piFinset.mp hf₂ j) (hj ▸ Fintype.mem_piFinset.mp hf₁ i)
        rw [← hj, hij]
      · intro e he
        rcases Finset.mem_filter.mp he with ⟨heall, hhit⟩
        obtain ⟨f, hf, hfe⟩ := hcross_eq_image e heall hhit
        exact ⟨f, hf, hfe⟩
    rw [hcard_cross, Nat.cast_pow]
  -- Now prove by contradiction: assume every nonempty I is α-balanced in both colors
  by_contra hbal
  push Not at hbal
  have hYcard : ∀ I : Finset (Fin t), (I.biUnion V).card = I.card * m := fun I => by
    rw [Finset.card_biUnion (fun i _ j _ hij => hVdisj i j hij)]; simp [hVcard]
  have hI_bounds : ∀ I : Finset (Fin t),
      α * (((I.card * m).choose t : ℕ) : ℝ) ≤
        ((((I.biUnion V).powersetCard t).filter (fun e => c e = b₁)).card : ℝ) ∧
      ((((I.biUnion V).powersetCard t).filter (fun e => c e = b₁)).card : ℝ) ≤
        (1 - α) * (((I.card * m).choose t : ℕ) : ℝ) := by
    intro I
    by_cases hI0 : I = ∅
    · subst hI0
      have h0 : (0 : ℕ).choose t = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have htne : (0 : ℕ) ≠ t := by omega
      simp [h0, htne]
    · have hIpos : 1 ≤ I.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hI0)
      have hm_le : m ≤ (I.biUnion V).card := by
        rw [hYcard]; exact Nat.le_mul_of_pos_left m hIpos
      have hb1_lb := hbal (I.biUnion V) hm_le b₁
      have hb0_lb := hbal (I.biUnion V) hm_le b₀
      rw [hYcard] at hb1_lb hb0_lb
      have hpart : (((I.biUnion V).powersetCard t).filter (fun e => c e = b₀)).card +
          (((I.biUnion V).powersetCard t).filter (fun e => c e = b₁)).card = (I.card * m).choose t := by
        have hdisj_c : Disjoint (((I.biUnion V).powersetCard t).filter (fun e => c e = b₀))
            (((I.biUnion V).powersetCard t).filter (fun e => c e = b₁)) := by
          rw [Finset.disjoint_left]
          intro e h0 h1
          have hc0 := (Finset.mem_filter.mp h0).2
          have hc1 := (Finset.mem_filter.mp h1).2
          rw [hc0] at hc1
          cases b₀ <;> simp [b₁] at hc1
        have hunion : ((I.biUnion V).powersetCard t).filter (fun e => c e = b₀) ∪
            ((I.biUnion V).powersetCard t).filter (fun e => c e = b₁) = (I.biUnion V).powersetCard t := by
          ext e
          simp only [Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
          · intro h
            by_cases hc : c e = b₀
            · exact Or.inl ⟨h, hc⟩
            · refine Or.inr ⟨h, ?_⟩
              cases hce : c e <;> cases b₀ <;> simp_all [b₁]
        rw [← Finset.card_union_of_disjoint hdisj_c, hunion, Finset.card_powersetCard, hYcard]
      have hpart_r : ((((I.biUnion V).powersetCard t).filter (fun e => c e = b₀)).card : ℝ) +
          ((((I.biUnion V).powersetCard t).filter (fun e => c e = b₁)).card : ℝ) =
          (((I.card * m).choose t : ℕ) : ℝ) := by exact_mod_cast hpart
      exact ⟨hb1_lb, by linarith⟩
  -- Cast Identities 1 & 2 to ℝ and apply pointwise lower bound on (-1)^(t - |I|) * e_{b₁}(Y_I)
  have hIE1_r : ∑ I : Finset (Fin t),
      (-1 : ℝ) ^ (t - I.card) *
        ((((I.biUnion V).powersetCard t).filter (fun e => c e = b₁)).card : ℝ) = 0 := by
    have : ((∑ I : Finset (Fin t), (-1 : ℤ) ^ (t - I.card) *
        (((I.biUnion V).powersetCard t |>.filter (fun e => c e = b₁)).card : ℤ) : ℤ) : ℝ) = 0 := by
      rw [hIE1]; simp
    simpa using this
  have hIE2_r : ∑ I : Finset (Fin t),
      (-1 : ℝ) ^ (t - I.card) * (((I.card * m).choose t : ℕ) : ℝ) = (m : ℝ) ^ t := by
    have : ((∑ I : Finset (Fin t), (-1 : ℤ) ^ (t - I.card) *
        (((I.card * m).choose t : ℕ) : ℤ) : ℤ) : ℝ) = ((m : ℤ) ^ t : ℤ) := by
      rw [hIE2]
    simpa using this
  -- Key pointwise bound: for EVERY I,
  -- (-1)^(t - |I|) * e_{b₁}(Y_I) ≥ (1/2) * (-1)^(t - |I|) * N_I - (1/2 - α) * N_I
  have hpt : ∀ I : Finset (Fin t),
      (1 / 2 : ℝ) * (-1 : ℝ) ^ (t - I.card) * (((I.card * m).choose t : ℕ) : ℝ) -
        (1 / 2 - α) * (((I.card * m).choose t : ℕ) : ℝ) ≤
      (-1 : ℝ) ^ (t - I.card) *
        ((((I.biUnion V).powersetCard t).filter (fun e => c e = b₁)).card : ℝ) := by
    intro I
    obtain ⟨hlb, hub⟩ := hI_bounds I
    rcases Nat.even_or_odd (t - I.card) with hev | hodd
    · rw [hev.neg_one_pow]; linarith
    · rw [hodd.neg_one_pow]; linarith
  have hsum_ineq : (1 / 2 : ℝ) * (m : ℝ) ^ t -
      (1 / 2 - α) * ∑ I : Finset (Fin t), (((I.card * m).choose t : ℕ) : ℝ) ≤ 0 := by
    have h1 := Finset.sum_le_sum (s := (Finset.univ : Finset (Finset (Fin t)))) (fun I _ => hpt I)
    rw [hIE1_r, Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
    have h2 : ∑ I : Finset (Fin t),
        (1 / 2 : ℝ) * (-1 : ℝ) ^ (t - I.card) * (((I.card * m).choose t : ℕ) : ℝ) =
        (1 / 2 : ℝ) * (m : ℝ) ^ t := by
      rw [← hIE2_r, Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => by ring
    rw [h2] at h1
    exact h1
  -- Group ∑_I ((I.card * m).choose t) by r = I.card ∈ [1, t] and bound ((r * m).choose t) ≤ (r*m)^t / t!
  have hsum_upper : ∑ I : Finset (Fin t), (((I.card * m).choose t : ℕ) : ℝ) ≤
      ((m : ℝ) ^ t / (t.factorial : ℝ)) *
        ∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t := by
    have hgroup : ∑ I : Finset (Fin t), (((I.card * m).choose t : ℕ) : ℝ) =
        ∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (((r * m).choose t : ℕ) : ℝ) := by
      have hbi : (Finset.univ : Finset (Finset (Fin t))) =
          (Finset.range (t + 1)).biUnion (fun r => (Finset.univ : Finset (Fin t)).powersetCard r) := by
        ext I
        simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
          true_iff]
        exact ⟨I.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ I), Finset.subset_univ I, rfl⟩
      conv_lhs => rw [hbi]
      rw [Finset.sum_biUnion]
      · have hrange : ∑ r ∈ Finset.range (t + 1),
            ∑ I ∈ (Finset.univ : Finset (Fin t)).powersetCard r, (((I.card * m).choose t : ℕ) : ℝ) =
            ∑ r ∈ Finset.range (t + 1), (t.choose r : ℝ) * (((r * m).choose t : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          have hin : ∑ I ∈ (Finset.univ : Finset (Fin t)).powersetCard r,
              (((I.card * m).choose t : ℕ) : ℝ) =
              ∑ _I ∈ (Finset.univ : Finset (Fin t)).powersetCard r, (((r * m).choose t : ℕ) : ℝ) :=
            Finset.sum_congr rfl fun I hI => by rw [(Finset.mem_powersetCard.mp hI).2]
          rw [hin, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
        rw [hrange]
        have h0mem : (0 : ℕ) ∈ Finset.range (t + 1) := Finset.mem_range.mpr (by omega)
        rw [← Finset.add_sum_erase _ _ h0mem]
        have h0val : (t.choose 0 : ℝ) * (((0 * m).choose t : ℕ) : ℝ) = 0 := by
          have : (0 : ℕ).choose t = 0 := Nat.choose_eq_zero_of_lt (by omega)
          simp [this]
        rw [h0val, zero_add]
        have hset : (Finset.range (t + 1)).erase 0 = Finset.Icc 1 t := by
          ext r
          simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
          omega
        rw [hset]
      · intro r₁ _ r₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro I h1 h2
        exact hne ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)
    rw [hgroup, Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    have hchoose_ub : (((r * m).choose t : ℕ) : ℝ) ≤ (r : ℝ) ^ t * (m : ℝ) ^ t / (t.factorial : ℝ) := by
      have hnat : t.factorial * (r * m).choose t ≤ (r * m) ^ t := by
        rw [← Nat.descFactorial_eq_factorial_mul_choose]
        exact Nat.descFactorial_le_pow (r * m) t
      have hr_cast : (t.factorial : ℝ) * (((r * m).choose t : ℕ) : ℝ) ≤ (r : ℝ) ^ t * (m : ℝ) ^ t := by
        have : ((t.factorial * (r * m).choose t : ℕ) : ℝ) ≤ (((r * m) ^ t : ℕ) : ℝ) := by
          exact_mod_cast hnat
        push_cast at this
        rw [mul_pow] at this
        exact this
      rw [le_div_iff₀ (by exact_mod_cast Nat.factorial_pos t)]
      linarith
    calc
      (t.choose r : ℝ) * (((r * m).choose t : ℕ) : ℝ)
          ≤ (t.choose r : ℝ) * ((r : ℝ) ^ t * (m : ℝ) ^ t / (t.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left hchoose_ub (Nat.cast_nonneg _)
      _ = (m : ℝ) ^ t / (t.factorial : ℝ) * ((t.choose r : ℝ) * (r : ℝ) ^ t) := by ring
  -- Combine hsum_ineq, hsum_upper, and hα_gt to get a contradiction!
  have hS_pos : 0 < ∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t := by
    have hmem : 1 ∈ Finset.Icc 1 t := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have hterm_pos : 0 < (t.choose 1 : ℝ) * ((1 : ℕ) : ℝ) ^ t := by
      rw [Nat.choose_one_right, Nat.cast_one, one_pow, mul_one]
      exact_mod_cast (by omega : 0 < t)
    exact lt_of_lt_of_le hterm_pos
      (Finset.single_le_sum (f := fun r => (t.choose r : ℝ) * (r : ℝ) ^ t)
        (fun r _ => by positivity) hmem)
  have hα_le_half : α ≤ 1 / 2 := by
    by_contra hgt
    push Not at hgt
    have h0 : 0 ≤ ∑ I : Finset (Fin t), (((I.card * m).choose t : ℕ) : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hm_pos : (0 : ℝ) < (m : ℝ) ^ t := by
      have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      positivity
    nlinarith
  have hcomb : (1 / 2 : ℝ) * (m : ℝ) ^ t ≤
      (1 / 2 - α) * (((m : ℝ) ^ t / (t.factorial : ℝ)) *
        ∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t) := by
    have h1 : (1 / 2 : ℝ) * (m : ℝ) ^ t ≤
        (1 / 2 - α) * ∑ I : Finset (Fin t), (((I.card * m).choose t : ℕ) : ℝ) := by linarith
    exact le_trans h1 (mul_le_mul_of_nonneg_left hsum_upper (by linarith))
  have hm_pow_pos : (0 : ℝ) < (m : ℝ) ^ t := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    positivity
  have hfac_pos : (0 : ℝ) < (t.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos t
  have hα_le_IE : α ≤ 1 / 2 - (t.factorial : ℝ) /
      (2 * ∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t) := by
    have hcancel : (1 / 2 : ℝ) ≤
        (1 / 2 - α) * ((∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t) / (t.factorial : ℝ)) := by
      have : (m : ℝ) ^ t * (1 / 2 : ℝ) ≤
          (m : ℝ) ^ t * ((1 / 2 - α) * ((∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t) /
            (t.factorial : ℝ))) := by
        calc
          (m : ℝ) ^ t * (1 / 2 : ℝ) = (1 / 2 : ℝ) * (m : ℝ) ^ t := by ring
          _ ≤ (1 / 2 - α) * (((m : ℝ) ^ t / (t.factorial : ℝ)) *
                ∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t) := hcomb
          _ = (m : ℝ) ^ t * ((1 / 2 - α) * ((∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t) /
                (t.factorial : ℝ))) := by ring
      exact le_of_mul_le_mul_left this hm_pow_pos
    have hdiv : (t.factorial : ℝ) / (2 * ∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t) ≤
        1 / 2 - α := by
      rw [div_le_iff₀ (by positivity)]
      rw [mul_div_assoc', le_div_iff₀ hfac_pos] at hcancel
      linarith
    linarith
  linarith

/-- **General `t ≥ 2` (Including All `t ≥ 4`) High-Density Asymptotic Equivalence:**
For every `t ≥ 2` and every `α` strictly between the explicit Inclusion-Exclusion threshold
`α_IE(t) = 1/2 - t! / (2 * ∑_{r=1}^t (t.choose r) * r^t)` and `1/2`,
`F^{(t)}(n, α) =Θ[atTop] (log n)^{1/(t-1)}`. -/
theorem ppl063_general_t_high_density_isTheta {t : ℕ} (ht : 2 ≤ t) {α : ℝ}
    (hα_gt : 1 / 2 - (t.factorial : ℝ) /
      (2 * ∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t) < α)
    (hα_lt : α < 1 / 2) :
    (fun n : ℕ => ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        α * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)} : ℕ) : ℝ))
      =Θ[atTop] (fun n : ℕ => (Real.log (n : ℝ)) ^ ((1 : ℝ) / ((t : ℝ) - 1))) := by
  -- Show 0 ≤ α_IE(t) so 0 < α
  have hα0 : 0 ≤ α := by
    have hS_ge : (t.factorial : ℝ) ≤ ∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t := by
      have hmem : t ∈ Finset.Icc 1 t := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
      have hfac_le_pow : t.factorial ≤ t ^ t := Nat.factorial_le_pow t
      have hterm : (t.factorial : ℝ) ≤ (t.choose t : ℝ) * (t : ℝ) ^ t := by
        rw [Nat.choose_self, Nat.cast_one, one_mul]
        exact_mod_cast hfac_le_pow
      exact le_trans hterm
        (Finset.single_le_sum (f := fun r => (t.choose r : ℝ) * (r : ℝ) ^ t)
          (fun r _ => by positivity) hmem)
    have hS_pos : 0 < ∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t :=
      lt_of_lt_of_le (by exact_mod_cast Nat.factorial_pos t) hS_ge
    have hfrac : (t.factorial : ℝ) /
        (2 * ∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  constructor
  · exact threshold_isBigO_log_rpow ht hα0 hα_lt
  · -- Lower bound: (log n)^{1/(t-1)} = O(F(n, t, α))
    have ht1_pos : (0 : ℝ) < (t : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      linarith
    have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
    -- Choose explicit threshold N₀ so that m = ⌊(log(n/(2*t)) / (2 * log 4))^(1/(t-1))⌋ - 1 ≥ t
    let C_lb : ℝ := (2 * Real.log 4) ^ ((1 : ℝ) / ((t : ℝ) - 1)) * 4
    rw [Asymptotics.isBigO_iff]
    refine ⟨C_lb, ?_⟩
    rw [Filter.eventually_atTop]
    let N₀ : ℕ := max (2 * t) (Nat.ceil (Real.exp (2 * Real.log 4 * ((2 * t + 2 : ℕ) : ℝ) ^ (t - 1)))) + 1
    refine ⟨N₀, fun n hn => ?_⟩
    have hn_ge_2t : 2 * t ≤ n := le_trans (le_trans (le_max_left _ _) (Nat.le_succ _)) hn
    have hnt : t ≤ n := by omega
    have hn_pos : 0 < n := by omega
    have hlogn_ge : 2 * Real.log 4 * ((2 * t + 2 : ℕ) : ℝ) ^ (t - 1) ≤ Real.log (n : ℝ) := by
      have h1 : Real.exp (2 * Real.log 4 * ((2 * t + 2 : ℕ) : ℝ) ^ (t - 1)) ≤ (n : ℝ) := by
        have hc : Real.exp (2 * Real.log 4 * ((2 * t + 2 : ℕ) : ℝ) ^ (t - 1)) ≤
            (Nat.ceil (Real.exp (2 * Real.log 4 * ((2 * t + 2 : ℕ) : ℝ) ^ (t - 1))) : ℝ) :=
          Nat.le_ceil _
        have hle_n : Nat.ceil (Real.exp (2 * Real.log 4 * ((2 * t + 2 : ℕ) : ℝ) ^ (t - 1))) ≤ n :=
          le_trans (le_trans (le_max_right _ _) (Nat.le_succ _)) hn
        exact le_trans hc (by exact_mod_cast hle_n)
      have h2 := Real.log_le_log (Real.exp_pos _) h1
      simpa using h2
    have hlogn_pos : 0 < Real.log (n : ℝ) := by
      have : (0 : ℝ) < 2 * Real.log 4 * ((2 * t + 2 : ℕ) : ℝ) ^ (t - 1) := by positivity
      linarith
    -- Define x = (log n / (2 * log 4))^(1/(t-1)), m = ⌊x / 2⌋ - 1
    let x : ℝ := (Real.log (n : ℝ) / (2 * Real.log 4)) ^ ((1 : ℝ) / ((t : ℝ) - 1))
    have hx_ge : ((2 * t + 2 : ℕ) : ℝ) ≤ x := by
      have hdiv : ((2 * t + 2 : ℕ) : ℝ) ^ (t - 1) ≤ Real.log (n : ℝ) / (2 * Real.log 4) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      have hrpow := Real.rpow_le_rpow (by positivity) hdiv (by positivity : (0 : ℝ) ≤ 1 / ((t : ℝ) - 1))
      have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]
      have hL : (((2 * t + 2 : ℕ) : ℝ) ^ (t - 1)) ^ ((1 : ℝ) / ((t : ℝ) - 1)) =
          ((2 * t + 2 : ℕ) : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hcast,
          mul_one_div_cancel (ne_of_gt ht1_pos), Real.rpow_one]
      rwa [hL] at hrpow
    let m : ℕ := Nat.floor (x / 2) - 1
    have htm : t ≤ m := by
      have hfl : t + 1 ≤ Nat.floor (x / 2) := by
        rw [Nat.le_floor_iff (by positivity)]
        push_cast at hx_ge ⊢
        linarith
      omega
    have hm1 : 1 ≤ m := by omega
    -- Show (m + 1)^(t - 1) ≤ (x / 2)^(t - 1) = log n / (2 * log 4) / 2^(t - 1)
    have hm1_le_x2 : ((m + 1 : ℕ) : ℝ) ≤ x / 2 := by
      have hfl_ge1 : 1 ≤ Nat.floor (x / 2) := by omega
      have hsub : m + 1 = Nat.floor (x / 2) := by omega
      rw [hsub]
      exact Nat.floor_le (by positivity)
    have hpow_le_log : ((m + 1 : ℕ) : ℝ) ^ (t - 1) * Real.log 4 ≤ Real.log (n : ℝ) / 2 := by
      have hx_pow : x ^ (t - 1) = Real.log (n : ℝ) / (2 * Real.log 4) := by
        dsimp only [x]
        have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hcast,
          one_div_mul_cancel (ne_of_gt ht1_pos), Real.rpow_one]
      have h1 : ((m + 1 : ℕ) : ℝ) ^ (t - 1) ≤ (x / 2) ^ (t - 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hm1_le_x2 (t - 1)
      have h2 : (x / 2) ^ (t - 1) ≤ x ^ (t - 1) := by
        rw [div_pow]
        exact div_le_self (by positivity) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      have h3 : ((m + 1 : ℕ) : ℝ) ^ (t - 1) ≤ Real.log (n : ℝ) / (2 * Real.log 4) :=
        le_trans (le_trans h1 h2) (le_of_eq hx_pow)
      have h4 := mul_le_mul_of_nonneg_right h3 (le_of_lt hlog4_pos)
      have hrhs : Real.log (n : ℝ) / (2 * Real.log 4) * Real.log 4 = Real.log (n : ℝ) / 2 := by
        field_simp [ne_of_gt hlog4_pos]
      linarith
    -- Check 2 * m * 4 ^ ((m + 1) ^ (t - 1)) ≤ n / t
    -- Note 4 ^ ((m + 1)^(t - 1)) ≤ √n, and 2 * t * (2 * m + 1) ≤ √n?
    -- Actually, check directly: log(2 * t * (2 * m + 1)) + (m+1)^(t-1) * log 4 ≤ log n!
    -- Even simpler: (2 * m + 1) ≤ 4 ^ (m + 1) and t ≤ 4 ^ t ≤ 4 ^ (m + 1),
    -- so 2 * t * (2 * m + 1) ≤ 4 ^ (2 * m + 2) ≤ 4 ^ ((m + 1)^(t - 1) ... wait for t = 2: (m+1)^1 = m+1!).
    -- For ALL t ≥ 2: use (m + 1) ≤ x / 2 ⇒ 4 ^ ((m + 1)^(t-1)) ≤ √n, AND check 2 * m * t ≤ n / (2 * √n) = √n / 2!
    -- Wait: when t = 2, (m + 1) ≤ log n / (4 * log 4), so 4^(m + 1) ≤ n^(1/4) and 2*t*(2*m) ≤ 4*m^2 ≤ 4^(m+1) ≤ n^(1/4) ⇒ product ≤ n^(1/2) ≤ n!
    -- Let's check for ALL t ≥ 2:
    -- Since m + 1 ≤ x / 2, we have (m + 1)^(t - 1) ≤ (x / 2)^(t - 1) = x^(t-1) / 2^(t-1) ≤ x^(t-1) / 2 = log n / (4 * log 4)!!
    -- YES!! Because 2^(t - 1) ≥ 2 for ALL t ≥ 2, we get (m + 1)^(t - 1) * log 4 ≤ log n / 4 (NOT / 2)!!
    have hpow_le_log4 : ((m + 1 : ℕ) : ℝ) ^ (t - 1) * Real.log 4 ≤ Real.log (n : ℝ) / 4 := by
      have hx_pow : x ^ (t - 1) = Real.log (n : ℝ) / (2 * Real.log 4) := by
        dsimp only [x]
        have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hcast,
          one_div_mul_cancel (ne_of_gt ht1_pos), Real.rpow_one]
      have h1 : ((m + 1 : ℕ) : ℝ) ^ (t - 1) ≤ (x / 2) ^ (t - 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hm1_le_x2 (t - 1)
      have h2pow : (2 : ℝ) ≤ (2 : ℝ) ^ (t - 1) := by
        calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
        _ ≤ (2 : ℝ) ^ (t - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : (x / 2) ^ (t - 1) ≤ x ^ (t - 1) / 2 := by
        rw [div_pow]
        exact div_le_div_of_nonneg_left (by positivity) (by norm_num) h2pow
      have h3 : ((m + 1 : ℕ) : ℝ) ^ (t - 1) ≤ Real.log (n : ℝ) / (4 * Real.log 4) := by
        have hstep := le_trans h1 h2
        rw [hx_pow] at hstep
        have hdiv_eq : Real.log (n : ℝ) / (2 * Real.log 4) / 2 = Real.log (n : ℝ) / (4 * Real.log 4) := by
          ring
        linarith
      have h4 := mul_le_mul_of_nonneg_right h3 (le_of_lt hlog4_pos)
      have hrhs : Real.log (n : ℝ) / (4 * Real.log 4) * Real.log 4 = Real.log (n : ℝ) / 4 := by
        field_simp [ne_of_gt hlog4_pos]
      linarith
    have h4pow_le : (4 : ℝ) ^ ((m + 1) ^ (t - 1)) ≤ Real.exp (Real.log (n : ℝ) / 4) := by
      have h4exp : (4 : ℝ) ^ ((m + 1) ^ (t - 1)) =
          Real.exp (((m + 1 : ℕ) : ℝ) ^ (t - 1) * Real.log 4) := by
        rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4), ← Nat.cast_pow,
          Real.rpow_natCast]
      rw [h4exp]
      exact Real.exp_le_exp.mpr hpow_le_log4
    -- Also 4 * t * m ≤ 4 * m^2 ≤ 4^(2*m) ≤ 4^(2*(m+1)^(t-1)) ≤ exp(log n / 2)
    have h4tm_le : 4 * (t : ℝ) * (m : ℝ) ≤ Real.exp (Real.log (n : ℝ) / 2) := by
      have hnat : 4 * t * m ≤ 4 ^ (2 * (m + 1) ^ (t - 1)) := by
        have h1 : t ≤ m := htm
        have h2 : 4 * t * m ≤ 4 * (m + 1) ^ 2 := by nlinarith
        have h3 : m + 1 ≤ 2 ^ (m + 1) := le_of_lt Nat.lt_two_pow_self
        have h4 : (m + 1) ^ 2 ≤ (2 ^ (m + 1)) ^ 2 := Nat.pow_le_pow_left h3 2
        have h5 : (2 ^ (m + 1)) ^ 2 = 4 ^ (m + 1) := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        have h6 : 4 * (m + 1) ^ 2 ≤ 4 ^ (m + 1 + 1) :=
          calc
            4 * (m + 1) ^ 2 ≤ 4 * (2 ^ (m + 1)) ^ 2 := Nat.mul_le_mul_left 4 h4
            _ = 4 * 4 ^ (m + 1) := by rw [h5]
            _ = 4 ^ (m + 1 + 1) := (pow_succ' 4 (m + 1)).symm
        have h7 : m + 1 + 1 ≤ 2 * (m + 1) ^ (t - 1) := by
          have hp : m + 1 ≤ (m + 1) ^ (t - 1) :=
            Nat.le_self_pow (by omega : t - 1 ≠ 0) (m + 1)
          omega
        exact le_trans (le_trans h2 h6) (Nat.pow_le_pow_right (by norm_num) h7)
      have hr : 4 * (t : ℝ) * (m : ℝ) ≤ (4 : ℝ) ^ (2 * (m + 1) ^ (t - 1)) := by
        exact_mod_cast hnat
      have hsq : (4 : ℝ) ^ (2 * (m + 1) ^ (t - 1)) = ((4 : ℝ) ^ ((m + 1) ^ (t - 1))) ^ 2 := by
        rw [mul_comm, pow_mul]
      rw [hsq] at hr
      have hsq_le : ((4 : ℝ) ^ ((m + 1) ^ (t - 1))) ^ 2 ≤ (Real.exp (Real.log (n : ℝ) / 4)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h4pow_le 2
      have hexp2 : (Real.exp (Real.log (n : ℝ) / 4)) ^ 2 = Real.exp (Real.log (n : ℝ) / 2) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      linarith
    -- Now combine to get 2 * m ≤ (1 / 4) ^ ((m + 1) ^ (t - 1)) * (n / t)
    have hlb_erdos : 2 * (m : ℝ) ≤ (1 / 4 : ℝ) ^ ((m + 1) ^ (t - 1)) * ((n / t : ℕ) : ℝ) := by
      have hdiv_ge : (n : ℝ) / (2 * (t : ℝ)) ≤ ((n / t : ℕ) : ℝ) := by
        have h1 : n ≤ (n / t + 1) * t := by
          have := Nat.lt_mul_div_succ n (by omega : 0 < t)
          linarith
        have h2 : 1 ≤ n / t := Nat.div_pos hnt (by omega)
        have h3 : n ≤ 2 * (n / t) * t := by nlinarith
        have h3r : (n : ℝ) ≤ 2 * ((n / t : ℕ) : ℝ) * (t : ℝ) := by exact_mod_cast h3
        rw [div_le_iff₀ (by positivity)]
        linarith
      have hprod : 4 * (t : ℝ) * (m : ℝ) * (4 : ℝ) ^ ((m + 1) ^ (t - 1)) ≤ (n : ℝ) := by
        have h1 : 4 * (t : ℝ) * (m : ℝ) * (4 : ℝ) ^ ((m + 1) ^ (t - 1)) ≤
            Real.exp (Real.log (n : ℝ) / 2) * Real.exp (Real.log (n : ℝ) / 4) :=
          mul_le_mul h4tm_le h4pow_le (by positivity) (le_of_lt (Real.exp_pos _))
        have h2 : Real.exp (Real.log (n : ℝ) / 2) * Real.exp (Real.log (n : ℝ) / 4) =
            Real.exp (3 * Real.log (n : ℝ) / 4) := by
          rw [← Real.exp_add]; congr 1; ring
        have h3 : Real.exp (3 * Real.log (n : ℝ) / 4) ≤ Real.exp (Real.log (n : ℝ)) :=
          Real.exp_le_exp.mpr (by linarith)
        rw [Real.exp_log (by exact_mod_cast hn_pos)] at h3
        linarith
      have hinv : (1 / 4 : ℝ) ^ ((m + 1) ^ (t - 1)) = ((4 : ℝ) ^ ((m + 1) ^ (t - 1)))⁻¹ := by
        rw [one_div, inv_pow]
      rw [hinv, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
      have hstep : 2 * (m : ℝ) * (4 : ℝ) ^ ((m + 1) ^ (t - 1)) ≤ (n : ℝ) / (2 * (t : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      exact le_trans hstep hdiv_ge
    -- Apply Erdős (1964) + Inclusion-Exclusion Discrepancy to prove m < F n t α!
    have hm_lt_F : m < F n t α := by
      apply lt_F_of_every_coloring_has_bad
      intro c
      obtain ⟨b₀, U, hUcard, hUdisj, hUcross⟩ :=
        erdos1964_mono_multipartite ht hm1 hnt c hlb_erdos
      obtain ⟨X, hXm, b, hb⟩ :=
        inclusion_exclusion_discrepancy ht htm U hUcard hUdisj c b₀ hUcross hα_gt
      exact ⟨X, hXm, b, Or.inr hb⟩
    -- Relate (log n)^{1/(t-1)} to m + 1 ≤ F n t α
    have hx_le_4m1 : x ≤ 4 * ((m + 1 : ℕ) : ℝ) := by
      have hfl_gt : x / 2 - 1 < (Nat.floor (x / 2) : ℝ) := Nat.sub_one_lt_floor (x / 2)
      have hsub : m + 1 = Nat.floor (x / 2) := by omega
      have hx_ge4 : (4 : ℝ) ≤ x := by
        have : (4 : ℝ) ≤ ((2 * t + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ 2 * t + 2)
        linarith
      rw [hsub]
      linarith
    have hlog_rpow_eq : (Real.log (n : ℝ)) ^ ((1 : ℝ) / ((t : ℝ) - 1)) =
        (2 * Real.log 4) ^ ((1 : ℝ) / ((t : ℝ) - 1)) * x := by
      dsimp only [x]
      rw [Real.div_rpow (le_of_lt hlogn_pos) (by positivity)]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 2 * Real.log 4) _)]
    have hm1_le_F : ((m + 1 : ℕ) : ℝ) ≤ (F n t α : ℝ) := by exact_mod_cast hm_lt_F
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hlogn_pos) _),
      Real.norm_of_nonneg (Nat.cast_nonneg _), hlog_rpow_eq]
    dsimp only [C_lb]
    calc
      (2 * Real.log 4) ^ ((1 : ℝ) / ((t : ℝ) - 1)) * x
          ≤ (2 * Real.log 4) ^ ((1 : ℝ) / ((t : ℝ) - 1)) * (4 * ((m + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hx_le_4m1 (by positivity)
      _ ≤ (2 * Real.log 4) ^ ((1 : ℝ) / ((t : ℝ) - 1)) * (4 * (F n t α : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm1_le_F (by norm_num)) (by positivity)
      _ = (2 * Real.log 4) ^ ((1 : ℝ) / ((t : ℝ) - 1)) * 4 * (F n t α : ℝ) := by ring

/-- **General `t ≥ 2` (and `t ≥ 4`) High-Density Collapse Theorem:**
For every `t ≥ 2` and all `α, β ∈ (α_IE(t), 1/2)` (where
`α_IE(t) = 1/2 - t! / (2 * ∑_{r=1}^t (t.choose r) * r^t)`),
`F^{(t)}(n, α) =Θ[atTop] F^{(t)}(n, β)`. -/
theorem ppl063_general_t_high_density_collapse {t : ℕ} (ht : 2 ≤ t) {α β : ℝ}
    (hα_gt : 1 / 2 - (t.factorial : ℝ) /
      (2 * ∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t) < α)
    (hα_lt : α < 1 / 2)
    (hβ_gt : 1 / 2 - (t.factorial : ℝ) /
      (2 * ∑ r ∈ Finset.Icc 1 t, (t.choose r : ℝ) * (r : ℝ) ^ t) < β)
    (hβ_lt : β < 1 / 2) :
    (fun n : ℕ => ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        α * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)} : ℕ) : ℝ))
      =Θ[atTop]
    (fun n : ℕ => ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard t).filter (fun e => c e = b)).card ∧
        β * (X.card.choose t : ℝ) ≤
          (((X.powersetCard t).filter (fun e => c e = b)).card : ℝ)} : ℕ) : ℝ)) :=
  (ppl063_general_t_high_density_isTheta ht hα_gt hα_lt).trans
    (ppl063_general_t_high_density_isTheta ht hβ_gt hβ_lt).symm

/-- Explicit evaluation of `α_IE(4) = 41 / 85`. -/
private lemma alpha_IE_four :
    (1 / 2 : ℝ) - ((4 : ℕ).factorial : ℝ) /
      (2 * ∑ r ∈ Finset.Icc 1 4, ((4 : ℕ).choose r : ℝ) * (r : ℝ) ^ 4) = 41 / 85 := by
  have hsum : ∑ r ∈ Finset.Icc 1 4, ((4 : ℕ).choose r : ℝ) * (r : ℝ) ^ 4 = 680 := by
    have hIcc : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
    rw [hIcc]
    norm_num [Nat.choose]
  rw [hsum]
  norm_num [Nat.factorial]

/-- **Explicit `t = 4` High-Density Collapse Theorem (`α, β ∈ (41 / 85, 1 / 2)`):**
For all `α ∈ (41 / 85, 1 / 2)`, `F^{(4)}(n, α) =Θ[atTop] (log n)^{1/3}`, and for all
`α, β ∈ (41 / 85, 1 / 2)`, `F^{(4)}(n, α) =Θ[atTop] F^{(4)}(n, β)`. -/
theorem ppl063_t4_high_density_isTheta {α : ℝ} (hα_gt : 41 / 85 < α) (hα_lt : α < 1 / 2) :
    (fun n : ℕ => ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard 4).filter (fun e => c e = b)).card ∧
        α * (X.card.choose 4 : ℝ) ≤
          (((X.powersetCard 4).filter (fun e => c e = b)).card : ℝ)} : ℕ) : ℝ))
      =Θ[atTop] (fun n : ℕ => (Real.log (n : ℝ)) ^ ((1 : ℝ) / 3)) := by
  have h := ppl063_general_t_high_density_isTheta (t := 4) (by omega)
    (by rw [alpha_IE_four]; exact hα_gt) hα_lt
  have heq : (fun n : ℕ => (Real.log (n : ℝ)) ^ ((1 : ℝ) / (((4 : ℕ) : ℝ) - 1))) =
      (fun n : ℕ => (Real.log (n : ℝ)) ^ ((1 : ℝ) / 3)) := by
    funext n; congr 1; norm_num
  rwa [heq] at h

theorem ppl063_t4_high_density_collapse {α β : ℝ}
    (hα_gt : 41 / 85 < α) (hα_lt : α < 1 / 2) (hβ_gt : 41 / 85 < β) (hβ_lt : β < 1 / 2) :
    (fun n : ℕ => ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard 4).filter (fun e => c e = b)).card ∧
        α * (X.card.choose 4 : ℝ) ≤
          (((X.powersetCard 4).filter (fun e => c e = b)).card : ℝ)} : ℕ) : ℝ))
      =Θ[atTop]
    (fun n : ℕ => ((sInf {m : ℕ | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool,
        0 < ((X.powersetCard 4).filter (fun e => c e = b)).card ∧
        β * (X.card.choose 4 : ℝ) ≤
          (((X.powersetCard 4).filter (fun e => c e = b)).card : ℝ)} : ℕ) : ℝ)) :=
  (ppl063_t4_high_density_isTheta hα_gt hα_lt).trans
    (ppl063_t4_high_density_isTheta hβ_gt hβ_lt).symm

end PPL063
