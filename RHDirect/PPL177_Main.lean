/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

/-!
# PPL 177 (Erdős Problem #78): Constructive Lower Bounds for Diagonal Ramsey Numbers

## Honest Scope & Literature Status
**Erdős Problem #78 ($100 prize, VERIFIED OPEN)** asks for an explicit (polynomial-time)
construction of a graph on `n` vertices with no clique and no independent set of size
`≥ c log n` (equivalently, a constructive proof that `R(k, k) > C^k` for some `C > 1`).

**This file does NOT claim to solve the open $100 Erdős Problem #78.** The best known explicit
construction to date is Xin Li (FOCS 2023, `arXiv:2303.06802`), achieving `(log n)^C`-Ramsey
graphs (`R(k) > 2^{k^{1/C}}`) via asymptotically optimal `O(log n)`-entropy two-source extractors.

Instead, this file provides a complete, self-contained, pure-Mathlib formalization (`0` `sorry`,
`0` `native_decide`, `0` custom definitions in any public theorem signature) of:
1. **Classical Erdős–Szekeres (1935) Ramsey Upper Bounds** (`R(s, t) ≤ (s + t - 2).choose (s - 1)`
   and `R(k, k) ≤ (2k - 2).choose (k - 1) ≤ 4^{k - 1}`).
2. **Erdős (1947) Non-Constructive Exponential Lower Bound** (`R(k, k) > 2^{k/2}` for all `k ≥ 3`).
3. **Explicit Elementary Constructions** (Turán `(s - 1)(t - 1)` and Nagy 1972 `(k - 1).choose 3`).
4. **Unified Frankl–Wilson Uniform Intersection Theorem** (over any field `K`, yielding both
   Ray-Chaudhuri–Wilson over `ℚ` and modular Frankl–Wilson over `ZMod p`) and **Explicit
   Superpolynomial Ramsey Graphs** (`(p^3).choose (p^2 - 1)` vertices avoiding homogeneous sets of
   size `(p^3).choose (p - 1) + 1`, beating every polynomial degree `d`).
5. **Sharp Small-`k` Explicit Paley Constructions** (`P(5)` for `R(3, 3) > 5` and `P(17)` for
   `R(4, 4) > 17`, proved algebraically without `native_decide`).
6. **Formalized Structural Barrier Theorems** (finite-field adjacency rank barrier
   `α(G) * p^{rank} ≥ N` and two-source disperser equivalence + information-theoretic min-entropy
   barrier `N ≥ K * (2K).choose K`).
-/

namespace PPL177

open scoped BigOperators

/-! ### Part 1: Classical Erdős–Szekeres (1935) Ramsey Upper Bounds -/

private lemma isNClique_compl_iff_isNIndepSet {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (S : Finset V) : Gᶜ.IsNClique k S ↔ G.IsNIndepSet k S := by
  simp only [SimpleGraph.isNClique_iff, SimpleGraph.isNIndepSet_iff, SimpleGraph.isClique_iff,
    SimpleGraph.isIndepSet_iff, Set.Pairwise, SimpleGraph.compl_adj]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun x hx y hy hxy => (h1 hx hy hxy).2, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun x hx y hy hxy => ⟨hxy, h1 hx hy hxy⟩, h2⟩

private lemma ramsey_upper_aux :
    ∀ n : ℕ, ∀ s t : ℕ, s + t = n → 1 ≤ s → 1 ≤ t →
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
    (s + t - 2).choose (s - 1) ≤ Fintype.card V →
    ¬ (G.CliqueFree s ∧ Gᶜ.CliqueFree t) := by
  intro n
  induction n with
  | zero =>
    intro s t hst hs _
    omega
  | succ n ih =>
    intro s t hst hs ht V _ G hcard hfree
    classical
    rcases hfree with ⟨hG, hGc⟩
    by_cases hs1 : s = 1
    · subst hs1
      have h1 : (1 + t - 2).choose (1 - 1) = 1 := Nat.choose_zero_right _
      have hpos : 0 < Fintype.card V := by omega
      have : Nonempty V := Fintype.card_pos_iff.mp hpos
      obtain ⟨v⟩ := this
      exact hG {v} (by simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff])
    · by_cases ht1 : t = 1
      · subst ht1
        have h1 : s + 1 - 2 = s - 1 := by omega
        rw [h1, Nat.choose_self] at hcard
        have hpos : 0 < Fintype.card V := by omega
        have : Nonempty V := Fintype.card_pos_iff.mp hpos
        obtain ⟨v⟩ := this
        exact hGc {v} (by simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff])
      · have hs2 : 2 ≤ s := by omega
        have ht2 : 2 ≤ t := by omega
        set a := ((s - 1) + t - 2).choose ((s - 1) - 1)
        set b := (s + (t - 1) - 2).choose (s - 1)
        have hpascal : (s + t - 2).choose (s - 1) = a + b := by
          have h1 : s + t - 2 = (s + t - 3) + 1 := by omega
          have h2 : s - 1 = (s - 2) + 1 := by omega
          have ha_eq : a = (s + t - 3).choose (s - 2) := by
            simp only [a]
            rw [show s - 1 + t - 2 = s + t - 3 by omega, show s - 1 - 1 = s - 2 by omega]
          have hb_eq : b = (s + t - 3).choose ((s - 2) + 1) := by
            simp only [b]
            rw [show s + (t - 1) - 2 = s + t - 3 by omega, show s - 1 = s - 2 + 1 by omega]
          rw [h1, h2, Nat.choose_succ_succ, ← ha_eq, ← hb_eq]
        have ha_pos : 1 ≤ a := Nat.choose_pos (by omega)
        have hb_pos : 1 ≤ b := Nat.choose_pos (by omega)
        have hVpos : 0 < Fintype.card V := by omega
        have : Nonempty V := Fintype.card_pos_iff.mp hVpos
        obtain ⟨v₀⟩ := this
        let rest : Finset V := Finset.univ.erase v₀
        let N₁ : Finset V := rest.filter (fun u => G.Adj v₀ u)
        let N₂ : Finset V := rest.filter (fun u => ¬ G.Adj v₀ u)
        have hrest_card : rest.card = Fintype.card V - 1 := by
          simp [rest, Finset.card_erase_of_mem]
        have hpart : N₁.card + N₂.card = rest.card := by
          simpa [N₁, N₂] using Finset.card_filter_add_card_filter_not (s := rest)
            (p := fun u => G.Adj v₀ u)
        have hsplit : a ≤ N₁.card ∨ b ≤ N₂.card := by omega
        rcases hsplit with hN₁ | hN₂
        · let H := G.induce (N₁ : Set V)
          have hcardH : a ≤ Fintype.card ↥(N₁ : Set V) := by
            have heq : Fintype.card ↥(N₁ : Set V) = N₁.card := Fintype.card_coe N₁
            omega
          have hcontra := ih (s - 1) t (by omega) (by omega) ht H hcardH
          apply hcontra
          refine ⟨?_, ?_⟩
          · intro S hS
            let S' : Finset V := S.map ⟨Subtype.val, Subtype.val_injective⟩
            have hv₀_not : v₀ ∉ S' := by
              intro hv
              rw [Finset.mem_map] at hv
              rcases hv with ⟨⟨u, hu⟩, _, hval⟩
              have hu' : u ∈ rest := (Finset.mem_filter.mp hu).1
              exact (Finset.mem_erase.mp hu').1 hval
            have hclique : G.IsNClique s (insert v₀ S') := by
              rw [SimpleGraph.isNClique_iff]
              refine ⟨?_, ?_⟩
              · intro x hx y hy hxy
                simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
                rcases hx with rfl | hx
                · rcases hy with rfl | hy
                  · exact (hxy rfl).elim
                  · rw [Finset.mem_coe, Finset.mem_map] at hy
                    rcases hy with ⟨⟨u, hu⟩, _, rfl⟩
                    exact (Finset.mem_filter.mp hu).2
                · rcases hy with rfl | hy
                  · rw [Finset.mem_coe, Finset.mem_map] at hx
                    rcases hx with ⟨⟨u, hu⟩, _, rfl⟩
                    exact (Finset.mem_filter.mp hu).2.symm
                  · rw [Finset.mem_coe, Finset.mem_map] at hx hy
                    rcases hx with ⟨x', hx', rfl⟩
                    rcases hy with ⟨y', hy', rfl⟩
                    have hne : x' ≠ y' := fun heq => hxy (congrArg Subtype.val heq)
                    exact hS.1 hx' hy' hne
              · rw [Finset.card_insert_of_notMem hv₀_not, Finset.card_map, hS.2]
                omega
            exact hG (insert v₀ S') hclique
          · intro S hS
            let S' : Finset V := S.map ⟨Subtype.val, Subtype.val_injective⟩
            have hclique : Gᶜ.IsNClique t S' := by
              rw [SimpleGraph.isNClique_iff]
              refine ⟨?_, ?_⟩
              · intro x hx y hy hxy
                rw [Finset.mem_coe, Finset.mem_map] at hx hy
                rcases hx with ⟨x', hx', rfl⟩
                rcases hy with ⟨y', hy', rfl⟩
                have hne : x' ≠ y' := fun heq => hxy (congrArg Subtype.val heq)
                have hadj := hS.1 hx' hy' hne
                rw [SimpleGraph.compl_adj] at hadj ⊢
                exact ⟨hxy, hadj.2⟩
              · rw [Finset.card_map, hS.2]
            exact hGc S' hclique
        · let H := G.induce (N₂ : Set V)
          have hcardH : b ≤ Fintype.card ↥(N₂ : Set V) := by
            have heq : Fintype.card ↥(N₂ : Set V) = N₂.card := Fintype.card_coe N₂
            omega
          have hcontra := ih s (t - 1) (by omega) hs (by omega) H hcardH
          apply hcontra
          refine ⟨?_, ?_⟩
          · intro S hS
            let S' : Finset V := S.map ⟨Subtype.val, Subtype.val_injective⟩
            have hclique : G.IsNClique s S' := by
              rw [SimpleGraph.isNClique_iff]
              refine ⟨?_, ?_⟩
              · intro x hx y hy hxy
                rw [Finset.mem_coe, Finset.mem_map] at hx hy
                rcases hx with ⟨x', hx', rfl⟩
                rcases hy with ⟨y', hy', rfl⟩
                have hne : x' ≠ y' := fun heq => hxy (congrArg Subtype.val heq)
                exact hS.1 hx' hy' hne
              · rw [Finset.card_map, hS.2]
            exact hG S' hclique
          · intro S hS
            let S' : Finset V := S.map ⟨Subtype.val, Subtype.val_injective⟩
            have hv₀_not : v₀ ∉ S' := by
              intro hv
              rw [Finset.mem_map] at hv
              rcases hv with ⟨⟨u, hu⟩, _, hval⟩
              have hu' : u ∈ rest := (Finset.mem_filter.mp hu).1
              exact (Finset.mem_erase.mp hu').1 hval
            have hclique : Gᶜ.IsNClique t (insert v₀ S') := by
              rw [SimpleGraph.isNClique_iff]
              refine ⟨?_, ?_⟩
              · intro x hx y hy hxy
                simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
                rcases hx with rfl | hx
                · rcases hy with rfl | hy
                  · exact (hxy rfl).elim
                  · rw [Finset.mem_coe, Finset.mem_map] at hy
                    rcases hy with ⟨⟨u, hu⟩, _, rfl⟩
                    rw [SimpleGraph.compl_adj]
                    exact ⟨hxy, (Finset.mem_filter.mp hu).2⟩
                · rcases hy with rfl | hy
                  · rw [Finset.mem_coe, Finset.mem_map] at hx
                    rcases hx with ⟨⟨u, hu⟩, _, rfl⟩
                    rw [SimpleGraph.compl_adj]
                    exact ⟨hxy, fun h => (Finset.mem_filter.mp hu).2 h.symm⟩
                  · rw [Finset.mem_coe, Finset.mem_map] at hx hy
                    rcases hx with ⟨x', hx', rfl⟩
                    rcases hy with ⟨y', hy', rfl⟩
                    have hne : x' ≠ y' := fun heq => hxy (congrArg Subtype.val heq)
                    have hadj := hS.1 hx' hy' hne
                    rw [SimpleGraph.compl_adj] at hadj ⊢
                    exact ⟨hxy, hadj.2⟩
              · rw [Finset.card_insert_of_notMem hv₀_not, Finset.card_map, hS.2]
                omega
            exact hGc (insert v₀ S') hclique

/-- **Erdős–Szekeres (1935) Off-Diagonal Ramsey Upper Bound**:
Every simple graph on `N ≥ (s + t - 2).choose (s - 1)` vertices contains either an `s`-clique
or a `t`-independent set (`¬ (G.CliqueFree s ∧ Gᶜ.CliqueFree t)`). -/
theorem ppl177_ramsey_upper_offdiag (s t N : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hN : (s + t - 2).choose (s - 1) ≤ N) (G : SimpleGraph (Fin N)) :
    ¬ (G.CliqueFree s ∧ Gᶜ.CliqueFree t) := by
  exact ramsey_upper_aux (s + t) s t rfl hs ht G (by simpa using hN)

/-- **Erdős–Szekeres (1935) Diagonal Ramsey Upper Bound**:
Every simple graph on `N ≥ (2k - 2).choose (k - 1)` vertices contains either a `k`-clique
or a `k`-independent set. -/
theorem ppl177_ramsey_upper_diag (k N : ℕ) (hk : 1 ≤ k)
    (hN : (2 * k - 2).choose (k - 1) ≤ N) (G : SimpleGraph (Fin N)) :
    ∃ S : Finset (Fin N), G.IsNClique k S ∨ G.IsNIndepSet k S := by
  have h := ppl177_ramsey_upper_offdiag k k N hk hk (by rwa [show k + k - 2 = 2 * k - 2 by omega]) G
  by_contra hall
  push Not at hall
  apply h
  refine ⟨?_, ?_⟩
  · intro S hS
    exact (hall S).1 hS
  · intro S hS
    exact (hall S).2 ((isNClique_compl_iff_isNIndepSet G k S).mp hS)

/-- **Exponential Upper Bound `R(k, k) ≤ 4^{k - 1}`**:
Every simple graph on `N ≥ 4 ^ (k - 1)` vertices has a `k`-clique or `k`-independent set. -/
theorem ppl177_ramsey_upper_four_pow (k N : ℕ) (hk : 1 ≤ k)
    (hN : 4 ^ (k - 1) ≤ N) (G : SimpleGraph (Fin N)) :
    ¬ (G.CliqueFree k ∧ Gᶜ.CliqueFree k) := by
  have hchoose : (2 * k - 2).choose (k - 1) ≤ 4 ^ (k - 1) := by
    have h1 : (2 * k - 2).choose (k - 1) ≤ 2 ^ (2 * k - 2) := by
      rw [← Nat.sum_range_choose (2 * k - 2)]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))
    have h2 : 2 ^ (2 * k - 2) = 4 ^ (k - 1) := by
      have heq : 2 * k - 2 = 2 * (k - 1) := by omega
      rw [heq, pow_mul]
      norm_num
    omega
  exact ppl177_ramsey_upper_offdiag k k N hk hk
    (by rw [show k + k - 2 = 2 * k - 2 by omega]; exact le_trans hchoose hN) G

/-! ### Part 2: Erdős (1947) Non-Constructive Exponential Lower Bound (`R(k, k) > 2^{k/2}`) -/

private abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

private def graphOfColoring {n : ℕ} (c : Edge n → Bool) : SimpleGraph (Fin n) where
  Adj u v := ∃ h : u ≠ v,
    (if hlt : u < v then c ⟨(u, v), hlt⟩
     else c ⟨(v, u), lt_of_le_of_ne (not_lt.mp hlt) h.symm⟩) = true
  symm := ⟨fun u v ⟨h, hc⟩ => by
    refine ⟨h.symm, ?_⟩
    by_cases hlt : u < v
    · have hnot : ¬ v < u := not_lt.mpr (le_of_lt hlt)
      simp only [hlt, ↓reduceDIte] at hc
      simp only [hnot, ↓reduceDIte, hc]
    · have hvlt : v < u := lt_of_le_of_ne (not_lt.mp hlt) h.symm
      simp only [hlt, ↓reduceDIte] at hc
      simp only [hvlt, ↓reduceDIte, hc]⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

private lemma graphOfColoring_adj_of_lt {n : ℕ} (c : Edge n → Bool) {u v : Fin n} (hlt : u < v) :
    (graphOfColoring c).Adj u v ↔ c ⟨(u, v), hlt⟩ = true := by
  constructor
  · rintro ⟨_, hc⟩
    simpa [hlt] using hc
  · intro hc
    exact ⟨ne_of_lt hlt, by simpa [hlt] using hc⟩

private lemma graphOfColoring_compl_adj_of_lt {n : ℕ} (c : Edge n → Bool) {u v : Fin n}
    (hlt : u < v) : (graphOfColoring c)ᶜ.Adj u v ↔ c ⟨(u, v), hlt⟩ = false := by
  rw [SimpleGraph.compl_adj, graphOfColoring_adj_of_lt c hlt]
  constructor
  · intro ⟨_, hne⟩
    cases h : c ⟨(u, v), hlt⟩ <;> simp_all
  · intro hf
    exact ⟨ne_of_lt hlt, by simp [hf]⟩

private lemma card_edgesIn {n : ℕ} (S : Finset (Fin n)) :
    (Finset.univ.filter (fun e : Edge n => e.1.1 ∈ S ∧ e.1.2 ∈ S)).card = S.card.choose 2 := by
  let f : Edge n → Finset (Fin n) := fun e => {e.1.1, e.1.2}
  have hf_inj : Set.InjOn f ↑(Finset.univ.filter (fun e : Edge n => e.1.1 ∈ S ∧ e.1.2 ∈ S)) := by
    intro e₁ _ e₂ _ heq
    have h1 : e₁.1.1 < e₁.1.2 := e₁.2
    have h2 : e₂.1.1 < e₂.1.2 := e₂.2
    have hpair : ({e₁.1.1, e₁.1.2} : Finset (Fin n)) = {e₂.1.1, e₂.1.2} := heq
    have hmem1 : e₁.1.1 ∈ ({e₂.1.1, e₂.1.2} : Finset (Fin n)) := by rw [← hpair]; simp
    have hmem2 : e₁.1.2 ∈ ({e₂.1.1, e₂.1.2} : Finset (Fin n)) := by rw [← hpair]; simp
    have hmem3 : e₂.1.1 ∈ ({e₁.1.1, e₁.1.2} : Finset (Fin n)) := by rw [hpair]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem1 hmem2 hmem3
    apply Subtype.ext
    ext
    · rcases hmem1 with h | h <;> rcases hmem3 with h' | h' <;> omega
    · rcases hmem1 with h | h <;> rcases hmem2 with h' | h' <;> omega
  have hf_img :
      (Finset.univ.filter (fun e : Edge n => e.1.1 ∈ S ∧ e.1.2 ∈ S)).image f =
      S.powersetCard 2 := by
    ext T
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powersetCard, f]
    constructor
    · rintro ⟨⟨⟨u, v⟩, huv⟩, ⟨hu, hv⟩, rfl⟩
      refine ⟨?_, Finset.card_pair (ne_of_lt huv)⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · rintro ⟨hsub, hcard⟩
      rw [Finset.card_eq_two] at hcard
      rcases hcard with ⟨a, b, hab, rfl⟩
      have ha : a ∈ S := hsub (by simp)
      have hb : b ∈ S := hsub (by simp)
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact ⟨⟨(a, b), hlt⟩, ⟨ha, hb⟩, rfl⟩
      · exact ⟨⟨(b, a), hgt⟩, ⟨hb, ha⟩, Finset.pair_comm b a⟩
  rw [← Finset.card_powersetCard, ← hf_img, Finset.card_image_of_injOn hf_inj]

private lemma card_edge (n : ℕ) : Fintype.card (Edge n) = n.choose 2 := by
  have h := card_edgesIn (Finset.univ : Finset (Fin n))
  simpa using h

private lemma card_badColorings {n : ℕ} (S : Finset (Fin n)) (b : Bool) :
    (Finset.univ.filter (fun c : Edge n → Bool =>
      ∀ e : Edge n, e.1.1 ∈ S → e.1.2 ∈ S → c e = b)).card =
    2 ^ (n.choose 2 - S.card.choose 2) := by
  classical
  let E_S : Finset (Edge n) := Finset.univ.filter (fun e => e.1.1 ∈ S ∧ e.1.2 ∈ S)
  let φ : ({e : Edge n // e ∉ E_S} → Bool) → (Edge n → Bool) :=
    fun g e => if h : e ∈ E_S then b else g ⟨e, h⟩
  have hφ_inj : Function.Injective φ := by
    intro g₁ g₂ h
    funext ⟨e, he⟩
    have h' := congrFun h e
    simpa [φ, he] using h'
  have hφ_img : Finset.univ.image φ =
      Finset.univ.filter (fun c : Edge n → Bool =>
        ∀ e : Edge n, e.1.1 ∈ S → e.1.2 ∈ S → c e = b) := by
    ext c
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨g, rfl⟩ e hu hv
      have he : e ∈ E_S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, hv⟩
      simp [φ, he]
    · intro hc
      refine ⟨fun ⟨e, _⟩ => c e, ?_⟩
      funext e
      by_cases he : e ∈ E_S
      · have hmem := (Finset.mem_filter.mp he).2
        simp [φ, he, hc e hmem.1 hmem.2]
      · simp [φ, he]
  rw [← hφ_img, Finset.card_image_of_injective _ hφ_inj, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_subtype_compl, card_edge, Fintype.card_coe]
  exact congrArg (fun x => 2 ^ (n.choose 2 - x)) (card_edgesIn S)

/-- **Erdős (1947) Counting Bound**:
Whenever `2 * n.choose k < 2 ^ (k.choose 2)`, there exists a simple graph on `Fin n` with no
`k`-clique and no `k`-independent set. -/
theorem ppl177_erdos_1947_counting (n k : ℕ) (h : 2 * n.choose k < 2 ^ (k.choose 2)) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  classical
  by_cases hkn : k ≤ n
  · let badS : Finset (Fin n) → Bool → Finset (Edge n → Bool) := fun S b =>
      Finset.univ.filter (fun c => ∀ e : Edge n, e.1.1 ∈ S → e.1.2 ∈ S → c e = b)
    let allBad : Finset (Edge n → Bool) :=
      ((Finset.univ : Finset (Fin n)).powersetCard k).biUnion (fun S =>
        badS S true ∪ badS S false)
    have hle_choose : k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hkn
    have hall_card : allBad.card ≤ 2 * n.choose k * 2 ^ (n.choose 2 - k.choose 2) := by
      calc allBad.card
          ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              (badS S true ∪ badS S false).card := Finset.card_biUnion_le
        _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              ((badS S true).card + (badS S false).card) := by
            apply Finset.sum_le_sum
            intro S _
            exact Finset.card_union_le _ _
        _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
            apply Finset.sum_congr rfl
            intro S hS
            have hSc : S.card = k := (Finset.mem_powersetCard.mp hS).2
            rw [card_badColorings S true, card_badColorings S false, hSc, two_mul]
        _ = n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
            simp [Finset.card_powersetCard]
        _ = 2 * n.choose k * 2 ^ (n.choose 2 - k.choose 2) := by ring
    have hlt_univ : allBad.card < (Finset.univ : Finset (Edge n → Bool)).card := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, card_edge]
      have hpow : 2 ^ (k.choose 2) * 2 ^ (n.choose 2 - k.choose 2) = 2 ^ (n.choose 2) := by
        rw [← pow_add, Nat.add_sub_cancel' hle_choose]
      calc allBad.card
          ≤ 2 * n.choose k * 2 ^ (n.choose 2 - k.choose 2) := hall_card
        _ < 2 ^ (k.choose 2) * 2 ^ (n.choose 2 - k.choose 2) :=
            Nat.mul_lt_mul_of_pos_right h (pow_pos (by decide) _)
        _ = 2 ^ (n.choose 2) := hpow
    have hne : (Finset.univ \ allBad).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have hsub : (Finset.univ : Finset (Edge n → Bool)) ⊆ allBad :=
        Finset.sdiff_eq_empty_iff_subset.mp hemp
      exact not_lt_of_ge (Finset.card_le_card hsub) hlt_univ
    obtain ⟨c, hc⟩ := hne
    have hc_not : c ∉ allBad := (Finset.mem_sdiff.mp hc).2
    refine ⟨graphOfColoring c, ?_, ?_⟩
    · intro S hS
      apply hc_not
      refine Finset.mem_biUnion.mpr ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS.2⟩,
        Finset.mem_union_left _ ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun e hu hv => ?_⟩
      exact (graphOfColoring_adj_of_lt c e.2).mp (hS.1 hu hv (ne_of_lt e.2))
    · intro S hS
      apply hc_not
      refine Finset.mem_biUnion.mpr ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS.2⟩,
        Finset.mem_union_right _ ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun e hu hv => ?_⟩
      exact (graphOfColoring_compl_adj_of_lt c e.2).mp (hS.1 hu hv (ne_of_lt e.2))
  · refine ⟨⊥, ?_, ?_⟩
    · intro S hS
      have hSc : S.card = k := hS.2
      have hle : S.card ≤ n := by simpa using Finset.card_le_univ S
      omega
    · intro S hS
      have hSc : S.card = k := hS.2
      have hle : S.card ≤ n := by simpa using Finset.card_le_univ S
      omega

private lemma four_mul_two_pow_lt_factorial_sq : ∀ k : ℕ, 3 ≤ k → 4 * 2 ^ k < (k.factorial) ^ 2 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ m hm ih =>
    rw [pow_succ, Nat.factorial_succ, mul_pow]
    have hm1 : 2 ≤ (m + 1) ^ 2 := by nlinarith
    calc 4 * (2 ^ m * 2) = (4 * 2 ^ m) * 2 := by ring
      _ < (m.factorial ^ 2) * 2 := Nat.mul_lt_mul_of_pos_right ih (by decide)
      _ ≤ (m.factorial ^ 2) * (m + 1) ^ 2 := Nat.mul_le_mul_left _ hm1
      _ = (m + 1) ^ 2 * m.factorial ^ 2 := by ring

/-- **Erdős (1947) Exponential Lower Bound (`R(k, k) > 2^{k/2}` for all `k ≥ 3`, integer form)**:
For every `k ≥ 3` and every `n` with `n ^ 2 ≤ 2 ^ k` (i.e. `n ≤ 2^{k/2}`), there exists a simple
graph on `Fin n` with no `k`-clique and no `k`-independent set. -/
theorem ppl177_erdos_1947_exp_lower (k n : ℕ) (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  apply ppl177_erdos_1947_counting n k
  have hcf : k.factorial * n.choose k ≤ n ^ k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n k
  have hsq : (k.factorial) ^ 2 * (2 * n.choose k) ^ 2 < (k.factorial) ^ 2 * (2 ^ (k.choose 2)) ^ 2 := by
    have h2c : 2 * k.choose 2 = k * (k - 1) := by
      rw [Nat.choose_two_right]
      exact Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd
    have hpow_eq : (2 ^ (k.choose 2)) ^ 2 = 2 ^ (k * (k - 1)) := by
      rw [← pow_mul, mul_comm, h2c]
    have hk_eq : k + k * (k - 1) = k * k := by
      cases k with
      | zero => omega
      | succ m =>
        simp only [Nat.add_sub_cancel]
        ring
    calc (k.factorial) ^ 2 * (2 * n.choose k) ^ 2
        = 4 * (k.factorial * n.choose k) ^ 2 := by ring
      _ ≤ 4 * (n ^ k) ^ 2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hcf 2)
      _ = 4 * (n ^ 2) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm k 2]
      _ ≤ 4 * (2 ^ k) ^ k := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hn k)
      _ = (4 * 2 ^ k) * 2 ^ (k * (k - 1)) := by
          rw [← pow_mul, ← hk_eq, pow_add, mul_assoc]
      _ < (k.factorial) ^ 2 * 2 ^ (k * (k - 1)) :=
          Nat.mul_lt_mul_of_pos_right (four_mul_two_pow_lt_factorial_sq k hk) (pow_pos (by decide) _)
      _ = (k.factorial) ^ 2 * (2 ^ (k.choose 2)) ^ 2 := by rw [hpow_eq]
  have hsq' : (2 * n.choose k) ^ 2 < (2 ^ (k.choose 2)) ^ 2 :=
    Nat.lt_of_mul_lt_mul_left hsq
  by_contra hle
  push Not at hle
  have hge := Nat.pow_le_pow_left hle 2
  omega

/-- **Erdős (1947) Exponential Lower Bound (Real `2^{k/2}` Form)**:
For every `k ≥ 3` and every `n : ℕ` with `(n : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) / 2)`, there exists a
simple graph on `Fin n` with no `k`-clique and no `k`-independent set. -/
theorem ppl177_erdos_1947_real_exp_lower (k n : ℕ) (hk : 3 ≤ k)
    (hn : (n : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) / 2)) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  apply ppl177_erdos_1947_exp_lower k n hk
  have hreal : ((n ^ 2 : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
    have h1 : ((n : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg n) hn 2
    have h2 : ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ (k : ℝ) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((k : ℝ) / 2)) 2,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring_nf
    rw [h2, Real.rpow_natCast] at h1
    simpa [Nat.cast_pow] using h1
  exact_mod_cast hreal

/-! ### Part 3: Explicit Elementary Polynomial Constructions (Turán) -/

/-- **Explicit Turán Disjoint-Cliques Off-Diagonal Lower Bound (`R(s, t) > (s - 1)(t - 1)`)**:
For all `s, t ≥ 1`, the explicit graph on `Fin ((s - 1) * (t - 1))` consisting of `t - 1` disjoint
cliques of size `s - 1` has no `s`-clique and no `t`-independent set. -/
theorem ppl177_turan_explicit (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    ∃ G : SimpleGraph (Fin ((s - 1) * (t - 1))), G.CliqueFree s ∧ Gᶜ.CliqueFree t := by
  let a := t - 1
  let b := s - 1
  let G : SimpleGraph (Fin ((s - 1) * (t - 1))) :=
    { Adj := fun u v => u ≠ v ∧ u.val / b = v.val / b
      symm := ⟨fun _ _ ⟨hne, heq⟩ => ⟨hne.symm, heq.symm⟩⟩
      loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩ }
  refine ⟨G, ?_, ?_⟩
  · intro S hS
    have hSc : S.card = s := hS.2
    by_cases hb : b = 0
    · have hcard0 : (s - 1) * (t - 1) = 0 := by simp [b] at hb; simp [hb]
      have hle : S.card ≤ 0 := by simpa [hcard0] using Finset.card_le_univ S
      omega
    · have hinj : Set.InjOn (fun u : Fin ((s - 1) * (t - 1)) => u.val % b) S := by
        intro x hx y hy hmod
        dsimp only at hmod
        by_contra hxy
        have hdiv : x.val / b = y.val / b := (hS.1 hx hy hxy).2
        have hval : x.val = y.val := by
          have hx' := Nat.div_add_mod x.val b
          have hy' := Nat.div_add_mod y.val b
          rw [hdiv, hmod] at hx'
          omega
        exact hxy (Fin.ext hval)
      have hsub : S.image (fun u : Fin ((s - 1) * (t - 1)) => u.val % b) ⊆ Finset.range b := by
        intro r hr
        rcases Finset.mem_image.mp hr with ⟨x, _, rfl⟩
        exact Finset.mem_range.mpr (Nat.mod_lt _ (Nat.pos_of_ne_zero hb))
      have hle : S.card ≤ b := by
        calc S.card
            = (S.image (fun u : Fin ((s - 1) * (t - 1)) => u.val % b)).card :=
                (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.range b).card := Finset.card_le_card hsub
          _ = b := Finset.card_range b
      omega
  · intro S hS
    have hSc : S.card = t := hS.2
    by_cases hb : b = 0
    · have hcard0 : (s - 1) * (t - 1) = 0 := by simp [b] at hb; simp [hb]
      have hle : S.card ≤ 0 := by simpa [hcard0] using Finset.card_le_univ S
      omega
    · have hinj : Set.InjOn (fun u : Fin ((s - 1) * (t - 1)) => u.val / b) S := by
        intro x hx y hy hdiv
        dsimp only at hdiv
        by_contra hxy
        have hadj := hS.1 hx hy hxy
        rw [SimpleGraph.compl_adj] at hadj
        exact hadj.2 ⟨hxy, hdiv⟩
      have hsub : S.image (fun u : Fin ((s - 1) * (t - 1)) => u.val / b) ⊆ Finset.range a := by
        intro q hq
        rcases Finset.mem_image.mp hq with ⟨x, _, rfl⟩
        exact Finset.mem_range.mpr (Nat.div_lt_of_lt_mul x.isLt)
      have hle : S.card ≤ a := by
        calc S.card
            = (S.image (fun u : Fin ((s - 1) * (t - 1)) => u.val / b)).card :=
                (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.range a).card := Finset.card_le_card hsub
          _ = a := Finset.card_range a
      omega

/-! ### Part 4: Unified Frankl–Wilson Uniform Intersection Theorem & Superpolynomial Ramsey Graphs -/

private def indFn (K : Type*) [Semiring K] {m : ℕ} (S : Finset (Fin m)) : Finset (Fin m) → K :=
  fun T => if S ⊆ T then 1 else 0

private lemma indFn_mul (K : Type*) [Semiring K] {m : ℕ} (S₁ S₂ : Finset (Fin m)) :
    (fun T => indFn K S₁ T * indFn K S₂ T) = indFn K (S₁ ∪ S₂) := by
  funext T
  by_cases h1 : S₁ ⊆ T <;> by_cases h2 : S₂ ⊆ T <;>
    simp [indFn, h1, h2, Finset.union_subset_iff]

private lemma indFn_empty (K : Type*) [Semiring K] {m : ℕ} :
    indFn K (∅ : Finset (Fin m)) = fun _ => 1 := by
  funext T
  simp [indFn]

private lemma card_inter_eq_sum_indFn (K : Type*) [CommRing K] {m : ℕ}
    (A T : Finset (Fin m)) : ((A ∩ T).card : K) = ∑ x ∈ A, indFn K {x} T := by
  simp only [indFn, Finset.singleton_subset_iff, Finset.sum_boole, Finset.filter_mem_eq_inter]

private def B_le (m d : ℕ) : Finset (Finset (Fin m)) :=
  Finset.univ.filter (fun S : Finset (Fin m) => S.card ≤ d)

private def B_lt (m d : ℕ) : Finset (Finset (Fin m)) :=
  Finset.univ.filter (fun S : Finset (Fin m) => S.card < d)

private def polySubspace (K : Type*) [Field K] (m d : ℕ) : Submodule K (Finset (Fin m) → K) :=
  Submodule.span K (Set.range (fun S : B_le m d => indFn K S.1))

private lemma indFn_mem_polySubspace (K : Type*) [Field K] {m d : ℕ}
    (S : Finset (Fin m)) (hS : S.card ≤ d) :
    indFn K S ∈ polySubspace K m d := by
  exact Submodule.subset_span ⟨⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩⟩, rfl⟩

private lemma polySubspace_mono (K : Type*) [Field K] {m d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    polySubspace K m d₁ ≤ polySubspace K m d₂ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  exact indFn_mem_polySubspace K S (le_trans (Finset.mem_filter.mp hS).2 h)

private lemma mul_indFn_singleton_mem_polySubspace (K : Type*) [Field K] {m r : ℕ}
    (f : Finset (Fin m) → K) (hf : f ∈ polySubspace K m r) (x : Fin m) :
    (fun T => f T * indFn K {x} T) ∈ polySubspace K m (r + 1) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨⟨S, hS⟩, rfl⟩
    rw [indFn_mul]
    apply indFn_mem_polySubspace
    have hcard : S.card ≤ r := (Finset.mem_filter.mp hS).2
    have hunion : (S ∪ {x}).card ≤ S.card + 1 := by
      calc (S ∪ {x}).card ≤ S.card + ({x} : Finset (Fin m)).card := Finset.card_union_le _ _
        _ = S.card + 1 := by simp
    dsimp only
    omega
  · convert (polySubspace K m (r + 1)).zero_mem using 1
    funext T
    simp
  · intro u v _ _ hu hv
    have heq : (fun T => (u + v) T * indFn K {x} T) =
        (fun T => u T * indFn K {x} T) + (fun T => v T * indFn K {x} T) := by
      funext T; simp [add_mul]
    rw [heq]
    exact (polySubspace K m (r + 1)).add_mem hu hv
  · intro c u _ hu
    have heq : (fun T => (c • u) T * indFn K {x} T) = c • (fun T => u T * indFn K {x} T) := by
      funext T; simp [mul_assoc]
    rw [heq]
    exact (polySubspace K m (r + 1)).smul_mem c hu

private def evalPoly (K : Type*) [CommRing K] {m : ℕ}
    (A : Finset (Fin m)) (L : Finset K) : Finset (Fin m) → K :=
  fun T => ∏ l ∈ L, (((A ∩ T).card : K) - l)

private lemma evalPoly_mem_polySubspace (K : Type*) [Field K] {m : ℕ}
    (A : Finset (Fin m)) (L : Finset K) :
    evalPoly K A L ∈ polySubspace K m L.card := by
  classical
  induction L using Finset.induction_on with
  | empty =>
    have heq : evalPoly K A ∅ = indFn K (∅ : Finset (Fin m)) := by
      funext T; simp [evalPoly, indFn]
    rw [heq, Finset.card_empty]
    exact indFn_mem_polySubspace K ∅ (le_refl 0)
  | insert a L ha ih =>
    rw [Finset.card_insert_of_notMem ha]
    have heq : evalPoly K A (insert a L) =
        (∑ x ∈ A, (fun T => evalPoly K A L T * indFn K {x} T)) - a • evalPoly K A L := by
      funext T
      simp only [evalPoly, Finset.prod_insert ha, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_apply, card_inter_eq_sum_indFn K A T]
      rw [sub_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [heq]
    apply (polySubspace K m (L.card + 1)).sub_mem
    · apply (polySubspace K m (L.card + 1)).sum_mem
      intro x _
      exact mul_indFn_singleton_mem_polySubspace K _ ih x
    · exact (polySubspace K m (L.card + 1)).smul_mem a
        (polySubspace_mono K (Nat.le_succ _) ih)

private def auxPoly (K : Type*) [CommRing K] {m : ℕ} (k : ℕ) (I : Finset (Fin m)) :
    Finset (Fin m) → K :=
  fun T => ((T.card : K) - (k : K)) * indFn K I T

private lemma auxPoly_mem_polySubspace (K : Type*) [Field K] {m k s : ℕ}
    (I : Finset (Fin m)) (hI : I.card < s) :
    auxPoly K k I ∈ polySubspace K m s := by
  have heq : auxPoly K k I =
      (∑ x : Fin m, (fun T => indFn K I T * indFn K {x} T)) - (k : K) • indFn K I := by
    funext T
    have hT : (T.card : K) = ∑ x : Fin m, indFn K {x} T := by
      have h := card_inter_eq_sum_indFn K (Finset.univ : Finset (Fin m)) T
      simpa using h
    simp only [auxPoly, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, hT]
    rw [sub_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq]
  apply (polySubspace K m s).sub_mem
  · apply (polySubspace K m s).sum_mem
    intro x _
    have hmem := mul_indFn_singleton_mem_polySubspace K (indFn K I)
      (indFn_mem_polySubspace K I (le_refl I.card)) x
    exact polySubspace_mono K (by omega) hmem
  · exact (polySubspace K m s).smul_mem (k : K)
      (indFn_mem_polySubspace K I (by omega))

private lemma finrank_polySubspace_le (K : Type*) [Field K] (m d : ℕ) :
    Module.finrank K (polySubspace K m d) ≤ (B_le m d).card := by
  let f : (B_le m d → K) →ₗ[K] (Finset (Fin m) → K) :=
    Fintype.linearCombination K (fun S : B_le m d => indFn K S.1)
  have hrange : LinearMap.range f = polySubspace K m d := by
    simp [f, polySubspace, Fintype.range_linearCombination]
  rw [← hrange]
  calc Module.finrank K (LinearMap.range f)
      ≤ Module.finrank K (B_le m d → K) := LinearMap.finrank_range_le f
    _ = Fintype.card (B_le m d) := Module.finrank_fintype_fun_eq_card K
    _ = (B_le m d).card := Fintype.card_coe _

private lemma card_B_le_eq_add_choose (m s : ℕ) :
    (B_le m s).card = (B_lt m s).card + m.choose s := by
  have hunion : B_le m s = B_lt m s ∪ (Finset.univ : Finset (Fin m)).powersetCard s := by
    ext S
    simp only [B_le, B_lt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_powersetCard, Finset.subset_univ]
    omega
  have hdisj : Disjoint (B_lt m s) ((Finset.univ : Finset (Fin m)).powersetCard s) := by
    rw [Finset.disjoint_left]
    intro S h1 h2
    have hc1 : S.card < s := (Finset.mem_filter.mp h1).2
    have hc2 : S.card = s := (Finset.mem_powersetCard.mp h2).2
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin]

/-- **Unified Frankl–Wilson Uniform Intersection Theorem (over any field `K`)**:
Let `K` be any field, `m, k, s : ℕ`, and `L : Finset K` with `L.card ≤ s`, `(k : K) ∉ L`, and
`(i : K) ≠ (k : K)` for all `i < s`. If `F` is a `k`-uniform family of subsets of `Fin m` such
that `((A ∩ B).card : K) ∈ L` for all distinct `A, B ∈ F`, then `F.card ≤ m.choose s`.
Covers both Ray-Chaudhuri–Wilson (1975, `K = ℚ`) and modular Frankl–Wilson (1981, `K = ZMod p`). -/
theorem ppl177_frankl_wilson_uniform (K : Type*) [Field K] (m k s : ℕ)
    (L : Finset K) (hLcard : L.card ≤ s) (hkL : (k : K) ∉ L)
    (hki : ∀ i < s, (i : K) ≠ (k : K))
    (F : Finset (Finset (Fin m)))
    (hunif : ∀ A ∈ F, A.card = k)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : K) ∈ L) :
    F.card ≤ m.choose s := by
  classical
  let W := polySubspace K m s
  let v : F ⊕ B_lt m s → W := fun z =>
    match z with
    | Sum.inl A => ⟨evalPoly K A.1 L, polySubspace_mono K hLcard (evalPoly_mem_polySubspace K A.1 L)⟩
    | Sum.inr I => ⟨auxPoly K k I.1, auxPoly_mem_polySubspace K I.1 (Finset.mem_filter.mp I.2).2⟩
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc_fn : (∑ A : F, c (Sum.inl A) • evalPoly K A.1 L) +
        (∑ I : B_lt m s, c (Sum.inr I) • auxPoly K k I.1) = 0 := by
      have hval := congrArg Subtype.val hc
      simp only [Fintype.sum_sum_type, Submodule.coe_add, Submodule.coe_sum,
        Submodule.coe_smul_of_tower, Submodule.coe_zero, v] at hval
      exact hval
    have hc_inl : ∀ A : F, c (Sum.inl A) = 0 := by
      intro B
      have heval := congrFun hc_fn B.1
      simp only [Pi.add_apply, Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at heval
      have haux0 : ∑ I : B_lt m s, c (Sum.inr I) * auxPoly K k I.1 B.1 = 0 := by
        apply Finset.sum_eq_zero
        intro I _
        simp [auxPoly, hunif B.1 B.2]
      rw [haux0, add_zero] at heval
      have hsingle : ∑ A : F, c (Sum.inl A) * evalPoly K A.1 L B.1 =
          c (Sum.inl B) * evalPoly K B.1 L B.1 := by
        rw [Finset.sum_eq_single B]
        · intro A _ hAB
          have hne : A.1 ≠ B.1 := fun h => hAB (Subtype.ext h)
          have hmem : ((A.1 ∩ B.1).card : K) ∈ L := hinter A.1 A.2 B.1 B.2 hne
          have hzero : evalPoly K A.1 L B.1 = 0 := by
            simp only [evalPoly]
            exact Finset.prod_eq_zero hmem (sub_self _)
          rw [hzero, mul_zero]
        · intro hB; exact (hB (Finset.mem_univ B)).elim
      rw [hsingle] at heval
      have hne0 : evalPoly K B.1 L B.1 ≠ 0 := by
        simp only [evalPoly, Finset.inter_self, hunif B.1 B.2]
        rw [Finset.prod_ne_zero_iff]
        intro l hl
        exact sub_ne_zero.mpr (fun h => hkL (h ▸ hl))
      exact (mul_eq_zero.mp heval).resolve_right hne0
    have hc_inr : ∀ I : B_lt m s, c (Sum.inr I) = 0 := by
      have hsum0 : ∑ I : B_lt m s, c (Sum.inr I) • auxPoly K k I.1 = 0 := by
        have h1 : ∑ A : F, c (Sum.inl A) • evalPoly K A.1 L = 0 :=
          Finset.sum_eq_zero (fun A _ => by rw [hc_inl A, zero_smul])
        rw [h1, zero_add] at hc_fn
        exact hc_fn
      by_contra hnot
      push Not at hnot
      let Snz : Finset (B_lt m s) := Finset.univ.filter (fun I => c (Sum.inr I) ≠ 0)
      have hSnz : Snz.Nonempty := by
        rcases hnot with ⟨I, hI⟩
        exact ⟨I, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI⟩⟩
      obtain ⟨I₀, hI₀_mem, hI₀_min⟩ := Finset.exists_min_image Snz (fun I => I.1.card) hSnz
      have hI₀_nz : c (Sum.inr I₀) ≠ 0 := (Finset.mem_filter.mp hI₀_mem).2
      have heval := congrFun hsum0 I₀.1
      simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at heval
      have hsingle : ∑ I : B_lt m s, c (Sum.inr I) * auxPoly K k I.1 I₀.1 =
          c (Sum.inr I₀) * auxPoly K k I₀.1 I₀.1 := by
        rw [Finset.sum_eq_single I₀]
        · intro I _ hII₀
          by_cases hcI : c (Sum.inr I) = 0
          · rw [hcI, zero_mul]
          · have hInz : I ∈ Snz := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcI⟩
            have hle : I₀.1.card ≤ I.1.card := hI₀_min I hInz
            have hnsub : ¬ I.1 ⊆ I₀.1 := by
              intro hsub
              have heq : I.1 = I₀.1 := Finset.eq_of_subset_of_card_le hsub hle
              exact hII₀ (Subtype.ext heq)
            simp [auxPoly, indFn, hnsub]
        · intro hI₀; exact (hI₀ (Finset.mem_univ I₀)).elim
      rw [hsingle] at heval
      have haux_ne : auxPoly K k I₀.1 I₀.1 ≠ 0 := by
        simp only [auxPoly, indFn, Finset.Subset.refl, ↓reduceIte, mul_one]
        exact sub_ne_zero.mpr (hki I₀.1.card (Finset.mem_filter.mp I₀.2).2)
      exact hI₀_nz ((mul_eq_zero.mp heval).resolve_right haux_ne)
    intro z
    cases z with
    | inl A => exact hc_inl A
    | inr I => exact hc_inr I
  have hdim : Fintype.card (F ⊕ B_lt m s) ≤ Module.finrank K W :=
    hli.fintype_card_le_finrank
  have hfin : Module.finrank K W ≤ (B_le m s).card := finrank_polySubspace_le K m s
  have hcard_sum : Fintype.card (F ⊕ B_lt m s) = F.card + (B_lt m s).card := by
    simp [Fintype.card_sum, Fintype.card_coe]
  have hble : (B_le m s).card = (B_lt m s).card + m.choose s := card_B_le_eq_add_choose m s
  omega

/-- **Ray-Chaudhuri–Wilson Theorem (1975)**:
Any `k`-uniform family on `Fin m` with pairwise intersections in a set `L : Finset ℕ` of size
`L.card ≤ s ≤ k` (with `k ∉ L`) has cardinality at most `m.choose s`. -/
theorem ppl177_ray_chaudhuri_wilson (m k s : ℕ) (hsk : s ≤ k)
    (L : Finset ℕ) (hLcard : L.card ≤ s) (hkL : k ∉ L)
    (F : Finset (Finset (Fin m)))
    (hunif : ∀ A ∈ F, A.card = k)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ∈ L) :
    F.card ≤ m.choose s := by
  let Lq : Finset ℚ := L.image (Nat.cast : ℕ → ℚ)
  apply ppl177_frankl_wilson_uniform ℚ m k s Lq
  · exact le_trans Finset.card_image_le hLcard
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨l, hl, hcast⟩
    have : l = k := Nat.cast_injective hcast
    exact hkL (this ▸ hl)
  · intro i hi hcast
    have : i = k := Nat.cast_injective hcast
    omega
  · exact hunif
  · intro A hA B hB hAB
    exact Finset.mem_image.mpr ⟨(A ∩ B).card, hinter A hA B hB hAB, rfl⟩

/-- **Modular Frankl–Wilson Theorem (1981)**:
For any prime `p`, `m, k, s : ℕ`, and `L : Finset (ZMod p)` with `L.card ≤ s`, `(k : ZMod p) ∉ L`,
and `(i : ZMod p) ≠ (k : ZMod p)` for all `i < s`, any `k`-uniform family on `Fin m` whose
distinct pairwise intersections mod `p` lie in `L` has size at most `m.choose s`. -/
theorem ppl177_frankl_wilson_mod_prime (p m k s : ℕ) [Fact (Nat.Prime p)]
    (L : Finset (ZMod p)) (hLcard : L.card ≤ s) (hkL : (k : ZMod p) ∉ L)
    (hki : ∀ i < s, (i : ZMod p) ≠ (k : ZMod p))
    (F : Finset (Finset (Fin m)))
    (hunif : ∀ A ∈ F, A.card = k)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : ZMod p) ∈ L) :
    F.card ≤ m.choose s :=
  ppl177_frankl_wilson_uniform (ZMod p) m k s L hLcard hkL hki F hunif hinter

/-- **Generalized Off-Diagonal Explicit Frankl–Wilson Ramsey Graphs**:
For every prime `p`, integer `q ≥ 2`, and universe `m`, there is an explicit graph on
`Fin (m.choose (q * p - 1))` (with vertices `{(q*p - 1)-subsets of Fin m}` and edge iff
`¬ (p ∣ (A ∩ B).card + 1)`) having no clique of size `m.choose (p - 1) + 1` and no independent set
of size `m.choose (q - 1) + 1`. -/
theorem ppl177_frankl_wilson_offdiag_explicit (p q m : ℕ) (hp : Nat.Prime p) (hq : 2 ≤ q) :
    ∃ G : SimpleGraph (Fin (m.choose (q * p - 1))),
      G.CliqueFree (m.choose (p - 1) + 1) ∧ Gᶜ.CliqueFree (m.choose (q - 1) + 1) := by
  classical
  have : Fact (Nat.Prime p) := ⟨hp⟩
  let k := q * p - 1
  let V := {A : Finset (Fin m) // A ∈ (Finset.univ : Finset (Fin m)).powersetCard k}
  have hVcard : Fintype.card V = m.choose k := by
    rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  let G0 : SimpleGraph V :=
    { Adj := fun A B => A ≠ B ∧ ¬ (p ∣ (A.1 ∩ B.1).card + 1)
      symm := ⟨fun _ _ ⟨hne, hndvd⟩ => ⟨hne.symm, by rwa [Finset.inter_comm]⟩⟩
      loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩ }
  have hp2 : 2 ≤ p := hp.two_le
  have hk_add : k + 1 = q * p := by
    have hqp : 1 ≤ q * p := by nlinarith
    omega
  have hk_zmod : (k : ZMod p) = -1 := by
    have h0 : ((k + 1 : ℕ) : ZMod p) = 0 := by
      rw [hk_add, Nat.cast_mul, ZMod.natCast_self, mul_zero]
    rw [Nat.cast_add, Nat.cast_one] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hG0_clique : G0.CliqueFree (m.choose (p - 1) + 1) := by
    intro S hS
    let F : Finset (Finset (Fin m)) := S.image Subtype.val
    have hFcard : F.card = S.card := Finset.card_image_of_injective S Subtype.val_injective
    let Lp : Finset (ZMod p) := Finset.univ.erase (-1 : ZMod p)
    have hLp_card : Lp.card = p - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    have hle : F.card ≤ m.choose (p - 1) := by
      apply ppl177_frankl_wilson_mod_prime p m k (p - 1) Lp (le_of_eq hLp_card)
      · rw [hk_zmod]
        exact Finset.notMem_erase _ _
      · intro i hi heq
        rw [hk_zmod] at heq
        have h0 : ((i + 1 : ℕ) : ZMod p) = 0 := by
          rw [Nat.cast_add, Nat.cast_one, heq, neg_add_cancel]
        have hdvd : p ∣ i + 1 := (ZMod.natCast_eq_zero_iff (i + 1) p).mp h0
        have hle_p : i + 1 < p := by omega
        exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos i) hle_p hdvd
      · intro A hA
        rcases Finset.mem_image.mp hA with ⟨A', _, rfl⟩
        exact (Finset.mem_powersetCard.mp A'.2).2
      · intro A hA B hB hAB
        rcases Finset.mem_image.mp hA with ⟨A', hA', rfl⟩
        rcases Finset.mem_image.mp hB with ⟨B', hB', rfl⟩
        have hne : A' ≠ B' := fun h => hAB (congrArg Subtype.val h)
        have hndvd : ¬ p ∣ (A'.1 ∩ B'.1).card + 1 := (hS.1 hA' hB' hne).2
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        intro heq
        apply hndvd
        rw [← ZMod.natCast_eq_zero_iff]
        rw [Nat.cast_add, Nat.cast_one, heq, neg_add_cancel]
    have hSc : S.card = m.choose (p - 1) + 1 := hS.2
    omega
  have hG0_indep : G0ᶜ.CliqueFree (m.choose (q - 1) + 1) := by
    intro S hS
    let F : Finset (Finset (Fin m)) := S.image Subtype.val
    have hFcard : F.card = S.card := Finset.card_image_of_injective S Subtype.val_injective
    let Lq : Finset ℕ := (Finset.range (q - 1)).image (fun t => (t + 1) * p - 1)
    have hLq_card : Lq.card ≤ q - 1 := le_trans Finset.card_image_le (by simp)
    have hle : F.card ≤ m.choose (q - 1) := by
      have hqk : q - 1 ≤ k := by
        have hqp : q ≤ q * p := Nat.le_mul_of_pos_right q (by omega)
        omega
      apply ppl177_ray_chaudhuri_wilson m k (q - 1) hqk Lq hLq_card
      · intro hmem
        rcases Finset.mem_image.mp hmem with ⟨t, ht, heq⟩
        have htlt : t < q - 1 := Finset.mem_range.mp ht
        have : (t + 1) * p < q * p := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        have : 1 ≤ (t + 1) * p := by nlinarith
        omega
      · intro A hA
        rcases Finset.mem_image.mp hA with ⟨A', _, rfl⟩
        exact (Finset.mem_powersetCard.mp A'.2).2
      · intro A hA B hB hAB
        rcases Finset.mem_image.mp hA with ⟨A', hA', rfl⟩
        rcases Finset.mem_image.mp hB with ⟨B', hB', rfl⟩
        have hne : A' ≠ B' := fun h => hAB (congrArg Subtype.val h)
        have hcadj := hS.1 hA' hB' hne
        rw [SimpleGraph.compl_adj] at hcadj
        have hdvd : p ∣ (A'.1 ∩ B'.1).card + 1 := by
          by_contra hndvd
          exact hcadj.2 ⟨hne, hndvd⟩
        have hlt_k : (A'.1 ∩ B'.1).card < k := by
          have hAc : A'.1.card = k := (Finset.mem_powersetCard.mp A'.2).2
          have hBc : B'.1.card = k := (Finset.mem_powersetCard.mp B'.2).2
          have hsub : A'.1 ∩ B'.1 ⊆ A'.1 := Finset.inter_subset_left
          have hne_inter : A'.1 ∩ B'.1 ≠ A'.1 := by
            intro heq
            have hABsub : A'.1 ⊆ B'.1 := Finset.inter_eq_left.mp heq
            exact hAB (Finset.eq_of_subset_of_card_le hABsub (by omega))
          have hssub : A'.1 ∩ B'.1 ⊂ A'.1 := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne_inter⟩
          calc (A'.1 ∩ B'.1).card < A'.1.card := Finset.card_lt_card hssub
            _ = k := hAc
        rcases hdvd with ⟨r, hr⟩
        have hr_pos : 1 ≤ r := by
          rcases Nat.eq_zero_or_pos r with rfl | hpos
          · omega
          · exact hpos
        have hr_lt : r < q := by
          have h1 : p * r < q * p := by omega
          rw [mul_comm] at h1
          exact Nat.lt_of_mul_lt_mul_right h1
        refine Finset.mem_image.mpr ⟨r - 1, Finset.mem_range.mpr (by omega), ?_⟩
        have h1 : r - 1 + 1 = r := by omega
        rw [h1, mul_comm]
        omega
    have hSc : S.card = m.choose (q - 1) + 1 := hS.2
    omega
  let e : V ≃ Fin (m.choose k) := (Fintype.equivFin V).trans (finCongr hVcard)
  let G : SimpleGraph (Fin (m.choose k)) := G0.map e.toEmbedding
  refine ⟨G, ?_, ?_⟩
  · intro S hS
    let S0 : Finset V := S.map e.symm.toEmbedding
    apply hG0_clique S0
    rw [SimpleGraph.isNClique_iff]
    refine ⟨?_, by simp [S0, hS.2]⟩
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_map] at hx hy
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    have hne' : x' ≠ y' := fun h => hxy (congrArg e.symm h)
    have hadj := hS.1 hx' hy' hne'
    rcases hadj with ⟨_, u, v, huv, hu, hv⟩
    have hux : u = e.symm x' := by simpa using congrArg e.symm hu
    have hvy : v = e.symm y' := by simpa using congrArg e.symm hv
    simpa [hux, hvy] using huv
  · intro S hS
    let S0 : Finset V := S.map e.symm.toEmbedding
    apply hG0_indep S0
    rw [SimpleGraph.isNClique_iff]
    refine ⟨?_, by simp [S0, hS.2]⟩
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_map] at hx hy
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    have hne' : x' ≠ y' := fun h => hxy (congrArg e.symm h)
    have hcadj := hS.1 hx' hy' hne'
    rw [SimpleGraph.compl_adj] at hcadj ⊢
    refine ⟨hxy, fun huv => hcadj.2 ?_⟩
    exact ⟨hne', e.symm x', e.symm y', huv, e.apply_symm_apply x', e.apply_symm_apply y'⟩

/-- **Nagy (1972) Explicit Cubic Ramsey Construction (`p = 2` Specialization of Frankl–Wilson)**:
For every `m : ℕ`, there is an explicit graph on `Fin (m.choose 3)` with no clique and no
independent set of size `m + 1` (giving `O(N^{1/3}) = o(√N)` and strictly beating Turán's
`(k - 1)^2` for all `k ≥ 10`). -/
theorem ppl177_nagy_explicit (m : ℕ) :
    ∃ G : SimpleGraph (Fin (m.choose 3)), G.CliqueFree (m + 1) ∧ Gᶜ.CliqueFree (m + 1) := by
  have h := ppl177_frankl_wilson_offdiag_explicit 2 2 m Nat.prime_two (le_refl 2)
  simpa using h

/-- **Generalized Diagonal Frankl–Wilson Construction**:
For every prime `p` and universe `m`, there is an explicit graph on `Fin (m.choose (p ^ 2 - 1))`
with no clique and no independent set of size `m.choose (p - 1) + 1`. -/
theorem ppl177_frankl_wilson_diag_explicit (p m : ℕ) (hp : Nat.Prime p) :
    ∃ G : SimpleGraph (Fin (m.choose (p ^ 2 - 1))),
      G.CliqueFree (m.choose (p - 1) + 1) ∧ Gᶜ.CliqueFree (m.choose (p - 1) + 1) := by
  rw [sq]
  exact ppl177_frankl_wilson_offdiag_explicit p p m hp hp.two_le

/-- **Frankl–Wilson (1981) Classical `m = p^3` Explicit Ramsey Graph**:
For every prime `p`, there is an explicit graph on `Fin ((p ^ 3).choose (p ^ 2 - 1))` with no
clique and no independent set of size `(p ^ 3).choose (p - 1) + 1`. -/
theorem ppl177_frankl_wilson_p3_explicit (p : ℕ) (hp : Nat.Prime p) :
    ∃ G : SimpleGraph (Fin ((p ^ 3).choose (p ^ 2 - 1))),
      G.CliqueFree ((p ^ 3).choose (p - 1) + 1) ∧ Gᶜ.CliqueFree ((p ^ 3).choose (p - 1) + 1) :=
  ppl177_frankl_wilson_diag_explicit p (p ^ 3) hp

private lemma pow_le_choose_of_mul_le :
    ∀ k a b : ℕ, k * a ≤ b → a ^ k ≤ b.choose k := by
  intro k
  induction k with
  | zero =>
    intro a b _
    simp
  | succ k ih =>
    intro a b hab
    by_cases ha : a = 0
    · subst ha
      simp
    · have ha1 : 1 ≤ a := Nat.pos_of_ne_zero ha
      have hb1 : 1 ≤ b := by nlinarith
      have hsub : k * a ≤ b - 1 := by
        have : k * a + a ≤ b := by linarith
        omega
      have hih := ih a (b - 1) hsub
      have hmul_fac : a ^ (k + 1) * (k + 1).factorial ≤ b.descFactorial (k + 1) := by
        have h1 : a ^ k * k.factorial ≤ (b - 1).descFactorial k := by
          rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm k.factorial]
          exact Nat.mul_le_mul_right k.factorial hih
        have hdesc : b.descFactorial (k + 1) = b * (b - 1).descFactorial k := by
          cases b with
          | zero => omega
          | succ b' =>
            simp only [Nat.add_sub_cancel]
            exact Nat.succ_descFactorial_succ b' k
        rw [hdesc, pow_succ, Nat.factorial_succ]
        calc a ^ k * a * ((k + 1) * k.factorial)
            = ((k + 1) * a) * (a ^ k * k.factorial) := by ring
          _ ≤ b * (b - 1).descFactorial k := Nat.mul_le_mul hab h1
      rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm (k + 1).factorial] at hmul_fac
      exact Nat.le_of_mul_le_mul_right hmul_fac (Nat.factorial_pos (k + 1))

/-- **Explicit Superpolynomial Lower Bound (Frankl–Wilson 1981 beats every polynomial degree `d`)**:
For every degree `d : ℕ` and every prime `p ≥ max 3 (3 * d)`, letting
`N = (p ^ 3).choose (p ^ 2 - 1)` and `r = (p ^ 3).choose (p - 1) + 1`, we have `r ^ d < N` and
there exists an explicit graph on `Fin N` with `G.CliqueFree r ∧ Gᶜ.CliqueFree r`. -/
theorem ppl177_frankl_wilson_superpolynomial (d p : ℕ) (hp : Nat.Prime p)
    (hp3 : 3 ≤ p) (hpd : 3 * d ≤ p) :
    ((p ^ 3).choose (p - 1) + 1) ^ d < (p ^ 3).choose (p ^ 2 - 1) ∧
    ∃ G : SimpleGraph (Fin ((p ^ 3).choose (p ^ 2 - 1))),
      G.CliqueFree ((p ^ 3).choose (p - 1) + 1) ∧ Gᶜ.CliqueFree ((p ^ 3).choose (p - 1) + 1) := by
  refine ⟨?_, ppl177_frankl_wilson_p3_explicit p hp⟩
  have hlower : p ^ (p ^ 2 - 1) ≤ (p ^ 3).choose (p ^ 2 - 1) := by
    apply pow_le_choose_of_mul_le
    have : p ^ 2 - 1 ≤ p ^ 2 := Nat.sub_le _ _
    calc (p ^ 2 - 1) * p ≤ p ^ 2 * p := Nat.mul_le_mul_right p this
      _ = p ^ 3 := by ring
  have hupper : (p ^ 3).choose (p - 1) + 1 < p ^ (3 * (p - 1)) := by
    have hfac2 : 2 ≤ (p - 1).factorial := by
      have h2 : 2 ≤ p - 1 := by omega
      calc 2 = (2 : ℕ).factorial := rfl
        _ ≤ (p - 1).factorial := Nat.factorial_le h2
    have hcf : (p - 1).factorial * (p ^ 3).choose (p - 1) ≤ (p ^ 3) ^ (p - 1) := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow (p ^ 3) (p - 1)
    have h2c : 2 * (p ^ 3).choose (p - 1) ≤ p ^ (3 * (p - 1)) := by
      calc 2 * (p ^ 3).choose (p - 1)
          ≤ (p - 1).factorial * (p ^ 3).choose (p - 1) := Nat.mul_le_mul_right _ hfac2
        _ ≤ (p ^ 3) ^ (p - 1) := hcf
        _ = p ^ (3 * (p - 1)) := by rw [← pow_mul]
    have hM3 : 3 ≤ p ^ (3 * (p - 1)) := by
      have h1 : 1 ≤ 3 * (p - 1) := by omega
      calc 3 ≤ p := hp3
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (3 * (p - 1)) := Nat.pow_le_pow_right (by omega) h1
    omega
  by_cases hd : d = 0
  · subst hd
    simp only [pow_zero]
    have h1 : 1 < p ^ (p ^ 2 - 1) := by
      have hp2 : 4 ≤ p ^ 2 := by nlinarith
      have hexp : 1 ≤ p ^ 2 - 1 := by omega
      calc 1 < 3 := by decide
        _ ≤ p := hp3
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (p ^ 2 - 1) := Nat.pow_le_pow_right (by omega) hexp
    omega
  · have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd
    have hlt_pow : ((p ^ 3).choose (p - 1) + 1) ^ d < (p ^ (3 * (p - 1))) ^ d :=
      Nat.pow_lt_pow_left hupper (by omega)
    have hexp_le : 3 * (p - 1) * d ≤ p ^ 2 - 1 := by
      have hfact : (p - 1) * (p + 1) = p ^ 2 - 1 := by
        zify [show 1 ≤ p by omega, show 1 ≤ p ^ 2 by nlinarith]
        ring
      calc 3 * (p - 1) * d = (p - 1) * (3 * d) := by ring
        _ ≤ (p - 1) * (p + 1) := Nat.mul_le_mul_left (p - 1) (by omega)
        _ = p ^ 2 - 1 := hfact
    calc ((p ^ 3).choose (p - 1) + 1) ^ d
        < (p ^ (3 * (p - 1))) ^ d := hlt_pow
      _ = p ^ (3 * (p - 1) * d) := by rw [← pow_mul]
      _ ≤ p ^ (p ^ 2 - 1) := Nat.pow_le_pow_right (by omega) hexp_le
      _ ≤ (p ^ 3).choose (p ^ 2 - 1) := hlower

/-! ### Part 5: Sharp Small-`k` Explicit Paley Constructions (`P(5)` & `P(17)`, Zero `native_decide`) -/

/-- **Explicit Paley `P(5)` Witnessing `R(3, 3) > 5`** (sharp with `ppl177_ramsey_upper_diag`
giving `R(3, 3) ≤ 6`). -/
theorem ppl177_paley5_ramsey3 :
    ∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3 := by
  let Q5 : Finset (ZMod 5) := {1, 4}
  let G : SimpleGraph (ZMod 5) :=
    { Adj := fun u v => u - v ∈ Q5
      symm := ⟨fun u v h => by
        have hneg : ∀ x : ZMod 5, x ∈ Q5 → -x ∈ Q5 := by decide
        simpa [neg_sub] using hneg (u - v) h⟩
      loopless := ⟨fun u h => by
        have h0 : (0 : ZMod 5) ∉ Q5 := by decide
        exact h0 (by simpa [sub_self] using h)⟩ }
  change ∃ G : SimpleGraph (ZMod 5), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3
  refine ⟨G, ?_, ?_⟩
  · intro S hS
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS.2
    have h1 : a - b ∈ Q5 := hS.1 (by simp) (by simp) hab
    have h2 : b - c ∈ Q5 := hS.1 (by simp) (by simp) hbc
    have h3 : a - c ∈ Q5 := hS.1 (by simp) (by simp) hac
    have hno : ∀ x y : ZMod 5, x ∈ Q5 → y ∈ Q5 → x + y ∉ Q5 := by decide
    have hsum : (a - b) + (b - c) = a - c := by ring
    exact hno (a - b) (b - c) h1 h2 (hsum.symm ▸ h3)
  · intro S hS
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS.2
    have h1 := hS.1 (by simp) (by simp) hab
    have h2 := hS.1 (by simp) (by simp) hbc
    have h3 := hS.1 (by simp) (by simp) hac
    rw [SimpleGraph.compl_adj] at h1 h2 h3
    have hno : ∀ x y : ZMod 5, x ≠ 0 → x ∉ Q5 → y ≠ 0 → y ∉ Q5 → x + y = 0 ∨ x + y ∈ Q5 := by
      decide
    have hsum : (a - b) + (b - c) = a - c := by ring
    have hres := hno (a - b) (b - c) (sub_ne_zero.mpr hab) h1.2 (sub_ne_zero.mpr hbc) h2.2
    rw [hsum] at hres
    rcases hres with h0 | hq
    · exact sub_ne_zero.mpr hac h0
    · exact h3.2 hq

/-- **Explicit Paley `P(17)` Witnessing `R(4, 4) > 17`** (sharp with `R(4, 4) = 18`),
proved algebraically via quadratic-residue affine transitivity and self-complementarity
without `native_decide`. -/
theorem ppl177_paley17_ramsey4 :
    ∃ G : SimpleGraph (Fin 17), G.CliqueFree 4 ∧ Gᶜ.CliqueFree 4 := by
  change ∃ G : SimpleGraph (ZMod 17), G.CliqueFree 4 ∧ Gᶜ.CliqueFree 4
  let Q17 : Finset (ZMod 17) := {1, 2, 4, 8, 9, 13, 15, 16}
  have hQ_neg : ∀ x : ZMod 17, x ∈ Q17 → -x ∈ Q17 := by decide
  have hQ_zero : (0 : ZMod 17) ∉ Q17 := by decide
  have hQ_mul : ∀ x y : ZMod 17, x ∈ Q17 → y ∈ Q17 → x * y ∈ Q17 := by decide
  have hQ_inv : ∀ x : ZMod 17, x ∈ Q17 → ∃ y ∈ Q17, y * x = 1 := by decide
  have hQ_mul3 : ∀ x : ZMod 17, x ≠ 0 → (3 * x ∈ Q17 ↔ x ∉ Q17) := by decide
  have hQ_tri : ∀ x : ZMod 17, x ∈ Q17 → x - 1 ∈ Q17 → x = 2 ∨ x = 9 ∨ x = 16 := by decide
  have hQ_no_pair : ∀ x y : ZMod 17,
      (x = 2 ∨ x = 9 ∨ x = 16) → (y = 2 ∨ y = 9 ∨ y = 16) → x - y ∉ Q17 := by decide
  have h1ne0 : (1 : ZMod 17) ≠ 0 := by decide
  have h3ne0 : (3 : ZMod 17) ≠ 0 := by decide
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  let G : SimpleGraph (ZMod 17) :=
    { Adj := fun u v => u - v ∈ Q17
      symm := ⟨fun u v h => by simpa [neg_sub] using hQ_neg (u - v) h⟩
      loopless := ⟨fun u h => hQ_zero (by simpa [sub_self] using h)⟩ }
  have hK4 : G.CliqueFree 4 := by
    intro S hS
    have hSpos : S.Nonempty := Finset.card_pos.mp (by rw [hS.2]; decide)
    obtain ⟨a, ha⟩ := hSpos
    let S₁ : Finset (ZMod 17) := S.image (· - a)
    have hS₁_card : S₁.card = 4 := by
      rw [Finset.card_image_of_injective _ (fun x y h => sub_left_inj.mp h), hS.2]
    have h0_S₁ : (0 : ZMod 17) ∈ S₁ := Finset.mem_image.mpr ⟨a, ha, sub_self a⟩
    have hS₁_clique : G.IsClique (S₁ : Set (ZMod 17)) := by
      intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_image] at hx hy
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      have hne : x' ≠ y' := fun h => hxy (congrArg (· - a) h)
      have hadj : x' - y' ∈ Q17 := hS.1 hx' hy' hne
      have heq : (x' - a) - (y' - a) = x' - y' := by ring
      simpa [G, heq] using hadj
    have hS₁_er_pos : (S₁.erase 0).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem h0_S₁, hS₁_card]; decide)
    obtain ⟨b, hb_er⟩ := hS₁_er_pos
    have hb_ne0 : b ≠ 0 := (Finset.mem_erase.mp hb_er).1
    have hb_S₁ : b ∈ S₁ := (Finset.mem_erase.mp hb_er).2
    have hb_Q : b ∈ Q17 := by
      have hadj : b - 0 ∈ Q17 := hS₁_clique hb_S₁ h0_S₁ hb_ne0
      simpa using hadj
    obtain ⟨binv, hbinv_Q, hbinv_mul⟩ := hQ_inv b hb_Q
    have hbinv_ne0 : binv ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hbinv_mul
      exact zero_ne_one hbinv_mul
    let S₂ : Finset (ZMod 17) := S₁.image (binv * ·)
    have hS₂_card : S₂.card = 4 := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ hbinv_ne0), hS₁_card]
    have h0_S₂ : (0 : ZMod 17) ∈ S₂ := Finset.mem_image.mpr ⟨0, h0_S₁, mul_zero _⟩
    have h1_S₂ : (1 : ZMod 17) ∈ S₂ := Finset.mem_image.mpr ⟨b, hb_S₁, hbinv_mul⟩
    have hS₂_clique : G.IsClique (S₂ : Set (ZMod 17)) := by
      intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_image] at hx hy
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      have hne : x' ≠ y' := fun h => hxy (congrArg (binv * ·) h)
      have hadj : x' - y' ∈ Q17 := hS₁_clique hx' hy' hne
      have heq : binv * x' - binv * y' = binv * (x' - y') := by ring
      simpa [G, heq] using hQ_mul binv (x' - y') hbinv_Q hadj
    let T : Finset (ZMod 17) := (S₂.erase 0).erase 1
    have h1_er0 : (1 : ZMod 17) ∈ S₂.erase 0 :=
      Finset.mem_erase.mpr ⟨h1ne0, h1_S₂⟩
    have hT_card : T.card = 2 := by
      rw [Finset.card_erase_of_mem h1_er0, Finset.card_erase_of_mem h0_S₂, hS₂_card]
    obtain ⟨x, y, hxy, hT_eq⟩ := Finset.card_eq_two.mp hT_card
    have hx_T : x ∈ T := by rw [hT_eq]; simp
    have hy_T : y ∈ T := by rw [hT_eq]; simp
    have hx_mem : x ∈ S₂ ∧ x ≠ 0 ∧ x ≠ 1 := by
      have h1 := Finset.mem_erase.mp hx_T
      have h2 := Finset.mem_erase.mp h1.2
      exact ⟨h2.2, h2.1, h1.1⟩
    have hy_mem : y ∈ S₂ ∧ y ≠ 0 ∧ y ≠ 1 := by
      have h1 := Finset.mem_erase.mp hy_T
      have h2 := Finset.mem_erase.mp h1.2
      exact ⟨h2.2, h2.1, h1.1⟩
    have hx_Q : x ∈ Q17 := by simpa [G] using hS₂_clique hx_mem.1 h0_S₂ hx_mem.2.1
    have hx1_Q : x - 1 ∈ Q17 := hS₂_clique hx_mem.1 h1_S₂ hx_mem.2.2
    have hy_Q : y ∈ Q17 := by simpa [G] using hS₂_clique hy_mem.1 h0_S₂ hy_mem.2.1
    have hy1_Q : y - 1 ∈ Q17 := hS₂_clique hy_mem.1 h1_S₂ hy_mem.2.2
    have hxy_Q : x - y ∈ Q17 := hS₂_clique hx_mem.1 hy_mem.1 hxy
    exact hQ_no_pair x y (hQ_tri x hx_Q hx1_Q) (hQ_tri y hy_Q hy1_Q) hxy_Q
  refine ⟨G, hK4, ?_⟩
  · intro S hS
    let S' : Finset (ZMod 17) := S.image (3 * ·)
    apply hK4 S'
    rw [SimpleGraph.isNClique_iff]
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_image] at hx hy
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      have hne : x' ≠ y' := fun h => hxy (congrArg (3 * ·) h)
      have hcadj := hS.1 hx' hy' hne
      rw [SimpleGraph.compl_adj] at hcadj
      have hdiff_ne : x' - y' ≠ 0 := sub_ne_zero.mpr hne
      have heq : 3 * x' - 3 * y' = 3 * (x' - y') := by ring
      simpa [G, heq] using (hQ_mul3 (x' - y') hdiff_ne).mpr hcadj.2
    · rw [Finset.card_image_of_injective _ (mul_right_injective₀ h3ne0), hS.2]

/-! ### Part 6: Formalized Structural Barrier Theorems -/

/-- **Finite-Field Adjacency Rank Barrier (`α(G) * p^{rank} ≥ N`)**:
For any prime `p`, any simple graph `G` on `Fin N`, and any `r : ℕ`, if the row space of the
`0/1` adjacency matrix of `G` over `ZMod p` has dimension `≤ r`, then `G` contains an independent
set `S` satisfying `N ≤ S.card * p ^ r`. -/
theorem ppl177_finite_field_rank_barrier (p N r : ℕ) [Fact (Nat.Prime p)]
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hrank : Module.finrank (ZMod p)
      (Submodule.span (ZMod p)
        (Set.range (fun u : Fin N => fun v : Fin N =>
          if G.Adj u v then (1 : ZMod p) else 0))) ≤ r) :
    ∃ S : Finset (Fin N), G.IsIndepSet (S : Set (Fin N)) ∧ N ≤ S.card * p ^ r := by
  classical
  let row : Fin N → (Fin N → ZMod p) := fun u v => if G.Adj u v then (1 : ZMod p) else 0
  let W : Submodule (ZMod p) (Fin N → ZMod p) := Submodule.span (ZMod p) (Set.range row)
  have hWcard : Fintype.card W = p ^ Module.finrank (ZMod p) W := by
    let b := Module.finBasis (ZMod p) W
    have heq := Fintype.card_congr b.equivFun.toEquiv
    rw [heq, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hWle : Fintype.card W ≤ p ^ r := by
    rw [hWcard]
    exact Nat.pow_le_pow_right (Fact.out : Nat.Prime p).pos hrank
  let f : Fin N → W := fun u => ⟨row u, Submodule.subset_span ⟨u, rfl⟩⟩
  let fiber : W → Finset (Fin N) := fun w => Finset.univ.filter (fun u => f u = w)
  have hWne : (Finset.univ : Finset W).Nonempty := ⟨0, Finset.mem_univ 0⟩
  obtain ⟨w₀, _, hw₀_max⟩ := Finset.exists_max_image (Finset.univ : Finset W)
    (fun w => (fiber w).card) hWne
  refine ⟨fiber w₀, ?_, ?_⟩
  · intro u hu v hv huv
    have hu' : f u = w₀ := (Finset.mem_filter.mp hu).2
    have hv' : f v = w₀ := (Finset.mem_filter.mp hv).2
    have hrow : row u = row v := congrArg Subtype.val (hu'.trans hv'.symm)
    have hat := congrFun hrow v
    simp only [row, G.loopless.irrefl v, ↓reduceIte] at hat
    intro hadj
    simp only [hadj, ↓reduceIte] at hat
    exact one_ne_zero hat
  · have hsum : ∑ w : W, (fiber w).card = N := by
      have hpart := Finset.card_eq_sum_card_fiberwise
        (f := f) (s := (Finset.univ : Finset (Fin N))) (t := (Finset.univ : Finset W))
        (fun u _ => Finset.mem_univ (f u))
      simpa [fiber] using hpart.symm
    calc N = ∑ w : W, (fiber w).card := hsum.symm
      _ ≤ ∑ _ : W, (fiber w₀).card := Finset.sum_le_sum (fun w _ => hw₀_max w (Finset.mem_univ w))
      _ = Fintype.card W * (fiber w₀).card := by simp
      _ = (fiber w₀).card * Fintype.card W := mul_comm _ _
      _ ≤ (fiber w₀).card * p ^ r := Nat.mul_le_mul_left _ hWle

/-- **Low-Rank Ramsey Barrier Corollary**:
Any `K`-Ramsey graph (`G.CliqueFree K ∧ Gᶜ.CliqueFree K`) on `Fin N` with `K ≥ 1` whose
adjacency matrix over `ZMod p` has rank `≤ r` must satisfy `N < K * p ^ r`
(so Erdős #78 graphs require `rank_{𝔽_p}(A_G) ≥ (1 - o(1)) log_p N` simultaneously for every
prime `p`). -/
theorem ppl177_low_rank_ramsey_barrier (p N r K : ℕ) [Fact (Nat.Prime p)]
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hfree : G.CliqueFree K ∧ Gᶜ.CliqueFree K)
    (hrank : Module.finrank (ZMod p)
      (Submodule.span (ZMod p)
        (Set.range (fun u : Fin N => fun v : Fin N =>
          if G.Adj u v then (1 : ZMod p) else 0))) ≤ r) :
    N < K * p ^ r := by
  obtain ⟨S, hSind, hNle⟩ := ppl177_finite_field_rank_barrier p N r G hrank
  have hSlt : S.card < K := by
    by_contra hge
    push Not at hge
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hge
    have hTind : G.IsNIndepSet K T := by
      rw [SimpleGraph.isNIndepSet_iff]
      exact ⟨fun x hx y hy hxy => hSind (hTsub hx) (hTsub hy) hxy, hTcard⟩
    exact hfree.2 T ((isNClique_compl_iff_isNIndepSet G K T).mpr hTind)
  have hpr : 0 < p ^ r := pow_pos (Fact.out : Nat.Prime p).pos r
  calc N ≤ S.card * p ^ r := hNle
    _ < K * p ^ r := Nat.mul_lt_mul_of_pos_right hSlt hpr

/-- **Symmetric Two-Source Disperser → Ramsey Graph Reduction**:
Every symmetric `(K, 0)`-two-source disperser `D : Fin N → Fin N → Bool` (hitting both `true`
and `false` on every `K × K` rectangle) yields a `2K`-Ramsey graph on `Fin N`. -/
theorem ppl177_symmetric_disperser_ramsey (N K : ℕ) (D : Fin N → Fin N → Bool)
    (hsym : ∀ x y, D x y = D y x)
    (hdisp : ∀ (A B : Finset (Fin N)), A.card = K → B.card = K →
      (∃ x ∈ A, ∃ y ∈ B, D x y = true) ∧ (∃ x ∈ A, ∃ y ∈ B, D x y = false)) :
    ∃ G : SimpleGraph (Fin N), G.CliqueFree (2 * K) ∧ Gᶜ.CliqueFree (2 * K) := by
  let G : SimpleGraph (Fin N) :=
    { Adj := fun u v => u ≠ v ∧ D u v = true
      symm := ⟨fun u v ⟨hne, hd⟩ => ⟨hne.symm, by rwa [hsym]⟩⟩
      loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩ }
  refine ⟨G, ?_, ?_⟩
  · intro S hS
    have hK_le : K ≤ S.card := by rw [hS.2]; omega
    obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hK_le
    let B := S \ A
    have hBcard : B.card = K := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAsub, hS.2, hAcard]; omega
    obtain ⟨x, hx, y, hy, hfalse⟩ := (hdisp A B hAcard hBcard).2
    have hne : x ≠ y := by
      intro hxy; subst hxy
      exact (Finset.mem_sdiff.mp hy).2 hx
    have htrue : D x y = true := (hS.1 (hAsub hx) (Finset.mem_sdiff.mp hy).1 hne).2
    rw [htrue] at hfalse
    exact Bool.noConfusion hfalse
  · intro S hS
    have hK_le : K ≤ S.card := by rw [hS.2]; omega
    obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hK_le
    let B := S \ A
    have hBcard : B.card = K := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAsub, hS.2, hAcard]; omega
    obtain ⟨x, hx, y, hy, htrue⟩ := (hdisp A B hAcard hBcard).1
    have hne : x ≠ y := by
      intro hxy; subst hxy
      exact (Finset.mem_sdiff.mp hy).2 hx
    have hcadj := hS.1 (hAsub hx) (Finset.mem_sdiff.mp hy).1 hne
    rw [SimpleGraph.compl_adj] at hcadj
    exact hcadj.2 ⟨hne, htrue⟩

/-- **Bipartite Ramsey Upper Bound (`N ≥ K * (2K).choose K`)**:
Every `2`-coloring `D : Fin N → Fin N → Bool` with `N ≥ K * (2K).choose K` (`K ≥ 1`) contains
a monochromatic `K × K` rectangle. -/
theorem ppl177_bipartite_ramsey_upper (N K : ℕ) (hK : 1 ≤ K)
    (hN : K * (2 * K).choose K ≤ N) (D : Fin N → Fin N → Bool) :
    ∃ (b : Bool) (A B : Finset (Fin N)),
      A.card = K ∧ B.card = K ∧ ∀ x ∈ A, ∀ y ∈ B, D x y = b := by
  classical
  have h2c : (2 * K).choose K = 2 * (2 * K - 1).choose K := by
    obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
    have h2m : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    have hsub : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    have hsym : (2 * m + 1).choose m = (2 * m + 1).choose (m + 1) := by
      rw [← Nat.choose_symm (by omega : m ≤ 2 * m + 1)]
      congr 1; omega
    rw [hsub, h2m, Nat.choose_succ_succ, hsym]
    change (2 * m + 1).choose (m + 1) + (2 * m + 1).choose (m + 1) = 2 * (2 * m + 1).choose (m + 1)
    ring
  have h2K_pos : 0 < (2 * K).choose K := Nat.choose_pos (by omega)
  have h2Km1_le : 2 * K - 1 ≤ N := by
    have hge2 : 2 ≤ (2 * K).choose K := by
      have hpos1 : 1 ≤ (2 * K - 1).choose K := Nat.choose_pos (by omega)
      omega
    have : 2 * K - 1 ≤ 2 * K := Nat.sub_le _ _
    nlinarith
  have hcard_univ : 2 * K - 1 ≤ (Finset.univ : Finset (Fin N)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact h2Km1_le
  obtain ⟨X₀, _, hX₀⟩ := Finset.exists_subset_card_eq hcard_univ
  let P := X₀.powersetCard K
  have hPcard : P.card = (2 * K - 1).choose K := by
    rw [Finset.card_powersetCard, hX₀]
  have hpick : ∀ y : Fin N, ∃ p : Bool × P, ∀ x ∈ p.2.1, D x y = p.1 := by
    intro y
    let T := X₀.filter (fun x => D x y = true)
    let F := X₀.filter (fun x => D x y ≠ true)
    have hpart : T.card + F.card = X₀.card := by
      simpa [T, F] using Finset.card_filter_add_card_filter_not (s := X₀) (p := fun x => D x y = true)
    have hsplit : K ≤ T.card ∨ K ≤ F.card := by omega
    rcases hsplit with hT | hF
    · obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hT
      have hAX₀ : A ⊆ X₀ := hAsub.trans (Finset.filter_subset _ _)
      refine ⟨(true, ⟨A, Finset.mem_powersetCard.mpr ⟨hAX₀, hAcard⟩⟩), fun x hx => ?_⟩
      exact (Finset.mem_filter.mp (hAsub hx)).2
    · obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hF
      have hAX₀ : A ⊆ X₀ := hAsub.trans (Finset.filter_subset _ _)
      refine ⟨(false, ⟨A, Finset.mem_powersetCard.mpr ⟨hAX₀, hAcard⟩⟩), fun x hx => ?_⟩
      have hne := (Finset.mem_filter.mp (hAsub hx)).2
      cases h : D x y <;> simp_all
  choose f hf using hpick
  let fiber : Bool × P → Finset (Fin N) := fun p => Finset.univ.filter (fun y => f y = p)
  have hcard_cod : Fintype.card (Bool × P) = (2 * K).choose K := by
    rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe, hPcard, ← h2c]
  have hne_cod : (Finset.univ : Finset (Bool × P)).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_univ, hcard_cod]; exact h2K_pos)
  obtain ⟨p₀, _, hp₀_max⟩ := Finset.exists_max_image (Finset.univ : Finset (Bool × P))
    (fun p => (fiber p).card) hne_cod
  have hN_le : N ≤ (2 * K).choose K * (fiber p₀).card := by
    have hsum : ∑ p : Bool × P, (fiber p).card = N := by
      have hpart := Finset.card_eq_sum_card_fiberwise
        (f := f) (s := (Finset.univ : Finset (Fin N))) (t := (Finset.univ : Finset (Bool × P)))
        (fun y _ => Finset.mem_univ (f y))
      simpa [fiber] using hpart.symm
    calc N = ∑ p : Bool × P, (fiber p).card := hsum.symm
      _ ≤ ∑ _ : Bool × P, (fiber p₀).card :=
          Finset.sum_le_sum (fun p _ => hp₀_max p (Finset.mem_univ p))
      _ = Fintype.card (Bool × P) * (fiber p₀).card := by simp
      _ = (2 * K).choose K * (fiber p₀).card := by rw [hcard_cod]
  have hK_le_fib : K ≤ (fiber p₀).card := by
    have hmul : K * (2 * K).choose K ≤ (fiber p₀).card * (2 * K).choose K := by
      calc K * (2 * K).choose K ≤ N := hN
        _ ≤ (2 * K).choose K * (fiber p₀).card := hN_le
        _ = (fiber p₀).card * (2 * K).choose K := mul_comm _ _
    exact Nat.le_of_mul_le_mul_right hmul h2K_pos
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hK_le_fib
  refine ⟨p₀.1, p₀.2.1, B, (Finset.mem_powersetCard.mp p₀.2.2).2, hBcard, fun x hx y hy => ?_⟩
  have hfy : f y = p₀ := (Finset.mem_filter.mp (hBsub hy)).2
  have hxy := hf y x (by rwa [hfy])
  rwa [hfy] at hxy

/-- **Information-Theoretic Min-Entropy Barrier for Two-Source Dispersers**:
For `N ≥ K * 4 ^ K` (`K ≥ 1`), NO function `D : Fin N → Fin N → Bool` can be a `(K, 0)`-two-source
disperser (equivalently, on `N = 2 ^ n`, any disperser requires `K * 4 ^ K > 2 ^ n`, forcing
min-entropy `h = log₂ K ≥ log₂ n - O(1)` — explaining why Xin Li's `h = C log₂ n` gives
`K = (log₂ N)^C`, while Erdős #78 requires pinning down the exact leading constant `C = 1`). -/
theorem ppl177_disperser_entropy_barrier (N K : ℕ) (hK : 1 ≤ K)
    (hN : K * 4 ^ K ≤ N) (D : Fin N → Fin N → Bool) :
    ¬ (∀ (A B : Finset (Fin N)), A.card = K → B.card = K →
      (∃ x ∈ A, ∃ y ∈ B, D x y = true) ∧ (∃ x ∈ A, ∃ y ∈ B, D x y = false)) := by
  intro hdisp
  have hchoose : (2 * K).choose K ≤ 4 ^ K := by
    have h1 : (2 * K).choose K ≤ 2 ^ (2 * K) := by
      rw [← Nat.sum_range_choose (2 * K)]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))
    have h2 : 2 ^ (2 * K) = 4 ^ K := by
      rw [pow_mul]
      norm_num
    omega
  obtain ⟨b, A, B, hA, hB, hmono⟩ :=
    ppl177_bipartite_ramsey_upper N K hK (le_trans (Nat.mul_le_mul_left K hchoose) hN) D
  cases b
  · obtain ⟨x, hx, y, hy, htrue⟩ := (hdisp A B hA hB).1
    have hfalse := hmono x hx y hy
    rw [htrue] at hfalse
    exact Bool.noConfusion hfalse
  · obtain ⟨x, hx, y, hy, hfalse⟩ := (hdisp A B hA hB).2
    have htrue := hmono x hx y hy
    rw [htrue] at hfalse
    exact Bool.noConfusion hfalse

end PPL177
