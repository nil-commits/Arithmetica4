/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-!
# PPL 042 (Erdős #77) & PPL 027 (Erdős #1029): Diagonal Ramsey Limit & Super-LLL Lower Bound

## Honest Scope & Literature Status
Both prize problems remain **VERIFIED OPEN**:
- **PPL 042 (Erdős Problem #77, $250):** Determine the value (and prove existence) of
  `lim_{k → ∞} R(k)^{1/k}`.
- **PPL 027 (Erdős Problem #1029, $100 / $1,000):** Prove (or disprove) that
  `R(k) / (k · 2^{k/2}) → ∞` as `k → ∞`.

This file makes **no** claim to solve either prize problem. Instead, it provides a complete,
self-contained, pure-Mathlib formalization (`0` `sorry`, `0` `native_decide`, `0` custom or
`private` definitions in any public theorem signature) of exact small values, Spencer's (1975)
Symmetric LLL lower bound, the exact Shearer/Symmetric LLL `√2 / e` barrier for Erdős #1029,
the Gupta–Ndiaye–Norin–Wei (GNNW 2024/2026) / CGMS (2023/2026) exponential upper bound
`R(k) ≤ (399 / 100)^k`, and the improved Erdős #77 limit sandwich `[√2, 399 / 100]`.
-/

namespace PPL042

open scoped BigOperators
open Finset Filter

/-! ### Section 1: Core Ramsey Infrastructure (Private Helpers) -/

private def ramseyProp (k l n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree k ∧ Gᶜ.CliqueFree l)

private noncomputable def R2 (k l : ℕ) : ℕ :=
  sInf {n : ℕ | ramseyProp k l n}

private lemma ramseyProp_mono_n {k l n m : ℕ} (hnm : n ≤ m) (h : ramseyProp k l n) :
    ramseyProp k l m := by
  intro G ⟨hGk, hGl⟩
  let f : Fin n ↪ Fin m := Fin.castLEEmb hnm
  let H : SimpleGraph (Fin n) := G.comap f
  apply h H
  refine ⟨?_, ?_⟩
  · intro s hs
    have hmap : G.IsNClique k (s.map f) := by
      refine ⟨?_, by simp [hs.card_eq]⟩
      intro a ha b hb hab
      rcases Finset.mem_map.mp ha with ⟨a', ha', rfl⟩
      rcases Finset.mem_map.mp hb with ⟨b', hb', rfl⟩
      have hab' : a' ≠ b' := fun hEq => hab (congrArg f hEq)
      exact hs.1 ha' hb' hab'
    exact hGk (s.map f) hmap
  · intro s hs
    have hmap : Gᶜ.IsNClique l (s.map f) := by
      refine ⟨?_, by simp [hs.card_eq]⟩
      intro a ha b hb hab
      rcases Finset.mem_map.mp ha with ⟨a', ha', rfl⟩
      rcases Finset.mem_map.mp hb with ⟨b', hb', rfl⟩
      have hab' : a' ≠ b' := fun hEq => hab (congrArg f hEq)
      have hadj := hs.1 ha' hb' hab'
      exact ⟨hab, fun hG => hadj.2 hG⟩
    exact hGl (s.map f) hmap

private lemma ramseyProp_symm {k l n : ℕ} (h : ramseyProp k l n) : ramseyProp l k n := by
  intro G ⟨hGl, hGk⟩
  apply h Gᶜ
  refine ⟨hGk, ?_⟩
  simpa using hGl

private lemma ramseyProp_one_left (l : ℕ) : ramseyProp 1 l 1 := by
  intro G ⟨hG1, _⟩
  apply hG1 {0}
  refine ⟨?_, by simp⟩
  intro a ha b hb hab
  have ha' : a = 0 := Finset.mem_singleton.mp ha
  have hb' : b = 0 := Finset.mem_singleton.mp hb
  exact absurd (ha'.trans hb'.symm) hab

private lemma ramseyProp_one_right (k : ℕ) : ramseyProp k 1 1 :=
  ramseyProp_symm (ramseyProp_one_left k)

private lemma ramseyProp_two_left (l : ℕ) : ramseyProp 2 l l := by
  intro G ⟨hG2, hGl⟩
  apply hGl Finset.univ
  refine ⟨?_, by simp⟩
  intro a _ b _ hab
  refine ⟨hab, fun hAdj => ?_⟩
  apply hG2 {a, b}
  refine ⟨?_, Finset.card_pair hab⟩
  intro x hx y hy hxy
  rcases Finset.mem_insert.mp hx with rfl | hx
  · rcases Finset.mem_insert.mp hy with rfl | hy
    · exact absurd rfl hxy
    · rw [Finset.mem_singleton.mp hy]; exact hAdj
  · rw [Finset.mem_singleton.mp hx] at hxy ⊢
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hAdj.symm
    · exact absurd (Finset.mem_singleton.mp hy).symm hxy

private lemma ramseyProp_two_right (k : ℕ) : ramseyProp k 2 k :=
  ramseyProp_symm (ramseyProp_two_left k)

/-- Pull back a `ramseyProp k l m` guarantee onto any vertex subset `S` of cardinality `≥ m`. -/
private lemma exists_clique_in_subset {n k l m : ℕ} {G : SimpleGraph (Fin n)}
    (S : Finset (Fin n)) (hm : ramseyProp k l m) (hcard : m ≤ S.card) :
    (∃ t ⊆ S, G.IsNClique k t) ∨ (∃ t ⊆ S, Gᶜ.IsNClique l t) := by
  obtain ⟨S', hS'S, hS'card⟩ := Finset.exists_subset_card_eq hcard
  have hfe : Fintype.card S' = m := by simp [hS'card]
  let e : Fin m ≃ S' := (Fintype.equivFinOfCardEq hfe).symm
  let f : Fin m ↪ Fin n := ⟨fun i => (e i).val, fun i j hij => e.injective (Subtype.ext hij)⟩
  let H : SimpleGraph (Fin m) := G.comap f
  have hnot := hm H
  by_contra hcontra
  push Not at hcontra
  apply hnot
  refine ⟨?_, ?_⟩
  · intro t ht
    apply hcontra.1 (t.map f)
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, _, rfl⟩
      exact hS'S (e i).property
    · refine ⟨?_, by simp [ht.card_eq]⟩
      intro a ha b hb hab
      rcases Finset.mem_map.mp ha with ⟨a', ha', rfl⟩
      rcases Finset.mem_map.mp hb with ⟨b', hb', rfl⟩
      exact ht.1 ha' hb' (fun hEq => hab (congrArg f hEq))
  · intro t ht
    apply hcontra.2 (t.map f)
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, _, rfl⟩
      exact hS'S (e i).property
    · refine ⟨?_, by simp [ht.card_eq]⟩
      intro a ha b hb hab
      rcases Finset.mem_map.mp ha with ⟨a', ha', rfl⟩
      rcases Finset.mem_map.mp hb with ⟨b', hb', rfl⟩
      have hadj := ht.1 ha' hb' (fun hEq => hab (congrArg f hEq))
      exact ⟨hab, fun hG => hadj.2 hG⟩

/-- Classic Erdős–Szekeres neighborhood step (for positive `a + b`). -/
private lemma ramseyProp_step {k l a b : ℕ} (hab0 : 0 < a + b)
    (ha : ramseyProp k (l + 1) a) (hb : ramseyProp (k + 1) l b) :
    ramseyProp (k + 1) (l + 1) (a + b) := by
  intro G ⟨hGk, hGl⟩
  let v0 : Fin (a + b) := ⟨0, hab0⟩
  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  let NR : Finset (Fin (a + b)) := Finset.univ.filter (fun u => G.Adj v0 u)
  let NB : Finset (Fin (a + b)) := Finset.univ.filter (fun u => u ≠ v0 ∧ ¬G.Adj v0 u)
  have hdisj : Disjoint NR NB := by
    rw [Finset.disjoint_left]
    intro u huR huB
    simp only [NR, NB, mem_filter, mem_univ, true_and] at huR huB
    exact huB.2 huR
  have hunion : NR ∪ NB = Finset.univ.erase v0 := by
    ext u
    simp only [NR, NB, mem_union, mem_filter, mem_univ, true_and, mem_erase, and_true]
    constructor
    · rintro (hR | ⟨hne, _⟩)
      · exact fun hEq => G.loopless.irrefl v0 (hEq ▸ hR)
      · exact hne
    · intro hne
      by_cases hR : G.Adj v0 u
      · exact Or.inl hR
      · exact Or.inr ⟨hne, hR⟩
  have hsum : NR.card + NB.card = a + b - 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_erase_of_mem (mem_univ v0),
      Finset.card_univ, Fintype.card_fin]
  by_cases hR : a ≤ NR.card
  · rcases exists_clique_in_subset (G := G) NR ha hR with ⟨t, htNR, ht⟩ | ⟨t, _, ht⟩
    · have hv0 : v0 ∉ t := fun hv => G.loopless.irrefl v0 ((mem_filter.mp (htNR hv)).2)
      apply hGk (insert v0 t)
      refine ⟨?_, by rw [Finset.card_insert_of_notMem hv0, ht.card_eq]⟩
      intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx <;>
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact absurd rfl hxy
      · exact (mem_filter.mp (htNR hy)).2
      · exact ((mem_filter.mp (htNR hx)).2).symm
      · exact ht.1 hx hy hxy
    · exact hGl t ht
  · have hB : b ≤ NB.card := by omega
    rcases exists_clique_in_subset (G := G) NB hb hB with ⟨t, _, ht⟩ | ⟨t, htNB, ht⟩
    · exact hGk t ht
    · have hv0 : v0 ∉ t := fun hv => (mem_filter.mp (htNB hv)).2.1 rfl
      apply hGl (insert v0 t)
      refine ⟨?_, by rw [Finset.card_insert_of_notMem hv0, ht.card_eq]⟩
      intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx <;>
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact absurd rfl hxy
      · exact ⟨hxy, (mem_filter.mp (htNB hy)).2.2⟩
      · exact ⟨hxy, fun h => (mem_filter.mp (htNB hx)).2.2 h.symm⟩
      · exact ht.1 hx hy hxy

/-- Classic Erdős–Szekeres binomial upper bound (existence of `ramseyProp`). -/
private lemma ramseyProp_erdos_szekeres :
    ∀ s k l : ℕ, 1 ≤ k → 1 ≤ l → k + l = s → ramseyProp k l ((k + l - 2).choose (k - 1)) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro k l hk hl hsum
    rcases Nat.eq_or_lt_of_le hk with rfl | hk2
    · simpa using ramseyProp_one_left l
    rcases Nat.eq_or_lt_of_le hl with rfl | hl2
    · have hch : (k + 1 - 2).choose (k - 1) = 1 := by
        have : k + 1 - 2 = k - 1 := by omega
        rw [this, Nat.choose_self]
      rw [hch]
      exact ramseyProp_one_right k
    have hk' : 1 ≤ k - 1 := by omega
    have hl' : 1 ≤ l - 1 := by omega
    have h1 := ih (k - 1 + l) (by omega) (k - 1) l hk' hl rfl
    have h2 := ih (k + (l - 1)) (by omega) k (l - 1) hk hl' rfl
    have hpos : 0 < (k - 1 + l - 2).choose (k - 1 - 1) + (k + (l - 1) - 2).choose (k - 1) := by
      have : 0 < (k + (l - 1) - 2).choose (k - 1) := Nat.choose_pos (by omega)
      omega
    have hstep := ramseyProp_step (k := k - 1) (l := l - 1) hpos
      (by simpa [Nat.sub_add_cancel hk, Nat.sub_add_cancel hl] using h1)
      (by simpa [Nat.sub_add_cancel hk, Nat.sub_add_cancel hl] using h2)
    have hEq : (k - 1 + l - 2).choose (k - 1 - 1) + (k + (l - 1) - 2).choose (k - 1) =
        (k + l - 2).choose (k - 1) := by
      have ha : k - 1 + l - 2 = k + l - 3 := by omega
      have hb : k + (l - 1) - 2 = k + l - 3 := by omega
      have hc : k + l - 2 = (k + l - 3) + 1 := by omega
      have hd : k - 1 = (k - 2) + 1 := by omega
      have he : k - 1 - 1 = k - 2 := by omega
      rw [ha, hb, hc, he, hd, Nat.choose_succ_succ]
    rw [← hEq]
    simpa [Nat.sub_add_cancel hk, Nat.sub_add_cancel hl] using hstep

private lemma ramseySet_nonempty {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    {n : ℕ | ramseyProp k l n}.Nonempty :=
  ⟨(k + l - 2).choose (k - 1), ramseyProp_erdos_szekeres (k + l) k l hk hl rfl⟩

private lemma R2_spec {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) : ramseyProp k l (R2 k l) :=
  Nat.sInf_mem (ramseySet_nonempty hk hl)

private lemma R2_le_of_ramseyProp {k l n : ℕ} (h : ramseyProp k l n) : R2 k l ≤ n :=
  Nat.sInf_le h

private lemma lt_R2_of_witness {k l n : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (G : SimpleGraph (Fin n)) (hGk : G.CliqueFree k) (hGl : Gᶜ.CliqueFree l) : n < R2 k l := by
  by_contra hle
  push Not at hle
  exact ramseyProp_mono_n hle (R2_spec hk hl) G ⟨hGk, hGl⟩

private lemma R2_symm (k l : ℕ) : R2 k l = R2 l k := by
  unfold R2
  congr 1
  ext n
  exact ⟨ramseyProp_symm, ramseyProp_symm⟩

private lemma R2_pos {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) : 1 ≤ R2 k l := by
  by_contra h0
  push Not at h0
  have hR0 : R2 k l = 0 := by omega
  have hspec := R2_spec hk hl
  rw [hR0] at hspec
  apply hspec ⊥
  refine ⟨?_, ?_⟩
  · intro s hs
    have hcard := hs.card_eq
    rw [Finset.eq_empty_of_isEmpty s, Finset.card_empty] at hcard
    omega
  · intro s hs
    have hcard := hs.card_eq
    rw [Finset.eq_empty_of_isEmpty s, Finset.card_empty] at hcard
    omega

private lemma R2_step_le {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    R2 (k + 1) (l + 1) ≤ R2 k (l + 1) + R2 (k + 1) l := by
  have hpos : 0 < R2 k (l + 1) + R2 (k + 1) l := by
    have := R2_pos hk (by omega : 1 ≤ l + 1); omega
  exact R2_le_of_ramseyProp (ramseyProp_step hpos (R2_spec hk (by omega)) (R2_spec (by omega) hl))

private lemma R2_erdos_szekeres {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    R2 k l ≤ (k + l - 2).choose (k - 1) :=
  R2_le_of_ramseyProp (ramseyProp_erdos_szekeres (k + l) k l hk hl rfl)

private lemma R2_le_pow_four (k : ℕ) : R2 k k ≤ 4 ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : ramseyProp 0 0 0 := by
      intro G ⟨hG0, _⟩
      exact hG0 ∅ (by simp)
    exact le_trans (R2_le_of_ramseyProp h0) (by norm_num)
  · calc R2 k k ≤ (2 * k - 2).choose (k - 1) := by
          have := R2_erdos_szekeres hk hk
          simpa [two_mul] using this
      _ ≤ 2 ^ (2 * k - 2) := Nat.choose_le_two_pow _ _
      _ ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 ^ k := by rw [pow_mul]; norm_num

private lemma R2_one_left (l : ℕ) (hl : 1 ≤ l) : R2 1 l = 1 :=
  le_antisymm (R2_le_of_ramseyProp (ramseyProp_one_left l)) (R2_pos le_rfl hl)

private lemma R2_one_right (k : ℕ) (hk : 1 ≤ k) : R2 k 1 = 1 := by
  rw [R2_symm]; exact R2_one_left k hk

/-- Public pure-Mathlib Erdős–Szekeres off-diagonal upper bound. -/
theorem ppl042_erdos_szekeres_offdiag (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree k ∧ Gᶜ.CliqueFree l)} ≤
      (k + l - 2).choose (k - 1) :=
  R2_erdos_szekeres hk hl

/-! ### Section 2: Exact Small Ramsey Values (`R(3,3) = 6`, `R(3,4) = 9`, `R(4,4) = 18`, 0 `native_decide`) -/

/-- `C_5` on `Fin 5`: triangle-free and self-complementary. -/
private def c5Graph : SimpleGraph (Fin 5) where
  Adj u v := (u.val + 5 - v.val) % 5 = 1 ∨ (u.val + 5 - v.val) % 5 = 4
  symm := ⟨fun u v h => by omega⟩
  loopless := ⟨fun u h => by omega⟩

private lemma c5_cliqueFree_three : c5Graph.CliqueFree 3 := by
  intro s hs
  rcases Finset.card_eq_three.mp hs.card_eq with ⟨a, b, c, hab, hac, hbc, rfl⟩
  have h1 : c5Graph.Adj a b := hs.1 (by simp) (by simp) hab
  have h2 : c5Graph.Adj a c := hs.1 (by simp) (by simp) hac
  have h3 : c5Graph.Adj b c := hs.1 (by simp) (by simp) hbc
  simp only [c5Graph] at h1 h2 h3
  omega

private lemma c5_compl_cliqueFree_three : c5Graphᶜ.CliqueFree 3 := by
  intro s hs
  rcases Finset.card_eq_three.mp hs.card_eq with ⟨a, b, c, hab, hac, hbc, rfl⟩
  have h1 : c5Graphᶜ.Adj a b := hs.1 (by simp) (by simp) hab
  have h2 : c5Graphᶜ.Adj a c := hs.1 (by simp) (by simp) hac
  have h3 : c5Graphᶜ.Adj b c := hs.1 (by simp) (by simp) hbc
  simp only [SimpleGraph.compl_adj, c5Graph] at h1 h2 h3
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
  have hne1 : a.val ≠ b.val := Fin.val_ne_of_ne hab
  have hne2 : a.val ≠ c.val := Fin.val_ne_of_ne hac
  have hne3 : b.val ≠ c.val := Fin.val_ne_of_ne hbc
  omega

/-- Exact diagonal Ramsey number `R(3, 3) = 6` (pure Mathlib, `0` `native_decide`). -/
theorem ppl042_ramsey_three_eq_six :
    sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3)} = 6 := by
  have hle : R2 3 3 ≤ 6 := by
    have := R2_erdos_szekeres (k := 3) (l := 3) (by norm_num) (by norm_num)
    norm_num at this
    exact this
  have hgt : 5 < R2 3 3 :=
    lt_R2_of_witness (by norm_num) (by norm_num) c5Graph c5_cliqueFree_three c5_compl_cliqueFree_three
  change R2 3 3 = 6
  omega

/-- Circulant graph on `Fin 8` with differences `{1, 4, 7}`: `K_3`-free with `K_4`-free complement. -/
private def circ8Graph : SimpleGraph (Fin 8) where
  Adj u v :=
    (u.val + 8 - v.val) % 8 = 1 ∨ (u.val + 8 - v.val) % 8 = 4 ∨ (u.val + 8 - v.val) % 8 = 7
  symm := ⟨fun u v h => by omega⟩
  loopless := ⟨fun u h => by omega⟩

private lemma circ8_cliqueFree_three : circ8Graph.CliqueFree 3 := by
  intro s hs
  rcases Finset.card_eq_three.mp hs.card_eq with ⟨a, b, c, hab, hac, hbc, rfl⟩
  have h1 : circ8Graph.Adj a b := hs.1 (by simp) (by simp) hab
  have h2 : circ8Graph.Adj a c := hs.1 (by simp) (by simp) hac
  have h3 : circ8Graph.Adj b c := hs.1 (by simp) (by simp) hbc
  simp only [circ8Graph] at h1 h2 h3
  omega

private lemma circ8_compl_cliqueFree_four : circ8Graphᶜ.CliqueFree 4 := by
  intro s hs
  have h4 : s.card = 4 := hs.card_eq
  obtain ⟨a, ha, rfl_s⟩ : ∃ a ∈ s, (s.erase a).card = 3 := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
    exact ⟨a, ha, by rw [Finset.card_erase_of_mem ha, h4]⟩
  rcases Finset.card_eq_three.mp rfl_s with ⟨b, c, d, hbc, hbd, hcd, hEq⟩
  have hb : b ∈ s ∧ b ≠ a := by
    have : b ∈ s.erase a := by rw [hEq]; simp
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  have hc : c ∈ s ∧ c ≠ a := by
    have : c ∈ s.erase a := by rw [hEq]; simp
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  have hd : d ∈ s ∧ d ≠ a := by
    have : d ∈ s.erase a := by rw [hEq]; simp
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  have h1 := hs.1 ha hb.1 hb.2.symm
  have h2 := hs.1 ha hc.1 hc.2.symm
  have h3 := hs.1 ha hd.1 hd.2.symm
  have h4' := hs.1 hb.1 hc.1 hbc
  have h5 := hs.1 hb.1 hd.1 hbd
  have h6 := hs.1 hc.1 hd.1 hcd
  simp only [SimpleGraph.compl_adj, circ8Graph] at h1 h2 h3 h4' h5 h6
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  have := Fin.val_ne_of_ne hb.2; have := Fin.val_ne_of_ne hc.2; have := Fin.val_ne_of_ne hd.2
  have := Fin.val_ne_of_ne hbc; have := Fin.val_ne_of_ne hbd; have := Fin.val_ne_of_ne hcd
  omega

/-- Handshaking-parity proof of `R(3, 4) ≤ 9`. -/
private lemma ramseyProp_three_four_nine : ramseyProp 3 4 9 := by
  intro G ⟨hG3, hG4⟩
  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  have hR33 : ramseyProp 3 3 6 := by
    have h6 : R2 3 3 = 6 := ppl042_ramsey_three_eq_six
    rw [← h6]
    exact R2_spec (by norm_num) (by norm_num)
  have hR24 : ramseyProp 2 4 4 := ramseyProp_two_left 4
  have hdeg_eq_three : ∀ v : Fin 9, G.degree v = 3 := by
    intro v
    let NR := G.neighborFinset v
    let NB := Finset.univ.filter (fun u => u ≠ v ∧ ¬G.Adj v u)
    have hdisj : Disjoint NR NB := by
      rw [Finset.disjoint_left]
      intro u huR huB
      rw [SimpleGraph.mem_neighborFinset] at huR
      simp only [NB, mem_filter, mem_univ, true_and] at huB
      exact huB.2 huR
    have hunion : NR ∪ NB = Finset.univ.erase v := by
      ext u
      simp only [NR, NB, mem_union, SimpleGraph.mem_neighborFinset, mem_filter, mem_univ,
        true_and, mem_erase, and_true]
      constructor
      · rintro (hR | ⟨hne, _⟩)
        · exact (G.ne_of_adj hR).symm
        · exact hne
      · intro hne
        by_cases hR : G.Adj v u
        · exact Or.inl hR
        · exact Or.inr ⟨hne, hR⟩
    have hsum : NR.card + NB.card = 8 := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_erase_of_mem (mem_univ v),
        Finset.card_univ, Fintype.card_fin]
    have hNR_lt : NR.card < 4 := by
      by_contra hge
      push Not at hge
      rcases exists_clique_in_subset (G := G) NR hR24 hge with ⟨t, htNR, ht⟩ | ⟨t, _, ht⟩
      · have hv : v ∉ t := fun hvt =>
          G.loopless.irrefl v ((SimpleGraph.mem_neighborFinset G v v).mp (htNR hvt))
        apply hG3 (insert v t)
        refine ⟨?_, by rw [Finset.card_insert_of_notMem hv, ht.card_eq]⟩
        intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with hxv | hx <;>
        rcases Finset.mem_insert.mp hy with hyv | hy
        · exact absurd (hxv.trans hyv.symm) hxy
        · rw [hxv]; exact (SimpleGraph.mem_neighborFinset G v y).mp (htNR hy)
        · rw [hyv]; exact ((SimpleGraph.mem_neighborFinset G v x).mp (htNR hx)).symm
        · exact ht.1 hx hy hxy
      · exact hG4 t ht
    have hNB_lt : NB.card < 6 := by
      by_contra hge
      push Not at hge
      rcases exists_clique_in_subset (G := G) NB hR33 hge with ⟨t, _, ht⟩ | ⟨t, htNB, ht⟩
      · exact hG3 t ht
      · have hv : v ∉ t := fun hvt => (mem_filter.mp (htNB hvt)).2.1 rfl
        apply hG4 (insert v t)
        refine ⟨?_, by rw [Finset.card_insert_of_notMem hv, ht.card_eq]⟩
        intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with hxv | hx <;>
        rcases Finset.mem_insert.mp hy with hyv | hy
        · exact absurd (hxv.trans hyv.symm) hxy
        · rw [hxv] at hxy ⊢; exact ⟨hxy, (mem_filter.mp (htNB hy)).2.2⟩
        · rw [hyv] at hxy ⊢; exact ⟨hxy, fun h => (mem_filter.mp (htNB hx)).2.2 h.symm⟩
        · exact ht.1 hx hy hxy
    have hdeg_eq : G.degree v = NR.card := rfl
    omega
  have hhandshake := G.sum_degrees_eq_twice_card_edges
  have hsum27 : ∑ v : Fin 9, G.degree v = 27 := by
    simp [hdeg_eq_three]
  omega

/-- Exact off-diagonal Ramsey number `R(3, 4) = 9` (pure Mathlib, `0` `native_decide`). -/
theorem ppl042_ramsey_three_four_eq_nine :
    sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree 3 ∧ Gᶜ.CliqueFree 4)} = 9 := by
  have hle : R2 3 4 ≤ 9 := R2_le_of_ramseyProp ramseyProp_three_four_nine
  have hgt : 8 < R2 3 4 :=
    lt_R2_of_witness (by norm_num) (by norm_num) circ8Graph circ8_cliqueFree_three
      circ8_compl_cliqueFree_four
  change R2 3 4 = 9
  omega

/-- Nonzero quadratic residues mod 17: `{1, 2, 4, 8, 9, 13, 15, 16}`. -/
private abbrev isQR17 (x : ZMod 17) : Prop :=
  x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 8 ∨ x = 9 ∨ x = 13 ∨ x = 15 ∨ x = 16

private lemma isQR17_neg {x : ZMod 17} (h : isQR17 x) : isQR17 (-x) := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma isQR17_ne_zero {x : ZMod 17} (h : isQR17 x) : x ≠ 0 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma isQR17_mul {x y : ZMod 17} (hx : isQR17 x) (hy : isQR17 y) :
    isQR17 (x * y) := by
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

private lemma isQR17_exists_inv {x : ZMod 17} (hx : isQR17 x) :
    ∃ z : ZMod 17, isQR17 z ∧ x * z = 1 := by
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨9, by decide, by decide⟩
  · exact ⟨13, by decide, by decide⟩
  · exact ⟨15, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨4, by decide, by decide⟩
  · exact ⟨8, by decide, by decide⟩
  · exact ⟨16, by decide, by decide⟩

private lemma isQR17_three_mul_iff (x : ZMod 17) (hx : x ≠ 0) :
    isQR17 (3 * x) ↔ ¬isQR17 x := by
  have hxeq : x = (x.val : ZMod 17) := (ZMod.natCast_zmod_val x).symm
  have hxlt : x.val < 17 := x.val_lt
  rw [hxeq] at hx ⊢
  interval_cases hv : x.val
  · exact absurd rfl hx
  all_goals
    constructor
    · intro h1 h2; revert h1 h2; decide
    · intro h1; first | (exfalso; apply h1; decide) | decide

/-- Paley graph `P(17)` on `Fin 17`: `u ~ v` iff `(u - v : ZMod 17)` is a nonzero square mod 17. -/
private def paley17 : SimpleGraph (Fin 17) where
  Adj u v := isQR17 ((u.val : ZMod 17) - (v.val : ZMod 17))
  symm := ⟨fun u v h => by
    have hneg := isQR17_neg h
    rwa [neg_sub] at hneg⟩
  loopless := ⟨fun u h => by
    rw [sub_self] at h
    exact isQR17_ne_zero h rfl⟩

private lemma paley17_cliqueFree_four : paley17.CliqueFree 4 := by
  intro s hs
  have h4 : s.card = 4 := hs.card_eq
  obtain ⟨a, ha, hcard3⟩ : ∃ a ∈ s, (s.erase a).card = 3 := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
    exact ⟨a, ha, by rw [Finset.card_erase_of_mem ha, h4]⟩
  rcases Finset.card_eq_three.mp hcard3 with ⟨b, c, d, hbc, hbd, hcd, hEq⟩
  have hb : b ∈ s ∧ b ≠ a := by
    have : b ∈ s.erase a := by rw [hEq]; simp
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  have hc : c ∈ s ∧ c ≠ a := by
    have : c ∈ s.erase a := by rw [hEq]; simp
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  have hd : d ∈ s ∧ d ≠ a := by
    have : d ∈ s.erase a := by rw [hEq]; simp
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  have hab : isQR17 ((b.val : ZMod 17) - (a.val : ZMod 17)) := hs.1 hb.1 ha hb.2
  have hac : isQR17 ((c.val : ZMod 17) - (a.val : ZMod 17)) := hs.1 hc.1 ha hc.2
  have had : isQR17 ((d.val : ZMod 17) - (a.val : ZMod 17)) := hs.1 hd.1 ha hd.2
  have hcb : isQR17 ((c.val : ZMod 17) - (b.val : ZMod 17)) := hs.1 hc.1 hb.1 hbc.symm
  have hdb : isQR17 ((d.val : ZMod 17) - (b.val : ZMod 17)) := hs.1 hd.1 hb.1 hbd.symm
  have hcd' : isQR17 ((c.val : ZMod 17) - (d.val : ZMod 17)) := hs.1 hc.1 hd.1 hcd
  set x : ZMod 17 := (b.val : ZMod 17) - (a.val : ZMod 17)
  obtain ⟨xinv, hxinv, hmul⟩ := isQR17_exists_inv hab
  set u : ZMod 17 := ((c.val : ZMod 17) - (a.val : ZMod 17)) * xinv
  set v : ZMod 17 := ((d.val : ZMod 17) - (a.val : ZMod 17)) * xinv
  have hu : isQR17 u := isQR17_mul hac hxinv
  have hv : isQR17 v := isQR17_mul had hxinv
  have hu1 : isQR17 (u - 1) := by
    have hEq1 : u - 1 = ((c.val : ZMod 17) - (b.val : ZMod 17)) * xinv := by
      calc u - 1 = ((c.val : ZMod 17) - (a.val : ZMod 17)) * xinv - x * xinv := by rw [hmul]
        _ = ((c.val : ZMod 17) - (a.val : ZMod 17) - x) * xinv := by ring
        _ = ((c.val : ZMod 17) - (b.val : ZMod 17)) * xinv := by simp only [x]; ring
    rw [hEq1]
    exact isQR17_mul hcb hxinv
  have hv1 : isQR17 (v - 1) := by
    have hEq1 : v - 1 = ((d.val : ZMod 17) - (b.val : ZMod 17)) * xinv := by
      calc v - 1 = ((d.val : ZMod 17) - (a.val : ZMod 17)) * xinv - x * xinv := by rw [hmul]
        _ = ((d.val : ZMod 17) - (a.val : ZMod 17) - x) * xinv := by ring
        _ = ((d.val : ZMod 17) - (b.val : ZMod 17)) * xinv := by simp only [x]; ring
    rw [hEq1]
    exact isQR17_mul hdb hxinv
  have huv : isQR17 (u - v) := by
    have hEq2 : u - v = ((c.val : ZMod 17) - (d.val : ZMod 17)) * xinv := by
      simp only [u, v]; ring
    rw [hEq2]
    exact isQR17_mul hcd' hxinv
  have honly : ∀ z : ZMod 17, isQR17 z → isQR17 (z - 1) → z = 2 ∨ z = 9 ∨ z = 16 := by
    intro z hz hz1
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hz1 <;> decide
  rcases honly u hu hu1 with hu_eq | hu_eq | hu_eq <;>
  rcases honly v hv hv1 with hv_eq | hv_eq | hv_eq <;>
    rw [hu_eq, hv_eq] at huv <;> revert huv <;> decide

private lemma paley17_compl_cliqueFree_four : paley17ᶜ.CliqueFree 4 := by
  intro s hs
  let f : Fin 17 ↪ Fin 17 :=
    ⟨fun i => ⟨(3 * i.val) % 17, Nat.mod_lt _ (by norm_num)⟩, by
      intro i j hij
      have hval : (3 * i.val) % 17 = (3 * j.val) % 17 := congrArg Fin.val hij
      have hi := i.isLt; have hj := j.isLt
      exact Fin.ext (by omega)⟩
  apply paley17_cliqueFree_four (s.map f)
  refine ⟨?_, by simp [hs.card_eq]⟩
  intro a ha b hb hab
  rcases Finset.mem_map.mp ha with ⟨a', ha', rfl⟩
  rcases Finset.mem_map.mp hb with ⟨b', hb', rfl⟩
  have hab' : a' ≠ b' := fun hEq => hab (congrArg f hEq)
  have hcomp := hs.1 ha' hb' hab'
  have hnotQR : ¬isQR17 ((a'.val : ZMod 17) - (b'.val : ZMod 17)) := hcomp.2
  have hneZ : ((a'.val : ZMod 17) - (b'.val : ZMod 17)) ≠ 0 := by
    intro h0
    have hEq : (a'.val : ZMod 17) = (b'.val : ZMod 17) := sub_eq_zero.mp h0
    have hmod : a'.val % 17 = b'.val % 17 := by
      have := congrArg ZMod.val hEq
      simpa [ZMod.val_natCast] using this
    rw [Nat.mod_eq_of_lt a'.isLt, Nat.mod_eq_of_lt b'.isLt] at hmod
    exact hab' (Fin.ext hmod)
  have h3 : isQR17 (3 * ((a'.val : ZMod 17) - (b'.val : ZMod 17))) :=
    (isQR17_three_mul_iff _ hneZ).mpr hnotQR
  have hcast : (((3 * a'.val) % 17 : ℕ) : ZMod 17) - (((3 * b'.val) % 17 : ℕ) : ZMod 17) =
      3 * ((a'.val : ZMod 17) - (b'.val : ZMod 17)) := by
    simp [ZMod.natCast_mod, mul_sub]
  have hfval : ∀ i : Fin 17, (f i).val = (3 * i.val) % 17 := fun _ => rfl
  show isQR17 (((f a').val : ZMod 17) - ((f b').val : ZMod 17))
  rw [hfval, hfval, hcast]
  exact h3

/-- Exact diagonal Ramsey number `R(4, 4) = 18` via Paley `P(17)` (pure Mathlib, `0` `native_decide`). -/
theorem ppl042_ramsey_four_eq_eighteen :
    sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree 4 ∧ Gᶜ.CliqueFree 4)} = 18 := by
  have h34 : R2 3 4 = 9 := ppl042_ramsey_three_four_eq_nine
  have h43 : R2 4 3 = 9 := by rw [R2_symm]; exact h34
  have hle : R2 4 4 ≤ 18 := by
    calc R2 4 4 ≤ R2 3 4 + R2 4 3 := R2_step_le (by norm_num) (by norm_num)
      _ = 18 := by rw [h34, h43]
  have hgt : 17 < R2 4 4 :=
    lt_R2_of_witness (by norm_num) (by norm_num) paley17 paley17_cliqueFree_four
      paley17_compl_cliqueFree_four
  change R2 4 4 = 18
  omega

/-! ### Section 3: Finite Edge-Coloring Space, Erdős 1947 First Moment & Symmetric LLL (Spencer 1975) -/

/-- Ordered pairs `(u, v)` with `u < v` in `Fin n` — the edge set of `K_n`. -/
private def edgesFin (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

/-- Edges of `K_n` with both endpoints in `S`. -/
private def edgesOf {n : ℕ} (S : Finset (Fin n)) : Finset (edgesFin n) :=
  Finset.univ.filter (fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S)

private lemma card_edgesOf {n : ℕ} (S : Finset (Fin n)) :
    (edgesOf S).card = S.card.choose 2 := by
  rw [← Finset.card_powersetCard 2 S]
  refine Finset.card_bij (fun e _ => ({e.val.1, e.val.2} : Finset (Fin n))) ?_ ?_ ?_
  · intro e he
    rw [edgesOf, mem_filter] at he
    have hlt : e.val.1 < e.val.2 := (mem_filter.mp e.property).2
    rw [Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_pair (ne_of_lt hlt)⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact he.2.1
    · rw [Finset.mem_singleton.mp hx]; exact he.2.2
  · intro e1 _ e2 _ hEq
    have hlt1 : e1.val.1 < e1.val.2 := (mem_filter.mp e1.property).2
    have hlt2 : e2.val.1 < e2.val.2 := (mem_filter.mp e2.property).2
    have h1in : e1.val.1 ∈ ({e2.val.1, e2.val.2} : Finset (Fin n)) := by rw [← hEq]; simp
    have h2in : e1.val.2 ∈ ({e2.val.1, e2.val.2} : Finset (Fin n)) := by rw [← hEq]; simp
    rcases Finset.mem_insert.mp h1in with h11 | h12
    · rcases Finset.mem_insert.mp h2in with h21 | h22
      · exact absurd (h11.trans h21.symm) (ne_of_lt hlt1)
      · exact Subtype.ext (Prod.ext h11 (Finset.mem_singleton.mp h22))
    · have h12' := Finset.mem_singleton.mp h12
      rcases Finset.mem_insert.mp h2in with h21 | h22
      · exfalso; exact lt_asymm hlt1 (h12'.symm ▸ h21.symm ▸ hlt2)
      · exfalso; exact ne_of_lt hlt1 (h12'.trans (Finset.mem_singleton.mp h22).symm)
  · intro T hT
    rw [Finset.mem_powersetCard] at hT
    rcases Finset.card_eq_two.mp hT.2 with ⟨a, b, hab, rfl⟩
    have ha : a ∈ S := hT.1 (by simp)
    have hb : b ∈ S := hT.1 (by simp)
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · refine ⟨⟨(a, b), mem_filter.mpr ⟨mem_univ _, hlt⟩⟩, ?_, rfl⟩
      rw [edgesOf, mem_filter]; exact ⟨mem_univ _, ha, hb⟩
    · refine ⟨⟨(b, a), mem_filter.mpr ⟨mem_univ _, hgt⟩⟩, ?_, Finset.pair_comm b a⟩
      rw [edgesOf, mem_filter]; exact ⟨mem_univ _, hb, ha⟩

/-- Build a `SimpleGraph (Fin n)` from a 2-coloring `c : edgesFin n → Bool`. -/
private def graphOfColor {n : ℕ} (c : edgesFin n → Bool) : SimpleGraph (Fin n) where
  Adj u v :=
    if hlt : u < v then c ⟨(u, v), mem_filter.mpr ⟨mem_univ _, hlt⟩⟩ = true
    else if hgt : v < u then c ⟨(v, u), mem_filter.mpr ⟨mem_univ _, hgt⟩⟩ = true
    else False
  symm := ⟨fun u v h => by
    by_cases hlt : u < v
    · have hng : ¬(v < u) := not_lt.mpr (le_of_lt hlt)
      simp only [hlt, dite_true] at h
      simp only [hng, dite_false, hlt, dite_true, h]
    · by_cases hgt : v < u
      · simp only [hlt, dite_false, hgt, dite_true] at h
        simp only [hgt, dite_true, h]
      · simp only [hlt, dite_false, hgt, dite_false] at h⟩
  loopless := ⟨fun u h => by
    have hnl : ¬(u < u) := lt_irrefl u
    simp only [hnl, dite_false] at h⟩

/-- The bad event: `S` is monochromatic (all `true` or all `false`) on `edgesOf S`. -/
private def monoEvent {n : ℕ} (S : Finset (Fin n)) : Finset (edgesFin n → Bool) :=
  Finset.univ.filter (fun c =>
    (∀ e ∈ edgesOf S, c e = true) ∨ (∀ e ∈ edgesOf S, c e = false))

private lemma graphOfColor_cliqueFree_of_not_mono {n k : ℕ} (c : edgesFin n → Bool)
    (h : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, c ∉ monoEvent S) :
    (graphOfColor c).CliqueFree k ∧ (graphOfColor c)ᶜ.CliqueFree k := by
  refine ⟨?_, ?_⟩
  · intro S hS
    apply h S (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS.card_eq⟩)
    rw [monoEvent, mem_filter]
    refine ⟨mem_univ _, Or.inl ?_⟩
    intro e he
    rw [edgesOf, mem_filter] at he
    have hlt : e.val.1 < e.val.2 := (mem_filter.mp e.property).2
    have hadj := hS.1 he.2.1 he.2.2 (ne_of_lt hlt)
    simpa [graphOfColor, hlt] using hadj
  · intro S hS
    apply h S (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS.card_eq⟩)
    rw [monoEvent, mem_filter]
    refine ⟨mem_univ _, Or.inr ?_⟩
    intro e he
    rw [edgesOf, mem_filter] at he
    have hlt : e.val.1 < e.val.2 := (mem_filter.mp e.property).2
    have hadj := (hS.1 he.2.1 he.2.2 (ne_of_lt hlt)).2
    have hnt : ¬(c e = true) := by simpa [graphOfColor, hlt] using hadj
    cases hce : c e with
    | false => rfl
    | true => exact absurd hce hnt

/-- Exact size of an event fixing all coordinates in `A` to a constant value `b`. -/
private lemma card_const_on_subset {E : Type*} [Fintype E] [DecidableEq E]
    (A : Finset E) (b : Bool) :
    (Finset.univ.filter (fun c : E → Bool => ∀ e ∈ A, c e = b)).card =
      2 ^ (Fintype.card E - A.card) := by
  let eEquiv : (E → Bool) ≃ ({x : E // x ∈ A} → Bool) × ({x : E // x ∉ A} → Bool) :=
    (Equiv.piCongrLeft' (fun _ => Bool) (Equiv.sumCompl (· ∈ A))).symm.trans
      (Equiv.sumArrowEquivProdArrow _ _ _)
  have hcard :
      (Finset.univ.filter (fun c : E → Bool => ∀ e ∈ A, c e = b)).card =
        Fintype.card ({x : E // x ∉ A} → Bool) := by
    refine Finset.card_bij (fun c _ x => c x.val) ?_ ?_ ?_
    · intro _ _; exact mem_univ _
    · intro c1 hc1 c2 hc2 hEq
      have h1 := (mem_filter.mp hc1).2
      have h2 := (mem_filter.mp hc2).2
      funext e
      by_cases he : e ∈ A
      · exact (h1 e he).trans (h2 e he).symm
      · exact congrFun hEq ⟨e, he⟩
    · intro f _
      refine ⟨fun e => if he : e ∈ A then b else f ⟨e, he⟩, ?_, ?_⟩
      · rw [mem_filter]
        refine ⟨mem_univ _, fun e he => by simp [he]⟩
      · funext ⟨e, he⟩
        simp [he]
  rw [hcard, Fintype.card_fun, Fintype.card_bool]
  congr 1
  have hcompl : Fintype.card {x : E // x ∉ A} = (Finset.univ \ A).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp
  rw [hcompl, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]

private lemma card_monoEvent_le {n : ℕ} (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    (monoEvent S).card * 2 ^ (S.card.choose 2) = 2 * Fintype.card (edgesFin n → Bool) := by
  set A := edgesOf S
  have hAcard : A.card = S.card.choose 2 := card_edgesOf S
  have hApos : 0 < A.card := by
    rw [hAcard]
    exact Nat.choose_pos hS
  let Btrue := Finset.univ.filter (fun c : edgesFin n → Bool => ∀ e ∈ A, c e = true)
  let Bfalse := Finset.univ.filter (fun c : edgesFin n → Bool => ∀ e ∈ A, c e = false)
  have hdisj : Disjoint Btrue Bfalse := by
    rw [Finset.disjoint_left]
    intro c ht hf
    obtain ⟨e, he⟩ := Finset.card_pos.mp hApos
    have h1 := (mem_filter.mp ht).2 e he
    have h2 := (mem_filter.mp hf).2 e he
    rw [h1] at h2
    exact Bool.noConfusion h2
  have hunion : monoEvent S = Btrue ∪ Bfalse := by
    ext c
    simp [monoEvent, Btrue, Bfalse, A]
  rw [hunion, Finset.card_union_of_disjoint hdisj,
    card_const_on_subset A true, card_const_on_subset A false]
  have hle : A.card ≤ Fintype.card (edgesFin n) := Finset.card_le_univ A
  rw [Fintype.card_fun, Fintype.card_bool, ← hAcard, ← two_mul, mul_assoc, ← pow_add,
    Nat.sub_add_cancel hle]

/-- **Erdős (1947) First-Moment Finite Lower Bound** (pure Mathlib signature). -/
theorem ppl042_erdos_first_moment_lower (k n : ℕ) (hk : 2 ≤ k)
    (h : (n.choose k : ℝ) * 2 < (2 : ℝ) ^ (k.choose 2)) :
    n < sInf {m : ℕ | ∀ G : SimpleGraph (Fin m), ¬(G.CliqueFree k ∧ Gᶜ.CliqueFree k)} := by
  let Ω := edgesFin n → Bool
  let cliques := (Finset.univ : Finset (Fin n)).powersetCard k
  let bad := cliques.biUnion monoEvent
  have hbad_le : (bad.card : ℝ) * (2 : ℝ) ^ (k.choose 2) ≤
      (n.choose k : ℝ) * 2 * (Fintype.card Ω : ℝ) := by
    have h1 : (bad.card : ℝ) ≤ ∑ S ∈ cliques, ((monoEvent S).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    calc (bad.card : ℝ) * (2 : ℝ) ^ (k.choose 2)
        ≤ (∑ S ∈ cliques, ((monoEvent S).card : ℝ)) * (2 : ℝ) ^ (k.choose 2) := by
          gcongr
      _ = ∑ S ∈ cliques, ((monoEvent S).card : ℝ) * (2 : ℝ) ^ (k.choose 2) := by
          rw [Finset.sum_mul]
      _ = ∑ S ∈ cliques, (2 * Fintype.card Ω : ℝ) := by
          refine Finset.sum_congr rfl (fun S hS => ?_)
          have hScard : S.card = k := (Finset.mem_powersetCard.mp hS).2
          have hEq := card_monoEvent_le S (by omega)
          rw [hScard] at hEq
          exact_mod_cast hEq
      _ = (cliques.card : ℝ) * (2 * Fintype.card Ω : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (n.choose k : ℝ) * 2 * (Fintype.card Ω : ℝ) := by
          have hc : cliques.card = n.choose k := by
            simp [cliques, Finset.card_powersetCard]
          rw [hc]; ring
  have hΩpos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
    have : 0 < Fintype.card Ω := Fintype.card_pos
    exact_mod_cast this
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (k.choose 2) := by positivity
  have hbad_lt : bad.card < Fintype.card Ω := by
    have hlt_real : (bad.card : ℝ) < (Fintype.card Ω : ℝ) := by
      have hmul : (bad.card : ℝ) * (2 : ℝ) ^ (k.choose 2) <
          (Fintype.card Ω : ℝ) * (2 : ℝ) ^ (k.choose 2) := by
        calc (bad.card : ℝ) * (2 : ℝ) ^ (k.choose 2)
            ≤ (n.choose k : ℝ) * 2 * (Fintype.card Ω : ℝ) := hbad_le
          _ < (2 : ℝ) ^ (k.choose 2) * (Fintype.card Ω : ℝ) := by
              exact mul_lt_mul_of_pos_right h hΩpos
          _ = (Fintype.card Ω : ℝ) * (2 : ℝ) ^ (k.choose 2) := by ring
      exact lt_of_mul_lt_mul_right hmul (le_of_lt hpowpos)
    exact_mod_cast hlt_real
  have hex : ∃ c : Ω, c ∉ bad := by
    by_contra hall
    push Not at hall
    have hEq : bad = Finset.univ := Finset.eq_univ_of_forall hall
    rw [hEq, Finset.card_univ] at hbad_lt
    exact lt_irrefl _ hbad_lt
  rcases hex with ⟨c, hc⟩
  have hgood : ∀ S ∈ cliques, c ∉ monoEvent S := by
    intro S hS hmem
    exact hc (Finset.mem_biUnion.mpr ⟨S, hS, hmem⟩)
  obtain ⟨hGk, hGkc⟩ := graphOfColor_cliqueFree_of_not_mono c hgood
  exact lt_R2_of_witness (by omega) (by omega) (graphOfColor c) hGk hGkc

/-- Classic Erdős (1947) exponential lower bound: `2^{k/2} < R(k)` for all `k ≥ 3`. -/
theorem ppl042_erdos_1947_exp_lower (k : ℕ) (hk : 3 ≤ k) :
    (2 : ℝ) ^ ((k : ℝ) / 2) <
      ((sInf {m : ℕ | ∀ G : SimpleGraph (Fin m), ¬(G.CliqueFree k ∧ Gᶜ.CliqueFree k)} : ℕ) : ℝ) := by
  set n : ℕ := Nat.floor ((2 : ℝ) ^ ((k : ℝ) / 2))
  have hn_le : (n : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) / 2) := Nat.floor_le (by positivity)
  have hlt_succ : (2 : ℝ) ^ ((k : ℝ) / 2) < (n + 1 : ℝ) := Nat.lt_floor_add_one _
  have hchoose_le : (n.choose k : ℝ) * (k.factorial : ℝ) ≤ (n : ℝ) ^ k := by
    have hnat : n.choose k * k.factorial ≤ n ^ k := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow n k
    exact_mod_cast hnat
  have hsq_lt : (4 : ℝ) * (2 : ℝ) ^ k < ((k.factorial : ℝ)) ^ 2 := by
    have hnat_all : ∀ m : ℕ, 3 ≤ m → 4 * 2 ^ m < m.factorial * m.factorial := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => norm_num [Nat.factorial]
      | succ r hr ih =>
        have hstep : 2 ≤ (r + 1) * (r + 1) := by nlinarith
        calc 4 * 2 ^ (r + 1) = 2 * (4 * 2 ^ r) := by ring
          _ < 2 * (r.factorial * r.factorial) := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
          _ ≤ ((r + 1) * (r + 1)) * (r.factorial * r.factorial) := Nat.mul_le_mul_right _ hstep
          _ = (r + 1).factorial * (r + 1).factorial := by
              rw [Nat.factorial_succ]; ring
    have hreal : (4 * 2 ^ k : ℝ) < (k.factorial * k.factorial : ℝ) := by
      exact_mod_cast hnat_all k hk
    linarith [sq (k.factorial : ℝ)]
  have h2pow_lt : (2 : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) < (k.factorial : ℝ) := by
    have hpos1 : 0 ≤ (2 : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) := by positivity
    have hpos2 : 0 ≤ (k.factorial : ℝ) := by positivity
    have hsq : ((2 : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 < ((k.factorial : ℝ)) ^ 2 := by
      have h2eq : ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ k := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ ((k : ℝ) / 2)) 2,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        have hmul : (k : ℝ) / 2 * (2 : ℕ) = (k : ℝ) := by push_cast; ring
        rw [hmul, Real.rpow_natCast]
      calc ((2 : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2
          = 4 * ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 := by ring
        _ = 4 * (2 : ℝ) ^ k := by rw [h2eq]
        _ < ((k.factorial : ℝ)) ^ 2 := hsq_lt
    nlinarith
  have hcond : (n.choose k : ℝ) * 2 < (2 : ℝ) ^ (k.choose 2) := by
    have hfact_pos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
    have hpow_nk : (n : ℝ) ^ k ≤ (2 : ℝ) ^ ((k : ℝ) / 2 * (k : ℝ)) := by
      calc (n : ℝ) ^ k ≤ ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ k := pow_le_pow_left₀ (by positivity) hn_le k
        _ = (2 : ℝ) ^ ((k : ℝ) / 2 * (k : ℝ)) := by
            rw [← Real.rpow_natCast ((2 : ℝ) ^ ((k : ℝ) / 2)) k,
              ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hpow_eq : (2 : ℝ) ^ ((k : ℝ) / 2 * (k : ℝ)) =
        (2 : ℝ) ^ ((k : ℝ) / 2) * (2 : ℝ) ^ (k.choose 2) := by
      rw [← Real.rpow_natCast (2 : ℝ) (k.choose 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      have hch : (k.choose 2 : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
        have hnat : 2 * k.choose 2 = k * (k - 1) := by
          rw [Nat.choose_two_right]
          exact Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd
        have hreal : (2 : ℝ) * (k.choose 2 : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
          have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ k)]; simp
          rw [← this]
          exact_mod_cast hnat
        linarith
      rw [hch]; ring
    have hmul : (n.choose k : ℝ) * 2 * (k.factorial : ℝ) <
        (2 : ℝ) ^ (k.choose 2) * (k.factorial : ℝ) := by
      calc (n.choose k : ℝ) * 2 * (k.factorial : ℝ)
          = 2 * ((n.choose k : ℝ) * (k.factorial : ℝ)) := by ring
        _ ≤ 2 * (n : ℝ) ^ k := by linarith
        _ ≤ 2 * (2 : ℝ) ^ ((k : ℝ) / 2 * (k : ℝ)) := by linarith
        _ = (2 * (2 : ℝ) ^ ((k : ℝ) / 2)) * (2 : ℝ) ^ (k.choose 2) := by rw [hpow_eq]; ring
        _ < (k.factorial : ℝ) * (2 : ℝ) ^ (k.choose 2) := by
            exact mul_lt_mul_of_pos_right h2pow_lt (by positivity)
        _ = (2 : ℝ) ^ (k.choose 2) * (k.factorial : ℝ) := by ring
    exact lt_of_mul_lt_mul_right hmul (le_of_lt hfact_pos)
  have hlt_nat : n < R2 k k := ppl042_erdos_first_moment_lower k n (by omega) hcond
  have hle_nat : n + 1 ≤ R2 k k := hlt_nat
  have hle_real : (n + 1 : ℝ) ≤ (R2 k k : ℝ) := by exact_mod_cast hle_nat
  exact lt_of_lt_of_le hlt_succ hle_real

/-! #### Finite Symmetric Lovász Local Lemma on `E → Bool` (Zero MeasureTheory!) -/

/-- Event `B ⊆ (E → Bool)` depends only on coordinates in `I ⊆ E`. -/
private def DependsOn {E : Type*} (I : Finset E) (B : Finset (E → Bool)) : Prop :=
  ∀ c1 c2 : E → Bool, (∀ e ∈ I, c1 e = c2 e) → (c1 ∈ B ↔ c2 ∈ B)

private lemma dependsOn_mono {E : Type*} {I J : Finset E} {B : Finset (E → Bool)}
    (hIJ : I ⊆ J) (h : DependsOn I B) : DependsOn J B :=
  fun c1 c2 hc => h c1 c2 (fun e he => hc e (hIJ he))

private lemma dependsOn_compl {E : Type*} [Fintype E] [DecidableEq E]
    {I : Finset E} {B : Finset (E → Bool)} (h : DependsOn I B) :
    DependsOn I (Finset.univ \ B) := by
  intro c1 c2 hc
  simp [h c1 c2 hc]

private lemma dependsOn_inter {E : Type*} [Fintype E] [DecidableEq E]
    {I J : Finset E} {B1 B2 : Finset (E → Bool)}
    (h1 : DependsOn I B1) (h2 : DependsOn J B2) : DependsOn (I ∪ J) (B1 ∩ B2) := by
  intro c1 c2 hc
  simp only [mem_inter]
  exact and_congr (h1 c1 c2 (fun e he => hc e (mem_union_left J he)))
    (h2 c1 c2 (fun e he => hc e (mem_union_right I he)))

/-- Exact independence of events with disjoint coordinate supports in `(E → Bool)`. -/
private lemma card_inter_eq_mul_of_disjoint_support {E : Type*} [Fintype E] [DecidableEq E]
    {I1 I2 : Finset E} {B1 B2 : Finset (E → Bool)}
    (hdisj : Disjoint I1 I2) (h1 : DependsOn I1 B1) (h2 : DependsOn I2 B2) :
    (B1 ∩ B2).card * Fintype.card (E → Bool) = B1.card * B2.card := by
  -- Bijection `(B1 ∩ B2) × univ ≃ B1 × B2` by swapping coordinates on `I1`!
  let swap : (E → Bool) × (E → Bool) → (E → Bool) × (E → Bool) :=
    fun p => (fun e => if e ∈ I1 then p.1 e else p.2 e,
              fun e => if e ∈ I1 then p.2 e else p.1 e)
  have hswap_inv : ∀ p, swap (swap p) = p := by
    intro ⟨c1, c2⟩
    ext e <;> by_cases he : e ∈ I1 <;> simp [swap, he]
  have hmem_fwd : ∀ p ∈ (B1 ∩ B2) ×ˢ (Finset.univ : Finset (E → Bool)),
      swap p ∈ B1 ×ˢ B2 := by
    intro ⟨c1, c2⟩ hp
    simp only [mem_product, mem_inter, mem_univ, and_true] at hp ⊢
    refine ⟨?_, ?_⟩
    · exact (h1 c1 _ (fun e he => by simp [swap, he])).mp hp.1
    · exact (h2 c1 _ (fun e he => by
        have hnot : e ∉ I1 := Finset.disjoint_right.mp hdisj he
        simp [swap, hnot])).mp hp.2
  have hmem_bwd : ∀ p ∈ B1 ×ˢ B2,
      swap p ∈ (B1 ∩ B2) ×ˢ (Finset.univ : Finset (E → Bool)) := by
    intro ⟨c1, c2⟩ hp
    simp only [mem_product, mem_inter, mem_univ, and_true] at hp ⊢
    refine ⟨?_, ?_⟩
    · exact (h1 c1 _ (fun e he => by simp [swap, he])).mp hp.1
    · exact (h2 c2 _ (fun e he => by
        have hnot : e ∉ I1 := Finset.disjoint_right.mp hdisj he
        simp [swap, hnot])).mp hp.2
  have hbij : ((B1 ∩ B2) ×ˢ (Finset.univ : Finset (E → Bool))).card = (B1 ×ˢ B2).card := by
    refine Finset.card_bij (fun p _ => swap p) hmem_fwd ?_ ?_
    · intro p1 _ p2 _ hEq
      have := congrArg swap hEq
      rwa [hswap_inv, hswap_inv] at this
    · intro q hq
      exact ⟨swap q, hmem_bwd q hq, hswap_inv q⟩
  simpa [Finset.card_product] using hbij

/-- **Symmetric Lovász Local Lemma** on finite uniform product spaces `E → Bool` (pure `Finset`!). -/
private lemma symmetric_lll_bool {E α : Type*} [Fintype E] [DecidableEq E] [DecidableEq α]
    (ι : Finset α) (supp : α → Finset E) (A : α → Finset (E → Bool))
    (hdep : ∀ i ∈ ι, DependsOn (supp i) (A i))
    (p x : ℝ) (d : ℕ)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hp : ∀ i ∈ ι, ((A i).card : ℝ) ≤ p * (Fintype.card (E → Bool) : ℝ))
    (hd : ∀ i ∈ ι, (ι.filter (fun j => j ≠ i ∧ ¬Disjoint (supp i) (supp j))).card ≤ d)
    (hlll : p ≤ x * (1 - x) ^ d) :
    ∃ c : E → Bool, ∀ i ∈ ι, c ∉ A i := by
  let good : Finset α → Finset (E → Bool) := fun J =>
    Finset.univ.filter (fun c => ∀ j ∈ J, c ∉ A j)
  have hgood_dep : ∀ J, J ⊆ ι → DependsOn (J.biUnion supp) (good J) := by
    intro J hJ c1 c2 hc
    simp only [good, mem_filter, mem_univ, true_and]
    refine forall₂_congr (fun j hj => not_congr ?_)
    exact hdep j (hJ hj) c1 c2 (fun e he => hc e (Finset.mem_biUnion.mpr ⟨j, hj, he⟩))
  have hgood_insert : ∀ (J : Finset α) (j : α),
      good (insert j J) = good J \ (A j ∩ good J) := by
    intro J j
    ext c
    simp only [Finset.mem_sdiff, Finset.mem_inter, good, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert]
    constructor
    · intro h
      exact ⟨fun j' hj' => h j' (Or.inr hj'), fun ⟨hj, _⟩ => h j (Or.inl rfl) hj⟩
    · rintro ⟨h1, h2⟩ j' (rfl | hj')
      · exact fun hmem => h2 ⟨hmem, h1⟩
      · exact h1 j' hj'
  have hgood_card_insert : ∀ (J : Finset α) (j : α),
      ((good (insert j J)).card : ℝ) = ((good J).card : ℝ) - ((A j ∩ good J).card : ℝ) := by
    intro J j
    rw [hgood_insert]
    have hsub : A j ∩ good J ⊆ good J := Finset.inter_subset_right
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  -- Main induction on `|J|`: `0 < (good J).card` and for all `i ∈ ι \ J`,
  -- `(A i ∩ good J).card ≤ x * (good J).card`.
  have hmain : ∀ m : ℕ, ∀ J ⊆ ι, J.card = m →
      0 < (good J).card ∧ ∀ i ∈ ι, i ∉ J → ((A i ∩ good J).card : ℝ) ≤ x * ((good J).card : ℝ) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro J hJ hJcard
      -- First prove `0 < (good J).card`.
      have hpos : 0 < (good J).card := by
        rcases Finset.eq_empty_or_nonempty J with rfl | ⟨j0, hj0⟩
        · have hge : good ∅ = Finset.univ := by ext c; simp [good]
          rw [hge, Finset.card_univ]
          exact Fintype.card_pos
        · let J' := J.erase j0
          have hJ'sub : J' ⊆ ι := Finset.Subset.trans (Finset.erase_subset j0 J) hJ
          have hJ'card : J'.card < m := by
            rw [← hJcard]; exact Finset.card_erase_lt_of_mem hj0
          have hih := ih J'.card hJ'card J' hJ'sub rfl
          have hbound := hih.2 j0 (hJ hj0) (Finset.notMem_erase j0 J)
          have hEqJ : insert j0 J' = J := Finset.insert_erase hj0
          have hcard_pos : (0 : ℝ) < ((good J).card : ℝ) := by
            rw [← hEqJ, hgood_card_insert]
            have h1 : (0 : ℝ) < ((good J').card : ℝ) := by exact_mod_cast hih.1
            nlinarith
          exact_mod_cast hcard_pos
      refine ⟨hpos, ?_⟩
      intro i hi hiJ
      let J1 := J.filter (fun j => ¬Disjoint (supp i) (supp j))
      let J2 := J.filter (fun j => Disjoint (supp i) (supp j))
      have hJ2sub : J2 ⊆ J := Finset.filter_subset _ J
      have hJ1sub_Γ : J1 ⊆ ι.filter (fun j => j ≠ i ∧ ¬Disjoint (supp i) (supp j)) := by
        intro j hj
        rw [mem_filter] at hj ⊢
        refine ⟨hJ hj.1, ?_, hj.2⟩
        intro hEq
        exact hiJ (hEq ▸ hj.1)
      have hJ1card : J1.card ≤ d := le_trans (Finset.card_le_card hJ1sub_Γ) (hd i hi)
      have hdisj_supp : Disjoint (supp i) (J2.biUnion supp) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact (mem_filter.mp hj).2
      have hindep :
          ((A i ∩ good J2).card : ℝ) * (Fintype.card (E → Bool) : ℝ) =
            ((A i).card : ℝ) * ((good J2).card : ℝ) := by
        exact_mod_cast card_inter_eq_mul_of_disjoint_support hdisj_supp
          (hdep i hi) (hgood_dep J2 (Finset.Subset.trans hJ2sub hJ))
      have hnum : ((A i ∩ good J).card : ℝ) ≤ p * ((good J2).card : ℝ) := by
        have hsub : A i ∩ good J ⊆ A i ∩ good J2 := by
          intro c hc
          simp only [mem_inter, good, mem_filter, mem_univ, true_and] at hc ⊢
          exact ⟨hc.1, fun j hj => hc.2 j (hJ2sub hj)⟩
        have hle1 : ((A i ∩ good J).card : ℝ) ≤ ((A i ∩ good J2).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        have hΩpos : (0 : ℝ) < (Fintype.card (E → Bool) : ℝ) := by
          exact_mod_cast (Fintype.card_pos (α := E → Bool))
        have hle2 : ((A i ∩ good J2).card : ℝ) ≤ p * ((good J2).card : ℝ) := by
          have hmul : ((A i ∩ good J2).card : ℝ) * (Fintype.card (E → Bool) : ℝ) ≤
              p * ((good J2).card : ℝ) * (Fintype.card (E → Bool) : ℝ) := by
            rw [hindep]
            have := hp i hi
            nlinarith
          exact le_of_mul_le_mul_right hmul hΩpos
        exact le_trans hle1 hle2
      -- Lower bound `(good J).card ≥ (1 - x)^|J1| * (good J2).card` by peeling `J1` one by one!
      have hJ_eq : J = J1 ∪ J2 := by
        ext j
        simp only [J1, J2, mem_union, mem_filter]
        tauto
      have hpeel : ∀ K : Finset α, K ⊆ J1 →
          ((1 - x) ^ K.card) * ((good J2).card : ℝ) ≤ ((good (K ∪ J2)).card : ℝ) := by
        intro K
        induction K using Finset.induction_on with
        | empty =>
          intro _
          simp
        | @insert a K ha ihK =>
          intro hKsub
          have haJ1 : a ∈ J1 := hKsub (mem_insert_self a K)
          have hKsub' : K ⊆ J1 := Finset.Subset.trans (Finset.subset_insert a K) hKsub
          have ha_not_J2 : a ∉ J2 := by
            intro haJ2
            exact (mem_filter.mp haJ1).2 (mem_filter.mp haJ2).2
          have ha_not_KJ2 : a ∉ K ∪ J2 := by
            simp [ha, ha_not_J2]
          have hKJ2_sub_J : K ∪ J2 ⊆ J := by
            rw [hJ_eq]
            exact Finset.union_subset_union_left (Finset.Subset.trans hKsub' (Finset.Subset.refl _))
          have hKJ2_lt : (K ∪ J2).card < m := by
            rw [← hJcard]
            exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
              ⟨hKJ2_sub_J, fun hEq => ha_not_KJ2 (hEq.symm ▸ (mem_filter.mp haJ1).1)⟩)
          have hih_a := ih (K ∪ J2).card hKJ2_lt (K ∪ J2) (Finset.Subset.trans hKJ2_sub_J hJ) rfl
          have hbound_a := hih_a.2 a (hJ (mem_filter.mp haJ1).1) ha_not_KJ2
          have hstep : (1 - x) * ((good (K ∪ J2)).card : ℝ) ≤
              ((good (insert a (K ∪ J2))).card : ℝ) := by
            rw [hgood_card_insert]
            linarith
          have h1x : 0 ≤ 1 - x := by linarith
          calc (1 - x) ^ (insert a K).card * ((good J2).card : ℝ)
              = (1 - x) * ((1 - x) ^ K.card * ((good J2).card : ℝ)) := by
                rw [Finset.card_insert_of_notMem ha, pow_succ]; ring
            _ ≤ (1 - x) * ((good (K ∪ J2)).card : ℝ) := by
                exact mul_le_mul_of_nonneg_left (ihK hKsub') h1x
            _ ≤ ((good (insert a (K ∪ J2))).card : ℝ) := hstep
            _ = ((good (insert a K ∪ J2)).card : ℝ) := by rw [Finset.insert_union]
      have hdenom : (1 - x) ^ d * ((good J2).card : ℝ) ≤ ((good J).card : ℝ) := by
        have h1 := hpeel J1 (Finset.Subset.refl _)
        rw [← hJ_eq] at h1
        have hpow : (1 - x) ^ d ≤ (1 - x) ^ J1.card :=
          pow_le_pow_of_le_one (by linarith) (by linarith) hJ1card
        have hJ2nn : (0 : ℝ) ≤ ((good J2).card : ℝ) := Nat.cast_nonneg _
        exact le_trans (mul_le_mul_of_nonneg_right hpow hJ2nn) h1
      calc ((A i ∩ good J).card : ℝ)
          ≤ p * ((good J2).card : ℝ) := hnum
        _ ≤ (x * (1 - x) ^ d) * ((good J2).card : ℝ) := by
            exact mul_le_mul_of_nonneg_right hlll (Nat.cast_nonneg _)
        _ = x * ((1 - x) ^ d * ((good J2).card : ℝ)) := by ring
        _ ≤ x * ((good J).card : ℝ) := by
            exact mul_le_mul_of_nonneg_left hdenom hx0
  obtain ⟨hpos, _⟩ := hmain ι.card ι (Finset.Subset.refl _) rfl
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  exact ⟨c, (mem_filter.mp hc).2⟩

/-- Elementary inequality `1 / e ≤ (1 - 1 / (d + 1))^d` for all `d : ℕ`. -/
private lemma one_div_exp_le_one_sub_inv_pow (d : ℕ) :
    (Real.exp 1)⁻¹ ≤ (1 - (1 : ℝ) / ((d : ℝ) + 1)) ^ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [pow_zero]
    exact inv_le_one_of_one_le₀ (Real.one_le_exp (by norm_num))
  · have hd0 : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
    have hstep : (1 + (1 : ℝ) / (d : ℝ)) ^ d ≤ Real.exp 1 := by
      calc (1 + (1 : ℝ) / (d : ℝ)) ^ d
          ≤ (Real.exp ((1 : ℝ) / (d : ℝ))) ^ d := by
            have h1 : 1 + (1 : ℝ) / (d : ℝ) ≤ Real.exp ((1 : ℝ) / (d : ℝ)) := by
              linarith [Real.add_one_le_exp ((1 : ℝ) / (d : ℝ))]
            exact pow_le_pow_left₀ (by positivity) h1 d
        _ = Real.exp ((d : ℝ) * ((1 : ℝ) / (d : ℝ))) := by
            rw [← Real.exp_nat_mul]
        _ = Real.exp 1 := by congr 1; field_simp
    have hinv : (1 - (1 : ℝ) / ((d : ℝ) + 1)) = (1 + (1 : ℝ) / (d : ℝ))⁻¹ := by
      field_simp; ring
    rw [hinv, inv_pow]
    exact inv_anti₀ (by positivity) hstep

/-- Overlap bound for the clique dependency graph of `K_n`:
at most `k.choose 2 * (n - 2).choose (k - 2)` other `k`-cliques share an edge with `S`. -/
private lemma clique_dep_deg_le {n k : ℕ} (hk : 2 ≤ k) (S : Finset (Fin n)) (hScard : S.card = k) :
    (((Finset.univ : Finset (Fin n)).powersetCard k).filter
      (fun T => T ≠ S ∧ ¬Disjoint (edgesOf S) (edgesOf T))).card ≤
      k.choose 2 * (n - 2).choose (k - 2) := by
  let pairs := S.powersetCard 2
  let cover : Finset (Finset (Fin n)) :=
    pairs.biUnion (fun P =>
      ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun T => P ⊆ T))
  have hsub :
      (((Finset.univ : Finset (Fin n)).powersetCard k).filter
        (fun T => T ≠ S ∧ ¬Disjoint (edgesOf S) (edgesOf T))) ⊆ cover := by
    intro T hT
    rw [mem_filter] at hT
    have hnotd := hT.2.2
    rw [Finset.not_disjoint_iff] at hnotd
    rcases hnotd with ⟨e, heS, heT⟩
    rw [edgesOf, mem_filter] at heS heT
    have hlt : e.val.1 < e.val.2 := (mem_filter.mp e.property).2
    let P : Finset (Fin n) := {e.val.1, e.val.2}
    refine Finset.mem_biUnion.mpr ⟨P, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair (ne_of_lt hlt)⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact heS.2.1
      · rw [Finset.mem_singleton.mp hx]; exact heS.2.2
    · rw [mem_filter]
      refine ⟨hT.1, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact heT.2.1
      · rw [Finset.mem_singleton.mp hx]; exact heT.2.2
  have hcard_each : ∀ P ∈ pairs,
      (((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun T => P ⊆ T)).card =
        (n - 2).choose (k - 2) := by
    intro P hP
    have hPcard : P.card = 2 := (Finset.mem_powersetCard.mp hP).2
    have hbij :
        (((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun T => P ⊆ T)).card =
          ((Finset.univ \ P).powersetCard (k - 2)).card := by
      refine Finset.card_bij (fun T _ => T \ P) ?_ ?_ ?_
      · intro T hT
        rw [mem_filter, Finset.mem_powersetCard] at hT
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ T) (Finset.Subset.refl P), ?_⟩
        rw [Finset.card_sdiff_of_subset hT.2, hT.1.2, hPcard]
      · intro T1 hT1 T2 hT2 hEq
        have h1 := (mem_filter.mp hT1).2
        have h2 := (mem_filter.mp hT2).2
        calc T1 = (T1 \ P) ∪ P := (Finset.sdiff_union_of_subset h1).symm
          _ = (T2 \ P) ∪ P := by rw [hEq]
          _ = T2 := Finset.sdiff_union_of_subset h2
      · intro U hU
        rw [Finset.mem_powersetCard] at hU
        have hdisj : Disjoint U P := Finset.disjoint_of_subset_left hU.1 disjoint_sdiff_self_left
        refine ⟨U ∪ P, ?_, Finset.union_sdiff_cancel_right hdisj⟩
        rw [mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.subset_union_right⟩
        rw [Finset.card_union_of_disjoint hdisj, hU.2, hPcard, Nat.sub_add_cancel hk]
    rw [hbij, Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ P),
      Finset.card_univ, Fintype.card_fin, hPcard]
  calc (((Finset.univ : Finset (Fin n)).powersetCard k).filter
          (fun T => T ≠ S ∧ ¬Disjoint (edgesOf S) (edgesOf T))).card
      ≤ cover.card := Finset.card_le_card hsub
    _ ≤ ∑ P ∈ pairs,
          (((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun T => P ⊆ T)).card :=
        Finset.card_biUnion_le
    _ = ∑ _P ∈ pairs, (n - 2).choose (k - 2) :=
        Finset.sum_congr rfl hcard_each
    _ = pairs.card * (n - 2).choose (k - 2) := by rw [Finset.sum_const, smul_eq_mul]
    _ = k.choose 2 * (n - 2).choose (k - 2) := by
        rw [Finset.card_powersetCard, hScard]

/-- **Spencer (1975) Symmetric LLL Finite Diagonal Ramsey Lower Bound** (pure Mathlib signature). -/
theorem ppl027_spencer_1975_lll_finite (k n : ℕ) (hk : 3 ≤ k)
    (h : Real.exp 1 * 2 * ((k.choose 2 * (n - 2).choose (k - 2) + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (k.choose 2)) :
    n < sInf {m : ℕ | ∀ G : SimpleGraph (Fin m), ¬(G.CliqueFree k ∧ Gᶜ.CliqueFree k)} := by
  let ι := (Finset.univ : Finset (Fin n)).powersetCard k
  let d := k.choose 2 * (n - 2).choose (k - 2)
  let p : ℝ := (2 : ℝ) / (2 : ℝ) ^ (k.choose 2)
  let x : ℝ := (1 : ℝ) / ((d : ℝ) + 1)
  have hx0 : 0 ≤ x := by positivity
  -- Cleanly split on `n < k` vs `k ≤ n` first!
  by_cases hnk : n < k
  · -- Empty graph on `Fin n` has no `K_k` and its complement has no `K_k` since `n < k`!
    apply lt_R2_of_witness (by omega) (by omega) (⊥ : SimpleGraph (Fin n))
    · intro s hs
      have hcard := hs.card_eq
      have hle : s.card ≤ n := by
        calc s.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ s
          _ = n := by simp
      omega
    · intro s hs
      have hcard := hs.card_eq
      have hle : s.card ≤ n := by
        calc s.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ s
          _ = n := by simp
      omega
  · push Not at hnk
    have hd_pos : 0 < d := by
      have h1 : 0 < k.choose 2 := Nat.choose_pos (by omega)
      have h2 : 0 < (n - 2).choose (k - 2) := Nat.choose_pos (by omega)
      exact Nat.mul_pos h1 h2
    have hx1' : x < 1 := by
      have hdposR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
      rw [div_lt_one (by linarith)]
      linarith
    have hdep : ∀ S ∈ ι, DependsOn (edgesOf S) (monoEvent S) := by
      intro S _ c1 c2 hc
      simp only [monoEvent, mem_filter, mem_univ, true_and]
      refine or_congr ?_ ?_ <;>
        exact forall₂_congr (fun e he => by rw [hc e he])
    have hp_bound : ∀ S ∈ ι, ((monoEvent S).card : ℝ) ≤ p * (Fintype.card (edgesFin n → Bool) : ℝ) := by
      intro S hS
      have hScard : S.card = k := (Finset.mem_powersetCard.mp hS).2
      have hEq := card_monoEvent_le S (by omega)
      rw [hScard] at hEq
      have hEqR : ((monoEvent S).card : ℝ) * (2 : ℝ) ^ (k.choose 2) =
          2 * (Fintype.card (edgesFin n → Bool) : ℝ) := by exact_mod_cast hEq
      have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (k.choose 2) := by positivity
      have : ((monoEvent S).card : ℝ) = p * (Fintype.card (edgesFin n → Bool) : ℝ) := by
        dsimp [p]
        field_simp [ne_of_gt hpowpos]
        linarith
      exact le_of_eq this
    have hd_bound : ∀ S ∈ ι,
        (ι.filter (fun T => T ≠ S ∧ ¬Disjoint (edgesOf S) (edgesOf T))).card ≤ d := by
      intro S hS
      exact clique_dep_deg_le (by omega) S (Finset.mem_powersetCard.mp hS).2
    have hlll : p ≤ x * (1 - x) ^ d := by
      have h1 := one_div_exp_le_one_sub_inv_pow d
      have hexp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (k.choose 2) := by positivity
      have hd1pos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
      have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; rfl
      have h' : p ≤ ((Real.exp 1) * ((d : ℝ) + 1))⁻¹ := by
        dsimp [p]
        rw [div_le_iff₀ hpowpos, inv_mul_eq_div, le_div_iff₀ (mul_pos hexp hd1pos)]
        rw [hcast] at h
        linarith
      calc p ≤ ((Real.exp 1) * ((d : ℝ) + 1))⁻¹ := h'
        _ = (1 / ((d : ℝ) + 1)) * (Real.exp 1)⁻¹ := by rw [mul_inv, mul_comm, one_div]
        _ ≤ x * (1 - x) ^ d := by
            exact mul_le_mul_of_nonneg_left h1 hx0
    obtain ⟨c, hc⟩ := symmetric_lll_bool ι edgesOf monoEvent hdep p x d hx0 hx1' hp_bound hd_bound hlll
    obtain ⟨hGk, hGkc⟩ := graphOfColor_cliqueFree_of_not_mono c hc
    exact lt_R2_of_witness (by omega) (by omega) (graphOfColor c) hGk hGkc

/-! #### Asymptotic Spencer (1975) Lower Bound & Exact Shearer / Symmetric LLL Barrier -/

/-- Elementary Stirling lower bound: `(m / e)^m ≤ m!` for all `m : ℕ`. -/
private lemma pow_div_exp_le_factorial (m : ℕ) :
    ((m : ℝ) / Real.exp 1) ^ m ≤ (m.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
    -- From the Taylor series of `exp m`: `m^m / m! ≤ exp m`!
    have hterm : (m : ℝ) ^ m / (m.factorial : ℝ) ≤ Real.exp (m : ℝ) :=
      Real.pow_div_factorial_le_exp (m : ℝ) (le_of_lt hm_pos) m
    have hfact_pos : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
    have hexp_eq : Real.exp (m : ℝ) = (Real.exp 1) ^ m := by
      rw [← Real.exp_nat_mul, mul_one]
    rw [hexp_eq, div_le_iff₀ hfact_pos] at hterm
    rw [div_pow, div_le_iff₀ (by positivity)]
    linarith

/-- Elementary Stirling upper bound: `m! ≤ e * m * (m / e)^m` for all `m ≥ 1`. -/
private lemma factorial_le_exp_mul_pow_div_exp (m : ℕ) (hm : 1 ≤ m) :
    (m.factorial : ℝ) ≤ Real.exp 1 * (m : ℝ) * ((m : ℝ) / Real.exp 1) ^ m := by
  induction m, hm using Nat.le_induction with
  | base =>
    simp [Nat.factorial]
  | succ k hk ih =>
    -- Need `(k + 1)! ≤ e * (k + 1) * ((k + 1) / e)^(k + 1)`.
    -- By IH, `(k + 1)! = (k + 1) * k! ≤ (k + 1) * e * k * (k / e)^k`.
    -- Enough to show `k * (k / e)^k ≤ ((k + 1) / e)^(k + 1)`, i.e., `e * k / (k + 1) ≤ (1 + 1 / k)^k`?
    -- Wait: `(1 + 1/k)^k < e`! So `e * k / (k + 1)` vs `(1 + 1/k)^k`:
    -- At k = 1: `e * 1 / 2 = 1.359 < 2 = (1 + 1)^1`!
    -- For general k ≥ 1: `e ≤ (1 + 1/k)^{k+1}`! YES!! Because `log(1 + 1/k) ≥ 1 / (k + 1)`!
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have hlog : (1 : ℝ) / ((k : ℝ) + 1) ≤ Real.log (1 + (1 : ℝ) / (k : ℝ)) := by
      -- `1 - 1 / x ≤ log x` at `x = 1 + 1 / k` gives `1 / (k + 1) ≤ log(1 + 1/k)`!
      have hxpos : (0 : ℝ) < 1 + (1 : ℝ) / (k : ℝ) := by positivity
      have h1 := Real.one_sub_inv_le_log_of_pos hxpos
      have hsimp : 1 - (1 + (1 : ℝ) / (k : ℝ))⁻¹ = (1 : ℝ) / ((k : ℝ) + 1) := by
        field_simp; ring
      rwa [hsimp] at h1
    have hexp_le : Real.exp 1 ≤ (1 + (1 : ℝ) / (k : ℝ)) ^ (k + 1) := by
      have hmul : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * Real.log (1 + (1 : ℝ) / (k : ℝ)) := by
        push_cast
        have h1 : ((k : ℝ) + 1) * ((1 : ℝ) / ((k : ℝ) + 1)) = 1 := by field_simp
        nlinarith
      calc Real.exp 1 ≤ Real.exp (((k + 1 : ℕ) : ℝ) * Real.log (1 + (1 : ℝ) / (k : ℝ))) :=
            Real.exp_le_exp.mpr hmul
        _ = (1 + (1 : ℝ) / (k : ℝ)) ^ (k + 1) := by
            rw [mul_comm, ← Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 1 + 1 / (k : ℝ)),
              Real.rpow_natCast]
    have hkey : (k : ℝ) * ((k : ℝ) / Real.exp 1) ^ k ≤
        (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) := by
      have hexp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      have hrewrite : (1 + (1 : ℝ) / (k : ℝ)) ^ (k + 1) =
          (((k + 1 : ℕ) : ℝ)) ^ (k + 1) / ((k : ℝ) ^ (k + 1)) := by
        rw [← div_pow]
        congr 1
        push_cast
        field_simp
      rw [hrewrite, le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ (k + 1))] at hexp_le
      rw [div_pow, div_pow, le_div_iff₀ (by positivity : (0 : ℝ) < (Real.exp 1) ^ (k + 1))]
      have hEq1 : (k : ℝ) * ((k : ℝ) ^ k / (Real.exp 1) ^ k) * (Real.exp 1) ^ (k + 1) =
          Real.exp 1 * (k : ℝ) ^ (k + 1) := by
        rw [pow_succ (Real.exp 1) k, pow_succ (k : ℝ) k]
        field_simp [ne_of_gt hexp_pos]
      linarith
    calc ((k + 1).factorial : ℝ)
        = ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by rw [Nat.factorial_succ]; push_cast; ring
      _ ≤ ((k + 1 : ℕ) : ℝ) * (Real.exp 1 * (k : ℝ) * ((k : ℝ) / Real.exp 1) ^ k) := by
          exact mul_le_mul_of_nonneg_left ih (by positivity)
      _ = Real.exp 1 * ((k + 1 : ℕ) : ℝ) * ((k : ℝ) * ((k : ℝ) / Real.exp 1) ^ k) := by ring
      _ ≤ Real.exp 1 * ((k + 1 : ℕ) : ℝ) * ((((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1)) := by
          exact mul_le_mul_of_nonneg_left hkey (by positivity)

/-- Key algebraic miracle of diagonal Ramsey LLL:
`2 * (k.choose 2 - 1) = (k - 2) * (k + 1)` for all `k ≥ 2`. -/
private lemma choose_two_sub_one_eq {k : ℕ} (hk : 2 ≤ k) :
    2 * (k.choose 2 - 1) = (k - 2) * (k + 1) := by
  have h1 : 2 * k.choose 2 = k * (k - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd
  have hpos : 1 ≤ k.choose 2 := Nat.choose_pos hk
  zify [hk, hpos, show 1 ≤ k by omega] at h1 ⊢
  nlinarith

/-- **Spencer (1975) Asymptotic Diagonal Ramsey Lower Bound** (pure Mathlib signature):
for every `ε > 0`, eventually `(√2 / e - ε) * k * 2^{k/2} ≤ R(k)`. -/
theorem ppl027_spencer_1975_asymptotic (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k ≥ K,
      (Real.sqrt 2 / Real.exp 1 - ε) * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) ≤
        ((sInf {m : ℕ | ∀ G : SimpleGraph (Fin m), ¬(G.CliqueFree k ∧ Gᶜ.CliqueFree k)} : ℕ) : ℝ) := by
  -- Use `c = √2 / e - ε`. If `c ≤ 0`, trivial; otherwise `0 < c < √2 / e`.
  by_cases hc : Real.sqrt 2 / Real.exp 1 - ε ≤ 0
  · refine ⟨1, fun k _ => ?_⟩
    have h1 : (Real.sqrt 2 / Real.exp 1 - ε) * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) ≤ 0 := by
      have : 0 ≤ (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) := by positivity
      nlinarith
    exact le_trans h1 (Nat.cast_nonneg _)
  · push Not at hc
    set c : ℝ := Real.sqrt 2 / Real.exp 1 - ε
    set θ : ℝ := c / (Real.sqrt 2 / Real.exp 1)
    have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hexp1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hθ_pos : 0 < θ := by positivity
    have hθ_lt : θ < 1 := by
      dsimp [θ, c]
      rw [div_lt_one (by positivity)]
      linarith
    set θ1 : ℝ := (θ + 1) / 2
    have hθ1_pos : 0 < θ1 := by dsimp [θ1]; linarith
    have hθ1_lt : θ1 < 1 := by dsimp [θ1]; linarith
    have htend1 : Tendsto (fun k : ℕ => Real.exp 1 * ((k : ℝ) ^ 2 + 1) * θ1 ^ (k - 2))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun k : ℕ => (k : ℝ) ^ 2 * θ1 ^ k) atTop (nhds 0) :=
        tendsto_pow_const_mul_const_pow_of_lt_one 2 hθ1_pos.le hθ1_lt
      have h2 : Tendsto (fun k : ℕ => θ1 ^ k) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hθ1_pos.le hθ1_lt
      have h3 : Tendsto (fun k : ℕ => (Real.exp 1 / θ1 ^ 2) * ((k : ℝ) ^ 2 * θ1 ^ k + θ1 ^ k))
          atTop (nhds ((Real.exp 1 / θ1 ^ 2) * (0 + 0))) :=
        (h1.add h2).const_mul _
      simp only [add_zero, mul_zero] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with k hk
      have hpow : θ1 ^ (k - 2) = θ1 ^ k / θ1 ^ 2 := by
        rw [eq_div_iff (pow_ne_zero 2 (ne_of_gt hθ1_pos)), ← pow_add, Nat.sub_add_cancel hk]
      rw [hpow]; ring
    have hev1 := (tendsto_order.mp htend1).2 1 (by norm_num)
    rw [Filter.eventually_atTop] at hev1
    rcases hev1 with ⟨K1, hK1⟩
    have hratio_gt : 1 < θ1 / θ := by rw [one_lt_div hθ_pos]; dsimp [θ1]; linarith
    obtain ⟨K2, hK2⟩ := exists_nat_gt (2 / (θ1 / θ - 1) + 2)
    refine ⟨max 4 (max K1 K2), fun k hk => ?_⟩
    have hk4 : 4 ≤ k := le_trans (le_max_left _ _) hk
    have hkK1 : K1 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
    have hkK2 : K2 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
    set n : ℕ := Nat.floor (c * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2))
    have hn_le : (n : ℝ) ≤ c * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) := Nat.floor_le (by positivity)
    have hlt_succ : c * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) < (n + 1 : ℝ) := Nat.lt_floor_add_one _
    -- Prove `n < R2 k k` via `ppl027_spencer_1975_lll_finite`!
    have hkm2_pos : (0 : ℝ) < ((k - 2 : ℕ) : ℝ) := by
      have : 0 < k - 2 := by omega
      exact_mod_cast this
    have hk_ratio : (k : ℝ) / ((k - 2 : ℕ) : ℝ) ≤ θ1 / θ := by
      have hsub : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ k)]; simp
      rw [hsub, div_le_iff₀ (by linarith)]
      have hK2' : 2 / (θ1 / θ - 1) + 2 < (k : ℝ) := lt_of_lt_of_le hK2 (by exact_mod_cast hkK2)
      have hK2'' : 2 / (θ1 / θ - 1) < (k : ℝ) - 2 := by linarith
      have h2 : 2 < ((k : ℝ) - 2) * (θ1 / θ - 1) := by
        rw [div_lt_iff₀ (by linarith)] at hK2''
        linarith
      linarith
    have hbase_le : (n : ℝ) / (((k - 2 : ℕ) : ℝ) / Real.exp 1) ≤
        θ1 * Real.sqrt 2 * (2 : ℝ) ^ ((k : ℝ) / 2) := by
      have hc_eq : c * Real.exp 1 = θ * Real.sqrt 2 := by
        dsimp [θ]
        field_simp [ne_of_gt hsqrt2, ne_of_gt hexp1]
      calc (n : ℝ) / (((k - 2 : ℕ) : ℝ) / Real.exp 1)
          ≤ (c * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)) / (((k - 2 : ℕ) : ℝ) / Real.exp 1) := by
            gcongr
        _ = (c * Real.exp 1) * ((k : ℝ) / ((k - 2 : ℕ) : ℝ)) * (2 : ℝ) ^ ((k : ℝ) / 2) := by
            field_simp [ne_of_gt hkm2_pos, ne_of_gt hexp1]
        _ = (θ * Real.sqrt 2) * ((k : ℝ) / ((k - 2 : ℕ) : ℝ)) * (2 : ℝ) ^ ((k : ℝ) / 2) := by
            rw [hc_eq]
        _ ≤ (θ * Real.sqrt 2) * (θ1 / θ) * (2 : ℝ) ^ ((k : ℝ) / 2) := by
            gcongr
        _ = θ1 * Real.sqrt 2 * (2 : ℝ) ^ ((k : ℝ) / 2) := by
            field_simp [ne_of_gt hθ_pos]
    have hchoose_bound : (((n - 2).choose (k - 2) : ℕ) : ℝ) ≤
        θ1 ^ (k - 2) * (2 : ℝ) ^ (k.choose 2 - 1) := by
      have hdesc : ((n - 2).choose (k - 2) : ℝ) * ((k - 2).factorial : ℝ) ≤ (n : ℝ) ^ (k - 2) := by
        have hnat : (n - 2).choose (k - 2) * (k - 2).factorial ≤ n ^ (k - 2) := by
          rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
          exact le_trans (Nat.descFactorial_le_pow (n - 2) (k - 2))
            (Nat.pow_le_pow_left (Nat.sub_le n 2) _)
        exact_mod_cast hnat
      have hstirl := pow_div_exp_le_factorial (k - 2)
      have hdiv_pos : (0 : ℝ) < (((k - 2 : ℕ) : ℝ) / Real.exp 1) ^ (k - 2) := by positivity
      have hfact_pos : (0 : ℝ) < ((k - 2).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
      have hpow_miracle : (Real.sqrt 2 * (2 : ℝ) ^ ((k : ℝ) / 2)) ^ (k - 2) =
          (2 : ℝ) ^ (k.choose 2 - 1) := by
        have hsqrt_eq : Real.sqrt 2 = (2 : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [Real.sqrt_eq_rpow]
        rw [hsqrt_eq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_natCast _ (k - 2), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.rpow_natCast (2 : ℝ) (k.choose 2 - 1)]
        congr 1
        have hmir := choose_two_sub_one_eq (by omega : 2 ≤ k)
        have hmirR : (2 : ℝ) * ((k.choose 2 - 1 : ℕ) : ℝ) =
            ((k - 2 : ℕ) : ℝ) * ((k : ℝ) + 1) := by exact_mod_cast hmir
        linarith
      calc (((n - 2).choose (k - 2) : ℕ) : ℝ)
          ≤ (n : ℝ) ^ (k - 2) / ((k - 2).factorial : ℝ) := by
            rwa [le_div_iff₀ hfact_pos]
        _ ≤ (n : ℝ) ^ (k - 2) / (((k - 2 : ℕ) : ℝ) / Real.exp 1) ^ (k - 2) := by
            exact div_le_div_of_nonneg_left (by positivity) hdiv_pos hstirl
        _ = ((n : ℝ) / (((k - 2 : ℕ) : ℝ) / Real.exp 1)) ^ (k - 2) := by rw [← div_pow]
        _ ≤ (θ1 * Real.sqrt 2 * (2 : ℝ) ^ ((k : ℝ) / 2)) ^ (k - 2) := by
            exact pow_le_pow_left₀ (by positivity) hbase_le (k - 2)
        _ = θ1 ^ (k - 2) * (Real.sqrt 2 * (2 : ℝ) ^ ((k : ℝ) / 2)) ^ (k - 2) := by
            rw [mul_assoc, mul_pow]
        _ = θ1 ^ (k - 2) * (2 : ℝ) ^ (k.choose 2 - 1) := by rw [hpow_miracle]
    have hspencer_cond :
        Real.exp 1 * 2 * ((k.choose 2 * (n - 2).choose (k - 2) + 1 : ℕ) : ℝ) ≤
          (2 : ℝ) ^ (k.choose 2) := by
      have hkch_le : (k.choose 2 : ℝ) ≤ (k : ℝ) ^ 2 := by
        have : k.choose 2 ≤ k * k := by
          rw [Nat.choose_two_right]
          exact le_trans (Nat.div_le_self _ 2) (Nat.mul_le_mul_left k (Nat.sub_le k 1))
        have : (k.choose 2 : ℝ) ≤ (k * k : ℝ) := by exact_mod_cast this
        linarith [sq (k : ℝ)]
      have hpow_split : (2 : ℝ) ^ (k.choose 2) = 2 * (2 : ℝ) ^ (k.choose 2 - 1) := by
        have hpos1 : 1 ≤ k.choose 2 := Nat.choose_pos (by omega)
        conv_lhs => rw [← Nat.sub_add_cancel hpos1, pow_succ, mul_comm]
      have h1_le : (1 : ℝ) ≤ θ1 ^ (k - 2) * (2 : ℝ) ^ (k.choose 2 - 1) ∨
          (n - 2).choose (k - 2) = 0 := by
        by_cases hz : (n - 2).choose (k - 2) = 0
        · exact Or.inr hz
        · left
          have hge1 : (1 : ℝ) ≤ (((n - 2).choose (k - 2) : ℕ) : ℝ) := by
            exact_mod_cast Nat.pos_of_ne_zero hz
          exact le_trans hge1 hchoose_bound
      rcases h1_le with hge1 | hz
      · have hK1' := hK1 k hkK1
        calc Real.exp 1 * 2 * ((k.choose 2 * (n - 2).choose (k - 2) + 1 : ℕ) : ℝ)
            = 2 * (Real.exp 1 * ((k.choose 2 : ℝ) * (((n - 2).choose (k - 2) : ℕ) : ℝ) + 1)) := by
              push_cast; ring
          _ ≤ 2 * (Real.exp 1 * ((k : ℝ) ^ 2 * (θ1 ^ (k - 2) * (2 : ℝ) ^ (k.choose 2 - 1)) +
                θ1 ^ (k - 2) * (2 : ℝ) ^ (k.choose 2 - 1))) := by
              gcongr
          _ = (Real.exp 1 * ((k : ℝ) ^ 2 + 1) * θ1 ^ (k - 2)) * (2 * (2 : ℝ) ^ (k.choose 2 - 1)) := by
              ring
          _ ≤ 1 * (2 * (2 : ℝ) ^ (k.choose 2 - 1)) := by
              exact mul_le_mul_of_nonneg_right (le_of_lt hK1') (by positivity)
          _ = (2 : ℝ) ^ (k.choose 2) := by rw [one_mul, hpow_split]
      · rw [hz, mul_zero, zero_add]
        push_cast
        have hexp_le4 : Real.exp 1 ≤ 4 := by
          have hhalf : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
            linarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
          rw [Real.exp_neg] at hhalf
          have hpos : (0 : ℝ) < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
          have h2 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
            rw [le_inv_comm₀ (by norm_num) hpos] at hhalf
            linarith
          have hsq : Real.exp 1 = (Real.exp (1 / 2 : ℝ)) ^ 2 := by
            rw [sq, ← Real.exp_add]; norm_num
          rw [hsq]; nlinarith
        have hpow6 : (2 : ℝ) ^ 6 ≤ (2 : ℝ) ^ (k.choose 2) := by
          have : 6 ≤ k.choose 2 := Nat.choose_le_choose 2 hk4
          exact pow_le_pow_right₀ (by norm_num) this
        linarith [show (2 : ℝ) ^ 6 = 64 by norm_num]
    have hlt_R : n < R2 k k := ppl027_spencer_1975_lll_finite k n (by omega) hspencer_cond
    have hle_R : (n + 1 : ℝ) ≤ (R2 k k : ℝ) := by exact_mod_cast (hlt_R : n + 1 ≤ R2 k k)
    exact le_of_lt (lt_of_lt_of_le hlt_succ hle_R)

/-- **Exact Shearer / Symmetric LLL `√2 / e` Barrier for PPL 027 (Erdős #1029)** (pure Mathlib):
In the clique dependency graph of `K_n`, the `k`-cliques sharing edge `{0, 1}` form a clique of size
`M = (n - 2).choose (k - 2)`, so EVEN Shearer's optimal LLL necessary condition `M * p < 1`
(which is strictly weaker than Symmetric LLL `e * p * (d + 1) ≤ 1`, Asymmetric LLL, and
Cluster-Expansion LLL) forces `limsup_{k → ∞} n(k) / (k · 2^{k/2}) ≤ √2 / e`! -/
theorem ppl027_shearer_and_symmetric_lll_barrier (n : ℕ → ℕ)
    (hShearer : ∀ᶠ k in Filter.atTop,
      (((n k - 2).choose (k - 2) : ℕ) : ℝ) * (2 : ℝ) < (2 : ℝ) ^ (k.choose 2)) :
    Filter.limsup (fun k : ℕ => (n k : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2))) Filter.atTop ≤
      Real.sqrt 2 / Real.exp 1 := by
  -- First prove an explicit upper bound on `n k / (k * 2^{k/2})` for all sufficiently large `k`!
  have hpointwise : ∀ᶠ k in Filter.atTop,
      (n k : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)) ≤
        (k : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)) +
          (Real.sqrt 2 / Real.exp 1) *
            ((Real.exp 1 * ((k - 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / ((k - 2 : ℕ) : ℝ))) := by
    filter_upwards [hShearer, eventually_ge_atTop 4] with k hSh hk4
    by_cases hnk : n k ≤ k
    · have h1 : (n k : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnk
      have h2 : (n k : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)) ≤
          (k : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)) := by gcongr
      have h3 : 0 ≤ (Real.sqrt 2 / Real.exp 1) *
          ((Real.exp 1 * ((k - 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / ((k - 2 : ℕ) : ℝ))) := by positivity
      linarith
    · push Not at hnk
      -- Lower bound `(n k - 2).choose (k - 2) ≥ (n k - k)^(k - 2) / (k - 2)!`.
      have hdesc : ((n k - k : ℕ) : ℝ) ^ (k - 2) ≤
          (((n k - 2).choose (k - 2) : ℕ) : ℝ) * ((k - 2).factorial : ℝ) := by
        have hnat : (n k - k) ^ (k - 2) ≤ (n k - 2).choose (k - 2) * (k - 2).factorial := by
          rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
          -- Each of the `k - 2` factors `(n k - 2 - i)` for `i < k - 2` is `≥ n k - k`!
          have hgen : ∀ a m : ℕ, m ≤ a → (a - m) ^ m ≤ a.descFactorial m := by
            intro a m
            induction m with
            | zero => intro _; simp
            | succ r ihr =>
              intro hr
              rw [Nat.descFactorial_succ, pow_succ']
              have h1 : (a - (r + 1)) ^ r ≤ (a - r) ^ r :=
                Nat.pow_le_pow_left (by omega) r
              have h2 : a - (r + 1) ≤ a - r := by omega
              exact Nat.mul_le_mul h2 (le_trans h1 (ihr (by omega)))
          have hEqSub : (n k - 2) - (k - 2) = n k - k := by omega
          have := hgen (n k - 2) (k - 2) (by omega)
          rwa [hEqSub] at this
        exact_mod_cast hnat
      have hstirl := factorial_le_exp_mul_pow_div_exp (k - 2) (by omega)
      have hpow_split : (2 : ℝ) ^ (k.choose 2) = 2 * (2 : ℝ) ^ (k.choose 2 - 1) := by
        have hpos1 : 1 ≤ k.choose 2 := Nat.choose_pos (by omega)
        conv_lhs => rw [← Nat.sub_add_cancel hpos1, pow_succ, mul_comm]
      have hSh' : (((n k - 2).choose (k - 2) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k.choose 2 - 1) := by
        rw [hpow_split] at hSh; linarith
      have hpow_miracle : (2 : ℝ) ^ (k.choose 2 - 1) =
          (Real.sqrt 2 * (2 : ℝ) ^ ((k : ℝ) / 2)) ^ (k - 2) := by
        have hsqrt_eq : Real.sqrt 2 = (2 : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow 2
        rw [hsqrt_eq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_natCast _ (k - 2), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.rpow_natCast (2 : ℝ) (k.choose 2 - 1)]
        congr 1
        have hmir := choose_two_sub_one_eq (by omega : 2 ≤ k)
        have hmirR : (2 : ℝ) * ((k.choose 2 - 1 : ℕ) : ℝ) =
            ((k - 2 : ℕ) : ℝ) * ((k : ℝ) + 1) := by exact_mod_cast hmir
        linarith
      have hpow_le : ((n k - k : ℕ) : ℝ) ^ (k - 2) ≤
          (Real.exp 1 * ((k - 2 : ℕ) : ℝ)) *
            ((((k - 2 : ℕ) : ℝ) / Real.exp 1) * (Real.sqrt 2 * (2 : ℝ) ^ ((k : ℝ) / 2))) ^ (k - 2) := by
        calc ((n k - k : ℕ) : ℝ) ^ (k - 2)
            ≤ (((n k - 2).choose (k - 2) : ℕ) : ℝ) * ((k - 2).factorial : ℝ) := hdesc
          _ ≤ (2 : ℝ) ^ (k.choose 2 - 1) *
                (Real.exp 1 * ((k - 2 : ℕ) : ℝ) * (((k - 2 : ℕ) : ℝ) / Real.exp 1) ^ (k - 2)) := by
              exact mul_le_mul hSh' hstirl (by positivity) (by positivity)
          _ = (Real.exp 1 * ((k - 2 : ℕ) : ℝ)) *
                ((((k - 2 : ℕ) : ℝ) / Real.exp 1) ^ (k - 2) *
                  (Real.sqrt 2 * (2 : ℝ) ^ ((k : ℝ) / 2)) ^ (k - 2)) := by
              rw [hpow_miracle]; ring
          _ = (Real.exp 1 * ((k - 2 : ℕ) : ℝ)) *
                ((((k - 2 : ℕ) : ℝ) / Real.exp 1) * (Real.sqrt 2 * (2 : ℝ) ^ ((k : ℝ) / 2))) ^ (k - 2) := by
              rw [← mul_pow]
      -- Take `(k - 2)`-th root via `Real.rpow_le_rpow`!
      have hkm2_pos : (0 : ℝ) < ((k - 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hroot : ((n k - k : ℕ) : ℝ) ≤
          ((Real.exp 1 * ((k - 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / ((k - 2 : ℕ) : ℝ))) *
            ((((k - 2 : ℕ) : ℝ) / Real.exp 1) * (Real.sqrt 2 * (2 : ℝ) ^ ((k : ℝ) / 2))) := by
        have hrpow := Real.rpow_le_rpow (by positivity) hpow_le
          (by positivity : (0 : ℝ) ≤ (1 : ℝ) / ((k - 2 : ℕ) : ℝ))
        have hLHS : (((n k - k : ℕ) : ℝ) ^ (k - 2)) ^ ((1 : ℝ) / ((k - 2 : ℕ) : ℝ)) =
            ((n k - k : ℕ) : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          have : ((k - 2 : ℕ) : ℝ) * ((1 : ℝ) / ((k - 2 : ℕ) : ℝ)) = 1 := by
            field_simp [ne_of_gt hkm2_pos]
          rw [this, Real.rpow_one]
        have hRHS :
            ((Real.exp 1 * ((k - 2 : ℕ) : ℝ)) *
              ((((k - 2 : ℕ) : ℝ) / Real.exp 1) *
                (Real.sqrt 2 * (2 : ℝ) ^ ((k : ℝ) / 2))) ^ (k - 2)) ^ ((1 : ℝ) / ((k - 2 : ℕ) : ℝ)) =
            ((Real.exp 1 * ((k - 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / ((k - 2 : ℕ) : ℝ))) *
              ((((k - 2 : ℕ) : ℝ) / Real.exp 1) * (Real.sqrt 2 * (2 : ℝ) ^ ((k : ℝ) / 2))) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          have : ((k - 2 : ℕ) : ℝ) * ((1 : ℝ) / ((k - 2 : ℕ) : ℝ)) = 1 := by
            field_simp [ne_of_gt hkm2_pos]
          rw [this, Real.rpow_one]
        rwa [hLHS, hRHS] at hrpow
      have hnk_split : (n k : ℝ) = (k : ℝ) + ((n k - k : ℕ) : ℝ) := by
        have : n k = k + (n k - k) := by omega
        exact_mod_cast this
      have hkm2_le_k : ((k - 2 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 2
      have hdenom_pos : (0 : ℝ) < (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) := by positivity
      rw [hnk_split, add_div]
      gcongr
      calc ((n k - k : ℕ) : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2))
          ≤ (((Real.exp 1 * ((k - 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / ((k - 2 : ℕ) : ℝ))) *
              ((((k - 2 : ℕ) : ℝ) / Real.exp 1) * (Real.sqrt 2 * (2 : ℝ) ^ ((k : ℝ) / 2)))) /
              ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)) := by gcongr
        _ ≤ (((Real.exp 1 * ((k - 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / ((k - 2 : ℕ) : ℝ))) *
              (((k : ℝ) / Real.exp 1) * (Real.sqrt 2 * (2 : ℝ) ^ ((k : ℝ) / 2)))) /
              ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)) := by gcongr
        _ = (Real.sqrt 2 / Real.exp 1) *
              ((Real.exp 1 * ((k - 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / ((k - 2 : ℕ) : ℝ))) := by
            have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
            have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((k : ℝ) / 2) := by positivity
            field_simp [ne_of_gt hkpos, ne_of_gt h2pos]
  -- Now the RHS tends to `0 + (√2 / e) * 1 = √2 / e` as `k → ∞`!
  have hRHS_tend : Tendsto (fun k : ℕ =>
      (k : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)) +
        (Real.sqrt 2 / Real.exp 1) *
          ((Real.exp 1 * ((k - 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / ((k - 2 : ℕ) : ℝ))))
      atTop (nhds (Real.sqrt 2 / Real.exp 1)) := by
    have ht1 : Tendsto (fun k : ℕ => (k : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)))
        atTop (nhds 0) := by
      have h0 : Tendsto (fun k : ℕ => ((Real.sqrt 2)⁻¹) ^ k) atTop (nhds 0) := by
        refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
        rw [inv_lt_one_iff₀]
        right
        have : (1 : ℝ) < Real.sqrt 2 := by
          rw [Real.lt_sqrt (by norm_num)]; norm_num
        exact this
      refine h0.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hkpos : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h2eq : ((Real.sqrt 2)⁻¹) ^ k = ((2 : ℝ) ^ ((k : ℝ) / 2))⁻¹ := by
        rw [inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 2; ring
      rw [h2eq]
      field_simp [hkpos]
    have ht2 : Tendsto (fun k : ℕ =>
        (Real.exp 1 * ((k - 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / ((k - 2 : ℕ) : ℝ))) atTop (nhds 1) := by
      have hlog_tend : Tendsto (fun m : ℕ => Real.log (Real.exp 1 * (m : ℝ)) / (m : ℝ))
          atTop (nhds 0) := by
        have h1 : Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ)) atTop (nhds 0) :=
          tendsto_one_div_atTop_nhds_zero_nat
        have h2 : Tendsto (fun m : ℕ => Real.log (m : ℝ) / (m : ℝ)) atTop (nhds 0) := by
          have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
          simp only [pow_one, one_mul, add_zero] at this
          exact this.comp tendsto_natCast_atTop_atTop
        have h12 : Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ) + Real.log (m : ℝ) / (m : ℝ))
            atTop (nhds (0 + 0)) := h1.add h2
        simp only [add_zero] at h12
        refine h12.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with m hm
        have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
        rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hmpos), Real.log_exp, add_div]
      have hexp_tend : Tendsto (fun m : ℕ => Real.exp (Real.log (Real.exp 1 * (m : ℝ)) / (m : ℝ)))
          atTop (nhds 1) := by
        have hcomp := (Real.continuous_exp.tendsto 0).comp hlog_tend
        simpa [Function.comp_def] using hcomp
      have hsub_tend : Tendsto (fun k : ℕ => k - 2) atTop atTop :=
        tendsto_atTop_atTop.mpr (fun b => ⟨b + 2, fun k hk => by omega⟩)
      refine (hexp_tend.comp hsub_tend).congr' ?_
      filter_upwards [eventually_ge_atTop 3] with k hk
      have hpos : (0 : ℝ) < Real.exp 1 * ((k - 2 : ℕ) : ℝ) := by
        have : 0 < k - 2 := by omega
        positivity
      simp only [Function.comp_apply]
      rw [Real.rpow_def_of_pos hpos, mul_one_div]
    have hcomb := ht1.add (ht2.const_mul (Real.sqrt 2 / Real.exp 1))
    simpa using hcomb
  -- Bound `limsup` by `√2 / e` via `Filter.limsup_le_limsup` + `hRHS_tend.limsup_eq`!
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun k : ℕ => (n k : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2))) :=
    Filter.isCoboundedUnder_le_of_eventually_le Filter.atTop
      (x := (0 : ℝ)) (by filter_upwards with k; positivity)
  have hbdd_rhs : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun k : ℕ => (k : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)) +
        (Real.sqrt 2 / Real.exp 1) *
          ((Real.exp 1 * ((k - 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / ((k - 2 : ℕ) : ℝ)))) :=
    hRHS_tend.isBoundedUnder_le
  calc Filter.limsup (fun k : ℕ => (n k : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2))) Filter.atTop
      ≤ Filter.limsup (fun k : ℕ => (k : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)) +
          (Real.sqrt 2 / Real.exp 1) *
            ((Real.exp 1 * ((k - 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / ((k - 2 : ℕ) : ℝ)))) Filter.atTop :=
        Filter.limsup_le_limsup hpointwise hcobdd hbdd_rhs
    _ = Real.sqrt 2 / Real.exp 1 := hRHS_tend.limsup_eq

/-! ### Section 4: GNNW (2024/2026) Section 2 — Short Inductive Off-Diagonal Exponential Bound -/

/-- Number of red (`G`) edges between `X` and `Y` (counted as ordered pairs `(u, v) ∈ X × Y`). -/
private noncomputable def eR {N : ℕ} (G : SimpleGraph (Fin N)) (X Y : Finset (Fin N)) : ℝ :=
  open Classical in
  ((X.sum (fun u => (Y.filter (fun v => G.Adj u v)).card) : ℕ) : ℝ)

/-- Edge density `e_R(X, Y) / (|X| |Y|)`, defined as `0` when `X` or `Y` is empty. -/
private noncomputable def dens {N : ℕ} (G : SimpleGraph (Fin N)) (X Y : Finset (Fin N)) : ℝ :=
  if X.card = 0 ∨ Y.card = 0 then 0 else eR G X Y / ((X.card : ℝ) * (Y.card : ℝ))

/-- Excess red edges over density `p`: `f_p(X, Y) = e_R(X, Y) - p |X| |Y|`. -/
private noncomputable def fp {N : ℕ} (G : SimpleGraph (Fin N)) (p : ℝ)
    (X Y : Finset (Fin N)) : ℝ :=
  eR G X Y - p * (X.card : ℝ) * (Y.card : ℝ)

/-- Candidate `(X, Y)` is `(k, l, t)`-good if `X ∪ Y` has a red `K_k`, or `X` has a blue `K_t`,
or `Y` has a blue `K_l`. -/
private def IsGood {N : ℕ} (G : SimpleGraph (Fin N)) (k l t : ℕ)
    (X Y : Finset (Fin N)) : Prop :=
  (∃ s ⊆ X ∪ Y, G.IsNClique k s) ∨ (∃ s ⊆ X, Gᶜ.IsNClique t s) ∨ (∃ s ⊆ Y, Gᶜ.IsNClique l s)

private lemma isGood_mono {N k l t : ℕ} {G : SimpleGraph (Fin N)}
    {X' X Y' Y : Finset (Fin N)} (hX : X' ⊆ X) (hY : Y' ⊆ Y)
    (h : IsGood G k l t X' Y') : IsGood G k l t X Y := by
  rcases h with ⟨s, hs, hcl⟩ | ⟨s, hs, hcl⟩ | ⟨s, hs, hcl⟩
  · exact Or.inl ⟨s, Finset.Subset.trans hs (Finset.union_subset_union hX hY), hcl⟩
  · exact Or.inr (Or.inl ⟨s, Finset.Subset.trans hs hX, hcl⟩)
  · exact Or.inr (Or.inr ⟨s, Finset.Subset.trans hs hY, hcl⟩)

private lemma isGood_of_k_one {N l t : ℕ} {G : SimpleGraph (Fin N)} {X Y : Finset (Fin N)}
    (hX : X.Nonempty) : IsGood G 1 l t X Y := by
  rcases hX with ⟨v, hv⟩
  left
  refine ⟨{v}, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact mem_union_left Y hv
  · refine ⟨?_, by simp⟩
    intro a ha b hb hab
    exact absurd ((Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm) hab

private lemma isGood_of_t_one {N k l : ℕ} {G : SimpleGraph (Fin N)} {X Y : Finset (Fin N)}
    (hX : X.Nonempty) : IsGood G k l 1 X Y := by
  rcases hX with ⟨v, hv⟩
  right; left
  refine ⟨{v}, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact hv
  · refine ⟨?_, by simp⟩
    intro a ha b hb hab
    exact absurd ((Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm) hab

private lemma eR_eq_sum_indicator {N : ℕ} (G : SimpleGraph (Fin N)) (X Y : Finset (Fin N)) :
    open Classical in
    eR G X Y = ∑ u ∈ X, ∑ v ∈ Y, if G.Adj u v then (1 : ℝ) else 0 := by
  classical
  unfold eR
  push_cast
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_boole]

private lemma eR_symm {N : ℕ} (G : SimpleGraph (Fin N)) (X Y : Finset (Fin N)) :
    eR G X Y = eR G Y X := by
  classical
  rw [eR_eq_sum_indicator, eR_eq_sum_indicator, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun u _ => ?_))
  by_cases h : G.Adj u v
  · simp [h, h.symm]
  · have h' : ¬G.Adj v u := fun hvu => h hvu.symm
    simp [h, h']

private lemma eR_nonneg {N : ℕ} (G : SimpleGraph (Fin N)) (X Y : Finset (Fin N)) :
    0 ≤ eR G X Y := by
  unfold eR; exact Nat.cast_nonneg _

private lemma eR_le_mul_card {N : ℕ} (G : SimpleGraph (Fin N)) (X Y : Finset (Fin N)) :
    eR G X Y ≤ (X.card : ℝ) * (Y.card : ℝ) := by
  classical
  have hnat : X.sum (fun u => (Y.filter (fun v => G.Adj u v)).card) ≤ X.card * Y.card := by
    calc X.sum (fun u => (Y.filter (fun v => G.Adj u v)).card)
        ≤ X.sum (fun _ => Y.card) :=
          Finset.sum_le_sum (fun u _ => Finset.card_filter_le Y _)
      _ = X.card * Y.card := by rw [Finset.sum_const, smul_eq_mul]
  unfold eR
  exact_mod_cast hnat

private lemma eR_union_left {N : ℕ} (G : SimpleGraph (Fin N))
    {X1 X2 Y : Finset (Fin N)} (hdisj : Disjoint X1 X2) :
    eR G (X1 ∪ X2) Y = eR G X1 Y + eR G X2 Y := by
  classical
  unfold eR
  rw [Finset.sum_union hdisj, Nat.cast_add]

private lemma fp_union_left {N : ℕ} (G : SimpleGraph (Fin N)) (p : ℝ)
    {X1 X2 Y : Finset (Fin N)} (hdisj : Disjoint X1 X2) :
    fp G p (X1 ∪ X2) Y = fp G p X1 Y + fp G p X2 Y := by
  unfold fp
  rw [eR_union_left G hdisj, Finset.card_union_of_disjoint hdisj, Nat.cast_add]
  ring

private lemma eR_singleton_left {N : ℕ} (G : SimpleGraph (Fin N)) (v : Fin N) (Y : Finset (Fin N)) :
    open Classical in
    eR G {v} Y = ((Y.filter (fun u => G.Adj v u)).card : ℝ) := by
  classical
  unfold eR
  simp

private lemma eR_eq_dens_mul {N : ℕ} (G : SimpleGraph (Fin N)) (X Y : Finset (Fin N)) :
    eR G X Y = dens G X Y * (X.card : ℝ) * (Y.card : ℝ) := by
  unfold dens
  by_cases h0 : X.card = 0 ∨ Y.card = 0
  · rw [if_pos h0]
    rcases h0 with hX | hY
    · have hXe : X = ∅ := Finset.card_eq_zero.mp hX
      subst hXe; unfold eR; simp
    · have hYe : Y = ∅ := Finset.card_eq_zero.mp hY
      subst hYe; unfold eR; simp
  · rw [if_neg h0]
    push Not at h0
    have hXp : (X.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0.1
    have hYp : (Y.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0.2
    field_simp [hXp, hYp]

private lemma dens_nonneg {N : ℕ} (G : SimpleGraph (Fin N)) (X Y : Finset (Fin N)) :
    0 ≤ dens G X Y := by
  unfold dens
  split_ifs
  · exact le_rfl
  · exact div_nonneg (eR_nonneg G X Y) (by positivity)

private lemma dens_le_one {N : ℕ} (G : SimpleGraph (Fin N)) (X Y : Finset (Fin N)) :
    dens G X Y ≤ 1 := by
  unfold dens
  split_ifs with h0
  · norm_num
  · push Not at h0
    have hpos : (0 : ℝ) < (X.card : ℝ) * (Y.card : ℝ) := by
      exact mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0.1))
        (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0.2))
    rw [div_le_one hpos]
    exact eR_le_mul_card G X Y

/-- **GNNW Observation 3:** For `0 < x < 1` and `k, l ≥ 1`, `R(k, l) ≤ x^{-(k-1)} (1 - x)^{-(l-1)}`. -/
private lemma gnnw_obs3 {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∀ s k l : ℕ, 1 ≤ k → 1 ≤ l → k + l = s →
      (R2 k l : ℝ) ≤ x⁻¹ ^ (k - 1) * (1 - x)⁻¹ ^ (l - 1) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro k l hk hl hsum
    have h1x : 0 < 1 - x := by linarith
    rcases Nat.eq_or_lt_of_le hk with rfl | hk2
    · rw [R2_one_left l hl]
      simp only [Nat.sub_self, pow_zero, one_mul, Nat.cast_one]
      have hge1 : 1 ≤ (1 - x)⁻¹ := one_le_inv₀ h1x |>.mpr (by linarith)
      exact one_le_pow₀ hge1
    rcases Nat.eq_or_lt_of_le hl with rfl | hl2
    · rw [R2_one_right k hk]
      simp only [Nat.sub_self, pow_zero, mul_one, Nat.cast_one]
      have hge1 : 1 ≤ x⁻¹ := one_le_inv₀ hx0 |>.mpr (by linarith)
      exact one_le_pow₀ hge1
    have h1 := ih (k - 1 + l) (by omega) (k - 1) l (by omega) hl rfl
    have h2 := ih (k + (l - 1)) (by omega) k (l - 1) hk (by omega) rfl
    have hstep : R2 k l ≤ R2 (k - 1) l + R2 k (l - 1) := by
      have := R2_step_le (k := k - 1) (l := l - 1) (by omega) (by omega)
      simpa [Nat.sub_add_cancel hk, Nat.sub_add_cancel hl] using this
    have hstepR : (R2 k l : ℝ) ≤ (R2 (k - 1) l : ℝ) + (R2 k (l - 1) : ℝ) := by
      exact_mod_cast hstep
    have hkm1 : k - 1 = (k - 2) + 1 := by omega
    have hlm1 : l - 1 = (l - 2) + 1 := by omega
    have hksub : k - 1 - 1 = k - 2 := by omega
    have hlsub : l - 1 - 1 = l - 2 := by omega
    calc (R2 k l : ℝ) ≤ (R2 (k - 1) l : ℝ) + (R2 k (l - 1) : ℝ) := hstepR
      _ ≤ x⁻¹ ^ (k - 1 - 1) * (1 - x)⁻¹ ^ (l - 1) +
            x⁻¹ ^ (k - 1) * (1 - x)⁻¹ ^ (l - 1 - 1) := add_le_add h1 h2
      _ = x⁻¹ ^ (k - 1) * (1 - x)⁻¹ ^ (l - 1) * (x + (1 - x)) := by
          rw [hksub, hlsub, hkm1, hlm1, pow_succ, pow_succ]
          field_simp [ne_of_gt hx0, ne_of_gt h1x]
      _ = x⁻¹ ^ (k - 1) * (1 - x)⁻¹ ^ (l - 1) := by ring

/-- **GNNW Lemma 2:** Exact excess variance identity
`∑_{v ∈ X} f_p(X, N_R(v) ∩ Y) - p |X| f_p(X, Y) = ∑_{y ∈ Y} (|N_R(y) ∩ X| - p |X|)^2 ≥ 0`. -/
private lemma gnnw_lemma2 {N : ℕ} (G : SimpleGraph (Fin N)) (p : ℝ) (X Y : Finset (Fin N)) :
    open Classical in
    p * (X.card : ℝ) * fp G p X Y ≤
      ∑ v ∈ X, fp G p X (Y.filter (fun y => G.Adj v y)) := by
  classical
  have hdiff :
      (∑ v ∈ X, fp G p X (Y.filter (fun y => G.Adj v y))) - p * (X.card : ℝ) * fp G p X Y =
        ∑ y ∈ Y, (((X.filter (fun v => G.Adj y v)).card : ℝ) - p * (X.card : ℝ)) ^ 2 := by
    have h1 : ∑ v ∈ X, eR G X (Y.filter (fun y => G.Adj v y)) =
        ∑ y ∈ Y, (((X.filter (fun v => G.Adj y v)).card : ℝ)) ^ 2 := by
      calc ∑ v ∈ X, eR G X (Y.filter (fun y => G.Adj v y))
          = ∑ v ∈ X, eR G (Y.filter (fun y => G.Adj v y)) X :=
            Finset.sum_congr rfl (fun v _ => eR_symm G _ _)
        _ = ∑ v ∈ X, ∑ y ∈ Y.filter (fun y => G.Adj v y),
              ((X.filter (fun u => G.Adj y u)).card : ℝ) := by
            refine Finset.sum_congr rfl (fun v _ => ?_)
            unfold eR; push_cast; rfl
        _ = ∑ v ∈ X, ∑ y ∈ Y,
              if G.Adj v y then ((X.filter (fun u => G.Adj y u)).card : ℝ) else 0 := by
            refine Finset.sum_congr rfl (fun v _ => by rw [Finset.sum_filter])
        _ = ∑ y ∈ Y, ∑ v ∈ X,
              if G.Adj v y then ((X.filter (fun u => G.Adj y u)).card : ℝ) else 0 :=
            Finset.sum_comm
        _ = ∑ y ∈ Y, (((X.filter (fun v => G.Adj y v)).card : ℝ)) ^ 2 := by
            refine Finset.sum_congr rfl (fun y _ => ?_)
            have hconv : (∑ v ∈ X, if G.Adj v y then ((X.filter (fun u => G.Adj y u)).card : ℝ) else 0) =
                ∑ v ∈ X.filter (fun v => G.Adj y v), ((X.filter (fun u => G.Adj y u)).card : ℝ) := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl (fun v _ => ?_)
              by_cases h : G.Adj v y
              · simp [h, h.symm]
              · have h' : ¬G.Adj y v := fun hy => h hy.symm
                simp [h, h']
            rw [hconv, Finset.sum_const, nsmul_eq_mul, sq]
    have h2 : ∑ v ∈ X, ((Y.filter (fun y => G.Adj v y)).card : ℝ) = eR G X Y := by
      unfold eR; push_cast; rfl
    have h3 : ∑ y ∈ Y, ((X.filter (fun v => G.Adj y v)).card : ℝ) = eR G X Y := by
      rw [eR_symm]; unfold eR; push_cast; rfl
    have hLHS : ∑ v ∈ X, fp G p X (Y.filter (fun y => G.Adj v y)) =
        (∑ y ∈ Y, (((X.filter (fun v => G.Adj y v)).card : ℝ)) ^ 2) -
          p * (X.card : ℝ) * eR G X Y := by
      unfold fp
      rw [Finset.sum_sub_distrib, h1, ← Finset.mul_sum, h2]
    have hRHS : ∑ y ∈ Y, (((X.filter (fun v => G.Adj y v)).card : ℝ) - p * (X.card : ℝ)) ^ 2 =
        (∑ y ∈ Y, (((X.filter (fun v => G.Adj y v)).card : ℝ)) ^ 2) -
          2 * p * (X.card : ℝ) * eR G X Y + p ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by
      have hexp : ∀ y ∈ Y,
          (((X.filter (fun v => G.Adj y v)).card : ℝ) - p * (X.card : ℝ)) ^ 2 =
            (((X.filter (fun v => G.Adj y v)).card : ℝ)) ^ 2 -
              2 * p * (X.card : ℝ) * ((X.filter (fun v => G.Adj y v)).card : ℝ) +
              p ^ 2 * (X.card : ℝ) ^ 2 := fun _ _ => by ring
      rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, h3, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hLHS, hRHS]
    unfold fp
    ring
  have hnn : 0 ≤ ∑ y ∈ Y, (((X.filter (fun v => G.Adj y v)).card : ℝ) - p * (X.card : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

/-- **GNNW Lemma 4:** Core inductive replacement of the book algorithm for off-diagonal bounds. -/
private lemma gnnw_lemma4 {N : ℕ} (G : SimpleGraph (Fin N)) {x p : ℝ}
    (hx0 : 0 < x) (hxp : x < p) (hp1 : p < 1) :
    ∀ s k l t : ℕ, 1 ≤ k → 1 ≤ l → 1 ≤ t → k + t = s →
      ∀ X Y : Finset (Fin N), Disjoint X Y →
        ((k + t : ℕ) : ℝ) * x⁻¹ ^ (k - 1) * (1 - x)⁻¹ ^ (l - 1) * (p - x)⁻¹ ^ (t - 1) ≤
          fp G p X Y →
        IsGood G k l t X Y := by
  classical
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro k l t hk hl ht hsum X Y hdisj hfp
    have hpx : 0 < p - x := by linarith
    have h1x : 0 < 1 - x := by linarith
    have hp0 : 0 < p := lt_trans hx0 hxp
    have hfp_pos : 0 < fp G p X Y := by
      have hrhs_pos : 0 < ((k + t : ℕ) : ℝ) * x⁻¹ ^ (k - 1) * (1 - x)⁻¹ ^ (l - 1) *
          (p - x)⁻¹ ^ (t - 1) := by positivity
      exact lt_of_lt_of_le hrhs_pos hfp
    have hXne : X.Nonempty := by
      by_contra hXe
      rw [Finset.not_nonempty_iff_eq_empty] at hXe
      subst hXe
      have : fp G p ∅ Y = 0 := by unfold fp eR; simp
      linarith
    rcases Nat.eq_or_lt_of_le hk with rfl | hk2
    · exact isGood_of_k_one hXne
    rcases Nat.eq_or_lt_of_le ht with rfl | ht2
    · exact isGood_of_t_one hXne
    -- By Lemma 2, pick `v ∈ X` with `fp G p X (Y.filter (G.Adj v)) ≥ p * fp G p X Y`.
    have hex_v : ∃ v ∈ X, p * fp G p X Y ≤ fp G p X (Y.filter (fun y => G.Adj v y)) := by
      by_contra hall
      push Not at hall
      have hsum_lt : ∑ v ∈ X, fp G p X (Y.filter (fun y => G.Adj v y)) <
          ∑ _v ∈ X, p * fp G p X Y :=
        Finset.sum_lt_sum_of_nonempty hXne hall
      rw [Finset.sum_const, nsmul_eq_mul] at hsum_lt
      have hlem2 := gnnw_lemma2 G p X Y
      linarith
    rcases hex_v with ⟨v, hvX, hv_fp⟩
    let Y' := Y.filter (fun y => G.Adj v y)
    let XR := X.filter (fun u => G.Adj v u)
    let XB := (X.erase v).filter (fun u => ¬G.Adj v u)
    have hdisj_RB : Disjoint XR XB := by
      rw [Finset.disjoint_left]
      intro u huR huB
      simp only [XR, XB, mem_filter] at huR huB
      exact huB.2 huR.2
    have hdisj_v : Disjoint ({v} : Finset (Fin N)) (XR ∪ XB) := by
      rw [Finset.disjoint_singleton_left, mem_union]
      rintro (hR | hB)
      · exact G.loopless.irrefl v (mem_filter.mp hR).2
      · exact (Finset.notMem_erase v X) (mem_filter.mp hB).1
    have hX_split : X = insert v (XR ∪ XB) := by
      ext u
      simp only [XR, XB, mem_insert, mem_union, mem_filter, mem_erase]
      constructor
      · intro huX
        by_cases huv : u = v
        · exact Or.inl huv
        · by_cases hadj : G.Adj v u
          · exact Or.inr (Or.inl ⟨huX, hadj⟩)
          · exact Or.inr (Or.inr ⟨⟨huv, huX⟩, hadj⟩)
      · rintro (rfl | ⟨huX, _⟩ | ⟨⟨_, huX⟩, _⟩)
        · exact hvX
        · exact huX
        · exact huX
    have hXR_sub : XR ⊆ X := Finset.filter_subset _ X
    have hXB_sub : XB ⊆ X := Finset.Subset.trans (Finset.filter_subset _ _) (Finset.erase_subset v X)
    have hY'_sub : Y' ⊆ Y := Finset.filter_subset _ Y
    -- Case 1: `fp G p XR Y'` is large enough to recurse on `(k - 1, l, t)`.
    by_cases hR : ((k + t - 1 : ℕ) : ℝ) / ((k + t : ℕ) : ℝ) * x * fp G p X Y ≤ fp G p XR Y'
    · have hih_R : IsGood G (k - 1) l t XR Y' := by
        apply ih (k - 1 + t) (by omega) (k - 1) l t (by omega) hl ht rfl XR Y'
          (Disjoint.mono hXR_sub hY'_sub hdisj)
        have hpow_x : x * x⁻¹ ^ (k - 1) = x⁻¹ ^ (k - 1 - 1) := by
          have hkm1 : k - 1 = (k - 1 - 1) + 1 := by omega
          conv_lhs => rw [hkm1, pow_succ]
          field_simp [ne_of_gt hx0]
        have hkt_pos : (0 : ℝ) < ((k + t : ℕ) : ℝ) := by positivity
        have hkt_eq : ((k - 1 + t : ℕ) : ℝ) = ((k + t - 1 : ℕ) : ℝ) := by congr 1; omega
        calc ((k - 1 + t : ℕ) : ℝ) * x⁻¹ ^ (k - 1 - 1) * (1 - x)⁻¹ ^ (l - 1) * (p - x)⁻¹ ^ (t - 1)
            = ((k + t - 1 : ℕ) : ℝ) / ((k + t : ℕ) : ℝ) * x *
                (((k + t : ℕ) : ℝ) * x⁻¹ ^ (k - 1) * (1 - x)⁻¹ ^ (l - 1) * (p - x)⁻¹ ^ (t - 1)) := by
              rw [hkt_eq, ← hpow_x]
              field_simp [ne_of_gt hkt_pos]
          _ ≤ ((k + t - 1 : ℕ) : ℝ) / ((k + t : ℕ) : ℝ) * x * fp G p X Y := by
              exact mul_le_mul_of_nonneg_left hfp (by positivity)
          _ ≤ fp G p XR Y' := hR
      rcases hih_R with ⟨c, hc, hcl⟩ | ⟨c, hc, hcl⟩ | ⟨c, hc, hcl⟩
      · left
        have hv_not : v ∉ c := by
          intro hvc
          rcases mem_union.mp (hc hvc) with hvR | hvY'
          · exact G.loopless.irrefl v (mem_filter.mp hvR).2
          · exact Finset.disjoint_left.mp hdisj hvX (hY'_sub hvY')
        refine ⟨insert v c, ?_, ?_, ?_⟩
        · intro u hu
          rcases mem_insert.mp hu with rfl | huc
          · exact mem_union_left Y hvX
          · exact Finset.union_subset_union hXR_sub hY'_sub (hc huc)
        · intro a ha b hb hab
          rcases mem_insert.mp ha with hav | hac <;>
          rcases mem_insert.mp hb with hbv | hbc
          · exact absurd (hav.trans hbv.symm) hab
          · rw [hav]
            rcases mem_union.mp (hc hbc) with h1 | h2
            · exact (mem_filter.mp h1).2
            · exact (mem_filter.mp h2).2
          · rw [hbv]
            rcases mem_union.mp (hc hac) with h1 | h2
            · exact (mem_filter.mp h1).2.symm
            · exact (mem_filter.mp h2).2.symm
          · exact hcl.1 hac hbc hab
        · rw [Finset.card_insert_of_notMem hv_not, hcl.card_eq]; omega
      · exact Or.inr (Or.inl ⟨c, Finset.Subset.trans hc hXR_sub, hcl⟩)
      · exact Or.inr (Or.inr ⟨c, Finset.Subset.trans hc hY'_sub, hcl⟩)
    · push Not at hR
      -- Case 2: `fp G p XB Y'` is large enough to recurse on `(k, l, t - 1)`.
      by_cases hB :
          ((k + t - 1 : ℕ) : ℝ) / ((k + t : ℕ) : ℝ) * (p - x) * fp G p X Y ≤ fp G p XB Y'
      · have hih_B : IsGood G k l (t - 1) XB Y' := by
          apply ih (k + (t - 1)) (by omega) k l (t - 1) hk hl (by omega) rfl XB Y'
            (Disjoint.mono hXB_sub hY'_sub hdisj)
          have hpow_px : (p - x) * (p - x)⁻¹ ^ (t - 1) = (p - x)⁻¹ ^ (t - 1 - 1) := by
            have htm1 : t - 1 = (t - 1 - 1) + 1 := by omega
            conv_lhs => rw [htm1, pow_succ]
            field_simp [ne_of_gt hpx]
          have hkt_pos : (0 : ℝ) < ((k + t : ℕ) : ℝ) := by positivity
          have hkt_eq : ((k + (t - 1) : ℕ) : ℝ) = ((k + t - 1 : ℕ) : ℝ) := by congr 1; omega
          calc ((k + (t - 1) : ℕ) : ℝ) * x⁻¹ ^ (k - 1) * (1 - x)⁻¹ ^ (l - 1) *
                (p - x)⁻¹ ^ (t - 1 - 1)
              = ((k + t - 1 : ℕ) : ℝ) / ((k + t : ℕ) : ℝ) * (p - x) *
                  (((k + t : ℕ) : ℝ) * x⁻¹ ^ (k - 1) * (1 - x)⁻¹ ^ (l - 1) *
                    (p - x)⁻¹ ^ (t - 1)) := by
                rw [hkt_eq, ← hpow_px]
                field_simp [ne_of_gt hkt_pos]
            _ ≤ ((k + t - 1 : ℕ) : ℝ) / ((k + t : ℕ) : ℝ) * (p - x) * fp G p X Y := by
                exact mul_le_mul_of_nonneg_left hfp (by positivity)
            _ ≤ fp G p XB Y' := hB
        rcases hih_B with ⟨c, hc, hcl⟩ | ⟨c, hc, hcl⟩ | ⟨c, hc, hcl⟩
        · exact Or.inl ⟨c, Finset.Subset.trans hc (Finset.union_subset_union hXB_sub hY'_sub), hcl⟩
        · right; left
          have hv_not : v ∉ c := fun hvc => (Finset.notMem_erase v X) (mem_filter.mp (hc hvc)).1
          refine ⟨insert v c, ?_, ?_, ?_⟩
          · intro u hu
            rcases mem_insert.mp hu with rfl | huc
            · exact hvX
            · exact hXB_sub (hc huc)
          · intro a ha b hb hab
            rcases mem_insert.mp ha with hav | hac <;>
            rcases mem_insert.mp hb with hbv | hbc
            · exact absurd (hav.trans hbv.symm) hab
            · rw [hav] at hab ⊢
              exact ⟨hab, (mem_filter.mp (hc hbc)).2⟩
            · rw [hbv] at hab ⊢
              exact ⟨hab, fun h => (mem_filter.mp (hc hac)).2 h.symm⟩
            · exact hcl.1 hac hbc hab
          · rw [Finset.card_insert_of_notMem hv_not, hcl.card_eq]; omega
        · exact Or.inr (Or.inr ⟨c, Finset.Subset.trans hc hY'_sub, hcl⟩)
      · push Not at hB
        -- Case 3: Neither branch fires ⇒ `|Y| ≥ R(k, l)`!
        have hfp_split : fp G p X Y' = fp G p {v} Y' + fp G p XR Y' + fp G p XB Y' := by
          have hEq : X = {v} ∪ (XR ∪ XB) := by rw [Finset.singleton_union]; exact hX_split
          rw [hEq, fp_union_left G p hdisj_v, fp_union_left G p hdisj_RB]
          ring
        have hfp_v_le : fp G p {v} Y' ≤ (Y.card : ℝ) := by
          unfold fp
          have he : eR G {v} Y' ≤ (Y.card : ℝ) := by
            rw [eR_singleton_left]
            exact_mod_cast le_trans (Finset.card_filter_le Y' _) (Finset.card_le_card hY'_sub)
          have hnn : 0 ≤ p * (({v} : Finset (Fin N)).card : ℝ) * (Y'.card : ℝ) :=
            mul_nonneg (mul_nonneg hp0.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
          linarith
        have hY_ge : p / ((k + t : ℕ) : ℝ) * fp G p X Y < (Y.card : ℝ) := by
          have hkt_pos : (0 : ℝ) < ((k + t : ℕ) : ℝ) := by positivity
          have hkt_sub : ((k + t - 1 : ℕ) : ℝ) = ((k + t : ℕ) : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega)]; simp
          have hsum_rb : fp G p XR Y' + fp G p XB Y' <
              ((k + t - 1 : ℕ) : ℝ) / ((k + t : ℕ) : ℝ) * p * fp G p X Y := by
            linarith
          have hcomb : p * fp G p X Y <
              ((k + t - 1 : ℕ) : ℝ) / ((k + t : ℕ) : ℝ) * p * fp G p X Y + (Y.card : ℝ) := by
            linarith
          have hdiff_eq : p * fp G p X Y -
              ((k + t - 1 : ℕ) : ℝ) / ((k + t : ℕ) : ℝ) * p * fp G p X Y =
              p / ((k + t : ℕ) : ℝ) * fp G p X Y := by
            rw [hkt_sub]; field_simp [ne_of_gt hkt_pos]; ring
          linarith
        have hpx_pow : 1 ≤ p * (p - x)⁻¹ ^ (t - 1) := by
          have htm1 : 1 ≤ t - 1 := by omega
          have hinv_ge : p⁻¹ ≤ (p - x)⁻¹ := inv_anti₀ hpx (by linarith)
          have hinv_ge1 : 1 ≤ (p - x)⁻¹ := one_le_inv₀ hpx |>.mpr (by linarith)
          calc (1 : ℝ) = p * p⁻¹ := by field_simp [show p ≠ 0 by linarith]
            _ ≤ p * (p - x)⁻¹ := by exact mul_le_mul_of_nonneg_left hinv_ge (by linarith)
            _ = p * (p - x)⁻¹ ^ 1 := by simp
            _ ≤ p * (p - x)⁻¹ ^ (t - 1) := by
                exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hinv_ge1 htm1) (by linarith)
        have hY_ge_R : (R2 k l : ℝ) ≤ (Y.card : ℝ) := by
          have hobs := gnnw_obs3 hx0 (lt_trans hxp hp1) (k + l) k l hk hl rfl
          have hkt_pos : (0 : ℝ) < ((k + t : ℕ) : ℝ) := by positivity
          calc (R2 k l : ℝ) ≤ x⁻¹ ^ (k - 1) * (1 - x)⁻¹ ^ (l - 1) := hobs
            _ = x⁻¹ ^ (k - 1) * (1 - x)⁻¹ ^ (l - 1) * 1 := by ring
            _ ≤ x⁻¹ ^ (k - 1) * (1 - x)⁻¹ ^ (l - 1) * (p * (p - x)⁻¹ ^ (t - 1)) := by
                exact mul_le_mul_of_nonneg_left hpx_pow (by positivity)
            _ = p / ((k + t : ℕ) : ℝ) *
                  (((k + t : ℕ) : ℝ) * x⁻¹ ^ (k - 1) * (1 - x)⁻¹ ^ (l - 1) *
                    (p - x)⁻¹ ^ (t - 1)) := by
                field_simp [ne_of_gt hkt_pos]
            _ ≤ p / ((k + t : ℕ) : ℝ) * fp G p X Y := by
                exact mul_le_mul_of_nonneg_left hfp (by positivity)
            _ ≤ (Y.card : ℝ) := le_of_lt hY_ge
        have hY_nat : R2 k l ≤ Y.card := by exact_mod_cast hY_ge_R
        rcases exists_clique_in_subset (G := G) Y (R2_spec hk hl) hY_nat with
          ⟨c, hc, hcl⟩ | ⟨c, hc, hcl⟩
        · exact Or.inl ⟨c, Finset.Subset.trans hc Finset.subset_union_right, hcl⟩
        · exact Or.inr (Or.inr ⟨c, hc, hcl⟩)

/-- Exact subset-cut count: for distinct `u ≠ v` in `Fin n`, exactly `2^(n - 2)` subsets `X`
contain `u` and exclude `v`. -/
private lemma card_subsets_mem_notMem {n : ℕ} {u v : Fin n} (huv : u ≠ v) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun X => u ∈ X ∧ v ∉ X)).card =
      2 ^ (n - 2) := by
  let rest : Finset (Fin n) := (Finset.univ.erase u).erase v
  have hrest_card : rest.card = n - 2 := by
    have hv_in : v ∈ (Finset.univ : Finset (Fin n)).erase u :=
      Finset.mem_erase.mpr ⟨huv.symm, mem_univ v⟩
    rw [Finset.card_erase_of_mem hv_in, Finset.card_erase_of_mem (mem_univ u),
      Finset.card_univ, Fintype.card_fin]
    omega
  rw [← hrest_card, ← Finset.card_powerset rest]
  refine Finset.card_bij (fun X _ => X.erase u) ?_ ?_ ?_
  · intro X hX
    rw [mem_filter] at hX
    rw [Finset.mem_powerset]
    intro w hw
    simp only [rest, mem_erase, mem_univ, and_true]
    have hwu : w ≠ u := Finset.ne_of_mem_erase hw
    have hwX : w ∈ X := Finset.mem_of_mem_erase hw
    have hwv : w ≠ v := fun hEq => hX.2.2 (hEq ▸ hwX)
    exact ⟨hwv, hwu⟩
  · intro X1 hX1 X2 hX2 hEq
    have h1 : u ∈ X1 := (mem_filter.mp hX1).2.1
    have h2 : u ∈ X2 := (mem_filter.mp hX2).2.1
    rw [← Finset.insert_erase h1, ← Finset.insert_erase h2, hEq]
  · intro Z hZ
    rw [Finset.mem_powerset] at hZ
    have huZ : u ∉ Z := fun hu => by
      have := hZ hu
      simp [rest] at this
    have hvZ : v ∉ Z := fun hv => by
      have := hZ hv
      simp [rest] at this
    refine ⟨insert u Z, ?_, Finset.erase_insert huZ⟩
    rw [mem_filter]
    refine ⟨mem_univ _, mem_insert_self u Z, ?_⟩
    rw [mem_insert]
    push Not
    exact ⟨huv.symm, hvZ⟩

/-- Average excess `f_p(X, Xᶜ)` over all cuts `X ⊆ Fin n`. -/
private lemma exists_cut_fp_ge {n : ℕ} (G : SimpleGraph (Fin n)) {p : ℝ} (hp0 : 0 ≤ p) (hn : 2 ≤ n) :
    open Classical in
    ∃ X : Finset (Fin n),
      (1 / 4 : ℝ) * (∑ v : Fin n, ((Finset.univ.filter (fun u => G.Adj v u)).card : ℝ)) -
        p * (n : ℝ) ^ 2 / 4 ≤ fp G p X Xᶜ := by
  classical
  have hsum_eR : ∑ X : Finset (Fin n), eR G X Xᶜ =
      (2 : ℝ) ^ (n - 2) * (∑ v : Fin n, ((Finset.univ.filter (fun u => G.Adj v u)).card : ℝ)) := by
    calc ∑ X : Finset (Fin n), eR G X Xᶜ
        = ∑ X : Finset (Fin n), ∑ u : Fin n, ∑ v : Fin n,
            if G.Adj u v ∧ u ∈ X ∧ v ∉ X then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl (fun X _ => ?_)
          rw [eR_eq_sum_indicator, ← Finset.sum_subset (Finset.subset_univ X)]
          · refine Finset.sum_congr rfl (fun u hu => ?_)
            rw [← Finset.sum_subset (Finset.subset_univ Xᶜ)]
            · refine Finset.sum_congr rfl (fun v hv => ?_)
              have hv' : v ∉ X := Finset.mem_compl.mp hv
              simp [hu, hv']
            · intro v _ hv
              have hv' : v ∈ X := by simpa using hv
              simp [hv']
          · intro u _ hu
            simp [hu]
      _ = ∑ u : Fin n, ∑ v : Fin n, ∑ X : Finset (Fin n),
            if G.Adj u v ∧ u ∈ X ∧ v ∉ X then (1 : ℝ) else 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
      _ = ∑ u : Fin n, ∑ v : Fin n, if G.Adj u v then (2 : ℝ) ^ (n - 2) else 0 := by
          refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
          by_cases hadj : G.Adj u v
          · have huv : u ≠ v := G.ne_of_adj hadj
            simp only [hadj, true_and, Finset.sum_boole, ite_true]
            exact_mod_cast card_subsets_mem_notMem huv
          · simp [hadj]
      _ = (2 : ℝ) ^ (n - 2) *
            ∑ u : Fin n, ((Finset.univ.filter (fun v => G.Adj u v)).card : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun u _ => ?_)
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsum_prod : ∑ X : Finset (Fin n), (X.card : ℝ) * (Xᶜ.card : ℝ) =
      (2 : ℝ) ^ (n - 2) * ((n : ℝ) * ((n : ℝ) - 1)) := by
    calc ∑ X : Finset (Fin n), (X.card : ℝ) * (Xᶜ.card : ℝ)
        = ∑ X : Finset (Fin n), ∑ u : Fin n, ∑ v : Fin n,
            if u ≠ v ∧ u ∈ X ∧ v ∉ X then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl (fun X _ => ?_)
          have h1 : (X.card : ℝ) * (Xᶜ.card : ℝ) =
              ∑ u ∈ X, ∑ v ∈ Xᶜ, (1 : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
          rw [h1, ← Finset.sum_subset (Finset.subset_univ X)]
          · refine Finset.sum_congr rfl (fun u hu => ?_)
            rw [← Finset.sum_subset (Finset.subset_univ Xᶜ)]
            · refine Finset.sum_congr rfl (fun v hv => ?_)
              have hv' : v ∉ X := Finset.mem_compl.mp hv
              have huv : u ≠ v := fun hEq => hv' (hEq ▸ hu)
              simp [hu, hv', huv]
            · intro v _ hv
              have hv' : v ∈ X := by simpa using hv
              simp [hv']
          · intro u _ hu
            simp [hu]
      _ = ∑ u : Fin n, ∑ v : Fin n, ∑ X : Finset (Fin n),
            if u ≠ v ∧ u ∈ X ∧ v ∉ X then (1 : ℝ) else 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
      _ = ∑ u : Fin n, ∑ v : Fin n, if u ≠ v then (2 : ℝ) ^ (n - 2) else 0 := by
          refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
          by_cases huv : u ≠ v
          · rw [if_pos huv]
            have hconv : (∑ X : Finset (Fin n), if u ≠ v ∧ u ∈ X ∧ v ∉ X then (1 : ℝ) else 0) =
                (((Finset.univ : Finset (Finset (Fin n))).filter (fun X => u ∈ X ∧ v ∉ X)).card : ℝ) := by
              rw [← Finset.sum_boole]
              refine Finset.sum_congr rfl (fun X _ => by simp [huv])
            rw [hconv]
            exact_mod_cast card_subsets_mem_notMem huv
          · simp [huv]
      _ = (2 : ℝ) ^ (n - 2) * ((n : ℝ) * ((n : ℝ) - 1)) := by
          have hinner : ∀ u : Fin n,
              (∑ v : Fin n, if u ≠ v then (2 : ℝ) ^ (n - 2) else 0) =
                ((n : ℝ) - 1) * (2 : ℝ) ^ (n - 2) := by
            intro u
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            have hc : (Finset.univ.filter (fun v : Fin n => u ≠ v)).card = n - 1 := by
              have hEq : Finset.univ.filter (fun v : Fin n => u ≠ v) = Finset.univ.erase u := by
                ext v; simp [ne_comm]
              rw [hEq, Finset.card_erase_of_mem (mem_univ u), Finset.card_univ, Fintype.card_fin]
            rw [hc, Nat.cast_sub (by omega)]; simp
          rw [Finset.sum_congr rfl (fun u _ => hinner u), Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          ring
  -- By pigeonhole over `Finset (Fin n)` (size `2^n = 4 * 2^(n-2)`):
  set B : ℝ := (1 / 4 : ℝ) * (∑ v : Fin n, ((Finset.univ.filter (fun u => G.Adj v u)).card : ℝ)) -
    p * (n : ℝ) ^ 2 / 4
  by_contra hall
  push Not at hall
  have hlt : ∑ X : Finset (Fin n), fp G p X Xᶜ < ∑ _X : Finset (Fin n), B :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun X _ => hall X)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul] at hlt
  have hsum_fp : ∑ X : Finset (Fin n), fp G p X Xᶜ =
      (2 : ℝ) ^ (n - 2) *
        ((∑ v : Fin n, ((Finset.univ.filter (fun u => G.Adj v u)).card : ℝ)) -
          p * ((n : ℝ) * ((n : ℝ) - 1))) := by
    have : ∑ X : Finset (Fin n), fp G p X Xᶜ =
        (∑ X : Finset (Fin n), eR G X Xᶜ) -
          p * ∑ X : Finset (Fin n), (X.card : ℝ) * (Xᶜ.card : ℝ) := by
      unfold fp
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1; refine Finset.sum_congr rfl (fun _ _ => by ring)
    rw [this, hsum_eR, hsum_prod]; ring
  have h2n : ((2 ^ n : ℕ) : ℝ) = 4 * (2 : ℝ) ^ (n - 2) := by
    have : 2 ^ n = 4 * 2 ^ (n - 2) := by
      calc 2 ^ n = 2 ^ (2 + (n - 2)) := by rw [Nat.add_sub_of_le hn]
        _ = 2 ^ 2 * 2 ^ (n - 2) := pow_add 2 2 (n - 2)
        _ = 4 * 2 ^ (n - 2) := by norm_num
    exact_mod_cast this
  rw [hsum_fp, h2n] at hlt
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (n - 2) := by positivity
  have hpn : p * ((n : ℝ) * ((n : ℝ) - 1)) ≤ p * (n : ℝ) ^ 2 := by nlinarith
  dsimp [B] at hlt
  nlinarith

/-- **GNNW Theorem 5 (2024/2026) — Public Pure-Mathlib Off-Diagonal Exponential Ramsey Bound:**
For all `k, l ≥ 1` and `(√5 - 1)/(√5 + 1) < p < 1`,
`R(k, l) ≤ 4 (k + l) (((1 + √5)/2) p + (1 - √5)/2)^{-k/2} (1 - p)^{-l}`. -/
theorem ppl042_gnnw_offdiag_exponential_bound (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l)
    (p : ℝ) (hp1 : (Real.sqrt 5 - 1) / (Real.sqrt 5 + 1) < p) (hp2 : p < 1) :
    ((sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree k ∧ Gᶜ.CliqueFree l)} : ℕ) : ℝ) ≤
      4 * ((k + l : ℕ) : ℝ) *
        (((1 + Real.sqrt 5) / 2) * p + (1 - Real.sqrt 5) / 2) ^ (-(k : ℝ) / 2) *
        (1 - p) ^ (-(l : ℝ)) := by
  have hsq5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  set x : ℝ := ((1 + Real.sqrt 5) / 2) * p + (1 - Real.sqrt 5) / 2
  have hx0 : 0 < x := by
    have hdenom : 0 < Real.sqrt 5 + 1 := by linarith
    rw [div_lt_iff₀ hdenom] at hp1
    dsimp [x]
    nlinarith
  have hp0 : 0 < p := by
    have h1 : 0 < (Real.sqrt 5 - 1) / (Real.sqrt 5 + 1) := by
      have : 1 < Real.sqrt 5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
      positivity
    exact lt_trans h1 hp1
  have h1p : 0 < 1 - p := by linarith
  have hxp : x < p := by
    have : 1 < Real.sqrt 5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    dsimp [x]; nlinarith
  have hx1 : x < 1 := lt_trans hxp hp2
  have hquad : (1 - x) * (p - x) = (1 - p) ^ 2 := by
    dsimp [x]; nlinarith
  -- Induct on `l` for fixed `k`!
  change (R2 k l : ℝ) ≤ 4 * ((k + l : ℕ) : ℝ) * x ^ (-(k : ℝ) / 2) * (1 - p) ^ (-(l : ℝ))
  induction l, hl using Nat.le_induction with
  | base =>
    rw [R2_one_right k hk, Nat.cast_one]
    have h1 : 1 ≤ x ^ (-(k : ℝ) / 2) := by
      rw [Real.rpow_def_of_pos hx0]
      exact Real.one_le_exp (mul_nonneg_of_nonpos_of_nonpos
        (Real.log_nonpos hx0.le hx1.le) (by linarith [Nat.cast_nonneg (α := ℝ) k]))
    have h2 : 1 ≤ (1 - p) ^ (-((1 : ℕ) : ℝ)) := by
      rw [Real.rpow_def_of_pos h1p]
      exact Real.one_le_exp (mul_nonneg_of_nonpos_of_nonpos
        (Real.log_nonpos h1p.le (by linarith)) (by norm_num))
    have h3 : (1 : ℝ) ≤ 4 * ((k + 1 : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
      linarith
    nlinarith [mul_le_mul h1 h2 (by norm_num) (by positivity)]
  | succ l hl ih =>
    rcases Nat.eq_or_lt_of_le hk with rfl | hk2
    · rw [R2_one_left (l + 1) (by omega), Nat.cast_one]
      have h1 : 1 ≤ x ^ (-((1 : ℕ) : ℝ) / 2) := by
        rw [Real.rpow_def_of_pos hx0]
        exact Real.one_le_exp (mul_nonneg_of_nonpos_of_nonpos
          (Real.log_nonpos hx0.le hx1.le) (by norm_num))
      have h2 : 1 ≤ (1 - p) ^ (-((l + 1 : ℕ) : ℝ)) := by
        rw [Real.rpow_def_of_pos h1p]
        exact Real.one_le_exp (mul_nonneg_of_nonpos_of_nonpos
          (Real.log_nonpos h1p.le (by linarith)) (by linarith [Nat.cast_nonneg (α := ℝ) (l + 1)]))
      have h3 : (1 : ℝ) ≤ 4 * ((1 + (l + 1) : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ ((1 + (l + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 1 + (l + 1))
        linarith
      nlinarith [mul_le_mul h1 h2 (by norm_num) (by positivity)]
    · -- Main step: `k ≥ 2`, `l + 1 ≥ 2`. Prove `ramseyProp k (l + 1) n` for `n = ⌊B⌋₊`.
      set B : ℝ := 4 * ((k + (l + 1) : ℕ) : ℝ) * x ^ (-(k : ℝ) / 2) * (1 - p) ^ (-((l + 1 : ℕ) : ℝ))
      set n : ℕ := Nat.floor B
      have hB_ge : 4 * ((k + (l + 1) : ℕ) : ℝ) * x⁻¹ * (1 - p)⁻¹ ^ 2 ≤ B := by
        have hxk : x⁻¹ ≤ x ^ (-(k : ℝ) / 2) := by
          rw [← Real.rpow_neg_one x]
          exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le
            (by have h2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
                linarith)
        have hpl : (1 - p)⁻¹ ^ 2 ≤ (1 - p) ^ (-((l + 1 : ℕ) : ℝ)) := by
          rw [← Real.rpow_natCast (1 - p)⁻¹ 2, Real.inv_rpow h1p.le, ← Real.rpow_neg h1p.le]
          exact Real.rpow_le_rpow_of_exponent_ge h1p (by linarith)
            (by have h2 : (2 : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ l + 1)
                push_cast at h2 ⊢; linarith)
        dsimp [B]
        have h4 : (0 : ℝ) ≤ 4 * ((k + (l + 1) : ℕ) : ℝ) := by positivity
        calc 4 * ((k + (l + 1) : ℕ) : ℝ) * x⁻¹ * (1 - p)⁻¹ ^ 2
            = 4 * ((k + (l + 1) : ℕ) : ℝ) * (x⁻¹ * (1 - p)⁻¹ ^ 2) := by ring
          _ ≤ 4 * ((k + (l + 1) : ℕ) : ℝ) *
                (x ^ (-(k : ℝ) / 2) * (1 - p) ^ (-((l + 1 : ℕ) : ℝ))) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul hxk hpl (by positivity) (by positivity)) h4
          _ = 4 * ((k + (l + 1) : ℕ) : ℝ) * x ^ (-(k : ℝ) / 2) *
                (1 - p) ^ (-((l + 1 : ℕ) : ℝ)) := by ring
      have hB_ge16 : 16 ≤ B := by
        have h1 : (4 : ℝ) ≤ ((k + (l + 1) : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 4 ≤ k + (l + 1))
        have h2 : 1 ≤ x⁻¹ := one_le_inv₀ hx0 |>.mpr hx1.le
        have h3 : 1 ≤ (1 - p)⁻¹ ^ 2 := one_le_pow₀ (one_le_inv₀ h1p |>.mpr (by linarith))
        nlinarith [mul_le_mul h2 h3 (by norm_num) (by positivity)]
      have hn_le : (n : ℝ) ≤ B := Nat.floor_le (by linarith)
      have hB_lt : B < (n : ℝ) + 1 := Nat.lt_floor_add_one B
      have hn2 : 2 ≤ n := by
        have : (15 : ℝ) < (n : ℝ) := by linarith
        have : 15 < n := by exact_mod_cast this
        omega
      -- Key bound (7): `n ≥ 4 (k + l + 1) / (p (1 - p))`.
      have hn_lower7 : 4 * ((k + (l + 1) : ℕ) : ℝ) ≤ p * (1 - p) * (n : ℝ) := by
        have hstep : 4 * ((k + (l + 1) : ℕ) : ℝ) * (1 - p) ≤ p * (1 - p) ^ 2 * (n : ℝ) := by
          have h1 : p * (1 - p) ^ 2 * (4 * ((k + (l + 1) : ℕ) : ℝ) * x⁻¹ * (1 - p)⁻¹ ^ 2 - 1) ≤
              p * (1 - p) ^ 2 * (n : ℝ) := by
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have h2 : p * (1 - p) ^ 2 * (4 * ((k + (l + 1) : ℕ) : ℝ) * x⁻¹ * (1 - p)⁻¹ ^ 2) =
              4 * ((k + (l + 1) : ℕ) : ℝ) * (p * x⁻¹) := by
            field_simp [ne_of_gt h1p]
          have hpx1 : 1 ≤ p * x⁻¹ := by rw [← div_eq_mul_inv, one_le_div hx0]; linarith
          have h3 : 4 * ((k + (l + 1) : ℕ) : ℝ) ≤ 4 * ((k + (l + 1) : ℕ) : ℝ) * (p * x⁻¹) := by
            nlinarith
          have h4 : p * (1 - p) ^ 2 ≤ p * (4 * ((k + (l + 1) : ℕ) : ℝ)) := by
            have : (1 - p) ^ 2 ≤ 1 := by nlinarith
            have : (1 : ℝ) ≤ 4 * ((k + (l + 1) : ℕ) : ℝ) := by
              have : (4 : ℝ) ≤ ((k + (l + 1) : ℕ) : ℝ) := by
                exact_mod_cast (by omega : 4 ≤ k + (l + 1))
              linarith
            nlinarith
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_right (by linarith : (0 : ℝ) ≤ 1 - p) (by positivity : (0 : ℝ) ≤ p)]
      -- Actually deduce `hn_lower7` directly by cancelling `1 - p > 0`:
      have hn_lower7' : 4 * ((k + (l + 1) : ℕ) : ℝ) ≤ p * (1 - p) * (n : ℝ) := by
        have hstep : 4 * ((k + (l + 1) : ℕ) : ℝ) * (1 - p) ≤ p * (1 - p) ^ 2 * (n : ℝ) := by
          have h1 : p * (1 - p) ^ 2 * (4 * ((k + (l + 1) : ℕ) : ℝ) * x⁻¹ * (1 - p)⁻¹ ^ 2 - 1) ≤
              p * (1 - p) ^ 2 * (n : ℝ) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have h2 : p * (1 - p) ^ 2 * (4 * ((k + (l + 1) : ℕ) : ℝ) * x⁻¹ * (1 - p)⁻¹ ^ 2) =
              4 * ((k + (l + 1) : ℕ) : ℝ) * (p * x⁻¹) := by field_simp [ne_of_gt h1p]
          have hpx1 : 1 ≤ p * x⁻¹ := by rw [← div_eq_mul_inv, one_le_div hx0]; linarith
          have h4 : p * (1 - p) ^ 2 ≤ 4 * ((k + (l + 1) : ℕ) : ℝ) * p := by
            have : (1 - p) ^ 2 ≤ 1 := by nlinarith
            have : (4 : ℝ) ≤ ((k + (l + 1) : ℕ) : ℝ) := by
              exact_mod_cast (by omega : 4 ≤ k + (l + 1))
            nlinarith
          nlinarith
        have hmul : (4 * ((k + (l + 1) : ℕ) : ℝ)) * (1 - p) ≤ (p * (1 - p) * (n : ℝ)) * (1 - p) := by
          linarith
        exact le_of_mul_le_mul_right hmul h1p
      -- Now prove `ramseyProp k (l + 1) n`!
      have hram : ramseyProp k (l + 1) n := by
        classical
        intro G ⟨hGk, hGl1⟩
        set Bprev : ℝ := 4 * ((k + l : ℕ) : ℝ) * x ^ (-(k : ℝ) / 2) * (1 - p) ^ (-(l : ℝ))
        -- If any vertex has `|N_B(v)| ≥ R2 k l`, contradiction by IH!
        have hNB_lt : ∀ v : Fin n,
            ((Finset.univ.filter (fun u => u ≠ v ∧ ¬G.Adj v u)).card : ℝ) ≤ Bprev - 1 := by
          intro v
          let NB := Finset.univ.filter (fun u => u ≠ v ∧ ¬G.Adj v u)
          have hltR : NB.card < R2 k l := by
            by_contra hge
            push Not at hge
            rcases exists_clique_in_subset (G := G) NB (R2_spec hk hl) hge with
              ⟨c, _, hcl⟩ | ⟨c, hcNB, hcl⟩
            · exact hGk c hcl
            · have hv_not : v ∉ c := fun hvc => (mem_filter.mp (hcNB hvc)).2.1 rfl
              apply hGl1 (insert v c)
              refine ⟨?_, by rw [Finset.card_insert_of_notMem hv_not, hcl.card_eq]⟩
              intro a ha b hb hab
              rcases mem_insert.mp ha with hav | hac <;>
              rcases mem_insert.mp hb with hbv | hbc
              · exact absurd (hav.trans hbv.symm) hab
              · rw [hav] at hab ⊢; exact ⟨hab, (mem_filter.mp (hcNB hbc)).2.2⟩
              · rw [hbv] at hab ⊢; exact ⟨hab, fun h => (mem_filter.mp (hcNB hac)).2.2 h.symm⟩
              · exact hcl.1 hac hbc hab
          have hle_pred : (NB.card : ℝ) + 1 ≤ (R2 k l : ℝ) := by
            exact_mod_cast (hltR : NB.card + 1 ≤ R2 k l)
          linarith
        have hNR_ge : ∀ v : Fin n,
            (p + (1 - p) / ((k + (l + 1) : ℕ) : ℝ)) * (n : ℝ) - 1 ≤
              ((Finset.univ.filter (fun u => G.Adj v u)).card : ℝ) := by
          intro v
          let NR := Finset.univ.filter (fun u => G.Adj v u)
          let NB := Finset.univ.filter (fun u => u ≠ v ∧ ¬G.Adj v u)
          have hdisj : Disjoint NR NB := by
            rw [Finset.disjoint_left]
            intro u huR huB
            exact (mem_filter.mp huB).2.2 (mem_filter.mp huR).2
          have hunion : NR ∪ NB = Finset.univ.erase v := by
            ext u
            simp only [NR, NB, mem_union, mem_filter, mem_univ, true_and, mem_erase, and_true]
            constructor
            · rintro (hR | ⟨hne, _⟩)
              · exact (G.ne_of_adj hR).symm
              · exact hne
            · intro hne
              by_cases hR : G.Adj v u
              · exact Or.inl hR
              · exact Or.inr ⟨hne, hR⟩
          have hsum : (NR.card : ℝ) + (NB.card : ℝ) = (n : ℝ) - 1 := by
            have hnat : NR.card + NB.card = n - 1 := by
              rw [← Finset.card_union_of_disjoint hdisj, hunion,
                Finset.card_erase_of_mem (mem_univ v), Finset.card_univ, Fintype.card_fin]
            have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega)]; simp
            rw [← hsub]; exact_mod_cast hnat
          have hBprev_eq : Bprev = ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) * (1 - p) * B := by
            have hkl_pos : (0 : ℝ) < ((k + (l + 1) : ℕ) : ℝ) := by positivity
            have hrpow_step : (1 - p) * (1 - p) ^ (-((l + 1 : ℕ) : ℝ)) = (1 - p) ^ (-(l : ℝ)) := by
              conv_lhs => arg 1; rw [← Real.rpow_one (1 - p)]
              rw [← Real.rpow_add h1p]
              congr 1; push_cast; ring
            dsimp [Bprev, B]
            calc 4 * ((k + l : ℕ) : ℝ) * x ^ (-(k : ℝ) / 2) * (1 - p) ^ (-(l : ℝ))
                = 4 * ((k + l : ℕ) : ℝ) * x ^ (-(k : ℝ) / 2) *
                    ((1 - p) * (1 - p) ^ (-((l + 1 : ℕ) : ℝ))) := by rw [hrpow_step]
              _ = ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) * (1 - p) *
                    (4 * ((k + (l + 1) : ℕ) : ℝ) * x ^ (-(k : ℝ) / 2) *
                      (1 - p) ^ (-((l + 1 : ℕ) : ℝ))) := by
                  field_simp [ne_of_gt hkl_pos]
          have hNB_le : (NB.card : ℝ) ≤
              ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) * (1 - p) * ((n : ℝ) + 1) - 1 := by
            have h1 := hNB_lt v
            rw [hBprev_eq] at h1
            have h2 : ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) * (1 - p) * B ≤
                ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) * (1 - p) * ((n : ℝ) + 1) := by
              exact mul_le_mul_of_nonneg_left (le_of_lt hB_lt) (by positivity)
            linarith
          have hkl_pos : (0 : ℝ) < ((k + (l + 1) : ℕ) : ℝ) := by positivity
          have hkl_diff : 1 - ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) =
              1 / ((k + (l + 1) : ℕ) : ℝ) := by
            have hadd : ((k + (l + 1) : ℕ) : ℝ) = ((k + l : ℕ) : ℝ) + 1 := by push_cast; ring
            rw [hadd]; field_simp [show ((k + l : ℕ) : ℝ) + 1 ≠ 0 by positivity]; ring
          have hfrac_le1 : ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) * (1 - p) ≤ 1 := by
            have hle1 : ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) ≤ 1 := by
              rw [div_le_one hkl_pos]; exact_mod_cast (by omega : k + l ≤ k + (l + 1))
            nlinarith
          -- `(NR.card) = n - 1 - NB.card ≥ n - ((k+l)/(k+l+1))*(1-p)*(n+1)`
          -- `= n * (1 - (1-p) + (1-p)/(k+l+1)) - ((k+l)/(k+l+1))*(1-p) ≥ (p + (1-p)/(k+l+1))*n - 1`!
          have halg : (n : ℝ) - ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) * (1 - p) * ((n : ℝ) + 1) =
              (p + (1 - p) / ((k + (l + 1) : ℕ) : ℝ)) * (n : ℝ) -
                ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) * (1 - p) := by
            have h1 : (1 : ℝ) - ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) * (1 - p) =
                p + (1 - p) / ((k + (l + 1) : ℕ) : ℝ) := by
              have := hkl_diff
              have h2 : ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) =
                  1 - 1 / ((k + (l + 1) : ℕ) : ℝ) := by linarith
              rw [h2]; ring
            calc (n : ℝ) - ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) * (1 - p) * ((n : ℝ) + 1)
                = (1 - ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) * (1 - p)) * (n : ℝ) -
                    ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) * (1 - p) := by ring
              _ = (p + (1 - p) / ((k + (l + 1) : ℕ) : ℝ)) * (n : ℝ) -
                    ((k + l : ℕ) : ℝ) / ((k + (l + 1) : ℕ) : ℝ) * (1 - p) := by rw [h1]
          linarith
        -- Now average over cuts `(X, Xᶜ)` via `exists_cut_fp_ge`!
        obtain ⟨X, hX_fp⟩ := exists_cut_fp_ge G hp0.le hn2
        have hsum_NR : (n : ℝ) * ((p + (1 - p) / ((k + (l + 1) : ℕ) : ℝ)) * (n : ℝ) - 1) ≤
            ∑ v : Fin n, ((Finset.univ.filter (fun u => G.Adj v u)).card : ℝ) := by
          calc (n : ℝ) * ((p + (1 - p) / ((k + (l + 1) : ℕ) : ℝ)) * (n : ℝ) - 1)
              = ∑ _v : Fin n, ((p + (1 - p) / ((k + (l + 1) : ℕ) : ℝ)) * (n : ℝ) - 1) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            _ ≤ ∑ v : Fin n, ((Finset.univ.filter (fun u => G.Adj v u)).card : ℝ) :=
                Finset.sum_le_sum (fun v _ => hNR_ge v)
        have hfp_step1 : (1 - p) ^ 2 / ((k + (l + 1) : ℕ) : ℝ) * ((n : ℝ) ^ 2 / 4) ≤ fp G p X Xᶜ := by
          have hkl_pos : (0 : ℝ) < ((k + (l + 1) : ℕ) : ℝ) := by positivity
          have hA : (1 - p) / ((k + (l + 1) : ℕ) : ℝ) * ((n : ℝ) ^ 2 / 4) - (n : ℝ) / 4 ≤
              fp G p X Xᶜ := by
            linarith
          have hB_term : (n : ℝ) / 4 ≤
              p * (1 - p) / ((k + (l + 1) : ℕ) : ℝ) * ((n : ℝ) ^ 2 / 4) := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) (by positivity)]
            have : (4 * ((k + (l + 1) : ℕ) : ℝ)) * (n : ℝ) ≤ (p * (1 - p) * (n : ℝ)) * (n : ℝ) :=
              mul_le_mul_of_nonneg_right hn_lower7' (Nat.cast_nonneg n)
            nlinarith
          have hdiff_sq : (1 - p) / ((k + (l + 1) : ℕ) : ℝ) * ((n : ℝ) ^ 2 / 4) -
              p * (1 - p) / ((k + (l + 1) : ℕ) : ℝ) * ((n : ℝ) ^ 2 / 4) =
              (1 - p) ^ 2 / ((k + (l + 1) : ℕ) : ℝ) * ((n : ℝ) ^ 2 / 4) := by ring
          linarith
        -- Since `B ≥ 16` and `n > B - 1`, we have `n ≥ (1/2) * B`!
        have hn_halfB : B / 2 ≤ (n : ℝ) := by linarith
        -- Wait: GNNW needs `(n/2)^2 ≥ (B/2)^2 / 4`? Check:
        -- `B = 4 * (k + l + 1) * x^{-k/2} * (1-p)^{-(l+1)}`.
        -- So `B / 2 = 2 * (k + l + 1) * x^{-k/2} * (1-p)^{-(l+1)}`,
        -- and `(n^2 / 4) ≥ (B / 2)^2 / 4 = (k + l + 1)^2 * x^{-k} * (1-p)^{-2(l+1)}`!
        -- Multiply by `(1 - p)^2 / (k + l + 1)`:
        -- `≥ (k + l + 1) * x^{-k} * (1 - p)^{-2 l} = (k + l + 1) * x^{-k} * (1-x)^{-l} * (p-x)^{-l}`!
        -- EXACT MATCH FOR `gnnw_lemma4` WITH `t = l + 1` (since `l + 1 - 1 = l`)!!
        have hfp_final :
            ((k + (l + 1) : ℕ) : ℝ) * x⁻¹ ^ (k - 1) * (1 - x)⁻¹ ^ l * (p - x)⁻¹ ^ l ≤
              fp G p X Xᶜ := by
          have hkl_pos : (0 : ℝ) < ((k + (l + 1) : ℕ) : ℝ) := by positivity
          have hnsq : (B / 2) ^ 2 / 4 ≤ (n : ℝ) ^ 2 / 4 := by
            have : (B / 2) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
            linarith
          have hBsq_eq : (1 - p) ^ 2 / ((k + (l + 1) : ℕ) : ℝ) * ((B / 2) ^ 2 / 4) =
              ((k + (l + 1) : ℕ) : ℝ) * x⁻¹ ^ k * (1 - x)⁻¹ ^ l * (p - x)⁻¹ ^ l := by
            have hx_sq : (x ^ (-(k : ℝ) / 2)) ^ 2 = x⁻¹ ^ k := by
              rw [← Real.rpow_natCast (x ^ (-(k : ℝ) / 2)) 2,
                ← Real.rpow_mul hx0.le]
              have hmul : (-(k : ℝ) / 2) * (2 : ℕ) = -(k : ℝ) := by push_cast; ring
              rw [hmul, Real.rpow_neg hx0.le, Real.rpow_natCast, inv_pow]
            have hp_sq : (1 - p) ^ 2 * ((1 - p) ^ (-((l + 1 : ℕ) : ℝ))) ^ 2 =
                ((1 - p) ^ 2)⁻¹ ^ l := by
              rw [← Real.rpow_natCast ((1 - p) ^ (-((l + 1 : ℕ) : ℝ))) 2,
                ← Real.rpow_mul h1p.le]
              have hmul : (-((l + 1 : ℕ) : ℝ)) * (2 : ℕ) = -2 - 2 * (l : ℝ) := by push_cast; ring
              rw [hmul, ← Real.rpow_natCast (1 - p) 2, ← Real.rpow_add h1p]
              have hexp : (2 : ℕ) + (-2 - 2 * (l : ℝ)) = -(2 * (l : ℝ)) := by push_cast; ring
              rw [hexp, Real.rpow_neg h1p.le, Real.rpow_mul h1p.le,
                Real.rpow_two, Real.rpow_natCast, Real.rpow_natCast, inv_pow]
            have hquad_pow : ((1 - p) ^ 2)⁻¹ ^ l = (1 - x)⁻¹ ^ l * (p - x)⁻¹ ^ l := by
              rw [← hquad, mul_inv, mul_pow]
            have hB_def : B = 4 * ((k + (l + 1) : ℕ) : ℝ) * x ^ (-(k : ℝ) / 2) *
                (1 - p) ^ (-((l + 1 : ℕ) : ℝ)) := rfl
            rw [hB_def]
            calc (1 - p) ^ 2 / ((k + (l + 1) : ℕ) : ℝ) *
                    ((4 * ((k + (l + 1) : ℕ) : ℝ) * x ^ (-(k : ℝ) / 2) *
                      (1 - p) ^ (-((l + 1 : ℕ) : ℝ)) / 2) ^ 2 / 4)
                = ((k + (l + 1) : ℕ) : ℝ) * (x ^ (-(k : ℝ) / 2)) ^ 2 *
                    ((1 - p) ^ 2 * ((1 - p) ^ (-((l + 1 : ℕ) : ℝ))) ^ 2) := by
                  field_simp [ne_of_gt hkl_pos]; ring
              _ = ((k + (l + 1) : ℕ) : ℝ) * x⁻¹ ^ k * ((1 - p) ^ 2)⁻¹ ^ l := by
                  rw [hx_sq, hp_sq]
              _ = ((k + (l + 1) : ℕ) : ℝ) * x⁻¹ ^ k * (1 - x)⁻¹ ^ l * (p - x)⁻¹ ^ l := by
                  rw [hquad_pow]; ring
          have hx_mono : x⁻¹ ^ (k - 1) ≤ x⁻¹ ^ k :=
            pow_le_pow_right₀ (one_le_inv₀ hx0 |>.mpr hx1.le) (Nat.sub_le k 1)
          have h1x_nn : 0 ≤ (1 - x)⁻¹ ^ l := pow_nonneg (inv_nonneg.mpr (by linarith)) l
          have hpx_nn : 0 ≤ (p - x)⁻¹ ^ l := pow_nonneg (inv_nonneg.mpr (by linarith)) l
          have hkl_nn : (0 : ℝ) ≤ ((k + (l + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
          have hstep_x :
              ((k + (l + 1) : ℕ) : ℝ) * x⁻¹ ^ (k - 1) * (1 - x)⁻¹ ^ l * (p - x)⁻¹ ^ l ≤
                ((k + (l + 1) : ℕ) : ℝ) * x⁻¹ ^ k * (1 - x)⁻¹ ^ l * (p - x)⁻¹ ^ l :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hx_mono hkl_nn) h1x_nn) hpx_nn
          have hcoef_nn : (0 : ℝ) ≤ (1 - p) ^ 2 / ((k + (l + 1) : ℕ) : ℝ) :=
            div_nonneg (sq_nonneg _) hkl_nn
          exact le_trans hstep_x
            (le_trans (le_of_eq hBsq_eq.symm)
              (le_trans (mul_le_mul_of_nonneg_left hnsq hcoef_nn) hfp_step1))
        have hgood := gnnw_lemma4 G hx0 hxp hp2 (k + (l + 1)) k (l + 1) (l + 1)
          hk (by omega) (by omega) rfl X Xᶜ disjoint_compl_right
          (by simpa [Nat.add_sub_cancel] using hfp_final)
        rcases hgood with ⟨c, _, hcl⟩ | ⟨c, _, hcl⟩ | ⟨c, _, hcl⟩
        · exact hGk c hcl
        · exact hGl1 c hcl
        · exact hGl1 c hcl
      have hR_le : R2 k (l + 1) ≤ n := R2_le_of_ramseyProp hram
      exact le_trans (by exact_mod_cast hR_le) hn_le

/-! ### Section 5: GNNW Section 3 + Unconditional Diagonal Exponential Improvement `R(k) ≤ (399 / 100)^k` -/

/-- **GNNW Lemma 7 (Convexity of Density):**
`∑_{v ∈ X} d(X, N_R(v) ∩ Y) * |N_R(v) ∩ Y| ≥ e_R(X, Y) * d(X, Y)`. -/
private lemma gnnw_lemma7 {N : ℕ} (G : SimpleGraph (Fin N)) (X Y : Finset (Fin N))
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    open Classical in
    eR G X Y * dens G X Y ≤
      ∑ v ∈ X, dens G X (Y.filter (fun y => G.Adj v y)) *
        ((Y.filter (fun y => G.Adj v y)).card : ℝ) := by
  classical
  have hXpos : (0 : ℝ) < (X.card : ℝ) := Nat.cast_pos.mpr hX.card_pos
  have hYpos : (0 : ℝ) < (Y.card : ℝ) := Nat.cast_pos.mpr hY.card_pos
  have hRHS_mul :
      (X.card : ℝ) * (∑ v ∈ X, dens G X (Y.filter (fun y => G.Adj v y)) *
          ((Y.filter (fun y => G.Adj v y)).card : ℝ)) =
        ∑ y ∈ Y, (((X.filter (fun u => G.Adj y u)).card : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    calc ∑ v ∈ X, (X.card : ℝ) * (dens G X (Y.filter (fun y => G.Adj v y)) *
            ((Y.filter (fun y => G.Adj v y)).card : ℝ))
        = ∑ v ∈ X, eR G X (Y.filter (fun y => G.Adj v y)) := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [eR_eq_dens_mul]; ring
      _ = ∑ v ∈ X, eR G (Y.filter (fun y => G.Adj v y)) X :=
          Finset.sum_congr rfl (fun v _ => eR_symm G _ _)
      _ = ∑ v ∈ X, ∑ y ∈ Y,
            if G.Adj v y then ((X.filter (fun u => G.Adj y u)).card : ℝ) else 0 := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          unfold eR; push_cast; rw [Finset.sum_filter]
      _ = ∑ y ∈ Y, ∑ v ∈ X,
            if G.Adj v y then ((X.filter (fun u => G.Adj y u)).card : ℝ) else 0 :=
          Finset.sum_comm
      _ = ∑ y ∈ Y, (((X.filter (fun u => G.Adj y u)).card : ℝ)) ^ 2 := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          have hconv : (∑ v ∈ X, if G.Adj v y then ((X.filter (fun u => G.Adj y u)).card : ℝ) else 0) =
              ∑ v ∈ X.filter (fun v => G.Adj y v), ((X.filter (fun u => G.Adj y u)).card : ℝ) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl (fun v _ => ?_)
            by_cases h : G.Adj v y
            · simp [h, h.symm]
            · have h' : ¬G.Adj y v := fun hy => h hy.symm
              simp [h, h']
          rw [hconv, Finset.sum_const, nsmul_eq_mul, sq]
  have hsum_deg : ∑ y ∈ Y, ((X.filter (fun u => G.Adj y u)).card : ℝ) = eR G X Y := by
    rw [eR_symm]; unfold eR; push_cast; rfl
  have hcs : (eR G X Y) ^ 2 ≤ (Y.card : ℝ) * ∑ y ∈ Y, (((X.filter (fun u => G.Adj y u)).card : ℝ)) ^ 2 := by
    rw [← hsum_deg]
    let f : Fin N → ℝ := fun y => ((X.filter (fun u => G.Adj y u)).card : ℝ)
    have hnn : 0 ≤ ∑ y1 ∈ Y, ∑ y2 ∈ Y, (f y1 - f y2) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hexp : ∑ y1 ∈ Y, ∑ y2 ∈ Y, (f y1 - f y2) ^ 2 =
        2 * ((Y.card : ℝ) * (∑ y ∈ Y, (f y) ^ 2) - (∑ y ∈ Y, f y) ^ 2) := by
      have h1 : ∀ y1 ∈ Y, ∑ y2 ∈ Y, (f y1 - f y2) ^ 2 =
          (Y.card : ℝ) * (f y1) ^ 2 - 2 * f y1 * (∑ y2 ∈ Y, f y2) + ∑ y2 ∈ Y, (f y2) ^ 2 := by
        intro y1 _
        have hsq : ∀ y2 ∈ Y, (f y1 - f y2) ^ 2 = (f y1) ^ 2 - 2 * f y1 * f y2 + (f y2) ^ 2 :=
          fun _ _ => by ring
        rw [Finset.sum_congr rfl hsq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      have hmid : ∑ y1 ∈ Y, 2 * f y1 * (∑ y2 ∈ Y, f y2) = 2 * (∑ y ∈ Y, f y) ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, sq]; ring
      rw [hmid]; ring
    linarith
  have hLHS_mul : (X.card : ℝ) * (eR G X Y * dens G X Y) = (eR G X Y) ^ 2 / (Y.card : ℝ) := by
    have hd : dens G X Y = eR G X Y / ((X.card : ℝ) * (Y.card : ℝ)) := by
      unfold dens
      rw [if_neg (by push Not; exact ⟨ne_of_gt hX.card_pos, ne_of_gt hY.card_pos⟩)]
    rw [hd]; field_simp [ne_of_gt hXpos, ne_of_gt hYpos]
  have hle_mul : (X.card : ℝ) * (eR G X Y * dens G X Y) ≤
      (X.card : ℝ) * (∑ v ∈ X, dens G X (Y.filter (fun y => G.Adj v y)) *
        ((Y.filter (fun y => G.Adj v y)).card : ℝ)) := by
    rw [hLHS_mul, hRHS_mul, div_le_iff₀ hYpos]
    linarith
  exact le_of_mul_le_mul_left hle_mul hXpos

/-- Continuous convex falling factorial `∏_{i < b} max(z - i, 0)` on `ℝ`. -/
private def fallPow (b : ℕ) (z : ℝ) : ℝ :=
  ∏ i ∈ Finset.range b, max (z - (i : ℝ)) 0

private lemma fallPow_nonneg (b : ℕ) (z : ℝ) : 0 ≤ fallPow b z :=
  Finset.prod_nonneg (fun _ _ => le_max_right _ _)

private lemma fallPow_monotone (b : ℕ) : Monotone (fallPow b) := by
  intro x y hxy
  unfold fallPow
  exact Finset.prod_le_prod (fun _ _ => le_max_right _ _)
    (fun i _ => max_le_max_right 0 (by linarith))

private lemma convexOn_mul_of_monotone {f g : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfm : Monotone f) (hgm : Monotone g)
    (hfc : ConvexOn ℝ Set.univ f) (hgc : ConvexOn ℝ Set.univ g) :
    ConvexOn ℝ Set.univ (fun x => f x * g x) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hfx := hfc.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have hgx := hgc.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hfx hgx ⊢
  have hcheb : 0 ≤ (f x - f y) * (g x - g y) := by
    rcases le_total x y with hxy | hyx
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hfm hxy)) (sub_nonpos.mpr (hgm hxy))
    · exact mul_nonneg (sub_nonneg.mpr (hfm hyx)) (sub_nonneg.mpr (hgm hyx))
  have h1 : f (a * x + b * y) * g (a * x + b * y) ≤
      (a * f x + b * f y) * (a * g x + b * g y) :=
    mul_le_mul hfx hgx (hg0 _) (by nlinarith [hf0 x, hf0 y])
  have h2 : (a * f x + b * f y) * (a * g x + b * g y) =
      a * (f x * g x) + b * (f y * g y) - a * b * ((f x - f y) * (g x - g y)) := by
    calc (a * f x + b * f y) * (a * g x + b * g y)
        = (a + b) * (a * (f x * g x) + b * (f y * g y)) -
            a * b * ((f x - f y) * (g x - g y)) := by ring
      _ = a * (f x * g x) + b * (f y * g y) - a * b * ((f x - f y) * (g x - g y)) := by
          rw [hab, one_mul]
  nlinarith [mul_nonneg (mul_nonneg ha hb) hcheb]

private lemma convexOn_fallPow (b : ℕ) : ConvexOn ℝ Set.univ (fallPow b) := by
  induction b with
  | zero =>
    have hEq : fallPow 0 = fun _ => (1 : ℝ) := by ext z; simp [fallPow]
    rw [hEq]
    exact convexOn_const 1 convex_univ
  | succ b ih =>
    have hEq : fallPow (b + 1) = fun z => fallPow b z * max (z - (b : ℝ)) 0 := by
      ext z; simp [fallPow, Finset.prod_range_succ]
    rw [hEq]
    refine convexOn_mul_of_monotone (fallPow_nonneg b) (fun _ => le_max_right _ _)
      (fallPow_monotone b) (fun x y hxy => max_le_max_right 0 (by linarith)) ih ?_
    refine ⟨convex_univ, fun x _ y _ a b' ha hb' hab => ?_⟩
    simp only [smul_eq_mul]
    have hlin : a * x + b' * y - (b : ℝ) = a * (x - (b : ℝ)) + b' * (y - (b : ℝ)) := by
      calc a * x + b' * y - (b : ℝ) = a * x + b' * y - (a + b') * (b : ℝ) := by rw [hab, one_mul]
        _ = a * (x - (b : ℝ)) + b' * (y - (b : ℝ)) := by ring
    rw [hlin]
    refine max_le ?_ ?_
    · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb')
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb' (le_max_right _ _))

private lemma fallPow_natCast_eq (b d : ℕ) :
    fallPow b (d : ℝ) = (d.choose b : ℝ) * (b.factorial : ℝ) := by
  have hdesc : (d.descFactorial b : ℝ) = (d.choose b : ℝ) * (b.factorial : ℝ) := by
    have : d.descFactorial b = d.choose b * b.factorial := by
      rw [mul_comm, Nat.descFactorial_eq_factorial_mul_choose]
    exact_mod_cast this
  rw [← hdesc]
  clear hdesc
  induction b with
  | zero => simp [fallPow]
  | succ b ih =>
    rw [Nat.descFactorial_succ, Nat.cast_mul]
    have hfp : fallPow (b + 1) (d : ℝ) = fallPow b (d : ℝ) * max ((d : ℝ) - (b : ℝ)) 0 := by
      simp [fallPow, Finset.prod_range_succ]
    rw [hfp, ih]
    by_cases hbd : b ≤ d
    · have hsub : ((d - b : ℕ) : ℝ) = (d : ℝ) - (b : ℝ) := Nat.cast_sub hbd
      rw [hsub, max_eq_left (by rw [← hsub]; exact Nat.cast_nonneg _), mul_comm]
    · push Not at hbd
      have h0 : d - b = 0 := by omega
      rw [h0, Nat.cast_zero, zero_mul, max_eq_right (by
        have : (d : ℝ) < (b : ℝ) := by exact_mod_cast hbd
        linarith), mul_zero]

/-- Elementary inequality `exp (-2 u) ≤ 1 - u` for `0 ≤ u ≤ 1 / 2`. -/
private lemma exp_neg_two_mul_le_one_sub {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    Real.exp (-(2 * u)) ≤ 1 - u := by
  rw [Real.exp_neg]
  have hpos : 0 < Real.exp (2 * u) := Real.exp_pos _
  have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  have h2 : 1 ≤ (1 + 2 * u) * (1 - u) := by nlinarith
  have h3 : 1 ≤ Real.exp (2 * u) * (1 - u) := le_trans h2 (mul_le_mul_of_nonneg_right h1 (by linarith))
  rw [inv_le_iff_one_le_mul₀' hpos]
  linarith

/-- **GNNW Fact 8 (`[CGMS, Fact 4.2]`):**
For `0 < σ ≤ 1`, `1 ≤ b`, `b ≤ σ m / 2`,
`σ^b * C(m, b) * exp(-b^2 / (σ m)) ≤ fallPow b (σ m) / b!`. -/
private lemma gnnw_fact8 {σ : ℝ} {b m : ℕ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hb : 1 ≤ b) (hbm : (b : ℝ) ≤ σ * (m : ℝ) / 2) :
    σ ^ b * (m.choose b : ℝ) * Real.exp (-((b : ℝ) ^ 2) / (σ * (m : ℝ))) ≤
      fallPow b (σ * (m : ℝ)) / (b.factorial : ℝ) := by
  have hσm_pos : 0 < σ * (m : ℝ) := by
    have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by nlinarith
  have hfact_pos : (0 : ℝ) < (b.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos b)
  rw [le_div_iff₀ hfact_pos]
  have hcm : (m.choose b : ℝ) * (b.factorial : ℝ) = ∏ i ∈ Finset.range b, ((m : ℝ) - (i : ℝ)) := by
    rw [← fallPow_natCast_eq b m]
    unfold fallPow
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hib : (i : ℝ) < (b : ℝ) := by exact_mod_cast Finset.mem_range.mp hi
    have hmi : 0 ≤ (m : ℝ) - (i : ℝ) := by nlinarith
    exact max_eq_left hmi
  have hfall : fallPow b (σ * (m : ℝ)) = ∏ i ∈ Finset.range b, (σ * (m : ℝ) - (i : ℝ)) := by
    unfold fallPow
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hib : (i : ℝ) < (b : ℝ) := by exact_mod_cast Finset.mem_range.mp hi
    exact max_eq_left (by linarith)
  rw [hfall]
  -- Compare term-by-term: `σ * (m - i) * exp(-2 i / (σ m)) ≤ σ m - i` for all `i < b`!
  have hterm : ∀ i ∈ Finset.range b,
      σ * ((m : ℝ) - (i : ℝ)) * Real.exp (-(2 * ((i : ℝ) / (σ * (m : ℝ))))) ≤
        σ * (m : ℝ) - (i : ℝ) := by
    intro i hi
    have hib : (i : ℝ) < (b : ℝ) := by exact_mod_cast Finset.mem_range.mp hi
    have hu0 : 0 ≤ (i : ℝ) / (σ * (m : ℝ)) := by positivity
    have hu1 : (i : ℝ) / (σ * (m : ℝ)) ≤ 1 / 2 := by
      rw [div_le_iff₀ hσm_pos]; linarith
    have hexp := exp_neg_two_mul_le_one_sub hu0 hu1
    have h1 : σ * ((m : ℝ) - (i : ℝ)) ≤ σ * (m : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) i]
    have h2 : σ * (m : ℝ) * (1 - (i : ℝ) / (σ * (m : ℝ))) = σ * (m : ℝ) - (i : ℝ) := by
      field_simp [ne_of_gt hσm_pos]
    calc σ * ((m : ℝ) - (i : ℝ)) * Real.exp (-(2 * ((i : ℝ) / (σ * (m : ℝ)))))
        ≤ σ * (m : ℝ) * (1 - (i : ℝ) / (σ * (m : ℝ))) :=
          mul_le_mul h1 hexp (Real.exp_pos _).le hσm_pos.le
      _ = σ * (m : ℝ) - (i : ℝ) := h2
  have hprod :
      ∏ i ∈ Finset.range b, (σ * ((m : ℝ) - (i : ℝ)) * Real.exp (-(2 * ((i : ℝ) / (σ * (m : ℝ)))))) ≤
        ∏ i ∈ Finset.range b, (σ * (m : ℝ) - (i : ℝ)) := by
    refine Finset.prod_le_prod (fun i hi => ?_) hterm
    have hib : (i : ℝ) < (b : ℝ) := by exact_mod_cast Finset.mem_range.mp hi
    have hmi : 0 ≤ (m : ℝ) - (i : ℝ) := by nlinarith
    positivity
  have hprod_split :
      ∏ i ∈ Finset.range b, (σ * ((m : ℝ) - (i : ℝ)) * Real.exp (-(2 * ((i : ℝ) / (σ * (m : ℝ)))))) =
        σ ^ b * ((m.choose b : ℝ) * (b.factorial : ℝ)) *
          Real.exp (-(∑ i ∈ Finset.range b, 2 * ((i : ℝ) / (σ * (m : ℝ))))) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      ← hcm, ← Real.exp_sum, Finset.sum_neg_distrib]
  have hsum_i : ∑ i ∈ Finset.range b, 2 * ((i : ℝ) / (σ * (m : ℝ))) ≤ (b : ℝ) ^ 2 / (σ * (m : ℝ)) := by
    have hnat : 2 * (∑ i ∈ Finset.range b, i) = b * (b - 1) := by
      have := Finset.sum_range_id_mul_two b
      linarith
    have hnatR : (2 : ℝ) * (∑ i ∈ Finset.range b, (i : ℝ)) = (b : ℝ) * ((b : ℝ) - 1) := by
      have hsub : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by rw [Nat.cast_sub hb]; simp
      rw [← hsub, ← Nat.cast_sum]
      exact_mod_cast hnat
    have hrewrite : ∑ i ∈ Finset.range b, 2 * ((i : ℝ) / (σ * (m : ℝ))) =
        (2 * ∑ i ∈ Finset.range b, (i : ℝ)) / (σ * (m : ℝ)) := by
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hrewrite, hnatR]
    apply div_le_div_of_nonneg_right _ hσm_pos.le
    nlinarith
  have hexp_le : Real.exp (-((b : ℝ) ^ 2) / (σ * (m : ℝ))) ≤
      Real.exp (-(∑ i ∈ Finset.range b, 2 * ((i : ℝ) / (σ * (m : ℝ))))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  calc σ ^ b * (m.choose b : ℝ) * Real.exp (-((b : ℝ) ^ 2) / (σ * (m : ℝ))) * (b.factorial : ℝ)
      = σ ^ b * ((m.choose b : ℝ) * (b.factorial : ℝ)) * Real.exp (-((b : ℝ) ^ 2) / (σ * (m : ℝ))) := by ring
    _ ≤ σ ^ b * ((m.choose b : ℝ) * (b.factorial : ℝ)) *
          Real.exp (-(∑ i ∈ Finset.range b, 2 * ((i : ℝ) / (σ * (m : ℝ))))) := by
        exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
    _ = ∏ i ∈ Finset.range b,
          (σ * ((m : ℝ) - (i : ℝ)) * Real.exp (-(2 * ((i : ℝ) / (σ * (m : ℝ)))))) := hprod_split.symm
    _ ≤ ∏ i ∈ Finset.range b, (σ * (m : ℝ) - (i : ℝ)) := hprod

/-- **GNNW Lemma 9 (Big Blue Book Extraction):**
If `W ⊆ X` has `|W| ≥ R(k, m)` vertices of blue degree `≥ μ |X|` in `X`, `m ≥ 10 μ⁻¹ b^2`,
and `|X| ≥ 5 m^2`, then `X` contains a red `K_k` or a blue book `(S, T)` with `|S| = b` and
`|T| ≥ (μ^b / 2) |X|`. -/
private lemma gnnw_lemma9 {N : ℕ} (G : SimpleGraph (Fin N)) {μ : ℝ} {b k m : ℕ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hb : 1 ≤ b) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hm_ge : 10 * μ⁻¹ * (b : ℝ) ^ 2 ≤ (m : ℝ))
    (X : Finset (Fin N)) (hX_ge : 5 * m ^ 2 ≤ X.card)
    (hW : open Classical in R2 k m ≤
      (X.filter (fun v => μ * (X.card : ℝ) ≤
        ((X.filter (fun u => u ≠ v ∧ ¬G.Adj v u)).card : ℝ))).card) :
    (∃ s ⊆ X, G.IsNClique k s) ∨
      ∃ S ⊆ X, ∃ T ⊆ X, Disjoint S T ∧ S.card = b ∧ Gᶜ.IsNClique b S ∧
        (∀ u ∈ S, ∀ v ∈ T, Gᶜ.Adj u v) ∧ μ ^ b / 2 * (X.card : ℝ) ≤ (T.card : ℝ) := by
  classical
  let W := X.filter (fun v => μ * (X.card : ℝ) ≤
    ((X.filter (fun u => u ≠ v ∧ ¬G.Adj v u)).card : ℝ))
  have hWX : W ⊆ X := Finset.filter_subset _ X
  rcases exists_clique_in_subset (G := G) W (R2_spec hk hm) hW with
    ⟨s, hsW, hs⟩ | ⟨U, hUW, hUcl⟩
  · exact Or.inl ⟨s, Finset.Subset.trans hsW hWX, hs⟩
  · right
    have hUX : U ⊆ X := Finset.Subset.trans hUW hWX
    have hUcard : U.card = m := hUcl.card_eq
    let XU := X \ U
    have hXU_card : XU.card = X.card - m := by
      rw [Finset.card_sdiff_of_subset hUX, hUcard]
    have hX_gt_m : m < X.card := by nlinarith
    have hXU_pos : (0 : ℝ) < (XU.card : ℝ) := by
      have : 0 < XU.card := by omega
      exact_mod_cast this
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
    have hX_pos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast (by omega : 0 < X.card)
    -- Count blue edges between `U` and `XU = X \ U`.
    let eBU : ℝ := ∑ v ∈ XU, ((U.filter (fun u => Gᶜ.Adj u v)).card : ℝ)
    let σ : ℝ := eBU / ((m : ℝ) * (XU.card : ℝ))
    have heBU_eq : eBU = ∑ u ∈ U, ((XU.filter (fun v => Gᶜ.Adj u v)).card : ℝ) := by
      have h1 : eBU = ∑ v ∈ XU, ∑ u ∈ U, if Gᶜ.Adj u v then (1 : ℝ) else 0 := by
        dsimp [eBU]
        refine Finset.sum_congr rfl (fun v _ => by rw [Finset.sum_boole])
      have h2 : ∑ u ∈ U, ((XU.filter (fun v => Gᶜ.Adj u v)).card : ℝ) =
          ∑ u ∈ U, ∑ v ∈ XU, if Gᶜ.Adj u v then (1 : ℝ) else 0 :=
        Finset.sum_congr rfl (fun u _ => by rw [Finset.sum_boole])
      rw [h1, h2, Finset.sum_comm]
    have heBU_ge : (m : ℝ) * (μ * (X.card : ℝ) - (m : ℝ)) ≤ eBU := by
      rw [heBU_eq]
      calc (m : ℝ) * (μ * (X.card : ℝ) - (m : ℝ))
          = ∑ _u ∈ U, (μ * (X.card : ℝ) - (m : ℝ)) := by
            rw [Finset.sum_const, hUcard, nsmul_eq_mul]
        _ ≤ ∑ u ∈ U, ((XU.filter (fun v => Gᶜ.Adj u v)).card : ℝ) := by
            refine Finset.sum_le_sum (fun u huU => ?_)
            have huW : u ∈ W := hUW huU
            have hdeg : μ * (X.card : ℝ) ≤ ((X.filter (fun v => v ≠ u ∧ ¬G.Adj u v)).card : ℝ) :=
              (mem_filter.mp huW).2
            have hsub : X.filter (fun v => v ≠ u ∧ ¬G.Adj u v) ⊆
                XU.filter (fun v => Gᶜ.Adj u v) ∪ U := by
              intro v hv
              rw [mem_filter] at hv
              by_cases hvU : v ∈ U
              · exact mem_union_right _ hvU
              · apply mem_union_left
                rw [mem_filter]
                exact ⟨Finset.mem_sdiff.mpr ⟨hv.1, hvU⟩, hv.2.1.symm, hv.2.2⟩
            have hcard_le : (X.filter (fun v => v ≠ u ∧ ¬G.Adj u v)).card ≤
                (XU.filter (fun v => Gᶜ.Adj u v)).card + m := by
              rw [← hUcard]
              exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
            have hcard_leR : ((X.filter (fun v => v ≠ u ∧ ¬G.Adj u v)).card : ℝ) ≤
                ((XU.filter (fun v => Gᶜ.Adj u v)).card : ℝ) + (m : ℝ) := by exact_mod_cast hcard_le
            linarith
    have hσ_le1 : σ ≤ 1 := by
      dsimp [σ]
      rw [div_le_one (mul_pos hm_pos hXU_pos)]
      rw [heBU_eq]
      calc ∑ u ∈ U, ((XU.filter (fun v => Gᶜ.Adj u v)).card : ℝ)
          ≤ ∑ _u ∈ U, (XU.card : ℝ) :=
            Finset.sum_le_sum (fun u _ => by exact_mod_cast Finset.card_filter_le XU _)
        _ = (m : ℝ) * (XU.card : ℝ) := by rw [Finset.sum_const, hUcard, nsmul_eq_mul]
    have hmb_le : 5 * μ⁻¹ * (m : ℝ) * (b : ℝ) ≤ (X.card : ℝ) := by
      have hb_pos : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      have hX_geR : 5 * (m : ℝ) ^ 2 ≤ (X.card : ℝ) := by exact_mod_cast hX_ge
      have h1 : μ⁻¹ * (b : ℝ) ≤ (m : ℝ) := by
        have hb2 : (b : ℝ) ≤ 10 * (b : ℝ) ^ 2 := by nlinarith
        have hmul := mul_le_mul_of_nonneg_left hb2 (inv_nonneg.mpr hμ0.le)
        linarith
      nlinarith
    have hσ_ge_factor : μ * (1 - 1 / (5 * (b : ℝ))) ≤ σ := by
      have hXU_le : (XU.card : ℝ) ≤ (X.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := X) (t := U))
      have h1 : (μ * (X.card : ℝ) - (m : ℝ)) / (X.card : ℝ) ≤ σ := by
        dsimp [σ]
        rw [div_le_div_iff₀ hX_pos (mul_pos hm_pos hXU_pos)]
        have hstep : (μ * (X.card : ℝ) - (m : ℝ)) * ((m : ℝ) * (XU.card : ℝ)) ≤
            (m : ℝ) * (μ * (X.card : ℝ) - (m : ℝ)) * (X.card : ℝ) := by
          have hnn : 0 ≤ μ * (X.card : ℝ) - (m : ℝ) := by
            have hb_pos : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
            have : 5 * (m : ℝ) * (b : ℝ) ≤ μ * (X.card : ℝ) := by
              have := mul_le_mul_of_nonneg_left hmb_le hμ0.le
              have hsimp : μ * (5 * μ⁻¹ * (m : ℝ) * (b : ℝ)) = 5 * (m : ℝ) * (b : ℝ) := by
                field_simp [ne_of_gt hμ0]
              linarith
            nlinarith
          have hmul := mul_le_mul_of_nonneg_left hXU_le (mul_nonneg hnn hm_pos.le)
          linarith
        exact le_trans hstep (mul_le_mul_of_nonneg_right heBU_ge hX_pos.le)
      have h2 : μ * (1 - 1 / (5 * (b : ℝ))) ≤ (μ * (X.card : ℝ) - (m : ℝ)) / (X.card : ℝ) := by
        have hb_pos : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
        rw [le_div_iff₀ hX_pos]
        have h3 : (m : ℝ) ≤ μ * (X.card : ℝ) / (5 * (b : ℝ)) := by
          rw [le_div_iff₀ (by positivity)]
          have := mul_le_mul_of_nonneg_left hmb_le hμ0.le
          have hsimp : μ * (5 * μ⁻¹ * (m : ℝ) * (b : ℝ)) = 5 * (m : ℝ) * (b : ℝ) := by
            field_simp [ne_of_gt hμ0]
          linarith
        have halg : μ * (1 - 1 / (5 * (b : ℝ))) * (X.card : ℝ) =
            μ * (X.card : ℝ) - μ * (X.card : ℝ) / (5 * (b : ℝ)) := by ring
        linarith
      exact le_trans h2 h1
    have hσ_ge_half : (1 / 2 : ℝ) * μ ≤ σ := by
      have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      have h1 : 1 / (5 * (b : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      nlinarith
    have hσ0 : 0 < σ := by linarith
    -- Check `b ≤ σ m / 2` and `b^2 / (σ m) ≤ 1 / 5`!
    have hb2_le : (b : ℝ) ^ 2 / (σ * (m : ℝ)) ≤ 1 / 5 := by
      rw [div_le_iff₀ (mul_pos hσ0 hm_pos)]
      have h1 : 10 * (b : ℝ) ^ 2 ≤ μ * (m : ℝ) := by
        have := mul_le_mul_of_nonneg_left hm_ge hμ0.le
        have hsimp : μ * (10 * μ⁻¹ * (b : ℝ) ^ 2) = 10 * (b : ℝ) ^ 2 := by
          field_simp [ne_of_gt hμ0]
        linarith
      nlinarith
    have hbm : (b : ℝ) ≤ σ * (m : ℝ) / 2 := by
      have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      have : (b : ℝ) ^ 2 ≤ σ * (m : ℝ) / 5 := by
        rw [div_le_iff₀ (mul_pos hσ0 hm_pos)] at hb2_le; linarith
      nlinarith
    -- Double count pairs `(S ∈ U.powersetCard b, v ∈ XU)` with `∀ u ∈ S, Gᶜ.Adj u v`!
    let Tset : Finset (Fin N) → Finset (Fin N) := fun S =>
      XU.filter (fun v => ∀ u ∈ S, Gᶜ.Adj u v)
    have hsum_T : ∑ S ∈ U.powersetCard b, ((Tset S).card : ℝ) =
        ∑ v ∈ XU, (((U.filter (fun u => Gᶜ.Adj u v)).card).choose b : ℝ) := by
      calc ∑ S ∈ U.powersetCard b, ((Tset S).card : ℝ)
          = ∑ S ∈ U.powersetCard b, ∑ v ∈ XU, if ∀ u ∈ S, Gᶜ.Adj u v then (1 : ℝ) else 0 := by
            refine Finset.sum_congr rfl (fun S _ => by simp [Tset, Finset.sum_boole])
        _ = ∑ v ∈ XU, ∑ S ∈ U.powersetCard b, if ∀ u ∈ S, Gᶜ.Adj u v then (1 : ℝ) else 0 :=
            Finset.sum_comm
        _ = ∑ v ∈ XU, (((U.filter (fun u => Gᶜ.Adj u v)).card).choose b : ℝ) := by
            refine Finset.sum_congr rfl (fun v _ => ?_)
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
            have hEq : (U.powersetCard b).filter (fun S => ∀ u ∈ S, Gᶜ.Adj u v) =
                (U.filter (fun u => Gᶜ.Adj u v)).powersetCard b := by
              ext S
              simp only [mem_filter, Finset.mem_powersetCard]
              constructor
              · rintro ⟨⟨hSU, hSc⟩, hall⟩
                exact ⟨fun u hu => mem_filter.mpr ⟨hSU hu, hall u hu⟩, hSc⟩
              · rintro ⟨hSsub, hSc⟩
                exact ⟨⟨fun u hu => (mem_filter.mp (hSsub hu)).1, hSc⟩,
                  fun u hu => (mem_filter.mp (hSsub hu)).2⟩
            rw [hEq, Finset.card_powersetCard]
    -- Apply Jensen to `fallPow b` on `XU`!
    have hjensen : (XU.card : ℝ) * (fallPow b (σ * (m : ℝ)) / (b.factorial : ℝ)) ≤
        ∑ v ∈ XU, (((U.filter (fun u => Gᶜ.Adj u v)).card).choose b : ℝ) := by
      have hconv := (convexOn_fallPow b).map_sum_le
        (t := XU) (w := fun _ => (1 : ℝ) / (XU.card : ℝ))
        (p := fun v => ((U.filter (fun u => Gᶜ.Adj u v)).card : ℝ))
        (fun _ _ => by positivity)
        (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp [ne_of_gt hXU_pos])
        (fun _ _ => Set.mem_univ _)
      have havg : ∑ v ∈ XU, ((1 : ℝ) / (XU.card : ℝ)) •
          ((U.filter (fun u => Gᶜ.Adj u v)).card : ℝ) = σ * (m : ℝ) := by
        simp only [smul_eq_mul]
        rw [← Finset.mul_sum]
        change (1 / (XU.card : ℝ)) * eBU = σ * (m : ℝ)
        dsimp [σ]
        field_simp [ne_of_gt hXU_pos, ne_of_gt hm_pos]
      rw [havg] at hconv
      have hfact_pos : (0 : ℝ) < (b.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos b)
      have hconv' : (XU.card : ℝ) * fallPow b (σ * (m : ℝ)) ≤
          ∑ v ∈ XU, fallPow b ((U.filter (fun u => Gᶜ.Adj u v)).card : ℝ) := by
        simp only [smul_eq_mul] at hconv
        rw [← Finset.mul_sum] at hconv
        have := mul_le_mul_of_nonneg_left hconv hXU_pos.le
        have hsimp : (XU.card : ℝ) * ((1 / (XU.card : ℝ)) *
            ∑ v ∈ XU, fallPow b ((U.filter (fun u => Gᶜ.Adj u v)).card : ℝ)) =
            ∑ v ∈ XU, fallPow b ((U.filter (fun u => Gᶜ.Adj u v)).card : ℝ) := by
          field_simp [ne_of_gt hXU_pos]
        linarith
      have hrhs_eq : ∑ v ∈ XU, fallPow b ((U.filter (fun u => Gᶜ.Adj u v)).card : ℝ) =
          (b.factorial : ℝ) * ∑ v ∈ XU, (((U.filter (fun u => Gᶜ.Adj u v)).card).choose b : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun v _ => by rw [fallPow_natCast_eq]; ring)
      rw [hrhs_eq] at hconv'
      rw [mul_div_assoc', div_le_iff₀ hfact_pos]
      linarith
    -- Chain Fact 8 + Bernoulli `(1 - 1/(5b))^b ≥ 4/5` + `exp(-1/5) ≥ 4/5` + `1 - m/|X| ≥ 4/5`!
    have hsum_lower : (m.choose b : ℝ) * (μ ^ b / 2 * (X.card : ℝ)) ≤
        ∑ S ∈ U.powersetCard b, ((Tset S).card : ℝ) := by
      have hf8 := gnnw_fact8 hσ0 hσ_le1 hb hbm
      have hexp15 : (4 / 5 : ℝ) ≤ Real.exp (-(1 / 5 : ℝ)) := by
        linarith [Real.add_one_le_exp (-(1 / 5 : ℝ))]
      have hexp_ge : (4 / 5 : ℝ) ≤ Real.exp (-((b : ℝ) ^ 2) / (σ * (m : ℝ))) :=
        le_trans hexp15 (Real.exp_le_exp.mpr (by rw [neg_div]; linarith))
      have hbern : (4 / 5 : ℝ) ≤ (1 - 1 / (5 * (b : ℝ))) ^ b := by
        have hgen : ∀ (c : ℝ) (n : ℕ), 0 ≤ c → c ≤ 1 → 1 - (n : ℝ) * c ≤ (1 - c) ^ n := by
          intro c n hc0 hc1
          induction n with
          | zero => simp
          | succ r ihr =>
            rw [pow_succ, Nat.cast_succ]
            have h1 : (1 - (r : ℝ) * c) * (1 - c) ≤ (1 - c) ^ r * (1 - c) :=
              mul_le_mul_of_nonneg_right ihr (by linarith)
            have h2 : 0 ≤ (r : ℝ) * c ^ 2 := by positivity
            nlinarith
        have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
        have hc0 : (0 : ℝ) ≤ 1 / (5 * (b : ℝ)) := by positivity
        have hc1 : 1 / (5 * (b : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        have h2 := hgen (1 / (5 * (b : ℝ))) b hc0 hc1
        have hb0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have h3 : 1 - (b : ℝ) * (1 / (5 * (b : ℝ))) = 4 / 5 := by field_simp [hb0]; ring
        linarith
      have hσb : μ ^ b * (4 / 5) ≤ σ ^ b := by
        have h1 : (μ * (1 - 1 / (5 * (b : ℝ)))) ^ b ≤ σ ^ b := by
          apply pow_le_pow_left₀ _ hσ_ge_factor b
          have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
          have : 1 / (5 * (b : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          nlinarith
        rw [mul_pow] at h1
        exact le_trans (mul_le_mul_of_nonneg_left hbern (pow_nonneg hμ0.le b)) h1
      have hXU_ge : (4 / 5 : ℝ) * (X.card : ℝ) ≤ (XU.card : ℝ) := by
        have hX_ge5m : 5 * (m : ℝ) ≤ (X.card : ℝ) := by
          have : 5 * m ≤ X.card := by nlinarith
          exact_mod_cast this
        have hsub : (XU.card : ℝ) = (X.card : ℝ) - (m : ℝ) := by
          rw [hXU_card, Nat.cast_sub (le_of_lt hX_gt_m)]
        linarith
      have h64 : (1 / 2 : ℝ) ≤ (4 / 5) * (4 / 5) * (4 / 5) := by norm_num
      have hcomb : μ ^ b / 2 * (X.card : ℝ) ≤
          (XU.card : ℝ) * (σ ^ b * Real.exp (-((b : ℝ) ^ 2) / (σ * (m : ℝ)))) := by
        have hprod1 : (μ ^ b * (4 / 5)) * (4 / 5) ≤
            σ ^ b * Real.exp (-((b : ℝ) ^ 2) / (σ * (m : ℝ))) :=
          mul_le_mul hσb hexp_ge (by norm_num) (pow_nonneg hσ0.le b)
        have hprod2 : ((4 / 5) * (X.card : ℝ)) * ((μ ^ b * (4 / 5)) * (4 / 5)) ≤
            (XU.card : ℝ) * (σ ^ b * Real.exp (-((b : ℝ) ^ 2) / (σ * (m : ℝ)))) :=
          mul_le_mul hXU_ge hprod1 (by positivity) hXU_pos.le
        have hprod3 : μ ^ b / 2 * (X.card : ℝ) ≤
            ((4 / 5) * (X.card : ℝ)) * ((μ ^ b * (4 / 5)) * (4 / 5)) := by
          have : 0 ≤ μ ^ b * (X.card : ℝ) := by positivity
          nlinarith
        exact le_trans hprod3 hprod2
      calc (m.choose b : ℝ) * (μ ^ b / 2 * (X.card : ℝ))
          ≤ (m.choose b : ℝ) * ((XU.card : ℝ) * (σ ^ b * Real.exp (-((b : ℝ) ^ 2) / (σ * (m : ℝ))))) :=
            mul_le_mul_of_nonneg_left hcomb (Nat.cast_nonneg _)
        _ = (XU.card : ℝ) * (σ ^ b * (m.choose b : ℝ) * Real.exp (-((b : ℝ) ^ 2) / (σ * (m : ℝ)))) := by ring
        _ ≤ (XU.card : ℝ) * (fallPow b (σ * (m : ℝ)) / (b.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left hf8 hXU_pos.le
        _ ≤ ∑ v ∈ XU, (((U.filter (fun u => Gᶜ.Adj u v)).card).choose b : ℝ) := hjensen
        _ = ∑ S ∈ U.powersetCard b, ((Tset S).card : ℝ) := hsum_T.symm
    -- Pigeonhole over `U.powersetCard b` (size `m.choose b > 0`)!
    have hbm_nat : b ≤ m := by
      have : (b : ℝ) ≤ (m : ℝ) := by nlinarith
      exact_mod_cast this
    have hUpset_ne : (U.powersetCard b).Nonempty := by
      rw [← Finset.card_pos, Finset.card_powersetCard, hUcard]
      exact Nat.choose_pos hbm_nat
    have hex_S : ∃ S ∈ U.powersetCard b, μ ^ b / 2 * (X.card : ℝ) ≤ ((Tset S).card : ℝ) := by
      by_contra hall
      push Not at hall
      have hlt := Finset.sum_lt_sum_of_nonempty hUpset_ne hall
      rw [Finset.sum_const, Finset.card_powersetCard, hUcard, nsmul_eq_mul] at hlt
      linarith
    rcases hex_S with ⟨S, hSU, hT_ge⟩
    rw [Finset.mem_powersetCard] at hSU
    refine ⟨S, Finset.Subset.trans hSU.1 hUX, Tset S,
      Finset.Subset.trans (Finset.filter_subset _ XU) Finset.sdiff_subset,
      ?_, hSU.2, ⟨fun a ha b' hb' hab' => hUcl.1 (hSU.1 ha) (hSU.1 hb') hab', hSU.2⟩, ?_, hT_ge⟩
    · rw [Finset.disjoint_left]
      intro u huS huT
      exact (Finset.mem_sdiff.mp (mem_filter.mp huT).1).2 (hSU.1 huS)
    · intro u huS v hvT
      exact (mem_filter.mp hvT).2 u huS

/-- **Pure-Young-Inequality Monotonicity Lemma for Lemma 12** (zero derivatives!):
For `r ≥ 2`, `0 < x`, `0 < μ`, `0 ≤ λ ≤ λ₀ < 1`, and `λ₀ ≤ μ / (μ + x)`:
`x^{1/r} (1 - λ)^{1 - 1/r} + μ^{1/r} λ^{1 - 1/r} ≤ x^{1/r} (1 - λ₀)^{1 - 1/r} + μ^{1/r} λ₀^{1 - 1/r}`. -/
private lemma rpow_concave_mono {r : ℕ} {x μ l l0 : ℝ}
    (hr : 2 ≤ r) (hx : 0 < x) (hμ : 0 < μ)
    (hl0_pos : 0 < l0) (hl0_lt1 : l0 < 1) (hl_nn : 0 ≤ l) (hl_le : l ≤ l0)
    (hcrit : l0 ≤ μ / (μ + x)) :
    x ^ ((1 : ℝ) / (r : ℝ)) * (1 - l) ^ (1 - (1 : ℝ) / (r : ℝ)) +
      μ ^ ((1 : ℝ) / (r : ℝ)) * l ^ (1 - (1 : ℝ) / (r : ℝ)) ≤
    x ^ ((1 : ℝ) / (r : ℝ)) * (1 - l0) ^ (1 - (1 : ℝ) / (r : ℝ)) +
      μ ^ ((1 : ℝ) / (r : ℝ)) * l0 ^ (1 - (1 : ℝ) / (r : ℝ)) := by
  set α : ℝ := (1 : ℝ) / (r : ℝ)
  set β : ℝ := 1 - α
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hα0 : 0 < α := by dsimp [α]; positivity
  have hβ0 : 0 < β := by dsimp [β, α]; rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hαβ : α + β = 1 := by dsimp [β]; ring
  have hyoung : ∀ t t0 : ℝ, 0 ≤ t → 0 < t0 →
      t ^ β ≤ t0 ^ β * (α + β * (t / t0)) := by
    intro t t0 ht ht0
    have hy := Real.geom_mean_le_arith_mean2_weighted hα0.le hβ0.le
      (by norm_num : (0 : ℝ) ≤ 1) (div_nonneg ht ht0.le) hαβ
    rw [Real.one_rpow, one_mul, Real.div_rpow ht ht0.le] at hy
    have hmul := mul_le_mul_of_nonneg_left hy (Real.rpow_pos_of_pos ht0 β).le
    have hsimp : t0 ^ β * (t ^ β / t0 ^ β) = t ^ β := by
      field_simp [ne_of_gt (Real.rpow_pos_of_pos ht0 β)]
    linarith
  have h1 := hyoung (1 - l) (1 - l0) (by linarith) (by linarith)
  have h2 := hyoung l l0 hl_nn hl0_pos
  have hterm1 : x ^ α * (1 - l) ^ β ≤
      x ^ α * (1 - l0) ^ β + β * (x ^ α * (1 - l0) ^ (-α)) * (l0 - l) := by
    have hstep := mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos hx α).le
    have hpow : (1 - l0) ^ β / (1 - l0) = (1 - l0) ^ (-α) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one (1 - l0), ← Real.rpow_add (by linarith)]
      congr 1; dsimp [β]; ring
    have halg : x ^ α * ((1 - l0) ^ β * (α + β * ((1 - l) / (1 - l0)))) =
        x ^ α * (1 - l0) ^ β + β * (x ^ α * ((1 - l0) ^ β / (1 - l0))) * (l0 - l) := by
      have hα1 : α = 1 - β := by linarith
      rw [hα1]; field_simp [show (1 - l0) ≠ 0 by linarith]; ring
    rw [halg, hpow] at hstep
    exact hstep
  have hterm2 : μ ^ α * l ^ β ≤
      μ ^ α * l0 ^ β - β * (μ ^ α * l0 ^ (-α)) * (l0 - l) := by
    have hstep := mul_le_mul_of_nonneg_left h2 (Real.rpow_pos_of_pos hμ α).le
    have hpow : l0 ^ β / l0 = l0 ^ (-α) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one l0, ← Real.rpow_add hl0_pos]
      congr 1; dsimp [β]; ring
    have halg : μ ^ α * (l0 ^ β * (α + β * (l / l0))) =
        μ ^ α * l0 ^ β - β * (μ ^ α * (l0 ^ β / l0)) * (l0 - l) := by
      have hα1 : α = 1 - β := by linarith
      rw [hα1]; field_simp [ne_of_gt hl0_pos]; ring
    rw [halg, hpow] at hstep
    exact hstep
  -- Compare slopes: `x^α * (1 - l0)^(-α) ≤ μ^α * l0^(-α)` iff `x / (1 - l0) ≤ μ / l0`!
  have hslope : x ^ α * (1 - l0) ^ (-α) ≤ μ ^ α * l0 ^ (-α) := by
    have hdiv : x / (1 - l0) ≤ μ / l0 := by
      rw [div_le_div_iff₀ (by linarith) hl0_pos]
      rw [le_div_iff₀ (by linarith)] at hcrit
      nlinarith
    have hrpow := Real.rpow_le_rpow (by positivity) hdiv hα0.le
    rw [Real.div_rpow hx.le (by linarith), Real.div_rpow hμ.le hl0_pos.le] at hrpow
    rwa [Real.rpow_neg (by linarith), Real.rpow_neg hl0_pos.le, ← div_eq_mul_inv, ← div_eq_mul_inv]
  have hdiff_nn : 0 ≤ β * (μ ^ α * l0 ^ (-α) - x ^ α * (1 - l0) ^ (-α)) * (l0 - l) :=
    mul_nonneg (mul_nonneg hβ0.le (sub_nonneg.mpr hslope)) (sub_nonneg.mpr hl_le)
  linarith

/-- Helper: for any `a > 1` and `d : ℕ`, `∃ M > 0, ∀ m : ℕ, (m : ℝ) ^ d ≤ M * a ^ m`. -/
private lemma exists_poly_le_const_mul_pow {a : ℝ} (ha : 1 < a) (d : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ m : ℕ, (m : ℝ) ^ d ≤ M * a ^ m := by
  have ha0 : 0 < a := by linarith
  have hinv_lt : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  have htend : Tendsto (fun m : ℕ => (m : ℝ) ^ d * (a⁻¹) ^ m) atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one d (inv_nonneg.mpr ha0.le) hinv_lt
  have hev := (tendsto_order.mp htend).2 1 (by norm_num)
  rw [Filter.eventually_atTop] at hev
  rcases hev with ⟨M0, hM0⟩
  let M : ℝ := max 1 ((Finset.range (M0 + 1)).sum (fun m => (m : ℝ) ^ d))
  refine ⟨M, lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun m => ?_⟩
  by_cases hm : M0 ≤ m
  · have h1 := (hM0 m hm).le
    rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (pow_pos ha0 m)] at h1
    have hM1 : 1 ≤ M := le_max_left _ _
    nlinarith [pow_pos ha0 m]
  · push Not at hm
    have hmem : m ∈ Finset.range (M0 + 1) := Finset.mem_range.mpr (by omega)
    have hle : (m : ℝ) ^ d ≤ (Finset.range (M0 + 1)).sum (fun j => (j : ℝ) ^ d) :=
      Finset.single_le_sum (f := fun j : ℕ => (j : ℝ) ^ d) (fun j _ => pow_nonneg (Nat.cast_nonneg j) d) hmem
    have hleM : (m : ℝ) ^ d ≤ M := le_trans hle (le_max_right _ _)
    have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
    have hapow : 1 ≤ a ^ m := one_le_pow₀ ha.le
    nlinarith

/-- Auxiliary blue-book parameter `b(u)` for concrete GNNW Lemma 12 (`r = 64, ε = 1/200000`). -/
private noncomputable def gnnwBFun (u : ℕ) : ℕ :=
  max 1 (Nat.ceil ((2 * (64 : ℝ) * Real.log (u : ℝ) - (64 : ℝ) * Real.log (1 / 200000 : ℝ) +
    Real.log 2) / Real.log (1 + 1 / 200000 : ℝ)))

/-- Auxiliary blue-book parameter `m(u)` for concrete GNNW Lemma 12 (`μ = 381005/1000000`). -/
private noncomputable def gnnwMFun (u : ℕ) : ℕ :=
  max 1 (Nat.ceil (10 * (381005 / 1000000 : ℝ)⁻¹ * ((gnnwBFun u : ℝ) ^ 2)))

/-- **Modular Part 1 of GNNW Lemma 12:** Existence of a single uniform threshold `L₀ ≥ 2`
certifying all four asymptotic inequalities needed by the concrete `r = 64` induction. -/
private lemma gnnw_lemma12_params :
    ∃ L₀ : ℕ, 2 ≤ L₀ ∧
      ∀ k l t : ℕ, 1 ≤ k → L₀ ≤ l → 1 ≤ t →
        ((R2 k l : ℝ) ≤ (20071 / 100000 : ℝ)⁻¹ ^ k * (82161 / 100000 : ℝ)⁻¹ ^ l) ∧
        (1 ≤ ((1 / 200000 : ℝ) / ((k + t : ℕ) : ℝ)) ^ 64 * (1 + 1 / 200000 : ℝ) ^ (k + l + t)) ∧
        (((k + t : ℕ) : ℝ) ^ 2 / ((1 / 200000 : ℝ) ^ 2) ≤ (1 + 1 / 200000 : ℝ) ^ (k + l + t)) ∧
        (5 * ((gnnwMFun (k + t) : ℝ) ^ 2) ≤ (1 + 1 / 200000 : ℝ) ^ (k + l + t)) ∧
        ((R2 k (gnnwMFun (k + t)) : ℝ) ≤
          ((1 / 200000 : ℝ) * (1 / 2 - 1 / 200000 : ℝ) / ((k + t : ℕ) : ℝ) ^ 3) *
            (1 + 1 / 200000 : ℝ) ^ (k + l + t)) := by
  let ε0 : ℝ := 1 / 200000
  let p0 : ℝ := 1 / 2
  let μ : ℝ := 381005 / 1000000
  let x1 : ℝ := 20071 / 100000
  let y1 : ℝ := 82161 / 100000
  let q0 : ℝ := 1 - 200715 / 1000000
  have hε0 : 0 < ε0 := by norm_num [ε0]
  have h1ε : 1 < 1 + ε0 := by norm_num [ε0]
  have hlog1ε : 0 < Real.log (1 + ε0) := Real.log_pos h1ε
  -- (A) Base Ramsey bound from Theorem 5 at `q0`:
  have hq0_gt : (Real.sqrt 5 - 1) / (Real.sqrt 5 + 1) < q0 := by
    have hsqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
    have hsqrt5_lt : Real.sqrt 5 < 23 / 10 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    rw [div_lt_iff₀ (by linarith)]
    dsimp [q0]; nlinarith
  have hq0_lt1 : q0 < 1 := by norm_num [q0]
  have hinner_gt : y1 ^ 2 < ((1 + Real.sqrt 5) / 2) * q0 + (1 - Real.sqrt 5) / 2 := by
    have hsqrt5_lt : Real.sqrt 5 < 22361 / 10000 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    dsimp [y1, q0]; nlinarith
  have hinner_pos : 0 < ((1 + Real.sqrt 5) / 2) * q0 + (1 - Real.sqrt 5) / 2 :=
    lt_trans (sq_pos_of_pos (by norm_num [y1] : (0 : ℝ) < y1)) hinner_gt
  let y_base : ℝ := Real.sqrt (((1 + Real.sqrt 5) / 2) * q0 + (1 - Real.sqrt 5) / 2)
  have hy_base_gt : y1 < y_base := by
    dsimp [y_base]
    rw [Real.lt_sqrt (by norm_num [y1])]
    exact hinner_gt
  have hbase_all : ∀ k l : ℕ, 1 ≤ k → 1 ≤ l →
      (R2 k l : ℝ) ≤ 4 * ((k + l : ℕ) : ℝ) * (200715 / 1000000 : ℝ)⁻¹ ^ k * y_base⁻¹ ^ l := by
    intro k l hk hl
    have hthm5 := ppl042_gnnw_offdiag_exponential_bound l k hl hk q0 hq0_gt hq0_lt1
    change (R2 l k : ℝ) ≤ _ at hthm5
    rw [R2_symm k l]
    have h1q : 1 - q0 = 200715 / 1000000 := by dsimp [q0]; norm_num
    have hyb_pos : 0 < y_base := Real.sqrt_pos.mpr hinner_pos
    have hpow_l : (((1 + Real.sqrt 5) / 2) * q0 + (1 - Real.sqrt 5) / 2) ^ (-(l : ℝ) / 2) =
        y_base⁻¹ ^ l := by
      have hsq : ((1 + Real.sqrt 5) / 2) * q0 + (1 - Real.sqrt 5) / 2 = y_base ^ 2 :=
        (Real.sq_sqrt hinner_pos.le).symm
      rw [hsq, ← Real.rpow_natCast y_base 2, ← Real.rpow_mul hyb_pos.le]
      have hmul : (2 : ℕ) * (-(l : ℝ) / 2) = -(l : ℝ) := by push_cast; ring
      rw [hmul, Real.rpow_neg hyb_pos.le, Real.rpow_natCast, inv_pow]
    have hpow_k : (1 - q0) ^ (-(k : ℝ)) = (200715 / 1000000 : ℝ)⁻¹ ^ k := by
      rw [h1q, Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
    have hkl_comm : ((l + k : ℕ) : ℝ) = ((k + l : ℕ) : ℝ) := by congr 1; omega
    rw [hpow_l, hpow_k, hkl_comm] at hthm5
    linarith
  let cA : ℝ := min ((200715 / 1000000 : ℝ) / x1) (y_base / y1)
  have hcA_gt1 : 1 < cA := by
    refine lt_min ?_ ?_
    · norm_num [x1]
    · rw [one_lt_div (by norm_num [y1])]; exact hy_base_gt
  have htendA : Tendsto (fun m : ℕ => 4 * (m : ℝ) * (cA⁻¹) ^ m) atTop (nhds 0) := by
    have := (tendsto_pow_const_mul_const_pow_of_lt_one 1
      (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ cA)) (inv_lt_one_of_one_lt₀ hcA_gt1)).const_mul 4
    simpa [pow_one, mul_assoc] using this
  rcases Filter.eventually_atTop.mp ((tendsto_order.mp htendA).2 1 (by norm_num)) with ⟨L1, hL1⟩
  -- (B) Polynomial bounds for `u^64` and `u^2`:
  obtain ⟨M_r, hMr_pos, hMr⟩ := exists_poly_le_const_mul_pow h1ε 64
  obtain ⟨M_2, hM2_pos, hM2⟩ := exists_poly_le_const_mul_pow h1ε 2
  -- (C) Blue-book `m(u)` and `(u + m(u))^m(u)` bounds:
  have hblue : ∃ M3 : ℝ, 0 < M3 ∧ ∀ u : ℕ, 2 ≤ u →
      5 * ((gnnwMFun u : ℝ) ^ 2) ≤ M3 * (1 + ε0) ^ u ∧
      ((u : ℝ) + (gnnwMFun u : ℝ)) ^ (gnnwMFun u) * ((u : ℝ) ^ 3) / (ε0 * (p0 - ε0)) ≤
        M3 * (1 + ε0) ^ u := by
    let C0 : ℝ := (128 + |-(64 : ℝ) * Real.log ε0 + Real.log 2|) / Real.log (1 + ε0) + 2
    let Cb : ℝ := max 2 C0
    have hCb2 : 2 ≤ Cb := le_max_left 2 C0
    have hCb_ge : C0 ≤ Cb := le_max_right 2 C0
    have hb_le : ∀ u : ℕ, 2 ≤ u → (gnnwBFun u : ℝ) ≤ Cb * (Real.log (u : ℝ) + 1) := by
      intro u hu
      have hlu_nn : 0 ≤ Real.log (u : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ u))
      unfold gnnwBFun
      rw [Nat.cast_max, Nat.cast_one]
      refine max_le (by nlinarith) ?_
      have harg_nn : 0 ≤ (2 * (64 : ℝ) * Real.log (u : ℝ) - (64 : ℝ) * Real.log ε0 + Real.log 2) /
          Real.log (1 + ε0) := by
        have h1 : 0 < -Real.log ε0 := by rw [neg_pos]; exact Real.log_neg hε0 (by norm_num [ε0])
        have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        exact div_nonneg (by nlinarith) hlog1ε.le
      have hceil : ((Nat.ceil ((2 * (64 : ℝ) * Real.log (u : ℝ) - (64 : ℝ) * Real.log ε0 +
          Real.log 2) / Real.log (1 + ε0)) : ℕ) : ℝ) ≤
          (2 * (64 : ℝ) * Real.log (u : ℝ) - (64 : ℝ) * Real.log ε0 + Real.log 2) /
            Real.log (1 + ε0) + 1 := (Nat.ceil_lt_add_one harg_nn).le
      have hnum : 2 * (64 : ℝ) * Real.log (u : ℝ) - (64 : ℝ) * Real.log ε0 + Real.log 2 ≤
          (128 + |-(64 : ℝ) * Real.log ε0 + Real.log 2|) * (Real.log (u : ℝ) + 1) := by
        have h1 : -(64 : ℝ) * Real.log ε0 + Real.log 2 ≤ |-(64 : ℝ) * Real.log ε0 + Real.log 2| :=
          le_abs_self _
        have h2 : 0 ≤ |-(64 : ℝ) * Real.log ε0 + Real.log 2| := abs_nonneg _
        nlinarith
      have hdiv : (2 * (64 : ℝ) * Real.log (u : ℝ) - (64 : ℝ) * Real.log ε0 + Real.log 2) /
          Real.log (1 + ε0) ≤
          (128 + |-(64 : ℝ) * Real.log ε0 + Real.log 2|) / Real.log (1 + ε0) *
            (Real.log (u : ℝ) + 1) := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right hnum hlog1ε.le
      have hstep : (2 * (64 : ℝ) * Real.log (u : ℝ) - (64 : ℝ) * Real.log ε0 + Real.log 2) /
          Real.log (1 + ε0) + 1 ≤ C0 * (Real.log (u : ℝ) + 1) := by
        dsimp [C0]; nlinarith
      exact le_trans hceil (le_trans hstep (mul_le_mul_of_nonneg_right hCb_ge (by linarith)))
    let Cm : ℝ := 10 * μ⁻¹ * Cb ^ 2 + 2
    have hCm_pos : 0 < Cm := by
      have : 0 < μ := by norm_num [μ]
      dsimp [Cm]; positivity
    have hm_le : ∀ u : ℕ, 2 ≤ u → (gnnwMFun u : ℝ) ≤ Cm * (Real.log (u : ℝ) + 1) ^ 2 := by
      intro u hu
      have hlu_nn : 0 ≤ Real.log (u : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ u))
      unfold gnnwMFun
      rw [Nat.cast_max, Nat.cast_one]
      have hsq1 : (1 : ℝ) ≤ (Real.log (u : ℝ) + 1) ^ 2 := by nlinarith
      have hCm2 : 2 ≤ Cm := by
        have : 0 ≤ 10 * μ⁻¹ * Cb ^ 2 := by
          have : 0 < μ := by norm_num [μ]
          positivity
        dsimp [Cm]; linarith
      refine max_le (by nlinarith) ?_
      have harg_nn : 0 ≤ 10 * μ⁻¹ * ((gnnwBFun u : ℝ) ^ 2) := by
        have : 0 < μ := by norm_num [μ]
        positivity
      have hceil := (Nat.ceil_lt_add_one harg_nn).le
      have hb2 : (gnnwBFun u : ℝ) ^ 2 ≤ (Cb * (Real.log (u : ℝ) + 1)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (hb_le u hu) 2
      have h10 : 0 ≤ 10 * μ⁻¹ := by
        have : 0 < μ := by norm_num [μ]
        positivity
      have hmul := mul_le_mul_of_nonneg_left hb2 h10
      dsimp [Cm]; nlinarith
    let Klog : ℝ := Cm * (Real.log (1 + Cm) + 3) + 4
    have hKlog_pos : 0 < Klog := by
      have : 0 ≤ Real.log (1 + Cm) := Real.log_nonneg (by linarith)
      dsimp [Klog]; positivity
    have hlog3_tend : Tendsto (fun u : ℕ => (Real.log (u : ℝ)) ^ 3 / (u : ℝ)) atTop (nhds 0) := by
      have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 (by norm_num)
      simp only [one_mul, add_zero] at this
      exact this.comp tendsto_natCast_atTop_atTop
    have hdiv_tend : Tendsto (fun u : ℕ =>
        8 * Klog * ((Real.log (u : ℝ)) ^ 3 / (u : ℝ)) +
          |Real.log (ε0 * (p0 - ε0))| / (u : ℝ)) atTop (nhds 0) := by
      have h1 := hlog3_tend.const_mul (8 * Klog)
      have h2 : Tendsto (fun u : ℕ => |Real.log (ε0 * (p0 - ε0))| / (u : ℝ)) atTop (nhds 0) := by
        have hinv := tendsto_one_div_atTop_nhds_zero_nat.const_mul |Real.log (ε0 * (p0 - ε0))|
        simpa [div_eq_mul_inv] using hinv
      have h12 := h1.add h2
      simpa using h12
    rcases Filter.eventually_atTop.mp ((tendsto_order.mp hdiv_tend).2 (Real.log (1 + ε0)) hlog1ε) with ⟨U1, hU1⟩
    have htend_quad : Tendsto (fun u : ℕ => 5 * Cm ^ 2 * ((u : ℝ) + 1) ^ 4 * ((1 + ε0)⁻¹) ^ u) atTop (nhds 0) := by
      have ht4 := (tendsto_pow_const_mul_const_pow_of_lt_one 4
        (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 + ε0))
        (inv_lt_one_of_one_lt₀ h1ε)).const_mul (80 * Cm ^ 2)
      simp only [mul_zero] at ht4
      refine squeeze_zero' (by filter_upwards with u; positivity) ?_ ht4
      filter_upwards [eventually_ge_atTop 1] with u hu
      have hu1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
      have hpow : ((u : ℝ) + 1) ^ 4 ≤ 16 * (u : ℝ) ^ 4 := by
        calc ((u : ℝ) + 1) ^ 4 ≤ (2 * (u : ℝ)) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
          _ = 16 * (u : ℝ) ^ 4 := by ring
      have hmul := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 5 * Cm ^ 2 by positivity)
      have hmul2 := mul_le_mul_of_nonneg_right hmul (show 0 ≤ ((1 + ε0)⁻¹) ^ u by positivity)
      linarith
    rcases Filter.eventually_atTop.mp ((tendsto_order.mp htend_quad).2 1 (by norm_num)) with ⟨U2, hU2⟩
    let U0 : ℕ := max 4 (max U1 U2)
    let M3 : ℝ := max 1 ((Finset.range U0).sum (fun u =>
      5 * ((gnnwMFun u : ℝ) ^ 2) +
        ((u : ℝ) + (gnnwMFun u : ℝ)) ^ (gnnwMFun u) * ((u : ℝ) ^ 3) / (ε0 * (p0 - ε0))))
    have hM3_1 : 1 ≤ M3 := le_max_left _ _
    refine ⟨M3, by linarith, fun u hu => ?_⟩
    by_cases huU0 : U0 ≤ u
    · have hu4 : 4 ≤ u := le_trans (le_max_left _ _) huU0
      have huU1 : U1 ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) huU0
      have huU2 : U2 ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) huU0
      have hu_pos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (by omega : 0 < u)
      have hlu_ge1 : 1 ≤ Real.log (u : ℝ) := by
        have hexp_le4 : Real.exp 1 ≤ 4 := by
          have hhalf : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
            linarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
          rw [Real.exp_neg] at hhalf
          have h2 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
            rw [le_inv_comm₀ (by norm_num) (Real.exp_pos _)] at hhalf; linarith
          have hsq : Real.exp 1 = (Real.exp (1 / 2 : ℝ)) ^ 2 := by rw [sq, ← Real.exp_add]; norm_num
          rw [hsq]; nlinarith [Real.exp_pos (1 / 2 : ℝ)]
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) (le_trans hexp_le4 (by exact_mod_cast hu4))
      have hpow_pos : 0 < (1 + ε0) ^ u := pow_pos (by linarith) u
      constructor
      · have hm_u := hm_le u hu
        have hlog_le_u : Real.log (u : ℝ) ≤ (u : ℝ) :=
          le_trans (Real.log_le_sub_one_of_pos hu_pos) (by linarith)
        have hpow4 : (Real.log (u : ℝ) + 1) ^ 4 ≤ ((u : ℝ) + 1) ^ 4 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 4
        have hU2' := (hU2 u huU2).le
        rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ hpow_pos] at hU2'
        have hstep1 : 5 * ((gnnwMFun u : ℝ) ^ 2) ≤ 5 * Cm ^ 2 * (Real.log (u : ℝ) + 1) ^ 4 := by
          have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hm_u 2
          linarith [show (Cm * (Real.log (u : ℝ) + 1) ^ 2) ^ 2 = Cm ^ 2 * (Real.log (u : ℝ) + 1) ^ 4 by ring]
        have hstep2 : 5 * Cm ^ 2 * (Real.log (u : ℝ) + 1) ^ 4 ≤ 5 * Cm ^ 2 * ((u : ℝ) + 1) ^ 4 :=
          mul_le_mul_of_nonneg_left hpow4 (by positivity)
        have hstep3 : 5 * ((gnnwMFun u : ℝ) ^ 2) ≤ (1 + ε0) ^ u := by linarith
        exact le_trans hstep3 (by nlinarith)
      · have hcube : (Real.log (u : ℝ) + 1) ^ 3 ≤ 8 * (Real.log (u : ℝ)) ^ 3 := by
          calc (Real.log (u : ℝ) + 1) ^ 3 ≤ (2 * Real.log (u : ℝ)) ^ 3 :=
                pow_le_pow_left₀ (by linarith) (by linarith) 3
            _ = 8 * (Real.log (u : ℝ)) ^ 3 := by ring
        have hU1' := (hU1 u huU1).le
        have hmul := mul_le_mul_of_nonneg_left hU1' hu_pos.le
        have hsimp : (u : ℝ) * (8 * Klog * ((Real.log (u : ℝ)) ^ 3 / (u : ℝ)) +
            |Real.log (ε0 * (p0 - ε0))| / (u : ℝ)) =
            8 * Klog * (Real.log (u : ℝ)) ^ 3 + |Real.log (ε0 * (p0 - ε0))| := by
          field_simp [ne_of_gt hu_pos]
        rw [hsimp] at hmul
        have hK_dom : Klog * (Real.log (u : ℝ) + 1) ^ 3 - Real.log (ε0 * (p0 - ε0)) ≤
            (u : ℝ) * Real.log (1 + ε0) := by
          have habs : -Real.log (ε0 * (p0 - ε0)) ≤ |Real.log (ε0 * (p0 - ε0))| := neg_le_abs _
          have hK_mul := mul_le_mul_of_nonneg_left hcube hKlog_pos.le
          linarith
        have hum_le : (u : ℝ) + (gnnwMFun u : ℝ) ≤ (1 + Cm) * ((u : ℝ) ^ 3) := by
          have hm_u := hm_le u hu
          have hlu_le : Real.log (u : ℝ) + 1 ≤ (u : ℝ) := by linarith [Real.log_le_sub_one_of_pos hu_pos]
          have hsq : (Real.log (u : ℝ) + 1) ^ 2 ≤ (u : ℝ) ^ 2 :=
            pow_le_pow_left₀ (by linarith) hlu_le 2
          have hu1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast (by omega : 1 ≤ u)
          have hu_le3 : (u : ℝ) ≤ (u : ℝ) ^ 3 := by nlinarith
          have hu2_le3 : (u : ℝ) ^ 2 ≤ (u : ℝ) ^ 3 := by nlinarith
          have hm_le3 : (gnnwMFun u : ℝ) ≤ Cm * (u : ℝ) ^ 3 :=
            le_trans hm_u (mul_le_mul_of_nonneg_left (le_trans hsq hu2_le3) hCm_pos.le)
          linarith
        have hlog_um : Real.log ((u : ℝ) + (gnnwMFun u : ℝ)) ≤
            (Real.log (1 + Cm) + 3) * (Real.log (u : ℝ) + 1) := by
          have h1 : Real.log ((u : ℝ) + (gnnwMFun u : ℝ)) ≤ Real.log ((1 + Cm) * (u : ℝ) ^ 3) :=
            Real.log_le_log (by positivity) hum_le
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
          have hlogCm_nn : 0 ≤ Real.log (1 + Cm) := Real.log_nonneg (by linarith)
          have h3cast : ((3 : ℕ) : ℝ) = 3 := by norm_num
          rw [h3cast] at h1
          nlinarith
        have hlog_lhs :
            Real.log (((u : ℝ) + (gnnwMFun u : ℝ)) ^ (gnnwMFun u) * ((u : ℝ) ^ 3) / (ε0 * (p0 - ε0))) ≤
              (u : ℝ) * Real.log (1 + ε0) := by
          have hpos1 : 0 < ((u : ℝ) + (gnnwMFun u : ℝ)) ^ (gnnwMFun u) := by positivity
          have hpos2 : 0 < (u : ℝ) ^ 3 := by positivity
          have hpos3 : 0 < ε0 * (p0 - ε0) := by norm_num [ε0, p0]
          rw [Real.log_div (mul_pos hpos1 hpos2).ne' hpos3.ne',
            Real.log_mul hpos1.ne' hpos2.ne', Real.log_pow, Real.log_pow]
          have h3cast : ((3 : ℕ) : ℝ) = 3 := by norm_num
          rw [h3cast]
          have hlog_nn : 0 ≤ Real.log ((u : ℝ) + (gnnwMFun u : ℝ)) := by
            apply Real.log_nonneg
            have hu1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast (by omega : 1 ≤ u)
            linarith [Nat.cast_nonneg (α := ℝ) (gnnwMFun u)]
          have hmul_m : (gnnwMFun u : ℝ) * Real.log ((u : ℝ) + (gnnwMFun u : ℝ)) ≤
              Cm * (Real.log (1 + Cm) + 3) * (Real.log (u : ℝ) + 1) ^ 3 := by
            have hprod := mul_le_mul (hm_le u hu) hlog_um hlog_nn (by positivity)
            linarith [show Cm * (Real.log (u : ℝ) + 1) ^ 2 *
                ((Real.log (1 + Cm) + 3) * (Real.log (u : ℝ) + 1)) =
                Cm * (Real.log (1 + Cm) + 3) * (Real.log (u : ℝ) + 1) ^ 3 by ring]
          have h3lu : 3 * Real.log (u : ℝ) ≤ 4 * (Real.log (u : ℝ) + 1) ^ 3 := by
            have : 1 ≤ (Real.log (u : ℝ) + 1) ^ 2 := by nlinarith
            nlinarith
          have hK_eq : Klog * (Real.log (u : ℝ) + 1) ^ 3 =
              Cm * (Real.log (1 + Cm) + 3) * (Real.log (u : ℝ) + 1) ^ 3 +
                4 * (Real.log (u : ℝ) + 1) ^ 3 := by dsimp [Klog]; ring
          linarith
        have hpos_lhs : 0 < ((u : ℝ) + (gnnwMFun u : ℝ)) ^ (gnnwMFun u) * ((u : ℝ) ^ 3) / (ε0 * (p0 - ε0)) := by
          have : 0 < ε0 * (p0 - ε0) := by norm_num [ε0, p0]
          positivity
        have hle_pow : ((u : ℝ) + (gnnwMFun u : ℝ)) ^ (gnnwMFun u) * ((u : ℝ) ^ 3) / (ε0 * (p0 - ε0)) ≤
            (1 + ε0) ^ u := by
          calc ((u : ℝ) + (gnnwMFun u : ℝ)) ^ (gnnwMFun u) * ((u : ℝ) ^ 3) / (ε0 * (p0 - ε0))
              = Real.exp (Real.log (((u : ℝ) + (gnnwMFun u : ℝ)) ^ (gnnwMFun u) * ((u : ℝ) ^ 3) /
                  (ε0 * (p0 - ε0)))) := (Real.exp_log hpos_lhs).symm
            _ ≤ Real.exp ((u : ℝ) * Real.log (1 + ε0)) := Real.exp_le_exp.mpr hlog_lhs
            _ = (1 + ε0) ^ u := by
                rw [mul_comm, ← Real.rpow_def_of_pos (by linarith : (0 : ℝ) < 1 + ε0), Real.rpow_natCast]
        exact le_trans hle_pow (by nlinarith)
    · push Not at huU0
      have hmem : u ∈ Finset.range U0 := Finset.mem_range.mpr huU0
      have hle_sum : 5 * ((gnnwMFun u : ℝ) ^ 2) +
          ((u : ℝ) + (gnnwMFun u : ℝ)) ^ (gnnwMFun u) * ((u : ℝ) ^ 3) / (ε0 * (p0 - ε0)) ≤ M3 := by
        refine le_trans (Finset.single_le_sum (f := fun j : ℕ =>
          5 * ((gnnwMFun j : ℝ) ^ 2) +
            ((j : ℝ) + (gnnwMFun j : ℝ)) ^ (gnnwMFun j) * ((j : ℝ) ^ 3) / (ε0 * (p0 - ε0)))
          (fun j _ => by
            have : 0 < ε0 * (p0 - ε0) := by norm_num [ε0, p0]
            positivity) hmem) (le_max_right _ _)
      have h1pow : (1 : ℝ) ≤ (1 + ε0) ^ u := one_le_pow₀ h1ε.le
      have hM3_le : M3 ≤ M3 * (1 + ε0) ^ u := by nlinarith
      have hnn1 : 0 ≤ 5 * ((gnnwMFun u : ℝ) ^ 2) := by positivity
      have hnn2 : 0 ≤ ((u : ℝ) + (gnnwMFun u : ℝ)) ^ (gnnwMFun u) * ((u : ℝ) ^ 3) / (ε0 * (p0 - ε0)) := by
        have : 0 < ε0 * (p0 - ε0) := by norm_num [ε0, p0]
        positivity
      exact ⟨le_trans (le_add_of_nonneg_right hnn2) (le_trans hle_sum hM3_le),
        le_trans (le_add_of_nonneg_left hnn1) (le_trans hle_sum hM3_le)⟩
  rcases hblue with ⟨M3, hM3_pos, hM3⟩
  -- Pick `L₀`!
  let thresh : ℝ := max (M_r / ε0 ^ 64) (max (M_2 / ε0 ^ 2) M3)
  have htend_exp : Tendsto (fun l : ℕ => (1 + ε0) ^ l) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt h1ε
  rcases Filter.eventually_atTop.mp (htend_exp.eventually_ge_atTop thresh) with ⟨L2, hL2⟩
  refine ⟨max 2 (max L1 L2), le_max_left _ _, fun k l t hk hl ht => ?_⟩
  have hl1 : 1 ≤ l := by omega
  have hlL1 : L1 ≤ l := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hl
  have hlL2 : L2 ≤ l := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hl
  have h1ε_l : thresh ≤ (1 + ε0) ^ l := hL2 l hlL2
  have hpow_split : (1 + ε0) ^ (k + l + t) = (1 + ε0) ^ l * (1 + ε0) ^ (k + t) := by
    rw [← pow_add]; congr 1; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) Base Ramsey bound
    have h1 := hbase_all k l hk hl1
    have hL1' := (hL1 (k + l) (by omega)).le
    rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (pow_pos (by linarith : 0 < cA) (k + l))] at hL1'
    have hcx : cA * (200715 / 1000000 : ℝ)⁻¹ ≤ x1⁻¹ := by
      have hle : cA ≤ (200715 / 1000000 : ℝ) / x1 := min_le_left _ _
      rw [← div_eq_mul_inv, div_le_iff₀ (by norm_num), mul_comm, ← div_eq_mul_inv]
      exact hle
    have hcy : cA * y_base⁻¹ ≤ y1⁻¹ := by
      have hle : cA ≤ y_base / y1 := min_le_right _ _
      have hy1p : 0 < y1 := by norm_num [y1]
      have hybp : 0 < y_base := lt_trans hy1p hy_base_gt
      rw [← div_eq_mul_inv, div_le_iff₀ hybp, mul_comm, ← div_eq_mul_inv]
      exact hle
    have hpow_xy : cA ^ (k + l) * ((200715 / 1000000 : ℝ)⁻¹ ^ k * y_base⁻¹ ^ l) ≤
        x1⁻¹ ^ k * y1⁻¹ ^ l := by
      rw [pow_add]
      have hx_p := pow_le_pow_left₀ (by positivity) hcx k
      have hy_p := pow_le_pow_left₀ (by positivity) hcy l
      rw [mul_pow] at hx_p hy_p
      have hprod := mul_le_mul hx_p hy_p (by positivity) (by positivity)
      linarith
    calc (R2 k l : ℝ) ≤ (4 * ((k + l : ℕ) : ℝ)) * ((200715 / 1000000 : ℝ)⁻¹ ^ k * y_base⁻¹ ^ l) := by
          linarith
      _ ≤ cA ^ (k + l) * ((200715 / 1000000 : ℝ)⁻¹ ^ k * y_base⁻¹ ^ l) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ x1⁻¹ ^ k * y1⁻¹ ^ l := hpow_xy
  · -- (2) Initial moment bound
    have hMr_le : M_r / ε0 ^ 64 ≤ (1 + ε0) ^ l := le_trans (le_max_left _ _) h1ε_l
    have h1 := hMr (k + t)
    have h2 : ((k + t : ℕ) : ℝ) ^ 64 / ε0 ^ 64 ≤ (1 + ε0) ^ (k + l + t) := by
      rw [hpow_split]
      have h3 := mul_le_mul_of_nonneg_right hMr_le (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε0) (k + t))
      rw [div_le_iff₀ (pow_pos hε0 64)]
      rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hε0 64)] at h3
      linarith
    rw [div_pow, div_mul_eq_mul_div, one_le_div (by positivity)]
    rw [div_le_iff₀ (pow_pos hε0 64)] at h2
    dsimp [ε0] at h2
    linarith
  · -- (3) Error term bound
    have hM2_le : M_2 / ε0 ^ 2 ≤ (1 + ε0) ^ l :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h1ε_l
    have h1 := hM2 (k + t)
    rw [hpow_split]
    have h3 := mul_le_mul_of_nonneg_right hM2_le (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε0) (k + t))
    rw [div_le_iff₀ (pow_pos hε0 2)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hε0 2)] at h3
    linarith
  · -- (4) `5 m(k + t)^2 ≤ (1 + ε0)^(k + l + t)`
    have hM3_le : M3 ≤ (1 + ε0) ^ l := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h1ε_l
    rw [hpow_split]
    exact le_trans (hM3 (k + t) (by omega)).1
      (mul_le_mul_of_nonneg_right hM3_le (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε0) (k + t)))
  · -- (5) `R(k, m(k + t)) ≤ (ε0 (p0 - ε0) / (k + t)^3) * (1 + ε0)^(k + l + t)`
    set m := gnnwMFun (k + t)
    have hm1 : 1 ≤ m := le_max_left _ _
    have hR_ch : R2 k m ≤ (k + m - 2).choose (m - 1) := by
      rw [R2_symm]
      have := R2_erdos_szekeres hm1 hk
      simpa [Nat.add_comm] using this
    have hch_pow : ((k + m - 2).choose (m - 1) : ℝ) ≤ ((k + t : ℕ) + m : ℝ) ^ m := by
      have h1 : (k + m - 2).choose (m - 1) ≤ (k + t + m) ^ m := by
        calc (k + m - 2).choose (m - 1)
            ≤ (k + m - 2) ^ (m - 1) := by
              have := Nat.descFactorial_le_pow (k + m - 2) (m - 1)
              rw [Nat.descFactorial_eq_factorial_mul_choose] at this
              exact le_trans (Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)) this
          _ ≤ (k + t + m) ^ (m - 1) := Nat.pow_le_pow_left (by omega) _
          _ ≤ (k + t + m) ^ m := Nat.pow_le_pow_right (by omega) (Nat.sub_le m 1)
      exact_mod_cast h1
    have hM3_le : M3 ≤ (1 + ε0) ^ l := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h1ε_l
    have h2 := (hM3 (k + t) (by omega)).2
    have hεp_pos : 0 < ε0 * (p0 - ε0) := by norm_num [ε0, p0]
    have hu_pos : (0 : ℝ) < ((k + t : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hεp_pos] at h2
    have hstep : (((k + t : ℕ) : ℝ) + (m : ℝ)) ^ m ≤
        (ε0 * (p0 - ε0) / ((k + t : ℕ) : ℝ) ^ 3) * (M3 * (1 + ε0) ^ (k + t)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hu_pos 3)]
      linarith
    rw [hpow_split]
    exact le_trans (by exact_mod_cast hR_ch)
      (le_trans hch_pow (le_trans hstep
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hM3_le (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε0) (k + t)))
          (by positivity))))

/-- **Modular Part 2 of GNNW Lemma 12:** Minimal-subset degree regularization. -/
private lemma gnnw_lemma12_deg_reg {N r : ℕ} (G : SimpleGraph (Fin N)) (hr : 1 ≤ r)
    (p_th M_val : ℝ) (hM_pos : 0 < M_val) (X Y : Finset (Fin N))
    (hYne : Y.Nonempty) (hdens : p_th ≤ dens G X Y)
    (hmom : M_val ≤ (dens G X Y - p_th) ^ r * (X.card : ℝ) * (Y.card : ℝ)) :
    open Classical in
    ∃ A ⊆ X, A.Nonempty ∧ p_th ≤ dens G A Y ∧
      M_val ≤ (dens G A Y - p_th) ^ r * (A.card : ℝ) * (Y.card : ℝ) ∧
      ∀ v ∈ A, p_th * (Y.card : ℝ) ≤ ((Y.filter (fun y => G.Adj v y)).card : ℝ) := by
  classical
  have hXne : X.Nonempty := by
    by_contra hXe
    rw [Finset.not_nonempty_iff_eq_empty] at hXe
    subst hXe; simp at hmom; linarith
  let validSub : Finset (Finset (Fin N)) :=
    X.powerset.filter (fun A =>
      A.Nonempty ∧ p_th ≤ dens G A Y ∧
      M_val ≤ (dens G A Y - p_th) ^ r * (A.card : ℝ) * (Y.card : ℝ))
  have hX_in : X ∈ validSub :=
    mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), hXne, hdens, hmom⟩
  obtain ⟨A, hA_mem, hA_min⟩ := Finset.exists_min_image validSub Finset.card ⟨X, hX_in⟩
  rcases mem_filter.mp hA_mem with ⟨hA_sub', hAne, hAdens, hAmom⟩
  have hA_sub : A ⊆ X := Finset.mem_powerset.mp hA_sub'
  refine ⟨A, hA_sub, hAne, hAdens, hAmom, fun v hvA => ?_⟩
  by_contra hlt
  push Not at hlt
  let A' := A.erase v
  have hA'ne : A'.Nonempty := by
    by_contra hA'e
    rw [Finset.not_nonempty_iff_eq_empty] at hA'e
    have hAsing : A = {v} := by
      ext u; simp only [mem_singleton]
      constructor
      · intro huA; by_contra huv
        have : u ∈ A' := Finset.mem_erase.mpr ⟨huv, huA⟩
        rw [hA'e] at this; exact Finset.notMem_empty u this
      · rintro rfl; exact hvA
    have hd_eq : dens G A Y = ((Y.filter (fun y => G.Adj v y)).card : ℝ) / (Y.card : ℝ) := by
      unfold dens
      rw [if_neg (by push Not; exact ⟨ne_of_gt hAne.card_pos, ne_of_gt hYne.card_pos⟩),
        hAsing, eR_singleton_left]
      simp
    rw [hd_eq, le_div_iff₀ (Nat.cast_pos.mpr hYne.card_pos)] at hAdens
    linarith
  have hA'sub : A' ⊆ X := Finset.Subset.trans (Finset.erase_subset v A) hA_sub
  have hA'card_pos : (0 : ℝ) < (A'.card : ℝ) := Nat.cast_pos.mpr hA'ne.card_pos
  have hYcard_pos : (0 : ℝ) < (Y.card : ℝ) := Nat.cast_pos.mpr hYne.card_pos
  have hAcard_lt : (A'.card : ℝ) < (A.card : ℝ) := by exact_mod_cast Finset.card_erase_lt_of_mem hvA
  have hdisj_vA' : Disjoint ({v} : Finset (Fin N)) A' :=
    Finset.disjoint_singleton_left.mpr (Finset.notMem_erase v A)
  have hfp_inc : fp G p_th A Y < fp G p_th A' Y := by
    have hEq : fp G p_th A Y = fp G p_th {v} Y + fp G p_th A' Y := by
      have : A = {v} ∪ A' := by rw [Finset.singleton_union]; exact (Finset.insert_erase hvA).symm
      rw [this, fp_union_left _ _ hdisj_vA']
    have hv_neg : fp G p_th {v} Y < 0 := by
      unfold fp; rw [eR_singleton_left]; simp only [Finset.card_singleton, Nat.cast_one, mul_one]; linarith
    linarith
  have hfp_A_eq : fp G p_th A Y = (dens G A Y - p_th) * (A.card : ℝ) * (Y.card : ℝ) := by
    unfold fp; rw [eR_eq_dens_mul]; ring
  have hfp_A'_eq : fp G p_th A' Y = (dens G A' Y - p_th) * (A'.card : ℝ) * (Y.card : ℝ) := by
    unfold fp; rw [eR_eq_dens_mul]; ring
  have hfp_A_nn : 0 ≤ fp G p_th A Y := by
    rw [hfp_A_eq]; exact mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hYcard_pos.le
  have hfp_A'_pos : 0 < fp G p_th A' Y := lt_of_le_of_lt hfp_A_nn hfp_inc
  have hA'dens : p_th ≤ dens G A' Y := by
    rw [hfp_A'_eq] at hfp_A'_pos
    have : 0 < dens G A' Y - p_th := by nlinarith [mul_pos hA'card_pos hYcard_pos]
    linarith
  have hd_inc : dens G A Y - p_th ≤ dens G A' Y - p_th := by
    have h1 : (dens G A Y - p_th) * (A'.card : ℝ) * (Y.card : ℝ) ≤
        (dens G A Y - p_th) * (A.card : ℝ) * (Y.card : ℝ) := by nlinarith [hYcard_pos]
    have h2 : (dens G A Y - p_th) * (A'.card : ℝ) * (Y.card : ℝ) ≤
        (dens G A' Y - p_th) * (A'.card : ℝ) * (Y.card : ℝ) := by linarith [hfp_A_eq, hfp_A'_eq, hfp_inc]
    nlinarith [mul_pos hA'card_pos hYcard_pos]
  have hA'mom : M_val ≤ (dens G A' Y - p_th) ^ r * (A'.card : ℝ) * (Y.card : ℝ) := by
    have hr1 : r = (r - 1) + 1 := by omega
    have hLHS : (dens G A Y - p_th) ^ r * (A.card : ℝ) * (Y.card : ℝ) =
        (dens G A Y - p_th) ^ (r - 1) * fp G p_th A Y := by
      rw [hfp_A_eq]; conv_lhs => rw [hr1, pow_succ]
      ring
    have hRHS : (dens G A' Y - p_th) ^ r * (A'.card : ℝ) * (Y.card : ℝ) =
        (dens G A' Y - p_th) ^ (r - 1) * fp G p_th A' Y := by
      rw [hfp_A'_eq]; conv_lhs => rw [hr1, pow_succ]
      ring
    rw [hLHS] at hAmom
    rw [hRHS]
    exact le_trans hAmom (mul_le_mul (pow_le_pow_left₀ (by linarith) hd_inc (r - 1))
      hfp_inc.le hfp_A_nn (pow_nonneg (by linarith) (r - 1)))
  have hA'_in : A' ∈ validSub :=
    mem_filter.mpr ⟨Finset.mem_powerset.mpr hA'sub, hA'ne, hA'dens, hA'mom⟩
  have hle := hA_min A' hA'_in
  have hlt_c := Finset.card_erase_lt_of_mem hvA
  exact not_lt_of_ge hle hlt_c

/-- **Modular Part 3 of GNNW Lemma 12:** Algebraic contradiction when neither the Red step nor
the Blue step fires at `r = 64, p0 = 1/2, ε0 = 1/200000, x = 200705/1000000, μ = 381005/1000000`. -/
private lemma gnnw_lemma12_red_blue_contra
    {α αR αB aR aB aTot : ℝ}
    (hα : 0 < α) (haTot : 0 < aTot) (haR : 0 ≤ aR) (haB : 0 ≤ aB)
    (hsum : aR + aB ≤ aTot)
    (hAB_le : aB ≤ (381005 / 1000000 + 1 / 200000 : ℝ) * aTot)
    (herr : 1 / (α * aTot) ≤ 1 / 200000)
    (heq24 : 1 ≤ αR / α * (aR / aTot) + αB / α * (aB / aTot) + 1 / (α * aTot))
    (hnotR : ¬(0 ≤ αR ∧ (200705 / 1000000 : ℝ) * α ^ 64 * aTot / (1 / 2 - 1 / 200000 : ℝ) ≤ αR ^ 64 * aR))
    (hnotB : ¬(0 ≤ αB ∧ (381005 / 1000000 : ℝ) * α ^ 64 * aTot / (1 / 2 - 1 / 200000 : ℝ) ≤ αB ^ 64 * aB)) :
    False := by
  let r : ℕ := 64
  let p0 : ℝ := 1 / 2
  let ε0 : ℝ := 1 / 200000
  let x : ℝ := 200705 / 1000000
  let μ : ℝ := 381005 / 1000000
  let s0 : ℝ := 989227 / 1000000
  have hpe_pos : 0 < p0 - ε0 := by norm_num [p0, ε0]
  have hpe_r_pos : 0 < (p0 - ε0) ^ ((1 : ℝ) / (r : ℝ)) := Real.rpow_pos_of_pos hpe_pos _
  have hroot_bound : ∀ (αc c_val ac : ℝ), 0 < c_val → 0 ≤ ac →
      ¬(0 ≤ αc ∧ c_val * α ^ r * aTot / (p0 - ε0) ≤ αc ^ r * ac) →
      αc / α * (ac / aTot) ≤
        c_val ^ ((1 : ℝ) / (r : ℝ)) * (p0 - ε0) ^ (-(1 : ℝ) / (r : ℝ)) *
          (ac / aTot) ^ (1 - (1 : ℝ) / (r : ℝ)) := by
    intro αc c_val ac hc_pos hac_nn hnot
    by_cases hαc_nn : 0 ≤ αc
    · have hlt : αc ^ r * ac < c_val * α ^ r * aTot / (p0 - ε0) := by
        by_contra hge; push Not at hge; exact hnot ⟨hαc_nn, hge⟩
      rcases eq_or_lt_of_le hac_nn with rfl | hac_pos
      · rw [zero_div, mul_zero]
        exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hc_pos.le _)
          (Real.rpow_nonneg hpe_pos.le _)) (Real.rpow_nonneg le_rfl _)
      · have hratio_lt : (αc / α) ^ r < c_val / (p0 - ε0) * (aTot / ac) := by
          rw [div_pow, div_lt_iff₀ (pow_pos hα r)]
          have h1 : αc ^ r < c_val * α ^ r * aTot / (p0 - ε0) / ac := by
            rw [lt_div_iff₀ hac_pos]; exact hlt
          have h2 : c_val * α ^ r * aTot / (p0 - ε0) / ac =
              c_val / (p0 - ε0) * (aTot / ac) * α ^ r := by ring
          linarith
        have hrpow := Real.rpow_le_rpow (pow_nonneg (div_nonneg hαc_nn hα.le) r)
          hratio_lt.le (by norm_num [r] : (0 : ℝ) ≤ (1 : ℝ) / (r : ℝ))
        have hLHS_r : ((αc / α) ^ r) ^ ((1 : ℝ) / (r : ℝ)) = αc / α := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hαc_nn hα.le)]
          have : (r : ℝ) * ((1 : ℝ) / (r : ℝ)) = 1 := by norm_num [r]
          rw [this, Real.rpow_one]
        rw [hLHS_r] at hrpow
        have hRHS_r : (c_val / (p0 - ε0) * (aTot / ac)) ^ ((1 : ℝ) / (r : ℝ)) =
            c_val ^ ((1 : ℝ) / (r : ℝ)) * (p0 - ε0) ^ (-(1 : ℝ) / (r : ℝ)) *
              (ac / aTot) ^ (-(1 : ℝ) / (r : ℝ)) := by
          rw [Real.mul_rpow (div_nonneg hc_pos.le hpe_pos.le) (div_nonneg haTot.le hac_pos.le),
            Real.div_rpow hc_pos.le hpe_pos.le,
            div_eq_mul_inv (c_val ^ _), ← Real.rpow_neg hpe_pos.le,
            show aTot / ac = (ac / aTot)⁻¹ by rw [inv_div],
            Real.inv_rpow (div_nonneg hac_pos.le haTot.le),
            ← Real.rpow_neg (div_nonneg hac_pos.le haTot.le), neg_div]
        rw [hRHS_r] at hrpow
        have hmul := mul_le_mul_of_nonneg_right hrpow (div_nonneg hac_pos.le haTot.le)
        have hmerge : (ac / aTot) ^ (-(1 : ℝ) / (r : ℝ)) * (ac / aTot) =
            (ac / aTot) ^ (1 - (1 : ℝ) / (r : ℝ)) := by
          conv_lhs => arg 2; rw [← Real.rpow_one (ac / aTot)]
          rw [← Real.rpow_add (div_pos hac_pos haTot)]
          congr 1; ring
        calc αc / α * (ac / aTot)
            ≤ c_val ^ ((1 : ℝ) / (r : ℝ)) * (p0 - ε0) ^ (-(1 : ℝ) / (r : ℝ)) *
                (ac / aTot) ^ (-(1 : ℝ) / (r : ℝ)) * (ac / aTot) := hmul
          _ = c_val ^ ((1 : ℝ) / (r : ℝ)) * (p0 - ε0) ^ (-(1 : ℝ) / (r : ℝ)) *
                (ac / aTot) ^ (1 - (1 : ℝ) / (r : ℝ)) := by rw [mul_assoc, hmerge]
    · push Not at hαc_nn
      exact le_trans (mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hαc_nn.le hα.le)
        (div_nonneg hac_nn haTot.le)) (mul_nonneg (mul_nonneg (Real.rpow_nonneg hc_pos.le _)
          (Real.rpow_nonneg hpe_pos.le _)) (Real.rpow_nonneg (div_nonneg hac_nn haTot.le) _))
  have hR_bd := hroot_bound αR x aR (by norm_num [x]) haR hnotR
  have hB_bd := hroot_bound αB μ aB (by norm_num [μ]) haB hnotB
  have hpe_cancel : (p0 - ε0) ^ ((1 : ℝ) / (r : ℝ)) * (p0 - ε0) ^ (-(1 : ℝ) / (r : ℝ)) = 1 := by
    rw [← Real.rpow_add hpe_pos]
    have : (1 : ℝ) / (r : ℝ) + -(1 : ℝ) / (r : ℝ) = 0 := by ring
    rw [this, Real.rpow_zero]
  have heq25 : (p0 - ε0) ^ ((1 : ℝ) / (r : ℝ)) ≤
      x ^ ((1 : ℝ) / (r : ℝ)) * (aR / aTot) ^ (1 - (1 : ℝ) / (r : ℝ)) +
      μ ^ ((1 : ℝ) / (r : ℝ)) * (aB / aTot) ^ (1 - (1 : ℝ) / (r : ℝ)) +
      (p0 - ε0) ^ ((1 : ℝ) / (r : ℝ)) * (1 / (α * aTot)) := by
    have h1 : 1 ≤
        x ^ ((1 : ℝ) / (r : ℝ)) * (p0 - ε0) ^ (-(1 : ℝ) / (r : ℝ)) * (aR / aTot) ^ (1 - (1 : ℝ) / (r : ℝ)) +
        μ ^ ((1 : ℝ) / (r : ℝ)) * (p0 - ε0) ^ (-(1 : ℝ) / (r : ℝ)) * (aB / aTot) ^ (1 - (1 : ℝ) / (r : ℝ)) +
        1 / (α * aTot) := by linarith
    have hmul := mul_le_mul_of_nonneg_left h1 hpe_r_pos.le
    have hsimp : (p0 - ε0) ^ ((1 : ℝ) / (r : ℝ)) *
        (x ^ ((1 : ℝ) / (r : ℝ)) * (p0 - ε0) ^ (-(1 : ℝ) / (r : ℝ)) * (aR / aTot) ^ (1 - (1 : ℝ) / (r : ℝ)) +
        μ ^ ((1 : ℝ) / (r : ℝ)) * (p0 - ε0) ^ (-(1 : ℝ) / (r : ℝ)) * (aB / aTot) ^ (1 - (1 : ℝ) / (r : ℝ)) +
        1 / (α * aTot)) =
        x ^ ((1 : ℝ) / (r : ℝ)) * (aR / aTot) ^ (1 - (1 : ℝ) / (r : ℝ)) +
        μ ^ ((1 : ℝ) / (r : ℝ)) * (aB / aTot) ^ (1 - (1 : ℝ) / (r : ℝ)) +
        (p0 - ε0) ^ ((1 : ℝ) / (r : ℝ)) * (1 / (α * aTot)) := by
      calc _ = (p0 - ε0) ^ ((1 : ℝ) / (r : ℝ)) * (p0 - ε0) ^ (-(1 : ℝ) / (r : ℝ)) *
              (x ^ ((1 : ℝ) / (r : ℝ)) * (aR / aTot) ^ (1 - (1 : ℝ) / (r : ℝ))) +
            (p0 - ε0) ^ ((1 : ℝ) / (r : ℝ)) * (p0 - ε0) ^ (-(1 : ℝ) / (r : ℝ)) *
              (μ ^ ((1 : ℝ) / (r : ℝ)) * (aB / aTot) ^ (1 - (1 : ℝ) / (r : ℝ))) +
            (p0 - ε0) ^ ((1 : ℝ) / (r : ℝ)) * (1 / (α * aTot)) := by ring
        _ = _ := by rw [hpe_cancel, one_mul, one_mul]
    linarith
  set lam : ℝ := aB / aTot
  have hlam_nn : 0 ≤ lam := div_nonneg haB haTot.le
  have hlam_le : lam ≤ μ + ε0 := by dsimp [lam]; rw [div_le_iff₀ haTot]; exact hAB_le
  have hAR_le_1lam : aR / aTot ≤ 1 - lam := by
    dsimp [lam]; rw [le_sub_iff_add_le, ← add_div, div_le_one haTot]; exact hsum
  have hmono1 := rpow_concave_mono (r := r) (x := x) (μ := μ) (l := lam) (l0 := μ + ε0)
    (by norm_num [r] : 2 ≤ r) (by norm_num [x]) (by norm_num [μ]) (by norm_num [μ, ε0])
    (by norm_num [μ, ε0]) hlam_nn hlam_le (by norm_num [μ, x, ε0])
  have hAR_rpow : (aR / aTot) ^ (1 - (1 : ℝ) / (r : ℝ)) ≤ (1 - lam) ^ (1 - (1 : ℝ) / (r : ℝ)) :=
    Real.rpow_le_rpow (div_nonneg haR haTot.le) hAR_le_1lam (by norm_num [r])
  have h1m_rpow : (1 - (μ + ε0)) ^ (1 - (1 : ℝ) / (r : ℝ)) ≤ (1 - μ) ^ (1 - (1 : ℝ) / (r : ℝ)) :=
    Real.rpow_le_rpow (by norm_num [μ, ε0]) (by norm_num [ε0]) (by norm_num [r])
  have hμ_rpow : μ ^ ((1 : ℝ) / (r : ℝ)) * (μ + ε0) ^ (1 - (1 : ℝ) / (r : ℝ)) ≤ μ + ε0 := by
    have h1 : μ ^ ((1 : ℝ) / (r : ℝ)) ≤ (μ + ε0) ^ ((1 : ℝ) / (r : ℝ)) :=
      Real.rpow_le_rpow (by norm_num [μ]) (by norm_num [ε0]) (by norm_num [r])
    have h2 : (μ + ε0) ^ ((1 : ℝ) / (r : ℝ)) * (μ + ε0) ^ (1 - (1 : ℝ) / (r : ℝ)) = μ + ε0 := by
      rw [← Real.rpow_add (by norm_num [μ, ε0])]; norm_num
    calc μ ^ ((1 : ℝ) / (r : ℝ)) * (μ + ε0) ^ (1 - (1 : ℝ) / (r : ℝ))
        ≤ (μ + ε0) ^ ((1 : ℝ) / (r : ℝ)) * (μ + ε0) ^ (1 - (1 : ℝ) / (r : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by norm_num [μ, ε0]) _)
      _ = μ + ε0 := h2
  have hpe_le1 : (p0 - ε0) ^ ((1 : ℝ) / (r : ℝ)) ≤ 1 :=
    Real.rpow_le_one hpe_pos.le (by norm_num [p0, ε0]) (by norm_num [r])
  have herr2 : (p0 - ε0) ^ ((1 : ℝ) / (r : ℝ)) * (1 / (α * aTot)) ≤ ε0 := by
    have h1 : 0 ≤ 1 / (α * aTot) := by positivity
    nlinarith
  have hfinal_ineq : (p0 - ε0) ^ ((1 : ℝ) / (r : ℝ)) ≤
      x ^ ((1 : ℝ) / (r : ℝ)) * (1 - μ) ^ (1 - (1 : ℝ) / (r : ℝ)) + μ + 2 * ε0 := by
    have h1 : x ^ ((1 : ℝ) / (r : ℝ)) * (aR / aTot) ^ (1 - (1 : ℝ) / (r : ℝ)) ≤
        x ^ ((1 : ℝ) / (r : ℝ)) * (1 - lam) ^ (1 - (1 : ℝ) / (r : ℝ)) :=
      mul_le_mul_of_nonneg_left hAR_rpow (Real.rpow_nonneg (by norm_num [x]) _)
    have h2 : x ^ ((1 : ℝ) / (r : ℝ)) * (1 - (μ + ε0)) ^ (1 - (1 : ℝ) / (r : ℝ)) ≤
        x ^ ((1 : ℝ) / (r : ℝ)) * (1 - μ) ^ (1 - (1 : ℝ) / (r : ℝ)) :=
      mul_le_mul_of_nonneg_left h1m_rpow (Real.rpow_nonneg (by norm_num [x]) _)
    linarith
  -- Fast 6-step repeated-squaring certificate for `s0 ^ 64 ≤ p0 - ε0` (instantaneous!).
  have hs0_pow : s0 ^ r ≤ p0 - ε0 := by
    have h1 : s0 ^ 2 ≤ 9785701 / 10000000 := by norm_num [s0]
    have h2 : (s0 ^ 2) ^ 2 ≤ 1915199 / 2000000 :=
      le_trans (pow_le_pow_left₀ (sq_nonneg _) h1 2) (by norm_num)
    have h3 : ((s0 ^ 2) ^ 2) ^ 2 ≤ 9169969 / 10000000 :=
      le_trans (pow_le_pow_left₀ (sq_nonneg _) h2 2) (by norm_num)
    have h4 : (((s0 ^ 2) ^ 2) ^ 2) ^ 2 ≤ 4204417 / 5000000 :=
      le_trans (pow_le_pow_left₀ (sq_nonneg _) h3 2) (by norm_num)
    have h5 : ((((s0 ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 ≤ 7070849 / 10000000 :=
      le_trans (pow_le_pow_left₀ (sq_nonneg _) h4 2) (by norm_num)
    have h6 : (((((s0 ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 ≤ 4999691 / 10000000 :=
      le_trans (pow_le_pow_left₀ (sq_nonneg _) h5 2) (by norm_num)
    have hpow64 : ∀ z : ℝ, z ^ r = (((((z ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := by
      intro z; dsimp [r]; ring
    rw [hpow64 s0]
    exact le_trans h6 (by norm_num [p0, ε0])
  have hs0_le : s0 ≤ (p0 - ε0) ^ ((1 : ℝ) / (r : ℝ)) := by
    have h1 := Real.rpow_le_rpow (pow_nonneg (by norm_num [s0] : (0 : ℝ) ≤ s0) r) hs0_pow
      (by norm_num [r] : (0 : ℝ) ≤ (1 : ℝ) / (r : ℝ))
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num [s0])] at h1
    have : (r : ℝ) * ((1 : ℝ) / (r : ℝ)) = 1 := by norm_num [r]
    rwa [this, Real.rpow_one] at h1
  -- Fast 6-step repeated-squaring certificate for `x * (1 - μ) ^ 63 < (s0 - μ - 2 ε0) ^ 64`!
  have hcert_lt : x * (1 - μ) ^ (r - 1) < (s0 - μ - 2 * ε0) ^ r := by
    let t : ℝ := (s0 - μ - 2 * ε0) / (1 - μ)
    have ht0 : 4912899 / 5000000 ≤ t := by norm_num [t, s0, μ, ε0]
    have ht1 : 965463 / 1000000 ≤ t ^ 2 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) ht0 2)
    have ht2 : 2330297 / 2500000 ≤ (t ^ 2) ^ 2 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) ht1 2)
    have ht3 : 4344227 / 5000000 ≤ ((t ^ 2) ^ 2) ^ 2 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) ht2 2)
    have ht4 : 7548923 / 10000000 ≤ (((t ^ 2) ^ 2) ^ 2) ^ 2 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) ht3 2)
    have ht5 : 5698623 / 10000000 ≤ ((((t ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) ht4 2)
    have ht6 : 324743 / 1000000 ≤ (((((t ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) ht5 2)
    have hpow64 : ∀ z : ℝ, z ^ r = (((((z ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := by
      intro z; dsimp [r]; ring
    have hlt_t : x / (1 - μ) < t ^ r := by
      rw [hpow64 t]
      exact lt_of_lt_of_le (by norm_num [x, μ]) ht6
    have h1m_pos : 0 < 1 - μ := by norm_num [μ]
    have hmul := mul_lt_mul_of_pos_right hlt_t (pow_pos h1m_pos r)
    have hLHS : x / (1 - μ) * (1 - μ) ^ r = x * (1 - μ) ^ (r - 1) := by
      have hr1 : r = (r - 1) + 1 := by norm_num [r]
      conv_lhs => rw [hr1, pow_succ]
      field_simp [ne_of_gt h1m_pos]
    have hRHS : t ^ r * (1 - μ) ^ r = (s0 - μ - 2 * ε0) ^ r := by
      dsimp [t]; rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero r (ne_of_gt h1m_pos))]
    rwa [hLHS, hRHS] at hmul
  have hcert_rpow : x ^ ((1 : ℝ) / (r : ℝ)) * (1 - μ) ^ (1 - (1 : ℝ) / (r : ℝ)) < s0 - μ - 2 * ε0 := by
    have h1 := Real.rpow_lt_rpow (mul_nonneg (by norm_num [x] : (0 : ℝ) ≤ x) (pow_nonneg (by norm_num [μ] : (0 : ℝ) ≤ 1 - μ) (r - 1))) hcert_lt
      (by norm_num [r] : (0 : ℝ) < (1 : ℝ) / (r : ℝ))
    have hLHS_eq : (x * (1 - μ) ^ (r - 1)) ^ ((1 : ℝ) / (r : ℝ)) =
        x ^ ((1 : ℝ) / (r : ℝ)) * (1 - μ) ^ (1 - (1 : ℝ) / (r : ℝ)) := by
      rw [Real.mul_rpow (by norm_num [x] : (0 : ℝ) ≤ x) (pow_nonneg (by norm_num [μ] : (0 : ℝ) ≤ 1 - μ) (r - 1)),
        ← Real.rpow_natCast (1 - μ) (r - 1), ← Real.rpow_mul (by norm_num [μ])]
      congr 2; norm_num [r]
    have hRHS_eq : ((s0 - μ - 2 * ε0) ^ r) ^ ((1 : ℝ) / (r : ℝ)) = s0 - μ - 2 * ε0 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num [s0, μ, ε0])]
      have : (r : ℝ) * ((1 : ℝ) / (r : ℝ)) = 1 := by norm_num [r]
      rw [this, Real.rpow_one]
    rwa [hLHS_eq, hRHS_eq] at h1
  linarith

/-- **Modular Part 4 of GNNW Lemma 12:** Main strong induction on `s = k' + t'`. -/
private lemma gnnw_lemma12_main_ind {L₀ N l r : ℕ} (hL₀2 : 2 ≤ L₀)
    (hparams : ∀ k l t : ℕ, 1 ≤ k → L₀ ≤ l → 1 ≤ t →
      ((R2 k l : ℝ) ≤ (20071 / 100000 : ℝ)⁻¹ ^ k * (82161 / 100000 : ℝ)⁻¹ ^ l) ∧
      (1 ≤ ((1 / 200000 : ℝ) / ((k + t : ℕ) : ℝ)) ^ 64 * (1 + 1 / 200000 : ℝ) ^ (k + l + t)) ∧
      (((k + t : ℕ) : ℝ) ^ 2 / ((1 / 200000 : ℝ) ^ 2) ≤ (1 + 1 / 200000 : ℝ) ^ (k + l + t)) ∧
      (5 * ((gnnwMFun (k + t) : ℝ) ^ 2) ≤ (1 + 1 / 200000 : ℝ) ^ (k + l + t)) ∧
      ((R2 k (gnnwMFun (k + t)) : ℝ) ≤
        ((1 / 200000 : ℝ) * (1 / 2 - 1 / 200000 : ℝ) / ((k + t : ℕ) : ℝ) ^ 3) *
          (1 + 1 / 200000 : ℝ) ^ (k + l + t)))
    (G : SimpleGraph (Fin N)) (hl : L₀ ≤ l) (hr : r = 64) :
    ∀ s k' t' : ℕ, 1 ≤ k' → 1 ≤ t' → k' + t' = s →
      ∀ X' Y' : Finset (Fin N), Disjoint X' Y' →
        (1 / 2 : ℝ) - (1 / 200000 : ℝ) / ((k' + t' : ℕ) : ℝ) ≤ dens G X' Y' →
        (200705 / 1000000 : ℝ)⁻¹ ^ k' * (821605 / 1000000 : ℝ)⁻¹ ^ l *
            (381005 / 1000000 : ℝ)⁻¹ ^ t' ≤
          (dens G X' Y' + (1 / 200000 : ℝ) / ((k' + t' : ℕ) : ℝ) - 1 / 2) ^ r *
            (X'.card : ℝ) * (Y'.card : ℝ) →
        IsGood G k' l t' X' Y' := by
  have hl1 : 1 ≤ l := by omega
  let δ : ℕ → ℝ := fun u => (1 / 200000 : ℝ) / (u : ℝ)
  have hr1_pos : 1 ≤ r := by omega
  suffices hmain : ∀ s k' t' : ℕ, 1 ≤ k' → 1 ≤ t' → k' + t' = s →
      ∀ X' Y' : Finset (Fin N), Disjoint X' Y' →
        (1 / 2 : ℝ) - δ (k' + t') ≤ dens G X' Y' →
        (200705 / 1000000 : ℝ)⁻¹ ^ k' * (821605 / 1000000 : ℝ)⁻¹ ^ l *
            (381005 / 1000000 : ℝ)⁻¹ ^ t' ≤
          (dens G X' Y' + δ (k' + t') - 1 / 2) ^ r * (X'.card : ℝ) * (Y'.card : ℝ) →
        IsGood G k' l t' X' Y' from hmain
  classical
  intro s
  induction s using Nat.strong_induction_on with
    | h s ih =>
      intro k' t' hk' ht' hsum X' Y' hdisj' hdens' hmom'
      have hM_pos : 0 < (200705 / 1000000 : ℝ)⁻¹ ^ k' * (821605 / 1000000 : ℝ)⁻¹ ^ l *
          (381005 / 1000000 : ℝ)⁻¹ ^ t' := by positivity
      have hX'ne : X'.Nonempty := by
        by_contra hXe; rw [Finset.not_nonempty_iff_eq_empty] at hXe
        subst hXe; simp at hmom'; linarith
      have hY'ne : Y'.Nonempty := by
        by_contra hYe; rw [Finset.not_nonempty_iff_eq_empty] at hYe
        subst hYe; simp at hmom'; linarith
      rcases Nat.eq_or_lt_of_le hk' with rfl | hk'2
      · exact isGood_of_k_one hX'ne
      rcases Nat.eq_or_lt_of_le ht' with rfl | ht'2
      · exact isGood_of_t_one hX'ne
      -- Step 1: Degree Regularization via `gnnw_lemma12_deg_reg`!
      have hmom_reg : (200705 / 1000000 : ℝ)⁻¹ ^ k' * (821605 / 1000000 : ℝ)⁻¹ ^ l *
          (381005 / 1000000 : ℝ)⁻¹ ^ t' ≤
          (dens G X' Y' - (1 / 2 - δ (k' + t'))) ^ r * (X'.card : ℝ) * (Y'.card : ℝ) := by
        have : dens G X' Y' - (1 / 2 - δ (k' + t')) = dens G X' Y' + δ (k' + t') - 1 / 2 := by ring
        rwa [this]
      obtain ⟨A, hA_sub, hAne, hAdens, hAmom', hA_deg⟩ :=
        gnnw_lemma12_deg_reg G hr1_pos (1 / 2 - δ (k' + t')) _ hM_pos X' Y' hY'ne hdens' hmom_reg
      have hAmom : (200705 / 1000000 : ℝ)⁻¹ ^ k' * (821605 / 1000000 : ℝ)⁻¹ ^ l *
          (381005 / 1000000 : ℝ)⁻¹ ^ t' ≤
          (dens G A Y' + δ (k' + t') - 1 / 2) ^ r * (A.card : ℝ) * (Y'.card : ℝ) := by
        have : dens G A Y' - (1 / 2 - δ (k' + t')) = dens G A Y' + δ (k' + t') - 1 / 2 := by ring
        rwa [← this]
      suffices hAgood : IsGood G k' l t' A Y' from isGood_mono hA_sub (Finset.Subset.refl Y') hAgood
      have hdisjA : Disjoint A Y' := Disjoint.mono_left hA_sub hdisj'
      have hA_sub_dens : ∀ T ⊆ A, T.Nonempty → 1 / 2 - δ (k' + t') ≤ dens G T Y' := by
        intro T hTA hTne
        have heT : (1 / 2 - δ (k' + t')) * (T.card : ℝ) * (Y'.card : ℝ) ≤ eR G T Y' := by
          have : eR G T Y' = ∑ v ∈ T, ((Y'.filter (fun y => G.Adj v y)).card : ℝ) := by
            unfold eR; push_cast; rfl
          rw [this]
          calc (1 / 2 - δ (k' + t')) * (T.card : ℝ) * (Y'.card : ℝ)
              = ∑ _v ∈ T, (1 / 2 - δ (k' + t')) * (Y'.card : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul]; ring
            _ ≤ ∑ v ∈ T, ((Y'.filter (fun y => G.Adj v y)).card : ℝ) :=
                Finset.sum_le_sum (fun v hv => hA_deg v (hTA hv))
        unfold dens
        rw [if_neg (by push Not; exact ⟨ne_of_gt hTne.card_pos, ne_of_gt hY'ne.card_pos⟩)]
        rw [le_div_iff₀ (mul_pos (Nat.cast_pos.mpr hTne.card_pos) (Nat.cast_pos.mpr hY'ne.card_pos))]
        simpa [mul_assoc] using heT
      obtain ⟨hP_base, hP_un, hP_err, hP_m5, hP_Rkm⟩ := hparams k' l t' hk' hl ht'
      clear hP_un
      -- Step 2: Upper bound `|Y'|` (else `Y'` has red `K_{k'}` or blue `K_l`) & lower bound `|A|`!
      by_cases hY_big : (20071 / 100000 : ℝ)⁻¹ ^ k' * (82161 / 100000 : ℝ)⁻¹ ^ l ≤ (Y'.card : ℝ)
      · have hR_nat : R2 k' l ≤ Y'.card := by exact_mod_cast le_trans hP_base hY_big
        rcases exists_clique_in_subset (G := G) Y' (R2_spec hk' hl1) hR_nat with
          ⟨c, hc, hcl⟩ | ⟨c, hc, hcl⟩
        · exact Or.inl ⟨c, Finset.Subset.trans hc Finset.subset_union_right, hcl⟩
        · exact Or.inr (Or.inr ⟨c, hc, hcl⟩)
      · push Not at hY_big
        have hAY_ge : (200705 / 1000000 : ℝ)⁻¹ ^ k' * (821605 / 1000000 : ℝ)⁻¹ ^ l *
            (381005 / 1000000 : ℝ)⁻¹ ^ t' ≤ (A.card : ℝ) * (Y'.card : ℝ) := by
          have hd1 := dens_le_one G A Y'
          have hδ1 : δ (k' + t') ≤ 1 / 200000 :=
            div_le_self (by norm_num) (by exact_mod_cast (by omega : 1 ≤ k' + t'))
          have hpow1 : (dens G A Y' + δ (k' + t') - 1 / 2) ^ r ≤ 1 :=
            pow_le_one₀ (by linarith) (by linarith)
          nlinarith [show (0 : ℝ) ≤ (A.card : ℝ) * (Y'.card : ℝ) by positivity]
        have hA_big : (1 + 1 / 200000 : ℝ) ^ (k' + l + t') ≤ (A.card : ℝ) := by
          have hY_pos : (0 : ℝ) < (20071 / 100000 : ℝ)⁻¹ ^ k' * (82161 / 100000 : ℝ)⁻¹ ^ l := by positivity
          have hA_step : ((200705 / 1000000 : ℝ)⁻¹ ^ k' * (821605 / 1000000 : ℝ)⁻¹ ^ l *
              (381005 / 1000000 : ℝ)⁻¹ ^ t') /
              ((20071 / 100000 : ℝ)⁻¹ ^ k' * (82161 / 100000 : ℝ)⁻¹ ^ l) ≤ (A.card : ℝ) := by
            rw [div_le_iff₀ hY_pos]
            exact le_trans hAY_ge (mul_le_mul_of_nonneg_left hY_big.le (Nat.cast_nonneg _))
          have hrx : (1 + 1 / 200000 : ℝ) ≤ (200705 / 1000000 : ℝ)⁻¹ / (20071 / 100000 : ℝ)⁻¹ := by norm_num
          have hry : (1 + 1 / 200000 : ℝ) ≤ (821605 / 1000000 : ℝ)⁻¹ / (82161 / 100000 : ℝ)⁻¹ := by norm_num
          have hrμ : (1 + 1 / 200000 : ℝ) ≤ (381005 / 1000000 : ℝ)⁻¹ := by norm_num
          calc (1 + 1 / 200000 : ℝ) ^ (k' + l + t')
              = (1 + 1 / 200000 : ℝ) ^ k' * (1 + 1 / 200000 : ℝ) ^ l * (1 + 1 / 200000 : ℝ) ^ t' := by
                rw [pow_add, pow_add]
            _ ≤ ((200705 / 1000000 : ℝ)⁻¹ / (20071 / 100000 : ℝ)⁻¹) ^ k' *
                  ((821605 / 1000000 : ℝ)⁻¹ / (82161 / 100000 : ℝ)⁻¹) ^ l *
                  (381005 / 1000000 : ℝ)⁻¹ ^ t' :=
                mul_le_mul (mul_le_mul (pow_le_pow_left₀ (by norm_num) hrx k')
                  (pow_le_pow_left₀ (by norm_num) hry l) (by positivity) (by positivity))
                  (pow_le_pow_left₀ (by norm_num) hrμ t') (by positivity) (by positivity)
            _ = ((200705 / 1000000 : ℝ)⁻¹ ^ k' * (821605 / 1000000 : ℝ)⁻¹ ^ l *
                  (381005 / 1000000 : ℝ)⁻¹ ^ t') /
                  ((20071 / 100000 : ℝ)⁻¹ ^ k' * (82161 / 100000 : ℝ)⁻¹ ^ l) := by
                rw [div_pow, div_pow]; ring
            _ ≤ (A.card : ℝ) := hA_step
        -- Step 3: Big Blue Step via `gnnw_lemma9`!
        let u := k' + t'
        have hu2 : 2 ≤ u := by omega
        let b := gnnwBFun u
        let m := gnnwMFun u
        have hb1 : 1 ≤ b := le_max_left _ _
        have hm1 : 1 ≤ m := le_max_left _ _
        have hm_ge : 10 * (381005 / 1000000 : ℝ)⁻¹ * (b : ℝ) ^ 2 ≤ (m : ℝ) :=
          le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (le_max_right 1 _))
        have hA_ge_5m2 : 5 * m ^ 2 ≤ A.card := by exact_mod_cast le_trans hP_m5 hA_big
        have hRkm_le : (R2 k' m : ℝ) ≤
            ((1 / 200000 : ℝ) * (1 / 2 - 1 / 200000 : ℝ) / (u : ℝ) ^ 3) * (A.card : ℝ) :=
          le_trans hP_Rkm (mul_le_mul_of_nonneg_left hA_big (by positivity))
        let W := A.filter (fun v => (381005 / 1000000 + 1 / 200000 : ℝ) * (A.card : ℝ) ≤
          ((A.filter (fun w => w ≠ v ∧ ¬G.Adj v w)).card : ℝ))
        by_cases hW_big : R2 k' m ≤ W.card
        · have hm_ge' : 10 * (381005 / 1000000 + 1 / 200000 : ℝ)⁻¹ * (b : ℝ) ^ 2 ≤ (m : ℝ) := by
            have h1 : 10 * (381005 / 1000000 + 1 / 200000 : ℝ)⁻¹ ≤ 10 * (381005 / 1000000 : ℝ)⁻¹ := by
              norm_num
            exact le_trans (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) hm_ge
          rcases gnnw_lemma9 G (by norm_num) (by norm_num) hb1 hk' hm1 hm_ge' A hA_ge_5m2 hW_big with
            ⟨c, hcA, hcl⟩ | ⟨S, hSA, T, hTA, hdisjST, hScard, hScl, hSTblue, hTcard⟩
          · exact Or.inl ⟨c, Finset.Subset.trans hcA Finset.subset_union_left, hcl⟩
          · by_cases hbt : t' ≤ b
            · obtain ⟨S', hS'S, hS'card⟩ := Finset.exists_subset_card_eq (hScard.symm ▸ hbt)
              exact Or.inr (Or.inl ⟨S', Finset.Subset.trans hS'S hSA,
                ⟨fun a ha b' hb' hab' => hScl.1 (hS'S ha) (hS'S hb') hab', hS'card⟩⟩)
            · push Not at hbt
              have hTne : T.Nonempty := by
                rw [← Finset.card_pos]
                have hpos : (0 : ℝ) < (T.card : ℝ) :=
                  lt_of_lt_of_le (by
                    have : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr hAne.card_pos
                    positivity) hTcard
                exact_mod_cast hpos
              have hTdens : 1 / 2 - δ (k' + (t' - b)) ≤ dens G T Y' := by
                have h1 := hA_sub_dens T hTA hTne
                have hδ_le : δ (k' + t') ≤ δ (k' + (t' - b)) :=
                  div_le_div_of_nonneg_left (by norm_num) (Nat.cast_pos.mpr (by omega))
                    (by exact_mod_cast (by omega : k' + (t' - b) ≤ k' + t'))
                linarith
              have hTgap : (1 / 200000 : ℝ) / ((u : ℝ) ^ 2) ≤ dens G T Y' + δ (k' + (t' - b)) - 1 / 2 := by
                have h1 := hA_sub_dens T hTA hTne
                have hle1 : δ (u - 1) ≤ δ (k' + (t' - b)) :=
                  div_le_div_of_nonneg_left (by norm_num) (Nat.cast_pos.mpr (by omega))
                    (by exact_mod_cast (by omega : k' + (t' - b) ≤ u - 1))
                have hdiff1 : δ (u - 1) - δ u = (1 / 200000 : ℝ) / (((u - 1 : ℕ) : ℝ) * (u : ℝ)) := by
                  dsimp [δ]
                  have hu1 : ((u - 1 : ℕ) : ℝ) = (u : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
                  have hu_ne : (u : ℝ) ≠ 0 := by positivity
                  have hu1_ne : (u : ℝ) - 1 ≠ 0 := ne_of_gt (by
                    have : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu2
                    linarith)
                  rw [hu1]; field_simp [hu_ne, hu1_ne]; ring
                have hstep : (1 / 200000 : ℝ) / ((u : ℝ) ^ 2) ≤
                    (1 / 200000 : ℝ) / (((u - 1 : ℕ) : ℝ) * (u : ℝ)) := by
                  apply div_le_div_of_nonneg_left (by norm_num)
                    (mul_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega)))
                  have : ((u - 1 : ℕ) : ℝ) ≤ (u : ℝ) := by exact_mod_cast Nat.sub_le u 1
                  nlinarith [show (0 : ℝ) < (u : ℝ) by positivity]
                change _ ≤ dens G T Y' + δ (k' + (t' - b)) - 1 / 2
                change 1 / 2 - δ u ≤ dens G T Y' at h1
                linarith
              have hb_choice : 2 * (((u : ℝ) ^ 2 / (1 / 200000 : ℝ)) ^ r) ≤
                  ((381005 / 1000000 + 1 / 200000 : ℝ) / (381005 / 1000000 : ℝ)) ^ b := by
                have hratio : (1 + 1 / 200000 : ℝ) ≤
                    (381005 / 1000000 + 1 / 200000 : ℝ) / (381005 / 1000000 : ℝ) := by norm_num
                have h1 := pow_le_pow_left₀ (by norm_num) hratio b
                have hlog1 : 0 < Real.log (1 + 1 / 200000 : ℝ) := Real.log_pos (by norm_num)
                have hb_log : 2 * (64 : ℝ) * Real.log (u : ℝ) - (64 : ℝ) * Real.log (1 / 200000 : ℝ) +
                    Real.log 2 ≤ (b : ℝ) * Real.log (1 + 1 / 200000 : ℝ) := by
                  have hceil : (2 * (64 : ℝ) * Real.log (u : ℝ) - (64 : ℝ) * Real.log (1 / 200000 : ℝ) +
                      Real.log 2) / Real.log (1 + 1 / 200000 : ℝ) ≤ (b : ℝ) :=
                    le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (le_max_right 1 _))
                  rwa [div_le_iff₀ hlog1] at hceil
                have hLHS_pos : 0 < 2 * (((u : ℝ) ^ 2 / (1 / 200000 : ℝ)) ^ r) := by positivity
                have hlog_eq : Real.log (2 * (((u : ℝ) ^ 2 / (1 / 200000 : ℝ)) ^ r)) =
                    2 * (64 : ℝ) * Real.log (u : ℝ) - (64 : ℝ) * Real.log (1 / 200000 : ℝ) + Real.log 2 := by
                  have hu_pos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (by omega : 0 < u)
                  have hrc : (r : ℝ) = (64 : ℝ) := by exact_mod_cast hr
                  rw [Real.log_mul (by norm_num) (pow_pos (div_pos (pow_pos hu_pos 2) (by norm_num)) r).ne',
                    Real.log_pow, Real.log_div (pow_pos hu_pos 2).ne' (by norm_num), Real.log_pow, hrc]
                  push_cast; ring
                have hexp_b : 2 * (((u : ℝ) ^ 2 / (1 / 200000 : ℝ)) ^ r) ≤ (1 + 1 / 200000 : ℝ) ^ b := by
                  calc _ = Real.exp (Real.log (2 * (((u : ℝ) ^ 2 / (1 / 200000 : ℝ)) ^ r))) :=
                        (Real.exp_log hLHS_pos).symm
                    _ = Real.exp (2 * (64 : ℝ) * Real.log (u : ℝ) - (64 : ℝ) * Real.log (1 / 200000 : ℝ) +
                          Real.log 2) := by rw [hlog_eq]
                    _ ≤ Real.exp ((b : ℝ) * Real.log (1 + 1 / 200000 : ℝ)) := Real.exp_le_exp.mpr hb_log
                    _ = (1 + 1 / 200000 : ℝ) ^ b := by
                        rw [mul_comm, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 200000),
                          Real.rpow_natCast]
                exact le_trans hexp_b h1
              have hTmom : (200705 / 1000000 : ℝ)⁻¹ ^ k' * (821605 / 1000000 : ℝ)⁻¹ ^ l *
                  (381005 / 1000000 : ℝ)⁻¹ ^ (t' - b) ≤
                  (dens G T Y' + δ (k' + (t' - b)) - 1 / 2) ^ r * (T.card : ℝ) * (Y'.card : ℝ) := by
                have hμ_split : (381005 / 1000000 : ℝ)⁻¹ ^ t' =
                    (381005 / 1000000 : ℝ)⁻¹ ^ b * (381005 / 1000000 : ℝ)⁻¹ ^ (t' - b) := by
                  rw [← pow_add, Nat.add_sub_of_le (le_of_lt hbt)]
                have hcoef_ge1 : 1 ≤ ((1 / 200000 : ℝ) / ((u : ℝ) ^ 2)) ^ r *
                    ((381005 / 1000000 + 1 / 200000 : ℝ) ^ b / 2) * (381005 / 1000000 : ℝ)⁻¹ ^ b := by
                  have h1 : ((1 / 200000 : ℝ) / ((u : ℝ) ^ 2)) ^ r *
                      ((381005 / 1000000 + 1 / 200000 : ℝ) ^ b / 2) * (381005 / 1000000 : ℝ)⁻¹ ^ b =
                      (((381005 / 1000000 + 1 / 200000 : ℝ) / (381005 / 1000000 : ℝ)) ^ b) /
                        (2 * (((u : ℝ) ^ 2 / (1 / 200000 : ℝ)) ^ r)) := by
                    have hinv1 : ((1 / 200000 : ℝ) / (u : ℝ) ^ 2) ^ r =
                        (((u : ℝ) ^ 2 / (1 / 200000 : ℝ)) ^ r)⁻¹ := by
                      rw [← inv_pow, inv_div]
                    have hinv2 : (381005 / 1000000 + 1 / 200000 : ℝ) ^ b *
                        (381005 / 1000000 : ℝ)⁻¹ ^ b =
                        ((381005 / 1000000 + 1 / 200000 : ℝ) / (381005 / 1000000 : ℝ)) ^ b := by
                      rw [← mul_pow]; congr 1
                    rw [hinv1, ← hinv2]
                    ring
                  rw [h1, one_le_div (by positivity)]
                  exact hb_choice
                calc (200705 / 1000000 : ℝ)⁻¹ ^ k' * (821605 / 1000000 : ℝ)⁻¹ ^ l *
                      (381005 / 1000000 : ℝ)⁻¹ ^ (t' - b)
                    ≤ (((1 / 200000 : ℝ) / ((u : ℝ) ^ 2)) ^ r *
                        ((381005 / 1000000 + 1 / 200000 : ℝ) ^ b / 2) * (381005 / 1000000 : ℝ)⁻¹ ^ b) *
                        ((200705 / 1000000 : ℝ)⁻¹ ^ k' * (821605 / 1000000 : ℝ)⁻¹ ^ l *
                          (381005 / 1000000 : ℝ)⁻¹ ^ (t' - b)) := by
                      have hnn : (0 : ℝ) ≤ (200705 / 1000000 : ℝ)⁻¹ ^ k' * (821605 / 1000000 : ℝ)⁻¹ ^ l *
                          (381005 / 1000000 : ℝ)⁻¹ ^ (t' - b) := by positivity
                      nlinarith
                  _ = ((1 / 200000 : ℝ) / ((u : ℝ) ^ 2)) ^ r *
                        ((381005 / 1000000 + 1 / 200000 : ℝ) ^ b / 2) *
                        ((200705 / 1000000 : ℝ)⁻¹ ^ k' * (821605 / 1000000 : ℝ)⁻¹ ^ l *
                          (381005 / 1000000 : ℝ)⁻¹ ^ t') := by rw [hμ_split]; ring
                  _ ≤ ((1 / 200000 : ℝ) / ((u : ℝ) ^ 2)) ^ r *
                        ((381005 / 1000000 + 1 / 200000 : ℝ) ^ b / 2) * ((A.card : ℝ) * (Y'.card : ℝ)) :=
                      mul_le_mul_of_nonneg_left hAY_ge (by positivity)
                  _ = ((1 / 200000 : ℝ) / ((u : ℝ) ^ 2)) ^ r *
                        (((381005 / 1000000 + 1 / 200000 : ℝ) ^ b / 2 * (A.card : ℝ)) * (Y'.card : ℝ)) := by ring
                  _ ≤ (dens G T Y' + δ (k' + (t' - b)) - 1 / 2) ^ r * ((T.card : ℝ) * (Y'.card : ℝ)) :=
                      mul_le_mul (pow_le_pow_left₀ (by positivity) hTgap r)
                        (mul_le_mul_of_nonneg_right hTcard (Nat.cast_nonneg _))
                        (by positivity) (pow_nonneg (by linarith) r)
                  _ = (dens G T Y' + δ (k' + (t' - b)) - 1 / 2) ^ r * (T.card : ℝ) * (Y'.card : ℝ) := by ring
              have hTgood := ih (k' + (t' - b)) (by omega) k' (t' - b) hk' (by omega) rfl
                T Y' (Disjoint.mono_left hTA hdisjA) hTdens hTmom
              rcases hTgood with ⟨c, hc, hcl⟩ | ⟨c, hcT, hcl⟩ | ⟨c, hcY, hcl⟩
              · exact Or.inl ⟨c, Finset.Subset.trans hc (Finset.union_subset_union hTA (Finset.Subset.refl _)), hcl⟩
              · right; left
                have hdisjSc : Disjoint S c := Disjoint.mono_right hcT hdisjST
                refine ⟨S ∪ c, Finset.union_subset hSA (Finset.Subset.trans hcT hTA), ?_, ?_⟩
                · intro a ha b' hb' hab'
                  rcases mem_union.mp ha with haS | hac <;>
                  rcases mem_union.mp hb' with hbS | hbc
                  · exact hScl.1 haS hbS hab'
                  · exact hSTblue a haS b' (hcT hbc)
                  · exact (hSTblue b' hbS a (hcT hac)).symm
                  · exact hcl.1 hac hbc hab'
                · rw [Finset.card_union_of_disjoint hdisjSc, hScard, hcl.card_eq]; omega
              · exact Or.inr (Or.inr ⟨c, hcY, hcl⟩)
        · -- Step 4: Red / Density-Boost Split via Lemma 7 + `gnnw_lemma12_red_blue_contra`!
          push Not at hW_big
          have hW_le : (W.card : ℝ) ≤
              ((1 / 200000 : ℝ) * (1 / 2 - 1 / 200000 : ℝ) / (u : ℝ) ^ 3) * (A.card : ℝ) :=
            le_trans (by exact_mod_cast hW_big.le) hRkm_le
          have hW_sum_le :
              ∑ v ∈ W, dens G A (Y'.filter (fun y => G.Adj v y)) *
                ((Y'.filter (fun y => G.Adj v y)).card : ℝ) ≤
              ((1 / 200000 : ℝ) / (u : ℝ) ^ 3) * eR G A Y' := by
            have h1 : ∑ v ∈ W, dens G A (Y'.filter (fun y => G.Adj v y)) *
                ((Y'.filter (fun y => G.Adj v y)).card : ℝ) ≤ (W.card : ℝ) * (Y'.card : ℝ) := by
              calc _ ≤ ∑ _v ∈ W, (Y'.card : ℝ) := by
                    refine Finset.sum_le_sum (fun v _ => ?_)
                    have hd1 := dens_le_one G A (Y'.filter (fun y => G.Adj v y))
                    have hc1 : ((Y'.filter (fun y => G.Adj v y)).card : ℝ) ≤ (Y'.card : ℝ) := by
                      exact_mod_cast Finset.card_filter_le Y' _
                    nlinarith [dens_nonneg G A (Y'.filter (fun y => G.Adj v y))]
                _ = (W.card : ℝ) * (Y'.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
            have h2 : (1 / 2 - 1 / 200000 : ℝ) * (A.card : ℝ) * (Y'.card : ℝ) ≤ eR G A Y' := by
              rw [eR_eq_dens_mul]
              have hδ_le : δ (k' + t') ≤ 1 / 200000 :=
                div_le_self (by norm_num) (by exact_mod_cast (by omega : 1 ≤ k' + t'))
              have : (1 / 2 - 1 / 200000 : ℝ) ≤ dens G A Y' := by linarith
              nlinarith [show (0 : ℝ) ≤ (A.card : ℝ) * (Y'.card : ℝ) by positivity]
            calc _ ≤ (W.card : ℝ) * (Y'.card : ℝ) := h1
              _ ≤ (((1 / 200000 : ℝ) * (1 / 2 - 1 / 200000 : ℝ) / (u : ℝ) ^ 3) * (A.card : ℝ)) *
                    (Y'.card : ℝ) := mul_le_mul_of_nonneg_right hW_le (Nat.cast_nonneg _)
              _ = ((1 / 200000 : ℝ) / (u : ℝ) ^ 3) * ((1 / 2 - 1 / 200000 : ℝ) * (A.card : ℝ) * (Y'.card : ℝ)) := by ring
              _ ≤ ((1 / 200000 : ℝ) / (u : ℝ) ^ 3) * eR G A Y' :=
                  mul_le_mul_of_nonneg_left h2 (by positivity)
          have hAW_sum_ge : (dens G A Y' - (1 / 200000 : ℝ) / (u : ℝ) ^ 3) * eR G A Y' ≤
              ∑ v ∈ A \ W, dens G A (Y'.filter (fun y => G.Adj v y)) *
                ((Y'.filter (fun y => G.Adj v y)).card : ℝ) := by
            have hlem7 := gnnw_lemma7 G A Y' hAne hY'ne
            have hsplit : ∑ v ∈ A, dens G A (Y'.filter (fun y => G.Adj v y)) *
                  ((Y'.filter (fun y => G.Adj v y)).card : ℝ) =
                (∑ v ∈ A \ W, dens G A (Y'.filter (fun y => G.Adj v y)) *
                  ((Y'.filter (fun y => G.Adj v y)).card : ℝ)) +
                (∑ v ∈ W, dens G A (Y'.filter (fun y => G.Adj v y)) *
                  ((Y'.filter (fun y => G.Adj v y)).card : ℝ)) := by
              rw [← Finset.sum_union disjoint_sdiff_self_left,
                Finset.sdiff_union_of_subset (Finset.filter_subset _ A)]
            linarith
          have hAW_deg_le : ∑ v ∈ A \ W, ((Y'.filter (fun y => G.Adj v y)).card : ℝ) ≤ eR G A Y' := by
            have heA : eR G A Y' = ∑ v ∈ A, ((Y'.filter (fun y => G.Adj v y)).card : ℝ) := by
              unfold eR; push_cast; rfl
            rw [heA]
            exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.cast_nonneg _)
          have hδ_le : δ (k' + t') ≤ 1 / 200000 :=
            div_le_self (by norm_num) (by exact_mod_cast (by omega : 1 ≤ k' + t'))
          have heR_pos : 0 < eR G A Y' := by
            rw [eR_eq_dens_mul]
            exact mul_pos (mul_pos (by linarith) (Nat.cast_pos.mpr hAne.card_pos))
              (Nat.cast_pos.mpr hY'ne.card_pos)
          have hd_sub_pos : 0 < dens G A Y' - (1 / 200000 : ℝ) / (u : ℝ) ^ 3 := by
            have h1 : (1 / 200000 : ℝ) / (u : ℝ) ^ 3 ≤ 1 / 200000 :=
              div_le_self (by norm_num) (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ u)))
            linarith
          have hex_v : ∃ v ∈ A \ W,
              dens G A Y' - (1 / 200000 : ℝ) / (u : ℝ) ^ 3 ≤
                dens G A (Y'.filter (fun y => G.Adj v y)) := by
            by_contra hall; push Not at hall
            have hAW_ne : (A \ W).Nonempty := by
              by_contra hE; rw [Finset.not_nonempty_iff_eq_empty] at hE
              rw [hE, Finset.sum_empty] at hAW_sum_ge; nlinarith
            have hlt : ∑ v ∈ A \ W, dens G A (Y'.filter (fun y => G.Adj v y)) *
                ((Y'.filter (fun y => G.Adj v y)).card : ℝ) <
                (dens G A Y' - (1 / 200000 : ℝ) / (u : ℝ) ^ 3) *
                  ∑ v ∈ A \ W, ((Y'.filter (fun y => G.Adj v y)).card : ℝ) := by
              rw [Finset.mul_sum]
              refine Finset.sum_lt_sum_of_nonempty hAW_ne (fun v hv => ?_)
              have hdeg_pos : (0 : ℝ) < ((Y'.filter (fun y => G.Adj v y)).card : ℝ) := by
                have h1 := hA_deg v (Finset.sdiff_subset hv)
                have : (0 : ℝ) < (Y'.card : ℝ) := Nat.cast_pos.mpr hY'ne.card_pos
                nlinarith
              exact mul_lt_mul_of_pos_right (hall v hv) hdeg_pos
            nlinarith
          rcases hex_v with ⟨v, hvAW, hv_dens⟩
          have hvA : v ∈ A := (Finset.mem_sdiff.mp hvAW).1
          have hv_notW : v ∉ W := (Finset.mem_sdiff.mp hvAW).2
          have hv_bdeg : ((A.filter (fun w => w ≠ v ∧ ¬G.Adj v w)).card : ℝ) <
              (381005 / 1000000 + 1 / 200000 : ℝ) * (A.card : ℝ) := by
            by_contra hge; push Not at hge; exact hv_notW (mem_filter.mpr ⟨hvA, hge⟩)
          let p' : ℝ := 1 / 2 - δ (u - 1)
          let Y'' := Y'.filter (fun y => G.Adj v y)
          let AR := A.filter (fun w => G.Adj v w)
          let AB := (A.erase v).filter (fun w => ¬G.Adj v w)
          have hAB_eq : AB = A.filter (fun w => w ≠ v ∧ ¬G.Adj v w) := by
            ext w; simp only [AB, mem_filter, mem_erase]; tauto
          have hY''_ge : (1 / 2 - 1 / 200000 : ℝ) * (Y'.card : ℝ) ≤ (Y''.card : ℝ) := by
            have h1 := hA_deg v hvA
            nlinarith [Nat.cast_nonneg (α := ℝ) Y'.card]
          have hY''_pos : (0 : ℝ) < (Y''.card : ℝ) := by
            have : (0 : ℝ) < (Y'.card : ℝ) := Nat.cast_pos.mpr hY'ne.card_pos
            nlinarith
          have hA_pos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr hAne.card_pos
          let α : ℝ := dens G A Y'' - p'
          let αR : ℝ := dens G AR Y'' - p'
          let αB : ℝ := dens G AB Y'' - p'
          have hdiff_δ : δ (u - 1) - δ u = (1 / 200000 : ℝ) / (((u - 1 : ℕ) : ℝ) * (u : ℝ)) := by
            dsimp [δ]
            have hu1 : ((u - 1 : ℕ) : ℝ) = (u : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
            have hu_ne : (u : ℝ) ≠ 0 := by positivity
            have hu1_ne : (u : ℝ) - 1 ≠ 0 := ne_of_gt (by
              have : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu2
              linarith)
            rw [hu1]; field_simp [hu_ne, hu1_ne]; ring
          have hα_ge_base : dens G A Y' + δ u - 1 / 2 ≤ α := by
            have hgap : (1 / 200000 : ℝ) / (u : ℝ) ^ 3 ≤ δ (u - 1) - δ u := by
              rw [hdiff_δ]
              apply div_le_div_of_nonneg_left (by norm_num)
                (mul_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega)))
              have : ((u - 1 : ℕ) : ℝ) ≤ (u : ℝ) := by exact_mod_cast Nat.sub_le u 1
              have hu1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast (by omega : 1 ≤ u)
              nlinarith
            dsimp [α, p']; linarith
          have hα_ge_eps : (1 / 200000 : ℝ) / (u : ℝ) ^ 2 ≤ α := by
            have hgap : (1 / 200000 : ℝ) / (u : ℝ) ^ 2 ≤ δ (u - 1) - δ u - (1 / 200000 : ℝ) / (u : ℝ) ^ 3 := by
              rw [hdiff_δ]
              have hu_pos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (by omega : 0 < u)
              have hu1_eq : ((u - 1 : ℕ) : ℝ) = (u : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
              rw [hu1_eq]
              have h2 : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu2
              have hsub_eq : (1 / 200000 : ℝ) / (((u : ℝ) - 1) * (u : ℝ)) -
                  (1 / 200000 : ℝ) / (u : ℝ) ^ 3 - (1 / 200000 : ℝ) / (u : ℝ) ^ 2 =
                  (1 / 200000 : ℝ) / (((u : ℝ) - 1) * (u : ℝ) ^ 3) := by
                field_simp [ne_of_gt hu_pos, ne_of_gt (by linarith : (0 : ℝ) < (u : ℝ) - 1)]; ring
              have hnn : (0 : ℝ) ≤ (1 / 200000 : ℝ) / (((u : ℝ) - 1) * (u : ℝ) ^ 3) :=
                div_nonneg (by norm_num) (mul_nonneg (by linarith) (by positivity))
              linarith
            dsimp [α, p']; change 1 / 2 - δ u ≤ dens G A Y' at hAdens; linarith
          have hα_pos : 0 < α := lt_of_lt_of_le (by positivity) hα_ge_eps
          by_cases hRed : 0 ≤ αR ∧
              (200705 / 1000000 : ℝ) * α ^ r * (A.card : ℝ) / (1 / 2 - 1 / 200000 : ℝ) ≤
                αR ^ r * (AR.card : ℝ)
          · have hAR_sub : AR ⊆ A := Finset.filter_subset _ A
            have hY''_sub : Y'' ⊆ Y' := Finset.filter_subset _ Y'
            have hAR_dens : 1 / 2 - δ ((k' - 1) + t') ≤ dens G AR Y'' := by
              have hEq : (k' - 1) + t' = u - 1 := by omega
              rw [hEq]; dsimp [αR, p'] at hRed; linarith
            have hAR_mom : (200705 / 1000000 : ℝ)⁻¹ ^ (k' - 1) * (821605 / 1000000 : ℝ)⁻¹ ^ l *
                (381005 / 1000000 : ℝ)⁻¹ ^ t' ≤
                (dens G AR Y'' + δ ((k' - 1) + t') - 1 / 2) ^ r * (AR.card : ℝ) * (Y''.card : ℝ) := by
              have hEq : (k' - 1) + t' = u - 1 := by omega
              have hαR_eq : dens G AR Y'' + δ (u - 1) - 1 / 2 = αR := by dsimp [αR, p']; ring
              rw [hEq, hαR_eq]
              have hpow_x : (200705 / 1000000 : ℝ) * (200705 / 1000000 : ℝ)⁻¹ ^ k' =
                  (200705 / 1000000 : ℝ)⁻¹ ^ (k' - 1) := by
                have hk1 : k' = (k' - 1) + 1 := by omega
                conv_lhs => rw [hk1, pow_succ]
                field_simp
              have hstep1 : (200705 / 1000000 : ℝ) * α ^ r * (A.card : ℝ) * (Y'.card : ℝ) ≤
                  αR ^ r * (AR.card : ℝ) * (Y''.card : ℝ) := by
                have h1 := mul_le_mul_of_nonneg_right hRed.2 hY''_pos.le
                have h2 : (200705 / 1000000 : ℝ) * α ^ r * (A.card : ℝ) * (Y'.card : ℝ) ≤
                    (200705 / 1000000 : ℝ) * α ^ r * (A.card : ℝ) / (1 / 2 - 1 / 200000 : ℝ) * (Y''.card : ℝ) := by
                  have hY_div : (Y'.card : ℝ) ≤ (Y''.card : ℝ) / (1 / 2 - 1 / 200000 : ℝ) := by
                    rw [le_div_iff₀ (by norm_num)]; linarith only [hY''_ge]
                  calc (200705 / 1000000 : ℝ) * α ^ r * (A.card : ℝ) * (Y'.card : ℝ)
                      ≤ ((200705 / 1000000 : ℝ) * α ^ r * (A.card : ℝ)) *
                          ((Y''.card : ℝ) / (1 / 2 - 1 / 200000 : ℝ)) :=
                        mul_le_mul_of_nonneg_left hY_div (by positivity)
                    _ = (200705 / 1000000 : ℝ) * α ^ r * (A.card : ℝ) / (1 / 2 - 1 / 200000 : ℝ) *
                          (Y''.card : ℝ) := by ring
                exact le_trans h2 h1
              calc _ = (200705 / 1000000 : ℝ) * ((200705 / 1000000 : ℝ)⁻¹ ^ k' *
                      (821605 / 1000000 : ℝ)⁻¹ ^ l * (381005 / 1000000 : ℝ)⁻¹ ^ t') := by
                    rw [← hpow_x]; ring
                _ ≤ (200705 / 1000000 : ℝ) *
                      ((dens G A Y' + δ u - 1 / 2) ^ r * (A.card : ℝ) * (Y'.card : ℝ)) :=
                    mul_le_mul_of_nonneg_left hAmom (by norm_num)
                _ ≤ (200705 / 1000000 : ℝ) * (α ^ r * (A.card : ℝ) * (Y'.card : ℝ)) := by
                    have h1 := pow_le_pow_left₀ (by linarith) hα_ge_base r
                    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_right h1 hA_pos.le) (Nat.cast_nonneg _)) (by norm_num)
                _ = (200705 / 1000000 : ℝ) * α ^ r * (A.card : ℝ) * (Y'.card : ℝ) := by ring
                _ ≤ αR ^ r * (AR.card : ℝ) * (Y''.card : ℝ) := hstep1
            have hgoodR := ih (k' - 1 + t') (by omega) (k' - 1) t' (by omega) ht' rfl
              AR Y'' (Disjoint.mono hAR_sub hY''_sub hdisjA) hAR_dens hAR_mom
            rcases hgoodR with ⟨c, hc, hcl⟩ | ⟨c, hc, hcl⟩ | ⟨c, hc, hcl⟩
            · left
              have hv_not : v ∉ c := by
                intro hvc
                rcases mem_union.mp (hc hvc) with hvR | hvY''
                · exact G.loopless.irrefl v (mem_filter.mp hvR).2
                · exact Finset.disjoint_left.mp hdisjA hvA (hY''_sub hvY'')
              refine ⟨insert v c, ?_, ?_, ?_⟩
              · intro w hw
                rcases mem_insert.mp hw with rfl | hwc
                · exact mem_union_left Y' hvA
                · exact Finset.union_subset_union hAR_sub hY''_sub (hc hwc)
              · intro a ha b' hb' hab'
                rcases mem_insert.mp ha with hav | hac <;>
                rcases mem_insert.mp hb' with hbv | hbc
                · exact absurd (hav.trans hbv.symm) hab'
                · rw [hav]; rcases mem_union.mp (hc hbc) with h1 | h2
                  · exact (mem_filter.mp h1).2
                  · exact (mem_filter.mp h2).2
                · rw [hbv]; rcases mem_union.mp (hc hac) with h1 | h2
                  · exact (mem_filter.mp h1).2.symm
                  · exact (mem_filter.mp h2).2.symm
                · exact hcl.1 hac hbc hab'
              · rw [Finset.card_insert_of_notMem hv_not, hcl.card_eq]; omega
            · exact Or.inr (Or.inl ⟨c, Finset.Subset.trans hc hAR_sub, hcl⟩)
            · exact Or.inr (Or.inr ⟨c, Finset.Subset.trans hc hY''_sub, hcl⟩)
          · by_cases hBlue : 0 ≤ αB ∧
                (381005 / 1000000 : ℝ) * α ^ r * (A.card : ℝ) / (1 / 2 - 1 / 200000 : ℝ) ≤
                  αB ^ r * (AB.card : ℝ)
            · have hAB_sub : AB ⊆ A :=
                Finset.Subset.trans (Finset.filter_subset _ _) (Finset.erase_subset v A)
              have hY''_sub : Y'' ⊆ Y' := Finset.filter_subset _ Y'
              have hAB_dens : 1 / 2 - δ (k' + (t' - 1)) ≤ dens G AB Y'' := by
                have hEq : k' + (t' - 1) = u - 1 := by omega
                rw [hEq]; dsimp [αB, p'] at hBlue; linarith
              have hAB_mom : (200705 / 1000000 : ℝ)⁻¹ ^ k' * (821605 / 1000000 : ℝ)⁻¹ ^ l *
                  (381005 / 1000000 : ℝ)⁻¹ ^ (t' - 1) ≤
                  (dens G AB Y'' + δ (k' + (t' - 1)) - 1 / 2) ^ r * (AB.card : ℝ) * (Y''.card : ℝ) := by
                have hEq : k' + (t' - 1) = u - 1 := by omega
                have hαB_eq : dens G AB Y'' + δ (u - 1) - 1 / 2 = αB := by dsimp [αB, p']; ring
                rw [hEq, hαB_eq]
                have hpow_μ : (381005 / 1000000 : ℝ) * (381005 / 1000000 : ℝ)⁻¹ ^ t' =
                    (381005 / 1000000 : ℝ)⁻¹ ^ (t' - 1) := by
                  have ht1 : t' = (t' - 1) + 1 := by omega
                  conv_lhs => rw [ht1, pow_succ]
                  field_simp
                have hstep1 : (381005 / 1000000 : ℝ) * α ^ r * (A.card : ℝ) * (Y'.card : ℝ) ≤
                    αB ^ r * (AB.card : ℝ) * (Y''.card : ℝ) := by
                  have h1 := mul_le_mul_of_nonneg_right hBlue.2 hY''_pos.le
                  have h2 : (381005 / 1000000 : ℝ) * α ^ r * (A.card : ℝ) * (Y'.card : ℝ) ≤
                      (381005 / 1000000 : ℝ) * α ^ r * (A.card : ℝ) / (1 / 2 - 1 / 200000 : ℝ) * (Y''.card : ℝ) := by
                    have hY_div : (Y'.card : ℝ) ≤ (Y''.card : ℝ) / (1 / 2 - 1 / 200000 : ℝ) := by
                      rw [le_div_iff₀ (by norm_num)]; linarith only [hY''_ge]
                    calc (381005 / 1000000 : ℝ) * α ^ r * (A.card : ℝ) * (Y'.card : ℝ)
                        ≤ ((381005 / 1000000 : ℝ) * α ^ r * (A.card : ℝ)) *
                            ((Y''.card : ℝ) / (1 / 2 - 1 / 200000 : ℝ)) :=
                          mul_le_mul_of_nonneg_left hY_div (by positivity)
                      _ = (381005 / 1000000 : ℝ) * α ^ r * (A.card : ℝ) / (1 / 2 - 1 / 200000 : ℝ) *
                            (Y''.card : ℝ) := by ring
                  exact le_trans h2 h1
                calc _ = (381005 / 1000000 : ℝ) * ((200705 / 1000000 : ℝ)⁻¹ ^ k' *
                        (821605 / 1000000 : ℝ)⁻¹ ^ l * (381005 / 1000000 : ℝ)⁻¹ ^ t') := by
                      rw [← hpow_μ]; ring
                  _ ≤ (381005 / 1000000 : ℝ) *
                        ((dens G A Y' + δ u - 1 / 2) ^ r * (A.card : ℝ) * (Y'.card : ℝ)) :=
                      mul_le_mul_of_nonneg_left hAmom (by norm_num)
                  _ ≤ (381005 / 1000000 : ℝ) * (α ^ r * (A.card : ℝ) * (Y'.card : ℝ)) := by
                      have h1 := pow_le_pow_left₀ (by linarith) hα_ge_base r
                      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
                        (mul_le_mul_of_nonneg_right h1 hA_pos.le) (Nat.cast_nonneg _)) (by norm_num)
                  _ = (381005 / 1000000 : ℝ) * α ^ r * (A.card : ℝ) * (Y'.card : ℝ) := by ring
                  _ ≤ αB ^ r * (AB.card : ℝ) * (Y''.card : ℝ) := hstep1
              have hgoodB := ih (k' + (t' - 1)) (by omega) k' (t' - 1) hk' (by omega) rfl
                AB Y'' (Disjoint.mono hAB_sub hY''_sub hdisjA) hAB_dens hAB_mom
              rcases hgoodB with ⟨c, hc, hcl⟩ | ⟨c, hc, hcl⟩ | ⟨c, hc, hcl⟩
              · exact Or.inl ⟨c, Finset.Subset.trans hc (Finset.union_subset_union hAB_sub hY''_sub), hcl⟩
              · right; left
                have hv_not : v ∉ c := fun hvc => (Finset.notMem_erase v A) (mem_filter.mp (hc hvc)).1
                refine ⟨insert v c, ?_, ?_, ?_⟩
                · intro w hw
                  rcases mem_insert.mp hw with rfl | hwc
                  · exact hvA
                  · exact hAB_sub (hc hwc)
                · intro a ha b' hb' hab'
                  rcases mem_insert.mp ha with hav | hac <;>
                  rcases mem_insert.mp hb' with hbv | hbc
                  · exact absurd (hav.trans hbv.symm) hab'
                  · rw [hav] at hab' ⊢; exact ⟨hab', (mem_filter.mp (hc hbc)).2⟩
                  · rw [hbv] at hab' ⊢; exact ⟨hab', fun h => (mem_filter.mp (hc hac)).2 h.symm⟩
                  · exact hcl.1 hac hbc hab'
                · rw [Finset.card_insert_of_notMem hv_not, hcl.card_eq]; omega
              · exact Or.inr (Or.inr ⟨c, Finset.Subset.trans hc hY''_sub, hcl⟩)
            · exfalso
              have hdisj_RB : Disjoint AR AB := by
                rw [Finset.disjoint_left]; intro w hwR hwB
                exact (mem_filter.mp hwB).2 (mem_filter.mp hwR).2
              have hdisj_v : Disjoint ({v} : Finset (Fin N)) (AR ∪ AB) := by
                rw [Finset.disjoint_singleton_left, mem_union]
                rintro (h1 | h2)
                · exact G.loopless.irrefl v (mem_filter.mp h1).2
                · exact (Finset.notMem_erase v A) (mem_filter.mp h2).1
              have hA_eq : A = {v} ∪ (AR ∪ AB) := by
                ext w; simp only [AR, AB, mem_union, mem_singleton, mem_filter, mem_erase]
                constructor
                · intro hwA; by_cases hwv : w = v
                  · exact Or.inl hwv
                  · by_cases hadj : G.Adj v w
                    · exact Or.inr (Or.inl ⟨hwA, hadj⟩)
                    · exact Or.inr (Or.inr ⟨⟨hwv, hwA⟩, hadj⟩)
                · rintro (rfl | ⟨hwA, _⟩ | ⟨⟨_, hwA⟩, _⟩) <;> assumption
              have hsum_c : (AR.card : ℝ) + (AB.card : ℝ) ≤ (A.card : ℝ) := by
                have h1 : AR.card + AB.card ≤ A.card := by
                  rw [← Finset.card_union_of_disjoint hdisj_RB]
                  exact Finset.card_le_card (by rw [hA_eq]; exact Finset.subset_union_right)
                exact_mod_cast h1
              have heq24 : 1 ≤ αR / α * ((AR.card : ℝ) / (A.card : ℝ)) +
                  αB / α * ((AB.card : ℝ) / (A.card : ℝ)) + 1 / (α * (A.card : ℝ)) := by
                have hfp_split : fp G p' A Y'' = fp G p' {v} Y'' + fp G p' AR Y'' + fp G p' AB Y'' := by
                  rw [hA_eq, fp_union_left G p' hdisj_v, fp_union_left G p' hdisj_RB]; ring
                have hfp_v : fp G p' {v} Y'' ≤ (Y''.card : ℝ) := by
                  unfold fp
                  have h1 : eR G {v} Y'' ≤ (Y''.card : ℝ) := by
                    rw [eR_singleton_left]; exact_mod_cast Finset.card_filter_le Y'' _
                  have hp'_nn : 0 ≤ p' := by
                    dsimp [p']
                    have hδ1 : δ (u - 1) ≤ 1 / 200000 :=
                      div_le_self (by norm_num) (by exact_mod_cast (by omega : 1 ≤ u - 1))
                    linarith only [hδ1]
                  have h2 : 0 ≤ p' * (Y''.card : ℝ) := mul_nonneg hp'_nn (Nat.cast_nonneg _)
                  simp only [Finset.card_singleton, Nat.cast_one, mul_one]
                  linarith only [h1, h2]
                have hfp_A : fp G p' A Y'' = α * (A.card : ℝ) * (Y''.card : ℝ) := by
                  unfold fp; rw [eR_eq_dens_mul]; dsimp [α]; ring
                have hfp_AR : fp G p' AR Y'' = αR * (AR.card : ℝ) * (Y''.card : ℝ) := by
                  unfold fp; rw [eR_eq_dens_mul]; dsimp [αR]; ring
                have hfp_AB : fp G p' AB Y'' = αB * (AB.card : ℝ) * (Y''.card : ℝ) := by
                  unfold fp; rw [eR_eq_dens_mul]; dsimp [αB]; ring
                have hineq : α * (A.card : ℝ) ≤ αR * (AR.card : ℝ) + αB * (AB.card : ℝ) + 1 :=
                  le_of_mul_le_mul_right (by linarith only [hfp_split, hfp_v, hfp_A, hfp_AR, hfp_AB]) hY''_pos
                have hdiv := div_le_div_of_nonneg_right hineq (mul_pos hα_pos hA_pos).le
                have hLHS : α * (A.card : ℝ) / (α * (A.card : ℝ)) = 1 :=
                  div_self (mul_pos hα_pos hA_pos).ne'
                have hRHS : (αR * (AR.card : ℝ) + αB * (AB.card : ℝ) + 1) / (α * (A.card : ℝ)) =
                    αR / α * ((AR.card : ℝ) / (A.card : ℝ)) +
                      αB / α * ((AB.card : ℝ) / (A.card : ℝ)) + 1 / (α * (A.card : ℝ)) := by
                  rw [add_div, add_div, mul_div_mul_comm, mul_div_mul_comm]
                linarith only [hdiv, hLHS, hRHS]
              have herr : 1 / (α * (A.card : ℝ)) ≤ 1 / 200000 := by
                have hA_ge_u2 : (u : ℝ) ^ 2 / ((1 / 200000 : ℝ) ^ 2) ≤ (A.card : ℝ) :=
                  le_trans hP_err hA_big
                have hαA_ge : 200000 ≤ α * (A.card : ℝ) := by
                  have h1 := mul_le_mul hα_ge_eps hA_ge_u2 (by positivity) hα_pos.le
                  have h2 : ((1 / 200000 : ℝ) / (u : ℝ) ^ 2) * ((u : ℝ) ^ 2 / ((1 / 200000 : ℝ) ^ 2)) =
                      200000 := by
                    have hu_pos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (by omega : 0 < u)
                    field_simp [ne_of_gt hu_pos]
                  linarith only [h1, h2]
                rw [div_le_iff₀ (mul_pos hα_pos hA_pos)]
                linarith only [hαA_ge]
              subst hr
              exact gnnw_lemma12_red_blue_contra hα_pos hA_pos (Nat.cast_nonneg _) (Nat.cast_nonneg _)
                hsum_c (by rw [hAB_eq]; exact hv_bdeg.le) herr heq24 hRed hBlue

/-- **Concrete GNNW Lemma 12 at `p = 1/2`, `r = 64`, `ε = 1/200000`, `μ₀ = 381/1000`,
`x₀ = 2007/10000`, `y₀ = 8216/10000`:**
There exists `L₀ : ℕ` such that for all `k, l, t ≥ 1` with `l ≥ L₀`, every candidate `(X, Y)`
with `d(X, Y) ≥ 1/2` and `|X| |Y| ≥ x₀^{-k} y₀^{-l} μ₀^{-t}` is `(k, l, t)`-good! -/
private lemma gnnw_lemma12_concrete :
    ∃ L₀ : ℕ, ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k l t : ℕ),
      1 ≤ k → L₀ ≤ l → 1 ≤ t →
      ∀ X Y : Finset (Fin N), Disjoint X Y →
        (1 / 2 : ℝ) ≤ dens G X Y →
        ((2007 / 10000 : ℝ)⁻¹ ^ k) * ((8216 / 10000 : ℝ)⁻¹ ^ l) * ((381 / 1000 : ℝ)⁻¹ ^ t) ≤
          (X.card : ℝ) * (Y.card : ℝ) →
        IsGood G k l t X Y := by
  obtain ⟨L₀, hL₀2, hparams⟩ := gnnw_lemma12_params
  refine ⟨L₀, fun N G k l t hk hl ht X Y hdisj hdens hXY => ?_⟩
  let δ : ℕ → ℝ := fun u => (1 / 200000 : ℝ) / (u : ℝ)
  suffices hgen : ∀ (r : ℕ), r = 64 → IsGood G k l t X Y by exact hgen 64 rfl
  intro r hr
  obtain ⟨_, hP_init, _, _, _⟩ := hparams k l t hk hl ht
  rw [← hr] at hP_init
  have hdens' : 1 / 2 - δ (k + t) ≤ dens G X Y := by
    have : 0 ≤ δ (k + t) := by dsimp [δ]; positivity
    linarith
  have hmom' : (200705 / 1000000 : ℝ)⁻¹ ^ k * (821605 / 1000000 : ℝ)⁻¹ ^ l *
      (381005 / 1000000 : ℝ)⁻¹ ^ t ≤
      (dens G X Y + δ (k + t) - 1 / 2) ^ r * (X.card : ℝ) * (Y.card : ℝ) := by
    have hgap : δ (k + t) ≤ dens G X Y + δ (k + t) - 1 / 2 := by linarith
    have hpow_gap := pow_le_pow_left₀ (by dsimp [δ]; positivity) hgap r
    have hrx : (1 + 1 / 200000 : ℝ) * (200705 / 1000000 : ℝ)⁻¹ ≤ (2007 / 10000 : ℝ)⁻¹ := by norm_num
    have hry : (1 + 1 / 200000 : ℝ) * (821605 / 1000000 : ℝ)⁻¹ ≤ (8216 / 10000 : ℝ)⁻¹ := by norm_num
    have hrμ : (1 + 1 / 200000 : ℝ) * (381005 / 1000000 : ℝ)⁻¹ ≤ (381 / 1000 : ℝ)⁻¹ := by norm_num
    have hprod_inv : (1 + 1 / 200000 : ℝ) ^ (k + l + t) *
        ((200705 / 1000000 : ℝ)⁻¹ ^ k * (821605 / 1000000 : ℝ)⁻¹ ^ l *
          (381005 / 1000000 : ℝ)⁻¹ ^ t) ≤
        (2007 / 10000 : ℝ)⁻¹ ^ k * (8216 / 10000 : ℝ)⁻¹ ^ l * (381 / 1000 : ℝ)⁻¹ ^ t := by
      rw [pow_add, pow_add]
      have h1 := pow_le_pow_left₀ (by norm_num) hrx k
      have h2 := pow_le_pow_left₀ (by norm_num) hry l
      have h3 := pow_le_pow_left₀ (by norm_num) hrμ t
      rw [mul_pow] at h1 h2 h3
      have h12 := mul_le_mul h1 h2 (by positivity) (by positivity)
      have h123 := mul_le_mul h12 h3 (by positivity) (by positivity)
      calc (1 + 1 / 200000 : ℝ) ^ k * (1 + 1 / 200000 : ℝ) ^ l * (1 + 1 / 200000 : ℝ) ^ t *
            ((200705 / 1000000 : ℝ)⁻¹ ^ k * (821605 / 1000000 : ℝ)⁻¹ ^ l *
              (381005 / 1000000 : ℝ)⁻¹ ^ t)
          = ((1 + 1 / 200000 : ℝ) ^ k * (200705 / 1000000 : ℝ)⁻¹ ^ k) *
              ((1 + 1 / 200000 : ℝ) ^ l * (821605 / 1000000 : ℝ)⁻¹ ^ l) *
              ((1 + 1 / 200000 : ℝ) ^ t * (381005 / 1000000 : ℝ)⁻¹ ^ t) := by ring
        _ ≤ (2007 / 10000 : ℝ)⁻¹ ^ k * (8216 / 10000 : ℝ)⁻¹ ^ l * (381 / 1000 : ℝ)⁻¹ ^ t := h123
    calc _ ≤ (((1 / 200000 : ℝ) / ((k + t : ℕ) : ℝ)) ^ r * (1 + 1 / 200000 : ℝ) ^ (k + l + t)) *
            ((200705 / 1000000 : ℝ)⁻¹ ^ k * (821605 / 1000000 : ℝ)⁻¹ ^ l *
              (381005 / 1000000 : ℝ)⁻¹ ^ t) :=
          le_mul_of_one_le_left (by positivity) hP_init
      _ = ((1 / 200000 : ℝ) / ((k + t : ℕ) : ℝ)) ^ r *
            ((1 + 1 / 200000 : ℝ) ^ (k + l + t) *
              ((200705 / 1000000 : ℝ)⁻¹ ^ k * (821605 / 1000000 : ℝ)⁻¹ ^ l *
                (381005 / 1000000 : ℝ)⁻¹ ^ t)) := by ring
      _ ≤ ((1 / 200000 : ℝ) / ((k + t : ℕ) : ℝ)) ^ r *
            ((2007 / 10000 : ℝ)⁻¹ ^ k * (8216 / 10000 : ℝ)⁻¹ ^ l * (381 / 1000 : ℝ)⁻¹ ^ t) :=
          mul_le_mul_of_nonneg_left hprod_inv (by positivity)
      _ ≤ (dens G X Y + δ (k + t) - 1 / 2) ^ r * ((X.card : ℝ) * (Y.card : ℝ)) :=
          mul_le_mul hpow_gap hXY (by positivity) (pow_nonneg (by linarith) r)
      _ = (dens G X Y + δ (k + t) - 1 / 2) ^ r * (X.card : ℝ) * (Y.card : ℝ) := by ring
  exact gnnw_lemma12_main_ind hL₀2 hparams G hl hr (k + t) k t hk ht rfl X Y hdisj hdens' hmom'

/-- Exact binomial identity for balanced bipartition averaging:
`(2m - 2).choose (m - 1) * (2m) * (2m - 1) = (2m).choose m * m * m` for `m ≥ 1`. -/
private lemma balanced_cut_choose_identity (m : ℕ) (hm : 1 ≤ m) :
    (2 * m - 2).choose (m - 1) * (2 * m) * (2 * m - 1) = (2 * m).choose m * m * m := by
  have hstep : ∀ a b : ℕ, b ≤ a → (a + 1) * a.choose b = (b + 1) * (a + 1).choose (b + 1) := by
    intro a b hba
    have h1 := Nat.choose_mul_factorial_mul_factorial hba
    have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.succ_le_succ hba)
    have hsub : (a + 1) - (b + 1) = a - b := by omega
    rw [hsub, Nat.factorial_succ a, Nat.factorial_succ b] at h2
    have hpos : 0 < b.factorial * (a - b).factorial :=
      Nat.mul_pos (Nat.factorial_pos b) (Nat.factorial_pos (a - b))
    have hmul : ((a + 1) * a.choose b) * (b.factorial * (a - b).factorial) =
        ((b + 1) * (a + 1).choose (b + 1)) * (b.factorial * (a - b).factorial) := by
      calc ((a + 1) * a.choose b) * (b.factorial * (a - b).factorial)
          = (a + 1) * (a.choose b * b.factorial * (a - b).factorial) := by ring
        _ = (a + 1) * a.factorial := by rw [h1]
        _ = (a + 1).choose (b + 1) * ((b + 1) * b.factorial) * (a - b).factorial := h2.symm
        _ = ((b + 1) * (a + 1).choose (b + 1)) * (b.factorial * (a - b).factorial) := by ring
    exact Nat.eq_of_mul_eq_mul_right hpos hmul
  have h1 : (2 * m) * (2 * m - 1).choose (m - 1) = m * (2 * m).choose m := by
    have := hstep (2 * m - 1) (m - 1) (by omega)
    have hsub1 : (2 * m - 1) + 1 = 2 * m := by omega
    have hsub2 : (m - 1) + 1 = m := by omega
    rwa [hsub1, hsub2] at this
  have h2 : (2 * m - 1) * (2 * m - 2).choose (m - 1) = m * (2 * m - 1).choose (m - 1) := by
    have := hstep (2 * m - 2) (m - 1) (by omega)
    have hsub1 : (2 * m - 2) + 1 = 2 * m - 1 := by omega
    have hsub2 : (m - 1) + 1 = m := by omega
    rw [hsub1, hsub2] at this
    have hsym : (2 * m - 1).choose m = (2 * m - 1).choose (m - 1) := by
      have := Nat.choose_symm (n := 2 * m - 1) (k := m) (by omega)
      have hsub3 : 2 * m - 1 - m = m - 1 := by omega
      rw [hsub3] at this
      exact this.symm
    rwa [hsym] at this
  calc (2 * m - 2).choose (m - 1) * (2 * m) * (2 * m - 1)
      = (2 * m) * ((2 * m - 1) * (2 * m - 2).choose (m - 1)) := by ring
    _ = (2 * m) * (m * (2 * m - 1).choose (m - 1)) := by rw [h2]
    _ = m * ((2 * m) * (2 * m - 1).choose (m - 1)) := by ring
    _ = m * (m * (2 * m).choose m) := by rw [h1]
    _ = (2 * m).choose m * m * m := by ring

/-- Exact count of `m`-subsets of `V` (size `2m`) containing `u` and excluding `v` (`u ≠ v ∈ V`). -/
private lemma card_powersetCard_mem_notMem {N m : ℕ} (V : Finset (Fin N)) (hV : V.card = 2 * m)
    {u v : Fin N} (hu : u ∈ V) (hv : v ∈ V) (huv : u ≠ v) (hm : 1 ≤ m) :
    ((V.powersetCard m).filter (fun X => u ∈ X ∧ v ∉ X)).card = (2 * m - 2).choose (m - 1) := by
  let rest := (V.erase u).erase v
  have hv_in : v ∈ V.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
  have hrest_card : rest.card = 2 * m - 2 := by
    rw [Finset.card_erase_of_mem hv_in, Finset.card_erase_of_mem hu, hV]
    omega
  rw [← hrest_card, ← Finset.card_powersetCard (m - 1) rest]
  refine Finset.card_bij (fun X _ => X.erase u) ?_ ?_ ?_
  · intro X hX
    rw [mem_filter, Finset.mem_powersetCard] at hX
    rw [Finset.mem_powersetCard]
    refine ⟨?_, by rw [Finset.card_erase_of_mem hX.2.1, hX.1.2]⟩
    intro w hw
    have hwu : w ≠ u := Finset.ne_of_mem_erase hw
    have hwX : w ∈ X := Finset.mem_of_mem_erase hw
    have hwv : w ≠ v := fun hEq => hX.2.2 (hEq ▸ hwX)
    exact Finset.mem_erase.mpr ⟨hwv, Finset.mem_erase.mpr ⟨hwu, hX.1.1 hwX⟩⟩
  · intro X1 hX1 X2 hX2 hEq
    have h1 : u ∈ X1 := (mem_filter.mp hX1).2.1
    have h2 : u ∈ X2 := (mem_filter.mp hX2).2.1
    rw [← Finset.insert_erase h1, ← Finset.insert_erase h2, hEq]
  · intro Z hZ
    rw [Finset.mem_powersetCard] at hZ
    have huZ : u ∉ Z := fun h => (Finset.notMem_erase u V) (Finset.mem_of_mem_erase (hZ.1 h))
    have hvZ : v ∉ Z := fun h => (Finset.notMem_erase v (V.erase u)) (hZ.1 h)
    refine ⟨insert u Z, ?_, Finset.erase_insert huZ⟩
    rw [mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, by rw [Finset.card_insert_of_notMem huZ, hZ.2, Nat.sub_add_cancel hm]⟩,
      mem_insert_self u Z, by rw [mem_insert]; push Not; exact ⟨huv.symm, hvZ⟩⟩
    intro w hw
    rcases mem_insert.mp hw with rfl | hwZ
    · exact hu
    · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hZ.1 hwZ))

/-- Balanced bipartition extraction: any graph `G` on `N ≥ 2` vertices with red edge count
`e_R(univ, univ) ≥ (1 / 2) * N * (N - 1)` contains disjoint sets `X, Y` of size `N / 2` with
`dens G X Y ≥ 1 / 2`. -/
private lemma exists_balanced_bipartition_half {N : ℕ} (G : SimpleGraph (Fin N)) (hN : 2 ≤ N)
    (hdense : (1 / 2 : ℝ) * (N : ℝ) * ((N : ℝ) - 1) ≤ eR G Finset.univ Finset.univ) :
    ∃ X Y : Finset (Fin N), Disjoint X Y ∧ X.card = N / 2 ∧ Y.card = N / 2 ∧
      (1 / 2 : ℝ) ≤ dens G X Y := by
  classical
  set m := N / 2
  have hm1 : 1 ≤ m := by omega
  -- First obtain an even-sized subset `V` of size `2 * m` with `eR G V V ≥ (1/2) * (2m) * (2m - 1)`!
  have hexV : ∃ V : Finset (Fin N), V.card = 2 * m ∧
      (1 / 2 : ℝ) * ((2 * m : ℕ) : ℝ) * (((2 * m : ℕ) : ℝ) - 1) ≤ eR G V V := by
    by_cases heven : N % 2 = 0
    · refine ⟨Finset.univ, by simp; omega, ?_⟩
      have hEq : 2 * m = N := by omega
      rwa [hEq]
    · -- `N = 2m + 1`: drop a vertex `v0` of minimum red degree!
      have hN_eq : N = 2 * m + 1 := by omega
      obtain ⟨v0, _, hv0_min⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N))
        (fun v => (Finset.univ.filter (fun u => G.Adj v u)).card)
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩)
      let V := (Finset.univ : Finset (Fin N)).erase v0
      have hVcard : V.card = 2 * m := by
        rw [Finset.card_erase_of_mem (mem_univ v0), Finset.card_univ, Fintype.card_fin]; omega
      refine ⟨V, hVcard, ?_⟩
      -- `eR G univ univ = eR G V V + 2 * d_R(v0)`, and `N * d_R(v0) ≤ eR G univ univ`!
      have hsum_all : eR G Finset.univ Finset.univ =
          ∑ v : Fin N, ((Finset.univ.filter (fun u => G.Adj v u)).card : ℝ) := by
        unfold eR; push_cast; rfl
      have hmin_le : (N : ℝ) * ((Finset.univ.filter (fun u => G.Adj v0 u)).card : ℝ) ≤
          eR G Finset.univ Finset.univ := by
        rw [hsum_all]
        calc (N : ℝ) * ((Finset.univ.filter (fun u => G.Adj v0 u)).card : ℝ)
            = ∑ _v : Fin N, ((Finset.univ.filter (fun u => G.Adj v0 u)).card : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ ≤ ∑ v : Fin N, ((Finset.univ.filter (fun u => G.Adj v u)).card : ℝ) :=
              Finset.sum_le_sum (fun v _ => by exact_mod_cast hv0_min v (mem_univ v))
      have hsplit_eR : eR G Finset.univ Finset.univ =
          eR G V V + 2 * ((Finset.univ.filter (fun u => G.Adj v0 u)).card : ℝ) := by
        have huniv : (Finset.univ : Finset (Fin N)) = {v0} ∪ V := by
          ext u; simp [V]
        have hdisj_v : Disjoint ({v0} : Finset (Fin N)) V :=
          Finset.disjoint_singleton_left.mpr (Finset.notMem_erase v0 _)
        have h1 : eR G Finset.univ Finset.univ =
            eR G {v0} Finset.univ + eR G V Finset.univ := by
          conv_lhs => arg 2; rw [huniv]
          exact eR_union_left G hdisj_v
        have h2 : eR G V Finset.univ = eR G V {v0} + eR G V V := by
          rw [eR_symm G V Finset.univ]
          conv_lhs => arg 2; rw [huniv]
          rw [eR_union_left G hdisj_v, eR_symm G {v0} V, eR_symm G V V]
        have h3 : eR G {v0} Finset.univ = ((Finset.univ.filter (fun u => G.Adj v0 u)).card : ℝ) :=
          eR_singleton_left G v0 Finset.univ
        have h4 : eR G V {v0} = ((Finset.univ.filter (fun u => G.Adj v0 u)).card : ℝ) := by
          rw [eR_symm, eR_singleton_left]
          congr 2
          ext u
          simp only [V, mem_filter, mem_erase, mem_univ, true_and, and_true]
          exact ⟨fun h => h.2, fun h => ⟨(G.ne_of_adj h).symm, h⟩⟩
        linarith
      have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      have h2m_eq : ((2 * m : ℕ) : ℝ) = (N : ℝ) - 1 := by
        have : 2 * m = N - 1 := by omega
        rw [this, Nat.cast_sub (by omega)]; simp
      rw [h2m_eq]
      -- From `eR V V = S - 2 d0 ≥ S * (N - 2) / N ≥ (1/2) * N * (N - 1) * (N - 2) / N = (1/2) * (N - 1) * (N - 2)`!
      have h1 : (N : ℝ) * eR G V V ≥ ((N : ℝ) - 2) * eR G Finset.univ Finset.univ := by nlinarith
      have h2 : ((N : ℝ) - 2) * eR G Finset.univ Finset.univ ≥
          (N : ℝ) * ((1 / 2 : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 1 - 1)) := by
        have hN2 : (0 : ℝ) ≤ (N : ℝ) - 2 := by
          have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          linarith
        nlinarith
      nlinarith
  rcases hexV with ⟨V, hVcard, hVdense⟩
  -- Average `eR G X (V \ X)` over `X ∈ V.powersetCard m`!
  have hsum_cut : ∑ X ∈ V.powersetCard m, eR G X (V \ X) =
      (((2 * m - 2).choose (m - 1) : ℕ) : ℝ) * eR G V V := by
    calc ∑ X ∈ V.powersetCard m, eR G X (V \ X)
        = ∑ X ∈ V.powersetCard m, ∑ u ∈ V, ∑ v ∈ V,
            if G.Adj u v ∧ u ∈ X ∧ v ∉ X then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl (fun X hX => ?_)
          have hXV : X ⊆ V := (Finset.mem_powersetCard.mp hX).1
          rw [eR_eq_sum_indicator, ← Finset.sum_subset hXV]
          · refine Finset.sum_congr rfl (fun u hu => ?_)
            rw [← Finset.sum_subset (s₁ := V \ X) (s₂ := V) Finset.sdiff_subset]
            · refine Finset.sum_congr rfl (fun v hv => ?_)
              have hv' : v ∉ X := (Finset.mem_sdiff.mp hv).2
              simp [hu, hv']
            · intro v hvV hv
              have hvX : v ∈ X := by
                by_contra hnot; exact hv (Finset.mem_sdiff.mpr ⟨hvV, hnot⟩)
              simp [hvX]
          · intro u _ hu; simp [hu]
      _ = ∑ u ∈ V, ∑ v ∈ V, ∑ X ∈ V.powersetCard m,
            if G.Adj u v ∧ u ∈ X ∧ v ∉ X then (1 : ℝ) else 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
      _ = ∑ u ∈ V, ∑ v ∈ V,
            if G.Adj u v then (((2 * m - 2).choose (m - 1) : ℕ) : ℝ) else 0 := by
          refine Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun v hv => ?_))
          by_cases hadj : G.Adj u v
          · rw [if_pos hadj]
            have hconv : (∑ X ∈ V.powersetCard m, if G.Adj u v ∧ u ∈ X ∧ v ∉ X then (1 : ℝ) else 0) =
                (((V.powersetCard m).filter (fun X => u ∈ X ∧ v ∉ X)).card : ℝ) := by
              rw [← Finset.sum_boole]
              refine Finset.sum_congr rfl (fun X _ => by simp [hadj])
            rw [hconv]
            exact_mod_cast card_powersetCard_mem_notMem V hVcard hu hv (G.ne_of_adj hadj) hm1
          · simp [hadj]
      _ = (((2 * m - 2).choose (m - 1) : ℕ) : ℝ) * eR G V V := by
          rw [eR_eq_sum_indicator, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun u _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun v _ => by split_ifs <;> ring)
  have hsum_ge : (((2 * m).choose m : ℕ) : ℝ) * ((1 / 2 : ℝ) * (m : ℝ) * (m : ℝ)) ≤
      ∑ X ∈ V.powersetCard m, eR G X (V \ X) := by
    rw [hsum_cut]
    have hid := balanced_cut_choose_identity m hm1
    have hidR : (((2 * m - 2).choose (m - 1) : ℕ) : ℝ) * ((2 * m : ℕ) : ℝ) * (((2 * m : ℕ) : ℝ) - 1) =
        (((2 * m).choose m : ℕ) : ℝ) * (m : ℝ) * (m : ℝ) := by
      have hsub : ((2 * m - 1 : ℕ) : ℝ) = ((2 * m : ℕ) : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [← hsub]; exact_mod_cast hid
    calc (((2 * m).choose m : ℕ) : ℝ) * ((1 / 2 : ℝ) * (m : ℝ) * (m : ℝ))
        = (1 / 2 : ℝ) * ((((2 * m).choose m : ℕ) : ℝ) * (m : ℝ) * (m : ℝ)) := by ring
      _ = (((2 * m - 2).choose (m - 1) : ℕ) : ℝ) *
            ((1 / 2 : ℝ) * ((2 * m : ℕ) : ℝ) * (((2 * m : ℕ) : ℝ) - 1)) := by rw [← hidR]; ring
      _ ≤ (((2 * m - 2).choose (m - 1) : ℕ) : ℝ) * eR G V V :=
          mul_le_mul_of_nonneg_left hVdense (Nat.cast_nonneg _)
  have hVpset_ne : (V.powersetCard m).Nonempty := by
    rw [← Finset.card_pos, Finset.card_powersetCard, hVcard]
    exact Nat.choose_pos (by omega)
  have hex_X : ∃ X ∈ V.powersetCard m, (1 / 2 : ℝ) * (m : ℝ) * (m : ℝ) ≤ eR G X (V \ X) := by
    by_contra hall
    push Not at hall
    have hlt := Finset.sum_lt_sum_of_nonempty hVpset_ne hall
    rw [Finset.sum_const, Finset.card_powersetCard, hVcard, nsmul_eq_mul] at hlt
    linarith
  rcases hex_X with ⟨X, hXV, hXeR⟩
  rw [Finset.mem_powersetCard] at hXV
  have hYcard : (V \ X).card = m := by
    rw [Finset.card_sdiff_of_subset hXV.1, hVcard, hXV.2]; omega
  refine ⟨X, V \ X, disjoint_sdiff_self_right, hXV.2, hYcard, ?_⟩
  unfold dens
  rw [if_neg (by push Not; rw [hXV.2, hYcard]; exact ⟨by omega, by omega⟩),
    hXV.2, hYcard, le_div_iff₀ (by positivity)]
  linarith

/-- **Unconditional CGMS/GNNW Exponential Improvement for Diagonal Ramsey Numbers** (pure Mathlib):
There exists `L₀ : ℕ` such that for all `k ≥ L₀`, `R(k) ≤ (399 / 100)^k` —
strictly beating both Erdős–Szekeres (1935) `4^k` and CGMS (2023/2026)'s headline `(4 - 1/128)^k`! -/
theorem ppl042_diagonal_exponential_improvement :
    ∃ L₀ : ℕ, ∀ k ≥ L₀,
      ((sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree k ∧ Gᶜ.CliqueFree k)} : ℕ) : ℝ) ≤
        (399 / 100 : ℝ) ^ k := by
  obtain ⟨L1, hL1⟩ := gnnw_lemma12_concrete
  -- Note `(399/100)^2 * (2007/10000) * (8216/10000) * (381/1000) > 1`!
  let x0 : ℝ := 2007 / 10000
  let y0 : ℝ := 8216 / 10000
  let μ0 : ℝ := 381 / 1000
  let ρ : ℝ := (399 / 100 : ℝ) ^ 2 * (x0 * y0 * μ0)
  have hρ_gt1 : 1 < ρ := by norm_num [ρ, x0, y0, μ0]
  have htend : Tendsto (fun k : ℕ => ρ ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hρ_gt1
  rcases Filter.eventually_atTop.mp (htend.eventually_ge_atTop 16) with ⟨L2, hL2⟩
  refine ⟨max 2 (max L1 L2), fun k hk => ?_⟩
  have hk2 : 2 ≤ k := le_trans (le_max_left _ _) hk
  have hkL1 : L1 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkL2 : L2 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  set N : ℕ := Nat.floor ((399 / 100 : ℝ) ^ k)
  have hN_le : (N : ℝ) ≤ (399 / 100 : ℝ) ^ k := Nat.floor_le (by positivity)
  have hN_gt : (399 / 100 : ℝ) ^ k - 1 < (N : ℝ) := by
    have := Nat.lt_floor_add_one ((399 / 100 : ℝ) ^ k); linarith
  have h399_ge16 : (15 : ℝ) ≤ (399 / 100 : ℝ) ^ k := by
    calc (15 : ℝ) ≤ (399 / 100 : ℝ) ^ 2 := by norm_num
      _ ≤ (399 / 100 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk2
  have hN2 : 2 ≤ N := by
    have : (14 : ℝ) < (N : ℝ) := by linarith
    have : 14 < N := by exact_mod_cast this
    omega
  -- Prove `ramseyProp k k N`!
  have hram : ramseyProp k k N := by
    classical
    intro G ⟨hGk, hGkc⟩
    -- By red/blue symmetry, either `G` or `Gᶜ` has red edge count `≥ (1/2) * N * (N - 1)`!
    have hsum_compl : eR G Finset.univ Finset.univ + eR Gᶜ Finset.univ Finset.univ =
        (N : ℝ) * ((N : ℝ) - 1) := by
      calc eR G Finset.univ Finset.univ + eR Gᶜ Finset.univ Finset.univ
          = ∑ u : Fin N, ((∑ v : Fin N, if G.Adj u v then (1 : ℝ) else 0) +
              (∑ v : Fin N, if Gᶜ.Adj u v then (1 : ℝ) else 0)) := by
            rw [eR_eq_sum_indicator, eR_eq_sum_indicator, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun u _ => ?_)
            refine congrArg₂ (· + ·)
              (Finset.sum_congr rfl (fun v _ => by split_ifs <;> rfl))
              (Finset.sum_congr rfl (fun v _ => by split_ifs <;> rfl))
        _ = ∑ _u : Fin N, ((N : ℝ) - 1) := by
            refine Finset.sum_congr rfl (fun u _ => ?_)
            rw [← Finset.sum_add_distrib]
            have hEq : (∑ v : Fin N, ((if G.Adj u v then (1 : ℝ) else 0) +
                  (if Gᶜ.Adj u v then (1 : ℝ) else 0))) =
                ∑ v : Fin N, if u ≠ v then (1 : ℝ) else 0 := by
              refine Finset.sum_congr rfl (fun v _ => ?_)
              by_cases huv : u = v
              · subst huv; simp
              · by_cases hadj : G.Adj u v
                · simp [huv, hadj, SimpleGraph.compl_adj]
                · simp [huv, hadj, SimpleGraph.compl_adj]
            rw [hEq, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
            have hc : (Finset.univ.filter (fun v : Fin N => u ≠ v)).card = N - 1 := by
              have : Finset.univ.filter (fun v : Fin N => u ≠ v) = Finset.univ.erase u := by
                ext v; simp [ne_comm]
              rw [this, Finset.card_erase_of_mem (mem_univ u), Finset.card_univ, Fintype.card_fin]
            rw [hc, Nat.cast_sub (by omega), Nat.cast_one]
        _ = (N : ℝ) * ((N : ℝ) - 1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    -- Helper that derives `False` from any `H` with `eR H univ univ ≥ (1/2) * N * (N - 1)` and `H.CliqueFree k ∧ Hᶜ.CliqueFree k`!
    have hcontra_of_dense : ∀ H : SimpleGraph (Fin N),
        H.CliqueFree k → Hᶜ.CliqueFree k →
        (1 / 2 : ℝ) * (N : ℝ) * ((N : ℝ) - 1) ≤ eR H Finset.univ Finset.univ → False := by
      intro H hHk hHkc hHdense
      obtain ⟨X, Y, hdisj, hXcard, hYcard, hdens⟩ := exists_balanced_bipartition_half H hN2 hHdense
      -- Check `|X| * |Y| = (N / 2)^2 ≥ x0⁻¹^k * y0⁻¹^k * μ0⁻¹^k`!
      have hNhalf : (399 / 100 : ℝ) ^ k / 4 ≤ ((N / 2 : ℕ) : ℝ) := by
        have h1 : (N : ℝ) - 1 ≤ 2 * ((N / 2 : ℕ) : ℝ) := by
          have : N ≤ 2 * (N / 2) + 1 := by omega
          have : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
          linarith
        linarith
      have hXY_ge : x0⁻¹ ^ k * y0⁻¹ ^ k * μ0⁻¹ ^ k ≤ (X.card : ℝ) * (Y.card : ℝ) := by
        rw [hXcard, hYcard]
        have h1 : ((399 / 100 : ℝ) ^ k / 4) ^ 2 ≤ ((N / 2 : ℕ) : ℝ) * ((N / 2 : ℕ) : ℝ) := by
          rw [← sq]; exact pow_le_pow_left₀ (by positivity) hNhalf 2
        have hρ_k : (16 : ℝ) ≤ ρ ^ k := hL2 k hkL2
        have h2 : x0⁻¹ ^ k * y0⁻¹ ^ k * μ0⁻¹ ^ k ≤ ((399 / 100 : ℝ) ^ k / 4) ^ 2 := by
          have hprod_pos : 0 < (x0 * y0 * μ0) ^ k := pow_pos (by norm_num [x0, y0, μ0]) k
          have hEq1 : ((399 / 100 : ℝ) ^ k / 4) ^ 2 = ((399 / 100 : ℝ) ^ 2) ^ k / 16 := by
            rw [div_pow, ← pow_mul, mul_comm k 2, pow_mul]; norm_num
          have hEq2 : x0⁻¹ ^ k * y0⁻¹ ^ k * μ0⁻¹ ^ k = ((x0 * y0 * μ0) ^ k)⁻¹ := by
            rw [← mul_pow, ← mul_pow, ← mul_inv, ← mul_inv, inv_pow]
          rw [hEq1, hEq2, le_div_iff₀ (by norm_num), inv_mul_le_iff₀ hprod_pos]
          have hEq3 : ρ ^ k = (x0 * y0 * μ0) ^ k * ((399 / 100 : ℝ) ^ 2) ^ k := by
            dsimp [ρ]; rw [mul_pow, mul_comm]
          rw [← hEq3]; exact hρ_k
        exact le_trans h2 h1
      have hgood := hL1 N H k k k (by omega) hkL1 (by omega) X Y hdisj hdens hXY_ge
      rcases hgood with ⟨c, _, hcl⟩ | ⟨c, _, hcl⟩ | ⟨c, _, hcl⟩
      · exact hHk c hcl
      · exact hHkc c hcl
      · exact hHkc c hcl
    by_cases hG : (1 / 2 : ℝ) * (N : ℝ) * ((N : ℝ) - 1) ≤ eR G Finset.univ Finset.univ
    · exact hcontra_of_dense G hGk hGkc hG
    · exact hcontra_of_dense Gᶜ hGkc (by simpa using hGk) (by linarith)
  have hR_le : R2 k k ≤ N := R2_le_of_ramseyProp hram
  exact le_trans (by exact_mod_cast hR_le) hN_le

/-! ### Section 6: Improved Erdős #77 Limit Sandwich (`√2 ≤ liminf R(k)^{1/k} ≤ limsup R(k)^{1/k} ≤ 399 / 100`) -/

/-- **Improved Erdős Problem #77 (PPL 042) Limit Sandwich** (pure Mathlib signature):
`√2 ≤ liminf_{k → ∞} R(k)^{1/k} ≤ limsup_{k → ∞} R(k)^{1/k} ≤ 399 / 100` (strictly `< 4`). -/
theorem ppl042_limit_sandwich_improved :
    Real.sqrt 2 ≤
      Filter.liminf
        (fun k : ℕ =>
          ((sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree k ∧ Gᶜ.CliqueFree k)} : ℕ) : ℝ) ^
            ((k : ℝ)⁻¹)) Filter.atTop ∧
    Filter.liminf
        (fun k : ℕ =>
          ((sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree k ∧ Gᶜ.CliqueFree k)} : ℕ) : ℝ) ^
            ((k : ℝ)⁻¹)) Filter.atTop ≤
      Filter.limsup
        (fun k : ℕ =>
          ((sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree k ∧ Gᶜ.CliqueFree k)} : ℕ) : ℝ) ^
            ((k : ℝ)⁻¹)) Filter.atTop ∧
    Filter.limsup
        (fun k : ℕ =>
          ((sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree k ∧ Gᶜ.CliqueFree k)} : ℕ) : ℝ) ^
            ((k : ℝ)⁻¹)) Filter.atTop ≤ 399 / 100 := by
  let f : ℕ → ℝ := fun k => (R2 k k : ℝ) ^ ((k : ℝ)⁻¹)
  change Real.sqrt 2 ≤ Filter.liminf f Filter.atTop ∧
    Filter.liminf f Filter.atTop ≤ Filter.limsup f Filter.atTop ∧
    Filter.limsup f Filter.atTop ≤ 399 / 100
  have hlower_ev : ∀ᶠ k in Filter.atTop, Real.sqrt 2 ≤ f k := by
    filter_upwards [eventually_ge_atTop 3] with k hk
    have hlt := ppl042_erdos_1947_exp_lower k hk
    change (2 : ℝ) ^ ((k : ℝ) / 2) < (R2 k k : ℝ) at hlt
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hrpow := Real.rpow_le_rpow (by positivity) hlt.le (inv_nonneg.mpr hk_pos.le)
    have hLHS : ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ ((k : ℝ)⁻¹) = Real.sqrt 2 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow]
      congr 1; field_simp [ne_of_gt hk_pos]
    rwa [hLHS] at hrpow
  have hupper_ev : ∀ᶠ k in Filter.atTop, f k ≤ 399 / 100 := by
    obtain ⟨L₀, hL₀⟩ := ppl042_diagonal_exponential_improvement
    filter_upwards [eventually_ge_atTop (max 1 L₀)] with k hk
    have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
    have hkL0 : L₀ ≤ k := le_trans (le_max_right _ _) hk
    have hle := hL₀ k hkL0
    change (R2 k k : ℝ) ≤ (399 / 100 : ℝ) ^ k at hle
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
    have hrpow := Real.rpow_le_rpow (Nat.cast_nonneg _) hle (inv_nonneg.mpr hk_pos.le)
    have hRHS : ((399 / 100 : ℝ) ^ k) ^ ((k : ℝ)⁻¹) = 399 / 100 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 399 / 100),
        mul_inv_cancel₀ (ne_of_gt hk_pos), Real.rpow_one]
    rwa [hRHS] at hrpow
  have hbdd_above : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop f :=
    ⟨399 / 100, hupper_ev⟩
  have hbdd_below : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop f :=
    ⟨Real.sqrt 2, hlower_ev⟩
  have hcobdd_le : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop f :=
    Filter.isCoboundedUnder_le_of_eventually_le Filter.atTop (x := Real.sqrt 2) hlower_ev
  have hcobdd_ge : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop f :=
    Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop (x := (399 / 100 : ℝ)) hupper_ev
  refine ⟨?_, ?_, ?_⟩
  · exact Filter.le_liminf_of_le hcobdd_ge hlower_ev
  · exact Filter.liminf_le_limsup hbdd_above hbdd_below
  · exact Filter.limsup_le_of_le hcobdd_le hupper_ev

end PPL042
