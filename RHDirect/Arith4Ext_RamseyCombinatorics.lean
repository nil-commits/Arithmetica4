/-
Copyright (c) 2026 Arithmetica4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Arithmetica4 Tier A Extension: Ramsey Theory, Erdős–Szekeres, Hales–Jewett & Van der Waerden

A 100% self-contained, targeted-import Tier A Lean 4 formalization covering:
1. **Finite Two-Color & Multicolor Ramsey Theorems + Erdős 1947 `2^{k/2}` Lower Bound:**
   - `ramsey_two_color_graph`, `ramsey_two_color`: explicit Erdős–Szekeres bound
     `R(s, t) ≤ C(s + t - 2, s - 1)`
   - `ramsey_multicolor`: arbitrary `r`-color finite Ramsey theorem
   - `ramsey_uniform_three_le`: explicit `R_r(3) ≤ 3 * r!` bound
   - `ramsey_erdos_lower_binom`, `ramsey_erdos_lower`: Erdős (1947) counting/probabilistic
     lower bound (`∀ k ≥ 3, ∀ n ≤ 2^{k/2}, ∃ G` on `Fin n` with no `k`-clique and no `k`-indep. set)
2. **Schur's Theorem (`schur_theorem`):**
   - Explicit `S(r) ≤ 3 * r! - 1` (and `3 * r!`) bound for monochromatic `x + y = z`
3. **Erdős–Szekeres Monotone Subsequence & Happy Ending Convex `n`-Gon Theorems:**
   - `erdos_szekeres_monotone` (`ab + 1` pigeonhole proof) & `erdos_szekeres_monotone_tight`
     (explicit injective witness on `Fin (a * b)`)
   - `InGeneralPosition`, `InConvexPosition`, `cups_and_caps_theorem`,
     `erdos_szekeres_happy_ending` (`C(2n - 4, n - 2) + 1` points in general position in `ℝ²`
     contain `n` points in convex position: `∀ p ∈ T, p ∉ convexHull ℝ (T.erase p)`)
4. **Full Hales–Jewett Theorem & Van der Waerden's Theorem:**
   - `linePoint`, `hales_jewett_theorem` (self-contained color-focusing proof)
   - `van_der_waerden_theorem` (arbitrary `r`-color `k`-AP theorem derived directly from Hales–Jewett)
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Arith4Ext.RamseyCombinatorics

open scoped BigOperators Classical

/-! ## Section 1: Finite Two-Color & Multicolor Ramsey Theorems + Erdős `2^{k/2}` Lower Bound -/

section RamseyTheorems

/-- **Two-Color Ramsey Theorem (Finset induction core, Erdős–Szekeres binomial bound):**
For any `s, t ≥ 1`, any symmetric 2-coloring `c : V → V → Bool`, and any subset `U : Finset V`
with `Nat.choose (s + t - 2) (s - 1) ≤ U.card`, `U` contains either a `true`-monochromatic
subset of size `s` or a `false`-monochromatic subset of size `t`. -/
theorem ramsey_two_color_finset {V : Type*} [DecidableEq V] (c : V → V → Bool)
    (hsymm : ∀ u v : V, c u v = c v u) :
    ∀ (s t : ℕ), 1 ≤ s → 1 ≤ t → ∀ (U : Finset V),
      Nat.choose (s + t - 2) (s - 1) ≤ U.card →
      (∃ S : Finset V, S ⊆ U ∧ S.card = s ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c u v = true) ∨
      (∃ T : Finset V, T ⊆ U ∧ T.card = t ∧ ∀ u ∈ T, ∀ v ∈ T, u ≠ v → c u v = false) := by
  intro s t
  -- Strong induction on `n = s + t`
  suffices h : ∀ n : ℕ, ∀ s t : ℕ, s + t = n → 1 ≤ s → 1 ≤ t → ∀ (U : Finset V),
      Nat.choose (s + t - 2) (s - 1) ≤ U.card →
      (∃ S : Finset V, S ⊆ U ∧ S.card = s ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c u v = true) ∨
      (∃ T : Finset V, T ⊆ U ∧ T.card = t ∧ ∀ u ∈ T, ∀ v ∈ T, u ≠ v → c u v = false) by
    exact h (s + t) s t rfl
  intro n
  induction n with
  | zero => intro s t hst hs; omega
  | succ n ih =>
    intro s t hst hs ht U hU
    by_cases hs1 : s = 1
    · subst hs1
      have hpos : 0 < U.card := by
        have : Nat.choose (1 + t - 2) (1 - 1) = 1 := Nat.choose_zero_right _
        omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      left
      refine ⟨{v}, Finset.singleton_subset_iff.mpr hv, Finset.card_singleton v, ?_⟩
      intro x hx y hy hne
      rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy] at hne
      exact absurd rfl hne
    · by_cases ht1 : t = 1
      · subst ht1
        have hpos : 0 < U.card := by
          have : Nat.choose (s + 1 - 2) (s - 1) = 1 := by
            have heq : s + 1 - 2 = s - 1 := by omega
            rw [heq, Nat.choose_self]
          omega
        obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
        right
        refine ⟨{v}, Finset.singleton_subset_iff.mpr hv, Finset.card_singleton v, ?_⟩
        intro x hx y hy hne
        rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy] at hne
        exact absurd rfl hne
      · -- `s ≥ 2` and `t ≥ 2`: pick a pivot `v₀ ∈ U` and partition `U.erase v₀`
        have hs2 : 2 ≤ s := by omega
        have ht2 : 2 ≤ t := by omega
        have hpascal : Nat.choose (s + t - 2) (s - 1) =
            Nat.choose ((s - 1) + t - 2) ((s - 1) - 1) + Nat.choose (s + (t - 1) - 2) (s - 1) := by
          have h1 : s + t - 2 = (s + t - 3) + 1 := by omega
          have h2 : s - 1 = (s - 2) + 1 := by omega
          have h3 : (s - 1) + t - 2 = s + t - 3 := by omega
          have h4 : (s - 1) - 1 = s - 2 := by omega
          have h5 : s + (t - 1) - 2 = s + t - 3 := by omega
          rw [h3, h4, h5, h1, h2, Nat.choose_succ_succ]
        have hchoose_pos : 0 < Nat.choose (s + t - 2) (s - 1) :=
          Nat.choose_pos (by omega)
        obtain ⟨v₀, hv₀⟩ := Finset.card_pos.mp (lt_of_lt_of_le hchoose_pos hU)
        let U_T : Finset V := (U.erase v₀).filter (fun v => c v₀ v = true)
        let U_F : Finset V := (U.erase v₀).filter (fun v => c v₀ v = false)
        have hpart : U_T.card + U_F.card = U.card - 1 := by
          have hdisj : Disjoint U_T U_F := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            have h1 := (Finset.mem_filter.mp hx1).2
            have h2 := (Finset.mem_filter.mp hx2).2
            rw [h1] at h2; exact Bool.noConfusion h2
          have hunion : U_T ∪ U_F = U.erase v₀ := by
            ext x
            simp only [U_T, U_F, Finset.mem_union, Finset.mem_filter]
            cases hc : c v₀ x <;> simp
          rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_erase_of_mem hv₀]
        by_cases hT_big : Nat.choose ((s - 1) + t - 2) ((s - 1) - 1) ≤ U_T.card
        · rcases ih (s - 1) t (by omega) (by omega) ht U_T hT_big with
            ⟨S, hSU, hScard, hSmono⟩ | ⟨T, hTU, hTcard, hTmono⟩
          · left
            have hv₀_notS : v₀ ∉ S := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp (hSU h)).1).1 rfl
            refine ⟨insert v₀ S, ?_, ?_, ?_⟩
            · exact Finset.insert_subset hv₀ (hSU.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _)))
            · rw [Finset.card_insert_of_notMem hv₀_notS, hScard]; omega
            · intro x hx y hy hne
              rcases Finset.mem_insert.mp hx with rfl | hxS <;>
                rcases Finset.mem_insert.mp hy with rfl | hyS
              · exact absurd rfl hne
              · exact (Finset.mem_filter.mp (hSU hyS)).2
              · rw [hsymm]; exact (Finset.mem_filter.mp (hSU hxS)).2
              · exact hSmono x hxS y hyS hne
          · right
            exact ⟨T, hTU.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _)), hTcard, hTmono⟩
        · have hF_big : Nat.choose (s + (t - 1) - 2) (s - 1) ≤ U_F.card := by omega
          rcases ih s (t - 1) (by omega) hs (by omega) U_F hF_big with
            ⟨S, hSU, hScard, hSmono⟩ | ⟨T, hTU, hTcard, hTmono⟩
          · left
            exact ⟨S, hSU.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _)), hScard, hSmono⟩
          · right
            have hv₀_notT : v₀ ∉ T := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp (hTU h)).1).1 rfl
            refine ⟨insert v₀ T, ?_, ?_, ?_⟩
            · exact Finset.insert_subset hv₀ (hTU.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _)))
            · rw [Finset.card_insert_of_notMem hv₀_notT, hTcard]; omega
            · intro x hx y hy hne
              rcases Finset.mem_insert.mp hx with rfl | hxT <;>
                rcases Finset.mem_insert.mp hy with rfl | hyT
              · exact absurd rfl hne
              · exact (Finset.mem_filter.mp (hTU hyT)).2
              · rw [hsymm]; exact (Finset.mem_filter.mp (hTU hxT)).2
              · exact hTmono x hxT y hyT hne

/-- **Two-Color Ramsey Theorem (Erdős–Szekeres Binomial Bound `R(s, t) ≤ C(s + t - 2, s - 1)`):**
Every symmetric `Bool`-coloring of the pairs of a finite vertex set `V` with
`|V| ≥ Nat.choose (s + t - 2) (s - 1)` (`s, t ≥ 1`) contains a `true`-clique of size `s` or
a `false`-clique of size `t`. -/
theorem ramsey_two_color {V : Type*} [Fintype V] [DecidableEq V]
    {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hcard : Nat.choose (s + t - 2) (s - 1) ≤ Fintype.card V)
    (c : V → V → Bool) (hsymm : ∀ u v : V, c u v = c v u) :
    (∃ S : Finset V, S.card = s ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c u v = true) ∨
    (∃ T : Finset V, T.card = t ∧ ∀ u ∈ T, ∀ v ∈ T, u ≠ v → c u v = false) := by
  rcases ramsey_two_color_finset c hsymm s t hs ht Finset.univ (by simpa using hcard) with
    ⟨S, _, hScard, hSmono⟩ | ⟨T, _, hTcard, hTmono⟩
  · exact Or.inl ⟨S, hScard, hSmono⟩
  · exact Or.inr ⟨T, hTcard, hTmono⟩

/-- **Graph-Theoretic Two-Color Ramsey Theorem:**
Every finite simple graph `G` on `|V| ≥ Nat.choose (s + t - 2) (s - 1)` vertices (`s, t ≥ 1`)
contains either an `s`-clique or a `t`-element independent set. -/
theorem ramsey_two_color_graph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hcard : Nat.choose (s + t - 2) (s - 1) ≤ Fintype.card V) :
    (∃ S : Finset V, S.card = s ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) ∨
    (∃ T : Finset V, T.card = t ∧ ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬ G.Adj u v) := by
  let c : V → V → Bool := fun u v => decide (G.Adj u v)
  have hsymm : ∀ u v : V, c u v = c v u := fun u v => by
    simp only [c, decide_eq_decide]
    exact G.adj_comm u v
  rcases ramsey_two_color hs ht hcard c hsymm with ⟨S, hScard, hS⟩ | ⟨T, hTcard, hT⟩
  · left
    exact ⟨S, hScard, fun u hu v hv hne => of_decide_eq_true (hS u hu v hv hne)⟩
  · right
    exact ⟨T, hTcard, fun u hu v hv hne => of_decide_eq_false (hT u hu v hv hne)⟩

/-- **General Multicolor Ramsey Theorem (`r` colors, arbitrary clique sizes `m : Fin r → ℕ`):**
For every `r ≥ 1` and target sizes `m : Fin r → ℕ` (`∀ i, 1 ≤ m i`), there exists `N : ℕ`
such that every symmetric `r`-coloring of pairs on any finite type `V` with `N ≤ |V|`
contains a monochromatic subset of size `m col` in some color `col : Fin r`. -/
theorem ramsey_multicolor :
    ∀ (r : ℕ), 1 ≤ r → ∀ (m : Fin r → ℕ), (∀ i : Fin r, 1 ≤ m i) →
      ∃ N : ℕ, 1 ≤ N ∧
        ∀ (V : Type*) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
          ∀ (c : V → V → Fin r), (∀ u v : V, c u v = c v u) →
            ∃ (col : Fin r) (S : Finset V),
              S.card = m col ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c u v = col := by
  intro r
  induction r with
  | zero => intro hr; omega
  | succ r ih =>
    intro _ m hm
    by_cases hr0 : r = 0
    · subst hr0
      refine ⟨m 0, hm 0, ?_⟩
      intro V _ _ hcard c _
      obtain ⟨S, _, hScard⟩ := Finset.exists_subset_card_eq (by simpa using hcard : m 0 ≤ (Finset.univ : Finset V).card)
      refine ⟨0, S, hScard, fun u _ v _ _ => Fin.ext (by have := (c u v).isLt; have := (0 : Fin (0 + 1)).isLt; omega)⟩
    · -- Merge colors `Fin r` into a single super-color `false` and color `Fin.last r` into `true`
      have hr1 : 1 ≤ r := by omega
      let m' : Fin r → ℕ := fun i => m i.castSucc
      obtain ⟨N', hN'1, hih⟩ := ih hr1 m' (fun i => hm i.castSucc)
      let N : ℕ := Nat.choose (m (Fin.last r) + N' - 2) (m (Fin.last r) - 1)
      have hN1 : 1 ≤ N := Nat.choose_pos (by have := hm (Fin.last r); omega)
      refine ⟨N, hN1, ?_⟩
      intro V _ _ hcard c hsymm
      let c2 : V → V → Bool := fun u v => decide (c u v = Fin.last r)
      have hsymm2 : ∀ u v : V, c2 u v = c2 v u := fun u v => by simp [c2, hsymm u v]
      rcases ramsey_two_color (hm (Fin.last r)) hN'1 hcard c2 hsymm2 with
        ⟨S, hScard, hS⟩ | ⟨T, hTcard, hT⟩
      · refine ⟨Fin.last r, S, hScard, fun u hu v hv hne => of_decide_eq_true (hS u hu v hv hne)⟩
      · -- Restrict `c` to the subtype `T` (`|T| = N'`), where no edge has color `Fin.last r`
        let cT : T → T → Fin r := fun u v =>
          if h : u.1 = v.1 then ⟨0, by omega⟩
          else
            let col := c u.1 v.1
            have hne : col ≠ Fin.last r := of_decide_eq_false (hT u.1 u.2 v.1 v.2 h)
            ⟨col.1, by have := col.isLt; have : col.1 ≠ r := fun heq => hne (Fin.ext heq); omega⟩
        have hsymmT : ∀ u v : T, cT u v = cT v u := by
          intro u v
          by_cases h : u.1 = v.1
          · have h' : v.1 = u.1 := h.symm
            simp only [cT, dif_pos h, dif_pos h']
          · have h' : v.1 ≠ u.1 := Ne.symm h
            simp only [cT, dif_neg h, dif_neg h']
            ext
            dsimp only
            rw [hsymm u.1 v.1]
        have hcardT : N' ≤ Fintype.card T := by rw [Fintype.card_coe, hTcard]
        obtain ⟨col', S', hS'card, hS'mono⟩ := hih T hcardT cT hsymmT
        let S : Finset V := S'.image Subtype.val
        have hScard : S.card = m col'.castSucc := by
          rw [Finset.card_image_of_injective _ Subtype.val_injective, hS'card]
        refine ⟨col'.castSucc, S, hScard, ?_⟩
        intro u hu v hv hne
        rcases Finset.mem_image.mp hu with ⟨u', hu', rfl⟩
        rcases Finset.mem_image.mp hv with ⟨v', hv', rfl⟩
        have hne' : u' ≠ v' := fun h => hne (congrArg Subtype.val h)
        have hcol := hS'mono u' hu' v' hv' hne'
        simp only [cT, dif_neg hne] at hcol
        exact Fin.ext (by simpa using congrArg Fin.val hcol)

/-- **Explicit Multicolor Triangle Ramsey Bound `R_r(3) ≤ 3 * r!`:**
For every `r ≥ 1` and every finite set `U` with `3 * r! ≤ U.card`, any symmetric `r`-coloring
of pairs in `U` contains a monochromatic triangle `{u, v, w} ⊆ U`. -/
theorem ramsey_uniform_three_finset {V : Type*} [DecidableEq V] :
    ∀ (r : ℕ), 1 ≤ r → ∀ (U : Finset V), 3 * Nat.factorial r ≤ U.card →
      ∀ (c : V → V → Fin r), (∀ u v : V, c u v = c v u) →
        ∃ (col : Fin r) (u v w : V), u ∈ U ∧ v ∈ U ∧ w ∈ U ∧
          u ≠ v ∧ v ≠ w ∧ u ≠ w ∧ c u v = col ∧ c v w = col ∧ c u w = col := by
  intro r
  induction r with
  | zero => intro hr; omega
  | succ r ih =>
    intro _ U hU c hsymm
    by_cases hr0 : r = 0
    · subst hr0
      have hU3 : 3 ≤ U.card := by simpa using hU
      obtain ⟨S, hSU, hS3⟩ := Finset.exists_subset_card_eq hU3
      obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := Finset.card_eq_three.mp hS3
      refine ⟨0, u, v, w, hSU (by simp), hSU (by simp), hSU (by simp), huv, hvw, huw,
        Fin.ext (by have := (c u v).isLt; have := (0 : Fin (0 + 1)).isLt; omega),
        Fin.ext (by have := (c v w).isLt; have := (0 : Fin (0 + 1)).isLt; omega),
        Fin.ext (by have := (c u w).isLt; have := (0 : Fin (0 + 1)).isLt; omega)⟩
    · have hr1 : 1 ≤ r := by omega
      have hfac_pos : 0 < Nat.factorial (r + 1) := Nat.factorial_pos (r + 1)
      obtain ⟨v₀, hv₀⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
      -- Partition `U.erase v₀` into `r + 1` color neighborhoods `N col = {v ∈ U.erase v₀ | c v₀ v = col}`
      have hsum : ∑ col : Fin (r + 1), ((U.erase v₀).filter (fun v => c v₀ v = col)).card = U.card - 1 := by
        conv_rhs => rw [← Finset.card_erase_of_mem hv₀, Finset.card_eq_sum_ones]
        rw [← Finset.sum_fiberwise_of_maps_to (g := fun v => c v₀ v)
          (t := (Finset.univ : Finset (Fin (r + 1)))) (fun _ _ => Finset.mem_univ _)]
        apply Finset.sum_congr rfl
        intro col _
        rw [Finset.card_eq_sum_ones]
      -- By pigeonhole, some color class `col₀` has size `≥ 3 * r!`
      have hex_big : ∃ col₀ : Fin (r + 1), 3 * Nat.factorial r ≤ ((U.erase v₀).filter (fun v => c v₀ v = col₀)).card := by
        by_contra h
        push Not at h
        have hlt : ∑ col : Fin (r + 1), ((U.erase v₀).filter (fun v => c v₀ v = col)).card ≤
            (r + 1) * (3 * Nat.factorial r - 1) := by
          calc ∑ col : Fin (r + 1), ((U.erase v₀).filter (fun v => c v₀ v = col)).card
              ≤ ∑ _col : Fin (r + 1), (3 * Nat.factorial r - 1) :=
                Finset.sum_le_sum fun col _ => by have := h col; omega
            _ = (r + 1) * (3 * Nat.factorial r - 1) := by simp
        have hfac_rec : Nat.factorial (r + 1) = (r + 1) * Nat.factorial r := Nat.factorial_succ r
        have hfac_r : 1 ≤ Nat.factorial r := Nat.factorial_pos r
        have hmul_sub : (r + 1) * (3 * Nat.factorial r - 1) + (r + 1) = 3 * ((r + 1) * Nat.factorial r) := by
          zify [show 1 ≤ 3 * Nat.factorial r by omega]
          ring
        omega
      rcases hex_big with ⟨col₀, hcol₀_big⟩
      let W : Finset V := (U.erase v₀).filter (fun v => c v₀ v = col₀)
      by_cases hhit : ∃ u ∈ W, ∃ v ∈ W, u ≠ v ∧ c u v = col₀
      · rcases hhit with ⟨u, hu, v, hv, huv, hcuv⟩
        have huU : u ∈ U := Finset.mem_of_mem_erase (Finset.mem_filter.mp hu).1
        have hvU : v ∈ U := Finset.mem_of_mem_erase (Finset.mem_filter.mp hv).1
        have hne_u : v₀ ≠ u := (Finset.mem_erase.mp (Finset.mem_filter.mp hu).1).1.symm
        have hne_v : v₀ ≠ v := (Finset.mem_erase.mp (Finset.mem_filter.mp hv).1).1.symm
        exact ⟨col₀, v₀, u, v, hv₀, huU, hvU, hne_u, huv, hne_v,
          (Finset.mem_filter.mp hu).2, hcuv, (Finset.mem_filter.mp hv).2⟩
      · push Not at hhit
        -- Every pair in `W` avoids `col₀`, inducing an `r`-coloring of `W`
        let e : Fin r ↪ Fin (r + 1) := Fin.succAboveEmb col₀
        let cW : V → V → Fin r := fun u v =>
          if h : c u v = col₀ then ⟨0, by omega⟩
          else
            -- `c u v ≠ col₀` so it lies in the range of `col₀.succAbove`
            let idx := if c u v < col₀ then (c u v).1 else (c u v).1 - 1
            ⟨idx, by
              have hlt := (c u v).isLt
              by_cases hc : c u v < col₀
              · dsimp only [idx]; rw [if_pos hc]
                have hcollt := col₀.isLt
                have : (c u v).1 < col₀.1 := hc
                omega
              · dsimp only [idx]; rw [if_neg hc]
                have hgt : col₀.1 < (c u v).1 := by
                  have hle : col₀ ≤ c u v := not_lt.mp hc
                  have hne : (c u v).1 ≠ col₀.1 := fun heq => h (Fin.ext heq)
                  omega
                omega⟩
        have hsymmW : ∀ u v : V, cW u v = cW v u := by
          intro u v
          simp only [cW, hsymm u v]
        have hcW_inj : ∀ u ∈ W, ∀ v ∈ W, u ≠ v → ∀ a ∈ W, ∀ b ∈ W, a ≠ b →
            cW u v = cW a b → c u v = c a b := by
          intro u hu v hv huv a ha b hb hab heq
          have h1 : c u v ≠ col₀ := hhit u hu v hv huv
          have h2 : c a b ≠ col₀ := hhit a ha b hb hab
          simp only [cW, dif_neg h1, dif_neg h2, Fin.mk.injEq] at heq
          by_cases hlt1 : c u v < col₀ <;> by_cases hlt2 : c a b < col₀
          · simp only [if_pos hlt1, if_pos hlt2] at heq
            exact Fin.ext heq
          · simp only [if_pos hlt1, if_neg hlt2] at heq
            have hle2 : col₀.1 ≤ (c a b).1 := not_lt.mp hlt2
            have hne2 : (c a b).1 ≠ col₀.1 := fun h => h2 (Fin.ext h)
            have : (c u v).1 < col₀.1 := hlt1
            omega
          · simp only [if_neg hlt1, if_pos hlt2] at heq
            have hle1 : col₀.1 ≤ (c u v).1 := not_lt.mp hlt1
            have hne1 : (c u v).1 ≠ col₀.1 := fun h => h1 (Fin.ext h)
            have : (c a b).1 < col₀.1 := hlt2
            omega
          · simp only [if_neg hlt1, if_neg hlt2] at heq
            have hle1 : col₀.1 ≤ (c u v).1 := not_lt.mp hlt1
            have hne1 : (c u v).1 ≠ col₀.1 := fun h => h1 (Fin.ext h)
            have hle2 : col₀.1 ≤ (c a b).1 := not_lt.mp hlt2
            have hne2 : (c a b).1 ≠ col₀.1 := fun h => h2 (Fin.ext h)
            exact Fin.ext (by omega)
        obtain ⟨col', u, v, w, huW, hvW, hwW, huv, hvw, huw, h1, h2, h3⟩ :=
          ih hr1 W hcol₀_big cW hsymmW
        have hWsub : W ⊆ U := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
        refine ⟨c u v, u, v, w, hWsub huW, hWsub hvW, hWsub hwW, huv, hvw, huw, rfl, ?_, ?_⟩
        · exact (hcW_inj u huW v hvW huv v hvW w hwW hvw (h1.trans h2.symm)).symm
        · exact (hcW_inj u huW v hvW huv u huW w hwW huw (h1.trans h3.symm)).symm

/-- **Erdős (1947) Probabilistic Lower Bound (Exact Binomial Form):**
Whenever `2 * Nat.choose n k < 2 ^ Nat.choose k 2` (`k ≥ 2`), there exists a simple graph `G`
on `Fin n` having neither a `k`-clique nor a `k`-element independent set. -/
theorem ramsey_erdos_lower_binom {n k : ℕ} (_hk : 2 ≤ k)
    (hbinom : 2 * Nat.choose n k < 2 ^ Nat.choose k 2) :
    ∃ G : SimpleGraph (Fin n),
      (∀ S : Finset (Fin n), S.card = k → ¬ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) ∧
      (∀ T : Finset (Fin n), T.card = k → ¬ ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬ G.Adj u v) := by
  let Pairs : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 < p.2)
  -- Helper: cardinality of ordered increasing pairs in any `S : Finset (Fin n)` is `C(|S|, 2)`
  have hlt_pairs_card : ∀ S : Finset (Fin n),
      ((S ×ˢ S).filter (fun p => p.1 < p.2)).card = Nat.choose S.card 2 := by
    intro S
    let L := (S ×ˢ S).filter (fun p => p.1 < p.2)
    let R := (S ×ˢ S).filter (fun p => p.2 < p.1)
    let D := (S ×ˢ S).filter (fun p => p.1 = p.2)
    have hLR_eq : L.card = R.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp
        simp only [L, R, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p₁ _ p₂ _ h
        exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro p hp
        simp only [L, R, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨(p.2, p.1), ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩, rfl⟩
    have hD_card : D.card = S.card := by
      refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
      · intro p hp; exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      · intro p₁ hp₁ p₂ hp₂ h
        have h1 := (Finset.mem_filter.mp hp₁).2
        have h2 := (Finset.mem_filter.mp hp₂).2
        exact Prod.ext h (h1.symm.trans (h.trans h2))
      · intro x hx
        exact ⟨(x, x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hx⟩, rfl⟩, rfl⟩
    have hdisjLR : Disjoint L R := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have hdisjLRD : Disjoint (L ∪ R) D := by
      rw [Finset.disjoint_left]; intro p h1 h2
      have heq := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h1 with hL | hR
      · exact (Finset.mem_filter.mp hL).2.ne heq
      · exact (Finset.mem_filter.mp hR).2.ne heq.symm
    have hunion : L ∪ R ∪ D = S ×ˢ S := by
      ext p
      simp only [L, R, D, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((h | h) | h) <;> exact h.1
      · intro hp
        rcases lt_trichotomy p.1 p.2 with h | h | h
        · exact Or.inl (Or.inl ⟨hp, h⟩)
        · exact Or.inr ⟨hp, h⟩
        · exact Or.inl (Or.inr ⟨hp, h⟩)
    have htot : L.card + R.card + D.card = S.card * S.card := by
      rw [← Finset.card_union_of_disjoint hdisjLR, ← Finset.card_union_of_disjoint hdisjLRD,
          hunion, Finset.card_product]
    rw [Nat.choose_two_right]
    have hdvd : 2 ∣ S.card * (S.card - 1) := (Nat.even_mul_pred_self S.card).two_dvd
    have hmul : 2 * (S.card * (S.card - 1) / 2) = S.card * (S.card - 1) := Nat.mul_div_cancel' hdvd
    have hsq : S.card * (S.card - 1) + S.card = S.card * S.card := by
      cases hc : S.card with
      | zero => simp
      | succ m => simp [Nat.mul_succ]
    dsimp only [L] at htot hLR_eq
    omega
  -- Space of all 2-colorings `E : Pairs → Bool` has cardinality `2 ^ Pairs.card`
  let Bad (S : Finset (Fin n)) (b : Bool) : Finset (Pairs → Bool) :=
    Finset.univ.filter (fun E => ∀ p : Pairs, p.1.1 ∈ S → p.1.2 ∈ S → E p = b)
  -- For any `k`-subset `S` and color `b`, `|Bad S b| * 2 ^ C(k, 2) = 2 ^ Pairs.card`
  have hBad_card : ∀ (S : Finset (Fin n)), S.card = k → ∀ (b : Bool),
      (Bad S b).card * 2 ^ Nat.choose k 2 = 2 ^ Pairs.card := by
    intro S hScard b
    let SPairs : Finset Pairs := Finset.univ.filter (fun p : Pairs => p.1.1 ∈ S ∧ p.1.2 ∈ S)
    have hSPairs_card : SPairs.card = Nat.choose k 2 := by
      have hbij : SPairs.card = ((S ×ˢ S).filter (fun p => p.1 < p.2)).card := by
        refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
        · intro p hp
          have hmem := (Finset.mem_filter.mp hp).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr hmem, (Finset.mem_filter.mp p.2).2⟩
        · intro p₁ _ p₂ _ h; exact Subtype.ext h
        · intro p hp
          have h1 := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
          have h2 := (Finset.mem_filter.mp hp).2
          exact ⟨⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, rfl⟩
      rw [hbij, hlt_pairs_card S, hScard]
    -- Bijection `Bad S b ≃ (SPairsᶜ → Bool)`
    let eBad : Bad S b ≃ ({p : Pairs // p ∉ SPairs} → Bool) :=
      { toFun := fun E p => E.1 p.1
        invFun := fun f =>
          ⟨fun p => if h : p ∈ SPairs then b else f ⟨p, h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            intro p h1 h2
            have hp : p ∈ SPairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩
            simp [hp]⟩⟩
        left_inv := by
          intro ⟨E, hE⟩
          ext p
          by_cases hp : p ∈ SPairs
          · simp only [dif_pos hp]
            have hmem := (Finset.mem_filter.mp hp).2
            exact ((Finset.mem_filter.mp hE).2 p hmem.1 hmem.2).symm
          · simp [hp]
        right_inv := by
          intro f
          funext ⟨p, hp⟩
          simp [hp] }
    have hcard_bad : (Bad S b).card = 2 ^ (Pairs.card - SPairs.card) := by
      have h1 := Fintype.card_congr eBad
      rw [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool] at h1
      have hcompl : Fintype.card {p : Pairs // p ∉ SPairs} = Pairs.card - SPairs.card := by
        rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_coe]
      rw [hcompl] at h1
      exact h1
    have hle : SPairs.card ≤ Pairs.card := by
      have := Finset.card_le_univ SPairs
      simpa only [Fintype.card_coe] using this
    rw [hcard_bad, ← hSPairs_card, ← pow_add, Nat.sub_add_cancel hle]
  -- Union bound: total number of bad colorings is strictly less than `2 ^ Pairs.card`
  let AllBad : Finset (Pairs → Bool) :=
    ((Finset.univ : Finset (Fin n)).powersetCard k).biUnion (fun S => Bad S true ∪ Bad S false)
  have hAllBad_lt : AllBad.card < (Finset.univ : Finset (Pairs → Bool)).card := by
    have hmul_lt : AllBad.card * 2 ^ Nat.choose k 2 < 2 ^ Pairs.card * 2 ^ Nat.choose k 2 := by
      calc AllBad.card * 2 ^ Nat.choose k 2
          ≤ (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              ((Bad S true).card + (Bad S false).card)) * 2 ^ Nat.choose k 2 := by
            apply Nat.mul_le_mul_right
            calc AllBad.card
                ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (Bad S true ∪ Bad S false).card :=
                  Finset.card_biUnion_le
              _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ((Bad S true).card + (Bad S false).card) :=
                  Finset.sum_le_sum fun S _ => Finset.card_union_le _ _
        _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              ((Bad S true).card * 2 ^ Nat.choose k 2 + (Bad S false).card * 2 ^ Nat.choose k 2) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun S _ => add_mul _ _ _
        _ = ∑ _S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (2 * 2 ^ Pairs.card) := by
            apply Finset.sum_congr rfl
            intro S hS
            have hScard := (Finset.mem_powersetCard.mp hS).2
            rw [hBad_card S hScard true, hBad_card S hScard false, two_mul]
        _ = Nat.choose n k * (2 * 2 ^ Pairs.card) := by
            rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        _ = (2 * Nat.choose n k) * 2 ^ Pairs.card := by ring
        _ < 2 ^ Nat.choose k 2 * 2 ^ Pairs.card :=
            Nat.mul_lt_mul_of_pos_right hbinom (pow_pos (by omega) _)
        _ = 2 ^ Pairs.card * 2 ^ Nat.choose k 2 := mul_comm _ _
    have hlt : AllBad.card < 2 ^ Pairs.card :=
      Nat.lt_of_mul_lt_mul_right hmul_lt
    simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using hlt
  have hne : (Finset.univ \ AllBad).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : (Finset.univ : Finset (Pairs → Bool)) ⊆ AllBad := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  obtain ⟨E, hE_mem⟩ := hne
  have hE_notBad : E ∉ AllBad := (Finset.mem_sdiff.mp hE_mem).2
  -- Build the graph `G` from `E`
  let G : SimpleGraph (Fin n) :=
    { Adj := fun u v =>
        if h1 : u < v then E ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩ = true
        else if h2 : v < u then E ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩ = true
        else False
      symm := ⟨by
        intro u v h
        by_cases h1 : u < v
        · have h2 : ¬ v < u := not_lt.mpr h1.le
          simp only [dif_pos h1] at h
          simp only [dif_neg h2, dif_pos h1]
          exact h
        · by_cases h2 : v < u
          · simp only [dif_neg h1, dif_pos h2] at h
            simp only [dif_pos h2]
            exact h
          · simp only [dif_neg h1, dif_neg h2] at h⟩
      loopless := ⟨fun u h => by simp at h⟩ }
  refine ⟨G, ?_, ?_⟩
  · intro S hScard hclique
    apply hE_notBad
    refine Finset.mem_biUnion.mpr ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hScard⟩,
      Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)⟩
    intro p h1 h2
    have hlt : p.1.1 < p.1.2 := (Finset.mem_filter.mp p.2).2
    have hadj := hclique p.1.1 h1 p.1.2 h2 (ne_of_lt hlt)
    simpa [G, dif_pos hlt] using hadj
  · intro T hTcard hindep
    apply hE_notBad
    refine Finset.mem_biUnion.mpr ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTcard⟩,
      Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)⟩
    intro p h1 h2
    have hlt : p.1.1 < p.1.2 := (Finset.mem_filter.mp p.2).2
    have hnadj := hindep p.1.1 h1 p.1.2 h2 (ne_of_lt hlt)
    have hne_true : E p ≠ true := by
      intro heq; apply hnadj; simpa [G, dif_pos hlt] using heq
    cases hval : E p
    · rfl
    · exact absurd hval hne_true

/-- **Erdős (1947) Exponential Lower Bound `R(k, k) > 2^{k/2}`:**
For every `k ≥ 3` and every `n : ℕ` with `(n : ℝ) ≤ 2^{k/2}`, there exists a simple graph `G`
on `Fin n` with no `k`-clique and no `k`-element independent set. -/
theorem ramsey_erdos_lower {k n : ℕ} (hk : 3 ≤ k) (hn : (n : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) / 2)) :
    ∃ G : SimpleGraph (Fin n),
      (∀ S : Finset (Fin n), S.card = k → ¬ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) ∧
      (∀ T : Finset (Fin n), T.card = k → ¬ ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬ G.Adj u v) := by
  apply ramsey_erdos_lower_binom (by omega)
  by_cases hk3 : k = 3
  · subst hk3
    have hn_lt3 : n < 3 := by
      by_contra hge
      push Not at hge
      have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hge
      have hsq : (3 : ℝ) ^ 2 ≤ ((2 : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 :=
        pow_le_pow_left₀ (by norm_num) (h3.trans hn) 2
      have h2pow : ((2 : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ (3 : ℕ) := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [h2pow] at hsq
      norm_num at hsq
    rw [Nat.choose_eq_zero_of_lt hn_lt3]
    norm_num
  · have hk4 : 4 ≤ k := by omega
    -- Prove `2 ^ (k + 2) < (k!)^2` for all `k ≥ 4` by induction
    have hfac_sq : ∀ m : ℕ, 4 ≤ m → 2 ^ (m + 2) < (Nat.factorial m) ^ 2 := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => norm_num [Nat.factorial]
      | succ m hm ih =>
        rw [Nat.factorial_succ, mul_pow]
        have h1 : 2 ^ (m + 1 + 2) = 2 * 2 ^ (m + 2) := by ring
        rw [h1]
        calc 2 * 2 ^ (m + 2) < 2 * (Nat.factorial m) ^ 2 := Nat.mul_lt_mul_of_pos_left ih (by omega)
          _ ≤ (m + 1) ^ 2 * (Nat.factorial m) ^ 2 :=
              Nat.mul_le_mul_right _ (by nlinarith)
    -- Also `k! * C(n, k) ≤ n ^ k`
    have hchoose_fac : Nat.factorial k * Nat.choose n k ≤ n ^ k := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow n k
    -- Square both sides of `(n : ℝ) ≤ 2 ^ (k / 2)` to get `n ^ 2 ≤ 2 ^ k`
    have hn_sq : n ^ 2 ≤ 2 ^ k := by
      have h1 : ((n : ℝ) ^ 2) ≤ ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg n) hn 2
      have h2 : ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ k := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num)]
        have : (k : ℝ) / 2 * (2 : ℕ) = (k : ℝ) := by push_cast; ring
        rw [this, Real.rpow_natCast]
      rw [h2] at h1
      exact_mod_cast h1
    -- Therefore `(k! * C(n, k))^2 ≤ (n^k)^2 = (n^2)^k ≤ 2^(k^2)`
    have hLHS_sq : (Nat.factorial k * Nat.choose n k) ^ 2 ≤ 2 ^ (k * k) := by
      calc (Nat.factorial k * Nat.choose n k) ^ 2
          ≤ (n ^ k) ^ 2 := Nat.pow_le_pow_left hchoose_fac 2
        _ = (n ^ 2) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left hn_sq k
        _ = 2 ^ (k * k) := by rw [← pow_mul]
    have h2choose2 : 2 * Nat.choose k 2 + k = k * k := by
      rw [Nat.choose_two_right]
      have hdvd : 2 ∣ k * (k - 1) := Nat.even_mul_pred_self k |>.two_dvd
      have hmul := Nat.mul_div_cancel' hdvd
      zify [show 1 ≤ k by omega] at hmul ⊢
      linarith
    -- Combine: `(2 * k! * C(n, k))^2 ≤ 4 * 2^(k^2) = 2^(k+2) * 2^(2 * C(k, 2)) < (k!)^2 * (2^C(k, 2))^2`
    have hsq_strict : (2 * Nat.choose n k * Nat.factorial k) ^ 2 <
        (2 ^ Nat.choose k 2 * Nat.factorial k) ^ 2 := by
      calc (2 * Nat.choose n k * Nat.factorial k) ^ 2
          = 2 ^ 2 * (Nat.factorial k * Nat.choose n k) ^ 2 := by ring
        _ ≤ 2 ^ 2 * 2 ^ (k * k) := Nat.mul_le_mul_left _ hLHS_sq
        _ = 2 ^ (k + 2) * (2 ^ Nat.choose k 2) ^ 2 := by
            rw [← pow_mul, mul_comm (Nat.choose k 2) 2, ← pow_add, ← pow_add]
            have hexp : 2 + k * k = k + 2 + 2 * Nat.choose k 2 := by linarith
            rw [hexp]
        _ < (Nat.factorial k) ^ 2 * (2 ^ Nat.choose k 2) ^ 2 :=
            Nat.mul_lt_mul_of_pos_right (hfac_sq k hk4) (pow_pos (pow_pos (by omega) _) _)
        _ = (2 ^ Nat.choose k 2 * Nat.factorial k) ^ 2 := by ring
    have hlt_fac : 2 * Nat.choose n k * Nat.factorial k < 2 ^ Nat.choose k 2 * Nat.factorial k := by
      by_contra hge
      push Not at hge
      have := Nat.pow_le_pow_left hge 2
      omega
    exact Nat.lt_of_mul_lt_mul_right hlt_fac

end RamseyTheorems

/-! ## Section 2: Schur's Theorem (`S(r) ≤ 3 * r!`) -/

section SchurTheorem

/-- **Schur's Theorem (`S(r) ≤ 3 * r! - 1`):**
For every `r ≥ 1`, every `N ≥ 3 * r! - 1` (in particular `N = 3 * r!`), and every `r`-coloring
`c : ℕ → Fin r`, there exist positive integers `1 ≤ x, 1 ≤ y` with `x + y ≤ N` such that
`x`, `y`, and `x + y` all receive the same color. -/
theorem schur_theorem {r N : ℕ} (hr : 1 ≤ r) (hN : 3 * Nat.factorial r - 1 ≤ N)
    (c : ℕ → Fin r) :
    ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ y ∧ z ≤ N ∧ x + y = z ∧ c x = c y ∧ c y = c z := by
  let M : ℕ := 3 * Nat.factorial r
  let edgeCol : Fin M → Fin M → Fin r := fun a b =>
    if a.1 ≤ b.1 then c (b.1 - a.1) else c (a.1 - b.1)
  have hsymm : ∀ a b : Fin M, edgeCol a b = edgeCol b a := by
    intro a b
    dsimp only [edgeCol]
    by_cases h1 : a.1 ≤ b.1
    · by_cases h2 : b.1 ≤ a.1
      · have heq : a.1 = b.1 := le_antisymm h1 h2
        simp [heq]
      · simp [h1, h2]
    · have h2 : b.1 ≤ a.1 := le_of_not_ge h1
      simp [h1, h2]
  have hcard : 3 * Nat.factorial r ≤ (Finset.univ : Finset (Fin M)).card := by simp [M]
  obtain ⟨col, u, v, w, _, _, _, huv, hvw, huw, h1, h2, h3⟩ :=
    ramsey_uniform_three_finset r hr Finset.univ hcard edgeCol hsymm
  -- Sort the 3 distinct vertices `u, v, w` as `a < b < d`
  have hsort : ∃ a b d : Fin M, a.1 < b.1 ∧ b.1 < d.1 ∧
      edgeCol a b = col ∧ edgeCol b d = col ∧ edgeCol a d = col := by
    have hne_uv : u.1 ≠ v.1 := fun h => huv (Fin.ext h)
    have hne_vw : v.1 ≠ w.1 := fun h => hvw (Fin.ext h)
    have hne_uw : u.1 ≠ w.1 := fun h => huw (Fin.ext h)
    rcases lt_or_gt_of_ne hne_uv with h_uv | h_vu
    · rcases lt_or_gt_of_ne hne_vw with h_vw | h_wv
      · exact ⟨u, v, w, h_uv, h_vw, h1, h2, h3⟩
      · rcases lt_or_gt_of_ne hne_uw with h_uw | h_wu
        · exact ⟨u, w, v, h_uw, h_wv, h3, (hsymm w v).trans h2, h1⟩
        · exact ⟨w, u, v, h_wu, h_uv, (hsymm w u).trans h3, h1, (hsymm w v).trans h2⟩
    · rcases lt_or_gt_of_ne hne_uw with h_uw | h_wu
      · exact ⟨v, u, w, h_vu, h_uw, (hsymm v u).trans h1, h3, h2⟩
      · rcases lt_or_gt_of_ne hne_vw with h_vw | h_wv
        · exact ⟨v, w, u, h_vw, h_wu, h2, (hsymm w u).trans h3, (hsymm v u).trans h1⟩
        · exact ⟨w, v, u, h_wv, h_vu, (hsymm w v).trans h2, (hsymm v u).trans h1, (hsymm w u).trans h3⟩
  rcases hsort with ⟨a, b, d, hab, hbd, h_ab, h_bd, h_ad⟩
  refine ⟨b.1 - a.1, d.1 - b.1, d.1 - a.1, by omega, by omega, ?_, by omega, ?_, ?_⟩
  · have hdlt : d.1 < 3 * Nat.factorial r := d.isLt
    omega
  · simp only [edgeCol, if_pos hab.le] at h_ab
    simp only [edgeCol, if_pos hbd.le] at h_bd
    exact h_ab.trans h_bd.symm
  · simp only [edgeCol, if_pos hbd.le] at h_bd
    simp only [edgeCol, if_pos (hab.trans hbd).le] at h_ad
    exact h_bd.trans h_ad.symm

end SchurTheorem

/-! ## Section 3: Erdős–Szekeres Monotone Subsequence & Happy Ending Convex `n`-Gon Theorems -/

section ErdosSzekeres

/-- **Erdős–Szekeres Monotone Subsequence Theorem (Seidenberg Pigeonhole Proof):**
Every sequence `f : Fin (a * b + 1) → α` in any linear order `α` contains either a
nondecreasing subsequence of length `a + 1` or a strictly decreasing subsequence of length `b + 1`. -/
theorem erdos_szekeres_monotone {α : Type*} [LinearOrder α] (a b : ℕ)
    (f : Fin (a * b + 1) → α) :
    (∃ s : Fin (a + 1) → Fin (a * b + 1), StrictMono s ∧ Monotone (f ∘ s)) ∨
    (∃ t : Fin (b + 1) → Fin (a * b + 1), StrictMono t ∧ StrictAnti (f ∘ t)) := by
  by_cases ha0 : a = 0
  · subst ha0
    left
    refine ⟨fun _ => ⟨0, by omega⟩, fun i j hij => by omega, fun i j _ => le_rfl⟩
  by_cases hb0 : b = 0
  · subst hb0
    right
    refine ⟨fun _ => ⟨0, by omega⟩, fun i j hij => by omega, fun i j hij => by omega⟩
  -- For each `i`, define the longest nondecreasing / strictly decreasing chain ending at `i`
  let IncEnds (i : Fin (a * b + 1)) (L : ℕ) : Prop :=
    ∃ s : Fin L → Fin (a * b + 1), StrictMono s ∧ Monotone (f ∘ s) ∧
      ∃ hL : 0 < L, s ⟨L - 1, by omega⟩ = i
  let DecEnds (i : Fin (a * b + 1)) (L : ℕ) : Prop :=
    ∃ t : Fin L → Fin (a * b + 1), StrictMono t ∧ StrictAnti (f ∘ t) ∧
      ∃ hL : 0 < L, t ⟨L - 1, by omega⟩ = i
  by_contra hnone
  push Not at hnone
  rcases hnone with ⟨hno_inc, hno_dec⟩
  have hInc1 : ∀ i, IncEnds i 1 := fun i =>
    ⟨fun _ => i, fun u v h => by omega, fun _ _ _ => le_rfl, by omega, rfl⟩
  have hDec1 : ∀ i, DecEnds i 1 := fun i =>
    ⟨fun _ => i, fun u v h => by omega, fun u v h => by omega, by omega, rfl⟩
  -- No chain has length `> a` (resp. `> b`)
  have hInc_le : ∀ i L, IncEnds i L → L ≤ a := by
    intro i L ⟨s, hs_mono, hf_mono, _, _⟩
    by_contra hgt
    push Not at hgt
    let s' : Fin (a + 1) → Fin (a * b + 1) := fun k => s ⟨k.1, by omega⟩
    exact hno_inc s' (fun u v huv => hs_mono (by exact huv)) (fun u v huv => hf_mono (by exact huv))
  have hDec_le : ∀ i L, DecEnds i L → L ≤ b := by
    intro i L ⟨t, ht_mono, hf_anti, _, _⟩
    by_contra hgt
    push Not at hgt
    let t' : Fin (b + 1) → Fin (a * b + 1) := fun k => t ⟨k.1, by omega⟩
    exact hno_dec t' (fun u v huv => ht_mono (by exact huv)) (fun u v huv => hf_anti (by exact huv))
  -- Define `maxInc i ∈ Fin a` and `maxDec i ∈ Fin b`
  let incSet (i : Fin (a * b + 1)) : Finset ℕ := (Finset.range (a + 1)).filter (IncEnds i)
  let decSet (i : Fin (a * b + 1)) : Finset ℕ := (Finset.range (b + 1)).filter (DecEnds i)
  have hinc_ne : ∀ i, (incSet i).Nonempty := fun i =>
    ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hInc1 i⟩⟩
  have hdec_ne : ∀ i, (decSet i).Nonempty := fun i =>
    ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hDec1 i⟩⟩
  let maxInc (i : Fin (a * b + 1)) : ℕ := (incSet i).max' (hinc_ne i)
  let maxDec (i : Fin (a * b + 1)) : ℕ := (decSet i).max' (hdec_ne i)
  have hmaxInc_spec : ∀ i, IncEnds i (maxInc i) ∧ 1 ≤ maxInc i ∧ maxInc i ≤ a := by
    intro i
    have hmem := Finset.max'_mem (incSet i) (hinc_ne i)
    have hinc := (Finset.mem_filter.mp hmem).2
    have hge1 : 1 ≤ maxInc i := Finset.le_max' (incSet i) 1
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hInc1 i⟩)
    exact ⟨hinc, hge1, hInc_le i _ hinc⟩
  have hmaxDec_spec : ∀ i, DecEnds i (maxDec i) ∧ 1 ≤ maxDec i ∧ maxDec i ≤ b := by
    intro i
    have hmem := Finset.max'_mem (decSet i) (hdec_ne i)
    have hdec := (Finset.mem_filter.mp hmem).2
    have hge1 : 1 ≤ maxDec i := Finset.le_max' (decSet i) 1
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hDec1 i⟩)
    exact ⟨hdec, hge1, hDec_le i _ hdec⟩
  -- Label map `i ↦ (maxInc i - 1, maxDec i - 1) : Fin a × Fin b` is injective!
  let label : Fin (a * b + 1) → Fin a × Fin b := fun i =>
    (⟨maxInc i - 1, by have := (hmaxInc_spec i).2; omega⟩,
     ⟨maxDec i - 1, by have := (hmaxDec_spec i).2; omega⟩)
  have hinj : Function.Injective label := by
    intro i j heq
    by_contra hne
    have hlt_or : ∀ u v : Fin (a * b + 1), u < v → label u ≠ label v := by
      intro u v huv hlbl
      have hIncEq : maxInc u = maxInc v := by
        have h1 := congrArg (fun p => p.1.1) hlbl
        dsimp only [label] at h1
        have := (hmaxInc_spec u).2.1
        have := (hmaxInc_spec v).2.1
        omega
      have hDecEq : maxDec u = maxDec v := by
        have h1 := congrArg (fun p => p.2.1) hlbl
        dsimp only [label] at h1
        have := (hmaxDec_spec u).2.1
        have := (hmaxDec_spec v).2.1
        omega
      by_cases hfv : f u ≤ f v
      · -- Extend the longest nondecreasing chain ending at `u` by appending `v`
        set L := maxInc u
        rcases (hmaxInc_spec u).1 with ⟨s, hs_mono, hf_mono, hLpos, hsend⟩
        let s' : Fin (L + 1) → Fin (a * b + 1) := fun k =>
          if hk : k.1 < L then s ⟨k.1, hk⟩ else v
        have hs'_mono : StrictMono s' := by
          intro x y hxy
          dsimp only [s']
          by_cases hy : y.1 < L
          · have hx : x.1 < L := lt_trans hxy hy
            simp only [dif_pos hx, dif_pos hy]
            exact hs_mono (show (⟨x.1, hx⟩ : Fin L) < ⟨y.1, hy⟩ from hxy)
          · have hx : x.1 < L := by have := y.isLt; omega
            simp only [dif_pos hx, dif_neg hy]
            have hle : s ⟨x.1, hx⟩ ≤ s ⟨L - 1, by omega⟩ :=
              hs_mono.monotone (show (⟨x.1, hx⟩ : Fin L) ≤ ⟨L - 1, by omega⟩ from by simp; omega)
            rw [hsend] at hle
            exact lt_of_le_of_lt hle huv
        have hf'_mono : Monotone (f ∘ s') := by
          intro x y hxy
          simp only [Function.comp, s']
          by_cases hy : y.1 < L
          · have hx : x.1 < L := lt_of_le_of_lt hxy hy
            simp only [dif_pos hx, dif_pos hy]
            exact hf_mono (show (⟨x.1, hx⟩ : Fin L) ≤ ⟨y.1, hy⟩ from hxy)
          · by_cases hx : x.1 < L
            · simp only [dif_pos hx, dif_neg hy]
              have hle : f (s ⟨x.1, hx⟩) ≤ f (s ⟨L - 1, by omega⟩) :=
                hf_mono (show (⟨x.1, hx⟩ : Fin L) ≤ ⟨L - 1, by omega⟩ from by simp; omega)
              rw [hsend] at hle
              exact hle.trans hfv
            · simp only [dif_neg hx, dif_neg hy]; exact le_rfl
        have hInc_v : IncEnds v (L + 1) := ⟨s', hs'_mono, hf'_mono, by omega, by simp [s']⟩
        have hL1_le : L + 1 ≤ a := hInc_le v (L + 1) hInc_v
        have hmax_ge : L + 1 ≤ maxInc v := Finset.le_max' (incSet v) (L + 1)
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hInc_v⟩)
        omega
      · -- `f v < f u`: extend the longest strictly decreasing chain ending at `u` by appending `v`
        have hfu : f v < f u := lt_of_not_ge hfv
        set L := maxDec u
        rcases (hmaxDec_spec u).1 with ⟨t, ht_mono, hf_anti, hLpos, htend⟩
        let t' : Fin (L + 1) → Fin (a * b + 1) := fun k =>
          if hk : k.1 < L then t ⟨k.1, hk⟩ else v
        have ht'_mono : StrictMono t' := by
          intro x y hxy
          dsimp only [t']
          by_cases hy : y.1 < L
          · have hx : x.1 < L := lt_trans hxy hy
            simp only [dif_pos hx, dif_pos hy]
            exact ht_mono (show (⟨x.1, hx⟩ : Fin L) < ⟨y.1, hy⟩ from hxy)
          · have hx : x.1 < L := by have := y.isLt; omega
            simp only [dif_pos hx, dif_neg hy]
            have hle : t ⟨x.1, hx⟩ ≤ t ⟨L - 1, by omega⟩ :=
              ht_mono.monotone (show (⟨x.1, hx⟩ : Fin L) ≤ ⟨L - 1, by omega⟩ from by simp; omega)
            rw [htend] at hle
            exact lt_of_le_of_lt hle huv
        have hf'_anti : StrictAnti (f ∘ t') := by
          intro x y hxy
          simp only [Function.comp, t']
          by_cases hy : y.1 < L
          · have hx : x.1 < L := lt_trans hxy hy
            simp only [dif_pos hx, dif_pos hy]
            exact hf_anti (show (⟨x.1, hx⟩ : Fin L) < ⟨y.1, hy⟩ from hxy)
          · have hx : x.1 < L := by have := y.isLt; omega
            simp only [dif_pos hx, dif_neg hy]
            have hge : f (t ⟨L - 1, by omega⟩) ≤ f (t ⟨x.1, hx⟩) :=
              hf_anti.antitone (show (⟨x.1, hx⟩ : Fin L) ≤ ⟨L - 1, by omega⟩ from by simp; omega)
            rw [htend] at hge
            exact lt_of_lt_of_le hfu hge
        have hDec_v : DecEnds v (L + 1) := ⟨t', ht'_mono, hf'_anti, by omega, by simp [t']⟩
        have hL1_le : L + 1 ≤ b := hDec_le v (L + 1) hDec_v
        have hmax_ge : L + 1 ≤ maxDec v := Finset.le_max' (decSet v) (L + 1)
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hDec_v⟩)
        omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hlt_or i j hlt heq
    · exact hlt_or j i hgt heq.symm
  have hcard := Fintype.card_le_of_injective label hinj
  simp only [Fintype.card_fin, Fintype.card_prod] at hcard
  omega

/-- **Tightness of Erdős–Szekeres (`a * b` extremal witness):**
For all `a, b : ℕ`, there exists an injective sequence `f : Fin (a * b) → ℕ` having no
monotone subsequence of length `a + 1` and no antitone subsequence of length `b + 1`. -/
theorem erdos_szekeres_monotone_tight (a b : ℕ) :
    ∃ f : Fin (a * b) → ℕ,
      Function.Injective f ∧
      (∀ s : Fin (a + 1) → Fin (a * b), StrictMono s → ¬ Monotone (f ∘ s)) ∧
      (∀ t : Fin (b + 1) → Fin (a * b), StrictMono t → ¬ Antitone (f ∘ t)) := by
  by_cases hb0 : b = 0
  · subst hb0
    refine ⟨fun i => Fin.elim0 (by simpa using i), fun i => Fin.elim0 (by simpa using i),
      fun s _ _ => Fin.elim0 (by simpa using s ⟨0, by omega⟩),
      fun t _ _ => Fin.elim0 (by simpa using t ⟨0, by omega⟩)⟩
  have hb_pos : 0 < b := Nat.pos_of_ne_zero hb0
  let f : Fin (a * b) → ℕ := fun k => (k.1 / b) * b + (b - 1 - k.1 % b)
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hi_mod : i.1 % b < b := Nat.mod_lt i.1 hb_pos
    have hj_mod : j.1 % b < b := Nat.mod_lt j.1 hb_pos
    have hdiv : i.1 / b = j.1 / b := by
      have h1 : f i / b = i.1 / b := by
        dsimp only [f]
        rw [add_comm, Nat.add_mul_div_right _ _ hb_pos, Nat.div_eq_of_lt (by omega), zero_add]
      have h2 : f j / b = j.1 / b := by
        dsimp only [f]
        rw [add_comm, Nat.add_mul_div_right _ _ hb_pos, Nat.div_eq_of_lt (by omega), zero_add]
      rw [← h1, ← h2, hij]
    dsimp only [f] at hij
    have hmod : i.1 % b = j.1 % b := by
      rw [hdiv] at hij
      omega
    have hi_rec := Nat.div_add_mod i.1 b
    have hj_rec := Nat.div_add_mod j.1 b
    exact Fin.ext (by rw [← hi_rec, ← hj_rec, hdiv, hmod])
  refine ⟨f, hf_inj, ?_, ?_⟩
  · -- Any monotone subsequence hits each block `k / b ∈ Fin a` at most once
    intro s hs_mono hf_mono
    let blk : Fin (a + 1) → Fin a := fun r =>
      ⟨(s r).1 / b, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq (s r).isLt (mul_comm a b))⟩
    have hblk_inj : Function.Injective blk := by
      intro x y hxy
      by_contra hne
      have hlt_contra : ∀ u v : Fin (a + 1), u < v → (s u).1 / b ≠ (s v).1 / b := by
        intro u v huv hdiv
        have hsuv : (s u).1 < (s v).1 := hs_mono huv
        have hmod_lt : (s u).1 % b < (s v).1 % b := by
          have hu_rec := Nat.div_add_mod (s u).1 b
          have hv_rec := Nat.div_add_mod (s v).1 b
          rw [hdiv] at hu_rec
          omega
        have hu_mod : (s u).1 % b < b := Nat.mod_lt _ hb_pos
        have hv_mod : (s v).1 % b < b := Nat.mod_lt _ hb_pos
        have hf_le : f (s u) ≤ f (s v) := hf_mono huv.le
        dsimp only [f] at hf_le
        rw [hdiv] at hf_le
        omega
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hlt_contra x y hlt (congrArg Fin.val hxy)
      · exact hlt_contra y x hgt (congrArg Fin.val hxy.symm)
    have hcard := Fintype.card_le_of_injective blk hblk_inj
    simp only [Fintype.card_fin] at hcard
    omega
  · -- Any antitone subsequence stays inside a single block, so hits distinct residues `mod b`
    intro t ht_mono hf_anti
    let res : Fin (b + 1) → Fin b := fun r => ⟨(t r).1 % b, Nat.mod_lt _ hb_pos⟩
    have hres_inj : Function.Injective res := by
      intro x y hxy
      by_contra hne
      have hlt_contra : ∀ u v : Fin (b + 1), u < v → (t u).1 % b ≠ (t v).1 % b := by
        intro u v huv hmod
        have htuv : (t u).1 < (t v).1 := ht_mono huv
        have hdiv_lt : (t u).1 / b < (t v).1 / b := by
          have hu_rec := Nat.div_add_mod (t u).1 b
          have hv_rec := Nat.div_add_mod (t v).1 b
          by_contra hge
          push Not at hge
          have hmul : b * ((t v).1 / b) ≤ b * ((t u).1 / b) := Nat.mul_le_mul_left b hge
          omega
        have hf_ge : f (t v) ≤ f (t u) := hf_anti huv.le
        dsimp only [f] at hf_ge
        rw [hmod] at hf_ge
        have hmul_lt : (t u).1 / b * b < (t v).1 / b * b := Nat.mul_lt_mul_of_pos_right hdiv_lt hb_pos
        omega
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hlt_contra x y hlt (congrArg Fin.val hxy)
      · exact hlt_contra y x hgt (congrArg Fin.val hxy.symm)
    have hcard := Fintype.card_le_of_injective res hres_inj
    simp only [Fintype.card_fin] at hcard
    omega

/-! ### Erdős–Szekeres Happy Ending Convex `n`-Gon Theorem (`C(2n - 4, n - 2) + 1`) -/

/-- A finite set of points in `ℝ²` is in **general position** if no three distinct points are
collinear. -/
def InGeneralPosition (S : Finset (ℝ × ℝ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r →
    (q.1 - p.1) * (r.2 - p.2) ≠ (q.2 - p.2) * (r.1 - p.1)

/-- A finite set of points in `ℝ²` is in **convex position** if no point belongs to the convex
hull of the remaining points. -/
def InConvexPosition (T : Finset (ℝ × ℝ)) : Prop :=
  ∀ p ∈ T, p ∉ convexHull ℝ ((T.erase p : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))

/-- A `k`-cup in `S` is a sequence `p : Fin k → ℝ × ℝ` in `S` with strictly increasing
`x`-coordinates and strictly increasing consecutive slopes. -/
private def IsCup (S : Finset (ℝ × ℝ)) {k : ℕ} (p : Fin k → ℝ × ℝ) : Prop :=
  (∀ i : Fin k, p i ∈ S) ∧
  (∀ i j : Fin k, i < j → (p i).1 < (p j).1) ∧
  (∀ (i : ℕ) (h : i + 2 < k),
    ((p ⟨i + 1, by omega⟩).2 - (p ⟨i, by omega⟩).2) / ((p ⟨i + 1, by omega⟩).1 - (p ⟨i, by omega⟩).1) <
    ((p ⟨i + 2, h⟩).2 - (p ⟨i + 1, by omega⟩).2) / ((p ⟨i + 2, h⟩).1 - (p ⟨i + 1, by omega⟩).1))

/-- A `k`-cap in `S` is a sequence `p : Fin k → ℝ × ℝ` in `S` with strictly increasing
`x`-coordinates and strictly decreasing consecutive slopes. -/
private def IsCap (S : Finset (ℝ × ℝ)) {k : ℕ} (p : Fin k → ℝ × ℝ) : Prop :=
  (∀ i : Fin k, p i ∈ S) ∧
  (∀ i j : Fin k, i < j → (p i).1 < (p j).1) ∧
  (∀ (i : ℕ) (h : i + 2 < k),
    ((p ⟨i + 2, h⟩).2 - (p ⟨i + 1, by omega⟩).2) / ((p ⟨i + 2, h⟩).1 - (p ⟨i + 1, by omega⟩).1) <
    ((p ⟨i + 1, by omega⟩).2 - (p ⟨i, by omega⟩).2) / ((p ⟨i + 1, by omega⟩).1 - (p ⟨i, by omega⟩).1))

/-- Helper: sort a `Finset (ℝ × ℝ)` of size `k` with pairwise distinct `x`-coordinates into a
strictly `x`-increasing sequence `p : Fin k → ℝ × ℝ` in `S`. -/
private lemma exists_xSorted_seq {k : ℕ} {S : Finset (ℝ × ℝ)}
    (hxdist : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → p.1 ≠ q.1) (hcard : k ≤ S.card) :
    ∃ p : Fin k → ℝ × ℝ, (∀ i : Fin k, p i ∈ S) ∧ (∀ i j : Fin k, i < j → (p i).1 < (p j).1) := by
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq hcard
  have hinj : Set.InjOn Prod.fst (S' : Set (ℝ × ℝ)) := by
    intro a ha b hb heq
    by_contra hne
    exact hxdist a (hS'sub ha) b (hS'sub hb) hne heq
  let X : Finset ℝ := S'.image Prod.fst
  have hXcard : X.card = k := by rw [Finset.card_image_of_injOn hinj, hS'card]
  let l : List ℝ := X.sort (· ≤ ·)
  have hlen : l.length = k := by rw [Finset.length_sort, hXcard]
  have hnodup : l.Nodup := Finset.sort_nodup _ _
  have hsorted : l.Pairwise (· ≤ ·) := Finset.pairwise_sort X (· ≤ ·)
  have hex_pt : ∀ i : Fin k, ∃ pt ∈ S', pt.1 = l[i.1]'(by omega) := by
    intro i
    have hxmem : l[i.1]'(by omega) ∈ X := (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem _)
    exact Finset.mem_image.mp hxmem
  let p : Fin k → ℝ × ℝ := fun i => Classical.choose (hex_pt i)
  refine ⟨p, fun i => hS'sub (Classical.choose_spec (hex_pt i)).1, ?_⟩
  intro i j hij
  have hpi : (p i).1 = l[i.1]'(by omega) := (Classical.choose_spec (hex_pt i)).2
  have hpj : (p j).1 = l[j.1]'(by omega) := (Classical.choose_spec (hex_pt j)).2
  rw [hpi, hpj]
  have hle : l[i.1]'(by omega) ≤ l[j.1]'(by omega) :=
    List.pairwise_iff_getElem.mp hsorted i.1 j.1 (by omega) (by omega) hij
  have hne : l[i.1]'(by omega) ≠ l[j.1]'(by omega) := by
    intro heq
    have hfin : (⟨i.1, by omega⟩ : Fin l.length) = ⟨j.1, by omega⟩ :=
      (List.nodup_iff_injective_getElem.mp hnodup) heq
    exact ne_of_lt hij (Fin.ext (by simpa using congrArg Fin.val hfin))
  exact lt_of_le_of_ne hle hne

/-- **Erdős–Szekeres Cups-and-Caps Theorem:**
For all `r, s ≥ 3`, any finite set `S ⊆ ℝ²` of at least `Nat.choose (r + s - 4) (r - 2) + 1`
points in general position with pairwise distinct `x`-coordinates contains either an `r`-cup or
an `s`-cap. -/
private theorem cups_and_caps_core :
    ∀ (m r s : ℕ), r + s = m → 3 ≤ r → 3 ≤ s →
      ∀ (S : Finset (ℝ × ℝ)), InGeneralPosition S →
        (∀ p ∈ S, ∀ q ∈ S, p ≠ q → p.1 ≠ q.1) →
        Nat.choose (r + s - 4) (r - 2) + 1 ≤ S.card →
        (∃ p : Fin r → ℝ × ℝ, IsCup S p) ∨ (∃ q : Fin s → ℝ × ℝ, IsCap S q) := by
  intro m
  induction m with
  | zero => intro r s hrs hr; omega
  | succ m ih =>
    intro r s hrs hr hs S hgen hxdist hcard
    by_cases hr3 : r = 3
    · subst hr3
      have hcard_s : s ≤ S.card := by
        have h1 : Nat.choose (3 + s - 4) (3 - 2) = s - 1 := by
          have : 3 + s - 4 = s - 1 := by omega
          rw [this, show 3 - 2 = 1 by rfl, Nat.choose_one_right]
        omega
      obtain ⟨q, hq_mem, hq_xmono⟩ := exists_xSorted_seq hxdist hcard_s
      by_cases hcup : ∃ (i : ℕ) (h : i + 2 < s),
          ((q ⟨i + 1, by omega⟩).2 - (q ⟨i, by omega⟩).2) / ((q ⟨i + 1, by omega⟩).1 - (q ⟨i, by omega⟩).1) <
          ((q ⟨i + 2, h⟩).2 - (q ⟨i + 1, by omega⟩).2) / ((q ⟨i + 2, h⟩).1 - (q ⟨i + 1, by omega⟩).1)
      · rcases hcup with ⟨i, hi, hlt⟩
        left
        let p : Fin 3 → ℝ × ℝ := fun j => q ⟨i + j.1, by omega⟩
        refine ⟨p, fun j => hq_mem _, fun u v huv => hq_xmono _ _ (show i + u.1 < i + v.1 by have : u.1 < v.1 := huv; omega), ?_⟩
        intro idx hidx
        have hidx0 : idx = 0 := by omega
        subst hidx0
        simpa [p] using hlt
      · push Not at hcup
        right
        refine ⟨q, hq_mem, hq_xmono, ?_⟩
        intro i hi
        have hle := hcup i hi
        have hdx1 : 0 < (q ⟨i + 1, by omega⟩).1 - (q ⟨i, by omega⟩).1 :=
          sub_pos.mpr (hq_xmono ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (by simp))
        have hdx2 : 0 < (q ⟨i + 2, hi⟩).1 - (q ⟨i + 1, by omega⟩).1 :=
          sub_pos.mpr (hq_xmono ⟨i + 1, by omega⟩ ⟨i + 2, hi⟩ (by simp))
        have hne_slope :
            ((q ⟨i + 2, hi⟩).2 - (q ⟨i + 1, by omega⟩).2) / ((q ⟨i + 2, hi⟩).1 - (q ⟨i + 1, by omega⟩).1) ≠
            ((q ⟨i + 1, by omega⟩).2 - (q ⟨i, by omega⟩).2) / ((q ⟨i + 1, by omega⟩).1 - (q ⟨i, by omega⟩).1) := by
          intro heq
          have hcross : ((q ⟨i + 1, by omega⟩).1 - (q ⟨i, by omega⟩).1) *
              ((q ⟨i + 2, hi⟩).2 - (q ⟨i, by omega⟩).2) =
              ((q ⟨i + 1, by omega⟩).2 - (q ⟨i, by omega⟩).2) *
              ((q ⟨i + 2, hi⟩).1 - (q ⟨i, by omega⟩).1) := by
            have h1 := (div_eq_div_iff hdx2.ne' hdx1.ne').mp heq
            linarith
          have hne01 : q ⟨i, by omega⟩ ≠ q ⟨i + 1, by omega⟩ :=
            fun h => hdx1.ne' (by rw [h, sub_self])
          have hne02 : q ⟨i, by omega⟩ ≠ q ⟨i + 2, hi⟩ :=
            fun h => (hq_xmono ⟨i, by omega⟩ ⟨i + 2, hi⟩ (by simp)).ne (by rw [h])
          have hne12 : q ⟨i + 1, by omega⟩ ≠ q ⟨i + 2, hi⟩ :=
            fun h => hdx2.ne' (by rw [h, sub_self])
          exact hgen _ (hq_mem _) _ (hq_mem _) _ (hq_mem _) hne01 hne02 hne12 hcross
        exact lt_of_le_of_ne hle hne_slope
    · by_cases hs3 : s = 3
      · subst hs3
        have hcard_r : r ≤ S.card := by
          have h1 : Nat.choose (r + 3 - 4) (r - 2) = r - 1 := by
            have hsub : r + 3 - 4 = (r - 2) + 1 := by omega
            rw [hsub, Nat.choose_succ_self_right]
            omega
          omega
        obtain ⟨p, hp_mem, hp_xmono⟩ := exists_xSorted_seq hxdist hcard_r
        by_cases hcap : ∃ (i : ℕ) (h : i + 2 < r),
            ((p ⟨i + 2, h⟩).2 - (p ⟨i + 1, by omega⟩).2) / ((p ⟨i + 2, h⟩).1 - (p ⟨i + 1, by omega⟩).1) <
            ((p ⟨i + 1, by omega⟩).2 - (p ⟨i, by omega⟩).2) / ((p ⟨i + 1, by omega⟩).1 - (p ⟨i, by omega⟩).1)
        · rcases hcap with ⟨i, hi, hlt⟩
          right
          let q : Fin 3 → ℝ × ℝ := fun j => p ⟨i + j.1, by omega⟩
          refine ⟨q, fun j => hp_mem _, fun u v huv => hp_xmono _ _ (show i + u.1 < i + v.1 by have : u.1 < v.1 := huv; omega), ?_⟩
          intro idx hidx
          have hidx0 : idx = 0 := by omega
          subst hidx0
          simpa [q] using hlt
        · push Not at hcap
          left
          refine ⟨p, hp_mem, hp_xmono, ?_⟩
          intro i hi
          have hle := hcap i hi
          have hdx1 : 0 < (p ⟨i + 1, by omega⟩).1 - (p ⟨i, by omega⟩).1 :=
            sub_pos.mpr (hp_xmono ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (by simp))
          have hdx2 : 0 < (p ⟨i + 2, hi⟩).1 - (p ⟨i + 1, by omega⟩).1 :=
            sub_pos.mpr (hp_xmono ⟨i + 1, by omega⟩ ⟨i + 2, hi⟩ (by simp))
          have hne_slope :
              ((p ⟨i + 1, by omega⟩).2 - (p ⟨i, by omega⟩).2) / ((p ⟨i + 1, by omega⟩).1 - (p ⟨i, by omega⟩).1) ≠
              ((p ⟨i + 2, hi⟩).2 - (p ⟨i + 1, by omega⟩).2) / ((p ⟨i + 2, hi⟩).1 - (p ⟨i + 1, by omega⟩).1) := by
            intro heq
            have hcross : ((p ⟨i + 1, by omega⟩).1 - (p ⟨i, by omega⟩).1) *
                ((p ⟨i + 2, hi⟩).2 - (p ⟨i, by omega⟩).2) =
                ((p ⟨i + 1, by omega⟩).2 - (p ⟨i, by omega⟩).2) *
                ((p ⟨i + 2, hi⟩).1 - (p ⟨i, by omega⟩).1) := by
              have h1 := (div_eq_div_iff hdx1.ne' hdx2.ne').mp heq
              linarith
            have hne01 : p ⟨i, by omega⟩ ≠ p ⟨i + 1, by omega⟩ := fun h => hdx1.ne' (by rw [h, sub_self])
            have hne02 : p ⟨i, by omega⟩ ≠ p ⟨i + 2, hi⟩ :=
              fun h => (hp_xmono ⟨i, by omega⟩ ⟨i + 2, hi⟩ (by simp)).ne (by rw [h])
            have hne12 : p ⟨i + 1, by omega⟩ ≠ p ⟨i + 2, hi⟩ := fun h => hdx2.ne' (by rw [h, sub_self])
            exact hgen _ (hp_mem _) _ (hp_mem _) _ (hp_mem _) hne01 hne02 hne12 hcross
          exact lt_of_le_of_ne hle hne_slope
      · -- Inductive step `r ≥ 4` and `s ≥ 4`
        have hr4 : 4 ≤ r := by omega
        have hs4 : 4 ≤ s := by omega
        have hpascal : Nat.choose (r + s - 4) (r - 2) =
            Nat.choose ((r - 1) + s - 4) ((r - 1) - 2) + Nat.choose (r + (s - 1) - 4) (r - 2) := by
          have h1 : r + s - 4 = (r + s - 5) + 1 := by omega
          have h2 : r - 2 = (r - 3) + 1 := by omega
          have h3 : (r - 1) + s - 4 = r + s - 5 := by omega
          have h4 : (r - 1) - 2 = r - 3 := by omega
          have h5 : r + (s - 1) - 4 = r + s - 5 := by omega
          rw [h3, h4, h5, h1, h2, Nat.choose_succ_succ]
        -- `L` = points of `S` that are the rightmost endpoint of some `(r - 1)`-cup in `S`
        let L : Finset (ℝ × ℝ) :=
          S.filter (fun x => ∃ p : Fin (r - 1) → ℝ × ℝ, IsCup S p ∧ p ⟨r - 2, by omega⟩ = x)
        have hLsub : L ⊆ S := Finset.filter_subset _ _
        have hgen_sub : ∀ T ⊆ S, InGeneralPosition T := fun T hTS a ha b hb c hc =>
          hgen a (hTS ha) b (hTS hb) c (hTS hc)
        have hx_sub : ∀ T ⊆ S, ∀ p ∈ T, ∀ q ∈ T, p ≠ q → p.1 ≠ q.1 := fun T hTS p hp q hq =>
          hxdist p (hTS hp) q (hTS hq)
        by_cases hSL : Nat.choose ((r - 1) + s - 4) ((r - 1) - 2) + 1 ≤ (S \ L).card
        · rcases ih (r - 1) s (by omega) (by omega) hs (S \ L)
            (hgen_sub _ Finset.sdiff_subset) (hx_sub _ Finset.sdiff_subset) hSL with
            ⟨p, hp_cup⟩ | ⟨q, hq_cap⟩
          · exfalso
            have hlast_in_SL : p ⟨r - 2, by omega⟩ ∈ S \ L := hp_cup.1 ⟨r - 2, by omega⟩
            have hp_in_S : IsCup S p := ⟨fun i => Finset.sdiff_subset (hp_cup.1 i), hp_cup.2.1, hp_cup.2.2⟩
            have hlast_in_L : p ⟨r - 2, by omega⟩ ∈ L :=
              Finset.mem_filter.mpr ⟨Finset.sdiff_subset hlast_in_SL, p, hp_in_S, rfl⟩
            exact (Finset.mem_sdiff.mp hlast_in_SL).2 hlast_in_L
          · right
            exact ⟨q, fun i => Finset.sdiff_subset (hq_cap.1 i), hq_cap.2.1, hq_cap.2.2⟩
        · have hLcard : Nat.choose (r + (s - 1) - 4) (r - 2) + 1 ≤ L.card := by
            have htot := Finset.card_sdiff_add_card_eq_card hLsub
            omega
          rcases ih r (s - 1) (by omega) hr (by omega) L
            (hgen_sub _ hLsub) (hx_sub _ hLsub) hLcard with
            ⟨p, hp_cup⟩ | ⟨q, hq_cap⟩
          · left
            exact ⟨p, fun i => hLsub (hp_cup.1 i), hp_cup.2.1, hp_cup.2.2⟩
          · -- `q` is an `(s - 1)`-cap in `L`; its leftmost point `q 0 ∈ L` ends an `(r - 1)`-cup `p` in `S`
            have hq0L : q ⟨0, by omega⟩ ∈ L := hq_cap.1 ⟨0, by omega⟩
            rcases (Finset.mem_filter.mp hq0L).2 with ⟨p, hp_cup, hp_end⟩
            -- Compare slope `(p_{r-3}, q_0)` with slope `(q_0, q_1)`
            let A := p ⟨r - 3, by omega⟩
            let B := q ⟨0, by omega⟩
            let C := q ⟨1, by omega⟩
            have hAB_x : A.1 < B.1 := by
              dsimp only [A, B]
              rw [← hp_end]; exact hp_cup.2.1 ⟨r - 3, by omega⟩ ⟨r - 2, by omega⟩ (by simp; omega)
            have hBC_x : B.1 < C.1 := hq_cap.2.1 ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
            have hm_ne : (B.2 - A.2) / (B.1 - A.1) ≠ (C.2 - B.2) / (C.1 - B.1) := by
              intro heq
              have hdx1 : 0 < B.1 - A.1 := sub_pos.mpr hAB_x
              have hdx2 : 0 < C.1 - B.1 := sub_pos.mpr hBC_x
              have h1 := (div_eq_div_iff hdx1.ne' hdx2.ne').mp heq
              have hcross : (B.1 - A.1) * (C.2 - A.2) = (B.2 - A.2) * (C.1 - A.1) := by linarith
              have hneAB : A ≠ B := fun h => hAB_x.ne (by rw [h])
              have hneAC : A ≠ C := fun h => (hAB_x.trans hBC_x).ne (by rw [h])
              have hneBC : B ≠ C := fun h => hBC_x.ne (by rw [h])
              exact hgen A (hp_cup.1 _) B (hLsub hq0L) C (hLsub (hq_cap.1 _)) hneAB hneAC hneBC hcross
            rcases lt_or_gt_of_ne hm_ne with hlt | hgt
            · -- Append `C = q 1` to the `(r - 1)`-cup `p` to obtain an `r`-cup!
              left
              let p' : Fin r → ℝ × ℝ := fun i =>
                if hi : i.1 < r - 1 then p ⟨i.1, hi⟩ else C
              refine ⟨p', ?_, ?_, ?_⟩
              · intro i; dsimp only [p']; split_ifs
                · exact hp_cup.1 _
                · exact hLsub (hq_cap.1 _)
              · intro i j hij
                dsimp only [p']
                by_cases hj : j.1 < r - 1
                · have hi : i.1 < r - 1 := lt_trans hij hj
                  simp only [dif_pos hi, dif_pos hj]
                  exact hp_cup.2.1 ⟨i.1, hi⟩ ⟨j.1, hj⟩ hij
                · have hi : i.1 < r - 1 := by have := j.isLt; omega
                  simp only [dif_pos hi, dif_neg hj]
                  by_cases hilast : i.1 = r - 2
                  · have heq : p ⟨i.1, hi⟩ = B := by
                      have : (⟨i.1, hi⟩ : Fin (r - 1)) = ⟨r - 2, by omega⟩ := Fin.ext hilast
                      rw [this, hp_end]
                    rw [heq]; exact hBC_x
                  · have hlt_B : (p ⟨i.1, hi⟩).1 < B.1 := by
                      dsimp only [B]
                      rw [← hp_end]
                      exact hp_cup.2.1 ⟨i.1, hi⟩ ⟨r - 2, by omega⟩ (by simp [Fin.lt_def]; omega)
                    exact hlt_B.trans hBC_x
              · intro i hi
                by_cases hi2 : i + 2 < r - 1
                · simp only [p', dif_pos (by omega : i < r - 1), dif_pos (by omega : i + 1 < r - 1),
                    dif_pos hi2]
                  exact hp_cup.2.2 i hi2
                · have hieq : i = r - 3 := by omega
                  subst hieq
                  have h1 : (⟨r - 3, by omega⟩ : Fin r).1 < r - 1 := by dsimp only; omega
                  have h2 : (⟨r - 3 + 1, by omega⟩ : Fin r).1 < r - 1 := by dsimp only; omega
                  have h3 : ¬ (⟨r - 3 + 2, hi⟩ : Fin r).1 < r - 1 := by dsimp only; omega
                  simp only [p', dif_pos h1, dif_pos h2, dif_neg h3]
                  have heqB : p ⟨r - 3 + 1, h2⟩ = B := by
                    have : (⟨r - 3 + 1, h2⟩ : Fin (r - 1)) = ⟨r - 2, by omega⟩ := Fin.ext (by dsimp only; omega)
                    rw [this, hp_end]
                  rw [heqB]
                  exact hlt
            · -- Prepend `A = p_{r-3}` to the `(s - 1)`-cap `q` to obtain an `s`-cap!
              right
              let q' : Fin s → ℝ × ℝ := fun i =>
                if hi : i.1 = 0 then A else q ⟨i.1 - 1, by omega⟩
              refine ⟨q', ?_, ?_, ?_⟩
              · intro i; dsimp only [q']; split_ifs
                · exact hp_cup.1 _
                · exact hLsub (hq_cap.1 _)
              · intro i j hij
                dsimp only [q']
                by_cases hi : i.1 = 0
                · have hj : j.1 ≠ 0 := by omega
                  simp only [dif_pos hi, dif_neg hj]
                  by_cases hj1 : j.1 = 1
                  · have heq : q ⟨j.1 - 1, by omega⟩ = B := by
                      have : (⟨j.1 - 1, by omega⟩ : Fin (s - 1)) = ⟨0, by omega⟩ := Fin.ext (by dsimp only; omega)
                      rw [this]
                    rw [heq]; exact hAB_x
                  · have hlt_j : B.1 < (q ⟨j.1 - 1, by omega⟩).1 :=
                      hq_cap.2.1 ⟨0, by omega⟩ ⟨j.1 - 1, by omega⟩ (by simp [Fin.lt_def]; omega)
                    exact hAB_x.trans hlt_j
                · have hj : j.1 ≠ 0 := by omega
                  simp only [dif_neg hi, dif_neg hj]
                  exact hq_cap.2.1 ⟨i.1 - 1, by omega⟩ ⟨j.1 - 1, by omega⟩ (by simp [Fin.lt_def]; omega)
              · intro i hi
                by_cases hi0 : i = 0
                · subst hi0
                  simp only [q', ↓reduceDIte, Nat.add_eq_zero_iff, one_ne_zero, and_false,
                    Nat.add_sub_cancel, show ¬ (0 + 2 = 0) by omega]
                  exact hgt
                · simp only [q', dif_neg hi0, dif_neg (show ¬ (i + 1 = 0) by omega),
                    dif_neg (show ¬ (i + 2 = 0) by omega)]
                  have hcap_step := hq_cap.2.2 (i - 1) (by omega)
                  have heq1 : (⟨i - 1 + 1, by omega⟩ : Fin (s - 1)) = ⟨i + 1 - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
                  have heq2 : (⟨i - 1 + 2, by omega⟩ : Fin (s - 1)) = ⟨i + 2 - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
                  rw [heq1, heq2] at hcap_step
                  exact hcap_step

/-- Strict linear separation implies non-membership in `convexHull ℝ`. -/
private lemma not_mem_convexHull_of_strict_sep {p : ℝ × ℝ} {T : Set (ℝ × ℝ)} (a b : ℝ)
    (hsep : ∀ q ∈ T, a * p.1 + b * p.2 < a * q.1 + b * q.2) :
    p ∉ convexHull ℝ T := by
  let H : Set (ℝ × ℝ) := {q | a * p.1 + b * p.2 < a * q.1 + b * q.2}
  have hH_conv : Convex ℝ H := by
    intro x hx y hy u v hu hv huv
    simp only [H, Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      smul_eq_mul] at hx hy ⊢
    have h1 : (a * p.1 + b * p.2) * (u + v) < u * (a * x.1 + b * x.2) + v * (a * y.1 + b * y.2) := by
      rcases eq_or_lt_of_le hu with rfl | hu_pos
      · have hv1 : v = 1 := by linarith
        subst hv1; linarith
      · have hxu : u * (a * p.1 + b * p.2) < u * (a * x.1 + b * x.2) :=
          mul_lt_mul_of_pos_left hx hu_pos
        have hyv : v * (a * p.1 + b * p.2) ≤ v * (a * y.1 + b * y.2) :=
          mul_le_mul_of_nonneg_left hy.le hv
        linarith
    rw [huv, mul_one] at h1
    linarith
  have hsub : convexHull ℝ T ⊆ H := convexHull_min hsep hH_conv
  intro hp
  have := hsub hp
  simp only [H, Set.mem_ofPred_eq] at this
  linarith

/-- Every `k`-cup (`k ≥ 3`) is in convex position. -/
private lemma inConvexPosition_of_isCup {S : Finset (ℝ × ℝ)} {k : ℕ} (hk : 3 ≤ k)
    {p : Fin k → ℝ × ℝ} (hcup : IsCup S p) :
    InConvexPosition (Finset.univ.image p) := by
  have hp_inj : Function.Injective p := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hcup.2.1 i j hlt).ne (congrArg Prod.fst hij)
    · exact (hcup.2.1 j i hgt).ne (congrArg Prod.fst hij.symm)
  -- Helper: consecutive slope monotonicity over arbitrary `i < j`
  have hslope_mono : ∀ (i j : ℕ) (hi : i + 1 < k) (hj : j + 1 < k), i < j →
      ((p ⟨i + 1, hi⟩).2 - (p ⟨i, by omega⟩).2) / ((p ⟨i + 1, hi⟩).1 - (p ⟨i, by omega⟩).1) <
      ((p ⟨j + 1, hj⟩).2 - (p ⟨j, by omega⟩).2) / ((p ⟨j + 1, hj⟩).1 - (p ⟨j, by omega⟩).1) := by
    intro i j hi hj hij
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases hij' : i = j
      · subst hij'; exact hcup.2.2 i hj
      · exact (ih (by omega) (by omega)).trans (hcup.2.2 j hj)
  -- Secant slope bounds for `i < j` and `j < i`
  have hsec_right : ∀ (j i : ℕ) (hj : j + 1 < k) (hi : i < k), j < i →
      ((p ⟨j + 1, hj⟩).2 - (p ⟨j, by omega⟩).2) / ((p ⟨j + 1, hj⟩).1 - (p ⟨j, by omega⟩).1) ≤
      ((p ⟨i, hi⟩).2 - (p ⟨j, by omega⟩).2) / ((p ⟨i, hi⟩).1 - (p ⟨j, by omega⟩).1) := by
    intro j i hj hi hji
    set m := ((p ⟨j + 1, hj⟩).2 - (p ⟨j, by omega⟩).2) / ((p ⟨j + 1, hj⟩).1 - (p ⟨j, by omega⟩).1)
    have hdx_ji : 0 < (p ⟨i, hi⟩).1 - (p ⟨j, by omega⟩).1 :=
      sub_pos.mpr (hcup.2.1 ⟨j, by omega⟩ ⟨i, hi⟩ (by simp [Fin.lt_def]; omega))
    rw [le_div_iff₀ hdx_ji]
    induction i with
    | zero => omega
    | succ i ih =>
      by_cases heq : j = i
      · subst heq
        have hdx : 0 < (p ⟨j + 1, hj⟩).1 - (p ⟨j, by omega⟩).1 :=
          sub_pos.mpr (hcup.2.1 ⟨j, by omega⟩ ⟨j + 1, hj⟩ (by simp))
        dsimp only [m]
        rw [div_mul_cancel₀ _ hdx.ne']
      · have hji' : j < i := by omega
        have hprev := ih (by omega) hji'
          (sub_pos.mpr (hcup.2.1 ⟨j, by omega⟩ ⟨i, by omega⟩ (by simp [Fin.lt_def]; omega)))
        have hstep_slope : m < ((p ⟨i + 1, hi⟩).2 - (p ⟨i, by omega⟩).2) /
            ((p ⟨i + 1, hi⟩).1 - (p ⟨i, by omega⟩).1) := hslope_mono j i hj hi hji'
        have hdx_step : 0 < (p ⟨i + 1, hi⟩).1 - (p ⟨i, by omega⟩).1 :=
          sub_pos.mpr (hcup.2.1 ⟨i, by omega⟩ ⟨i + 1, hi⟩ (by simp))
        have hstep : m * ((p ⟨i + 1, hi⟩).1 - (p ⟨i, by omega⟩).1) <
            (p ⟨i + 1, hi⟩).2 - (p ⟨i, by omega⟩).2 := (lt_div_iff₀ hdx_step).mp hstep_slope
        linarith
  have hsec_left : ∀ (i j : ℕ) (hj0 : 0 < j) (hj : j < k) (hi : i < k), i < j →
      ((p ⟨j, hj⟩).2 - (p ⟨i, hi⟩).2) / ((p ⟨j, hj⟩).1 - (p ⟨i, hi⟩).1) ≤
      ((p ⟨j, hj⟩).2 - (p ⟨j - 1, by omega⟩).2) / ((p ⟨j, hj⟩).1 - (p ⟨j - 1, by omega⟩).1) := by
    intro i j hj0 hj hi hij
    set m := ((p ⟨j, hj⟩).2 - (p ⟨j - 1, by omega⟩).2) / ((p ⟨j, hj⟩).1 - (p ⟨j - 1, by omega⟩).1)
    have hdx_ij : 0 < (p ⟨j, hj⟩).1 - (p ⟨i, hi⟩).1 :=
      sub_pos.mpr (hcup.2.1 ⟨i, hi⟩ ⟨j, hj⟩ (by simp [Fin.lt_def]; omega))
    rw [div_le_iff₀ hdx_ij]
    -- Induct on `d = j - i` (`1 ≤ d`)
    suffices h : ∀ d : ℕ, 1 ≤ d → ∀ (i : ℕ) (hi : i < k), j - i = d →
        (p ⟨j, hj⟩).2 - (p ⟨i, hi⟩).2 ≤ m * ((p ⟨j, hj⟩).1 - (p ⟨i, hi⟩).1) by
      exact h (j - i) (by omega) i hi rfl
    intro d hd
    induction d, hd using Nat.le_induction with
    | base =>
      intro i hi hji
      have hieq : i = j - 1 := by omega
      subst hieq
      have hdx : 0 < (p ⟨j, hj⟩).1 - (p ⟨j - 1, hi⟩).1 :=
        sub_pos.mpr (hcup.2.1 ⟨j - 1, hi⟩ ⟨j, hj⟩ (by simp [Fin.lt_def]; omega))
      dsimp only [m]
      rw [div_mul_cancel₀ _ hdx.ne']
    | succ d hd ih =>
      intro i hi hji
      have hprev := ih (i + 1) (by omega) (by omega)
      have hstep_slope : ((p ⟨i + 1, by omega⟩).2 - (p ⟨i, hi⟩).2) /
          ((p ⟨i + 1, by omega⟩).1 - (p ⟨i, hi⟩).1) < m := by
        have hlt := hslope_mono i (j - 1) (by omega) (by omega) (by omega)
        have hjj : (⟨j - 1 + 1, by omega⟩ : Fin k) = ⟨j, hj⟩ := Fin.ext (by dsimp only; omega)
        simpa [m, hjj] using hlt
      have hdx_step : 0 < (p ⟨i + 1, by omega⟩).1 - (p ⟨i, hi⟩).1 :=
        sub_pos.mpr (hcup.2.1 ⟨i, hi⟩ ⟨i + 1, by omega⟩ (by simp))
      have hstep : (p ⟨i + 1, by omega⟩).2 - (p ⟨i, hi⟩).2 <
          m * ((p ⟨i + 1, by omega⟩).1 - (p ⟨i, hi⟩).1) := (div_lt_iff₀ hdx_step).mp hstep_slope
      linarith
  -- Now exhibit a strict separating linear functional for every `p j`
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
  by_cases hj0 : j.1 = 0
  · apply not_mem_convexHull_of_strict_sep 1 0
    intro y hy
    rcases Finset.mem_image.mp (Finset.mem_of_mem_erase hy) with ⟨i, _, rfl⟩
    have hne : i ≠ j := fun h => (Finset.mem_erase.mp hy).1 (by rw [h])
    have hlt : j < i := lt_of_le_of_ne (show j.1 ≤ i.1 by omega) hne.symm
    have hxlt := hcup.2.1 j i hlt
    linarith
  · by_cases hjk : j.1 = k - 1
    · apply not_mem_convexHull_of_strict_sep (-1) 0
      intro y hy
      rcases Finset.mem_image.mp (Finset.mem_of_mem_erase hy) with ⟨i, _, rfl⟩
      have hne : i ≠ j := fun h => (Finset.mem_erase.mp hy).1 (by rw [h])
      have hlt : i < j := lt_of_le_of_ne (show i.1 ≤ j.1 by have := i.isLt; omega) hne
      have hxlt := hcup.2.1 i j hlt
      linarith
    · -- Interior point `0 < j.1 < k - 1`: midpoint slope separates strictly!
      have hj1 : 0 < j.1 := by omega
      have hjn : j.1 + 1 < k := by omega
      let mL := ((p j).2 - (p ⟨j.1 - 1, by omega⟩).2) / ((p j).1 - (p ⟨j.1 - 1, by omega⟩).1)
      let mR := ((p ⟨j.1 + 1, hjn⟩).2 - (p j).2) / ((p ⟨j.1 + 1, hjn⟩).1 - (p j).1)
      have hm_lt : mL < mR := by
        have h := hcup.2.2 (j.1 - 1) (by omega)
        have h1 : (⟨j.1 - 1 + 1, by omega⟩ : Fin k) = j := Fin.ext (by dsimp only; omega)
        have h2 : (⟨j.1 - 1 + 2, by omega⟩ : Fin k) = ⟨j.1 + 1, hjn⟩ := Fin.ext (by dsimp only; omega)
        simpa [mL, mR, h1, h2] using h
      let m := (mL + mR) / 2
      apply not_mem_convexHull_of_strict_sep (-m) 1
      intro y hy
      rcases Finset.mem_image.mp (Finset.mem_of_mem_erase hy) with ⟨i, _, rfl⟩
      have hne : i ≠ j := fun h => (Finset.mem_erase.mp hy).1 (by rw [h])
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hdx : 0 < (p j).1 - (p i).1 := sub_pos.mpr (hcup.2.1 i j hlt)
        have hle := hsec_left i.1 j.1 hj1 j.isLt i.isLt hlt
        have hsec : ((p j).2 - (p i).2) / ((p j).1 - (p i).1) < m := lt_of_le_of_lt hle (by dsimp only [m, mL]; linarith)
        have hmul := (div_lt_iff₀ hdx).mp hsec
        linarith
      · have hdx : 0 < (p i).1 - (p j).1 := sub_pos.mpr (hcup.2.1 j i hgt)
        have hle := hsec_right j.1 i.1 hjn i.isLt hgt
        have hsec : m < ((p i).2 - (p j).2) / ((p i).1 - (p j).1) := lt_of_lt_of_le (by dsimp only [m, mR]; linarith) hle
        have hmul := (lt_div_iff₀ hdx).mp hsec
        linarith

/-- Reflection `(x, y) ↦ (x, -y)` turns any `k`-cap into a `k`-cup and preserves convex position. -/
private lemma inConvexPosition_of_isCap {S : Finset (ℝ × ℝ)} {k : ℕ} (hk : 3 ≤ k)
    {q : Fin k → ℝ × ℝ} (hcap : IsCap S q) :
    InConvexPosition (Finset.univ.image q) := by
  let refl : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, -p.2)
  let S' : Finset (ℝ × ℝ) := S.image refl
  let p : Fin k → ℝ × ℝ := fun i => refl (q i)
  have hcup : IsCup S' p := by
    refine ⟨fun i => Finset.mem_image.mpr ⟨q i, hcap.1 i, rfl⟩,
      fun i j hij => hcap.2.1 i j hij, ?_⟩
    intro i hi
    have h := hcap.2.2 i hi
    dsimp only [p, refl]
    have h1 : (-(q ⟨i + 1, by omega⟩).2 - -(q ⟨i, by omega⟩).2) /
        ((q ⟨i + 1, by omega⟩).1 - (q ⟨i, by omega⟩).1) =
        -(((q ⟨i + 1, by omega⟩).2 - (q ⟨i, by omega⟩).2) /
        ((q ⟨i + 1, by omega⟩).1 - (q ⟨i, by omega⟩).1)) := by ring
    have h2 : (-(q ⟨i + 2, hi⟩).2 - -(q ⟨i + 1, by omega⟩).2) /
        ((q ⟨i + 2, hi⟩).1 - (q ⟨i + 1, by omega⟩).1) =
        -(((q ⟨i + 2, hi⟩).2 - (q ⟨i + 1, by omega⟩).2) /
        ((q ⟨i + 2, hi⟩).1 - (q ⟨i + 1, by omega⟩).1)) := by ring
    linarith
  have hconv' := inConvexPosition_of_isCup hk hcup
  let f : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := refl
      map_add' := fun u v => by ext <;> simp [refl]; ring
      map_smul' := fun r u => by ext <;> simp [refl] }
  have hf_inj : Function.Injective f := fun u v h => by
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    dsimp only [f, LinearMap.coe_mk, AddHom.coe_mk, refl] at h1 h2
    ext <;> linarith
  intro x hx hmem
  have hmem' : f x ∈ f '' convexHull ℝ (((Finset.univ.image q).erase x : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) :=
    ⟨x, hmem, rfl⟩
  rw [LinearMap.image_convexHull] at hmem'
  have himg_eq : f '' (((Finset.univ.image q).erase x : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) =
      (((Finset.univ.image p).erase (f x) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
    ext y
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_erase, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨z, ⟨hzx, ⟨i, rfl⟩⟩, rfl⟩
      exact ⟨fun h => hzx (hf_inj h), i, rfl⟩
    · rintro ⟨hyx, ⟨i, rfl⟩⟩
      exact ⟨q i, ⟨fun h => hyx (congrArg f h), i, rfl⟩, rfl⟩
  rw [himg_eq] at hmem'
  have hfx_mem : f x ∈ Finset.univ.image p := by
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  exact hconv' (f x) hfx_mem hmem'

/-- **Erdős–Szekeres Happy Ending Theorem (`C(2n - 4, n - 2) + 1`):**
For every `n ≥ 3`, every finite set `S ⊆ ℝ²` of at least `Nat.choose (2 * n - 4) (n - 2) + 1`
points in general position contains a subset `T ⊆ S` of size `n` in convex position
(`∀ p ∈ T, p ∉ convexHull ℝ (T.erase p)`). -/
theorem erdos_szekeres_happy_ending {n : ℕ} (hn : 3 ≤ n) (S : Finset (ℝ × ℝ))
    (hgen : InGeneralPosition S) (hcard : Nat.choose (2 * n - 4) (n - 2) + 1 ≤ S.card) :
    ∃ T : Finset (ℝ × ℝ), T ⊆ S ∧ T.card = n ∧ InConvexPosition T := by
  -- Choose a real shear parameter `t` so that `T_t(x, y) = (x + t * y, y)` makes all `x`-coords distinct
  let badT : Finset ℝ := (S ×ˢ S).image (fun pq => -(pq.1.1 - pq.2.1) / (pq.1.2 - pq.2.2))
  let t : ℝ := if h : badT.Nonempty then badT.max' h + 1 else 0
  have ht_notBad : t ∉ badT := by
    intro hmem
    have hne : badT.Nonempty := ⟨t, hmem⟩
    have hle := Finset.le_max' badT t hmem
    simp only [t, dif_pos hne] at hle
    linarith
  let shear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun p => (p.1 + t * p.2, p.2)
      map_add' := fun u v => by ext <;> (simp; try ring)
      map_smul' := fun c u => by ext <;> (simp; try ring) }
  have hshear_inj : Function.Injective shear := by
    intro u v h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    dsimp only [shear, LinearMap.coe_mk, AddHom.coe_mk] at h1 h2
    ext
    · linear_combination h1 - t * h2
    · exact h2
  let S' : Finset (ℝ × ℝ) := S.image shear
  have hS'_card : S'.card = S.card := Finset.card_image_of_injective S hshear_inj
  have hS'_gen : InGeneralPosition S' := by
    intro a ha b hb c hc hab hac hbc hcol
    rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨q, hq, rfl⟩
    rcases Finset.mem_image.mp hc with ⟨r, hr, rfl⟩
    have hpq : p ≠ q := fun h => hab (congrArg shear h)
    have hpr : p ≠ r := fun h => hac (congrArg shear h)
    have hqr : q ≠ r := fun h => hbc (congrArg shear h)
    dsimp only [shear, LinearMap.coe_mk, AddHom.coe_mk] at hcol
    have horig : (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1) := by linear_combination hcol
    exact hgen p hp q hq r hr hpq hpr hqr horig
  have hS'_xdist : ∀ a ∈ S', ∀ b ∈ S', a ≠ b → a.1 ≠ b.1 := by
    intro a ha b hb hab hxeq
    rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨q, hq, rfl⟩
    dsimp only [shear, LinearMap.coe_mk, AddHom.coe_mk] at hxeq
    by_cases hy : p.2 = q.2
    · have hx : p.1 = q.1 := by linear_combination hxeq - t * hy
      exact hab (congrArg shear (Prod.ext hx hy))
    · have hdy : p.2 - q.2 ≠ 0 := sub_ne_zero.mpr hy
      have ht_eq : t = -(p.1 - q.1) / (p.2 - q.2) := by
        rw [eq_div_iff hdy]; linear_combination hxeq
      exact ht_notBad (ht_eq ▸ Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩)
  have hcard' : Nat.choose (n + n - 4) (n - 2) + 1 ≤ S'.card := by
    rw [hS'_card, show n + n = 2 * n by omega]; exact hcard
  -- Apply Cups-and-Caps theorem to `S'`
  have hT' : ∃ T' : Finset (ℝ × ℝ), T' ⊆ S' ∧ T'.card = n ∧ InConvexPosition T' := by
    rcases cups_and_caps_core (n + n) n n rfl hn hn S' hS'_gen hS'_xdist hcard' with
      ⟨p, hcup⟩ | ⟨q, hcap⟩
    · have hinj : Function.Injective p := by
        intro i j hij; by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact (hcup.2.1 i j hlt).ne (congrArg Prod.fst hij)
        · exact (hcup.2.1 j i hgt).ne (congrArg Prod.fst hij.symm)
      refine ⟨Finset.univ.image p, Finset.image_subset_iff.mpr fun i _ => hcup.1 i, ?_,
        inConvexPosition_of_isCup hn hcup⟩
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    · have hinj : Function.Injective q := by
        intro i j hij; by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact (hcap.2.1 i j hlt).ne (congrArg Prod.fst hij)
        · exact (hcap.2.1 j i hgt).ne (congrArg Prod.fst hij.symm)
      refine ⟨Finset.univ.image q, Finset.image_subset_iff.mpr fun i _ => hcap.1 i, ?_,
        inConvexPosition_of_isCap hn hcap⟩
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  -- Pull back `T' ⊆ S'` via the inverse linear shear
  rcases hT' with ⟨T', hT'sub, hT'card, hT'conv⟩
  let invShear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun p => (p.1 - t * p.2, p.2)
      map_add' := fun u v => by ext <;> (simp; try ring)
      map_smul' := fun c u => by ext <;> (simp; try ring) }
  have hleft : ∀ p, invShear (shear p) = p := fun p => by
    ext <;> simp [shear, invShear]
  have hright : ∀ p, shear (invShear p) = p := fun p => by
    ext <;> simp [shear, invShear]
  have hinv_inj : Function.Injective invShear := fun u v h => by
    have := congrArg shear h; rwa [hright, hright] at this
  let T : Finset (ℝ × ℝ) := T'.image invShear
  refine ⟨T, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hyT', rfl⟩
    rcases Finset.mem_image.mp (hT'sub hyT') with ⟨p, hpS, rfl⟩
    rwa [hleft]
  · rw [Finset.card_image_of_injective T' hinv_inj, hT'card]
  · intro x hx hmem
    have hmem' : shear x ∈ shear '' convexHull ℝ ((T.erase x : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) :=
      ⟨x, hmem, rfl⟩
    rw [LinearMap.image_convexHull] at hmem'
    have himg_eq : shear '' ((T.erase x : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) =
        ((T'.erase (shear x) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
      ext y
      simp only [Set.mem_image, Finset.mem_coe, Finset.mem_erase, T, Finset.mem_image]
      constructor
      · rintro ⟨z, ⟨hzx, ⟨w, hwT', rfl⟩⟩, rfl⟩
        rw [hright]
        exact ⟨fun h => hzx (by rw [h, hleft]), hwT'⟩
      · rintro ⟨hyx, hyT'⟩
        refine ⟨invShear y, ⟨fun h => hyx (by rw [← h, hright]), y, hyT', rfl⟩, hright y⟩
    rw [himg_eq] at hmem'
    have hsx_mem : shear x ∈ T' := by
      rcases Finset.mem_image.mp hx with ⟨y, hyT', rfl⟩
      rwa [hright]
    exact hT'conv (shear x) hsx_mem hmem'

end ErdosSzekeres

/-! ## Section 4: Full Hales–Jewett Theorem & Van der Waerden's Theorem -/

section HalesJewettAndVdW

/-- The point of a combinatorial line in `Fin N → Fin k` with wildcard set `W` and fixed
background `base`, evaluated at letter `a : Fin k`. -/
def linePoint {N k : ℕ} (W : Finset (Fin N)) (base : Fin N → Fin k) (a : Fin k) :
    Fin N → Fin k :=
  fun i => if i ∈ W then a else base i

/-- Every combinatorial line with nonempty wildcard set `W` is injective in `a : Fin k`. -/
lemma linePoint_injective {N k : ℕ} {W : Finset (Fin N)} (hW : W.Nonempty)
    (base : Fin N → Fin k) : Function.Injective (linePoint W base) := by
  intro a b hab
  rcases hW with ⟨i₀, hi₀⟩
  have h := congrFun hab i₀
  simpa [linePoint, hi₀] using h

/-- Concatenate two finite coordinate vectors `x : Fin N₁ → α` and `y : Fin N₂ → α`
into `Fin (N₁ + N₂) → α`. -/
private def combineVec {N₁ N₂ : ℕ} {α : Type*} (x : Fin N₁ → α) (y : Fin N₂ → α) :
    Fin (N₁ + N₂) → α :=
  fun m => if h : m.1 < N₁ then x ⟨m.1, h⟩ else y ⟨m.1 - N₁, by omega⟩

/-- Color-focusing fan vector in `Fin N → Fin (k + 1)`: puts `Fin.last k` on blocks `W s`
with `s < j`, `a.castSucc` on blocks `W s` with `j ≤ s`, and `base i` outside `⋃ W s`. -/
private def fanPoint {N k t : ℕ} (W : Fin t → Finset (Fin N)) (base : Fin N → Fin (k + 1))
    (j : Fin (t + 1)) (a : Fin k) : Fin N → Fin (k + 1) :=
  fun i =>
    if ∃ s : Fin t, s.1 < j.1 ∧ i ∈ W s then Fin.last k
    else if ∃ s : Fin t, j.1 ≤ s.1 ∧ i ∈ W s then a.castSucc
    else base i

/-- **Hales–Jewett Color-Focusing Step:**
Assuming the Hales–Jewett theorem holds for alphabet size `k ≥ 1` and every number of colors,
for every `r ≥ 1` and every `t : ℕ`, there exists `N : ℕ` such that every `r`-coloring of
`Fin N → Fin (k + 1)` admits either a monochromatic combinatorial line or a `t`-block
color-focused fan with `t + 1` pairwise distinct colors. -/
private lemma hales_jewett_focusing {k : ℕ} (hk : 1 ≤ k)
    (ihHJ : ∀ r : ℕ, 1 ≤ r → ∃ N : ℕ, ∀ c : (Fin N → Fin k) → Fin r,
      ∃ (W : Finset (Fin N)) (base : Fin N → Fin k), W.Nonempty ∧
        ∃ col : Fin r, ∀ a : Fin k, c (linePoint W base a) = col)
    {r : ℕ} (hr : 1 ≤ r) :
    ∀ t : ℕ, ∃ N : ℕ, ∀ c : (Fin N → Fin (k + 1)) → Fin r,
      (∃ (W : Finset (Fin N)) (base : Fin N → Fin (k + 1)), W.Nonempty ∧
        ∃ col : Fin r, ∀ a : Fin (k + 1), c (linePoint W base a) = col) ∨
      (∃ (W : Fin t → Finset (Fin N)) (base : Fin N → Fin (k + 1)) (col : Fin (t + 1) → Fin r),
        (∀ s : Fin t, (W s).Nonempty) ∧
        (∀ s₁ s₂ : Fin t, s₁ ≠ s₂ → Disjoint (W s₁) (W s₂)) ∧
        Function.Injective col ∧
        ∀ (j : Fin (t + 1)) (a : Fin k), c (fanPoint W base j a) = col j) := by
  intro t
  induction t with
  | zero =>
    refine ⟨1, fun c => Or.inr ?_⟩
    let base : Fin 1 → Fin (k + 1) := fun _ => Fin.last k
    refine ⟨Fin.elim0, base, fun _ => c base, fun s => Fin.elim0 s, fun s => Fin.elim0 s,
      fun i j _ => Fin.ext (by have := i.isLt; have := j.isLt; omega), ?_⟩
    intro j a
    have hfan : fanPoint (Fin.elim0 : Fin 0 → Finset (Fin 1)) base j a = base := by
      funext i
      simp [fanPoint]
    rw [hfan]
  | succ t ih =>
    rcases ih with ⟨N₁, hN₁⟩
    let ColorFun := (Fin N₁ → Fin (k + 1)) → Fin r
    have hCF_pos : 1 ≤ Fintype.card ColorFun := by
      have : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
      exact Fintype.card_pos (α := ColorFun)
    rcases ihHJ (Fintype.card ColorFun) hCF_pos with ⟨N₂, hN₂⟩
    refine ⟨N₁ + N₂, ?_⟩
    intro c
    -- Induce a `ColorFun`-coloring on `Fin N₂ → Fin k`
    let eCol : ColorFun ≃ Fin (Fintype.card ColorFun) := Fintype.equivFin ColorFun
    let c₂ : (Fin N₂ → Fin k) → Fin (Fintype.card ColorFun) :=
      fun y => eCol (fun x => c (combineVec x (fun i => (y i).castSucc)))
    rcases hN₂ c₂ with ⟨W₂, base₂, hW₂_ne, col₂, hcol₂⟩
    let g : ColorFun := eCol.symm col₂
    have hg_spec : ∀ (x : Fin N₁ → Fin (k + 1)) (a : Fin k),
        c (combineVec x (fun i => (linePoint W₂ base₂ a i).castSucc)) = g x := by
      intro x a
      have h1 : eCol (fun x' => c (combineVec x' (fun i => (linePoint W₂ base₂ a i).castSucc))) = col₂ :=
        hcol₂ a
      have h2 := congrArg eCol.symm h1
      rw [Equiv.symm_apply_apply] at h2
      exact congrFun h2 x
    let a₀ : Fin k := ⟨0, by omega⟩
    -- Apply focusing IH for `t` to `g`
    rcases hN₁ g with
      ⟨W₁, base₁, hW₁_ne, col₁, hmono₁⟩ |
      ⟨W₁, base₁, col₁, hW₁_ne, hW₁_disj, hcol₁_inj, hfan₁⟩
    · -- Case 1: `g` already has a monochromatic combinatorial line! Lift it to `Fin (N₁ + N₂)`.
      left
      let W : Finset (Fin (N₁ + N₂)) := W₁.image (fun i : Fin N₁ => (⟨i.1, by omega⟩ : Fin (N₁ + N₂)))
      let base : Fin (N₁ + N₂) → Fin (k + 1) :=
        combineVec base₁ (fun i => (linePoint W₂ base₂ a₀ i).castSucc)
      refine ⟨W, base, hW₁_ne.image _, col₁, ?_⟩
      intro a
      have hvec : linePoint W base a =
          combineVec (linePoint W₁ base₁ a) (fun i => (linePoint W₂ base₂ a₀ i).castSucc) := by
        funext m
        dsimp only [linePoint, combineVec, base]
        by_cases hm : m.1 < N₁
        · simp only [dif_pos hm]
          have hmem : m ∈ W ↔ (⟨m.1, hm⟩ : Fin N₁) ∈ W₁ := by
            simp only [W, Finset.mem_image]
            constructor
            · rintro ⟨i, hi, heq⟩
              have : i = ⟨m.1, hm⟩ := Fin.ext (by simpa using congrArg Fin.val heq)
              exact this ▸ hi
            · intro hi
              exact ⟨⟨m.1, hm⟩, hi, Fin.ext rfl⟩
          by_cases h : (⟨m.1, hm⟩ : Fin N₁) ∈ W₁
          · rw [if_pos (hmem.mpr h), if_pos h]
          · rw [if_neg (mt hmem.mp h), if_neg h]
        · simp only [dif_neg hm]
          have hnotW : m ∉ W := by
            simp only [W, Finset.mem_image, not_exists, not_and]
            intro i _ heq
            have : i.1 = m.1 := congrArg Fin.val heq
            have := i.isLt
            omega
          rw [if_neg hnotW]
      rw [hvec, hg_spec, hmono₁ a]
    · -- Case 2: `g` has a `t`-fan `(W₁, base₁, col₁)`; append `W₂` as block `t`!
      let lift₁ : Fin N₁ → Fin (N₁ + N₂) := fun i => ⟨i.1, by omega⟩
      let lift₂ : Fin N₂ → Fin (N₁ + N₂) := fun i => ⟨N₁ + i.1, by omega⟩
      let W' : Fin (t + 1) → Finset (Fin (N₁ + N₂)) := fun s =>
        if hs : s.1 < t then (W₁ ⟨s.1, hs⟩).image lift₁
        else W₂.image lift₂
      let base' : Fin (N₁ + N₂) → Fin (k + 1) :=
        combineVec base₁ (fun i => (base₂ i).castSucc)
      have hW'_ne : ∀ s : Fin (t + 1), (W' s).Nonempty := by
        intro s
        dsimp only [W']
        split_ifs with hs
        · exact (hW₁_ne ⟨s.1, hs⟩).image lift₁
        · exact hW₂_ne.image lift₂
      have hW'_disj : ∀ s₁ s₂ : Fin (t + 1), s₁ ≠ s₂ → Disjoint (W' s₁) (W' s₂) := by
        intro s₁ s₂ hne
        rw [Finset.disjoint_left]
        intro m hm₁ hm₂
        dsimp only [W'] at hm₁ hm₂
        by_cases h1 : s₁.1 < t <;> by_cases h2 : s₂.1 < t
        · rw [dif_pos h1] at hm₁; rw [dif_pos h2] at hm₂
          rcases Finset.mem_image.mp hm₁ with ⟨i₁, hi₁, heq₁⟩
          rcases Finset.mem_image.mp hm₂ with ⟨i₂, hi₂, heq₂⟩
          have hi_eq : i₁ = i₂ := Fin.ext (by
            have := congrArg Fin.val (heq₁.trans heq₂.symm)
            simpa [lift₁] using this)
          subst hi_eq
          have hsne : (⟨s₁.1, h1⟩ : Fin t) ≠ ⟨s₂.1, h2⟩ := fun h =>
            hne (Fin.ext (by simpa using congrArg Fin.val h))
          exact Finset.disjoint_left.mp (hW₁_disj _ _ hsne) hi₁ hi₂
        · rw [dif_pos h1] at hm₁; rw [dif_neg h2] at hm₂
          rcases Finset.mem_image.mp hm₁ with ⟨i₁, _, heq₁⟩
          rcases Finset.mem_image.mp hm₂ with ⟨i₂, _, heq₂⟩
          have := congrArg Fin.val (heq₁.trans heq₂.symm)
          simp only [lift₁, lift₂] at this
          have := i₁.isLt; omega
        · rw [dif_neg h1] at hm₁; rw [dif_pos h2] at hm₂
          rcases Finset.mem_image.mp hm₁ with ⟨i₁, _, heq₁⟩
          rcases Finset.mem_image.mp hm₂ with ⟨i₂, _, heq₂⟩
          have := congrArg Fin.val (heq₁.trans heq₂.symm)
          simp only [lift₁, lift₂] at this
          have := i₂.isLt; omega
        · have hs₁ : s₁.1 = t := by have := s₁.isLt; omega
          have hs₂ : s₂.1 = t := by have := s₂.isLt; omega
          exact hne (Fin.ext (by omega))
      -- Helper: membership of `m` in `W' s`
      have hmem_W'_lt : ∀ (m : Fin (N₁ + N₂)) (hm : m.1 < N₁) (s : Fin (t + 1)),
          m ∈ W' s ↔ ∃ hs : s.1 < t, (⟨m.1, hm⟩ : Fin N₁) ∈ W₁ ⟨s.1, hs⟩ := by
        intro m hm s
        dsimp only [W']
        by_cases hs : s.1 < t
        · rw [dif_pos hs, Finset.mem_image]
          constructor
          · rintro ⟨i, hi, heq⟩
            have : i = ⟨m.1, hm⟩ := Fin.ext (by simpa using congrArg Fin.val heq)
            exact ⟨hs, this ▸ hi⟩
          · rintro ⟨_, hi⟩
            exact ⟨⟨m.1, hm⟩, hi, Fin.ext rfl⟩
        · rw [dif_neg hs, Finset.mem_image]
          constructor
          · rintro ⟨i, _, heq⟩
            have : N₁ + i.1 = m.1 := by simpa [lift₂] using congrArg Fin.val heq
            omega
          · rintro ⟨hs', _⟩; exact absurd hs' hs
      have hmem_W'_ge : ∀ (m : Fin (N₁ + N₂)) (hm : ¬ m.1 < N₁) (s : Fin (t + 1)),
          m ∈ W' s ↔ s.1 = t ∧ (⟨m.1 - N₁, by omega⟩ : Fin N₂) ∈ W₂ := by
        intro m hm s
        dsimp only [W']
        by_cases hs : s.1 < t
        · rw [dif_pos hs, Finset.mem_image]
          constructor
          · rintro ⟨i, _, heq⟩
            have : i.1 = m.1 := by simpa [lift₁] using congrArg Fin.val heq
            have := i.isLt; omega
          · rintro ⟨heq, _⟩; omega
        · rw [dif_neg hs, Finset.mem_image]
          have hst : s.1 = t := by have := s.isLt; omega
          constructor
          · rintro ⟨i, hi, heq⟩
            have : i = ⟨m.1 - N₁, by omega⟩ := Fin.ext (by
              have := congrArg Fin.val heq; simp only [lift₂] at this; dsimp only; omega)
            exact ⟨hst, this ▸ hi⟩
          · rintro ⟨_, hi⟩
            exact ⟨⟨m.1 - N₁, by omega⟩, hi, Fin.ext (by simp only [lift₂]; omega)⟩
      -- For `j < t + 1`: `fanPoint W' base' j a = combineVec (fanPoint W₁ base₁ j a) (line₂ a)`
      have hfan'_lt : ∀ (j : Fin (t + 2)) (hj : j.1 < t + 1) (a : Fin k),
          fanPoint W' base' j a =
            combineVec (fanPoint W₁ base₁ ⟨j.1, hj⟩ a) (fun i => (linePoint W₂ base₂ a i).castSucc) := by
        intro j hj a
        funext m
        dsimp only [fanPoint, combineVec, base']
        by_cases hm : m.1 < N₁
        · simp only [dif_pos hm]
          have hiff1 : (∃ s : Fin (t + 1), s.1 < j.1 ∧ m ∈ W' s) ↔
              (∃ s : Fin t, s.1 < j.1 ∧ (⟨m.1, hm⟩ : Fin N₁) ∈ W₁ s) := by
            constructor
            · rintro ⟨s, hsj, hms⟩
              rcases (hmem_W'_lt m hm s).mp hms with ⟨hst, hmem⟩
              exact ⟨⟨s.1, hst⟩, hsj, hmem⟩
            · rintro ⟨s, hsj, hmem⟩
              exact ⟨⟨s.1, by omega⟩, hsj, (hmem_W'_lt m hm ⟨s.1, by omega⟩).mpr ⟨s.isLt, hmem⟩⟩
          have hiff2 : (∃ s : Fin (t + 1), j.1 ≤ s.1 ∧ m ∈ W' s) ↔
              (∃ s : Fin t, j.1 ≤ s.1 ∧ (⟨m.1, hm⟩ : Fin N₁) ∈ W₁ s) := by
            constructor
            · rintro ⟨s, hsj, hms⟩
              rcases (hmem_W'_lt m hm s).mp hms with ⟨hst, hmem⟩
              exact ⟨⟨s.1, hst⟩, hsj, hmem⟩
            · rintro ⟨s, hsj, hmem⟩
              exact ⟨⟨s.1, by omega⟩, hsj, (hmem_W'_lt m hm ⟨s.1, by omega⟩).mpr ⟨s.isLt, hmem⟩⟩
          simp only [hiff1, hiff2]
        · simp only [dif_neg hm]
          have hno1 : ¬ ∃ s : Fin (t + 1), s.1 < j.1 ∧ m ∈ W' s := by
            rintro ⟨s, hsj, hms⟩
            have hst := ((hmem_W'_ge m hm s).mp hms).1
            omega
          have hiff2 : (∃ s : Fin (t + 1), j.1 ≤ s.1 ∧ m ∈ W' s) ↔
              (⟨m.1 - N₁, by omega⟩ : Fin N₂) ∈ W₂ := by
            constructor
            · rintro ⟨s, _, hms⟩; exact ((hmem_W'_ge m hm s).mp hms).2
            · intro hmem
              exact ⟨Fin.last t, by simp; omega,
                (hmem_W'_ge m hm (Fin.last t)).mpr ⟨rfl, hmem⟩⟩
          rw [if_neg hno1]
          dsimp only [linePoint]
          by_cases h2 : (⟨m.1 - N₁, by omega⟩ : Fin N₂) ∈ W₂
          · rw [if_pos (hiff2.mpr h2), if_pos h2]
          · rw [if_neg (mt hiff2.mp h2), if_neg h2]
      -- Focus apex `z := fanPoint W' base' (Fin.last (t + 1)) a₀` (independent of `a : Fin k`)
      let z : Fin (N₁ + N₂) → Fin (k + 1) :=
        fun m => if ∃ s : Fin (t + 1), m ∈ W' s then Fin.last k else base' m
      have hfan'_last : ∀ a : Fin k, fanPoint W' base' (Fin.last (t + 1)) a = z := by
        intro a
        funext m
        dsimp only [fanPoint, z]
        have hiff1 : (∃ s : Fin (t + 1), s.1 < (Fin.last (t + 1)).1 ∧ m ∈ W' s) ↔
            (∃ s : Fin (t + 1), m ∈ W' s) := by
          constructor
          · rintro ⟨s, _, hms⟩; exact ⟨s, hms⟩
          · rintro ⟨s, hms⟩; exact ⟨s, by rw [Fin.val_last]; exact s.isLt, hms⟩
        have hno2 : ¬ ∃ s : Fin (t + 1), (Fin.last (t + 1)).1 ≤ s.1 ∧ m ∈ W' s := by
          rintro ⟨s, hs, _⟩
          have := s.isLt; simp at hs; omega
        rw [if_neg hno2]
        by_cases h1 : ∃ s : Fin (t + 1), m ∈ W' s
        · rw [if_pos (hiff1.mpr h1), if_pos h1]
        · rw [if_neg (mt hiff1.mp h1), if_neg h1]
      -- Check if `c z` collides with any existing fan color `col₁ j₀`
      by_cases hcoll : ∃ j₀ : Fin (t + 1), col₁ j₀ = c z
      · -- Collision! Build a monochromatic combinatorial line of color `c z`!
        left
        rcases hcoll with ⟨j₀, hj₀_col⟩
        let U : Finset (Fin (N₁ + N₂)) :=
          (Finset.univ.filter (fun s : Fin (t + 1) => j₀.1 ≤ s.1)).biUnion W'
        have hU_ne : U.Nonempty := by
          obtain ⟨m₀, hm₀⟩ := hW'_ne (Fin.last t)
          refine ⟨m₀, Finset.mem_biUnion.mpr ⟨Fin.last t, ?_, hm₀⟩⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last]
          have := j₀.isLt; omega
        let baseU : Fin (N₁ + N₂) → Fin (k + 1) := fun m =>
          if ∃ s : Fin (t + 1), s.1 < j₀.1 ∧ m ∈ W' s then Fin.last k else base' m
        refine ⟨U, baseU, hU_ne, c z, ?_⟩
        intro a
        by_cases halast : a = Fin.last k
        · subst halast
          have hpt : linePoint U baseU (Fin.last k) = z := by
            funext m
            dsimp only [linePoint, baseU, z]
            by_cases hmU : m ∈ U
            · rw [if_pos hmU, if_pos]
              rcases Finset.mem_biUnion.mp hmU with ⟨s, _, hms⟩
              exact ⟨s, hms⟩
            · rw [if_neg hmU]
              by_cases hlt : ∃ s : Fin (t + 1), s.1 < j₀.1 ∧ m ∈ W' s
              · rw [if_pos hlt, if_pos]
                rcases hlt with ⟨s, _, hms⟩; exact ⟨s, hms⟩
              · rw [if_neg hlt, if_neg]
                rintro ⟨s, hms⟩
                by_cases hs : s.1 < j₀.1
                · exact hlt ⟨s, hs, hms⟩
                · exact hmU (Finset.mem_biUnion.mpr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, hms⟩)
          rw [hpt]
        · -- `a = b.castSucc` for some `b : Fin k`: equals `fanPoint W' base' j₀.castSucc b`!
          have halt : a.1 < k := by
            have := a.isLt
            have hne : a.1 ≠ k := fun h => halast (Fin.ext h)
            omega
          let b : Fin k := ⟨a.1, halt⟩
          have hab : a = b.castSucc := Fin.ext rfl
          rw [hab]
          have hpt : linePoint U baseU b.castSucc = fanPoint W' base' j₀.castSucc b := by
            funext m
            dsimp only [linePoint, baseU, fanPoint]
            have hU_iff : m ∈ U ↔ ∃ s : Fin (t + 1), j₀.1 ≤ s.1 ∧ m ∈ W' s := by
              simp [U]
            by_cases hlt : ∃ s : Fin (t + 1), s.1 < j₀.1 ∧ m ∈ W' s
            · have hnotU : m ∉ U := by
                intro hmU
                rcases hlt with ⟨s₁, hs₁, hm₁⟩
                rcases hU_iff.mp hmU with ⟨s₂, hs₂, hm₂⟩
                have hsne : s₁ ≠ s₂ := fun h => by rw [h] at hs₁; omega
                exact Finset.disjoint_left.mp (hW'_disj s₁ s₂ hsne) hm₁ hm₂
              rw [if_neg hnotU, if_pos hlt]
              have hlt' : ∃ s : Fin (t + 1), s.1 < j₀.castSucc.1 ∧ m ∈ W' s := hlt
              rw [if_pos hlt']
            · have hlt' : ¬ ∃ s : Fin (t + 1), s.1 < j₀.castSucc.1 ∧ m ∈ W' s := hlt
              rw [if_neg hlt']
              simp only [Fin.val_castSucc]
              by_cases hmU : m ∈ U
              · rw [if_pos hmU, if_pos (hU_iff.mp hmU)]
              · rw [if_neg hmU, if_neg hlt, if_neg (mt hU_iff.mpr hmU)]
          have hj₀_eq : (⟨j₀.castSucc.1, j₀.isLt⟩ : Fin (t + 1)) = j₀ := Fin.ext rfl
          rw [hpt, hfan'_lt j₀.castSucc j₀.isLt b, hj₀_eq, hg_spec, hfan₁ j₀ b, hj₀_col]
      · -- No collision! Extend `col₁` by `c z` to get a `(t + 1)`-fan with `t + 2` distinct colors!
        push Not at hcoll
        right
        let col' : Fin (t + 2) → Fin r := fun j =>
          if hj : j.1 < t + 1 then col₁ ⟨j.1, hj⟩ else c z
        have hcol'_inj : Function.Injective col' := by
          intro j₁ j₂ heq
          dsimp only [col'] at heq
          by_cases h1 : j₁.1 < t + 1 <;> by_cases h2 : j₂.1 < t + 1
          · rw [dif_pos h1, dif_pos h2] at heq
            exact Fin.ext (by simpa using congrArg Fin.val (hcol₁_inj heq))
          · rw [dif_pos h1, dif_neg h2] at heq
            exact absurd heq (hcoll ⟨j₁.1, h1⟩)
          · rw [dif_neg h1, dif_pos h2] at heq
            exact absurd heq.symm (hcoll ⟨j₂.1, h2⟩)
          · have hj₁ : j₁.1 = t + 1 := by have := j₁.isLt; omega
            have hj₂ : j₂.1 = t + 1 := by have := j₂.isLt; omega
            exact Fin.ext (by omega)
        refine ⟨W', base', col', hW'_ne, hW'_disj, hcol'_inj, ?_⟩
        intro j a
        dsimp only [col']
        by_cases hj : j.1 < t + 1
        · rw [dif_pos hj, hfan'_lt j hj a, hg_spec, hfan₁ ⟨j.1, hj⟩ a]
        · rw [dif_neg hj]
          have hjlast : j = Fin.last (t + 1) := Fin.ext (by have := j.isLt; simp; omega)
          rw [hjlast, hfan'_last a]

/-- **Full Hales–Jewett Theorem:**
For every alphabet size `k ≥ 1` and every number of colors `r ≥ 1`, there exists `N : ℕ`
such that every `r`-coloring `c : (Fin N → Fin k) → Fin r` admits a monochromatic
combinatorial line `(W, base)` (`W.Nonempty`). -/
theorem hales_jewett_theorem (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    ∃ N : ℕ, ∀ (c : (Fin N → Fin k) → Fin r),
      ∃ (W : Finset (Fin N)) (base : Fin N → Fin k), W.Nonempty ∧
        ∃ col : Fin r, ∀ a : Fin k, c (linePoint W base a) = col := by
  induction k generalizing r with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      refine ⟨1, fun c => ⟨Finset.univ, fun _ => 0, Finset.univ_nonempty, c (fun _ => 0), ?_⟩⟩
      intro a
      congr 1
      funext i
      exact Fin.ext (by
        have := (linePoint Finset.univ (fun _ => (0 : Fin (0 + 1))) a i).isLt
        have := (0 : Fin (0 + 1)).isLt
        omega)
    · have hk1 : 1 ≤ k := by omega
      -- Apply `hales_jewett_focusing` with `t = r`: an `(r + 1)`-tuple of distinct colors in `Fin r` is impossible!
      obtain ⟨N, hN⟩ := hales_jewett_focusing hk1 (fun r' hr' => ih r' hk1 hr') hr r
      refine ⟨N, ?_⟩
      intro c
      rcases hN c with hline | ⟨_, _, col, _, _, hcol_inj, _⟩
      · exact hline
      · exfalso
        have hcard := Fintype.card_le_of_injective col hcol_inj
        simp only [Fintype.card_fin] at hcard
        omega

/-- **Van der Waerden's Theorem (Derived Directly from Hales–Jewett):**
For every progression length `k ≥ 1` and every number of colors `r ≥ 1`, there exists `N : ℕ`
such that every `r`-coloring `c : ℕ → Fin r` contains a monochromatic `k`-term arithmetic
progression `a, a + d, ..., a + (k - 1) * d < N` with `0 < d`. -/
theorem van_der_waerden_theorem (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    ∃ N : ℕ, ∀ (c : ℕ → Fin r),
      ∃ (a d : ℕ), 0 < d ∧ a + (k - 1) * d < N ∧
        ∃ col : Fin r, ∀ j : Fin k, c (a + j.1 * d) = col := by
  obtain ⟨M, hM⟩ := hales_jewett_theorem k r hk hr
  refine ⟨M * (k - 1) + 1, ?_⟩
  intro c
  let Φ : (Fin M → Fin k) → ℕ := fun x => ∑ i : Fin M, (x i).1
  obtain ⟨W, base, hW_ne, col, hmono⟩ := hM (fun x => c (Φ x))
  let a : ℕ := ∑ i ∈ Finset.univ.filter (fun i : Fin M => i ∉ W), (base i).1
  let d : ℕ := W.card
  have hd_pos : 0 < d := Finset.card_pos.mpr hW_ne
  have hPhi_line : ∀ j : Fin k, Φ (linePoint W base j) = a + j.1 * d := by
    intro j
    dsimp only [Φ, linePoint, a, d]
    have hsplit : (∑ i : Fin M, (if i ∈ W then j else base i).1) =
        (∑ i ∈ Finset.univ.filter (fun i : Fin M => i ∈ W), (if i ∈ W then j else base i).1) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin M => i ∉ W), (if i ∈ W then j else base i).1) :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin M => i ∈ W) _).symm
    rw [hsplit]
    have h1 : (∑ i ∈ Finset.univ.filter (fun i : Fin M => i ∈ W), (if i ∈ W then j else base i).1) =
        j.1 * W.card := by
      have hflt : Finset.univ.filter (fun i : Fin M => i ∈ W) = W := by ext i; simp
      rw [hflt]
      calc ∑ i ∈ W, (if i ∈ W then j else base i).1
          = ∑ _i ∈ W, j.1 := Finset.sum_congr rfl fun i hi => by simp [hi]
        _ = j.1 * W.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have h2 : (∑ i ∈ Finset.univ.filter (fun i : Fin M => i ∉ W), (if i ∈ W then j else base i).1) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin M => i ∉ W), (base i).1 :=
      Finset.sum_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
    rw [h1, h2, add_comm]
  have hbound : a + (k - 1) * d < M * (k - 1) + 1 := by
    let jmax : Fin k := ⟨k - 1, by omega⟩
    have hle : Φ (linePoint W base jmax) ≤ M * (k - 1) := by
      dsimp only [Φ]
      calc ∑ i : Fin M, (linePoint W base jmax i).1
          ≤ ∑ _i : Fin M, (k - 1) := Finset.sum_le_sum fun i _ => by
            have := (linePoint W base jmax i).isLt; omega
        _ = M * (k - 1) := by simp
    have heq := hPhi_line jmax
    dsimp only [jmax] at heq
    rw [heq] at hle
    omega
  refine ⟨a, d, hd_pos, hbound, col, ?_⟩
  intro j
  rw [← hPhi_line j]
  exact hmono j

end HalesJewettAndVdW

end Arith4Ext.RamseyCombinatorics
