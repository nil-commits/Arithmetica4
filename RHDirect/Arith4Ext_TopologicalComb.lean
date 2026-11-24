/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-!
# Arithmetica4 Tier A Extension: Topological Combinatorics (`Arith4Ext.TopologicalComb`)

Clean, general, non-vacuous Tier A reusable library built 100% from scratch on targeted
Mathlib imports (`0` monolithic `import Mathlib`, `0` Tier C imports, `0` custom axioms).

## Exported API Summary (`namespace Arith4Ext.TopologicalComb`)
1. **Sperner's Simplicial Lemma (Freudenthal / Kuhn Triangulation):**
   - `KuhnSimplex d N`, `allKuhnSimplices`, `KuhnSimplex.vertex`, `IsSpernerColoring`, `KuhnSimplex.IsRainbow`
   - `sperner_lemma`: any proper Sperner coloring of the `N`-subdivided `d`-simplex `Δ_d(N)`
     has an **odd** number of rainbow simplices (proved by parity double-counting of facets).
   - `sperner_lemma_exists`: existence of at least one rainbow simplex in `Δ_d(N)`.
2. **Brouwer Fixed Point Theorem on the Standard `d`-Simplex `Δ_d`:**
   - `brouwer_fixed_point_simplex`: every continuous self-map of
     `{x : Fin (d + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}` has a fixed point `f x = x`.
3. **Ky Fan's Lemma, Combinatorial Tucker's Lemma, & Discrete Borsuk–Ulam:**
   - `ky_fan_lemma`: any antipodal nonzero labeling of `{-1, 0, 1}^n \ {0}` without a
     complementary face-pair `x ≼ y` (`lam x + lam y = 0`) contains a `+`-alternating
     maximal chain `v 0 ≺ ... ≺ v (n - 1)`.
   - `tucker_lemma_combinatorial`: any antipodal `lam : {-1, 0, 1}^n \ {0} → {±1, ..., ±(n - 1)}`
     admits `x ≼ y` with `lam x + lam y = 0`.
   - `tucker_lemma_linf`: `‖x - y‖_∞ ≤ 1` form of Combinatorial Tucker's Lemma.
   - `discrete_borsuk_ulam`: no antipodal `lam : {-1, 0, 1}^n \ {0} → {±1, ..., ±(n - 1)}`
     avoids complementary adjacent pairs.
4. **Lovász's 1978 Kneser Graph Chromatic Number Theorem (`χ(KG(n, k)) = n - 2k + 2`):**
   - `kneser_coloring_exists`: explicit proper `(n - 2k + 2)`-coloring of `KG(n, k)`.
   - `kneser_no_coloring_lt`: Matoušek's combinatorial Tucker-Lemma proof that no proper
     `(n - 2k + 1)`-coloring exists (`n ≥ 2k ≥ 2`).
   - `kneser_chromatic_number`: exact `SimpleGraph.chromaticNumber` equality `n - 2k + 2`.
-/

namespace Arith4Ext.TopologicalComb

open scoped BigOperators Classical
open Finset

/-! ## Section 0: Finite Parity Involution Principle -/

section ParityInvolution

/-- If `ι` is a fixed-point-free involution on a finite set `S`, then `Even S.card`. -/
lemma even_card_of_involution {α : Type*} [DecidableEq α] {S : Finset α}
    (ι : α → α)
    (hmaps : ∀ x ∈ S, ι x ∈ S)
    (hinv : ∀ x ∈ S, ι (ι x) = x)
    (hfp : ∀ x ∈ S, ι x ≠ x) :
    Even S.card := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · rw [Finset.card_empty] at hn; rw [← hn]; exact ⟨0, rfl⟩
    · let b := ι a
      have hb : b ∈ S := hmaps a ha
      have hab : b ≠ a := hfp a ha
      let S' := (S.erase a).erase b
      have hb_in : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hab, hb⟩
      have hcard' : S'.card + 2 = S.card := by
        have h1 := Finset.card_erase_add_one hb_in
        have h2 := Finset.card_erase_add_one ha
        dsimp only [S']
        omega
      have hmaps' : ∀ x ∈ S', ι x ∈ S' := by
        intro x hx
        have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
        have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
        have hxS : x ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hmaps x hxS⟩⟩
        · intro hEq; exact hxa (by rw [← hinv x hxS, hEq, hinv a ha])
        · intro hEq; exact hxb (by rw [← hinv x hxS, hEq])
      have hinv' : ∀ x ∈ S', ι (ι x) = x := fun x hx =>
        hinv x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
      have hfp' : ∀ x ∈ S', ι x ≠ x := fun x hx =>
        hfp x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
      have heven' : Even S'.card := ih S'.card (by omega) hmaps' hinv' hfp' rfl
      rcases heven' with ⟨k, hk⟩
      exact ⟨k + 1, by omega⟩

/-- Parity congruence between two sums over `S` when `f x ≡ g x (mod 2)` for every `x ∈ S`. -/
lemma sum_mod_two_eq {α : Type*} {S : Finset α} {f g : α → ℕ}
    (h : ∀ x ∈ S, f x % 2 = g x % 2) :
    (∑ x ∈ S, f x) % 2 = (∑ x ∈ S, g x) % 2 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    omega

end ParityInvolution

/-! ## Section 1: Sperner's Simplicial Lemma (Freudenthal / Kuhn Triangulation) -/

section SpernerLemma

/-- A `d`-simplex in the Kuhn / Freudenthal triangulation of the `N`-subdivided
standard `d`-simplex `Δ_d(N)`, represented in cumulative order-simplex coordinates
`0 ≤ y_0 ≤ y_1 ≤ ... ≤ y_{d-1} ≤ N`:
- `base : Fin d → ℕ` is monotone with `∀ j, base j < N`;
- `perm : Equiv.Perm (Fin d)` records the coordinate-increment order, with tie-breaking
  `base j = base (j + 1) → perm.symm (j + 1) < perm.symm j` so that every intermediate
  vertex stays monotone. -/
structure KuhnSimplex (d N : ℕ) where
  base : Fin d → ℕ
  perm : Equiv.Perm (Fin d)
  mono : Monotone base
  lt_N : ∀ j : Fin d, base j < N
  tie : ∀ (j : ℕ) (hj : j + 1 < d),
    base ⟨j, Nat.lt_of_succ_lt hj⟩ = base ⟨j + 1, hj⟩ →
    perm.symm ⟨j + 1, hj⟩ < perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩

instance {d N : ℕ} : DecidableEq (KuhnSimplex d N) := fun s t =>
  if h : s.base = t.base ∧ s.perm = t.perm then
    isTrue (by cases s; cases t; simp only at h; rcases h with ⟨rfl, rfl⟩; rfl)
  else
    isFalse (by rintro rfl; exact h ⟨rfl, rfl⟩)

lemma KuhnSimplex.ext {d N : ℕ} {s t : KuhnSimplex d N}
    (hb : s.base = t.base) (hp : s.perm = t.perm) : s = t := by
  cases s; cases t; cases hb; cases hp; rfl

/-- The `Finset` of all Kuhn `d`-simplices in `Δ_d(N)` (constructed explicitly via
`(Fin d → Fin N) × Equiv.Perm (Fin d)`). -/
noncomputable def allKuhnSimplices (d N : ℕ) : Finset (KuhnSimplex d N) :=
  let raw := (Finset.univ : Finset ((Fin d → Fin N) × Equiv.Perm (Fin d)))
  let valid := raw.filter fun p =>
    Monotone (fun j => (p.1 j).val) ∧
    ∀ (j : ℕ) (hj : j + 1 < d),
      (p.1 ⟨j, Nat.lt_of_succ_lt hj⟩).val = (p.1 ⟨j + 1, hj⟩).val →
      p.2.symm ⟨j + 1, hj⟩ < p.2.symm ⟨j, Nat.lt_of_succ_lt hj⟩
  valid.attach.image fun ⟨p, hp⟩ =>
    let h := (Finset.mem_filter.mp hp).2
    ⟨fun j => (p.1 j).val, p.2, h.1, fun j => (p.1 j).isLt, h.2⟩

lemma mem_allKuhnSimplices {d N : ℕ} (σ : KuhnSimplex d N) :
    σ ∈ allKuhnSimplices d N := by
  unfold allKuhnSimplices
  refine Finset.mem_image.mpr ?_
  let p : (Fin d → Fin N) × Equiv.Perm (Fin d) := (fun j => ⟨σ.base j, σ.lt_N j⟩, σ.perm)
  have hp : p ∈ (Finset.univ.filter fun q : (Fin d → Fin N) × Equiv.Perm (Fin d) =>
      Monotone (fun j => (q.1 j).val) ∧
      ∀ (j : ℕ) (hj : j + 1 < d),
        (q.1 ⟨j, Nat.lt_of_succ_lt hj⟩).val = (q.1 ⟨j + 1, hj⟩).val →
        q.2.symm ⟨j + 1, hj⟩ < q.2.symm ⟨j, Nat.lt_of_succ_lt hj⟩) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.mono, σ.tie⟩
  refine ⟨⟨p, hp⟩, Finset.mem_attach _ _, ?_⟩
  exact KuhnSimplex.ext rfl rfl

/-- The `k`-th vertex (`k : Fin (d + 1)`) of `σ : KuhnSimplex d N` in cumulative
order-simplex coordinates `Fin d → ℕ`: `y_j = base j + 1` if `perm.symm j < k`, else `base j`. -/
def KuhnSimplex.cumVertex {d N : ℕ} (σ : KuhnSimplex d N) (k : Fin (d + 1)) (j : Fin d) : ℕ :=
  σ.base j + if (σ.perm.symm j).val < k.val then 1 else 0

lemma KuhnSimplex.cumVertex_mono {d N : ℕ} (σ : KuhnSimplex d N) (k : Fin (d + 1)) :
    Monotone (σ.cumVertex k) := by
  intro j₁ j₂ hle
  suffices ∀ (m : ℕ) (hm : m + 1 < d),
      σ.cumVertex k ⟨m, Nat.lt_of_succ_lt hm⟩ ≤ σ.cumVertex k ⟨m + 1, hm⟩ by
    have hstep : ∀ (a b : ℕ) (ha : a < d) (hb : b < d), a ≤ b →
        σ.cumVertex k ⟨a, ha⟩ ≤ σ.cumVertex k ⟨b, hb⟩ := by
      intro a b ha hb hab
      induction b with
      | zero =>
        have : a = 0 := Nat.eq_zero_of_le_zero hab
        subst this; exact le_rfl
      | succ m ih =>
        rcases eq_or_lt_of_le hab with rfl | hlt
        · exact le_rfl
        · exact le_trans (ih (Nat.lt_of_succ_lt hb) (Nat.le_of_lt_succ hlt)) (this m hb)
    exact hstep j₁.val j₂.val j₁.isLt j₂.isLt hle
  intro m hm
  unfold KuhnSimplex.cumVertex
  have hble : σ.base ⟨m, Nat.lt_of_succ_lt hm⟩ ≤ σ.base ⟨m + 1, hm⟩ :=
    σ.mono (show (⟨m, Nat.lt_of_succ_lt hm⟩ : Fin d) ≤ ⟨m + 1, hm⟩ by
      change m ≤ m + 1; omega)
  rcases eq_or_lt_of_le hble with hEq | hlt
  · have htie := σ.tie m hm hEq
    rw [hEq]
    by_cases h1 : (σ.perm.symm ⟨m, Nat.lt_of_succ_lt hm⟩).val < k.val
    · have h2 : (σ.perm.symm ⟨m + 1, hm⟩).val < k.val := lt_trans htie h1
      simp [h1, h2]
    · simp only [h1, ↓reduceIte, add_zero]
      exact Nat.le_add_right _ _
  · split_ifs <;> omega

lemma KuhnSimplex.cumVertex_le_N {d N : ℕ} (σ : KuhnSimplex d N) (k : Fin (d + 1)) (j : Fin d) :
    σ.cumVertex k j ≤ N := by
  unfold KuhnSimplex.cumVertex
  have := σ.lt_N j
  split_ifs <;> omega

/-- Convert cumulative coordinates `y : Fin d → ℕ` (`0 ≤ y_0 ≤ ... ≤ y_{d-1} ≤ N`) to
barycentric lattice coordinates `v : Fin (d + 1) → ℕ` summing to `N`:
`v_0 = y_0`, `v_{j+1} = y_{j+1} - y_j`, `v_d = N - y_{d-1}` (and `v_0 = N` when `d = 0`). -/
def cumToBary {d : ℕ} (N : ℕ) (y : Fin d → ℕ) (i : Fin (d + 1)) : ℕ :=
  if h0 : i.val = 0 then
    if hd : 0 < d then y ⟨0, hd⟩ else N
  else if hlt : i.val < d then
    y ⟨i.val, hlt⟩ - y ⟨i.val - 1, by omega⟩
  else
    N - y ⟨d - 1, by omega⟩

lemma sum_cumToBary {d N : ℕ} {y : Fin d → ℕ}
    (hmono : Monotone y) (hle : ∀ j, y j ≤ N) :
    ∑ i : Fin (d + 1), cumToBary N y i = N := by
  cases d with
  | zero =>
    simp [cumToBary]
  | succ m =>
    have hprefix : ∀ (r : ℕ) (hr : r ≤ m),
        ∑ i ∈ Finset.univ.filter (fun i : Fin (m + 2) => i.val ≤ r), cumToBary N y i = y ⟨r, by omega⟩ := by
      intro r hr
      induction r with
      | zero =>
        have hfilt : Finset.univ.filter (fun i : Fin (m + 2) => i.val ≤ 0) = {(0 : Fin (m + 2))} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, Fin.val_zero]
          omega
        rw [hfilt, Finset.sum_singleton]
        simp [cumToBary]
      | succ k ih =>
        have hsplit : Finset.univ.filter (fun i : Fin (m + 2) => i.val ≤ k + 1) =
            insert ⟨k + 1, by omega⟩ (Finset.univ.filter (fun i : Fin (m + 2) => i.val ≤ k)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          omega
        have hnotmem : (⟨k + 1, by omega⟩ : Fin (m + 2)) ∉
            Finset.univ.filter (fun i : Fin (m + 2) => i.val ≤ k) := by
          simp
        rw [hsplit, Finset.sum_insert hnotmem, ih (by omega)]
        have hval : cumToBary N y ⟨k + 1, by omega⟩ = y ⟨k + 1, by omega⟩ - y ⟨k, by omega⟩ := by
          unfold cumToBary
          have h2 : k + 1 < m + 1 := by omega
          simp [h2]
        rw [hval]
        have hle_k : y ⟨k, by omega⟩ ≤ y ⟨k + 1, by omega⟩ :=
          hmono (show (⟨k, by omega⟩ : Fin (m + 1)) ≤ ⟨k + 1, by omega⟩ by change k ≤ k + 1; omega)
        omega
    have huniv : (Finset.univ : Finset (Fin (m + 2))) =
        insert ⟨m + 1, by omega⟩ (Finset.univ.filter (fun i : Fin (m + 2) => i.val ≤ m)) := by
      ext i
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and, Fin.ext_iff, true_iff]
      have := i.isLt; omega
    have hnotmem : (⟨m + 1, by omega⟩ : Fin (m + 2)) ∉
        Finset.univ.filter (fun i : Fin (m + 2) => i.val ≤ m) := by simp
    rw [huniv, Finset.sum_insert hnotmem, hprefix m le_rfl]
    have hlast : cumToBary N y ⟨m + 1, by omega⟩ = N - y ⟨m, by omega⟩ := by
      unfold cumToBary
      simp
    rw [hlast]
    have hle_m := hle ⟨m, by omega⟩
    omega

/-- The `k`-th vertex of `σ : KuhnSimplex d N` in barycentric lattice coordinates
`Fin (d + 1) → ℕ` summing to `N`. -/
def KuhnSimplex.vertex {d N : ℕ} (σ : KuhnSimplex d N) (k : Fin (d + 1)) : Fin (d + 1) → ℕ :=
  cumToBary N (σ.cumVertex k)

lemma KuhnSimplex.vertex_sum {d N : ℕ} (σ : KuhnSimplex d N) (k : Fin (d + 1)) :
    ∑ i : Fin (d + 1), σ.vertex k i = N :=
  sum_cumToBary (σ.cumVertex_mono k) (σ.cumVertex_le_N k)

/-- Any two vertices of the same Kuhn simplex differ by at most `1` in every barycentric coordinate. -/
lemma KuhnSimplex.vertex_diff_le_one {d N : ℕ} (σ : KuhnSimplex d N)
    (k₁ k₂ : Fin (d + 1)) (i : Fin (d + 1)) :
    |((σ.vertex k₁ i : ℝ) - (σ.vertex k₂ i : ℝ))| ≤ 1 := by
  have hcum : ∀ j : Fin d, σ.base j ≤ σ.cumVertex k₁ j ∧ σ.cumVertex k₁ j ≤ σ.base j + 1 ∧
      σ.base j ≤ σ.cumVertex k₂ j ∧ σ.cumVertex k₂ j ≤ σ.base j + 1 := by
    intro j; unfold KuhnSimplex.cumVertex; split_ifs <;> omega
  unfold KuhnSimplex.vertex cumToBary
  split_ifs with h0 hd hlt
  · have h1 := hcum ⟨0, hd⟩
    rw [abs_le]; constructor <;>
    · have : (σ.base ⟨0, hd⟩ : ℝ) ≤ (σ.cumVertex k₁ ⟨0, hd⟩ : ℝ) := by exact_mod_cast h1.1
      have : (σ.cumVertex k₁ ⟨0, hd⟩ : ℝ) ≤ (σ.base ⟨0, hd⟩ : ℝ) + 1 := by exact_mod_cast h1.2.1
      have : (σ.base ⟨0, hd⟩ : ℝ) ≤ (σ.cumVertex k₂ ⟨0, hd⟩ : ℝ) := by exact_mod_cast h1.2.2.1
      have : (σ.cumVertex k₂ ⟨0, hd⟩ : ℝ) ≤ (σ.base ⟨0, hd⟩ : ℝ) + 1 := by exact_mod_cast h1.2.2.2
      linarith
  · simp
  · have hj1 := hcum ⟨i.val, hlt⟩
    have hj0 := hcum ⟨i.val - 1, by omega⟩
    have hle1 : σ.cumVertex k₁ ⟨i.val - 1, by omega⟩ ≤ σ.cumVertex k₁ ⟨i.val, hlt⟩ :=
      σ.cumVertex_mono k₁ (show (⟨i.val - 1, by omega⟩ : Fin d) ≤ ⟨i.val, hlt⟩ by
        change i.val - 1 ≤ i.val; omega)
    have hle2 : σ.cumVertex k₂ ⟨i.val - 1, by omega⟩ ≤ σ.cumVertex k₂ ⟨i.val, hlt⟩ :=
      σ.cumVertex_mono k₂ (show (⟨i.val - 1, by omega⟩ : Fin d) ≤ ⟨i.val, hlt⟩ by
        change i.val - 1 ≤ i.val; omega)
    -- Both `y(i) - y(i-1)` equal `(base i - base (i-1)) + δ`, where `δ ∈ {-1, 0, 1}`,
    -- and wait: could one have `δ₁ = +1` and the other `δ₂ = -1`?
    -- NO! Because `y(i) - base(i) = 1 ↔ perm⁻¹(i) < k`, so `δ₁ = 1` means `perm⁻¹(i) < k₁ ≤ perm⁻¹(i-1)`
    -- while `δ₂ = -1` means `perm⁻¹(i-1) < k₂ ≤ perm⁻¹(i)`, IMPOSSIBLE simultaneously!
    have hno_opp : ¬ (σ.cumVertex k₁ ⟨i.val, hlt⟩ = σ.base ⟨i.val, hlt⟩ + 1 ∧
        σ.cumVertex k₁ ⟨i.val - 1, by omega⟩ = σ.base ⟨i.val - 1, by omega⟩ ∧
        σ.cumVertex k₂ ⟨i.val, hlt⟩ = σ.base ⟨i.val, hlt⟩ ∧
        σ.cumVertex k₂ ⟨i.val - 1, by omega⟩ = σ.base ⟨i.val - 1, by omega⟩ + 1) := by
      unfold KuhnSimplex.cumVertex
      rintro ⟨h1, h2, h3, h4⟩
      have ha : (σ.perm.symm ⟨i.val, hlt⟩).val < k₁.val := by by_contra hc; simp [hc] at h1
      have hb : ¬ (σ.perm.symm ⟨i.val - 1, by omega⟩).val < k₁.val := by by_contra hc; simp [hc] at h2
      have hc : ¬ (σ.perm.symm ⟨i.val, hlt⟩).val < k₂.val := by by_contra hc'; simp [hc'] at h3
      have hd' : (σ.perm.symm ⟨i.val - 1, by omega⟩).val < k₂.val := by by_contra hc'; simp [hc'] at h4
      omega
    have hno_opp' : ¬ (σ.cumVertex k₂ ⟨i.val, hlt⟩ = σ.base ⟨i.val, hlt⟩ + 1 ∧
        σ.cumVertex k₂ ⟨i.val - 1, by omega⟩ = σ.base ⟨i.val - 1, by omega⟩ ∧
        σ.cumVertex k₁ ⟨i.val, hlt⟩ = σ.base ⟨i.val, hlt⟩ ∧
        σ.cumVertex k₁ ⟨i.val - 1, by omega⟩ = σ.base ⟨i.val - 1, by omega⟩ + 1) := by
      unfold KuhnSimplex.cumVertex
      rintro ⟨h1, h2, h3, h4⟩
      have ha : (σ.perm.symm ⟨i.val, hlt⟩).val < k₂.val := by by_contra hc; simp [hc] at h1
      have hb : ¬ (σ.perm.symm ⟨i.val - 1, by omega⟩).val < k₂.val := by by_contra hc; simp [hc] at h2
      have hc : ¬ (σ.perm.symm ⟨i.val, hlt⟩).val < k₁.val := by by_contra hc'; simp [hc'] at h3
      have hd' : (σ.perm.symm ⟨i.val - 1, by omega⟩).val < k₁.val := by by_contra hc'; simp [hc'] at h4
      omega
    have hnat1 : σ.cumVertex k₁ ⟨i.val, hlt⟩ - σ.cumVertex k₁ ⟨i.val - 1, by omega⟩ ≤
        (σ.cumVertex k₂ ⟨i.val, hlt⟩ - σ.cumVertex k₂ ⟨i.val - 1, by omega⟩) + 1 := by omega
    have hnat2 : σ.cumVertex k₂ ⟨i.val, hlt⟩ - σ.cumVertex k₂ ⟨i.val - 1, by omega⟩ ≤
        (σ.cumVertex k₁ ⟨i.val, hlt⟩ - σ.cumVertex k₁ ⟨i.val - 1, by omega⟩) + 1 := by omega
    rw [abs_le]
    have hr1 : ((σ.cumVertex k₁ ⟨i.val, hlt⟩ - σ.cumVertex k₁ ⟨i.val - 1, by omega⟩ : ℕ) : ℝ) ≤
        ((σ.cumVertex k₂ ⟨i.val, hlt⟩ - σ.cumVertex k₂ ⟨i.val - 1, by omega⟩ : ℕ) : ℝ) + 1 := by
      exact_mod_cast hnat1
    have hr2 : ((σ.cumVertex k₂ ⟨i.val, hlt⟩ - σ.cumVertex k₂ ⟨i.val - 1, by omega⟩ : ℕ) : ℝ) ≤
        ((σ.cumVertex k₁ ⟨i.val, hlt⟩ - σ.cumVertex k₁ ⟨i.val - 1, by omega⟩ : ℕ) : ℝ) + 1 := by
      exact_mod_cast hnat2
    constructor <;> linarith
  · have hd_pos : 0 < d := by have := i.isLt; omega
    have h1 := hcum ⟨d - 1, by omega⟩
    have hle1 := σ.cumVertex_le_N k₁ ⟨d - 1, by omega⟩
    have hle2 := σ.cumVertex_le_N k₂ ⟨d - 1, by omega⟩
    have hnat1 : N - σ.cumVertex k₁ ⟨d - 1, by omega⟩ ≤ (N - σ.cumVertex k₂ ⟨d - 1, by omega⟩) + 1 := by omega
    have hnat2 : N - σ.cumVertex k₂ ⟨d - 1, by omega⟩ ≤ (N - σ.cumVertex k₁ ⟨d - 1, by omega⟩) + 1 := by omega
    rw [abs_le]
    have hr1 : ((N - σ.cumVertex k₁ ⟨d - 1, by omega⟩ : ℕ) : ℝ) ≤
        ((N - σ.cumVertex k₂ ⟨d - 1, by omega⟩ : ℕ) : ℝ) + 1 := by exact_mod_cast hnat1
    have hr2 : ((N - σ.cumVertex k₂ ⟨d - 1, by omega⟩ : ℕ) : ℝ) ≤
        ((N - σ.cumVertex k₁ ⟨d - 1, by omega⟩ : ℕ) : ℝ) + 1 := by exact_mod_cast hnat2
    constructor <;> linarith

/-- A coloring `c : (Fin (d + 1) → ℕ) → Fin (d + 1)` is a **proper Sperner coloring** on
`Δ_d(N)` if every vertex `v` with `∑ i, v i = N` receives a color `c v` whose coordinate
`v (c v)` is nonzero (equivalently, `v i = 0 → c v ≠ i`). -/
def IsSpernerColoring (d N : ℕ) (c : (Fin (d + 1) → ℕ) → Fin (d + 1)) : Prop :=
  ∀ v : Fin (d + 1) → ℕ, (∑ i, v i = N) → v (c v) ≠ 0

/-- A Kuhn simplex `σ` is **rainbow** (pan-chromatic) under `c` if its `d + 1` vertices
receive all `d + 1` distinct colors `Fin (d + 1)`. -/
def KuhnSimplex.IsRainbow {d N : ℕ} (c : (Fin (d + 1) → ℕ) → Fin (d + 1))
    (σ : KuhnSimplex d N) : Prop :=
  Function.Bijective (fun k : Fin (d + 1) => c (σ.vertex k))

/-- Local facet parity for `f : Fin (d + 1) → Fin (d + 1)`:
the number of `k : Fin (d + 1)` whose omitted-`k` image equals `{i : Fin (d + 1) | i.val < d}`
has the same parity as `(if Function.Bijective f then 1 else 0)`. -/
private lemma local_sperner_facet_parity {d : ℕ} (f : Fin (d + 1) → Fin (d + 1)) :
    ((Finset.univ : Finset (Fin (d + 1))).filter (fun k =>
      ∀ r : Fin d, ∃ j : Fin (d + 1), j ≠ k ∧ f j = r.castSucc)).card % 2 =
    if Function.Bijective f then 1 else 0 := by
  let good := (Finset.univ : Finset (Fin (d + 1))).filter (fun k =>
    ∀ r : Fin d, ∃ j : Fin (d + 1), j ≠ k ∧ f j = r.castSucc)
  by_cases hbij : Function.Bijective f
  · simp only [hbij, ↓reduceIte]
    obtain ⟨k₀, hk₀⟩ := hbij.2 (Fin.last d)
    have hgood_eq : good = {k₀} := by
      ext k
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hk
        by_contra hne
        -- Every r : Fin d has a preimage j ≠ k; since f is injective, k cannot map to any r.castSucc!
        have hnotlt : ∀ r : Fin d, f k ≠ r.castSucc := by
          intro r hEq
          obtain ⟨j, hjk, hjr⟩ := hk r
          exact hjk (hbij.1 (hjr.trans hEq.symm))
        have hlast : f k = Fin.last d := by
          ext; change (f k).val = d
          have hlt := (f k).isLt
          by_contra hne'
          exact hnotlt ⟨(f k).val, by omega⟩ (Fin.ext rfl)
        exact hne (hbij.1 (hlast.trans hk₀.symm))
      · rintro rfl r
        obtain ⟨j, hj⟩ := hbij.2 r.castSucc
        refine ⟨j, ?_, hj⟩
        rintro rfl
        have : r.castSucc = Fin.last d := hj.symm.trans hk₀
        have := congrArg Fin.val this; simp at this; omega
    change good.card % 2 = 1
    rw [hgood_eq, Finset.card_singleton]
  · simp only [hbij, ↓reduceIte]
    -- Since f is not bijective on a finite type of equal size, it is not surjective!
    have hnsurj : ¬ Function.Surjective f := fun h => hbij ⟨Finite.injective_iff_surjective.mpr h, h⟩
    have hninj : ¬ Function.Injective f := fun h => hbij ⟨h, Finite.injective_iff_surjective.mp h⟩
    by_cases hmiss : ∃ r : Fin d, ∀ j : Fin (d + 1), f j ≠ r.castSucc
    · obtain ⟨r₀, hr₀⟩ := hmiss
      have hgood_eq : good = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro k hk
        obtain ⟨j, _, hj⟩ := (Finset.mem_filter.mp hk).2 r₀
        exact hr₀ j hj
      change good.card % 2 = 0
      rw [hgood_eq]; simp
    · push Not at hmiss
      -- Every r : Fin d IS in the image of f, so Fin.last d is NOT in the image of f!
      have hno_last : ∀ j : Fin (d + 1), f j ≠ Fin.last d := by
        intro j hj
        apply hnsurj
        intro y
        by_cases hy : y.val < d
        · obtain ⟨x, hx⟩ := hmiss ⟨y.val, hy⟩
          exact ⟨x, hx.trans (Fin.ext rfl)⟩
        · have : y = Fin.last d := Fin.ext (by change y.val = d; have := y.isLt; omega)
          exact ⟨j, hj.trans this.symm⟩
      -- Thus f takes values in {0, ..., d - 1} (d values from d + 1 elements),
      -- and hits ALL d values, so EXACTLY ONE value r₀ is hit TWICE and all others ONCE!
      have hfib_sum : ∑ r : Fin d, (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card = d + 1 := by
        have hpart : (Finset.univ : Finset (Fin (d + 1))) =
            Finset.univ.biUnion (fun r : Fin d => Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)) := by
          ext j
          simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, true_iff]
          have hlt : (f j).val < d := by
            have := (f j).isLt
            by_contra hc
            exact hno_last j (Fin.ext (by change (f j).val = d; omega))
          exact ⟨⟨(f j).val, hlt⟩, Fin.ext rfl⟩
        have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin d)) : Set (Fin d))
            (fun r : Fin d => Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)) := by
          intro r₁ _ r₂ _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro j h1 h2
          have e1 := (Finset.mem_filter.mp h1).2
          have e2 := (Finset.mem_filter.mp h2).2
          exact hne (Fin.ext (by simpa using congrArg Fin.val (e1.symm.trans e2)))
        have hc := congrArg Finset.card hpart
        rw [Finset.card_univ, Fintype.card_fin, Finset.card_biUnion hdisj] at hc
        exact hc.symm
      have hfib_ge1 : ∀ r : Fin d, 1 ≤ (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card := by
        intro r
        obtain ⟨j, hj⟩ := hmiss r
        exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
      -- Find the unique r₀ with fiber card ≥ 2!
      have hex_ge2 : ∃ r₀ : Fin d, 2 ≤ (Finset.univ.filter (fun j : Fin (d + 1) => f j = r₀.castSucc)).card := by
        by_contra hall
        push Not at hall
        have hle : ∑ r : Fin d, (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card ≤ d := by
          calc ∑ r : Fin d, (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card
              ≤ ∑ _r : Fin d, 1 := Finset.sum_le_sum fun r _ => by have := hall r; omega
            _ = d := by simp
        omega
      obtain ⟨r₀, hr₀_ge2⟩ := hex_ge2
      have hr₀_eq2 : (Finset.univ.filter (fun j : Fin (d + 1) => f j = r₀.castSucc)).card = 2 ∧
          ∀ r : Fin d, r ≠ r₀ → (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card = 1 := by
        have hsum_rest : ∑ r ∈ Finset.univ.erase r₀,
            (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card ≥ d - 1 := by
          calc ∑ r ∈ Finset.univ.erase r₀, (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card
              ≥ ∑ _r ∈ Finset.univ.erase r₀, 1 := Finset.sum_le_sum fun r _ => hfib_ge1 r
            _ = d - 1 := by simp
        have hsplit := Finset.add_sum_erase Finset.univ
          (fun r : Fin d => (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card)
          (Finset.mem_univ r₀)
        have hd_pos : 1 ≤ d := Nat.pos_of_ne_zero (fun h => by subst h; exact Fin.elim0 r₀)
        have h2 : (Finset.univ.filter (fun j : Fin (d + 1) => f j = r₀.castSucc)).card = 2 := by omega
        refine ⟨h2, fun r hr => ?_⟩
        by_contra hne1
        have hge2' : 2 ≤ (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card := by
          have := hfib_ge1 r; omega
        have hrest_ge : ∑ r' ∈ Finset.univ.erase r₀,
            (Finset.univ.filter (fun j : Fin (d + 1) => f j = r'.castSucc)).card ≥ d := by
          have hsp := Finset.add_sum_erase (Finset.univ.erase r₀)
            (fun r' : Fin d => (Finset.univ.filter (fun j : Fin (d + 1) => f j = r'.castSucc)).card)
            (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ _⟩)
          have hrem : ∑ r' ∈ (Finset.univ.erase r₀).erase r,
              (Finset.univ.filter (fun j : Fin (d + 1) => f j = r'.castSucc)).card ≥ d - 2 := by
            calc ∑ r' ∈ (Finset.univ.erase r₀).erase r,
                  (Finset.univ.filter (fun j : Fin (d + 1) => f j = r'.castSucc)).card
                ≥ ∑ _r' ∈ (Finset.univ.erase r₀).erase r, 1 := Finset.sum_le_sum fun r' _ => hfib_ge1 r'
              _ = ((Finset.univ.erase r₀).erase r).card := by simp
              _ = d - 2 := by
                rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ _⟩),
                  Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
                omega
          omega
        omega
      -- Therefore `good` is EXACTLY the 2-element fiber of `r₀`!
      have hgood_eq : good = Finset.univ.filter (fun j : Fin (d + 1) => f j = r₀.castSucc) := by
        ext k
        simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hk
          by_contra hne
          have hlt : (f k).val < d := by
            have := (f k).isLt
            by_contra hc; exact hno_last k (Fin.ext (by change (f k).val = d; omega))
          let rk : Fin d := ⟨(f k).val, hlt⟩
          have hrk_ne : rk ≠ r₀ := fun h => hne (by rw [← h]; exact Fin.ext rfl)
          obtain ⟨j, hjk, hj⟩ := hk rk
          have hfib1 := hr₀_eq2.2 rk hrk_ne
          have h2le : 2 ≤ (Finset.univ.filter (fun x : Fin (d + 1) => f x = rk.castSucc)).card := by
            have hsub : ({k, j} : Finset (Fin (d + 1))) ⊆
                Finset.univ.filter (fun x : Fin (d + 1) => f x = rk.castSucc) := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl
              · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.ext rfl⟩
              · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
            have hc2 : ({k, j} : Finset (Fin (d + 1))).card = 2 := Finset.card_pair hjk.symm
            exact hc2 ▸ Finset.card_le_card hsub
          omega
        · intro hk r
          by_cases hr : r = r₀
          · subst hr
            obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega :
              1 < (Finset.univ.filter (fun j : Fin (d + 1) => f j = r.castSucc)).card)
            by_cases hka : a = k
            · exact ⟨b, by rw [← hka]; exact hab.symm, (Finset.mem_filter.mp hb).2⟩
            · exact ⟨a, hka, (Finset.mem_filter.mp ha).2⟩
          · obtain ⟨j, hj⟩ := hmiss r
            refine ⟨j, ?_, hj⟩
            rintro rfl
            exact hr (Fin.ext (by simpa using congrArg Fin.val (hj.symm.trans hk)))
      change good.card % 2 = 0
      rw [hgood_eq, hr₀_eq2.1]

/-- Cyclic left shift on `Fin (d + 1)`: `0 → 1 → ... → d → 0`. -/
private def cycShift (d : ℕ) : Equiv.Perm (Fin (d + 1)) where
  toFun i := if h : i.val + 1 < d + 1 then ⟨i.val + 1, h⟩ else ⟨0, Nat.succ_pos d⟩
  invFun i := if h : 0 < i.val then ⟨i.val - 1, by omega⟩ else ⟨d, Nat.lt_succ_self d⟩
  left_inv i := by
    ext; dsimp only
    by_cases h : i.val + 1 < d + 1
    · simp [h]
    · have hi : i.val = d := by have := i.isLt; omega
      simp [hi]
  right_inv i := by
    ext; dsimp only
    by_cases h : 0 < i.val
    · have hlt : i.val - 1 + 1 < d + 1 := by have := i.isLt; omega
      simp [h, hlt]; omega
    · have hi : i.val = 0 := by omega
      simp [hi]

set_option maxHeartbeats 1200000 in
/-- **Sperner's Simplicial Lemma (Freudenthal / Kuhn Triangulation):**
For any dimension `d : ℕ`, subdivision `N ≥ 1`, and proper Sperner coloring
`c : (Fin (d + 1) → ℕ) → Fin (d + 1)` on `Δ_d(N)`, the number of rainbow Kuhn
`d`-simplices in `Δ_d(N)` is **odd**. -/
theorem sperner_lemma (d : ℕ) {N : ℕ} (hN : 1 ≤ N)
    (c : (Fin (d + 1) → ℕ) → Fin (d + 1))
    (hc : IsSpernerColoring d N c) :
    Odd ((allKuhnSimplices d N).filter (KuhnSimplex.IsRainbow c)).card := by
  induction d with
  | zero =>
    -- Base case d = 0: unique Kuhn 0-simplex with unique vertex `fun _ => N`, unique color 0!
    let σ₀ : KuhnSimplex 0 N :=
      ⟨Fin.elim0, Equiv.refl _, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun j hj => by omega⟩
    have hall : allKuhnSimplices 0 N = {σ₀} := by
      ext σ
      simp only [Finset.mem_singleton]
      constructor
      · intro _; exact KuhnSimplex.ext (funext fun i => Fin.elim0 i) (Equiv.ext fun i => Fin.elim0 i)
      · rintro rfl; exact mem_allKuhnSimplices σ₀
    have hrb : σ₀.IsRainbow c := by
      refine ⟨fun a b _ => Fin.ext (by have := a.isLt; have := b.isLt; omega),
        fun y => ⟨0, Fin.ext (by have := (c (σ₀.vertex 0)).isLt; have := y.isLt; omega)⟩⟩
    rw [hall, Finset.filter_singleton, if_pos hrb, Finset.card_singleton]
    exact odd_one
  | succ m ih =>
    -- Induction step d = m + 1 ≥ 1!
    -- Count pairs (σ, k) ∈ allKuhnSimplices (m + 1) N × Fin (m + 2) whose omitted-k facet has colors {0, ..., m}!
    let D := m + 1
    let goodPairs : Finset (KuhnSimplex D N × Fin (D + 1)) :=
      ((allKuhnSimplices D N) ×ˢ (Finset.univ : Finset (Fin (D + 1)))).filter fun p =>
        ∀ r : Fin D, ∃ j : Fin (D + 1), j ≠ p.2 ∧ c (p.1.vertex j) = r.castSucc
    -- Step 1: By local_sperner_facet_parity, goodPairs.card ≡ (#rainbow simplices) (mod 2)!
    have hmod_rainbow : goodPairs.card % 2 =
        ((allKuhnSimplices D N).filter (KuhnSimplex.IsRainbow c)).card % 2 := by
      have hcard_eq : goodPairs.card =
          ∑ σ ∈ allKuhnSimplices D N,
            ((Finset.univ : Finset (Fin (D + 1))).filter (fun k =>
              ∀ r : Fin D, ∃ j : Fin (D + 1), j ≠ k ∧ c (σ.vertex j) = r.castSucc)).card := by
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.card_filter]
      have hrb_eq : ((allKuhnSimplices D N).filter (KuhnSimplex.IsRainbow c)).card =
          ∑ σ ∈ allKuhnSimplices D N, if KuhnSimplex.IsRainbow c σ then 1 else 0 := by
        rw [Finset.card_filter]
      rw [hcard_eq, hrb_eq]
      refine sum_mod_two_eq fun σ _ => ?_
      have hloc := local_sperner_facet_parity (fun k => c (σ.vertex k))
      have hrb_iff : KuhnSimplex.IsRainbow c σ ↔ Function.Bijective (fun k => c (σ.vertex k)) := Iff.rfl
      rw [hloc]
      by_cases hb : Function.Bijective (fun k => c (σ.vertex k))
      · rw [if_pos hb, if_pos (hrb_iff.mpr hb)]
      · rw [if_neg hb, if_neg (mt hrb_iff.mp hb)]
    -- Step 2: Classify every (σ, k) ∈ goodPairs as either:
    --   (B) Boundary on face D: k = 0 ∧ σ.perm 0 = Fin.last m ∧ σ.base (Fin.last m) = N - 1
    --   (I) Interior: everything else!
    -- Show that NO (σ, k) ∈ goodPairs can lie on any boundary face i < D!
    have hno_bdry_lt : ∀ p ∈ goodPairs,
        (p.2.val = 0 → p.1.base (p.1.perm 0) = N - 1 → p.1.perm 0 = Fin.last m) ∧
        (p.2.val = D → 0 < p.1.base (p.1.perm (Fin.last m))) ∧
        (∀ (h0 : 0 < p.2.val) (hD : p.2.val < D),
          ∀ (j : ℕ) (hj : j + 1 < D),
            p.1.perm ⟨p.2.val - 1, by omega⟩ = ⟨j + 1, hj⟩ →
            p.1.perm ⟨p.2.val, hD⟩ = ⟨j, Nat.lt_of_succ_lt hj⟩ →
            p.1.base ⟨j, Nat.lt_of_succ_lt hj⟩ ≠ p.1.base ⟨j + 1, hj⟩) := by
      intro ⟨σ, k⟩ hp
      have hgood := (Finset.mem_filter.mp hp).2
      dsimp only at hgood ⊢
      refine ⟨?_, ?_, ?_⟩
      · -- If base (perm 0) = N - 1, then perm 0 MUST be Fin.last m by monotonicity + tie!
        intro _ hmax
        by_contra hne
        have hlt : (σ.perm 0).val < m := by
          have := (σ.perm 0).isLt
          have hvalne : (σ.perm 0).val ≠ m := fun h => hne (Fin.ext h)
          omega
        have hle1 : σ.base (σ.perm 0) ≤ σ.base ⟨(σ.perm 0).val + 1, by omega⟩ :=
          σ.mono (show σ.perm 0 ≤ ⟨(σ.perm 0).val + 1, by omega⟩ by change (σ.perm 0).val ≤ (σ.perm 0).val + 1; omega)
        have hltN := σ.lt_N ⟨(σ.perm 0).val + 1, by omega⟩
        have hEq : σ.base ⟨(σ.perm 0).val, by omega⟩ = σ.base ⟨(σ.perm 0).val + 1, by omega⟩ := by
          have : (⟨(σ.perm 0).val, by omega⟩ : Fin D) = σ.perm 0 := Fin.ext rfl
          rw [this]; omega
        have htie := σ.tie (σ.perm 0).val (by omega) hEq
        have h0eq : (⟨(σ.perm 0).val, by omega⟩ : Fin D) = σ.perm 0 := Fin.ext rfl
        rw [h0eq, Equiv.symm_apply_apply] at htie
        exact Nat.not_lt_zero _ htie
      · -- If k = D and base (perm (Fin.last m)) = 0, then perm (Fin.last m) = 0,
        -- so ALL vertices j ≠ D have barycentric coord 0 equal to 0, hence no vertex has color 0!
        intro hkD
        by_contra h0
        have hb0 : σ.base (σ.perm (Fin.last m)) = 0 := by omega
        have hlast0 : σ.perm (Fin.last m) = 0 := by
          by_contra hne
          have hpos : 0 < (σ.perm (Fin.last m)).val := by
            have hvalne : (σ.perm (Fin.last m)).val ≠ 0 := fun h => hne (Fin.ext h)
            omega
          have hle1 : σ.base ⟨(σ.perm (Fin.last m)).val - 1, by omega⟩ ≤ σ.base (σ.perm (Fin.last m)) :=
            σ.mono (show (⟨(σ.perm (Fin.last m)).val - 1, by omega⟩ : Fin D) ≤ σ.perm (Fin.last m) by
              change (σ.perm (Fin.last m)).val - 1 ≤ (σ.perm (Fin.last m)).val; omega)
          have hEq : σ.base ⟨(σ.perm (Fin.last m)).val - 1, by omega⟩ =
              σ.base ⟨(σ.perm (Fin.last m)).val - 1 + 1, by omega⟩ := by
            have : (⟨(σ.perm (Fin.last m)).val - 1 + 1, by omega⟩ : Fin D) = σ.perm (Fin.last m) :=
              Fin.ext (by dsimp only; omega)
            rw [this]; omega
          have htie := σ.tie ((σ.perm (Fin.last m)).val - 1) (by omega) hEq
          have heq' : (⟨(σ.perm (Fin.last m)).val - 1 + 1, by omega⟩ : Fin D) = σ.perm (Fin.last m) :=
            Fin.ext (by dsimp only; omega)
          rw [heq', Equiv.symm_apply_apply] at htie
          have hlt' := (σ.perm.symm ⟨(σ.perm (Fin.last m)).val - 1, by omega⟩).isLt
          change m < _ at htie
          omega
        obtain ⟨j, hjk, hjc⟩ := hgood ⟨0, Nat.succ_pos m⟩
        have hjlt : j.val < D := by have := j.isLt; have : j.val ≠ k.val := Fin.val_ne_of_ne hjk; omega
        have hv0 : σ.vertex j 0 = 0 := by
          unfold KuhnSimplex.vertex cumToBary KuhnSimplex.cumVertex
          have hsymm0 : σ.perm.symm 0 = Fin.last m := by
            rw [← hlast0, Equiv.symm_apply_apply]
          have hnotlt : ¬ (σ.perm.symm 0).val < j.val := by
            rw [hsymm0]; change ¬ m < j.val; omega
          have hbase0 : σ.base 0 = 0 := by
            rw [← hlast0]; exact hb0
          have h0eq : (⟨0, Nat.succ_pos m⟩ : Fin D) = 0 := rfl
          simp only [Fin.val_zero, ↓reduceDIte, show 0 < D from Nat.succ_pos m, h0eq, hbase0, hnotlt, ↓reduceIte, add_zero]
        have hsp := hc (σ.vertex j) (σ.vertex_sum j)
        rw [hjc] at hsp
        exact hsp hv0
      · -- If 0 < k < D and perm(k-1) = j+1, perm(k) = j, base j = base (j+1),
        -- then ALL vertices r ≠ k have barycentric coord (j+1) equal to 0, hence no vertex has color j+1!
        intro h0 hD j hj hp1 hp2 hEq
        obtain ⟨r, hrk, hrc⟩ := hgood ⟨j + 1, hj⟩
        have hvr : σ.vertex r ⟨j + 1, by omega⟩ = 0 := by
          unfold KuhnSimplex.vertex cumToBary KuhnSimplex.cumVertex
          have h1 : ¬ (j + 1 = 0) := by omega
          have h2 : j + 1 < D := hj
          simp only [h1, ↓reduceDIte, h2]
          have hs1 : σ.perm.symm ⟨j + 1, hj⟩ = ⟨k.val - 1, by omega⟩ := by
            rw [← hp1, Equiv.symm_apply_apply]
          have hs2 : σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩ = ⟨k.val, hD⟩ := by
            rw [← hp2, Equiv.symm_apply_apply]
          have hsub : (⟨j + 1 - 1, by omega⟩ : Fin D) = ⟨j, Nat.lt_of_succ_lt hj⟩ := Fin.ext (by simp)
          rw [hsub, hs1, hs2, hEq]
          have hrne : r.val ≠ k.val := Fin.val_ne_of_ne hrk
          by_cases hlt : k.val - 1 < r.val
          · have hlt2 : k.val < r.val := by omega
            simp [hlt, hlt2]
          · have hlt2 : ¬ k.val < r.val := by omega
            simp [hlt, hlt2]
        have hsp := hc (σ.vertex r) (σ.vertex_sum r)
        rw [hrc] at hsp
        exact hsp hvr
    -- Step 3: Split goodPairs into boundary on face D vs interior!
    let bdryPairs := goodPairs.filter (fun p => p.2.val = 0 ∧ p.1.base (p.1.perm 0) = N - 1)
    let intPairs := goodPairs.filter (fun p => ¬ (p.2.val = 0 ∧ p.1.base (p.1.perm 0) = N - 1))
    have hsplit_card : goodPairs.card = bdryPairs.card + intPairs.card := by
      have hdisj : Disjoint bdryPairs intPairs := by
        rw [Finset.disjoint_left]; intro p h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hunion : bdryPairs ∪ intPairs = goodPairs := by
        ext p; simp only [bdryPairs, intPairs, Finset.mem_union, Finset.mem_filter]
        tauto
      rw [← hunion, Finset.card_union_of_disjoint hdisj]
    -- Step 4: Fixed-point-free involution on intPairs → Even intPairs.card!
    have hint_even : Even intPairs.card := by
      -- Define the pivot map on `KuhnSimplex D N × Fin (D + 1)`!
      let pivot : KuhnSimplex D N × Fin (D + 1) → KuhnSimplex D N × Fin (D + 1) := fun ⟨σ, k⟩ =>
        if h0 : k.val = 0 then
          if hlt : σ.base (σ.perm 0) + 1 < N then
            let i₀ := σ.perm 0
            let b' : Fin D → ℕ := Function.update σ.base i₀ (σ.base i₀ + 1)
            let p' : Equiv.Perm (Fin D) := (cycShift m).trans σ.perm
            have hmono' : Monotone b' := by
              intro a b hab
              by_cases ha : a = i₀
              · subst ha
                rcases eq_or_lt_of_le hab with rfl | hlt'
                · exact le_rfl
                · have hne_eq : σ.base i₀ ≠ σ.base ⟨i₀.val + 1, by omega⟩ := by
                    intro hEq
                    have htie := σ.tie i₀.val (by omega) hEq
                    have hi0eq : (⟨i₀.val, by omega⟩ : Fin D) = σ.perm 0 := Fin.ext rfl
                    rw [hi0eq, Equiv.symm_apply_apply] at htie
                    exact Nat.not_lt_zero _ htie
                  have hle1 : σ.base i₀ ≤ σ.base ⟨i₀.val + 1, by omega⟩ :=
                    σ.mono (show i₀ ≤ ⟨i₀.val + 1, by omega⟩ by change i₀.val ≤ i₀.val + 1; omega)
                  have hle2 : σ.base ⟨i₀.val + 1, by omega⟩ ≤ σ.base b :=
                    σ.mono (show (⟨i₀.val + 1, by omega⟩ : Fin D) ≤ b by change i₀.val + 1 ≤ b.val; omega)
                  have hne_b : b ≠ i₀ := ne_of_gt hlt'
                  simp only [b', Function.update_self, Function.update_of_ne hne_b]
                  omega
              · by_cases hb : b = i₀
                · subst hb
                  simp only [b', Function.update_self, Function.update_of_ne ha]
                  exact le_trans (σ.mono hab) (Nat.le_succ _)
                · simp only [b', Function.update_of_ne ha, Function.update_of_ne hb]
                  exact σ.mono hab
            have hltN' : ∀ j, b' j < N := by
              intro j; by_cases hj : j = i₀
              · subst hj; simpa [b'] using hlt
              · simp [b', hj, σ.lt_N j]
            have htie' : ∀ (j : ℕ) (hj : j + 1 < D),
                b' ⟨j, Nat.lt_of_succ_lt hj⟩ = b' ⟨j + 1, hj⟩ →
                p'.symm ⟨j + 1, hj⟩ < p'.symm ⟨j, Nat.lt_of_succ_lt hj⟩ := by
              intro j hj hEq
              have hp'symm : ∀ x : Fin D, p'.symm x = (cycShift m).symm (σ.perm.symm x) := fun _ => rfl
              rw [hp'symm, hp'symm]
              by_cases h1 : (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin D) = i₀
              · have h2 : (⟨j + 1, hj⟩ : Fin D) ≠ i₀ := fun h => by
                  have := congrArg Fin.val (h.trans h1.symm); simp at this
                have hv1 : σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩ = 0 := by
                  rw [h1]; exact Equiv.symm_apply_apply σ.perm 0
                have hv2_ne : σ.perm.symm ⟨j + 1, hj⟩ ≠ 0 := by
                  intro h; exact h2 (by dsimp only [i₀]; rw [← h, Equiv.apply_symm_apply])
                rw [hv1]
                change ((cycShift m).symm (σ.perm.symm ⟨j + 1, hj⟩)).val < ((cycShift m).symm 0).val
                have hpos : 0 < (σ.perm.symm ⟨j + 1, hj⟩).val :=
                  Nat.pos_of_ne_zero (Fin.val_ne_of_ne hv2_ne)
                have hltm := (σ.perm.symm ⟨j + 1, hj⟩).isLt
                have h0lt : ¬ (0 : ℕ) < (0 : Fin D).val := by simp
                simp only [cycShift, Equiv.coe_fn_symm_mk, hpos, h0lt, ↓reduceDIte]
                omega
              · by_cases h2 : (⟨j + 1, hj⟩ : Fin D) = i₀
                · simp only [b', Function.update_of_ne h1, h2, Function.update_self] at hEq
                  have hle1 : σ.base ⟨j, Nat.lt_of_succ_lt hj⟩ ≤ σ.base i₀ :=
                    σ.mono (show (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin D) ≤ i₀ by
                      rw [← h2]; change j ≤ j + 1; omega)
                  omega
                · simp only [b', Function.update_of_ne h1, Function.update_of_ne h2] at hEq
                  have htie0 := σ.tie j hj hEq
                  have hpos1 : 0 < (σ.perm.symm ⟨j + 1, hj⟩).val := by
                    by_contra hz
                    have hz0 : σ.perm.symm ⟨j + 1, hj⟩ = 0 := Fin.ext (by change (σ.perm.symm _).val = 0; omega)
                    exact h2 (by dsimp only [i₀]; rw [← hz0, Equiv.apply_symm_apply])
                  have hpos2 : 0 < (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩).val := lt_trans hpos1 htie0
                  change ((cycShift m).symm (σ.perm.symm ⟨j + 1, hj⟩)).val <
                    ((cycShift m).symm (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩)).val
                  simp only [cycShift, Equiv.coe_fn_symm_mk, hpos1, hpos2, ↓reduceDIte]
                  exact Nat.sub_lt_sub_right (by omega) htie0
            (⟨b', p', hmono', hltN', htie'⟩, Fin.last D)
          else (σ, k)
        else if hD : k.val = D then
          if hpos : 0 < σ.base (σ.perm (Fin.last m)) then
            let i₁ := σ.perm (Fin.last m)
            let b' : Fin D → ℕ := Function.update σ.base i₁ (σ.base i₁ - 1)
            let p' : Equiv.Perm (Fin D) := (cycShift m).symm.trans σ.perm
            have hmono' : Monotone b' := by
              intro a b hab
              by_cases hb : b = i₁
              · subst hb
                rcases eq_or_lt_of_le hab with rfl | hlt'
                · exact le_rfl
                · have hi1_pos : 0 < i₁.val := by omega
                  have hne_eq : σ.base ⟨i₁.val - 1, by omega⟩ ≠ σ.base i₁ := by
                    intro hEq
                    have hEq' : σ.base ⟨i₁.val - 1, by omega⟩ = σ.base ⟨i₁.val - 1 + 1, by omega⟩ := by
                      have : (⟨i₁.val - 1 + 1, by omega⟩ : Fin D) = i₁ := Fin.ext (by dsimp only; omega)
                      rwa [this]
                    have htie := σ.tie (i₁.val - 1) (by omega) hEq'
                    have hi1eq : (⟨i₁.val - 1 + 1, by omega⟩ : Fin D) = σ.perm (Fin.last m) :=
                      Fin.ext (by dsimp only; omega)
                    rw [hi1eq, Equiv.symm_apply_apply] at htie
                    have hltm := (σ.perm.symm ⟨i₁.val - 1, by omega⟩).isLt
                    change m < _ at htie; omega
                  have hle1 : σ.base a ≤ σ.base ⟨i₁.val - 1, by omega⟩ :=
                    σ.mono (show a ≤ ⟨i₁.val - 1, by omega⟩ by change a.val ≤ i₁.val - 1; omega)
                  have hle2 : σ.base ⟨i₁.val - 1, by omega⟩ ≤ σ.base i₁ :=
                    σ.mono (show (⟨i₁.val - 1, by omega⟩ : Fin D) ≤ i₁ by change i₁.val - 1 ≤ i₁.val; omega)
                  have hne_a : a ≠ i₁ := ne_of_lt hlt'
                  simp only [b', Function.update_self, Function.update_of_ne hne_a]
                  omega
              · by_cases ha : a = i₁
                · subst ha
                  simp only [b', Function.update_self, Function.update_of_ne hb]
                  exact le_trans (Nat.sub_le _ _) (σ.mono hab)
                · simp only [b', Function.update_of_ne ha, Function.update_of_ne hb]
                  exact σ.mono hab
            have hltN' : ∀ j, b' j < N := by
              intro j; by_cases hj : j = i₁
              · subst hj; simp only [b', Function.update_self]; have := σ.lt_N i₁; omega
              · simp [b', hj, σ.lt_N j]
            have htie' : ∀ (j : ℕ) (hj : j + 1 < D),
                b' ⟨j, Nat.lt_of_succ_lt hj⟩ = b' ⟨j + 1, hj⟩ →
                p'.symm ⟨j + 1, hj⟩ < p'.symm ⟨j, Nat.lt_of_succ_lt hj⟩ := by
              intro j hj hEq
              have hp'symm : ∀ x : Fin D, p'.symm x = (cycShift m) (σ.perm.symm x) := fun _ => rfl
              rw [hp'symm, hp'symm]
              by_cases h2 : (⟨j + 1, hj⟩ : Fin D) = i₁
              · have h1 : (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin D) ≠ i₁ := fun h => by
                  have := congrArg Fin.val (h.trans h2.symm); simp at this
                have hv2 : σ.perm.symm ⟨j + 1, hj⟩ = Fin.last m := by
                  rw [h2]; exact Equiv.symm_apply_apply σ.perm (Fin.last m)
                have hv1_ne : σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩ ≠ Fin.last m := by
                  intro h; exact h1 (by dsimp only [i₁]; rw [← h, Equiv.apply_symm_apply])
                rw [hv2]
                change ((cycShift m) (Fin.last m)).val < ((cycShift m) (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩)).val
                have hlt1 : (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩).val + 1 < m + 1 := by
                  have := (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩).isLt
                  have hne := Fin.val_ne_of_ne hv1_ne; simp at hne; omega
                have hnotlast : ¬ (Fin.last m).val + 1 < m + 1 := by simp
                simp only [cycShift, Equiv.coe_fn_mk, hlt1, hnotlast, ↓reduceDIte]
                exact Nat.succ_pos _
              · by_cases h1 : (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin D) = i₁
                · simp only [b', h1, Function.update_self, Function.update_of_ne h2] at hEq
                  have hle1 : σ.base i₁ ≤ σ.base ⟨j + 1, hj⟩ :=
                    σ.mono (show i₁ ≤ ⟨j + 1, hj⟩ by rw [← h1]; change j ≤ j + 1; omega)
                  dsimp only [i₁] at hEq hle1
                  omega
                · simp only [b', Function.update_of_ne h1, Function.update_of_ne h2] at hEq
                  have htie0 := σ.tie j hj hEq
                  have hlt2 : (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩).val + 1 < m + 1 := by
                    have hlt' := (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩).isLt
                    have hne : σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩ ≠ Fin.last m := by
                      intro h; exact h1 (by dsimp only [i₁]; rw [← h, Equiv.apply_symm_apply])
                    have hvalne : (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩).val ≠ m := fun h => hne (Fin.ext h)
                    omega
                  have hlt1 : (σ.perm.symm ⟨j + 1, hj⟩).val + 1 < m + 1 := by
                    have : (σ.perm.symm ⟨j + 1, hj⟩).val < (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩).val := htie0
                    omega
                  change ((cycShift m) (σ.perm.symm ⟨j + 1, hj⟩)).val <
                    ((cycShift m) (σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩)).val
                  simp only [cycShift, Equiv.coe_fn_mk, hlt1, hlt2, ↓reduceDIte]
                  exact Nat.succ_lt_succ htie0
            (⟨b', p', hmono', hltN', htie'⟩, 0)
          else (σ, k)
        else
          -- Middle pivot 0 < k < D: swap perm(k-1) and perm(k)!
          have hklt : k.val < D := by have := k.isLt; omega
          let p' : Equiv.Perm (Fin D) := (Equiv.swap (⟨k.val - 1, by omega⟩ : Fin D) ⟨k.val, hklt⟩).trans σ.perm
          if hvalid : ∀ (j : ℕ) (hj : j + 1 < D),
              σ.base ⟨j, Nat.lt_of_succ_lt hj⟩ = σ.base ⟨j + 1, hj⟩ →
              p'.symm ⟨j + 1, hj⟩ < p'.symm ⟨j, Nat.lt_of_succ_lt hj⟩ then
            (⟨σ.base, p', σ.mono, σ.lt_N, hvalid⟩, k)
          else (σ, k)
      -- Helper: for any p ∈ intPairs, pivot p has the SAME omitted-k facet vertices as p,
      -- lies in intPairs, is an involution, and has pivot p ≠ p!
      have hpivot_props : ∀ p ∈ intPairs,
          pivot p ∈ intPairs ∧ pivot (pivot p) = p ∧ pivot p ≠ p := by
        intro ⟨σ, k⟩ hp
        obtain ⟨hpG, hpNotB⟩ := Finset.mem_filter.mp hp
        have hgood := (Finset.mem_filter.mp hpG).2
        have hnb := hno_bdry_lt (σ, k) hpG
        dsimp only at hpNotB hgood hnb
        by_cases h0 : k.val = 0
        · -- Case k = 0: since not in bdryPairs, σ.base (σ.perm 0) + 1 < N!
          have hlt : σ.base (σ.perm 0) + 1 < N := by
            have := σ.lt_N (σ.perm 0)
            by_contra hc; exact hpNotB ⟨h0, by omega⟩
          have hp_eq : (pivot (σ, k)).2 = Fin.last D := by simp only [pivot, h0, hlt, ↓reduceDIte]
          have hσ'_base : (pivot (σ, k)).1.base = Function.update σ.base (σ.perm 0) (σ.base (σ.perm 0) + 1) := by
            simp only [pivot, h0, hlt, ↓reduceDIte]
          have hσ'_perm : (pivot (σ, k)).1.perm = (cycShift m).trans σ.perm := by
            simp only [pivot, h0, hlt, ↓reduceDIte]
          -- Vertex correspondence: (pivot (σ, k)).1.vertex r = σ.vertex (r + 1) for r < D!
          have hv_eq : ∀ (r : Fin (D + 1)) (hr : r.val < D),
              (pivot (σ, k)).1.vertex r = σ.vertex ⟨r.val + 1, by omega⟩ := by
            intro r hr
            funext i; unfold KuhnSimplex.vertex cumToBary
            suffices hcum : ∀ j : Fin D, (pivot (σ, k)).1.cumVertex r j = σ.cumVertex ⟨r.val + 1, by omega⟩ j by
              simp [hcum]
            intro j
            unfold KuhnSimplex.cumVertex
            rw [hσ'_base, hσ'_perm]
            have hsymm : ((cycShift m).trans σ.perm).symm j = (cycShift m).symm (σ.perm.symm j) := rfl
            rw [hsymm]
            by_cases hj : j = σ.perm 0
            · subst hj
              rw [Function.update_self, Equiv.symm_apply_apply]
              have hc0 : ((cycShift m).symm 0).val = m := by simp [cycShift]
              rw [hc0]
              have hnotlt : ¬ m < r.val := by omega
              have hlt1 : (0 : ℕ) < r.val + 1 := Nat.succ_pos _
              simp [hnotlt, hlt1]
            · rw [Function.update_of_ne hj]
              have hpos : 0 < (σ.perm.symm j).val := by
                by_contra hz
                have hz0 : σ.perm.symm j = 0 := Fin.ext (by change (σ.perm.symm j).val = 0; omega)
                exact hj (by rw [← hz0, Equiv.apply_symm_apply])
              have hcs : ((cycShift m).symm (σ.perm.symm j)).val = (σ.perm.symm j).val - 1 := by
                simp only [cycShift, Equiv.coe_fn_symm_mk, hpos, ↓reduceDIte]
              rw [hcs]
              by_cases hc : (σ.perm.symm j).val < r.val + 1
              · have hc' : (σ.perm.symm j).val - 1 < r.val := by omega
                simp [hc, hc']
              · have hc' : ¬ (σ.perm.symm j).val - 1 < r.val := by omega
                simp [hc, hc']
          have hmem_int : pivot (σ, k) ∈ intPairs := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
              ⟨mem_allKuhnSimplices _, Finset.mem_univ _⟩, ?_⟩, ?_⟩
            · intro r
              obtain ⟨j, hjk, hjc⟩ := hgood r
              have hjpos : 0 < j.val := by
                have := Fin.val_ne_of_ne hjk; omega
              refine ⟨⟨j.val - 1, by omega⟩, ?_, ?_⟩
              · rw [hp_eq]; intro hEq; have := congrArg Fin.val hEq; simp at this; omega
              · have hjlt' : j.val - 1 < D := by have := j.isLt; omega
                rw [hv_eq ⟨j.val - 1, by omega⟩ hjlt']
                have heq' : (⟨j.val - 1 + 1, by omega⟩ : Fin (D + 1)) = j := Fin.ext (by dsimp only; omega)
                rw [heq']; exact hjc
            · rw [hp_eq]; rintro ⟨h, _⟩; simp [D] at h
          have hinv : pivot (pivot (σ, k)) = (σ, k) := by
            let σ' := (pivot (σ, k)).1
            have hk' : (pivot (σ, k)).2 = Fin.last D := hp_eq
            have h0' : ¬ (Fin.last D).val = 0 := by simp [D]
            have hD' : (Fin.last D).val = D := rfl
            have hp_last : σ'.perm (Fin.last m) = σ.perm 0 := by
              rw [hσ'_perm]; change σ.perm ((cycShift m) (Fin.last m)) = σ.perm 0
              congr 1; ext; simp [cycShift]
            have hpos' : 0 < σ'.base (σ'.perm (Fin.last m)) := by
              rw [hp_last, hσ'_base, Function.update_self]; omega
            have h1 : (pivot (σ', Fin.last D)).2 = k := by
              have : (pivot (σ', Fin.last D)).2 = 0 := by
                dsimp only [pivot]; rw [dif_neg h0', dif_pos hD', dif_pos hpos']
              rw [this]; exact Fin.ext h0.symm
            have h2 : (pivot (σ', Fin.last D)).1 = σ := by
              apply KuhnSimplex.ext
              · funext j
                have hbase_eq : (pivot (σ', Fin.last D)).1.base =
                    Function.update σ'.base (σ'.perm (Fin.last m)) (σ'.base (σ'.perm (Fin.last m)) - 1) := by
                  dsimp only [pivot]; rw [dif_neg h0', dif_pos hD', dif_pos hpos']
                rw [hbase_eq, hp_last, hσ'_base]
                by_cases hj : j = σ.perm 0
                · subst hj; simp
                · simp [hj]
              · have hperm_eq : (pivot (σ', Fin.last D)).1.perm = (cycShift m).symm.trans σ'.perm := by
                  dsimp only [pivot]; rw [dif_neg h0', dif_pos hD', dif_pos hpos']
                rw [hperm_eq, hσ'_perm]
                ext j; simp
            exact Prod.ext (by rw [← hk'] at h2; exact h2) (by rw [← hk'] at h1; exact h1)
          have hne : pivot (σ, k) ≠ (σ, k) := by
            intro hEq
            have := congrArg (fun q : KuhnSimplex D N × Fin (D + 1) => q.2.val) hEq
            rw [hp_eq] at this; simp [D] at this; omega
          exact ⟨hmem_int, hinv, hne⟩
        · by_cases hD : k.val = D
          · -- Case k = D: by hnb.2.1, 0 < σ.base (σ.perm (Fin.last m))!
            have hpos : 0 < σ.base (σ.perm (Fin.last m)) := hnb.2.1 hD
            have hp_eq : (pivot (σ, k)).2 = 0 := by
              dsimp only [pivot]; rw [dif_neg h0, dif_pos hD, dif_pos hpos]
            have hσ'_base : (pivot (σ, k)).1.base =
                Function.update σ.base (σ.perm (Fin.last m)) (σ.base (σ.perm (Fin.last m)) - 1) := by
              dsimp only [pivot]; rw [dif_neg h0, dif_pos hD, dif_pos hpos]
            have hσ'_perm : (pivot (σ, k)).1.perm = (cycShift m).symm.trans σ.perm := by
              dsimp only [pivot]; rw [dif_neg h0, dif_pos hD, dif_pos hpos]
            have hv_eq : ∀ (r : Fin (D + 1)) (hr : 0 < r.val),
                (pivot (σ, k)).1.vertex r = σ.vertex ⟨r.val - 1, by omega⟩ := by
              intro r hr
              funext i; unfold KuhnSimplex.vertex cumToBary
              suffices hcum : ∀ j : Fin D, (pivot (σ, k)).1.cumVertex r j = σ.cumVertex ⟨r.val - 1, by omega⟩ j by
                simp [hcum]
              intro j; unfold KuhnSimplex.cumVertex
              rw [hσ'_base, hσ'_perm]
              have hsymm : ((cycShift m).symm.trans σ.perm).symm j = (cycShift m) (σ.perm.symm j) := rfl
              rw [hsymm]
              by_cases hj : j = σ.perm (Fin.last m)
              · subst hj
                rw [Function.update_self, Equiv.symm_apply_apply]
                have hc : ((cycShift m) (Fin.last m)).val = 0 := by simp [cycShift]
                rw [hc]
                have hnotlt : ¬ (Fin.last m).val < r.val - 1 := by simp; have := r.isLt; omega
                dsimp only
                rw [if_pos hr, if_neg hnotlt]
                omega
              · rw [Function.update_of_ne hj]
                have hlt : (σ.perm.symm j).val + 1 < m + 1 := by
                  have := (σ.perm.symm j).isLt
                  have hne : σ.perm.symm j ≠ Fin.last m := fun h =>
                    hj (by rw [← h, Equiv.apply_symm_apply])
                  have := Fin.val_ne_of_ne hne; simp at this; omega
                have hcs : ((cycShift m) (σ.perm.symm j)).val = (σ.perm.symm j).val + 1 := by
                  simp only [cycShift, Equiv.coe_fn_mk, hlt, ↓reduceDIte]
                rw [hcs]
                by_cases hc : (σ.perm.symm j).val < r.val - 1
                · have hc' : (σ.perm.symm j).val + 1 < r.val := by omega
                  simp [hc, hc']
                · have hc' : ¬ (σ.perm.symm j).val + 1 < r.val := by omega
                  simp [hc, hc']
            have hp0 : (pivot (σ, k)).1.perm 0 = σ.perm (Fin.last m) := by
              rw [hσ'_perm]
              exact congrArg σ.perm (Fin.ext (by simp [cycShift]))
            have hlt' : (pivot (σ, k)).1.base ((pivot (σ, k)).1.perm 0) + 1 < N := by
              rw [hp0, hσ'_base, Function.update_self]
              have := σ.lt_N (σ.perm (Fin.last m)); omega
            have hmem_int : pivot (σ, k) ∈ intPairs := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                ⟨mem_allKuhnSimplices _, Finset.mem_univ _⟩, ?_⟩, ?_⟩
              · intro r
                obtain ⟨j, hjk, hjc⟩ := hgood r
                have hjlt : j.val < D := by have := j.isLt; have := Fin.val_ne_of_ne hjk; omega
                refine ⟨⟨j.val + 1, by omega⟩, ?_, ?_⟩
                · rw [hp_eq]; intro hEq; have := congrArg Fin.val hEq; simp at this
                · rw [hv_eq ⟨j.val + 1, by omega⟩ (Nat.succ_pos _)]
                  have heq' : (⟨j.val + 1 - 1, by omega⟩ : Fin (D + 1)) = j := Fin.ext (by simp)
                  rw [heq']; exact hjc
              · rintro ⟨_, hmax⟩; omega
            have hinv : pivot (pivot (σ, k)) = (σ, k) := by
              let σ' := (pivot (σ, k)).1
              have hk' : (pivot (σ, k)).2 = 0 := hp_eq
              have h0' : (0 : Fin (D + 1)).val = 0 := rfl
              have hlt'' : σ'.base (σ'.perm 0) + 1 < N := hlt'
              have h1 : (pivot (σ', 0)).2 = k := by
                have : (pivot (σ', 0)).2 = Fin.last D := by simp only [pivot, h0', hlt'', ↓reduceDIte]
                rw [this]; exact Fin.ext hD.symm
              have h2 : (pivot (σ', 0)).1 = σ := by
                apply KuhnSimplex.ext
                · funext j
                  have hbase_eq : (pivot (σ', 0)).1.base =
                      Function.update σ'.base (σ'.perm 0) (σ'.base (σ'.perm 0) + 1) := by
                    simp only [pivot, h0', hlt'', ↓reduceDIte]
                  rw [hbase_eq, hp0, hσ'_base]
                  by_cases hj : j = σ.perm (Fin.last m)
                  · subst hj; simp; omega
                  · simp [hj]
                · have hperm_eq : (pivot (σ', 0)).1.perm = (cycShift m).trans σ'.perm := by
                    simp only [pivot, h0', hlt'', ↓reduceDIte]
                  rw [hperm_eq, hσ'_perm]
                  ext j; simp
              exact Prod.ext (by rw [← hk'] at h2; exact h2) (by rw [← hk'] at h1; exact h1)
            have hne : pivot (σ, k) ≠ (σ, k) := by
              intro hEq
              have := congrArg (fun q : KuhnSimplex D N × Fin (D + 1) => q.2.val) hEq
              rw [hp_eq] at this; simp at this; omega
            exact ⟨hmem_int, hinv, hne⟩
          · -- Case 0 < k < D: middle swap!
            have hkpos : 0 < k.val := by omega
            have hklt : k.val < D := by have := k.isLt; omega
            let sw : Equiv.Perm (Fin D) := Equiv.swap ⟨k.val - 1, by omega⟩ ⟨k.val, hklt⟩
            let p' : Equiv.Perm (Fin D) := sw.trans σ.perm
            have hvalid : ∀ (j : ℕ) (hj : j + 1 < D),
                σ.base ⟨j, Nat.lt_of_succ_lt hj⟩ = σ.base ⟨j + 1, hj⟩ →
                p'.symm ⟨j + 1, hj⟩ < p'.symm ⟨j, Nat.lt_of_succ_lt hj⟩ := by
              intro j hj hEq
              have htie0 := σ.tie j hj hEq
              have hp's : ∀ x : Fin D, p'.symm x = sw (σ.perm.symm x) := fun x => by
                change sw.symm (σ.perm.symm x) = sw (σ.perm.symm x)
                rw [Equiv.symm_swap]
              rw [hp's, hp's]
              let a := σ.perm.symm ⟨j + 1, hj⟩
              let b := σ.perm.symm ⟨j, Nat.lt_of_succ_lt hj⟩
              have hab : a.val < b.val := htie0
              -- Only way sw a ≥ sw b is if a = k - 1 and b = k, which hnb.2.2 forbids!
              by_cases h1 : a = ⟨k.val - 1, by omega⟩ ∧ b = ⟨k.val, hklt⟩
              · exfalso
                have hp1 : σ.perm ⟨k.val - 1, by omega⟩ = ⟨j + 1, hj⟩ := by
                  rw [← h1.1]; exact Equiv.apply_symm_apply _ _
                have hp2 : σ.perm ⟨k.val, hklt⟩ = ⟨j, Nat.lt_of_succ_lt hj⟩ := by
                  rw [← h1.2]; exact Equiv.apply_symm_apply _ _
                exact hnb.2.2 hkpos hklt j hj hp1 hp2 hEq
              · change (sw a).val < (sw b).val
                by_cases ha1 : a = ⟨k.val - 1, by omega⟩
                · have hb2 : b ≠ ⟨k.val, hklt⟩ := fun hb => h1 ⟨ha1, hb⟩
                  have hb1 : b ≠ ⟨k.val - 1, by omega⟩ := fun hb => by rw [ha1, hb] at hab; exact lt_irrefl _ hab
                  have hbv : k.val < b.val := by
                    have hne := Fin.val_ne_of_ne hb2; rw [ha1] at hab; dsimp at hab hne; omega
                  rw [ha1, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hb1 hb2]
                  exact hbv
                · by_cases ha2 : a = ⟨k.val, hklt⟩
                  · have hb1 : b ≠ ⟨k.val - 1, by omega⟩ := fun hb => by rw [ha2, hb] at hab; dsimp at hab; omega
                    have hb2 : b ≠ ⟨k.val, hklt⟩ := fun hb => by rw [ha2, hb] at hab; exact lt_irrefl _ hab
                    rw [ha2, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hb1 hb2]
                    rw [ha2] at hab; dsimp at hab ⊢; omega
                  · rw [Equiv.swap_apply_of_ne_of_ne ha1 ha2]
                    by_cases hb1 : b = ⟨k.val - 1, by omega⟩
                    · rw [hb1, Equiv.swap_apply_left]; rw [hb1] at hab; dsimp at hab ⊢; omega
                    · by_cases hb2 : b = ⟨k.val, hklt⟩
                      · rw [hb2, Equiv.swap_apply_right]
                        have hne1 := Fin.val_ne_of_ne ha1
                        rw [hb2] at hab; dsimp at hab hne1 ⊢; omega
                      · rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2]; exact hab
            have hp_eq : pivot (σ, k) = (⟨σ.base, p', σ.mono, σ.lt_N, hvalid⟩, k) := by
              dsimp only [pivot]; rw [dif_neg h0, dif_neg hD, dif_pos hvalid]
            -- For every r ≠ k, vertex r is IDENTICAL!
            have hv_eq : ∀ r : Fin (D + 1), r ≠ k →
                (pivot (σ, k)).1.vertex r = σ.vertex r := by
              intro r hrk
              funext i; unfold KuhnSimplex.vertex cumToBary
              suffices hcum : ∀ j : Fin D, (pivot (σ, k)).1.cumVertex r j = σ.cumVertex r j by
                simp [hcum]
              intro j; unfold KuhnSimplex.cumVertex
              rw [hp_eq]; dsimp only
              have hp's : p'.symm j = sw (σ.perm.symm j) := by
                change sw.symm (σ.perm.symm j) = sw (σ.perm.symm j); rw [Equiv.symm_swap]
              rw [hp's]
              have hrne : r.val ≠ k.val := Fin.val_ne_of_ne hrk
              have hiff : (sw (σ.perm.symm j)).val < r.val ↔ (σ.perm.symm j).val < r.val := by
                by_cases h1 : σ.perm.symm j = ⟨k.val - 1, by omega⟩
                · rw [h1, Equiv.swap_apply_left]; dsimp; omega
                · by_cases h2 : σ.perm.symm j = ⟨k.val, hklt⟩
                  · rw [h2, Equiv.swap_apply_right]; dsimp; omega
                  · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
              by_cases h : (σ.perm.symm j).val < r.val
              · simp [h, hiff.mpr h]
              · simp [h, mt hiff.mp h]
            have hmem_int : pivot (σ, k) ∈ intPairs := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                ⟨mem_allKuhnSimplices _, Finset.mem_univ _⟩, ?_⟩, ?_⟩
              · intro r
                obtain ⟨j, hjk, hjc⟩ := hgood r
                rw [hp_eq] at *
                refine ⟨j, hjk, ?_⟩
                have := hv_eq j hjk; rw [hp_eq] at this; rw [this]; exact hjc
              · rw [hp_eq]; rintro ⟨h, _⟩; exact h0 h
            have hinv : pivot (pivot (σ, k)) = (σ, k) := by
              rw [hp_eq]
              have hvalid2 : ∀ (j : ℕ) (hj : j + 1 < D),
                  σ.base ⟨j, Nat.lt_of_succ_lt hj⟩ = σ.base ⟨j + 1, hj⟩ →
                  (sw.trans p').symm ⟨j + 1, hj⟩ < (sw.trans p').symm ⟨j, Nat.lt_of_succ_lt hj⟩ := by
                have hsw2 : sw.trans p' = σ.perm := by ext x; simp [p', sw]
                rw [hsw2]; exact σ.tie
              have h2 : pivot (⟨σ.base, p', σ.mono, σ.lt_N, hvalid⟩, k) =
                  (⟨σ.base, sw.trans p', σ.mono, σ.lt_N, hvalid2⟩, k) := by
                dsimp only [pivot]; rw [dif_neg h0, dif_neg hD, dif_pos hvalid2]
              rw [h2]
              refine Prod.ext (KuhnSimplex.ext rfl ?_) rfl
              ext x; simp [p', sw]
            have hne : pivot (σ, k) ≠ (σ, k) := by
              intro hEq
              rw [hp_eq] at hEq
              have hpEq : p' = σ.perm := congrArg (fun q : KuhnSimplex D N × Fin (D + 1) => q.1.perm) hEq
              have hval := congrArg (fun e : Equiv.Perm (Fin D) => e ⟨k.val, hklt⟩) hpEq
              simp [p', sw] at hval
              omega
            exact ⟨hmem_int, hinv, hne⟩
      exact even_card_of_involution pivot
        (fun p hp => (hpivot_props p hp).1)
        (fun p hp => (hpivot_props p hp).2.1)
        (fun p hp => (hpivot_props p hp).2.2)
    -- Step 5: Biject bdryPairs with rainbow m-simplices of Δ_m(N) under the face-D restriction of c!
    let embedBary : (Fin D → ℕ) → (Fin (D + 1) → ℕ) := fun v i =>
      if h : i.val < D then v ⟨i.val, h⟩ else 0
    have hembed_sum : ∀ v : Fin D → ℕ, ∑ i : Fin (D + 1), embedBary v i = ∑ j : Fin D, v j := by
      intro v
      rw [Fin.sum_univ_castSucc]
      have hlast : embedBary v (Fin.last D) = 0 := by simp [embedBary]
      rw [hlast, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [embedBary, j.isLt]
    let c' : (Fin D → ℕ) → Fin D := fun v =>
      let col := c (embedBary v)
      if h : col.val < D then ⟨col.val, h⟩ else ⟨0, Nat.succ_pos m⟩
    have hc'_sp : IsSpernerColoring m N c' := by
      intro v hv
      have hsum : ∑ i : Fin (D + 1), embedBary v i = N := by rw [hembed_sum]; exact hv
      have hsp := hc (embedBary v) hsum
      have hlt : (c (embedBary v)).val < D := by
        by_contra hge
        have hlast : c (embedBary v) = Fin.last D := Fin.ext (by change (c (embedBary v)).val = D; have := (c (embedBary v)).isLt; omega)
        rw [hlast] at hsp
        simp [embedBary] at hsp
      have hc'eq : (c' v).castSucc = c (embedBary v) := by
        ext; simp [c', hlt]
      have hveq : embedBary v (c (embedBary v)) = v (c' v) := by
        rw [← hc'eq]; simp [embedBary, (c' v).isLt]
      rwa [← hveq]
    have hIH := ih c' hc'_sp
    -- Construct the explicit bijection lift : KuhnSimplex m N → KuhnSimplex D N × Fin (D + 1)!
    let liftPerm : Equiv.Perm (Fin m) → Equiv.Perm (Fin D) := fun π =>
      { toFun := fun i => if h : 0 < i.val then (π ⟨i.val - 1, by omega⟩).castSucc else Fin.last m
        invFun := fun j => if h : j.val < m then ⟨(π.symm ⟨j.val, h⟩).val + 1, by omega⟩ else 0
        left_inv := fun i => by
          ext; dsimp only
          by_cases h : 0 < i.val
          · have hlt : (π ⟨i.val - 1, by omega⟩).val < m := (π _).isLt
            simp [h, hlt]; omega
          · have hi : i.val = 0 := by omega
            simp [hi]
        right_inv := fun j => by
          ext; dsimp only
          by_cases h : j.val < m
          · simp [h]
          · have hj : j.val = m := by have := j.isLt; omega
            simp [hj] }
    let lift : KuhnSimplex m N → KuhnSimplex D N × Fin (D + 1) := fun τ =>
      let b : Fin D → ℕ := fun j => if h : j.val < m then τ.base ⟨j.val, h⟩ else N - 1
      have hmono : Monotone b := by
        intro j₁ j₂ hle
        by_cases h2 : j₂.val < m
        · have h1 : j₁.val < m := lt_of_le_of_lt hle h2
          simp only [b, h1, h2, ↓reduceDIte]
          exact τ.mono (show (⟨j₁.val, h1⟩ : Fin m) ≤ ⟨j₂.val, h2⟩ from hle)
        · simp only [b, h2, ↓reduceDIte]
          by_cases h1 : j₁.val < m
          · simp only [h1, ↓reduceDIte]; have := τ.lt_N ⟨j₁.val, h1⟩; omega
          · simp [h1]
      have hltN : ∀ j, b j < N := by
        intro j; by_cases h : j.val < m
        · simp [b, h, τ.lt_N]
        · simp [b, h]; omega
      have htie : ∀ (j : ℕ) (hj : j + 1 < D),
          b ⟨j, Nat.lt_of_succ_lt hj⟩ = b ⟨j + 1, hj⟩ →
          (liftPerm τ.perm).symm ⟨j + 1, hj⟩ < (liftPerm τ.perm).symm ⟨j, Nat.lt_of_succ_lt hj⟩ := by
        intro j hj hEq
        by_cases h2 : j + 1 < m
        · have h1 : j < m := by omega
          simp only [b, h1, h2, ↓reduceDIte] at hEq
          have htie0 := τ.tie j h2 hEq
          change ((liftPerm τ.perm).symm ⟨j + 1, hj⟩).val < ((liftPerm τ.perm).symm ⟨j, Nat.lt_of_succ_lt hj⟩).val
          simp only [liftPerm, Equiv.coe_fn_symm_mk, h1, h2, ↓reduceDIte]
          exact Nat.succ_lt_succ htie0
        · have h1 : j < m := by omega
          change ((liftPerm τ.perm).symm ⟨j + 1, hj⟩).val < ((liftPerm τ.perm).symm ⟨j, Nat.lt_of_succ_lt hj⟩).val
          simp [liftPerm, h1, h2]
      (⟨b, liftPerm τ.perm, hmono, hltN, htie⟩, 0)
    -- Vertex correspondence: (lift τ).1.vertex r.succ = embedBary (τ.vertex r) for all r : Fin D!
    have hlift_vertex : ∀ (τ : KuhnSimplex m N) (r : Fin D),
        (lift τ).1.vertex r.succ = embedBary (τ.vertex r) := by
      intro τ r
      have hcum : ∀ j : Fin m, (lift τ).1.cumVertex r.succ j.castSucc = τ.cumVertex r j := by
        intro j
        unfold KuhnSimplex.cumVertex
        have hb : (lift τ).1.base j.castSucc = τ.base j := by simp [lift, j.isLt]
        have hp : ((lift τ).1.perm.symm j.castSucc).val = (τ.perm.symm j).val + 1 := by
          simp [lift, liftPerm, j.isLt]
        rw [hb, hp]
        change τ.base j + (if (τ.perm.symm j).val + 1 < r.val + 1 then 1 else 0) =
          τ.base j + (if (τ.perm.symm j).val < r.val then 1 else 0)
        simp
      have hcum_last : (lift τ).1.cumVertex r.succ (Fin.last m) = N := by
        unfold KuhnSimplex.cumVertex
        have hb : (lift τ).1.base (Fin.last m) = N - 1 := by simp [lift]
        have hp : ((lift τ).1.perm.symm (Fin.last m)).val = 0 := by simp [lift, liftPerm]
        rw [hb, hp]
        simp; omega
      funext i
      unfold KuhnSimplex.vertex embedBary cumToBary
      by_cases hi : i.val < D
      · simp only [hi, ↓reduceDIte]
        by_cases h0 : i.val = 0
        · simp only [h0, ↓reduceDIte]
          by_cases hm : 0 < m
          · have hDpos : 0 < D := Nat.succ_pos m
            simp only [hDpos, hm, ↓reduceDIte]
            have := hcum ⟨0, hm⟩; exact this
          · have hm0 : m = 0 := by omega
            subst hm0
            have hDpos : 0 < D := Nat.succ_pos 0
            simp only [hDpos, ↓reduceDIte]
            exact hcum_last
        · by_cases him : i.val < m
          · simp only [h0, ↓reduceDIte, him]
            exact congrArg₂ (· - ·) (hcum ⟨i.val, him⟩) (hcum ⟨i.val - 1, by omega⟩)
          · have him_eq : i.val = m := by omega
            simp only [h0, ↓reduceDIte, him]
            have h1 : (lift τ).1.cumVertex r.succ ⟨i.val, hi⟩ = N := by
              have hlast_eq : (⟨i.val, hi⟩ : Fin D) = Fin.last m := Fin.ext him_eq
              rw [hlast_eq]; exact hcum_last
            have h2 : (lift τ).1.cumVertex r.succ ⟨i.val - 1, by omega⟩ = τ.cumVertex r ⟨m - 1, by omega⟩ := by
              have hprev_eq : (⟨i.val - 1, by omega⟩ : Fin D) = (⟨m - 1, by omega⟩ : Fin m).castSucc :=
                Fin.ext (by dsimp; omega)
              rw [hprev_eq]; exact hcum ⟨m - 1, by omega⟩
            rw [h1, h2]
      · simp only [hi, ↓reduceDIte]
        have h0 : ¬ i.val = 0 := by omega
        simp only [h0, ↓reduceDIte]
        have hlast_eq : (⟨D - 1, by omega⟩ : Fin D) = Fin.last m := Fin.ext (by simp [D])
        rw [hlast_eq, hcum_last]; omega
    -- Show bdryPairs = ((allKuhnSimplices m N).filter (KuhnSimplex.IsRainbow c')).image lift!
    have hbdry_card : bdryPairs.card = ((allKuhnSimplices m N).filter (KuhnSimplex.IsRainbow c')).card := by
      have hinj : Set.InjOn lift ((allKuhnSimplices m N).filter (KuhnSimplex.IsRainbow c')) := by
        intro τ₁ _ τ₂ _ hEq
        have hσEq := congrArg Prod.fst hEq
        apply KuhnSimplex.ext
        · funext j
          have hb := congrFun (congrArg KuhnSimplex.base hσEq) j.castSucc
          simpa [lift, j.isLt] using hb
        · ext j
          have hp := congrArg (fun e : Equiv.Perm (Fin D) => (e ⟨j.val + 1, by omega⟩).val)
            (congrArg KuhnSimplex.perm hσEq)
          simp only [lift, liftPerm, Equiv.coe_fn_mk, Nat.succ_pos, ↓reduceDIte,
            Fin.val_castSucc, Nat.add_sub_cancel, Fin.eta] at hp
          exact hp
      have himg : ((allKuhnSimplices m N).filter (KuhnSimplex.IsRainbow c')).image lift = bdryPairs := by
        ext ⟨σ, k⟩
        simp only [Finset.mem_image, Finset.mem_filter, bdryPairs, goodPairs,
          Finset.mem_product, Finset.mem_univ, and_true]
        constructor
        · rintro ⟨τ, ⟨_, hrb⟩, hEq⟩
          have hσEq : (lift τ).1 = σ := congrArg Prod.fst hEq
          have hkEq : (lift τ).2 = k := congrArg Prod.snd hEq
          subst hσEq; subst hkEq
          refine ⟨⟨mem_allKuhnSimplices _, ?_⟩, rfl, ?_⟩
          · intro r
            obtain ⟨j, hj⟩ := hrb.2 r
            refine ⟨j.succ, Fin.succ_ne_zero j, ?_⟩
            rw [hlift_vertex τ j]
            have hsum : ∑ i, embedBary (τ.vertex j) i = N := by
              rw [hembed_sum]; exact τ.vertex_sum j
            have hsp := hc (embedBary (τ.vertex j)) hsum
            have hlt : (c (embedBary (τ.vertex j))).val < D := by
              by_contra hge
              have hlast : c (embedBary (τ.vertex j)) = Fin.last D :=
                Fin.ext (by change (c (embedBary (τ.vertex j))).val = D; have := (c (embedBary (τ.vertex j))).isLt; omega)
              rw [hlast] at hsp; simp [embedBary] at hsp
            have hc'eq : (c' (τ.vertex j)).castSucc = c (embedBary (τ.vertex j)) := by
              ext; simp [c', hlt]
            dsimp only at hj
            rw [← hc'eq, hj]
          · simp [lift, liftPerm]
        · rintro ⟨⟨hσ, hgood⟩, hk0, hmax⟩
          have hperm0 : σ.perm 0 = Fin.last m :=
            (hno_bdry_lt (σ, k) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hσ, Finset.mem_univ _⟩, hgood⟩)).1
              hk0 hmax
          -- Reconstruct τ : KuhnSimplex m N from σ!
          let b₀ : Fin m → ℕ := fun j => σ.base j.castSucc
          let p₀ : Equiv.Perm (Fin m) :=
            { toFun := fun j =>
                let y := σ.perm ⟨j.val + 1, by omega⟩
                have hy : y.val < m := by
                  have hne : y ≠ Fin.last m := by
                    rw [← hperm0]; intro h; have := congrArg Fin.val (σ.perm.injective h); simp at this
                  have := y.isLt; have := Fin.val_ne_of_ne hne; simp at this; omega
                ⟨y.val, hy⟩
              invFun := fun i =>
                let x := σ.perm.symm i.castSucc
                have hx : 0 < x.val := by
                  have hne : x ≠ 0 := by
                    intro h; have := congrArg Fin.val (show i.castSucc = σ.perm 0 by rw [← h, Equiv.apply_symm_apply])
                    rw [hperm0] at this; simp at this; omega
                  exact Nat.pos_of_ne_zero (Fin.val_ne_of_ne hne)
                ⟨x.val - 1, by have := x.isLt; omega⟩
              left_inv := fun j => by
                ext; dsimp only
                have hcast : ∀ h : (σ.perm ⟨j.val + 1, by omega⟩).val < m,
                    (⟨(σ.perm ⟨j.val + 1, by omega⟩).val, h⟩ : Fin m).castSucc =
                    σ.perm ⟨j.val + 1, by omega⟩ := fun _ => Fin.ext rfl
                rw [hcast, Equiv.symm_apply_apply]; simp
              right_inv := fun i => by
                ext; dsimp only
                have hpos : 0 < (σ.perm.symm i.castSucc).val := by
                  by_contra hz
                  have h0 : σ.perm.symm i.castSucc = 0 := Fin.ext (by change (σ.perm.symm _).val = 0; omega)
                  have := congrArg Fin.val (show i.castSucc = σ.perm 0 by rw [← h0, Equiv.apply_symm_apply])
                  rw [hperm0] at this; simp at this; omega
                have hmk : (⟨(σ.perm.symm i.castSucc).val - 1 + 1, by omega⟩ : Fin D) = σ.perm.symm i.castSucc :=
                  Fin.ext (by dsimp; omega)
                rw [hmk, Equiv.apply_symm_apply]; rfl }
          let τ : KuhnSimplex m N :=
            ⟨b₀, p₀, fun a b hab => σ.mono hab, fun j => σ.lt_N j.castSucc, fun j hj hEq => by
              have htie0 := σ.tie j (by omega) hEq
              have hpos1 : 0 < (σ.perm.symm ⟨j + 1, by omega⟩).val := by
                by_contra hz
                have h0 : σ.perm.symm ⟨j + 1, by omega⟩ = 0 := Fin.ext (by change (σ.perm.symm _).val = 0; omega)
                have := congrArg Fin.val (show (⟨j + 1, by omega⟩ : Fin D) = σ.perm 0 by
                  rw [← h0, Equiv.apply_symm_apply])
                rw [hperm0] at this; simp at this; omega
              change (p₀.symm ⟨j + 1, hj⟩).val < (p₀.symm ⟨j, Nat.lt_of_succ_lt hj⟩).val
              dsimp only [p₀, Equiv.coe_fn_symm_mk]
              exact Nat.sub_lt_sub_right (show 1 ≤ (σ.perm.symm ⟨j + 1, by omega⟩).val from hpos1) htie0⟩
          have hlift_eq : lift τ = (σ, k) := by
            refine Prod.ext (KuhnSimplex.ext ?_ ?_) (Fin.ext hk0.symm)
            · funext j; dsimp only [lift]
              by_cases hj : j.val < m
              · simp [hj, τ, b₀]
              · have hlast : j = Fin.last m := Fin.ext (by change j.val = m; have := j.isLt; omega)
                subst hlast; simp [hperm0] at hmax ⊢; exact hmax.symm
            · ext j; dsimp only [lift, liftPerm]
              by_cases hj : 0 < j.val
              · simp only [hj, ↓reduceDIte, τ, p₀, Equiv.coe_fn_mk, Fin.val_castSucc]
                have hmk : (⟨j.val - 1 + 1, by omega⟩ : Fin D) = j := Fin.ext (by dsimp; omega)
                rw [hmk]
              · have h0 : j = 0 := Fin.ext (by change j.val = 0; omega)
                subst h0; simp [hperm0]
          have hrb : τ.IsRainbow c' := by
            have hsurj : Function.Surjective (fun j : Fin D => c' (τ.vertex j)) := by
              intro r
              obtain ⟨j, hjk, hjc⟩ := hgood r
              have hjpos : 0 < j.val := by have := Fin.val_ne_of_ne hjk; omega
              let j' : Fin D := ⟨j.val - 1, by have := j.isLt; omega⟩
              refine ⟨j', ?_⟩
              have hj_eq : j'.succ = j := Fin.ext (by dsimp [j']; omega)
              have hv := hlift_vertex τ j'
              rw [hlift_eq, hj_eq] at hv
              ext; simp only [c', ← hv, hjc, Fin.val_castSucc, r.isLt, ↓reduceDIte]
            exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
          exact ⟨τ, ⟨mem_allKuhnSimplices τ, hrb⟩, hlift_eq⟩
      rw [← himg, Finset.card_image_of_injOn hinj]
    -- Step 6: Combine parities!
    rcases hint_even with ⟨e, he⟩
    rcases hIH with ⟨q, hq⟩
    have hodd : ((allKuhnSimplices D N).filter (KuhnSimplex.IsRainbow c)).card % 2 = 1 := by
      rw [← hmod_rainbow, hsplit_card, hbdry_card, he, hq]; omega
    exact Nat.odd_iff.mpr hodd

/-- **Existence form of Sperner's Lemma:** every proper Sperner coloring of `Δ_d(N)` (`N ≥ 1`)
has at least one rainbow Kuhn simplex. -/
theorem sperner_lemma_exists (d : ℕ) {N : ℕ} (hN : 1 ≤ N)
    (c : (Fin (d + 1) → ℕ) → Fin (d + 1))
    (hc : IsSpernerColoring d N c) :
    ∃ σ : KuhnSimplex d N, σ.IsRainbow c := by
  have hodd := sperner_lemma d hN c hc
  have hpos : 0 < ((allKuhnSimplices d N).filter (KuhnSimplex.IsRainbow c)).card := by
    rcases hodd with ⟨k, hk⟩; omega
  obtain ⟨σ, hσ⟩ := Finset.card_pos.mp hpos
  exact ⟨σ, (Finset.mem_filter.mp hσ).2⟩

end SpernerLemma

/-! ## Section 2: Brouwer Fixed Point Theorem on the Standard `d`-Simplex `Δ_d` -/

section BrouwerFixedPoint

/-- The closed standard `d`-simplex `{x : Fin (d + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}`
is compact in `Fin (d + 1) → ℝ`. -/
lemma isCompact_stdSimplex (d : ℕ) :
    IsCompact {x : Fin (d + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1} := by
  let box : Set (Fin (d + 1) → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)
  have hbox_cpt : IsCompact box := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : {x : Fin (d + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1} ⊆ box := by
    intro x ⟨hnn, hsum⟩ i _
    refine ⟨hnn i, ?_⟩
    have hle : x i ≤ ∑ j : Fin (d + 1), x j :=
      Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    linarith
  have hclosed : IsClosed {x : Fin (d + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1} := by
    have h1 : IsClosed {x : Fin (d + 1) → ℝ | ∀ i, 0 ≤ x i} := by
      have : {x : Fin (d + 1) → ℝ | ∀ i, 0 ≤ x i} = ⋂ i : Fin (d + 1), {x | (0 : ℝ) ≤ x i} := by
        ext x; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {x : Fin (d + 1) → ℝ | ∑ i : Fin (d + 1), x i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  exact hbox_cpt.of_isClosed_subset hclosed hsub

/-- **Brouwer Fixed Point Theorem on the Standard `d`-Simplex `Δ_d`:**
Every continuous self-map `f` of `{x : Fin (d + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}`
has a fixed point `f x = x`. Deduced cleanly from `sperner_lemma_exists` + compactness. -/
theorem brouwer_fixed_point_simplex (d : ℕ)
    (f : (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ))
    (hf_cont : ContinuousOn f {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1})
    (hf_maps : Set.MapsTo f {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}
      {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}) :
    ∃ x : Fin (d + 1) → ℝ, (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧ f x = x := by
  let Δ : Set (Fin (d + 1) → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}
  -- For each N ≥ 1, build a proper Sperner coloring c_N on Δ_d(N) with f(v/N)_i ≤ (v/N)_i!
  have hchoice : ∀ (N : ℕ), 1 ≤ N → ∀ (v : Fin (d + 1) → ℕ), (∑ i, v i = N) →
      ∃ i : Fin (d + 1), v i ≠ 0 ∧ f (fun j => (v j : ℝ) / (N : ℝ)) i ≤ (v i : ℝ) / (N : ℝ) := by
    intro N hN v hv
    let x : Fin (d + 1) → ℝ := fun j => (v j : ℝ) / (N : ℝ)
    have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    have hx_mem : x ∈ Δ := by
      refine ⟨fun j => by positivity, ?_⟩
      simp only [x, ← Finset.sum_div]
      have : (∑ j : Fin (d + 1), (v j : ℝ)) = (N : ℝ) := by exact_mod_cast hv
      rw [this, div_self (ne_of_gt hN_pos)]
    have hfx_mem : f x ∈ Δ := hf_maps hx_mem
    by_contra hall
    push Not at hall
    have hle_all : ∀ j : Fin (d + 1), x j ≤ f x j := by
      intro j
      by_cases hj : v j = 0
      · have hxj : x j = 0 := by simp [x, hj]
        rw [hxj]; exact hfx_mem.1 j
      · exact le_of_lt (hall j hj)
    have hex_pos : ∃ j₀ : Fin (d + 1), v j₀ ≠ 0 := by
      by_contra h0; push Not at h0
      have : ∑ j : Fin (d + 1), v j = 0 := Finset.sum_eq_zero fun j _ => h0 j
      omega
    obtain ⟨j₀, hj₀⟩ := hex_pos
    have hlt_sum : ∑ j : Fin (d + 1), x j < ∑ j : Fin (d + 1), f x j :=
      Finset.sum_lt_sum (fun j _ => hle_all j) ⟨j₀, Finset.mem_univ _, hall j₀ hj₀⟩
    linarith [hx_mem.2, hfx_mem.2]
  -- Extract for each n : ℕ (with N = n + 1) a rainbow simplex σ_n and its color-i vertices!
  have hrainbow : ∀ n : ℕ, ∃ u : Fin (d + 1) → (Fin (d + 1) → ℝ),
      (∀ i, u i ∈ Δ) ∧
      (∀ i, f (u i) i ≤ u i i) ∧
      (∀ i j k, |u i k - u j k| ≤ 1 / ((n + 1 : ℕ) : ℝ)) := by
    intro n
    let N := n + 1
    have hN : 1 ≤ N := Nat.succ_pos n
    have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    let c : (Fin (d + 1) → ℕ) → Fin (d + 1) := fun v =>
      if h : ∑ i, v i = N then (hchoice N hN v h).choose else 0
    have hc : IsSpernerColoring d N c := by
      intro v hv
      simp only [c, dif_pos hv]
      exact (hchoice N hN v hv).choose_spec.1
    obtain ⟨σ, hrb⟩ := sperner_lemma_exists d hN c hc
    let invC : Fin (d + 1) → Fin (d + 1) := fun i => (hrb.2 i).choose
    have hinvC : ∀ i, c (σ.vertex (invC i)) = i := fun i => (hrb.2 i).choose_spec
    let u : Fin (d + 1) → (Fin (d + 1) → ℝ) := fun i k => (σ.vertex (invC i) k : ℝ) / (N : ℝ)
    refine ⟨u, ?_, ?_, ?_⟩
    · intro i
      refine ⟨fun k => by positivity, ?_⟩
      simp only [u, ← Finset.sum_div]
      have : (∑ k : Fin (d + 1), (σ.vertex (invC i) k : ℝ)) = (N : ℝ) := by
        exact_mod_cast σ.vertex_sum (invC i)
      rw [this, div_self (ne_of_gt hN_pos)]
    · intro i
      have hsum := σ.vertex_sum (invC i)
      have hspec := (hchoice N hN (σ.vertex (invC i)) hsum).choose_spec.2
      have hceq : (hchoice N hN (σ.vertex (invC i)) hsum).choose = i := by
        have := hinvC i; simpa [c, dif_pos hsum] using this
      rw [hceq] at hspec
      exact hspec
    · intro i j k
      have hdiff := σ.vertex_diff_le_one (invC i) (invC j) k
      have hrew : u i k - u j k =
          ((σ.vertex (invC i) k : ℝ) - (σ.vertex (invC j) k : ℝ)) / (N : ℝ) := by
        simp only [u, sub_div]
      rw [hrew, abs_div, abs_of_pos hN_pos]
      exact div_le_div_of_nonneg_right hdiff (le_of_lt hN_pos)
  let uSeq : ℕ → Fin (d + 1) → (Fin (d + 1) → ℝ) := fun n => (hrainbow n).choose
  have hu_mem : ∀ n i, uSeq n i ∈ Δ := fun n => (hrainbow n).choose_spec.1
  have hu_le : ∀ n i, f (uSeq n i) i ≤ uSeq n i i := fun n => (hrainbow n).choose_spec.2.1
  have hu_diam : ∀ n i j k, |uSeq n i k - uSeq n j k| ≤ 1 / ((n + 1 : ℕ) : ℝ) :=
    fun n => (hrainbow n).choose_spec.2.2
  -- Extract a convergent subsequence of n ↦ uSeq n 0 in the compact simplex Δ!
  obtain ⟨x, hxΔ, φ, hφ_mono, hx_tendsto⟩ :=
    (isCompact_stdSimplex d).tendsto_subseq (fun n => hu_mem n 0)
  -- For every i : Fin (d + 1), uSeq (φ n) i ALSO converges to x!
  have hu_tendsto : ∀ i : Fin (d + 1),
      Filter.Tendsto (fun n => uSeq (φ n) i) Filter.atTop (nhds x) := by
    intro i
    rw [tendsto_pi_nhds]
    intro k
    have hx_k : Filter.Tendsto (fun n => uSeq (φ n) 0 k) Filter.atTop (nhds (x k)) :=
      (tendsto_pi_nhds.mp hx_tendsto) k
    have hdiff_zero : Filter.Tendsto (fun n => uSeq (φ n) i k - uSeq (φ n) 0 k) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((φ n + 1 : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
        have hnat : Filter.Tendsto (fun n : ℕ => ((φ n + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
          rw [Filter.tendsto_atTop_atTop]
          intro b
          obtain ⟨M, hM⟩ := exists_nat_gt b
          refine ⟨M, fun n hn => ?_⟩
          have hφn : n ≤ φ n := hφ_mono.id_le n
          have : (M : ℝ) ≤ ((φ n + 1 : ℕ) : ℝ) := by exact_mod_cast (show M ≤ φ n + 1 by omega)
          linarith
        exact tendsto_const_nhds.div_atTop hnat
      have hneg : Filter.Tendsto (fun n : ℕ => -((1 : ℝ) / ((φ n + 1 : ℕ) : ℝ))) Filter.atTop (nhds 0) := by
        simpa using h1.neg
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg h1
        (fun n => (abs_le.mp (hu_diam (φ n) i 0 k)).1)
        (fun n => (abs_le.mp (hu_diam (φ n) i 0 k)).2)
    have hadd := hdiff_zero.add hx_k
    simpa [sub_add_cancel] using hadd
  -- Pass f (uSeq (φ n) i) i ≤ uSeq (φ n) i i to the limit for every i!
  have hfx_le : ∀ i : Fin (d + 1), f x i ≤ x i := by
    intro i
    have hf_cont_x : Filter.Tendsto f (nhdsWithin x Δ) (nhds (f x)) := hf_cont x hxΔ
    have hu_within : Filter.Tendsto (fun n => uSeq (φ n) i) Filter.atTop (nhdsWithin x Δ) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hu_tendsto i)
        (Filter.Eventually.of_forall fun n => hu_mem (φ n) i)
    have hft : Filter.Tendsto (fun n => f (uSeq (φ n) i) i) Filter.atTop (nhds (f x i)) :=
      (tendsto_pi_nhds.mp (hf_cont_x.comp hu_within)) i
    have hxt : Filter.Tendsto (fun n => uSeq (φ n) i i) Filter.atTop (nhds (x i)) :=
      (tendsto_pi_nhds.mp (hu_tendsto i)) i
    exact le_of_tendsto_of_tendsto hft hxt (Filter.Eventually.of_forall fun n => hu_le (φ n) i)
  -- Since ∑ f x i = 1 = ∑ x i and ∀ i, f x i ≤ x i, we have f x = x!
  have hfx_mem : f x ∈ Δ := hf_maps hxΔ
  have hfx_eq : f x = x := by
    funext i
    by_contra hne
    have hlt : f x i < x i := lt_of_le_of_ne (hfx_le i) hne
    have hsum_lt : ∑ j : Fin (d + 1), f x j < ∑ j : Fin (d + 1), x j :=
      Finset.sum_lt_sum (fun j _ => hfx_le j) ⟨i, Finset.mem_univ _, hlt⟩
    linarith [hxΔ.2, hfx_mem.2]
  exact ⟨x, hxΔ.1, hxΔ.2, hfx_eq⟩

end BrouwerFixedPoint

/-! ## Section 3: Ky Fan's Lemma, Combinatorial Tucker's Lemma, & Discrete Borsuk–Ulam -/

section KyFanTucker

/-- A maximal signed chain in `{-1, 0, 1}^n \ {0}`, represented by a permutation `π` of `Fin n`
(the order in which coordinates become nonzero) and a sign assignment `s : Fin n → Bool`. -/
private abbrev SignedChain (n : ℕ) := Equiv.Perm (Fin n) × (Fin n → Bool)

/-- The `r`-th vertex (`r : Fin n`) of the maximal signed chain `(π, s)`:
coordinate `j` is `+1` (if `s j = true`) or `-1` (if `s j = false`) when `π.symm j ≤ r`, and `0` otherwise. -/
private def chainVertex {n : ℕ} (σ : SignedChain n) (r : Fin n) : Fin n → ℤ :=
  fun j => if (σ.1.symm j).val ≤ r.val then (if σ.2 j then 1 else -1) else 0

private lemma chainVertex_mem_sign {n : ℕ} (σ : SignedChain n) (r : Fin n) :
    (∀ j : Fin n, chainVertex σ r j = -1 ∨ chainVertex σ r j = 0 ∨ chainVertex σ r j = 1) ∧
    chainVertex σ r ≠ 0 := by
  constructor
  · intro j; unfold chainVertex
    split_ifs <;> simp
  · intro h0
    have hn_pos : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; exact Fin.elim0 r)
    let z0 : Fin n := ⟨0, hn_pos⟩
    have hval := congrFun h0 (σ.1 z0)
    have h0le : z0.val ≤ r.val := Nat.zero_le r.val
    simp only [chainVertex, Equiv.symm_apply_apply, h0le, ↓reduceIte, Pi.zero_apply] at hval
    cases h : σ.2 (σ.1 z0) <;> simp [h] at hval

private lemma chainVertex_face_le {n : ℕ} (σ : SignedChain n) {r₁ r₂ : Fin n} (hle : r₁ ≤ r₂) :
    ∀ j : Fin n, chainVertex σ r₁ j = 0 ∨ chainVertex σ r₁ j = chainVertex σ r₂ j := by
  intro j; unfold chainVertex
  by_cases h1 : (σ.1.symm j).val ≤ r₁.val
  · have h2 : (σ.1.symm j).val ≤ r₂.val := le_trans h1 hle
    right; simp [h1, h2]
  · left; simp [h1]

private lemma chainVertex_neg {n : ℕ} (σ : SignedChain n) (r : Fin n) :
    chainVertex (σ.1, fun j => !σ.2 j) r = -chainVertex σ r := by
  funext j; unfold chainVertex
  simp only [Pi.neg_apply]
  by_cases h1 : (σ.1.symm j).val ≤ r.val
  · rcases Bool.eq_false_or_eq_true (σ.2 j) with h2 | h2 <;> simp [h1, h2]
  · simp [h1]

/-- An `m`-tuple of integers `h : Fin m → ℤ` is **`sgn`-alternating** if its absolute values
are pairwise distinct and, when sorted in strictly increasing order of `|h|`, the signs
alternate starting with `+` (when `sgn = true`) or `-` (when `sgn = false`). -/
private def IsAlt (sgn : Bool) {m : ℕ} (h : Fin m → ℤ) : Prop :=
  ∃ e : Fin m ≃ Fin m,
    StrictMono (fun r : Fin m => (h (e r)).natAbs) ∧
    ∀ r : Fin m, if (r.val % 2 = 0 ↔ sgn = true) then 0 < h (e r) else h (e r) < 0

private lemma isAlt_neg {m : ℕ} (h : Fin m → ℤ) :
    IsAlt true (fun i => -h i) ↔ IsAlt false h := by
  constructor <;> rintro ⟨e, hmono, hsgn⟩ <;> refine ⟨e, ?_, ?_⟩
  · simpa [Int.natAbs_neg] using hmono
  · intro r
    have hr := hsgn r
    by_cases hp : r.val % 2 = 0 <;> simp [hp] at hr ⊢ <;> omega
  · simpa [Int.natAbs_neg] using hmono
  · intro r
    have hr := hsgn r
    by_cases hp : r.val % 2 = 0 <;> simp [hp] at hr ⊢ <;> omega

private lemma isAlt_comp_equiv {sgn : Bool} {m : ℕ} (h : Fin m → ℤ) (e₀ : Fin m ≃ Fin m) :
    IsAlt sgn (h ∘ e₀) ↔ IsAlt sgn h := by
  constructor
  · rintro ⟨e, hm, hs⟩; exact ⟨e.trans e₀, hm, hs⟩
  · rintro ⟨e, hm, hs⟩; exact ⟨e.trans e₀.symm, by simpa using hm, by simpa using hs⟩

private lemma isAlt_inj {sgn : Bool} {m : ℕ} {h : Fin m → ℤ} (halt : IsAlt sgn h) :
    Function.Injective (fun i => (h i).natAbs) := by
  rcases halt with ⟨e, hm, _⟩
  intro a b hEq
  have h1 : (h (e (e.symm a))).natAbs = (h (e (e.symm b))).natAbs := by simpa using hEq
  have h2 : e.symm a = e.symm b := hm.injective h1
  exact e.symm.injective h2

private lemma isAlt_not_both {m : ℕ} (hm : 0 < m) (h : Fin m → ℤ) :
    ¬ (IsAlt true h ∧ IsAlt false h) := by
  rintro ⟨⟨e₁, hm₁, hs₁⟩, ⟨e₂, hm₂, hs₂⟩⟩
  have hmin : ∀ r : Fin m, (h (e₁ ⟨0, hm⟩)).natAbs ≤ (h (e₁ r)).natAbs := fun r =>
    hm₁.monotone (show (⟨0, hm⟩ : Fin m) ≤ r from Nat.zero_le r.val)
  have hmin₂ : ∀ r : Fin m, (h (e₂ ⟨0, hm⟩)).natAbs ≤ (h (e₂ r)).natAbs := fun r =>
    hm₂.monotone (show (⟨0, hm⟩ : Fin m) ≤ r from Nat.zero_le r.val)
  have hle1 : (h (e₁ ⟨0, hm⟩)).natAbs ≤ (h (e₂ ⟨0, hm⟩)).natAbs := by
    have := hmin (e₁.symm (e₂ ⟨0, hm⟩)); simpa using this
  have hle2 : (h (e₂ ⟨0, hm⟩)).natAbs ≤ (h (e₁ ⟨0, hm⟩)).natAbs := by
    have := hmin₂ (e₂.symm (e₁ ⟨0, hm⟩)); simpa using this
  have heq_abs : (h (e₁ ⟨0, hm⟩)).natAbs = (h (e₂ ⟨0, hm⟩)).natAbs := le_antisymm hle1 hle2
  have heq : e₁ ⟨0, hm⟩ = e₂ ⟨0, hm⟩ := isAlt_inj ⟨e₁, hm₁, hs₁⟩ heq_abs
  have hpos := hs₁ ⟨0, hm⟩
  have hneg := hs₂ ⟨0, hm⟩
  simp at hpos hneg
  rw [heq] at hpos; omega

/-- StrictMono sorting uniqueness on `Fin m`: if two permutations sort a function into
strictly increasing order, they are identical! -/
private lemma strictMono_equiv_unique {m : ℕ} {f : Fin m → ℕ} {e₁ e₂ : Fin m ≃ Fin m}
    (h1 : StrictMono (f ∘ e₁)) (h2 : StrictMono (f ∘ e₂)) : e₁ = e₂ := by
  have hpoint : ∀ (k : ℕ) (hk : k < m), e₁ ⟨k, hk⟩ = e₂ ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      let r : Fin m := ⟨k, hk⟩
      let s : Fin m := e₂.symm (e₁ r)
      let t : Fin m := e₁.symm (e₂ r)
      have hrs : r ≤ s := by
        by_contra hlt; push Not at hlt
        have heq := ih s.val hlt s.isLt
        have hs1 : e₁ s = e₁ r := by
          have : e₂ s = e₁ r := Equiv.apply_symm_apply e₂ (e₁ r)
          rw [← this]; exact heq
        exact ne_of_lt hlt (e₁.injective hs1)
      have hrt : r ≤ t := by
        by_contra hlt; push Not at hlt
        have heq := ih t.val hlt t.isLt
        have ht2 : e₂ t = e₂ r := by
          have : e₁ t = e₂ r := Equiv.apply_symm_apply e₁ (e₂ r)
          rw [← this]; exact heq.symm
        exact ne_of_lt hlt (e₂.injective ht2)
      have hle1 : f (e₂ r) ≤ f (e₁ r) := by
        have := h2.monotone hrs
        simpa [s, Function.comp_apply] using this
      have hle2 : f (e₁ r) ≤ f (e₂ r) := by
        have := h1.monotone hrt
        simpa [t, Function.comp_apply] using this
      have hfeq : f (e₂ s) = f (e₂ r) := by
        have : e₂ s = e₁ r := Equiv.apply_symm_apply e₂ (e₁ r)
        rw [this]; exact le_antisymm hle2 hle1
      have hsr : s = r := h2.injective hfeq
      have : e₂ s = e₁ r := Equiv.apply_symm_apply e₂ (e₁ r)
      rw [← this, hsr]
  ext r
  exact congrArg Fin.val (hpoint r.val r.isLt)

/-- **Local Ky Fan Parity Lemma:**
For any `g : Fin (n + 1) → ℤ` with `∀ i, g i ≠ 0` and no opposite-sign pair `g i + g j = 0`,
the number of `k : Fin (n + 1)` such that `g ∘ k.succAbove` is `+`-alternating has the same
parity as `(if IsAlt true g then 1 else 0) + (if IsAlt false g then 1 else 0)`. -/
private lemma local_kyfan_parity {n : ℕ} (g : Fin (n + 1) → ℤ)
    (h0 : ∀ i, g i ≠ 0) (hno : ∀ i j, g i + g j ≠ 0) :
    ((Finset.univ : Finset (Fin (n + 1))).filter (fun k => IsAlt true (g ∘ k.succAbove))).card % 2 =
    ((if IsAlt true g then 1 else 0) + (if IsAlt false g then 1 else 0)) % 2 := by
  let good := (Finset.univ : Finset (Fin (n + 1))).filter (fun k => IsAlt true (g ∘ k.succAbove))
  by_cases hinj : Function.Injective (fun i => (g i).natAbs)
  · -- Case 1: All `|g i|` are distinct! Sort `Fin (n + 1)` by strictly increasing `|g|`!
    let S := (Finset.univ : Finset (Fin (n + 1))).image (fun i => (g i).natAbs)
    have hScard : S.card = n + 1 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    let φ : Fin (n + 1) ↪o ℕ := S.orderEmbOfFin hScard
    have hmem_ex : ∀ r : Fin (n + 1), ∃ i : Fin (n + 1), (g i).natAbs = φ r := fun r => by
      rcases Finset.mem_image.mp (S.orderEmbOfFin_mem hScard r) with ⟨i, _, hi⟩
      exact ⟨i, hi⟩
    let eFun : Fin (n + 1) → Fin (n + 1) := fun r => (hmem_ex r).choose
    have heFun_abs : ∀ r, (g (eFun r)).natAbs = φ r := fun r => (hmem_ex r).choose_spec
    have heFun_inj : Function.Injective eFun := fun r₁ r₂ h =>
      φ.injective (by rw [← heFun_abs r₁, ← heFun_abs r₂, h])
    let e : Fin (n + 1) ≃ Fin (n + 1) :=
      Equiv.ofBijective eFun ⟨heFun_inj, Finite.injective_iff_surjective.mp heFun_inj⟩
    have he_mono : StrictMono (fun r => (g (e r)).natAbs) := by
      intro a b hab; change (g (eFun a)).natAbs < (g (eFun b)).natAbs
      rw [heFun_abs, heFun_abs]; exact φ.strictMono hab
    -- Sign match indicator: `b r = true` iff `g (e r)` matches the `(+,-,+,-,...)` pattern at index `r`!
    let b : Fin (n + 1) → Bool := fun r =>
      decide (if r.val % 2 = 0 then 0 < g (e r) else g (e r) < 0)
    have hb_true : ∀ r, b r = true ↔ (if r.val % 2 = 0 then 0 < g (e r) else g (e r) < 0) := by
      intro r; simp [b]
    have hb_false : ∀ r, b r = false ↔ (if r.val % 2 = 0 then g (e r) < 0 else 0 < g (e r)) := by
      intro r
      have hne := h0 (e r)
      simp only [b, decide_eq_false_iff_not]
      by_cases hp : r.val % 2 = 0 <;> simp only [hp, ↓reduceIte] <;> omega
    -- Equivalence: `IsAlt true (g ∘ (e r).succAbove) ↔ (∀ j < r, b j = true) ∧ (∀ j > r, b j = false)`!
    have hiff : ∀ r : Fin (n + 1),
        IsAlt true (g ∘ (e r).succAbove) ↔
        (∀ j : Fin (n + 1), j < r → b j = true) ∧ (∀ j : Fin (n + 1), r < j → b j = false) := by
      intro r
      -- Build the unique order-preserving sorting bijection `e' : Fin n ≃ Fin n` such that
      -- `(e r).succAbove (e' j) = e (r.succAbove j)` for all `j : Fin n`!
      have hex_j : ∀ j : Fin n, ∃ i : Fin n, (e r).succAbove i = e (r.succAbove j) := by
        intro j
        have hne : e (r.succAbove j) ≠ e r := fun h => r.succAbove_ne j (e.injective h)
        exact Fin.exists_succAbove_eq hne
      let e'Fun : Fin n → Fin n := fun j => (hex_j j).choose
      have he'Fun_eq : ∀ j, (e r).succAbove (e'Fun j) = e (r.succAbove j) := fun j => (hex_j j).choose_spec
      have he'Fun_inj : Function.Injective e'Fun := fun j₁ j₂ h =>
        r.succAbove_right_injective (e.injective (by rw [← he'Fun_eq j₁, ← he'Fun_eq j₂, h]))
      let e' : Fin n ≃ Fin n :=
        Equiv.ofBijective e'Fun ⟨he'Fun_inj, Finite.injective_iff_surjective.mp he'Fun_inj⟩
      have he'_eq : ∀ j : Fin n, (e r).succAbove (e' j) = e (r.succAbove j) := he'Fun_eq
      have he'_mono : StrictMono (fun j : Fin n => ((g ∘ (e r).succAbove) (e' j)).natAbs) := by
        intro a b hab
        simp only [Function.comp_apply, he'_eq]
        exact he_mono (r.strictMono_succAbove hab)
      constructor
      · rintro ⟨e₁, hm₁, hs₁⟩
        have heq_e : e₁ = e' := strictMono_equiv_unique (f := fun i => (g ((e r).succAbove i)).natAbs) hm₁ he'_mono
        subst heq_e
        constructor
        · intro j hj
          let j' : Fin n := ⟨j.val, by have := r.isLt; omega⟩
          have hj_eq : r.succAbove j' = j := by
            rw [Fin.succAbove_of_castSucc_lt r j' (show j'.castSucc < r from hj)]
            exact Fin.ext rfl
          have hs := hs₁ j'
          simp only [Function.comp_apply, he'_eq, hj_eq, iff_true] at hs
          exact (hb_true j).mpr (by simpa [j'] using hs)
        · intro j hj
          let j' : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩
          have hge : r ≤ j'.castSucc := by
            change r.val ≤ j.val - 1; have : r.val < j.val := hj; omega
          have hj_eq : r.succAbove j' = j := by
            rw [Fin.succAbove_of_le_castSucc r j' hge]
            exact Fin.ext (by dsimp [j']; have : r.val < j.val := hj; omega)
          have hs := hs₁ j'
          simp only [Function.comp_apply, he'_eq, hj_eq, iff_true] at hs
          apply (hb_false j).mpr
          have hpar : j'.val % 2 = 0 ↔ ¬ j.val % 2 = 0 := by
            dsimp [j']; have : r.val < j.val := hj; omega
          by_cases hp : j.val % 2 = 0
          · have hp' : ¬ j'.val % 2 = 0 := fun h => hpar.mp h hp
            simp only [hp', ↓reduceIte] at hs; simp [hp, hs]
          · have hp' : j'.val % 2 = 0 := hpar.mpr hp
            simp only [hp', ↓reduceIte] at hs; simp [hp, hs]
      · rintro ⟨hL, hR⟩
        refine ⟨e', he'_mono, fun j => ?_⟩
        simp only [Function.comp_apply, he'_eq, iff_true]
        by_cases hlt : j.castSucc < r
        · rw [Fin.succAbove_of_castSucc_lt r j hlt]
          have := (hb_true j.castSucc).mp (hL j.castSucc hlt)
          simpa using this
        · have hge : r ≤ j.castSucc := le_of_not_gt hlt
          rw [Fin.succAbove_of_le_castSucc r j hge]
          have hgt : r < j.succ := lt_of_le_of_lt hge Fin.castSucc_lt_succ
          have := (hb_false j.succ).mp (hR j.succ hgt)
          have hpar : j.succ.val % 2 = 0 ↔ ¬ j.val % 2 = 0 := by simp; omega
          by_cases hp : j.val % 2 = 0
          · have hp' : ¬ j.succ.val % 2 = 0 := fun h => hpar.mp h hp
            simp only [hp', ↓reduceIte] at this; simp [hp, this]
          · have hp' : j.succ.val % 2 = 0 := hpar.mpr hp
            simp only [hp', ↓reduceIte] at this; simp [hp, this]
    -- Also characterize `IsAlt true g` and `IsAlt false g` via `b`!
    have halt_true : IsAlt true g ↔ ∀ j : Fin (n + 1), b j = true := by
      constructor
      · rintro ⟨e₁, hm₁, hs₁⟩ j
        have heq_e : e₁ = e := strictMono_equiv_unique (f := fun i => (g i).natAbs) hm₁ he_mono
        subst heq_e
        exact (hb_true j).mpr (by simpa using hs₁ j)
      · intro hb
        exact ⟨e, he_mono, fun r => by simpa using (hb_true r).mp (hb r)⟩
    have halt_false : IsAlt false g ↔ ∀ j : Fin (n + 1), b j = false := by
      constructor
      · rintro ⟨e₁, hm₁, hs₁⟩ j
        have heq_e : e₁ = e := strictMono_equiv_unique (f := fun i => (g i).natAbs) hm₁ he_mono
        subst heq_e
        have hs := hs₁ j
        apply (hb_false j).mpr
        by_cases hp : j.val % 2 = 0
        · simp only [hp, Bool.false_eq_true, iff_false, not_true_eq_false, ↓reduceIte] at hs; simp [hp, hs]
        · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hs; simp [hp, hs]
      · intro hb
        refine ⟨e, he_mono, fun r => ?_⟩
        have hs := (hb_false r).mp (hb r)
        by_cases hp : r.val % 2 = 0
        · simp only [hp, ↓reduceIte] at hs; simp [hp, hs]
        · simp only [hp, ↓reduceIte] at hs; simp [hp, hs]
    -- Re-index `good` by `e`!
    let T := (Finset.univ : Finset (Fin (n + 1))).filter
      (fun r => (∀ j : Fin (n + 1), j < r → b j = true) ∧ (∀ j : Fin (n + 1), r < j → b j = false))
    have hgood_card : good.card = T.card := by
      have himg : T.image e = good := by
        ext k
        simp only [Finset.mem_image, T, good, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨r, hr, rfl⟩; exact (hiff r).mpr hr
        · intro hk; exact ⟨e.symm k, (hiff (e.symm k)).mp (by simpa using hk), by simp⟩
      rw [← himg, Finset.card_image_of_injective _ e.injective]
    rw [hgood_card]
    -- Count `T.card` by inspecting `F := {j | b j = false}`!
    let F := (Finset.univ : Finset (Fin (n + 1))).filter (fun j => b j = false)
    by_cases hFempty : F = ∅
    · have hallT : ∀ j, b j = true := by
        intro j
        by_contra hne
        have hbf : b j = false := by cases hb : b j <;> simp [hb] at hne ⊢
        have : j ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbf⟩
        rw [hFempty] at this; exact Finset.notMem_empty _ this
      have hTeq : T = {Fin.last n} := by
        ext r
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨_, hR⟩
          by_contra hne
          have hlt : r < Fin.last n := lt_of_le_of_ne (Fin.le_last r) hne
          have h1 := hR (Fin.last n) hlt
          have h2 := hallT (Fin.last n)
          rw [h1] at h2; exact Bool.noConfusion h2
        · rintro rfl
          exact ⟨fun j _ => hallT j, fun j hj => absurd hj (not_lt_of_ge (Fin.le_last j))⟩
      have ht : IsAlt true g := halt_true.mpr hallT
      have hf : ¬ IsAlt false g := fun hf' => isAlt_not_both (Nat.succ_pos n) g ⟨ht, hf'⟩
      rw [hTeq, Finset.card_singleton]; simp [ht, hf]
    · have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFempty
      let r₀ := F.min' hFne
      have hr₀F : b r₀ = false := (Finset.mem_filter.mp (F.min'_mem hFne)).2
      have hbefore : ∀ j : Fin (n + 1), j < r₀ → b j = true := by
        intro j hj
        by_contra hne
        have hbf : b j = false := by cases hb : b j <;> simp [hb] at hne ⊢
        have hle := F.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbf⟩)
        exact not_lt_of_ge hle hj
      have hnt : ¬ IsAlt true g := fun ht => by
        have := halt_true.mp ht r₀; rw [hr₀F] at this; exact Bool.noConfusion this
      by_cases hafter : ∀ j : Fin (n + 1), r₀ < j → b j = false
      · by_cases hr₀0 : r₀.val = 0
        · have hallF : ∀ j : Fin (n + 1), b j = false := by
            intro j
            rcases eq_or_lt_of_le (show r₀ ≤ j by change r₀.val ≤ j.val; omega) with rfl | hgt
            · exact hr₀F
            · exact hafter j hgt
          have hTeq : T = {r₀} := by
            ext r
            simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · rintro ⟨hL, _⟩
              by_contra hne
              have hgt : r₀ < r := lt_of_le_of_ne (show r₀ ≤ r by change r₀.val ≤ r.val; omega) (Ne.symm hne)
              have h1 := hL r₀ hgt; rw [hr₀F] at h1; exact Bool.noConfusion h1
            · rintro rfl
              exact ⟨fun j hj => by change j.val < r₀.val at hj; omega, hafter⟩
          have hf : IsAlt false g := halt_false.mpr hallF
          rw [hTeq, Finset.card_singleton]; simp [hnt, hf]
        · -- `0 < r₀.val` and `b j = true` for `j < r₀`, `b j = false` for `j ≥ r₀`: `T = {r₀ - 1, r₀}`!
          let r₁ : Fin (n + 1) := ⟨r₀.val - 1, by have := r₀.isLt; omega⟩
          have hr1_lt : r₁ < r₀ := by change r₀.val - 1 < r₀.val; omega
          have hnf : ¬ IsAlt false g := fun hf => by
            have h1 := halt_false.mp hf r₁
            have h2 := hbefore r₁ hr1_lt
            rw [h1] at h2; exact Bool.noConfusion h2
          have hTeq : T = {r₁, r₀} := by
            ext r
            simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨hL, hR⟩
              by_contra hnot; push Not at hnot; obtain ⟨hne1, hne0⟩ := hnot
              have hval1 : r.val ≠ r₀.val - 1 := fun h => hne1 (Fin.ext h)
              have hval0 : r.val ≠ r₀.val := fun h => hne0 (Fin.ext h)
              rcases lt_or_gt_of_ne hval0 with hlt | hgt
              · have hlt1 : r < r₁ := by change r.val < r₀.val - 1; omega
                have h1 := hR r₁ hlt1; have h2 := hbefore r₁ hr1_lt
                rw [h1] at h2; exact Bool.noConfusion h2
              · have h1 := hL r₀ hgt; rw [hr₀F] at h1; exact Bool.noConfusion h1
            · rintro (rfl | rfl)
              · refine ⟨fun j hj => hbefore j (lt_trans hj hr1_lt), fun j hj => ?_⟩
                rcases eq_or_lt_of_le (show r₀ ≤ j by
                  have : r₀.val - 1 < j.val := hj; change r₀.val ≤ j.val; omega) with rfl | hgt
                · exact hr₀F
                · exact hafter j hgt
              · exact ⟨hbefore, hafter⟩
          rw [hTeq, Finset.card_pair (ne_of_lt hr1_lt)]
          simp [hnt, hnf]
      · -- `∃ j₁ > r₀, b j₁ = true`: `T = ∅` and neither `IsAlt true g` nor `IsAlt false g`!
        push Not at hafter
        obtain ⟨j₁, hj₁_gt, hj₁_ne⟩ := hafter
        have hj₁T : b j₁ = true := by cases hb : b j₁ <;> simp [hb] at hj₁_ne ⊢
        have hnf : ¬ IsAlt false g := fun hf => by
          have := halt_false.mp hf j₁; rw [hj₁T] at this; exact Bool.noConfusion this
        have hTeq : T = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro r hr
          obtain ⟨hL, hR⟩ := (Finset.mem_filter.mp hr).2
          rcases le_or_gt r r₀ with hle | hgt
          · have h1 := hR j₁ (lt_of_le_of_lt hle hj₁_gt)
            rw [hj₁T] at h1; exact Bool.noConfusion h1
          · have h1 := hL r₀ hgt
            rw [hr₀F] at h1; exact Bool.noConfusion h1
        rw [hTeq, Finset.card_empty]
        simp [hnt, hnf]
  · -- Case 2: `¬ Function.Injective (fun i => (g i).natAbs)`:
    -- Neither `IsAlt true g` nor `IsAlt false g` holds, and `good.card ∈ {0, 2}` (EVEN)!
    have hnt : ¬ IsAlt true g := fun h => hinj (isAlt_inj h)
    have hnf : ¬ IsAlt false g := fun h => hinj (isAlt_inj h)
    simp only [hnt, hnf, ↓reduceIte, add_zero, Nat.zero_mod]
    have hdup : ∃ a b : Fin (n + 1), a ≠ b ∧ g a = g b := by
      unfold Function.Injective at hinj; push Not at hinj
      obtain ⟨a, b, hab_abs, hab_ne⟩ := hinj
      refine ⟨a, b, hab_ne, ?_⟩
      rcases Int.natAbs_eq_natAbs_iff.mp hab_abs with h | h
      · exact h
      · exfalso; exact hno a b (by omega)
    obtain ⟨a, b, hab, hgab⟩ := hdup
    have hsub : good ⊆ {a, b} := by
      intro k hk
      by_contra hnot
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      obtain ⟨hka, hkb⟩ := hnot
      obtain ⟨ia, hia⟩ := Fin.exists_succAbove_eq (Ne.symm hka)
      obtain ⟨ib, hib⟩ := Fin.exists_succAbove_eq (Ne.symm hkb)
      have hia_ne : ia ≠ ib := fun h => hab (by rw [← hia, ← hib, h])
      have hinj_k := isAlt_inj (Finset.mem_filter.mp hk).2
      exact hia_ne (hinj_k (by simp only [Function.comp_apply, hia, hib, hgab]))
    -- Show `a ∈ good ↔ b ∈ good` by swapping `a` and `b`!
    have hab_iff : a ∈ good ↔ b ∈ good := by
      have hmap : ∀ (u v : Fin (n + 1)), u ≠ v → g u = g v →
          IsAlt true (g ∘ u.succAbove) → IsAlt true (g ∘ v.succAbove) := by
        intro u v huv hguv halt_u
        -- Build `e_uv : Fin n ≃ Fin n` such that `v.succAbove (e_uv i) = Equiv.swap u v (u.succAbove i)`!
        have hex : ∀ i : Fin n, ∃ j : Fin n, v.succAbove j = Equiv.swap u v (u.succAbove i) := by
          intro i
          apply Fin.exists_succAbove_eq
          intro hEq
          have h1 := congrArg (Equiv.swap u v) hEq
          simp only [Equiv.swap_apply_right, Equiv.swap_apply_self] at h1
          exact u.succAbove_ne i h1
        let f_uv : Fin n → Fin n := fun i => (hex i).choose
        have hf_eq : ∀ i, v.succAbove (f_uv i) = Equiv.swap u v (u.succAbove i) := fun i => (hex i).choose_spec
        have hf_inj : Function.Injective f_uv := fun i₁ i₂ h =>
          u.succAbove_right_injective ((Equiv.swap u v).injective (by rw [← hf_eq i₁, ← hf_eq i₂, h]))
        let e_uv : Fin n ≃ Fin n :=
          Equiv.ofBijective f_uv ⟨hf_inj, Finite.injective_iff_surjective.mp hf_inj⟩
        have hcomp : (g ∘ v.succAbove) ∘ e_uv = g ∘ u.succAbove := by
          funext i
          simp only [Function.comp_apply]
          change g (v.succAbove (f_uv i)) = g (u.succAbove i)
          rw [hf_eq i]
          by_cases h1 : u.succAbove i = v
          · rw [h1, Equiv.swap_apply_right, hguv]
          · rw [Equiv.swap_apply_of_ne_of_ne (u.succAbove_ne i) h1]
        exact (isAlt_comp_equiv (g ∘ v.succAbove) e_uv).mp (hcomp ▸ halt_u)
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hmap a b hab hgab, hmap b a hab.symm hgab.symm⟩
    by_cases ha : a ∈ good
    · have hEq : good = {a, b} := by
        apply Finset.Subset.antisymm hsub
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ha
        · exact hab_iff.mp ha
      change good.card % 2 = 0
      rw [hEq, Finset.card_pair hab]
    · have hEq : good = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        have := hsub hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · exact ha hx
        · exact ha (hab_iff.mpr hx)
      change good.card % 2 = 0
      rw [hEq, Finset.card_empty]

/-- **Ky Fan's Combinatorial Lemma (1952) on the Barycentric Cube `{-1, 0, 1}^n \ {0}`:**
For any `n ≥ 1` and any antipodal nonzero labeling `λ : (Fin n → ℤ) → ℤ` on `{-1, 0, 1}^n \ {0}`
that admits NO complementary face-pair `x ≼ y` with `λ x + λ y = 0`, the number of maximal
signed chains `(π, s)` whose vertex labels are `+`-alternating is **odd** (hence `≥ 1`). -/
private theorem ky_fan_odd_alternating (n : ℕ) (hn : 1 ≤ n)
    (lam : (Fin n → ℤ) → ℤ)
    (hanti : ∀ x : Fin n → ℤ, (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 → lam (-x) = -lam x)
    (hnz : ∀ x : Fin n → ℤ, (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 → lam x ≠ 0)
    (hno_comp : ∀ x y : Fin n → ℤ,
      (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 →
      (∀ j, y j = -1 ∨ y j = 0 ∨ y j = 1) → y ≠ 0 →
      (∀ j, x j = 0 ∨ x j = y j) → lam x + lam y ≠ 0) :
    Odd ((Finset.univ : Finset (SignedChain n)).filter
      (fun σ => IsAlt true (fun r => lam (chainVertex σ r)))).card := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction m with
  | zero =>
    -- Base case n = 1: two chains `(1, fun _ => true)` and `(1, fun _ => false)` with opposite labels!
    have hfin1_eq : ∀ a b : Fin (0 + 1), a = b := fun a b => Fin.ext (by have := a.isLt; have := b.isLt; omega)
    let σP : SignedChain 1 := (Equiv.refl _, fun _ => true)
    let σM : SignedChain 1 := (Equiv.refl _, fun _ => false)
    have hne : σP ≠ σM := fun h => by
      have := congrFun (congrArg Prod.snd h) 0; simp [σP, σM] at this
    have huniv : (Finset.univ : Finset (SignedChain 1)) = {σP, σM} := by
      ext ⟨π, s⟩
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      have hπ : π = Equiv.refl _ := Equiv.ext fun i => hfin1_eq _ _
      cases hs0 : s 0
      · right; exact Prod.ext hπ (funext fun i => by dsimp only [σM]; rw [hfin1_eq i 0, hs0])
      · left; exact Prod.ext hπ (funext fun i => by dsimp only [σP]; rw [hfin1_eq i 0, hs0])
    have hvM : chainVertex σM 0 = -chainVertex σP 0 := by
      have := chainVertex_neg σP 0
      have hEq : (σP.1, fun j => !σP.2 j) = σM := Prod.ext rfl (funext fun _ => rfl)
      rwa [hEq] at this
    have hPsign := chainVertex_mem_sign σP 0
    have hlamM : lam (chainVertex σM 0) = -lam (chainVertex σP 0) := by
      rw [hvM]; exact hanti _ hPsign.1 hPsign.2
    have hlamNz : lam (chainVertex σP 0) ≠ 0 := hnz _ hPsign.1 hPsign.2
    have halt_iff : ∀ σ : SignedChain 1,
        IsAlt true (fun r => lam (chainVertex σ r)) ↔ 0 < lam (chainVertex σ 0) := by
      intro σ; constructor
      · rintro ⟨e, _, hs⟩
        have h0 := hs 0
        have he0 : e 0 = 0 := hfin1_eq _ _
        simpa [he0] using h0
      · intro hpos
        refine ⟨Equiv.refl _, fun a b hab => absurd (hfin1_eq a b) (ne_of_lt hab), fun r => ?_⟩
        rw [hfin1_eq r 0]; simpa using hpos
    rw [huniv]
    by_cases hpos : 0 < lam (chainVertex σP 0)
    · have h1 : IsAlt true (fun r => lam (chainVertex σP r)) := (halt_iff σP).mpr hpos
      have h2 : ¬ IsAlt true (fun r => lam (chainVertex σM r)) := by
        rw [halt_iff, hlamM]; omega
      have hfilt : ({σP, σM} : Finset (SignedChain 1)).filter
          (fun σ => IsAlt true (fun r => lam (chainVertex σ r))) = {σP} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, hx⟩
          · rfl
          · exact absurd hx h2
        · rintro rfl; exact ⟨Or.inl rfl, h1⟩
      rw [hfilt, Finset.card_singleton]; exact odd_one
    · have h1 : ¬ IsAlt true (fun r => lam (chainVertex σP r)) := by rw [halt_iff]; exact hpos
      have h2 : IsAlt true (fun r => lam (chainVertex σM r)) := by rw [halt_iff, hlamM]; omega
      have hfilt : ({σP, σM} : Finset (SignedChain 1)).filter
          (fun σ => IsAlt true (fun r => lam (chainVertex σ r))) = {σM} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, hx⟩
          · exact absurd hx h1
          · rfl
        · rintro rfl; exact ⟨Or.inr rfl, h2⟩
      rw [hfilt, Finset.card_singleton]; exact odd_one
  | succ k ih =>
    -- Induction step: D = k + 2 ≥ 2!
    let D := k + 2
    let lastD : Fin D := Fin.last (k + 1)
    let Hpos : Finset (SignedChain D) := Finset.univ.filter (fun σ => σ.2 lastD = true)
    let Hneg : Finset (SignedChain D) := Finset.univ.filter (fun σ => σ.2 lastD = false)
    let goodPairs : Finset (SignedChain D × Fin D) :=
      (Hpos ×ˢ (Finset.univ : Finset (Fin D))).filter fun p =>
        IsAlt true (fun j : Fin (k + 1) => lam (chainVertex p.1 (p.2.succAbove j)))
    -- Step 1: By local_kyfan_parity + antipodality between Hpos and Hneg,
    -- goodPairs.card % 2 = (#{σ : SignedChain D | IsAlt true (lam ∘ chainVertex σ)}) % 2!
    have hmod_all : goodPairs.card % 2 =
        ((Finset.univ : Finset (SignedChain D)).filter
          (fun σ => IsAlt true (fun r => lam (chainVertex σ r)))).card % 2 := by
      have h1 : goodPairs.card = ∑ σ ∈ Hpos,
          ((Finset.univ : Finset (Fin D)).filter (fun r =>
            IsAlt true ((fun t => lam (chainVertex σ t)) ∘ r.succAbove))).card := by
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun σ _ => by rw [Finset.card_filter]; rfl
      have h2 : goodPairs.card % 2 =
          (∑ σ ∈ Hpos, ((if IsAlt true (fun r => lam (chainVertex σ r)) then 1 else 0) +
            (if IsAlt false (fun r => lam (chainVertex σ r)) then 1 else 0))) % 2 := by
        rw [h1]
        refine sum_mod_two_eq fun σ _ => ?_
        apply local_kyfan_parity (fun r => lam (chainVertex σ r))
        · intro r; exact hnz _ (chainVertex_mem_sign σ r).1 (chainVertex_mem_sign σ r).2
        · intro r₁ r₂
          rcases le_total r₁ r₂ with hle | hle
          · exact hno_comp _ _ (chainVertex_mem_sign σ r₁).1 (chainVertex_mem_sign σ r₁).2
              (chainVertex_mem_sign σ r₂).1 (chainVertex_mem_sign σ r₂).2 (chainVertex_face_le σ hle)
          · rw [add_comm]
            exact hno_comp _ _ (chainVertex_mem_sign σ r₂).1 (chainVertex_mem_sign σ r₂).2
              (chainVertex_mem_sign σ r₁).1 (chainVertex_mem_sign σ r₁).2 (chainVertex_face_le σ hle)
      -- Biject `{σ ∈ Hpos | IsAlt false ...}` with `{σ ∈ Hneg | IsAlt true ...}` via `σ ↦ (σ.1, !σ.2)`!
      let negChain : SignedChain D → SignedChain D := fun σ => (σ.1, fun j => !σ.2 j)
      have hneg_inv : ∀ σ, negChain (negChain σ) = σ := fun ⟨π, s⟩ =>
        Prod.ext rfl (funext fun j => Bool.not_not (s j))
      have hneg_alt : ∀ σ, IsAlt false (fun r => lam (chainVertex σ r)) ↔
          IsAlt true (fun r => lam (chainVertex (negChain σ) r)) := by
        intro σ
        have hfun : (fun r => lam (chainVertex (negChain σ) r)) =
            (fun r => -lam (chainVertex σ r)) := by
          funext r
          rw [chainVertex_neg]
          exact hanti _ (chainVertex_mem_sign σ r).1 (chainVertex_mem_sign σ r).2
        rw [hfun, isAlt_neg]
      have hneg_card : (Hpos.filter (fun σ => IsAlt false (fun r => lam (chainVertex σ r)))).card =
          (Hneg.filter (fun σ => IsAlt true (fun r => lam (chainVertex σ r)))).card := by
        have hinj : Function.Injective negChain := fun a b h => by
          have := congrArg negChain h; rwa [hneg_inv, hneg_inv] at this
        have himg : (Hpos.filter (fun σ => IsAlt false (fun r => lam (chainVertex σ r)))).image negChain =
            Hneg.filter (fun σ => IsAlt true (fun r => lam (chainVertex σ r))) := by
          ext σ
          simp only [Finset.mem_image, Finset.mem_filter, Hpos, Hneg, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨τ, ⟨hτpos, hτalt⟩, rfl⟩
            exact ⟨by simp [negChain, hτpos], (hneg_alt τ).mp hτalt⟩
          · rintro ⟨hσneg, hσalt⟩
            refine ⟨negChain σ, ⟨by simp [negChain, hσneg], ?_⟩, hneg_inv σ⟩
            rw [hneg_alt, hneg_inv]; exact hσalt
        rw [← himg, Finset.card_image_of_injective _ hinj]
      have hsplit_all : ((Finset.univ : Finset (SignedChain D)).filter
            (fun σ => IsAlt true (fun r => lam (chainVertex σ r)))).card =
          (Hpos.filter (fun σ => IsAlt true (fun r => lam (chainVertex σ r)))).card +
          (Hneg.filter (fun σ => IsAlt true (fun r => lam (chainVertex σ r)))).card := by
        have hdisj : Disjoint (Hpos.filter (fun σ => IsAlt true (fun r => lam (chainVertex σ r))))
            (Hneg.filter (fun σ => IsAlt true (fun r => lam (chainVertex σ r)))) := by
          rw [Finset.disjoint_left]; intro σ h1 h2
          have c1 := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
          have c2 := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
          rw [c1] at c2; exact Bool.noConfusion c2
        have hunion : Hpos.filter (fun σ => IsAlt true (fun r => lam (chainVertex σ r))) ∪
            Hneg.filter (fun σ => IsAlt true (fun r => lam (chainVertex σ r))) =
            Finset.univ.filter (fun σ => IsAlt true (fun r => lam (chainVertex σ r))) := by
          ext σ
          simp only [Finset.mem_union, Finset.mem_filter, Hpos, Hneg, Finset.mem_univ, true_and]
          cases h : σ.2 lastD <;> simp
        rw [← hunion, Finset.card_union_of_disjoint hdisj]
      rw [h2, Finset.sum_add_distrib, ← Finset.card_filter, ← Finset.card_filter, hneg_card, hsplit_all]
    -- Step 2: Split goodPairs into boundary (`r = lastD ∧ σ.1 lastD = lastD`) vs interior!
    let bdry := goodPairs.filter (fun p => p.2 = lastD ∧ p.1.1 lastD = lastD)
    let interior := goodPairs.filter (fun p => ¬ (p.2 = lastD ∧ p.1.1 lastD = lastD))
    have hsplit : goodPairs.card = bdry.card + interior.card := by
      have hdisj : Disjoint bdry interior := by
        rw [Finset.disjoint_left]; intro p h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hunion : bdry ∪ interior = goodPairs := by
        ext p; simp only [bdry, interior, Finset.mem_union, Finset.mem_filter]; tauto
      rw [← hunion, Finset.card_union_of_disjoint hdisj]
    -- Step 3: Fixed-point-free involution on `interior` → Even interior.card!
    have hint_even : Even interior.card := by
      let piv : SignedChain D × Fin D → SignedChain D × Fin D := fun ⟨⟨π, s⟩, r⟩ =>
        if hr : r.val < k + 1 then
          (((Equiv.swap r ⟨r.val + 1, by omega⟩).trans π, s), r)
        else
          let j₀ := π lastD
          ((π, Function.update s j₀ (!s j₀)), r)
      have hpiv_props : ∀ p ∈ interior, piv p ∈ interior ∧ piv (piv p) = p ∧ piv p ≠ p := by
        intro ⟨⟨π, s⟩, r⟩ hp
        obtain ⟨hpG, hpNotB⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpProd, hAlt⟩ := Finset.mem_filter.mp hpG
        have hsLast : s lastD = true := (Finset.mem_filter.mp (Finset.mem_product.mp hpProd).1).2
        dsimp only at hpNotB hAlt
        by_cases hr : r.val < k + 1
        · let sw : Equiv.Perm (Fin D) := Equiv.swap r ⟨r.val + 1, by omega⟩
          have hp_eq : piv ((π, s), r) = ((sw.trans π, s), r) := by simp only [piv, hr, ↓reduceDIte, sw]
          -- Vertex invariance for every `j : Fin (k + 1)` (`r.succAbove j ≠ r`)!
          have hv_eq : ∀ j : Fin (k + 1),
              chainVertex (sw.trans π, s) (r.succAbove j) = chainVertex (π, s) (r.succAbove j) := by
            intro j; funext i; unfold chainVertex
            have hsymm : (sw.trans π).symm i = sw (π.symm i) := by
              change sw.symm (π.symm i) = sw (π.symm i); rw [Equiv.symm_swap]
            rw [hsymm]
            have hne : (r.succAbove j).val ≠ r.val := Fin.val_ne_of_ne (r.succAbove_ne j)
            have hiff : (sw (π.symm i)).val ≤ (r.succAbove j).val ↔ (π.symm i).val ≤ (r.succAbove j).val := by
              by_cases h1 : π.symm i = r
              · rw [h1, Equiv.swap_apply_left]; dsimp; omega
              · by_cases h2 : π.symm i = ⟨r.val + 1, by omega⟩
                · rw [h2, Equiv.swap_apply_right]; dsimp; omega
                · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
            by_cases h : (π.symm i).val ≤ (r.succAbove j).val
            · simp [h, hiff.mpr h]
            · simp [h, mt hiff.mp h]
          refine ⟨?_, ?_, ?_⟩
          · rw [hp_eq]
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsLast⟩, Finset.mem_univ _⟩, ?_⟩, ?_⟩
            · simpa [hv_eq] using hAlt
            · rintro ⟨hEq, _⟩; have := congrArg Fin.val hEq; simp [lastD] at this; omega
          · rw [hp_eq]; simp only [piv, hr, ↓reduceDIte]
            refine Prod.ext (Prod.ext ?_ rfl) rfl
            ext x; simp [sw]
          · rw [hp_eq]; intro hEq
            have hπEq : sw.trans π = π := congrArg (fun q : SignedChain D × Fin D => q.1.1) hEq
            have hval := congrArg (fun e : Equiv.Perm (Fin D) => e r) hπEq
            simp only [Equiv.trans_apply, sw, Equiv.swap_apply_left] at hval
            have := congrArg Fin.val (π.injective hval); dsimp at this; omega
        · -- `r = lastD` and `π lastD ≠ lastD`!
          have hr_eq : r = lastD := Fin.ext (by have := r.isLt; change r.val = k + 1; omega)
          have hπne : π lastD ≠ lastD := fun h => hpNotB ⟨hr_eq, h⟩
          let j₀ := π lastD
          let s' := Function.update s j₀ (!s j₀)
          have hp_eq : piv ((π, s), r) = ((π, s'), r) := by simp only [piv, hr, ↓reduceDIte, s', j₀]
          have hv_eq : ∀ j : Fin (k + 1),
              chainVertex (π, s') (r.succAbove j) = chainVertex (π, s) (r.succAbove j) := by
            intro j; funext i; unfold chainVertex
            have hlt : (r.succAbove j).val < k + 1 := by
              rw [hr_eq, Fin.succAbove_last]; exact j.isLt
            by_cases hi : i = j₀
            · subst hi
              have hsymm : (π.symm j₀).val = k + 1 := by dsimp only [j₀]; rw [Equiv.symm_apply_apply]; rfl
              have hnotle : ¬ (π.symm j₀).val ≤ (r.succAbove j).val := by omega
              simp only [hnotle, ↓reduceIte]
            · simp only [s', Function.update_of_ne hi]
          refine ⟨?_, ?_, ?_⟩
          · rw [hp_eq]
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩, ?_⟩, ?_⟩
            · dsimp only [s', j₀]; rw [Function.update_of_ne hπne.symm]; exact hsLast
            · simpa [hv_eq] using hAlt
            · rintro ⟨_, hEq⟩; exact hπne hEq
          · rw [hp_eq]; simp only [piv, hr, ↓reduceDIte]
            refine Prod.ext (Prod.ext rfl ?_) rfl
            funext i
            dsimp only [s', j₀]
            by_cases hi : i = π lastD
            · subst hi; simp
            · simp [Function.update_of_ne hi]
          · rw [hp_eq]; intro hEq
            have hsEq := congrFun (congrArg (fun q : SignedChain D × Fin D => q.1.2) hEq) j₀
            simp [s'] at hsEq
      exact even_card_of_involution piv
        (fun p hp => (hpiv_props p hp).1)
        (fun p hp => (hpiv_props p hp).2.1)
        (fun p hp => (hpiv_props p hp).2.2)
    -- Step 4: Biject `bdry` with `{τ : SignedChain (k + 1) | IsAlt true (lam' ∘ chainVertex τ)}`!
    let embedVec : (Fin (k + 1) → ℤ) → (Fin D → ℤ) := fun x j =>
      if h : j.val < k + 1 then x ⟨j.val, h⟩ else 0
    have hembed_sign : ∀ x : Fin (k + 1) → ℤ,
        (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 →
        (∀ j, embedVec x j = -1 ∨ embedVec x j = 0 ∨ embedVec x j = 1) ∧ embedVec x ≠ 0 := by
      intro x hx hnzx
      refine ⟨fun j => ?_, fun h0 => hnzx (funext fun j => ?_)⟩
      · unfold embedVec; split_ifs with h
        · exact hx ⟨j.val, h⟩
        · exact Or.inr (Or.inl rfl)
      · have hval := congrFun h0 j.castSucc
        simp only [embedVec, Fin.val_castSucc, j.isLt, ↓reduceDIte, Pi.zero_apply] at hval
        exact hval
    let lam' : (Fin (k + 1) → ℤ) → ℤ := fun x => lam (embedVec x)
    have hIH := ih lam'
      (fun x hx hnzx => by
        have hneg : embedVec (-x) = -embedVec x := by
          funext j; simp only [Pi.neg_apply, embedVec]
          by_cases h : j.val < k + 1 <;> simp only [h, ↓reduceDIte, neg_zero]
        rw [show lam' (-x) = lam (embedVec (-x)) from rfl, hneg]
        exact hanti _ (hembed_sign x hx hnzx).1 (hembed_sign x hx hnzx).2)
      (fun x hx hnzx => hnz _ (hembed_sign x hx hnzx).1 (hembed_sign x hx hnzx).2)
      (fun x y hx hnzx hy hnzy hle =>
        hno_comp _ _ (hembed_sign x hx hnzx).1 (hembed_sign x hx hnzx).2
          (hembed_sign y hy hnzy).1 (hembed_sign y hy hnzy).2 (fun j => by
            unfold embedVec; split_ifs with h
            · exact hle ⟨j.val, h⟩
            · exact Or.inl rfl))
    -- Build the explicit bijection `lift : SignedChain (k + 1) → SignedChain D × Fin D`!
    let liftPerm : Equiv.Perm (Fin (k + 1)) → Equiv.Perm (Fin D) := fun π =>
      { toFun := fun i => if h : i.val < k + 1 then (π ⟨i.val, h⟩).castSucc else lastD
        invFun := fun j => if h : j.val < k + 1 then (π.symm ⟨j.val, h⟩).castSucc else lastD
        left_inv := fun i => by
          ext; dsimp only
          by_cases h : i.val < k + 1
          · have hlt : (π ⟨i.val, h⟩).val < k + 1 := (π _).isLt
            simp only [h, ↓reduceDIte, Fin.val_castSucc, hlt, Fin.eta, Equiv.symm_apply_apply]
          · have hi : i.val = k + 1 := by have := i.isLt; omega
            have hnl : ¬ lastD.val < k + 1 := by simp [lastD]
            simp only [h, ↓reduceDIte, hnl]
            simp only [lastD, Fin.val_last, hi]
        right_inv := fun j => by
          ext; dsimp only
          by_cases h : j.val < k + 1
          · have hlt : (π.symm ⟨j.val, h⟩).val < k + 1 := (π.symm _).isLt
            simp only [h, ↓reduceDIte, Fin.val_castSucc, hlt, Fin.eta, Equiv.apply_symm_apply]
          · have hj : j.val = k + 1 := by have := j.isLt; omega
            have hnl : ¬ lastD.val < k + 1 := by simp [lastD]
            simp only [h, ↓reduceDIte, hnl]
            simp only [lastD, Fin.val_last, hj] }
    let lift : SignedChain (k + 1) → SignedChain D × Fin D := fun ⟨π, s⟩ =>
      ((liftPerm π, fun j => if h : j.val < k + 1 then s ⟨j.val, h⟩ else true), lastD)
    have hlift_vertex : ∀ (τ : SignedChain (k + 1)) (j : Fin (k + 1)),
        chainVertex (lift τ).1 (lastD.succAbove j) = embedVec (chainVertex τ j) := by
      intro ⟨π, s⟩ j
      funext i
      rw [Fin.succAbove_last]
      unfold chainVertex embedVec
      by_cases hi : i.val < k + 1
      · simp only [lift, liftPerm, hi, ↓reduceDIte, Equiv.coe_fn_symm_mk, Fin.val_castSucc]
      · simp only [lift, liftPerm, hi, ↓reduceDIte, Equiv.coe_fn_symm_mk]
        have hnotle : ¬ lastD.val ≤ j.val := by have := j.isLt; simp [lastD]; omega
        simp [hnotle]
    have hbdry_card : bdry.card = ((Finset.univ : Finset (SignedChain (k + 1))).filter
        (fun τ => IsAlt true (fun r => lam' (chainVertex τ r)))).card := by
      have hinj : Function.Injective lift := by
        rintro ⟨π₁, s₁⟩ ⟨π₂, s₂⟩ hEq
        have h1 := congrArg (fun q : SignedChain D × Fin D => q.1.1) hEq
        have h2 := congrArg (fun q : SignedChain D × Fin D => q.1.2) hEq
        refine Prod.ext (Equiv.ext fun i => Fin.ext ?_) (funext fun i => ?_)
        · have hv := congrArg (fun e : Equiv.Perm (Fin D) => (e i.castSucc).val) h1
          simp only [lift, liftPerm, Equiv.coe_fn_mk, Fin.val_castSucc, i.isLt, ↓reduceDIte, Fin.eta] at hv
          exact hv
        · have hv := congrFun h2 i.castSucc
          simp only [lift, Fin.val_castSucc, i.isLt, ↓reduceDIte, Fin.eta] at hv
          exact hv
      have himg : ((Finset.univ : Finset (SignedChain (k + 1))).filter
          (fun τ => IsAlt true (fun r => lam' (chainVertex τ r)))).image lift = bdry := by
        ext ⟨⟨π, s⟩, r⟩
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, and_true,
          bdry, goodPairs, Hpos, Finset.mem_product]
        constructor
        · rintro ⟨τ, hτAlt, hEq⟩
          have h1 : (lift τ).1 = (π, s) := congrArg Prod.fst hEq
          have h2 : (lift τ).2 = r := congrArg Prod.snd hEq
          subst h2
          have hπ : π = (lift τ).1.1 := (congrArg Prod.fst h1).symm
          have hs : s = (lift τ).1.2 := (congrArg Prod.snd h1).symm
          subst hπ; subst hs
          have hnl : ¬ lastD.val < k + 1 := by simp [lastD]
          refine ⟨⟨by dsimp only [lift]; rw [dif_neg hnl], ?_⟩, rfl,
            by simp only [lift, liftPerm, Equiv.coe_fn_mk, hnl, ↓reduceDIte]⟩
          have hfun : (fun j : Fin (k + 1) => lam (chainVertex (lift τ).1 ((lift τ).2.succAbove j))) =
              (fun j : Fin (k + 1) => lam' (chainVertex τ j)) := by
            funext j; exact congrArg lam (hlift_vertex τ j)
          rw [hfun]; exact hτAlt
        · rintro ⟨⟨hsLast, hAlt⟩, hrLast, hπLast⟩
          subst hrLast
          let π₀ : Equiv.Perm (Fin (k + 1)) :=
            { toFun := fun i =>
                have hi : (π i.castSucc).val < k + 1 := by
                  have hne : π i.castSucc ≠ lastD := by
                    rw [← hπLast]; intro h; have := congrArg Fin.val (π.injective h); simp [lastD] at this; omega
                  have := (π i.castSucc).isLt; have := Fin.val_ne_of_ne hne; simp [lastD] at this; omega
                ⟨(π i.castSucc).val, hi⟩
              invFun := fun j =>
                have hj : (π.symm j.castSucc).val < k + 1 := by
                  have hne : π.symm j.castSucc ≠ lastD := by
                    intro h
                    have := congrArg Fin.val (show j.castSucc = π lastD by rw [← h, Equiv.apply_symm_apply])
                    rw [hπLast] at this; simp [lastD] at this; omega
                  have := (π.symm j.castSucc).isLt; have := Fin.val_ne_of_ne hne; simp [lastD] at this; omega
                ⟨(π.symm j.castSucc).val, hj⟩
              left_inv := fun i => by
                ext; dsimp only
                have hcast : ∀ h, (⟨(π i.castSucc).val, h⟩ : Fin (k + 1)).castSucc = π i.castSucc :=
                  fun _ => Fin.ext rfl
                rw [hcast, Equiv.symm_apply_apply]; rfl
              right_inv := fun j => by
                ext; dsimp only
                have hcast : ∀ h, (⟨(π.symm j.castSucc).val, h⟩ : Fin (k + 1)).castSucc = π.symm j.castSucc :=
                  fun _ => Fin.ext rfl
                rw [hcast, Equiv.apply_symm_apply]; rfl }
          let s₀ : Fin (k + 1) → Bool := fun i => s i.castSucc
          have hlift_eq : lift (π₀, s₀) = ((π, s), lastD) := by
            refine Prod.ext (Prod.ext ?_ ?_) rfl
            · ext i; dsimp only [lift, liftPerm, π₀]; rw [Equiv.coe_fn_mk]
              by_cases hi : i.val < k + 1
              · simp only [hi, ↓reduceDIte, Fin.val_castSucc, Equiv.coe_fn_mk]
                exact congrArg (fun x => (π x).val) (Fin.ext rfl)
              · have hlast : i = lastD := Fin.ext (by have := i.isLt; change i.val = k + 1; omega)
                subst hlast; simp only [hi, ↓reduceDIte]
                exact congrArg Fin.val hπLast.symm
            · funext i; dsimp only [lift, s₀]
              by_cases hi : i.val < k + 1
              · rw [dif_pos hi]; exact congrArg s (Fin.ext rfl)
              · have hlast : i = lastD := Fin.ext (by have := i.isLt; change i.val = k + 1; omega)
                subst hlast; rw [dif_neg hi]; exact hsLast.symm
          have hAlt0 : IsAlt true (fun j => lam' (chainVertex (π₀, s₀) j)) := by
            have hfun : (fun j => lam' (chainVertex (π₀, s₀) j)) =
                (fun j => lam (chainVertex (π, s) (lastD.succAbove j))) := by
              funext j; change lam (embedVec (chainVertex (π₀, s₀) j)) = _
              rw [← hlift_vertex (π₀, s₀) j, hlift_eq]
            rw [hfun]; exact hAlt
          exact ⟨(π₀, s₀), hAlt0, hlift_eq⟩
      rw [← himg, Finset.card_image_of_injective _ hinj]
    -- Step 5: Combine parities!
    rcases hint_even with ⟨e, he⟩
    rcases hIH with ⟨q, hq⟩
    have hodd : ((Finset.univ : Finset (SignedChain D)).filter
        (fun σ => IsAlt true (fun r => lam (chainVertex σ r)))).card % 2 = 1 := by
      rw [← hmod_all, hsplit, hbdry_card, he, hq]; omega
    exact Nat.odd_iff.mpr hodd

/-- **Ky Fan's Lemma (1952, Pure-Mathlib Existence Form):**
For any `n ≥ 1` and any antipodal nonzero labeling `lam : (Fin n → ℤ) → ℤ` on `{-1, 0, 1}^n \ {0}`
without a complementary face-pair `x ≼ y` (`lam x + lam y = 0`), there exists a maximal chain
`v : Fin n → (Fin n → ℤ)` in `{-1, 0, 1}^n \ {0}` (`v r₁ ≼ v r₂` for `r₁ ≤ r₂`) and a sorting
permutation `e : Equiv.Perm (Fin n)` whose labels have strictly increasing absolute values and
alternating signs `+ , - , + , ...`. -/
theorem ky_fan_lemma (n : ℕ) (hn : 1 ≤ n)
    (lam : (Fin n → ℤ) → ℤ)
    (hanti : ∀ x : Fin n → ℤ, (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 → lam (-x) = -lam x)
    (hnz : ∀ x : Fin n → ℤ, (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 → lam x ≠ 0)
    (hno_comp : ∀ x y : Fin n → ℤ,
      (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 →
      (∀ j, y j = -1 ∨ y j = 0 ∨ y j = 1) → y ≠ 0 →
      (∀ j, x j = 0 ∨ x j = y j) → lam x + lam y ≠ 0) :
    ∃ (v : Fin n → (Fin n → ℤ)) (e : Equiv.Perm (Fin n)),
      (∀ r, (∀ j, v r j = -1 ∨ v r j = 0 ∨ v r j = 1) ∧ v r ≠ 0) ∧
      (∀ r₁ r₂, r₁ ≤ r₂ → ∀ j, v r₁ j = 0 ∨ v r₁ j = v r₂ j) ∧
      StrictMono (fun r => (lam (v (e r))).natAbs) ∧
      ∀ r : Fin n, if r.val % 2 = 0 then 0 < lam (v (e r)) else lam (v (e r)) < 0 := by
  have hodd := ky_fan_odd_alternating n hn lam hanti hnz hno_comp
  have hpos : 0 < ((Finset.univ : Finset (SignedChain n)).filter
      (fun σ => IsAlt true (fun r => lam (chainVertex σ r)))).card := by
    rcases hodd with ⟨k, hk⟩; omega
  obtain ⟨σ, hσ⟩ := Finset.card_pos.mp hpos
  obtain ⟨e, hmono, hsgn⟩ := (Finset.mem_filter.mp hσ).2
  refine ⟨chainVertex σ, e, fun r => chainVertex_mem_sign σ r,
    fun r₁ r₂ hle => chainVertex_face_le σ hle, hmono, fun r => ?_⟩
  simpa using hsgn r

/-- **Combinatorial Tucker's Lemma (Face-Poset Form on `{-1, 0, 1}^n \ {0}`):**
For any `n ≥ 1` and any antipodal labeling `lam : (Fin n → ℤ) → ℤ` taking values in
`{±1, ..., ±(n - 1)}` on `{-1, 0, 1}^n \ {0}`, there exist `x, y ∈ {-1, 0, 1}^n \ {0}`
with `x ≼ y` (every nonzero entry of `x` equals the corresponding entry of `y`) such that
`lam x + lam y = 0`. -/
theorem tucker_lemma_combinatorial (n : ℕ) (hn : 1 ≤ n)
    (lam : (Fin n → ℤ) → ℤ)
    (hanti : ∀ x : Fin n → ℤ, (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 → lam (-x) = -lam x)
    (hrange : ∀ x : Fin n → ℤ, (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 →
      lam x ≠ 0 ∧ (lam x).natAbs ≤ n - 1) :
    ∃ x y : Fin n → ℤ,
      (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) ∧ x ≠ 0 ∧
      (∀ j, y j = -1 ∨ y j = 0 ∨ y j = 1) ∧ y ≠ 0 ∧
      (∀ j, x j = 0 ∨ x j = y j) ∧
      lam x + lam y = 0 := by
  by_contra hno
  push Not at hno
  have hodd := ky_fan_odd_alternating n hn lam hanti
    (fun x hx hnzx => (hrange x hx hnzx).1) hno
  have hpos : 0 < ((Finset.univ : Finset (SignedChain n)).filter
      (fun σ => IsAlt true (fun r => lam (chainVertex σ r)))).card := by
    rcases hodd with ⟨k, hk⟩; omega
  obtain ⟨σ, hσ⟩ := Finset.card_pos.mp hpos
  have halt := (Finset.mem_filter.mp hσ).2
  have hinj : Function.Injective (fun r : Fin n => (lam (chainVertex σ r)).natAbs) := isAlt_inj halt
  have hsub : (Finset.univ : Finset (Fin n)).image (fun r => (lam (chainVertex σ r)).natAbs) ⊆
      Finset.Icc 1 (n - 1) := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨r, _, rfl⟩
    have hsign := chainVertex_mem_sign σ r
    have hr := hrange _ hsign.1 hsign.2
    refine Finset.mem_Icc.mpr ⟨?_, hr.2⟩
    have : (lam (chainVertex σ r)).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hr.1
    omega
  have hcard_le := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, Nat.card_Icc] at hcard_le
  omega

/-- **Combinatorial Tucker's Lemma (`ℓ_∞`-Adjacency Form):**
Every antipodal labeling `lam : {-1, 0, 1}^n \ {0} → {±1, ..., ±(n - 1)}` admits two sign
vectors `x, y` with `∀ j, |x j - y j| ≤ 1` and `lam x + lam y = 0`. -/
theorem tucker_lemma_linf (n : ℕ) (hn : 1 ≤ n)
    (lam : (Fin n → ℤ) → ℤ)
    (hanti : ∀ x : Fin n → ℤ, (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 → lam (-x) = -lam x)
    (hrange : ∀ x : Fin n → ℤ, (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 →
      lam x ≠ 0 ∧ (lam x).natAbs ≤ n - 1) :
    ∃ x y : Fin n → ℤ,
      (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) ∧ x ≠ 0 ∧
      (∀ j, y j = -1 ∨ y j = 0 ∨ y j = 1) ∧ y ≠ 0 ∧
      (∀ j, |x j - y j| ≤ 1) ∧
      lam x + lam y = 0 := by
  obtain ⟨x, y, hx, hnx, hy, hny, hle, hsum⟩ := tucker_lemma_combinatorial n hn lam hanti hrange
  refine ⟨x, y, hx, hnx, hy, hny, fun j => ?_, hsum⟩
  rcases hle j with h0 | hEq
  · rw [h0, zero_sub, abs_neg]
    rcases hy j with h | h | h <;> simp [h]
  · rw [hEq, sub_self, abs_zero]; norm_num

/-- **Discrete Borsuk–Ulam Theorem:**
There is NO antipodal map `lam : {-1, 0, 1}^n \ {0} → {±1, ..., ±(n - 1)}` that avoids
complementary adjacent sign vectors `x ≼ y` (`lam x + lam y = 0`). -/
theorem discrete_borsuk_ulam (n : ℕ) (hn : 1 ≤ n)
    (lam : (Fin n → ℤ) → ℤ)
    (hanti : ∀ x : Fin n → ℤ, (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 → lam (-x) = -lam x)
    (hrange : ∀ x : Fin n → ℤ, (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 →
      lam x ≠ 0 ∧ (lam x).natAbs ≤ n - 1)
    (hno_comp : ∀ x y : Fin n → ℤ,
      (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 →
      (∀ j, y j = -1 ∨ y j = 0 ∨ y j = 1) → y ≠ 0 →
      (∀ j, x j = 0 ∨ x j = y j) → lam x + lam y ≠ 0) :
    False := by
  obtain ⟨x, y, hx, hnx, hy, hny, hle, hsum⟩ := tucker_lemma_combinatorial n hn lam hanti hrange
  exact hno_comp x y hx hnx hy hny hle hsum

end KyFanTucker

/-! ## Section 4: Lovász's 1978 Kneser Graph Chromatic Number Theorem (`χ(KG(n, k)) = n - 2k + 2`) -/

section KneserChromaticNumber

/-- Binary weight `∑ i ∈ s, 2 ^ i.val` on subsets of `Fin n` (strictly injective, giving a
canonical linear order on `Finset (Fin n)`). -/
private def bitVal {n : ℕ} (s : Finset (Fin n)) : ℕ :=
  ∑ i ∈ s, 2 ^ i.val

private lemma sum_pow_two_lt (m : ℕ) : ∑ i ∈ Finset.range m, 2 ^ i < 2 ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

private lemma bitVal_lt_of_max_diff {n : ℕ} {s t : Finset (Fin n)} {m : Fin n}
    (hms : m ∈ s) (hmt : m ∉ t)
    (hgt : ∀ j : Fin n, m < j → (j ∈ s ↔ j ∈ t)) :
    bitVal t < bitVal s := by
  let hi := Finset.univ.filter (fun j : Fin n => m < j)
  let lo := Finset.univ.filter (fun j : Fin n => j < m)
  have hpart_s : s = (s ∩ hi) ∪ insert m (s ∩ lo) := by
    ext j
    simp only [hi, lo, Finset.mem_union, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hjs
      rcases lt_trichotomy j m with hlt | rfl | hgt'
      · exact Or.inr (Or.inr ⟨hjs, hlt⟩)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl ⟨hjs, hgt'⟩
    · rintro (⟨hjs, _⟩ | rfl | ⟨hjs, _⟩)
      · exact hjs
      · exact hms
      · exact hjs
  have hpart_t : t = (t ∩ hi) ∪ (t ∩ lo) := by
    ext j
    simp only [hi, lo, Finset.mem_union, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hjt
      rcases lt_trichotomy j m with hlt | rfl | hgt'
      · exact Or.inr ⟨hjt, hlt⟩
      · exact absurd hjt hmt
      · exact Or.inl ⟨hjt, hgt'⟩
    · rintro (⟨hjt, _⟩ | ⟨hjt, _⟩) <;> exact hjt
  have hhi_eq : s ∩ hi = t ∩ hi := by
    ext j
    simp only [hi, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(hgt j h2).mp h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(hgt j h2).mpr h1, h2⟩⟩
  have hdisj_s : Disjoint (s ∩ hi) (insert m (s ∩ lo)) := by
    rw [Finset.disjoint_left]; intro j h1 h2
    have hgtj : m < j := (Finset.mem_filter.mp (Finset.mem_inter.mp h1).2).2
    simp only [Finset.mem_insert, Finset.mem_inter, lo, Finset.mem_filter, Finset.mem_univ, true_and] at h2
    rcases h2 with rfl | ⟨_, hltj⟩
    · exact lt_irrefl _ hgtj
    · exact lt_asymm hgtj hltj
  have hdisj_t : Disjoint (t ∩ hi) (t ∩ lo) := by
    rw [Finset.disjoint_left]; intro j h1 h2
    have hgtj : m < j := (Finset.mem_filter.mp (Finset.mem_inter.mp h1).2).2
    have hltj : j < m := (Finset.mem_filter.mp (Finset.mem_inter.mp h2).2).2
    exact lt_asymm hgtj hltj
  have hm_not_lo : m ∉ s ∩ lo := by
    simp [lo]
  have hlo_lt : ∑ j ∈ t ∩ lo, 2 ^ j.val < 2 ^ m.val := by
    have hsub : (t ∩ lo).image Fin.val ⊆ Finset.range m.val := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
      exact Finset.mem_range.mpr (Finset.mem_filter.mp (Finset.mem_inter.mp hj).2).2
    have hsum_img : ∑ j ∈ t ∩ lo, 2 ^ j.val = ∑ x ∈ (t ∩ lo).image Fin.val, 2 ^ x := by
      rw [Finset.sum_image (fun a _ b _ h => Fin.ext h)]
    calc ∑ j ∈ t ∩ lo, 2 ^ j.val
        = ∑ x ∈ (t ∩ lo).image Fin.val, 2 ^ x := hsum_img
      _ ≤ ∑ x ∈ Finset.range m.val, 2 ^ x := Finset.sum_le_sum_of_subset hsub
      _ < 2 ^ m.val := sum_pow_two_lt m.val
  unfold bitVal
  rw [hpart_s, hpart_t, Finset.sum_union hdisj_s, Finset.sum_union hdisj_t,
    Finset.sum_insert hm_not_lo, hhi_eq]
  omega

private lemma bitVal_injective {n : ℕ} : Function.Injective (@bitVal n) := by
  intro s t hEq
  by_contra hne
  let diff := (s \ t) ∪ (t \ s)
  have hdiff_ne : diff.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hne; ext j
    have h1 : j ∉ s \ t := fun h => by
      have : j ∈ diff := Finset.mem_union_left _ h
      rw [hemp] at this; exact Finset.notMem_empty _ this
    have h2 : j ∉ t \ s := fun h => by
      have : j ∈ diff := Finset.mem_union_right _ h
      rw [hemp] at this; exact Finset.notMem_empty _ this
    simp only [Finset.mem_sdiff, not_and, not_not] at h1 h2
    exact ⟨h1, h2⟩
  let m := diff.max' hdiff_ne
  have hm_mem : m ∈ diff := diff.max'_mem hdiff_ne
  have hgt : ∀ j : Fin n, m < j → (j ∈ s ↔ j ∈ t) := by
    intro j hgtj
    have hj_not : j ∉ diff := fun h => not_lt_of_ge (diff.le_max' j h) hgtj
    simp only [diff, Finset.mem_union, Finset.mem_sdiff, not_or, not_and, not_not] at hj_not
    exact ⟨hj_not.1, hj_not.2⟩
  rcases Finset.mem_union.mp hm_mem with hst | hts
  · obtain ⟨hms, hmt⟩ := Finset.mem_sdiff.mp hst
    have := bitVal_lt_of_max_diff hms hmt hgt
    omega
  · obtain ⟨hmt, hms⟩ := Finset.mem_sdiff.mp hts
    have := bitVal_lt_of_max_diff hmt hms (fun j hj => (hgt j hj).symm)
    omega

/-- **Kneser Graph Upper Bound (`χ(KG(n, k)) ≤ n - 2k + 2`):**
For all `n ≥ 2k ≥ 2`, there exists an explicit proper `(n - 2k + 2)`-coloring of the
Kneser graph on `k`-element subsets of `Fin n`. -/
theorem kneser_coloring_exists (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ col : Finset (Fin n) → Fin (n - 2 * k + 2),
      ∀ A B : Finset (Fin n), A.card = k → B.card = k → Disjoint A B → col A ≠ col B := by
  let col : Finset (Fin n) → Fin (n - 2 * k + 2) := fun A =>
    if hA : A.Nonempty then
      let m := A.min' hA
      if hm : m.val < n - 2 * k + 1 then ⟨m.val, by omega⟩ else ⟨n - 2 * k + 1, by omega⟩
    else ⟨0, by omega⟩
  refine ⟨col, fun A B hA hB hdisj hEq => ?_⟩
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
  let mA := A.min' hAne
  let mB := B.min' hBne
  by_cases hmA : mA.val < n - 2 * k + 1
  · have hcA : (col A).val = mA.val := by dsimp only [col]; rw [dif_pos hAne, dif_pos hmA]
    have hmB : mB.val < n - 2 * k + 1 := by
      by_contra hc
      have hcB : (col B).val = n - 2 * k + 1 := by dsimp only [col]; rw [dif_pos hBne, dif_neg hc]
      have := congrArg Fin.val hEq
      omega
    have hcB : (col B).val = mB.val := by dsimp only [col]; rw [dif_pos hBne, dif_pos hmB]
    have hmEq : mA = mB := Fin.ext (by have := congrArg Fin.val hEq; omega)
    have hmemA : mA ∈ A := A.min'_mem hAne
    have hmemB : mA ∈ B := hmEq ▸ B.min'_mem hBne
    exact Finset.disjoint_left.mp hdisj hmemA hmemB
  · have hcA : (col A).val = n - 2 * k + 1 := by dsimp only [col]; rw [dif_pos hAne, dif_neg hmA]
    have hmB : ¬ mB.val < n - 2 * k + 1 := by
      intro hlt
      have hcB : (col B).val = mB.val := by dsimp only [col]; rw [dif_pos hBne, dif_pos hlt]
      have := congrArg Fin.val hEq
      omega
    let tail := (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => n - 2 * k + 1 ≤ i.val)
    have hAtail : A ⊆ tail := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      have hle : mA ≤ i := A.min'_le i hi
      change mA.val ≤ i.val at hle; omega⟩
    have hBtail : B ⊆ tail := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      have hle : mB ≤ i := B.min'_le i hi
      change mB.val ≤ i.val at hle; omega⟩
    have hAB_sub : A ∪ B ⊆ tail := Finset.union_subset hAtail hBtail
    have htail_le : tail.card ≤ 2 * k - 1 := by
      let f : Fin (2 * k - 1) → Fin n := fun i => ⟨n - 2 * k + 1 + i.val, by omega⟩
      have hsub : tail ⊆ Finset.univ.image f := by
        intro j hj
        have hge : n - 2 * k + 1 ≤ j.val := (Finset.mem_filter.mp hj).2
        have hlt := j.isLt
        refine Finset.mem_image.mpr ⟨⟨j.val - (n - 2 * k + 1), by omega⟩, Finset.mem_univ _, ?_⟩
        ext; dsimp [f]; omega
      exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le (by simp))
    have hcard_u : (A ∪ B).card = 2 * k := by
      rw [Finset.card_union_of_disjoint hdisj, hA, hB]; omega
    have hle := Finset.card_le_card hAB_sub
    omega

/-- **Lovász's 1978 Kneser Conjecture Lower Bound (`χ(KG(n, k)) ≥ n - 2k + 2`),
via Matoušek's (2004) Combinatorial Tucker-Lemma Proof:**
For all `n ≥ 2k ≥ 2`, there is NO proper `(n - 2k + 1)`-coloring of the Kneser graph
on `k`-element subsets of `Fin n`. -/
theorem kneser_no_coloring_lt (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (col : Finset (Fin n) → Fin (n - 2 * k + 1)) :
    ¬ ∀ A B : Finset (Fin n), A.card = k → B.card = k → Disjoint A B → col A ≠ col B := by
  intro hcol
  have hn1 : 1 ≤ n := by omega
  let posSet : (Fin n → ℤ) → Finset (Fin n) := fun x => Finset.univ.filter (fun i => x i = 1)
  let negSet : (Fin n → ℤ) → Finset (Fin n) := fun x => Finset.univ.filter (fun i => x i = -1)
  have hdisj_pn : ∀ x : Fin n → ℤ, Disjoint (posSet x) (negSet x) := by
    intro x; rw [Finset.disjoint_left]; intro i h1 h2
    have e1 := (Finset.mem_filter.mp h1).2
    have e2 := (Finset.mem_filter.mp h2).2
    omega
  have hpos_neg : ∀ x : Fin n → ℤ, posSet (-x) = negSet x := by
    intro x; ext i; simp only [posSet, negSet, Finset.mem_filter, Finset.mem_univ, true_and, Pi.neg_apply]
    omega
  have hneg_neg : ∀ x : Fin n → ℤ, negSet (-x) = posSet x := by
    intro x; ext i; simp only [posSet, negSet, Finset.mem_filter, Finset.mem_univ, true_and, Pi.neg_apply]
    omega
  have hsz_pos : ∀ x : Fin n → ℤ, (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 →
      1 ≤ (posSet x).card + (negSet x).card := by
    intro x hx hnz
    have hex : ∃ j : Fin n, x j ≠ 0 := by
      by_contra h0; push Not at h0; exact hnz (funext h0)
    obtain ⟨j, hj⟩ := hex
    rcases hx j with h | h | h
    · have : j ∈ negSet x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      have := Finset.card_pos.mpr ⟨j, this⟩; omega
    · exact absurd h hj
    · have : j ∈ posSet x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      have := Finset.card_pos.mpr ⟨j, this⟩; omega
  let availCols : (Fin n → ℤ) → Finset ℕ := fun x =>
    ((posSet x).powersetCard k ∪ (negSet x).powersetCard k).image (fun A => (col A).val)
  have havail_neg : ∀ x : Fin n → ℤ, availCols (-x) = availCols x := by
    intro x; simp only [availCols, hpos_neg, hneg_neg, Finset.union_comm]
  have havail_ne : ∀ x : Fin n → ℤ, ¬ ((posSet x).card + (negSet x).card ≤ 2 * k - 2) →
      (availCols x).Nonempty := by
    intro x hge
    have hge' : k ≤ (posSet x).card ∨ k ≤ (negSet x).card := by omega
    rcases hge' with hp | hm
    · obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hp
      exact ⟨(col A).val, Finset.mem_image.mpr ⟨A, Finset.mem_union_left _
        (Finset.mem_powersetCard.mpr ⟨hAsub, hAcard⟩), rfl⟩⟩
    · obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hm
      exact ⟨(col B).val, Finset.mem_image.mpr ⟨B, Finset.mem_union_right _
        (Finset.mem_powersetCard.mpr ⟨hBsub, hBcard⟩), rfl⟩⟩
  -- Matoušek's antipodal Tucker labeling `lam : {-1, 0, 1}^n \ {0} → {±1, ..., ±(n - 1)}`!
  let lam : (Fin n → ℤ) → ℤ := fun x =>
    let sz := (posSet x).card + (negSet x).card
    if _hlow : sz ≤ 2 * k - 2 then
      if bitVal (negSet x) < bitVal (posSet x) then (sz : ℤ) else -(sz : ℤ)
    else if hne : (availCols x).Nonempty then
      let cMax := (availCols x).max' hne
      if ∃ A ∈ (posSet x).powersetCard k, (col A).val = cMax then
        ((2 * k - 1 + cMax : ℕ) : ℤ)
      else
        -((2 * k - 1 + cMax : ℕ) : ℤ)
    else 0
  have hanti : ∀ x : Fin n → ℤ, (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 → lam (-x) = -lam x := by
    intro x hx hnz
    have hsz_eq : (posSet (-x)).card + (negSet (-x)).card = (posSet x).card + (negSet x).card := by
      rw [hpos_neg, hneg_neg, add_comm]
    by_cases hlow : (posSet x).card + (negSet x).card ≤ 2 * k - 2
    · have hlow' : (posSet (-x)).card + (negSet (-x)).card ≤ 2 * k - 2 := by rw [hsz_eq]; exact hlow
      have hne_pn : posSet x ≠ negSet x := by
        intro hEq
        have h1 := hdisj_pn x
        rw [hEq, disjoint_self] at h1
        have h2 : posSet x = ∅ := hEq.trans h1
        have := hsz_pos x hx hnz
        rw [h1, h2] at this; simp at this
      have hbit_ne : bitVal (posSet x) ≠ bitVal (negSet x) := fun h => hne_pn (bitVal_injective h)
      dsimp only [lam]
      rw [dif_pos hlow', dif_pos hlow, hsz_eq, hpos_neg, hneg_neg]
      rcases lt_or_gt_of_ne hbit_ne with hlt | hgt
      · have hnot : ¬ bitVal (negSet x) < bitVal (posSet x) := not_lt_of_gt hlt
        rw [if_pos hlt, if_neg hnot, neg_neg]
      · have hnot : ¬ bitVal (posSet x) < bitVal (negSet x) := not_lt_of_gt hgt
        rw [if_neg hnot, if_pos hgt]
    · have hlow' : ¬ (posSet (-x)).card + (negSet (-x)).card ≤ 2 * k - 2 := by rw [hsz_eq]; exact hlow
      have hne := havail_ne x hlow
      have hne' : (availCols (-x)).Nonempty := (havail_neg x).symm ▸ hne
      let cMax := (availCols x).max' hne
      have hcMax_eq : (availCols (-x)).max' hne' = cMax := by
        congr 1; exact havail_neg x
      -- Exactly ONE of posSet x and negSet x contains a k-subset of color cMax!
      have hxor : (∃ A ∈ (posSet x).powersetCard k, (col A).val = cMax) ↔
          ¬ (∃ B ∈ (negSet x).powersetCard k, (col B).val = cMax) := by
        constructor
        · rintro ⟨A, hA, hAc⟩ ⟨B, hB, hBc⟩
          obtain ⟨hAsub, hAcard⟩ := Finset.mem_powersetCard.mp hA
          obtain ⟨hBsub, hBcard⟩ := Finset.mem_powersetCard.mp hB
          have hABdisj : Disjoint A B := (hdisj_pn x).mono hAsub hBsub
          exact hcol A B hAcard hBcard hABdisj (Fin.ext (hAc.trans hBc.symm))
        · intro hnoB
          have hmem : cMax ∈ availCols x := (availCols x).max'_mem hne
          rcases Finset.mem_image.mp hmem with ⟨C, hC, hCc⟩
          rcases Finset.mem_union.mp hC with hCp | hCn
          · exact ⟨C, hCp, hCc⟩
          · exact absurd ⟨C, hCn, hCc⟩ hnoB
      dsimp only [lam]
      rw [dif_neg hlow', dif_neg hlow, dif_pos hne', dif_pos hne, hcMax_eq, hpos_neg]
      by_cases hex : ∃ A ∈ (posSet x).powersetCard k, (col A).val = cMax
      · have hno : ¬ ∃ B ∈ (negSet x).powersetCard k, (col B).val = cMax := hxor.mp hex
        rw [if_neg hno, if_pos hex]
      · have hyes : ∃ B ∈ (negSet x).powersetCard k, (col B).val = cMax := by
          by_contra hno; exact hex (hxor.mpr hno)
        rw [if_pos hyes, if_neg hex, neg_neg]
  have hrange : ∀ x : Fin n → ℤ, (∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1) → x ≠ 0 →
      lam x ≠ 0 ∧ (lam x).natAbs ≤ n - 1 := by
    intro x hx hnz
    have hsz1 := hsz_pos x hx hnz
    by_cases hlow : (posSet x).card + (negSet x).card ≤ 2 * k - 2
    · simp only [lam, hlow, ↓reduceDIte]
      split_ifs <;> refine ⟨by omega, ?_⟩ <;> simp <;> omega
    · have hne := havail_ne x hlow
      let cMax := (availCols x).max' hne
      have hcMax_lt : cMax < n - 2 * k + 1 := by
        have hmem : cMax ∈ availCols x := (availCols x).max'_mem hne
        rcases Finset.mem_image.mp hmem with ⟨A, _, hAc⟩
        rw [← hAc]; exact (col A).isLt
      simp only [lam, hlow, hne, ↓reduceDIte]
      split_ifs <;> refine ⟨by omega, ?_⟩ <;> simp <;> omega
  -- Apply Combinatorial Tucker's Lemma!
  obtain ⟨x, y, hx, hnx, hy, hny, hxy_le, hsum0⟩ :=
    tucker_lemma_combinatorial n hn1 lam hanti hrange
  have hpos_sub : posSet x ⊆ posSet y := fun j hj => by
    have h1 := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases hxy_le j with h0 | hEq
    · omega
    · rw [← hEq, h1]
  have hneg_sub : negSet x ⊆ negSet y := fun j hj => by
    have h1 := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases hxy_le j with h0 | hEq
    · omega
    · rw [← hEq, h1]
  have habs_eq : (lam x).natAbs = (lam y).natAbs := by
    have : lam x = -lam y := by omega
    rw [this, Int.natAbs_neg]
  have hnz_x : lam x ≠ 0 := (hrange x hx hnx).1
  by_cases hlow_x : (posSet x).card + (negSet x).card ≤ 2 * k - 2
  · have habs_x : (lam x).natAbs = (posSet x).card + (negSet x).card := by
      dsimp only [lam]; rw [dif_pos hlow_x]
      split_ifs <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]
    have hlow_y : (posSet y).card + (negSet y).card ≤ 2 * k - 2 := by
      by_contra hnot
      have hne_y := havail_ne y hnot
      have habs_y : (lam y).natAbs = 2 * k - 1 + (availCols y).max' hne_y := by
        dsimp only [lam]; rw [dif_neg hnot, dif_pos hne_y]
        split_ifs <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]
      omega
    have habs_y : (lam y).natAbs = (posSet y).card + (negSet y).card := by
      dsimp only [lam]; rw [dif_pos hlow_y]
      split_ifs <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]
    have hcard_p : (posSet x).card ≤ (posSet y).card := Finset.card_le_card hpos_sub
    have hcard_n : (negSet x).card ≤ (negSet y).card := Finset.card_le_card hneg_sub
    have hpos_eq : posSet x = posSet y := Finset.eq_of_subset_of_card_le hpos_sub (by omega)
    have hneg_eq : negSet x = negSet y := Finset.eq_of_subset_of_card_le hneg_sub (by omega)
    have hxy_eq : x = y := by
      funext j
      rcases hx j with h | h | h
      · have hj : j ∈ negSet y := hneg_eq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        exact h.trans (Finset.mem_filter.mp hj).2.symm
      · rcases hy j with hyj | hyj | hyj
        · have hj : j ∈ negSet x := hneg_eq.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyj⟩
          have := (Finset.mem_filter.mp hj).2; omega
        · exact h.trans hyj.symm
        · have hj : j ∈ posSet x := hpos_eq.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyj⟩
          have := (Finset.mem_filter.mp hj).2; omega
      · have hj : j ∈ posSet y := hpos_eq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        exact h.trans (Finset.mem_filter.mp hj).2.symm
    rw [hxy_eq] at hsum0; omega
  · have hne_x := havail_ne x hlow_x
    have habs_x : (lam x).natAbs = 2 * k - 1 + (availCols x).max' hne_x := by
      dsimp only [lam]; rw [dif_neg hlow_x, dif_pos hne_x]
      split_ifs <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]
    have hlow_y : ¬ (posSet y).card + (negSet y).card ≤ 2 * k - 2 := by
      have hp := Finset.card_le_card hpos_sub
      have hn' := Finset.card_le_card hneg_sub
      omega
    have hne_y := havail_ne y hlow_y
    have habs_y : (lam y).natAbs = 2 * k - 1 + (availCols y).max' hne_y := by
      dsimp only [lam]; rw [dif_neg hlow_y, dif_pos hne_y]
      split_ifs <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]
    have hc_eq : (availCols x).max' hne_x = (availCols y).max' hne_y := by omega
    let c := (availCols x).max' hne_x
    by_cases hex_x : ∃ A ∈ (posSet x).powersetCard k, (col A).val = c
    · -- `lam x = +(2k - 1 + c)`, so `lam y = -(2k - 1 + c)`, hence `negSet y` has a k-subset of color `c`!
      have hlx : lam x = ((2 * k - 1 + c : ℕ) : ℤ) := by
        simp only [lam, hlow_x, hne_x, ↓reduceDIte, c, hex_x, ↓reduceIte]
      have hno_y : ¬ ∃ A ∈ (posSet y).powersetCard k, (col A).val = c := by
        intro hy_pos
        have hly : lam y = ((2 * k - 1 + c : ℕ) : ℤ) := by
          simp only [lam, hlow_y, hne_y, ↓reduceDIte, ← hc_eq, c, hy_pos, ↓reduceIte]
        omega
      have hmem_y : c ∈ availCols y := by dsimp only [c]; rw [hc_eq]; exact (availCols y).max'_mem hne_y
      rcases Finset.mem_image.mp hmem_y with ⟨B, hB, hBc⟩
      have hBn : B ∈ (negSet y).powersetCard k := by
        rcases Finset.mem_union.mp hB with hBp | hBn
        · exact absurd ⟨B, hBp, hBc⟩ hno_y
        · exact hBn
      obtain ⟨A, hAp, hAc⟩ := hex_x
      obtain ⟨hAsub, hAcard⟩ := Finset.mem_powersetCard.mp hAp
      obtain ⟨hBsub, hBcard⟩ := Finset.mem_powersetCard.mp hBn
      have hABdisj : Disjoint A B := (hdisj_pn y).mono (hAsub.trans hpos_sub) hBsub
      exact hcol A B hAcard hBcard hABdisj (Fin.ext (hAc.trans hBc.symm))
    · -- `lam x = -(2k - 1 + c)`, so `negSet x` has color `c` and `lam y > 0` so `posSet y` has color `c`!
      have hlx : lam x = -((2 * k - 1 + c : ℕ) : ℤ) := by
        simp only [lam, hlow_x, hne_x, ↓reduceDIte, c, hex_x, ↓reduceIte]
      have hex_y : ∃ B ∈ (posSet y).powersetCard k, (col B).val = c := by
        by_contra hno_y
        have hly : lam y = -((2 * k - 1 + c : ℕ) : ℤ) := by
          simp only [lam, hlow_y, hne_y, ↓reduceDIte, ← hc_eq, c, hno_y, ↓reduceIte]
        omega
      have hmem_x : c ∈ availCols x := (availCols x).max'_mem hne_x
      rcases Finset.mem_image.mp hmem_x with ⟨A, hA, hAc⟩
      have hAn : A ∈ (negSet x).powersetCard k := by
        rcases Finset.mem_union.mp hA with hAp | hAn
        · exact absurd ⟨A, hAp, hAc⟩ hex_x
        · exact hAn
      obtain ⟨B, hBp, hBc⟩ := hex_y
      obtain ⟨hAsub, hAcard⟩ := Finset.mem_powersetCard.mp hAn
      obtain ⟨hBsub, hBcard⟩ := Finset.mem_powersetCard.mp hBp
      have hABdisj : Disjoint A B := (hdisj_pn y).symm.mono (hAsub.trans hneg_sub) hBsub
      exact hcol A B hAcard hBcard hABdisj (Fin.ext (hAc.trans hBc.symm))

/-- **Lovász's 1978 Kneser Graph Chromatic Number Theorem (`χ(KG(n, k)) = n - 2k + 2`):**
For all `n ≥ 2k ≥ 2`, the chromatic number of the Kneser graph `KG(n, k)` (vertices =
`k`-element subsets of `Fin n`, edges = disjoint pairs) equals `n - 2k + 2`. -/
theorem kneser_chromatic_number (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (SimpleGraph.mk
      (fun A B : {A : Finset (Fin n) // A.card = k} => Disjoint A.1 B.1)
      ⟨fun _ _ h => h.symm⟩
      ⟨fun A h => absurd (disjoint_self.mp h)
        (Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp (by omega : 0 < A.1.card)))⟩).chromaticNumber =
    ((n - 2 * k + 2 : ℕ) : ℕ∞) := by
  let G : SimpleGraph {A : Finset (Fin n) // A.card = k} :=
    SimpleGraph.mk (fun A B => Disjoint A.1 B.1)
      ⟨fun _ _ h => h.symm⟩
      ⟨fun A h => absurd (disjoint_self.mp h)
        (Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp (by omega : 0 < A.1.card)))⟩
  change G.chromaticNumber = ((n - 2 * k + 2 : ℕ) : ℕ∞)
  have hcol_ub : G.Colorable (n - 2 * k + 2) := by
    obtain ⟨col, hcol⟩ := kneser_coloring_exists n k hk hn
    exact ⟨SimpleGraph.Coloring.mk (fun A => col A.1) (fun {A B} hAB => hcol A.1 B.1 A.2 B.2 hAB)⟩
  apply le_antisymm
  · exact hcol_ub.chromaticNumber_le
  · apply le_iInf₂
    intro c hc
    by_contra hlt
    push Not at hlt
    have hc_le : c ≤ n - 2 * k + 1 := by
      have : (c : ℕ∞) < ((n - 2 * k + 2 : ℕ) : ℕ∞) := hlt
      have hnat : c < n - 2 * k + 2 := Nat.cast_lt.mp this
      omega
    obtain ⟨f⟩ := hc
    let col' : Finset (Fin n) → Fin (n - 2 * k + 1) := fun A =>
      if hA : A.card = k then Fin.castLE hc_le (f ⟨A, hA⟩) else ⟨0, by omega⟩
    apply kneser_no_coloring_lt n k hk hn col'
    intro A B hA hB hdisj hEq
    simp only [col', dif_pos hA, dif_pos hB] at hEq
    have hfEq : f ⟨A, hA⟩ = f ⟨B, hB⟩ := Fin.ext (by simpa using congrArg Fin.val hEq)
    exact f.valid (show G.Adj ⟨A, hA⟩ ⟨B, hB⟩ from hdisj) hfEq

end KneserChromaticNumber

end Arith4Ext.TopologicalComb
