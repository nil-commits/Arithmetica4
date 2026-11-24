/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Logic.Equiv.Defs
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-!
# PPL 071 (Erdős Problem #89): The Erdős Distinct Distances Problem

## Honest Scope & Literature Status
This file formalizes a pure-Mathlib milestone (`0` `sorry`, `0` `native_decide`, `0` custom or
`private` definitions in any public theorem signature) for **PPL 071 / Erdős Problem #89** ($500):
> *Does every set of `n` distinct points in `ℝ²` determine `≫ n / √(log n)` distinct distances?*

**Erdős Problem #89 REMAINS OPEN as of November 2026.**
- Best known lower bound: `Ω(n / log n)` by Guth–Katz (2015, *Annals of Mathematics*).
- Best known upper bound: `O(n / √(log n))` by Erdős (1946) via the `√n × √n` integer grid and
  Landau's (1908) sums-of-two-squares theorem.
- Note: The May 2026 AI-assisted breakthrough (verified by Alon, Bloom, Gowers, Tao, et al.)
  disproved Erdős's *unit distance* conjecture (`u(n) = O(n^{1+o(1)})`, Erdős #90), whereas
  Erdős #89 (distinct distances, closing the `√(log n)` gap between `n / log n` and
  `n / √(log n)`) remains open.

This file does **not** claim to prove `g(n) ≫ n / √(log n)`. Instead, it formally proves:
1. **Erdős (1946) Exact `√n` Distinct Distances Lower Bound** (`k(k+1) ≥ n - 1`, pinned & global)
   and the **Two-Circle Intersection Lemma** (`≤ 2` intersection points in `EuclideanSpace ℝ (Fin 2)`).
2. **Erdős (1946) `√n × √n` Integer-Grid `O(n / √(log n))` Upper Bound** (for all `m × m` grids
   and all `n ≥ 4`, via the `p ≡ 3 (mod 4)` prime obstruction, elementary Dirichlet-convolution
   identity `1_{A'} * 1_{A'} = g * f`, and self-contained Chebyshev `ψ(N) ≤ 4 (log 2) N` bound).
3. **Guth–Katz Quadruple-Energy Cauchy–Schwarz Barrier**:
   - Exact Elekes–Sharir / Guth–Katz Cauchy–Schwarz inequality `|D(P)| · Q(P) ≥ (n(n-1))²`.
   - Sharp lower bound `Q(grid_m) ≥ c · m⁶ · log m` on the `m × m` integer grid, certifying
     rigorously that the `Q(P)` Cauchy–Schwarz pipeline is capped at `O(n / log n)` and can
     never close the `√(log n)` gap to Erdős's `$500` conjecture.
4. **Szemerédi–Trotter (1983) Incidence Theorem & `k`-Rich Lines Bound** (via a completely
   self-contained, topology-free Sweepline / Wiring-Diagram Multigraph Crossing Lemma
   `E³ ≤ 64 m n² K` — zero Jordan Curve Theorem, zero measure theory!).
5. **Spencer–Szemerédi–Trotter (1984) `O(n^{4/3})` Unit Distance Upper Bound**
   (`|{(p, q) ∈ P × P : dist p q = 1}| ≤ 16 |P|^{4/3}`).
6. **Székely (1997) `Ω(n^{4/5})` Pinned & Global Distinct Distances Lower Bound**
   (`∃ p ∈ P, |P|^{4/5} / 250 ≤ |D_p(P)|` and `|P|^{4/5} / 250 ≤ |D(P)|` for all `|P| ≥ 2`).
-/

namespace PPL071

open scoped BigOperators Classical
open Filter Finset

/-! ### Shared Elementary Helpers -/

/-- Extensionality for `EuclideanSpace ℝ (Fin 2)` using coordinates `0` and `1`. -/
private lemma euc2_ext {a b : EuclideanSpace ℝ (Fin 2)} (h0 : a 0 = b 0) (h1 : a 1 = b 1) :
    a = b := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- Squared Euclidean distance formula in `EuclideanSpace ℝ (Fin 2)`. -/
private lemma dist_sq_eq_euc2 (p q : EuclideanSpace ℝ (Fin 2)) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Fin.sum_univ_two, Real.dist_eq]

/-- Self-contained injective sum comparison helper. -/
private lemma sum_le_sum_of_inj_nonneg {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → ℝ) (g : β → ℝ) (φ : α → β)
    (hmaps : ∀ a ∈ s, φ a ∈ t)
    (hinj : Set.InjOn φ (s : Set α))
    (hnonneg : ∀ b ∈ t, 0 ≤ g b)
    (hle : ∀ a ∈ s, f a ≤ g (φ a)) :
    ∑ a ∈ s, f a ≤ ∑ b ∈ t, g b := by
  calc ∑ a ∈ s, f a
      ≤ ∑ a ∈ s, g (φ a) := Finset.sum_le_sum hle
    _ = ∑ b ∈ s.image φ, g b := (Finset.sum_image (fun x hx y hy h => hinj hx hy h)).symm
    _ ≤ ∑ b ∈ t, g b := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b hb _ => hnonneg b hb)
        intro b hb
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        exact hmaps a ha

/-- Self-contained Cauchy–Schwarz for `ℕ`-valued functions over a `Finset`. -/
private lemma sq_sum_le_card_mul_sum_sq_nat {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  have h : (0 : ℤ) ≤ ∑ i ∈ s, ∑ j ∈ s, ((f i : ℤ) - (f j : ℤ)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexp : ∑ i ∈ s, ∑ j ∈ s, ((f i : ℤ) - (f j : ℤ)) ^ 2 =
      2 * ((s.card : ℤ) * ∑ i ∈ s, (f i : ℤ) ^ 2 - (∑ i ∈ s, (f i : ℤ)) ^ 2) := by
    have h1 : ∀ i ∈ s, ∑ j ∈ s, ((f i : ℤ) - (f j : ℤ)) ^ 2 =
        (s.card : ℤ) * (f i : ℤ) ^ 2 - 2 * (f i : ℤ) * (∑ j ∈ s, (f j : ℤ)) +
          ∑ j ∈ s, (f j : ℤ) ^ 2 := by
      intro i _
      calc ∑ j ∈ s, ((f i : ℤ) - (f j : ℤ)) ^ 2
          = ∑ j ∈ s, ((f i : ℤ) ^ 2 - 2 * (f i : ℤ) * (f j : ℤ) + (f j : ℤ) ^ 2) :=
            Finset.sum_congr rfl fun j _ => by ring
        _ = (∑ _j ∈ s, (f i : ℤ) ^ 2) - (∑ j ∈ s, 2 * (f i : ℤ) * (f j : ℤ)) +
              (∑ j ∈ s, (f j : ℤ) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = (s.card : ℤ) * (f i : ℤ) ^ 2 - 2 * (f i : ℤ) * (∑ j ∈ s, (f j : ℤ)) +
              ∑ j ∈ s, (f j : ℤ) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have hmul : ∑ i ∈ s, 2 * (f i : ℤ) * (∑ j ∈ s, (f j : ℤ)) =
        2 * (∑ i ∈ s, (f i : ℤ)) * (∑ j ∈ s, (f j : ℤ)) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [hmul]; ring
  rw [hexp] at h
  have hZ : (∑ i ∈ s, (f i : ℤ)) ^ 2 ≤ (s.card : ℤ) * ∑ i ∈ s, (f i : ℤ) ^ 2 := by linarith
  exact_mod_cast hZ

/-- Number of ordered pairs of distinct elements in a `Finset`. -/
private lemma card_off_diag {α : Type*} [DecidableEq α] (A : Finset α) :
    ((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).card = A.card * (A.card - 1) := by
  have hsplit : ((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).card +
      ((A ×ˢ A).filter (fun p => p.1 = p.2)).card = (A ×ˢ A).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext p; simp; tauto
    · rw [Finset.disjoint_left]; intro p h1 h2
      simp only [Finset.mem_filter] at h1 h2; exact h1.2 h2.2
  have hdiag : ((A ×ˢ A).filter (fun p => p.1 = p.2)).card = A.card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_product] at hp; exact hp.1.1
    · intro p1 hp1 p2 hp2 h
      simp only [Finset.mem_filter, Finset.mem_product] at hp1 hp2
      exact Prod.ext h (hp1.2.symm.trans (h.trans hp2.2))
    · intro a ha; exact ⟨(a, a), by simp [ha], rfl⟩
  rw [hdiag, Finset.card_product] at hsplit
  cases h : A.card with
  | zero => simp [h] at hsplit ⊢; omega
  | succ k => rw [h] at hsplit; simp only [Nat.add_sub_cancel]; nlinarith

/-- Telescoping bound: `∑_{k=1}^N 1 / k^2 ≤ 2`. -/
private lemma sum_inv_sq_le_two (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · suffices hstrong : ∀ m : ℕ, 1 ≤ m →
        ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 - 1 / (m : ℝ) by
      have hm := hstrong N (Nat.one_le_iff_ne_zero.mpr hN)
      have hpos : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      linarith
    intro m hm
    induction m with
    | zero => omega
    | succ j ihj =>
      rcases eq_or_ne j 0 with rfl | hj
      · norm_num
      · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
        have hins : Finset.Icc 1 (j + 1) = insert (j + 1) (Finset.Icc 1 j) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hins, Finset.sum_insert (by simp)]
        have hprev := ihj hj1
        have hjpos : (0 : ℝ) < (j : ℝ) := by positivity
        have hstep : (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2 ≤
            1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ) := by
          have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
          rw [hcast, div_sub_div _ _ (ne_of_gt hjpos) (by linarith),
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith

/-- Elementary harmonic sum upper bound: `∑_{k=1}^N 1/k ≤ Real.log N + 1` for `N ≥ 1`. -/
private lemma harmonic_le_log_add_one (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) ≤ Real.log (N : ℝ) + 1 := by
  induction N with
  | zero => omega
  | succ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hins : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hins, Finset.sum_insert (by simp)]
      have hih := ih hn1
      have hstep : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
        have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
        have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [← Real.log_div (ne_of_gt hn1_pos) (ne_of_gt hn_pos)]
        have hle := Real.one_sub_inv_le_log_of_pos (div_pos hn1_pos hn_pos)
        have heq : 1 - (((n + 1 : ℕ) : ℝ) / (n : ℝ))⁻¹ = 1 / ((n + 1 : ℕ) : ℝ) := by
          rw [inv_div, hcast]; field_simp; ring
        linarith
      linarith

/-- Elementary harmonic sum lower bound: `Real.log (N + 1) ≤ ∑_{k=1}^N 1/k` for all `N`. -/
private lemma log_succ_le_harmonic (N : ℕ) :
    Real.log ((N + 1 : ℕ) : ℝ) ≤ ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hins : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert (by simp)]
    have hstep : Real.log ((n + 2 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) ≤
        1 / ((n + 1 : ℕ) : ℝ) := by
      have h1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have h2 : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
      rw [← Real.log_div (ne_of_gt h2) (ne_of_gt h1)]
      have hle := Real.log_le_sub_one_of_pos (div_pos h2 h1)
      have heq : ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) - 1 = 1 / ((n + 1 : ℕ) : ℝ) := by
        have hc1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        have hc2 : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
        rw [hc1, hc2]; field_simp; ring
      linarith
    linarith

/-- Smallest prime factor of a prime power `p^k` (`k ≥ 1`) is `p`. -/
private lemma minFac_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    (p ^ k).minFac = p := by
  have hne1 : p ^ k ≠ 1 := ne_of_gt (one_lt_pow₀ hp.one_lt (by omega))
  have hpr : (p ^ k).minFac.Prime := Nat.minFac_prime hne1
  have hdvd : (p ^ k).minFac ∣ p := hpr.dvd_of_dvd_pow (Nat.minFac_dvd (p ^ k))
  exact (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hpr.ne_one

/-! ### Section 1: Erdős (1946) Exact `√n` Distinct Distances Lower Bound & Two-Circle Lemma -/

/-- **Two-Circle Intersection Lemma**: Two circles in `EuclideanSpace ℝ (Fin 2)` with distinct
centers `a ≠ b` intersect in at most `2` points of any finite set `P`. -/
theorem ppl071_two_circles_inter_le_two
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (a b : EuclideanSpace ℝ (Fin 2)) (hab : a ≠ b) (r₁ r₂ : ℝ) :
    (P.filter (fun q => dist a q = r₁ ∧ dist b q = r₂)).card ≤ 2 := by
  set S := P.filter (fun q => dist a q = r₁ ∧ dist b q = r₂)
  by_contra hgt
  push Not at hgt
  obtain ⟨q₁, hq₁, S₁, hS₁_sub, hq₁_not, hS₁_card⟩ :
      ∃ q₁ ∈ S, ∃ S₁ ⊆ S, q₁ ∉ S₁ ∧ 2 ≤ S₁.card := by
    obtain ⟨q₁, hq₁⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    refine ⟨q₁, hq₁, S.erase q₁, Finset.erase_subset _ _, Finset.notMem_erase _ _, ?_⟩
    rw [Finset.card_erase_of_mem hq₁]; omega
  obtain ⟨q₂, hq₂S₁, S₂, hS₂_sub, hq₂_not, hS₂_card⟩ :
      ∃ q₂ ∈ S₁, ∃ S₂ ⊆ S₁, q₂ ∉ S₂ ∧ 1 ≤ S₂.card := by
    obtain ⟨q₂, hq₂⟩ := Finset.card_pos.mp (by omega : 0 < S₁.card)
    refine ⟨q₂, hq₂, S₁.erase q₂, Finset.erase_subset _ _, Finset.notMem_erase _ _, ?_⟩
    rw [Finset.card_erase_of_mem hq₂]; omega
  obtain ⟨q₃, hq₃S₂⟩ := Finset.card_pos.mp (by omega : 0 < S₂.card)
  have hq₂ : q₂ ∈ S := hS₁_sub hq₂S₁
  have hq₃ : q₃ ∈ S := hS₁_sub (hS₂_sub hq₃S₂)
  have h12 : q₁ ≠ q₂ := fun h => hq₁_not (h ▸ hq₂S₁)
  have h13 : q₁ ≠ q₃ := fun h => hq₁_not (h ▸ hS₂_sub hq₃S₂)
  have h23 : q₂ ≠ q₃ := fun h => hq₂_not (h ▸ hq₃S₂)
  have hd : ∀ q ∈ S, (q 0 - a 0) ^ 2 + (q 1 - a 1) ^ 2 = r₁ ^ 2 ∧
      (q 0 - b 0) ^ 2 + (q 1 - b 1) ^ 2 = r₂ ^ 2 := by
    intro q hq
    simp only [S, Finset.mem_filter] at hq
    have ha := dist_sq_eq_euc2 q a
    have hb := dist_sq_eq_euc2 q b
    rw [dist_comm, hq.2.1] at ha
    rw [dist_comm, hq.2.2] at hb
    exact ⟨ha.symm, hb.symm⟩
  obtain ⟨ha1, hb1⟩ := hd q₁ hq₁
  obtain ⟨ha2, hb2⟩ := hd q₂ hq₂
  obtain ⟨ha3, hb3⟩ := hd q₃ hq₃
  set dx := b 0 - a 0
  set dy := b 1 - a 1
  have hne : dx ≠ 0 ∨ dy ≠ 0 := by
    by_contra hall; push Not at hall
    apply hab
    exact euc2_ext (by dsimp [dx] at hall; linarith) (by dsimp [dy] at hall; linarith)
  have hlin12 : (q₂ 0 - q₁ 0) * dx + (q₂ 1 - q₁ 1) * dy = 0 := by
    dsimp [dx, dy]; nlinarith
  have hlin13 : (q₃ 0 - q₁ 0) * dx + (q₃ 1 - q₁ 1) * dy = 0 := by
    dsimp [dx, dy]; nlinarith
  have hcol : (q₂ 0 - q₁ 0) * (q₃ 1 - q₁ 1) = (q₃ 0 - q₁ 0) * (q₂ 1 - q₁ 1) := by
    rcases hne with hdx | hdy
    · apply mul_right_cancel₀ hdx
      linear_combination (q₃ 1 - q₁ 1) * hlin12 - (q₂ 1 - q₁ 1) * hlin13
    · apply mul_right_cancel₀ hdy
      linear_combination -(q₃ 0 - q₁ 0) * hlin12 + (q₂ 0 - q₁ 0) * hlin13
  have hc12 : (q₂ 0 - q₁ 0) * (q₂ 0 + q₁ 0 - 2 * a 0) +
      (q₂ 1 - q₁ 1) * (q₂ 1 + q₁ 1 - 2 * a 1) = 0 := by linarith
  have hc13 : (q₃ 0 - q₁ 0) * (q₃ 0 + q₁ 0 - 2 * a 0) +
      (q₃ 1 - q₁ 1) * (q₃ 1 + q₁ 1 - 2 * a 1) = 0 := by linarith
  set u := q₂ 0 - q₁ 0
  set v := q₂ 1 - q₁ 1
  have huv : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h0; push Not at h0
    apply h12
    exact euc2_ext (by dsimp [u] at h0; linarith) (by dsimp [v] at h0; linarith)
  obtain ⟨t, ht0, ht1⟩ : ∃ t : ℝ, q₃ 0 - q₁ 0 = t * u ∧ q₃ 1 - q₁ 1 = t * v := by
    rcases huv with hu | hv
    · refine ⟨(q₃ 0 - q₁ 0) / u, by field_simp, ?_⟩
      field_simp; linarith [hcol]
    · refine ⟨(q₃ 1 - q₁ 1) / v, ?_, by field_simp⟩
      field_simp; linarith [hcol]
  have ht_ne0 : t ≠ 0 := by
    intro ht0'
    apply h13
    exact euc2_ext (by rw [ht0'] at ht0; linarith) (by rw [ht0'] at ht1; linarith)
  have ht_ne1 : t ≠ 1 := by
    intro ht1'
    apply h23
    exact euc2_ext (by rw [ht1'] at ht0; dsimp [u] at ht0; linarith)
      (by rw [ht1'] at ht1; dsimp [v] at ht1; linarith)
  have hsum_pos : 0 < u ^ 2 + v ^ 2 := by
    rcases huv with hu | hv
    · nlinarith [sq_pos_of_ne_zero hu, sq_nonneg v]
    · nlinarith [sq_pos_of_ne_zero hv, sq_nonneg u]
  have hquad : t * (t - 1) * (u ^ 2 + v ^ 2) = 0 := by
    have hq30 : q₃ 0 = q₁ 0 + t * u := by linarith
    have hq31 : q₃ 1 = q₁ 1 + t * v := by linarith
    have hq20 : q₂ 0 = q₁ 0 + u := by dsimp [u]; ring
    have hq21 : q₂ 1 = q₁ 1 + v := by dsimp [v]; ring
    rw [hq30, hq31] at hc13
    rw [hq20, hq21] at hc12
    linear_combination hc13 - t * hc12
  have hmul_ne : t * (t - 1) * (u ^ 2 + v ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero ht_ne0 (sub_ne_zero.mpr ht_ne1)) (ne_of_gt hsum_pos)
  exact hmul_ne hquad

/-- Helper: On the right semicircle `x ≥ p₀ 0` of radius `r > 0` centered at `p₀`, distances from
a point `q₀` strictly increase with the second coordinate `y` for `q₀ 1 ≤ q₁ 1 < q₂ 1`. -/
private lemma semicircle_dist_strictMono
    (p₀ q₀ q₁ q₂ : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (hr : 0 < r)
    (h0 : dist p₀ q₀ = r) (h1 : dist p₀ q₁ = r) (h2 : dist p₀ q₂ = r)
    (hx0 : p₀ 0 ≤ q₀ 0) (hx1 : p₀ 0 ≤ q₁ 0) (hx2 : p₀ 0 ≤ q₂ 0)
    (hy01 : q₀ 1 ≤ q₁ 1) (hy12 : q₁ 1 < q₂ 1) :
    dist q₀ q₁ < dist q₀ q₂ := by
  have hs0 : (q₀ 0 - p₀ 0) ^ 2 + (q₀ 1 - p₀ 1) ^ 2 = r ^ 2 := by
    have := dist_sq_eq_euc2 q₀ p₀; rw [dist_comm, h0] at this; linarith
  have hs1 : (q₁ 0 - p₀ 0) ^ 2 + (q₁ 1 - p₀ 1) ^ 2 = r ^ 2 := by
    have := dist_sq_eq_euc2 q₁ p₀; rw [dist_comm, h1] at this; linarith
  have hs2 : (q₂ 0 - p₀ 0) ^ 2 + (q₂ 1 - p₀ 1) ^ 2 = r ^ 2 := by
    have := dist_sq_eq_euc2 q₂ p₀; rw [dist_comm, h2] at this; linarith
  set x₀ := q₀ 0 - p₀ 0
  set y₀ := q₀ 1 - p₀ 1
  set x₁ := q₁ 0 - p₀ 0
  set y₁ := q₁ 1 - p₀ 1
  set x₂ := q₂ 0 - p₀ 0
  set y₂ := q₂ 1 - p₀ 1
  have hdx0 : 0 ≤ x₀ := sub_nonneg.mpr hx0
  have hdx1 : 0 ≤ x₁ := sub_nonneg.mpr hx1
  have hdx2 : 0 ≤ x₂ := sub_nonneg.mpr hx2
  have hdy01 : y₀ ≤ y₁ := by dsimp [y₀, y₁]; linarith
  have hdy12 : y₁ < y₂ := by dsimp [y₁, y₂]; linarith
  have hd1 : dist q₀ q₁ ^ 2 = 2 * r ^ 2 - 2 * (x₀ * x₁ + y₀ * y₁) := by
    rw [dist_sq_eq_euc2]; dsimp [x₀, y₀, x₁, y₁]; linarith
  have hd2 : dist q₀ q₂ ^ 2 = 2 * r ^ 2 - 2 * (x₀ * x₂ + y₀ * y₂) := by
    rw [dist_sq_eq_euc2]; dsimp [x₀, y₀, x₂, y₂]; linarith
  suffices hdot : x₀ * x₂ + y₀ * y₂ < x₀ * x₁ + y₀ * y₁ by
    have hsq : dist q₀ q₁ ^ 2 < dist q₀ q₂ ^ 2 := by linarith
    nlinarith [dist_nonneg (x := q₀) (y := q₁), dist_nonneg (x := q₀) (y := q₂)]
  rcases eq_or_lt_of_le hdy01 with hy_eq | hy01_lt
  · have hx_eq : x₀ = x₁ := by
      have hsq : x₀ ^ 2 = x₁ ^ 2 := by rw [hy_eq] at hs0; linarith
      nlinarith
    have hneq : 0 < (x₀ - x₂) ^ 2 + (y₀ - y₂) ^ 2 := by
      have hyne : y₀ - y₂ ≠ 0 := by linarith
      nlinarith [sq_pos_of_ne_zero hyne, sq_nonneg (x₀ - x₂)]
    rw [← hx_eq, ← hy_eq]; linarith
  · have hy0_ge : -r ≤ y₀ := by nlinarith [sq_nonneg x₀]
    have hy2_le : y₂ ≤ r := by nlinarith [sq_nonneg x₂]
    have hy1_sq_lt : y₁ ^ 2 < r ^ 2 := by nlinarith
    have hx1_pos : 0 < x₁ := by nlinarith
    have hx12_pos : 0 < x₁ + x₂ := by linarith
    have hc01 : 0 < x₀ * y₁ - y₀ * x₁ := by
      by_cases hya : y₀ ≤ 0
      · by_cases hyb : 0 ≤ y₁
        · rcases eq_or_lt_of_le hya with hya0 | hya_neg
          · have hx0_pos : 0 < x₀ := by rw [hya0] at hs0; nlinarith
            have hy1_pos : 0 < y₁ := by linarith
            rw [hya0]; nlinarith [mul_pos hx0_pos hy1_pos]
          · have h1 : 0 ≤ x₀ * y₁ := mul_nonneg hdx0 hyb
            have h2 : 0 < (-y₀) * x₁ := mul_pos (by linarith) hx1_pos
            linarith
        · push Not at hyb
          have hsq : x₀ ^ 2 < x₁ ^ 2 := by nlinarith
          have hxlt : x₀ < x₁ := by nlinarith
          have h1 : 0 < (-y₁) * (x₁ - x₀) := mul_pos (by linarith) (by linarith)
          have h2 : 0 < (y₁ - y₀) * x₁ := mul_pos (by linarith) hx1_pos
          nlinarith
      · push Not at hya
        have hsq : x₁ ^ 2 < x₀ ^ 2 := by nlinarith
        have hxlt : x₁ < x₀ := by nlinarith
        have h1 : 0 < y₀ * (x₀ - x₁) := mul_pos hya (by linarith)
        have h2 : 0 ≤ x₀ * (y₁ - y₀) := mul_nonneg hdx0 (by linarith)
        linarith
    have hc02 : 0 ≤ x₀ * y₂ - y₀ * x₂ := by
      by_cases hya : y₀ ≤ 0
      · by_cases hyb : 0 ≤ y₂
        · exact add_nonneg (mul_nonneg hdx0 hyb) (by nlinarith)
        · push Not at hyb
          have hsq : x₀ ^ 2 < x₂ ^ 2 := by nlinarith
          have hxlt : x₀ < x₂ := by nlinarith
          have h1 : 0 ≤ (-y₂) * (x₂ - x₀) := mul_nonneg (by linarith) (by linarith)
          have h2 : 0 ≤ (y₂ - y₀) * x₂ := mul_nonneg (by linarith) hdx2
          linarith
      · push Not at hya
        have hsq : x₂ ^ 2 < x₀ ^ 2 := by nlinarith
        have hxlt : x₂ < x₀ := by nlinarith
        have h1 : 0 ≤ y₀ * (x₀ - x₂) := mul_nonneg (by linarith) (by linarith)
        have h2 : 0 ≤ x₀ * (y₂ - y₀) := mul_nonneg hdx0 (by linarith)
        linarith
    have hid : (x₁ + x₂) * ((x₀ * x₁ + y₀ * y₁) - (x₀ * x₂ + y₀ * y₂)) =
        (y₂ - y₁) * ((x₀ * y₁ - y₀ * x₁) + (x₀ * y₂ - y₀ * x₂)) := by
      linear_combination x₀ * (hs1 - hs2)
    have hprod : 0 < (x₁ + x₂) * ((x₀ * x₁ + y₀ * y₁) - (x₀ * x₂ + y₀ * y₂)) := by
      rw [hid]; exact mul_pos (by linarith) (by linarith)
    nlinarith

/-- **Erdős (1946) Exact `√n` Distinct Distances Lower Bound (Quadratic Form)**:
Every finite set `P ⊂ ℝ²` with `|P| ≥ 2` determines `k` distinct positive distances satisfying
`k * (k + 1) ≥ |P| - 1` (equivalently `k ≥ √(|P| - 3/4) - 1/2`).
Pure Mathlib signature (`0` custom definitions). -/
theorem ppl071_erdos_1946_sqrt_lower
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (hP : 2 ≤ P.card) :
    let D := ((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)
    P.card - 1 ≤ D.card * (D.card + 1) := by
  intro D
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p₀, hp₀, hp₀_min⟩ := Finset.exists_min_image P (fun p => p 0) hPne
  set P' := P.erase p₀
  have hP'_card : P'.card = P.card - 1 := Finset.card_erase_of_mem hp₀
  set R := P'.image (fun q => dist p₀ q)
  have hR_sub : R ⊆ D := by
    intro r hr
    simp only [R, Finset.mem_image, P', Finset.mem_erase] at hr
    obtain ⟨q, ⟨hqp, hqP⟩, rfl⟩ := hr
    simp only [D, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
    exact ⟨(p₀, q), ⟨⟨hp₀, hqP⟩, hqp.symm⟩, rfl⟩
  have hR_card_le : R.card ≤ D.card := Finset.card_le_card hR_sub
  have hsum : ∑ r ∈ R, (P'.filter (fun q => dist p₀ q = r)).card = P'.card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext q
      simp only [Finset.mem_biUnion, Finset.mem_filter, R, Finset.mem_image]
      constructor
      · rintro ⟨_, _, hq, _⟩; exact hq
      · intro hq; exact ⟨dist p₀ q, ⟨q, hq, rfl⟩, hq, rfl⟩
    · intro r₁ _ r₂ _ hne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro q h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  have hfiber : ∀ r ∈ R, (P'.filter (fun q => dist p₀ q = r)).card ≤ D.card + 1 := by
    intro r hr
    set F := P'.filter (fun q => dist p₀ q = r)
    by_cases hFne : F.Nonempty
    · have hr_pos : 0 < r := by
        obtain ⟨q, hq⟩ := hFne
        simp only [F, P', Finset.mem_filter, Finset.mem_erase] at hq
        rw [← hq.2]; exact dist_pos.mpr hq.1.1.symm
      obtain ⟨q₀, hq₀, hq₀_min⟩ := Finset.exists_min_image F (fun q => q 1) hFne
      have hq₀P : q₀ ∈ P := by
        simp only [F, P', Finset.mem_filter, Finset.mem_erase] at hq₀; exact hq₀.1.2
      have hinj : Set.InjOn (fun q => dist q₀ q) (F.erase q₀ : Set (EuclideanSpace ℝ (Fin 2))) := by
        intro q₁ hq₁ q₂ hq₂ heq
        simp only [Finset.mem_coe, Finset.mem_erase, F, P', Finset.mem_filter] at hq₁ hq₂ hq₀
        have hsame_y : ∀ a b : EuclideanSpace ℝ (Fin 2),
            a ∈ P → b ∈ P → dist p₀ a = r → dist p₀ b = r → a 1 = b 1 → a = b := by
          intro a b haP hbP hda hdb hy
          have hsa := dist_sq_eq_euc2 a p₀
          have hsb := dist_sq_eq_euc2 b p₀
          rw [dist_comm, hda] at hsa
          rw [dist_comm, hdb] at hsb
          have hxa : 0 ≤ a 0 - p₀ 0 := sub_nonneg.mpr (hp₀_min a haP)
          have hxb : 0 ≤ b 0 - p₀ 0 := sub_nonneg.mpr (hp₀_min b hbP)
          have hxsq : (a 0 - p₀ 0) ^ 2 = (b 0 - p₀ 0) ^ 2 := by rw [hy] at hsa; linarith
          exact euc2_ext (by nlinarith) hy
        rcases lt_trichotomy (q₁ 1) (q₂ 1) with hlt | hy | hgt
        · exfalso
          have hlt' := semicircle_dist_strictMono p₀ q₀ q₁ q₂ r hr_pos
            hq₀.2 hq₁.2.2 hq₂.2.2
            (hp₀_min q₀ hq₀P) (hp₀_min q₁ hq₁.2.1.2) (hp₀_min q₂ hq₂.2.1.2)
            (hq₀_min q₁ (by simp [F, P', hq₁.2.1.1, hq₁.2.1.2, hq₁.2.2])) hlt
          linarith
        · exact hsame_y q₁ q₂ hq₁.2.1.2 hq₂.2.1.2 hq₁.2.2 hq₂.2.2 hy
        · exfalso
          have hlt' := semicircle_dist_strictMono p₀ q₀ q₂ q₁ r hr_pos
            hq₀.2 hq₂.2.2 hq₁.2.2
            (hp₀_min q₀ hq₀P) (hp₀_min q₂ hq₂.2.1.2) (hp₀_min q₁ hq₁.2.1.2)
            (hq₀_min q₂ (by simp [F, P', hq₂.2.1.1, hq₂.2.1.2, hq₂.2.2])) hgt
          linarith
      have hsubD : (F.erase q₀).image (fun q => dist q₀ q) ⊆ D := by
        intro d hd
        simp only [Finset.mem_image, Finset.mem_erase, F, P', Finset.mem_filter] at hd
        obtain ⟨q, ⟨hqq₀, ⟨_, hqP⟩, _⟩, rfl⟩ := hd
        simp only [D, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
        exact ⟨(q₀, q), ⟨⟨hq₀P, hqP⟩, hqq₀.symm⟩, rfl⟩
      have hcard_er : (F.erase q₀).card ≤ D.card := by
        rw [← Finset.card_image_of_injOn hinj]
        exact Finset.card_le_card hsubD
      rw [Finset.card_erase_of_mem hq₀] at hcard_er
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hFne]; simp
  calc P.card - 1 = P'.card := hP'_card.symm
    _ = ∑ r ∈ R, (P'.filter (fun q => dist p₀ q = r)).card := hsum.symm
    _ ≤ ∑ _r ∈ R, (D.card + 1) := Finset.sum_le_sum hfiber
    _ = R.card * (D.card + 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ D.card * (D.card + 1) := Nat.mul_le_mul_right _ hR_card_le

/-- **Erdős (1946) Explicit `√n` Corollary**:
For every finite set `P ⊂ ℝ²` with `|P| ≥ 2`, the number of distinct positive distances is at
least `Real.sqrt (P.card - 3/4) - 1/2`. Pure Mathlib signature. -/
theorem ppl071_erdos_1946_sqrt_lower_real
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (hP : 2 ≤ P.card) :
    Real.sqrt ((P.card : ℝ) - 3 / 4) - 1 / 2 ≤
      ((((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)).card : ℝ) := by
  have hnat := ppl071_erdos_1946_sqrt_lower P hP
  set k := (((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)).card
  have hreal : (P.card : ℝ) - 1 ≤ (k : ℝ) * ((k : ℝ) + 1) := by
    have h1 : ((P.card - 1 : ℕ) : ℝ) ≤ ((k * (k + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    rw [Nat.cast_sub (by omega : 1 ≤ P.card)] at h1
    push_cast at h1 ⊢
    linarith
  have hsq : (P.card : ℝ) - 3 / 4 ≤ ((k : ℝ) + 1 / 2) ^ 2 := by nlinarith
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (by positivity)] at hsqrt
  linarith

/-! ### Section 2: Erdős (1946) `√n × √n` Integer-Grid `O(n / √(log n))` Upper Bound -/

/-- **Fermat–Euler `p ≡ 3 (mod 4)` Obstruction to Sums of Two Squares**:
If `p` is prime with `p % 4 = 3` and `n = x² + y² > 0`, then `p` divides `n` to an even power. -/
theorem ppl071_prime_mod4_eq3_sum_two_sq_even_val
    (p n x y : ℕ) (hp : p.Prime) (hp3 : p % 4 = 3) (hn : 0 < n) (hxy : n = x ^ 2 + y ^ 2) :
    Even (n.factorization p) := by
  induction n using Nat.strong_induction_on generalizing x y with
  | h n ih =>
    by_cases hdiv : p ∣ n
    · have : Fact p.Prime := ⟨hp⟩
      have hnot_sq : ¬ IsSquare (-1 : ZMod p) := by
        rw [ZMod.exists_sq_eq_neg_one_iff]
        omega
      have hpx : p ∣ x := by
        by_contra hnx
        have hx0 : (x : ZMod p) ≠ 0 := by
          intro hz; exact hnx ((ZMod.natCast_eq_zero_iff x p).mp hz)
        have hsum0 : (x : ZMod p) ^ 2 + (y : ZMod p) ^ 2 = 0 := by
          have : ((x ^ 2 + y ^ 2 : ℕ) : ZMod p) = 0 := by
            rw [← hxy]; exact (ZMod.natCast_eq_zero_iff n p).mpr hdiv
          push_cast at this; exact this
        have hsq : ((y : ZMod p) * (x : ZMod p)⁻¹) ^ 2 = -1 := by
          rw [mul_pow, inv_pow]
          have hx2 : (x : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 hx0
          have hy2 : (y : ZMod p) ^ 2 = -((x : ZMod p) ^ 2) := eq_neg_of_add_eq_zero_right hsum0
          rw [hy2, neg_mul, mul_inv_cancel₀ hx2]
        exact hnot_sq ⟨(y : ZMod p) * (x : ZMod p)⁻¹, by rw [← sq]; exact hsq.symm⟩
      have hpy : p ∣ y := by
        obtain ⟨x', rfl⟩ := hpx
        have hpy2 : p ∣ y ^ 2 := by
          have h1 : p ∣ (p * x') ^ 2 + y ^ 2 := hxy ▸ hdiv
          have h2 : p ∣ (p * x') ^ 2 := by
            rw [mul_pow]; exact dvd_mul_of_dvd_left (dvd_pow_self p (by norm_num)) _
          exact (Nat.dvd_add_right h2).mp h1
        exact hp.dvd_of_dvd_pow hpy2
      obtain ⟨x', rfl⟩ := hpx
      obtain ⟨y', rfl⟩ := hpy
      set m := x' ^ 2 + y' ^ 2
      have hnm : n = p ^ 2 * m := by rw [hxy]; dsimp [m]; ring
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · rw [hm0, mul_zero] at hnm; omega
        · exact hmpos
      have hm_lt : m < n := by
        have hp2 : 2 ≤ p := hp.two_le
        have : 1 < p ^ 2 := by nlinarith
        rw [hnm]; exact lt_mul_of_one_lt_left hm_pos this
      have hih := ih m hm_lt x' y' hm_pos rfl
      rw [hnm, Nat.factorization_mul (pow_ne_zero 2 hp.ne_zero) (ne_of_gt hm_pos)]
      simp only [Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same]
      exact (even_two).add hih
    · have h0 : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hdiv
      rw [h0]; exact Even.zero

/-- Indicator predicate `A'(n)`: `1 ≤ n` and every prime `p ≡ 3 (mod 4)` has even exponent in `n`. -/
private def isTwoSqCand (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (n.factorization p)

private lemma isTwoSqCand_of_sq_add_sq {n x y : ℕ} (hn : 1 ≤ n) (hxy : n = x ^ 2 + y ^ 2) :
    isTwoSqCand n :=
  ⟨hn, fun p hp hp3 => ppl071_prime_mod4_eq3_sum_two_sq_even_val p n x y hp hp3 (by omega) hxy⟩

private lemma isTwoSqCand_mul_iff {a b : ℕ} (hcop : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    isTwoSqCand (a * b) ↔ isTwoSqCand a ∧ isTwoSqCand b := by
  constructor
  · intro hab
    refine ⟨⟨ha, fun p hp hp3 => ?_⟩, ⟨hb, fun p hp hp3 => ?_⟩⟩
    · have h := hab.2 p hp hp3
      rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply] at h
      by_cases hpa : p ∣ a
      · have hnpb : ¬ p ∣ b := fun hpb => hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hpa hpb)
        rw [Nat.factorization_eq_zero_of_not_dvd hnpb, add_zero] at h; exact h
      · rw [Nat.factorization_eq_zero_of_not_dvd hpa]; exact Even.zero
    · have h := hab.2 p hp hp3
      rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply] at h
      by_cases hpb : p ∣ b
      · have hnpa : ¬ p ∣ a := fun hpa => hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hpa hpb)
        rw [Nat.factorization_eq_zero_of_not_dvd hnpa, zero_add] at h; exact h
      · rw [Nat.factorization_eq_zero_of_not_dvd hpb]; exact Even.zero
  · rintro ⟨ha', hb'⟩
    refine ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), fun p hp hp3 => ?_⟩
    rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply]
    exact (ha'.2 p hp hp3).add (hb'.2 p hp hp3)

/-- Primitive Dirichlet character mod 4: `χ₄(n) = 1` if `n ≡ 1 (4)`, `-1` if `n ≡ 3 (4)`, else `0`. -/
private def chi4 (n : ℕ) : ℤ :=
  if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

private lemma chi4_mul (a b : ℕ) : chi4 (a * b) = chi4 a * chi4 b := by
  unfold chi4
  have h : (a * b) % 4 = ((a % 4) * (b % 4)) % 4 := Nat.mul_mod a b 4
  have ha : a % 4 < 4 := Nat.mod_lt a (by norm_num)
  have hb : b % 4 < 4 := Nat.mod_lt b (by norm_num)
  rw [h]
  interval_cases (a % 4) <;> interval_cases (b % 4) <;> norm_num

private lemma chi4_one : chi4 1 = 1 := by unfold chi4; norm_num

/-- Alternating partial sum bound: `0 ≤ ∑_{k=1}^X χ₄(k) / k ≤ 1` for all `X : ℕ`. -/
private lemma sum_chi4_div_bounds (X : ℕ) :
    0 ≤ ∑ k ∈ Finset.Icc 1 X, (chi4 k : ℝ) / (k : ℝ) ∧
    ∑ k ∈ Finset.Icc 1 X, (chi4 k : ℝ) / (k : ℝ) ≤ 1 := by
  have hmain : ∀ m : ℕ,
      0 ≤ ∑ k ∈ Finset.Icc 1 (4 * m), (chi4 k : ℝ) / (k : ℝ) ∧
      ∑ k ∈ Finset.Icc 1 (4 * m), (chi4 k : ℝ) / (k : ℝ) + 1 / (4 * (m : ℝ) + 1) ≤ 1 := by
    intro m
    induction m with
    | zero => simp
    | succ j ih =>
      have hsplit : Finset.Icc 1 (4 * (j + 1)) =
          Finset.Icc 1 (4 * j) ∪ {4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        omega
      have hdisj : Disjoint (Finset.Icc 1 (4 * j)) {4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
        omega
      rw [hsplit, Finset.sum_union hdisj]
      have hblock : ∑ k ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ),
          (chi4 k : ℝ) / (k : ℝ) =
          1 / (4 * (j : ℝ) + 1) - 1 / (4 * (j : ℝ) + 3) := by
        rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
          Finset.sum_insert (by simp), Finset.sum_singleton]
        have hc1 : chi4 (4 * j + 1) = 1 := by unfold chi4; simp
        have hc2 : chi4 (4 * j + 2) = 0 := by unfold chi4; simp
        have hc3 : chi4 (4 * j + 3) = -1 := by unfold chi4; simp
        have hc4 : chi4 (4 * j + 4) = 0 := by unfold chi4; simp
        rw [hc1, hc2, hc3, hc4]; push_cast; ring
      rw [hblock]
      have hpos1 : (0 : ℝ) < 4 * (j : ℝ) + 1 := by positivity
      have hpos3 : (0 : ℝ) < 4 * (j : ℝ) + 3 := by positivity
      have h13 : 1 / (4 * (j : ℝ) + 3) ≤ 1 / (4 * (j : ℝ) + 1) :=
        one_div_le_one_div_of_le hpos1 (by linarith)
      have h35 : 1 / (4 * ((j + 1 : ℕ) : ℝ) + 1) ≤ 1 / (4 * (j : ℝ) + 3) := by
        apply one_div_le_one_div_of_le hpos3; push_cast; linarith
      constructor <;> linarith [ih.1, ih.2]
  set m := X / 4
  set r := X % 4
  have hX : X = 4 * m + r := (Nat.div_add_mod X 4).symm
  have hr : r < 4 := Nat.mod_lt X (by norm_num)
  have hm := hmain m
  rw [hX]
  interval_cases r
  · simp only [add_zero]
    have hpos : (0 : ℝ) ≤ 1 / (4 * (m : ℝ) + 1) := by positivity
    exact ⟨hm.1, by linarith [hm.2]⟩
  · have hins : Finset.Icc 1 (4 * m + 1) = insert (4 * m + 1) (Finset.Icc 1 (4 * m)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert (by simp)]
    have hc : chi4 (4 * m + 1) = 1 := by unfold chi4; simp
    rw [hc]; push_cast
    have hpos : (0 : ℝ) ≤ 1 / (4 * (m : ℝ) + 1) := by positivity
    constructor <;> linarith [hm.1, hm.2]
  · have hsp : Finset.Icc 1 (4 * m + 2) =
        insert (4 * m + 2) (insert (4 * m + 1) (Finset.Icc 1 (4 * m))) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsp, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    have hc1 : chi4 (4 * m + 1) = 1 := by unfold chi4; simp
    have hc2 : chi4 (4 * m + 2) = 0 := by unfold chi4; simp
    rw [hc1, hc2]; push_cast; simp only [zero_div, zero_add]
    have hpos : (0 : ℝ) ≤ 1 / (4 * (m : ℝ) + 1) := by positivity
    constructor <;> linarith [hm.1, hm.2]
  · have hsp : Finset.Icc 1 (4 * m + 3) =
        insert (4 * m + 3) (insert (4 * m + 2) (insert (4 * m + 1) (Finset.Icc 1 (4 * m)))) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsp, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp)]
    have hc1 : chi4 (4 * m + 1) = 1 := by unfold chi4; simp
    have hc2 : chi4 (4 * m + 2) = 0 := by unfold chi4; simp
    have hc3 : chi4 (4 * m + 3) = -1 := by unfold chi4; simp
    rw [hc1, hc2, hc3]; push_cast; simp only [zero_div, zero_add, neg_div]
    have hpos1 : (0 : ℝ) < 4 * (m : ℝ) + 1 := by positivity
    have h13 : 1 / (4 * (m : ℝ) + 3) ≤ 1 / (4 * (m : ℝ) + 1) :=
      one_div_le_one_div_of_le hpos1 (by linarith)
    have hpos3 : (0 : ℝ) ≤ 1 / (4 * (m : ℝ) + 3) := by positivity
    constructor <;> linarith [hm.1, hm.2]

/-- Divisor sum `f(n) = ∑_{d ∣ n} χ₄(d)`. -/
private def fChi4 (n : ℕ) : ℤ := ∑ d ∈ n.divisors, chi4 d

/-- Auxiliary indicator `g(n)`: `1` iff `n ≥ 1`, no prime `p ≡ 1 (4)` divides `n`, and every
prime `p ≡ 3 (4)` divides `n` to an even power. -/
private def isGSupp (n : ℕ) : Prop :=
  1 ≤ n ∧ (∀ p : ℕ, p.Prime → p % 4 = 1 → n.factorization p = 0) ∧
    (∀ p : ℕ, p.Prime → p % 4 = 3 → Even (n.factorization p))

private noncomputable def indA (n : ℕ) : ℤ := if isTwoSqCand n then 1 else 0
private noncomputable def indG (n : ℕ) : ℤ := if isGSupp n then 1 else 0

/-- Dirichlet convolution on `ℕ → ℤ`. -/
private def dconv (u v : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, u d * v (n / d)

/-- Multiplicativity of Dirichlet convolution for multiplicative `ℕ → ℤ` functions. -/
private lemma dconv_mul_coprime (u v : ℕ → ℤ)
    (hu : ∀ a b, Nat.Coprime a b → 1 ≤ a → 1 ≤ b → u (a * b) = u a * u b)
    (hv : ∀ a b, Nat.Coprime a b → 1 ≤ a → 1 ≤ b → v (a * b) = v a * v b)
    {a b : ℕ} (hcop : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    dconv u v (a * b) = dconv u v a * dconv u v b := by
  unfold dconv
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  refine (Finset.sum_nbij (fun p : ℕ × ℕ => p.1 * p.2) ?_ ?_ ?_ ?_).symm
  · intro p hp
    simp only [Finset.mem_product, Nat.mem_divisors] at hp ⊢
    exact ⟨mul_dvd_mul hp.1.1 hp.2.1, by positivity⟩
  · intro p1 hp1 p2 hp2 heq
    simp only [Finset.mem_coe, Finset.mem_product, Nat.mem_divisors] at hp1 hp2
    have heq' : p1.1 * p1.2 = p2.1 * p2.2 := heq
    have hcop12 : Nat.Coprime p1.1 p2.2 := hcop.coprime_dvd_left hp1.1.1 |>.coprime_dvd_right hp2.2.1
    have hcop21 : Nat.Coprime p2.1 p1.2 := hcop.coprime_dvd_left hp2.1.1 |>.coprime_dvd_right hp1.2.1
    have hd1 : p1.1 ∣ p2.1 := hcop12.dvd_of_dvd_mul_right (heq' ▸ dvd_mul_right p1.1 p1.2)
    have hd2 : p2.1 ∣ p1.1 := hcop21.dvd_of_dvd_mul_right (heq'.symm ▸ dvd_mul_right p2.1 p2.2)
    have h1 : p1.1 = p2.1 := Nat.dvd_antisymm hd1 hd2
    have hpos : 0 < p1.1 := Nat.pos_of_dvd_of_pos hp1.1.1 (by omega)
    have h2 : p1.2 = p2.2 := Nat.eq_of_mul_eq_mul_left hpos (by rw [← h1] at heq'; exact heq')
    exact Prod.ext h1 h2
  · intro d hd
    simp only [Finset.mem_coe, Nat.mem_divisors] at hd
    refine ⟨(Nat.gcd d a, Nat.gcd d b), ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_product, Nat.mem_divisors]
      exact ⟨⟨Nat.gcd_dvd_right d a, by omega⟩, ⟨Nat.gcd_dvd_right d b, by omega⟩⟩
    · change Nat.gcd d a * Nat.gcd d b = d
      rw [← Nat.Coprime.gcd_mul d hcop, Nat.gcd_eq_left hd.1]
  · intro p hp
    simp only [Finset.mem_product, Nat.mem_divisors] at hp
    have hpa : 1 ≤ p.1 := Nat.pos_of_dvd_of_pos hp.1.1 (by omega)
    have hpb : 1 ≤ p.2 := Nat.pos_of_dvd_of_pos hp.2.1 (by omega)
    have hqa : 1 ≤ a / p.1 := Nat.div_pos (Nat.le_of_dvd (by omega) hp.1.1) (by omega)
    have hqb : 1 ≤ b / p.2 := Nat.div_pos (Nat.le_of_dvd (by omega) hp.2.1) (by omega)
    have hcop_p : Nat.Coprime p.1 p.2 := hcop.coprime_dvd_left hp.1.1 |>.coprime_dvd_right hp.2.1
    have hcop_q : Nat.Coprime (a / p.1) (b / p.2) :=
      hcop.coprime_dvd_left (Nat.div_dvd_of_dvd hp.1.1) |>.coprime_dvd_right (Nat.div_dvd_of_dvd hp.2.1)
    have hdiv : a * b / (p.1 * p.2) = (a / p.1) * (b / p.2) := by
      obtain ⟨qa, rfl⟩ := hp.1.1
      obtain ⟨qb, rfl⟩ := hp.2.1
      have h1 : p.1 * qa * (p.2 * qb) = (p.1 * p.2) * (qa * qb) := by ring
      rw [h1, Nat.mul_div_cancel_left _ (by positivity),
        Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)]
    rw [hdiv, hu p.1 p.2 hcop_p hpa hpb, hv (a / p.1) (b / p.2) hcop_q hqa hqb]
    ring

/-- Multiplicativity of `indA`. -/
private lemma indA_mul_coprime (a b : ℕ) (hcop : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    indA (a * b) = indA a * indA b := by
  unfold indA
  simp only [isTwoSqCand_mul_iff hcop ha hb]
  by_cases h1 : isTwoSqCand a <;> by_cases h2 : isTwoSqCand b <;> simp [h1, h2]

/-- Multiplicativity of `indG`. -/
private lemma indG_mul_coprime (a b : ℕ) (hcop : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    indG (a * b) = indG a * indG b := by
  have hiff : isGSupp (a * b) ↔ isGSupp a ∧ isGSupp b := by
    constructor
    · intro hab
      refine ⟨⟨ha, fun p hp hp1 => ?_, fun p hp hp3 => ?_⟩,
        ⟨hb, fun p hp hp1 => ?_, fun p hp hp3 => ?_⟩⟩
      · have h := hab.2.1 p hp hp1
        rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply] at h; omega
      · have h := hab.2.2 p hp hp3
        rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply] at h
        by_cases hpa : p ∣ a
        · have hnpb : ¬ p ∣ b := fun hpb => hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hpa hpb)
          rw [Nat.factorization_eq_zero_of_not_dvd hnpb, add_zero] at h; exact h
        · rw [Nat.factorization_eq_zero_of_not_dvd hpa]; exact Even.zero
      · have h := hab.2.1 p hp hp1
        rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply] at h; omega
      · have h := hab.2.2 p hp hp3
        rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply] at h
        by_cases hpb : p ∣ b
        · have hnpa : ¬ p ∣ a := fun hpa => hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hpa hpb)
          rw [Nat.factorization_eq_zero_of_not_dvd hnpa, zero_add] at h; exact h
        · rw [Nat.factorization_eq_zero_of_not_dvd hpb]; exact Even.zero
    · rintro ⟨ha', hb'⟩
      refine ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), fun p hp hp1 => ?_, fun p hp hp3 => ?_⟩
      · rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
          ha'.2.1 p hp hp1, hb'.2.1 p hp hp1]
      · rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply]
        exact (ha'.2.2 p hp hp3).add (hb'.2.2 p hp hp3)
  unfold indG; simp only [hiff]
  by_cases h1 : isGSupp a <;> by_cases h2 : isGSupp b <;> simp [h1, h2]

/-- Multiplicativity of `fChi4 = 1 * χ₄`. -/
private lemma fChi4_mul_coprime (a b : ℕ) (hcop : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    fChi4 (a * b) = fChi4 a * fChi4 b := by
  have heq : ∀ n, fChi4 n = dconv chi4 (fun _ => 1) n := by
    intro n; unfold fChi4 dconv; simp
  rw [heq, heq, heq]
  exact dconv_mul_coprime chi4 (fun _ => 1)
    (fun x y _ _ _ => chi4_mul x y) (fun _ _ _ _ _ => by simp) hcop ha hb

/-- Exact arithmetic identity: `(1_{A'} * 1_{A'})(n) = (g * f)(n)` for all `n ≥ 1`! -/
private lemma dconv_indA_eq_dconv_indG_fChi4 (n : ℕ) (hn : 1 ≤ n) :
    dconv indA indA n = dconv indG fChi4 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n = 1
    · subst hn1; unfold dconv indA indG fChi4; simp [isTwoSqCand, isGSupp, chi4_one]
    · set p := n.minFac
      have hp : p.Prime := Nat.minFac_prime hn1
      have hpdvd : p ∣ n := Nat.minFac_dvd n
      set e := n.factorization p
      have he_pos : 1 ≤ e := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpdvd
      have hpe_dvd : p ^ e ∣ n := Nat.ordProj_dvd n p
      set m := n / p ^ e
      have hnm : p ^ e * m = n := Nat.mul_div_cancel' hpe_dvd
      have hcop : Nat.Coprime (p ^ e) m := by
        refine Nat.Coprime.pow_left e (hp.coprime_iff_not_dvd.mpr ?_)
        intro hpm
        have hpe1 : p ^ (e + 1) ∣ n := by
          rw [pow_succ, ← hnm]; exact Nat.mul_dvd_mul_left (p ^ e) hpm
        have hle := (hp.pow_dvd_iff_le_factorization (by omega)).mp hpe1
        omega
      have hpe_ge : 1 ≤ p ^ e := Nat.one_le_pow e p hp.pos
      have hm_ge : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · rw [hm0, mul_zero] at hnm; omega
        · exact hmpos
      have hm_lt : m < n := by
        have : 1 < p ^ e := one_lt_pow₀ hp.one_lt (by omega)
        rw [← hnm]; exact lt_mul_of_one_lt_left hm_ge this
      rw [← hnm,
        dconv_mul_coprime indA indA indA_mul_coprime indA_mul_coprime hcop hpe_ge hm_ge,
        dconv_mul_coprime indG fChi4 indG_mul_coprime fChi4_mul_coprime hcop hpe_ge hm_ge,
        ih m hm_lt hm_ge]
      congr 1
      unfold dconv
      rw [Nat.divisors_prime_pow hp, Finset.sum_map, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk]
      have hdiv_pow : ∀ j ∈ Finset.range (e + 1), p ^ e / p ^ j = p ^ (e - j) := by
        intro j hj
        have hje : j ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact Nat.pow_div hje hp.pos
      have hp_indA : ∀ k : ℕ, indA (p ^ k) =
          if p % 4 = 3 then (if Even k then 1 else 0) else 1 := by
        intro k
        unfold indA
        have hk1 : 1 ≤ p ^ k := Nat.one_le_pow k p hp.pos
        by_cases hp3 : p % 4 = 3
        · simp only [hp3, ↓reduceIte]
          by_cases hk : Even k
          · simp only [hk, ↓reduceIte]
            exact if_pos ⟨hk1, fun q _ hq3 => by
              rw [hp.factorization_pow]
              by_cases hqp : q = p
              · subst hqp; simp [hk]
              · rw [Finsupp.single_eq_of_ne hqp]; exact Even.zero⟩
          · simp only [hk, ↓reduceIte]
            exact if_neg fun hc => by
              have := hc.2 p hp hp3
              rw [hp.factorization_pow, Finsupp.single_eq_same] at this
              exact hk this
        · simp only [hp3, ↓reduceIte]
          exact if_pos ⟨hk1, fun q _ hq3 => by
            rw [hp.factorization_pow]
            have hqp : q ≠ p := fun h => hp3 (h ▸ hq3)
            rw [Finsupp.single_eq_of_ne hqp]; exact Even.zero⟩
      have hp_indG : ∀ k : ℕ, indG (p ^ k) =
          if p % 4 = 1 then (if k = 0 then 1 else 0)
          else if p % 4 = 3 then (if Even k then 1 else 0) else 1 := by
        intro k
        unfold indG
        have hk1 : 1 ≤ p ^ k := Nat.one_le_pow k p hp.pos
        by_cases hp1 : p % 4 = 1
        · simp only [hp1, ↓reduceIte]
          by_cases hk0 : k = 0
          · subst hk0; simp only [↓reduceIte, pow_zero]
            exact if_pos ⟨le_rfl, fun _ _ _ => by simp, fun _ _ _ => by simp⟩
          · simp only [hk0, ↓reduceIte]
            exact if_neg fun hc => by
              have := hc.2.1 p hp hp1
              rw [hp.factorization_pow, Finsupp.single_eq_same] at this
              exact hk0 this
        · simp only [hp1, ↓reduceIte]
          by_cases hp3 : p % 4 = 3
          · simp only [hp3, ↓reduceIte]
            by_cases hk : Even k
            · simp only [hk, ↓reduceIte]
              exact if_pos ⟨hk1,
                fun q _ hq1 => by
                  rw [hp.factorization_pow]
                  have hne : q ≠ p := fun h => hp1 (h ▸ hq1)
                  exact Finsupp.single_eq_of_ne hne,
                fun q _ hq3 => by
                  rw [hp.factorization_pow]
                  by_cases hqp : q = p
                  · subst hqp; simp [hk]
                  · rw [Finsupp.single_eq_of_ne hqp]; exact Even.zero⟩
            · simp only [hk, ↓reduceIte]
              exact if_neg fun hc => by
                have := hc.2.2 p hp hp3
                rw [hp.factorization_pow, Finsupp.single_eq_same] at this
                exact hk this
          · simp only [hp3, ↓reduceIte]
            exact if_pos ⟨hk1,
              fun q _ hq1 => by
                rw [hp.factorization_pow]
                have hne : q ≠ p := fun h => hp1 (h ▸ hq1)
                exact Finsupp.single_eq_of_ne hne,
              fun q _ hq3 => by
                rw [hp.factorization_pow]
                have hne : q ≠ p := fun h => hp3 (h ▸ hq3)
                rw [Finsupp.single_eq_of_ne hne]; exact Even.zero⟩
      have hp_fChi4 : ∀ k : ℕ, fChi4 (p ^ k) =
          if p % 4 = 1 then (k + 1 : ℤ)
          else if p % 4 = 3 then (if Even k then 1 else 0) else 1 := by
        intro k
        unfold fChi4
        rw [Nat.divisors_prime_pow hp, Finset.sum_map]
        simp only [Function.Embedding.coeFn_mk]
        have hchi_pow : ∀ j : ℕ, chi4 (p ^ j) = (chi4 p) ^ j := by
          intro j; induction j with
          | zero => simp [chi4_one]
          | succ j ihj => rw [pow_succ, pow_succ, chi4_mul, ihj]
        simp_rw [hchi_pow]
        by_cases hp1 : p % 4 = 1
        · simp only [hp1, ↓reduceIte]
          have hc : chi4 p = 1 := by unfold chi4; simp [hp1]
          rw [hc]; simp
        · simp only [hp1, ↓reduceIte]
          by_cases hp3 : p % 4 = 3
          · simp only [hp3, ↓reduceIte]
            have hc : chi4 p = -1 := by unfold chi4; simp [hp3]
            rw [hc]
            induction k with
            | zero => simp
            | succ k ihk =>
              rw [Finset.sum_range_succ, ihk]
              by_cases hk : Even k
              · have hns : ¬ Even (k + 1) := by
                  rw [Nat.even_add_one]; exact not_not.mpr hk
                simp only [hk, hns, ↓reduceIte]
                obtain ⟨r, rfl⟩ := hk
                have : (-1 : ℤ) ^ (r + r + 1) = -1 := by
                  rw [pow_succ, ← two_mul, pow_mul]; norm_num
                linarith
              · have hs : Even (k + 1) := by rw [Nat.even_add_one]; exact hk
                simp only [hk, hs, ↓reduceIte]
                obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp hk
                rw [hr]
                have : (-1 : ℤ) ^ (2 * r + 1 + 1) = 1 := by
                  have : 2 * r + 1 + 1 = 2 * (r + 1) := by omega
                  rw [this, pow_mul]; norm_num
                linarith
          · simp only [hp3, ↓reduceIte]
            have hc : chi4 p = 0 := by unfold chi4; simp [hp1, hp3]
            rw [hc]
            rw [Finset.sum_eq_single 0]
            · simp
            · intro b _ hb0; exact zero_pow hb0
            · intro h0; exfalso; exact h0 (Finset.mem_range.mpr (Nat.succ_pos k))
      by_cases hp1 : p % 4 = 1
      · have hp3 : p % 4 ≠ 3 := by omega
        calc ∑ j ∈ Finset.range (e + 1), indA (p ^ j) * indA (p ^ e / p ^ j)
            = ∑ j ∈ Finset.range (e + 1), (1 : ℤ) := by
              refine Finset.sum_congr rfl fun j hj => ?_
              rw [hdiv_pow j hj, hp_indA, hp_indA]; simp [hp3]
          _ = (e + 1 : ℤ) := by simp
          _ = ∑ j ∈ Finset.range (e + 1), indG (p ^ j) * fChi4 (p ^ e / p ^ j) := by
              rw [Finset.sum_eq_single 0]
              · rw [hdiv_pow 0 (Finset.mem_range.mpr (Nat.succ_pos e)), Nat.sub_zero,
                  hp_indG, hp_fChi4]; simp [hp1]
              · intro j hj hj0
                rw [hdiv_pow j hj, hp_indG]; simp [hp1, hj0]
              · intro h0; exfalso; exact h0 (Finset.mem_range.mpr (Nat.succ_pos e))
      · by_cases hp3 : p % 4 = 3
        · refine Finset.sum_congr rfl fun j hj => ?_
          rw [hdiv_pow j hj, hp_indA, hp_indA, hp_indG, hp_fChi4]
          simp [hp3]
        · refine Finset.sum_congr rfl fun j hj => ?_
          rw [hdiv_pow j hj, hp_indA, hp_indA, hp_indG, hp_fChi4]
          simp [hp1, hp3]

/-- Bound `∑_{d=1}^N indG(d) / d ≤ 4` via `d = 2^a * u^2`! -/
private lemma sum_indG_div_le_four (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, (indG d : ℝ) / (d : ℝ) ≤ 4 := by
  set S := (Finset.Icc 1 N).filter isGSupp
  have h1 : ∑ d ∈ Finset.Icc 1 N, (indG d : ℝ) / (d : ℝ) = ∑ d ∈ S, (1 : ℝ) / (d : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    unfold indG; split_ifs <;> simp
  rw [h1]
  have hfactor : ∀ d ∈ S, ∃ a ∈ Finset.range (N + 1), ∃ u ∈ Finset.Icc 1 N, d = 2 ^ a * u ^ 2 := by
    intro d hd
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hd
    set a := d.factorization 2
    set m := d / 2 ^ a
    have h2a_dvd : 2 ^ a ∣ d := Nat.ordProj_dvd d 2
    have hdm : 2 ^ a * m = d := Nat.mul_div_cancel' h2a_dvd
    have hm_pos : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · rw [hm0, mul_zero] at hdm; omega
      · exact hmpos
    have ha_le : a ≤ N := by
      have : a < 2 ^ a := Nat.lt_two_pow_self
      have : 2 ^ a ≤ d := Nat.le_of_dvd (by omega) h2a_dvd
      omega
    have hm_even : ∀ p : ℕ, Even (m.factorization p) := by
      intro p
      by_cases hp : p.Prime
      · by_cases hpm : p ∣ m
        · have hp_ne2 : p ≠ 2 := by
            intro hp2; subst hp2
            have h2a1 : 2 ^ (a + 1) ∣ d := by
              rw [pow_succ, ← hdm]; exact Nat.mul_dvd_mul_left (2 ^ a) hpm
            have := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp h2a1
            omega
          have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp_ne2
          have hp_mod : p % 4 = 1 ∨ p % 4 = 3 := by omega
          have hfac_eq : m.factorization p = d.factorization p := by
            have := congrArg (fun f : ℕ →₀ ℕ => f p)
              (Nat.factorization_mul (pow_ne_zero a (by norm_num)) (by omega) :
                (2 ^ a * m).factorization = (2 ^ a).factorization + m.factorization)
            rw [hdm, Finsupp.add_apply, Nat.prime_two.factorization_pow,
              Finsupp.single_eq_of_ne hp_ne2, zero_add] at this
            exact this.symm
          rcases hp_mod with hp1 | hp3
          · exfalso
            have hz := hd.2.2.1 p hp hp1
            rw [← hfac_eq] at hz
            have hpos := hp.factorization_pos_of_dvd (by omega) hpm
            omega
          · rw [hfac_eq]; exact hd.2.2.2 p hp hp3
        · rw [Nat.factorization_eq_zero_of_not_dvd hpm]; exact Even.zero
      · rw [Nat.factorization_eq_zero_of_not_prime m hp]; exact Even.zero
    set u := ∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2)
    have hmu : m = u ^ 2 := by
      dsimp [u]
      rw [← Finset.prod_pow]
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self (by omega : m ≠ 0)]
      rw [Finsupp.prod]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← pow_mul]
      obtain ⟨r, hr⟩ := hm_even p
      congr 1; omega
    have hu_ge : 1 ≤ u := by
      rcases Nat.eq_zero_or_pos u with hu0 | hupos
      · rw [hu0] at hmu; simp at hmu; omega
      · exact hupos
    have hu_le : u ≤ N := by
      have : u ≤ u ^ 2 := Nat.le_self_pow (by norm_num) u
      have : m ≤ d := Nat.div_le_self d (2 ^ a)
      omega
    exact ⟨a, Finset.mem_range.mpr (by omega), u, Finset.mem_Icc.mpr ⟨hu_ge, hu_le⟩,
      hmu ▸ hdm.symm⟩
  set Img := ((Finset.range (N + 1)) ×ˢ (Finset.Icc 1 N)).image (fun p : ℕ × ℕ => 2 ^ p.1 * p.2 ^ 2)
  have hsub : S ⊆ Img := by
    intro d hd
    obtain ⟨a, ha, u, hu, rfl⟩ := hfactor d hd
    exact Finset.mem_image.mpr ⟨(a, u), Finset.mem_product.mpr ⟨ha, hu⟩, rfl⟩
  calc ∑ d ∈ S, (1 : ℝ) / (d : ℝ)
      ≤ ∑ d ∈ Img, (1 : ℝ) / (d : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ p ∈ (Finset.range (N + 1)) ×ˢ (Finset.Icc 1 N),
          (1 : ℝ) / ((2 ^ p.1 * p.2 ^ 2 : ℕ) : ℝ) :=
        Finset.sum_image_le_of_nonneg (f := fun d : ℕ => (1 : ℝ) / (d : ℝ)) (fun _ _ => by positivity)
    _ = (∑ a ∈ Finset.range (N + 1), ((1 / 2 : ℝ) ^ a)) *
          (∑ u ∈ Finset.Icc 1 N, (1 : ℝ) / (u : ℝ) ^ 2) := by
        rw [Finset.sum_product, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        push_cast; rw [one_div_pow]; ring
    _ ≤ 2 * 2 := by
        have hgeom : ∑ a ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ a ≤ 2 := by
          rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
          have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (N + 1) := by positivity
          have hrew : ((1 / 2 : ℝ) ^ (N + 1) - 1) / (1 / 2 - 1) =
              2 - 2 * (1 / 2 : ℝ) ^ (N + 1) := by ring
          linarith
        exact mul_le_mul hgeom (sum_inv_sq_le_two N)
          (Finset.sum_nonneg fun _ _ => by positivity) (by norm_num)
    _ = 4 := by norm_num

/-- Bound `∑_{m=1}^M fChi4(m) / m ≤ Real.log M + 1` for `M ≥ 1`! -/
private lemma sum_fChi4_div_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, (fChi4 m : ℝ) / (m : ℝ) ≤ Real.log (M : ℝ) + 1 := by
  have hswap : ∑ m ∈ Finset.Icc 1 M, (fChi4 m : ℝ) / (m : ℝ) =
      ∑ q ∈ Finset.Icc 1 M, (1 / (q : ℝ)) *
        (∑ k ∈ Finset.Icc 1 (M / q), (chi4 k : ℝ) / (k : ℝ)) := by
    have h1 : ∀ m ∈ Finset.Icc 1 M, (fChi4 m : ℝ) / (m : ℝ) =
        ∑ k ∈ m.divisors, (chi4 k : ℝ) / (m : ℝ) := by
      intro m _; unfold fChi4; push_cast; rw [Finset.sum_div]
    rw [Finset.sum_congr rfl h1]
    set P := ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter (fun p => p.1 * p.2 ≤ M)
    have hlhs : ∑ m ∈ Finset.Icc 1 M, ∑ k ∈ m.divisors, (chi4 k : ℝ) / (m : ℝ) =
        ∑ p ∈ P, (chi4 p.1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := by
      rw [Finset.sum_sigma']
      refine (Finset.sum_nbij (fun p : ℕ × ℕ => (⟨p.1 * p.2, p.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_).symm
      · intro p hp
        simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        have hp12 : p.1 * p.2 ≠ 0 := mul_ne_zero (by omega) (by omega)
        simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
        exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hp12, hp.2⟩, ⟨dvd_mul_right p.1 p.2, hp12⟩⟩
      · intro p1 hp1 p2 hp2 heq
        simp only [P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp1 hp2
        have hfst : p1.1 * p1.2 = p2.1 * p2.2 := congrArg Sigma.fst heq
        have hsnd : p1.1 = p2.1 := by simpa using eq_of_heq (Sigma.mk.inj_iff.mp heq).2
        have h2 : p1.2 = p2.2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p1.1) (hsnd ▸ hfst)
        exact Prod.ext hsnd h2
      · intro s hs
        simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hs
        have hk_pos : 1 ≤ s.2 := Nat.pos_of_dvd_of_pos hs.2.1 (by omega)
        have hq_pos : 1 ≤ s.1 / s.2 := Nat.div_pos (Nat.le_of_dvd (by omega) hs.2.1) (by omega)
        have hk_le : s.2 ≤ M := le_trans (Nat.le_of_dvd (by omega) hs.2.1) hs.1.2
        have hq_le : s.1 / s.2 ≤ M := le_trans (Nat.div_le_self s.1 s.2) hs.1.2
        have hmul : s.2 * (s.1 / s.2) = s.1 := Nat.mul_div_cancel' hs.2.1
        refine ⟨(s.2, s.1 / s.2), ?_, ?_⟩
        · simp only [P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
          exact ⟨⟨⟨hk_pos, hk_le⟩, ⟨hq_pos, hq_le⟩⟩, hmul.symm ▸ hs.1.2⟩
        · exact Sigma.ext hmul (heq_of_eq rfl)
      · intro p _; rfl
    have hrhs : ∑ q ∈ Finset.Icc 1 M, (1 / (q : ℝ)) *
          (∑ k ∈ Finset.Icc 1 (M / q), (chi4 k : ℝ) / (k : ℝ)) =
        ∑ p ∈ P, (chi4 p.1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_sigma']
      refine (Finset.sum_nbij (fun p : ℕ × ℕ => (⟨p.2, p.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_).symm
      · intro p hp
        simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        simp only [Finset.mem_sigma, Finset.mem_Icc]
        exact ⟨hp.1.2, ⟨hp.1.1.1, (Nat.le_div_iff_mul_le (by omega : 0 < p.2)).mpr hp.2⟩⟩
      · intro p1 _ p2 _ heq
        have h2 : p1.2 = p2.2 := congrArg Sigma.fst heq
        have h1 : p1.1 = p2.1 := by simpa using eq_of_heq (Sigma.mk.inj_iff.mp heq).2
        exact Prod.ext h1 h2
      · intro s hs
        simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc] at hs
        have hmul : s.2 * s.1 ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < s.1)).mp hs.2.2
        have hk_le : s.2 ≤ M := le_trans (Nat.le_mul_of_pos_right s.2 (by omega)) hmul
        refine ⟨(s.2, s.1), ?_, rfl⟩
        simp only [P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨⟨hs.2.1, hk_le⟩, hs.1⟩, hmul⟩
      · intro p _; push_cast; ring
    rw [hlhs, hrhs]
  rw [hswap]
  calc ∑ q ∈ Finset.Icc 1 M, (1 / (q : ℝ)) *
          (∑ k ∈ Finset.Icc 1 (M / q), (chi4 k : ℝ) / (k : ℝ))
      ≤ ∑ q ∈ Finset.Icc 1 M, (1 / (q : ℝ)) * 1 := by
        refine Finset.sum_le_sum fun q _ => ?_
        exact mul_le_mul_of_nonneg_left (sum_chi4_div_bounds (M / q)).2 (by positivity)
    _ = ∑ q ∈ Finset.Icc 1 M, (1 : ℝ) / (q : ℝ) := by simp
    _ ≤ Real.log (M : ℝ) + 1 := harmonic_le_log_add_one M hM

/-- Key harmonic bound on sums-of-two-squares candidates:
`∑_{a ∈ A', a ≤ X} 1/a ≤ √(8 * log X + 4)` for all `X ≥ 1`! -/
private lemma sum_inv_twoSqCand_le (X : ℕ) (hX : 1 ≤ X) :
    ∑ a ∈ (Finset.Icc 1 X).filter isTwoSqCand, (1 : ℝ) / (a : ℝ) ≤
      Real.sqrt (8 * Real.log (X : ℝ) + 4) := by
  set S := (Finset.Icc 1 X).filter isTwoSqCand
  have hnonneg : 0 ≤ ∑ a ∈ S, (1 : ℝ) / (a : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  rw [← Real.sqrt_sq hnonneg]
  apply Real.sqrt_le_sqrt
  have hsq : (∑ a ∈ S, (1 : ℝ) / (a : ℝ)) ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 (X ^ 2), (dconv indA indA n : ℝ) / (n : ℝ) := by
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_product']
    have hrewrite : ∀ n ∈ Finset.Icc 1 (X ^ 2), (dconv indA indA n : ℝ) / (n : ℝ) =
        ∑ d ∈ n.divisors, ((indA d : ℝ) * (indA (n / d) : ℝ)) / (n : ℝ) := by
      intro n _; unfold dconv; push_cast; rw [Finset.sum_div]
    rw [Finset.sum_congr rfl hrewrite, Finset.sum_sigma']
    refine sum_le_sum_of_inj_nonneg (S ×ˢ S) ((Finset.Icc 1 (X ^ 2)).sigma Nat.divisors)
      (fun p => (1 : ℝ) / (p.1 : ℝ) * ((1 : ℝ) / (p.2 : ℝ)))
      (fun s => ((indA s.2 : ℝ) * (indA (s.1 / s.2) : ℝ)) / (s.1 : ℝ))
      (fun p : ℕ × ℕ => (⟨p.1 * p.2, p.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [S, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hp
      have hp12 : p.1 * p.2 ≠ 0 := mul_ne_zero (by omega) (by omega)
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr hp12, ?_⟩, ⟨dvd_mul_right p.1 p.2, hp12⟩⟩
      rw [sq]; exact Nat.mul_le_mul hp.1.1.2 hp.2.1.2
    · intro p1 hp1 p2 hp2 heq
      simp only [S, Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hp1 hp2
      have hfst : p1.1 * p1.2 = p2.1 * p2.2 := congrArg Sigma.fst heq
      have hsnd : p1.1 = p2.1 := by simpa using eq_of_heq (Sigma.mk.inj_iff.mp heq).2
      have h2 : p1.2 = p2.2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p1.1) (hsnd ▸ hfst)
      exact Prod.ext hsnd h2
    · intro s _
      unfold indA; split_ifs <;> positivity
    · intro p hp
      simp only [S, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hp
      have h1 : indA p.1 = 1 := by unfold indA; simp [hp.1.2]
      have h2 : indA (p.1 * p.2 / p.1) = 1 := by
        rw [Nat.mul_div_cancel_left _ (by omega : 0 < p.1)]
        unfold indA; simp [hp.2.2]
      rw [h1, h2]; push_cast; ring_nf; exact le_rfl
  have hid : ∑ n ∈ Finset.Icc 1 (X ^ 2), (dconv indA indA n : ℝ) / (n : ℝ) =
      ∑ n ∈ Finset.Icc 1 (X ^ 2), (dconv indG fChi4 n : ℝ) / (n : ℝ) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [dconv_indA_eq_dconv_indG_fChi4 n (Finset.mem_Icc.mp hn).1]
  have hswap : ∑ n ∈ Finset.Icc 1 (X ^ 2), (dconv indG fChi4 n : ℝ) / (n : ℝ) =
      ∑ d ∈ Finset.Icc 1 (X ^ 2), ((indG d : ℝ) / (d : ℝ)) *
        (∑ m ∈ Finset.Icc 1 (X ^ 2 / d), (fChi4 m : ℝ) / (m : ℝ)) := by
    set N := X ^ 2
    have h1 : ∀ n ∈ Finset.Icc 1 N, (dconv indG fChi4 n : ℝ) / (n : ℝ) =
        ∑ d ∈ n.divisors, ((indG d : ℝ) * (fChi4 (n / d) : ℝ)) / (n : ℝ) := by
      intro n _; unfold dconv; push_cast; rw [Finset.sum_div]
    rw [Finset.sum_congr rfl h1]
    set P := ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p => p.1 * p.2 ≤ N)
    have hlhs : ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
          ((indG d : ℝ) * (fChi4 (n / d) : ℝ)) / (n : ℝ) =
        ∑ p ∈ P, ((indG p.1 : ℝ) * (fChi4 p.2 : ℝ)) / ((p.1 * p.2 : ℕ) : ℝ) := by
      rw [Finset.sum_sigma']
      refine (Finset.sum_nbij (fun p : ℕ × ℕ => (⟨p.1 * p.2, p.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_).symm
      · intro p hp
        simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        have hp12 : p.1 * p.2 ≠ 0 := mul_ne_zero (by omega) (by omega)
        simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
        exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hp12, hp.2⟩, ⟨dvd_mul_right p.1 p.2, hp12⟩⟩
      · intro p1 hp1 p2 hp2 heq
        simp only [P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp1 hp2
        have hfst : p1.1 * p1.2 = p2.1 * p2.2 := congrArg Sigma.fst heq
        have hsnd : p1.1 = p2.1 := by simpa using eq_of_heq (Sigma.mk.inj_iff.mp heq).2
        have h2 : p1.2 = p2.2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p1.1) (hsnd ▸ hfst)
        exact Prod.ext hsnd h2
      · intro s hs
        simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hs
        have hd_pos : 1 ≤ s.2 := Nat.pos_of_dvd_of_pos hs.2.1 (by omega)
        have hm_pos : 1 ≤ s.1 / s.2 := Nat.div_pos (Nat.le_of_dvd (by omega) hs.2.1) (by omega)
        have hd_le : s.2 ≤ N := le_trans (Nat.le_of_dvd (by omega) hs.2.1) hs.1.2
        have hm_le : s.1 / s.2 ≤ N := le_trans (Nat.div_le_self s.1 s.2) hs.1.2
        have hmul : s.2 * (s.1 / s.2) = s.1 := Nat.mul_div_cancel' hs.2.1
        refine ⟨(s.2, s.1 / s.2), ?_, ?_⟩
        · simp only [P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
          exact ⟨⟨⟨hd_pos, hd_le⟩, ⟨hm_pos, hm_le⟩⟩, hmul.symm ▸ hs.1.2⟩
        · exact Sigma.ext hmul (heq_of_eq rfl)
      · intro p hp
        simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        rw [Nat.mul_div_cancel_left _ (by omega : 0 < p.1)]
    have hrhs : ∑ d ∈ Finset.Icc 1 N, ((indG d : ℝ) / (d : ℝ)) *
          (∑ m ∈ Finset.Icc 1 (N / d), (fChi4 m : ℝ) / (m : ℝ)) =
        ∑ p ∈ P, ((indG p.1 : ℝ) * (fChi4 p.2 : ℝ)) / ((p.1 * p.2 : ℕ) : ℝ) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_sigma']
      refine (Finset.sum_nbij (fun p : ℕ × ℕ => (⟨p.1, p.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_).symm
      · intro p hp
        simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        simp only [Finset.mem_sigma, Finset.mem_Icc]
        exact ⟨hp.1.1, ⟨hp.1.2.1, (Nat.le_div_iff_mul_le (by omega : 0 < p.1)).mpr (mul_comm p.1 p.2 ▸ hp.2)⟩⟩
      · intro p1 _ p2 _ heq
        have h1 : p1.1 = p2.1 := congrArg Sigma.fst heq
        have h2 : p1.2 = p2.2 := by simpa using eq_of_heq (Sigma.mk.inj_iff.mp heq).2
        exact Prod.ext h1 h2
      · intro s hs
        simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc] at hs
        have hmul : s.1 * s.2 ≤ N :=
          mul_comm s.2 s.1 ▸ (Nat.le_div_iff_mul_le (by omega : 0 < s.1)).mp hs.2.2
        have hm_le : s.2 ≤ N := le_trans (Nat.le_mul_of_pos_left s.2 (by omega)) hmul
        refine ⟨(s.1, s.2), ?_, rfl⟩
        simp only [P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨hs.1, ⟨hs.2.1, hm_le⟩⟩, hmul⟩
      · intro p _; push_cast; ring
    rw [hlhs, hrhs]
  have hbound : ∑ d ∈ Finset.Icc 1 (X ^ 2), ((indG d : ℝ) / (d : ℝ)) *
        (∑ m ∈ Finset.Icc 1 (X ^ 2 / d), (fChi4 m : ℝ) / (m : ℝ)) ≤
      4 * (Real.log ((X ^ 2 : ℕ) : ℝ) + 1) := by
    calc ∑ d ∈ Finset.Icc 1 (X ^ 2), ((indG d : ℝ) / (d : ℝ)) *
            (∑ m ∈ Finset.Icc 1 (X ^ 2 / d), (fChi4 m : ℝ) / (m : ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 (X ^ 2), ((indG d : ℝ) / (d : ℝ)) *
            (Real.log ((X ^ 2 : ℕ) : ℝ) + 1) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hgnn : 0 ≤ (indG d : ℝ) / (d : ℝ) := by unfold indG; split_ifs <;> positivity
          apply mul_le_mul_of_nonneg_left _ hgnn
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hdle : d ≤ X ^ 2 := (Finset.mem_Icc.mp hd).2
          have hq1 : 1 ≤ X ^ 2 / d := Nat.div_pos hdle (by omega)
          have h1 := sum_fChi4_div_le (X ^ 2 / d) hq1
          have hlog : Real.log ((X ^ 2 / d : ℕ) : ℝ) ≤ Real.log ((X ^ 2 : ℕ) : ℝ) := by
            apply Real.log_le_log (by positivity)
            exact_mod_cast Nat.div_le_self (X ^ 2) d
          linarith
      _ = (∑ d ∈ Finset.Icc 1 (X ^ 2), (indG d : ℝ) / (d : ℝ)) *
            (Real.log ((X ^ 2 : ℕ) : ℝ) + 1) := by rw [← Finset.sum_mul]
      _ ≤ 4 * (Real.log ((X ^ 2 : ℕ) : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_right (sum_indG_div_le_four (X ^ 2))
          have h1 : (1 : ℝ) ≤ ((X ^ 2 : ℕ) : ℝ) := by
            exact_mod_cast Nat.one_le_pow 2 X (by omega)
          linarith [Real.log_nonneg h1]
  have hlog2 : Real.log ((X ^ 2 : ℕ) : ℝ) = 2 * Real.log (X : ℝ) := by
    push_cast; rw [Real.log_pow]; ring
  linarith [hsq, hid, hswap, hbound, hlog2]

/-- Self-contained von Mangoldt function `Λ(d)`: `log p` if `d = p^k` (`p` prime, `k ≥ 1`), else `0`. -/
private noncomputable def vonMangoldtReal (d : ℕ) : ℝ :=
  if IsPrimePow d then Real.log (d.minFac : ℝ) else 0

private lemma vonMangoldtReal_nonneg (d : ℕ) : 0 ≤ vonMangoldtReal d := by
  unfold vonMangoldtReal
  split_ifs with h
  · have hp : d.minFac.Prime := Nat.minFac_prime h.ne_one
    exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · rfl

private lemma vonMangoldtReal_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    vonMangoldtReal (p ^ k) = Real.log (p : ℝ) := by
  unfold vonMangoldtReal
  have hpp : IsPrimePow (p ^ k) := hp.isPrimePow.pow (by omega)
  rw [if_pos hpp, minFac_prime_pow hp hk]

/-- Self-contained Legendre's formula helper for `C(2m, m)`:
for any prime `p` and `m ≥ 1`, `|{k ≥ 1 : m < p^k ≤ 2m}| ≤ (Nat.centralBinom m).factorization p`. -/
private lemma card_prime_pow_Ioc_le_factorization_centralBinom
    (p m : ℕ) (hp : p.Prime) (hm : 1 ≤ m) :
    ((Finset.Icc 1 (2 * m)).filter (fun k => m < p ^ k ∧ p ^ k ≤ 2 * m)).card ≤
      (Nat.centralBinom m).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hcb_ne : Nat.centralBinom m ≠ 0 := Nat.centralBinom_ne_zero m
  have hfac_eq : Nat.centralBinom m * (m.factorial * m.factorial) = (2 * m).factorial := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m)
    have hsub : 2 * m - m = m := by omega
    rw [hsub] at this
    linarith
  have hval_add : (Nat.centralBinom m).factorization p + 2 * (m.factorial).factorization p =
      ((2 * m).factorial).factorization p := by
    have h1 := congrArg (fun x => x.factorization p) hfac_eq
    rw [Nat.factorization_mul hcb_ne (mul_ne_zero (Nat.factorial_ne_zero m) (Nat.factorial_ne_zero m)),
      Nat.factorization_mul (Nat.factorial_ne_zero m) (Nat.factorial_ne_zero m),
      Finsupp.add_apply, Finsupp.add_apply] at h1
    omega
  have hbound_pow : 2 * m < p ^ (2 * m + 1) := by
    calc 2 * m < 2 ^ (2 * m) := Nat.lt_two_pow_self
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ p ^ (2 * m + 1) := Nat.pow_le_pow_left hp.two_le _
  have hval_2m : ((2 * m).factorial).factorization p =
      ∑ k ∈ Finset.Icc 1 (2 * m), (2 * m) / p ^ k := by
    have hpad := padicValNat_factorial (p := p) (n := 2 * m) (b := 2 * m + 1)
      (by
        rw [Nat.log_lt_iff_lt_pow hp.one_lt (by omega : 2 * m ≠ 0)]
        exact hbound_pow)
    rw [← Nat.factorization_def _ hp] at hpad
    rw [hpad]; congr 1
  have hval_m : (m.factorial).factorization p =
      ∑ k ∈ Finset.Icc 1 (2 * m), m / p ^ k := by
    have hpad := padicValNat_factorial (p := p) (n := m) (b := 2 * m + 1)
      (by
        rw [Nat.log_lt_iff_lt_pow hp.one_lt (by omega : m ≠ 0)]
        omega)
    rw [← Nat.factorization_def _ hp] at hpad
    rw [hpad]; congr 1
  have hterm_le : ∀ k : ℕ, 2 * (m / p ^ k) ≤ (2 * m) / p ^ k := by
    intro k
    have hq : 0 < p ^ k := pow_pos hp.pos k
    exact (Nat.le_div_iff_mul_le hq).mpr (by
      have := Nat.div_mul_le_self m (p ^ k); linarith)
  have hterm_ind : ∀ k ∈ Finset.Icc 1 (2 * m),
      (if m < p ^ k ∧ p ^ k ≤ 2 * m then 1 else 0) + 2 * (m / p ^ k) ≤ (2 * m) / p ^ k := by
    intro k _
    split_ifs with hk
    · have h1 : m / p ^ k = 0 := Nat.div_eq_of_lt hk.1
      have h2 : 1 ≤ (2 * m) / p ^ k := Nat.div_pos hk.2 (pow_pos hp.pos k)
      omega
    · rw [zero_add]; exact hterm_le k
  have hsum_le := Finset.sum_le_sum hterm_ind
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id] at hsum_le
  rw [← hval_m, ← hval_2m] at hsum_le
  omega

/-- Dyadic Chebyshev step: `∑_{m < d ≤ 2m} Λ(d) ≤ 2 * m * log 2` for all `m ≥ 1`. -/
private lemma sum_vonMangoldt_Ioc_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ d ∈ Finset.Ioc m (2 * m), vonMangoldtReal d ≤ 2 * (m : ℝ) * Real.log 2 := by
  set S := (Finset.Ioc m (2 * m)).filter IsPrimePow
  have h1 : ∑ d ∈ Finset.Ioc m (2 * m), vonMangoldtReal d =
      ∑ d ∈ S, Real.log (d.minFac : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    unfold vonMangoldtReal; split_ifs <;> rfl
  rw [h1]
  set Pr := (Finset.Icc 1 (2 * m)).filter Nat.Prime
  have hgroup : ∑ d ∈ S, Real.log (d.minFac : ℝ) ≤
      ∑ p ∈ Pr, (((Finset.Icc 1 (2 * m)).filter (fun k => m < p ^ k ∧ p ^ k ≤ 2 * m)).card : ℝ) *
        Real.log (p : ℝ) := by
    have hmap : ∀ d ∈ S, d.minFac ∈ Pr := by
      intro d hd
      simp only [S, Finset.mem_filter, Finset.mem_Ioc] at hd
      simp only [Pr, Finset.mem_filter, Finset.mem_Icc]
      have hp := Nat.minFac_prime hd.2.ne_one
      exact ⟨⟨hp.one_le, le_trans (Nat.minFac_le (by omega)) hd.1.2⟩, hp⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_le_sum fun p hp => ?_
    simp only [Pr, Finset.mem_filter, Finset.mem_Icc] at hp
    have hcongr : ∑ d ∈ S.filter (fun d => d.minFac = p), Real.log (d.minFac : ℝ) =
        ((S.filter (fun d => d.minFac = p)).card : ℝ) * Real.log (p : ℝ) := by
      rw [Finset.sum_congr rfl (fun d hd => by rw [(Finset.mem_filter.mp hd).2]),
        Finset.sum_const, nsmul_eq_mul]
    rw [hcongr]
    apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast hp.2.one_le))
    have hcard : (S.filter (fun d => d.minFac = p)).card ≤
        ((Finset.Icc 1 (2 * m)).filter (fun k => m < p ^ k ∧ p ^ k ≤ 2 * m)).card := by
      refine Finset.card_le_card_of_injOn (fun d => d.factorization p) ?_ ?_
      · intro d hd
        simp only [Finset.mem_coe, Finset.mem_filter, S, Finset.mem_Ioc] at hd
        obtain ⟨⟨⟨hdm, hd2m⟩, hpp⟩, hmin⟩ := hd
        obtain ⟨q, k, hq, hk, hqk⟩ := hpp
        have hqp : q = p := by
          have : (q ^ k).minFac = q := minFac_prime_pow (Nat.prime_iff.mpr hq) (by omega)
          rw [← hmin, ← hqk, this]
        subst hqp
        have hfac : d.factorization q = k := by
          rw [← hqk, hp.2.factorization_pow, Finsupp.single_eq_same]
        change d.factorization q ∈ ((Finset.Icc 1 (2 * m)).filter (fun k => m < q ^ k ∧ q ^ k ≤ 2 * m) : Set ℕ)
        rw [hfac]
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
        have hk_le : k ≤ 2 * m := by
          have : k < 2 ^ k := Nat.lt_two_pow_self
          have : 2 ^ k ≤ q ^ k := Nat.pow_le_pow_left hp.2.two_le k
          omega
        exact ⟨⟨by omega, hk_le⟩, hqk ▸ hdm, hqk ▸ hd2m⟩
      · intro d1 hd1 d2 hd2 heq
        simp only [Finset.mem_coe, Finset.mem_filter, S, Finset.mem_Ioc] at hd1 hd2
        obtain ⟨q1, k1, hq1, hk1, hqk1⟩ := hd1.1.2
        obtain ⟨q2, k2, hq2, hk2, hqk2⟩ := hd2.1.2
        have h1 : q1 = p := by
          rw [← hd1.2, ← hqk1, minFac_prime_pow (Nat.prime_iff.mpr hq1) (by omega)]
        have h2 : q2 = p := by
          rw [← hd2.2, ← hqk2, minFac_prime_pow (Nat.prime_iff.mpr hq2) (by omega)]
        subst h1; subst h2
        have heq' : d1.factorization q2 = d2.factorization q2 := heq
        rw [← hqk1, ← hqk2, hp.2.factorization_pow, hp.2.factorization_pow,
          Finsupp.single_eq_same, Finsupp.single_eq_same] at heq'
        rw [← hqk1, ← hqk2, heq']
    exact_mod_cast hcard
  have hcb_pos : 0 < Nat.centralBinom m := Nat.centralBinom_pos m
  calc ∑ d ∈ S, Real.log (d.minFac : ℝ)
      ≤ ∑ p ∈ Pr, (((Finset.Icc 1 (2 * m)).filter (fun k => m < p ^ k ∧ p ^ k ≤ 2 * m)).card : ℝ) *
          Real.log (p : ℝ) := hgroup
    _ ≤ ∑ p ∈ Pr, (((Nat.centralBinom m).factorization p : ℕ) : ℝ) * Real.log (p : ℝ) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpr := (Finset.mem_filter.mp hp).2
        apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast hpr.one_le))
        exact_mod_cast card_prime_pow_Ioc_le_factorization_centralBinom p m hpr hm
    _ ≤ ∑ p ∈ (Nat.centralBinom m).primeFactors,
          (((Nat.centralBinom m).factorization p : ℕ) : ℝ) * Real.log (p : ℝ) := by
        have h1 : ∑ p ∈ Pr, (((Nat.centralBinom m).factorization p : ℕ) : ℝ) * Real.log (p : ℝ) =
            ∑ p ∈ Pr ∩ (Nat.centralBinom m).primeFactors,
              (((Nat.centralBinom m).factorization p : ℕ) : ℝ) * Real.log (p : ℝ) := by
          refine (Finset.sum_subset Finset.inter_subset_left fun p hp hnot => ?_).symm
          have hpr := (Finset.mem_filter.mp hp).2
          have hnd : ¬ p ∣ Nat.centralBinom m := fun hd =>
            hnot (Finset.mem_inter.mpr ⟨hp, Nat.mem_primeFactors.mpr ⟨hpr, hd, by omega⟩⟩)
          rw [Nat.factorization_eq_zero_of_not_dvd hnd]; simp
        rw [h1]
        refine Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun p hp _ => ?_
        have hpr := Nat.prime_of_mem_primeFactors hp
        exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hpr.one_le))
    _ = Real.log ((Nat.centralBinom m : ℕ) : ℝ) := by
        have hprod := Nat.prod_factorization_pow_eq_self (ne_of_gt hcb_pos)
        conv_rhs => rw [← hprod, Finsupp.prod]
        rw [Nat.cast_prod, Real.log_prod]
        · refine Finset.sum_congr rfl fun p _ => by rw [Nat.cast_pow, Real.log_pow]
        · intro p hp
          have hpr := Nat.prime_of_mem_primeFactors hp
          exact_mod_cast pow_ne_zero _ hpr.ne_zero
    _ ≤ Real.log ((4 ^ m : ℕ) : ℝ) := by
        apply Real.log_le_log (by exact_mod_cast hcb_pos)
        exact_mod_cast Nat.centralBinom_le_four_pow m
    _ = 2 * (m : ℝ) * Real.log 2 := by
        have h4 : ((4 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ (2 * m) := by
          push_cast; rw [pow_mul]; norm_num
        rw [h4, Real.log_pow]; push_cast; ring

/-- Self-contained Chebyshev bound: `∑_{d=1}^N Λ(d) ≤ 4 * (log 2) * N` for all `N : ℕ`! -/
private lemma chebyshev_psi_le (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, vonMangoldtReal d ≤ 4 * Real.log 2 * (N : ℝ) := by
  induction N using Nat.strong_induction_on with
  | h n ih =>
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    by_cases hn0 : n = 0
    · subst hn0; simp
    · by_cases hn1 : n = 1
      · subst hn1; simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, mul_one]
        unfold vonMangoldtReal
        rw [if_neg not_isPrimePow_one]; positivity
      · by_cases hn2 : n = 2
        · subst hn2
          have h12 : Finset.Icc 1 2 = {1, 2} := by decide
          rw [h12, Finset.sum_insert (by decide), Finset.sum_singleton]
          have h1 : vonMangoldtReal 1 = 0 := by unfold vonMangoldtReal; rw [if_neg not_isPrimePow_one]
          have h2 : vonMangoldtReal 2 = Real.log 2 := by
            simpa using vonMangoldtReal_prime_pow Nat.prime_two le_rfl
          rw [h1, h2]; push_cast; linarith
        · by_cases hn3 : n = 3
          · subst hn3
            have h13 : Finset.Icc 1 3 = {1, 2, 3} := by decide
            rw [h13, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
            have h1 : vonMangoldtReal 1 = 0 := by unfold vonMangoldtReal; rw [if_neg not_isPrimePow_one]
            have h2 : vonMangoldtReal 2 = Real.log 2 := by
              simpa using vonMangoldtReal_prime_pow Nat.prime_two le_rfl
            have h3 : vonMangoldtReal 3 = Real.log 3 := by
              simpa using vonMangoldtReal_prime_pow Nat.prime_three le_rfl
            have h34 : Real.log 3 ≤ 2 * Real.log 2 := by
              have : (3 : ℝ) ≤ 2 ^ 2 := by norm_num
              have h := Real.log_le_log (by norm_num) this
              rw [Real.log_pow] at h; push_cast at h; linarith
            rw [h1, h2, h3]; push_cast; linarith
          · set m := (n + 1) / 2
            have hm_ge : 2 ≤ m := by omega
            have hm_lt : m < n := by omega
            have hn_le : n ≤ 2 * m := by omega
            have hsub : Finset.Icc 1 n ⊆ Finset.Icc 1 m ∪ Finset.Ioc m (2 * m) := by
              intro d hd
              simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc] at hd ⊢
              omega
            have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Ioc m (2 * m)) := by
              rw [Finset.disjoint_left]; intro d h1 h2
              simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
            calc ∑ d ∈ Finset.Icc 1 n, vonMangoldtReal d
                ≤ ∑ d ∈ Finset.Icc 1 m ∪ Finset.Ioc m (2 * m), vonMangoldtReal d :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => vonMangoldtReal_nonneg d)
              _ = (∑ d ∈ Finset.Icc 1 m, vonMangoldtReal d) +
                    (∑ d ∈ Finset.Ioc m (2 * m), vonMangoldtReal d) :=
                  Finset.sum_union hdisj
              _ ≤ 4 * Real.log 2 * (m : ℝ) + 2 * (m : ℝ) * Real.log 2 :=
                  add_le_add (ih m hm_lt) (sum_vonMangoldt_Ioc_le m (by omega))
              _ = 6 * Real.log 2 * (m : ℝ) := by ring
              _ ≤ 4 * Real.log 2 * (n : ℝ) := by
                  have hmn : 6 * (m : ℝ) ≤ 4 * (n : ℝ) := by
                    have : 6 * m ≤ 4 * n := by omega
                    exact_mod_cast this
                  nlinarith

/-- Key `log a` domination for `a ∈ A'`: `log a ≤ 2 * ∑_{d ∣ a, a/d ∈ A'} Λ(d)`. -/
private lemma log_le_two_sum_vonMangoldt_twoSqCand (a : ℕ) (ha : isTwoSqCand a) :
    Real.log (a : ℝ) ≤
      2 * ∑ d ∈ a.divisors.filter (fun d => isTwoSqCand (a / d)), vonMangoldtReal d := by
  have ha_pos : 0 < a := ha.1
  have hlog : Real.log (a : ℝ) =
      ∑ p ∈ a.primeFactors, (a.factorization p : ℝ) * Real.log (p : ℝ) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self (ne_of_gt ha_pos), Finsupp.prod]
    rw [Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun p _ => by rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      exact_mod_cast pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [hlog]
  let B : ℕ → Finset ℕ := fun p =>
    if p % 4 = 3 then
      (Finset.Icc 1 (a.factorization p / 2)).image (fun j => p ^ (2 * j))
    else
      (Finset.Icc 1 (a.factorization p)).image (fun j => p ^ j)
  have hB_sub : ∀ p ∈ a.primeFactors, B p ⊆ a.divisors.filter (fun d => isTwoSqCand (a / d)) := by
    intro p hp d hd
    have hpr := Nat.prime_of_mem_primeFactors hp
    simp only [Finset.mem_filter, Nat.mem_divisors]
    dsimp [B] at hd
    by_cases hp3 : p % 4 = 3
    · simp only [hp3, ↓reduceIte, Finset.mem_image, Finset.mem_Icc] at hd
      obtain ⟨j, ⟨hj1, hje⟩, rfl⟩ := hd
      have h2j_le : 2 * j ≤ a.factorization p := by omega
      have hdvd : p ^ (2 * j) ∣ a := (hpr.pow_dvd_iff_le_factorization (by omega)).mpr h2j_le
      refine ⟨⟨hdvd, by omega⟩, ⟨Nat.div_pos (Nat.le_of_dvd ha_pos hdvd) (pow_pos hpr.pos _),
        fun q hq hq3 => ?_⟩⟩
      rw [Nat.factorization_div hdvd, Finsupp.tsub_apply, hpr.factorization_pow]
      by_cases hqp : q = p
      · subst hqp
        simp only [Finsupp.single_eq_same]
        obtain ⟨r, hr⟩ := ha.2 q hq hq3
        refine ⟨r - j, ?_⟩; omega
      · rw [Finsupp.single_eq_of_ne hqp, Nat.sub_zero]
        exact ha.2 q hq hq3
    · simp only [hp3, ↓reduceIte, Finset.mem_image, Finset.mem_Icc] at hd
      obtain ⟨j, ⟨hj1, hje⟩, rfl⟩ := hd
      have hdvd : p ^ j ∣ a := (hpr.pow_dvd_iff_le_factorization (by omega)).mpr hje
      refine ⟨⟨hdvd, by omega⟩, ⟨Nat.div_pos (Nat.le_of_dvd ha_pos hdvd) (pow_pos hpr.pos _),
        fun q hq hq3 => ?_⟩⟩
      rw [Nat.factorization_div hdvd, Finsupp.tsub_apply, hpr.factorization_pow]
      have hqp : q ≠ p := fun h => hp3 (h ▸ hq3)
      rw [Finsupp.single_eq_of_ne hqp, Nat.sub_zero]
      exact ha.2 q hq hq3
  have hB_disj : Set.PairwiseDisjoint (a.primeFactors : Set ℕ) B := by
    intro p1 hp1 p2 hp2 hne
    have hpr1 := Nat.prime_of_mem_primeFactors hp1
    have hpr2 := Nat.prime_of_mem_primeFactors hp2
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    have hmin1 : d.minFac = p1 := by
      dsimp [B] at hd1; split_ifs at hd1 <;>
      · simp only [Finset.mem_image, Finset.mem_Icc] at hd1
        obtain ⟨j, ⟨hj1, _⟩, rfl⟩ := hd1
        exact minFac_prime_pow hpr1 (by omega)
    have hmin2 : d.minFac = p2 := by
      dsimp [B] at hd2; split_ifs at hd2 <;>
      · simp only [Finset.mem_image, Finset.mem_Icc] at hd2
        obtain ⟨j, ⟨hj1, _⟩, rfl⟩ := hd2
        exact minFac_prime_pow hpr2 (by omega)
    exact hne (hmin1.symm.trans hmin2)
  have hB_sum : ∀ p ∈ a.primeFactors,
      (a.factorization p : ℝ) * Real.log (p : ℝ) ≤ 2 * ∑ d ∈ B p, vonMangoldtReal d := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpr.one_le)
    dsimp [B]
    by_cases hp3 : p % 4 = 3
    · simp only [hp3, ↓reduceIte]
      have hinj : Set.InjOn (fun j => p ^ (2 * j)) (Finset.Icc 1 (a.factorization p / 2) : Set ℕ) := by
        intro j1 _ j2 _ heq
        have := Nat.pow_right_injective hpr.two_le heq; omega
      rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
      have hcongr : ∑ j ∈ Finset.Icc 1 (a.factorization p / 2), vonMangoldtReal (p ^ (2 * j)) =
          ∑ _j ∈ Finset.Icc 1 (a.factorization p / 2), Real.log (p : ℝ) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        exact vonMangoldtReal_prime_pow hpr (by have := (Finset.mem_Icc.mp hj).1; omega)
      rw [hcongr, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      obtain ⟨r, hr⟩ := ha.2 p hpr hp3
      have hhalf : a.factorization p / 2 = r := by omega
      have hcast : (a.factorization p : ℝ) = 2 * (r : ℝ) := by
        have : a.factorization p = 2 * r := by omega
        exact_mod_cast this
      rw [hhalf, hcast]; ring_nf; exact le_rfl
    · simp only [hp3, ↓reduceIte]
      have hinj : Set.InjOn (fun j => p ^ j) (Finset.Icc 1 (a.factorization p) : Set ℕ) := by
        intro j1 _ j2 _ heq; exact Nat.pow_right_injective hpr.two_le heq
      rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
      have hcongr : ∑ j ∈ Finset.Icc 1 (a.factorization p), vonMangoldtReal (p ^ j) =
          ∑ _j ∈ Finset.Icc 1 (a.factorization p), Real.log (p : ℝ) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        exact vonMangoldtReal_prime_pow hpr (Finset.mem_Icc.mp hj).1
      rw [hcongr, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      nlinarith
  calc ∑ p ∈ a.primeFactors, (a.factorization p : ℝ) * Real.log (p : ℝ)
      ≤ ∑ p ∈ a.primeFactors, 2 * ∑ d ∈ B p, vonMangoldtReal d := Finset.sum_le_sum hB_sum
    _ = 2 * ∑ p ∈ a.primeFactors, ∑ d ∈ B p, vonMangoldtReal d := by rw [← Finset.mul_sum]
    _ = 2 * ∑ d ∈ a.primeFactors.biUnion B, vonMangoldtReal d := by
        rw [Finset.sum_biUnion hB_disj]
    _ ≤ 2 * ∑ d ∈ a.divisors.filter (fun d => isTwoSqCand (a / d)), vonMangoldtReal d := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => vonMangoldtReal_nonneg d)
        intro d hd
        obtain ⟨p, hp, hdp⟩ := Finset.mem_biUnion.mp hd
        exact hB_sub p hp hdp

/-- **Landau (1908) / Erdős (1946) Sums-of-Two-Squares Upper Bound**:
For every integer `N ≥ 3`, the number of integers `1 ≤ k ≤ N` expressible as `x² + y²` satisfies
`|{1 ≤ k ≤ N : ∃ x y, k = x² + y²}| ≤ 70 * N / √(log N)`.
Pure Mathlib signature (`0` custom definitions). -/
theorem ppl071_sum_two_squares_count_upper (N : ℕ) (hN : 3 ≤ N) :
    (((Finset.Icc 1 N).filter (fun k => ∃ x y : ℕ, k = x ^ 2 + y ^ 2)).card : ℝ) ≤
      70 * (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
  set S := (Finset.Icc 1 N).filter isTwoSqCand
  have hsub_S : (Finset.Icc 1 N).filter (fun k => ∃ x y : ℕ, k = x ^ 2 + y ^ 2) ⊆ S := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc, S] at hk ⊢
    obtain ⟨x, y, hxy⟩ := hk.2
    exact ⟨hk.1, isTwoSqCand_of_sq_add_sq hk.1.1 hxy⟩
  have hcard_le : (((Finset.Icc 1 N).filter (fun k => ∃ x y : ℕ, k = x ^ 2 + y ^ 2)).card : ℝ) ≤
      (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub_S
  refine le_trans hcard_le ?_
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogN_ge1 : 1 ≤ Real.log (N : ℝ) := by
    have h3 : Real.exp 1 ≤ (N : ℝ) := by
      have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have h3N : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have := Real.log_le_log (Real.exp_pos 1) h3
    rwa [Real.log_exp] at this
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hsqrt_pos : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hlogN_pos
  have hlog_sum_upper : ∑ a ∈ S, Real.log (a : ℝ) ≤
      8 * Real.log 2 * (N : ℝ) * Real.sqrt (8 * Real.log (N : ℝ) + 4) := by
    have hstep1 : ∑ a ∈ S, Real.log (a : ℝ) ≤
        2 * ∑ a ∈ S, ∑ d ∈ a.divisors.filter (fun d => isTwoSqCand (a / d)), vonMangoldtReal d := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a ha => ?_
      exact log_le_two_sum_vonMangoldt_twoSqCand a (Finset.mem_filter.mp ha).2
    have hswap : ∑ a ∈ S, ∑ d ∈ a.divisors.filter (fun d => isTwoSqCand (a / d)), vonMangoldtReal d ≤
        ∑ b ∈ S, ∑ d ∈ Finset.Icc 1 (N / b), vonMangoldtReal d := by
      rw [Finset.sum_sigma', Finset.sum_sigma']
      refine sum_le_sum_of_inj_nonneg
        (S.sigma fun a => a.divisors.filter (fun d => isTwoSqCand (a / d)))
        (S.sigma fun b => Finset.Icc 1 (N / b))
        (fun s => vonMangoldtReal s.2) (fun s => vonMangoldtReal s.2)
        (fun s : Σ _ : ℕ, ℕ => (⟨s.1 / s.2, s.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
      · intro s hs
        simp only [Finset.mem_sigma, S, Finset.mem_filter, Finset.mem_Icc,
          Nat.mem_divisors] at hs ⊢
        have hd_pos : 1 ≤ s.2 := Nat.pos_of_dvd_of_pos hs.2.1.1 (by omega)
        have hb_pos : 1 ≤ s.1 / s.2 := hs.2.2.1
        have hb_le : s.1 / s.2 ≤ N := le_trans (Nat.div_le_self s.1 s.2) hs.1.1.2
        have hmul : s.2 * (s.1 / s.2) = s.1 := Nat.mul_div_cancel' hs.2.1.1
        have hd_le : s.2 ≤ N / (s.1 / s.2) :=
          (Nat.le_div_iff_mul_le (by omega : 0 < s.1 / s.2)).mpr (by omega)
        exact ⟨⟨⟨hb_pos, hb_le⟩, hs.2.2⟩, ⟨hd_pos, hd_le⟩⟩
      · intro s1 hs1 s2 hs2 heq
        simp only [Finset.mem_coe, Finset.mem_sigma, S, Finset.mem_filter, Finset.mem_Icc,
          Nat.mem_divisors] at hs1 hs2
        have hq : s1.1 / s1.2 = s2.1 / s2.2 := congrArg Sigma.fst heq
        have hd : s1.2 = s2.2 := by simpa using eq_of_heq (Sigma.mk.inj_iff.mp heq).2
        have ha : s1.1 = s2.1 := by
          rw [← Nat.mul_div_cancel' hs1.2.1.1, ← Nat.mul_div_cancel' hs2.2.1.1, hq, hd]
        exact Sigma.ext ha (heq_of_eq hd)
      · intro _ _; exact vonMangoldtReal_nonneg _
      · intro _ _; exact le_rfl
    have hcheb : ∑ b ∈ S, ∑ d ∈ Finset.Icc 1 (N / b), vonMangoldtReal d ≤
        4 * Real.log 2 * (N : ℝ) * ∑ b ∈ S, (1 : ℝ) / (b : ℝ) := by
      calc ∑ b ∈ S, ∑ d ∈ Finset.Icc 1 (N / b), vonMangoldtReal d
          ≤ ∑ b ∈ S, 4 * Real.log 2 * ((N / b : ℕ) : ℝ) :=
            Finset.sum_le_sum fun b _ => chebyshev_psi_le (N / b)
        _ ≤ ∑ b ∈ S, 4 * Real.log 2 * ((N : ℝ) / (b : ℝ)) := by
            refine Finset.sum_le_sum fun b hb => ?_
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have hb_pos : (0 : ℝ) < (b : ℝ) := by
              have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1; positivity
            rw [le_div_iff₀ hb_pos]
            exact_mod_cast Nat.div_mul_le_self N b
        _ = 4 * Real.log 2 * (N : ℝ) * ∑ b ∈ S, (1 : ℝ) / (b : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => by ring
    have hhar := sum_inv_twoSqCand_le N (by omega)
    have hcoeff : 0 ≤ 8 * Real.log 2 * (N : ℝ) := by
      have : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    calc ∑ a ∈ S, Real.log (a : ℝ)
        ≤ 2 * (4 * Real.log 2 * (N : ℝ) * ∑ b ∈ S, (1 : ℝ) / (b : ℝ)) := by linarith
      _ = 8 * Real.log 2 * (N : ℝ) * ∑ b ∈ S, (1 : ℝ) / (b : ℝ) := by ring
      _ ≤ 8 * Real.log 2 * (N : ℝ) * Real.sqrt (8 * Real.log (N : ℝ) + 4) :=
          mul_le_mul_of_nonneg_left hhar hcoeff
  set S_lo : Finset ℕ := S.filter (fun a : ℕ => (a : ℝ) ≤ Real.sqrt (N : ℝ))
  set S_hi : Finset ℕ := S.filter (fun a : ℕ => Real.sqrt (N : ℝ) < (a : ℝ))
  have hS_card : S.card = S_lo.card + S_hi.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext a; simp only [S_lo, S_hi, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro ha; rcases le_or_gt (a : ℝ) (Real.sqrt (N : ℝ)) with h | h
        · exact Or.inl ⟨ha, h⟩
        · exact Or.inr ⟨ha, h⟩
      · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
    · rw [Finset.disjoint_left]; intro a h1 h2
      simp only [S_lo, S_hi, Finset.mem_filter] at h1 h2; linarith
  have hlo_card : (S_lo.card : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hsub : S_lo ⊆ Finset.Icc 1 (Nat.floor (Real.sqrt (N : ℝ))) := by
      intro a ha
      simp only [S_lo, S, Finset.mem_filter, Finset.mem_Icc] at ha ⊢
      exact ⟨ha.1.1.1, Nat.le_floor ha.2⟩
    have hc : S_lo.card ≤ Nat.floor (Real.sqrt (N : ℝ)) := by
      have := Finset.card_le_card hsub
      rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact le_trans (by exact_mod_cast hc) (Nat.floor_le (Real.sqrt_nonneg _))
  have hhi_bound : (S_hi.card : ℝ) * ((1 / 2 : ℝ) * Real.log (N : ℝ)) ≤ ∑ a ∈ S, Real.log (a : ℝ) := by
    calc (S_hi.card : ℝ) * ((1 / 2 : ℝ) * Real.log (N : ℝ))
        = ∑ _a ∈ S_hi, ((1 / 2 : ℝ) * Real.log (N : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ a ∈ S_hi, Real.log (a : ℝ) := by
          refine Finset.sum_le_sum fun a ha => ?_
          have hgt := (Finset.mem_filter.mp ha).2
          have h1 := Real.log_le_log (Real.sqrt_pos.mpr hN_pos) (le_of_lt hgt)
          rw [Real.log_sqrt (le_of_lt hN_pos)] at h1; linarith
      _ ≤ ∑ a ∈ S, Real.log (a : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun a ha _ => ?_
          have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
          exact Real.log_nonneg (by exact_mod_cast ha1)
  have hsqrt_12 : Real.sqrt (8 * Real.log (N : ℝ) + 4) ≤ 4 * Real.sqrt (Real.log (N : ℝ)) := by
    have h1 : 8 * Real.log (N : ℝ) + 4 ≤ 16 * Real.log (N : ℝ) := by linarith
    calc Real.sqrt (8 * Real.log (N : ℝ) + 4)
        ≤ Real.sqrt (16 * Real.log (N : ℝ)) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt 16 * Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_mul (by norm_num) _
      _ = 4 * Real.sqrt (Real.log (N : ℝ)) := by
          have : Real.sqrt 16 = 4 := by
            rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          rw [this]
  have hlog2_le : Real.log 2 ≤ 1 := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have := Real.log_le_log (by norm_num) h2e
    rwa [Real.log_exp] at this
  have hhi_le : (S_hi.card : ℝ) ≤ 64 * (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
    have h1 : (S_hi.card : ℝ) * Real.log (N : ℝ) ≤
        64 * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) := by
      have h2 : 8 * Real.log 2 * (N : ℝ) * Real.sqrt (8 * Real.log (N : ℝ) + 4) ≤
          32 * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) := by
        have ha : 8 * Real.log 2 * (N : ℝ) ≤ 8 * (N : ℝ) := by nlinarith
        have hb : 0 ≤ 8 * Real.log 2 * (N : ℝ) := by positivity
        calc 8 * Real.log 2 * (N : ℝ) * Real.sqrt (8 * Real.log (N : ℝ) + 4)
            ≤ 8 * Real.log 2 * (N : ℝ) * (4 * Real.sqrt (Real.log (N : ℝ))) :=
              mul_le_mul_of_nonneg_left hsqrt_12 hb
          _ ≤ 8 * (N : ℝ) * (4 * Real.sqrt (Real.log (N : ℝ))) :=
              mul_le_mul_of_nonneg_right ha (by positivity)
          _ = 32 * (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) := by ring
      linarith
    rw [le_div_iff₀ hsqrt_pos]
    have hsq : Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (N : ℝ)) = Real.log (N : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hlogN_pos)
    nlinarith
  have hlo_le : (S_lo.card : ℝ) ≤ (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
    rw [le_div_iff₀ hsqrt_pos]
    have hlog_le_N : Real.log (N : ℝ) ≤ (N : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hN_pos]
    have hsq : Real.sqrt (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤ (N : ℝ) := by
      calc Real.sqrt (N : ℝ) * Real.sqrt (Real.log (N : ℝ))
          ≤ Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlog_le_N) (Real.sqrt_nonneg _)
        _ = (N : ℝ) := Real.mul_self_sqrt (le_of_lt hN_pos)
    nlinarith
  have hS_cast : (S.card : ℝ) = (S_lo.card : ℝ) + (S_hi.card : ℝ) := by exact_mod_cast hS_card
  rw [hS_cast]
  have hpos_rhs : 0 ≤ (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by positivity
  have h65 : (S_lo.card : ℝ) + (S_hi.card : ℝ) ≤
      65 * ((N : ℝ) / Real.sqrt (Real.log (N : ℝ))) := by
    have hhi' : (S_hi.card : ℝ) ≤ 64 * ((N : ℝ) / Real.sqrt (Real.log (N : ℝ))) := by
      linarith [show 64 * (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) =
        64 * ((N : ℝ) / Real.sqrt (Real.log (N : ℝ))) by ring]
    linarith
  have h70 : 65 * ((N : ℝ) / Real.sqrt (Real.log (N : ℝ))) ≤
      70 * (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
    have heq : 70 * (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) =
        70 * ((N : ℝ) / Real.sqrt (Real.log (N : ℝ))) := by ring
    linarith
  exact le_trans h65 h70

/-- **Erdős (1946) `m × m` Integer-Grid `O(n / √(log n))` Upper Bound**:
For every `m ≥ 3`, the explicit `m × m` integer grid `G_m ⊂ ℝ²` has `|G_m| = m²` points and
determines at most `200 * |G_m| / √(log |G_m|)` distinct positive distances.
Pure Mathlib signature (`0` custom definitions). -/
theorem ppl071_erdos_1946_grid_upper (m : ℕ) (hm : 3 ≤ m) :
    let G : Finset (EuclideanSpace ℝ (Fin 2)) :=
      ((Finset.range m) ×ˢ (Finset.range m)).image
        (fun ab => WithLp.toLp 2 ![(ab.1 : ℝ), (ab.2 : ℝ)])
    G.card = m ^ 2 ∧
    ((((G ×ˢ G).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)).card : ℝ) ≤
      200 * (G.card : ℝ) / Real.sqrt (Real.log (G.card : ℝ)) := by
  intro G
  have hinj : Set.InjOn (fun ab : ℕ × ℕ => WithLp.toLp 2 ![(ab.1 : ℝ), (ab.2 : ℝ)])
      ((Finset.range m ×ˢ Finset.range m : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro p1 _ p2 _ heq
    have h0 : (p1.1 : ℝ) = (p2.1 : ℝ) := by
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) heq; simpa using this
    have h1 : (p1.2 : ℝ) = (p2.2 : ℝ) := by
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) heq; simpa using this
    exact Prod.ext (by exact_mod_cast h0) (by exact_mod_cast h1)
  have hGcard : G.card = m ^ 2 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range, sq]
  refine ⟨hGcard, ?_⟩
  set N := 2 * m ^ 2
  set S2 := (Finset.Icc 1 N).filter (fun k => ∃ x y : ℕ, k = x ^ 2 + y ^ 2)
  set D := ((G ×ˢ G).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)
  have hD_sub : D ⊆ S2.image (fun k : ℕ => Real.sqrt (k : ℝ)) := by
    intro d hd
    simp only [D, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hd
    obtain ⟨⟨p, q⟩, ⟨⟨hpG, hqG⟩, hpq⟩, rfl⟩ := hd
    simp only [G, Finset.mem_image, Finset.mem_product, Finset.mem_range] at hpG hqG
    obtain ⟨⟨a1, b1⟩, ⟨ha1, hb1⟩, rfl⟩ := hpG
    obtain ⟨⟨a2, b2⟩, ⟨ha2, hb2⟩, rfl⟩ := hqG
    set dx : ℕ := if a1 ≥ a2 then a1 - a2 else a2 - a1
    set dy : ℕ := if b1 ≥ b2 then b1 - b2 else b2 - b1
    have hdx_sq : ((a1 : ℝ) - (a2 : ℝ)) ^ 2 = (dx : ℝ) ^ 2 := by
      dsimp [dx]; split_ifs with h
      · rw [Nat.cast_sub h]
      · push Not at h; rw [Nat.cast_sub (le_of_lt h)]; ring
    have hdy_sq : ((b1 : ℝ) - (b2 : ℝ)) ^ 2 = (dy : ℝ) ^ 2 := by
      dsimp [dy]; split_ifs with h
      · rw [Nat.cast_sub h]
      · push Not at h; rw [Nat.cast_sub (le_of_lt h)]; ring
    have hdsq : dist (WithLp.toLp 2 ![(a1 : ℝ), (b1 : ℝ)]) (WithLp.toLp 2 ![(a2 : ℝ), (b2 : ℝ)]) ^ 2 =
        ((dx ^ 2 + dy ^ 2 : ℕ) : ℝ) := by
      rw [dist_sq_eq_euc2]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hdx_sq, hdy_sq]; push_cast; ring
    have hd_eq : dist (WithLp.toLp 2 ![(a1 : ℝ), (b1 : ℝ)]) (WithLp.toLp 2 ![(a2 : ℝ), (b2 : ℝ)]) =
        Real.sqrt ((dx ^ 2 + dy ^ 2 : ℕ) : ℝ) := by
      rw [← hdsq, Real.sqrt_sq dist_nonneg]
    have hk_pos : 1 ≤ dx ^ 2 + dy ^ 2 := by
      by_contra h0; push Not at h0
      have hdx0 : dx = 0 := by nlinarith
      have hdy0 : dy = 0 := by nlinarith
      have ha_eq : a1 = a2 := by dsimp [dx] at hdx0; split_ifs at hdx0 <;> omega
      have hb_eq : b1 = b2 := by dsimp [dy] at hdy0; split_ifs at hdy0 <;> omega
      exact hpq (by rw [ha_eq, hb_eq])
    have hk_le : dx ^ 2 + dy ^ 2 ≤ N := by
      have h1 : dx ≤ m := by dsimp [dx]; split_ifs <;> omega
      have h2 : dy ≤ m := by dsimp [dy]; split_ifs <;> omega
      dsimp [N]; nlinarith
    exact Finset.mem_image.mpr ⟨dx ^ 2 + dy ^ 2,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk_pos, hk_le⟩, ⟨dx, dy, rfl⟩⟩, hd_eq.symm⟩
  have hD_le : (D.card : ℝ) ≤ (S2.card : ℝ) := by
    exact_mod_cast le_trans (Finset.card_le_card hD_sub) Finset.card_image_le
  have hS2 := ppl071_sum_two_squares_count_upper N (by dsimp [N]; nlinarith)
  rw [hGcard]
  have hm2_pos : (0 : ℝ) < ((m ^ 2 : ℕ) : ℝ) := by positivity
  have hlog_m2 : 0 < Real.log ((m ^ 2 : ℕ) : ℝ) := by
    apply Real.log_pos; exact_mod_cast (by nlinarith : 1 < m ^ 2)
  have hlog_le : Real.log ((m ^ 2 : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
    apply Real.log_le_log hm2_pos; exact_mod_cast (by dsimp [N]; omega : m ^ 2 ≤ N)
  have hsqrt_le : Real.sqrt (Real.log ((m ^ 2 : ℕ) : ℝ)) ≤ Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_le_sqrt hlog_le
  have hN_cast : (N : ℝ) = 2 * ((m ^ 2 : ℕ) : ℝ) := by dsimp [N]; push_cast; ring
  calc (D.card : ℝ)
      ≤ 70 * (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := le_trans hD_le hS2
    _ ≤ 70 * (N : ℝ) / Real.sqrt (Real.log ((m ^ 2 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hlog_m2) hsqrt_le
    _ = 140 * ((m ^ 2 : ℕ) : ℝ) / Real.sqrt (Real.log ((m ^ 2 : ℕ) : ℝ)) := by rw [hN_cast]; ring
    _ ≤ 200 * ((m ^ 2 : ℕ) : ℝ) / Real.sqrt (Real.log ((m ^ 2 : ℕ) : ℝ)) := by
        have hnn : 0 ≤ ((m ^ 2 : ℕ) : ℝ) / Real.sqrt (Real.log ((m ^ 2 : ℕ) : ℝ)) := by positivity
        have h140 : 140 * ((m ^ 2 : ℕ) : ℝ) / Real.sqrt (Real.log ((m ^ 2 : ℕ) : ℝ)) =
            140 * (((m ^ 2 : ℕ) : ℝ) / Real.sqrt (Real.log ((m ^ 2 : ℕ) : ℝ))) := by ring
        have h200 : 200 * ((m ^ 2 : ℕ) : ℝ) / Real.sqrt (Real.log ((m ^ 2 : ℕ) : ℝ)) =
            200 * (((m ^ 2 : ℕ) : ℝ) / Real.sqrt (Real.log ((m ^ 2 : ℕ) : ℝ))) := by ring
        linarith

/-- **Erdős (1946) Upper Bound for ALL `n ≥ 4`**:
For EVERY integer `n ≥ 4`, there exists a set `P ⊂ ℝ²` of exact cardinality `n` determining at
most `600 * n / √(log n)` distinct positive distances. Pure Mathlib signature. -/
theorem ppl071_erdos_1946_grid_all_n (n : ℕ) (hn : 4 ≤ n) :
    ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧
      ((((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)).card : ℝ) ≤
        600 * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by
  set s := Nat.sqrt (n - 1)
  set m := max 3 (s + 1)
  have hm3 : 3 ≤ m := le_max_left 3 (s + 1)
  have hn_le_m2 : n ≤ m ^ 2 := by
    have hlt : n - 1 < (s + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt (n - 1)
    have hle : s + 1 ≤ m := le_max_right 3 (s + 1)
    have hsq : (s + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hle 2
    omega
  have hm2_le_3n : m ^ 2 ≤ 3 * n := by
    by_cases h : s + 1 ≤ 3
    · have hm_eq : m = 3 := max_eq_left h
      rw [hm_eq]; omega
    · push Not at h
      have hm_eq : m = s + 1 := max_eq_right (by omega)
      rw [hm_eq]
      have hs2 : s ^ 2 ≤ n := by
        have : s * s ≤ n - 1 := Nat.sqrt_le (n - 1)
        rw [sq]; omega
      nlinarith
  set G : Finset (EuclideanSpace ℝ (Fin 2)) :=
    ((Finset.range m) ×ˢ (Finset.range m)).image
      (fun ab => WithLp.toLp 2 ![(ab.1 : ℝ), (ab.2 : ℝ)])
  obtain ⟨hGcard, hGdist⟩ := ppl071_erdos_1946_grid_upper m hm3
  obtain ⟨P, hPG, hPcard⟩ := Finset.exists_subset_card_eq (hGcard.symm ▸ hn_le_m2)
  refine ⟨P, hPcard, ?_⟩
  have hD_sub : ((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2) ⊆
      ((G ×ˢ G).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2) := by
    intro d hd
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hd ⊢
    obtain ⟨pq, ⟨⟨h1, h2⟩, hne⟩, rfl⟩ := hd
    exact ⟨pq, ⟨⟨hPG h1, hPG h2⟩, hne⟩, rfl⟩
  have hD_le : ((((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)).card : ℝ) ≤
      ((((G ×ˢ G).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hD_sub
  rw [hGcard] at hGdist
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlog_le : Real.log (n : ℝ) ≤ Real.log ((m ^ 2 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hn_le_m2)
  have hsqrt_le : Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log ((m ^ 2 : ℕ) : ℝ)) :=
    Real.sqrt_le_sqrt hlog_le
  have hm2_real : ((m ^ 2 : ℕ) : ℝ) ≤ 3 * (n : ℝ) := by exact_mod_cast hm2_le_3n
  calc ((((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)).card : ℝ)
      ≤ 200 * ((m ^ 2 : ℕ) : ℝ) / Real.sqrt (Real.log ((m ^ 2 : ℕ) : ℝ)) := le_trans hD_le hGdist
    _ ≤ 200 * ((m ^ 2 : ℕ) : ℝ) / Real.sqrt (Real.log (n : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hlogn_pos) hsqrt_le
    _ ≤ 200 * (3 * (n : ℝ)) / Real.sqrt (Real.log (n : ℝ)) :=
        div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    _ = 600 * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by ring

/-! ### Section 3: Guth–Katz Quadruple-Energy Cauchy–Schwarz Barrier -/

/-- **Elekes–Sharir / Guth–Katz Cauchy–Schwarz Reduction**:
For EVERY finite set `P ⊂ ℝ²`, letting `D(P)` be the set of positive distances and
`Q(P) = |{(p,q,r,s) ∈ P⁴ : dist p q = dist r s ∧ p ≠ q}|` be the distance quadruple energy,
we have `(|P| * (|P| - 1))² ≤ |D(P)| · Q(P)`. Pure Mathlib signature (`0` custom defs). -/
theorem ppl071_elekes_sharir_cauchy_schwarz
    (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    (((P.card * (P.card - 1)) : ℕ) : ℝ) ^ 2 ≤
      ((((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)).card : ℝ) *
      ((((P ×ˢ P) ×ˢ (P ×ˢ P)).filter
        (fun x => dist x.1.1 x.1.2 = dist x.2.1 x.2.2 ∧ x.1.1 ≠ x.1.2)).card : ℝ) := by
  set E := (P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2)
  set D := E.image (fun pq => dist pq.1 pq.2)
  set Q := ((P ×ˢ P) ×ˢ (P ×ˢ P)).filter
    (fun x => dist x.1.1 x.1.2 = dist x.2.1 x.2.2 ∧ x.1.1 ≠ x.1.2)
  let m : ℝ → ℕ := fun d => (E.filter (fun pq => dist pq.1 pq.2 = d)).card
  have hsum_m : ∑ d ∈ D, m d = P.card * (P.card - 1) := by
    rw [← card_off_diag P]
    dsimp [m]
    rw [← Finset.card_biUnion]
    · congr 1; ext pq
      simp only [Finset.mem_biUnion, Finset.mem_filter, D, Finset.mem_image]
      constructor
      · rintro ⟨_, _, hpq, _⟩; exact Finset.mem_filter.mp hpq
      · intro hpq
        have hpqE : pq ∈ E := Finset.mem_filter.mpr hpq
        exact ⟨dist pq.1 pq.2, ⟨pq, hpqE, rfl⟩, hpqE, rfl⟩
    · intro d1 _ d2 _ hne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]; intro pq h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  have hsum_m2 : ∑ d ∈ D, (m d) ^ 2 = Q.card := by
    have hcard_d : ∀ d ∈ D, (m d) ^ 2 =
        ((E.filter (fun pq => dist pq.1 pq.2 = d)) ×ˢ
          (E.filter (fun rs => dist rs.1 rs.2 = d))).card := by
      intro d _; rw [Finset.card_product, sq]
    rw [Finset.sum_congr rfl hcard_d, ← Finset.card_biUnion]
    · congr 1; ext x
      simp only [Finset.mem_biUnion, Finset.mem_product, Finset.mem_filter, D, Finset.mem_image, Q, E]
      constructor
      · rintro ⟨d, _, ⟨⟨h1, hne1⟩, hd1⟩, ⟨⟨h2, _⟩, hd2⟩⟩
        exact ⟨⟨h1, h2⟩, hd1.trans hd2.symm, hne1⟩
      · rintro ⟨⟨h1, h2⟩, hdeq, hne1⟩
        have hne2 : x.2.1 ≠ x.2.2 := by
          intro heq
          have hd0 : dist x.1.1 x.1.2 = 0 := by rw [hdeq, heq, dist_self]
          exact hne1 (dist_eq_zero.mp hd0)
        exact ⟨dist x.1.1 x.1.2, ⟨x.1, ⟨h1, hne1⟩, rfl⟩, ⟨⟨h1, hne1⟩, rfl⟩, ⟨⟨h2, hne2⟩, hdeq.symm⟩⟩
    · intro d1 _ d2 _ hne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]; intro x h1 h2
      simp only [Finset.mem_product, Finset.mem_filter] at h1 h2
      exact hne (h1.1.2.symm.trans h2.1.2)
  have hcs := sq_sum_le_card_mul_sum_sq_nat D m
  rw [hsum_m, hsum_m2] at hcs
  exact_mod_cast hcs

/-- Elementary totient reciprocal sum lower bound:
`∑_{d=1}^R φ(d) / d² ≥ (1/2) * Real.log (R + 1)` for all `R : ℕ` (via `Nat.sum_totient`). -/
private lemma sum_totient_div_sq_ge (R : ℕ) :
    (1 / 2 : ℝ) * Real.log ((R + 1 : ℕ) : ℝ) ≤
      ∑ d ∈ Finset.Icc 1 R, (Nat.totient d : ℝ) / (d : ℝ) ^ 2 := by
  have hharm := log_succ_le_harmonic R
  have h1 : ∑ n ∈ Finset.Icc 1 R, (1 : ℝ) / (n : ℝ) =
      ∑ d ∈ Finset.Icc 1 R, ((Nat.totient d : ℝ) / (d : ℝ) ^ 2) *
        (∑ q ∈ Finset.Icc 1 (R / d), (1 : ℝ) / (q : ℝ) ^ 2) := by
    have htot : ∀ n ∈ Finset.Icc 1 R, (1 : ℝ) / (n : ℝ) =
        ∑ d ∈ n.divisors, (Nat.totient d : ℝ) / (n : ℝ) ^ 2 := by
      intro n hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := by have := (Finset.mem_Icc.mp hn).1; positivity
      rw [← Finset.sum_div]
      have hs : (∑ d ∈ n.divisors, (Nat.totient d : ℝ)) = (n : ℝ) := by
        exact_mod_cast Nat.sum_totient n
      rw [hs]; field_simp
    rw [Finset.sum_congr rfl htot]
    set P := ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R)).filter (fun p => p.1 * p.2 ≤ R)
    have hlhs : ∑ n ∈ Finset.Icc 1 R, ∑ d ∈ n.divisors, (Nat.totient d : ℝ) / (n : ℝ) ^ 2 =
        ∑ p ∈ P, (Nat.totient p.1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) ^ 2 := by
      rw [Finset.sum_sigma']
      refine (Finset.sum_nbij (fun p : ℕ × ℕ => (⟨p.1 * p.2, p.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_).symm
      · intro p hp
        simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        have hp12 : p.1 * p.2 ≠ 0 := mul_ne_zero (by omega) (by omega)
        simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
        exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hp12, hp.2⟩, ⟨dvd_mul_right p.1 p.2, hp12⟩⟩
      · intro p1 hp1 p2 hp2 heq
        simp only [P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp1 hp2
        have hfst : p1.1 * p1.2 = p2.1 * p2.2 := congrArg Sigma.fst heq
        have hsnd : p1.1 = p2.1 := by simpa using eq_of_heq (Sigma.mk.inj_iff.mp heq).2
        have h2 : p1.2 = p2.2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p1.1) (hsnd ▸ hfst)
        exact Prod.ext hsnd h2
      · intro s hs
        simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hs
        have hd_pos : 1 ≤ s.2 := Nat.pos_of_dvd_of_pos hs.2.1 (by omega)
        have hq_pos : 1 ≤ s.1 / s.2 := Nat.div_pos (Nat.le_of_dvd (by omega) hs.2.1) (by omega)
        have hd_le : s.2 ≤ R := le_trans (Nat.le_of_dvd (by omega) hs.2.1) hs.1.2
        have hq_le : s.1 / s.2 ≤ R := le_trans (Nat.div_le_self s.1 s.2) hs.1.2
        have hmul : s.2 * (s.1 / s.2) = s.1 := Nat.mul_div_cancel' hs.2.1
        refine ⟨(s.2, s.1 / s.2), ?_, ?_⟩
        · simp only [P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
          exact ⟨⟨⟨hd_pos, hd_le⟩, ⟨hq_pos, hq_le⟩⟩, hmul.symm ▸ hs.1.2⟩
        · exact Sigma.ext hmul (heq_of_eq rfl)
      · intro p _; rfl
    have hrhs : ∑ d ∈ Finset.Icc 1 R, ((Nat.totient d : ℝ) / (d : ℝ) ^ 2) *
          (∑ q ∈ Finset.Icc 1 (R / d), (1 : ℝ) / (q : ℝ) ^ 2) =
        ∑ p ∈ P, (Nat.totient p.1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) ^ 2 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_sigma']
      refine (Finset.sum_nbij (fun p : ℕ × ℕ => (⟨p.1, p.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_).symm
      · intro p hp
        simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        simp only [Finset.mem_sigma, Finset.mem_Icc]
        exact ⟨hp.1.1, ⟨hp.1.2.1, (Nat.le_div_iff_mul_le (by omega : 0 < p.1)).mpr (mul_comm p.1 p.2 ▸ hp.2)⟩⟩
      · intro p1 _ p2 _ heq
        have h1 : p1.1 = p2.1 := congrArg Sigma.fst heq
        have h2 : p1.2 = p2.2 := by simpa using eq_of_heq (Sigma.mk.inj_iff.mp heq).2
        exact Prod.ext h1 h2
      · intro s hs
        simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc] at hs
        have hmul : s.1 * s.2 ≤ R :=
          mul_comm s.2 s.1 ▸ (Nat.le_div_iff_mul_le (by omega : 0 < s.1)).mp hs.2.2
        have hq_le : s.2 ≤ R := le_trans (Nat.le_mul_of_pos_left s.2 (by omega)) hmul
        refine ⟨(s.1, s.2), ?_, rfl⟩
        simp only [P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨hs.1, ⟨hs.2.1, hq_le⟩⟩, hmul⟩
      · intro p _; push_cast; ring
    rw [hlhs, hrhs]
  have h2 : ∑ d ∈ Finset.Icc 1 R, ((Nat.totient d : ℝ) / (d : ℝ) ^ 2) *
        (∑ q ∈ Finset.Icc 1 (R / d), (1 : ℝ) / (q : ℝ) ^ 2) ≤
      2 * ∑ d ∈ Finset.Icc 1 R, (Nat.totient d : ℝ) / (d : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d _ => ?_
    have hnn : 0 ≤ (Nat.totient d : ℝ) / (d : ℝ) ^ 2 := by positivity
    calc ((Nat.totient d : ℝ) / (d : ℝ) ^ 2) * (∑ q ∈ Finset.Icc 1 (R / d), (1 : ℝ) / (q : ℝ) ^ 2)
        ≤ ((Nat.totient d : ℝ) / (d : ℝ) ^ 2) * 2 :=
          mul_le_mul_of_nonneg_left (sum_inv_sq_le_two (R / d)) hnn
      _ = 2 * ((Nat.totient d : ℝ) / (d : ℝ) ^ 2) := by ring
  linarith

/-- **Guth–Katz Quadruple-Energy Barrier Theorem on the `m × m` Integer Grid**:
For every `m ≥ 16`, on the explicit `m × m` integer grid `G_m ⊂ ℝ²` (`n = m²` points):
1. The distance quadruple energy satisfies `Q(G_m) ≥ (1 / 65536) * m⁶ * log m`
   (i.e. `Q(G_m) ≥ (1 / 131072) * n³ * log n`).
2. Consequently, the Elekes–Sharir / Guth–Katz Cauchy–Schwarz lower bound satisfies
   `(n(n-1))² / Q(G_m) ≤ 131072 * n / log n`,
   rigorously certifying that the `Q(P)` energy pipeline can NEVER beat `O(n / log n)` to close
   the `√(log n)` gap to Erdős's `$500` conjecture `Ω(n / √(log n))`!
Pure Mathlib signature (`0` custom definitions). -/
theorem ppl071_guth_katz_quadruple_energy_barrier (m : ℕ) (hm : 16 ≤ m) :
    let G : Finset (EuclideanSpace ℝ (Fin 2)) :=
      ((Finset.range m) ×ˢ (Finset.range m)).image
        (fun ab => WithLp.toLp 2 ![(ab.1 : ℝ), (ab.2 : ℝ)])
    let Q := ((G ×ˢ G) ×ˢ (G ×ˢ G)).filter
      (fun x => dist x.1.1 x.1.2 = dist x.2.1 x.2.2 ∧ x.1.1 ≠ x.1.2)
    (1 / 65536 : ℝ) * (m : ℝ) ^ 6 * Real.log (m : ℝ) ≤ (Q.card : ℝ) ∧
    (((G.card * (G.card - 1)) : ℕ) : ℝ) ^ 2 / (Q.card : ℝ) ≤
      131072 * (G.card : ℝ) / Real.log (G.card : ℝ) := by
  intro G Q
  have hinjG : Set.InjOn (fun ab : ℕ × ℕ => WithLp.toLp 2 ![(ab.1 : ℝ), (ab.2 : ℝ)])
      ((Finset.range m ×ˢ Finset.range m : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro p1 _ p2 _ heq
    have h0 : (p1.1 : ℝ) = (p2.1 : ℝ) := by
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) heq; simpa using this
    have h1 : (p1.2 : ℝ) = (p2.2 : ℝ) := by
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) heq; simpa using this
    exact Prod.ext (by exact_mod_cast h0) (by exact_mod_cast h1)
  have hGcard : G.card = m ^ 2 := by
    rw [Finset.card_image_of_injOn hinjG, Finset.card_product, Finset.card_range, sq]
  set L := m / 4
  set R := L / 2
  set K := m / 2
  have hL_ge : 4 ≤ L := by omega
  have hR_ge : 2 ≤ R := by omega
  have hK_ge : 8 ≤ K := by omega
  have h2L_le_K : 2 * L ≤ K := by omega
  have hK_add_2L : K + 2 * L ≤ m := by omega
  let GoodMult : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (Finset.Icc 1 R).biUnion fun r =>
      (((Finset.Icc 1 r).filter (fun p => Nat.Coprime p r)).image (fun p => (r, p))) ×ˢ
      ((Finset.Icc 1 (L / r)) ×ˢ (Finset.Icc 1 (L / r)))
  let Base := ((Finset.range K) ×ˢ (Finset.range K)) ×ˢ ((Finset.range K) ×ˢ (Finset.range K))
  let mkPt : ℕ → ℕ → EuclideanSpace ℝ (Fin 2) :=
    fun x y => WithLp.toLp 2 ![(x : ℝ), (y : ℝ)]
  let embed : (((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) →
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
    fun w =>
      let r := w.1.1.1; let p := w.1.1.2; let g := w.1.2.1; let h := w.1.2.2
      let a := g * p; let b := h * r; let c := g * r; let d := h * p
      let u1 := w.2.1.1; let v1 := w.2.1.2; let u2 := w.2.2.1; let v2 := w.2.2.2
      ((mkPt u1 (v1 + L), mkPt (u1 + a + b) (v1 + L + d - c)),
       (mkPt (u2 + L) v2, mkPt (u2 + L + b - a) (v2 + c + d)))
  have hmem_Good : ∀ t ∈ GoodMult,
      1 ≤ t.1.1 ∧ t.1.1 ≤ R ∧ 1 ≤ t.1.2 ∧ t.1.2 ≤ t.1.1 ∧ Nat.Coprime t.1.2 t.1.1 ∧
      1 ≤ t.2.1 ∧ t.2.1 ≤ L / t.1.1 ∧ 1 ≤ t.2.2 ∧ t.2.2 ≤ L / t.1.1 := by
    intro t ht
    simp only [GoodMult, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_product,
      Finset.mem_image, Finset.mem_filter] at ht
    obtain ⟨r, ⟨hr1, hrR⟩, ⟨⟨p, ⟨⟨hp1, hpr⟩, hcop⟩, hpeq⟩, ⟨hg1, hgr⟩, ⟨hh1, hhr⟩⟩⟩ := ht
    have hr_eq : t.1.1 = r := congrArg Prod.fst hpeq.symm
    have hp_eq : t.1.2 = p := congrArg Prod.snd hpeq.symm
    rw [hr_eq, hp_eq]
    exact ⟨hr1, hrR, hp1, hpr, hcop, hg1, hgr, hh1, hhr⟩
  have hmaps : Set.MapsTo embed ((GoodMult ×ˢ Base : Finset _) : Set _) (Q : Set _) := by
    intro w hw
    simp only [Finset.mem_coe, Finset.mem_product, Base, Finset.mem_range] at hw
    have hg := hmem_Good w.1 hw.1
    obtain ⟨hr1, hrR, hp1, hpr, hcop, hg1, hgr, hh1, hhr⟩ := hg
    obtain ⟨⟨hu1, hv1⟩, ⟨hu2, hv2⟩⟩ := hw.2
    have ha_le : w.1.2.1 * w.1.1.2 ≤ L := le_trans (Nat.mul_le_mul_left _ hpr)
      ((Nat.le_div_iff_mul_le (by omega : 0 < w.1.1.1)).mp hgr)
    have hb_le : w.1.2.2 * w.1.1.1 ≤ L := (Nat.le_div_iff_mul_le (by omega : 0 < w.1.1.1)).mp hhr
    have hc_le : w.1.2.1 * w.1.1.1 ≤ L := (Nat.le_div_iff_mul_le (by omega : 0 < w.1.1.1)).mp hgr
    have hd_le : w.1.2.2 * w.1.1.2 ≤ L := le_trans (Nat.mul_le_mul_left _ hpr)
      ((Nat.le_div_iff_mul_le (by omega : 0 < w.1.1.1)).mp hhr)
    have ha_pos : 1 ≤ w.1.2.1 * w.1.1.2 := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
    have hb_pos : 1 ≤ w.1.2.2 * w.1.1.1 := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
    have hptG : ∀ x y, x < m → y < m → mkPt x y ∈ G := by
      intro x y hx hy
      exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hx, Finset.mem_range.mpr hy⟩, rfl⟩
    simp only [Finset.mem_coe, Q, Finset.mem_filter, Finset.mem_product, embed]
    refine ⟨⟨⟨hptG _ _ (by omega) (by omega), hptG _ _ (by omega) (by omega)⟩,
      ⟨hptG _ _ (by omega) (by omega), hptG _ _ (by omega) (by omega)⟩⟩, ?_, ?_⟩
    · have hsq1 : dist (mkPt w.2.1.1 (w.2.1.2 + L))
          (mkPt (w.2.1.1 + w.1.2.1 * w.1.1.2 + w.1.2.2 * w.1.1.1)
            (w.2.1.2 + L + w.1.2.2 * w.1.1.2 - w.1.2.1 * w.1.1.1)) ^ 2 =
          ((w.1.2.1 * w.1.1.2 : ℕ) + (w.1.2.2 * w.1.1.1 : ℕ) : ℝ) ^ 2 +
          ((w.1.2.2 * w.1.1.2 : ℕ) - (w.1.2.1 * w.1.1.1 : ℕ) : ℝ) ^ 2 := by
        rw [dist_sq_eq_euc2]; simp [mkPt]
        rw [Nat.cast_sub (by omega : w.1.2.1 * w.1.1.1 ≤ w.2.1.2 + L + w.1.2.2 * w.1.1.2)]
        push_cast; ring
      have hsq2 : dist (mkPt (w.2.2.1 + L) w.2.2.2)
          (mkPt (w.2.2.1 + L + w.1.2.2 * w.1.1.1 - w.1.2.1 * w.1.1.2)
            (w.2.2.2 + w.1.2.1 * w.1.1.1 + w.1.2.2 * w.1.1.2)) ^ 2 =
          ((w.1.2.2 * w.1.1.1 : ℕ) - (w.1.2.1 * w.1.1.2 : ℕ) : ℝ) ^ 2 +
          ((w.1.2.1 * w.1.1.1 : ℕ) + (w.1.2.2 * w.1.1.2 : ℕ) : ℝ) ^ 2 := by
        rw [dist_sq_eq_euc2]; simp [mkPt]
        rw [Nat.cast_sub (by omega : w.1.2.1 * w.1.1.2 ≤ w.2.2.1 + L + w.1.2.2 * w.1.1.1)]
        push_cast; ring
      have hsq_eq : dist (mkPt w.2.1.1 (w.2.1.2 + L))
          (mkPt (w.2.1.1 + w.1.2.1 * w.1.1.2 + w.1.2.2 * w.1.1.1)
            (w.2.1.2 + L + w.1.2.2 * w.1.1.2 - w.1.2.1 * w.1.1.1)) ^ 2 =
          dist (mkPt (w.2.2.1 + L) w.2.2.2)
            (mkPt (w.2.2.1 + L + w.1.2.2 * w.1.1.1 - w.1.2.1 * w.1.1.2)
              (w.2.2.2 + w.1.2.1 * w.1.1.1 + w.1.2.2 * w.1.1.2)) ^ 2 := by
        rw [hsq1, hsq2]; push_cast; ring
      nlinarith [dist_nonneg (x := mkPt w.2.1.1 (w.2.1.2 + L))
          (y := mkPt (w.2.1.1 + w.1.2.1 * w.1.1.2 + w.1.2.2 * w.1.1.1)
            (w.2.1.2 + L + w.1.2.2 * w.1.1.2 - w.1.2.1 * w.1.1.1)),
        dist_nonneg (x := mkPt (w.2.2.1 + L) w.2.2.2)
          (y := mkPt (w.2.2.1 + L + w.1.2.2 * w.1.1.1 - w.1.2.1 * w.1.1.2)
            (w.2.2.2 + w.1.2.1 * w.1.1.1 + w.1.2.2 * w.1.1.2))]
    · intro heq
      have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) heq
      simp [mkPt] at h0
      have : w.2.1.1 = w.2.1.1 + w.1.2.1 * w.1.1.2 + w.1.2.2 * w.1.1.1 := by exact_mod_cast h0
      omega
  have hinj_emb : Set.InjOn embed ((GoodMult ×ˢ Base : Finset _) : Set _) := by
    intro w1 hw1 w2 hw2 heq
    simp only [Finset.mem_coe, Finset.mem_product, Base, Finset.mem_range] at hw1 hw2
    have hg1 := hmem_Good w1.1 hw1.1
    have hg2 := hmem_Good w2.1 hw2.1
    have hpt_inj : ∀ x1 y1 x2 y2 : ℕ, mkPt x1 y1 = mkPt x2 y2 → x1 = x2 ∧ y1 = y2 := by
      intro x1 y1 x2 y2 h
      have h0 : (x1 : ℝ) = (x2 : ℝ) := by
        have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h; simpa [mkPt] using this
      have h1 : (y1 : ℝ) = (y2 : ℝ) := by
        have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h; simpa [mkPt] using this
      exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩
    dsimp [embed] at heq
    have hp1 := hpt_inj _ _ _ _ (congrArg (fun z => z.1.1) heq)
    have hq1 := hpt_inj _ _ _ _ (congrArg (fun z => z.1.2) heq)
    have hp2 := hpt_inj _ _ _ _ (congrArg (fun z => z.2.1) heq)
    have hq2 := hpt_inj _ _ _ _ (congrArg (fun z => z.2.2) heq)
    have hu1 : w1.2.1.1 = w2.2.1.1 := hp1.1
    have hv1 : w1.2.1.2 = w2.2.1.2 := by omega
    have hu2 : w1.2.2.1 = w2.2.2.1 := by omega
    have hv2 : w1.2.2.2 = w2.2.2.2 := hp2.2
    set a1 := w1.1.2.1 * w1.1.1.2; set b1 := w1.1.2.2 * w1.1.1.1
    set c1 := w1.1.2.1 * w1.1.1.1; set d1 := w1.1.2.2 * w1.1.1.2
    set a2 := w2.1.2.1 * w2.1.1.2; set b2 := w2.1.2.2 * w2.1.1.1
    set c2 := w2.1.2.1 * w2.1.1.1; set d2 := w2.1.2.2 * w2.1.1.2
    have ha1_le : a1 ≤ L := le_trans (Nat.mul_le_mul_left _ hg1.2.2.2.1)
      ((Nat.le_div_iff_mul_le (by omega : 0 < w1.1.1.1)).mp hg1.2.2.2.2.2.2.1)
    have hc1_le : c1 ≤ L := (Nat.le_div_iff_mul_le (by omega : 0 < w1.1.1.1)).mp hg1.2.2.2.2.2.2.1
    have ha2_le : a2 ≤ L := le_trans (Nat.mul_le_mul_left _ hg2.2.2.2.1)
      ((Nat.le_div_iff_mul_le (by omega : 0 < w2.1.1.1)).mp hg2.2.2.2.2.2.2.1)
    have hc2_le : c2 ≤ L := (Nat.le_div_iff_mul_le (by omega : 0 < w2.1.1.1)).mp hg2.2.2.2.2.2.2.1
    have hab : a1 + b1 = a2 + b2 := by omega
    have hba : L + b1 - a1 = L + b2 - a2 := by omega
    have hcd : c1 + d1 = c2 + d2 := by omega
    have hdc : L + d1 - c1 = L + d2 - c2 := by omega
    have ha_eq : a1 = a2 := by omega
    have hb_eq : b1 = b2 := by omega
    have hc_eq : c1 = c2 := by omega
    have hd_eq : d1 = d2 := by omega
    have hg_eq : w1.1.2.1 = w2.1.2.1 := by
      have h1 : Nat.gcd a1 c1 = w1.1.2.1 := by
        dsimp [a1, c1]; rw [Nat.gcd_mul_left, hg1.2.2.2.2.1.gcd_eq_one, mul_one]
      have h2 : Nat.gcd a2 c2 = w2.1.2.1 := by
        dsimp [a2, c2]; rw [Nat.gcd_mul_left, hg2.2.2.2.2.1.gcd_eq_one, mul_one]
      rw [← h1, ← h2, ha_eq, hc_eq]
    have hp_eq : w1.1.1.2 = w2.1.1.2 := by
      dsimp [a1, a2] at ha_eq; rw [hg_eq] at ha_eq
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < w2.1.2.1) ha_eq
    have hr_eq : w1.1.1.1 = w2.1.1.1 := by
      dsimp [c1, c2] at hc_eq; rw [hg_eq] at hc_eq
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < w2.1.2.1) hc_eq
    have hh_eq : w1.1.2.2 = w2.1.2.2 := by
      dsimp [b1, b2] at hb_eq; rw [hr_eq] at hb_eq
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < w2.1.1.1) hb_eq
    exact Prod.ext
      (Prod.ext (Prod.ext hr_eq hp_eq) (Prod.ext hg_eq hh_eq))
      (Prod.ext (Prod.ext hu1 hv1) (Prod.ext hu2 hv2))
  have hQ_ge_card : GoodMult.card * Base.card ≤ Q.card := by
    rw [← Finset.card_product]
    exact Finset.card_le_card_of_injOn embed hmaps hinj_emb
  have hBase_card : Base.card = K ^ 4 := by
    dsimp [Base]; simp [Finset.card_product]; ring
  have hGood_card : GoodMult.card = ∑ r ∈ Finset.Icc 1 R, Nat.totient r * (L / r) ^ 2 := by
    dsimp [GoodMult]
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.card_product, Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel, ← sq]
      congr 1
      rw [Finset.card_image_of_injOn (fun p1 _ p2 _ h => (Prod.mk.inj h).2)]
      rw [Nat.totient_eq_card_coprime]
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      by_cases hreq1 : r = 1
      · subst hreq1; decide
      · congr 1; ext p
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
        constructor
        · rintro ⟨⟨hp1, hpr⟩, hcop⟩
          have hne : p ≠ r := by
            intro h; subst h; rw [Nat.coprime_self] at hcop; exact hreq1 hcop
          exact ⟨by omega, hcop.symm⟩
        · rintro ⟨hpr, hcop⟩
          have hp_ne0 : p ≠ 0 := by
            intro h; subst h; rw [Nat.coprime_zero_right] at hcop; exact hreq1 hcop
          exact ⟨⟨by omega, by omega⟩, hcop.symm⟩
    · intro r1 _ r2 _ hne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]; intro t h1 h2
      simp only [Finset.mem_product, Finset.mem_image] at h1 h2
      obtain ⟨_, _, heq1⟩ := h1.1
      obtain ⟨_, _, heq2⟩ := h2.1
      have : r1 = r2 := (congrArg Prod.fst heq1).trans (congrArg Prod.fst heq2).symm
      exact hne this
  have hGood_real : (L : ℝ) ^ 2 / 8 * Real.log ((R + 1 : ℕ) : ℝ) ≤ (GoodMult.card : ℝ) := by
    have h1 : ∑ r ∈ Finset.Icc 1 R, (Nat.totient r : ℝ) * ((L : ℝ) / (2 * (r : ℝ))) ^ 2 ≤
        (GoodMult.card : ℝ) := by
      rw [hGood_card]; push_cast
      refine Finset.sum_le_sum fun r hr => ?_
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hrR : r ≤ R := (Finset.mem_Icc.mp hr).2
      have hdiv_ge : (L : ℝ) / (2 * (r : ℝ)) ≤ ((L / r : ℕ) : ℝ) := by
        have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
        rw [div_le_iff₀ (by positivity)]
        have hq_ge : 1 ≤ L / r := Nat.div_pos (by omega : r ≤ L) (by omega)
        have hnat : L ≤ 2 * r * (L / r) := by
          have hrem := Nat.div_add_mod L r
          have hmod : L % r < r := Nat.mod_lt L (by omega)
          have hqr : r ≤ r * (L / r) := Nat.le_mul_of_pos_right r (by omega)
          nlinarith
        have hreal : (L : ℝ) ≤ 2 * (r : ℝ) * ((L / r : ℕ) : ℝ) := by exact_mod_cast hnat
        linarith
      exact pow_le_pow_left₀ (by positivity) hdiv_ge 2
    have h2 : ∑ r ∈ Finset.Icc 1 R, (Nat.totient r : ℝ) * ((L : ℝ) / (2 * (r : ℝ))) ^ 2 =
        ((L : ℝ) ^ 2 / 4) * ∑ r ∈ Finset.Icc 1 R, (Nat.totient r : ℝ) / (r : ℝ) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => by ring
    have htot := sum_totient_div_sq_ge R
    nlinarith
  have hlog_R : (1 / 4 : ℝ) * Real.log (m : ℝ) ≤ Real.log ((R + 1 : ℕ) : ℝ) := by
    have hR4 : (m : ℝ) ≤ ((R + 1 : ℕ) : ℝ) ^ 4 := by
      have hR1 : m ≤ 8 * (R + 1) := by omega
      have hnat : m ≤ (R + 1) ^ 4 := by
        have h3 : 3 ≤ R + 1 := by omega
        have h1 : 27 ≤ (R + 1) ^ 3 := by exact Nat.pow_le_pow_left h3 3
        have h2 : 8 * (R + 1) ≤ (R + 1) ^ 4 := by
          have : (R + 1) ^ 4 = (R + 1) ^ 3 * (R + 1) := by ring
          nlinarith
        omega
      exact_mod_cast hnat
    have h1 := Real.log_le_log (by positivity : (0 : ℝ) < (m : ℝ)) hR4
    rw [Real.log_pow] at h1; push_cast at h1 ⊢; linarith
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hQ_lower : (1 / 65536 : ℝ) * (m : ℝ) ^ 6 * Real.log (m : ℝ) ≤ (Q.card : ℝ) := by
    have hQ1 : (GoodMult.card : ℝ) * (Base.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hQ_ge_card
    rw [hBase_card] at hQ1
    push_cast at hQ1
    have hK_sharp : (7 / 16 : ℝ) * (m : ℝ) ≤ (K : ℝ) := by
      have : 7 * m ≤ 16 * K := by omega
      have hreal : 7 * (m : ℝ) ≤ 16 * (K : ℝ) := by exact_mod_cast this
      linarith
    have hL_sharp : (3 / 16 : ℝ) * (m : ℝ) ≤ (L : ℝ) := by
      have : 3 * m ≤ 16 * L := by omega
      have hreal : 3 * (m : ℝ) ≤ 16 * (L : ℝ) := by exact_mod_cast this
      linarith
    have hK4s : ((7 / 16 : ℝ) * (m : ℝ)) ^ 4 ≤ (K : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hK_sharp 4
    have hL2s : ((3 / 16 : ℝ) * (m : ℝ)) ^ 2 ≤ (L : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hL_sharp 2
    have hGs : (((3 / 16 : ℝ) * (m : ℝ)) ^ 2 / 8) * ((1 / 4 : ℝ) * Real.log (m : ℝ)) ≤
        (GoodMult.card : ℝ) := by
      have hstep : (((3 / 16 : ℝ) * (m : ℝ)) ^ 2 / 8) * ((1 / 4 : ℝ) * Real.log (m : ℝ)) ≤
          (L : ℝ) ^ 2 / 8 * Real.log ((R + 1 : ℕ) : ℝ) :=
        mul_le_mul (by linarith) hlog_R (by positivity) (by positivity)
      linarith
    have hprods : ((((3 / 16 : ℝ) * (m : ℝ)) ^ 2 / 8) * ((1 / 4 : ℝ) * Real.log (m : ℝ))) *
        ((7 / 16 : ℝ) * (m : ℝ)) ^ 4 ≤ (GoodMult.card : ℝ) * (K : ℝ) ^ 4 :=
      mul_le_mul hGs hK4s (by positivity) (by positivity)
    have hm6_pos : 0 < (m : ℝ) ^ 6 * Real.log (m : ℝ) := by positivity
    nlinarith
  refine ⟨hQ_lower, ?_⟩
  rw [hGcard]
  have hQ_pos : 0 < (Q.card : ℝ) := by
    have : 0 < (1 / 65536 : ℝ) * (m : ℝ) ^ 6 * Real.log (m : ℝ) := by positivity
    linarith
  have hlog_m2 : Real.log ((m ^ 2 : ℕ) : ℝ) = 2 * Real.log (m : ℝ) := by
    push_cast; rw [Real.log_pow]; ring
  have hlog_m2_pos : 0 < Real.log ((m ^ 2 : ℕ) : ℝ) := by rw [hlog_m2]; linarith
  have hnum : (((m ^ 2 * (m ^ 2 - 1) : ℕ) : ℝ)) ^ 2 ≤ ((m : ℝ) ^ 2) ^ 4 := by
    have h1 : ((m ^ 2 * (m ^ 2 - 1) : ℕ) : ℝ) ≤ (m : ℝ) ^ 4 := by
      have : m ^ 2 * (m ^ 2 - 1) ≤ m ^ 4 := by
        calc m ^ 2 * (m ^ 2 - 1) ≤ m ^ 2 * m ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          _ = m ^ 4 := by ring
      exact_mod_cast this
    have h2 : (((m ^ 2 * (m ^ 2 - 1) : ℕ) : ℝ)) ^ 2 ≤ ((m : ℝ) ^ 4) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
    linarith
  rw [div_le_div_iff₀ hQ_pos hlog_m2_pos, hlog_m2]
  have hm2_cast : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  rw [hm2_cast]
  have hstep : ((m : ℝ) ^ 2) ^ 4 * (2 * Real.log (m : ℝ)) ≤
      131072 * (m : ℝ) ^ 2 * ((1 / 65536 : ℝ) * (m : ℝ) ^ 6 * Real.log (m : ℝ)) := by
    ring_nf; exact le_rfl
  have hstep2 : 131072 * (m : ℝ) ^ 2 * ((1 / 65536 : ℝ) * (m : ℝ) ^ 6 * Real.log (m : ℝ)) ≤
      131072 * (m : ℝ) ^ 2 * (Q.card : ℝ) :=
    mul_le_mul_of_nonneg_left hQ_lower (by positivity)
  nlinarith

/-- **Asymptotic Consequence of the Guth–Katz Quadruple-Energy Barrier**:
For EVERY positive constant `c > 0`, there exists `M₀` such that for all `m ≥ M₀`, on the
`m × m` integer grid `G_m`, the Elekes–Sharir / Guth–Katz Cauchy–Schwarz lower bound
`(|G_m|(|G_m| - 1))² / Q(G_m)` is STRICTLY LESS than `c * |G_m| / √(log |G_m|)`.
Thus no improvement to the `Q(P)` energy bound alone can ever reach Erdős's `$500` conjecture.
Pure Mathlib signature (`0` custom definitions). -/
theorem ppl071_guth_katz_barrier_cannot_reach_erdos89 (c : ℝ) (hc : 0 < c) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m →
      let G : Finset (EuclideanSpace ℝ (Fin 2)) :=
        ((Finset.range m) ×ˢ (Finset.range m)).image
          (fun ab => WithLp.toLp 2 ![(ab.1 : ℝ), (ab.2 : ℝ)])
      let Q := ((G ×ˢ G) ×ˢ (G ×ˢ G)).filter
        (fun x => dist x.1.1 x.1.2 = dist x.2.1 x.2.2 ∧ x.1.1 ≠ x.1.2)
      (((G.card * (G.card - 1)) : ℕ) : ℝ) ^ 2 / (Q.card : ℝ) <
        c * (G.card : ℝ) / Real.sqrt (Real.log (G.card : ℝ)) := by
  set B := (131072 / c) ^ 2 + 1
  refine ⟨max 16 (Nat.ceil (Real.exp B) + 1), fun m hm => ?_⟩
  intro G Q
  have hm16 : 16 ≤ m := le_trans (le_max_left _ _) hm
  have hm_exp : Real.exp B < (m : ℝ) := by
    have h1 : Nat.ceil (Real.exp B) + 1 ≤ m := le_trans (le_max_right _ _) hm
    have h2 : Real.exp B ≤ (Nat.ceil (Real.exp B) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (Real.exp B) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h1
    linarith
  have hbar := (ppl071_guth_katz_quadruple_energy_barrier m hm16).2
  have hinjG : Set.InjOn (fun ab : ℕ × ℕ => WithLp.toLp 2 ![(ab.1 : ℝ), (ab.2 : ℝ)])
      ((Finset.range m ×ˢ Finset.range m : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro p1 _ p2 _ heq
    have h0 : (p1.1 : ℝ) = (p2.1 : ℝ) := by
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) heq; simpa using this
    have h1 : (p1.2 : ℝ) = (p2.2 : ℝ) := by
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) heq; simpa using this
    exact Prod.ext (by exact_mod_cast h0) (by exact_mod_cast h1)
  have hGcard : G.card = m ^ 2 := by
    rw [Finset.card_image_of_injOn hinjG, Finset.card_product, Finset.card_range, sq]
  have hlog_gt : B < Real.log (m : ℝ) := by
    have := Real.log_lt_log (Real.exp_pos B) hm_exp
    rwa [Real.log_exp] at this
  have hlogG : Real.log (G.card : ℝ) = 2 * Real.log (m : ℝ) := by
    rw [hGcard]; push_cast; rw [Real.log_pow]; ring
  have hlogG_gt : (131072 / c) ^ 2 < Real.log (G.card : ℝ) := by
    have hB_pos : 0 < B := by positivity
    rw [hlogG]; dsimp [B] at hlog_gt ⊢; linarith
  have hsqrt_gt : 131072 / c < Real.sqrt (Real.log (G.card : ℝ)) := by
    have h1 := Real.sqrt_lt_sqrt (sq_nonneg _) hlogG_gt
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hGpos : (0 : ℝ) < (G.card : ℝ) := by rw [hGcard]; positivity
  have hlogG_pos : 0 < Real.log (G.card : ℝ) := by
    have : 0 ≤ (131072 / c) ^ 2 := sq_nonneg _
    linarith
  have hsqrt_pos : 0 < Real.sqrt (Real.log (G.card : ℝ)) := Real.sqrt_pos.mpr hlogG_pos
  have hstrict : 131072 * (G.card : ℝ) / Real.log (G.card : ℝ) <
      c * (G.card : ℝ) / Real.sqrt (Real.log (G.card : ℝ)) := by
    rw [div_lt_div_iff₀ hlogG_pos hsqrt_pos]
    have hsq : Real.log (G.card : ℝ) =
        Real.sqrt (Real.log (G.card : ℝ)) * Real.sqrt (Real.log (G.card : ℝ)) :=
      (Real.mul_self_sqrt (le_of_lt hlogG_pos)).symm
    have h131 : 131072 < c * Real.sqrt (Real.log (G.card : ℝ)) := by
      rw [div_lt_iff₀ hc] at hsqrt_gt; linarith
    have hmul : 131072 * ((G.card : ℝ) * Real.sqrt (Real.log (G.card : ℝ))) <
        (c * Real.sqrt (Real.log (G.card : ℝ))) * ((G.card : ℝ) * Real.sqrt (Real.log (G.card : ℝ))) :=
      mul_lt_mul_of_pos_right h131 (mul_pos hGpos hsqrt_pos)
    have hrhs_eq : c * (G.card : ℝ) * Real.log (G.card : ℝ) =
        (c * Real.sqrt (Real.log (G.card : ℝ))) * ((G.card : ℝ) * Real.sqrt (Real.log (G.card : ℝ))) := by
      conv_lhs => rw [hsq]
      ring
    linarith
  exact lt_of_le_of_lt hbar hstrict


/-! ## Section 4: Self-Contained Sweepline / Wiring-Diagram Multigraph Crossing Lemma -/

/-! ### Self-Contained Sweepline / Wiring-Diagram Multigraph Crossing Lemma -/

/-- A labeled directed multigraph edge `(id, l, r)` on `Fin n` with `l < r`. -/
private structure MEdge (n : ℕ) where
  id : ℕ
  l : Fin n
  r : Fin n
  hlr : l < r
deriving DecidableEq

/-- Adjacent-transposition sequence transforming list `L₁` into `L₂`, recording the swapped pairs. -/
private inductive SwapSeq {α : Type*} : List (α × α) → List α → List α → Prop
  | nil (L : List α) : SwapSeq [] L L
  | cons {a b : α} {ps : List (α × α)} {L₁ L₂ L₃ : List α}
      (hstep : ∃ pre suf : List α, L₁ = pre ++ [a, b] ++ suf ∧ L₂ = pre ++ [b, a] ++ suf)
      (hrest : SwapSeq ps L₂ L₃) : SwapSeq ((a, b) :: ps) L₁ L₃

private lemma SwapSeq.nil_eq {α : Type*} {L₁ L₂ : List α} (h : SwapSeq [] L₁ L₂) : L₁ = L₂ := by
  cases h; rfl

private lemma SwapSeq.append {α : Type*} {ps qs : List (α × α)} {L₁ L₂ L₃ : List α}
    (h1 : SwapSeq ps L₁ L₂) (h2 : SwapSeq qs L₂ L₃) : SwapSeq (ps ++ qs) L₁ L₃ := by
  induction h1 with
  | nil _ => simpa using h2
  | cons hstep _ ih => exact SwapSeq.cons hstep (ih h2)

private lemma SwapSeq.perm {α : Type*} {ps : List (α × α)} {L₁ L₂ : List α}
    (h : SwapSeq ps L₁ L₂) : L₁.Perm L₂ := by
  induction h with
  | nil _ => exact List.Perm.refl _
  | @cons a b _ _ _ _ hstep _ ih =>
    obtain ⟨pre, suf, rfl, rfl⟩ := hstep
    have hsw : (pre ++ [a, b] ++ suf).Perm (pre ++ [b, a] ++ suf) := by
      simp only [List.append_assoc]
      exact List.Perm.append_left pre (List.Perm.append_right suf (List.Perm.swap b a []))
    exact hsw.trans ih

private lemma SwapSeq.mem_swaps {α : Type*} {ps : List (α × α)} {L₁ L₂ : List α}
    (h : SwapSeq ps L₁ L₂) {p : α × α} (hp : p ∈ ps) : p.1 ∈ L₁ ∧ p.2 ∈ L₁ := by
  induction h with
  | nil _ => cases hp
  | @cons a b _ L₁ L₂ _ hstep _ ih =>
    obtain ⟨pre, suf, rfl, rfl⟩ := hstep
    rcases List.mem_cons.mp hp with rfl | hmem
    · simp
    · have h2 := ih hmem
      have hperm : (pre ++ [a, b] ++ suf).Perm (pre ++ [b, a] ++ suf) := by
        simp only [List.append_assoc]
        exact List.Perm.append_left pre (List.Perm.append_right suf (List.Perm.swap b a []))
      exact ⟨hperm.mem_iff.mpr h2.1, hperm.mem_iff.mpr h2.2⟩

private lemma SwapSeq.ne_of_nodup {α : Type*} {ps : List (α × α)} {L₁ L₂ : List α}
    (h : SwapSeq ps L₁ L₂) (hnd : L₁.Nodup) {p : α × α} (hp : p ∈ ps) : p.1 ≠ p.2 := by
  induction h with
  | nil _ => cases hp
  | @cons a b _ L₁ L₂ _ hstep _ ih =>
    obtain ⟨pre, suf, rfl, rfl⟩ := hstep
    have hperm : (pre ++ [a, b] ++ suf).Perm (pre ++ [b, a] ++ suf) := by
      simp only [List.append_assoc]
      exact List.Perm.append_left pre (List.Perm.append_right suf (List.Perm.swap b a []))
    rcases List.mem_cons.mp hp with rfl | hmem
    · simp only [List.append_assoc, List.nodup_append, List.nodup_cons] at hnd
      change a ≠ b
      intro hab; subst hab
      exact hnd.2.1.1.1 (by simp)
    · exact ih (hperm.nodup_iff.mp hnd) hmem

private lemma SwapSeq.filter {α : Type*} (P : α → Bool) {ps : List (α × α)} {L₁ L₂ : List α}
    (h : SwapSeq ps L₁ L₂) :
    SwapSeq (ps.filter (fun p => P p.1 && P p.2)) (L₁.filter P) (L₂.filter P) := by
  induction h with
  | nil L => exact SwapSeq.nil (L.filter P)
  | @cons a b ps L₁ L₂ L₃ hstep _ ih =>
    obtain ⟨pre, suf, rfl, rfl⟩ := hstep
    simp only [List.filter_cons]
    cases hPa : P a <;> cases hPb : P b
    · simp only [Bool.false_and]
      have heq : (pre ++ [a, b] ++ suf).filter P = (pre ++ [b, a] ++ suf).filter P := by
        simp [List.filter_append, hPa, hPb]
      rw [heq]; exact ih
    · simp only [Bool.false_and]
      have heq : (pre ++ [a, b] ++ suf).filter P = (pre ++ [b, a] ++ suf).filter P := by
        simp [List.filter_append, hPa, hPb]
      rw [heq]; exact ih
    · simp only [Bool.and_false]
      have heq : (pre ++ [a, b] ++ suf).filter P = (pre ++ [b, a] ++ suf).filter P := by
        simp [List.filter_append, hPa, hPb]
      rw [heq]; exact ih
    · simp only [Bool.and_self, ↓reduceIte]
      refine SwapSeq.cons ?_ ih
      refine ⟨pre.filter P, suf.filter P, ?_, ?_⟩
      · simp [List.filter_append, hPa, hPb]
      · simp [List.filter_append, hPa, hPb]

private lemma SwapSeq.map {α β : Type*} (f : α → β) {ps : List (α × α)} {L₁ L₂ : List α}
    (h : SwapSeq ps L₁ L₂) :
    SwapSeq (ps.map (fun p => (f p.1, f p.2))) (L₁.map f) (L₂.map f) := by
  induction h with
  | nil L => exact SwapSeq.nil (L.map f)
  | @cons a b ps L₁ L₂ L₃ hstep _ ih =>
    obtain ⟨pre, suf, rfl, rfl⟩ := hstep
    refine SwapSeq.cons ⟨pre.map f, suf.map f, by simp, by simp⟩ ih

/-- Helper: mapping `Equiv.swap a b` fixes a list containing neither `a` nor `b`. -/
private lemma list_map_swap_of_not_mem {α : Type*} [DecidableEq α] {a b : α} {L : List α}
    (ha : a ∉ L) (hb : b ∉ L) : L.map (Equiv.swap a b) = L := by
  have h : L.map (Equiv.swap a b) = L.map id :=
    List.map_congr_left fun x hx =>
      Equiv.swap_apply_of_ne_of_ne (fun h => ha (h ▸ hx)) (fun h => hb (h ▸ hx))
  rw [h, List.map_id]

/-- Mapping `Equiv.swap a b` over `pre ++ [a, b] ++ suf` (nodup) yields `pre ++ [b, a] ++ suf`! -/
private lemma list_map_swap_adj {α : Type*} [DecidableEq α] {a b : α} {pre suf : List α}
    (hnd : (pre ++ [a, b] ++ suf).Nodup) :
    (pre ++ [a, b] ++ suf).map (Equiv.swap a b) = pre ++ [b, a] ++ suf := by
  simp only [List.append_assoc, List.nodup_append, List.nodup_cons] at hnd
  have ha_pre : a ∉ pre := fun h => hnd.2.2 a h a (by simp) rfl
  have hb_pre : b ∉ pre := fun h => hnd.2.2 b h b (by simp) rfl
  have ha_suf : a ∉ suf := fun h => hnd.2.1.2.2 a (by simp) a h rfl
  have hb_suf : b ∉ suf := fun h => hnd.2.1.2.2 b (by simp) b h rfl
  have hpre : pre.map (Equiv.swap a b) = pre := list_map_swap_of_not_mem ha_pre hb_pre
  have hsuf : suf.map (Equiv.swap a b) = suf := list_map_swap_of_not_mem ha_suf hb_suf
  simp [List.map_append, hpre, hsuf]

/-- Deleting one occurrence of swap `(a, b)` in `SwapSeq ps L₁ L₂` by swapping labels BEFORE it. -/
private lemma SwapSeq.delete_before {α : Type*} [DecidableEq α] {a b : α}
    {ps : List (α × α)} {L₁ L₂ : List α}
    (h : SwapSeq ps L₁ L₂) (hnd : L₁.Nodup) (hmem : (a, b) ∈ ps) :
    ∃ ps' : List (α × α), ps'.length < ps.length ∧ SwapSeq ps' (L₁.map (Equiv.swap a b)) L₂ := by
  induction h with
  | nil _ => cases hmem
  | @cons c d rest L₁ L₂ L₃ hstep hrest ih =>
    obtain ⟨pre, suf, rfl, rfl⟩ := hstep
    rcases List.mem_cons.mp hmem with heq | hmem'
    · injection heq with hca hdb; subst hca; subst hdb
      refine ⟨rest, Nat.lt_succ_self _, ?_⟩
      rw [list_map_swap_adj hnd]; exact hrest
    · have hperm : (pre ++ [c, d] ++ suf).Perm (pre ++ [d, c] ++ suf) := by
        simp only [List.append_assoc]
        exact List.Perm.append_left pre (List.Perm.append_right suf (List.Perm.swap d c []))
      obtain ⟨ps', hlen, hseq'⟩ := ih (hperm.nodup_iff.mp hnd) hmem'
      refine ⟨(Equiv.swap a b c, Equiv.swap a b d) :: ps', by simp; omega, ?_⟩
      exact SwapSeq.cons ⟨pre.map (Equiv.swap a b), suf.map (Equiv.swap a b), by simp, by simp⟩ hseq'

/-- Deleting one occurrence of swap `(a, b)` in `SwapSeq ps L₁ L₂` by swapping labels AFTER it. -/
private lemma SwapSeq.delete_after {α : Type*} [DecidableEq α] {a b : α}
    {ps : List (α × α)} {L₁ L₂ : List α}
    (h : SwapSeq ps L₁ L₂) (hnd : L₁.Nodup) (hmem : (a, b) ∈ ps) :
    ∃ ps' : List (α × α), ps'.length < ps.length ∧ SwapSeq ps' L₁ (L₂.map (Equiv.swap a b)) := by
  induction h with
  | nil _ => cases hmem
  | @cons c d rest L₁ L₂ L₃ hstep hrest ih =>
    obtain ⟨pre, suf, rfl, rfl⟩ := hstep
    rcases List.mem_cons.mp hmem with heq | hmem'
    · injection heq with hca hdb; subst hca; subst hdb
      refine ⟨rest.map (fun p => (Equiv.swap a b p.1, Equiv.swap a b p.2)), by simp, ?_⟩
      have hmap := hrest.map (Equiv.swap a b)
      have hback : (pre ++ [b, a] ++ suf).map (Equiv.swap a b) = pre ++ [a, b] ++ suf := by
        have hperm : (pre ++ [a, b] ++ suf).Perm (pre ++ [b, a] ++ suf) := by
          simp only [List.append_assoc]
          exact List.Perm.append_left pre (List.Perm.append_right suf (List.Perm.swap b a []))
        have hnd2 := hperm.nodup_iff.mp hnd
        rw [Equiv.swap_comm a b]
        exact list_map_swap_adj hnd2
      rw [hback] at hmap
      exact hmap
    · have hperm : (pre ++ [c, d] ++ suf).Perm (pre ++ [d, c] ++ suf) := by
        simp only [List.append_assoc]
        exact List.Perm.append_left pre (List.Perm.append_right suf (List.Perm.swap d c []))
      obtain ⟨ps', hlen, hseq'⟩ := ih (hperm.nodup_iff.mp hnd) hmem'
      refine ⟨(c, d) :: ps', by simp; omega, ?_⟩
      exact SwapSeq.cons ⟨pre, suf, rfl, rfl⟩ hseq'

/-- A wiring diagram of an edge set `E` on `n` x-ordered vertices `Fin n`. -/
private structure WiringDiagram (n : ℕ) (E : Finset (MEdge n)) where
  B : Fin n → List (MEdge n)
  A : Fin n → List (MEdge n)
  InL : Fin n → List (MEdge n)
  OutL : Fin n → List (MEdge n)
  swaps : (i : Fin n) → (i.val + 1 < n) → List (MEdge n × MEdge n)
  hIn_nodup : ∀ i, (InL i).Nodup
  hOut_nodup : ∀ i, (OutL i).Nodup
  hIn_mem : ∀ i e, e ∈ InL i ↔ e ∈ E ∧ e.r = i
  hOut_mem : ∀ i e, e ∈ OutL i ↔ e ∈ E ∧ e.l = i
  hB_pass : ∀ i e, e ∈ B i → e ∈ E ∧ e.l < i ∧ i < e.r
  hA_pass : ∀ i e, e ∈ A i → e ∈ E ∧ e.l < i ∧ i < e.r
  hbefore_nodup : ∀ i, (B i ++ InL i ++ A i).Nodup
  hafter_nodup : ∀ i, (B i ++ OutL i ++ A i).Nodup
  hslab : ∀ (i : Fin n) (hi : i.val + 1 < n),
    SwapSeq (swaps i hi) (B i ++ OutL i ++ A i)
      (B ⟨i.val + 1, hi⟩ ++ InL ⟨i.val + 1, hi⟩ ++ A ⟨i.val + 1, hi⟩)

/-- Total number of swaps in a wiring diagram. -/
private def WiringDiagram.totalSwaps {n : ℕ} {E : Finset (MEdge n)} (W : WiringDiagram n E) : ℕ :=
  ∑ i : Fin n, if hi : i.val + 1 < n then (W.swaps i hi).length else 0

/-- Filtering a wiring diagram by a predicate on edges. -/
private def WiringDiagram.filter {n : ℕ} {E : Finset (MEdge n)} (W : WiringDiagram n E)
    (P : MEdge n → Bool) : WiringDiagram n (E.filter (fun e => P e = true)) where
  B i := (W.B i).filter P
  A i := (W.A i).filter P
  InL i := (W.InL i).filter P
  OutL i := (W.OutL i).filter P
  swaps i hi := (W.swaps i hi).filter (fun p => P p.1 && P p.2)
  hIn_nodup i := (W.hIn_nodup i).filter P
  hOut_nodup i := (W.hOut_nodup i).filter P
  hIn_mem i e := by
    simp only [List.mem_filter, W.hIn_mem i e, Finset.mem_filter]; tauto
  hOut_mem i e := by
    simp only [List.mem_filter, W.hOut_mem i e, Finset.mem_filter]; tauto
  hB_pass i e he := by
    simp only [List.mem_filter, Finset.mem_filter] at he ⊢
    have h := W.hB_pass i e he.1; exact ⟨⟨h.1, he.2⟩, h.2⟩
  hA_pass i e he := by
    simp only [List.mem_filter, Finset.mem_filter] at he ⊢
    have h := W.hA_pass i e he.1; exact ⟨⟨h.1, he.2⟩, h.2⟩
  hbefore_nodup i := by
    have h := (W.hbefore_nodup i).filter P
    simpa [List.filter_append] using h
  hafter_nodup i := by
    have h := (W.hafter_nodup i).filter P
    simpa [List.filter_append] using h
  hslab i hi := by
    have h := (W.hslab i hi).filter P
    simpa [List.filter_append] using h

/-- Every swap `(e₁, e₂)` in slab `i` satisfies `e₁, e₂ ∈ E`, `e₁ ≠ e₂`, and both are active in slab `i`. -/
private lemma WiringDiagram.swap_active {n : ℕ} {E : Finset (MEdge n)} (W : WiringDiagram n E)
    (i : Fin n) (hi : i.val + 1 < n) {p : MEdge n × MEdge n} (hp : p ∈ W.swaps i hi) :
    p.1 ∈ E ∧ p.2 ∈ E ∧ p.1 ≠ p.2 ∧
    p.1.l ≤ i ∧ i < p.1.r ∧ p.2.l ≤ i ∧ i < p.2.r := by
  have hmem := (W.hslab i hi).mem_swaps hp
  have hne := (W.hslab i hi).ne_of_nodup (W.hafter_nodup i) hp
  have hact : ∀ e, e ∈ W.B i ++ W.OutL i ++ W.A i → e ∈ E ∧ e.l ≤ i ∧ i < e.r := by
    intro e he
    simp only [List.mem_append] at he
    rcases he with (hB | hOut) | hA
    · have h := W.hB_pass i e hB; exact ⟨h.1, le_of_lt h.2.1, h.2.2⟩
    · have h := (W.hOut_mem i e).mp hOut; exact ⟨h.1, le_of_eq h.2, h.2 ▸ e.hlr⟩
    · have h := W.hA_pass i e hA; exact ⟨h.1, le_of_lt h.2.1, h.2.2⟩
  have h1 := hact p.1 hmem.1
  have h2 := hact p.2 hmem.2
  exact ⟨h1.1, h2.1, hne, h1.2.1, h1.2.2, h2.2.1, h2.2.2⟩

/-- **Adjacent-Swap Elimination**: If a wiring diagram `W` has a swap `(e₁, e₂)` sharing either
left endpoint (`e₁.l = e₂.l`) or right endpoint (`e₁.r = e₂.r`), then there exists a wiring
diagram `W'` for the SAME edge set `E` with strictly fewer total swaps! -/
private lemma WiringDiagram.exists_fewer_swaps_of_adj {n : ℕ} {E : Finset (MEdge n)}
    (W : WiringDiagram n E) (j : Fin n) (hj : j.val + 1 < n)
    {e₁ e₂ : MEdge n} (hmem : (e₁, e₂) ∈ W.swaps j hj)
    (hadj : e₁.l = e₂.l ∨ e₁.r = e₂.r) :
    ∃ W' : WiringDiagram n E, W'.totalSwaps < W.totalSwaps := by
  have hact := W.swap_active j hj hmem
  set τ := Equiv.swap e₁ e₂
  rcases hadj with hl_eq | hr_eq
  · -- Case 1: `e₁.l = e₂.l = u ≤ j`. Delete `(e₁, e₂)` via `delete_before` and apply `τ` on `[u, j]`.
    set u := e₁.l
    have hu_eq1 : e₁.l = u := rfl
    have hu_eq2 : e₂.l = u := hl_eq.symm
    have hu_le : u ≤ j := hact.2.2.2.1
    have h1r : j < e₁.r := hact.2.2.2.2.1
    have h2r : j < e₂.r := hact.2.2.2.2.2.2
    obtain ⟨ps', hps'_lt, hps'_seq⟩ := (W.hslab j hj).delete_before (W.hafter_nodup j) hmem
    have hnot_B : ∀ i : Fin n, i ≤ u → e₁ ∉ W.B i ∧ e₂ ∉ W.B i := by
      intro i hi
      exact ⟨fun h => absurd (lt_of_lt_of_le (W.hB_pass i e₁ h).2.1 hi) (lt_irrefl u),
             fun h => absurd (lt_of_lt_of_le (hu_eq2 ▸ (W.hB_pass i e₂ h).2.1) hi) (lt_irrefl u)⟩
    have hnot_A : ∀ i : Fin n, i ≤ u → e₁ ∉ W.A i ∧ e₂ ∉ W.A i := by
      intro i hi
      exact ⟨fun h => absurd (lt_of_lt_of_le (W.hA_pass i e₁ h).2.1 hi) (lt_irrefl u),
             fun h => absurd (lt_of_lt_of_le (hu_eq2 ▸ (W.hA_pass i e₂ h).2.1) hi) (lt_irrefl u)⟩
    have hnot_Out : ∀ i : Fin n, i ≠ u → e₁ ∉ W.OutL i ∧ e₂ ∉ W.OutL i := by
      intro i hi
      exact ⟨fun h => hi (((W.hOut_mem i e₁).mp h).2.symm.trans hu_eq1),
             fun h => hi (((W.hOut_mem i e₂).mp h).2.symm.trans hu_eq2)⟩
    have hnot_In : ∀ i : Fin n, i ≤ j → e₁ ∉ W.InL i ∧ e₂ ∉ W.InL i := by
      intro i hi
      constructor
      · intro h; have := ((W.hIn_mem i e₁).mp h).2; exact absurd (this ▸ h1r) (not_lt.mpr hi)
      · intro h; have := ((W.hIn_mem i e₂).mp h).2; exact absurd (this ▸ h2r) (not_lt.mpr hi)
    have hpass_both : ∀ i : Fin n, u < i → i ≤ j →
        (e₁ ∈ E ∧ e₁.l < i ∧ i < e₁.r) ∧ (e₂ ∈ E ∧ e₂.l < i ∧ i < e₂.r) := by
      intro i hui hij
      exact ⟨⟨hact.1, hui, lt_of_le_of_lt hij h1r⟩,
             ⟨hact.2.1, hu_eq2.symm ▸ hui, lt_of_le_of_lt hij h2r⟩⟩
    let W' : WiringDiagram n E := {
      B := fun i => if u < i ∧ i ≤ j then (W.B i).map τ else W.B i
      A := fun i => if u < i ∧ i ≤ j then (W.A i).map τ else W.A i
      InL := W.InL
      OutL := fun i => if i = u then (W.OutL i).map τ else W.OutL i
      swaps := fun i hi =>
        if i = j then ps'
        else if u ≤ i ∧ i < j then (W.swaps i hi).map (fun p => (τ p.1, τ p.2))
        else W.swaps i hi
      hIn_nodup := W.hIn_nodup
      hOut_nodup := fun i => by
        split_ifs
        · exact (W.hOut_nodup i).map τ.injective
        · exact W.hOut_nodup i
      hIn_mem := W.hIn_mem
      hOut_mem := fun i e => by
        split_ifs with hiu
        · subst hiu
          rw [List.mem_map]
          constructor
          · rintro ⟨x, hx, rfl⟩
            have hx' := (W.hOut_mem u x).mp hx
            by_cases h1 : x = e₁
            · subst h1; simp [τ, hact.2.1, hu_eq2]
            · by_cases h2 : x = e₂
              · subst h2; simp [τ, hact.1, hu_eq1]
              · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hx'
          · intro he
            refine ⟨τ e, ?_, τ.apply_symm_apply e⟩
            rw [W.hOut_mem]
            by_cases h1 : e = e₁
            · subst h1; simp [τ, hact.2.1, hu_eq2]
            · by_cases h2 : e = e₂
              · subst h2; simp [τ, hact.1, hu_eq1]
              · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact he
        · exact W.hOut_mem i e
      hB_pass := fun i e he => by
        split_ifs at he with hi
        · rw [List.mem_map] at he
          obtain ⟨x, hx, rfl⟩ := he
          by_cases h1 : x = e₁
          · subst h1; simp [τ, (hpass_both i hi.1 hi.2).2]
          · by_cases h2 : x = e₂
            · subst h2; simp [τ, (hpass_both i hi.1 hi.2).1]
            · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact W.hB_pass i x hx
        · exact W.hB_pass i e he
      hA_pass := fun i e he => by
        split_ifs at he with hi
        · rw [List.mem_map] at he
          obtain ⟨x, hx, rfl⟩ := he
          by_cases h1 : x = e₁
          · subst h1; simp [τ, (hpass_both i hi.1 hi.2).2]
          · by_cases h2 : x = e₂
            · subst h2; simp [τ, (hpass_both i hi.1 hi.2).1]
            · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact W.hA_pass i x hx
        · exact W.hA_pass i e he
      hbefore_nodup := fun i => by
        split_ifs with hi
        · have hmap := (W.hbefore_nodup i).map τ.injective
          have hIn_fix := list_map_swap_of_not_mem (hnot_In i hi.2).1 (hnot_In i hi.2).2
          rw [List.map_append, List.map_append, hIn_fix] at hmap
          exact hmap
        · exact W.hbefore_nodup i
      hafter_nodup := fun i => by
        by_cases hiu : i = u
        · subst hiu
          have hni : ¬(u < u ∧ u ≤ j) := fun h => lt_irrefl u h.1
          simp only [hni, ↓reduceIte]
          have hmap := (W.hafter_nodup u).map τ.injective
          have hBf := list_map_swap_of_not_mem (hnot_B u le_rfl).1 (hnot_B u le_rfl).2
          have hAf := list_map_swap_of_not_mem (hnot_A u le_rfl).1 (hnot_A u le_rfl).2
          rw [List.map_append, List.map_append, hBf, hAf] at hmap
          exact hmap
        · simp only [hiu, ↓reduceIte]
          split_ifs with hi
          · have hmap := (W.hafter_nodup i).map τ.injective
            have hOf := list_map_swap_of_not_mem (hnot_Out i hiu).1 (hnot_Out i hiu).2
            rw [List.map_append, List.map_append, hOf] at hmap
            exact hmap
          · exact W.hafter_nodup i
      hslab := fun i hi => by
        have hafter_eq : (if u < i ∧ i ≤ j then (W.B i).map τ else W.B i) ++
            (if i = u then (W.OutL i).map τ else W.OutL i) ++
            (if u < i ∧ i ≤ j then (W.A i).map τ else W.A i) =
            if u ≤ i ∧ i ≤ j then (W.B i ++ W.OutL i ++ W.A i).map τ
            else W.B i ++ W.OutL i ++ W.A i := by
          by_cases hiu : i = u
          · subst hiu
            have h1 : ¬(u < u ∧ u ≤ j) := fun h => lt_irrefl u h.1
            have h2 : u ≤ u ∧ u ≤ j := ⟨le_rfl, hu_le⟩
            rw [if_neg h1, if_pos rfl, if_neg h1, if_pos h2, List.map_append, List.map_append,
              list_map_swap_of_not_mem (hnot_B u le_rfl).1 (hnot_B u le_rfl).2,
              list_map_swap_of_not_mem (hnot_A u le_rfl).1 (hnot_A u le_rfl).2]
          · have hiff : (u < i ∧ i ≤ j) ↔ (u ≤ i ∧ i ≤ j) := by
              constructor
              · rintro ⟨h1, h2⟩; exact ⟨le_of_lt h1, h2⟩
              · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm hiu), h2⟩
            rw [if_neg hiu]
            simp only [hiff]
            split_ifs
            · rw [List.map_append, List.map_append,
                list_map_swap_of_not_mem (hnot_Out i hiu).1 (hnot_Out i hiu).2]
            · rfl
        have hbefore_eq : (if u < (⟨i.val + 1, hi⟩ : Fin n) ∧ (⟨i.val + 1, hi⟩ : Fin n) ≤ j
              then (W.B ⟨i.val + 1, hi⟩).map τ else W.B ⟨i.val + 1, hi⟩) ++
            W.InL ⟨i.val + 1, hi⟩ ++
            (if u < (⟨i.val + 1, hi⟩ : Fin n) ∧ (⟨i.val + 1, hi⟩ : Fin n) ≤ j
              then (W.A ⟨i.val + 1, hi⟩).map τ else W.A ⟨i.val + 1, hi⟩) =
            if u ≤ i ∧ i < j then
              (W.B ⟨i.val + 1, hi⟩ ++ W.InL ⟨i.val + 1, hi⟩ ++ W.A ⟨i.val + 1, hi⟩).map τ
            else W.B ⟨i.val + 1, hi⟩ ++ W.InL ⟨i.val + 1, hi⟩ ++ W.A ⟨i.val + 1, hi⟩ := by
          have hiff : (u < (⟨i.val + 1, hi⟩ : Fin n) ∧ (⟨i.val + 1, hi⟩ : Fin n) ≤ j) ↔
              (u ≤ i ∧ i < j) := by
            simp only [Fin.lt_def, Fin.le_def]; omega
          simp only [hiff]
          split_ifs with hcond
          · have hle : (⟨i.val + 1, hi⟩ : Fin n) ≤ j := by
              simp only [Fin.le_def]; have := Fin.lt_def.mp hcond.2; omega
            rw [List.map_append, List.map_append,
              list_map_swap_of_not_mem (hnot_In _ hle).1 (hnot_In _ hle).2]
          · rfl
        rw [hafter_eq, hbefore_eq]
        by_cases hji : i = j
        · subst hji
          have h1 : u ≤ i ∧ i ≤ i := ⟨hu_le, le_rfl⟩
          have h2 : ¬(u ≤ i ∧ i < i) := fun h => lt_irrefl i h.2
          rw [if_pos rfl, if_pos h1, if_neg h2]
          exact hps'_seq
        · rw [if_neg hji]
          have hiff : (u ≤ i ∧ i ≤ j) ↔ (u ≤ i ∧ i < j) := by
            constructor
            · rintro ⟨h1, h2⟩; exact ⟨h1, lt_of_le_of_ne h2 hji⟩
            · rintro ⟨h1, h2⟩; exact ⟨h1, le_of_lt h2⟩
          simp only [hiff]
          split_ifs
          · exact (W.hslab i hi).map τ
          · exact W.hslab i hi
    }
    refine ⟨W', ?_⟩
    unfold WiringDiagram.totalSwaps
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
    · split_ifs with hi
      · dsimp [W']
        split_ifs with hji _
        · subst hji; exact le_of_lt hps'_lt
        · simp
        · exact le_rfl
      · exact le_rfl
    · simp only [hj, ↓reduceDIte, W', ↓reduceIte]; exact hps'_lt
  · -- Case 2: `e₁.r = e₂.r = w > j`. Delete `(e₁, e₂)` via `delete_after` and apply `τ` on `[j+1, w]`.
    set w := e₁.r
    have hw_eq1 : e₁.r = w := rfl
    have hw_eq2 : e₂.r = w := hr_eq.symm
    have hj_lt_w : j < w := hact.2.2.2.2.1
    have h1l : e₁.l ≤ j := hact.2.2.2.1
    have h2l : e₂.l ≤ j := hact.2.2.2.2.2.1
    obtain ⟨ps', hps'_lt, hps'_seq⟩ := (W.hslab j hj).delete_after (W.hafter_nodup j) hmem
    have hnot_B : ∀ i : Fin n, w ≤ i → e₁ ∉ W.B i ∧ e₂ ∉ W.B i := by
      intro i hi
      exact ⟨fun h => absurd (lt_of_le_of_lt hi (W.hB_pass i e₁ h).2.2) (lt_irrefl w),
             fun h => absurd (lt_of_le_of_lt hi (hw_eq2 ▸ (W.hB_pass i e₂ h).2.2)) (lt_irrefl w)⟩
    have hnot_A : ∀ i : Fin n, w ≤ i → e₁ ∉ W.A i ∧ e₂ ∉ W.A i := by
      intro i hi
      exact ⟨fun h => absurd (lt_of_le_of_lt hi (W.hA_pass i e₁ h).2.2) (lt_irrefl w),
             fun h => absurd (lt_of_le_of_lt hi (hw_eq2 ▸ (W.hA_pass i e₂ h).2.2)) (lt_irrefl w)⟩
    have hnot_In : ∀ i : Fin n, i ≠ w → e₁ ∉ W.InL i ∧ e₂ ∉ W.InL i := by
      intro i hi
      exact ⟨fun h => hi (((W.hIn_mem i e₁).mp h).2.symm.trans hw_eq1),
             fun h => hi (((W.hIn_mem i e₂).mp h).2.symm.trans hw_eq2)⟩
    have hnot_Out : ∀ i : Fin n, j < i → e₁ ∉ W.OutL i ∧ e₂ ∉ W.OutL i := by
      intro i hi
      constructor
      · intro h; have := ((W.hOut_mem i e₁).mp h).2; exact absurd (this ▸ hi) (not_lt.mpr h1l)
      · intro h; have := ((W.hOut_mem i e₂).mp h).2; exact absurd (this ▸ hi) (not_lt.mpr h2l)
    have hpass_both : ∀ i : Fin n, j < i → i < w →
        (e₁ ∈ E ∧ e₁.l < i ∧ i < e₁.r) ∧ (e₂ ∈ E ∧ e₂.l < i ∧ i < e₂.r) := by
      intro i hji hiw
      exact ⟨⟨hact.1, lt_of_le_of_lt h1l hji, hiw⟩,
             ⟨hact.2.1, lt_of_le_of_lt h2l hji, hw_eq2.symm ▸ hiw⟩⟩
    let W' : WiringDiagram n E := {
      B := fun i => if j < i ∧ i < w then (W.B i).map τ else W.B i
      A := fun i => if j < i ∧ i < w then (W.A i).map τ else W.A i
      InL := fun i => if i = w then (W.InL i).map τ else W.InL i
      OutL := W.OutL
      swaps := fun i hi =>
        if i = j then ps'
        else if j < i ∧ i < w then (W.swaps i hi).map (fun p => (τ p.1, τ p.2))
        else W.swaps i hi
      hIn_nodup := fun i => by
        split_ifs
        · exact (W.hIn_nodup i).map τ.injective
        · exact W.hIn_nodup i
      hOut_nodup := W.hOut_nodup
      hIn_mem := fun i e => by
        split_ifs with hiw
        · subst hiw
          rw [List.mem_map]
          constructor
          · rintro ⟨x, hx, rfl⟩
            have hx' := (W.hIn_mem w x).mp hx
            by_cases h1 : x = e₁
            · subst h1; simp [τ, hact.2.1, hw_eq2]
            · by_cases h2 : x = e₂
              · subst h2; simp [τ, hact.1, hw_eq1]
              · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hx'
          · intro he
            refine ⟨τ e, ?_, τ.apply_symm_apply e⟩
            rw [W.hIn_mem]
            by_cases h1 : e = e₁
            · subst h1; simp [τ, hact.2.1, hw_eq2]
            · by_cases h2 : e = e₂
              · subst h2; simp [τ, hact.1, hw_eq1]
              · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact he
        · exact W.hIn_mem i e
      hOut_mem := W.hOut_mem
      hB_pass := fun i e he => by
        split_ifs at he with hi
        · rw [List.mem_map] at he
          obtain ⟨x, hx, rfl⟩ := he
          by_cases h1 : x = e₁
          · subst h1; simp [τ, (hpass_both i hi.1 hi.2).2]
          · by_cases h2 : x = e₂
            · subst h2; simp [τ, (hpass_both i hi.1 hi.2).1]
            · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact W.hB_pass i x hx
        · exact W.hB_pass i e he
      hA_pass := fun i e he => by
        split_ifs at he with hi
        · rw [List.mem_map] at he
          obtain ⟨x, hx, rfl⟩ := he
          by_cases h1 : x = e₁
          · subst h1; simp [τ, (hpass_both i hi.1 hi.2).2]
          · by_cases h2 : x = e₂
            · subst h2; simp [τ, (hpass_both i hi.1 hi.2).1]
            · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact W.hA_pass i x hx
        · exact W.hA_pass i e he
      hbefore_nodup := fun i => by
        by_cases hiw : i = w
        · subst hiw
          have hni : ¬(j < w ∧ w < w) := fun h => lt_irrefl w h.2
          simp only [hni, ↓reduceIte]
          have hmap := (W.hbefore_nodup w).map τ.injective
          have hBf := list_map_swap_of_not_mem (hnot_B w le_rfl).1 (hnot_B w le_rfl).2
          have hAf := list_map_swap_of_not_mem (hnot_A w le_rfl).1 (hnot_A w le_rfl).2
          rw [List.map_append, List.map_append, hBf, hAf] at hmap
          exact hmap
        · simp only [hiw, ↓reduceIte]
          split_ifs with hi
          · have hmap := (W.hbefore_nodup i).map τ.injective
            have hIf := list_map_swap_of_not_mem (hnot_In i hiw).1 (hnot_In i hiw).2
            rw [List.map_append, List.map_append, hIf] at hmap
            exact hmap
          · exact W.hbefore_nodup i
      hafter_nodup := fun i => by
        split_ifs with hi
        · have hmap := (W.hafter_nodup i).map τ.injective
          have hOf := list_map_swap_of_not_mem (hnot_Out i hi.1).1 (hnot_Out i hi.1).2
          rw [List.map_append, List.map_append, hOf] at hmap
          exact hmap
        · exact W.hafter_nodup i
      hslab := fun i hi => by
        have hafter_eq : (if j < i ∧ i < w then (W.B i).map τ else W.B i) ++
            W.OutL i ++
            (if j < i ∧ i < w then (W.A i).map τ else W.A i) =
            if j < i ∧ i < w then (W.B i ++ W.OutL i ++ W.A i).map τ
            else W.B i ++ W.OutL i ++ W.A i := by
          split_ifs with hcond
          · rw [List.map_append, List.map_append,
              list_map_swap_of_not_mem (hnot_Out i hcond.1).1 (hnot_Out i hcond.1).2]
          · rfl
        have hbefore_eq : (if j < (⟨i.val + 1, hi⟩ : Fin n) ∧ (⟨i.val + 1, hi⟩ : Fin n) < w
              then (W.B ⟨i.val + 1, hi⟩).map τ else W.B ⟨i.val + 1, hi⟩) ++
            (if (⟨i.val + 1, hi⟩ : Fin n) = w then (W.InL ⟨i.val + 1, hi⟩).map τ else W.InL ⟨i.val + 1, hi⟩) ++
            (if j < (⟨i.val + 1, hi⟩ : Fin n) ∧ (⟨i.val + 1, hi⟩ : Fin n) < w
              then (W.A ⟨i.val + 1, hi⟩).map τ else W.A ⟨i.val + 1, hi⟩) =
            if j ≤ i ∧ i < w then
              (W.B ⟨i.val + 1, hi⟩ ++ W.InL ⟨i.val + 1, hi⟩ ++ W.A ⟨i.val + 1, hi⟩).map τ
            else W.B ⟨i.val + 1, hi⟩ ++ W.InL ⟨i.val + 1, hi⟩ ++ W.A ⟨i.val + 1, hi⟩ := by
          by_cases hiw : (⟨i.val + 1, hi⟩ : Fin n) = w
          · have h1 : ¬(j < (⟨i.val + 1, hi⟩ : Fin n) ∧ (⟨i.val + 1, hi⟩ : Fin n) < w) :=
              fun h => lt_irrefl w (hiw ▸ h.2)
            have h2 : j ≤ i ∧ i < w := by
              have hwval : i.val + 1 = w.val := congrArg Fin.val hiw
              have hjw : j.val < w.val := Fin.lt_def.mp hj_lt_w
              exact ⟨Fin.le_def.mpr (by omega), Fin.lt_def.mpr (by omega)⟩
            rw [if_neg h1, if_pos hiw, if_neg h1, if_pos h2, List.map_append, List.map_append, hiw,
              list_map_swap_of_not_mem (hnot_B w le_rfl).1 (hnot_B w le_rfl).2,
              list_map_swap_of_not_mem (hnot_A w le_rfl).1 (hnot_A w le_rfl).2]
          · have hiff : (j < (⟨i.val + 1, hi⟩ : Fin n) ∧ (⟨i.val + 1, hi⟩ : Fin n) < w) ↔
                (j ≤ i ∧ i < w) := by
              have hne : i.val + 1 ≠ w.val := fun h => hiw (Fin.ext h)
              simp only [Fin.lt_def, Fin.le_def]; omega
            rw [if_neg hiw]
            simp only [hiff]
            split_ifs
            · rw [List.map_append, List.map_append,
                list_map_swap_of_not_mem (hnot_In _ hiw).1 (hnot_In _ hiw).2]
            · rfl
        rw [hafter_eq, hbefore_eq]
        by_cases hji : i = j
        · subst hji
          have h1 : ¬(i < i ∧ i < w) := fun h => lt_irrefl i h.1
          have h2 : i ≤ i ∧ i < w := ⟨le_rfl, hj_lt_w⟩
          rw [if_pos rfl, if_neg h1, if_pos h2]
          exact hps'_seq
        · rw [if_neg hji]
          have hiff : (j ≤ i ∧ i < w) ↔ (j < i ∧ i < w) := by
            constructor
            · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm hji), h2⟩
            · rintro ⟨h1, h2⟩; exact ⟨le_of_lt h1, h2⟩
          simp only [hiff]
          split_ifs
          · exact (W.hslab i hi).map τ
          · exact W.hslab i hi
    }
    refine ⟨W', ?_⟩
    unfold WiringDiagram.totalSwaps
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
    · split_ifs with hi
      · dsimp [W']
        split_ifs with hji _
        · subst hji; exact le_of_lt hps'_lt
        · simp
        · exact le_rfl
      · exact le_rfl
    · simp only [hj, ↓reduceDIte, W', ↓reduceIte]; exact hps'_lt

/-- Every wiring diagram `W` can be replaced by a wiring diagram `W'` with `totalSwaps W' ≤ totalSwaps W`
in which EVERY swap `(e₁, e₂)` is between two vertex-disjoint edges (4 distinct vertices)! -/
private lemma WiringDiagram.exists_disjoint_swaps {n : ℕ} {E : Finset (MEdge n)}
    (W : WiringDiagram n E) :
    ∃ W' : WiringDiagram n E, W'.totalSwaps ≤ W.totalSwaps ∧
      ∀ (i : Fin n) (hi : i.val + 1 < n), ∀ p ∈ W'.swaps i hi,
        p.1.l ≠ p.2.l ∧ p.1.l ≠ p.2.r ∧ p.1.r ≠ p.2.l ∧ p.1.r ≠ p.2.r := by
  suffices hmain : ∀ k : ℕ, ∀ W : WiringDiagram n E, W.totalSwaps = k →
      ∃ W' : WiringDiagram n E, W'.totalSwaps ≤ W.totalSwaps ∧
        ∀ (i : Fin n) (hi : i.val + 1 < n), ∀ p ∈ W'.swaps i hi,
          p.1.l ≠ p.2.l ∧ p.1.l ≠ p.2.r ∧ p.1.r ≠ p.2.l ∧ p.1.r ≠ p.2.r by
    exact hmain W.totalSwaps W rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro W hW
    by_cases hex : ∃ (j : Fin n) (hj : j.val + 1 < n) (p : MEdge n × MEdge n),
        p ∈ W.swaps j hj ∧ (p.1.l = p.2.l ∨ p.1.r = p.2.r)
    · obtain ⟨j, hj, ⟨e₁, e₂⟩, hmem, hadj⟩ := hex
      obtain ⟨W₁, hlt⟩ := W.exists_fewer_swaps_of_adj j hj hmem hadj
      obtain ⟨W', hle, hdisj⟩ := ih W₁.totalSwaps (hW ▸ hlt) W₁ rfl
      exact ⟨W', le_trans hle (le_of_lt hlt), hdisj⟩
    · refine ⟨W, le_rfl, fun i hi p hp => ?_⟩
      have hact := W.swap_active i hi hp
      have hnot : ¬(p.1.l = p.2.l ∨ p.1.r = p.2.r) := fun h => hex ⟨i, hi, p, hp, h⟩
      push Not at hnot
      refine ⟨hnot.1, ?_, ?_, hnot.2⟩
      · intro heq
        have : p.1.l < p.2.r := lt_of_le_of_lt hact.2.2.2.1 hact.2.2.2.2.2.2
        exact absurd heq (ne_of_lt this)
      · intro heq
        have : p.2.l < p.1.r := lt_of_le_of_lt hact.2.2.2.2.2.1 hact.2.2.2.2.1
        exact absurd heq (ne_of_gt this)

/-! ### Sweepline `goodGaps` Potential → `|E| ≤ 3|V|` for Planar (`0`-Swap) Simple Wiring Diagrams -/

/-- Number of adjacent pairs `(e₁, e₂)` in a list of edges with distinct left endpoints. -/
private def goodGaps {n : ℕ} : List (MEdge n) → ℕ
  | [] => 0
  | [_] => 0
  | e₁ :: e₂ :: rest => (if e₁.l ≠ e₂.l then 1 else 0) + goodGaps (e₂ :: rest)

private lemma goodGaps_append_ge {n : ℕ} (L₁ L₂ : List (MEdge n)) :
    goodGaps L₁ + goodGaps L₂ ≤ goodGaps (L₁ ++ L₂) := by
  induction L₁ with
  | nil => simp [goodGaps]
  | cons a t ih =>
    cases t with
    | nil =>
      cases L₂ with
      | nil => simp [goodGaps]
      | cons b s => simp [goodGaps]
    | cons b t' =>
      simp only [List.cons_append, goodGaps] at ih ⊢
      omega

private lemma goodGaps_append_le {n : ℕ} (L₁ L₂ : List (MEdge n)) :
    goodGaps (L₁ ++ L₂) ≤ goodGaps L₁ + goodGaps L₂ + 1 := by
  induction L₁ with
  | nil => simp [goodGaps]
  | cons a t ih =>
    cases t with
    | nil =>
      cases L₂ with
      | nil => simp [goodGaps]
      | cons b s => simp only [List.singleton_append, goodGaps]; split_ifs <;> omega
    | cons b t' =>
      simp only [List.cons_append, goodGaps] at ih ⊢
      omega

private lemma goodGaps_eq_zero_of_same_l {n : ℕ} (u : Fin n) (L : List (MEdge n))
    (h : ∀ e ∈ L, e.l = u) : goodGaps L = 0 := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t' =>
      simp only [goodGaps]
      have ha : a.l = u := h a (by simp)
      have hb : b.l = u := h b (by simp)
      rw [ha, hb]; simp only [ne_eq, not_true_eq_false, ↓reduceIte, zero_add]
      exact ih fun e he => h e (by simp [he])

private lemma goodGaps_eq_len_sub_one_of_pairwise_l {n : ℕ} (L : List (MEdge n))
    (h : L.Pairwise (fun e₁ e₂ => e₁.l ≠ e₂.l)) :
    L.length ≤ goodGaps L + 1 := by
  induction L with
  | nil => simp [goodGaps]
  | cons a t ih =>
    cases t with
    | nil => simp [goodGaps]
    | cons b t' =>
      have hpw := List.pairwise_cons.mp h
      have hab : a.l ≠ b.l := hpw.1 b (by simp)
      have iht := ih hpw.2
      simp only [goodGaps, hab, ne_eq, not_false_eq_true, ↓reduceIte, List.length_cons] at iht ⊢
      omega

/-- **Planar (`0`-Swap) Simple Wiring Diagram Bound on Active Vertex Set `V`**:
If `W` has `0` swaps, `E` is simple, and every edge has endpoints in `V ⊆ Fin n`, then
`E.card ≤ 3 * V.card` (zero Jordan Curve Theorem!). -/
private lemma WiringDiagram.card_le_three_mul_active_of_zero_swaps {n : ℕ} {E : Finset (MEdge n)}
    (W : WiringDiagram n E) (V : Finset (Fin n))
    (hsimple : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁.l = e₂.l → e₁.r = e₂.r → e₁ = e₂)
    (hV : ∀ e ∈ E, e.l ∈ V ∧ e.r ∈ V)
    (hzero : W.totalSwaps = 0) :
    E.card ≤ 3 * V.card := by
  rcases eq_or_ne n 0 with rfl | hn
  · have hE : E = ∅ := by ext e; exact Fin.elim0 e.l
    simp [hE]
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have hlink : ∀ (i : Fin n) (hi : i.val + 1 < n),
      W.B i ++ W.OutL i ++ W.A i =
        W.B ⟨i.val + 1, hi⟩ ++ W.InL ⟨i.val + 1, hi⟩ ++ W.A ⟨i.val + 1, hi⟩ := by
    intro i hi
    have hlen0 : (W.swaps i hi).length = 0 := by
      have hle : (if hi' : i.val + 1 < n then (W.swaps i hi').length else 0) ≤ W.totalSwaps := by
        unfold WiringDiagram.totalSwaps
        exact Finset.single_le_sum
          (f := fun k : Fin n => if hk : k.val + 1 < n then (W.swaps k hk).length else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      simp only [hi, ↓reduceDIte] at hle; omega
    have hseq := W.hslab i hi
    rw [List.eq_nil_of_length_eq_zero hlen0] at hseq
    exact hseq.nil_eq
  have hB0 : W.B ⟨0, hn_pos⟩ = [] := List.eq_nil_iff_forall_not_mem.mpr fun e he =>
    absurd (W.hB_pass ⟨0, hn_pos⟩ e he).2.1 (Nat.not_lt_zero _)
  have hA0 : W.A ⟨0, hn_pos⟩ = [] := List.eq_nil_iff_forall_not_mem.mpr fun e he =>
    absurd (W.hA_pass ⟨0, hn_pos⟩ e he).2.1 (Nat.not_lt_zero _)
  have hI0 : W.InL ⟨0, hn_pos⟩ = [] := List.eq_nil_iff_forall_not_mem.mpr fun e he => by
    have := ((W.hIn_mem ⟨0, hn_pos⟩ e).mp he).2
    have hlt : e.l.val < e.r.val := e.hlr
    rw [this] at hlt; simp at hlt
  have hstep : ∀ i : Fin n,
      goodGaps (W.B i ++ W.OutL i ++ W.A i) + (W.InL i).length ≤
        goodGaps (W.B i ++ W.InL i ++ W.A i) + (if i ∈ V then 3 else 0) := by
    intro i
    by_cases hiV : i ∈ V
    · simp only [hiV, ↓reduceIte]
      have hout0 : goodGaps (W.OutL i) = 0 :=
        goodGaps_eq_zero_of_same_l i (W.OutL i) (fun e he => ((W.hOut_mem i e).mp he).2)
      have hafter_ub : goodGaps (W.B i ++ W.OutL i ++ W.A i) ≤
          goodGaps (W.B i) + goodGaps (W.A i) + 2 := by
        have h1 := goodGaps_append_le (W.B i ++ W.OutL i) (W.A i)
        have h2 := goodGaps_append_le (W.B i) (W.OutL i)
        omega
      have hIn_pw : (W.InL i).Pairwise (fun e₁ e₂ => e₁.l ≠ e₂.l) := by
        refine List.Pairwise.imp_of_mem ?_ (W.hIn_nodup i)
        intro e₁ e₂ h1 h2 hne hl
        have he1 := (W.hIn_mem i e₁).mp h1
        have he2 := (W.hIn_mem i e₂).mp h2
        exact hne (hsimple e₁ he1.1 e₂ he2.1 hl (he1.2.trans he2.2.symm))
      have hin_lb : (W.InL i).length ≤ goodGaps (W.InL i) + 1 :=
        goodGaps_eq_len_sub_one_of_pairwise_l (W.InL i) hIn_pw
      have hbefore_lb : goodGaps (W.B i) + goodGaps (W.InL i) + goodGaps (W.A i) ≤
          goodGaps (W.B i ++ W.InL i ++ W.A i) := by
        have h1 := goodGaps_append_ge (W.B i ++ W.InL i) (W.A i)
        have h2 := goodGaps_append_ge (W.B i) (W.InL i)
        omega
      omega
    · simp only [hiV, ↓reduceIte, add_zero]
      have hIn_nil : W.InL i = [] := List.eq_nil_iff_forall_not_mem.mpr fun e he => by
        have h := (W.hIn_mem i e).mp he; exact hiV (h.2 ▸ (hV e h.1).2)
      have hOut_nil : W.OutL i = [] := List.eq_nil_iff_forall_not_mem.mpr fun e he => by
        have h := (W.hOut_mem i e).mp he; exact hiV (h.2 ▸ (hV e h.1).1)
      simp [hIn_nil, hOut_nil]
  have htelesc : ∀ t : ℕ, (ht : t ≤ n) →
      (if htn : t < n then goodGaps (W.B ⟨t, htn⟩ ++ W.InL ⟨t, htn⟩ ++ W.A ⟨t, htn⟩) else 0) +
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < t), (W.InL i).length ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < t), (if i ∈ V then 3 else 0) := by
    intro t ht
    induction t with
    | zero =>
      simp only [hn_pos, ↓reduceDIte, hB0, hI0, hA0, List.append_nil, goodGaps,
        Nat.not_lt_zero, Finset.filter_false, Finset.sum_empty, add_zero, le_refl]
    | succ t iht =>
      have ht_lt : t < n := by omega
      have hih := iht (by omega)
      simp only [ht_lt, ↓reduceDIte] at hih
      set it : Fin n := ⟨t, ht_lt⟩
      have hsplit : Finset.univ.filter (fun i : Fin n => i.val < t + 1) =
          insert it (Finset.univ.filter (fun i : Fin n => i.val < t)) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff, it]; omega
      rw [hsplit, Finset.sum_insert (by simp [it]), Finset.sum_insert (by simp [it])]
      have hst := hstep it
      by_cases ht1 : t + 1 < n
      · simp only [ht1, ↓reduceDIte]; rw [← hlink it ht1]; omega
      · simp only [ht1, ↓reduceDIte, zero_add]; omega
  have hfull := htelesc n le_rfl
  simp only [lt_irrefl, ↓reduceDIte, zero_add] at hfull
  have hall : Finset.univ.filter (fun i : Fin n => i.val < n) = Finset.univ := by
    ext i; simp
  rw [hall] at hfull
  have h3V : ∑ i : Fin n, (if i ∈ V then 3 else 0) = 3 * V.card := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    congr 2; ext i; simp
  have hcard_eq : E.card = ∑ i : Fin n, (W.InL i).length := by
    have h1 : ∀ i : Fin n, (W.InL i).length = (E.filter (fun e => e.r = i)).card := by
      intro i
      rw [← List.toFinset_card_of_nodup (W.hIn_nodup i)]
      congr 1; ext e; simp [W.hIn_mem i e]
    simp_rw [h1]
    rw [← Finset.card_biUnion]
    · congr 1; ext e; simp
    · intro i1 _ i2 _ hne; dsimp [Function.onFun]
      rw [Finset.disjoint_left]; intro e h1 h2
      simp only [Finset.mem_filter] at h1 h2; exact hne (h1.2.symm.trans h2.2)
  omega

/-- **Linear Crossing Bound on Active Vertex Set `V`**: `E.card ≤ 3 * V.card + W.totalSwaps`. -/
private lemma WiringDiagram.card_le_three_mul_active_add_swaps {n : ℕ} {E : Finset (MEdge n)}
    (W : WiringDiagram n E) (V : Finset (Fin n))
    (hsimple : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁.l = e₂.l → e₁.r = e₂.r → e₁ = e₂)
    (hV : ∀ e ∈ E, e.l ∈ V ∧ e.r ∈ V) :
    E.card ≤ 3 * V.card + W.totalSwaps := by
  suffices hmain : ∀ k : ℕ, ∀ (E₁ : Finset (MEdge n)) (W₁ : WiringDiagram n E₁),
      (∀ e₁ ∈ E₁, ∀ e₂ ∈ E₁, e₁.l = e₂.l → e₁.r = e₂.r → e₁ = e₂) →
      (∀ e ∈ E₁, e.l ∈ V ∧ e.r ∈ V) →
      W₁.totalSwaps = k → E₁.card ≤ 3 * V.card + k by
    exact hmain W.totalSwaps E W hsimple hV rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro E₁ W₁ hsim₁ hV₁ hk₁
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [add_zero]; exact W₁.card_le_three_mul_active_of_zero_swaps V hsim₁ hV₁ hk₁
    · have hex : ∃ (j : Fin n) (hj : j.val + 1 < n) (p : MEdge n × MEdge n), p ∈ W₁.swaps j hj := by
        by_contra hall; push Not at hall
        have h0 : W₁.totalSwaps = 0 := by
          unfold WiringDiagram.totalSwaps
          apply Finset.sum_eq_zero; intro i _
          split_ifs with hi
          · rw [List.length_eq_zero_iff]; exact List.eq_nil_iff_forall_not_mem.mpr (hall i hi)
          · rfl
        omega
      obtain ⟨j, hj, ⟨e₁, e₂⟩, hmem⟩ := hex
      have he1E : e₁ ∈ E₁ := (W₁.swap_active j hj hmem).1
      let P : MEdge n → Bool := fun e => decide (e ≠ e₁)
      let W₂ := W₁.filter P
      have hE₂_card : (E₁.filter (fun e => P e = true)).card = E₁.card - 1 := by
        have heq : E₁.filter (fun e => P e = true) = E₁.erase e₁ := by
          ext e; simp [P, Finset.mem_erase, and_comm]
        rw [heq, Finset.card_erase_of_mem he1E]
      have hW₂_lt : W₂.totalSwaps < k := by
        rw [← hk₁]; unfold WiringDiagram.totalSwaps
        refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
        · split_ifs with hi
          · dsimp [W₂, WiringDiagram.filter]; exact List.length_filter_le _ _
          · exact le_rfl
        · simp only [hj, ↓reduceDIte, W₂, WiringDiagram.filter]
          refine List.length_filter_lt_length_iff_exists.mpr ⟨(e₁, e₂), hmem, by simp [P]⟩
      have hih := ih W₂.totalSwaps hW₂_lt _ W₂
        (fun a ha b hb => hsim₁ a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1)
        (fun e he => hV₁ e (Finset.mem_filter.mp he).1) rfl
      rw [hE₂_card] at hih
      have hpos : 1 ≤ E₁.card := Finset.card_pos.mpr ⟨e₁, he1E⟩
      omega

/-! ### Finite-Product Probabilistic Multigraph Crossing Lemma (`E³ ≤ 64 m n² K`) -/

/-- Exact count of functions `f : α → Fin q` satisfying `(f a).val < c` for every `a ∈ S`. -/
private lemma card_pi_lt_on_subset {α : Type*} [Fintype α] [DecidableEq α]
    (q c : ℕ) (hc : c ≤ q) (S : Finset α) :
    (Finset.univ.filter (fun f : α → Fin q => ∀ a ∈ S, (f a).val < c)).card =
      c ^ S.card * q ^ (Fintype.card α - S.card) := by
  have hbij : (Finset.univ.filter (fun f : α → Fin q => ∀ a ∈ S, (f a).val < c)).card =
      Fintype.card (∀ a : α, {x : Fin q // a ∈ S → x.val < c}) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr
      { toFun := fun ⟨f, hf⟩ a => ⟨f a, fun ha => (Finset.mem_filter.mp hf).2 a ha⟩
        invFun := fun g => ⟨fun a => (g a).1,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a ha => (g a).2 ha⟩⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun _ => rfl }
  rw [hbij, Fintype.card_pi]
  have hfiber : ∀ a : α, Fintype.card {x : Fin q // a ∈ S → x.val < c} =
      if a ∈ S then c else q := by
    intro a
    by_cases ha : a ∈ S
    · simp only [ha, ↓reduceIte, forall_true_left]
      have hcard : Fintype.card {x : Fin q // x.val < c} = Fintype.card (Fin c) := by
        refine Fintype.card_congr
          { toFun := fun ⟨x, hx⟩ => ⟨x.val, hx⟩
            invFun := fun y => ⟨⟨y.val, lt_of_lt_of_le y.isLt hc⟩, y.isLt⟩
            left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
            right_inv := fun ⟨_, _⟩ => rfl }
      rw [hcard, Fintype.card_fin]
    · simp only [ha, ↓reduceIte, IsEmpty.forall_iff]
      have hcard : Fintype.card {x : Fin q // True} = Fintype.card (Fin q) := by
        refine Fintype.card_congr
          { toFun := fun x => x.1
            invFun := fun y => ⟨y, trivial⟩
            left_inv := fun ⟨_, _⟩ => rfl
            right_inv := fun _ => rfl }
      rw [hcard, Fintype.card_fin]
  simp_rw [hfiber]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (Finset.univ.filter (fun a : α => a ∈ S)).card = S.card := by
    congr 1; ext a; simp
  have h2 : (Finset.univ.filter (fun a : α => a ∉ S)).card = Fintype.card α - S.card := by
    have : Finset.univ.filter (fun a : α => a ∉ S) = Sᶜ := by ext a; simp
    rw [this, Finset.card_compl]
  rw [h1, h2]

/-- Exact count of functions `g : β → Fin m` matching fixed values on a subset `T`. -/
private lemma card_pi_eq_on_subset {β : Type*} [Fintype β] [DecidableEq β]
    (m : ℕ) (T : Finset β) (val : β → Fin m) :
    (Finset.univ.filter (fun g : β → Fin m => ∀ b ∈ T, g b = val b)).card =
      m ^ (Fintype.card β - T.card) := by
  have hbij : (Finset.univ.filter (fun g : β → Fin m => ∀ b ∈ T, g b = val b)).card =
      Fintype.card (∀ b : β, {x : Fin m // b ∈ T → x = val b}) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr
      { toFun := fun ⟨g, hg⟩ b => ⟨g b, fun hb => (Finset.mem_filter.mp hg).2 b hb⟩
        invFun := fun h => ⟨fun b => (h b).1,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun b hb => (h b).2 hb⟩⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun _ => rfl }
  rw [hbij, Fintype.card_pi]
  have hfiber : ∀ b : β, Fintype.card {x : Fin m // b ∈ T → x = val b} =
      if b ∈ T then 1 else m := by
    intro b
    by_cases hb : b ∈ T
    · simp only [hb, ↓reduceIte, forall_true_left]
      exact Fintype.card_unique
    · simp only [hb, ↓reduceIte, IsEmpty.forall_iff]
      have hcard : Fintype.card {x : Fin m // True} = Fintype.card (Fin m) :=
        Fintype.card_congr ⟨fun x => x.1, fun y => ⟨y, trivial⟩, fun ⟨_, _⟩ => rfl, fun _ => rfl⟩
      rw [hcard, Fintype.card_fin]
  simp_rw [hfiber]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, one_mul]
  have h2 : (Finset.univ.filter (fun b : β => b ∉ T)).card = Fintype.card β - T.card := by
    have : Finset.univ.filter (fun b : β => b ∉ T) = Tᶜ := by ext b; simp
    rw [this, Finset.card_compl]
  rw [h2]

/-- **Multigraph Crossing Lemma (Finitary Wiring-Diagram Version)**:
For ANY wiring diagram `W` on `n` vertices and edge set `E` with max multiplicity `≤ m` (`m ≥ 1`),
if `4 * m * n ≤ E.card`, then `E.card ^ 3 ≤ 64 * m * n ^ 2 * W.totalSwaps`! -/
private theorem wiring_multigraph_crossing_lemma {n m : ℕ} {E : Finset (MEdge n)}
    (W : WiringDiagram n E) (hm : 1 ≤ m)
    (hmult : ∀ u v : Fin n, (E.filter (fun e => e.l = u ∧ e.r = v)).card ≤ m)
    (hdense : 4 * m * n ≤ E.card) :
    E.card ^ 3 ≤ 64 * m * n ^ 2 * W.totalSwaps := by
  obtain ⟨W', hW'_le, hdisj⟩ := W.exists_disjoint_swaps
  suffices hmain : E.card ^ 3 ≤ 64 * m * n ^ 2 * W'.totalSwaps by
    exact le_trans hmain (Nat.mul_le_mul_left _ hW'_le)
  -- Step 1: Rule out `n = 0` and deduce `n ≥ 4` (in fact `n ≥ 9`)!
  rcases eq_or_ne n 0 with rfl | hn0
  · have hE0 : E = ∅ := by ext e; exact Fin.elim0 e.l
    simp [hE0]
  have hn_ge4 : 4 ≤ n := by
    have hE_ub2 : E.card ≤ m * (n * (n - 1) / 2) := by
      have hpairs2 : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card * 2 ≤ n * (n - 1) := by
        have hdisj_lt : Disjoint (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
            (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)) := by
          rw [Finset.disjoint_left]; intro p h1 h2
          simp only [Finset.mem_filter] at h1 h2; exact absurd (lt_trans h1.2 h2.2) (lt_irrefl _)
        have hsymm : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card =
            (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)).card := by
          refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
          · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
          · intro p1 _ p2 _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
          · intro p hp; exact ⟨(p.2, p.1), by simpa using hp, rfl⟩
        have hsub : Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2) ∪
            Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1) ⊆
            (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.1 ≠ p.2) := by
          intro p hp
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, Finset.mem_product,
            true_and] at hp ⊢
          rcases hp with h | h
          · exact ne_of_lt h
          · exact ne_of_gt h
        have hcard_off : ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).card =
            n * (n - 1) := by
          have hsp : ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).card +
              ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.1 = p.2)).card = n * n := by
            rw [← Finset.card_union_of_disjoint]
            · have : (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.1 ≠ p.2) ∪
                  (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.1 = p.2) =
                  Finset.univ ×ˢ Finset.univ := by ext p; simp; tauto
              rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fin]
            · rw [Finset.disjoint_left]; intro p h1 h2
              simp only [Finset.mem_filter] at h1 h2; exact h1.2 h2.2
          have hdiag : ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.1 = p.2)).card = n := by
            trans (Finset.univ : Finset (Fin n)).card
            · refine Finset.card_bij (fun p _ => p.1) (fun _ _ => Finset.mem_univ _) ?_ ?_
              · intro p1 hp1 p2 hp2 h; simp only [Finset.mem_filter] at hp1 hp2
                exact Prod.ext h (hp1.2.symm.trans (h.trans hp2.2))
              · intro a _; exact ⟨(a, a), by simp, rfl⟩
            · exact Finset.card_fin n
          cases n with
          | zero => contradiction
          | succ k => rw [hdiag] at hsp; simp only [Nat.add_sub_cancel]; nlinarith
        have hle := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj_lt, ← hsymm, hcard_off] at hle
        omega
      have hpart2 : E.card ≤ m * (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card := by
        have hp : E.card = ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
            (E.filter (fun e => e.l = p.1 ∧ e.r = p.2)).card := by
          rw [← Finset.card_biUnion]
          · congr 1; ext e; simp [e.hlr]
          · intro p1 _ p2 _ hne; dsimp [Function.onFun]
            rw [Finset.disjoint_left]; intro e h1 h2
            simp only [Finset.mem_filter] at h1 h2
            exact hne (Prod.ext (h1.2.1.symm.trans h2.2.1) (h1.2.2.symm.trans h2.2.2))
        rw [hp]
        calc ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
              (E.filter (fun e => e.l = p.1 ∧ e.r = p.2)).card
            ≤ ∑ _p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), m :=
              Finset.sum_le_sum fun p _ => hmult p.1 p.2
          _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      have hdiv : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card ≤ n * (n - 1) / 2 :=
        (Nat.le_div_iff_mul_le (by norm_num)).mpr hpairs2
      exact le_trans hpart2 (Nat.mul_le_mul_left m hdiv)
    have h4n : 4 * n ≤ n * (n - 1) / 2 := by
      have : m * (4 * n) ≤ m * (n * (n - 1) / 2) := by linarith
      exact Nat.le_of_mul_le_mul_left this (by omega)
    have h8n : 8 * n ≤ n * (n - 1) := by
      have := Nat.div_mul_le_self (n * (n - 1)) 2; omega
    have h9 : 8 ≤ n - 1 := Nat.le_of_mul_le_mul_left (by linarith : n * 8 ≤ n * (n - 1)) (Nat.pos_of_ne_zero hn0)
    omega
  have hE_pos : 1 ≤ E.card := by nlinarith
  -- Step 2: Assign each edge `e ∈ E` a slot `slot e : Fin m` injective on each parallel class `(e.l, e.r)`!
  have hslot_ex : ∃ slot : MEdge n → Fin m,
      ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁.l = e₂.l → e₁.r = e₂.r → slot e₁ = slot e₂ → e₁ = e₂ := by
    have hfib : ∀ u v : Fin n,
        ∃ g : MEdge n → Fin m,
          ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁.l = u → e₁.r = v → e₂.l = u → e₂.r = v → g e₁ = g e₂ → e₁ = e₂ := by
      intro u v
      set F := E.filter (fun e => e.l = u ∧ e.r = v)
      have hcard : Fintype.card {e : MEdge n // e ∈ F} ≤ Fintype.card (Fin m) := by
        rw [Fintype.card_coe, Fintype.card_fin]; exact hmult u v
      obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
      refine ⟨fun e => if he : e ∈ F then emb ⟨e, he⟩ else ⟨0, hm⟩, ?_⟩
      intro e₁ h1 e₂ h2 hl1 hr1 hl2 hr2 heq
      have hf1 : e₁ ∈ F := Finset.mem_filter.mpr ⟨h1, hl1, hr1⟩
      have hf2 : e₂ ∈ F := Finset.mem_filter.mpr ⟨h2, hl2, hr2⟩
      simp only [hf1, hf2, ↓reduceDIte] at heq
      exact congrArg Subtype.val (emb.injective heq)
    choose g hg using hfib
    refine ⟨fun e => g e.l e.r e, fun e₁ h1 e₂ h2 hl hr hs => ?_⟩
    dsimp only at hs
    rw [← hl, ← hr] at hs
    exact hg e₁.l e₁.r e₁ h1 e₂ h2 rfl rfl hl.symm hr.symm hs
  obtain ⟨slot, hslot_inj⟩ := hslot_ex
  -- Step 3: Set `q = E.card`, `a = 4 * m * n ≤ q`, average over `(f, g) : (Fin n → Fin q) × (Fin n × Fin n → Fin m)`!
  set q := E.card
  set a := 4 * m * n
  have ha_le_q : a ≤ q := hdense
  let keep : (Fin n → Fin q) → (Fin n × Fin n → Fin m) → MEdge n → Bool :=
    fun f g e => decide ((f e.l).val < a ∧ (f e.r).val < a ∧ g (e.l, e.r) = slot e)
  have hpointwise : ∀ (f : Fin n → Fin q) (g : Fin n × Fin n → Fin m),
      (E.filter (fun e => keep f g e = true)).card ≤
        3 * (Finset.univ.filter (fun v : Fin n => (f v).val < a)).card +
        (W'.filter (keep f g)).totalSwaps := by
    intro f g
    set V := Finset.univ.filter (fun v : Fin n => (f v).val < a)
    set Efg := E.filter (fun e => keep f g e = true)
    set Wfg := W'.filter (keep f g)
    have hsim_fg : ∀ e₁ ∈ Efg, ∀ e₂ ∈ Efg, e₁.l = e₂.l → e₁.r = e₂.r → e₁ = e₂ := by
      intro e₁ h1 e₂ h2 hl hr
      simp only [Efg, Finset.mem_filter, keep, decide_eq_true_eq] at h1 h2
      have hs : slot e₁ = slot e₂ := by rw [← h1.2.2.2, ← h2.2.2.2, hl, hr]
      exact hslot_inj e₁ h1.1 e₂ h2.1 hl hr hs
    refine Wfg.card_le_three_mul_active_add_swaps V hsim_fg ?_
    intro e he
    simp only [Finset.mem_filter, keep, decide_eq_true_eq, V, Finset.mem_univ, true_and] at he ⊢
    exact ⟨he.2.1, he.2.2.1⟩
  have hsum_all :
      ∑ f : Fin n → Fin q, ∑ g : Fin n × Fin n → Fin m,
        (E.filter (fun e => keep f g e = true)).card ≤
      3 * (∑ f : Fin n → Fin q, ∑ g : Fin n × Fin n → Fin m,
            (Finset.univ.filter (fun v : Fin n => (f v).val < a)).card) +
      ∑ f : Fin n → Fin q, ∑ g : Fin n × Fin n → Fin m,
        (W'.filter (keep f g)).totalSwaps := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun f _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun g _ => hpointwise f g
  have hsum_V : ∑ f : Fin n → Fin q, ∑ _g : Fin n × Fin n → Fin m,
      (Finset.univ.filter (fun v : Fin n => (f v).val < a)).card =
      n * a * q ^ (n - 1) * m ^ (n * n) := by
    have hcard_g : Fintype.card (Fin n × Fin n → Fin m) = m ^ (n * n) := by
      rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    simp_rw [Finset.sum_const, Finset.card_univ, hcard_g, smul_eq_mul]
    rw [← Finset.mul_sum, mul_comm]
    congr 1
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    have hinner : ∀ v : Fin n,
        ∑ f : Fin n → Fin q, (if (f v).val < a then 1 else 0) = a * q ^ (n - 1) := by
      intro v
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      have heq := card_pi_lt_on_subset q a ha_le_q ({v} : Finset (Fin n))
      simp only [Finset.card_singleton, Fintype.card_fin, pow_one, Finset.mem_singleton,
        forall_eq] at heq
      exact heq
    simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hsum_E : ∑ f : Fin n → Fin q, ∑ g : Fin n × Fin n → Fin m,
      (E.filter (fun e => keep f g e = true)).card =
      E.card * a ^ 2 * q ^ (n - 2) * m ^ (n * n - 1) := by
    simp_rw [Finset.card_filter]
    trans ∑ f : Fin n → Fin q, ∑ e ∈ E, ∑ g : Fin n × Fin n → Fin m,
        (if keep f g e = true then 1 else 0)
    · refine Finset.sum_congr rfl fun f _ => Finset.sum_comm
    · rw [Finset.sum_comm]
      have hinner : ∀ e ∈ E,
          ∑ f : Fin n → Fin q, ∑ g : Fin n × Fin n → Fin m,
            (if keep f g e = true then 1 else 0) =
          a ^ 2 * q ^ (n - 2) * m ^ (n * n - 1) := by
        intro e _
        have hsplit : ∀ f g, (if keep f g e = true then (1 : ℕ) else 0) =
            (if (f e.l).val < a ∧ (f e.r).val < a then 1 else 0) *
            (if g (e.l, e.r) = slot e then 1 else 0) := by
          intro f g; dsimp [keep]; by_cases h1 : (f e.l).val < a ∧ (f e.r).val < a
          · by_cases h2 : g (e.l, e.r) = slot e <;> simp [h1, h2]
          · have : ¬((f e.l).val < a ∧ (f e.r).val < a ∧ g (e.l, e.r) = slot e) :=
              fun ⟨a1, a2, _⟩ => h1 ⟨a1, a2⟩
            simp [h1, this]
        simp_rw [hsplit, ← Finset.mul_sum, ← Finset.sum_mul]
        have hf_cnt : ∑ f : Fin n → Fin q, (if (f e.l).val < a ∧ (f e.r).val < a then 1 else 0) =
            a ^ 2 * q ^ (n - 2) := by
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
          have hne : e.l ≠ e.r := ne_of_lt e.hlr
          have heq := card_pi_lt_on_subset q a ha_le_q ({e.l, e.r} : Finset (Fin n))
          rw [Finset.card_pair hne, Fintype.card_fin] at heq
          convert heq using 2
          ext f; simp
        have hg_cnt : ∑ g : Fin n × Fin n → Fin m, (if g (e.l, e.r) = slot e then 1 else 0) =
            m ^ (n * n - 1) := by
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
          have heq := card_pi_eq_on_subset m ({(e.l, e.r)} : Finset (Fin n × Fin n))
            (fun _ => slot e)
          simp only [Finset.card_singleton, Fintype.card_prod, Fintype.card_fin,
            Finset.mem_singleton, forall_eq] at heq
          exact heq
        rw [hf_cnt, hg_cnt]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
      ring
  have hsum_K : ∑ f : Fin n → Fin q, ∑ g : Fin n × Fin n → Fin m,
      (W'.filter (keep f g)).totalSwaps =
      W'.totalSwaps * a ^ 4 * q ^ (n - 4) * m ^ (n * n - 2) := by
    unfold WiringDiagram.totalSwaps
    trans ∑ f : Fin n → Fin q, ∑ i : Fin n, ∑ g : Fin n × Fin n → Fin m,
        if hi : i.val + 1 < n then ((W'.filter (keep f g)).swaps i hi).length else 0
    · refine Finset.sum_congr rfl fun f _ => Finset.sum_comm
    · rw [Finset.sum_comm]
      have hinner_i : ∀ i : Fin n,
          ∑ f : Fin n → Fin q, ∑ g : Fin n × Fin n → Fin m,
            (if hi : i.val + 1 < n then ((W'.filter (keep f g)).swaps i hi).length else 0) =
          (if hi : i.val + 1 < n then (W'.swaps i hi).length else 0) *
            (a ^ 4 * q ^ (n - 4) * m ^ (n * n - 2)) := by
        intro i
        split_ifs with hi
        · dsimp [WiringDiagram.filter]
          have hlist : ∀ L : List (MEdge n × MEdge n),
              (∀ p ∈ L, p ∈ W'.swaps i hi) →
              ∑ f : Fin n → Fin q, ∑ g : Fin n × Fin n → Fin m,
                (L.filter (fun p => keep f g p.1 && keep f g p.2)).length =
              L.length * (a ^ 4 * q ^ (n - 4) * m ^ (n * n - 2)) := by
            intro L hL
            induction L with
            | nil => simp
            | cons p t iht =>
              have hp_mem : p ∈ W'.swaps i hi := hL p (by simp)
              have hd := hdisj i hi p hp_mem
              have hsplit_cons : ∀ f g,
                  ((p :: t).filter (fun r => keep f g r.1 && keep f g r.2)).length =
                  (if (keep f g p.1 && keep f g p.2) = true then 1 else 0) +
                  (t.filter (fun r => keep f g r.1 && keep f g r.2)).length := by
                intro f g; simp only [List.filter_cons]
                cases (keep f g p.1 && keep f g p.2) <;> simp; omega
              simp_rw [hsplit_cons, Finset.sum_add_distrib]
              rw [iht (fun r hr => hL r (by simp [hr])), List.length_cons, Nat.succ_mul, add_comm]
              congr 1
              have hprod : ∀ f g,
                  (if (keep f g p.1 && keep f g p.2) = true then (1 : ℕ) else 0) =
                  (if (f p.1.l).val < a ∧ (f p.1.r).val < a ∧ (f p.2.l).val < a ∧ (f p.2.r).val < a
                    then 1 else 0) *
                  (if g (p.1.l, p.1.r) = slot p.1 ∧ g (p.2.l, p.2.r) = slot p.2 then 1 else 0) := by
                intro f g
                simp only [Bool.and_eq_true, keep, decide_eq_true_eq]
                by_cases h1 : (f p.1.l).val < a ∧ (f p.1.r).val < a ∧ (f p.2.l).val < a ∧ (f p.2.r).val < a
                · by_cases h2 : g (p.1.l, p.1.r) = slot p.1 ∧ g (p.2.l, p.2.r) = slot p.2
                  · simp [h1, h2]
                  · have : ¬(((f p.1.l).val < a ∧ (f p.1.r).val < a ∧ g (p.1.l, p.1.r) = slot p.1) ∧
                        ((f p.2.l).val < a ∧ (f p.2.r).val < a ∧ g (p.2.l, p.2.r) = slot p.2)) :=
                      fun h => h2 ⟨h.1.2.2, h.2.2.2⟩
                    simp [h1, h2]
                · have hnot : ¬(((f p.1.l).val < a ∧ (f p.1.r).val < a ∧ g (p.1.l, p.1.r) = slot p.1) ∧
                      ((f p.2.l).val < a ∧ (f p.2.r).val < a ∧ g (p.2.l, p.2.r) = slot p.2)) :=
                    fun h => h1 ⟨h.1.1, h.1.2.1, h.2.1, h.2.2.1⟩
                  simp [h1, hnot]
              simp_rw [hprod, ← Finset.mul_sum, ← Finset.sum_mul]
              have hf4 : ∑ f : Fin n → Fin q,
                  (if (f p.1.l).val < a ∧ (f p.1.r).val < a ∧ (f p.2.l).val < a ∧ (f p.2.r).val < a
                    then 1 else 0) = a ^ 4 * q ^ (n - 4) := by
                rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
                set S4 : Finset (Fin n) := {p.1.l, p.1.r, p.2.l, p.2.r}
                have hS4_card : S4.card = 4 := by
                  have h12 : p.1.l ≠ p.1.r := ne_of_lt p.1.hlr
                  have h34 : p.2.l ≠ p.2.r := ne_of_lt p.2.hlr
                  dsimp [S4]
                  rw [Finset.card_insert_of_notMem (by simp [h12, hd.1, hd.2.1]),
                      Finset.card_insert_of_notMem (by simp [hd.2.2.1, hd.2.2.2]),
                      Finset.card_pair h34]
                have heq := card_pi_lt_on_subset q a ha_le_q S4
                rw [hS4_card, Fintype.card_fin] at heq
                convert heq using 2
                ext f; simp [S4]
              have hg2 : ∑ g : Fin n × Fin n → Fin m,
                  (if g (p.1.l, p.1.r) = slot p.1 ∧ g (p.2.l, p.2.r) = slot p.2 then 1 else 0) =
                  m ^ (n * n - 2) := by
                rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
                have hp_ne : (p.1.l, p.1.r) ≠ (p.2.l, p.2.r) := fun h => hd.1 (congrArg Prod.fst h)
                let val : Fin n × Fin n → Fin m :=
                  fun uv => if uv = (p.1.l, p.1.r) then slot p.1 else slot p.2
                have heq := card_pi_eq_on_subset m
                  ({(p.1.l, p.1.r), (p.2.l, p.2.r)} : Finset (Fin n × Fin n)) val
                rw [Finset.card_pair hp_ne, Fintype.card_prod, Fintype.card_fin] at heq
                convert heq using 2
                ext g; simp [val, Ne.symm hp_ne]
              rw [hf4, hg2]
          exact hlist (W'.swaps i hi) (fun _ h => h)
        · simp
      rw [Finset.sum_congr rfl (fun i _ => hinner_i i), ← Finset.sum_mul]
      ring
  rw [hsum_E, hsum_V, hsum_K] at hsum_all
  have hpow_q1 : q ^ (n - 1) = q ^ 3 * q ^ (n - 4) := by
    rw [← pow_add]; congr 1; omega
  have hpow_q2 : q ^ (n - 2) = q ^ 2 * q ^ (n - 4) := by
    rw [← pow_add]; congr 1; omega
  have hn2_ge2 : 2 ≤ n * n := by nlinarith
  have hpow_m0 : m ^ (n * n) = m ^ 2 * m ^ (n * n - 2) := by
    rw [← pow_add]; congr 1; omega
  have hpow_m1 : m ^ (n * n - 1) = m * m ^ (n * n - 2) := by
    have : m * m ^ (n * n - 2) = m ^ (1 + (n * n - 2)) := by rw [pow_add, pow_one]
    rw [this]; congr 1; omega
  rw [hpow_q1, hpow_q2, hpow_m0, hpow_m1] at hsum_all
  have hcommon_pos : 0 < q ^ (n - 4) * m ^ (n * n - 2) := by positivity
  have hfactor : (E.card * a ^ 2 * q ^ 2 * m) * (q ^ (n - 4) * m ^ (n * n - 2)) ≤
      (3 * n * a * q ^ 3 * m ^ 2 + W'.totalSwaps * a ^ 4) * (q ^ (n - 4) * m ^ (n * n - 2)) := by
    linarith
  have hcancel : E.card * a ^ 2 * q ^ 2 * m ≤ 3 * n * a * q ^ 3 * m ^ 2 + W'.totalSwaps * a ^ 4 :=
    Nat.le_of_mul_le_mul_right hfactor hcommon_pos
  have h4pos : 0 < 4 * m ^ 3 * n ^ 2 := by positivity
  have halg : (4 * m ^ 3 * n ^ 2) * E.card ^ 3 ≤
      (4 * m ^ 3 * n ^ 2) * (64 * m * n ^ 2 * W'.totalSwaps) := by
    have hL : E.card * a ^ 2 * q ^ 2 * m = 16 * m ^ 3 * n ^ 2 * E.card ^ 3 := by
      dsimp [a, q]; ring
    have hR1 : 3 * n * a * q ^ 3 * m ^ 2 = 12 * m ^ 3 * n ^ 2 * E.card ^ 3 := by
      dsimp [a, q]; ring
    have hR2 : W'.totalSwaps * a ^ 4 = (4 * m ^ 3 * n ^ 2) * (64 * m * n ^ 2 * W'.totalSwaps) := by
      dsimp [a]; ring
    rw [hL, hR1, hR2] at hcancel
    linarith
  exact Nat.le_of_mul_le_mul_left halg h4pos

/-! ### Section 4B: Bubble-Sort Inversion Count & X-Monotone Arc-to-Wiring Conversion -/

/-- Number of inversions in a list `L` with respect to a real key `g : α → ℝ`. -/
private noncomputable def invCount {α : Type*} (g : α → ℝ) : List α → ℕ
  | [] => 0
  | a :: t => (t.filter (fun b => decide (g b < g a))).length + invCount g t

private lemma invCount_eq_zero_iff_pairwise {α : Type*} (g : α → ℝ) (L : List α) :
    invCount g L = 0 ↔ L.Pairwise (fun a b => g a ≤ g b) := by
  induction L with
  | nil => simp [invCount]
  | cons a t ih =>
    simp only [invCount, Nat.add_eq_zero_iff, List.length_eq_zero_iff, List.filter_eq_nil_iff,
      decide_eq_true_eq, not_lt, List.pairwise_cons, ih]

private lemma exists_adj_inv_of_invCount_pos {α : Type*} (g : α → ℝ) (L : List α)
    (hpos : 0 < invCount g L) :
    ∃ (pre suf : List α) (a b : α), L = pre ++ [a, b] ++ suf ∧ g b < g a := by
  induction L with
  | nil => simp [invCount] at hpos
  | cons a t ih =>
    cases t with
    | nil => simp [invCount] at hpos
    | cons b t' =>
      by_cases hab : g b < g a
      · exact ⟨[], t', a, b, rfl, hab⟩
      · push Not at hab
        by_cases htail : 0 < invCount g (b :: t')
        · obtain ⟨pre, suf, x, y, heq, hxy⟩ := ih htail
          exact ⟨a :: pre, suf, x, y, by simp [heq], hxy⟩
        · exfalso
          have ht0 : invCount g (b :: t') = 0 := Nat.eq_zero_of_not_pos htail
          have hpw := (invCount_eq_zero_iff_pairwise g (b :: t')).mp ht0
          have hall : ∀ c ∈ b :: t', g a ≤ g c := by
            intro c hc
            rcases List.mem_cons.mp hc with rfl | hct'
            · exact hab
            · exact le_trans hab ((List.pairwise_cons.mp hpw).1 c hct')
          have hfilt : ((b :: t').filter (fun c => decide (g c < g a))).length = 0 := by
            rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
            intro c hc; simp only [decide_eq_true_eq, not_lt]; exact hall c hc
          change ((b :: t').filter (fun c => decide (g c < g a))).length + invCount g (b :: t') > 0 at hpos
          rw [hfilt, ht0] at hpos
          omega

private lemma invCount_swap_adj {α : Type*} (g : α → ℝ) (pre suf : List α) (a b : α)
    (hab : g b < g a) :
    invCount g (pre ++ [b, a] ++ suf) + 1 = invCount g (pre ++ [a, b] ++ suf) := by
  induction pre with
  | nil =>
    simp only [List.nil_append, List.cons_append, invCount, List.filter_cons,
      decide_eq_true_eq, hab, ↓reduceIte, not_lt.mpr (le_of_lt hab), List.length_cons]
    omega
  | cons c pre' ih =>
    simp only [List.cons_append, invCount]
    have hperm : (pre' ++ [b, a] ++ suf).Perm (pre' ++ [a, b] ++ suf) := by
      simp only [List.append_assoc]
      exact List.Perm.append_left pre' (List.Perm.append_right suf (List.Perm.swap a b []))
    have hflen : ((pre' ++ [b, a] ++ suf).filter (fun x => decide (g x < g c))).length =
        ((pre' ++ [a, b] ++ suf).filter (fun x => decide (g x < g c))).length :=
      (hperm.filter _).length_eq
    omega

/-- **Bubble-Sort `SwapSeq` Lemma**: Any nodup list `L₁` can be transformed into a permutation `L₂`
strictly sorted by `g` using exactly `invCount g L₁` adjacent swaps! -/
private lemma exists_swapSeq_sort {α : Type*} [DecidableEq α] (g : α → ℝ) (L₁ L₂ : List α)
    (hnd : L₁.Nodup) (hperm : L₁.Perm L₂) (hsort : L₂.Pairwise (fun a b => g a < g b)) :
    ∃ ps : List (α × α), ps.length = invCount g L₁ ∧ SwapSeq ps L₁ L₂ := by
  suffices hmain : ∀ k : ℕ, ∀ L : List α, L.Nodup → L.Perm L₂ → invCount g L = k →
      ∃ ps : List (α × α), ps.length = k ∧ SwapSeq ps L L₂ by
    exact hmain (invCount g L₁) L₁ hnd hperm rfl
  intro k
  induction k with
  | zero =>
    intro L hLnd hLperm hk0
    have hLpw : L.Pairwise (fun a b => g a ≤ g b) := (invCount_eq_zero_iff_pairwise g L).mp hk0
    have hLstrict : L.Pairwise (fun a b => g a < g b) := by
      have hginj : ∀ a ∈ L, ∀ b ∈ L, g a = g b → a = b := by
        intro a ha b hb hgab
        have ha2 : a ∈ L₂ := hLperm.mem_iff.mp ha
        have hb2 : b ∈ L₂ := hLperm.mem_iff.mp hb
        -- On `L₂`, `Pairwise (g · < g ·)` implies `g` is injective on `L₂`!
        by_contra hne
        have hlt_or : g a < g b ∨ g b < g a := by
          clear hLnd hLperm hk0 hLpw ha hb hperm hnd
          induction L₂ with
          | nil => cases ha2
          | cons x t iht =>
            have hpw := List.pairwise_cons.mp hsort
            rcases List.mem_cons.mp ha2 with rfl | hat <;>
            rcases List.mem_cons.mp hb2 with rfl | hbt
            · exact absurd rfl hne
            · exact Or.inl (hpw.1 b hbt)
            · exact Or.inr (hpw.1 a hat)
            · exact iht hpw.2 hat hbt
        rcases hlt_or with h | h <;> linarith
      refine List.Pairwise.imp_of_mem ?_ (hLpw.and hLnd)
      intro a b ha hb ⟨hle, hne⟩
      exact lt_of_le_of_ne hle (fun heq => hne (hginj a ha b hb heq))
    have hLeq : L = L₂ := List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 =>
      absurd (lt_trans h1 h2) (lt_irrefl _)) hLstrict hsort hLperm
    subst hLeq
    exact ⟨[], rfl, SwapSeq.nil L⟩
  | succ k ih =>
    intro L hLnd hLperm hk
    obtain ⟨pre, suf, a, b, rfl, hab⟩ := exists_adj_inv_of_invCount_pos g L (by omega)
    set L' := pre ++ [b, a] ++ suf
    have hsw : (pre ++ [a, b] ++ suf).Perm L' := by
      simp only [L', List.append_assoc]
      exact List.Perm.append_left pre (List.Perm.append_right suf (List.Perm.swap b a []))
    have hinv' : invCount g L' = k := by
      have := invCount_swap_adj g pre suf a b hab; dsimp [L']; omega
    obtain ⟨ps', hlen', hseq'⟩ := ih L' (hsw.nodup_iff.mp hLnd) (hsw.symm.trans hLperm) hinv'
    exact ⟨(a, b) :: ps', by simp [hlen'], SwapSeq.cons ⟨pre, suf, rfl, rfl⟩ hseq'⟩

/-- Characterization of `invCount g L` as unordered inversion pairs when `L` is strictly sorted by `f`. -/
private lemma invCount_eq_card_inversions {α : Type*} [DecidableEq α]
    (f g : α → ℝ) (L : List α) (hnd : L.Nodup) (hsort : L.Pairwise (fun a b => f a < f b)) :
    invCount g L =
      ((L.toFinset ×ˢ L.toFinset).filter (fun p => f p.1 < f p.2 ∧ g p.2 < g p.1)).card := by
  induction L with
  | nil => simp [invCount]
  | cons a t ih =>
    have hnd' := List.nodup_cons.mp hnd
    have hpw := List.pairwise_cons.mp hsort
    have iht := ih hnd'.2 hpw.2
    simp only [invCount, iht]
    -- Split `((insert a t.toFinset) ×ˢ (insert a t.toFinset)).filter ...` into `p.1 = a` and `p.1 ∈ t.toFinset`!
    set S := ((a :: t).toFinset ×ˢ (a :: t).toFinset).filter (fun p => f p.1 < f p.2 ∧ g p.2 < g p.1)
    set S₁ := (t.toFinset.filter (fun b => g b < g a)).image (fun b => (a, b))
    set S₂ := (t.toFinset ×ˢ t.toFinset).filter (fun p => f p.1 < f p.2 ∧ g p.2 < g p.1)
    have hS_eq : S = S₁ ∪ S₂ := by
      ext ⟨x, y⟩
      simp only [S, S₁, S₂, List.toFinset_cons, Finset.mem_union, Finset.mem_filter,
        Finset.mem_product, Finset.mem_insert, Finset.mem_image, List.mem_toFinset]
      constructor
      · rintro ⟨⟨hx | hx, hy | hy⟩, hfx, hgy⟩
        · subst hx; subst hy; exact absurd hfx (lt_irrefl _)
        · subst hx; exact Or.inl ⟨y, ⟨hy, hgy⟩, rfl⟩
        · subst hy; exact absurd (lt_trans hfx (hpw.1 x hx)) (lt_irrefl _)
        · exact Or.inr ⟨⟨hx, hy⟩, hfx, hgy⟩
      · rintro (⟨b, ⟨hbt, hgb⟩, heq⟩ | ⟨⟨hx, hy⟩, hfx, hgy⟩)
        · injection heq with h1 h2; subst h1; subst h2
          exact ⟨⟨Or.inl rfl, Or.inr hbt⟩, hpw.1 b hbt, hgb⟩
        · exact ⟨⟨Or.inr hx, Or.inr hy⟩, hfx, hgy⟩
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]; intro ⟨x, y⟩ h1 h2
      simp only [S₁, S₂, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
        List.mem_toFinset] at h1 h2
      obtain ⟨b, _, heq⟩ := h1
      have hx : x = a := (Prod.mk.inj heq).1.symm
      exact hnd'.1 (hx ▸ h2.1.1)
    rw [hS_eq, Finset.card_union_of_disjoint hdisj]
    congr 1
    rw [Finset.card_image_of_injOn (fun b1 _ b2 _ h => (Prod.mk.inj h).2)]
    rw [← List.toFinset_card_of_nodup (hnd'.2.filter _)]
    congr 1; ext b; simp

/-- Sorting a `Finset` by an injective real key `f : α → ℝ` gives a strictly sorted nodup `List`. -/
private noncomputable def sortByKey {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ) : List α :=
  (S.image f).sort (· ≤ ·) |>.filterMap (fun r => if h : ∃ a ∈ S, f a = r then some (Classical.choose h) else none)

private lemma sortByKey_spec {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ)
    (hinj : Set.InjOn f (S : Set α)) :
    (sortByKey S f).Nodup ∧
    (∀ a, a ∈ sortByKey S f ↔ a ∈ S) ∧
    (sortByKey S f).Pairwise (fun a b => f a < f b) := by
  set R := (S.image f).sort (· ≤ ·)
  have hR_nd : R.Nodup := Finset.sort_nodup _ _
  have hR_pw : R.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hR_strict : R.Pairwise (· < ·) := by
    refine List.Pairwise.imp_of_mem ?_ (hR_pw.and hR_nd)
    intro x y _ _ ⟨hle, hne⟩; exact lt_of_le_of_ne hle hne
  have hchoose : ∀ r (h : ∃ a ∈ S, f a = r), Classical.choose h ∈ S ∧ f (Classical.choose h) = r :=
    fun r h => Classical.choose_spec h
  -- Actually `sortByKey S f = R.map (fun r => ...)` since every `r ∈ R` IS in `S.image f`!
  have hR_mem : ∀ r ∈ R, ∃ a ∈ S, f a = r := by
    intro r hr
    have := (Finset.mem_sort (· ≤ ·)).mp hr
    exact Finset.mem_image.mp this
  -- Prove the 3 properties directly on `List.filterMap`!
  let φ : ℝ → Option α := fun r => if h : ∃ a ∈ S, f a = r then some (Classical.choose h) else none
  have hmem_iff : ∀ a, a ∈ sortByKey S f ↔ a ∈ S := by
    intro a
    simp only [sortByKey, List.mem_filterMap]
    constructor
    · rintro ⟨r, _, hopt⟩
      split_ifs at hopt with hex
      · injection hopt with heq; rw [← heq]; exact (hchoose r hex).1
    · intro ha
      have hr : f a ∈ R := (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      have hex : ∃ b ∈ S, f b = f a := ⟨a, ha, rfl⟩
      refine ⟨f a, hr, ?_⟩
      simp only [hex, ↓reduceDIte, Option.some.injEq]
      exact hinj (hchoose (f a) hex).1 ha (hchoose (f a) hex).2
  have hpw_strict : (sortByKey S f).Pairwise (fun a b => f a < f b) := by
    dsimp [sortByKey]
    have hgen : ∀ L : List ℝ, L.Pairwise (· < ·) →
        (L.filterMap (fun r => if h : ∃ a ∈ S, f a = r then some (Classical.choose h) else none)).Pairwise
          (fun a b => f a < f b) := by
      intro L hL
      induction L with
      | nil => simp
      | cons r t ih =>
        have hpw := List.pairwise_cons.mp hL
        simp only [List.filterMap_cons]
        split_ifs with hex
        · rw [List.pairwise_cons]
          refine ⟨fun b hb => ?_, ih hpw.2⟩
          simp only [List.mem_filterMap] at hb
          obtain ⟨r', hr', hopt⟩ := hb
          split_ifs at hopt with hex'
          · injection hopt with hb_eq
            rw [(hchoose r hex).2, ← hb_eq, (hchoose r' hex').2]
            exact hpw.1 r' hr'
        · exact ih hpw.2
    exact hgen R hR_strict
  have hnd : (sortByKey S f).Nodup :=
    hpw_strict.imp (fun {a b} hlt heq => absurd (heq ▸ hlt) (lt_irrefl _))
  exact ⟨hnd, hmem_iff, hpw_strict⟩

private lemma pairwise_le_of_getLast? {L : List ℝ} {c : ℝ}
    (hpw : L.Pairwise (· ≤ ·)) (hgl : L.getLast? = some c) : ∀ t ∈ L, t ≤ c := by
  induction L with
  | nil => simp at hgl
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hgl
      subst hgl; intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact le_rfl
    | cons b rest' =>
      have hpw' := List.pairwise_cons.mp hpw
      have hgl' : (b :: rest').getLast? = some c := by simpa using hgl
      intro t ht
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact hpw'.1 c (List.mem_of_getLast? hgl')
      · exact ih hpw'.2 hgl' t hmem

private lemma fin_succ_le_of_lt {n : ℕ} {a b : Fin n} (h : a < b) (ha : a.val + 1 < n) :
    (⟨a.val + 1, ha⟩ : Fin n) ≤ b := Fin.le_def.mpr h

private lemma fin_le_pred_of_lt {n : ℕ} {a b : Fin n} (h : a < b) (hb : 0 < b.val) :
    a ≤ (⟨b.val - 1, by omega⟩ : Fin n) := Fin.le_def.mpr (by have := Fin.lt_def.mp h; dsimp only; omega)

/-- **X-Monotone Continuous Arc Family → Wiring Diagram Conversion**:
Given `n` vertices with strictly increasing `x`-coordinates `x : Fin n → ℝ`, vertex heights
`yv : Fin n → ℝ`, a finite edge set `E : Finset (MEdge n)` with continuous curves `arc e : ℝ → ℝ`
avoiding non-endpoint vertices, and a finite set `Crit : Finset ℝ` containing every pairwise
intersection `x`-coordinate of distinct arcs on their overlapping open domains, there exists a
`WiringDiagram n E` with:
`2 * W.totalSwaps ≤ ∑ t ∈ Crit, ((E ×ˢ E).filter (fun p => p.1 ≠ p.2 ∧ x p.1.l < t ∧ t < x p.1.r ∧ x p.2.l < t ∧ t < x p.2.r ∧ arc p.1 t = arc p.2 t)).card`! -/
private theorem xmonotone_to_wiring {n : ℕ}
    (x yv : Fin n → ℝ) (hx : StrictMono x)
    (E : Finset (MEdge n))
    (arc : MEdge n → ℝ → ℝ)
    (hcont : ∀ e ∈ E, ContinuousOn (arc e) (Set.Icc (x e.l) (x e.r)))
    (hl_val : ∀ e ∈ E, arc e (x e.l) = yv e.l)
    (hr_val : ∀ e ∈ E, arc e (x e.r) = yv e.r)
    (havoid : ∀ e ∈ E, ∀ i : Fin n, e.l < i → i < e.r → arc e (x i) ≠ yv i)
    (Crit : Finset ℝ)
    (hCrit : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ≠ e₂ → ∀ t : ℝ,
      x e₁.l < t → t < x e₁.r → x e₂.l < t → t < x e₂.r → arc e₁ t = arc e₂ t → t ∈ Crit) :
    ∃ W : WiringDiagram n E,
      2 * W.totalSwaps ≤
        ∑ t ∈ Crit, ((E ×ˢ E).filter (fun p => p.1 ≠ p.2 ∧
          x p.1.l < t ∧ t < x p.1.r ∧ x p.2.l < t ∧ t < x p.2.r ∧
          arc p.1 t = arc p.2 t)).card := by
  -- Helper: IVT crossing detector on `[a, b]`!
  have hivt : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ≠ e₂ → ∀ a b : ℝ, a < b →
      x e₁.l ≤ a → b ≤ x e₁.r → x e₂.l ≤ a → b ≤ x e₂.r →
      arc e₁ a < arc e₂ a → arc e₂ b < arc e₁ b →
      ∃ t ∈ Set.Ioo a b, arc e₁ t = arc e₂ t := by
    intro e₁ h1 e₂ h2 _ a b hab ha1 hb1 ha2 hb2 hfa hfb
    have hc1 : ContinuousOn (arc e₁) (Set.Icc a b) :=
      (hcont e₁ h1).mono (Set.Icc_subset_Icc ha1 hb1)
    have hc2 : ContinuousOn (arc e₂) (Set.Icc a b) :=
      (hcont e₂ h2).mono (Set.Icc_subset_Icc ha2 hb2)
    have hdiff : ContinuousOn (fun t => arc e₂ t - arc e₁ t) (Set.Icc a b) := hc2.sub hc1
    have h0_mem : (0 : ℝ) ∈ Set.Icc (arc e₂ b - arc e₁ b) (arc e₂ a - arc e₁ a) :=
      ⟨by linarith, by linarith⟩
    obtain ⟨t, ht_Icc, ht_eq⟩ := intermediate_value_Icc' (le_of_lt hab) hdiff h0_mem
    have hta : a < t := by
      refine lt_of_le_of_ne ht_Icc.1 ?_
      intro h; rw [← h] at ht_eq; linarith
    have htb : t < b := by
      refine lt_of_le_of_ne ht_Icc.2 ?_
      intro h; rw [h] at ht_eq; linarith
    exact ⟨t, ⟨hta, htb⟩, by linarith⟩
  -- For each slab `i` (`i.val + 1 < n`), define the sorted list of critical points strictly inside `(x i, x (i+1))`:
  let slabCrits (i : Fin n) (hi : i.val + 1 < n) : List ℝ :=
    (Crit.filter (fun t => x i < t ∧ t < x ⟨i.val + 1, hi⟩)).sort (· ≤ ·)
  -- Let `sFirst i hi` be the first midpoint (strictly in `(x i, c₁)` or `(x i, x (i+1))`),
  -- and `sLast i hi` be the last midpoint (strictly in `(c_k, x (i+1))` or `(x i, x (i+1))`).
  let sFirst (i : Fin n) (hi : i.val + 1 < n) : ℝ :=
    match slabCrits i hi with
    | [] => (x i + x ⟨i.val + 1, hi⟩) / 2
    | c :: _ => (x i + c) / 2
  let sLast (i : Fin n) (hi : i.val + 1 < n) : ℝ :=
    match (slabCrits i hi).getLast? with
    | none => (x i + x ⟨i.val + 1, hi⟩) / 2
    | some c => (c + x ⟨i.val + 1, hi⟩) / 2
  -- Verify `sFirst i hi` and `sLast i hi` have NO critical points in `(x i, sFirst i hi]` and `[sLast i hi, x (i+1))`!
  have hsFirst_prop : ∀ (i : Fin n) (hi : i.val + 1 < n),
      x i < sFirst i hi ∧ sFirst i hi < x ⟨i.val + 1, hi⟩ ∧
      ∀ t ∈ Crit, ¬(x i < t ∧ t ≤ sFirst i hi) := by
    intro i hi
    have hxi : x i < x ⟨i.val + 1, hi⟩ := hx (Fin.lt_def.mpr (by simp))
    dsimp [sFirst]
    cases hsc : slabCrits i hi with
    | nil =>
      refine ⟨by linarith, by linarith, fun t ht ⟨h1, h2⟩ => ?_⟩
      have hmem : t ∈ slabCrits i hi :=
        (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_filter.mpr ⟨ht, h1, lt_of_le_of_lt h2 (by linarith)⟩)
      rw [hsc] at hmem; cases hmem
    | cons c rest =>
      have hc_mem : c ∈ Crit ∧ x i < c ∧ c < x ⟨i.val + 1, hi⟩ := by
        have h1 : c ∈ slabCrits i hi := by rw [hsc]; simp
        have h2 := Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp h1)
        exact ⟨h2.1, h2.2.1, h2.2.2⟩
      refine ⟨by linarith [hc_mem.2.1], by linarith [hc_mem.2.2], fun t ht ⟨h1, h2⟩ => ?_⟩
      have hmem : t ∈ slabCrits i hi :=
        (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_filter.mpr ⟨ht, h1, lt_of_le_of_lt h2 (by linarith)⟩)
      rw [hsc] at hmem
      have hpw : (c :: rest).Pairwise (· ≤ ·) := hsc ▸ Finset.pairwise_sort _ _
      rcases List.mem_cons.mp hmem with rfl | hrest
      · linarith [hc_mem.2.1]
      · have hct : c ≤ t := (List.pairwise_cons.mp hpw).1 t hrest
        linarith [hc_mem.2.1]
  have hsLast_prop : ∀ (i : Fin n) (hi : i.val + 1 < n),
      x i < sLast i hi ∧ sLast i hi < x ⟨i.val + 1, hi⟩ ∧
      ∀ t ∈ Crit, ¬(sLast i hi ≤ t ∧ t < x ⟨i.val + 1, hi⟩) := by
    intro i hi
    have hxi : x i < x ⟨i.val + 1, hi⟩ := hx (Fin.lt_def.mpr (by simp))
    dsimp [sLast]
    cases hgl : (slabCrits i hi).getLast? with
    | none =>
      have hnil : slabCrits i hi = [] := List.getLast?_eq_none_iff.mp hgl
      refine ⟨by linarith, by linarith, fun t ht ⟨h1, h2⟩ => ?_⟩
      have hmem : t ∈ slabCrits i hi :=
        (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_filter.mpr ⟨ht, lt_of_lt_of_le (by linarith) h1, h2⟩)
      rw [hnil] at hmem; cases hmem
    | some c =>
      have hc_mem : c ∈ Crit ∧ x i < c ∧ c < x ⟨i.val + 1, hi⟩ := by
        have h1 : c ∈ slabCrits i hi := List.mem_of_getLast? hgl
        have h2 := Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp h1)
        exact ⟨h2.1, h2.2.1, h2.2.2⟩
      refine ⟨by linarith [hc_mem.2.1], by linarith [hc_mem.2.2], fun t ht ⟨h1, h2⟩ => ?_⟩
      have hmem : t ∈ slabCrits i hi :=
        (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_filter.mpr ⟨ht, lt_of_lt_of_le (by linarith) h1, h2⟩)
      have htc : t ≤ c := pairwise_le_of_getLast? (Finset.pairwise_sort _ _) hgl t hmem
      linarith [hc_mem.2.2]
  -- Active edges in slab `i` (`i.val + 1 < n`):
  let active (i : Fin n) (hi : i.val + 1 < n) : Finset (MEdge n) :=
    E.filter (fun e => e.l ≤ i ∧ ⟨i.val + 1, hi⟩ ≤ e.r)
  -- At any `s ∈ (x i, x (i+1)) \ Crit`, `arc · s` is injective on `active i hi`!
  have harc_inj : ∀ (i : Fin n) (hi : i.val + 1 < n) (s : ℝ),
      x i < s → s < x ⟨i.val + 1, hi⟩ → s ∉ Crit →
      Set.InjOn (fun e => arc e s) (active i hi : Set (MEdge n)) := by
    intro i hi s hs1 hs2 hs_nc e₁ h1 e₂ h2 heq
    by_contra hne
    simp only [active, Finset.mem_coe, Finset.mem_filter] at h1 h2
    have h1l : x e₁.l < s := lt_of_le_of_lt (hx.monotone h1.2.1) hs1
    have h1r : s < x e₁.r := lt_of_lt_of_le hs2 (hx.monotone h1.2.2)
    have h2l : x e₂.l < s := lt_of_le_of_lt (hx.monotone h2.2.1) hs1
    have h2r : s < x e₂.r := lt_of_lt_of_le hs2 (hx.monotone h2.2.2)
    exact hs_nc (hCrit e₁ h1.1 e₂ h2.1 hne s h1l h1r h2l h2r heq)
  -- Define `B i, A i, InL i, OutL i` for each `i : Fin n`!
  -- For `i.val > 0`, let `prev i hi0 := ⟨i.val - 1, _⟩` and `sPrev := sLast (prev i) _`.
  -- Passing edges below `v_i`: `E_B i = {e ∈ E : e.l < i ∧ i < e.r ∧ arc e (x i) < yv i}`.
  -- Passing edges above `v_i`: `E_A i = {e ∈ E : e.l < i ∧ i < e.r ∧ yv i < arc e (x i)}`.
  let E_B (i : Fin n) : Finset (MEdge n) := E.filter (fun e => e.l < i ∧ i < e.r ∧ arc e (x i) < yv i)
  let E_A (i : Fin n) : Finset (MEdge n) := E.filter (fun e => e.l < i ∧ i < e.r ∧ yv i < arc e (x i))
  let E_In (i : Fin n) : Finset (MEdge n) := E.filter (fun e => e.r = i)
  let E_Out (i : Fin n) : Finset (MEdge n) := E.filter (fun e => e.l = i)
  let B_list (i : Fin n) : List (MEdge n) :=
    if hi0 : 0 < i.val then
      let p : Fin n := ⟨i.val - 1, by omega⟩
      have hp : p.val + 1 < n := by dsimp [p]; omega
      sortByKey (E_B i) (fun e => arc e (sLast p hp))
    else []
  let A_list (i : Fin n) : List (MEdge n) :=
    if hi0 : 0 < i.val then
      let p : Fin n := ⟨i.val - 1, by omega⟩
      have hp : p.val + 1 < n := by dsimp [p]; omega
      sortByKey (E_A i) (fun e => arc e (sLast p hp))
    else []
  let In_list (i : Fin n) : List (MEdge n) :=
    if hi0 : 0 < i.val then
      let p : Fin n := ⟨i.val - 1, by omega⟩
      have hp : p.val + 1 < n := by dsimp [p]; omega
      sortByKey (E_In i) (fun e => arc e (sLast p hp))
    else []
  let Out_list (i : Fin n) : List (MEdge n) :=
    if hi : i.val + 1 < n then
      sortByKey (E_Out i) (fun e => arc e (sFirst i hi))
    else []
  -- Key separation lemma at `sLast p hp` (just before `x i` where `i = p + 1`):
  -- For `e₁ ∈ E_B i, f ∈ E_In i, e₂ ∈ E_A i`: `arc e₁ s < arc f s < arc e₂ s`!
  have hsep_before : ∀ (p : Fin n) (hp : p.val + 1 < n),
      let i : Fin n := ⟨p.val + 1, hp⟩
      let s := sLast p hp
      (∀ e ∈ E_B i, ∀ f ∈ E_In i, arc e s < arc f s) ∧
      (∀ f ∈ E_In i, ∀ e ∈ E_A i, arc f s < arc e s) ∧
      (∀ e₁ ∈ E_B i, ∀ e₂ ∈ E_A i, arc e₁ s < arc e₂ s) := by
    intro p hp i s
    have hsp := hsLast_prop p hp
    have hs_nc : s ∉ Crit := fun hc => hsp.2.2 s hc ⟨le_rfl, hsp.2.1⟩
    -- Generic IVT ordering helper: if `e₁, e₂ ∈ active p hp` and `arc e₁ (x i) < arc e₂ (x i)`, then `arc e₁ s < arc e₂ s`!
    have hord : ∀ e₁ ∈ active p hp, ∀ e₂ ∈ active p hp, arc e₁ (x i) < arc e₂ (x i) → arc e₁ s < arc e₂ s := by
      intro e₁ h1 e₂ h2 hlt
      have hne : e₁ ≠ e₂ := fun heq => absurd (heq ▸ hlt) (lt_irrefl _)
      have hneq_s : arc e₁ s ≠ arc e₂ s := fun heq => hne (harc_inj p hp s hsp.1 hsp.2.1 hs_nc h1 h2 heq)
      rcases lt_or_gt_of_ne hneq_s with h | h
      · exact h
      · exfalso
        simp only [active, Finset.mem_filter] at h1 h2
        have ⟨t, ht, hteq⟩ := hivt e₂ h2.1 e₁ h1.1 hne.symm s (x i) hsp.2.1
          (le_of_lt (lt_of_le_of_lt (hx.monotone h2.2.1) hsp.1)) (hx.monotone h2.2.2)
          (le_of_lt (lt_of_le_of_lt (hx.monotone h1.2.1) hsp.1)) (hx.monotone h1.2.2) h hlt
        have htC : t ∈ Crit := hCrit e₂ h2.1 e₁ h1.1 hne.symm t
          (lt_of_le_of_lt (hx.monotone h2.2.1) (lt_trans hsp.1 ht.1))
          (lt_of_lt_of_le ht.2 (hx.monotone h2.2.2))
          (lt_of_le_of_lt (hx.monotone h1.2.1) (lt_trans hsp.1 ht.1))
          (lt_of_lt_of_le ht.2 (hx.monotone h1.2.2)) hteq
        exact hsp.2.2 t htC ⟨le_of_lt ht.1, ht.2⟩
    have hB_act : ∀ e ∈ E_B i, e ∈ active p hp := fun e he => by
      simp only [E_B, active, Finset.mem_filter] at he ⊢
      exact ⟨he.1, Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.1; dsimp [i] at this; omega),
        le_of_lt he.2.2.1⟩
    have hA_act : ∀ e ∈ E_A i, e ∈ active p hp := fun e he => by
      simp only [E_A, active, Finset.mem_filter] at he ⊢
      exact ⟨he.1, Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.1; dsimp [i] at this; omega),
        le_of_lt he.2.2.1⟩
    have hIn_act : ∀ f ∈ E_In i, f ∈ active p hp := fun f hf => by
      simp only [E_In, active, Finset.mem_filter] at hf ⊢
      exact ⟨hf.1, Fin.le_def.mpr (by have := Fin.lt_def.mp (hf.2 ▸ f.hlr); dsimp [i] at this; omega),
        le_of_eq hf.2.symm⟩
    refine ⟨fun e he f hf => hord e (hB_act e he) f (hIn_act f hf) ?_,
            fun f hf e he => hord f (hIn_act f hf) e (hA_act e he) ?_,
            fun e₁ h1 e₂ h2 => hord e₁ (hB_act e₁ h1) e₂ (hA_act e₂ h2) ?_⟩
    · simp only [E_B, E_In, Finset.mem_filter] at he hf
      rw [← hf.2, hr_val f hf.1, hf.2]; exact he.2.2.2
    · simp only [E_A, E_In, Finset.mem_filter] at he hf
      rw [← hf.2, hr_val f hf.1, hf.2]; exact he.2.2.2
    · simp only [E_B, E_A, Finset.mem_filter] at h1 h2
      exact lt_trans h1.2.2.2 h2.2.2.2
  -- Symmetric separation lemma at `sFirst i hi` (just after `x i`):
  have hsep_after : ∀ (i : Fin n) (hi : i.val + 1 < n),
      let s := sFirst i hi
      (∀ e ∈ E_B i, ∀ g ∈ E_Out i, arc e s < arc g s) ∧
      (∀ g ∈ E_Out i, ∀ e ∈ E_A i, arc g s < arc e s) ∧
      (∀ e₁ ∈ E_B i, ∀ e₂ ∈ E_A i, arc e₁ s < arc e₂ s) := by
    intro i hi s
    have hsp := hsFirst_prop i hi
    have hs_nc : s ∉ Crit := fun hc => hsp.2.2 s hc ⟨hsp.1, le_rfl⟩
    have hord : ∀ e₁ ∈ active i hi, ∀ e₂ ∈ active i hi, arc e₁ (x i) < arc e₂ (x i) → arc e₁ s < arc e₂ s := by
      intro e₁ h1 e₂ h2 hlt
      have hne : e₁ ≠ e₂ := fun heq => absurd (heq ▸ hlt) (lt_irrefl _)
      have hneq_s : arc e₁ s ≠ arc e₂ s := fun heq => hne (harc_inj i hi s hsp.1 hsp.2.1 hs_nc h1 h2 heq)
      rcases lt_or_gt_of_ne hneq_s with h | h
      · exact h
      · exfalso
        simp only [active, Finset.mem_filter] at h1 h2
        have ⟨t, ht, hteq⟩ := hivt e₁ h1.1 e₂ h2.1 hne (x i) s hsp.1
          (hx.monotone h1.2.1) (le_of_lt (lt_of_lt_of_le hsp.2.1 (hx.monotone h1.2.2)))
          (hx.monotone h2.2.1) (le_of_lt (lt_of_lt_of_le hsp.2.1 (hx.monotone h2.2.2))) hlt h
        have htC : t ∈ Crit := hCrit e₁ h1.1 e₂ h2.1 hne t
          (lt_of_le_of_lt (hx.monotone h1.2.1) ht.1)
          (lt_of_lt_of_le (lt_trans ht.2 hsp.2.1) (hx.monotone h1.2.2))
          (lt_of_le_of_lt (hx.monotone h2.2.1) ht.1)
          (lt_of_lt_of_le (lt_trans ht.2 hsp.2.1) (hx.monotone h2.2.2)) hteq
        exact hsp.2.2 t htC ⟨ht.1, le_of_lt ht.2⟩
    have hB_act : ∀ e ∈ E_B i, e ∈ active i hi := fun e he => by
      simp only [E_B, active, Finset.mem_filter] at he ⊢
      exact ⟨he.1, le_of_lt he.2.1, fin_succ_le_of_lt he.2.2.1 hi⟩
    have hA_act : ∀ e ∈ E_A i, e ∈ active i hi := fun e he => by
      simp only [E_A, active, Finset.mem_filter] at he ⊢
      exact ⟨he.1, le_of_lt he.2.1, fin_succ_le_of_lt he.2.2.1 hi⟩
    have hOut_act : ∀ g ∈ E_Out i, g ∈ active i hi := fun g hg => by
      simp only [E_Out, active, Finset.mem_filter] at hg ⊢
      exact ⟨hg.1, le_of_eq hg.2, fin_succ_le_of_lt (hg.2 ▸ g.hlr) hi⟩
    refine ⟨fun e he g hg => hord e (hB_act e he) g (hOut_act g hg) ?_,
            fun g hg e he => hord g (hOut_act g hg) e (hA_act e he) ?_,
            fun e₁ h1 e₂ h2 => hord e₁ (hB_act e₁ h1) e₂ (hA_act e₂ h2) ?_⟩
    · simp only [E_B, E_Out, Finset.mem_filter] at he hg
      rw [← hg.2, hl_val g hg.1, hg.2]; exact he.2.2.2
    · simp only [E_A, E_Out, Finset.mem_filter] at he hg
      rw [← hg.2, hl_val g hg.1, hg.2]; exact he.2.2.2
    · simp only [E_B, E_A, Finset.mem_filter] at h1 h2
      exact lt_trans h1.2.2.2 h2.2.2.2
  -- For any `i` with `hi : i.val + 1 < n`, notice `before (i+1) = B_list (i+1) ++ In_list (i+1) ++ A_list (i+1)`
  -- is STRICTLY SORTED by `arc · (sLast i hi)` and is a permutation of `active i hi`!
  have hbefore_eq_sort : ∀ (i : Fin n) (hi : i.val + 1 < n),
      let j : Fin n := ⟨i.val + 1, hi⟩
      (B_list j ++ In_list j ++ A_list j).Nodup ∧
      (∀ e, e ∈ B_list j ++ In_list j ++ A_list j ↔ e ∈ active i hi) ∧
      (B_list j ++ In_list j ++ A_list j).Pairwise (fun e₁ e₂ => arc e₁ (sLast i hi) < arc e₂ (sLast i hi)) := by
    intro i hi j
    have hj0 : 0 < j.val := by dsimp [j]; omega
    have hp_eq : (⟨j.val - 1, by omega⟩ : Fin n) = i := Fin.ext (by dsimp [j])
    have hsp := hsLast_prop i hi
    have hs_nc : sLast i hi ∉ Crit := fun hc => hsp.2.2 _ hc ⟨le_rfl, hsp.2.1⟩
    have hinj_act := harc_inj i hi (sLast i hi) hsp.1 hsp.2.1 hs_nc
    have hB_sub : E_B j ⊆ active i hi := fun e he => by
      simp only [E_B, active, Finset.mem_filter] at he ⊢
      exact ⟨he.1, Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.1; dsimp [j] at this; omega),
        le_of_lt he.2.2.1⟩
    have hA_sub : E_A j ⊆ active i hi := fun e he => by
      simp only [E_A, active, Finset.mem_filter] at he ⊢
      exact ⟨he.1, Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.1; dsimp [j] at this; omega),
        le_of_lt he.2.2.1⟩
    have hIn_sub : E_In j ⊆ active i hi := fun e he => by
      simp only [E_In, active, Finset.mem_filter] at he ⊢
      exact ⟨he.1, Fin.le_def.mpr (by have := Fin.lt_def.mp (he.2 ▸ e.hlr); dsimp [j] at this; omega),
        le_of_eq he.2.symm⟩
    have hB_spec := sortByKey_spec (E_B j) (fun e => arc e (sLast i hi)) (hinj_act.mono (Finset.coe_subset.mpr hB_sub))
    have hA_spec := sortByKey_spec (E_A j) (fun e => arc e (sLast i hi)) (hinj_act.mono (Finset.coe_subset.mpr hA_sub))
    have hIn_spec := sortByKey_spec (E_In j) (fun e => arc e (sLast i hi)) (hinj_act.mono (Finset.coe_subset.mpr hIn_sub))
    have hB_eq : B_list j = sortByKey (E_B j) (fun e => arc e (sLast i hi)) := by
      dsimp [B_list]; rw [dif_pos hj0]; simp [hp_eq]
    have hA_eq : A_list j = sortByKey (E_A j) (fun e => arc e (sLast i hi)) := by
      dsimp [A_list]; rw [dif_pos hj0]; simp [hp_eq]
    have hIn_eq : In_list j = sortByKey (E_In j) (fun e => arc e (sLast i hi)) := by
      dsimp [In_list]; rw [dif_pos hj0]; simp [hp_eq]
    rw [hB_eq, hA_eq, hIn_eq]
    have hsep := hsep_before i hi
    have hpw : (sortByKey (E_B j) (fun e => arc e (sLast i hi)) ++
        sortByKey (E_In j) (fun e => arc e (sLast i hi)) ++
        sortByKey (E_A j) (fun e => arc e (sLast i hi))).Pairwise
        (fun e₁ e₂ => arc e₁ (sLast i hi) < arc e₂ (sLast i hi)) := by
      rw [List.pairwise_append, List.pairwise_append]
      refine ⟨⟨hB_spec.2.2, hIn_spec.2.2, fun a ha b hb =>
          hsep.1 a ((hB_spec.2.1 a).mp ha) b ((hIn_spec.2.1 b).mp hb)⟩,
        hA_spec.2.2, fun a ha b hb => ?_⟩
      rcases List.mem_append.mp ha with haB | haIn
      · exact hsep.2.2 a ((hB_spec.2.1 a).mp haB) b ((hA_spec.2.1 b).mp hb)
      · exact hsep.2.1 a ((hIn_spec.2.1 a).mp haIn) b ((hA_spec.2.1 b).mp hb)
    have hnd : (sortByKey (E_B j) (fun e => arc e (sLast i hi)) ++
        sortByKey (E_In j) (fun e => arc e (sLast i hi)) ++
        sortByKey (E_A j) (fun e => arc e (sLast i hi))).Nodup :=
      hpw.imp (fun {a b} hlt heq => absurd (heq ▸ hlt) (lt_irrefl _))
    have hmem : ∀ e, e ∈ sortByKey (E_B j) (fun e => arc e (sLast i hi)) ++
        sortByKey (E_In j) (fun e => arc e (sLast i hi)) ++
        sortByKey (E_A j) (fun e => arc e (sLast i hi)) ↔ e ∈ active i hi := by
      intro e
      simp only [List.mem_append, hB_spec.2.1, hIn_spec.2.1, hA_spec.2.1]
      constructor
      · rintro ((h | h) | h)
        · exact hB_sub h
        · exact hIn_sub h
        · exact hA_sub h
      · intro he
        simp only [active, Finset.mem_filter] at he
        rcases eq_or_lt_of_le he.2.2 with hr | hr
        · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he.1, hr.symm⟩))
        · have hl_lt : e.l < j := Fin.lt_def.mpr (by have := Fin.le_def.mp he.2.1; dsimp [j]; omega)
          have hne := havoid e he.1 j hl_lt hr
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨he.1, hl_lt, hr, hlt⟩))
          · exact Or.inr (Finset.mem_filter.mpr ⟨he.1, hl_lt, hr, hgt⟩)
    exact ⟨hnd, hmem, hpw⟩
  -- For any `i` with `hi : i.val + 1 < n`, check `after i` has the SAME elements as `active i hi`, is nodup,
  -- and its inversions relative to `sFirst i hi` are bounded by crossings at `x i`!
  have hafter_spec : ∀ (i : Fin n) (hi : i.val + 1 < n),
      (B_list i ++ Out_list i ++ A_list i).Nodup ∧
      (∀ e, e ∈ B_list i ++ Out_list i ++ A_list i ↔ e ∈ active i hi) := by
    intro i hi
    have hsp := hsFirst_prop i hi
    have hs_nc : sFirst i hi ∉ Crit := fun hc => hsp.2.2 _ hc ⟨hsp.1, le_rfl⟩
    have hinj_act := harc_inj i hi (sFirst i hi) hsp.1 hsp.2.1 hs_nc
    have hOut_sub : E_Out i ⊆ active i hi := fun e he => by
      simp only [E_Out, active, Finset.mem_filter] at he ⊢
      exact ⟨he.1, le_of_eq he.2, fin_succ_le_of_lt (he.2 ▸ e.hlr) hi⟩
    have hOut_spec := sortByKey_spec (E_Out i) (fun e => arc e (sFirst i hi))
      (hinj_act.mono (Finset.coe_subset.mpr hOut_sub))
    have hOut_eq : Out_list i = sortByKey (E_Out i) (fun e => arc e (sFirst i hi)) := by
      dsimp [Out_list]; rw [dif_pos hi]
    by_cases hi0 : 0 < i.val
    · set p : Fin n := ⟨i.val - 1, by omega⟩
      have hp : p.val + 1 < n := by dsimp [p]; omega
      have hsp_prev := hsLast_prop p hp
      have hs_nc_prev : sLast p hp ∉ Crit := fun hc => hsp_prev.2.2 _ hc ⟨le_rfl, hsp_prev.2.1⟩
      have hinj_prev := harc_inj p hp (sLast p hp) hsp_prev.1 hsp_prev.2.1 hs_nc_prev
      have hB_sub_prev : E_B i ⊆ active p hp := fun e he => by
        simp only [E_B, active, Finset.mem_filter] at he ⊢
        exact ⟨he.1, fin_le_pred_of_lt he.2.1 hi0, Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.2.1; dsimp [p]; omega)⟩
      have hA_sub_prev : E_A i ⊆ active p hp := fun e he => by
        simp only [E_A, active, Finset.mem_filter] at he ⊢
        exact ⟨he.1, fin_le_pred_of_lt he.2.1 hi0, Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.2.1; dsimp [p]; omega)⟩
      have hB_spec := sortByKey_spec (E_B i) (fun e => arc e (sLast p hp))
        (hinj_prev.mono (Finset.coe_subset.mpr hB_sub_prev))
      have hA_spec := sortByKey_spec (E_A i) (fun e => arc e (sLast p hp))
        (hinj_prev.mono (Finset.coe_subset.mpr hA_sub_prev))
      have hB_eq : B_list i = sortByKey (E_B i) (fun e => arc e (sLast p hp)) := by
        dsimp [B_list]; rw [dif_pos hi0]
      have hA_eq : A_list i = sortByKey (E_A i) (fun e => arc e (sLast p hp)) := by
        dsimp [A_list]; rw [dif_pos hi0]
      rw [hB_eq, hOut_eq, hA_eq]
      have hdisj_BO : ∀ e, e ∈ E_B i → e ∉ E_Out i := fun e h1 h2 => by
        simp only [E_B, E_Out, Finset.mem_filter] at h1 h2; exact absurd (h2.2 ▸ h1.2.1) (lt_irrefl _)
      have hdisj_BA : ∀ e, e ∈ E_B i → e ∉ E_A i := fun e h1 h2 => by
        simp only [E_B, E_A, Finset.mem_filter] at h1 h2; linarith [h1.2.2.2, h2.2.2.2]
      have hdisj_OA : ∀ e, e ∈ E_Out i → e ∉ E_A i := fun e h1 h2 => by
        simp only [E_Out, E_A, Finset.mem_filter] at h1 h2; exact absurd (h1.2 ▸ h2.2.1) (lt_irrefl _)
      have hnd : (sortByKey (E_B i) (fun e => arc e (sLast p hp)) ++
          sortByKey (E_Out i) (fun e => arc e (sFirst i hi)) ++
          sortByKey (E_A i) (fun e => arc e (sLast p hp))).Nodup := by
        rw [List.nodup_append, List.nodup_append]
        refine ⟨⟨hB_spec.1, hOut_spec.1, fun a ha b hb heq =>
            hdisj_BO a ((hB_spec.2.1 a).mp ha) (heq ▸ (hOut_spec.2.1 b).mp hb)⟩,
          hA_spec.1, fun a ha b hb heq => ?_⟩
        rcases List.mem_append.mp ha with h | h
        · exact hdisj_BA a ((hB_spec.2.1 a).mp h) (heq ▸ (hA_spec.2.1 b).mp hb)
        · exact hdisj_OA a ((hOut_spec.2.1 a).mp h) (heq ▸ (hA_spec.2.1 b).mp hb)
      have hmem : ∀ e, e ∈ sortByKey (E_B i) (fun e => arc e (sLast p hp)) ++
          sortByKey (E_Out i) (fun e => arc e (sFirst i hi)) ++
          sortByKey (E_A i) (fun e => arc e (sLast p hp)) ↔ e ∈ active i hi := by
        intro e
        simp only [List.mem_append, hB_spec.2.1, hOut_spec.2.1, hA_spec.2.1]
        constructor
        · rintro ((h | h) | h)
          · simp only [E_B, active, Finset.mem_filter] at h ⊢
            exact ⟨h.1, le_of_lt h.2.1, fin_succ_le_of_lt h.2.2.1 hi⟩
          · exact hOut_sub h
          · simp only [E_A, active, Finset.mem_filter] at h ⊢
            exact ⟨h.1, le_of_lt h.2.1, fin_succ_le_of_lt h.2.2.1 hi⟩
        · intro he
          simp only [active, Finset.mem_filter] at he
          rcases eq_or_lt_of_le he.2.1 with hl | hl
          · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he.1, hl⟩))
          · have hr_gt : i < e.r := Fin.lt_def.mpr (by have := Fin.le_def.mp he.2.2; dsimp only at this; omega)
            have hne := havoid e he.1 i hl hr_gt
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨he.1, hl, hr_gt, hlt⟩))
            · exact Or.inr (Finset.mem_filter.mpr ⟨he.1, hl, hr_gt, hgt⟩)
      exact ⟨hnd, hmem⟩
    · have hi_eq0 : i.val = 0 := by omega
      have hB0 : B_list i = [] := by dsimp [B_list]; rw [dif_neg hi0]
      have hA0 : A_list i = [] := by dsimp [A_list]; rw [dif_neg hi0]
      rw [hB0, hOut_eq, hA0, List.nil_append, List.append_nil]
      refine ⟨hOut_spec.1, fun e => ?_⟩
      rw [hOut_spec.2.1]
      simp only [E_Out, active, Finset.mem_filter]
      constructor
      · intro h; exact ⟨h.1, le_of_eq h.2, fin_succ_le_of_lt (h.2 ▸ e.hlr) hi⟩
      · intro h; exact ⟨h.1, Fin.ext (by have := Fin.le_def.mp h.2.1; omega)⟩
  -- Define crossing pair count at a single real `t : ℝ`:
  let crossAt (t : ℝ) : ℕ :=
    ((E ×ˢ E).filter (fun p => p.1 ≠ p.2 ∧
      x p.1.l < t ∧ t < x p.1.r ∧ x p.2.l < t ∧ t < x p.2.r ∧
      arc p.1 t = arc p.2 t)).card
  -- Step A: For each slab `i` (`hi : i.val + 1 < n`), build `SwapSeq` from `after i` to `before (i+1)`
  -- whose swap count is bounded by `1/2` of the crossings at `x i` (if `x i ∈ Crit`) plus all `c ∈ slabCrits i hi`!
  have hslab_exists : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∃ ps : List (MEdge n × MEdge n),
        SwapSeq ps (B_list i ++ Out_list i ++ A_list i)
          (B_list ⟨i.val + 1, hi⟩ ++ In_list ⟨i.val + 1, hi⟩ ++ A_list ⟨i.val + 1, hi⟩) ∧
        2 * ps.length ≤
          (if x i ∈ Crit then crossAt (x i) else 0) +
          ∑ c ∈ Crit.filter (fun t => x i < t ∧ t < x ⟨i.val + 1, hi⟩), crossAt c := by
    intro i hi
    have hspF := hsFirst_prop i hi
    have hsF_nc : sFirst i hi ∉ Crit := fun hc => hspF.2.2 _ hc ⟨hspF.1, le_rfl⟩
    have hinjF := harc_inj i hi (sFirst i hi) hspF.1 hspF.2.1 hsF_nc
    set πF := sortByKey (active i hi) (fun e => arc e (sFirst i hi))
    have hπF_spec := sortByKey_spec (active i hi) (fun e => arc e (sFirst i hi)) hinjF
    -- Sub-step A1: From `after i` to `πF`, swaps ≤ `(1/2) * (if x i ∈ Crit then crossAt (x i) else 0)`!
    have hstep1 : ∃ ps₁ : List (MEdge n × MEdge n),
        SwapSeq ps₁ (B_list i ++ Out_list i ++ A_list i) πF ∧
        2 * ps₁.length ≤ (if x i ∈ Crit then crossAt (x i) else 0) := by
      have ha_sp := hafter_spec i hi
      have hperm1 : (B_list i ++ Out_list i ++ A_list i).Perm πF :=
        (List.perm_ext_iff_of_nodup ha_sp.1 hπF_spec.1).mpr fun e => by
          rw [ha_sp.2, hπF_spec.2.1]
      obtain ⟨ps₁, hlen1, hseq1⟩ :=
        exists_swapSeq_sort (fun e => arc e (sFirst i hi)) _ πF ha_sp.1 hperm1 hπF_spec.2.2
      refine ⟨ps₁, hseq1, ?_⟩
      rw [hlen1]
      by_cases hi0 : 0 < i.val
      · set p : Fin n := ⟨i.val - 1, by omega⟩
        have hp : p.val + 1 < n := by dsimp [p]; omega
        have hspP := hsLast_prop p hp
        have hsP_nc : sLast p hp ∉ Crit := fun hc => hspP.2.2 _ hc ⟨le_rfl, hspP.2.1⟩
        have hinjP := harc_inj p hp (sLast p hp) hspP.1 hspP.2.1 hsP_nc
        have hB_sub_p : E_B i ⊆ active p hp := fun e he => by
          simp only [E_B, active, Finset.mem_filter] at he ⊢
          exact ⟨he.1, Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.1; dsimp [p]; omega),
            Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.2.1; dsimp [p]; omega)⟩
        have hA_sub_p : E_A i ⊆ active p hp := fun e he => by
          simp only [E_A, active, Finset.mem_filter] at he ⊢
          exact ⟨he.1, Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.1; dsimp [p]; omega),
            Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.2.1; dsimp [p]; omega)⟩
        have hOut_sub : E_Out i ⊆ active i hi := fun e he => by
          simp only [E_Out, active, Finset.mem_filter] at he ⊢
          exact ⟨he.1, le_of_eq he.2, fin_succ_le_of_lt (he.2 ▸ e.hlr) hi⟩
        have hB_sp := sortByKey_spec (E_B i) (fun e => arc e (sLast p hp))
          (hinjP.mono (Finset.coe_subset.mpr hB_sub_p))
        have hA_sp := sortByKey_spec (E_A i) (fun e => arc e (sLast p hp))
          (hinjP.mono (Finset.coe_subset.mpr hA_sub_p))
        have hOut_sp := sortByKey_spec (E_Out i) (fun e => arc e (sFirst i hi))
          (hinjF.mono (Finset.coe_subset.mpr hOut_sub))
        have hB_eq : B_list i = sortByKey (E_B i) (fun e => arc e (sLast p hp)) := by
          dsimp [B_list]; rw [dif_pos hi0]
        have hA_eq : A_list i = sortByKey (E_A i) (fun e => arc e (sLast p hp)) := by
          dsimp [A_list]; rw [dif_pos hi0]
        have hOut_eq : Out_list i = sortByKey (E_Out i) (fun e => arc e (sFirst i hi)) := by
          dsimp [Out_list]; rw [dif_pos hi]
        -- Helper: `invCount g (X ++ Y) = invCount g X + invCount g Y` when `∀ a ∈ X, ∀ b ∈ Y, g a < g b`!
        have hinv_app : ∀ (g : MEdge n → ℝ) (X Y : List (MEdge n)),
            (∀ a ∈ X, ∀ b ∈ Y, g a < g b) → invCount g (X ++ Y) = invCount g X + invCount g Y := by
          intro g X Y hlt
          induction X with
          | nil => simp [invCount]
          | cons a t iht =>
            simp only [List.cons_append, invCount, List.filter_append, List.length_append]
            have hY0 : (Y.filter (fun b => decide (g b < g a))).length = 0 := by
              rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
              intro b hb; simp only [decide_eq_true_eq, not_lt]
              exact le_of_lt (hlt a (by simp) b hb)
            rw [hY0, add_zero, iht (fun x hx b hb => hlt x (by simp [hx]) b hb)]
            omega
        have hsep := hsep_after i hi
        have hinv_split : invCount (fun e => arc e (sFirst i hi)) (B_list i ++ Out_list i ++ A_list i) =
            invCount (fun e => arc e (sFirst i hi)) (B_list i) +
            invCount (fun e => arc e (sFirst i hi)) (A_list i) := by
          rw [hB_eq, hOut_eq, hA_eq]
          have h1 : invCount (fun e => arc e (sFirst i hi))
              ((sortByKey (E_B i) (fun e => arc e (sLast p hp)) ++
                sortByKey (E_Out i) (fun e => arc e (sFirst i hi))) ++
                sortByKey (E_A i) (fun e => arc e (sLast p hp))) =
              invCount (fun e => arc e (sFirst i hi))
                (sortByKey (E_B i) (fun e => arc e (sLast p hp)) ++
                  sortByKey (E_Out i) (fun e => arc e (sFirst i hi))) +
              invCount (fun e => arc e (sFirst i hi))
                (sortByKey (E_A i) (fun e => arc e (sLast p hp))) := by
            apply hinv_app
            intro a ha b hb
            rcases List.mem_append.mp ha with haB | haO
            · exact hsep.2.2 a ((hB_sp.2.1 a).mp haB) b ((hA_sp.2.1 b).mp hb)
            · exact hsep.2.1 a ((hOut_sp.2.1 a).mp haO) b ((hA_sp.2.1 b).mp hb)
          have h2 : invCount (fun e => arc e (sFirst i hi))
              (sortByKey (E_B i) (fun e => arc e (sLast p hp)) ++
                sortByKey (E_Out i) (fun e => arc e (sFirst i hi))) =
              invCount (fun e => arc e (sFirst i hi))
                (sortByKey (E_B i) (fun e => arc e (sLast p hp))) +
              invCount (fun e => arc e (sFirst i hi))
                (sortByKey (E_Out i) (fun e => arc e (sFirst i hi))) := by
            apply hinv_app
            intro a ha b hb
            exact hsep.1 a ((hB_sp.2.1 a).mp ha) b ((hOut_sp.2.1 b).mp hb)
          have hO0 : invCount (fun e => arc e (sFirst i hi))
              (sortByKey (E_Out i) (fun e => arc e (sFirst i hi))) = 0 :=
            (invCount_eq_zero_iff_pairwise _ _).mpr (hOut_sp.2.2.imp fun h => le_of_lt h)
          omega
        rw [hinv_split, hB_eq, hA_eq,
          invCount_eq_card_inversions (fun e => arc e (sLast p hp)) (fun e => arc e (sFirst i hi)) _ hB_sp.1 hB_sp.2.2,
          invCount_eq_card_inversions (fun e => arc e (sLast p hp)) (fun e => arc e (sFirst i hi)) _ hA_sp.1 hA_sp.2.2]
        -- Any pair `(e₁, e₂)` in `E_B i` or `E_A i` inverted between `sLast p hp` and `sFirst i hi` MUST cross at `x i`!
        have hcross_xi : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁.l < i → i < e₁.r → e₂.l < i → i < e₂.r →
            arc e₁ (sLast p hp) < arc e₂ (sLast p hp) →
            arc e₂ (sFirst i hi) < arc e₁ (sFirst i hi) →
            e₁ ≠ e₂ ∧ arc e₁ (x i) = arc e₂ (x i) ∧ x i ∈ Crit := by
          intro e₁ h1 e₂ h2 hl1 hr1 hl2 hr2 hlt1 hlt2
          have hne : e₁ ≠ e₂ := fun h => absurd (h ▸ hlt1) (lt_irrefl _)
          have hp_eq : (⟨p.val + 1, hp⟩ : Fin n) = i := Fin.ext (by dsimp [p]; omega)
          have hsP_lt : sLast p hp < x i := hp_eq ▸ hspP.2.1
          have hle1 : x e₁.l ≤ sLast p hp :=
            le_of_lt (lt_of_le_of_lt (hx.monotone (Fin.le_def.mpr (by have := Fin.lt_def.mp hl1; dsimp [p]; omega))) hspP.1)
          have hle2 : x e₂.l ≤ sLast p hp :=
            le_of_lt (lt_of_le_of_lt (hx.monotone (Fin.le_def.mpr (by have := Fin.lt_def.mp hl2; dsimp [p]; omega))) hspP.1)
          have hge1 : sFirst i hi ≤ x e₁.r :=
            le_of_lt (lt_of_lt_of_le hspF.2.1 (hx.monotone (fin_succ_le_of_lt hr1 hi)))
          have hge2 : sFirst i hi ≤ x e₂.r :=
            le_of_lt (lt_of_lt_of_le hspF.2.1 (hx.monotone (fin_succ_le_of_lt hr2 hi)))
          obtain ⟨t, ht, hteq⟩ := hivt e₁ h1 e₂ h2 hne (sLast p hp) (sFirst i hi)
            (lt_trans hsP_lt hspF.1) hle1 hge1 hle2 hge2 hlt1 hlt2
          have htC : t ∈ Crit := hCrit e₁ h1 e₂ h2 hne t
            (lt_of_le_of_lt hle1 ht.1) (lt_of_lt_of_le ht.2 hge1)
            (lt_of_le_of_lt hle2 ht.1) (lt_of_lt_of_le ht.2 hge2) hteq
          have ht_eq_xi : t = x i := by
            rcases lt_trichotomy t (x i) with h | h | h
            · exact absurd ⟨le_of_lt ht.1, hp_eq.symm ▸ h⟩ (hspP.2.2 t htC)
            · exact h
            · exact absurd ⟨h, le_of_lt ht.2⟩ (hspF.2.2 t htC)
          subst ht_eq_xi
          exact ⟨hne, hteq, htC⟩
        -- Both sets `InvB` and `InvA` are disjoint, and for every `p ∈ InvB ∪ InvA`, BOTH `p` and `p.swap` lie in `CrossAt (x i)`!
        set InvB := ((sortByKey (E_B i) (fun e => arc e (sLast p hp))).toFinset ×ˢ
          (sortByKey (E_B i) (fun e => arc e (sLast p hp))).toFinset).filter
          (fun q => arc q.1 (sLast p hp) < arc q.2 (sLast p hp) ∧ arc q.2 (sFirst i hi) < arc q.1 (sFirst i hi))
        set InvA := ((sortByKey (E_A i) (fun e => arc e (sLast p hp))).toFinset ×ˢ
          (sortByKey (E_A i) (fun e => arc e (sLast p hp))).toFinset).filter
          (fun q => arc q.1 (sLast p hp) < arc q.2 (sLast p hp) ∧ arc q.2 (sFirst i hi) < arc q.1 (sFirst i hi))
        have hdisj_BA : Disjoint InvB InvA := by
          rw [Finset.disjoint_left]; intro q h1 h2
          simp only [InvB, InvA, Finset.mem_filter, Finset.mem_product, List.mem_toFinset,
            hB_sp.2.1, hA_sp.2.1, E_B, E_A] at h1 h2
          linarith [h1.1.1.2.2.2, h2.1.1.2.2.2]
        set Inv := InvB ∪ InvA
        set InvRev := Inv.image Prod.swap
        have hdisj_rev : Disjoint Inv InvRev := by
          rw [Finset.disjoint_left]; intro q h1 h2
          simp only [InvRev, Finset.mem_image] at h2
          obtain ⟨q', hq', rfl⟩ := h2
          have hlt1 : arc q'.2 (sLast p hp) < arc q'.1 (sLast p hp) := by
            rcases Finset.mem_union.mp h1 with h | h <;> exact (Finset.mem_filter.mp h).2.1
          have hlt2 : arc q'.1 (sLast p hp) < arc q'.2 (sLast p hp) := by
            rcases Finset.mem_union.mp hq' with h | h <;> exact (Finset.mem_filter.mp h).2.1
          linarith
        have hInv_card : InvB.card + InvA.card = Inv.card := (Finset.card_union_of_disjoint hdisj_BA).symm
        have hRev_card : InvRev.card = Inv.card :=
          Finset.card_image_of_injOn (fun _ _ _ _ h => Prod.swap_injective h)
        by_cases hxiC : x i ∈ Crit
        · simp only [hxiC, ↓reduceIte]
          have hsub : Inv ∪ InvRev ⊆ (E ×ˢ E).filter (fun q => q.1 ≠ q.2 ∧
              x q.1.l < x i ∧ x i < x q.1.r ∧ x q.2.l < x i ∧ x i < x q.2.r ∧
              arc q.1 (x i) = arc q.2 (x i)) := by
            have hInv_sub : ∀ q ∈ Inv, q.1 ∈ E ∧ q.2 ∈ E ∧ q.1 ≠ q.2 ∧
                x q.1.l < x i ∧ x i < x q.1.r ∧ x q.2.l < x i ∧ x i < x q.2.r ∧
                arc q.1 (x i) = arc q.2 (x i) := by
              intro q hq
              have hBA : (q.1 ∈ E ∧ q.1.l < i ∧ i < q.1.r) ∧ (q.2 ∈ E ∧ q.2.l < i ∧ i < q.2.r) ∧
                  arc q.1 (sLast p hp) < arc q.2 (sLast p hp) ∧ arc q.2 (sFirst i hi) < arc q.1 (sFirst i hi) := by
                rcases Finset.mem_union.mp hq with h | h
                · simp only [InvB, Finset.mem_filter, Finset.mem_product, List.mem_toFinset,
                    hB_sp.2.1, E_B] at h
                  exact ⟨⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.1⟩, ⟨h.1.2.1, h.1.2.2.1, h.1.2.2.2.1⟩, h.2⟩
                · simp only [InvA, Finset.mem_filter, Finset.mem_product, List.mem_toFinset,
                    hA_sp.2.1, E_A] at h
                  exact ⟨⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.1⟩, ⟨h.1.2.1, h.1.2.2.1, h.1.2.2.2.1⟩, h.2⟩
              have hc := hcross_xi q.1 hBA.1.1 q.2 hBA.2.1.1 hBA.1.2.1 hBA.1.2.2 hBA.2.1.2.1 hBA.2.1.2.2
                hBA.2.2.1 hBA.2.2.2
              exact ⟨hBA.1.1, hBA.2.1.1, hc.1, hx hBA.1.2.1, hx hBA.1.2.2,
                hx hBA.2.1.2.1, hx hBA.2.1.2.2, hc.2.1⟩
            intro q hq
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product] at hq ⊢
            rcases hq with h | h
            · have := hInv_sub q h
              exact ⟨⟨this.1, this.2.1⟩, this.2.2⟩
            · simp only [InvRev, Finset.mem_image] at h
              obtain ⟨q', hq', rfl⟩ := h
              have := hInv_sub q' hq'
              exact ⟨⟨this.2.1, this.1⟩, this.2.2.1.symm, this.2.2.2.2.2.1, this.2.2.2.2.2.2.1,
                this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.2.2.symm⟩
          have hle := Finset.card_le_card hsub
          rw [Finset.card_union_of_disjoint hdisj_rev, hRev_card] at hle
          change 2 * (InvB.card + InvA.card) ≤ _
          dsimp only [crossAt]
          have hle' : 2 * Inv.card ≤ ((E ×ˢ E).filter (fun p => p.1 ≠ p.2 ∧
              x p.1.l < x i ∧ x i < x p.1.r ∧ x p.2.l < x i ∧ x i < x p.2.r ∧
              arc p.1 (x i) = arc p.2 (x i))).card := by omega
          omega
        · simp only [hxiC, ↓reduceIte]
          have hInv_empty : Inv = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro q hq
            have hBA : (q.1 ∈ E ∧ q.1.l < i ∧ i < q.1.r) ∧ (q.2 ∈ E ∧ q.2.l < i ∧ i < q.2.r) ∧
                arc q.1 (sLast p hp) < arc q.2 (sLast p hp) ∧ arc q.2 (sFirst i hi) < arc q.1 (sFirst i hi) := by
              rcases Finset.mem_union.mp hq with h | h
              · simp only [InvB, Finset.mem_filter, Finset.mem_product, List.mem_toFinset,
                  hB_sp.2.1, E_B] at h
                exact ⟨⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.1⟩, ⟨h.1.2.1, h.1.2.2.1, h.1.2.2.2.1⟩, h.2⟩
              · simp only [InvA, Finset.mem_filter, Finset.mem_product, List.mem_toFinset,
                  hA_sp.2.1, E_A] at h
                exact ⟨⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.1⟩, ⟨h.1.2.1, h.1.2.2.1, h.1.2.2.2.1⟩, h.2⟩
            exact hxiC (hcross_xi q.1 hBA.1.1 q.2 hBA.2.1.1 hBA.1.2.1 hBA.1.2.2 hBA.2.1.2.1 hBA.2.1.2.2
              hBA.2.2.1 hBA.2.2.2).2.2
          rw [hInv_empty, Finset.card_empty] at hInv_card; omega
      · -- `i.val = 0`: `B_list 0 = []`, `A_list 0 = []`, `Out_list 0 = sortByKey (E_Out 0) (sFirst 0)`, already sorted!
        have hB0 : B_list i = [] := by dsimp [B_list]; rw [dif_neg hi0]
        have hA0 : A_list i = [] := by dsimp [A_list]; rw [dif_neg hi0]
        have hOut0 : Out_list i = sortByKey (E_Out i) (fun e => arc e (sFirst i hi)) := by
          dsimp [Out_list]; rw [dif_pos hi]
        have hOut_sub : E_Out i ⊆ active i hi := fun e he => by
          simp only [E_Out, active, Finset.mem_filter] at he ⊢
          exact ⟨he.1, le_of_eq he.2, fin_succ_le_of_lt (he.2 ▸ e.hlr) hi⟩
        have hOut_sp := sortByKey_spec (E_Out i) (fun e => arc e (sFirst i hi))
          (hinjF.mono (Finset.coe_subset.mpr hOut_sub))
        rw [hB0, hA0, hOut0, List.nil_append, List.append_nil]
        have h0 : invCount (fun e => arc e (sFirst i hi))
            (sortByKey (E_Out i) (fun e => arc e (sFirst i hi))) = 0 :=
          (invCount_eq_zero_iff_pairwise _ _).mpr (hOut_sp.2.2.imp fun h => le_of_lt h)
        rw [h0]; omega
    -- Sub-step A2: From `πF` (sorted at `sFirst i hi`) to `before (i+1)` (sorted at `sLast i hi`),
    -- march across `slabCrits i hi` one critical point `c` at a time!
    have hstep2 : ∃ ps₂ : List (MEdge n × MEdge n),
        SwapSeq ps₂ πF
          (B_list ⟨i.val + 1, hi⟩ ++ In_list ⟨i.val + 1, hi⟩ ++ A_list ⟨i.val + 1, hi⟩) ∧
        2 * ps₂.length ≤
          ∑ c ∈ Crit.filter (fun t => x i < t ∧ t < x ⟨i.val + 1, hi⟩), crossAt c := by
      -- Induct on ANY sorted list `cs : List ℝ` of critical points in `(a, b) ⊆ (x i, x (i+1))`!
      have hchain : ∀ (cs : List ℝ) (a b : ℝ),
          x i ≤ a → a < b → b ≤ x ⟨i.val + 1, hi⟩ →
          cs.Nodup → cs.Pairwise (· < ·) →
          (∀ c ∈ cs, c ∈ Crit ∧ a < c ∧ c < b) →
          (∀ t ∈ Crit, a < t → t < b → t ∈ cs) →
          let sL := match cs with | [] => (a + b) / 2 | c :: _ => (a + c) / 2
          let sR := match cs.getLast? with | none => (a + b) / 2 | some c => (c + b) / 2
          ∃ ps : List (MEdge n × MEdge n),
            SwapSeq ps (sortByKey (active i hi) (fun e => arc e sL))
                       (sortByKey (active i hi) (fun e => arc e sR)) ∧
            2 * ps.length ≤ (cs.map crossAt).sum := by
        intro cs
        induction cs with
        | nil =>
          intro a b _ _ _ _ _ _ _
          exact ⟨[], SwapSeq.nil _, by simp⟩
        | cons c rest ih =>
          intro a b ha hab hb hnd hpw hmem hall
          have hc_info := hmem c (by simp)
          have hnd' := List.nodup_cons.mp hnd
          have hpw' := List.pairwise_cons.mp hpw
          -- Midpoint just left of `c`: `sL = (a + c) / 2`; midpoint just right of `c`: `sM`!
          set sL := (a + c) / 2
          set sM := match rest with | [] => (c + b) / 2 | c' :: _ => (c + c') / 2
          set sR := match rest.getLast? with | none => (c + b) / 2 | some c' => (c' + b) / 2
          have hsR_eq : (match (c :: rest).getLast? with | none => (a + b) / 2 | some c' => (c' + b) / 2) = sR := by
            cases rest with
            | nil => rfl
            | cons d rest' =>
                dsimp only [sR]
                rw [List.getLast?_cons_cons, List.getLast?_eq_some_getLast (List.cons_ne_nil d rest')]
          -- Show `sL < c < sM` and NO critical points in `(sL, c)` or `(c, sM)`!
          have hsL_lt : x i < sL ∧ sL < c ∧ ∀ t ∈ Crit, ¬(sL ≤ t ∧ t < c) := by
            refine ⟨by dsimp [sL]; linarith [hc_info.2.1], by dsimp [sL]; linarith [hc_info.2.1], fun t ht ⟨h1, h2⟩ => ?_⟩
            have htm : t ∈ c :: rest := hall t ht (by dsimp [sL] at h1; linarith [hc_info.2.1]) (by linarith [hc_info.2.2])
            rcases List.mem_cons.mp htm with rfl | htr
            · linarith
            · linarith [hpw'.1 t htr]
          have hsM_gt : c < sM ∧ sM < x ⟨i.val + 1, hi⟩ ∧ ∀ t ∈ Crit, ¬(c < t ∧ t ≤ sM) := by
            dsimp [sM]
            cases rest with
            | nil =>
              refine ⟨by linarith [hc_info.2.2], by linarith [hc_info.2.2], fun t ht ⟨h1, h2⟩ => ?_⟩
              have htm := hall t ht (lt_trans hc_info.2.1 h1) (by linarith [hc_info.2.2])
              simp only [List.mem_singleton] at htm; linarith
            | cons d rest' =>
              have hd_info := hmem d (by simp)
              have hcd : c < d := hpw'.1 d (by simp)
              refine ⟨by linarith, by linarith [hd_info.2.2], fun t ht ⟨h1, h2⟩ => ?_⟩
              have htm := hall t ht (lt_trans hc_info.2.1 h1) (by linarith [hd_info.2.2])
              rcases List.mem_cons.mp htm with rfl | htr
              · linarith
              · rcases List.mem_cons.mp htr with rfl | htr'
                · linarith
                · have hdt : d < t := (List.pairwise_cons.mp hpw'.2).1 t htr'
                  linarith
          have hsL_nc : sL ∉ Crit := fun h => hsL_lt.2.2 sL h ⟨le_rfl, hsL_lt.2.1⟩
          have hsM_nc : sM ∉ Crit := fun h => hsM_gt.2.2 sM h ⟨hsM_gt.1, le_rfl⟩
          have hinjL := harc_inj i hi sL hsL_lt.1 (lt_trans hsL_lt.2.1 (lt_trans hsM_gt.1 hsM_gt.2.1)) hsL_nc
          have hinjM := harc_inj i hi sM (lt_trans hsL_lt.1 (lt_trans hsL_lt.2.1 hsM_gt.1)) hsM_gt.2.1 hsM_nc
          have hL_sp := sortByKey_spec (active i hi) (fun e => arc e sL) hinjL
          have hM_sp := sortByKey_spec (active i hi) (fun e => arc e sM) hinjM
          have hpermLM : (sortByKey (active i hi) (fun e => arc e sL)).Perm
              (sortByKey (active i hi) (fun e => arc e sM)) :=
            (List.perm_ext_iff_of_nodup hL_sp.1 hM_sp.1).mpr fun e => by rw [hL_sp.2.1, hM_sp.2.1]
          obtain ⟨ps_c, hlen_c, hseq_c⟩ := exists_swapSeq_sort (fun e => arc e sM) _ _
            hL_sp.1 hpermLM hM_sp.2.2
          -- Bound `2 * ps_c.length ≤ crossAt c`!
          have hlen_c_ub : 2 * ps_c.length ≤ crossAt c := by
            rw [hlen_c, invCount_eq_card_inversions (fun e => arc e sL) (fun e => arc e sM) _ hL_sp.1 hL_sp.2.2]
            set Inv := ((sortByKey (active i hi) (fun e => arc e sL)).toFinset ×ˢ
              (sortByKey (active i hi) (fun e => arc e sL)).toFinset).filter
              (fun q => arc q.1 sL < arc q.2 sL ∧ arc q.2 sM < arc q.1 sM)
            set InvRev := Inv.image Prod.swap
            have hdisj_rev : Disjoint Inv InvRev := by
              rw [Finset.disjoint_left]; intro q h1 h2
              simp only [InvRev, Finset.mem_image] at h2
              obtain ⟨q', hq', rfl⟩ := h2
              have h1' := (Finset.mem_filter.mp h1).2.1
              have h2' := (Finset.mem_filter.mp hq').2.1
              dsimp only [Prod.swap] at h1'
              linarith
            have hRev_card : InvRev.card = Inv.card :=
              Finset.card_image_of_injOn (fun _ _ _ _ h => Prod.swap_injective h)
            have hInv_sub : ∀ q ∈ Inv, q.1 ∈ E ∧ q.2 ∈ E ∧ q.1 ≠ q.2 ∧
                x q.1.l < c ∧ c < x q.1.r ∧ x q.2.l < c ∧ c < x q.2.r ∧ arc q.1 c = arc q.2 c := by
              intro q hq
              simp only [Inv, Finset.mem_filter, Finset.mem_product, List.mem_toFinset,
                hL_sp.2.1, active] at hq
              have hne : q.1 ≠ q.2 := fun h => absurd (h ▸ hq.2.1) (lt_irrefl _)
              have hle1 : x q.1.l ≤ sL := le_of_lt (lt_of_le_of_lt (hx.monotone hq.1.1.2.1) hsL_lt.1)
              have hle2 : x q.2.l ≤ sL := le_of_lt (lt_of_le_of_lt (hx.monotone hq.1.2.2.1) hsL_lt.1)
              have hge1 : sM ≤ x q.1.r := le_of_lt (lt_of_lt_of_le hsM_gt.2.1 (hx.monotone hq.1.1.2.2))
              have hge2 : sM ≤ x q.2.r := le_of_lt (lt_of_lt_of_le hsM_gt.2.1 (hx.monotone hq.1.2.2.2))
              obtain ⟨t, ht, hteq⟩ := hivt q.1 hq.1.1.1 q.2 hq.1.2.1 hne sL sM
                (lt_trans hsL_lt.2.1 hsM_gt.1) hle1 hge1 hle2 hge2 hq.2.1 hq.2.2
              have htC : t ∈ Crit := hCrit q.1 hq.1.1.1 q.2 hq.1.2.1 hne t
                (lt_of_le_of_lt hle1 ht.1) (lt_of_lt_of_le ht.2 hge1)
                (lt_of_le_of_lt hle2 ht.1) (lt_of_lt_of_le ht.2 hge2) hteq
              have ht_eq_c : t = c := by
                rcases lt_trichotomy t c with h | h | h
                · exact absurd ⟨le_of_lt ht.1, h⟩ (hsL_lt.2.2 t htC)
                · exact h
                · exact absurd ⟨h, le_of_lt ht.2⟩ (hsM_gt.2.2 t htC)
              subst ht_eq_c
              exact ⟨hq.1.1.1, hq.1.2.1, hne,
                lt_trans (lt_of_le_of_lt (hx.monotone hq.1.1.2.1) hsL_lt.1) hsL_lt.2.1,
                lt_trans hsM_gt.1 (lt_of_lt_of_le hsM_gt.2.1 (hx.monotone hq.1.1.2.2)),
                lt_trans (lt_of_le_of_lt (hx.monotone hq.1.2.2.1) hsL_lt.1) hsL_lt.2.1,
                lt_trans hsM_gt.1 (lt_of_lt_of_le hsM_gt.2.1 (hx.monotone hq.1.2.2.2)), hteq⟩
            have hsub : Inv ∪ InvRev ⊆ (E ×ˢ E).filter (fun q => q.1 ≠ q.2 ∧
                x q.1.l < c ∧ c < x q.1.r ∧ x q.2.l < c ∧ c < x q.2.r ∧ arc q.1 c = arc q.2 c) := by
              intro q hq
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product] at hq ⊢
              rcases hq with h | h
              · have := hInv_sub q h; exact ⟨⟨this.1, this.2.1⟩, this.2.2⟩
              · simp only [InvRev, Finset.mem_image] at h
                obtain ⟨q', hq', rfl⟩ := h
                have := hInv_sub q' hq'
                exact ⟨⟨this.2.1, this.1⟩, this.2.2.1.symm, this.2.2.2.2.2.1, this.2.2.2.2.2.2.1,
                  this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.2.2.symm⟩
            have hle := Finset.card_le_card hsub
            rw [Finset.card_union_of_disjoint hdisj_rev, hRev_card] at hle
            change 2 * Inv.card ≤ crossAt c
            dsimp only [crossAt]
            omega
          -- Apply IH on `rest` over `(c, b)`!
          obtain ⟨ps_rest, hseq_rest, hlen_rest⟩ := ih c b
            (le_of_lt (lt_of_le_of_lt ha hc_info.2.1)) hc_info.2.2 hb hnd'.2 hpw'.2
            (fun d hd => ⟨(hmem d (by simp [hd])).1, hpw'.1 d hd, (hmem d (by simp [hd])).2.2⟩)
            (fun t ht htc htb => by
              have htm := hall t ht (lt_trans hc_info.2.1 htc) htb
              rcases List.mem_cons.mp htm with rfl | htr
              · exact absurd htc (lt_irrefl _)
              · exact htr)
          refine ⟨ps_c ++ ps_rest, ?_, ?_⟩
          · dsimp only; rw [hsR_eq]; exact hseq_c.append hseq_rest
          · simp only [List.length_append, List.map_cons, List.sum_cons]; omega
      -- Apply `hchain` to `slabCrits i hi` on `(x i, x (i+1))`!
      set sc := slabCrits i hi
      have hsc_nd : sc.Nodup := Finset.sort_nodup _ _
      have hsc_pw : sc.Pairwise (· < ·) :=
        List.Pairwise.imp_of_mem (fun {a b} _ _ ⟨h1, h2⟩ => lt_of_le_of_ne h1 h2)
          ((Finset.pairwise_sort _ _).and hsc_nd)
      obtain ⟨ps₂, hseq₂, hlen₂⟩ := hchain sc (x i) (x ⟨i.val + 1, hi⟩)
        le_rfl (hx (Fin.lt_def.mpr (by simp))) le_rfl hsc_nd hsc_pw
        (fun c hc => by
          have := Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hc)
          exact ⟨this.1, this.2.1, this.2.2⟩)
        (fun t ht h1 h2 => (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_filter.mpr ⟨ht, h1, h2⟩))
      -- Note `sortByKey (active i hi) (arc · (sLast i hi)) = before (i+1)`!
      have hspL := hsLast_prop i hi
      have hsL_nc : sLast i hi ∉ Crit := fun hc => hspL.2.2 _ hc ⟨le_rfl, hspL.2.1⟩
      have hinjL := harc_inj i hi (sLast i hi) hspL.1 hspL.2.1 hsL_nc
      have hπL_sp := sortByKey_spec (active i hi) (fun e => arc e (sLast i hi)) hinjL
      have hbef_sp := hbefore_eq_sort i hi
      have hπL_eq : sortByKey (active i hi) (fun e => arc e (sLast i hi)) =
          B_list ⟨i.val + 1, hi⟩ ++ In_list ⟨i.val + 1, hi⟩ ++ A_list ⟨i.val + 1, hi⟩ :=
        List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => absurd (lt_trans h1 h2) (lt_irrefl _))
          hπL_sp.2.2 hbef_sp.2.2
          ((List.perm_ext_iff_of_nodup hπL_sp.1 hbef_sp.1).mpr fun e => by rw [hπL_sp.2.1, hbef_sp.2.1])
      rw [hπL_eq] at hseq₂
      have hsum_eq : (sc.map crossAt).sum =
          ∑ c ∈ Crit.filter (fun t => x i < t ∧ t < x ⟨i.val + 1, hi⟩), crossAt c := by
        rw [← List.sum_toFinset _ hsc_nd]
        congr 1; ext t; simp only [sc, slabCrits, List.mem_toFinset, Finset.mem_sort, Finset.mem_filter]
      rw [hsum_eq] at hlen₂
      exact ⟨ps₂, hseq₂, hlen₂⟩
    obtain ⟨ps₁, hseq₁, hlen₁⟩ := hstep1
    obtain ⟨ps₂, hseq₂, hlen₂⟩ := hstep2
    exact ⟨ps₁ ++ ps₂, hseq₁.append hseq₂, by simp only [List.length_append]; omega⟩
  choose slabSwaps hslab_seq hslab_len using hslab_exists
  -- Assemble the `WiringDiagram n E`!
  let W : WiringDiagram n E := {
    B := B_list
    A := A_list
    InL := In_list
    OutL := Out_list
    swaps := slabSwaps
    hIn_nodup := fun i => by
      dsimp [In_list]; split_ifs with hi0
      · set p : Fin n := ⟨i.val - 1, by omega⟩
        have hp : p.val + 1 < n := by dsimp [p]; omega
        have hsp := hsLast_prop p hp
        have hinj := harc_inj p hp (sLast p hp) hsp.1 hsp.2.1 (fun h => hsp.2.2 _ h ⟨le_rfl, hsp.2.1⟩)
        have hsub : E_In i ⊆ active p hp := fun e he => by
          simp only [E_In, active, Finset.mem_filter] at he ⊢
          exact ⟨he.1, Fin.le_def.mpr (by have := Fin.lt_def.mp (he.2 ▸ e.hlr); dsimp [p]; omega),
            Fin.le_def.mpr (by have := congrArg Fin.val he.2; dsimp [p]; omega)⟩
        exact (sortByKey_spec (E_In i) _ (hinj.mono (Finset.coe_subset.mpr hsub))).1
      · exact List.nodup_nil
    hOut_nodup := fun i => by
      dsimp [Out_list]; split_ifs with hi
      · have hsp := hsFirst_prop i hi
        have hinj := harc_inj i hi (sFirst i hi) hsp.1 hsp.2.1 (fun h => hsp.2.2 _ h ⟨hsp.1, le_rfl⟩)
        have hsub : E_Out i ⊆ active i hi := fun e he => by
          simp only [E_Out, active, Finset.mem_filter] at he ⊢
          exact ⟨he.1, le_of_eq he.2, fin_succ_le_of_lt (he.2 ▸ e.hlr) hi⟩
        exact (sortByKey_spec (E_Out i) _ (hinj.mono (Finset.coe_subset.mpr hsub))).1
      · exact List.nodup_nil
    hIn_mem := fun i e => by
      dsimp [In_list]; split_ifs with hi0
      · set p : Fin n := ⟨i.val - 1, by omega⟩
        have hp : p.val + 1 < n := by dsimp [p]; omega
        have hsp := hsLast_prop p hp
        have hinj := harc_inj p hp (sLast p hp) hsp.1 hsp.2.1 (fun h => hsp.2.2 _ h ⟨le_rfl, hsp.2.1⟩)
        have hsub : E_In i ⊆ active p hp := fun e he => by
          simp only [E_In, active, Finset.mem_filter] at he ⊢
          exact ⟨he.1, Fin.le_def.mpr (by have := Fin.lt_def.mp (he.2 ▸ e.hlr); dsimp [p]; omega),
            Fin.le_def.mpr (by have := congrArg Fin.val he.2; dsimp [p]; omega)⟩
        rw [(sortByKey_spec (E_In i) _ (hinj.mono (Finset.coe_subset.mpr hsub))).2.1]
        simp [E_In]
      · simp only [List.not_mem_nil, false_iff, not_and]
        intro _ hr; have hlt : e.l.val < e.r.val := e.hlr; rw [hr] at hlt; omega
    hOut_mem := fun i e => by
      dsimp [Out_list]; split_ifs with hi
      · have hsp := hsFirst_prop i hi
        have hinj := harc_inj i hi (sFirst i hi) hsp.1 hsp.2.1 (fun h => hsp.2.2 _ h ⟨hsp.1, le_rfl⟩)
        have hsub : E_Out i ⊆ active i hi := fun e he => by
          simp only [E_Out, active, Finset.mem_filter] at he ⊢
          exact ⟨he.1, le_of_eq he.2, fin_succ_le_of_lt (he.2 ▸ e.hlr) hi⟩
        rw [(sortByKey_spec (E_Out i) _ (hinj.mono (Finset.coe_subset.mpr hsub))).2.1]
        simp [E_Out]
      · simp only [List.not_mem_nil, false_iff, not_and]
        intro _ hl; have hlt : e.l.val < e.r.val := e.hlr; have hr : e.r.val < n := e.r.isLt; rw [hl] at hlt; omega
    hB_pass := fun i e he => by
      dsimp [B_list] at he; split_ifs at he with hi0
      · set p : Fin n := ⟨i.val - 1, by omega⟩
        have hp : p.val + 1 < n := by dsimp [p]; omega
        have hsp := hsLast_prop p hp
        have hinj := harc_inj p hp (sLast p hp) hsp.1 hsp.2.1 (fun h => hsp.2.2 _ h ⟨le_rfl, hsp.2.1⟩)
        have hsub : E_B i ⊆ active p hp := fun e he => by
          simp only [E_B, active, Finset.mem_filter] at he ⊢
          exact ⟨he.1, Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.1; dsimp [p]; omega),
            Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.2.1; dsimp [p]; omega)⟩
        have hmem := (sortByKey_spec (E_B i) _ (hinj.mono (Finset.coe_subset.mpr hsub))).2.1 e |>.mp he
        simp only [E_B, Finset.mem_filter] at hmem; exact ⟨hmem.1, hmem.2.1, hmem.2.2.1⟩
      · cases he
    hA_pass := fun i e he => by
      dsimp [A_list] at he; split_ifs at he with hi0
      · set p : Fin n := ⟨i.val - 1, by omega⟩
        have hp : p.val + 1 < n := by dsimp [p]; omega
        have hsp := hsLast_prop p hp
        have hinj := harc_inj p hp (sLast p hp) hsp.1 hsp.2.1 (fun h => hsp.2.2 _ h ⟨le_rfl, hsp.2.1⟩)
        have hsub : E_A i ⊆ active p hp := fun e he => by
          simp only [E_A, active, Finset.mem_filter] at he ⊢
          exact ⟨he.1, Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.1; dsimp [p]; omega),
            Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.2.1; dsimp [p]; omega)⟩
        have hmem := (sortByKey_spec (E_A i) _ (hinj.mono (Finset.coe_subset.mpr hsub))).2.1 e |>.mp he
        simp only [E_A, Finset.mem_filter] at hmem; exact ⟨hmem.1, hmem.2.1, hmem.2.2.1⟩
      · cases he
    hbefore_nodup := fun i => by
      by_cases hi0 : 0 < i.val
      · set p : Fin n := ⟨i.val - 1, by omega⟩
        have hp : p.val + 1 < n := by dsimp [p]; omega
        have hi_eq : (⟨p.val + 1, hp⟩ : Fin n) = i := Fin.ext (by dsimp [p]; omega)
        have h := (hbefore_eq_sort p hp).1
        simpa [hi_eq] using h
      · simp [B_list, In_list, A_list, hi0]
    hafter_nodup := fun i => by
      by_cases hi : i.val + 1 < n
      · exact (hafter_spec i hi).1
      · -- At `i = n - 1`: `E_B i = ∅`, `E_A i = ∅`, `Out_list i = []`!
        have hOut : Out_list i = [] := by dsimp [Out_list]; rw [dif_neg hi]
        have hB : B_list i = [] := by
          dsimp [B_list]; split_ifs with hi0
          · set p : Fin n := ⟨i.val - 1, by omega⟩
            have hp : p.val + 1 < n := by dsimp [p]; omega
            have hsp := hsLast_prop p hp
            have hinj := harc_inj p hp (sLast p hp) hsp.1 hsp.2.1 (fun h => hsp.2.2 _ h ⟨le_rfl, hsp.2.1⟩)
            have hsub : E_B i ⊆ active p hp := fun e he => by
              simp only [E_B, active, Finset.mem_filter] at he ⊢
              exact ⟨he.1, Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.1; dsimp [p]; omega),
                Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.2.1; dsimp [p]; omega)⟩
            apply List.eq_nil_iff_forall_not_mem.mpr; intro e he
            have hm := (sortByKey_spec (E_B i) _ (hinj.mono (Finset.coe_subset.mpr hsub))).2.1 e |>.mp he
            simp only [E_B, Finset.mem_filter] at hm
            have : i.val < e.r.val := hm.2.2.1; have : e.r.val < n := e.r.isLt; omega
          · rfl
        have hA : A_list i = [] := by
          dsimp [A_list]; split_ifs with hi0
          · set p : Fin n := ⟨i.val - 1, by omega⟩
            have hp : p.val + 1 < n := by dsimp [p]; omega
            have hsp := hsLast_prop p hp
            have hinj := harc_inj p hp (sLast p hp) hsp.1 hsp.2.1 (fun h => hsp.2.2 _ h ⟨le_rfl, hsp.2.1⟩)
            have hsub : E_A i ⊆ active p hp := fun e he => by
              simp only [E_A, active, Finset.mem_filter] at he ⊢
              exact ⟨he.1, Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.1; dsimp [p]; omega),
                Fin.le_def.mpr (by have := Fin.lt_def.mp he.2.2.1; dsimp [p]; omega)⟩
            apply List.eq_nil_iff_forall_not_mem.mpr; intro e he
            have hm := (sortByKey_spec (E_A i) _ (hinj.mono (Finset.coe_subset.mpr hsub))).2.1 e |>.mp he
            simp only [E_A, Finset.mem_filter] at hm
            have : i.val < e.r.val := hm.2.2.1; have : e.r.val < n := e.r.isLt; omega
          · rfl
        simp [hB, hOut, hA]
    hslab := hslab_seq
  }
  refine ⟨W, ?_⟩
  -- Sum `2 * (slabSwaps i hi).length` over `i : Fin n`: all intervals `[x i, x (i+1))` are PAIRWISE DISJOINT subsets of `Crit`!
  let slabSet (i : Fin n) : Finset ℝ :=
    if hi : i.val + 1 < n then
      Crit.filter (fun t => x i ≤ t ∧ t < x ⟨i.val + 1, hi⟩)
    else ∅
  have hdisj_slabs : Set.PairwiseDisjoint (Finset.univ : Finset (Fin n)) slabSet := by
    intro i _ j _ hne
    dsimp [Function.onFun, slabSet]
    rw [Finset.disjoint_left]; intro t h1 h2
    split_ifs at h1 h2 with hi hj
    · simp only [Finset.mem_filter] at h1 h2
      rcases lt_or_gt_of_ne hne with hij | hji
      · have hle : (⟨i.val + 1, hi⟩ : Fin n) ≤ j := fin_succ_le_of_lt hij hi
        have := hx.monotone hle
        linarith [h1.2.2, h2.2.1]
      · have hle : (⟨j.val + 1, hj⟩ : Fin n) ≤ i := fin_succ_le_of_lt hji hj
        have := hx.monotone hle
        linarith [h2.2.2, h1.2.1]
    · simp at h2
    · simp at h1
    · simp at h1
  have hstep_sum : ∀ i : Fin n,
      2 * (if hi : i.val + 1 < n then (W.swaps i hi).length else 0) ≤
        ∑ c ∈ slabSet i, crossAt c := by
    intro i
    dsimp [W, slabSet]
    split_ifs with hi
    · have h1 := hslab_len i hi
      have hsplit : Crit.filter (fun t => x i ≤ t ∧ t < x ⟨i.val + 1, hi⟩) =
          (if x i ∈ Crit then {x i} else ∅) ∪
          Crit.filter (fun t => x i < t ∧ t < x ⟨i.val + 1, hi⟩) := by
        ext t
        by_cases hxiC : x i ∈ Crit
        · simp only [hxiC, ↓reduceIte, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter]
          constructor
          · rintro ⟨htC, hle, hlt⟩
            rcases eq_or_lt_of_le hle with rfl | hlt'
            · exact Or.inl rfl
            · exact Or.inr ⟨htC, hlt', hlt⟩
          · rintro (rfl | ⟨htC, hlt', hlt⟩)
            · exact ⟨hxiC, le_rfl, hx (Fin.lt_def.mpr (by simp))⟩
            · exact ⟨htC, le_of_lt hlt', hlt⟩
        · simp only [hxiC, ↓reduceIte, Finset.empty_union, Finset.mem_filter]
          constructor
          · rintro ⟨htC, hle, hlt⟩
            rcases eq_or_lt_of_le hle with rfl | hlt'
            · exact absurd htC hxiC
            · exact ⟨htC, hlt', hlt⟩
          · rintro ⟨htC, hlt', hlt⟩; exact ⟨htC, le_of_lt hlt', hlt⟩
      have hdisj_xi : Disjoint (if x i ∈ Crit then ({x i} : Finset ℝ) else ∅)
          (Crit.filter (fun t => x i < t ∧ t < x ⟨i.val + 1, hi⟩)) := by
        split_ifs
        · rw [Finset.disjoint_left]; intro t h1 h2
          simp only [Finset.mem_singleton] at h1; subst h1
          exact absurd (Finset.mem_filter.mp h2).2.1 (lt_irrefl _)
        · exact Finset.disjoint_empty_left _
      rw [hsplit, Finset.sum_union hdisj_xi]
      have hxi_sum : (∑ c ∈ (if x i ∈ Crit then ({x i} : Finset ℝ) else ∅), crossAt c) =
          if x i ∈ Crit then crossAt (x i) else 0 := by split_ifs <;> simp
      rw [hxi_sum]; exact h1
    · simp
  unfold WiringDiagram.totalSwaps
  rw [Finset.mul_sum]
  calc ∑ i : Fin n, 2 * (if hi : i.val + 1 < n then (W.swaps i hi).length else 0)
      ≤ ∑ i : Fin n, ∑ c ∈ slabSet i, crossAt c := Finset.sum_le_sum fun i _ => hstep_sum i
    _ = ∑ c ∈ Finset.univ.biUnion slabSet, crossAt c := (Finset.sum_biUnion hdisj_slabs).symm
    _ ≤ ∑ c ∈ Crit, crossAt c := by
        refine Finset.sum_le_sum_of_subset ?_
        intro c hc
        obtain ⟨i, _, hci⟩ := Finset.mem_biUnion.mp hc
        dsimp [slabSet] at hci; split_ifs at hci
        · exact (Finset.mem_filter.mp hci).1
        · cases hci


/-! ## Section 5: Szemerédi–Trotter (1983), Unit Distances O(n^{4/3}), and Székely (1997) Ω(n^{4/5}) -/
private lemma medge_ext {n : ℕ} {e₁ e₂ : MEdge n}
    (hid : e₁.id = e₂.id) (hl : e₁.l = e₂.l) (hr : e₁.r = e₂.r) : e₁ = e₂ := by
  cases e₁; cases e₂; simp only [MEdge.mk.injEq] at *; exact ⟨hid, hl, hr⟩


/-- Generic similarity tilt `(x, y) ↦ (x + t y, -t x + y)` in `EuclideanSpace ℝ (Fin 2)`. -/
private def tilt (t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![p 0 + t * p 1, -t * p 0 + p 1]

@[simp] private lemma tilt_zero_coord (t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    tilt t p 0 = p 0 + t * p 1 := by simp [tilt]

@[simp] private lemma tilt_one_coord (t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    tilt t p 1 = -t * p 0 + p 1 := by simp [tilt]

private lemma tilt_add (t : ℝ) (p q : EuclideanSpace ℝ (Fin 2)) :
    tilt t (p + q) = tilt t p + tilt t q := by
  apply euc2_ext <;> simp [tilt] <;> ring

private lemma tilt_sub (t : ℝ) (p q : EuclideanSpace ℝ (Fin 2)) :
    tilt t (p - q) = tilt t p - tilt t q := by
  apply euc2_ext <;> simp [tilt] <;> ring

private lemma tilt_smul (t s : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    tilt t (s • p) = s • tilt t p := by
  apply euc2_ext <;> simp [tilt] <;> ring

private lemma dist_tilt (t : ℝ) (p q : EuclideanSpace ℝ (Fin 2)) :
    dist (tilt t p) (tilt t q) = Real.sqrt (1 + t ^ 2) * dist p q := by
  have hL : 0 ≤ dist (tilt t p) (tilt t q) := dist_nonneg
  have hR : 0 ≤ Real.sqrt (1 + t ^ 2) * dist p q := by positivity
  have hsq : dist (tilt t p) (tilt t q) ^ 2 = (Real.sqrt (1 + t ^ 2) * dist p q) ^ 2 := by
    rw [dist_sq_eq_euc2, mul_pow, Real.sq_sqrt (by positivity), dist_sq_eq_euc2,
      tilt_zero_coord, tilt_zero_coord, tilt_one_coord, tilt_one_coord]
    ring
  nlinarith

private lemma tilt_injective (t : ℝ) : Function.Injective (tilt t) := by
  intro p q h
  have h0 : dist (tilt t p) (tilt t q) = 0 := by rw [h, dist_self]
  rw [dist_tilt] at h0
  have hpos : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hd : dist p q = 0 := by nlinarith
  exact dist_eq_zero.mp hd

/-- For any finite point set `P ⊂ ℝ²`, there exists a similarity tilt `t : ℝ` such that BOTH
the `x`-coordinates and the `y`-coordinates of `tilt t '' P` are pairwise distinct! -/
private lemma exists_tilt_xy_inj (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ t : ℝ,
      Set.InjOn (fun p => (tilt t p) 0) (P : Set (EuclideanSpace ℝ (Fin 2))) ∧
      Set.InjOn (fun p => (tilt t p) 1) (P : Set (EuclideanSpace ℝ (Fin 2))) := by
  let badX : Finset ℝ := (P ×ˢ P).image (fun pq => -(pq.1 0 - pq.2 0) / (pq.1 1 - pq.2 1))
  let badY : Finset ℝ := (P ×ˢ P).image (fun pq => (pq.1 1 - pq.2 1) / (pq.1 0 - pq.2 0))
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (badX ∪ badY)
  have htX : t ∉ badX := fun h => ht (Finset.mem_union_left _ h)
  have htY : t ∉ badY := fun h => ht (Finset.mem_union_right _ h)
  refine ⟨t, ?_, ?_⟩
  · intro p hp q hq heq
    by_contra hne
    simp only [tilt_zero_coord] at heq
    by_cases h1 : p 1 = q 1
    · have h0 : p 0 = q 0 := by rw [h1] at heq; linarith
      exact hne (euc2_ext h0 h1)
    · have ht_eq : t = -(p 0 - q 0) / (p 1 - q 1) := by
        have hsub : p 1 - q 1 ≠ 0 := sub_ne_zero.mpr h1
        field_simp [hsub]
        linarith
      apply htX
      rw [ht_eq]
      exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩
  · intro p hp q hq heq
    by_contra hne
    simp only [tilt_one_coord] at heq
    by_cases h0 : p 0 = q 0
    · have h1 : p 1 = q 1 := by rw [h0] at heq; linarith
      exact hne (euc2_ext h0 h1)
    · have ht_eq : t = (p 1 - q 1) / (p 0 - q 0) := by
        have hsub : p 0 - q 0 ≠ 0 := sub_ne_zero.mpr h0
        field_simp [hsub]
        linarith
      apply htY
      rw [ht_eq]
      exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩

/-- Explicit 2-element `Finset` containing all intersection points of two circles with distinct
centers `c₁ ≠ c₂`. Zero topology, pure quadratic formula! -/
private lemma two_circles_inter_finset (c₁ c₂ : EuclideanSpace ℝ (Fin 2)) (r₁ r₂ : ℝ)
    (hne : c₁ ≠ c₂) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card ≤ 2 ∧
      ∀ p : EuclideanSpace ℝ (Fin 2), dist p c₁ = r₁ → dist p c₂ = r₂ → p ∈ S := by
  let a := c₂ 0 - c₁ 0
  let b := c₂ 1 - c₁ 1
  have hab : a ^ 2 + b ^ 2 ≠ 0 := by
    intro h0
    have ha : a = 0 := by nlinarith
    have hb : b = 0 := by nlinarith
    exact hne (euc2_ext (by dsimp [a] at ha; linarith) (by dsimp [b] at hb; linarith))
  have hab_pos : 0 < a ^ 2 + b ^ 2 := by
    have : 0 ≤ a ^ 2 + b ^ 2 := by positivity
    exact lt_of_le_of_ne this (Ne.symm hab)
  -- For any intersection point `p`, write `u = p 0 - c₁ 0`, `v = p 1 - c₁ 1`.
  -- Then `u² + v² = r₁²` and `(u - a)² + (v - b)² = r₂²`, so `2 (a u + b v) = r₁² - r₂² + a² + b²`.
  -- Letting `K = (r₁² - r₂² + a² + b²) / 2` and `D = a² + b² > 0`:
  -- `a u + b v = K` and `(-b u + a v)² = D (u² + v²) - (a u + b v)² = D r₁² - K²`!
  -- Thus `-b u + a v = ± s` where `s = √(D r₁² - K²)`, uniquely determining `(u, v)`!
  let D := a ^ 2 + b ^ 2
  let K := (r₁ ^ 2 - r₂ ^ 2 + D) / 2
  let s := Real.sqrt (D * r₁ ^ 2 - K ^ 2)
  let mkP (sgn : ℝ) : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 ![c₁ 0 + (a * K - b * sgn * s) / D, c₁ 1 + (b * K + a * sgn * s) / D]
  refine ⟨{mkP 1, mkP (-1)}, ?_, ?_⟩
  · calc ({mkP 1, mkP (-1)} : Finset _).card
        ≤ ({mkP (-1)} : Finset _).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  · intro p hp1 hp2
    have hsq1 : (p 0 - c₁ 0) ^ 2 + (p 1 - c₁ 1) ^ 2 = r₁ ^ 2 := by
      rw [← dist_sq_eq_euc2, hp1]
    have hsq2 : (p 0 - c₂ 0) ^ 2 + (p 1 - c₂ 1) ^ 2 = r₂ ^ 2 := by
      rw [← dist_sq_eq_euc2, hp2]
    set u := p 0 - c₁ 0
    set v := p 1 - c₁ 1
    have hlin : a * u + b * v = K := by
      have h2 : (u - a) ^ 2 + (v - b) ^ 2 = r₂ ^ 2 := by
        have hu : u - a = p 0 - c₂ 0 := by dsimp [u, a]; ring
        have hv : v - b = p 1 - c₂ 1 := by dsimp [v, b]; ring
        rw [hu, hv]; exact hsq2
      dsimp [K, D]
      nlinarith
    have hperp_sq : (-b * u + a * v) ^ 2 = D * r₁ ^ 2 - K ^ 2 := by
      have hid : (a * u + b * v) ^ 2 + (-b * u + a * v) ^ 2 = D * (u ^ 2 + v ^ 2) := by
        dsimp [D]; ring
      rw [hlin, hsq1] at hid
      linarith
    have hnonneg : 0 ≤ D * r₁ ^ 2 - K ^ 2 := by rw [← hperp_sq]; positivity
    have hs_sq : s ^ 2 = D * r₁ ^ 2 - K ^ 2 := Real.sq_sqrt hnonneg
    have hor : -b * u + a * v = s ∨ -b * u + a * v = -s :=
      sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [hperp_sq, hs_sq])
    have hD_ne : D ≠ 0 := hab
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hor with hpos | hneg
    · left
      apply euc2_ext <;> simp only [mkP, Matrix.cons_val_zero, Matrix.cons_val_one]
      · have : D * u = a * K - b * (1 * s) := by dsimp [D]; rw [← hlin, ← hpos]; ring
        have : u = (a * K - b * 1 * s) / D := by
          field_simp [hD_ne]; linarith
        dsimp [u] at this; linarith
      · have : D * v = b * K + a * (1 * s) := by dsimp [D]; rw [← hlin, ← hpos]; ring
        have : v = (b * K + a * 1 * s) / D := by
          field_simp [hD_ne]; linarith
        dsimp [v] at this; linarith
    · right
      have hs_eq : s = b * u - a * v := by linarith
      apply euc2_ext <;> simp only [mkP, Matrix.cons_val_zero, Matrix.cons_val_one]
      · have : D * u = a * K - b * (-1 * s) := by dsimp [D]; rw [← hlin, hs_eq]; ring
        have : u = (a * K - b * (-1) * s) / D := by
          field_simp [hD_ne]; linarith
        dsimp [u] at this; linarith
      · have : D * v = b * K + a * (-1 * s) := by dsimp [D]; rw [← hlin, hs_eq]; ring
        have : v = (b * K + a * (-1) * s) / D := by
          field_simp [hD_ne]; linarith
        dsimp [v] at this; linarith

/-! ### Part 2: Consecutive-Pairs Builder & 1D `AffineSubspace` Line Algebra -/

/-- Given a sorted `Nodup` list `ls : List (Fin n)` with `ls.Pairwise (· < ·)`, produce the list
of consecutive ordered pairs `(a, b)` with `a < b`. -/
private def consecPairs {n : ℕ} : List (Fin n) → List (Fin n × Fin n)
  | [] => []
  | [_] => []
  | a :: b :: rest => (a, b) :: consecPairs (b :: rest)

private lemma consecPairs_length {n : ℕ} (ls : List (Fin n)) :
    (consecPairs ls).length + 1 ≥ ls.length := by
  induction ls with
  | nil => simp [consecPairs]
  | cons a rest ih =>
    cases rest with
    | nil => simp [consecPairs]
    | cons b rest' =>
      simp only [consecPairs, List.length_cons] at ih ⊢
      omega

private lemma consecPairs_lt {n : ℕ} {ls : List (Fin n)} (hpw : ls.Pairwise (· < ·))
    {p : Fin n × Fin n} (hp : p ∈ consecPairs ls) : p.1 < p.2 := by
  induction ls with
  | nil => cases hp
  | cons a rest ih =>
    cases rest with
    | nil => cases hp
    | cons b rest' =>
      simp only [consecPairs, List.mem_cons] at hp
      rcases hp with rfl | hp'
      · exact (List.pairwise_cons.mp hpw).1 b (by simp)
      · exact ih (List.pairwise_cons.mp hpw).2 hp'

private lemma consecPairs_mem {n : ℕ} {ls : List (Fin n)}
    {p : Fin n × Fin n} (hp : p ∈ consecPairs ls) : p.1 ∈ ls ∧ p.2 ∈ ls := by
  induction ls with
  | nil => cases hp
  | cons a rest ih =>
    cases rest with
    | nil => cases hp
    | cons b rest' =>
      simp only [consecPairs, List.mem_cons] at hp
      rcases hp with rfl | hp'
      · exact ⟨by simp, by simp⟩
      · obtain ⟨h1, h2⟩ := ih hp'
        exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

private lemma consecPairs_no_between {n : ℕ} {ls : List (Fin n)} (hpw : ls.Pairwise (· < ·))
    {p : Fin n × Fin n} (hp : p ∈ consecPairs ls) {k : Fin n} (hk : k ∈ ls) :
    ¬(p.1 < k ∧ k < p.2) := by
  induction ls with
  | nil => cases hp
  | cons a rest ih =>
    cases rest with
    | nil => cases hp
    | cons b rest' =>
      have hpw1 := List.pairwise_cons.mp hpw
      have hpw2 := List.pairwise_cons.mp hpw1.2
      simp only [consecPairs, List.mem_cons] at hp
      rcases hp with rfl | hp'
      · rintro ⟨h1, h2⟩
        rcases List.mem_cons.mp hk with rfl | hk'
        · exact lt_irrefl _ h1
        · rcases List.mem_cons.mp hk' with rfl | hk''
          · exact lt_irrefl _ h2
          · exact lt_asymm h2 (hpw2.1 k hk'')
      · rcases List.mem_cons.mp hk with rfl | hk'
        · rintro ⟨h1, _⟩
          have hlt : k < p.1 := hpw1.1 p.1 (consecPairs_mem hp').1
          exact lt_asymm h1 hlt
        · exact ih hpw1.2 hp' hk'

private lemma consecPairs_disjoint_open {n : ℕ} {ls : List (Fin n)} (hpw : ls.Pairwise (· < ·))
    {p q : Fin n × Fin n} (hp : p ∈ consecPairs ls) (hq : q ∈ consecPairs ls) (hne : p ≠ q) :
    p.2 ≤ q.1 ∨ q.2 ≤ p.1 := by
  induction ls with
  | nil => cases hp
  | cons a rest ih =>
    cases rest with
    | nil => cases hp
    | cons b rest' =>
      have hpw1 := List.pairwise_cons.mp hpw
      have hpw2 := List.pairwise_cons.mp hpw1.2
      simp only [consecPairs, List.mem_cons] at hp hq
      rcases hp with rfl | hp' <;> rcases hq with rfl | hq'
      · exact absurd rfl hne
      · left
        have hq1 : q.1 ∈ b :: rest' := (consecPairs_mem hq').1
        rcases List.mem_cons.mp hq1 with rfl | hq1'
        · exact le_rfl
        · exact le_of_lt (hpw2.1 q.1 hq1')
      · right
        have hp1 : p.1 ∈ b :: rest' := (consecPairs_mem hp').1
        rcases List.mem_cons.mp hp1 with rfl | hp1'
        · exact le_rfl
        · exact le_of_lt (hpw2.1 p.1 hp1')
      · exact ih hpw1.2 hp' hq'

private lemma consecPairs_nodup {n : ℕ} {ls : List (Fin n)} (hpw : ls.Pairwise (· < ·)) :
    (consecPairs ls).Nodup := by
  induction ls with
  | nil => simp [consecPairs]
  | cons a rest ih =>
    cases rest with
    | nil => simp [consecPairs]
    | cons b rest' =>
      have hpw1 := List.pairwise_cons.mp hpw
      simp only [consecPairs, List.nodup_cons]
      refine ⟨fun hmem => ?_, ih hpw1.2⟩
      have ha_in : a ∈ b :: rest' := (consecPairs_mem hmem).1
      exact lt_irrefl a (hpw1.1 a ha_in)

/-- Characterize a 1-dimensional `AffineSubspace` containing two distinct points `p ≠ q` in `ℝ²`. -/
private lemma affineSubspace_finrank_one_iff (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
    (hdim : Module.finrank ℝ ℓ.direction = 1)
    {p q : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ ℓ) (hq : q ∈ ℓ) (hpq : p ≠ q)
    (r : EuclideanSpace ℝ (Fin 2)) :
    r ∈ ℓ ↔ ∃ s : ℝ, r = p + s • (q - p) := by
  have hqp_mem : q - p ∈ ℓ.direction := by
    have := AffineSubspace.vsub_mem_direction hq hp
    simpa [vsub_eq_sub] using this
  have hqp_ne : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hspan_le : Submodule.span ℝ ({q - p} : Set (EuclideanSpace ℝ (Fin 2))) ≤ ℓ.direction :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hqp_mem)
  have hspan_finrank : Module.finrank ℝ (Submodule.span ℝ ({q - p} : Set (EuclideanSpace ℝ (Fin 2)))) = 1 :=
    finrank_span_singleton hqp_ne
  have hdir_eq : Submodule.span ℝ ({q - p} : Set (EuclideanSpace ℝ (Fin 2))) = ℓ.direction :=
    Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [hspan_finrank, hdim])
  constructor
  · intro hr
    have hrmem : r - p ∈ ℓ.direction := by
      have := AffineSubspace.vsub_mem_direction hr hp
      simpa [vsub_eq_sub] using this
    rw [← hdir_eq, Submodule.mem_span_singleton] at hrmem
    obtain ⟨s, hs⟩ := hrmem
    exact ⟨s, by rw [hs]; abel⟩
  · rintro ⟨s, rfl⟩
    have hsmem : s • (q - p) ∈ ℓ.direction :=
      ℓ.direction.smul_mem s hqp_mem
    have := AffineSubspace.vadd_mem_of_mem_direction hsmem hp
    simpa [vadd_eq_add, add_comm] using this

/-- If a 1D `AffineSubspace` `ℓ` contains two points `p, q` with `tilt t p 0 ≠ tilt t q 0`, then
`r ∈ ℓ` iff `tilt t r` lies on the explicit non-vertical line `y = a * x + b`! -/
private lemma affineSubspace_tilt_line (t : ℝ) (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
    (hdim : Module.finrank ℝ ℓ.direction = 1)
    {p q : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ ℓ) (hq : q ∈ ℓ)
    (hxne : tilt t p 0 ≠ tilt t q 0) :
    let m := (tilt t q 1 - tilt t p 1) / (tilt t q 0 - tilt t p 0)
    let b := tilt t p 1 - m * tilt t p 0
    ∀ r : EuclideanSpace ℝ (Fin 2), r ∈ ℓ ↔ tilt t r 1 = m * tilt t r 0 + b := by
  intro m b r
  have hpq : p ≠ q := fun h => hxne (by rw [h])
  rw [affineSubspace_finrank_one_iff ℓ hdim hp hq hpq r]
  have hdx : tilt t q 0 - tilt t p 0 ≠ 0 := sub_ne_zero.mpr hxne.symm
  constructor
  · rintro ⟨s, rfl⟩
    have h0 : tilt t (p + s • (q - p)) 0 = tilt t p 0 + s * (tilt t q 0 - tilt t p 0) := by
      rw [tilt_add, tilt_smul, tilt_sub]; simp
    have h1 : tilt t (p + s • (q - p)) 1 = tilt t p 1 + s * (tilt t q 1 - tilt t p 1) := by
      rw [tilt_add, tilt_smul, tilt_sub]; simp
    rw [h0, h1]
    dsimp [m, b]
    field_simp [hdx]
    ring
  · intro hy
    let s := (tilt t r 0 - tilt t p 0) / (tilt t q 0 - tilt t p 0)
    refine ⟨s, tilt_injective t ?_⟩
    apply euc2_ext
    · rw [tilt_add, tilt_smul, tilt_sub]; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      dsimp [s]; field_simp [hdx]; ring
    · rw [tilt_add, tilt_smul, tilt_sub]; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [hy]
      dsimp [s, m, b]; field_simp [hdx]; ring

/-! ### Part 3: Szemerédi–Trotter (1983) Incidence Theorem & `t`-Rich Lines -/

/-- **Szemerédi–Trotter (1983) Cube Form (Exact Algebraic Bound)**:
For any finite set of points `P` and finite set of 1D affine lines `L` in `ℝ²`, letting
`I = ∑ ℓ ∈ L, (P.filter (· ∈ ℓ)).card` and `E = ∑ ℓ ∈ L, ((P.filter (· ∈ ℓ)).card - 1)`:
either `E < 4 * P.card`, or `E ^ 3 ≤ 32 * P.card ^ 2 * L.card ^ 2`! -/
private theorem szemeredi_trotter_cube (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (hL : ∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1) :
    let E_cnt := ∑ ℓ ∈ L, ((P.filter (· ∈ ℓ)).card - 1)
    E_cnt < 4 * P.card ∨ E_cnt ^ 3 ≤ 32 * P.card ^ 2 * L.card ^ 2 := by
  intro E_cnt
  by_cases hsmall : E_cnt < 4 * P.card
  · exact Or.inl hsmall
  right
  push Not at hsmall
  -- Discard lines with `< 2` points of `P`: they contribute `0` to `E_cnt`!
  let L2 := L.filter (fun ℓ => 2 ≤ (P.filter (· ∈ ℓ)).card)
  have hE_eq : E_cnt = ∑ ℓ ∈ L2, ((P.filter (· ∈ ℓ)).card - 1) := by
    dsimp [E_cnt, L2]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    split_ifs with h2
    · rfl
    · omega
  have hL2_le : L2.card ≤ L.card := Finset.card_le_card (Finset.filter_subset _ _)
  -- Apply generic similarity tilt `t` so `x`-coordinates of `P` are strictly injective!
  obtain ⟨t, htX, _⟩ := exists_tilt_xy_inj P
  set n := P.card
  -- Sort `P` by increasing `(tilt t p) 0`, obtaining a bijection `v : Fin n → P`!
  let X : Finset ℝ := P.image (fun p => (tilt t p) 0)
  have hX_card : X.card = n := Finset.card_image_of_injOn htX
  let sortedX : List ℝ := X.sort (· ≤ ·)
  have hlenX : sortedX.length = n := by rw [Finset.length_sort, hX_card]
  have hv_ex : ∀ i : Fin n, ∃ p ∈ P, (tilt t p) 0 = sortedX[i.val]'(by omega) := fun i =>
    Finset.mem_image.mp ((Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem (l := sortedX) (n := i.val) (by omega)))
  let v : Fin n → EuclideanSpace ℝ (Fin 2) := fun i => Classical.choose (hv_ex i)
  have hv_mem : ∀ i : Fin n, v i ∈ P := fun i => (Classical.choose_spec (hv_ex i)).1
  have hv_x : ∀ i : Fin n, (tilt t (v i)) 0 = sortedX[i.val]'(by omega) := fun i =>
    (Classical.choose_spec (hv_ex i)).2
  have hx_strict : StrictMono (fun i : Fin n => (tilt t (v i)) 0) := by
    intro i j hij
    dsimp only
    rw [hv_x i, hv_x j]
    have hpw : sortedX.Pairwise (· ≤ ·) := Finset.pairwise_sort X (· ≤ ·)
    have hnd : sortedX.Nodup := Finset.sort_nodup X (· ≤ ·)
    have hle : sortedX[i.val]'(by omega) ≤ sortedX[j.val]'(by omega) :=
      List.pairwise_iff_getElem.mp hpw i.val j.val (by omega) (by omega) hij
    have hne : sortedX[i.val]'(by omega) ≠ sortedX[j.val]'(by omega) :=
      List.pairwise_iff_getElem.mp hnd i.val j.val (by omega) (by omega) hij
    exact lt_of_le_of_ne hle hne
  have hv_inj : Function.Injective v := fun i j h => by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact ne_of_lt (hx_strict hij) (by dsimp only; rw [h])
    · exact ne_of_gt (hx_strict hji) (by dsimp only; rw [h])
  have hv_surj : ∀ p ∈ P, ∃ i : Fin n, v i = p := fun p hp => by
    have hmem : (tilt t p) 0 ∈ sortedX := (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_image_of_mem _ hp)
    obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
    refine ⟨⟨k, by omega⟩, htX (hv_mem _) hp ?_⟩
    dsimp only; rw [hv_x]; exact hget
  -- For each line `ℓ ∈ L2`, extract its explicit linear function `y = slope ℓ * x + intercept ℓ`!
  have hline_params : ∀ ℓ ∈ L2, ∃ ab : ℝ × ℝ,
      ∀ r : EuclideanSpace ℝ (Fin 2), r ∈ ℓ ↔ tilt t r 1 = ab.1 * tilt t r 0 + ab.2 := by
    intro ℓ hℓ
    have hℓL : ℓ ∈ L := (Finset.mem_filter.mp hℓ).1
    have h2 : 1 < (P.filter (· ∈ ℓ)).card := by have := (Finset.mem_filter.mp hℓ).2; omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h2
    simp only [Finset.mem_filter] at hp hq
    have hxne : tilt t p 0 ≠ tilt t q 0 := fun h => hpq (htX hp.1 hq.1 h)
    exact ⟨((tilt t q 1 - tilt t p 1) / (tilt t q 0 - tilt t p 0),
      tilt t p 1 - ((tilt t q 1 - tilt t p 1) / (tilt t q 0 - tilt t p 0)) * tilt t p 0),
      affineSubspace_tilt_line t ℓ (hL ℓ hℓL) hp.2 hq.2 hxne⟩
  let lineFun (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : ℝ × ℝ :=
    if h : ℓ ∈ L2 then Classical.choose (hline_params ℓ h) else (0, 0)
  have hlineFun_spec : ∀ ℓ ∈ L2, ∀ r : EuclideanSpace ℝ (Fin 2),
      r ∈ ℓ ↔ tilt t r 1 = (lineFun ℓ).1 * tilt t r 0 + (lineFun ℓ).2 := fun ℓ hℓ => by
    dsimp [lineFun]; rw [dif_pos hℓ]; exact Classical.choose_spec (hline_params ℓ hℓ)
  -- Two distinct lines `ℓ₁ ≠ ℓ₂` in `L2` have DISTINCT linear functions!
  have hlineFun_inj : Set.InjOn lineFun (L2 : Set _) := by
    intro ℓ₁ h₁ ℓ₂ h₂ heq
    apply SetLike.ext; intro r
    rw [hlineFun_spec ℓ₁ h₁ r, hlineFun_spec ℓ₂ h₂ r, heq]
  -- Assign each `ℓ ∈ L2` a unique `ℕ` id via `L2.equivFin`!
  let eL2 : L2 ≃ Fin L2.card := L2.equivFin
  let lineOfId (k : ℕ) : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
    if hk : k < L2.card then (eL2.symm ⟨k, hk⟩).1 else ⊥
  -- For each `ℓ ∈ L2`, build the sorted list of indices `i : Fin n` with `v i ∈ ℓ`!
  let idxList (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : List (Fin n) :=
    (Finset.univ.filter (fun i : Fin n => v i ∈ ℓ)).sort (· ≤ ·)
  have hidx_len : ∀ ℓ ∈ L2, (idxList ℓ).length = (P.filter (· ∈ ℓ)).card := fun ℓ _ => by
    rw [Finset.length_sort]
    refine Finset.card_bij (fun i _ => v i) (fun i hi => ?_) (fun _ _ _ _ h => hv_inj h) (fun p hp => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨hv_mem i, hi⟩
    · simp only [Finset.mem_filter] at hp
      obtain ⟨i, rfl⟩ := hv_surj p hp.1
      exact ⟨i, by simp [hp.2], rfl⟩
  have hidx_pw : ∀ ℓ, (idxList ℓ).Pairwise (· < ·) := fun ℓ =>
    List.Pairwise.imp_of_mem (fun {a b} _ _ ⟨h1, h2⟩ => lt_of_le_of_ne h1 h2)
      ((Finset.pairwise_sort _ _).and (Finset.sort_nodup _ _))
  -- Build the edge set `E : Finset (MEdge n)`: consecutive pairs on each `ℓ ∈ L2`!
  let lineEdges (k : Fin L2.card) : Finset (MEdge n) :=
    let ℓ := (eL2.symm k).1
    ((consecPairs (idxList ℓ)).attach.map
      (fun pq => (⟨k.val, pq.1.1, pq.1.2, consecPairs_lt (hidx_pw ℓ) pq.2⟩ : MEdge n))).toFinset
  have hlineEdges_card : ∀ k : Fin L2.card,
      (lineEdges k).card = (P.filter (· ∈ (eL2.symm k).1)).card - 1 := fun k => by
    let ℓ := (eL2.symm k).1
    have hℓ : ℓ ∈ L2 := (eL2.symm k).2
    have hnd : ((consecPairs (idxList ℓ)).attach.map
        (fun pq => (⟨k.val, pq.1.1, pq.1.2, consecPairs_lt (hidx_pw ℓ) pq.2⟩ : MEdge n))).Nodup :=
      (List.nodup_attach.mpr (consecPairs_nodup (hidx_pw ℓ))).map (fun a b h => by
        cases a; cases b; simp only [MEdge.mk.injEq] at h
        exact Subtype.ext (Prod.ext h.2.1 h.2.2))
    dsimp only [lineEdges]
    rw [List.toFinset_card_of_nodup hnd, List.length_map, List.length_attach]
    have hexact : ∀ ls : List (Fin n), (consecPairs ls).length = ls.length - 1 := by
      intro ls; induction ls with
      | nil => rfl
      | cons a rest ih =>
        cases rest with
        | nil => rfl
        | cons b rest' => simp only [consecPairs, List.length_cons] at ih ⊢; omega
    rw [hexact, hidx_len ℓ hℓ]
  have hlineEdges_disj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin L2.card)) lineEdges := by
    intro k₁ _ k₂ _ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]; intro e h1 h2
    simp only [lineEdges, List.mem_toFinset, List.mem_map, List.mem_attach, true_and, Subtype.exists] at h1 h2
    obtain ⟨_, _, h1eq⟩ := h1; obtain ⟨_, _, h2eq⟩ := h2
    have hid1 : e.id = k₁.val := congrArg MEdge.id h1eq.symm
    have hid2 : e.id = k₂.val := congrArg MEdge.id h2eq.symm
    exact hne (Fin.ext (by omega))
  let E : Finset (MEdge n) := Finset.univ.biUnion lineEdges
  have hE_card : E.card = E_cnt := by
    rw [Finset.card_biUnion hlineEdges_disj, hE_eq]
    trans ∑ k : Fin L2.card, ((P.filter (· ∈ (eL2.symm k).1)).card - 1)
    · exact Finset.sum_congr rfl fun k _ => hlineEdges_card k
    · exact Finset.sum_bij (fun k _ => (eL2.symm k).1) (fun k _ => (eL2.symm k).2)
        (fun k₁ _ k₂ _ h => eL2.symm.injective (Subtype.ext h))
        (fun ℓ hℓ => ⟨eL2 ⟨ℓ, hℓ⟩, Finset.mem_univ _, by simp⟩) (fun _ _ => rfl)
  -- Helper: recover the line `ℓ` of any edge `e ∈ E`!
  have he_info : ∀ e ∈ E, ∃ hk : e.id < L2.card,
      (e.l, e.r) ∈ consecPairs (idxList (eL2.symm ⟨e.id, hk⟩).1) := by
    intro e he
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp he
    simp only [lineEdges, List.mem_toFinset, List.mem_map, List.mem_attach, true_and, Subtype.exists] at hk
    obtain ⟨pq, hpq, heq⟩ := hk
    have hid : e.id = k.val := congrArg MEdge.id heq.symm
    have hlt : e.id < L2.card := by rw [hid]; exact k.isLt
    have hkeq : (⟨e.id, hlt⟩ : Fin L2.card) = k := Fin.ext hid
    refine ⟨hlt, ?_⟩
    rw [hkeq]
    have hlr : (e.l, e.r) = pq := by cases heq; rfl
    rw [hlr]; exact hpq
  -- Multiplicity bound `m = 1`: two distinct lines cannot BOTH contain `v i` and `v j`!
  have hmult1 : ∀ (i j : Fin n), (E.filter (fun e => e.l = i ∧ e.r = j)).card ≤ 1 := by
    intro i j
    refine Finset.card_le_one.mpr fun e₁ he₁ e₂ he₂ => ?_
    simp only [Finset.mem_filter] at he₁ he₂
    obtain ⟨hk₁, hpq₁⟩ := he_info e₁ he₁.1
    obtain ⟨hk₂, hpq₂⟩ := he_info e₂ he₂.1
    let ℓ₁ := (eL2.symm ⟨e₁.id, hk₁⟩).1
    let ℓ₂ := (eL2.symm ⟨e₂.id, hk₂⟩).1
    have hℓ₁ : ℓ₁ ∈ L2 := (eL2.symm ⟨e₁.id, hk₁⟩).2
    have hℓ₂ : ℓ₂ ∈ L2 := (eL2.symm ⟨e₂.id, hk₂⟩).2
    have hm1 := consecPairs_mem hpq₁
    have hm2 := consecPairs_mem hpq₂
    have hi1 : v i ∈ ℓ₁ := by
      have := (Finset.mem_sort (· ≤ ·)).mp (he₁.2.1 ▸ hm1.1)
      exact (Finset.mem_filter.mp this).2
    have hj1 : v j ∈ ℓ₁ := by
      have := (Finset.mem_sort (· ≤ ·)).mp (he₁.2.2 ▸ hm1.2)
      exact (Finset.mem_filter.mp this).2
    have hi2 : v i ∈ ℓ₂ := by
      have := (Finset.mem_sort (· ≤ ·)).mp (he₂.2.1 ▸ hm2.1)
      exact (Finset.mem_filter.mp this).2
    have hj2 : v j ∈ ℓ₂ := by
      have := (Finset.mem_sort (· ≤ ·)).mp (he₂.2.2 ▸ hm2.2)
      exact (Finset.mem_filter.mp this).2
    have hij : i < j := he₁.2.1 ▸ he₁.2.2 ▸ e₁.hlr
    have hxij : (tilt t (v i)) 0 ≠ (tilt t (v j)) 0 := ne_of_lt (hx_strict hij)
    have hline_eq : lineFun ℓ₁ = lineFun ℓ₂ := by
      have hi1' := (hlineFun_spec ℓ₁ hℓ₁ (v i)).mp hi1
      have hj1' := (hlineFun_spec ℓ₁ hℓ₁ (v j)).mp hj1
      have hi2' := (hlineFun_spec ℓ₂ hℓ₂ (v i)).mp hi2
      have hj2' := (hlineFun_spec ℓ₂ hℓ₂ (v j)).mp hj2
      have hsub : (tilt t (v j)) 0 - (tilt t (v i)) 0 ≠ 0 := sub_ne_zero.mpr hxij.symm
      have ha : (lineFun ℓ₁).1 = (lineFun ℓ₂).1 := by
        have hmul : ((lineFun ℓ₁).1 - (lineFun ℓ₂).1) * ((tilt t (v j)) 0 - (tilt t (v i)) 0) = 0 := by linarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hsub)
      have hb : (lineFun ℓ₁).2 = (lineFun ℓ₂).2 := by rw [ha] at hi1'; linarith
      exact Prod.ext ha hb
    have hℓ_eq : ℓ₁ = ℓ₂ := hlineFun_inj hℓ₁ hℓ₂ hline_eq
    have hid_eq : e₁.id = e₂.id := by
      have := eL2.symm.injective (Subtype.ext hℓ_eq)
      exact congrArg Fin.val this
    have hl_eq : e₁.l = e₂.l := he₁.2.1.trans he₂.2.1.symm
    have hr_eq : e₁.r = e₂.r := he₁.2.2.trans he₂.2.2.symm
    cases e₁; cases e₂; simp only [MEdge.mk.injEq] at hl_eq hr_eq hid_eq ⊢
    exact ⟨hid_eq, hl_eq, hr_eq⟩
  -- Define linear arc `arc e x = (lineFun ℓ).1 * x + (lineFun ℓ).2`!
  let x : Fin n → ℝ := fun i => (tilt t (v i)) 0
  let yv : Fin n → ℝ := fun i => (tilt t (v i)) 1
  let arc (e : MEdge n) (s : ℝ) : ℝ :=
    let ab := lineFun (lineOfId e.id)
    ab.1 * s + ab.2
  -- Critical x-coordinates: intersection of every pair of non-parallel lines in `L2`!
  let interX (ℓ₁ ℓ₂ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : ℝ :=
    ((lineFun ℓ₂).2 - (lineFun ℓ₁).2) / ((lineFun ℓ₁).1 - (lineFun ℓ₂).1)
  let Crit : Finset ℝ := (L2 ×ˢ L2).image (fun p => interX p.1 p.2)
  have hCrit : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ≠ e₂ → ∀ s : ℝ,
      x e₁.l < s → s < x e₁.r → x e₂.l < s → s < x e₂.r → arc e₁ s = arc e₂ s → s ∈ Crit := by
    intro e₁ he₁ e₂ he₂ hne s h1l h1r h2l h2r heq
    obtain ⟨hk₁, hpq₁⟩ := he_info e₁ he₁
    obtain ⟨hk₂, hpq₂⟩ := he_info e₂ he₂
    let ℓ₁ := (eL2.symm ⟨e₁.id, hk₁⟩).1
    let ℓ₂ := (eL2.symm ⟨e₂.id, hk₂⟩).1
    have hℓ₁ : ℓ₁ ∈ L2 := (eL2.symm ⟨e₁.id, hk₁⟩).2
    have hℓ₂ : ℓ₂ ∈ L2 := (eL2.symm ⟨e₂.id, hk₂⟩).2
    have hid_ne : e₁.id ≠ e₂.id := by
      intro hsame
      have hpq2' : (e₂.l, e₂.r) ∈ consecPairs (idxList ℓ₁) := by
        have hfin : (⟨e₁.id, hk₁⟩ : Fin L2.card) = ⟨e₂.id, hk₂⟩ := Fin.ext hsame
        simpa [ℓ₁, hfin] using hpq₂
      have hpq_ne : (e₁.l, e₁.r) ≠ (e₂.l, e₂.r) := fun h => hne (by
        have h1 : e₁.l = e₂.l := congrArg Prod.fst h
        have h2 : e₁.r = e₂.r := congrArg Prod.snd h
        cases e₁; cases e₂; simp only [MEdge.mk.injEq] at h1 h2 hsame ⊢; exact ⟨hsame, h1, h2⟩)
      rcases consecPairs_disjoint_open (hidx_pw ℓ₁) hpq₁ hpq2' hpq_ne with hle | hle
      · have := hx_strict.monotone hle; linarith
      · have := hx_strict.monotone hle; linarith
    have hℓ_ne : ℓ₁ ≠ ℓ₂ := fun h => hid_ne (congrArg Fin.val (eL2.symm.injective (Subtype.ext h)))
    have hfun_ne : lineFun ℓ₁ ≠ lineFun ℓ₂ := fun h => hℓ_ne (hlineFun_inj hℓ₁ hℓ₂ h)
    have hlo1 : lineOfId e₁.id = ℓ₁ := by dsimp [lineOfId, ℓ₁]; rw [dif_pos hk₁]
    have hlo2 : lineOfId e₂.id = ℓ₂ := by dsimp [lineOfId, ℓ₂]; rw [dif_pos hk₂]
    dsimp [arc] at heq; rw [hlo1, hlo2] at heq
    have hslope_ne : (lineFun ℓ₁).1 ≠ (lineFun ℓ₂).1 := by
      intro h1
      have h2 : (lineFun ℓ₁).2 = (lineFun ℓ₂).2 := by rw [h1] at heq; linarith
      exact hfun_ne (Prod.ext h1 h2)
    have hs_eq : s = interX ℓ₁ ℓ₂ := by
      dsimp [interX]
      have hsub : (lineFun ℓ₁).1 - (lineFun ℓ₂).1 ≠ 0 := sub_ne_zero.mpr hslope_ne
      field_simp [hsub]; linarith
    rw [hs_eq]
    exact Finset.mem_image.mpr ⟨(ℓ₁, ℓ₂), Finset.mem_product.mpr ⟨hℓ₁, hℓ₂⟩, rfl⟩
  -- Invoke `xmonotone_to_wiring`!
  obtain ⟨W, hW_swaps⟩ := xmonotone_to_wiring (n := n) x yv hx_strict E arc
    (fun e _ => (continuous_const.mul continuous_id |>.add continuous_const).continuousOn)
    (fun e he => by
      obtain ⟨hk, hpq⟩ := he_info e he
      have hlo : lineOfId e.id = (eL2.symm ⟨e.id, hk⟩).1 := by dsimp [lineOfId]; rw [dif_pos hk]
      have hmem : v e.l ∈ (eL2.symm ⟨e.id, hk⟩).1 :=
        (Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp (consecPairs_mem hpq).1)).2
      dsimp [arc, x, yv]; rw [hlo]
      exact ((hlineFun_spec _ (eL2.symm ⟨e.id, hk⟩).2 (v e.l)).mp hmem).symm)
    (fun e he => by
      obtain ⟨hk, hpq⟩ := he_info e he
      have hlo : lineOfId e.id = (eL2.symm ⟨e.id, hk⟩).1 := by dsimp [lineOfId]; rw [dif_pos hk]
      have hmem : v e.r ∈ (eL2.symm ⟨e.id, hk⟩).1 :=
        (Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp (consecPairs_mem hpq).2)).2
      dsimp [arc, x, yv]; rw [hlo]
      exact ((hlineFun_spec _ (eL2.symm ⟨e.id, hk⟩).2 (v e.r)).mp hmem).symm)
    (fun e he i hli hir hEq => by
      obtain ⟨hk, hpq⟩ := he_info e he
      have hlo : lineOfId e.id = (eL2.symm ⟨e.id, hk⟩).1 := by dsimp [lineOfId]; rw [dif_pos hk]
      dsimp [arc, x, yv] at hEq; rw [hlo] at hEq
      have hvi : v i ∈ (eL2.symm ⟨e.id, hk⟩).1 :=
        (hlineFun_spec _ (eL2.symm ⟨e.id, hk⟩).2 (v i)).mpr hEq.symm
      have hi_mem : i ∈ idxList (eL2.symm ⟨e.id, hk⟩).1 :=
        (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvi⟩)
      exact consecPairs_no_between (hidx_pw _) hpq hi_mem ⟨hli, hir⟩)
    Crit hCrit
  -- Bound `∑ c ∈ Crit, crossAt c ≤ L2.card ^ 2` by mapping each crossing pair `(e₁, e₂)` injectively to `(e₁.id, e₂.id)`!
  have hcross_ub :
      (∑ c ∈ Crit, ((E ×ˢ E).filter (fun p => p.1 ≠ p.2 ∧
        x p.1.l < c ∧ c < x p.1.r ∧ x p.2.l < c ∧ c < x p.2.r ∧
        arc p.1 c = arc p.2 c)).card) ≤ L2.card ^ 2 := by
    let Cross := (Crit.sigma fun c =>
      (E ×ˢ E).filter (fun p => p.1 ≠ p.2 ∧
        x p.1.l < c ∧ c < x p.1.r ∧ x p.2.l < c ∧ c < x p.2.r ∧
        arc p.1 c = arc p.2 c))
    have hcard_eq : (∑ c ∈ Crit, ((E ×ˢ E).filter (fun p => p.1 ≠ p.2 ∧
        x p.1.l < c ∧ c < x p.1.r ∧ x p.2.l < c ∧ c < x p.2.r ∧
        arc p.1 c = arc p.2 c)).card) = Cross.card := (Finset.card_sigma _ _).symm
    rw [hcard_eq]
    have hinj : Set.InjOn (fun q : Σ _ : ℝ, MEdge n × MEdge n => (q.2.1.id, q.2.2.id)) (Cross : Set _) := by
      intro q₁ hq₁ q₂ hq₂ heq
      simp only [Cross, Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Finset.mem_product] at hq₁ hq₂
      obtain ⟨hid1, hid2⟩ := Prod.mk.inj heq
      obtain ⟨hk₁a, hpq₁a⟩ := he_info q₁.2.1 hq₁.2.1.1
      obtain ⟨hk₁b, hpq₁b⟩ := he_info q₁.2.2 hq₁.2.1.2
      obtain ⟨hk₂a, hpq₂a⟩ := he_info q₂.2.1 hq₂.2.1.1
      obtain ⟨hk₂b, hpq₂b⟩ := he_info q₂.2.2 hq₂.2.1.2
      -- Distinct lines have a UNIQUE intersection x-coordinate, so `q₁.1 = q₂.1`!
      have hlo1a : lineOfId q₁.2.1.id = (eL2.symm ⟨q₁.2.1.id, hk₁a⟩).1 := by dsimp [lineOfId]; rw [dif_pos hk₁a]
      have hlo1b : lineOfId q₁.2.2.id = (eL2.symm ⟨q₁.2.2.id, hk₁b⟩).1 := by dsimp [lineOfId]; rw [dif_pos hk₁b]
      have hne_id : q₁.2.1.id ≠ q₁.2.2.id := by
        intro hsame
        have hfin : (⟨q₁.2.1.id, hk₁a⟩ : Fin L2.card) = ⟨q₁.2.2.id, hk₁b⟩ := Fin.ext hsame
        have hpq' : (q₁.2.2.l, q₁.2.2.r) ∈ consecPairs (idxList (eL2.symm ⟨q₁.2.1.id, hk₁a⟩).1) := by
          simpa [hfin] using hpq₁b
        have hpq_ne : (q₁.2.1.l, q₁.2.1.r) ≠ (q₁.2.2.l, q₁.2.2.r) := fun h => hq₁.2.2.1
          (medge_ext hsame (congrArg Prod.fst h) (congrArg Prod.snd h))
        rcases consecPairs_disjoint_open (hidx_pw _) hpq₁a hpq' hpq_ne with hle | hle
        · have := hx_strict.monotone hle; linarith [hq₁.2.2.2.2.1, hq₁.2.2.2.2.2.1]
        · have := hx_strict.monotone hle; linarith [hq₁.2.2.2.1, hq₁.2.2.2.2.2.2.1]
      have hℓ_ne : (eL2.symm ⟨q₁.2.1.id, hk₁a⟩).1 ≠ (eL2.symm ⟨q₁.2.2.id, hk₁b⟩).1 :=
        fun h => hne_id (congrArg Fin.val (eL2.symm.injective (Subtype.ext h)))
      have hfun_ne := fun h => hℓ_ne (hlineFun_inj (eL2.symm ⟨q₁.2.1.id, hk₁a⟩).2 (eL2.symm ⟨q₁.2.2.id, hk₁b⟩).2 h)
      have heq1 := hq₁.2.2.2.2.2.2.2
      have heq2 := hq₂.2.2.2.2.2.2.2
      dsimp [arc] at heq1 heq2
      rw [hlo1a, hlo1b] at heq1
      have hlo2a : lineOfId q₂.2.1.id = (eL2.symm ⟨q₁.2.1.id, hk₁a⟩).1 := by
        rw [← hid1]; exact hlo1a
      have hlo2b : lineOfId q₂.2.2.id = (eL2.symm ⟨q₁.2.2.id, hk₁b⟩).1 := by
        rw [← hid2]; exact hlo1b
      rw [hlo2a, hlo2b] at heq2
      have hslope_ne : (lineFun (eL2.symm ⟨q₁.2.1.id, hk₁a⟩).1).1 ≠ (lineFun (eL2.symm ⟨q₁.2.2.id, hk₁b⟩).1).1 := by
        intro h1; rw [h1] at heq1; exact hfun_ne (Prod.ext h1 (by linarith))
      have hc_eq : q₁.1 = q₂.1 := by
        have hmul : ((lineFun (eL2.symm ⟨q₁.2.1.id, hk₁a⟩).1).1 - (lineFun (eL2.symm ⟨q₁.2.2.id, hk₁b⟩).1).1) *
            (q₁.1 - q₂.1) = 0 := by linarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hslope_ne))
      -- At the same x-coordinate `q₁.1 = q₂.1`, each line has AT MOST ONE active consecutive segment!
      have he1_eq : q₁.2.1 = q₂.2.1 := by
        by_contra hne1
        have hfin : (⟨q₁.2.1.id, hk₁a⟩ : Fin L2.card) = ⟨q₂.2.1.id, hk₂a⟩ := Fin.ext hid1
        have hpq' : (q₂.2.1.l, q₂.2.1.r) ∈ consecPairs (idxList (eL2.symm ⟨q₁.2.1.id, hk₁a⟩).1) := by
          simpa [hfin] using hpq₂a
        have hpq_ne : (q₁.2.1.l, q₁.2.1.r) ≠ (q₂.2.1.l, q₂.2.1.r) := fun h => hne1
          (medge_ext hid1 (congrArg Prod.fst h) (congrArg Prod.snd h))
        rcases consecPairs_disjoint_open (hidx_pw _) hpq₁a hpq' hpq_ne with hle | hle
        · have := hx_strict.monotone hle; linarith [hq₁.2.2.2.2.1, hq₂.2.2.2.1, hc_eq]
        · have := hx_strict.monotone hle; linarith [hq₁.2.2.2.1, hq₂.2.2.2.2.1, hc_eq]
      have he2_eq : q₁.2.2 = q₂.2.2 := by
        by_contra hne2
        have hfin : (⟨q₁.2.2.id, hk₁b⟩ : Fin L2.card) = ⟨q₂.2.2.id, hk₂b⟩ := Fin.ext hid2
        have hpq' : (q₂.2.2.l, q₂.2.2.r) ∈ consecPairs (idxList (eL2.symm ⟨q₁.2.2.id, hk₁b⟩).1) := by
          simpa [hfin] using hpq₂b
        have hpq_ne : (q₁.2.2.l, q₁.2.2.r) ≠ (q₂.2.2.l, q₂.2.2.r) := fun h => hne2
          (medge_ext hid2 (congrArg Prod.fst h) (congrArg Prod.snd h))
        rcases consecPairs_disjoint_open (hidx_pw _) hpq₁b hpq' hpq_ne with hle | hle
        · have := hx_strict.monotone hle; linarith [hq₁.2.2.2.2.2.2.1, hq₂.2.2.2.2.2.1, hc_eq]
        · have := hx_strict.monotone hle; linarith [hq₁.2.2.2.2.2.1, hq₂.2.2.2.2.2.2.1, hc_eq]
      cases q₁; cases q₂; simp only at hc_eq he1_eq he2_eq
      subst hc_eq; congr 1; exact Prod.ext he1_eq he2_eq
    have hsub : Cross.image (fun q => (q.2.1.id, q.2.2.id)) ⊆ Finset.range L2.card ×ˢ Finset.range L2.card := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      simp only [Cross, Finset.mem_sigma, Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨hk1, _⟩ := he_info q.2.1 hq.2.1.1
      obtain ⟨hk2, _⟩ := he_info q.2.2 hq.2.1.2
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hk1, Finset.mem_range.mpr hk2⟩
    calc Cross.card
        = (Cross.image (fun q => (q.2.1.id, q.2.2.id))).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range L2.card ×ˢ Finset.range L2.card).card := Finset.card_le_card hsub
      _ = L2.card ^ 2 := by rw [Finset.card_product, Finset.card_range, sq]
  have hW_le : 2 * W.totalSwaps ≤ L2.card ^ 2 := le_trans hW_swaps hcross_ub
  -- Apply our self-contained Multigraph Crossing Lemma (`m = 1`)!
  have hcl := wiring_multigraph_crossing_lemma (n := n) (E := E) (m := 1) W (by omega) hmult1
    (by rw [hE_card]; omega)
  rw [hE_card, mul_one] at hcl
  have hL2_sq : L2.card ^ 2 ≤ L.card ^ 2 := Nat.pow_le_pow_left hL2_le 2
  calc E_cnt ^ 3
      ≤ 64 * n ^ 2 * W.totalSwaps := hcl
    _ = 32 * n ^ 2 * (2 * W.totalSwaps) := by ring
    _ ≤ 32 * n ^ 2 * L2.card ^ 2 := Nat.mul_le_mul_left _ hW_le
    _ ≤ 32 * n ^ 2 * L.card ^ 2 := Nat.mul_le_mul_left _ hL2_sq

/-- **Szemerédi–Trotter (1983) Incidence Theorem (Full Real Form)**:
For any finite set of points `P` and finite set of 1D affine lines `L` in `ℝ²`:
`∑ ℓ ∈ L, (P.filter (· ∈ ℓ)).card ≤ 4 * P.card^(2/3) * L.card^(2/3) + 4 * P.card + L.card`. -/
theorem ppl071_szemeredi_trotter
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (hL : ∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1) :
    ((∑ ℓ ∈ L, (P.filter (· ∈ ℓ)).card : ℕ) : ℝ) ≤
      4 * (P.card : ℝ) ^ (2 / 3 : ℝ) * (L.card : ℝ) ^ (2 / 3 : ℝ) +
      4 * (P.card : ℝ) + (L.card : ℝ) := by
  let E_cnt := ∑ ℓ ∈ L, ((P.filter (· ∈ ℓ)).card - 1)
  have hI_le : ∑ ℓ ∈ L, (P.filter (· ∈ ℓ)).card ≤ E_cnt + L.card := by
    calc ∑ ℓ ∈ L, (P.filter (· ∈ ℓ)).card
        ≤ ∑ ℓ ∈ L, (((P.filter (· ∈ ℓ)).card - 1) + 1) :=
          Finset.sum_le_sum fun ℓ _ => by omega
      _ = E_cnt + L.card := by rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hI_le_r : ((∑ ℓ ∈ L, (P.filter (· ∈ ℓ)).card : ℕ) : ℝ) ≤ (E_cnt : ℝ) + (L.card : ℝ) := by
    exact_mod_cast hI_le
  rcases szemeredi_trotter_cube P L hL with hlt | hcube
  · have hE_r : (E_cnt : ℝ) ≤ 4 * (P.card : ℝ) := by exact_mod_cast le_of_lt hlt
    have hnonneg : (0 : ℝ) ≤ 4 * (P.card : ℝ) ^ (2 / 3 : ℝ) * (L.card : ℝ) ^ (2 / 3 : ℝ) := by positivity
    linarith
  · have hE_r : (E_cnt : ℝ) ≤ 4 * (P.card : ℝ) ^ (2 / 3 : ℝ) * (L.card : ℝ) ^ (2 / 3 : ℝ) := by
      have hcube_r : (E_cnt : ℝ) ^ 3 ≤ (4 * (P.card : ℝ) ^ (2 / 3 : ℝ) * (L.card : ℝ) ^ (2 / 3 : ℝ)) ^ 3 := by
        have h1 : (E_cnt : ℝ) ^ 3 ≤ 32 * (P.card : ℝ) ^ 2 * (L.card : ℝ) ^ 2 := by exact_mod_cast hcube
        have hp_pow : ((P.card : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (P.card : ℝ) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
          norm_num
        have hl_pow : ((L.card : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (L.card : ℝ) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
          norm_num
        have hrhs : (4 * (P.card : ℝ) ^ (2 / 3 : ℝ) * (L.card : ℝ) ^ (2 / 3 : ℝ)) ^ 3 =
            64 * (P.card : ℝ) ^ 2 * (L.card : ℝ) ^ 2 := by
          rw [mul_pow, mul_pow, hp_pow, hl_pow]; ring
        rw [hrhs]
        nlinarith [sq_nonneg (P.card : ℝ), sq_nonneg (L.card : ℝ)]
      have hnonneg : 0 ≤ 4 * (P.card : ℝ) ^ (2 / 3 : ℝ) * (L.card : ℝ) ^ (2 / 3 : ℝ) := by positivity
      by_contra hgt
      push Not at hgt
      have : (4 * (P.card : ℝ) ^ (2 / 3 : ℝ) * (L.card : ℝ) ^ (2 / 3 : ℝ)) ^ 3 < (E_cnt : ℝ) ^ 3 :=
        pow_lt_pow_left₀ hgt hnonneg (by norm_num)
      linarith
    have h4p : (0 : ℝ) ≤ 4 * (P.card : ℝ) := by positivity
    linarith

/-- **Szemerédi–Trotter `k`-Rich Lines Corollary (Exact Algebraic Form)**:
If every line `ℓ ∈ L` contains at least `k ≥ 2` points of `P`, then
`k ^ 2 * (∑ ℓ ∈ L, |P ∩ ℓ|) ≤ 256 * P.card ^ 2 + 8 * k ^ 2 * P.card`! -/
theorem ppl071_szemeredi_trotter_rich_lines
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (hL : ∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1)
    (k : ℕ) (hk : 2 ≤ k)
    (hrich : ∀ ℓ ∈ L, k ≤ (P.filter (· ∈ ℓ)).card) :
    k ^ 2 * (∑ ℓ ∈ L, (P.filter (· ∈ ℓ)).card) ≤ 256 * P.card ^ 2 + 8 * k ^ 2 * P.card := by
  let I := ∑ ℓ ∈ L, (P.filter (· ∈ ℓ)).card
  let E_cnt := ∑ ℓ ∈ L, ((P.filter (· ∈ ℓ)).card - 1)
  have hI_ge_kL : k * L.card ≤ I := by
    calc k * L.card = ∑ _ℓ ∈ L, k := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ ℓ ∈ L, (P.filter (· ∈ ℓ)).card := Finset.sum_le_sum hrich
  have hI_le_2E : I ≤ 2 * E_cnt := by
    calc I = ∑ ℓ ∈ L, (P.filter (· ∈ ℓ)).card := rfl
      _ ≤ ∑ ℓ ∈ L, 2 * ((P.filter (· ∈ ℓ)).card - 1) :=
          Finset.sum_le_sum fun ℓ hℓ => by have := hrich ℓ hℓ; omega
      _ = 2 * E_cnt := (Finset.mul_sum _ _ _).symm
  rcases szemeredi_trotter_cube P L hL with hlt | hcube
  · have hI_lt : I ≤ 8 * P.card := by omega
    calc k ^ 2 * I ≤ k ^ 2 * (8 * P.card) := Nat.mul_le_mul_left _ hI_lt
      _ = 8 * k ^ 2 * P.card := by ring
      _ ≤ 256 * P.card ^ 2 + 8 * k ^ 2 * P.card := Nat.le_add_left _ _
  · by_cases hI0 : I = 0
    · change k ^ 2 * I ≤ _; rw [hI0]; simp
    have hI_pos : 0 < I := Nat.pos_of_ne_zero hI0
    -- `I^3 ≤ 8 E_cnt^3 ≤ 256 P^2 L^2`, so `k^2 I^3 ≤ 256 P^2 (k L)^2 ≤ 256 P^2 I^2`!
    have hmul : k ^ 2 * I ^ 3 ≤ 256 * P.card ^ 2 * I ^ 2 := by
      have h1 : I ^ 3 ≤ 8 * E_cnt ^ 3 := by
        have := Nat.pow_le_pow_left hI_le_2E 3
        calc I ^ 3 ≤ (2 * E_cnt) ^ 3 := this
          _ = 8 * E_cnt ^ 3 := by ring
      have h2 : (k * L.card) ^ 2 ≤ I ^ 2 := Nat.pow_le_pow_left hI_ge_kL 2
      calc k ^ 2 * I ^ 3
          ≤ k ^ 2 * (8 * E_cnt ^ 3) := Nat.mul_le_mul_left _ h1
        _ ≤ k ^ 2 * (8 * (32 * P.card ^ 2 * L.card ^ 2)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hcube)
        _ = 256 * P.card ^ 2 * (k * L.card) ^ 2 := by ring
        _ ≤ 256 * P.card ^ 2 * I ^ 2 := Nat.mul_le_mul_left _ h2
    have hI2_pos : 0 < I ^ 2 := pow_pos hI_pos 2
    have hcancel : k ^ 2 * I ≤ 256 * P.card ^ 2 := by
      have : (k ^ 2 * I) * I ^ 2 ≤ (256 * P.card ^ 2) * I ^ 2 := by
        calc (k ^ 2 * I) * I ^ 2 = k ^ 2 * I ^ 3 := by ring
          _ ≤ 256 * P.card ^ 2 * I ^ 2 := hmul
      exact Nat.le_of_mul_le_mul_right this hI2_pos
    exact le_trans hcancel (Nat.le_add_right _ _)

/-! ### Part 4: Circle-Arc X-Monotone Builder & Crossing Bound (`W.totalSwaps ≤ C.card ^ 2`) -/

/-- Exact length of `consecPairs ls` is `ls.length - 1`. -/
private lemma consecPairs_length_eq {n : ℕ} (ls : List (Fin n)) :
    (consecPairs ls).length = ls.length - 1 := by
  induction ls with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' => simp only [consecPairs, List.length_cons] at ih ⊢; omega

/-- Helper: given a finite point set `P` and a similarity tilt `t` with injective `x`-coordinates,
produce the `x`-sorted indexing `v : Fin P.card → EuclideanSpace ℝ (Fin 2)` of `tilt t '' P`. -/
private lemma sorted_tilted_points (P : Finset (EuclideanSpace ℝ (Fin 2))) (t : ℝ)
    (htX : Set.InjOn (fun p => (tilt t p) 0) (P : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∃ v : Fin P.card → EuclideanSpace ℝ (Fin 2),
      StrictMono (fun i => v i 0) ∧
      Function.Injective v ∧
      (∀ i, v i ∈ P.image (tilt t)) ∧
      (∀ q ∈ P.image (tilt t), ∃ i, v i = q) := by
  set n := P.card
  let P' := P.image (tilt t)
  have hP'_card : P'.card = n := Finset.card_image_of_injective P (tilt_injective t)
  have hX_inj : Set.InjOn (fun q : EuclideanSpace ℝ (Fin 2) => q 0) (P' : Set _) := by
    intro q₁ hq₁ q₂ hq₂ heq
    obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hq₁
    obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.mp hq₂
    rw [htX hp₁ hp₂ heq]
  let X : Finset ℝ := P'.image (fun q => q 0)
  have hX_card : X.card = n := by rw [Finset.card_image_of_injOn hX_inj, hP'_card]
  let sortedX : List ℝ := X.sort (· ≤ ·)
  have hlenX : sortedX.length = n := by rw [Finset.length_sort, hX_card]
  have hv_ex : ∀ i : Fin n, ∃ q ∈ P', q 0 = sortedX[i.val]'(by omega) := fun i =>
    Finset.mem_image.mp ((Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem (l := sortedX) (n := i.val) (by omega)))
  let v : Fin n → EuclideanSpace ℝ (Fin 2) := fun i => Classical.choose (hv_ex i)
  have hv_mem : ∀ i : Fin n, v i ∈ P' := fun i => (Classical.choose_spec (hv_ex i)).1
  have hv_x : ∀ i : Fin n, v i 0 = sortedX[i.val]'(by omega) := fun i => (Classical.choose_spec (hv_ex i)).2
  have hx : StrictMono (fun i : Fin n => v i 0) := by
    intro i j hij
    dsimp only; rw [hv_x i, hv_x j]
    have hpw : sortedX.Pairwise (· ≤ ·) := Finset.pairwise_sort X (· ≤ ·)
    have hnd : sortedX.Nodup := Finset.sort_nodup X (· ≤ ·)
    have hle : sortedX[i.val]'(by omega) ≤ sortedX[j.val]'(by omega) :=
      List.pairwise_iff_getElem.mp hpw i.val j.val (by omega) (by omega) hij
    have hne : sortedX[i.val]'(by omega) ≠ sortedX[j.val]'(by omega) :=
      List.pairwise_iff_getElem.mp hnd i.val j.val (by omega) (by omega) hij
    exact lt_of_le_of_ne hle hne
  have hv_inj : Function.Injective v := fun i j h => by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact ne_of_lt (hx hij) (by dsimp only; rw [h])
    · exact ne_of_gt (hx hji) (by dsimp only; rw [h])
  have hv_surj : ∀ q ∈ P', ∃ i : Fin n, v i = q := fun q hq => by
    have hmem : q 0 ∈ sortedX := (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_image_of_mem _ hq)
    obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
    refine ⟨⟨k, by omega⟩, hX_inj (hv_mem _) hq ?_⟩
    dsimp only; rw [hv_x]; exact hget
  exact ⟨v, hx, hv_inj, hv_mem, hv_surj⟩

/-- **Circle-Arc X-Monotone Wiring Theorem**:
Given `n` points `v : Fin n → ℝ²` with strictly increasing `x`-coordinates, a finite family of
circles `C` (with `r > 0` and no equator points `v i 1 = c 1` on any circle), and ANY edge-filter
predicate `keep : (ℝ² × ℝ) → Fin n → Fin n → Prop`:
1. Each circle `(c, r) ∈ C` is split into open upper (`y > c 1`) and lower (`y < c 1`) semicircles;
   consecutive points on each semicircle form edges in `E_all`, and `E_keep` keeps those satisfying
   `keep cr i j`.
2. There exists a `WiringDiagram n E_keep` with **`W.totalSwaps ≤ C.card ^ 2`**!
3. Every parallel class `(i, j)` in `E_keep` has cardinality at most
   `(C.filter (fun cr => dist cr.1 (v i) = cr.2 ∧ dist cr.1 (v j) = cr.2 ∧ keep cr i j)).card`!
4. The total number of edges satisfies
   `E_keep.card + E_drop_count + 2 * C.card ≥ ∑ cr ∈ C, |{i : Fin n | dist cr.1 (v i) = cr.2}|`,
   where `E_drop_count` is the sum over `cr ∈ C` and `side ∈ {false, true}` of the number of
   consecutive pairs `(i, j)` on `(cr, side)` with `¬ keep cr i j`! -/
private lemma circles_arc_wiring
    {n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin 2))
    (hx : StrictMono (fun i => v i 0))
    (C : Finset (EuclideanSpace ℝ (Fin 2) × ℝ))
    (hCr : ∀ cr ∈ C, 0 < cr.2)
    (hCy : ∀ cr ∈ C, ∀ i : Fin n, dist cr.1 (v i) = cr.2 → v i 1 ≠ cr.1 1)
    (keep : EuclideanSpace ℝ (Fin 2) × ℝ → Fin n → Fin n → Prop) :
    let sideIdx (cr : EuclideanSpace ℝ (Fin 2) × ℝ) (side : Bool) : List (Fin n) :=
      (Finset.univ.filter (fun i : Fin n =>
        dist cr.1 (v i) = cr.2 ∧ (if side then cr.1 1 < v i 1 else v i 1 < cr.1 1))).sort (· ≤ ·)
    ∃ (E : Finset (MEdge n)) (W : WiringDiagram n E),
      W.totalSwaps ≤ C.card ^ 2 ∧
      (∀ i j : Fin n, (E.filter (fun e => e.l = i ∧ e.r = j)).card ≤
        (C.filter (fun cr => dist cr.1 (v i) = cr.2 ∧ dist cr.1 (v j) = cr.2 ∧ keep cr i j)).card) ∧
      (∑ cr ∈ C, (Finset.univ.filter (fun i : Fin n => dist cr.1 (v i) = cr.2)).card) ≤
        E.card +
        (∑ cr ∈ C, (((consecPairs (sideIdx cr true)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length +
                    ((consecPairs (sideIdx cr false)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length)) +
        2 * C.card := by
  intro sideIdx
  let eC : C ≃ Fin C.card := C.equivFin
  have hside_pw : ∀ cr side, (sideIdx cr side).Pairwise (· < ·) := fun cr side =>
    List.Pairwise.imp_of_mem (fun {a b} _ _ ⟨h1, h2⟩ => lt_of_le_of_ne h1 h2)
      ((Finset.pairwise_sort _ _).and (Finset.sort_nodup _ _))
  -- Build edges for `(k : Fin C.card, side : Bool)` with id `2 * k.val + (if side then 1 else 0)`!
  let edgeId (k : Fin C.card) (side : Bool) : ℕ := 2 * k.val + if side then 1 else 0
  let csEdgesAll (k : Fin C.card) (side : Bool) : Finset (MEdge n) :=
    let cr := (eC.symm k).1
    ((consecPairs (sideIdx cr side)).attach.map
      (fun pq => (⟨edgeId k side, pq.1.1, pq.1.2, consecPairs_lt (hside_pw cr side) pq.2⟩ : MEdge n))).toFinset
  let csEdgesKeep (k : Fin C.card) (side : Bool) : Finset (MEdge n) :=
    (csEdgesAll k side).filter (fun e => keep (eC.symm k).1 e.l e.r)
  have hcsAll_card : ∀ k side,
      (csEdgesAll k side).card = (sideIdx (eC.symm k).1 side).length - 1 := fun k side => by
    let cr := (eC.symm k).1
    have hnd : ((consecPairs (sideIdx cr side)).attach.map
        (fun pq => (⟨edgeId k side, pq.1.1, pq.1.2, consecPairs_lt (hside_pw cr side) pq.2⟩ : MEdge n))).Nodup :=
      (List.nodup_attach.mpr (consecPairs_nodup (hside_pw cr side))).map (fun a b h => by
        cases a; cases b; simp only [MEdge.mk.injEq] at h
        exact Subtype.ext (Prod.ext h.2.1 h.2.2))
    dsimp only [csEdgesAll]
    rw [List.toFinset_card_of_nodup hnd, List.length_map, List.length_attach, consecPairs_length_eq]
  have hcsDrop_card : ∀ k side,
      ((csEdgesAll k side).filter (fun e => ¬ keep (eC.symm k).1 e.l e.r)).card =
        ((consecPairs (sideIdx (eC.symm k).1 side)).filter (fun pq => ¬ keep (eC.symm k).1 pq.1 pq.2)).length := by
    intro k side
    let cr := (eC.symm k).1
    have hnd_filt : ((consecPairs (sideIdx cr side)).filter (fun pq => ¬ keep cr pq.1 pq.2)).Nodup :=
      (consecPairs_nodup (hside_pw cr side)).filter _
    rw [← List.toFinset_card_of_nodup hnd_filt]
    refine Finset.card_bij (fun e _ => (e.l, e.r)) (fun e he => ?_) (fun e₁ h1 e₂ h2 heq => ?_) (fun pq hpq => ?_)
    · simp only [Finset.mem_filter, csEdgesAll, List.mem_toFinset, List.mem_map, List.mem_attach,
        true_and, Subtype.exists] at he
      obtain ⟨⟨pq, hpq, rfl⟩, hnk⟩ := he
      exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hpq, by simpa using hnk⟩)
    · simp only [Finset.mem_filter, csEdgesAll, List.mem_toFinset, List.mem_map, List.mem_attach,
        true_and, Subtype.exists] at h1 h2
      obtain ⟨⟨_, _, rfl⟩, _⟩ := h1; obtain ⟨⟨_, _, rfl⟩, _⟩ := h2
      exact medge_ext rfl (congrArg Prod.fst heq) (congrArg Prod.snd heq)
    · simp only [List.mem_toFinset, List.mem_filter] at hpq
      refine ⟨⟨edgeId k side, pq.1, pq.2, consecPairs_lt (hside_pw cr side) hpq.1⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, csEdgesAll, List.mem_toFinset, List.mem_map, List.mem_attach,
        true_and, Subtype.exists]
      exact ⟨⟨pq, hpq.1, rfl⟩, by simpa using hpq.2⟩
  have hcs_disj : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin C.card × Bool)) : Set (Fin C.card × Bool))
      (fun ks => csEdgesKeep ks.1 ks.2) := by
    rintro ⟨k₁, s₁⟩ _ ⟨k₂, s₂⟩ _ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]; intro e h1 h2
    simp only [csEdgesKeep, Finset.mem_filter, csEdgesAll, List.mem_toFinset, List.mem_map,
      List.mem_attach, true_and, Subtype.exists] at h1 h2
    obtain ⟨⟨_, _, h1eq⟩, _⟩ := h1; obtain ⟨⟨_, _, h2eq⟩, _⟩ := h2
    have hid1 : e.id = edgeId k₁ s₁ := congrArg MEdge.id h1eq.symm
    have hid2 : e.id = edgeId k₂ s₂ := congrArg MEdge.id h2eq.symm
    have heq_id : edgeId k₁ s₁ = edgeId k₂ s₂ := hid1.symm.trans hid2
    dsimp [edgeId] at heq_id
    have hk : k₁ = k₂ := Fin.ext (by cases s₁ <;> cases s₂ <;> simp at heq_id <;> omega)
    have hs : s₁ = s₂ := by cases s₁ <;> cases s₂ <;> simp at heq_id ⊢ <;> omega
    exact hne (Prod.ext hk hs)
  let E : Finset (MEdge n) := (Finset.univ : Finset (Fin C.card × Bool)).biUnion (fun ks => csEdgesKeep ks.1 ks.2)
  -- Helper: recover `(k, side)` and membership in `consecPairs` from `e ∈ E`!
  have he_info : ∀ e ∈ E, ∃ hk : e.id / 2 < C.card,
      let side := decide (e.id % 2 = 1)
      let cr := (eC.symm ⟨e.id / 2, hk⟩).1
      (e.l, e.r) ∈ consecPairs (sideIdx cr side) ∧ keep cr e.l e.r := by
    intro e he
    obtain ⟨⟨k, side⟩, _, hks⟩ := Finset.mem_biUnion.mp he
    simp only [csEdgesKeep, Finset.mem_filter, csEdgesAll, List.mem_toFinset, List.mem_map,
      List.mem_attach, true_and, Subtype.exists] at hks
    obtain ⟨⟨pq, hpq, heq⟩, hkeep⟩ := hks
    have hid : e.id = 2 * k.val + if side then 1 else 0 := congrArg MEdge.id heq.symm
    have hdiv : e.id / 2 = k.val := by cases side <;> simp at hid <;> omega
    have hmod : decide (e.id % 2 = 1) = side := by cases side <;> simp at hid ⊢ <;> omega
    have hk : e.id / 2 < C.card := by rw [hdiv]; exact k.isLt
    refine ⟨hk, ?_⟩
    have hfin : (⟨e.id / 2, hk⟩ : Fin C.card) = k := Fin.ext hdiv
    dsimp only; rw [hfin, hmod]
    have hlr : (e.l, e.r) = pq := by cases heq; rfl
    exact ⟨hlr.symm ▸ hpq, hkeep⟩
  -- Arc function `arc e s = c 1 ± √(r² - (s - c 0)²)`:
  let circleOfId (m : ℕ) : EuclideanSpace ℝ (Fin 2) × ℝ :=
    if hk : m / 2 < C.card then (eC.symm ⟨m / 2, hk⟩).1 else (0, 1)
  let arc (e : MEdge n) (s : ℝ) : ℝ :=
    let cr := circleOfId e.id
    if e.id % 2 = 1 then
      cr.1 1 + Real.sqrt (cr.2 ^ 2 - (s - cr.1 0) ^ 2)
    else
      cr.1 1 - Real.sqrt (cr.2 ^ 2 - (s - cr.1 0) ^ 2)
  -- Key geometric property of `arc e s` for any `e ∈ E` and `s ∈ [v e.l 0, v e.r 0]`:
  have harc_geom : ∀ e ∈ E, ∀ hk : e.id / 2 < C.card,
      let cr := (eC.symm ⟨e.id / 2, hk⟩).1
      ∀ s : ℝ, v e.l 0 ≤ s → s ≤ v e.r 0 →
        0 < cr.2 ^ 2 - (s - cr.1 0) ^ 2 ∧
        dist cr.1 (WithLp.toLp 2 ![s, arc e s]) = cr.2 ∧
        (if e.id % 2 = 1 then cr.1 1 < arc e s else arc e s < cr.1 1) := by
    intro e he hk cr s hsl hsr
    obtain ⟨hk', hpq, _⟩ := he_info e he
    have hm := consecPairs_mem hpq
    have hfl := Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hm.1)
    have hfr := Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hm.2)
    have hr_pos : 0 < cr.2 := hCr cr (eC.symm ⟨e.id / 2, hk⟩).2
    have hsq_l : (v e.l 0 - cr.1 0) ^ 2 + (v e.l 1 - cr.1 1) ^ 2 = cr.2 ^ 2 := by
      rw [← dist_sq_eq_euc2, dist_comm, hfl.2.1]
    have hsq_r : (v e.r 0 - cr.1 0) ^ 2 + (v e.r 1 - cr.1 1) ^ 2 = cr.2 ^ 2 := by
      rw [← dist_sq_eq_euc2, dist_comm, hfr.2.1]
    have hyl_ne : v e.l 1 ≠ cr.1 1 := hCy cr (eC.symm ⟨e.id / 2, hk⟩).2 e.l hfl.2.1
    have hyr_ne : v e.r 1 ≠ cr.1 1 := hCy cr (eC.symm ⟨e.id / 2, hk⟩).2 e.r hfr.2.1
    have hdx_l : (v e.l 0 - cr.1 0) ^ 2 < cr.2 ^ 2 := by
      have : 0 < (v e.l 1 - cr.1 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hyl_ne)
      linarith
    have hdx_r : (v e.r 0 - cr.1 0) ^ 2 < cr.2 ^ 2 := by
      have : 0 < (v e.r 1 - cr.1 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hyr_ne)
      linarith
    have hrad_pos : 0 < cr.2 ^ 2 - (s - cr.1 0) ^ 2 := by
      -- Since `v e.l 0 ≤ s ≤ v e.r 0`, `(s - c 0)² ≤ max((v e.l 0 - c 0)², (v e.r 0 - c 0)²) < r²`!
      have : (s - cr.1 0) ^ 2 ≤ max ((v e.l 0 - cr.1 0) ^ 2) ((v e.r 0 - cr.1 0) ^ 2) := by
        rcases le_total (s - cr.1 0) 0 with hle | hge
        · exact le_trans (by nlinarith) (le_max_left _ _)
        · exact le_trans (by nlinarith) (le_max_right _ _)
      have hmax_lt : max ((v e.l 0 - cr.1 0) ^ 2) ((v e.r 0 - cr.1 0) ^ 2) < cr.2 ^ 2 :=
        max_lt hdx_l hdx_r
      linarith
    have hsqrt_pos : 0 < Real.sqrt (cr.2 ^ 2 - (s - cr.1 0) ^ 2) := Real.sqrt_pos.mpr hrad_pos
    have hco : circleOfId e.id = cr := by dsimp [circleOfId, cr]; rw [dif_pos hk]
    have hdist : dist cr.1 (WithLp.toLp 2 ![s, arc e s]) = cr.2 := by
      have hsq : dist cr.1 (WithLp.toLp 2 ![s, arc e s]) ^ 2 = cr.2 ^ 2 := by
        rw [dist_sq_eq_euc2]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        dsimp only [arc]; rw [hco]
        split_ifs
        · have : (cr.1 1 - (cr.1 1 + Real.sqrt (cr.2 ^ 2 - (s - cr.1 0) ^ 2))) ^ 2 =
              Real.sqrt (cr.2 ^ 2 - (s - cr.1 0) ^ 2) ^ 2 := by ring
          rw [this, Real.sq_sqrt (le_of_lt hrad_pos)]; ring
        · have : (cr.1 1 - (cr.1 1 - Real.sqrt (cr.2 ^ 2 - (s - cr.1 0) ^ 2))) ^ 2 =
              Real.sqrt (cr.2 ^ 2 - (s - cr.1 0) ^ 2) ^ 2 := by ring
          rw [this, Real.sq_sqrt (le_of_lt hrad_pos)]; ring
      have hd0 : 0 ≤ dist cr.1 (WithLp.toLp 2 ![s, arc e s]) := dist_nonneg
      nlinarith
    have hside_strict : if e.id % 2 = 1 then cr.1 1 < arc e s else arc e s < cr.1 1 := by
      dsimp only [arc]; rw [hco]
      split_ifs <;> linarith
    exact ⟨hrad_pos, hdist, hside_strict⟩
  -- Build finite `Crit` from all pairwise intersections of circles with distinct centers!
  let interS (cr₁ cr₂ : EuclideanSpace ℝ (Fin 2) × ℝ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
    if h : cr₁.1 ≠ cr₂.1 then Classical.choose (two_circles_inter_finset cr₁.1 cr₂.1 cr₁.2 cr₂.2 h) else ∅
  have hinterS_spec : ∀ cr₁ cr₂, cr₁.1 ≠ cr₂.1 →
      (interS cr₁ cr₂).card ≤ 2 ∧ ∀ p, dist p cr₁.1 = cr₁.2 → dist p cr₂.1 = cr₂.2 → p ∈ interS cr₁ cr₂ :=
    fun cr₁ cr₂ h => by dsimp [interS]; rw [dif_pos h]; exact Classical.choose_spec (two_circles_inter_finset cr₁.1 cr₂.1 cr₁.2 cr₂.2 h)
  let Crit : Finset ℝ :=
    ((C ×ˢ C).filter (fun p => p.1.1 ≠ p.2.1)).biUnion (fun p => (interS p.1 p.2).image (fun q => q 0))
  -- Endpoint matching helper:
  have harc_ep : ∀ e ∈ E, arc e (v e.l 0) = v e.l 1 ∧ arc e (v e.r 0) = v e.r 1 := by
    intro e he
    obtain ⟨hk, hpq, _⟩ := he_info e he
    let cr := (eC.symm ⟨e.id / 2, hk⟩).1
    have hco : circleOfId e.id = cr := by dsimp [circleOfId, cr]; rw [dif_pos hk]
    have hm := consecPairs_mem hpq
    have hfl := Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hm.1)
    have hfr := Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hm.2)
    have hpt : ∀ i : Fin n, dist cr.1 (v i) = cr.2 →
        (if decide (e.id % 2 = 1) then cr.1 1 < v i 1 else v i 1 < cr.1 1) →
        arc e (v i 0) = v i 1 := by
      intro i hdi hsi
      have hsq : (v i 1 - cr.1 1) ^ 2 = cr.2 ^ 2 - (v i 0 - cr.1 0) ^ 2 := by
        have := dist_sq_eq_euc2 cr.1 (v i); rw [hdi] at this; linarith
      dsimp only [arc]; rw [hco]
      by_cases hmod : e.id % 2 = 1
      · simp only [hmod, decide_true, ↓reduceIte] at hsi ⊢
        rw [← hsq, Real.sqrt_sq (by linarith)]; linarith
      · simp only [hmod, decide_false, Bool.false_eq_true, ↓reduceIte] at hsi ⊢
        have hsq' : (cr.1 1 - v i 1) ^ 2 = cr.2 ^ 2 - (v i 0 - cr.1 0) ^ 2 := by linarith
        rw [← hsq', Real.sqrt_sq (by linarith)]; linarith
    exact ⟨hpt e.l hfl.2.1 hfl.2.2, hpt e.r hfr.2.1 hfr.2.2⟩
  -- Verify `hCrit`:
  have hCrit : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ≠ e₂ → ∀ s : ℝ,
      v e₁.l 0 < s → s < v e₁.r 0 → v e₂.l 0 < s → s < v e₂.r 0 → arc e₁ s = arc e₂ s → s ∈ Crit := by
    intro e₁ he₁ e₂ he₂ hne s h1l h1r h2l h2r heq
    obtain ⟨hk₁, hpq₁, _⟩ := he_info e₁ he₁
    obtain ⟨hk₂, hpq₂, _⟩ := he_info e₂ he₂
    let cr₁ := (eC.symm ⟨e₁.id / 2, hk₁⟩).1
    let cr₂ := (eC.symm ⟨e₂.id / 2, hk₂⟩).1
    have hg₁ := harc_geom e₁ he₁ hk₁ s (le_of_lt h1l) (le_of_lt h1r)
    have hg₂ := harc_geom e₂ he₂ hk₂ s (le_of_lt h2l) (le_of_lt h2r)
    have hdiv_ne : e₁.id / 2 ≠ e₂.id / 2 := by
      intro hdiv
      have hcr_eq : cr₁ = cr₂ := by
        dsimp [cr₁, cr₂]; congr 1; exact congrArg eC.symm (Fin.ext hdiv)
      by_cases hmod : e₁.id % 2 = e₂.id % 2
      · have hid_eq : e₁.id = e₂.id := by omega
        have hpq2' : (e₂.l, e₂.r) ∈ consecPairs (sideIdx cr₁ (decide (e₁.id % 2 = 1))) := by
          simpa [cr₁, cr₂, hcr_eq, hmod] using hpq₂
        have hpq_ne : (e₁.l, e₁.r) ≠ (e₂.l, e₂.r) := fun h => hne
          (medge_ext hid_eq (congrArg Prod.fst h) (congrArg Prod.snd h))
        rcases consecPairs_disjoint_open (hside_pw cr₁ _) hpq₁ hpq2' hpq_ne with hle | hle
        · have := hx.monotone hle; linarith
        · have := hx.monotone hle; linarith
      · have h1s : if e₁.id % 2 = 1 then cr₁.1 1 < arc e₁ s else arc e₁ s < cr₁.1 1 := hg₁.2.2
        have h2s : if e₂.id % 2 = 1 then cr₂.1 1 < arc e₂ s else arc e₂ s < cr₂.1 1 := hg₂.2.2
        rw [← hcr_eq, ← heq] at h2s
        by_cases hm1 : e₁.id % 2 = 1
        · have hm2 : e₂.id % 2 ≠ 1 := by omega
          simp only [hm1, ↓reduceIte] at h1s; simp only [hm2, ↓reduceIte] at h2s; linarith
        · have hm2 : e₂.id % 2 = 1 := by omega
          simp only [hm1, ↓reduceIte] at h1s; simp only [hm2, ↓reduceIte] at h2s; linarith
    have hcr_ne : cr₁ ≠ cr₂ := fun h => hdiv_ne (congrArg Fin.val (eC.symm.injective (Subtype.ext h)))
    let pt : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![s, arc e₁ s]
    have hd1 : dist pt cr₁.1 = cr₁.2 := by rw [dist_comm]; exact hg₁.2.1
    have hd2 : dist pt cr₂.1 = cr₂.2 := by rw [dist_comm]; dsimp [pt]; rw [heq]; exact hg₂.2.1
    have hc_ne : cr₁.1 ≠ cr₂.1 := fun hc => hcr_ne (Prod.ext hc (by rw [← hd1, ← hd2, hc]))
    have hpt_in : pt ∈ interS cr₁ cr₂ := (hinterS_spec cr₁ cr₂ hc_ne).2 pt hd1 hd2
    have hmemC : (cr₁, cr₂) ∈ (C ×ˢ C).filter (fun p => p.1.1 ≠ p.2.1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(eC.symm ⟨e₁.id / 2, hk₁⟩).2, (eC.symm ⟨e₂.id / 2, hk₂⟩).2⟩, hc_ne⟩
    refine Finset.mem_biUnion.mpr ⟨(cr₁, cr₂), hmemC, Finset.mem_image.mpr ⟨pt, hpt_in, by simp [pt]⟩⟩
  -- Invoke `xmonotone_to_wiring`!
  obtain ⟨W, hW_swaps⟩ := xmonotone_to_wiring (n := n) (fun i => v i 0) (fun i => v i 1) hx E arc
    (fun e _ => by
      dsimp only [arc]
      split_ifs
      · exact (continuous_const.add (Real.continuous_sqrt.comp
          (continuous_const.sub ((continuous_id.sub continuous_const).pow 2)))).continuousOn
      · exact (continuous_const.sub (Real.continuous_sqrt.comp
          (continuous_const.sub ((continuous_id.sub continuous_const).pow 2)))).continuousOn)
    (fun e he => (harc_ep e he).1)
    (fun e he => (harc_ep e he).2)
    (fun e he i hli hir hEq => by
      obtain ⟨hk, hpq, _⟩ := he_info e he
      let cr := (eC.symm ⟨e.id / 2, hk⟩).1
      have hg := harc_geom e he hk (v i 0) (le_of_lt (hx hli)) (le_of_lt (hx hir))
      have hvi_eq : WithLp.toLp 2 ![v i 0, arc e (v i 0)] = v i := by
        apply euc2_ext <;> simp [hEq]
      have hdi : dist cr.1 (v i) = cr.2 := by rw [← hvi_eq]; exact hg.2.1
      have hsi : if decide (e.id % 2 = 1) then cr.1 1 < v i 1 else v i 1 < cr.1 1 := by
        have := hg.2.2; rw [hEq] at this
        by_cases hm : e.id % 2 = 1 <;> simp [hm] at this ⊢ <;> exact this
      have hi_mem : i ∈ sideIdx cr (decide (e.id % 2 = 1)) :=
        (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdi, hsi⟩)
      exact consecPairs_no_between (hside_pw cr _) hpq hi_mem ⟨hli, hir⟩)
    Crit hCrit
  -- Bound `∑ c ∈ Crit, crossAt c ≤ 2 * C.card ^ 2` by injecting `Cross` into `Σ p, interS p.1 p.2`!
  have hW_bound : W.totalSwaps ≤ C.card ^ 2 := by
    let Cross := Crit.sigma (fun c =>
      (E ×ˢ E).filter (fun p => p.1 ≠ p.2 ∧
        v p.1.l 0 < c ∧ c < v p.1.r 0 ∧ v p.2.l 0 < c ∧ c < v p.2.r 0 ∧
        arc p.1 c = arc p.2 c))
    let Target := ((C ×ˢ C).filter (fun p => p.1.1 ≠ p.2.1)).sigma (fun p => interS p.1 p.2)
    let φ : (Σ _ : ℝ, MEdge n × MEdge n) →
        (Σ _ : (EuclideanSpace ℝ (Fin 2) × ℝ) × (EuclideanSpace ℝ (Fin 2) × ℝ), EuclideanSpace ℝ (Fin 2)) :=
      fun q => ⟨(circleOfId q.2.1.id, circleOfId q.2.2.id), WithLp.toLp 2 ![q.1, arc q.2.1 q.1]⟩
    have hmaps : ∀ q ∈ Cross, φ q ∈ Target := by
      intro q hq
      simp only [Cross, Finset.mem_sigma, Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨hk₁, hpq₁, _⟩ := he_info q.2.1 hq.2.1.1
      obtain ⟨hk₂, hpq₂, _⟩ := he_info q.2.2 hq.2.1.2
      let cr₁ := (eC.symm ⟨q.2.1.id / 2, hk₁⟩).1
      let cr₂ := (eC.symm ⟨q.2.2.id / 2, hk₂⟩).1
      have hco1 : circleOfId q.2.1.id = cr₁ := by dsimp [circleOfId, cr₁]; rw [dif_pos hk₁]
      have hco2 : circleOfId q.2.2.id = cr₂ := by dsimp [circleOfId, cr₂]; rw [dif_pos hk₂]
      have hg₁ := harc_geom q.2.1 hq.2.1.1 hk₁ q.1 (le_of_lt hq.2.2.2.1) (le_of_lt hq.2.2.2.2.1)
      have hg₂ := harc_geom q.2.2 hq.2.1.2 hk₂ q.1 (le_of_lt hq.2.2.2.2.2.1) (le_of_lt hq.2.2.2.2.2.2.1)
      have hdiv_ne : q.2.1.id / 2 ≠ q.2.2.id / 2 := by
        intro hdiv
        have hcr_eq : cr₁ = cr₂ := by dsimp [cr₁, cr₂]; congr 1; exact congrArg eC.symm (Fin.ext hdiv)
        by_cases hmod : q.2.1.id % 2 = q.2.2.id % 2
        · have hid_eq : q.2.1.id = q.2.2.id := by omega
          have hpq2' : (q.2.2.l, q.2.2.r) ∈ consecPairs (sideIdx cr₁ (decide (q.2.1.id % 2 = 1))) := by
            simpa [cr₁, cr₂, hcr_eq, hmod] using hpq₂
          have hpq_ne : (q.2.1.l, q.2.1.r) ≠ (q.2.2.l, q.2.2.r) := fun h => hq.2.2.1
            (medge_ext hid_eq (congrArg Prod.fst h) (congrArg Prod.snd h))
          rcases consecPairs_disjoint_open (hside_pw cr₁ _) hpq₁ hpq2' hpq_ne with hle | hle
          · have := hx.monotone hle; linarith [hq.2.2.2.2.1, hq.2.2.2.2.2.1]
          · have := hx.monotone hle; linarith [hq.2.2.2.1, hq.2.2.2.2.2.2.1]
        · have h1s : if q.2.1.id % 2 = 1 then cr₁.1 1 < arc q.2.1 q.1 else arc q.2.1 q.1 < cr₁.1 1 := hg₁.2.2
          have h2s : if q.2.2.id % 2 = 1 then cr₂.1 1 < arc q.2.2 q.1 else arc q.2.2 q.1 < cr₂.1 1 := hg₂.2.2
          rw [← hcr_eq, ← hq.2.2.2.2.2.2.2] at h2s
          by_cases hm1 : q.2.1.id % 2 = 1
          · have hm2 : q.2.2.id % 2 ≠ 1 := by omega
            simp only [hm1, ↓reduceIte] at h1s; simp only [hm2, ↓reduceIte] at h2s; linarith
          · have hm2 : q.2.2.id % 2 = 1 := by omega
            simp only [hm1, ↓reduceIte] at h1s; simp only [hm2, ↓reduceIte] at h2s; linarith
      have hcr_ne : cr₁ ≠ cr₂ := fun h => hdiv_ne (congrArg Fin.val (eC.symm.injective (Subtype.ext h)))
      let pt : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![q.1, arc q.2.1 q.1]
      have hd1 : dist pt cr₁.1 = cr₁.2 := by rw [dist_comm]; exact hg₁.2.1
      have hd2 : dist pt cr₂.1 = cr₂.2 := by rw [dist_comm]; dsimp [pt]; rw [hq.2.2.2.2.2.2.2]; exact hg₂.2.1
      have hc_ne : cr₁.1 ≠ cr₂.1 := fun hc => hcr_ne (Prod.ext hc (by rw [← hd1, ← hd2, hc]))
      simp only [Target, φ, Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, hco1, hco2]
      exact ⟨⟨⟨(eC.symm ⟨q.2.1.id / 2, hk₁⟩).2, (eC.symm ⟨q.2.2.id / 2, hk₂⟩).2⟩, hc_ne⟩,
        (hinterS_spec cr₁ cr₂ hc_ne).2 pt hd1 hd2⟩
    have hinj : Set.InjOn φ (Cross : Set _) := by
      intro q₁ hq₁ q₂ hq₂ heq
      simp only [Cross, Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Finset.mem_product] at hq₁ hq₂
      have hfst := congrArg Sigma.fst heq
      have hsnd : WithLp.toLp 2 ![q₁.1, arc q₁.2.1 q₁.1] = WithLp.toLp 2 ![q₂.1, arc q₂.2.1 q₂.1] :=
        eq_of_heq (Sigma.ext_iff.mp heq).2
      have hc_eq : q₁.1 = q₂.1 := by
        have := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hsnd; simpa using this
      have hy_eq : arc q₁.2.1 q₁.1 = arc q₂.2.1 q₂.1 := by
        have := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) hsnd; simpa using this
      -- Helper: same circle + same `(x, y)` on open interior uniquely determines the edge `e`!
      have huniq_edge : ∀ e₁ ∈ E, ∀ e₂ ∈ E,
          circleOfId e₁.id = circleOfId e₂.id →
          v e₁.l 0 < q₁.1 → q₁.1 < v e₁.r 0 →
          v e₂.l 0 < q₁.1 → q₁.1 < v e₂.r 0 →
          arc e₁ q₁.1 = arc e₂ q₁.1 → e₁ = e₂ := by
        intro e₁ he₁ e₂ he₂ hco_eq h1l h1r h2l h2r ha_eq
        obtain ⟨hk₁, hpq₁, _⟩ := he_info e₁ he₁
        obtain ⟨hk₂, hpq₂, _⟩ := he_info e₂ he₂
        have hco1 : circleOfId e₁.id = (eC.symm ⟨e₁.id / 2, hk₁⟩).1 := by dsimp [circleOfId]; rw [dif_pos hk₁]
        have hco2 : circleOfId e₂.id = (eC.symm ⟨e₂.id / 2, hk₂⟩).1 := by dsimp [circleOfId]; rw [dif_pos hk₂]
        have hcr_eq : (eC.symm ⟨e₁.id / 2, hk₁⟩).1 = (eC.symm ⟨e₂.id / 2, hk₂⟩).1 := hco1.symm.trans (hco_eq.trans hco2)
        have hdiv_eq : e₁.id / 2 = e₂.id / 2 := congrArg Fin.val (eC.symm.injective (Subtype.ext hcr_eq))
        have hg₁ := harc_geom e₁ he₁ hk₁ q₁.1 (le_of_lt h1l) (le_of_lt h1r)
        have hg₂ := harc_geom e₂ he₂ hk₂ q₁.1 (le_of_lt h2l) (le_of_lt h2r)
        have hmod_eq : e₁.id % 2 = e₂.id % 2 := by
          have h1s := hg₁.2.2; have h2s := hg₂.2.2
          rw [← hcr_eq, ← ha_eq] at h2s
          by_cases hm1 : e₁.id % 2 = 1 <;> by_cases hm2 : e₂.id % 2 = 1
          · omega
          · simp only [hm1, ↓reduceIte] at h1s; simp only [hm2, ↓reduceIte] at h2s; linarith
          · simp only [hm1, ↓reduceIte] at h1s; simp only [hm2, ↓reduceIte] at h2s; linarith
          · omega
        have hid_eq : e₁.id = e₂.id := by omega
        by_contra hne
        have hpq2' : (e₂.l, e₂.r) ∈ consecPairs (sideIdx (eC.symm ⟨e₁.id / 2, hk₁⟩).1 (decide (e₁.id % 2 = 1))) := by
          simpa [hcr_eq, hmod_eq] using hpq₂
        have hpq_ne : (e₁.l, e₁.r) ≠ (e₂.l, e₂.r) := fun h => hne
          (medge_ext hid_eq (congrArg Prod.fst h) (congrArg Prod.snd h))
        rcases consecPairs_disjoint_open (hside_pw _ _) hpq₁ hpq2' hpq_ne with hle | hle
        · have := hx.monotone hle; linarith
        · have := hx.monotone hle; linarith
      have he1_eq : q₁.2.1 = q₂.2.1 :=
        huniq_edge q₁.2.1 hq₁.2.1.1 q₂.2.1 hq₂.2.1.1 (congrArg Prod.fst hfst)
          hq₁.2.2.2.1 hq₁.2.2.2.2.1 (hc_eq ▸ hq₂.2.2.2.1) (hc_eq ▸ hq₂.2.2.2.2.1) (hc_eq ▸ hy_eq)
      have he2_eq : q₁.2.2 = q₂.2.2 :=
        huniq_edge q₁.2.2 hq₁.2.1.2 q₂.2.2 hq₂.2.1.2 (congrArg Prod.snd hfst)
          hq₁.2.2.2.2.2.1 hq₁.2.2.2.2.2.2.1 (hc_eq ▸ hq₂.2.2.2.2.2.1) (hc_eq ▸ hq₂.2.2.2.2.2.2.1)
          (by rw [← hq₁.2.2.2.2.2.2.2, hy_eq, hc_eq, hq₂.2.2.2.2.2.2.2])
      cases q₁; cases q₂; simp only at hc_eq he1_eq he2_eq
      subst hc_eq; congr 1; exact Prod.ext he1_eq he2_eq
    have hTarget_ub : Target.card ≤ 2 * C.card ^ 2 := by
      rw [Finset.card_sigma]
      calc ∑ p ∈ (C ×ˢ C).filter (fun p => p.1.1 ≠ p.2.1), (interS p.1 p.2).card
          ≤ ∑ _p ∈ (C ×ˢ C).filter (fun p => p.1.1 ≠ p.2.1), 2 :=
            Finset.sum_le_sum fun p hp => (hinterS_spec p.1 p.2 (Finset.mem_filter.mp hp).2).1
        _ ≤ ∑ _p ∈ C ×ˢ C, 2 := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = 2 * C.card ^ 2 := by rw [Finset.sum_const, Finset.card_product, smul_eq_mul]; ring
    have hCross_le : Cross.card ≤ Target.card := by
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card (fun y hy => by
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy; exact hmaps q hq)
    have hsum_eq : (∑ c ∈ Crit, ((E ×ˢ E).filter (fun p => p.1 ≠ p.2 ∧
        v p.1.l 0 < c ∧ c < v p.1.r 0 ∧ v p.2.l 0 < c ∧ c < v p.2.r 0 ∧
        arc p.1 c = arc p.2 c)).card) = Cross.card := (Finset.card_sigma _ _).symm
    omega
  -- Multiplicity bound: map each `e ∈ E` with `(e.l, e.r) = (i, j)` injectively to `circleOfId e.id`!
  have hmult : ∀ i j : Fin n, (E.filter (fun e => e.l = i ∧ e.r = j)).card ≤
      (C.filter (fun cr => dist cr.1 (v i) = cr.2 ∧ dist cr.1 (v j) = cr.2 ∧ keep cr i j)).card := by
    intro i j
    have hinj_c : Set.InjOn (fun e : MEdge n => circleOfId e.id)
        ((E.filter (fun e => e.l = i ∧ e.r = j)) : Set (MEdge n)) := by
      intro e₁ h1 e₂ h2 hco_eq
      simp only [Finset.mem_coe, Finset.mem_filter] at h1 h2
      obtain ⟨hk₁, hpq₁, _⟩ := he_info e₁ h1.1
      obtain ⟨hk₂, hpq₂, _⟩ := he_info e₂ h2.1
      have hco1 : circleOfId e₁.id = (eC.symm ⟨e₁.id / 2, hk₁⟩).1 := by dsimp [circleOfId]; rw [dif_pos hk₁]
      have hco2 : circleOfId e₂.id = (eC.symm ⟨e₂.id / 2, hk₂⟩).1 := by dsimp [circleOfId]; rw [dif_pos hk₂]
      have hcr_eq : (eC.symm ⟨e₁.id / 2, hk₁⟩).1 = (eC.symm ⟨e₂.id / 2, hk₂⟩).1 := hco1.symm.trans (hco_eq.trans hco2)
      have hdiv_eq : e₁.id / 2 = e₂.id / 2 := congrArg Fin.val (eC.symm.injective (Subtype.ext hcr_eq))
      have hm1 := Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp (consecPairs_mem hpq₁).1)
      have hm2 := Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp (consecPairs_mem hpq₂).1)
      have hmod_eq : e₁.id % 2 = e₂.id % 2 := by
        have h1s := hm1.2.2; have h2s := hm2.2.2
        rw [h1.2.1] at h1s; rw [h2.2.1, ← hcr_eq] at h2s
        by_cases ha : e₁.id % 2 = 1 <;> by_cases hb : e₂.id % 2 = 1
        · omega
        · simp [ha] at h1s; simp [hb] at h2s; linarith
        · simp [ha] at h1s; simp [hb] at h2s; linarith
        · omega
      exact medge_ext (by omega) (h1.2.1.trans h2.2.1.symm) (h1.2.2.trans h2.2.2.symm)
    rw [← Finset.card_image_of_injOn hinj_c]
    refine Finset.card_le_card fun cr hcr => ?_
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hcr
    simp only [Finset.mem_filter] at he ⊢
    obtain ⟨hk, hpq, hkeep⟩ := he_info e he.1
    have hco : circleOfId e.id = (eC.symm ⟨e.id / 2, hk⟩).1 := by dsimp [circleOfId]; rw [dif_pos hk]
    rw [hco]
    have hm := consecPairs_mem hpq
    have hfl := Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hm.1)
    have hfr := Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hm.2)
    exact ⟨(eC.symm ⟨e.id / 2, hk⟩).2, he.2.1 ▸ hfl.2.1, he.2.2 ▸ hfr.2.1, he.2.1 ▸ he.2.2 ▸ hkeep⟩
  -- Edge-count identity:
  have hcount : (∑ cr ∈ C, (Finset.univ.filter (fun i : Fin n => dist cr.1 (v i) = cr.2)).card) ≤
      E.card +
      (∑ cr ∈ C, (((consecPairs (sideIdx cr true)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length +
                  ((consecPairs (sideIdx cr false)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length)) +
      2 * C.card := by
    have hE_sum : E.card = ∑ k : Fin C.card, ((csEdgesKeep k true).card + (csEdgesKeep k false).card) := by
      rw [Finset.card_biUnion hcs_disj, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fintype.sum_bool]
    have hper_k : ∀ k : Fin C.card,
        let cr := (eC.symm k).1
        (Finset.univ.filter (fun i : Fin n => dist cr.1 (v i) = cr.2)).card ≤
          ((csEdgesKeep k true).card + (csEdgesKeep k false).card) +
          (((consecPairs (sideIdx cr true)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length +
           ((consecPairs (sideIdx cr false)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length) + 2 := by
      intro k cr
      have hpart : (Finset.univ.filter (fun i : Fin n => dist cr.1 (v i) = cr.2)).card =
          (sideIdx cr true).length + (sideIdx cr false).length := by
        simp only [sideIdx, Finset.length_sort]
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
            Bool.false_eq_true, ↓reduceIte]
          constructor
          · intro hd
            have hne := hCy cr (eC.symm k).2 i hd
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact Or.inr ⟨hd, hlt⟩
            · exact Or.inl ⟨hd, hgt⟩
          · rintro (⟨hd, _⟩ | ⟨hd, _⟩) <;> exact hd
        · rw [Finset.disjoint_left]; intro i h1 h2
          simp only [Finset.mem_filter, Bool.false_eq_true, ↓reduceIte] at h1 h2; linarith
      have hsplit : ∀ side : Bool, (csEdgesKeep k side).card +
          ((csEdgesAll k side).filter (fun e => ¬ keep cr e.l e.r)).card = (csEdgesAll k side).card := by
        intro side
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext e; simp only [csEdgesKeep, Finset.mem_union, Finset.mem_filter]
          tauto
        · rw [Finset.disjoint_left]; intro e h1 h2
          simp only [csEdgesKeep, Finset.mem_filter] at h1 h2; exact h2.2 h1.2
      have hsplitT := hsplit true
      have hsplitF := hsplit false
      have hT1 := hcsAll_card k true
      have hF1 := hcsAll_card k false
      have hT2 := hcsDrop_card k true
      have hF2 := hcsDrop_card k false
      dsimp only [cr] at hpart hsplitT hsplitF ⊢
      omega
    have hsum_k : ∑ k : Fin C.card, (Finset.univ.filter (fun i : Fin n => dist (eC.symm k).1.1 (v i) = (eC.symm k).1.2)).card ≤
        E.card +
        (∑ k : Fin C.card, (((consecPairs (sideIdx (eC.symm k).1 true)).filter (fun pq => ¬ keep (eC.symm k).1 pq.1 pq.2)).length +
                            ((consecPairs (sideIdx (eC.symm k).1 false)).filter (fun pq => ¬ keep (eC.symm k).1 pq.1 pq.2)).length)) +
        2 * C.card := by
      have h1 := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hper_k k
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
      rw [hE_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
      omega
    have hbij1 : (∑ cr ∈ C, (Finset.univ.filter (fun i : Fin n => dist cr.1 (v i) = cr.2)).card) =
        ∑ k : Fin C.card, (Finset.univ.filter (fun i : Fin n => dist (eC.symm k).1.1 (v i) = (eC.symm k).1.2)).card :=
      (Finset.sum_bij (fun k _ => (eC.symm k).1) (fun k _ => (eC.symm k).2)
        (fun _ _ _ _ h => eC.symm.injective (Subtype.ext h))
        (fun cr hcr => ⟨eC ⟨cr, hcr⟩, Finset.mem_univ _, by simp⟩) (fun _ _ => rfl)).symm
    have hbij2 : (∑ cr ∈ C, (((consecPairs (sideIdx cr true)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length +
                             ((consecPairs (sideIdx cr false)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length)) =
        ∑ k : Fin C.card, (((consecPairs (sideIdx (eC.symm k).1 true)).filter (fun pq => ¬ keep (eC.symm k).1 pq.1 pq.2)).length +
                           ((consecPairs (sideIdx (eC.symm k).1 false)).filter (fun pq => ¬ keep (eC.symm k).1 pq.1 pq.2)).length) :=
      (Finset.sum_bij (fun k _ => (eC.symm k).1) (fun k _ => (eC.symm k).2)
        (fun _ _ _ _ h => eC.symm.injective (Subtype.ext h))
        (fun cr hcr => ⟨eC ⟨cr, hcr⟩, Finset.mem_univ _, by simp⟩) (fun _ _ => rfl)).symm
    rw [hbij1, hbij2]; exact hsum_k
  exact ⟨E, W, hW_bound, hmult, hcount⟩

/-! ### Part 5: Spencer–Szemerédi–Trotter (1984) `O(n^{4/3})` Unit Distance Upper Bound -/

/-- **Spencer–Szemerédi–Trotter (1984) Unit Distance Upper Bound (Pure-Mathlib Public Theorem)**:
For every finite point set `P ⊂ ℝ²`, the number of ordered pairs `(p, q) ∈ P × P` at Euclidean
distance `1` satisfies `|{(p, q) ∈ P × P : dist p q = 1}| ≤ 16 * |P|^{4/3}`! -/
theorem ppl071_unit_distances_upper (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    (((P ×ˢ P).filter (fun pq => dist pq.1 pq.2 = 1)).card : ℝ) ≤
      16 * (P.card : ℝ) ^ (4 / 3 : ℝ) := by
  set U := ((P ×ˢ P).filter (fun pq => dist pq.1 pq.2 = 1)).card
  set n := P.card
  by_cases hn0 : n = 0
  · have hP0 : P = ∅ := Finset.card_eq_zero.mp hn0
    simp [U, n, hP0]
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  -- Apply generic similarity tilt `t` so both `x`- and `y`-coordinates are strictly injective!
  obtain ⟨t, htX, htY⟩ := exists_tilt_xy_inj P
  obtain ⟨v, hx, hv_inj, hv_mem, hv_surj⟩ := sorted_tilted_points P t htX
  let P' := P.image (tilt t)
  have hP'_card : P'.card = n := Finset.card_image_of_injective P (tilt_injective t)
  let R : ℝ := Real.sqrt (1 + t ^ 2)
  have hR_pos : 0 < R := Real.sqrt_pos.mpr (by positivity)
  -- `U` equals the number of ordered pairs in `P'` at distance `R`!
  have hU_eq : U = ∑ c ∈ P', (Finset.univ.filter (fun i : Fin n => dist c (v i) = R)).card := by
    have h1 : U = ((P' ×ˢ P').filter (fun pq => dist pq.1 pq.2 = R)).card := by
      refine Finset.card_bij (fun pq _ => (tilt t pq.1, tilt t pq.2)) (fun pq hpq => ?_)
        (fun a _ b _ h => Prod.ext (tilt_injective t (congrArg Prod.fst h)) (tilt_injective t (congrArg Prod.snd h)))
        (fun pq hpq => ?_)
      · simp only [Finset.mem_filter, Finset.mem_product] at hpq ⊢
        refine ⟨⟨Finset.mem_image_of_mem _ hpq.1.1, Finset.mem_image_of_mem _ hpq.1.2⟩, ?_⟩
        rw [dist_tilt, hpq.2, mul_one]
      · simp only [Finset.mem_filter, Finset.mem_product, P', Finset.mem_image] at hpq
        obtain ⟨⟨⟨p, hp, hp_eq⟩, ⟨q, hq, hq_eq⟩⟩, hd⟩ := hpq
        refine ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩, Prod.ext hp_eq hq_eq⟩
        rw [← hp_eq, ← hq_eq, dist_tilt] at hd
        have : R * dist p q = R * 1 := by simpa [R] using hd
        exact mul_left_cancel₀ (ne_of_gt hR_pos) this
    rw [h1, Finset.card_eq_sum_ones]
    have hsum_P' : ∑ _x ∈ (P' ×ˢ P').filter (fun pq => dist pq.1 pq.2 = R), 1 =
        ∑ c ∈ P', (P'.filter (fun q => dist c q = R)).card := by
      rw [Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.card_filter]
    rw [hsum_P']
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.card_bij (fun q _ => Classical.choose (hv_surj q (Finset.mem_filter.mp ‹_›).1))
      (fun q hq => ?_) (fun q₁ h1 q₂ h2 h => ?_) (fun i hi => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [Classical.choose_spec (hv_surj q hq.1)]; exact hq.2
    · simp only [Finset.mem_filter] at h1 h2
      have hq1 := Classical.choose_spec (hv_surj q₁ h1.1)
      have hq2 := Classical.choose_spec (hv_surj q₂ h2.1)
      rw [← hq1, ← hq2, h]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine ⟨v i, Finset.mem_filter.mpr ⟨hv_mem i, hi⟩, ?_⟩
      exact hv_inj (Classical.choose_spec (hv_surj (v i) (hv_mem i)))
  -- Apply `circles_arc_wiring` to the `n` circles of radius `R` centered at `P'`!
  let C : Finset (EuclideanSpace ℝ (Fin 2) × ℝ) := P'.image (fun c => (c, R))
  have hC_card : C.card = n := by
    rw [Finset.card_image_of_injOn (fun _ _ _ _ h => congrArg Prod.fst h), hP'_card]
  have hCy : ∀ cr ∈ C, ∀ i : Fin n, dist cr.1 (v i) = cr.2 → v i 1 ≠ cr.1 1 := by
    intro cr hcr i hd heq
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hcr
    obtain ⟨p₁, hp₁, h1⟩ := Finset.mem_image.mp (hv_mem i)
    obtain ⟨p₂, hp₂, h2⟩ := Finset.mem_image.mp hc
    have hpeq : p₁ = p₂ := htY hp₁ hp₂ (by dsimp only; rw [h1, h2]; exact heq)
    have hveq : v i = c := by rw [← h1, ← h2, hpeq]
    rw [hveq, dist_self] at hd; linarith
  obtain ⟨E, W, hW, hmult, hcount⟩ := circles_arc_wiring v hx C
    (fun cr hcr => by obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hcr; exact hR_pos)
    hCy (fun _ _ _ => True)
  -- Drop count is `0` since `keep = True`, and sum over `C` equals `U`!
  have hU_le : U ≤ E.card + 2 * n := by
    have hsumC : (∑ cr ∈ C, (Finset.univ.filter (fun i : Fin n => dist cr.1 (v i) = cr.2)).card) = U := by
      rw [hU_eq]
      exact Finset.sum_image (fun _ _ _ _ h => congrArg Prod.fst h)
    rw [hsumC, hC_card] at hcount
    refine le_trans hcount ?_
    refine Nat.add_le_add_right ?_ (2 * n)
    have hzero : ∀ (p : Fin #P × Fin #P → Bool) (L : List (Fin #P × Fin #P)),
        (∀ a, p a ≠ true) → (L.filter p).length = 0 := by
      intro p L hp
      induction L with
      | nil => rfl
      | cons a t ih =>
        have hpa : p a = false := Bool.eq_false_iff.mpr (hp a)
        simp [hpa, ih]
    have hdec : ∀ (d : Decidable (¬True)), @decide (¬True) d ≠ true := fun d => by
      cases d with
      | isTrue h => exact (h trivial).elim
      | isFalse _ => exact Bool.false_ne_true
    have hadd : ∀ (a b : ℕ), b = 0 → a + b ≤ a := fun a b hb => by omega
    refine hadd E.card _ (Finset.sum_eq_zero fun cr _ => ?_)
    refine Nat.add_eq_zero_iff.mpr ⟨hzero _ _ ?_, hzero _ _ ?_⟩ <;>
      · intro _; exact hdec _
  -- Multiplicity bound `m = 2`: any two distinct points `v i ≠ v j` lie on at most 2 circles of radius `R`!
  have hmult2 : ∀ i j : Fin n, (E.filter (fun e => e.l = i ∧ e.r = j)).card ≤ 2 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have hemp : E.filter (fun e => e.l = i ∧ e.r = i) = ∅ := by
        ext e; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro _ h1 h2; exact ne_of_lt e.hlr (h1.trans h2.symm)
      rw [hemp, Finset.card_empty]; omega
    have hvne : v i ≠ v j := fun h => hij (hv_inj h)
    obtain ⟨S, hS_card, hS_mem⟩ := two_circles_inter_finset (v i) (v j) R R hvne
    refine le_trans (hmult i j) (le_trans ?_ hS_card)
    refine Finset.card_le_card_of_injOn Prod.fst (fun cr hcr => ?_) (fun a ha b hb hfst => ?_)
    · simp only [Finset.mem_coe, Finset.mem_filter] at hcr
      obtain ⟨_, _, hcreq⟩ := Finset.mem_image.mp hcr.1
      have hr2 : cr.2 = R := by rw [← hcreq]
      exact hS_mem cr.1 (hr2 ▸ hcr.2.1) (hr2 ▸ hcr.2.2.1)
    · simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
      obtain ⟨_, _, haeq⟩ := Finset.mem_image.mp ha.1
      obtain ⟨_, _, hbeq⟩ := Finset.mem_image.mp hb.1
      have ha2 : a.2 = R := by rw [← haeq]
      have hb2 : b.2 = R := by rw [← hbeq]
      exact Prod.ext hfst (ha2.trans hb2.symm)
  -- Apply `wiring_multigraph_crossing_lemma` (`m = 2`)!
  have hn_le_rpow : (n : ℝ) ≤ (n : ℝ) ^ (4 / 3 : ℝ) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  by_cases hdense : 4 * 2 * n ≤ E.card
  · have hcl := wiring_multigraph_crossing_lemma (n := n) (E := E) (m := 2) W (by omega) hmult2 hdense
    have hW_n : W.totalSwaps ≤ n ^ 2 := by rw [← hC_card]; exact hW
    have hE3 : E.card ^ 3 ≤ 128 * n ^ 4 := by
      calc E.card ^ 3 ≤ 64 * 2 * n ^ 2 * W.totalSwaps := hcl
        _ ≤ 64 * 2 * n ^ 2 * n ^ 2 := Nat.mul_le_mul_left _ hW_n
        _ = 128 * n ^ 4 := by ring
    have hE_le : (E.card : ℝ) ≤ 6 * (n : ℝ) ^ (4 / 3 : ℝ) := by
      have hE3_r : (E.card : ℝ) ^ 3 ≤ (6 * (n : ℝ) ^ (4 / 3 : ℝ)) ^ 3 := by
        have h1 : (E.card : ℝ) ^ 3 ≤ 128 * (n : ℝ) ^ 4 := by exact_mod_cast hE3
        have hpow : ((n : ℝ) ^ (4 / 3 : ℝ)) ^ 3 = (n : ℝ) ^ 4 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
        rw [mul_pow, hpow]
        nlinarith only [h1, pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) 4]
      by_contra hgt; push Not at hgt
      have hnn : (0 : ℝ) ≤ 6 * (n : ℝ) ^ (4 / 3 : ℝ) :=
        mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have : (6 * (n : ℝ) ^ (4 / 3 : ℝ)) ^ 3 < (E.card : ℝ) ^ 3 :=
        pow_lt_pow_left₀ hgt hnn (by norm_num)
      linarith
    have hU_r : (U : ℝ) ≤ (E.card : ℝ) + 2 * (n : ℝ) := by exact_mod_cast hU_le
    linarith
  · push Not at hdense
    have hU_r : (U : ℝ) ≤ 10 * (n : ℝ) := by exact_mod_cast (show U ≤ 10 * n by omega)
    linarith

/-! ### Part 6: Székely (1997) `Ω(n^{4/5})` Pinned & Global Distinct Distances Lower Bound -/

/-- The perpendicular bisector of two distinct points `a, b ∈ ℝ²` as an explicit 1D `AffineSubspace`. -/
private noncomputable def perpBisector (a b : EuclideanSpace ℝ (Fin 2)) :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  AffineSubspace.mk' ((1 / 2 : ℝ) • (a + b))
    (Submodule.span ℝ {WithLp.toLp 2 ![-(b 1 - a 1), b 0 - a 0]})

private lemma perpBisector_finrank {a b : EuclideanSpace ℝ (Fin 2)} (hab : a ≠ b) :
    Module.finrank ℝ (perpBisector a b).direction = 1 := by
  have hdir : (perpBisector a b).direction =
      Submodule.span ℝ ({WithLp.toLp 2 ![-(b 1 - a 1), b 0 - a 0]} : Set (EuclideanSpace ℝ (Fin 2))) :=
    AffineSubspace.direction_mk' _ _
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _ hdir)]
  refine finrank_span_singleton fun h0 => hab (euc2_ext ?_ ?_)
  · have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h0; simp at this; linarith
  · have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h0; simp at this; linarith

private lemma mem_perpBisector_iff {a b : EuclideanSpace ℝ (Fin 2)} (hab : a ≠ b)
    (p : EuclideanSpace ℝ (Fin 2)) :
    p ∈ perpBisector a b ↔ dist p a = dist p b := by
  dsimp [perpBisector]
  rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
  set mid := (1 / 2 : ℝ) • (a + b)
  set dir : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![-(b 1 - a 1), b 0 - a 0]
  have hmid0 : mid 0 = (a 0 + b 0) / 2 := by simp [mid]; ring
  have hmid1 : mid 1 = (a 1 + b 1) / 2 := by simp [mid]; ring
  have hD_pos : 0 < (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 := by
    have hne : (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 ≠ 0 := fun h0 => hab (euc2_ext (by nlinarith) (by nlinarith))
    exact lt_of_le_of_ne (by positivity) (Ne.symm hne)
  have hdist_iff : dist p a = dist p b ↔
      (b 0 - a 0) * (p 0 - mid 0) + (b 1 - a 1) * (p 1 - mid 1) = 0 := by
    have hsq_eq : dist p a ^ 2 - dist p b ^ 2 =
        2 * ((b 0 - a 0) * (p 0 - mid 0) + (b 1 - a 1) * (p 1 - mid 1)) := by
      rw [dist_sq_eq_euc2, dist_sq_eq_euc2, hmid0, hmid1]; ring
    constructor
    · intro h; rw [h, sub_self] at hsq_eq; linarith
    · intro h
      have hsq : dist p a ^ 2 = dist p b ^ 2 := by linarith
      have h1 : 0 ≤ dist p a := dist_nonneg
      have h2 : 0 ≤ dist p b := dist_nonneg
      nlinarith
  rw [hdist_iff]
  constructor
  · rintro ⟨s, hs⟩
    have h0 : p 0 - mid 0 = -s * (b 1 - a 1) := by
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hs
      simp [vsub_eq_sub, dir] at this; linarith
    have h1 : p 1 - mid 1 = s * (b 0 - a 0) := by
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hs
      simp [vsub_eq_sub, dir] at this; linarith
    rw [h0, h1]; ring
  · intro horth
    let D := (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2
    let s := (-(b 1 - a 1) * (p 0 - mid 0) + (b 0 - a 0) * (p 1 - mid 1)) / D
    refine ⟨s, euc2_ext ?_ ?_⟩
    · simp only [vsub_eq_sub, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, dir,
        Matrix.cons_val_zero]
      have hD_ne : D ≠ 0 := ne_of_gt hD_pos
      dsimp [s]; field_simp [hD_ne]
      have hid : -((b 1 - a 1) * (-(b 1 - a 1) * (p 0 - mid 0) + (b 0 - a 0) * (p 1 - mid 1))) =
          D * (p 0 - mid 0) - (b 0 - a 0) * ((b 0 - a 0) * (p 0 - mid 0) + (b 1 - a 1) * (p 1 - mid 1)) := by
        dsimp [D]; ring
      rw [horth] at hid; linarith
    · simp only [vsub_eq_sub, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, dir,
        Matrix.cons_val_one]
      have hD_ne : D ≠ 0 := ne_of_gt hD_pos
      dsimp [s]; field_simp [hD_ne]
      have hid : (b 0 - a 0) * (-(b 1 - a 1) * (p 0 - mid 0) + (b 0 - a 0) * (p 1 - mid 1)) =
          D * (p 1 - mid 1) - (b 1 - a 1) * ((b 0 - a 0) * (p 0 - mid 0) + (b 1 - a 1) * (p 1 - mid 1)) := by
        dsimp [D]; ring
      rw [horth] at hid; linarith

/-- **Diameter-Straddling Uniqueness Lemma (Core of Székely 1997)**:
On any open semicircle (upper or lower) of circle `(c, r)` (`r > 0`), for ANY fixed line `ℓ`,
AT MOST ONE consecutive arc `(i, j) ∈ consecPairs (sideIdx)` can have `perpBisector (v i) (v j) = ℓ`!
Proof: `g(s) = w₀(s - c₀) ± w₁√(r² - (s - c₀)²)` has strictly opposite signs at the endpoints of
any chord whose perpendicular bisector is `ℓ`, so by IVT each such arc contains a root of `g` in its
open x-interval `(v i 0, v j 0)`; yet `g` has AT MOST ONE root on `(c₀ - r, c₀ + r)`! -/
private lemma circle_consecPairs_perpBisector_le_one
    {n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin 2))
    (hx : StrictMono (fun i => v i 0))
    (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (_hr : 0 < r) (side : Bool)
    (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :
    let ls := (Finset.univ.filter (fun i : Fin n =>
      dist c (v i) = r ∧ (if side then c 1 < v i 1 else v i 1 < c 1))).sort (· ≤ ·)
    ((consecPairs ls).filter (fun pq => perpBisector (v pq.1) (v pq.2) = ℓ)).length ≤ 1 := by
  intro ls
  have hpw : ls.Pairwise (· < ·) :=
    List.Pairwise.imp_of_mem (fun {a b} _ _ ⟨h1, h2⟩ => lt_of_le_of_ne h1 h2)
      ((Finset.pairwise_sort _ _).and (Finset.sort_nodup _ _))
  have hnd : ((consecPairs ls).filter (fun pq => perpBisector (v pq.1) (v pq.2) = ℓ)).Nodup :=
    (consecPairs_nodup hpw).filter _
  -- Show any two elements `p, q` in the filtered list must be equal!
  suffices hsub : ∀ p ∈ (consecPairs ls).filter (fun pq => perpBisector (v pq.1) (v pq.2) = ℓ),
      ∀ q ∈ (consecPairs ls).filter (fun pq => perpBisector (v pq.1) (v pq.2) = ℓ), p = q by
    cases hf : (consecPairs ls).filter (fun pq => perpBisector (v pq.1) (v pq.2) = ℓ) with
    | nil => simp
    | cons a rest =>
      cases rest with
      | nil => simp
      | cons b rest' =>
        have ha : a ∈ a :: b :: rest' := by simp
        have hb : b ∈ a :: b :: rest' := by simp
        have hab : a = b := hsub a (hf ▸ ha) b (hf ▸ hb)
        rw [hf] at hnd
        exact absurd (hab ▸ (by simp : b ∈ b :: rest')) (List.nodup_cons.mp hnd).1
  intro p hp q hq
  by_contra hne
  simp only [List.mem_filter, decide_eq_true_eq] at hp hq
  -- Use `w = v p.2 - v p.1 ≠ 0` as the nonzero normal to `ℓ = perpBisector (v p.1) (v p.2)`!
  have hp_lt : p.1 < p.2 := consecPairs_lt hpw hp.1
  have hq_lt : q.1 < q.2 := consecPairs_lt hpw hq.1
  have hp_ne : v p.1 ≠ v p.2 := fun h => ne_of_lt (hx hp_lt) (by dsimp only; rw [h])
  have hq_ne : v q.1 ≠ v q.2 := fun h => ne_of_lt (hx hq_lt) (by dsimp only; rw [h])
  have hmem_info : ∀ i ∈ ls, dist c (v i) = r ∧ (if side then c 1 < v i 1 else v i 1 < c 1) :=
    fun i hi => (Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hi)).2
  have hp1 := hmem_info p.1 (consecPairs_mem hp.1).1
  have hp2 := hmem_info p.2 (consecPairs_mem hp.1).2
  have hq1 := hmem_info q.1 (consecPairs_mem hq.1).1
  have hq2 := hmem_info q.2 (consecPairs_mem hq.1).2
  set w0 := v p.2 0 - v p.1 0
  set w1 := v p.2 1 - v p.1 1
  have hw_pos : 0 < w0 ^ 2 + w1 ^ 2 := by
    have : w0 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (hx hp_lt))
    positivity
  -- Both `c` lies on `perpBisector (v p.1) (v p.2) = perpBisector (v q.1) (v q.2)`!
  have hc_p : c ∈ perpBisector (v p.1) (v p.2) :=
    (mem_perpBisector_iff hp_ne c).mpr (hp1.1.trans hp2.1.symm)
  -- Define `f s = w0 * (s - c 0) + w1 * (sgn * √(r² - (s - c 0)²))`!
  let sgn : ℝ := if side then 1 else -1
  let f (s : ℝ) : ℝ := w0 * (s - c 0) + w1 * (sgn * Real.sqrt (r ^ 2 - (s - c 0) ^ 2))
  have hf_cont : Continuous f :=
    (continuous_const.mul (continuous_id.sub continuous_const)).add
      (continuous_const.mul (continuous_const.mul (Real.continuous_sqrt.comp
        (continuous_const.sub ((continuous_id.sub continuous_const).pow 2)))))
  -- Evaluate `f` at any `v i 0` for `i ∈ ls`: `f (v i 0) = w0 * (v i 0 - c 0) + w1 * (v i 1 - c 1)`!
  have hf_at : ∀ i ∈ ls, f (v i 0) = w0 * (v i 0 - c 0) + w1 * (v i 1 - c 1) := by
    intro i hi
    have hinfo := hmem_info i hi
    have hsq : (v i 1 - c 1) ^ 2 = r ^ 2 - (v i 0 - c 0) ^ 2 := by
      have := dist_sq_eq_euc2 c (v i); rw [hinfo.1] at this; linarith
    dsimp [f, sgn]
    cases side
    · simp only [Bool.false_eq_true, ↓reduceIte] at hinfo ⊢
      have hsq' : (c 1 - v i 1) ^ 2 = r ^ 2 - (v i 0 - c 0) ^ 2 := by linarith
      rw [← hsq', Real.sqrt_sq (by linarith)]; ring
    · simp only [↓reduceIte] at hinfo ⊢
      rw [← hsq, Real.sqrt_sq (by linarith)]; ring
  -- Show `f` has strictly opposite signs at `v p.1 0` and `v p.2 0`!
  have hfp1_neg : f (v p.1 0) < 0 := by
    rw [hf_at p.1 (consecPairs_mem hp.1).1]
    have h1 := dist_sq_eq_euc2 c (v p.1); rw [hp1.1] at h1
    have h2 := dist_sq_eq_euc2 c (v p.2); rw [hp2.1] at h2
    have hid : 2 * (w0 * (v p.1 0 - c 0) + w1 * (v p.1 1 - c 1)) =
        ((c 0 - v p.2 0) ^ 2 + (c 1 - v p.2 1) ^ 2) - ((c 0 - v p.1 0) ^ 2 + (c 1 - v p.1 1) ^ 2) -
        (w0 ^ 2 + w1 ^ 2) := by dsimp [w0, w1]; ring
    linarith
  have hfp2_pos : 0 < f (v p.2 0) := by
    rw [hf_at p.2 (consecPairs_mem hp.1).2]
    have h1 := dist_sq_eq_euc2 c (v p.1); rw [hp1.1] at h1
    have h2 := dist_sq_eq_euc2 c (v p.2); rw [hp2.1] at h2
    have hid : 2 * (w0 * (v p.2 0 - c 0) + w1 * (v p.2 1 - c 1)) =
        ((c 0 - v p.2 0) ^ 2 + (c 1 - v p.2 1) ^ 2) - ((c 0 - v p.1 0) ^ 2 + (c 1 - v p.1 1) ^ 2) +
        (w0 ^ 2 + w1 ^ 2) := by dsimp [w0, w1]; ring
    linarith
  -- Show `f` also has strictly opposite signs at `v q.1 0` and `v q.2 0`!
  -- Because `perpBisector (v p.1) (v p.2) = perpBisector (v q.1) (v q.2)`, `(v q.2 - v q.1)` is parallel to `w`!
  set u0 := v q.2 0 - v q.1 0
  set u1 := v q.2 1 - v q.1 1
  have hu_pos : 0 < u0 ^ 2 + u1 ^ 2 := by
    have : u0 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (hx hq_lt))
    positivity
  have hcross : w0 * (-u1) + w1 * u0 = 0 := by
    -- Point `z = c + (-u1, u0)` lies on `perpBisector (v q.1) (v q.2) = perpBisector (v p.1) (v p.2)`!
    let z : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![c 0 - u1, c 1 + u0]
    have hz_q : z ∈ perpBisector (v q.1) (v q.2) := by
      rw [mem_perpBisector_iff hq_ne]
      have h1 := dist_sq_eq_euc2 c (v q.1); rw [hq1.1] at h1
      have h2 := dist_sq_eq_euc2 c (v q.2); rw [hq2.1] at h2
      have hsq : dist z (v q.1) ^ 2 = dist z (v q.2) ^ 2 := by
        rw [dist_sq_eq_euc2, dist_sq_eq_euc2]
        simp only [z, Matrix.cons_val_zero, Matrix.cons_val_one]
        have hid : ((c 0 - u1 - v q.1 0) ^ 2 + (c 1 + u0 - v q.1 1) ^ 2) -
            ((c 0 - u1 - v q.2 0) ^ 2 + (c 1 + u0 - v q.2 1) ^ 2) =
            ((c 0 - v q.1 0) ^ 2 + (c 1 - v q.1 1) ^ 2) - ((c 0 - v q.2 0) ^ 2 + (c 1 - v q.2 1) ^ 2) := by
          dsimp [u0, u1]; ring
        linarith
      have d1 : 0 ≤ dist z (v q.1) := dist_nonneg
      have d2 : 0 ≤ dist z (v q.2) := dist_nonneg
      nlinarith
    have hz_p : dist z (v p.1) = dist z (v p.2) :=
      (mem_perpBisector_iff hp_ne z).mp (hp.2.symm ▸ hq.2 ▸ hz_q)
    have h1 := dist_sq_eq_euc2 c (v p.1); rw [hp1.1] at h1
    have h2 := dist_sq_eq_euc2 c (v p.2); rw [hp2.1] at h2
    have hsq := congrArg (· ^ 2) hz_p
    rw [dist_sq_eq_euc2, dist_sq_eq_euc2] at hsq
    simp only [z, Matrix.cons_val_zero, Matrix.cons_val_one] at hsq
    have hid : ((c 0 - u1 - v p.1 0) ^ 2 + (c 1 + u0 - v p.1 1) ^ 2) -
        ((c 0 - u1 - v p.2 0) ^ 2 + (c 1 + u0 - v p.2 1) ^ 2) =
        ((c 0 - v p.1 0) ^ 2 + (c 1 - v p.1 1) ^ 2) - ((c 0 - v p.2 0) ^ 2 + (c 1 - v p.2 1) ^ 2) +
        2 * (w0 * (-u1) + w1 * u0) := by dsimp [w0, w1]; ring
    linarith
  let lam := (w0 * u0 + w1 * u1) / (u0 ^ 2 + u1 ^ 2)
  have hw0_eq : w0 = lam * u0 := by
    dsimp [lam]; field_simp [ne_of_gt hu_pos]
    have h1 : (w0 * u0 + w1 * u1) * u0 = w0 * (u0 ^ 2 + u1 ^ 2) + u1 * (w0 * (-u1) + w1 * u0) := by ring
    rw [hcross] at h1; linarith
  have hw1_eq : w1 = lam * u1 := by
    dsimp [lam]; field_simp [ne_of_gt hu_pos]
    have h1 : (w0 * u0 + w1 * u1) * u1 = w1 * (u0 ^ 2 + u1 ^ 2) - u0 * (w0 * (-u1) + w1 * u0) := by ring
    rw [hcross] at h1; linarith
  have hlam_ne : lam ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hw0_eq hw1_eq; rw [hw0_eq, hw1_eq] at hw_pos; linarith
  have hfq1 : f (v q.1 0) = -lam * (u0 ^ 2 + u1 ^ 2) / 2 := by
    rw [hf_at q.1 (consecPairs_mem hq.1).1, hw0_eq, hw1_eq]
    have h1 := dist_sq_eq_euc2 c (v q.1); rw [hq1.1] at h1
    have h2 := dist_sq_eq_euc2 c (v q.2); rw [hq2.1] at h2
    have hid : 2 * (u0 * (v q.1 0 - c 0) + u1 * (v q.1 1 - c 1)) =
        ((c 0 - v q.2 0) ^ 2 + (c 1 - v q.2 1) ^ 2) - ((c 0 - v q.1 0) ^ 2 + (c 1 - v q.1 1) ^ 2) -
        (u0 ^ 2 + u1 ^ 2) := by dsimp [u0, u1]; ring
    have hval : u0 * (v q.1 0 - c 0) + u1 * (v q.1 1 - c 1) = -(u0 ^ 2 + u1 ^ 2) / 2 := by linarith
    have : lam * u0 * (v q.1 0 - c 0) + lam * u1 * (v q.1 1 - c 1) =
        lam * (u0 * (v q.1 0 - c 0) + u1 * (v q.1 1 - c 1)) := by ring
    rw [this, hval]; ring
  have hfq2 : f (v q.2 0) = lam * (u0 ^ 2 + u1 ^ 2) / 2 := by
    rw [hf_at q.2 (consecPairs_mem hq.1).2, hw0_eq, hw1_eq]
    have h1 := dist_sq_eq_euc2 c (v q.1); rw [hq1.1] at h1
    have h2 := dist_sq_eq_euc2 c (v q.2); rw [hq2.1] at h2
    have hid : 2 * (u0 * (v q.2 0 - c 0) + u1 * (v q.2 1 - c 1)) =
        ((c 0 - v q.2 0) ^ 2 + (c 1 - v q.2 1) ^ 2) - ((c 0 - v q.1 0) ^ 2 + (c 1 - v q.1 1) ^ 2) +
        (u0 ^ 2 + u1 ^ 2) := by dsimp [u0, u1]; ring
    have hval : u0 * (v q.2 0 - c 0) + u1 * (v q.2 1 - c 1) = (u0 ^ 2 + u1 ^ 2) / 2 := by linarith
    have : lam * u0 * (v q.2 0 - c 0) + lam * u1 * (v q.2 1 - c 1) =
        lam * (u0 * (v q.2 0 - c 0) + u1 * (v q.2 1 - c 1)) := by ring
    rw [this, hval]; ring
  -- By IVT, `f` has a root `s1 ∈ (v p.1 0, v p.2 0)` AND a root `s2 ∈ (v q.1 0, v q.2 0)`!
  have hs1_ex : ∃ s1, v p.1 0 < s1 ∧ s1 < v p.2 0 ∧ f s1 = 0 := by
    have h0mem : (0 : ℝ) ∈ Set.Icc (f (v p.1 0)) (f (v p.2 0)) := ⟨le_of_lt hfp1_neg, le_of_lt hfp2_pos⟩
    obtain ⟨s1, hs1_icc, hs1_eq⟩ := intermediate_value_Icc (le_of_lt (hx hp_lt)) hf_cont.continuousOn h0mem
    have h1ne : s1 ≠ v p.1 0 := fun h => by rw [h] at hs1_eq; linarith
    have h2ne : s1 ≠ v p.2 0 := fun h => by rw [h] at hs1_eq; linarith
    exact ⟨s1, lt_of_le_of_ne hs1_icc.1 h1ne.symm, lt_of_le_of_ne hs1_icc.2 h2ne, hs1_eq⟩
  have hs2_ex : ∃ s2, v q.1 0 < s2 ∧ s2 < v q.2 0 ∧ f s2 = 0 := by
    rcases lt_or_gt_of_ne hlam_ne with hlam_neg | hlam_pos
    · have h1 : 0 < f (v q.1 0) := by rw [hfq1]; nlinarith
      have h2 : f (v q.2 0) < 0 := by rw [hfq2]; nlinarith
      have h0mem : (0 : ℝ) ∈ Set.Icc (f (v q.2 0)) (f (v q.1 0)) := ⟨le_of_lt h2, le_of_lt h1⟩
      obtain ⟨s2, hs2_icc, hs2_eq⟩ := intermediate_value_Icc' (le_of_lt (hx hq_lt)) hf_cont.continuousOn h0mem
      have h1ne : s2 ≠ v q.1 0 := fun h => by rw [h] at hs2_eq; linarith
      have h2ne : s2 ≠ v q.2 0 := fun h => by rw [h] at hs2_eq; linarith
      exact ⟨s2, lt_of_le_of_ne hs2_icc.1 h1ne.symm, lt_of_le_of_ne hs2_icc.2 h2ne, hs2_eq⟩
    · have h1 : f (v q.1 0) < 0 := by rw [hfq1]; nlinarith
      have h2 : 0 < f (v q.2 0) := by rw [hfq2]; nlinarith
      have h0mem : (0 : ℝ) ∈ Set.Icc (f (v q.1 0)) (f (v q.2 0)) := ⟨le_of_lt h1, le_of_lt h2⟩
      obtain ⟨s2, hs2_icc, hs2_eq⟩ := intermediate_value_Icc (le_of_lt (hx hq_lt)) hf_cont.continuousOn h0mem
      have h1ne : s2 ≠ v q.1 0 := fun h => by rw [h] at hs2_eq; linarith
      have h2ne : s2 ≠ v q.2 0 := fun h => by rw [h] at hs2_eq; linarith
      exact ⟨s2, lt_of_le_of_ne hs2_icc.1 h1ne.symm, lt_of_le_of_ne hs2_icc.2 h2ne, hs2_eq⟩
  obtain ⟨s1, hs1l, hs1r, hfs1⟩ := hs1_ex
  obtain ⟨s2, hs2l, hs2r, hfs2⟩ := hs2_ex
  -- Since `p ≠ q` are consecutive pairs, `(v p.1 0, v p.2 0)` and `(v q.1 0, v q.2 0)` are disjoint → `s1 ≠ s2`!
  have hs_ne : s1 ≠ s2 := by
    rcases consecPairs_disjoint_open hpw hp.1 hq.1 hne with hle | hle
    · have := hx.monotone hle; linarith
    · have := hx.monotone hle; linarith
  -- Both `s1` and `s2` satisfy `0 < r² - (s - c 0)²`!
  have hrad_in : ∀ i j : Fin n, i ∈ ls → j ∈ ls → ∀ s, v i 0 < s → s < v j 0 → 0 < r ^ 2 - (s - c 0) ^ 2 := by
    intro i j hi hj s h1 h2
    have hi' := hmem_info i hi; have hj' := hmem_info j hj
    have hsq_i := dist_sq_eq_euc2 c (v i); rw [hi'.1] at hsq_i
    have hsq_j := dist_sq_eq_euc2 c (v j); rw [hj'.1] at hsq_j
    have hyi : c 1 - v i 1 ≠ 0 := by cases side <;> simp at hi' <;> linarith
    have hyj : c 1 - v j 1 ≠ 0 := by cases side <;> simp at hj' <;> linarith
    have hxi : (v i 0 - c 0) ^ 2 < r ^ 2 := by
      have hpos : 0 < (c 1 - v i 1) ^ 2 := sq_pos_of_ne_zero hyi
      have hsym : (v i 0 - c 0) ^ 2 = (c 0 - v i 0) ^ 2 := by ring
      linarith only [hsq_i, hpos, hsym]
    have hxj : (v j 0 - c 0) ^ 2 < r ^ 2 := by
      have hpos : 0 < (c 1 - v j 1) ^ 2 := sq_pos_of_ne_zero hyj
      have hsym : (v j 0 - c 0) ^ 2 = (c 0 - v j 0) ^ 2 := by ring
      linarith only [hsq_j, hpos, hsym]
    have hmax : (s - c 0) ^ 2 ≤ max ((v i 0 - c 0) ^ 2) ((v j 0 - c 0) ^ 2) := by
      rcases le_total (s - c 0) 0 with hle | hge
      · exact le_trans (by nlinarith only [h1, hle]) (le_max_left _ _)
      · exact le_trans (by nlinarith only [h2, hge]) (le_max_right _ _)
    linarith only [hmax, max_lt hxi hxj]
  have hr1 : 0 < r ^ 2 - (s1 - c 0) ^ 2 := hrad_in p.1 p.2 (consecPairs_mem hp.1).1 (consecPairs_mem hp.1).2 s1 hs1l hs1r
  have hr2 : 0 < r ^ 2 - (s2 - c 0) ^ 2 := hrad_in q.1 q.2 (consecPairs_mem hq.1).1 (consecPairs_mem hq.1).2 s2 hs2l hs2r
  -- Yet `f s = w0 * (s - c 0) + w1 * sgn * √(r² - (s - c 0)²) = 0` has AT MOST ONE root with `r² - (s - c 0)² > 0`!
  -- Note `w0 = v p.2 0 - v p.1 0 > 0` strictly!
  have hw0_pos : 0 < w0 := sub_pos.mpr (hx hp_lt)
  have hsgn_sq : sgn ^ 2 = 1 := by dsimp [sgn]; cases side <;> norm_num
  have hsq1 : (w0 ^ 2 + w1 ^ 2) * (s1 - c 0) ^ 2 = w1 ^ 2 * r ^ 2 := by
    have h1 : w0 * (s1 - c 0) = -(w1 * (sgn * Real.sqrt (r ^ 2 - (s1 - c 0) ^ 2))) := by
      dsimp [f] at hfs1; linarith
    have h2 := congrArg (· ^ 2) h1
    have h3 : (-(w1 * (sgn * Real.sqrt (r ^ 2 - (s1 - c 0) ^ 2)))) ^ 2 =
        w1 ^ 2 * sgn ^ 2 * (Real.sqrt (r ^ 2 - (s1 - c 0) ^ 2)) ^ 2 := by ring
    rw [h3, hsgn_sq, Real.sq_sqrt (le_of_lt hr1)] at h2
    ring_nf at h2 ⊢; linarith
  have hsq2 : (w0 ^ 2 + w1 ^ 2) * (s2 - c 0) ^ 2 = w1 ^ 2 * r ^ 2 := by
    have h1 : w0 * (s2 - c 0) = -(w1 * (sgn * Real.sqrt (r ^ 2 - (s2 - c 0) ^ 2))) := by
      dsimp [f] at hfs2; linarith
    have h2 := congrArg (· ^ 2) h1
    have h3 : (-(w1 * (sgn * Real.sqrt (r ^ 2 - (s2 - c 0) ^ 2)))) ^ 2 =
        w1 ^ 2 * sgn ^ 2 * (Real.sqrt (r ^ 2 - (s2 - c 0) ^ 2)) ^ 2 := by ring
    rw [h3, hsgn_sq, Real.sq_sqrt (le_of_lt hr2)] at h2
    ring_nf at h2 ⊢; linarith
  have hdiff_sq : (s1 - c 0) ^ 2 = (s2 - c 0) ^ 2 := by nlinarith only [hsq1, hsq2, hw_pos]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hdiff_sq with hsame | hopp
  · exact hs_ne (by linarith)
  · -- `s1 - c 0 = -(s2 - c 0)` implies `w0 * (s1 - c 0) + w0 * (s2 - c 0) = 0`,
    -- so `w1 * sgn * (√(...) + √(...)) = 0`, forcing `w1 = 0`, hence `s1 = c 0 = s2`!
    have hsum0 : f s1 + f s2 = 0 := by linarith
    dsimp [f] at hsum0
    have hsqrt_sum : 0 < Real.sqrt (r ^ 2 - (s1 - c 0) ^ 2) + Real.sqrt (r ^ 2 - (s2 - c 0) ^ 2) :=
      add_pos (Real.sqrt_pos.mpr hr1) (Real.sqrt_pos.mpr hr2)
    have hw1_0 : w1 = 0 := by
      have hfac : w1 * sgn * (Real.sqrt (r ^ 2 - (s1 - c 0) ^ 2) + Real.sqrt (r ^ 2 - (s2 - c 0) ^ 2)) = 0 := by
        have hw0_sum : w0 * (s1 - c 0) + w0 * (s2 - c 0) = 0 := by rw [hopp]; ring
        linarith only [hsum0, hw0_sum]
      have hws : w1 * sgn = 0 := (mul_eq_zero.mp hfac).resolve_right (ne_of_gt hsqrt_sum)
      have hsgn_ne : sgn ≠ 0 := by dsimp [sgn]; cases side <;> norm_num
      exact (mul_eq_zero.mp hws).resolve_right hsgn_ne
    dsimp [f] at hfs1 hfs2
    rw [hw1_0] at hfs1 hfs2
    exact hs_ne (by nlinarith only [hfs1, hfs2, hw0_pos])

/-- **Székely (1997) Pinned Distinct Distances Lower Bound (`Ω(n^{4/5})`, Pure-Mathlib Public Theorem)**:
For every finite point set `P ⊂ ℝ²` with `|P| ≥ 2`, there exists a point `p ∈ P` determining at
least `|P|^{4/5} / 250` distinct distances to the remaining points of `P`!
(Equivalently: if every point `p ∈ P` determines at most `t` distinct distances, then
`|P|^{4/5} / 250 ≤ t`.) -/
theorem ppl071_szekely_1997_pinned_distinct_distances
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (hP : 2 ≤ P.card) :
    ∃ p ∈ P, (P.card : ℝ) ^ (4 / 5 : ℝ) / 250 ≤ (((P.erase p).image (dist p)).card : ℝ) := by
  by_contra hall
  push Not at hall
  set n := P.card
  -- Let `t` be the maximum number of distinct distances from any `p ∈ P`!
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  let t : ℕ := P.sup (fun p => ((P.erase p).image (dist p)).card)
  have ht_ge1 : 1 ≤ t := by
    obtain ⟨p, hp⟩ := hPne
    have her_ne : (P.erase p).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hp]; omega
    have him_pos : 1 ≤ ((P.erase p).image (dist p)).card :=
      Finset.card_pos.mpr (her_ne.image _)
    exact le_trans him_pos (Finset.le_sup (f := fun p => ((P.erase p).image (dist p)).card) hp)
  have ht_lt : (t : ℝ) < (n : ℝ) ^ (4 / 5 : ℝ) / 250 := by
    obtain ⟨p₀, hp₀, hmax⟩ := Finset.exists_mem_eq_sup P hPne (fun p => ((P.erase p).image (dist p)).card)
    have h1 := hall p₀ hp₀
    have h2 : t = ((P.erase p₀).image (dist p₀)).card := hmax
    rw [h2]; exact h1
  -- Immediate lower bound on `n`: since `1 ≤ t < n^{4/5} / 250`, we have `n > 250`!
  have hn_gt250 : 250 < n := by
    by_contra hle; push Not at hle
    have hn_r : (n : ℝ) ≤ 250 := by exact_mod_cast hle
    have hpow_le : (n : ℝ) ^ (4 / 5 : ℝ) ≤ (n : ℝ) := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      calc (n : ℝ) ^ (4 / 5 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
        _ = (n : ℝ) := Real.rpow_one _
    have ht1_r : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_ge1
    linarith
  -- Also `t < n / 250` (since `n^{4/5} ≤ n` for `n ≥ 1`)!
  have ht_lt_div : (t : ℝ) < (n : ℝ) / 250 := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hpow_le : (n : ℝ) ^ (4 / 5 : ℝ) ≤ (n : ℝ) := by
      calc (n : ℝ) ^ (4 / 5 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
        _ = (n : ℝ) := Real.rpow_one _
    linarith
  -- Apply generic similarity tilt `s` so both `x`- and `y`-coordinates of `P'` are strictly injective!
  obtain ⟨s, hsX, hsY⟩ := exists_tilt_xy_inj P
  obtain ⟨v, hx, hv_inj, hv_mem, hv_surj⟩ := sorted_tilted_points P s hsX
  let P' := P.image (tilt s)
  have hP'_card : P'.card = n := Finset.card_image_of_injective P (tilt_injective s)
  let R : ℝ := Real.sqrt (1 + s ^ 2)
  have hR_pos : 0 < R := Real.sqrt_pos.mpr (by positivity)
  -- Every point `c ∈ P'` determines at most `t` distinct distances to `P'.erase c`!
  have hP'_pinned : ∀ c ∈ P', ((P'.erase c).image (dist c)).card ≤ t := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    have hcard_eq : ((P'.erase (tilt s p)).image (dist (tilt s p))).card =
        ((P.erase p).image (dist p)).card := by
      refine Finset.card_bij (fun d _ => d / R) (fun d hd => ?_) (fun d₁ _ d₂ _ h => ?_) (fun d hd => ?_)
      · obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hd
        have hq'm := Finset.mem_erase.mp hq'
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'm.2
        refine Finset.mem_image.mpr ⟨q, Finset.mem_erase.mpr ⟨fun h => hq'm.1 (by rw [h]), hq⟩, ?_⟩
        rw [dist_tilt]; dsimp [R]; field_simp [ne_of_gt hR_pos]
      · exact (div_left_inj' (ne_of_gt hR_pos)).mp h
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hd
        have hqm := Finset.mem_erase.mp hq
        refine ⟨R * dist p q, Finset.mem_image.mpr ⟨tilt s q,
          Finset.mem_erase.mpr ⟨fun h => hqm.1 (tilt_injective s h), Finset.mem_image_of_mem _ hqm.2⟩,
          dist_tilt s p q⟩, ?_⟩
        field_simp [ne_of_gt hR_pos]
    rw [hcard_eq]
    exact Finset.le_sup (f := fun p => ((P.erase p).image (dist p)).card) hp
  -- Construct the concentric circle family `C` of size `≤ n * t`!
  let C : Finset (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    P'.biUnion (fun c => ((P'.erase c).image (dist c)).image (fun r => (c, r)))
  have hC_card : C.card ≤ n * t := by
    calc C.card
        ≤ ∑ c ∈ P', (((P'.erase c).image (dist c)).image (fun r => (c, r))).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ P', ((P'.erase c).image (dist c)).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ ≤ ∑ _c ∈ P', t := Finset.sum_le_sum fun c hc => hP'_pinned c hc
      _ = n * t := by rw [Finset.sum_const, hP'_card, smul_eq_mul]
  have hCr : ∀ cr ∈ C, 0 < cr.2 := by
    intro cr hcr
    obtain ⟨c, _, hcr'⟩ := Finset.mem_biUnion.mp hcr
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hcr'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    exact dist_pos.mpr (Finset.mem_erase.mp hq).1.symm
  have hCy : ∀ cr ∈ C, ∀ i : Fin n, dist cr.1 (v i) = cr.2 → v i 1 ≠ cr.1 1 := by
    intro cr hcr i hd heq
    obtain ⟨c, hc, hcr'⟩ := Finset.mem_biUnion.mp hcr
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hcr'
    have hr_pos : 0 < r := hCr (c, r) hcr
    obtain ⟨p₁, hp₁, h1⟩ := Finset.mem_image.mp (hv_mem i)
    obtain ⟨p₂, hp₂, h2⟩ := Finset.mem_image.mp hc
    have hpeq : p₁ = p₂ := hsY hp₁ hp₂ (by dsimp only; rw [h1, h2]; exact heq)
    have hveq : v i = c := by rw [← h1, ← h2, hpeq]
    rw [hveq, dist_self] at hd; linarith
  -- Sum of incidences over `C` equals `n * (n - 1)`!
  have hsum_inc : ∑ cr ∈ C, (Finset.univ.filter (fun i : Fin n => dist cr.1 (v i) = cr.2)).card = n * (n - 1) := by
    have h1 : ∑ cr ∈ C, (Finset.univ.filter (fun i : Fin n => dist cr.1 (v i) = cr.2)).card =
        (C.sigma (fun cr => Finset.univ.filter (fun i : Fin n => dist cr.1 (v i) = cr.2))).card :=
      (Finset.card_sigma _ _).symm
    rw [h1]
    have h2 : ((P' ×ˢ P').filter (fun pq => pq.1 ≠ pq.2)).card = n * (n - 1) := by
      rw [Finset.card_filter, Finset.sum_product]
      have hrow : ∀ c ∈ P', (∑ q ∈ P', if c ≠ q then 1 else 0) = n - 1 := fun c hc => by
        rw [← Finset.card_filter]
        have hfeq : P'.filter (fun q => c ≠ q) = P'.erase c := by
          ext q; simp [Finset.mem_erase, ne_comm, and_comm]
        rw [hfeq, Finset.card_erase_of_mem hc, hP'_card]
      rw [Finset.sum_congr rfl hrow, Finset.sum_const, hP'_card, smul_eq_mul]
    rw [← h2]
    refine Finset.card_bij (fun x _ => (x.1.1, v x.2)) (fun x hx_in => ?_)
      (fun a ha b hb heq => ?_) (fun pq hpq => ?_)
    · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hx_in ⊢
      have hc : x.1.1 ∈ P' := by
        obtain ⟨c, hc, hcr'⟩ := Finset.mem_biUnion.mp hx_in.1
        obtain ⟨r, _, hreq⟩ := Finset.mem_image.mp hcr'
        rw [← congrArg Prod.fst hreq]; exact hc
      have hne : x.1.1 ≠ v x.2 := fun h => by
        have hpos := hCr x.1 hx_in.1
        rw [h, dist_self] at hx_in; linarith [hx_in.2]
      exact ⟨⟨hc, hv_mem x.2⟩, hne⟩
    · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have h1 : a.1.1 = b.1.1 := (Prod.mk.inj heq).1
      have h2 : a.2 = b.2 := hv_inj (Prod.mk.inj heq).2
      have h3 : a.1.2 = b.1.2 := by rw [← ha.2, ← hb.2, h1, h2]
      cases a; cases b; simp only at h1 h2 h3
      subst h2; congr 1; exact Prod.ext h1 h3
    · simp only [Finset.mem_filter, Finset.mem_product] at hpq
      obtain ⟨i, hi⟩ := hv_surj pq.2 hpq.1.2
      have hcr : (pq.1, dist pq.1 pq.2) ∈ C :=
        Finset.mem_biUnion.mpr ⟨pq.1, hpq.1.1, Finset.mem_image.mpr ⟨dist pq.1 pq.2,
          Finset.mem_image.mpr ⟨pq.2, Finset.mem_erase.mpr ⟨hpq.2.symm, hpq.1.2⟩, rfl⟩, rfl⟩⟩
      refine ⟨⟨(pq.1, dist pq.1 pq.2), i⟩, ?_, by simp [hi]⟩
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hcr, by rw [hi]⟩
  -- Choose Székely's multiplicity threshold `m = Nat.ceil (46 * Real.sqrt t)` (`m ≥ 46 ≥ 2`)!
  let m : ℕ := Nat.ceil (46 * Real.sqrt (t : ℝ))
  have hm_ge46 : 46 ≤ m := by
    have h1 : (46 : ℝ) ≤ 46 * Real.sqrt (t : ℝ) := by
      have : (1 : ℝ) ≤ Real.sqrt (t : ℝ) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast ht_ge1)
      linarith
    exact_mod_cast le_trans h1 (Nat.le_ceil _)
  have hm_sq : 2116 * t ≤ m ^ 2 := by
    have h1 : (46 * Real.sqrt (t : ℝ)) ^ 2 ≤ (m : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (Nat.le_ceil _) 2
    have h2 : (46 * Real.sqrt (t : ℝ)) ^ 2 = 2116 * (t : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; norm_num
    rw [h2] at h1; exact_mod_cast h1
  have hm_ub : (m : ℝ) ≤ 47 * Real.sqrt (t : ℝ) := by
    have h1 : (m : ℝ) < 46 * Real.sqrt (t : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : ℝ) ≤ Real.sqrt (t : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast ht_ge1)
    linarith
  -- Apply `circles_arc_wiring` with `keep cr i j := |P' ∩ perpBisector (v i) (v j)| ≤ m`!
  let keep (_ : EuclideanSpace ℝ (Fin 2) × ℝ) (i j : Fin n) : Prop :=
    (P'.filter (fun c => dist c (v i) = dist c (v j))).card ≤ m
  obtain ⟨E, W, hW, hmult, hcount⟩ := circles_arc_wiring v hx C hCr hCy keep
  let sideIdx (cr : EuclideanSpace ℝ (Fin 2) × ℝ) (side : Bool) : List (Fin n) :=
    (Finset.univ.filter (fun i : Fin n =>
      dist cr.1 (v i) = cr.2 ∧ (if side then cr.1 1 < v i 1 else v i 1 < cr.1 1))).sort (· ≤ ·)
  -- Bound the dropped (high-multiplicity) edges via Diameter-Straddling + Szemerédi–Trotter Rich Lines!
  let L_rich : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
    ((Finset.univ ×ˢ Finset.univ).filter (fun ij : Fin n × Fin n =>
      ij.1 < ij.2 ∧ m < (P'.filter (fun c => dist c (v ij.1) = dist c (v ij.2))).card)).image
      (fun ij => perpBisector (v ij.1) (v ij.2))
  have hL_rich_dim : ∀ ℓ ∈ L_rich, Module.finrank ℝ ℓ.direction = 1 := by
    intro ℓ hℓ
    obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hℓ
    have hij_lt := (Finset.mem_filter.mp hij).2.1
    exact perpBisector_finrank (fun h => ne_of_lt (hx hij_lt) (by dsimp only; rw [h]))
  have hL_rich_card : ∀ ℓ ∈ L_rich, m ≤ (P'.filter (· ∈ ℓ)).card := by
    intro ℓ hℓ
    obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hℓ
    have hij' := Finset.mem_filter.mp hij
    have hne : v ij.1 ≠ v ij.2 := fun h => ne_of_lt (hx hij'.2.1) (by dsimp only; rw [h])
    have heq : P'.filter (· ∈ perpBisector (v ij.1) (v ij.2)) =
        P'.filter (fun c => dist c (v ij.1) = dist c (v ij.2)) := by
      ext c; simp [mem_perpBisector_iff hne]
    rw [heq]; omega
  -- Bound dropped edges per circle `cr ∈ C`: each `ℓ ∈ L_rich` with `cr.1 ∈ ℓ` accounts for ≤ 2 dropped edges on `cr`!
  have hdrop_per_circle : ∀ cr ∈ C,
      ((consecPairs (sideIdx cr true)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length +
      ((consecPairs (sideIdx cr false)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length ≤
        2 * (L_rich.filter (fun ℓ => cr.1 ∈ ℓ)).card := by
    intro cr hcr
    have hside_le : ∀ side : Bool,
        ((consecPairs (sideIdx cr side)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length ≤
          (L_rich.filter (fun ℓ => cr.1 ∈ ℓ)).card := by
      intro side
      have hpw : (sideIdx cr side).Pairwise (· < ·) :=
        List.Pairwise.imp_of_mem (fun {a b} _ _ ⟨h1, h2⟩ => lt_of_le_of_ne h1 h2)
          ((Finset.pairwise_sort _ _).and (Finset.sort_nodup _ _))
      have hnd : ((consecPairs (sideIdx cr side)).filter (fun pq => ¬ keep cr pq.1 pq.2)).Nodup :=
        (consecPairs_nodup hpw).filter _
      rw [← List.toFinset_card_of_nodup hnd]
      let Sdrop := ((consecPairs (sideIdx cr side)).filter (fun pq => ¬ keep cr pq.1 pq.2)).toFinset
      have hmaps : ∀ pq ∈ Sdrop, perpBisector (v pq.1) (v pq.2) ∈ L_rich.filter (fun ℓ => cr.1 ∈ ℓ) := by
        intro pq hpq
        simp only [Sdrop, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hpq
        have hlt : pq.1 < pq.2 := consecPairs_lt hpw hpq.1
        have hne : v pq.1 ≠ v pq.2 := fun h => ne_of_lt (hx hlt) (by dsimp only; rw [h])
        have hgt : m < (P'.filter (fun c => dist c (v pq.1) = dist c (v pq.2))).card := by
          dsimp [keep] at hpq; omega
        have hm1 := (Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp (consecPairs_mem hpq.1).1)).2.1
        have hm2 := (Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp (consecPairs_mem hpq.1).2)).2.1
        refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨pq, Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hlt, hgt⟩, rfl⟩, ?_⟩
        exact (mem_perpBisector_iff hne cr.1).mpr (hm1.trans hm2.symm)
      have hinj : Set.InjOn (fun pq : Fin n × Fin n => perpBisector (v pq.1) (v pq.2)) (Sdrop : Set _) := by
        intro pq₁ h1 pq₂ h2 heq
        simp only [Sdrop, Finset.mem_coe, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at h1 h2
        let ℓ := perpBisector (v pq₁.1) (v pq₁.2)
        have hle1 := circle_consecPairs_perpBisector_le_one v hx cr.1 cr.2 (hCr cr hcr) side ℓ
        by_contra hne_pq
        have hnd2 : ((consecPairs (sideIdx cr side)).filter (fun pq => perpBisector (v pq.1) (v pq.2) = ℓ)).Nodup :=
          (consecPairs_nodup hpw).filter _
        have hmem1 : pq₁ ∈ (consecPairs (sideIdx cr side)).filter (fun pq => perpBisector (v pq.1) (v pq.2) = ℓ) :=
          List.mem_filter.mpr ⟨h1.1, by simp [ℓ]⟩
        have hmem2 : pq₂ ∈ (consecPairs (sideIdx cr side)).filter (fun pq => perpBisector (v pq.1) (v pq.2) = ℓ) :=
          List.mem_filter.mpr ⟨h2.1, by simp [ℓ, heq]⟩
        have hcard2 : 2 ≤ ((consecPairs (sideIdx cr side)).filter (fun pq => perpBisector (v pq.1) (v pq.2) = ℓ)).toFinset.card := by
          have hsub : ({pq₁, pq₂} : Finset (Fin n × Fin n)) ⊆
              ((consecPairs (sideIdx cr side)).filter (fun pq => perpBisector (v pq.1) (v pq.2) = ℓ)).toFinset := by
            intro x hx_in; simp only [Finset.mem_insert, Finset.mem_singleton] at hx_in
            rcases hx_in with rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
          calc 2 = ({pq₁, pq₂} : Finset (Fin n × Fin n)).card := (Finset.card_pair hne_pq).symm
            _ ≤ _ := Finset.card_le_card hsub
        rw [List.toFinset_card_of_nodup hnd2] at hcard2
        have hle1' : ((consecPairs (sideIdx cr side)).filter (fun pq => perpBisector (v pq.1) (v pq.2) = ℓ)).length ≤ 1 := by
          convert hle1
        omega
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card (fun ℓ hℓ => by
        obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hℓ; exact hmaps pq hpq)
    have hT := hside_le true; have hF := hside_le false; omega
  -- Sum dropped edges over `cr ∈ C`, then apply Szemerédi–Trotter `m`-Rich Lines!
  let I_rich := ∑ ℓ ∈ L_rich, (P'.filter (· ∈ ℓ)).card
  have hdrop_total :
      (∑ cr ∈ C, (((consecPairs (sideIdx cr true)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length +
                  ((consecPairs (sideIdx cr false)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length)) ≤
        2 * t * I_rich := by
    have h1 : (∑ cr ∈ C, (((consecPairs (sideIdx cr true)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length +
                          ((consecPairs (sideIdx cr false)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length)) ≤
        2 * ∑ cr ∈ C, (L_rich.filter (fun ℓ => cr.1 ∈ ℓ)).card := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun cr hcr => hdrop_per_circle cr hcr
    have h2 : ∑ cr ∈ C, (L_rich.filter (fun ℓ => cr.1 ∈ ℓ)).card ≤ t * I_rich := by
      have hswap : ∑ cr ∈ C, (L_rich.filter (fun ℓ => cr.1 ∈ ℓ)).card =
          ∑ ℓ ∈ L_rich, (C.filter (fun cr => cr.1 ∈ ℓ)).card := by
        simp only [Finset.card_filter]; exact Finset.sum_comm
      rw [hswap, Finset.mul_sum]
      refine Finset.sum_le_sum fun ℓ _ => ?_
      have hsub : C.filter (fun cr => cr.1 ∈ ℓ) ⊆
          (P'.filter (· ∈ ℓ)).biUnion (fun c => ((P'.erase c).image (dist c)).image (fun r => (c, r))) := by
        intro cr hcr
        simp only [Finset.mem_filter] at hcr
        obtain ⟨c, hc, hcr'⟩ := Finset.mem_biUnion.mp hcr.1
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hcr'
        exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, hcr.2⟩, Finset.mem_image.mpr ⟨r, hr, rfl⟩⟩
      calc (C.filter (fun cr => cr.1 ∈ ℓ)).card
          ≤ ((P'.filter (· ∈ ℓ)).biUnion (fun c => ((P'.erase c).image (dist c)).image (fun r => (c, r)))).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ c ∈ P'.filter (· ∈ ℓ), (((P'.erase c).image (dist c)).image (fun r => (c, r))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ c ∈ P'.filter (· ∈ ℓ), ((P'.erase c).image (dist c)).card :=
            Finset.sum_le_sum fun _ _ => Finset.card_image_le
        _ ≤ ∑ _c ∈ P'.filter (· ∈ ℓ), t :=
            Finset.sum_le_sum fun c hc => hP'_pinned c (Finset.mem_filter.mp hc).1
        _ = t * (P'.filter (· ∈ ℓ)).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    calc _ ≤ 2 * ∑ cr ∈ C, (L_rich.filter (fun ℓ => cr.1 ∈ ℓ)).card := h1
      _ ≤ 2 * (t * I_rich) := Nat.mul_le_mul_left 2 h2
      _ = 2 * t * I_rich := by ring
  have hrich := ppl071_szemeredi_trotter_rich_lines P' L_rich hL_rich_dim m (by omega) hL_rich_card
  rw [hP'_card] at hrich
  -- From `m² * I_rich ≤ 256 * n² + 8 * m² * n` and `2116 * t ≤ m²`, deduce `2 * t * I_rich ≤ n² / 4 + 16 * t * n`!
  have hdrop_r : (2 * t * I_rich : ℝ) ≤ (n : ℝ) ^ 2 / 4 + 16 * (t : ℝ) * (n : ℝ) := by
    have hm_pos : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    have hrich_r : (m : ℝ) ^ 2 * (I_rich : ℝ) ≤ 256 * (n : ℝ) ^ 2 + 8 * (m : ℝ) ^ 2 * (n : ℝ) := by
      exact_mod_cast hrich
    have hm2_r : 2116 * (t : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hm_sq
    have hI_le : (I_rich : ℝ) ≤ 256 * (n : ℝ) ^ 2 / (m : ℝ) ^ 2 + 8 * (n : ℝ) := by
      rw [← mul_le_mul_iff_right₀ hm_pos]
      have : (256 * (n : ℝ) ^ 2 / (m : ℝ) ^ 2 + 8 * (n : ℝ)) * (m : ℝ) ^ 2 =
          256 * (n : ℝ) ^ 2 + 8 * (m : ℝ) ^ 2 * (n : ℝ) := by field_simp [ne_of_gt hm_pos]
      linarith
    have hfrac : 2 * (t : ℝ) * (256 * (n : ℝ) ^ 2 / (m : ℝ) ^ 2) ≤ (n : ℝ) ^ 2 / 4 := by
      have h512 : 512 * (t : ℝ) ≤ (m : ℝ) ^ 2 / 4 := by linarith
      have : 2 * (t : ℝ) * (256 * (n : ℝ) ^ 2 / (m : ℝ) ^ 2) =
          (512 * (t : ℝ)) * ((n : ℝ) ^ 2 / (m : ℝ) ^ 2) := by ring
      rw [this]
      have hdiv_nn : (0 : ℝ) ≤ (n : ℝ) ^ 2 / (m : ℝ) ^ 2 := by positivity
      calc (512 * (t : ℝ)) * ((n : ℝ) ^ 2 / (m : ℝ) ^ 2)
          ≤ ((m : ℝ) ^ 2 / 4) * ((n : ℝ) ^ 2 / (m : ℝ) ^ 2) := mul_le_mul_of_nonneg_right h512 hdiv_nn
        _ = (n : ℝ) ^ 2 / 4 := by field_simp [ne_of_gt hm_pos]
    have ht_nn : (0 : ℝ) ≤ 2 * (t : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hI_le ht_nn
    linarith
  -- Hence `E.card ≥ n² / 2`!
  have hE_ge : (n : ℝ) ^ 2 / 2 ≤ (E.card : ℝ) := by
    rw [hsum_inc] at hcount
    have hcount_r : (n : ℝ) * ((n : ℝ) - 1) ≤ (E.card : ℝ) + (2 * t * I_rich : ℝ) + 2 * (n : ℝ) * (t : ℝ) := by
      have h1 : n * (n - 1) ≤ E.card + 2 * t * I_rich + 2 * (n * t) := by
        have h2C := Nat.mul_le_mul_left 2 hC_card
        have hcount' : n * (n - 1) ≤ E.card +
            (∑ cr ∈ C, (((consecPairs (sideIdx cr true)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length +
                        ((consecPairs (sideIdx cr false)).filter (fun pq => ¬ keep cr pq.1 pq.2)).length)) +
            2 * C.card := by convert hcount
        omega
      have h1_r : ((n * (n - 1) : ℕ) : ℝ) ≤ (E.card : ℝ) + (2 * t * I_rich : ℝ) + 2 * ((n : ℝ) * (t : ℝ)) := by
        exact_mod_cast h1
      have hcast : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
      linarith
    have hn_r : (250 : ℝ) < (n : ℝ) := by exact_mod_cast hn_gt250
    have h18 : 18 * (t : ℝ) * (n : ℝ) ≤ 18 / 250 * (n : ℝ) ^ 2 := by nlinarith only [ht_lt_div, hn_r]
    have hn1 : (n : ℝ) ≤ (n : ℝ) ^ 2 / 250 := by nlinarith only [hn_r]
    linarith only [hcount_r, hdrop_r, h18, hn1]
  -- Multiplicity bound on `E`: at most `m`!
  have hmult_m : ∀ i j : Fin n, (E.filter (fun e => e.l = i ∧ e.r = j)).card ≤ m := by
    intro i j
    refine le_trans (hmult i j) ?_
    by_cases hk_ij : (P'.filter (fun c => dist c (v i) = dist c (v j))).card ≤ m
    · refine le_trans (Finset.card_le_card_of_injOn Prod.fst (fun cr hcr => ?_) (fun a ha b hb hfst => ?_)) hk_ij
      · simp only [Finset.mem_coe, Finset.mem_filter] at hcr ⊢
        have hcP' : cr.1 ∈ P' := by
          obtain ⟨c', hc', hcr'⟩ := Finset.mem_biUnion.mp hcr.1
          obtain ⟨r', _, hreq⟩ := Finset.mem_image.mp hcr'
          rw [← congrArg Prod.fst hreq]; exact hc'
        exact ⟨hcP', hcr.2.1.trans hcr.2.2.1.symm⟩
      · simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
        exact Prod.ext hfst (by rw [← ha.2.1, ← hb.2.1, hfst])
    · refine le_trans ?_ (Nat.zero_le m)
      rw [Nat.le_zero, Finset.card_eq_zero]
      ext cr
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _ _ _ hk; exact hk_ij hk
  -- Apply `wiring_multigraph_crossing_lemma` (`m`) and derive a contradiction with `t < n^{4/5} / 250`!
  by_cases hdense : 4 * m * n ≤ E.card
  · have hcl := wiring_multigraph_crossing_lemma (n := n) (E := E) (m := m) W (by omega) hmult_m hdense
    have hW_nt : W.totalSwaps ≤ (n * t) ^ 2 := le_trans hW (Nat.pow_le_pow_left hC_card 2)
    have hE3 : (E.card : ℝ) ^ 3 ≤ 64 * (m : ℝ) * (n : ℝ) ^ 4 * (t : ℝ) ^ 2 := by
      have hnat : E.card ^ 3 ≤ 64 * m * n ^ 4 * t ^ 2 := by
        calc E.card ^ 3 ≤ 64 * m * n ^ 2 * W.totalSwaps := hcl
          _ ≤ 64 * m * n ^ 2 * (n * t) ^ 2 := Nat.mul_le_mul_left _ hW_nt
          _ = 64 * m * n ^ 4 * t ^ 2 := by ring
      exact_mod_cast hnat
    have hE3_lb : (n : ℝ) ^ 6 / 8 ≤ (E.card : ℝ) ^ 3 := by
      have h1 := pow_le_pow_left₀ (by positivity) hE_ge 3
      linarith only [h1, show ((n : ℝ) ^ 2 / 2) ^ 3 = (n : ℝ) ^ 6 / 8 by ring]
    have hn4_pos : (0 : ℝ) < (n : ℝ) ^ 4 := pow_pos (by exact_mod_cast (show 0 < n by omega)) 4
    have hn2_le : (n : ℝ) ^ 2 ≤ 512 * (m : ℝ) * (t : ℝ) ^ 2 := by
      have : (n : ℝ) ^ 4 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 * (512 * (m : ℝ) * (t : ℝ) ^ 2) := by
        linarith only [hE3, hE3_lb]
      exact le_of_mul_le_mul_left this hn4_pos
    have hn2_le' : (n : ℝ) ^ 2 ≤ 24064 * Real.sqrt (t : ℝ) * (t : ℝ) ^ 2 := by
      have h1 : 512 * (m : ℝ) * (t : ℝ) ^ 2 ≤ 512 * (47 * Real.sqrt (t : ℝ)) * (t : ℝ) ^ 2 := by
        have hnn : (0 : ℝ) ≤ 512 * (t : ℝ) ^ 2 := by positivity
        nlinarith only [hm_ub, hnn]
      linarith only [hn2_le, h1]
    have hn4_le : (n : ℝ) ^ 4 ≤ 24064 ^ 2 * (t : ℝ) ^ 5 := by
      have hsq := pow_le_pow_left₀ (sq_nonneg _) hn2_le' 2
      have hrhs : (24064 * Real.sqrt (t : ℝ) * (t : ℝ) ^ 2) ^ 2 = 24064 ^ 2 * (t : ℝ) ^ 5 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
      linarith only [hsq, hrhs]
    -- Yet `t < n^{4/5} / 250` gives `t^5 < n^4 / 250^5`, and `24064^2 < 250^5` (`579,076,096 < 976,562,500,000`)!
    have ht5_lt : (t : ℝ) ^ 5 < (n : ℝ) ^ 4 / 250 ^ 5 := by
      have h1 : (t : ℝ) ^ 5 < ((n : ℝ) ^ (4 / 5 : ℝ) / 250) ^ 5 :=
        pow_lt_pow_left₀ ht_lt (Nat.cast_nonneg _) (by norm_num)
      have hpow : ((n : ℝ) ^ (4 / 5 : ℝ)) ^ 5 = (n : ℝ) ^ 4 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
      rw [div_pow, hpow] at h1; exact h1
    nlinarith only [hn4_le, ht5_lt, hn4_pos]
  · -- Sparse case: `E.card < 4 * m * n`, so `n² / 2 < 4 * m * n`, i.e., `n < 8 * m ≤ 376 * √t`!
    push Not at hdense
    have hE_lt : (E.card : ℝ) < 4 * (m : ℝ) * (n : ℝ) := by exact_mod_cast hdense
    have hn_pos_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn_lt : (n : ℝ) < 8 * (m : ℝ) := by nlinarith only [hE_ge, hE_lt, hn_pos_r]
    have hn_lt2 : (n : ℝ) < 376 * Real.sqrt (t : ℝ) := by linarith only [hn_lt, hm_ub]
    have hn2_lt : (n : ℝ) ^ 2 < 376 ^ 2 * (t : ℝ) := by
      have hsq := pow_lt_pow_left₀ hn_lt2 (le_of_lt hn_pos_r) (by norm_num : 2 ≠ 0)
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hsq; exact hsq
    -- Yet `t < n^{4/5} / 250` gives `n^2 < (376^2 / 250) * n^{4/5}`, i.e. `n^{6/5} < 376^2 / 250`,
    -- so `n^6 < (376^2 / 250)^5`, contradicting `n > 250` (`250^6 > (376^2 / 250)^5`)!
    have hn2_lt2 : (n : ℝ) ^ 2 < (376 ^ 2 / 250) * (n : ℝ) ^ (4 / 5 : ℝ) := by nlinarith only [hn2_lt, ht_lt]
    have hpow5 : ((n : ℝ) ^ 2) ^ 5 < ((376 ^ 2 / 250) * (n : ℝ) ^ (4 / 5 : ℝ)) ^ 5 :=
      pow_lt_pow_left₀ hn2_lt2 (sq_nonneg _) (by norm_num)
    have hpow_r : ((n : ℝ) ^ (4 / 5 : ℝ)) ^ 5 = (n : ℝ) ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
    rw [mul_pow, hpow_r] at hpow5
    have hn4_pos : (0 : ℝ) < (n : ℝ) ^ 4 := pow_pos hn_pos_r 4
    have hn6_lt : (n : ℝ) ^ 6 < (376 ^ 2 / 250 : ℝ) ^ 5 := by
      have : (n : ℝ) ^ 4 * (n : ℝ) ^ 6 < (n : ℝ) ^ 4 * (376 ^ 2 / 250 : ℝ) ^ 5 := by linarith only [hpow5]
      exact lt_of_mul_lt_mul_left this (le_of_lt hn4_pos)
    have hn6_ge : (250 : ℝ) ^ 6 < (n : ℝ) ^ 6 :=
      pow_lt_pow_left₀ (by exact_mod_cast hn_gt250) (by norm_num) (by norm_num)
    norm_num at hn6_lt hn6_ge
    linarith only [hn6_lt, hn6_ge]

/-- **Székely (1997) Global Distinct Distances Lower Bound (`Ω(n^{4/5})`, Pure-Mathlib Public Theorem)**:
Every finite set `P ⊂ ℝ²` with `|P| ≥ 2` determines at least `|P|^{4/5} / 250` distinct positive
pairwise distances! -/
theorem ppl071_szekely_1997_distinct_distances
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (hP : 2 ≤ P.card) :
    (P.card : ℝ) ^ (4 / 5 : ℝ) / 250 ≤
      ((((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)).card : ℝ) := by
  obtain ⟨p, hp, hpin⟩ := ppl071_szekely_1997_pinned_distinct_distances P hP
  refine le_trans hpin ?_
  exact_mod_cast Finset.card_le_card (fun d hd => by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hd
    have hqm := Finset.mem_erase.mp hq
    exact Finset.mem_image.mpr ⟨(p, q),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hqm.2⟩, hqm.1.symm⟩, rfl⟩)


end PPL071
