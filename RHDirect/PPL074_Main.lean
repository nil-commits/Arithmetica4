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
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# PPL 074 & PPL 023 (Erdős Problems #500 & #712): Turán Density of `K_4^3` and `K_k^r`

## Honest Scope & Literature Status
This file formalizes a pure-Mathlib milestone (`0` `sorry`, `0` `native_decide`, `0` custom
definitions in any public theorem signature) for:
- **PPL 074 / Erdős Problem #500** ($500, OPEN): Determine `ex_3(n, K_4^3)` and Turán's conjectured
  density `π(K_4^3) = 5/9`.
- **PPL 023 / Erdős Problem #712** ($500 / $1000, OPEN): Determine `π(K_k^r)` for any `k > r > 2`.

**BOTH open prize problems REMAIN OPEN** as of November 2026 (the sharpest published upper bound is
`π(K_4^3) ≤ 14993367693127837 / 26880000000000000 < 0.557789` by Jeong–Park–Im–Lee–Yang,
arXiv:2609.27495, Sep–Oct 2026). This file does **not** claim to prove `π(K_4^3) = 5/9` or
determine `π(K_k^r)` for any `k > r > 2`.

## Verified Pure-Mathlib Theorems
1. **General Hypergraph Turán Density Framework (Erdős #712 / PPL 023):**
   - `ppl074_katona_nemetz_simonovits_mono`: Monotonicity of normalized extremal density for all
     `1 ≤ r ≤ n`.
   - `ppl074_turan_density_exists`: Existence of `π(K_k^r) ∈ [0, 1]` for all `1 ≤ r ≤ k`.
   - `ppl074_de_caen_k_r_plus_one`: De Caen's (1983) exact finite-`n` bound
     `r^2 * |E| ≤ ((r - 1) * (n - r) + r) * n.choose (r - 1)` for all `r ≥ 2`, `n ≥ r + 1`
     (specializing to Mantel's exact theorem `4 * |E| ≤ n^2` at `r = 2`, and `π(K_{r+1}^r) ≤ 1 - 1/r`
     for all `r ≥ 2`).
2. **Exact Small-`n` Extremal Numbers for `K_4^3` (Erdős #500 / PPL 074):**
   - `ppl074_ex3_4_eq_3`: Exact `ex_3(4, K_4^3) = 3`.
   - `ppl074_ex3_5_eq_7`: Exact `ex_3(5, K_4^3) = 7`.
   - `ppl074_ex3_6_eq_14`: Exact `ex_3(6, K_4^3) = 14` (via Steiner `S(2,3,6)` parity obstruction).
3. **Turán `5/9` Lower Bound & Structural Non-Uniqueness Barriers:**
   - `ppl074_turan_lower_all_n`: Exact universal lower bound `9 * |E| ≥ 5 * n.choose 3` for all `n`.
   - `ppl074_turan_lower_asymptotic`: Asymptotic `5/9` lower bound (`∀ ε > 0, ∀ᶠ n, ...`).
   - `ppl074_fon_der_flaass_k43_free`: Fon-der-Flaass (1988) theorem (every `C_4`-free oriented
     graph yields a `K_4^3`-free 3-graph).
   - `ppl074_brown_non_uniqueness_barrier`: Brown (1983) stability obstruction (`⌊m/2⌋ + 1` pairwise
     non-isomorphic `K_4^3`-free 3-graphs on `3m` vertices all hitting exact Turán count `T(3m)`).
4. **Certified 4-Square Rational Flag-Algebra SOS Upper Bound (`289 / 500 = 0.578`):**
   - `ppl074_flag5_sos_finite_upper`, `ppl074_flag5_sos_density_finite`, and
     `ppl074_density_sandwich_beats_chung_lu` (strictly beating de Caen `5/8` and Chung–Lu
     `(3 + √17) / 12`).
-/

namespace PPL074

open scoped BigOperators
open Filter Finset

/-! ### Section 1: General Hypergraph Turán Framework (Erdős #712 / PPL 023) -/

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
          = ∑ j ∈ s, ((f i : ℤ) ^ 2 - 2 * (f i : ℤ) * (f j : ℤ) + (f j : ℤ) ^ 2) := by
            refine Finset.sum_congr rfl fun j _ => by ring
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
    rw [hmul]
    ring
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
      simp only [Finset.mem_filter] at hp1 hp2
      exact Prod.ext h (hp1.2.symm.trans (h.trans hp2.2))
    · intro x hx; exact ⟨(x, x), by simp [hx], rfl⟩
  rw [Finset.card_product, hdiag] at hsplit
  cases hc : A.card with
  | zero =>
    rw [hc] at hsplit
    simp only [Nat.zero_mul, Nat.add_zero] at hsplit
    exact hsplit
  | succ m =>
    rw [hc] at hsplit
    rw [Nat.add_sub_cancel]
    have hmul : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
    omega

/-- For `r ≤ k`, the empty `r`-graph on `Fin n` is `K_k^r`-free. -/
private lemma empty_k_r_free (n r k : ℕ) (hrk : r ≤ k) :
    (∀ e ∈ (∅ : Finset (Finset (Fin n))), e.card = r) ∧
    (∀ K : Finset (Fin n), K.card = k → ¬ K.powersetCard r ⊆ ∅) := by
  refine ⟨by simp, fun K hK hsub => ?_⟩
  have hpos : 0 < (K.powersetCard r).card := by
    rw [Finset.card_powersetCard, hK]
    exact Nat.choose_pos hrk
  have hzero : (K.powersetCard r).card = 0 := by
    rw [Finset.subset_empty.mp hsub, Finset.card_empty]
  omega

/-- Every `r`-uniform hypergraph on `Fin n` has at most `n.choose r` edges. -/
private lemma uniform_card_le_choose {n r : ℕ} (E : Finset (Finset (Fin n)))
    (hE : ∀ e ∈ E, e.card = r) : E.card ≤ n.choose r := by
  have hsub : E ⊆ (Finset.univ : Finset (Fin n)).powersetCard r := by
    intro e he
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ e, hE e he⟩
  calc E.card ≤ ((Finset.univ : Finset (Fin n)).powersetCard r).card :=
        Finset.card_le_card hsub
    _ = n.choose r := by simp [Finset.card_powersetCard]

/-- The set of achievable cardinalities of `K_k^r`-free `r`-graphs on `Fin n` is bounded above. -/
private lemma ex_set_bddAbove (n r k : ℕ) :
    BddAbove {m : ℕ | ∃ E : Finset (Finset (Fin n)),
      (∀ e ∈ E, e.card = r) ∧
      (∀ K : Finset (Fin n), K.card = k → ¬ K.powersetCard r ⊆ E) ∧
      E.card = m} := by
  refine ⟨n.choose r, ?_⟩
  rintro m ⟨E, hE, _, rfl⟩
  exact uniform_card_le_choose E hE

/-- For `r ≤ k`, the extremal number `ex_r(n, K_k^r)` is attained by some `K_k^r`-free
`r`-graph on `Fin n`. -/
private lemma ex_attained (n r k : ℕ) (hrk : r ≤ k) :
    ∃ E : Finset (Finset (Fin n)),
      (∀ e ∈ E, e.card = r) ∧
      (∀ K : Finset (Fin n), K.card = k → ¬ K.powersetCard r ⊆ E) ∧
      E.card = sSup {m : ℕ | ∃ E' : Finset (Finset (Fin n)),
        (∀ e ∈ E', e.card = r) ∧
        (∀ K : Finset (Fin n), K.card = k → ¬ K.powersetCard r ⊆ E') ∧
        E'.card = m} := by
  set S : Set ℕ := {m : ℕ | ∃ E' : Finset (Finset (Fin n)),
    (∀ e ∈ E', e.card = r) ∧
    (∀ K : Finset (Fin n), K.card = k → ¬ K.powersetCard r ⊆ E') ∧
    E'.card = m}
  have hne : S.Nonempty := ⟨0, ∅, (empty_k_r_free n r k hrk).1,
    (empty_k_r_free n r k hrk).2, Finset.card_empty⟩
  have hmem : sSup S ∈ S := Nat.sSup_mem hne (ex_set_bddAbove n r k)
  rcases hmem with ⟨E, hE, hfree, hcard⟩
  exact ⟨E, hE, hfree, hcard⟩

/-- Key binomial identity: `(n + 1 - r) * (n + 1).choose r = (n + 1) * n.choose r` for `r ≤ n + 1`. -/
private lemma choose_succ_mul_sub (n r : ℕ) (hr : r ≤ n + 1) :
    (n + 1 - r) * (n + 1).choose r = (n + 1) * n.choose r := by
  induction n generalizing r with
  | zero =>
    have : r = 0 ∨ r = 1 := by omega
    rcases this with rfl | rfl <;> simp
  | succ m ih =>
    cases r with
    | zero => simp
    | succ j =>
      have hj : j ≤ m + 1 := by omega
      have h_pas : (m + 2).choose (j + 1) = (m + 1).choose j + (m + 1).choose (j + 1) :=
        Nat.choose_succ_succ (m + 1) j
      have h_id2 : (m + 1).choose (j + 1) * (j + 1) = (m + 1 - j) * (m + 1).choose j := by
        have h := Nat.choose_succ_right_eq (m + 1) j
        linarith
      have h_id3 : (m + 2).choose (j + 1) * (j + 1) = (m + 2) * (m + 1).choose j := by
        rw [h_pas, Nat.add_mul, h_id2]
        have h1 : (m + 1).choose j * (j + 1) + (m + 1 - j) * (m + 1).choose j =
            ((j + 1) + (m + 1 - j)) * (m + 1).choose j := by ring
        rw [h1]
        have h2 : j + 1 + (m + 1 - j) = m + 2 := by omega
        rw [h2]
      have hmul : ((m + 2 - (j + 1)) * (m + 2).choose (j + 1)) * (j + 1) =
                  ((m + 2) * (m + 1).choose (j + 1)) * (j + 1) := by
        have hsub : m + 2 - (j + 1) = m + 1 - j := by omega
        rw [hsub]
        calc (m + 1 - j) * (m + 2).choose (j + 1) * (j + 1)
            = (m + 1 - j) * ((m + 2).choose (j + 1) * (j + 1)) := by ring
          _ = (m + 1 - j) * ((m + 2) * (m + 1).choose j) := by rw [h_id3]
          _ = (m + 2) * ((m + 1 - j) * (m + 1).choose j) := by ring
          _ = (m + 2) * ((m + 1).choose (j + 1) * (j + 1)) := by rw [h_id2]
          _ = (m + 2) * (m + 1).choose (j + 1) * (j + 1) := by ring
      exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos j) hmul

/-- **Katona–Nemetz–Simonovits (1964) Monotonicity**:
Every `K_k^r`-free `r`-uniform hypergraph `E` on `Fin (n + 1)` (with `1 ≤ r ≤ n`) admits a
`K_k^r`-free `r`-uniform hypergraph `E'` on `Fin n` with at least the same normalized edge density:
`E.card * n.choose r ≤ E'.card * (n + 1).choose r`. -/
theorem ppl074_katona_nemetz_simonovits_mono {n r k : ℕ} (_hr : 1 ≤ r) (hrn : r ≤ n)
    (E : Finset (Finset (Fin (n + 1))))
    (hE : ∀ e ∈ E, e.card = r)
    (hfree : ∀ K : Finset (Fin (n + 1)), K.card = k → ¬ K.powersetCard r ⊆ E) :
    ∃ E' : Finset (Finset (Fin n)),
      (∀ e ∈ E', e.card = r) ∧
      (∀ K : Finset (Fin n), K.card = k → ¬ K.powersetCard r ⊆ E') ∧
      E.card * n.choose r ≤ E'.card * (n + 1).choose r := by
  classical
  let Ev : Fin (n + 1) → Finset (Finset (Fin (n + 1))) := fun v => E.filter (fun e => v ∉ e)
  have hsum : ∑ v : Fin (n + 1), (Ev v).card = (n + 1 - r) * E.card := by
    calc ∑ v : Fin (n + 1), (Ev v).card
        = ∑ v : Fin (n + 1), ∑ e ∈ E, if v ∉ e then 1 else 0 := by
          refine Finset.sum_congr rfl fun v _ => ?_
          dsimp only [Ev]
          rw [Finset.card_filter]
      _ = ∑ e ∈ E, ∑ v : Fin (n + 1), if v ∉ e then 1 else 0 := Finset.sum_comm
      _ = ∑ e ∈ E, (n + 1 - r) := by
          refine Finset.sum_congr rfl fun e he => ?_
          have h1 : (∑ v : Fin (n + 1), if v ∉ e then 1 else 0) = (Finset.univ \ e).card := by
            rw [← Finset.card_filter]
            congr 1; ext v; simp
          rw [h1, Finset.card_sdiff_of_subset (Finset.subset_univ e), Finset.card_univ,
            Fintype.card_fin, hE e he]
      _ = E.card * (n + 1 - r) := by rw [Finset.sum_const, smul_eq_mul]
      _ = (n + 1 - r) * E.card := Nat.mul_comm _ _
  have hex_v : ∃ v : Fin (n + 1), (n + 1 - r) * E.card ≤ (n + 1) * (Ev v).card := by
    by_contra h
    push Not at h
    have hlt : ∑ v : Fin (n + 1), (n + 1) * (Ev v).card <
               ∑ _v : Fin (n + 1), (n + 1 - r) * E.card :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun v _ => h v)
    rw [← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at hlt
    exact Nat.lt_irrefl _ hlt
  obtain ⟨v, hv⟩ := hex_v
  let f : Fin n ↪ Fin (n + 1) := Fin.succAboveEmb v
  let E' : Finset (Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)).powersetCard r).filter (fun e => e.map f ∈ E)
  have hE'_unif : ∀ e ∈ E', e.card = r := by
    intro e he
    rw [Finset.mem_filter, Finset.mem_powersetCard] at he
    exact he.1.2
  have hE'_free : ∀ K : Finset (Fin n), K.card = k → ¬ K.powersetCard r ⊆ E' := by
    intro K hK hsub
    apply hfree (K.map f) (by rw [Finset.card_map, hK])
    intro e' he'
    rw [Finset.mem_powersetCard] at he'
    have he_pre : ∃ e : Finset (Fin n), e ⊆ K ∧ e.map f = e' := by
      refine ⟨K.filter (fun x => f x ∈ e'), Finset.filter_subset _ _, ?_⟩
      ext y
      simp only [Finset.mem_map, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨_, hx⟩, rfl⟩; exact hx
      · intro hy
        have hyK : y ∈ K.map f := he'.1 hy
        rw [Finset.mem_map] at hyK
        rcases hyK with ⟨x, hxK, rfl⟩
        exact ⟨x, ⟨hxK, hy⟩, rfl⟩
    obtain ⟨e, heK, rfl⟩ := he_pre
    have he_card : e.card = r := by
      have := he'.2; rwa [Finset.card_map] at this
    have he_mem : e ∈ E' := hsub (Finset.mem_powersetCard.mpr ⟨heK, he_card⟩)
    rw [Finset.mem_filter] at he_mem
    exact he_mem.2
  have hE'_card : E'.card = (Ev v).card := by
    refine Finset.card_bij (fun e _ => e.map f) ?_ ?_ ?_
    · intro e he
      rw [Finset.mem_filter] at he
      rw [Finset.mem_filter]
      refine ⟨he.2, ?_⟩
      intro hvmem
      rw [Finset.mem_map] at hvmem
      rcases hvmem with ⟨x, _, hx⟩
      exact Fin.succAbove_ne v x hx
    · intro e1 _ e2 _ h
      exact Finset.map_injective f h
    · intro e' he'
      rw [Finset.mem_filter] at he'
      rcases he' with ⟨he'E, hvne⟩
      let e : Finset (Fin n) := Finset.univ.filter (fun x => f x ∈ e')
      have hmap : e.map f = e' := by
        ext y
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, e]
        constructor
        · rintro ⟨x, hx, rfl⟩; exact hx
        · intro hy
          have hyv : y ≠ v := fun h => hvne (h ▸ hy)
          obtain ⟨x, rfl⟩ := Fin.exists_succAbove_eq hyv
          exact ⟨x, hy, rfl⟩
      have hcard : e.card = r := by
        have := hE e' he'E
        rw [← hmap, Finset.card_map] at this
        exact this
      refine ⟨e, ?_, hmap⟩
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ e, hcard⟩, hmap.symm ▸ he'E⟩
  refine ⟨E', hE'_unif, hE'_free, ?_⟩
  rw [hE'_card]
  have hbin : (n + 1 - r) * (n + 1).choose r = (n + 1) * n.choose r :=
    choose_succ_mul_sub n r (by omega)
  have hmul : (n + 1) * (E.card * n.choose r) ≤ (n + 1) * ((Ev v).card * (n + 1).choose r) := by
    calc (n + 1) * (E.card * n.choose r)
        = E.card * ((n + 1) * n.choose r) := by ring
      _ = E.card * ((n + 1 - r) * (n + 1).choose r) := by rw [← hbin]
      _ = ((n + 1 - r) * E.card) * (n + 1).choose r := by ring
      _ ≤ ((n + 1) * (Ev v).card) * (n + 1).choose r := Nat.mul_le_mul_right _ hv
      _ = (n + 1) * ((Ev v).card * (n + 1).choose r) := by ring
  exact Nat.le_of_mul_le_mul_left hmul (Nat.succ_pos n)

/-- **Existence of Hypergraph Turán Density (Erdős #712 / PPL 023)**:
For all `1 ≤ r ≤ k`, the normalized extremal density `ex_r(n, K_k^r) / n.choose r` converges to a
limit `π ∈ [0, 1]` as `n → ∞`. -/
theorem ppl074_turan_density_exists (r k : ℕ) (hr : 1 ≤ r) (hrk : r ≤ k) :
    ∃ π ∈ Set.Icc (0 : ℝ) 1,
      Filter.Tendsto
        (fun n : ℕ =>
          ((sSup {m : ℕ | ∃ E : Finset (Finset (Fin n)),
            (∀ e ∈ E, e.card = r) ∧
            (∀ K : Finset (Fin n), K.card = k → ¬ K.powersetCard r ⊆ E) ∧
            E.card = m} : ℕ) : ℝ) / (n.choose r : ℝ))
        Filter.atTop (nhds π) := by
  let ex : ℕ → ℕ := fun n =>
    sSup {m : ℕ | ∃ E : Finset (Finset (Fin n)),
      (∀ e ∈ E, e.card = r) ∧
      (∀ K : Finset (Fin n), K.card = k → ¬ K.powersetCard r ⊆ E) ∧
      E.card = m}
  let d : ℕ → ℝ := fun n => (ex n : ℝ) / (n.choose r : ℝ)
  have hd_nonneg : ∀ n, 0 ≤ d n := fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hd_le_one : ∀ n, d n ≤ 1 := by
    intro n
    by_cases h0 : (n.choose r : ℝ) = 0
    · simp [d, h0]
    · have hpos : 0 < (n.choose r : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h0)
      rw [div_le_one hpos]
      obtain ⟨E, hE, _, hcard⟩ := ex_attained n r k hrk
      exact_mod_cast (hcard ▸ uniform_card_le_choose E hE)
  have hd_step : ∀ n ≥ r, d (n + 1) ≤ d n := by
    intro n hn
    obtain ⟨E, hE, hfree, hcard⟩ := ex_attained (n + 1) r k hrk
    obtain ⟨E', hE', hfree', hmono⟩ := ppl074_katona_nemetz_simonovits_mono hr hn E hE hfree
    have hE'_le : E'.card ≤ ex n :=
      le_csSup (ex_set_bddAbove n r k) ⟨E', hE', hfree', rfl⟩
    have hnat : ex (n + 1) * n.choose r ≤ ex n * (n + 1).choose r := by
      calc ex (n + 1) * n.choose r
          = E.card * n.choose r := by rw [hcard]
        _ ≤ E'.card * (n + 1).choose r := hmono
        _ ≤ ex n * (n + 1).choose r := Nat.mul_le_mul_right _ hE'_le
    have hpos1 : (0 : ℝ) < (n.choose r : ℝ) := by exact_mod_cast Nat.choose_pos hn
    have hpos2 : (0 : ℝ) < ((n + 1).choose r : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
    dsimp [d]
    rw [div_le_div_iff₀ hpos2 hpos1]
    exact_mod_cast hnat
  let d' : ℕ → ℝ := fun m => d (m + r)
  have hd'_anti : Antitone d' := antitone_nat_of_succ_le (fun m => by
    show d (m + 1 + r) ≤ d (m + r)
    rw [Nat.add_right_comm m 1 r]
    exact hd_step (m + r) (by omega))
  have hd'_bdd : BddBelow (Set.range d') := ⟨0, by rintro _ ⟨m, rfl⟩; exact hd_nonneg _⟩
  have htend' : Filter.Tendsto d' Filter.atTop (nhds (⨅ m, d' m)) :=
    tendsto_atTop_ciInf hd'_anti hd'_bdd
  have htend : Filter.Tendsto d Filter.atTop (nhds (⨅ m, d' m)) :=
    (Filter.tendsto_add_atTop_iff_nat r).mp htend'
  refine ⟨⨅ m, d' m, ⟨?_, ?_⟩, htend⟩
  · exact le_ciInf (fun m => hd_nonneg _)
  · exact ciInf_le_of_le hd'_bdd 0 (hd_le_one _)

/-- **De Caen (1983) Exact Bound for `K_{r+1}^r`** (covers all `r ≥ 2`, Erdős #712):
For any `r ≥ 2`, `n ≥ r + 1`, and any `K_{r+1}^r`-free `r`-uniform hypergraph `E` on `Fin n`:
`r^2 * E.card ≤ ((r - 1) * (n - r) + r) * n.choose (r - 1)`. -/
theorem ppl074_de_caen_k_r_plus_one {n r : ℕ} (hr : 2 ≤ r) (_hn : r + 1 ≤ n)
    (E : Finset (Finset (Fin n)))
    (hE : ∀ e ∈ E, e.card = r)
    (hfree : ∀ K : Finset (Fin n), K.card = r + 1 → ¬ K.powersetCard r ⊆ E) :
    r ^ 2 * E.card ≤ ((r - 1) * (n - r) + r) * n.choose (r - 1) := by
  classical
  let P : Finset (Finset (Fin n) × Finset (Fin n)) :=
    (E ×ˢ E).filter (fun p => p.1 ≠ p.2 ∧ (p.1 ∩ p.2).card = r - 1)
  have hinter_iff : ∀ e1 ∈ E, ∀ e2 ∈ E, e1 ≠ e2 →
      ((e1 ∩ e2).card = r - 1 ↔ (e1 ∪ e2).card = r + 1) := by
    intro e1 h1 e2 h2 _
    have hcu := Finset.card_union_add_card_inter e1 e2
    rw [hE e1 h1, hE e2 h2] at hcu
    omega
  let deg : Finset (Fin n) → ℕ := fun S => (E.filter (fun e => S ⊆ e)).card
  have hsum_deg : ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (r - 1), deg S =
      r * E.card := by
    calc ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (r - 1), deg S
        = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (r - 1),
            ∑ e ∈ E, if S ⊆ e then 1 else 0 := by
          refine Finset.sum_congr rfl fun S _ => ?_
          dsimp only [deg]; rw [Finset.card_filter]
      _ = ∑ e ∈ E, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (r - 1),
            if S ⊆ e then 1 else 0 := Finset.sum_comm
      _ = ∑ e ∈ E, r := by
          refine Finset.sum_congr rfl fun e he => ?_
          have hflt : ((Finset.univ : Finset (Fin n)).powersetCard (r - 1)).filter (fun S => S ⊆ e) =
              e.powersetCard (r - 1) := by
            ext S
            simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
            tauto
          rw [← Finset.card_filter, hflt, Finset.card_powersetCard, hE e he]
          rcases Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0) with ⟨r', hr'⟩
          rw [hr', Nat.succ_sub_one]
          exact Nat.choose_succ_self_right r'
      _ = E.card * r := by rw [Finset.sum_const, smul_eq_mul]
      _ = r * E.card := Nat.mul_comm _ _
  have hP_inter : P.card =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (r - 1), deg S * (deg S - 1) := by
    have hdisj : P = ((Finset.univ : Finset (Fin n)).powersetCard (r - 1)).biUnion
        (fun S => ((E.filter (fun e => S ⊆ e)) ×ˢ (E.filter (fun e => S ⊆ e))).filter
          (fun p => p.1 ≠ p.2)) := by
      ext ⟨e1, e2⟩
      simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
        Finset.mem_powersetCard, Finset.subset_univ, true_and]
      constructor
      · rintro ⟨⟨h1, h2⟩, hne, hcard⟩
        exact ⟨e1 ∩ e2, hcard, ⟨⟨h1, Finset.inter_subset_left⟩, ⟨h2, Finset.inter_subset_right⟩⟩, hne⟩
      · rintro ⟨S, hScard, ⟨⟨h1, hS1⟩, ⟨h2, hS2⟩⟩, hne⟩
        refine ⟨⟨h1, h2⟩, hne, ?_⟩
        have hSsub : S ⊆ e1 ∩ e2 := Finset.subset_inter hS1 hS2
        have hlt : (e1 ∩ e2).card < r := by
          have hle : (e1 ∩ e2).card ≤ r := by
            calc (e1 ∩ e2).card ≤ e1.card := Finset.card_le_card Finset.inter_subset_left
              _ = r := hE e1 h1
          by_contra hge
          have heq : (e1 ∩ e2).card = r := by omega
          have he1 : e1 ∩ e2 = e1 :=
            Finset.eq_of_subset_of_card_le (Finset.inter_subset_left (s₁ := e1) (s₂ := e2))
              (by rw [heq, hE e1 h1])
          have he2 : e1 ∩ e2 = e2 :=
            Finset.eq_of_subset_of_card_le (Finset.inter_subset_right (s₁ := e1) (s₂ := e2))
              (by rw [heq, hE e2 h2])
          exact hne (he1.symm.trans he2)
        have hge : r - 1 ≤ (e1 ∩ e2).card := hScard ▸ Finset.card_le_card hSsub
        omega
    rw [hdisj, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun S _ => card_off_diag (E.filter (fun e => S ⊆ e))
    · intro S1 hS1 S2 hS2 hne
      rw [Function.onFun, Finset.disjoint_left]
      intro ⟨e1, e2⟩ hp1 hp2
      simp only [Finset.mem_filter, Finset.mem_product] at hp1 hp2
      rw [Finset.mem_coe, Finset.mem_powersetCard] at hS1 hS2
      have hlt : (e1 ∩ e2).card < r := by
        have hle : (e1 ∩ e2).card ≤ r := by
          calc (e1 ∩ e2).card ≤ e1.card := Finset.card_le_card Finset.inter_subset_left
            _ = r := hE e1 hp1.1.1.1
        by_contra hge
        have heq : (e1 ∩ e2).card = r := by omega
        have he1 := Finset.eq_of_subset_of_card_le (Finset.inter_subset_left (s₁ := e1) (s₂ := e2))
          (by rw [heq, hE e1 hp1.1.1.1])
        have he2 := Finset.eq_of_subset_of_card_le (Finset.inter_subset_right (s₁ := e1) (s₂ := e2))
          (by rw [heq, hE e2 hp1.1.2.1])
        exact hp1.2 (he1.symm.trans he2)
      have hsub1 : S1 ⊆ e1 ∩ e2 := Finset.subset_inter hp1.1.1.2 hp1.1.2.2
      have hsub2 : S2 ⊆ e1 ∩ e2 := Finset.subset_inter hp2.1.1.2 hp2.1.2.2
      have hcard_i : (e1 ∩ e2).card = r - 1 := by
        have := Finset.card_le_card hsub1; omega
      have heq1 : S1 = e1 ∩ e2 := Finset.eq_of_subset_of_card_le hsub1 (by omega)
      have heq2 : S2 = e1 ∩ e2 := Finset.eq_of_subset_of_card_le hsub2 (by omega)
      exact hne (heq1.trans heq2.symm)
  let cnt : Finset (Fin n) → ℕ := fun Q => (E.filter (fun e => e ⊆ Q)).card
  have hsum_cnt : ∑ Q ∈ (Finset.univ : Finset (Fin n)).powersetCard (r + 1), cnt Q =
      (n - r) * E.card := by
    calc ∑ Q ∈ (Finset.univ : Finset (Fin n)).powersetCard (r + 1), cnt Q
        = ∑ Q ∈ (Finset.univ : Finset (Fin n)).powersetCard (r + 1),
            ∑ e ∈ E, if e ⊆ Q then 1 else 0 := by
          refine Finset.sum_congr rfl fun Q _ => ?_
          dsimp only [cnt]; rw [Finset.card_filter]
      _ = ∑ e ∈ E, ∑ Q ∈ (Finset.univ : Finset (Fin n)).powersetCard (r + 1),
            if e ⊆ Q then 1 else 0 := Finset.sum_comm
      _ = ∑ e ∈ E, (n - r) := by
          refine Finset.sum_congr rfl fun e he => ?_
          rw [← Finset.card_filter]
          have hbij : (Finset.univ \ e).card =
              (((Finset.univ : Finset (Fin n)).powersetCard (r + 1)).filter
                (fun Q => e ⊆ Q)).card := by
            refine Finset.card_bij (fun v _ => insert v e) ?_ ?_ ?_
            · intro v hv
              rw [Finset.mem_sdiff] at hv
              rw [Finset.mem_filter, Finset.mem_powersetCard]
              refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.subset_insert v e⟩
              rw [Finset.card_insert_of_notMem hv.2, hE e he]
            · intro v1 hv1 v2 hv2 heq
              rw [Finset.mem_sdiff] at hv1 hv2
              have hv1in : v1 ∈ insert v2 e := heq ▸ Finset.mem_insert_self v1 e
              rcases Finset.mem_insert.mp hv1in with h | h
              · exact h
              · exact absurd h hv1.2
            · intro Q hQ
              rw [Finset.mem_filter, Finset.mem_powersetCard] at hQ
              have hdiff_card : (Q \ e).card = 1 := by
                rw [Finset.card_sdiff_of_subset hQ.2, hQ.1.2, hE e he]; omega
              obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdiff_card
              have hvmem : v ∈ Q \ e := hv ▸ Finset.mem_singleton_self v
              rw [Finset.mem_sdiff] at hvmem
              refine ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvmem.2⟩, ?_⟩
              ext x
              simp only [Finset.mem_insert]
              constructor
              · rintro (rfl | hx); exact hvmem.1; exact hQ.2 hx
              · intro hx
                by_cases hxe : x ∈ e
                · exact Or.inr hxe
                · left
                  have : x ∈ Q \ e := Finset.mem_sdiff.mpr ⟨hx, hxe⟩
                  rw [hv, Finset.mem_singleton] at this
                  exact this
          rw [← hbij, Finset.card_sdiff_of_subset (Finset.subset_univ e), Finset.card_univ,
            Fintype.card_fin, hE e he]
      _ = E.card * (n - r) := by rw [Finset.sum_const, smul_eq_mul]
      _ = (n - r) * E.card := Nat.mul_comm _ _
  have hP_union : P.card =
      ∑ Q ∈ (Finset.univ : Finset (Fin n)).powersetCard (r + 1), cnt Q * (cnt Q - 1) := by
    have hdisj : P = ((Finset.univ : Finset (Fin n)).powersetCard (r + 1)).biUnion
        (fun Q => ((E.filter (fun e => e ⊆ Q)) ×ˢ (E.filter (fun e => e ⊆ Q))).filter
          (fun p => p.1 ≠ p.2)) := by
      ext ⟨e1, e2⟩
      simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
        Finset.mem_powersetCard, Finset.subset_univ, true_and]
      constructor
      · rintro ⟨⟨h1, h2⟩, hne, hcard⟩
        have hu := (hinter_iff e1 h1 e2 h2 hne).mp hcard
        exact ⟨e1 ∪ e2, hu, ⟨⟨h1, Finset.subset_union_left⟩, ⟨h2, Finset.subset_union_right⟩⟩, hne⟩
      · rintro ⟨Q, hQcard, ⟨⟨h1, h1Q⟩, ⟨h2, h2Q⟩⟩, hne⟩
        refine ⟨⟨h1, h2⟩, hne, ?_⟩
        rw [hinter_iff e1 h1 e2 h2 hne]
        have hu_sub : e1 ∪ e2 ⊆ Q := Finset.union_subset h1Q h2Q
        have hu_le : (e1 ∪ e2).card ≤ r + 1 := hQcard ▸ Finset.card_le_card hu_sub
        have hu_gt : r < (e1 ∪ e2).card := by
          by_contra hle
          have heq : (e1 ∪ e2).card = r := by
            have := Finset.card_le_card (Finset.subset_union_left (s₁ := e1) (s₂ := e2))
            rw [hE e1 h1] at this; omega
          have he1 := Finset.eq_of_subset_of_card_le (Finset.subset_union_left (s₁ := e1) (s₂ := e2))
            (by rw [heq, hE e1 h1])
          have he2 := Finset.eq_of_subset_of_card_le (Finset.subset_union_right (s₁ := e1) (s₂ := e2))
            (by rw [heq, hE e2 h2])
          exact hne (he1.trans he2.symm)
        omega
    rw [hdisj, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun Q _ => card_off_diag (E.filter (fun e => e ⊆ Q))
    · intro Q1 hQ1 Q2 hQ2 hne
      rw [Function.onFun, Finset.disjoint_left]
      intro ⟨e1, e2⟩ hp1 hp2
      simp only [Finset.mem_filter, Finset.mem_product] at hp1 hp2
      rw [Finset.mem_coe, Finset.mem_powersetCard] at hQ1 hQ2
      have hu_gt : r < (e1 ∪ e2).card := by
        by_contra hle
        have heq : (e1 ∪ e2).card = r := by
          have := Finset.card_le_card (Finset.subset_union_left (s₁ := e1) (s₂ := e2))
          rw [hE e1 hp1.1.1.1] at this; omega
        have he1 := Finset.eq_of_subset_of_card_le (Finset.subset_union_left (s₁ := e1) (s₂ := e2))
          (by rw [heq, hE e1 hp1.1.1.1])
        have he2 := Finset.eq_of_subset_of_card_le (Finset.subset_union_right (s₁ := e1) (s₂ := e2))
          (by rw [heq, hE e2 hp1.1.2.1])
        exact hp1.2 (he1.trans he2.symm)
      have hsub1 : e1 ∪ e2 ⊆ Q1 := Finset.union_subset hp1.1.1.2 hp1.1.2.2
      have hsub2 : e1 ∪ e2 ⊆ Q2 := Finset.union_subset hp2.1.1.2 hp2.1.2.2
      have hcu : (e1 ∪ e2).card = r + 1 := by
        have := Finset.card_le_card hsub1; omega
      have heq1 := Finset.eq_of_subset_of_card_le hsub1 (by omega)
      have heq2 := Finset.eq_of_subset_of_card_le hsub2 (by omega)
      exact hne (heq1.symm.trans heq2)
  have hcnt_le : ∀ Q ∈ (Finset.univ : Finset (Fin n)).powersetCard (r + 1), cnt Q ≤ r := by
    intro Q hQ
    rw [Finset.mem_powersetCard] at hQ
    have hsub : E.filter (fun e => e ⊆ Q) ⊆ Q.powersetCard r := by
      intro e he
      rw [Finset.mem_filter] at he
      exact Finset.mem_powersetCard.mpr ⟨he.2, hE e he.1⟩
    have hle : cnt Q ≤ r + 1 := by
      calc cnt Q ≤ (Q.powersetCard r).card := Finset.card_le_card hsub
        _ = (r + 1).choose r := by rw [Finset.card_powersetCard, hQ.2]
        _ = r + 1 := Nat.choose_succ_self_right r
    by_contra hgt
    have heq : (E.filter (fun e => e ⊆ Q)).card = r + 1 := by dsimp [cnt] at hle hgt; omega
    have hfull : E.filter (fun e => e ⊆ Q) = Q.powersetCard r :=
      Finset.eq_of_subset_of_card_le hsub
        (by rw [Finset.card_powersetCard, hQ.2, Nat.choose_succ_self_right, heq])
    apply hfree Q hQ.2
    rw [← hfull]
    exact Finset.filter_subset _ _
  have hP_upper : P.card ≤ (r - 1) * (n - r) * E.card := by
    rw [hP_union]
    calc ∑ Q ∈ (Finset.univ : Finset (Fin n)).powersetCard (r + 1), cnt Q * (cnt Q - 1)
        ≤ ∑ Q ∈ (Finset.univ : Finset (Fin n)).powersetCard (r + 1), (r - 1) * cnt Q := by
          refine Finset.sum_le_sum fun Q hQ => ?_
          have hc := hcnt_le Q hQ
          calc cnt Q * (cnt Q - 1) ≤ cnt Q * (r - 1) := Nat.mul_le_mul_left _ (by omega)
            _ = (r - 1) * cnt Q := Nat.mul_comm _ _
      _ = (r - 1) * ∑ Q ∈ (Finset.univ : Finset (Fin n)).powersetCard (r + 1), cnt Q := by
          rw [← Finset.mul_sum]
      _ = (r - 1) * ((n - r) * E.card) := by rw [hsum_cnt]
      _ = (r - 1) * (n - r) * E.card := by ring
  have hCS : (r * E.card) ^ 2 ≤ n.choose (r - 1) *
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (r - 1), deg S ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq_nat
      ((Finset.univ : Finset (Fin n)).powersetCard (r - 1)) deg
    rw [hsum_deg, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h
    exact h
  have hsum_sq : ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (r - 1), deg S ^ 2 =
      P.card + r * E.card := by
    rw [hP_inter, ← hsum_deg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    cases h : deg S with
    | zero => simp
    | succ m =>
      rw [Nat.add_sub_cancel]
      ring
  rw [hsum_sq] at hCS
  by_cases hE0 : E.card = 0
  · simp [hE0]
  · have hpos : 0 < E.card := Nat.pos_of_ne_zero hE0
    have hstep : (r ^ 2 * E.card) * E.card ≤
        (((r - 1) * (n - r) + r) * n.choose (r - 1)) * E.card := by
      calc (r ^ 2 * E.card) * E.card
          = (r * E.card) ^ 2 := by ring
        _ ≤ n.choose (r - 1) * (P.card + r * E.card) := hCS
        _ ≤ n.choose (r - 1) * ((r - 1) * (n - r) * E.card + r * E.card) :=
            Nat.mul_le_mul_left _ (Nat.add_le_add_right hP_upper _)
        _ = (((r - 1) * (n - r) + r) * n.choose (r - 1)) * E.card := by ring
    exact Nat.le_of_mul_le_mul_right hstep hpos

/-- **Mantel's Theorem** as the `r = 2` specialization of `ppl074_de_caen_k_r_plus_one`. -/
theorem ppl074_mantel_from_de_caen {n : ℕ} (hn : 3 ≤ n)
    (E : Finset (Finset (Fin n)))
    (hE : ∀ e ∈ E, e.card = 2)
    (hfree : ∀ K : Finset (Fin n), K.card = 3 → ¬ K.powersetCard 2 ⊆ E) :
    4 * E.card ≤ n ^ 2 := by
  have h := ppl074_de_caen_k_r_plus_one (r := 2) (by omega) hn E hE hfree
  have hch : n.choose (2 - 1) = n := Nat.choose_one_right n
  have hsub : (2 - 1) * (n - 2) + 2 = n := by omega
  rw [hch, hsub] at h
  nlinarith

/-! ### Section 2: Exact Small-`n` Extremal Numbers for `K_4^3` (`n = 4, 5, 6`) -/

/-- Exact `ex_3(4, K_4^3) = 3`. -/
theorem ppl074_ex3_4_eq_3 :
    (∀ E : Finset (Finset (Fin 4)),
      (∀ e ∈ E, e.card = 3) →
      (∀ K : Finset (Fin 4), K.card = 4 → ¬ K.powersetCard 3 ⊆ E) →
      E.card ≤ 3) ∧
    (∃ E : Finset (Finset (Fin 4)),
      (∀ e ∈ E, e.card = 3) ∧
      (∀ K : Finset (Fin 4), K.card = 4 → ¬ K.powersetCard 3 ⊆ E) ∧
      E.card = 3) := by
  constructor
  · intro E hE hfree
    have hle : E.card ≤ 4 := by simpa using uniform_card_le_choose E hE
    by_contra hgt
    have heq : E.card = 4 := by omega
    have hsub : E ⊆ (Finset.univ : Finset (Fin 4)).powersetCard 3 := by
      intro e he; exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, hE e he⟩
    have hfull := Finset.eq_of_subset_of_card_le hsub (by simp [heq])
    exact hfree Finset.univ (by simp) (hfull ▸ Subset.rfl)
  · let e0 : Finset (Fin 4) := {0, 1, 2}
    let E : Finset (Finset (Fin 4)) := ((Finset.univ : Finset (Fin 4)).powersetCard 3).erase e0
    have he0 : e0 ∈ (Finset.univ : Finset (Fin 4)).powersetCard 3 := by decide
    refine ⟨E, ?_, ?_, ?_⟩
    · intro e he
      exact (Finset.mem_powersetCard.mp (Finset.mem_of_mem_erase he)).2
    · intro K hK hsub
      have hKuniv : K = Finset.univ :=
        Finset.eq_of_subset_of_card_le (Finset.subset_univ K) (by simp [hK])
      subst hKuniv
      have : e0 ∈ E := hsub he0
      exact Finset.notMem_erase e0 _ this
    · rw [Finset.card_erase_of_mem he0]; decide

/-- Exact `ex_3(5, K_4^3) = 7`. -/
theorem ppl074_ex3_5_eq_7 :
    (∀ E : Finset (Finset (Fin 5)),
      (∀ e ∈ E, e.card = 3) →
      (∀ K : Finset (Fin 5), K.card = 4 → ¬ K.powersetCard 3 ⊆ E) →
      E.card ≤ 7) ∧
    (∃ E : Finset (Finset (Fin 5)),
      (∀ e ∈ E, e.card = 3) ∧
      (∀ K : Finset (Fin 5), K.card = 4 → ¬ K.powersetCard 3 ⊆ E) ∧
      E.card = 7) := by
  classical
  constructor
  · intro E hE hfree
    let F : Finset (Finset (Fin 5)) := ((Finset.univ : Finset (Fin 5)).powersetCard 3) \ E
    have hEsub : E ⊆ (Finset.univ : Finset (Fin 5)).powersetCard 3 := fun e he =>
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, hE e he⟩
    have hFcard : F.card + E.card = 10 := by
      have h := Finset.card_sdiff_add_card_eq_card hEsub
      have hc : ((Finset.univ : Finset (Fin 5)).powersetCard 3).card = 10 := by decide
      rw [hc] at h
      exact h
    have hhit : ∀ Q ∈ (Finset.univ : Finset (Fin 5)).powersetCard 4,
        1 ≤ (F.filter (fun e => e ⊆ Q)).card := by
      intro Q hQ
      rw [Finset.mem_powersetCard] at hQ
      obtain ⟨e, heQ, heE⟩ := Finset.not_subset.mp (hfree Q hQ.2)
      rw [Finset.mem_powersetCard] at heQ
      have heF : e ∈ F := Finset.mem_sdiff.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, heQ.2⟩, heE⟩
      exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heF, heQ.1⟩⟩
    have h5le : 5 ≤ ∑ Q ∈ (Finset.univ : Finset (Fin 5)).powersetCard 4,
        (F.filter (fun e => e ⊆ Q)).card := by
      calc 5 = ∑ _Q ∈ (Finset.univ : Finset (Fin 5)).powersetCard 4, 1 := by decide
        _ ≤ _ := Finset.sum_le_sum hhit
    have hdouble : ∑ Q ∈ (Finset.univ : Finset (Fin 5)).powersetCard 4,
        (F.filter (fun e => e ⊆ Q)).card = 2 * F.card := by
      calc ∑ Q ∈ (Finset.univ : Finset (Fin 5)).powersetCard 4,
              (F.filter (fun e => e ⊆ Q)).card
          = ∑ Q ∈ (Finset.univ : Finset (Fin 5)).powersetCard 4,
              ∑ e ∈ F, if e ⊆ Q then 1 else 0 := by
            refine Finset.sum_congr rfl fun Q _ => ?_; rw [Finset.card_filter]
        _ = ∑ e ∈ F, ∑ Q ∈ (Finset.univ : Finset (Fin 5)).powersetCard 4,
              if e ⊆ Q then 1 else 0 := Finset.sum_comm
        _ = ∑ e ∈ F, 2 := by
            refine Finset.sum_congr rfl fun e he => ?_
            have hec : e.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp he).1).2
            rw [← Finset.card_filter]
            have hbij : (Finset.univ \ e).card =
                (((Finset.univ : Finset (Fin 5)).powersetCard 4).filter (fun Q => e ⊆ Q)).card := by
              refine Finset.card_bij (fun v _ => insert v e) ?_ ?_ ?_
              · intro v hv
                rw [Finset.mem_sdiff] at hv
                rw [Finset.mem_filter, Finset.mem_powersetCard]
                exact ⟨⟨Finset.subset_univ _, by rw [Finset.card_insert_of_notMem hv.2, hec]⟩,
                  Finset.subset_insert v e⟩
              · intro v1 hv1 v2 hv2 heq
                rw [Finset.mem_sdiff] at hv1 hv2
                rcases Finset.mem_insert.mp (heq ▸ Finset.mem_insert_self v1 e) with h | h
                · exact h
                · exact absurd h hv1.2
              · intro Q hQ
                rw [Finset.mem_filter, Finset.mem_powersetCard] at hQ
                have hdc : (Q \ e).card = 1 := by
                  rw [Finset.card_sdiff_of_subset hQ.2, hQ.1.2, hec]
                obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdc
                have hvm := Finset.mem_sdiff.mp (hv ▸ Finset.mem_singleton_self v)
                refine ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvm.2⟩, ?_⟩
                ext x; simp only [Finset.mem_insert]
                constructor
                · rintro (rfl | hx); exact hvm.1; exact hQ.2 hx
                · intro hx
                  by_cases hxe : x ∈ e
                  · exact Or.inr hxe
                  · left; have := Finset.mem_sdiff.mpr ⟨hx, hxe⟩; rw [hv, Finset.mem_singleton] at this; exact this
            rw [← hbij, Finset.card_sdiff_of_subset (Finset.subset_univ e), Finset.card_univ,
              Fintype.card_fin, hec]
        _ = F.card * 2 := by rw [Finset.sum_const, smul_eq_mul]
        _ = 2 * F.card := Nat.mul_comm _ _
    omega
  · let miss : Finset (Finset (Fin 5)) := {{0, 1, 4}, {0, 2, 3}, {1, 2, 3}}
    let E : Finset (Finset (Fin 5)) := ((Finset.univ : Finset (Fin 5)).powersetCard 3) \ miss
    refine ⟨E, ?_, ?_, ?_⟩
    · intro e he; exact (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp he).1).2
    · intro K hK hsub
      have hcheck : ∀ Q ∈ (Finset.univ : Finset (Fin 5)).powersetCard 4,
          ¬ Q.powersetCard 3 ⊆ E := by decide
      exact hcheck K (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ K, hK⟩) hsub
    · decide

/-- Exact `ex_3(6, K_4^3) = 14` (proved via Steiner `S(2,3,6)` parity obstruction). -/
theorem ppl074_ex3_6_eq_14 :
    (∀ E : Finset (Finset (Fin 6)),
      (∀ e ∈ E, e.card = 3) →
      (∀ K : Finset (Fin 6), K.card = 4 → ¬ K.powersetCard 3 ⊆ E) →
      E.card ≤ 14) ∧
    (∃ E : Finset (Finset (Fin 6)),
      (∀ e ∈ E, e.card = 3) ∧
      (∀ K : Finset (Fin 6), K.card = 4 → ¬ K.powersetCard 3 ⊆ E) ∧
      E.card = 14) := by
  classical
  constructor
  · intro E hE hfree
    let F : Finset (Finset (Fin 6)) := ((Finset.univ : Finset (Fin 6)).powersetCard 3) \ E
    have hEsub : E ⊆ (Finset.univ : Finset (Fin 6)).powersetCard 3 := fun e he =>
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, hE e he⟩
    have hFcard : F.card + E.card = 20 := by
      have h := Finset.card_sdiff_add_card_eq_card hEsub
      have hc : ((Finset.univ : Finset (Fin 6)).powersetCard 3).card = 20 := by decide
      rw [hc] at h
      exact h
    have hFunif : ∀ e ∈ F, e.card = 3 := fun e he =>
      (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp he).1).2
    have hhit : ∀ Q ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
        1 ≤ (F.filter (fun e => e ⊆ Q)).card := by
      intro Q hQ
      rw [Finset.mem_powersetCard] at hQ
      obtain ⟨e, heQ, heE⟩ := Finset.not_subset.mp (hfree Q hQ.2)
      rw [Finset.mem_powersetCard] at heQ
      have heF : e ∈ F := Finset.mem_sdiff.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, heQ.2⟩, heE⟩
      exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heF, heQ.1⟩⟩
    have hdouble : ∑ Q ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
        (F.filter (fun e => e ⊆ Q)).card = 3 * F.card := by
      calc ∑ Q ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
              (F.filter (fun e => e ⊆ Q)).card
          = ∑ Q ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
              ∑ e ∈ F, if e ⊆ Q then 1 else 0 := by
            refine Finset.sum_congr rfl fun Q _ => ?_; rw [Finset.card_filter]
        _ = ∑ e ∈ F, ∑ Q ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
              if e ⊆ Q then 1 else 0 := Finset.sum_comm
        _ = ∑ e ∈ F, 3 := by
            refine Finset.sum_congr rfl fun e he => ?_
            have hec := hFunif e he
            rw [← Finset.card_filter]
            have hbij : (Finset.univ \ e).card =
                (((Finset.univ : Finset (Fin 6)).powersetCard 4).filter (fun Q => e ⊆ Q)).card := by
              refine Finset.card_bij (fun v _ => insert v e) ?_ ?_ ?_
              · intro v hv
                rw [Finset.mem_sdiff] at hv
                rw [Finset.mem_filter, Finset.mem_powersetCard]
                exact ⟨⟨Finset.subset_univ _, by rw [Finset.card_insert_of_notMem hv.2, hec]⟩,
                  Finset.subset_insert v e⟩
              · intro v1 hv1 v2 hv2 heq
                rw [Finset.mem_sdiff] at hv1 hv2
                rcases Finset.mem_insert.mp (heq ▸ Finset.mem_insert_self v1 e) with h | h
                · exact h
                · exact absurd h hv1.2
              · intro Q hQ
                rw [Finset.mem_filter, Finset.mem_powersetCard] at hQ
                have hdc : (Q \ e).card = 1 := by
                  rw [Finset.card_sdiff_of_subset hQ.2, hQ.1.2, hec]
                obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdc
                have hvm := Finset.mem_sdiff.mp (hv ▸ Finset.mem_singleton_self v)
                refine ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvm.2⟩, ?_⟩
                ext x; simp only [Finset.mem_insert]
                constructor
                · rintro (rfl | hx); exact hvm.1; exact hQ.2 hx
                · intro hx
                  by_cases hxe : x ∈ e
                  · exact Or.inr hxe
                  · left; have := Finset.mem_sdiff.mpr ⟨hx, hxe⟩; rw [hv, Finset.mem_singleton] at this; exact this
            rw [← hbij, Finset.card_sdiff_of_subset (Finset.subset_univ e), Finset.card_univ,
              Fintype.card_fin, hec]
        _ = F.card * 3 := by rw [Finset.sum_const, smul_eq_mul]
        _ = 3 * F.card := Nat.mul_comm _ _
    have h15le : 15 ≤ 3 * F.card := by
      rw [← hdouble]
      calc 15 = ∑ _Q ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4, 1 := by decide
        _ ≤ _ := Finset.sum_le_sum hhit
    by_contra hgt
    have hF5 : F.card = 5 := by omega
    have hexact1 : ∀ Q ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
        (F.filter (fun e => e ⊆ Q)).card = 1 := by
      by_contra hne
      push Not at hne
      obtain ⟨Q0, hQ0, hne0⟩ := hne
      have hge2 : 2 ≤ (F.filter (fun e => e ⊆ Q0)).card := by
        have := hhit Q0 hQ0; omega
      have hsum_gt : 15 < ∑ Q ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
          (F.filter (fun e => e ⊆ Q)).card := by
        calc 15 = ∑ _Q ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4, 1 := by decide
          _ < _ := Finset.sum_lt_sum hhit ⟨Q0, hQ0, hge2⟩
      omega
    have hdisj_pairs : (F : Set (Finset (Fin 6))).PairwiseDisjoint (fun e => e.powersetCard 2) := by
      intro e1 h1 e2 h2 hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      rw [Finset.mem_powersetCard] at hp1 hp2
      have hsub : p ⊆ e1 ∩ e2 := Finset.subset_inter hp1.1 hp2.1
      have hge2 : 2 ≤ (e1 ∩ e2).card := hp1.2 ▸ Finset.card_le_card hsub
      have hlt3 : (e1 ∩ e2).card < 3 := by
        by_contra hge3
        have hle3 : (e1 ∩ e2).card ≤ 3 :=
          (Finset.card_le_card (Finset.inter_subset_left (s₁ := e1) (s₂ := e2))).trans
            (by rw [hFunif e1 h1])
        have heq3 : (e1 ∩ e2).card = 3 := by omega
        have he1 := Finset.eq_of_subset_of_card_le
          (Finset.inter_subset_left (s₁ := e1) (s₂ := e2)) (by rw [heq3, hFunif e1 h1])
        have he2 := Finset.eq_of_subset_of_card_le
          (Finset.inter_subset_right (s₁ := e1) (s₂ := e2)) (by rw [heq3, hFunif e2 h2])
        exact hne (he1.symm.trans he2)
      have hcu := Finset.card_union_add_card_inter e1 e2
      rw [hFunif e1 h1, hFunif e2 h2] at hcu
      have hQ4 : (e1 ∪ e2).card = 4 := by omega
      have hQmem : e1 ∪ e2 ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4 :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hQ4⟩
      have htwo : 2 ≤ (F.filter (fun e => e ⊆ e1 ∪ e2)).card := by
        have hpair_sub : ({e1, e2} : Finset (Finset (Fin 6))) ⊆ F.filter (fun e => e ⊆ e1 ∪ e2) := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact Finset.mem_filter.mpr ⟨h1, Finset.subset_union_left⟩
          · rw [Finset.mem_singleton.mp hx]
            exact Finset.mem_filter.mpr ⟨h2, Finset.subset_union_right⟩
        calc 2 = ({e1, e2} : Finset (Finset (Fin 6))).card := (Finset.card_pair hne).symm
          _ ≤ _ := Finset.card_le_card hpair_sub
      have := hexact1 (e1 ∪ e2) hQmem
      omega
    have hcover : F.biUnion (fun e => e.powersetCard 2) =
        (Finset.univ : Finset (Fin 6)).powersetCard 2 := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro p hp
        rw [Finset.mem_biUnion] at hp
        rcases hp with ⟨e, _, hpe⟩
        rw [Finset.mem_powersetCard] at hpe ⊢
        exact ⟨Finset.subset_univ p, hpe.2⟩
      · rw [Finset.card_biUnion hdisj_pairs]
        have hsum3 : ∑ e ∈ F, (e.powersetCard 2).card = 15 := by
          calc ∑ e ∈ F, (e.powersetCard 2).card
              = ∑ e ∈ F, 3 := by
                refine Finset.sum_congr rfl fun e he => ?_
                rw [Finset.card_powersetCard, hFunif e he]; decide
            _ = F.card * 3 := by rw [Finset.sum_const, smul_eq_mul]
            _ = 15 := by rw [hF5]
        rw [hsum3]; decide
    have h0_left : (((Finset.univ : Finset (Fin 6)).powersetCard 2).filter
        (fun p => (0 : Fin 6) ∈ p)).card = 5 := by decide
    have h0_right : ((F.biUnion (fun e => e.powersetCard 2)).filter
        (fun p => (0 : Fin 6) ∈ p)).card = 2 * (F.filter (fun e => (0 : Fin 6) ∈ e)).card := by
      rw [Finset.filter_biUnion, Finset.card_biUnion]
      · calc ∑ e ∈ F, ((e.powersetCard 2).filter (fun p => (0 : Fin 6) ∈ p)).card
            = ∑ e ∈ F, if (0 : Fin 6) ∈ e then 2 else 0 := by
              refine Finset.sum_congr rfl fun e he => ?_
              by_cases h0e : (0 : Fin 6) ∈ e
              · simp only [if_pos h0e]
                have hbij : (e.erase 0).card =
                    ((e.powersetCard 2).filter (fun p => (0 : Fin 6) ∈ p)).card := by
                  refine Finset.card_bij (fun v _ => {0, v}) ?_ ?_ ?_
                  · intro v hv
                    rw [Finset.mem_erase] at hv
                    rw [Finset.mem_filter, Finset.mem_powersetCard]
                    refine ⟨⟨?_, Finset.card_pair (Ne.symm hv.1)⟩, Finset.mem_insert_self 0 {v}⟩
                    intro x hx
                    rcases Finset.mem_insert.mp hx with rfl | hx
                    · exact h0e
                    · rw [Finset.mem_singleton.mp hx]; exact hv.2
                  · intro v1 hv1 v2 hv2 heq
                    rw [Finset.mem_erase] at hv1 hv2
                    have hv1m : v1 ∈ ({0, v2} : Finset (Fin 6)) :=
                      heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v1)
                    rcases Finset.mem_insert.mp hv1m with h | h
                    · exact absurd h hv1.1
                    · exact Finset.mem_singleton.mp h
                  · intro p hp
                    rw [Finset.mem_filter, Finset.mem_powersetCard] at hp
                    have hpc : (p.erase 0).card = 1 := by
                      rw [Finset.card_erase_of_mem hp.2, hp.1.2]
                    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hpc
                    have hvm : v ∈ p.erase 0 := hv ▸ Finset.mem_singleton_self v
                    rw [Finset.mem_erase] at hvm
                    refine ⟨v, Finset.mem_erase.mpr ⟨hvm.1, hp.1.1 hvm.2⟩, ?_⟩
                    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
                    constructor
                    · rintro (rfl | rfl); exact hp.2; exact hvm.2
                    · intro hx
                      by_cases hx0 : x = 0
                      · exact Or.inl hx0
                      · right; have := Finset.mem_erase.mpr ⟨hx0, hx⟩; rw [hv, Finset.mem_singleton] at this; exact this
                rw [← hbij, Finset.card_erase_of_mem h0e, hFunif e he]
              · simp only [if_neg h0e]
                rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                intro p hp h0p
                exact h0e ((Finset.mem_powersetCard.mp hp).1 h0p)
          _ = 2 * (F.filter (fun e => (0 : Fin 6) ∈ e)).card := by
              rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
                Nat.mul_comm]
      · intro e1 h1 e2 h2 hne
        exact (hdisj_pairs h1 h2 hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [hcover] at h0_right
    omega
  · let miss : Finset (Finset (Fin 6)) :=
      {{0, 1, 4}, {0, 1, 5}, {0, 2, 3}, {1, 2, 3}, {2, 4, 5}, {3, 4, 5}}
    let E : Finset (Finset (Fin 6)) := ((Finset.univ : Finset (Fin 6)).powersetCard 3) \ miss
    refine ⟨E, ?_, ?_, ?_⟩
    · intro e he; exact (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp he).1).2
    · intro K hK hsub
      have hcheck : ∀ Q ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
          ¬ Q.powersetCard 3 ⊆ E := by decide
      exact hcheck K (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ K, hK⟩) hsub
    · decide

/-! ### Section 3: Turán `5/9` Universal Lower Bound, Fon-der-Flaass & Brown Barrier -/

/-- Exact `n.choose 2 * 2 = n * (n - 1)` helper. -/
private lemma choose_two_mul_two (n : ℕ) : n.choose 2 * 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd

/-- Exact `n.choose 3 * 6 = n * (n - 1) * (n - 2)` helper. -/
private lemma choose_three_mul_six (n : ℕ) : n.choose 3 * 6 = n * (n - 1) * (n - 2) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.add_mul, ih]
    have h2 := choose_two_mul_two m
    cases m with
    | zero => simp
    | succ m' =>
      cases m' with
      | zero => simp
      | succ m'' =>
        have hs1 : m'' + 1 + 1 - 1 = m'' + 1 := by omega
        have hs2 : m'' + 1 + 1 - 2 = m'' := by omega
        have hs3 : m'' + 1 + 1 + 1 - 1 = m'' + 2 := by omega
        have hs4 : m'' + 1 + 1 + 1 - 2 = m'' + 1 := by omega
        rw [hs1, hs2] at ih ⊢
        rw [hs1] at h2
        rw [hs3, hs4]
        nlinarith

/-- **Fon-der-Flaass (1988) Theorem**:
For any asymmetric oriented graph `adj` on `Fin n` containing no induced directed 4-cycle `C_4`,
the 3-uniform hypergraph consisting of all triples on which every vertex has degree `≥ 1` and
out-degree `≤ 1` is `K_4^3`-free. -/
theorem ppl074_fon_der_flaass_k43_free {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (hasym : ∀ u v, adj u v → ¬ adj v u)
    (hc4 : ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      adj a b → adj b c → adj c d → adj d a →
      adj a c ∨ adj c a ∨ adj b d ∨ adj d b) :
    ∀ K : Finset (Fin n), K.card = 4 →
      ¬ K.powersetCard 3 ⊆
        ((Finset.univ : Finset (Fin n)).powersetCard 3).filter (fun e =>
          (∀ u ∈ e, ∃ v ∈ e, adj u v ∨ adj v u) ∧
          (∀ u ∈ e, (e.filter (fun v => adj u v)).card ≤ 1)) := by
  intro K hK hsub
  have hirrefl : ∀ u, ¬ adj u u := fun u h => hasym u u h h
  -- Every triple in K satisfies the FDF condition.
  have htriple : ∀ e : Finset (Fin n), e ⊆ K → e.card = 3 →
      (∀ u ∈ e, ∃ v ∈ e, adj u v ∨ adj v u) ∧
      (∀ u ∈ e, (e.filter (fun v => adj u v)).card ≤ 1) := by
    intro e heK he3
    have hmem := hsub (Finset.mem_powersetCard.mpr ⟨heK, he3⟩)
    rw [Finset.mem_filter] at hmem
    exact hmem.2
  -- Step 1: Every vertex u ∈ K has out-degree ≤ 1 in K.
  have hout_le : ∀ u ∈ K, (K.filter (fun v => adj u v)).card ≤ 1 := by
    intro u hu
    by_contra hgt
    have hge2 : 2 ≤ (K.filter (fun v => adj u v)).card := by omega
    obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp (by omega : 1 < (K.filter (fun v => adj u v)).card)
    rw [Finset.mem_filter] at hv1 hv2
    have huv1 : u ≠ v1 := fun h => hirrefl u (h ▸ hv1.2)
    have huv2 : u ≠ v2 := fun h => hirrefl u (h ▸ hv2.2)
    let e : Finset (Fin n) := {u, v1, v2}
    have heK : e ⊆ K := by
      intro x hx
      simp only [e, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hu
      · exact hv1.1
      · exact hv2.1
    have he3 : e.card = 3 := by
      dsimp only [e]
      rw [Finset.card_insert_of_notMem (by simp [huv1, huv2]), Finset.card_pair hvne]
    have hle1 := (htriple e heK he3).2 u (by simp [e])
    have hpair : ({v1, v2} : Finset (Fin n)) ⊆ e.filter (fun v => adj u v) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_filter]
      rcases hx with rfl | rfl
      · exact ⟨by simp [e], hv1.2⟩
      · exact ⟨by simp [e], hv2.2⟩
    have h2le : 2 ≤ (e.filter (fun v => adj u v)).card := by
      calc 2 = ({v1, v2} : Finset (Fin n)).card := (Finset.card_pair hvne).symm
        _ ≤ _ := Finset.card_le_card hpair
    omega
  -- Step 2: Every vertex u ∈ K has out-degree ≥ 1 in K.
  have hout_ge : ∀ u ∈ K, 1 ≤ (K.filter (fun v => adj u v)).card := by
    intro u hu
    by_contra hlt
    have hout0 : ∀ v ∈ K, ¬ adj u v := by
      intro v hv huv
      have : 0 < (K.filter (fun w => adj u w)).card :=
        Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, huv⟩⟩
      omega
    -- Check in-neighbors of u in K.
    let inU := K.filter (fun v => adj v u)
    by_cases hin2 : 2 ≤ inU.card
    · -- Two distinct in-neighbors x, y → u; consider the remaining triple e = K.erase u.
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < inU.card)
      rw [Finset.mem_filter] at hx hy
      let e := K.erase u
      have heK : e ⊆ K := Finset.erase_subset u K
      have he3 : e.card = 3 := by rw [Finset.card_erase_of_mem hu, hK]
      have hxu : x ≠ u := fun h => hirrefl u (h ▸ hx.2)
      have hyu : y ≠ u := fun h => hirrefl u (h ▸ hy.2)
      have hxe : x ∈ e := Finset.mem_erase.mpr ⟨hxu, hx.1⟩
      have hye : y ∈ e := Finset.mem_erase.mpr ⟨hyu, hy.1⟩
      -- Since outdeg_K(x) ≤ 1 and adj x u, x has NO out-neighbors in e!
      have hx_no_out : ∀ w ∈ e, ¬ adj x w := by
        intro w hw hxw
        have hwu : w ≠ u := (Finset.mem_erase.mp hw).1
        have hsub2 : ({u, w} : Finset (Fin n)) ⊆ K.filter (fun v => adj x v) := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hu, hx.2⟩
          · exact Finset.mem_filter.mpr ⟨heK hw, hxw⟩
        have h2 := (Finset.card_pair (Ne.symm hwu)).symm.trans_le (Finset.card_le_card hsub2)
        have := hout_le x hx.1; omega
      have hy_no_out : ∀ w ∈ e, ¬ adj y w := by
        intro w hw hyw
        have hwu : w ≠ u := (Finset.mem_erase.mp hw).1
        have hsub2 : ({u, w} : Finset (Fin n)) ⊆ K.filter (fun v => adj y v) := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hu, hy.2⟩
          · exact Finset.mem_filter.mpr ⟨heK hw, hyw⟩
        have h2 := (Finset.card_pair (Ne.symm hwu)).symm.trans_le (Finset.card_le_card hsub2)
        have := hout_le y hy.1; omega
      -- Find the unique 3rd element z ∈ e \ {x, y}.
      have hz_ex : ∃ z ∈ e, z ≠ x ∧ z ≠ y := by
        have hcard : (e \ {x, y}).card = 1 := by
          have hsubxy : ({x, y} : Finset (Fin n)) ⊆ e := by
            intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl <;> assumption
          rw [Finset.card_sdiff_of_subset hsubxy, he3, Finset.card_pair hxy]
        obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
        have hzm := Finset.mem_sdiff.mp (hz ▸ Finset.mem_singleton_self z)
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzm
        exact ⟨z, hzm.1, hzm.2.1, hzm.2.2⟩
      obtain ⟨z, hze, hzx, hzy⟩ := hz_ex
      have he_eq : e = {x, y, z} := by
        refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
        · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl <;> assumption
        · rw [he3, Finset.card_insert_of_notMem (by simp [hxy, hzx.symm]),
            Finset.card_pair hzy.symm]
      -- Neither x nor y has an out-edge in e, and x, y are not isolated in e, so z → x AND z → y!
      obtain ⟨vx, hvx, hvx_adj⟩ := (htriple e heK he3).1 x hxe
      have hzx_adj : adj z x := by
        have hvx_in : adj vx x := hvx_adj.resolve_left (hx_no_out vx hvx)
        rw [he_eq] at hvx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hvx
        rcases hvx with h | h | h
        · exact absurd (h ▸ hvx_in) (hirrefl x)
        · exact absurd (h ▸ hvx_in) (hy_no_out x hxe)
        · exact h ▸ hvx_in
      obtain ⟨vy, hvy, hvy_adj⟩ := (htriple e heK he3).1 y hye
      have hzy_adj : adj z y := by
        have hvy_in : adj vy y := hvy_adj.resolve_left (hy_no_out vy hvy)
        rw [he_eq] at hvy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hvy
        rcases hvy with h | h | h
        · exact absurd (h ▸ hvy_in) (hx_no_out y hye)
        · exact absurd (h ▸ hvy_in) (hirrefl y)
        · exact h ▸ hvy_in
      -- Then z has out-degree 2 in e (contradicting htriple)!
      have h2le : 2 ≤ (e.filter (fun v => adj z v)).card := by
        have hsub2 : ({x, y} : Finset (Fin n)) ⊆ e.filter (fun v => adj z v) := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hxe, hzx_adj⟩
          · exact Finset.mem_filter.mpr ⟨hye, hzy_adj⟩
        exact (Finset.card_pair hxy).symm.trans_le (Finset.card_le_card hsub2)
      have := (htriple e heK he3).2 z hze
      omega
    · -- inU.card ≤ 1: pick 2 vertices v1, v2 in (K.erase u) \ inU; then u is isolated in {u, v1, v2}!
      have hrem : 2 ≤ ((K.erase u) \ inU).card := by
        have hle1 : inU.card ≤ 1 := by omega
        have hcard_er : (K.erase u).card = 3 := by rw [Finset.card_erase_of_mem hu, hK]
        have hsub_sdiff : (K.erase u).card ≤ ((K.erase u) \ inU).card + inU.card := by
          have h1 := Finset.card_sdiff_add_card_inter (K.erase u) inU
          have hle_i : (K.erase u ∩ inU).card ≤ inU.card :=
            Finset.card_le_card Finset.inter_subset_right
          omega
        omega
      obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp (by omega : 1 < ((K.erase u) \ inU).card)
      rw [Finset.mem_sdiff, Finset.mem_erase] at hv1 hv2
      let e : Finset (Fin n) := {u, v1, v2}
      have heK : e ⊆ K := by
        intro t ht; simp only [e, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact hu
        · exact hv1.1.2
        · exact hv2.1.2
      have he3 : e.card = 3 := by
        dsimp only [e]
        rw [Finset.card_insert_of_notMem (by simp [hv1.1.1.symm, hv2.1.1.symm]), Finset.card_pair hvne]
      obtain ⟨w, hw, hwadj⟩ := (htriple e heK he3).1 u (by simp [e])
      have hwu : adj w u := hwadj.resolve_left (hout0 w (heK hw))
      simp only [e, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with h | h | h
      · exact hirrefl u (h ▸ hwu)
      · exact hv1.2 (Finset.mem_filter.mpr ⟨hv1.1.2, h ▸ hwu⟩)
      · exact hv2.2 (Finset.mem_filter.mpr ⟨hv2.1.2, h ▸ hwu⟩)
  -- Step 3: Every u ∈ K has a UNIQUE out-neighbor f u ∈ K!
  have hex_uniq : ∀ u ∈ K, ∃! v, v ∈ K ∧ adj u v := by
    intro u hu
    have h1 : (K.filter (fun v => adj u v)).card = 1 := by
      have := hout_le u hu; have := hout_ge u hu; omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
    refine ⟨v, ?_, ?_⟩
    · have : v ∈ K.filter (fun w => adj u w) := hv ▸ Finset.mem_singleton_self v
      exact Finset.mem_filter.mp this
    · intro w hw
      have : w ∈ K.filter (fun x => adj u x) := Finset.mem_filter.mpr hw
      rw [hv, Finset.mem_singleton] at this
      exact this
  -- Pick a ∈ K and follow the unique out-edges a → b → c → d.
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < K.card)
  obtain ⟨b, ⟨hb, hab⟩, hbu⟩ := hex_uniq a ha
  obtain ⟨c, ⟨hc, hbc⟩, hcu⟩ := hex_uniq b hb
  obtain ⟨d, ⟨hd, hcd⟩, hdu⟩ := hex_uniq c hc
  have hne_ab : a ≠ b := fun h => hirrefl a (h ▸ hab)
  have hne_bc : b ≠ c := fun h => hirrefl b (h ▸ hbc)
  have hne_cd : c ≠ d := fun h => hirrefl c (h ▸ hcd)
  have hne_ac : a ≠ c := fun h => hasym a b hab (h ▸ hbc)
  have hne_bd : b ≠ d := fun h => hasym b c hbc (h ▸ hcd)
  -- Cannot have d = a (i.e. a → b → c → a is a 3-cycle), else the 4th vertex x ∈ K \ {a,b,c}
  -- has its unique out-neighbor f x ∈ {a, b, c} and is isolated in K.erase (f x)!
  have hne_ad : a ≠ d := by
    intro had
    subst had
    have hsub3 : ({a, b, c} : Finset (Fin n)) ⊆ K := by
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> assumption
    have hcard3 : ({a, b, c} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hne_ab, hne_ac]), Finset.card_pair hne_bc]
    have hcard_diff : (K \ {a, b, c}).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub3, hK, hcard3]
    obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp hcard_diff
    have hxm := Finset.mem_sdiff.mp (hx_eq ▸ Finset.mem_singleton_self x)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxm
    have hxK : x ∈ K := hxm.1
    have hxa : x ≠ a := hxm.2.1
    have hxb : x ≠ b := hxm.2.2.1
    have hxc : x ≠ c := hxm.2.2.2
    obtain ⟨fx, ⟨hfxK, hxfx⟩, hfxu⟩ := hex_uniq x hxK
    have hfx_ne_x : fx ≠ x := fun h => hirrefl x (h ▸ hxfx)
    -- In triple e = K.erase fx, x ∈ e has NO incident arc!
    let e := K.erase fx
    have heK : e ⊆ K := Finset.erase_subset fx K
    have he3 : e.card = 3 := by rw [Finset.card_erase_of_mem hfxK, hK]
    have hxe : x ∈ e := Finset.mem_erase.mpr ⟨hfx_ne_x.symm, hxK⟩
    obtain ⟨w, hwe, hwadj⟩ := (htriple e heK he3).1 x hxe
    have hwK : w ∈ K := heK hwe
    have hw_ne_fx : w ≠ fx := (Finset.mem_erase.mp hwe).1
    rcases hwadj with hxw | hwx
    · exact hw_ne_fx (hfxu w ⟨hwK, hxw⟩)
    · -- w ∈ {a, b, c, x}; cannot be x (irrefl), and a, b, c have unique out-neighbors b, c, a ≠ x!
      have hK_eq : K = {a, b, c, x} := by
        refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
        · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl | rfl <;> assumption
        · rw [hK, Finset.card_insert_of_notMem (by simp [hne_ab, hne_ac, hxa.symm]),
            Finset.card_insert_of_notMem (by simp [hne_bc, hxb.symm]), Finset.card_pair hxc.symm]
      rw [hK_eq] at hwK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwK
      rcases hwK with h | h | h | h
      · exact hxb (hbu x ⟨hxK, h ▸ hwx⟩)
      · exact hxc (hcu x ⟨hxK, h ▸ hwx⟩)
      · exact hxa (hdu x ⟨hxK, h ▸ hwx⟩)
      · exact hirrefl x (h ▸ hwx)
  -- Now a, b, c, d are 4 distinct vertices, so K = {a, b, c, d}!
  have hK_eq : K = {a, b, c, d} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> assumption
    · rw [hK, Finset.card_insert_of_notMem (by simp [hne_ab, hne_ac, hne_ad]),
        Finset.card_insert_of_notMem (by simp [hne_bc, hne_bd]), Finset.card_pair hne_cd]
  -- Find unique out-neighbor fd of d in K: must be a!
  obtain ⟨fd, ⟨hfdK, hdfd⟩, hfdu⟩ := hex_uniq d hd
  have hfd_eq_a : fd = a := by
    have hfd_mem := hfdK
    rw [hK_eq] at hfd_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfd_mem
    rcases hfd_mem with h | h | h | h
    · exact h
    · -- If d → b, then in {a, c, d}, a is isolated!
      exfalso
      let e : Finset (Fin n) := {a, c, d}
      have heK : e ⊆ K := by rw [hK_eq]; intro t ht; simp [e] at ht ⊢; tauto
      have he3 : e.card = 3 := by
        dsimp only [e]
        rw [Finset.card_insert_of_notMem (by simp [hne_ac, hne_ad]), Finset.card_pair hne_cd]
      obtain ⟨w, hwe, hwadj⟩ := (htriple e heK he3).1 a (by simp [e])
      rcases hwadj with haw | hwa
      · have hwb := hbu w ⟨heK hwe, haw⟩
        subst hwb; simp [e] at hwe; rcases hwe with h1 | h1 | h1
        · exact hne_ab h1.symm
        · exact hne_bc h1
        · exact hne_bd h1
      · simp [e] at hwe
        rcases hwe with h1 | h1 | h1
        · exact hirrefl a (h1 ▸ hwa)
        · exact hne_ad (hdu a ⟨ha, h1 ▸ hwa⟩)
        · exact hne_ab ((hfdu a ⟨ha, h1 ▸ hwa⟩).trans h)
    · exact absurd (h ▸ hdfd) (hasym c d hcd)
    · exact absurd (h ▸ hdfd) (hirrefl d)
  have hda : adj d a := hfd_eq_a ▸ hdfd
  -- Finally, by hc4, there is a chord among {a,c} or {b,d}, contradicting unique out-neighbors!
  have hchord := hc4 a b c d hne_ab hne_ac hne_ad hne_bc hne_bd hne_cd hab hbc hcd hda
  rcases hchord with hac | hca | hbd | hdb
  · exact hne_bc (hbu c ⟨hc, hac⟩).symm
  · exact hne_ad (hdu a ⟨ha, hca⟩)
  · exact hne_cd (hcu d ⟨hd, hbd⟩).symm
  · exact hne_ab ((hfdu b ⟨hb, hdb⟩).trans hfd_eq_a).symm

/-- **Exact Universal Turán `5/9` Lower Bound (Erdős #500 / PPL 074)**:
For **every** `n : ℕ`, there exists a `K_4^3`-free 3-uniform hypergraph `E` on `Fin n` satisfying
`9 * E.card ≥ 5 * n.choose 3`. -/
theorem ppl074_turan_lower_all_n (n : ℕ) :
    ∃ E : Finset (Finset (Fin n)),
      (∀ e ∈ E, e.card = 3) ∧
      (∀ K : Finset (Fin n), K.card = 4 → ¬ K.powersetCard 3 ⊆ E) ∧
      5 * n.choose 3 ≤ 9 * E.card := by
  -- Use Fon-der-Flaass on the blow-up of the directed 3-cycle `c(v) = v.val % 3`!
  let adj : Fin n → Fin n → Prop := fun u v => (u.val + 1) % 3 = v.val % 3
  have hasym : ∀ u v, adj u v → ¬ adj v u := by
    intro u v h1 h2; dsimp only [adj] at h1 h2; omega
  have hc4 : ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      adj a b → adj b c → adj c d → adj d a →
      adj a c ∨ adj c a ∨ adj b d ∨ adj d b := by
    intro a b c d _ _ _ _ _ _ h1 h2 h3 h4
    dsimp only [adj] at h1 h2 h3 h4
    omega
  let E : Finset (Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)).powersetCard 3).filter (fun e =>
      (∀ u ∈ e, ∃ v ∈ e, adj u v ∨ adj v u) ∧
      (∀ u ∈ e, (e.filter (fun v => adj u v)).card ≤ 1))
  refine ⟨E, ?_, ppl074_fon_der_flaass_k43_free adj hasym hc4, ?_⟩
  · intro e he; exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
  · -- Count E.card via the 4 disjoint types of triples in parts V0, V1, V2!
    let V0 : Finset (Fin n) := Finset.univ.filter (fun v => v.val % 3 = 0)
    let V1 : Finset (Fin n) := Finset.univ.filter (fun v => v.val % 3 = 1)
    let V2 : Finset (Fin n) := Finset.univ.filter (fun v => v.val % 3 = 2)
    -- Helper: any triple {x, y, z} with 1 in each part OR 2 in V_i and 1 in V_{i+1} lies in E.
    have hmem_rainbow : ∀ x ∈ V0, ∀ y ∈ V1, ∀ z ∈ V2, ({x, y, z} : Finset (Fin n)) ∈ E := by
      intro x hx y hy z hz
      rw [Finset.mem_filter] at hx hy hz
      have hxy : x ≠ y := fun h => by rw [h] at hx; omega
      have hxz : x ≠ z := fun h => by rw [h] at hx; omega
      have hyz : y ≠ z := fun h => by rw [h] at hy; omega
      have hcard : ({x, y, z} : Finset (Fin n)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]), Finset.card_pair hyz]
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, hcard⟩, ?_, ?_⟩
      · intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact ⟨y, by simp, Or.inl (by dsimp [adj]; omega)⟩
        · exact ⟨z, by simp, Or.inl (by dsimp [adj]; omega)⟩
        · exact ⟨x, by simp, Or.inl (by dsimp [adj]; omega)⟩
      · intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h | h
        · rw [h]
          have hf : ({x, y, z} : Finset (Fin n)).filter (fun v => adj x v) = {y} := by
            ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, adj]
            constructor
            · rintro ⟨rfl | rfl | rfl, hv⟩ <;> omega
            · rintro rfl; exact ⟨Or.inr (Or.inl rfl), by omega⟩
          rw [hf]; simp
        · rw [h]
          have hf : ({x, y, z} : Finset (Fin n)).filter (fun v => adj y v) = {z} := by
            ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, adj]
            constructor
            · rintro ⟨rfl | rfl | rfl, hv⟩ <;> omega
            · rintro rfl; exact ⟨Or.inr (Or.inr rfl), by omega⟩
          rw [hf]; simp
        · rw [h]
          have hf : ({x, y, z} : Finset (Fin n)).filter (fun v => adj z v) = {x} := by
            ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, adj]
            constructor
            · rintro ⟨rfl | rfl | rfl, hv⟩ <;> omega
            · rintro rfl; exact ⟨Or.inl rfl, by omega⟩
          rw [hf]; simp
    have hmem_two_one : ∀ (c : ℕ), c < 3 →
        ∀ p ∈ (Finset.univ.filter (fun v : Fin n => v.val % 3 = c)).powersetCard 2,
        ∀ z ∈ Finset.univ.filter (fun v : Fin n => v.val % 3 = (c + 1) % 3),
        insert z p ∈ E := by
      intro c hc p hp z hz
      rw [Finset.mem_powersetCard] at hp
      rw [Finset.mem_filter] at hz
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hp.2
      have hx : x.val % 3 = c := (Finset.mem_filter.mp (hp.1 (by simp))).2
      have hy : y.val % 3 = c := (Finset.mem_filter.mp (hp.1 (by simp))).2
      have hzx : z ≠ x := fun h => by rw [h] at hz; omega
      have hzy : z ≠ y := fun h => by rw [h] at hz; omega
      have hcard : (insert z ({x, y} : Finset (Fin n))).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hzx, hzy]), Finset.card_pair hxy]
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, hcard⟩, ?_, ?_⟩
      · intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact ⟨x, by simp, Or.inr (by dsimp [adj]; omega)⟩
        · exact ⟨z, by simp, Or.inl (by dsimp [adj]; omega)⟩
        · exact ⟨z, by simp, Or.inl (by dsimp [adj]; omega)⟩
      · intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h | h
        · rw [h]
          have hf : (insert z ({x, y} : Finset (Fin n))).filter (fun v => adj z v) = ∅ := by
            ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
              Finset.notMem_empty, iff_false, not_and, adj]
            rintro (rfl | rfl | rfl) <;> omega
          rw [hf]; simp
        · rw [h]
          have hf : (insert z ({x, y} : Finset (Fin n))).filter (fun v => adj x v) = {z} := by
            ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, adj]
            constructor
            · rintro ⟨rfl | rfl | rfl, hv⟩ <;> omega
            · rintro rfl; exact ⟨Or.inl rfl, by omega⟩
          rw [hf]; simp
        · rw [h]
          have hf : (insert z ({x, y} : Finset (Fin n))).filter (fun v => adj y v) = {z} := by
            ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, adj]
            constructor
            · rintro ⟨rfl | rfl | rfl, hv⟩ <;> omega
            · rintro rfl; exact ⟨Or.inl rfl, by omega⟩
          rw [hf]; simp
    -- Build the 4 disjoint subsets of E and compute their cardinalities!
    let E012 : Finset (Finset (Fin n)) :=
      ((V0 ×ˢ V1) ×ˢ V2).image (fun t => {t.1.1, t.1.2, t.2})
    let E001 : Finset (Finset (Fin n)) :=
      (V0.powersetCard 2 ×ˢ V1).image (fun t => insert t.2 t.1)
    let E112 : Finset (Finset (Fin n)) :=
      (V1.powersetCard 2 ×ˢ V2).image (fun t => insert t.2 t.1)
    let E220 : Finset (Finset (Fin n)) :=
      (V2.powersetCard 2 ×ˢ V0).image (fun t => insert t.2 t.1)
    have hE012_card : E012.card = V0.card * V1.card * V2.card := by
      rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_product]
      intro t1 ht1 t2 ht2 heq
      dsimp only at heq
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
        true_and, V0, V1, V2] at ht1 ht2
      have h1 : t1.1.1 ∈ ({t2.1.1, t2.1.2, t2.2} : Finset (Fin n)) := heq ▸ by simp
      have h2 : t1.1.2 ∈ ({t2.1.1, t2.1.2, t2.2} : Finset (Fin n)) := heq ▸ by simp
      have h3 : t1.2 ∈ ({t2.1.1, t2.1.2, t2.2} : Finset (Fin n)) := heq ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3
      have eq1 : t1.1.1 = t2.1.1 := by rcases h1 with h | h | h; exact h; omega; omega
      have eq2 : t1.1.2 = t2.1.2 := by rcases h2 with h | h | h; omega; exact h; omega
      have eq3 : t1.2 = t2.2 := by rcases h3 with h | h | h; omega; omega; exact h
      exact Prod.ext (Prod.ext eq1 eq2) eq3
    have hcard_two_one : ∀ (c1 c2 : ℕ), c1 ≠ c2 →
        (((Finset.univ.filter (fun v : Fin n => v.val % 3 = c1)).powersetCard 2 ×ˢ
          Finset.univ.filter (fun v : Fin n => v.val % 3 = c2)).image
          (fun t => insert t.2 t.1)).card =
        (Finset.univ.filter (fun v : Fin n => v.val % 3 = c1)).card.choose 2 *
        (Finset.univ.filter (fun v : Fin n => v.val % 3 = c2)).card := by
      intro c1 c2 hne
      rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_powersetCard]
      intro t1 ht1 t2 ht2 heq
      dsimp only at heq
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard,
        Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
      have h2mem : t1.2 ∈ insert t2.2 t2.1 := heq ▸ Finset.mem_insert_self _ _
      rcases Finset.mem_insert.mp h2mem with eq2 | hbad
      · have hnot1 : t1.2 ∉ t1.1 := fun h => hne ((Finset.mem_filter.mp (ht1.1.1 h)).2.symm.trans ht1.2)
        have hnot2 : t2.2 ∉ t2.1 := fun h => hne ((Finset.mem_filter.mp (ht2.1.1 h)).2.symm.trans ht2.2)
        have eq1 : t1.1 = t2.1 := by
          have := congrArg (fun s => s.erase t1.2) heq
          rw [Finset.erase_insert hnot1, eq2, Finset.erase_insert hnot2] at this
          exact this
        exact Prod.ext eq1 eq2
      · exact absurd ((Finset.mem_filter.mp (ht2.1.1 hbad)).2.symm.trans ht1.2) hne
    have hE001_card : E001.card = V0.card.choose 2 * V1.card := hcard_two_one 0 1 (by omega)
    have hE112_card : E112.card = V1.card.choose 2 * V2.card := hcard_two_one 1 2 (by omega)
    have hE220_card : E220.card = V2.card.choose 2 * V0.card := hcard_two_one 2 0 (by omega)
    -- Helper: color-count signatures prove pairwise disjointness of E012, E001, E112, E220!
    have hsig : ∀ (e : Finset (Fin n)),
        (e ∈ E012 → (e.filter (fun v => v.val % 3 = 0)).card = 1 ∧
                    (e.filter (fun v => v.val % 3 = 1)).card = 1) ∧
        (e ∈ E001 → (e.filter (fun v => v.val % 3 = 0)).card = 2 ∧
                    (e.filter (fun v => v.val % 3 = 1)).card = 1) ∧
        (e ∈ E112 → (e.filter (fun v => v.val % 3 = 0)).card = 0 ∧
                    (e.filter (fun v => v.val % 3 = 1)).card = 2) ∧
        (e ∈ E220 → (e.filter (fun v => v.val % 3 = 0)).card = 1 ∧
                    (e.filter (fun v => v.val % 3 = 1)).card = 0) := by
      intro e
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro he
        rcases Finset.mem_image.mp he with ⟨⟨⟨x, y⟩, z⟩, hmem, rfl⟩
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, V0, V1, V2] at hmem
        have hf0 : ({x, y, z} : Finset (Fin n)).filter (fun v => v.val % 3 = 0) = {x} := by
          ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | rfl, h⟩ <;> omega
          · rintro rfl; exact ⟨Or.inl rfl, hmem.1.1⟩
        have hf1 : ({x, y, z} : Finset (Fin n)).filter (fun v => v.val % 3 = 1) = {y} := by
          ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | rfl, h⟩ <;> omega
          · rintro rfl; exact ⟨Or.inr (Or.inl rfl), hmem.1.2⟩
        rw [hf0, hf1]; simp
      · intro he
        rcases Finset.mem_image.mp he with ⟨⟨p, y⟩, hmem, rfl⟩
        simp only [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_filter,
          Finset.mem_univ, true_and, V0, V1] at hmem
        have hf0 : (insert y p).filter (fun v => v.val % 3 = 0) = p := by
          ext v; simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hv, h⟩; omega; exact hv
          · intro hv; exact ⟨Or.inr hv, (Finset.mem_filter.mp (hmem.1.1 hv)).2⟩
        have hf1 : (insert y p).filter (fun v => v.val % 3 = 1) = {y} := by
          ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | hv, h⟩; rfl
            have := (Finset.mem_filter.mp (hmem.1.1 hv)).2; omega
          · rintro rfl; exact ⟨Or.inl rfl, hmem.2⟩
        rw [hf0, hf1, hmem.1.2]; simp
      · intro he
        rcases Finset.mem_image.mp he with ⟨⟨p, z⟩, hmem, rfl⟩
        simp only [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_filter,
          Finset.mem_univ, true_and, V1, V2] at hmem
        have hf0 : (insert z p).filter (fun v => v.val % 3 = 0) = ∅ := by
          ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false, not_and]
          rintro (rfl | hv); omega
          have := (Finset.mem_filter.mp (hmem.1.1 hv)).2; omega
        have hf1 : (insert z p).filter (fun v => v.val % 3 = 1) = p := by
          ext v; simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hv, h⟩; omega; exact hv
          · intro hv; exact ⟨Or.inr hv, (Finset.mem_filter.mp (hmem.1.1 hv)).2⟩
        rw [hf0, hf1, hmem.1.2]; simp
      · intro he
        rcases Finset.mem_image.mp he with ⟨⟨p, x⟩, hmem, rfl⟩
        simp only [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_filter,
          Finset.mem_univ, true_and, V2, V0] at hmem
        have hf0 : (insert x p).filter (fun v => v.val % 3 = 0) = {x} := by
          ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | hv, h⟩; rfl
            have := (Finset.mem_filter.mp (hmem.1.1 hv)).2; omega
          · rintro rfl; exact ⟨Or.inl rfl, hmem.2⟩
        have hf1 : (insert x p).filter (fun v => v.val % 3 = 1) = ∅ := by
          ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false, not_and]
          rintro (rfl | hv); omega
          have := (Finset.mem_filter.mp (hmem.1.1 hv)).2; omega
        rw [hf0, hf1]; simp
    have hsub_E : ((E012 ∪ E001) ∪ (E112 ∪ E220)) ⊆ E := by
      intro e he
      simp only [Finset.mem_union] at he
      rcases he with (he | he) | (he | he)
      · rcases Finset.mem_image.mp he with ⟨⟨⟨x, y⟩, z⟩, hm, rfl⟩
        simp only [Finset.mem_product] at hm
        exact hmem_rainbow x hm.1.1 y hm.1.2 z hm.2
      · rcases Finset.mem_image.mp he with ⟨⟨p, y⟩, hm, rfl⟩
        simp only [Finset.mem_product] at hm
        exact hmem_two_one 0 (by omega) p hm.1 y hm.2
      · rcases Finset.mem_image.mp he with ⟨⟨p, z⟩, hm, rfl⟩
        simp only [Finset.mem_product] at hm
        exact hmem_two_one 1 (by omega) p hm.1 z hm.2
      · rcases Finset.mem_image.mp he with ⟨⟨p, x⟩, hm, rfl⟩
        simp only [Finset.mem_product] at hm
        exact hmem_two_one 2 (by omega) p hm.1 x hm.2
    have hcard_union : ((E012 ∪ E001) ∪ (E112 ∪ E220)).card =
        E012.card + E001.card + (E112.card + E220.card) := by
      rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
      · rw [Finset.disjoint_left]; intro e h1 h2
        have := (hsig e).2.2.1 h1; have := (hsig e).2.2.2 h2; omega
      · rw [Finset.disjoint_left]; intro e h1 h2
        have := (hsig e).1 h1; have := (hsig e).2.1 h2; omega
      · rw [Finset.disjoint_left]; intro e h1 h2
        simp only [Finset.mem_union] at h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · have := (hsig e).1 h1; have := (hsig e).2.2.1 h2; omega
        · have := (hsig e).1 h1; have := (hsig e).2.2.2 h2; omega
        · have := (hsig e).2.1 h1; have := (hsig e).2.2.1 h2; omega
        · have := (hsig e).2.1 h1; have := (hsig e).2.2.2 h2; omega
    have hE_ge : V0.card * V1.card * V2.card + V0.card.choose 2 * V1.card +
        V1.card.choose 2 * V2.card + V2.card.choose 2 * V0.card ≤ E.card := by
      have := Finset.card_le_card hsub_E
      rw [hcard_union, hE012_card, hE001_card, hE112_card, hE220_card] at this
      omega
    -- Exact sizes of V0, V1, V2 via n = 3*k + r (r ∈ {0, 1, 2}):
    have hV_sum : V0.card + V1.card + V2.card = n := by
      have hpart : (V0 ∪ V1) ∪ V2 = Finset.univ := by
        ext v; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true,
          V0, V1, V2]; omega
      have hcu : ((V0 ∪ V1) ∪ V2).card = V0.card + V1.card + V2.card := by
        rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
        · rw [Finset.disjoint_left]; intro v h1 h2; simp [V0, V1] at h1 h2; omega
        · rw [Finset.disjoint_left]; intro v h1 h2; simp [V0, V1, V2] at h1 h2; omega
      rw [← hcu, hpart, Finset.card_univ, Fintype.card_fin]
    -- Show V2.card ≤ V1.card ≤ V0.card ≤ V2.card + 1 via shift injections!
    have hV1_le_V0 : V1.card ≤ V0.card := by
      refine Finset.card_le_card_of_injOn (fun v => ⟨v.val - 1, by omega⟩) ?_ ?_
      · intro v hv; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, V0, V1] at hv ⊢
        omega
      · intro u hu v hv heq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, V1] at hu hv
        have hval := congrArg Fin.val heq; dsimp at hval; ext; omega
    have hV2_le_V1 : V2.card ≤ V1.card := by
      refine Finset.card_le_card_of_injOn (fun v => ⟨v.val - 1, by omega⟩) ?_ ?_
      · intro v hv; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, V1, V2] at hv ⊢
        omega
      · intro u hu v hv heq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, V2] at hu hv
        have hval := congrArg Fin.val heq; dsimp at hval; ext; omega
    have hV0_le_V2_add : V0.card ≤ V2.card + 1 := by
      -- Map v ∈ V0 with v.val ≥ 1 to v - 1 ∈ V2!
      let V0pos := V0.filter (fun v => 1 ≤ v.val)
      have hpos_le : V0pos.card ≤ V2.card := by
        refine Finset.card_le_card_of_injOn (fun v => ⟨v.val - 1, by omega⟩) ?_ ?_
        · intro v hv
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, V0pos, V0, V2] at hv ⊢
          omega
        · intro u hu v hv heq
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, V0pos, V0] at hu hv
          have hval := congrArg Fin.val heq; dsimp at hval; ext; omega
      have hzero_le : (V0.filter (fun v => ¬ 1 ≤ v.val)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro u hu v hv
        simp only [Finset.mem_filter] at hu hv
        ext; omega
      have hsplit : V0.card = V0pos.card + (V0.filter (fun v => ¬ 1 ≤ v.val)).card := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext v; simp only [Finset.mem_union, Finset.mem_filter, V0pos]; tauto
        · rw [Finset.disjoint_left]; intro v h1 h2
          simp only [Finset.mem_filter, V0pos] at h1 h2; exact h2.2 h1.2
      omega
    -- Now let a = V0.card, b = V1.card, c = V2.card; only 3 cases: (c,c,c), (c+1,c,c), (c+1,c+1,c)!
    set a := V0.card; set b := V1.card; set c := V2.card
    have hch3 := choose_three_mul_six n
    have ha2 := choose_two_mul_two a
    have hb2 := choose_two_mul_two b
    have hc2 := choose_two_mul_two c
    suffices h6 : 5 * (n.choose 3 * 6) ≤ 9 * (E.card * 6) by omega
    have hE6 : 6 * (a * b * c) + 3 * (a * (a - 1) * b) + 3 * (b * (b - 1) * c) +
        3 * (c * (c - 1) * a) ≤ E.card * 6 := by
      have : E.card * 6 ≥ (a * b * c + a.choose 2 * b + b.choose 2 * c + c.choose 2 * a) * 6 :=
        Nat.mul_le_mul_right 6 hE_ge
      nlinarith
    set ec := E.card
    clear_value ec a b c
    rw [hch3]
    have hcases : (a = c ∧ b = c) ∨ (a = c + 1 ∧ b = c) ∨ (a = c + 1 ∧ b = c + 1) := by omega
    rcases hcases with ⟨hac, hbc⟩ | ⟨hac, hbc⟩ | ⟨hac, hbc⟩
    · have hn : n = 3 * c := by omega
      rw [hac, hbc] at hE6
      have hLHS : 5 * (n * (n - 1) * (n - 2)) = 5 * (3 * c * (3 * c - 1) * (3 * c - 2)) := by rw [hn]
      rw [hLHS]
      cases c with
      | zero => simp
      | succ k =>
        have h1 : 3 * (k + 1) - 1 = 3 * k + 2 := by omega
        have h2 : 3 * (k + 1) - 2 = 3 * k + 1 := by omega
        have h3 : k + 1 - 1 = k := by omega
        rw [h1, h2]
        rw [h3] at hE6
        nlinarith
    · have hn : n = 3 * c + 1 := by omega
      rw [hac, hbc] at hE6
      have hLHS : 5 * (n * (n - 1) * (n - 2)) =
          5 * ((3 * c + 1) * (3 * c + 1 - 1) * (3 * c + 1 - 2)) := by rw [hn]
      rw [hLHS]
      cases c with
      | zero => simp
      | succ k =>
        have h1 : 3 * (k + 1) + 1 - 1 = 3 * k + 3 := by omega
        have h2 : 3 * (k + 1) + 1 - 2 = 3 * k + 2 := by omega
        have h3 : k + 1 + 1 - 1 = k + 1 := by omega
        have h4 : k + 1 - 1 = k := by omega
        rw [h1, h2]
        rw [h3, h4] at hE6
        nlinarith
    · have hn : n = 3 * c + 2 := by omega
      rw [hac, hbc] at hE6
      have hLHS : 5 * (n * (n - 1) * (n - 2)) =
          5 * ((3 * c + 2) * (3 * c + 2 - 1) * (3 * c + 2 - 2)) := by rw [hn]
      rw [hLHS]
      cases c with
      | zero => simp
      | succ k =>
        have h1 : 3 * (k + 1) + 2 - 1 = 3 * k + 4 := by omega
        have h2 : 3 * (k + 1) + 2 - 2 = 3 * k + 3 := by omega
        have h3 : k + 1 + 1 - 1 = k + 1 := by omega
        have h4 : k + 1 - 1 = k := by omega
        rw [h1, h2]
        rw [h3, h4] at hE6
        nlinarith

/-- **Asymptotic Turán `5/9` Lower Bound (matches `erdos_500.variants.lower_bound`)**:
For every `ε > 0`, eventually for all `n`, `(5 / 9 - ε) * n.choose 3 ≤ ex_3(n, K_4^3)`. -/
theorem ppl074_turan_lower_asymptotic (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (5 / 9 - ε) * (n.choose 3 : ℝ) ≤
        ((sSup {m : ℕ | ∃ E : Finset (Finset (Fin n)),
          (∀ e ∈ E, e.card = 3) ∧
          (∀ K : Finset (Fin n), K.card = 4 → ¬ K.powersetCard 3 ⊆ E) ∧
          E.card = m} : ℕ) : ℝ) := by
  filter_upwards with n
  obtain ⟨E, hE, hfree, h9⟩ := ppl074_turan_lower_all_n n
  have hle : E.card ≤ sSup {m : ℕ | ∃ E' : Finset (Finset (Fin n)),
      (∀ e ∈ E', e.card = 3) ∧
      (∀ K : Finset (Fin n), K.card = 4 → ¬ K.powersetCard 3 ⊆ E') ∧
      E'.card = m} :=
    le_csSup (ex_set_bddAbove n 3 4) ⟨E, hE, hfree, rfl⟩
  have h9R : (5 : ℝ) * (n.choose 3 : ℝ) ≤ 9 * (E.card : ℝ) := by exact_mod_cast h9
  have hleR : (E.card : ℝ) ≤ ((sSup {m : ℕ | ∃ E' : Finset (Finset (Fin n)),
      (∀ e ∈ E', e.card = 3) ∧
      (∀ K : Finset (Fin n), K.card = 4 → ¬ K.powersetCard 3 ⊆ E') ∧
      E'.card = m} : ℕ) : ℝ) := by exact_mod_cast hle
  have hch_nn : (0 : ℝ) ≤ (n.choose 3 : ℝ) := Nat.cast_nonneg _
  nlinarith

/-! #### Brown (1983) Multi-Extremal Stability Barrier (6-Vertex Oriented Octahedron Blow-Up) -/

/-- The 6-vertex `C_4`-free oriented octahedron `Γ_6` (`0=A, 1=B, 2=C, 3=a, 4=b, 5=c`). -/
private def octAdj : Fin 6 → Fin 6 → Bool
  | 0, 1 => true | 1, 2 => true | 2, 0 => true
  | 3, 5 => true | 5, 4 => true | 4, 3 => true
  | 0, 3 => true | 3, 2 => true | 2, 5 => true
  | 5, 1 => true | 1, 4 => true | 4, 0 => true
  | _, _ => false

private lemma octAdj_asym : ∀ a b : Fin 6, octAdj a b = true → octAdj b a ≠ true := by decide

private lemma octAdj_no_c4 : ∀ a b c d : Fin 6,
    octAdj a b = true → octAdj b c = true → octAdj c d = true → octAdj d a = true →
    octAdj a c = true ∨ octAdj c a = true ∨ octAdj b d = true ∨ octAdj d b = true := by decide

/-- Induced Fon-der-Flaass edge predicate on 3 block indices in `Fin 6` (for 3 distinct vertices). -/
private def octTriple (a b c : Fin 6) : Bool :=
  let hasInc (x y z : Fin 6) : Bool :=
    octAdj x y || octAdj y x || octAdj x z || octAdj z x
  let outLe1 (x y z : Fin 6) : Bool :=
    !(octAdj x y && octAdj x z)
  hasInc a b c && hasInc b a c && hasInc c a b &&
  outLe1 a b c && outLe1 b a c && outLe1 c a b

/-- Block assignment `Fin (3 * m) → Fin 6` with block sizes `(m - q, m - q, m - q, q, q, q)`. -/
private def brownBlock (m q : ℕ) (v : Fin (3 * m)) : Fin 6 :=
  let r := v.val % m
  let g := v.val / m
  if r < m - q then
    if g = 0 then 0 else if g = 1 then 1 else 2
  else
    if g = 0 then 3 else if g = 1 then 4 else 5

private lemma brownBlock_fiber_card (m q : ℕ) (hq : q ≤ m) (b : Fin 6) :
    ((Finset.univ : Finset (Fin (3 * m))).filter (fun v => brownBlock m q v = b)).card =
      if b.val < 3 then m - q else q := by
  have hgen : ∀ (g off L : ℕ), g < 3 → off + L ≤ m →
      (Finset.univ.filter (fun v : Fin (3 * m) => v.val / m = g ∧ off ≤ v.val % m ∧ v.val % m < off + L)).card = L := by
    intro g off L hg hoff
    by_cases hL0 : L = 0
    · subst hL0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v _; omega
    · have hm : 0 < m := by omega
      have hL : (Finset.univ : Finset (Fin L)).card = L := by simp
      rw [← hL]
      symm
      refine Finset.card_bij (fun (r : Fin L) _ => (⟨m * g + (off + r.val), by
        have : m * (g + 1) ≤ 3 * m := by nlinarith
        nlinarith [r.isLt]⟩ : Fin (3 * m))) ?_ ?_ ?_
      · intro r _
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
        · dsimp only
          rw [Nat.mul_add_div hm, Nat.div_eq_of_lt (by omega)]; omega
        · dsimp only
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]; omega
        · dsimp only
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]; omega
      · intro r1 _ r2 _ heq
        have hv := congrArg Fin.val heq; dsimp at hv; ext; omega
      · intro v hv
        rw [Finset.mem_filter] at hv
        have hdiv := hv.2.1
        have hlo := hv.2.2.1
        have hhi := hv.2.2.2
        refine ⟨⟨v.val % m - off, by omega⟩, Finset.mem_univ _, ?_⟩
        ext; dsimp only
        have heq := Nat.div_add_mod v.val m
        rw [hdiv] at heq
        omega
  have hdiv_lt : ∀ v : Fin (3 * m), v.val / m < 3 := by
    intro v
    have hm : 0 < m := by have := v.isLt; omega
    exact Nat.div_lt_of_lt_mul (by linarith [v.isLt])
  have hmod_lt : ∀ v : Fin (3 * m), v.val % m < m - q + q := by
    intro v
    have hm : 0 < m := by have := v.isLt; omega
    have := Nat.mod_lt v.val hm; omega
  fin_cases b
  · change (Finset.univ.filter (fun v : Fin (3 * m) => brownBlock m q v = 0)).card = m - q
    have hfilt : (Finset.univ.filter (fun v : Fin (3 * m) => brownBlock m q v = 0)) =
        Finset.univ.filter (fun v : Fin (3 * m) => v.val / m = 0 ∧ 0 ≤ v.val % m ∧ v.val % m < 0 + (m - q)) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.zero_le, Nat.zero_add]
      dsimp only [brownBlock]; set d := v.val / m; split_ifs <;>
        exact ⟨fun h => by first | exact absurd h (by decide) | omega,
               fun h => by first | rfl | omega⟩
    rw [hfilt, hgen 0 0 (m - q) (by omega) (by omega)]
  · change (Finset.univ.filter (fun v : Fin (3 * m) => brownBlock m q v = 1)).card = m - q
    have hfilt : (Finset.univ.filter (fun v : Fin (3 * m) => brownBlock m q v = 1)) =
        Finset.univ.filter (fun v : Fin (3 * m) => v.val / m = 1 ∧ 0 ≤ v.val % m ∧ v.val % m < 0 + (m - q)) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.zero_le, Nat.zero_add]
      dsimp only [brownBlock]; set d := v.val / m; split_ifs <;>
        exact ⟨fun h => by first | exact absurd h (by decide) | omega,
               fun h => by first | rfl | omega⟩
    rw [hfilt, hgen 1 0 (m - q) (by omega) (by omega)]
  · change (Finset.univ.filter (fun v : Fin (3 * m) => brownBlock m q v = 2)).card = m - q
    have hfilt : (Finset.univ.filter (fun v : Fin (3 * m) => brownBlock m q v = 2)) =
        Finset.univ.filter (fun v : Fin (3 * m) => v.val / m = 2 ∧ 0 ≤ v.val % m ∧ v.val % m < 0 + (m - q)) := by
      ext v
      have hlt := hdiv_lt v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.zero_le, Nat.zero_add]
      dsimp only [brownBlock]
      generalize v.val / m = d at hlt ⊢
      split_ifs <;>
        exact ⟨fun h => by first | exact absurd h (by decide) | omega,
               fun h => by first | rfl | omega⟩
    rw [hfilt, hgen 2 0 (m - q) (by omega) (by omega)]
  · change (Finset.univ.filter (fun v : Fin (3 * m) => brownBlock m q v = 3)).card = q
    have hfilt : (Finset.univ.filter (fun v : Fin (3 * m) => brownBlock m q v = 3)) =
        Finset.univ.filter (fun v : Fin (3 * m) => v.val / m = 0 ∧ (m - q) ≤ v.val % m ∧ v.val % m < (m - q) + q) := by
      ext v
      have hmlt := hmod_lt v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [brownBlock]; set d := v.val / m; split_ifs <;>
        exact ⟨fun h => by first | exact absurd h (by decide) | omega,
               fun h => by first | rfl | omega⟩
    rw [hfilt, hgen 0 (m - q) q (by omega) (by omega)]
  · change (Finset.univ.filter (fun v : Fin (3 * m) => brownBlock m q v = 4)).card = q
    have hfilt : (Finset.univ.filter (fun v : Fin (3 * m) => brownBlock m q v = 4)) =
        Finset.univ.filter (fun v : Fin (3 * m) => v.val / m = 1 ∧ (m - q) ≤ v.val % m ∧ v.val % m < (m - q) + q) := by
      ext v
      have hmlt := hmod_lt v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [brownBlock]; set d := v.val / m; split_ifs <;>
        exact ⟨fun h => by first | exact absurd h (by decide) | omega,
               fun h => by first | rfl | omega⟩
    rw [hfilt, hgen 1 (m - q) q (by omega) (by omega)]
  · change (Finset.univ.filter (fun v : Fin (3 * m) => brownBlock m q v = 5)).card = q
    have hfilt : (Finset.univ.filter (fun v : Fin (3 * m) => brownBlock m q v = 5)) =
        Finset.univ.filter (fun v : Fin (3 * m) => v.val / m = 2 ∧ (m - q) ≤ v.val % m ∧ v.val % m < (m - q) + q) := by
      ext v
      have hmlt := hmod_lt v
      have hlt := hdiv_lt v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [brownBlock]
      generalize v.val / m = d at hlt ⊢
      split_ifs <;>
        exact ⟨fun h => by first | exact absurd h (by decide) | omega,
               fun h => by first | rfl | omega⟩
    rw [hfilt, hgen 2 (m - q) q (by omega) (by omega)]

/-- For 3 distinct vertices `x, y, z`, membership of `{x, y, z}` in the Fon-der-Flaass 3-graph
of a `brownBlock` blow-up of `octAdj` equals `octTriple (blk x) (blk y) (blk z) = true`. -/
private lemma fdf_blowup_mem_iff {n : ℕ} (blk : Fin n → Fin 6) {x y z : Fin n}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ((∀ u ∈ ({x, y, z} : Finset (Fin n)), ∃ v ∈ ({x, y, z} : Finset (Fin n)),
        octAdj (blk u) (blk v) = true ∨ octAdj (blk v) (blk u) = true) ∧
     (∀ u ∈ ({x, y, z} : Finset (Fin n)),
        (({x, y, z} : Finset (Fin n)).filter (fun v => octAdj (blk u) (blk v) = true)).card ≤ 1)) ↔
    octTriple (blk x) (blk y) (blk z) = true := by
  have hirr : ∀ b : Fin 6, octAdj b b = false := by decide
  have hout_iff : ∀ (u v w : Fin n), u ≠ v → u ≠ w → v ≠ w →
      ((({u, v, w} : Finset (Fin n)).filter (fun t => octAdj (blk u) (blk t) = true)).card ≤ 1 ↔
        (!(octAdj (blk u) (blk v) && octAdj (blk u) (blk w))) = true) := by
    intro u v w _ _ hvw
    cases h1 : octAdj (blk u) (blk v) <;> cases h2 : octAdj (blk u) (blk w)
    · have hf : ({u, v, w} : Finset (Fin n)).filter (fun t => octAdj (blk u) (blk t) = true) = ∅ := by
        ext t; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
          Finset.notMem_empty, iff_false, not_and]
        rintro (rfl | rfl | rfl)
        · rw [hirr]; decide
        · rw [h1]; decide
        · rw [h2]; decide
      rw [hf]; simp
    · have hf : ({u, v, w} : Finset (Fin n)).filter (fun t => octAdj (blk u) (blk t) = true) = {w} := by
        ext t; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl | rfl, ht⟩
          · rw [hirr] at ht; contradiction
          · rw [h1] at ht; contradiction
          · rfl
        · rintro rfl; exact ⟨Or.inr (Or.inr rfl), h2⟩
      rw [hf]; simp
    · have hf : ({u, v, w} : Finset (Fin n)).filter (fun t => octAdj (blk u) (blk t) = true) = {v} := by
        ext t; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl | rfl, ht⟩
          · rw [hirr] at ht; contradiction
          · rfl
          · rw [h2] at ht; contradiction
        · rintro rfl; exact ⟨Or.inr (Or.inl rfl), h1⟩
      rw [hf]; simp
    · have hf : ({u, v, w} : Finset (Fin n)).filter (fun t => octAdj (blk u) (blk t) = true) = {v, w} := by
        ext t; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl | rfl, ht⟩
          · rw [hirr] at ht; contradiction
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact ⟨Or.inr (Or.inl rfl), h1⟩
          · exact ⟨Or.inr (Or.inr rfl), h2⟩
      rw [hf, Finset.card_pair hvw]; decide
  have hinc_iff : ∀ (u v w : Fin n),
      (∃ t ∈ ({u, v, w} : Finset (Fin n)), octAdj (blk u) (blk t) = true ∨ octAdj (blk t) (blk u) = true) ↔
        (octAdj (blk u) (blk v) || octAdj (blk v) (blk u) ||
         octAdj (blk u) (blk w) || octAdj (blk w) (blk u)) = true := by
    intro u v w
    simp only [Finset.mem_insert, Finset.mem_singleton, Bool.or_eq_true]
    constructor
    · rintro ⟨t, rfl | rfl | rfl, ht | ht⟩
      · rw [hirr] at ht; contradiction
      · rw [hirr] at ht; contradiction
      · exact Or.inl (Or.inl (Or.inl ht))
      · exact Or.inl (Or.inl (Or.inr ht))
      · exact Or.inl (Or.inr ht)
      · exact Or.inr ht
    · rintro (((h | h) | h) | h)
      · exact ⟨v, Or.inr (Or.inl rfl), Or.inl h⟩
      · exact ⟨v, Or.inr (Or.inl rfl), Or.inr h⟩
      · exact ⟨w, Or.inr (Or.inr rfl), Or.inl h⟩
      · exact ⟨w, Or.inr (Or.inr rfl), Or.inr h⟩
  have hset_y : ({x, y, z} : Finset (Fin n)) = {y, x, z} := by ext t; simp; tauto
  have hset_z : ({x, y, z} : Finset (Fin n)) = {z, x, y} := by ext t; simp; tauto
  have hlhs :
      ((∀ u ∈ ({x, y, z} : Finset (Fin n)), ∃ v ∈ ({x, y, z} : Finset (Fin n)),
          octAdj (blk u) (blk v) = true ∨ octAdj (blk v) (blk u) = true) ∧
       (∀ u ∈ ({x, y, z} : Finset (Fin n)),
          (({x, y, z} : Finset (Fin n)).filter (fun v => octAdj (blk u) (blk v) = true)).card ≤ 1)) ↔
      ((∃ t ∈ ({x, y, z} : Finset (Fin n)), octAdj (blk x) (blk t) = true ∨ octAdj (blk t) (blk x) = true) ∧
       (∃ t ∈ ({y, x, z} : Finset (Fin n)), octAdj (blk y) (blk t) = true ∨ octAdj (blk t) (blk y) = true) ∧
       (∃ t ∈ ({z, x, y} : Finset (Fin n)), octAdj (blk z) (blk t) = true ∨ octAdj (blk t) (blk z) = true) ∧
       (({x, y, z} : Finset (Fin n)).filter (fun v => octAdj (blk x) (blk v) = true)).card ≤ 1 ∧
       (({y, x, z} : Finset (Fin n)).filter (fun v => octAdj (blk y) (blk v) = true)).card ≤ 1 ∧
       (({z, x, y} : Finset (Fin n)).filter (fun v => octAdj (blk z) (blk v) = true)).card ≤ 1) := by
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1 x (by simp), hset_y ▸ h1 y (by simp), hset_z ▸ h1 z (by simp),
        h2 x (by simp), hset_y ▸ h2 y (by simp), hset_z ▸ h2 z (by simp)⟩
    · rintro ⟨hx1, hy1, hz1, hx2, hy2, hz2⟩
      refine ⟨fun u hu => ?_, fun u hu => ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact hx1
        · exact hset_y.symm ▸ hy1
        · exact hset_z.symm ▸ hz1
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact hx2
        · exact hset_y.symm ▸ hy2
        · exact hset_z.symm ▸ hz2
  rw [hlhs, hinc_iff x y z, hinc_iff y x z, hinc_iff z x y,
    hout_iff x y z hxy hxz hyz, hout_iff y x z hxy.symm hyz hxz,
    hout_iff z x y hxz.symm hyz.symm hxy]
  dsimp only [octTriple]
  simp only [Bool.and_eq_true]
  tauto

/-- Fast kernel-verified count of valid `octTriple` extensions of `(a, b)` in top/bottom halves. -/
private def octTopCount (a b : Fin 6) : ℕ :=
  ((Finset.univ : Finset (Fin 6)).filter (fun c => c.val < 3 ∧ octTriple a b c = true)).card

private def octBotCount (a b : Fin 6) : ℕ :=
  ((Finset.univ : Finset (Fin 6)).filter (fun c => ¬ c.val < 3 ∧ octTriple a b c = true)).card

private lemma octCounts_spec : ∀ a b : Fin 6,
    (a = b → octTopCount a b = 1 ∧ octBotCount a b = 1 ∧
             octTriple a b a = false ∧ octTriple a b b = false) ∧
    (a ≠ b → (octTopCount a b = 2 ∧ octBotCount a b = 2 ∧ ¬ (octTriple a b a = true ∧ octTriple a b b = true)) ∨
             (octTopCount a b = 2 ∧ octBotCount a b = 1 ∧ ¬ (octTriple a b a = true ∧ octTriple a b b = true)) ∨
             (octTopCount a b = 1 ∧ octBotCount a b = 2 ∧ octTriple a b a = false ∧ octTriple a b b = false ∧
               (¬ a.val < 3 ∨ ¬ b.val < 3))) := by decide

private lemma octPoly_coeff_30 :
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
      if octTriple a b c = true ∧ a.val < 3 ∧ b.val < 3 ∧ c.val < 3 then 1 else 0) = 15 ∧
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
      if octTriple a b c = true ∧ a.val < 3 ∧ b.val < 3 ∧ ¬ c.val < 3 then 1 else 0) = 15 ∧
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
      if octTriple a b c = true ∧ a.val < 3 ∧ ¬ b.val < 3 ∧ c.val < 3 then 1 else 0) = 15 ∧
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
      if octTriple a b c = true ∧ ¬ a.val < 3 ∧ b.val < 3 ∧ c.val < 3 then 1 else 0) = 15 ∧
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
      if octTriple a b c = true ∧ a.val < 3 ∧ ¬ b.val < 3 ∧ ¬ c.val < 3 then 1 else 0) = 15 ∧
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
      if octTriple a b c = true ∧ ¬ a.val < 3 ∧ b.val < 3 ∧ ¬ c.val < 3 then 1 else 0) = 15 ∧
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
      if octTriple a b c = true ∧ ¬ a.val < 3 ∧ ¬ b.val < 3 ∧ c.val < 3 then 1 else 0) = 15 ∧
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
      if octTriple a b c = true ∧ ¬ a.val < 3 ∧ ¬ b.val < 3 ∧ ¬ c.val < 3 then 1 else 0) = 15 ∧
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
      if octTriple a b c = true ∧ a = b ∧ a.val < 3 ∧ c.val < 3 then 1 else 0) = 3 ∧
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
      if octTriple a b c = true ∧ a = b ∧ a.val < 3 ∧ ¬ c.val < 3 then 1 else 0) = 3 ∧
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
      if octTriple a b c = true ∧ a = b ∧ ¬ a.val < 3 ∧ c.val < 3 then 1 else 0) = 3 ∧
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
      if octTriple a b c = true ∧ a = b ∧ ¬ a.val < 3 ∧ ¬ c.val < 3 then 1 else 0) = 3 ∧
    (∀ a : Fin 6, octTriple a a a = false) ∧
    (∀ a b c : Fin 6, octTriple a b c = octTriple b a c ∧ octTriple a b c = octTriple a c b) := by decide

/-- **Brown (1983) Non-Uniqueness / Stability Barrier**:
For every `m ≥ 3`, there exist `m / 2 + 1` **pairwise non-isomorphic** `K_4^3`-free 3-uniform
hypergraphs on `Fin (3 * m)` that **all** achieve the exact Turán edge count
`m ^ 3 + 3 * m.choose 2 * m` (hence `9 * |E| ≥ 5 * (3 * m).choose 3`). -/
theorem ppl074_brown_non_uniqueness_barrier (m : ℕ) (hm : 3 ≤ m) :
    ∃ F : Fin (m / 2 + 1) → Finset (Finset (Fin (3 * m))),
      (∀ i, ∀ e ∈ F i, e.card = 3) ∧
      (∀ i, ∀ K : Finset (Fin (3 * m)), K.card = 4 → ¬ K.powersetCard 3 ⊆ F i) ∧
      (∀ i, (F i).card = m ^ 3 + 3 * m.choose 2 * m) ∧
      (∀ i j, i ≠ j → ∀ σ : Equiv.Perm (Fin (3 * m)),
        (F i).image (Finset.image σ) ≠ F j) := by
  classical
  let F : Fin (m / 2 + 1) → Finset (Finset (Fin (3 * m))) := fun i =>
    let adj : Fin (3 * m) → Fin (3 * m) → Prop :=
      fun u v => octAdj (brownBlock m i.val u) (brownBlock m i.val v) = true
    ((Finset.univ : Finset (Fin (3 * m))).powersetCard 3).filter (fun e =>
      (∀ u ∈ e, ∃ v ∈ e, adj u v ∨ adj v u) ∧
      (∀ u ∈ e, (e.filter (fun v => adj u v)).card ≤ 1))
  -- Helper: size of block b for parameter q = i.val.
  let sz : ℕ → Fin 6 → ℕ := fun q b => if b.val < 3 then m - q else q
  -- Helper: for any q ≤ m / 2, compute pair-codegree of any u ≠ v in F ⟨q, _⟩!
  have hcodeg : ∀ (i : Fin (m / 2 + 1)) (u v : Fin (3 * m)), u ≠ v →
      ((Finset.univ : Finset (Fin (3 * m))).filter
        (fun w => w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) ∈ F i)).card =
      ∑ c : Fin 6, if octTriple (brownBlock m i.val u) (brownBlock m i.val v) c = true then
        sz i.val c - (if brownBlock m i.val u = c then 1 else 0) -
          (if brownBlock m i.val v = c then 1 else 0)
      else 0 := by
    intro i u v huv
    have hq : i.val ≤ m := by omega
    -- Partition the filtered vertices w by `c = brownBlock m i.val w`.
    have hpart : (Finset.univ.filter
        (fun w : Fin (3 * m) => w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) ∈ F i)).card =
        ∑ c : Fin 6, (Finset.univ.filter (fun w : Fin (3 * m) =>
          brownBlock m i.val w = c ∧ w ≠ u ∧ w ≠ v ∧
            ({u, v, w} : Finset (Fin (3 * m))) ∈ F i)).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext w; simp
      · intro c1 _ c2 _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro w h1 h2
        simp only [Finset.mem_filter] at h1 h2
        exact hne (h1.2.1.symm.trans h2.2.1)
    rw [hpart]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hfilt_eq : Finset.univ.filter (fun w : Fin (3 * m) =>
        brownBlock m i.val w = c ∧ w ≠ u ∧ w ≠ v ∧
          ({u, v, w} : Finset (Fin (3 * m))) ∈ F i) =
        if octTriple (brownBlock m i.val u) (brownBlock m i.val v) c = true then
          ((Finset.univ.filter (fun w : Fin (3 * m) => brownBlock m i.val w = c)).erase u).erase v
        else ∅ := by
      split_ifs with hoct
      · ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        constructor
        · rintro ⟨hc, hwu, hwv, _⟩; exact ⟨hwv, hwu, hc⟩
        · rintro ⟨hwv, hwu, hc⟩
          refine ⟨hc, hwu, hwv, ?_⟩
          rw [Finset.mem_filter, Finset.mem_powersetCard]
          have hcard3 : ({u, v, w} : Finset (Fin (3 * m))).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [huv, hwu.symm]), Finset.card_pair hwv.symm]
          refine ⟨⟨Finset.subset_univ _, hcard3⟩, ?_⟩
          rw [fdf_blowup_mem_iff (brownBlock m i.val) huv hwu.symm hwv.symm, hc]
          exact hoct
      · ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨hc, hwu, hwv, hmem⟩
        rw [Finset.mem_filter] at hmem
        have htri := (fdf_blowup_mem_iff (brownBlock m i.val) huv hwu.symm hwv.symm).mp hmem.2
        rw [hc] at htri
        exact hoct htri
    rw [hfilt_eq]
    by_cases hoct : octTriple (brownBlock m i.val u) (brownBlock m i.val v) c = true
    · rw [if_pos hoct, if_pos hoct]
      have hfc := brownBlock_fiber_card m i.val hq c
      set S := Finset.univ.filter (fun w : Fin (3 * m) => brownBlock m i.val w = c)
      have hS : S.card = sz i.val c := hfc
      by_cases hu : brownBlock m i.val u = c <;> by_cases hv : brownBlock m i.val v = c
      · have huS : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
        have hvS : v ∈ S.erase u := Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩
        rw [Finset.card_erase_of_mem hvS, Finset.card_erase_of_mem huS, hS, if_pos hu, if_pos hv]
      · have huS : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
        have hvS : v ∉ S.erase u := fun h => hv (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).2
        rw [Finset.erase_eq_of_notMem hvS, Finset.card_erase_of_mem huS, hS, if_pos hu, if_neg hv, Nat.sub_zero]
      · have huS : u ∉ S := fun h => hu (Finset.mem_filter.mp h).2
        have hvS : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
        rw [Finset.erase_eq_of_notMem huS, Finset.card_erase_of_mem hvS, hS, if_neg hu, if_pos hv, Nat.sub_zero]
      · have huS : u ∉ S := fun h => hu (Finset.mem_filter.mp h).2
        have hvS : v ∉ S := fun h => hv (Finset.mem_filter.mp h).2
        rw [Finset.erase_eq_of_notMem huS, Finset.erase_eq_of_notMem hvS, hS, if_neg hu, if_neg hv]
        simp
    · rw [if_neg hoct, if_neg hoct, Finset.card_empty]
  -- Fast evaluation of the Fin 6 codegree sum using `octCounts_spec`!
  have hcodeg_eval : ∀ (q : ℕ) (hq : q ≤ m / 2) (a b : Fin 6),
      (sz q a ≥ 1) → (sz q b ≥ 1) → (a = b → sz q a ≥ 2) →
      let cd := ∑ c : Fin 6, if octTriple a b c = true then
        sz q c - (if a = c then 1 else 0) - (if b = c then 1 else 0) else 0
      (a = b → cd = m) ∧ (a ≠ b → m + 1 ≤ cd) := by
    intro q hq a b hsa hsb _
    -- Express the sum over c : Fin 6 in terms of octTopCount, octBotCount, octTriple a b a, octTriple a b b!
    have hsplit_c : (∑ c : Fin 6, if octTriple a b c = true then
        sz q c - (if a = c then 1 else 0) - (if b = c then 1 else 0) else 0) +
        (if octTriple a b a = true then 1 else 0) + (if octTriple a b b = true then 1 else 0) =
        octTopCount a b * (m - q) + octBotCount a b * q := by
      have hterm : ∀ c : Fin 6,
          (if octTriple a b c = true then
            sz q c - (if a = c then 1 else 0) - (if b = c then 1 else 0) else 0) +
          (if octTriple a b c = true ∧ a = c then 1 else 0) +
          (if octTriple a b c = true ∧ b = c then 1 else 0) =
          if octTriple a b c = true then sz q c else 0 := by
        intro c
        by_cases ho : octTriple a b c = true
        · rw [if_pos ho, if_pos ho]
          by_cases ha : a = c <;> by_cases hb : b = c
          · have ho3 : octTriple c c c = true := by rwa [ha, hb] at ho
            have := (octCounts_spec c c).1 rfl; rw [this.2.2.1] at ho3; contradiction
          · rw [if_pos ha, if_neg hb, if_pos ⟨ho, ha⟩, if_neg (by tauto)]
            have : 1 ≤ sz q c := ha ▸ hsa; omega
          · rw [if_neg ha, if_pos hb, if_neg (by tauto), if_pos ⟨ho, hb⟩]
            have : 1 ≤ sz q c := hb ▸ hsb; omega
          · rw [if_neg ha, if_neg hb, if_neg (by tauto), if_neg (by tauto)]; omega
        · simp [ho]
      have hsum_all := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin 6)) = Finset.univ) (fun c _ => hterm c)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum_all
      have h1 : (∑ c : Fin 6, if octTriple a b c = true ∧ a = c then 1 else 0) =
          if octTriple a b a = true then 1 else 0 := by
        rw [Finset.sum_eq_single a]
        · simp
        · intro c _ hca; rw [if_neg]; rintro ⟨_, h⟩; exact hca h.symm
        · intro h; exact absurd (Finset.mem_univ a) h
      have h2 : (∑ c : Fin 6, if octTriple a b c = true ∧ b = c then 1 else 0) =
          if octTriple a b b = true then 1 else 0 := by
        rw [Finset.sum_eq_single b]
        · simp
        · intro c _ hcb; rw [if_neg]; rintro ⟨_, h⟩; exact hcb h.symm
        · intro h; exact absurd (Finset.mem_univ b) h
      have h3 : (∑ c : Fin 6, if octTriple a b c = true then sz q c else 0) =
          octTopCount a b * (m - q) + octBotCount a b * q := by
        have hpart_tb : (∑ c : Fin 6, if octTriple a b c = true then sz q c else 0) =
            (∑ c : Fin 6, if c.val < 3 ∧ octTriple a b c = true then m - q else 0) +
            (∑ c : Fin 6, if ¬ c.val < 3 ∧ octTriple a b c = true then q else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun c _ => ?_
          dsimp only [sz]
          by_cases hc : c.val < 3 <;> by_cases ho : octTriple a b c = true <;> simp [hc, ho]
        rw [hpart_tb, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
          Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
        rfl
      rw [h1, h2, h3] at hsum_all
      exact hsum_all
    have hsp := octCounts_spec a b
    dsimp only [sz] at hsa hsb
    constructor
    · intro hab
      obtain ⟨ht, hb, hoa, hob⟩ := hsp.1 hab
      rw [ht, hb, hoa, hob] at hsplit_c
      simp at hsplit_c
      omega
    · intro hne
      rcases hsp.2 hne with ⟨ht, hb, hnot2⟩ | ⟨ht, hb, hnot2⟩ | ⟨ht, hb, hoa, hob, hbot⟩
      · rw [ht, hb] at hsplit_c
        have hsum1 : (if octTriple a b a = true then 1 else 0) +
            (if octTriple a b b = true then 1 else 0) ≤ 1 := by
          by_cases h1 : octTriple a b a = true <;> by_cases h2 : octTriple a b b = true
          · exact absurd ⟨h1, h2⟩ hnot2
          · simp [h1, h2]
          · simp [h1, h2]
          · simp [h1, h2]
        omega
      · rw [ht, hb] at hsplit_c
        have hsum1 : (if octTriple a b a = true then 1 else 0) +
            (if octTriple a b b = true then 1 else 0) ≤ 1 := by
          by_cases h1 : octTriple a b a = true <;> by_cases h2 : octTriple a b b = true
          · exact absurd ⟨h1, h2⟩ hnot2
          · simp [h1, h2]
          · simp [h1, h2]
          · simp [h1, h2]
        omega
      · rw [ht, hb, hoa, hob] at hsplit_c; simp at hsplit_c
        have hqpos : 1 ≤ q := by
          rcases hbot with hna | hnb
          · simp [hna] at hsa; exact hsa
          · simp [hnb] at hsb; exact hsb
        omega
  -- Now prove all 4 claims of the theorem!
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro i e he; exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
  · intro i
    let adj : Fin (3 * m) → Fin (3 * m) → Prop :=
      fun u v => octAdj (brownBlock m i.val u) (brownBlock m i.val v) = true
    have hasym : ∀ u v, adj u v → ¬ adj v u := fun u v h1 h2 => octAdj_asym _ _ h1 h2
    have hc4 : ∀ a b c d : Fin (3 * m), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        adj a b → adj b c → adj c d → adj d a →
        adj a c ∨ adj c a ∨ adj b d ∨ adj d b := fun a b c d _ _ _ _ _ _ h1 h2 h3 h4 =>
      octAdj_no_c4 _ _ _ _ h1 h2 h3 h4
    exact ppl074_fon_der_flaass_k43_free adj hasym hc4
  · -- Edge count: 6 * (F i).card = ∑ u, ∑ v ≠ u, codeg(u, v) = 6 * (m^3 + 3 * m.choose 2 * m)!
    intro i
    have hq : i.val ≤ m / 2 := Nat.lt_succ_iff.mp i.isLt
    have h6 : 6 * (F i).card = ∑ u : Fin (3 * m), ∑ v ∈ Finset.univ.erase u,
        ((Finset.univ : Finset (Fin (3 * m))).filter
          (fun w => w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) ∈ F i)).card := by
      -- Count ordered distinct triples (u, v, w) with {u, v, w} ∈ F i in two ways.
      have hrhs : ∑ u : Fin (3 * m), ∑ v ∈ Finset.univ.erase u,
          ((Finset.univ : Finset (Fin (3 * m))).filter
            (fun w => w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) ∈ F i)).card =
          ∑ e ∈ F i, ∑ u : Fin (3 * m), ∑ v ∈ Finset.univ.erase u,
            ∑ w : Fin (3 * m), if w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) = e then 1 else 0 := by
        calc ∑ u : Fin (3 * m), ∑ v ∈ Finset.univ.erase u,
              ((Finset.univ : Finset (Fin (3 * m))).filter
                (fun w => w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) ∈ F i)).card
            = ∑ u : Fin (3 * m), ∑ v ∈ Finset.univ.erase u, ∑ w : Fin (3 * m),
                if w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) ∈ F i then 1 else 0 := by
              refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
              rw [Finset.card_filter]
          _ = ∑ u : Fin (3 * m), ∑ v ∈ Finset.univ.erase u, ∑ w : Fin (3 * m),
                ∑ e ∈ F i, if w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) = e then 1 else 0 := by
              refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
                Finset.sum_congr rfl fun w _ => ?_
              by_cases h : w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) ∈ F i
              · rw [if_pos h]
                have : (∑ e ∈ F i, if w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) = e then 1 else 0) =
                    ∑ e ∈ F i, if ({u, v, w} : Finset (Fin (3 * m))) = e then 1 else 0 :=
                  Finset.sum_congr rfl fun e _ => by simp [h.1, h.2.1]
                rw [this, Finset.sum_ite_eq _ _ (fun _ => 1), if_pos h.2.2]
              · rw [if_neg h]
                symm; refine Finset.sum_eq_zero fun e he => ?_
                rw [if_neg]; rintro ⟨h1, h2, rfl⟩; exact h ⟨h1, h2, he⟩
          _ = _ := by
              simp_rw [Finset.sum_comm (s := Finset.univ) (t := F i)]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun e _ => ?_
              rw [Finset.sum_comm]
      rw [hrhs]
      have heach : ∀ e ∈ F i,
          (∑ u : Fin (3 * m), ∑ v ∈ Finset.univ.erase u, ∑ w : Fin (3 * m),
            if w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) = e then 1 else 0) = 6 := by
        intro e he
        have he3 : e.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
        obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp he3
        -- Only u ∈ {x,y,z}, v ∈ {x,y,z} \ {u}, w ∈ {x,y,z} \ {u,v} contribute 1 -> 3 * 2 * 1 = 6!
        have hstep : ∀ u : Fin (3 * m),
            (∑ v ∈ Finset.univ.erase u, ∑ w : Fin (3 * m),
              if w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) = {x, y, z} then 1 else 0) =
            if u ∈ ({x, y, z} : Finset (Fin (3 * m))) then 2 else 0 := by
          intro u
          by_cases hu : u ∈ ({x, y, z} : Finset (Fin (3 * m)))
          · rw [if_pos hu]
            have hinner : ∀ v ∈ Finset.univ.erase u,
                (∑ w : Fin (3 * m),
                  if w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) = {x, y, z} then 1 else 0) =
                if v ∈ ({x, y, z} : Finset (Fin (3 * m))).erase u then 1 else 0 := by
              intro v hv
              have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
              by_cases hv3 : v ∈ ({x, y, z} : Finset (Fin (3 * m))).erase u
              · rw [if_pos hv3]
                have hcard1 : ((({x, y, z} : Finset (Fin (3 * m))).erase u).erase v).card = 1 := by
                  rw [Finset.card_erase_of_mem hv3, Finset.card_erase_of_mem hu,
                    Finset.card_insert_of_notMem (by simp [hxy, hxz]), Finset.card_pair hyz]
                obtain ⟨w0, hw0⟩ := Finset.card_eq_one.mp hcard1
                have hw0m := hw0 ▸ Finset.mem_singleton_self w0
                rw [Finset.mem_erase, Finset.mem_erase] at hw0m
                have hcond : ∀ w : Fin (3 * m),
                    (w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) = {x, y, z}) ↔ w = w0 := by
                  intro w
                  constructor
                  · rintro ⟨hwu, hwv, hset⟩
                    have hwm : w ∈ (({x, y, z} : Finset (Fin (3 * m))).erase u).erase v := by
                      rw [Finset.mem_erase, Finset.mem_erase]
                      refine ⟨hwv, hwu, hset ▸ by simp⟩
                    rw [hw0, Finset.mem_singleton] at hwm; exact hwm
                  · rintro rfl
                    refine ⟨hw0m.2.1, hw0m.1, ?_⟩
                    refine Finset.eq_of_subset_of_card_le ?_ ?_
                    · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
                      rcases ht with rfl | rfl | rfl
                      · exact hu
                      · exact Finset.mem_of_mem_erase hv3
                      · exact hw0m.2.2
                    · rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]), Finset.card_pair hyz,
                        Finset.card_insert_of_notMem (by simp [hvu.symm, hw0m.2.1.symm]),
                        Finset.card_pair hw0m.1.symm]
                simp_rw [hcond]
                simp
              · rw [if_neg hv3]
                refine Finset.sum_eq_zero fun w _ => ?_
                rw [if_neg]; rintro ⟨_, _, hset⟩
                have : v ∈ ({x, y, z} : Finset (Fin (3 * m))) := hset ▸ by simp
                exact hv3 (Finset.mem_erase.mpr ⟨hvu, this⟩)
            rw [Finset.sum_congr rfl hinner, Finset.sum_ite_mem, Finset.inter_eq_right.mpr
              (Finset.erase_subset_erase u (Finset.subset_univ _)),
              Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hu,
              Finset.card_insert_of_notMem (by simp [hxy, hxz]), Finset.card_pair hyz]
          · rw [if_neg hu]
            refine Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun w _ => ?_
            rw [if_neg]; rintro ⟨_, _, hset⟩
            exact hu (hset ▸ by simp)
        rw [Finset.sum_congr rfl (fun u _ => hstep u), Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_const, smul_eq_mul, Finset.card_insert_of_notMem (by simp [hxy, hxz]),
          Finset.card_pair hyz]
      rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    -- Now evaluate the RHS of h6 by grouping (u, v) over blocks (a, b) ∈ Fin 6 × Fin 6!
    have hrhs_eval : (∑ u : Fin (3 * m), ∑ v ∈ Finset.univ.erase u,
        ((Finset.univ : Finset (Fin (3 * m))).filter
          (fun w => w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) ∈ F i)).card) =
        ∑ a : Fin 6, ∑ b : Fin 6,
          (sz i.val a * (sz i.val b - if a = b then 1 else 0)) *
          (∑ c : Fin 6, if octTriple a b c = true then
            sz i.val c - (if a = c then 1 else 0) - (if b = c then 1 else 0) else 0) := by
      -- First rewrite inner term using `hcodeg`.
      have h1 : (∑ u : Fin (3 * m), ∑ v ∈ Finset.univ.erase u,
          ((Finset.univ : Finset (Fin (3 * m))).filter
            (fun w => w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) ∈ F i)).card) =
          ∑ u : Fin (3 * m), ∑ v ∈ Finset.univ.erase u,
            ∑ c : Fin 6, if octTriple (brownBlock m i.val u) (brownBlock m i.val v) c = true then
              sz i.val c - (if brownBlock m i.val u = c then 1 else 0) -
                (if brownBlock m i.val v = c then 1 else 0) else 0 :=
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v hv =>
          hcodeg i u v (Finset.mem_erase.mp hv).1.symm
      rw [h1]
      -- Group u by block a, v by block b!
      have hu_part : ∀ (g : Fin (3 * m) → ℕ),
          ∑ u : Fin (3 * m), g u =
          ∑ a : Fin 6, ∑ u ∈ Finset.univ.filter (fun u : Fin (3 * m) => brownBlock m i.val u = a), g u := by
        intro g
        rw [← Finset.sum_biUnion]
        · congr 1; ext u; simp
        · intro a1 _ a2 _ hne; rw [Function.onFun, Finset.disjoint_left]
          intro u h1 h2; simp only [Finset.mem_filter] at h1 h2
          exact hne (h1.2.symm.trans h2.2)
      rw [hu_part]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hinner_a : ∀ u ∈ Finset.univ.filter (fun u : Fin (3 * m) => brownBlock m i.val u = a),
          (∑ v ∈ Finset.univ.erase u,
            ∑ c : Fin 6, if octTriple (brownBlock m i.val u) (brownBlock m i.val v) c = true then
              sz i.val c - (if brownBlock m i.val u = c then 1 else 0) -
                (if brownBlock m i.val v = c then 1 else 0) else 0) =
          ∑ b : Fin 6, (sz i.val b - if a = b then 1 else 0) *
            (∑ c : Fin 6, if octTriple a b c = true then
              sz i.val c - (if a = c then 1 else 0) - (if b = c then 1 else 0) else 0) := by
        intro u hu
        have hua : brownBlock m i.val u = a := (Finset.mem_filter.mp hu).2
        have hv_part : ∀ (g : Fin (3 * m) → ℕ),
            ∑ v ∈ Finset.univ.erase u, g v =
            ∑ b : Fin 6, ∑ v ∈ (Finset.univ.erase u).filter (fun v => brownBlock m i.val v = b), g v := by
          intro g
          rw [← Finset.sum_biUnion]
          · congr 1; ext v; simp
          · intro b1 _ b2 _ hne; rw [Function.onFun, Finset.disjoint_left]
            intro v h1 h2; simp only [Finset.mem_filter] at h1 h2
            exact hne (h1.2.symm.trans h2.2)
        rw [hv_part]
        refine Finset.sum_congr rfl fun b _ => ?_
        have hconst : ∑ v ∈ (Finset.univ.erase u).filter (fun v => brownBlock m i.val v = b),
            (∑ c : Fin 6, if octTriple (brownBlock m i.val u) (brownBlock m i.val v) c = true then
              sz i.val c - (if brownBlock m i.val u = c then 1 else 0) -
                (if brownBlock m i.val v = c then 1 else 0) else 0) =
            ((Finset.univ.erase u).filter (fun v => brownBlock m i.val v = b)).card *
            (∑ c : Fin 6, if octTriple a b c = true then
              sz i.val c - (if a = c then 1 else 0) - (if b = c then 1 else 0) else 0) := by
          rw [Finset.sum_congr rfl (fun v hv => by rw [hua, (Finset.mem_filter.mp hv).2]),
            Finset.sum_const, smul_eq_mul]
        rw [hconst]
        congr 1
        have hflt : (Finset.univ.erase u).filter (fun v => brownBlock m i.val v = b) =
            (Finset.univ.filter (fun v => brownBlock m i.val v = b)).erase u := by
          ext v; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]; tauto
        rw [hflt]
        have hfc := brownBlock_fiber_card m i.val (by omega) b
        by_cases hab : a = b
        · have hu_in : u ∈ Finset.univ.filter (fun v => brownBlock m i.val v = b) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ u, hab ▸ hua⟩
          rw [Finset.card_erase_of_mem hu_in, hfc, if_pos hab]
        · have hu_nin : u ∉ Finset.univ.filter (fun v => brownBlock m i.val v = b) :=
            fun h => hab (hua.symm.trans (Finset.mem_filter.mp h).2)
          rw [Finset.erase_eq_of_notMem hu_nin, hfc, if_neg hab, Nat.sub_zero]
      rw [Finset.sum_congr rfl hinner_a, Finset.sum_const, smul_eq_mul,
        brownBlock_fiber_card m i.val (by omega) a, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      dsimp only [sz]; ring
    rw [hrhs_eval] at h6
    -- Evaluate the closed-form Fin 6 triple sum algebraically in p = m - q and q!
    set q := i.val
    set p := m - q
    have hpq : p + q = m := Nat.sub_add_cancel (by omega)
    have hp1 : 1 ≤ p := by omega
    have hpoly : (∑ a : Fin 6, ∑ b : Fin 6,
          (sz q a * (sz q b - if a = b then 1 else 0)) *
          (∑ c : Fin 6, if octTriple a b c = true then
            sz q c - (if a = c then 1 else 0) - (if b = c then 1 else 0) else 0)) =
        6 * (m ^ 3 + 3 * m.choose 2 * m) := by
      have hm2 := choose_two_mul_two m
      have hsub_m : 6 * (m ^ 3 + 3 * m.choose 2 * m) = 6 * m ^ 3 + 9 * m * (m - 1) * m := by
        nlinarith
      rw [hsub_m]
      -- Work in ℤ to avoid Nat subtraction pain!
      suffices hZ : ((∑ a : Fin 6, ∑ b : Fin 6,
          (sz q a * (sz q b - if a = b then 1 else 0)) *
          (∑ c : Fin 6, if octTriple a b c = true then
            sz q c - (if a = c then 1 else 0) - (if b = c then 1 else 0) else 0) : ℕ) : ℤ) =
          ((6 * m ^ 3 + 9 * m * (m - 1) * m : ℕ) : ℤ) by exact_mod_cast hZ
      -- Move into a single triple sum in ℤ!
      have hcast_term : ∀ a b c : Fin 6,
          (((sz q a * (sz q b - if a = b then 1 else 0)) *
            (if octTriple a b c = true then
              sz q c - (if a = c then 1 else 0) - (if b = c then 1 else 0) else 0) : ℕ) : ℤ) =
          if octTriple a b c = true then
            (sz q a : ℤ) * (sz q b : ℤ) * (sz q c : ℤ)
            - (if a = b then (sz q a : ℤ) * (sz q c : ℤ) else 0)
            - (if a = c then (sz q a : ℤ) * (sz q b : ℤ) else 0)
            - (if b = c then (sz q a : ℤ) * (sz q b : ℤ) else 0)
          else 0 := by
        intro a b c
        by_cases ho : octTriple a b c = true
        · rw [if_pos ho, if_pos ho]
          have hnot3 : ¬ (a = b ∧ b = c) := by
            rintro ⟨rfl, rfl⟩
            have := octPoly_coeff_30.2.2.2.2.2.2.2.2.2.2.2.2.1 a
            rw [this] at ho; contradiction
          have hsub_mul : ∀ x : ℕ, ((x * (x - 1) : ℕ) : ℤ) = (x : ℤ) * ((x : ℤ) - 1) := by
            intro x; cases x with | zero => simp | succ x' => push_cast; ring
          by_cases hab : a = b
          · subst hab
            have hac : a ≠ c := fun h => hnot3 ⟨rfl, h⟩
            simp only [ite_true, if_neg hac, Nat.sub_zero]
            push_cast [hsub_mul]
            ring
          · by_cases hac : a = c
            · subst hac
              have hbc : b ≠ a := fun h => hab h.symm
              simp only [ite_true, if_neg hab, if_neg hbc, Nat.sub_zero]
              have hrw : (sz q a * sz q b) * (sz q a - 1) = (sz q a * (sz q a - 1)) * sz q b := by ring
              rw [hrw]
              push_cast [hsub_mul]
              ring
            · by_cases hbc : b = c
              · subst hbc
                simp only [ite_true, if_neg hab, Nat.sub_zero]
                have hrw : (sz q a * sz q b) * (sz q b - 1) = sz q a * (sz q b * (sz q b - 1)) := by ring
                rw [hrw]
                push_cast [hsub_mul]
                ring
              · simp only [if_neg hab, if_neg hac, if_neg hbc, Nat.sub_zero]
                push_cast; ring
        · simp [ho]
      have hrewrite : ((∑ a : Fin 6, ∑ b : Fin 6,
          (sz q a * (sz q b - if a = b then 1 else 0)) *
          (∑ c : Fin 6, if octTriple a b c = true then
            sz q c - (if a = c then 1 else 0) - (if b = c then 1 else 0) else 0) : ℕ) : ℤ) =
          (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
            if octTriple a b c = true then (sz q a : ℤ) * (sz q b : ℤ) * (sz q c : ℤ) else 0)
          - (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
            if octTriple a b c = true ∧ a = b then (sz q a : ℤ) * (sz q c : ℤ) else 0)
          - (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
            if octTriple a b c = true ∧ a = c then (sz q a : ℤ) * (sz q b : ℤ) else 0)
          - (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
            if octTriple a b c = true ∧ b = c then (sz q a : ℤ) * (sz q b : ℤ) else 0) := by
        simp_rw [Finset.mul_sum]
        simp_rw [Nat.cast_sum]
        simp_rw [hcast_term]
        simp_rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => ?_
        by_cases ho : octTriple a b c = true
        · simp [ho]
        · simp [ho]
      rw [hrewrite]
      have hcnt : ∀ (P : Fin 6 → Fin 6 → Fin 6 → Prop) [∀ a b c, Decidable (P a b c)] (K : ℤ),
          (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6, if P a b c then K else 0) =
          ((∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6, if P a b c then (1 : ℕ) else 0 : ℕ) : ℤ) * K := by
        intro P _ K
        push_cast
        simp_rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> simp
      -- Compute the cubic sum = 15 * (p + q)^3 = 15 * m^3!
      have hcubic : (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
          if octTriple a b c = true then (sz q a : ℤ) * (sz q b : ℤ) * (sz q c : ℤ) else 0) =
          15 * ((p : ℤ) + (q : ℤ)) ^ 3 := by
        have hdecomp : ∀ a b c : Fin 6,
            (if octTriple a b c = true then (sz q a : ℤ) * (sz q b : ℤ) * (sz q c : ℤ) else 0) =
            (if octTriple a b c = true ∧ a.val < 3 ∧ b.val < 3 ∧ c.val < 3 then (p : ℤ)^3 else 0) +
            (if octTriple a b c = true ∧ a.val < 3 ∧ b.val < 3 ∧ ¬ c.val < 3 then (p : ℤ)^2 * (q : ℤ) else 0) +
            (if octTriple a b c = true ∧ a.val < 3 ∧ ¬ b.val < 3 ∧ c.val < 3 then (p : ℤ)^2 * (q : ℤ) else 0) +
            (if octTriple a b c = true ∧ ¬ a.val < 3 ∧ b.val < 3 ∧ c.val < 3 then (p : ℤ)^2 * (q : ℤ) else 0) +
            (if octTriple a b c = true ∧ a.val < 3 ∧ ¬ b.val < 3 ∧ ¬ c.val < 3 then (p : ℤ) * (q : ℤ)^2 else 0) +
            (if octTriple a b c = true ∧ ¬ a.val < 3 ∧ b.val < 3 ∧ ¬ c.val < 3 then (p : ℤ) * (q : ℤ)^2 else 0) +
            (if octTriple a b c = true ∧ ¬ a.val < 3 ∧ ¬ b.val < 3 ∧ c.val < 3 then (p : ℤ) * (q : ℤ)^2 else 0) +
            (if octTriple a b c = true ∧ ¬ a.val < 3 ∧ ¬ b.val < 3 ∧ ¬ c.val < 3 then (q : ℤ)^3 else 0) := by
          intro a b c
          dsimp only [sz]
          by_cases ho : octTriple a b c = true <;>
          by_cases ha : a.val < 3 <;> by_cases hb : b.val < 3 <;> by_cases hc : c.val < 3 <;>
          simp only [ho, ha, hb, hc, and_self, and_true, and_false,
            not_true_eq_false, not_false_eq_true, ↓reduceIte, add_zero, zero_add] <;>
          (try rfl) <;> ring
        simp_rw [hdecomp, Finset.sum_add_distrib]
        rw [hcnt (fun a b c => octTriple a b c = true ∧ a.val < 3 ∧ b.val < 3 ∧ c.val < 3) ((p : ℤ)^3),
          hcnt (fun a b c => octTriple a b c = true ∧ a.val < 3 ∧ b.val < 3 ∧ ¬ c.val < 3) ((p : ℤ)^2 * (q : ℤ)),
          hcnt (fun a b c => octTriple a b c = true ∧ a.val < 3 ∧ ¬ b.val < 3 ∧ c.val < 3) ((p : ℤ)^2 * (q : ℤ)),
          hcnt (fun a b c => octTriple a b c = true ∧ ¬ a.val < 3 ∧ b.val < 3 ∧ c.val < 3) ((p : ℤ)^2 * (q : ℤ)),
          hcnt (fun a b c => octTriple a b c = true ∧ a.val < 3 ∧ ¬ b.val < 3 ∧ ¬ c.val < 3) ((p : ℤ) * (q : ℤ)^2),
          hcnt (fun a b c => octTriple a b c = true ∧ ¬ a.val < 3 ∧ b.val < 3 ∧ ¬ c.val < 3) ((p : ℤ) * (q : ℤ)^2),
          hcnt (fun a b c => octTriple a b c = true ∧ ¬ a.val < 3 ∧ ¬ b.val < 3 ∧ c.val < 3) ((p : ℤ) * (q : ℤ)^2),
          hcnt (fun a b c => octTriple a b c = true ∧ ¬ a.val < 3 ∧ ¬ b.val < 3 ∧ ¬ c.val < 3) ((q : ℤ)^3)]
        rcases octPoly_coeff_30 with ⟨c1, c2, c3, c4, c5, c6, c7, c8, _⟩
        rw [c1, c2, c3, c4, c5, c6, c7, c8]
        push_cast; ring
      -- Compute the quadratic subtraction sum for `a = b`: equals 3 * (p + q)^2!
      have hquad_ab : (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
          if octTriple a b c = true ∧ a = b then (sz q a : ℤ) * (sz q c : ℤ) else 0) =
          3 * ((p : ℤ) + (q : ℤ)) ^ 2 := by
        have hdecomp : ∀ a b c : Fin 6,
            (if octTriple a b c = true ∧ a = b then (sz q a : ℤ) * (sz q c : ℤ) else 0) =
            (if octTriple a b c = true ∧ a = b ∧ a.val < 3 ∧ c.val < 3 then (p : ℤ)^2 else 0) +
            (if octTriple a b c = true ∧ a = b ∧ a.val < 3 ∧ ¬ c.val < 3 then (p : ℤ) * (q : ℤ) else 0) +
            (if octTriple a b c = true ∧ a = b ∧ ¬ a.val < 3 ∧ c.val < 3 then (p : ℤ) * (q : ℤ) else 0) +
            (if octTriple a b c = true ∧ a = b ∧ ¬ a.val < 3 ∧ ¬ c.val < 3 then (q : ℤ)^2 else 0) := by
          intro a b c
          dsimp only [sz]
          by_cases hab : a = b
          · subst hab
            by_cases ho : octTriple a a c = true <;>
            by_cases ha : a.val < 3 <;> by_cases hc : c.val < 3 <;>
            simp only [ho, ha, hc, and_self, and_true, and_false,
              not_true_eq_false, not_false_eq_true, ↓reduceIte, add_zero, zero_add] <;>
            (try rfl) <;> ring
          · simp [hab]
        simp_rw [hdecomp, Finset.sum_add_distrib]
        rw [hcnt (fun a b c => octTriple a b c = true ∧ a = b ∧ a.val < 3 ∧ c.val < 3) ((p : ℤ)^2),
          hcnt (fun a b c => octTriple a b c = true ∧ a = b ∧ a.val < 3 ∧ ¬ c.val < 3) ((p : ℤ) * (q : ℤ)),
          hcnt (fun a b c => octTriple a b c = true ∧ a = b ∧ ¬ a.val < 3 ∧ c.val < 3) ((p : ℤ) * (q : ℤ)),
          hcnt (fun a b c => octTriple a b c = true ∧ a = b ∧ ¬ a.val < 3 ∧ ¬ c.val < 3) ((q : ℤ)^2)]
        rcases octPoly_coeff_30 with ⟨_, _, _, _, _, _, _, _, d1, d2, d3, d4, _⟩
        rw [d1, d2, d3, d4]
        push_cast; ring
      -- By symmetry of octTriple, the `a = c` and `b = c` sums both equal `hquad_ab`!
      have hsym := octPoly_coeff_30.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hquad_ac : (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
          if octTriple a b c = true ∧ a = c then (sz q a : ℤ) * (sz q b : ℤ) else 0) =
          3 * ((p : ℤ) + (q : ℤ)) ^ 2 := by
        rw [← hquad_ab]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
        rw [(hsym a c b).2]
      have hquad_bc : (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6,
          if octTriple a b c = true ∧ b = c then (sz q a : ℤ) * (sz q b : ℤ) else 0) =
          3 * ((p : ℤ) + (q : ℤ)) ^ 2 := by
        rw [← hquad_ab]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
        have h1 : octTriple a b c = octTriple b c a := by
          rw [(hsym a b c).1, (hsym b a c).2]
        rw [h1]
        by_cases hbc : b = c <;> simp [hbc, mul_comm]
      rw [hcubic, hquad_ab, hquad_ac, hquad_bc]
      have hmZ : (p : ℤ) + (q : ℤ) = (m : ℤ) := by exact_mod_cast hpq
      have hm1Z : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := Nat.cast_sub (by omega)
      rw [hmZ]
      push_cast [hm1Z]
      ring
    omega
  · -- Pairwise non-isomorphic: count unordered pairs with codegree ≤ m!
    intro i j hij σ hEq
    -- Invariantly, for any 3-graph H, let lowPairs H = number of 2-subsets {u,v} with codegree ≤ m.
    let lowPairs : Finset (Finset (Fin (3 * m))) → ℕ := fun H =>
      (((Finset.univ : Finset (Fin (3 * m))).powersetCard 2).filter (fun e =>
        (H.filter (fun t => e ⊆ t)).card ≤ m)).card
    -- Isomorphism σ preserves lowPairs!
    have hlow_inv : lowPairs ((F i).image (Finset.image σ)) = lowPairs (F i) := by
      dsimp only [lowPairs]
      symm
      refine Finset.card_bij (fun e _ => e.image σ) ?_ ?_ ?_
      · intro e he
        rw [Finset.mem_filter, Finset.mem_powersetCard] at he ⊢
        refine ⟨⟨Finset.subset_univ _, by rw [Finset.card_image_of_injective _ σ.injective, he.1.2]⟩, ?_⟩
        have hcard_eq : (((F i).image (Finset.image σ)).filter (fun t => e.image σ ⊆ t)).card =
            ((F i).filter (fun t => e ⊆ t)).card := by
          symm
          refine Finset.card_bij (fun t _ => t.image σ) ?_ ?_ ?_
          · intro t ht
            rw [Finset.mem_filter] at ht ⊢
            exact ⟨Finset.mem_image_of_mem _ ht.1, Finset.image_subset_image ht.2⟩
          · intro t1 _ t2 _ h
            exact Finset.image_injective σ.injective h
          · intro t' ht'
            rw [Finset.mem_filter] at ht'
            rcases Finset.mem_image.mp ht'.1 with ⟨t, htF, rfl⟩
            refine ⟨t, Finset.mem_filter.mpr ⟨htF, ?_⟩, rfl⟩
            intro x hx
            have hx' : σ x ∈ t.image σ := ht'.2 (Finset.mem_image_of_mem σ hx)
            rcases Finset.mem_image.mp hx' with ⟨y, hy, hyx⟩
            rwa [← σ.injective hyx]
        rw [hcard_eq]; exact he.2
      · intro e1 _ e2 _ h; exact Finset.image_injective σ.injective h
      · intro e' he'
        rw [Finset.mem_filter, Finset.mem_powersetCard] at he'
        let e := e'.image σ.symm
        have he_img : e.image σ = e' := by
          ext y; simp [e, Equiv.apply_symm_apply]
        refine ⟨e, ?_, he_img⟩
        rw [Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨Finset.subset_univ _, by rw [Finset.card_image_of_injective _ σ.symm.injective, he'.1.2]⟩, ?_⟩
        have hcard_eq : ((F i).filter (fun t => e ⊆ t)).card =
            (((F i).image (Finset.image σ)).filter (fun t => e' ⊆ t)).card := by
          refine Finset.card_bij (fun t _ => t.image σ) ?_ ?_ ?_
          · intro t ht
            rw [Finset.mem_filter] at ht ⊢
            exact ⟨Finset.mem_image_of_mem _ ht.1, he_img ▸ Finset.image_subset_image ht.2⟩
          · intro t1 _ t2 _ h; exact Finset.image_injective σ.injective h
          · intro t' ht'
            rw [Finset.mem_filter] at ht'
            rcases Finset.mem_image.mp ht'.1 with ⟨t, htF, rfl⟩
            refine ⟨t, Finset.mem_filter.mpr ⟨htF, ?_⟩, rfl⟩
            intro x hx
            have hx' : σ x ∈ t.image σ := ht'.2 (he_img ▸ Finset.mem_image_of_mem σ hx)
            rcases Finset.mem_image.mp hx' with ⟨y, hy, hyx⟩
            rwa [← σ.injective hyx]
        rw [hcard_eq]; exact he'.2
    -- Compute lowPairs (F k) = 3 * (m - k.val).choose 2 + 3 * k.val.choose 2!
    have hlow_eval : ∀ k : Fin (m / 2 + 1),
        lowPairs (F k) = 3 * (m - k.val).choose 2 + 3 * k.val.choose 2 := by
      intro k
      have hqk : k.val ≤ m / 2 := Nat.lt_succ_iff.mp k.isLt
      -- A 2-set {u, v} has codegree ≤ m iff brownBlock m k.val u = brownBlock m k.val v!
      have hiff : ∀ e ∈ (Finset.univ : Finset (Fin (3 * m))).powersetCard 2,
          ((F k).filter (fun t => e ⊆ t)).card ≤ m ↔
          ∃ b : Fin 6, e ⊆ Finset.univ.filter (fun v => brownBlock m k.val v = b) := by
        intro e he
        obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp he).2
        have hcd_eq : ((F k).filter (fun t => ({u, v} : Finset (Fin (3 * m))) ⊆ t)).card =
            ((Finset.univ : Finset (Fin (3 * m))).filter
              (fun w => w ≠ u ∧ w ≠ v ∧ ({u, v, w} : Finset (Fin (3 * m))) ∈ F k)).card := by
          symm
          refine Finset.card_bij (fun w _ => {u, v, w}) ?_ ?_ ?_
          · intro w hw
            rw [Finset.mem_filter] at hw ⊢
            refine ⟨hw.2.2.2, ?_⟩
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto
          · intro w1 hw1 w2 hw2 heq
            rw [Finset.mem_filter] at hw1 hw2
            have hw1m : w1 ∈ ({u, v, w2} : Finset (Fin (3 * m))) := heq ▸ by simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw1m
            rcases hw1m with h | h | h
            · exact absurd h hw1.2.1
            · exact absurd h hw1.2.2.1
            · exact h
          · intro t ht
            rw [Finset.mem_filter] at ht
            have ht3 : t.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp ht.1).1).2
            have hdc : (t \ {u, v}).card = 1 := by
              rw [Finset.card_sdiff_of_subset ht.2, ht3, Finset.card_pair huv]
            obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hdc
            have hwm := Finset.mem_sdiff.mp (hw ▸ Finset.mem_singleton_self w)
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwm
            have hteq : ({u, v, w} : Finset (Fin (3 * m))) = t := by
              refine Finset.eq_of_subset_of_card_le ?_ ?_
              · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl
                · exact ht.2 (by simp)
                · exact ht.2 (by simp)
                · exact hwm.1
              · rw [ht3, Finset.card_insert_of_notMem (by simp [huv, Ne.symm hwm.2.1]),
                  Finset.card_pair (Ne.symm hwm.2.2)]
            exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwm.2.1, hwm.2.2, hteq.symm ▸ ht.1⟩, hteq⟩
        rw [hcd_eq, hcodeg k u v huv]
        have hsa : 1 ≤ sz k.val (brownBlock m k.val u) := by
          dsimp only [sz]
          rw [← brownBlock_fiber_card m k.val (by omega)]
          exact Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, rfl⟩⟩
        have hsb : 1 ≤ sz k.val (brownBlock m k.val v) := by
          dsimp only [sz]
          rw [← brownBlock_fiber_card m k.val (by omega)]
          exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, rfl⟩⟩
        have hab2 : brownBlock m k.val u = brownBlock m k.val v →
            2 ≤ sz k.val (brownBlock m k.val u) := by
          intro heqb
          dsimp only [sz]
          rw [← brownBlock_fiber_card m k.val (by omega)]
          have hsub2 : ({u, v} : Finset (Fin (3 * m))) ⊆
              Finset.univ.filter (fun w => brownBlock m k.val w = brownBlock m k.val u) := by
            intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heqb.symm⟩
          exact (Finset.card_pair huv).symm.trans_le (Finset.card_le_card hsub2)
        have hev := hcodeg_eval k.val hqk (brownBlock m k.val u) (brownBlock m k.val v) hsa hsb hab2
        constructor
        · intro hle
          by_cases heqb : brownBlock m k.val u = brownBlock m k.val v
          · refine ⟨brownBlock m k.val u, ?_⟩
            intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heqb.symm⟩
          · have := hev.2 heqb; omega
        · rintro ⟨b, hb⟩
          have hu_b : brownBlock m k.val u = b := (Finset.mem_filter.mp (hb (by simp))).2
          have hv_b : brownBlock m k.val v = b := (Finset.mem_filter.mp (hb (by simp))).2
          rw [hev.1 (hu_b.trans hv_b.symm)]
      -- Thus the filtered set equals biUnion_{b : Fin 6} (fiber b).powersetCard 2!
      have heq_set : (((Finset.univ : Finset (Fin (3 * m))).powersetCard 2).filter (fun e =>
          ((F k).filter (fun t => e ⊆ t)).card ≤ m)) =
          (Finset.univ : Finset (Fin 6)).biUnion
            (fun b => (Finset.univ.filter (fun v : Fin (3 * m) => brownBlock m k.val v = b)).powersetCard 2) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and,
          Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨_, he2⟩, hcd⟩
          obtain ⟨b, hb⟩ := (hiff e (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, he2⟩)).mp hcd
          exact ⟨b, hb, he2⟩
        · rintro ⟨b, hb, he2⟩
          refine ⟨⟨Finset.subset_univ e, he2⟩, ?_⟩
          exact (hiff e (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, he2⟩)).mpr ⟨b, hb⟩
      dsimp only [lowPairs]
      rw [heq_set, Finset.card_biUnion]
      · simp_rw [Finset.card_powersetCard, brownBlock_fiber_card m k.val (by omega)]
        simp only [Fin.sum_univ_six, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two,
          show (0 : ℕ) < 3 by omega, show (1 : ℕ) < 3 by omega, show (2 : ℕ) < 3 by omega,
          show ¬ ((3 : Fin 6).val < 3) by decide, show ¬ ((4 : Fin 6).val < 3) by decide,
          show ¬ ((5 : Fin 6).val < 3) by decide, ite_true, ite_false]
        ring
      · intro b1 _ b2 _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro e h1 h2
        rw [Finset.mem_powersetCard] at h1 h2
        obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < e.card)
        have h1u := (Finset.mem_filter.mp (h1.1 hu)).2
        have h2u := (Finset.mem_filter.mp (h2.1 hu)).2
        exact hne (h1u.symm.trans h2u)
    have hlow_eq : lowPairs (F i) = lowPairs (F j) := by
      rw [← hlow_inv, hEq]
    rw [hlow_eval i, hlow_eval j] at hlow_eq
    have hi_le : i.val ≤ m / 2 := Nat.lt_succ_iff.mp i.isLt
    have hj_le : j.val ≤ m / 2 := Nat.lt_succ_iff.mp j.isLt
    have h1 := choose_two_mul_two (m - i.val)
    have h2 := choose_two_mul_two i.val
    have h3 := choose_two_mul_two (m - j.val)
    have h4 := choose_two_mul_two j.val
    -- 2 * (C(m-q,2) + C(q,2)) = (m-q)(m-q-1) + q(q-1) = 2q^2 - 2mq + m^2 - m, strictly decreasing on q ≤ m/2!
    have hval_ne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hquad : ((m - i.val) * (m - i.val - 1) + i.val * (i.val - 1)) =
        ((m - j.val) * (m - j.val - 1) + j.val * (j.val - 1)) := by omega
    have hquadZ : (((m : ℤ) - (i.val : ℤ)) * ((m : ℤ) - (i.val : ℤ) - 1) +
        (i.val : ℤ) * ((i.val : ℤ) - 1)) =
        (((m : ℤ) - (j.val : ℤ)) * ((m : ℤ) - (j.val : ℤ) - 1) +
        (j.val : ℤ) * ((j.val : ℤ) - 1)) := by
      -- Careful when i.val = 0 or j.val = 0: q * (q - 1) = q * (q - 1) in ℤ too since 0 * (-1) = 0!
      have hcast : ∀ a : ℕ, ((a * (a - 1) : ℕ) : ℤ) = (a : ℤ) * ((a : ℤ) - 1) := by
        intro a; cases a with | zero => simp | succ a' => push_cast; ring
      have hZ : (((m - i.val) * (m - i.val - 1) + i.val * (i.val - 1) : ℕ) : ℤ) =
          (((m - j.val) * (m - j.val - 1) + j.val * (j.val - 1) : ℕ) : ℤ) := by exact_mod_cast hquad
      push_cast [hcast] at hZ
      have hmi : ((m - i.val : ℕ) : ℤ) = (m : ℤ) - (i.val : ℤ) := Nat.cast_sub (by omega)
      have hmj : ((m - j.val : ℕ) : ℤ) = (m : ℤ) - (j.val : ℤ) := Nat.cast_sub (by omega)
      rw [hmi, hmj] at hZ
      exact hZ
    have hfact : 2 * ((i.val : ℤ) - (j.val : ℤ)) * ((i.val : ℤ) + (j.val : ℤ) - (m : ℤ)) = 0 := by
      linarith
    have h1ne : (i.val : ℤ) - (j.val : ℤ) ≠ 0 := by omega
    have h2ne : (i.val : ℤ) + (j.val : ℤ) - (m : ℤ) ≠ 0 := by omega
    exact absurd hfact (mul_ne_zero (mul_ne_zero (by norm_num) h1ne) h2ne)

/-! ### Section 4: Certified 4-Square Rational Flag-Algebra SOS Upper Bound (`289 / 500 = 0.578`) -/

private def sosV0 : Fin 8 → ℤ
  | 0 => -2 | 1 => 1 | 2 => 1 | 3 => -2 | 4 => 1 | 5 => -2 | 6 => -2 | 7 => 4

private def sosV1 : Fin 8 → ℤ
  | 0 => -3 | 1 => -4 | 2 => -4 | 3 => 3 | 4 => -4 | 5 => 3 | 6 => 3 | 7 => 1

private def sosV2 : Fin 8 → ℤ
  | 0 => 0 | 1 => -5 | 2 => 5 | 3 => 0 | 4 => 0 | 5 => -2 | 6 => 2 | 7 => 0

private def sosV3 : Fin 8 → ℤ
  | 0 => 0 | 1 => -3 | 2 => 3 | 3 => 0 | 4 => 0 | 5 => -2 | 6 => 2 | 7 => 0

private def sosPairScore (et : Bool) (fx fy : Fin 8) : ℤ :=
  if et then 55 * (sosV3 fx * sosV3 fy)
  else 25 * (sosV0 fx * sosV0 fy) + 14 * (sosV1 fx * sosV1 fy) + 5 * (sosV2 fx * sosV2 fy)

private lemma sosPairScore_diag_le : ∀ (et : Bool) (fx : Fin 8), sosPairScore et fx fx ≤ 495 := by
  decide

private def mkFlagCode (b0 b1 b2 : Bool) : Fin 8 :=
  ⟨(if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0), by
    cases b0 <;> cases b1 <;> cases b2 <;> decide⟩

/-- Sum of `sosPairScore` over all 12 permutations of `(a,b,c)` (6) and `(x,y)` (2). -/
private def sym12Score (eT bx0 bx1 bx2 by0 by1 by2 : Bool) : ℤ :=
  let term (p0 p1 p2 q0 q1 q2 : Bool) : ℤ :=
    sosPairScore eT (mkFlagCode p0 p1 p2) (mkFlagCode q0 q1 q2) +
    sosPairScore eT (mkFlagCode q0 q1 q2) (mkFlagCode p0 p1 p2)
  term bx0 bx1 bx2 by0 by1 by2 +
  term bx1 bx0 bx2 by1 by0 by2 +
  term bx0 bx2 bx1 by0 by2 by1 +
  term bx2 bx0 bx1 by2 by0 by1 +
  term bx1 bx2 bx0 by1 by2 by0 +
  term bx2 bx1 bx0 by2 by1 by0

/-- Compact `S_3`-invariant evaluation of `sym12Score` in terms of `(dx, dy, mxy)`. -/
private def fastTripleScore (eT bx0 bx1 bx2 by0 by1 by2 : Bool) : ℤ :=
  let dx : ℕ := (if bx0 then 1 else 0) + (if bx1 then 1 else 0) + (if bx2 then 1 else 0)
  let dy : ℕ := (if by0 then 1 else 0) + (if by1 then 1 else 0) + (if by2 then 1 else 0)
  let mxy : ℕ := (if bx0 && by0 then 1 else 0) + (if bx1 && by1 then 1 else 0) +
    (if bx2 && by2 then 1 else 0)
  let stdTerm (α β : ℤ) : ℤ :=
    if dx = 1 ∧ dy = 1 then 4 * α * α * (if mxy = 1 then 2 else -1)
    else if (dx = 1 ∧ dy = 2) ∨ (dx = 2 ∧ dy = 1) then -4 * α * β * (if mxy = 0 then 2 else -1)
    else if dx = 2 ∧ dy = 2 then 4 * β * β * (if mxy = 2 then 2 else -1)
    else 0
  if eT then
    55 * stdTerm (-3) (-2)
  else
    let c0 : ℕ → ℤ | 0 => -2 | 1 => 1 | 2 => -2 | _ => 4
    let c1 : ℕ → ℤ | 0 => -3 | 1 => -4 | 2 => 3 | _ => 1
    12 * (25 * (c0 dx * c0 dy) + 14 * (c1 dx * c1 dy)) + 5 * stdTerm (-5) (-2)

private lemma sym12Score_eq_fast :
    ∀ eT bx0 bx1 bx2 by0 by1 by2 : Bool,
      sym12Score eT bx0 bx1 bx2 by0 by1 by2 = fastTripleScore eT bx0 bx1 bx2 by0 by1 by2 := by
  decide

private def maskBit (m : Fin 1024) (i : Fin 10) : Bool :=
  decide ((m.val / (2 ^ i.val)) % 2 = 1)

private def maskEdgeCount (m : Fin 1024) : ℤ :=
  (if maskBit m 0 then 1 else 0) + (if maskBit m 1 then 1 else 0) +
  (if maskBit m 2 then 1 else 0) + (if maskBit m 3 then 1 else 0) +
  (if maskBit m 4 then 1 else 0) + (if maskBit m 5 then 1 else 0) +
  (if maskBit m 6 then 1 else 0) + (if maskBit m 7 then 1 else 0) +
  (if maskBit m 8 then 1 else 0) + (if maskBit m 9 then 1 else 0)

private def maskIsK4Free (m : Fin 1024) : Bool :=
  !(maskBit m 0 && maskBit m 1 && maskBit m 3 && maskBit m 6) &&
  !(maskBit m 0 && maskBit m 2 && maskBit m 4 && maskBit m 7) &&
  !(maskBit m 1 && maskBit m 2 && maskBit m 5 && maskBit m 8) &&
  !(maskBit m 3 && maskBit m 4 && maskBit m 5 && maskBit m 9) &&
  !(maskBit m 6 && maskBit m 7 && maskBit m 8 && maskBit m 9)

private def fastPhiMask (m : Fin 1024) : ℤ :=
  let b := maskBit m
  fastTripleScore (b 0) (b 1) (b 3) (b 6) (b 2) (b 4) (b 7) +
  fastTripleScore (b 1) (b 0) (b 3) (b 6) (b 2) (b 5) (b 8) +
  fastTripleScore (b 2) (b 0) (b 4) (b 7) (b 1) (b 5) (b 8) +
  fastTripleScore (b 3) (b 0) (b 1) (b 6) (b 4) (b 5) (b 9) +
  fastTripleScore (b 4) (b 0) (b 2) (b 7) (b 3) (b 5) (b 9) +
  fastTripleScore (b 5) (b 1) (b 2) (b 8) (b 3) (b 4) (b 9) +
  fastTripleScore (b 6) (b 0) (b 1) (b 3) (b 7) (b 8) (b 9) +
  fastTripleScore (b 7) (b 0) (b 2) (b 4) (b 6) (b 8) (b 9) +
  fastTripleScore (b 8) (b 1) (b 2) (b 5) (b 6) (b 7) (b 9) +
  fastTripleScore (b 9) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8)

/-- **Kernel-Verified 5-Vertex 4-Square Rational SOS Certificate (`0` `native_decide`)**:
Split `Fin 1024` as `32 × 32` so kernel `decide` stays at recursion depth `≤ 32`. -/
private lemma sos_cert_32x32 :
    ∀ hi lo : Fin 32,
      let m : Fin 1024 := ⟨hi.val * 32 + lo.val, by omega⟩
      maskIsK4Free m = true → 4800 * maskEdgeCount m + fastPhiMask m ≤ 27744 := by
  decide

private lemma sos_cert_1024 :
    ∀ m : Fin 1024, maskIsK4Free m = true → 4800 * maskEdgeCount m + fastPhiMask m ≤ 27744 := by
  intro m hm
  have h := sos_cert_32x32 ⟨m.val / 32, by omega⟩ ⟨m.val % 32, by omega⟩
  have hmeq : (⟨m.val / 32 * 32 + m.val % 32, by omega⟩ : Fin 1024) = m := by
    ext; dsimp only; omega
  rw [hmeq] at h
  exact h hm

/-- Explicit enumeration of the 10 unordered triples of `Fin 5` paired with the remaining 2 vertices. -/
private def tripleSplit5 : Fin 10 → Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5
  | 0 => (0, 1, 2, 3, 4) | 1 => (0, 1, 3, 2, 4) | 2 => (0, 1, 4, 2, 3)
  | 3 => (0, 2, 3, 1, 4) | 4 => (0, 2, 4, 1, 3) | 5 => (0, 3, 4, 1, 2)
  | 6 => (1, 2, 3, 0, 4) | 7 => (1, 2, 4, 0, 3) | 8 => (1, 3, 4, 0, 2)
  | 9 => (2, 3, 4, 0, 1)

private def perm5Fn (t : Fin 10) (p : Fin 6) (q : Fin 2) (i : Fin 5) : Fin 5 :=
  let (a, b, c, x, y) := tripleSplit5 t
  match i with
  | 0 => match p with | 0 => a | 1 => a | 2 => b | 3 => b | 4 => c | 5 => c
  | 1 => match p with | 0 => b | 1 => c | 2 => a | 3 => c | 4 => a | 5 => b
  | 2 => match p with | 0 => c | 1 => b | 2 => c | 3 => a | 4 => b | 5 => a
  | 3 => if q = 0 then x else y
  | 4 => if q = 0 then y else x

private lemma perm5Fn_inj : ∀ t p q, Function.Injective (perm5Fn t p q) := by decide

private def perm5Emb (x : Fin 10 × Fin 6 × Fin 2) : Fin 5 ↪ Fin 5 :=
  ⟨perm5Fn x.1 x.2.1 x.2.2, perm5Fn_inj x.1 x.2.1 x.2.2⟩

private lemma perm5Emb_inj : Function.Injective perm5Emb := by
  have h : ∀ (t1 t2 : Fin 10) (p1 p2 : Fin 6) (q1 q2 : Fin 2),
      (∀ i : Fin 5, perm5Fn t1 p1 q1 i = perm5Fn t2 p2 q2 i) →
      t1 = t2 ∧ p1 = p2 ∧ q1 = q2 := by decide
  rintro ⟨t1, p1, q1⟩ ⟨t2, p2, q2⟩ heq
  obtain ⟨ht, hp, hq⟩ := h t1 t2 p1 p2 q1 q2 (fun i => congrArg (fun f : Fin 5 ↪ Fin 5 => f i) heq)
  subst ht; subst hp; subst hq; rfl

private lemma perm5Emb_bij : Function.Bijective perm5Emb := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨perm5Emb_inj, ?_⟩
  simp only [Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_fin]
  decide

/-- Helper: expand a sum over `Fin 10` explicitly into concrete numerals `0..9`. -/
private lemma sum_fin10 {α : Type*} [AddCommMonoid α] (f : Fin 10 → α) :
    ∑ i : Fin 10, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  have h10 : (Finset.univ : Finset (Fin 10)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  rw [h10]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
    Fin.reduceEq, or_self, not_false_eq_true, add_assoc]

/-- Encode a symmetric 3-graph predicate on `Fin 5` into a 10-bit mask `Fin 1024`. -/
private def encodeMask5 (g : Fin 5 → Fin 5 → Fin 5 → Bool) : Fin 1024 :=
  ⟨(if g 0 1 2 then 1 else 0) + (if g 0 1 3 then 2 else 0) +
   (if g 0 1 4 then 4 else 0) + (if g 0 2 3 then 8 else 0) +
   (if g 0 2 4 then 16 else 0) + (if g 0 3 4 then 32 else 0) +
   (if g 1 2 3 then 64 else 0) + (if g 1 2 4 then 128 else 0) +
   (if g 1 3 4 then 256 else 0) + (if g 2 3 4 then 512 else 0), by
     split_ifs <;> omega⟩

private lemma maskBit_encodeMask5 (g : Fin 5 → Fin 5 → Fin 5 → Bool) :
    maskBit (encodeMask5 g) 0 = g 0 1 2 ∧ maskBit (encodeMask5 g) 1 = g 0 1 3 ∧
    maskBit (encodeMask5 g) 2 = g 0 1 4 ∧ maskBit (encodeMask5 g) 3 = g 0 2 3 ∧
    maskBit (encodeMask5 g) 4 = g 0 2 4 ∧ maskBit (encodeMask5 g) 5 = g 0 3 4 ∧
    maskBit (encodeMask5 g) 6 = g 1 2 3 ∧ maskBit (encodeMask5 g) 7 = g 1 2 4 ∧
    maskBit (encodeMask5 g) 8 = g 1 3 4 ∧ maskBit (encodeMask5 g) 9 = g 2 3 4 := by
  have hbit : ∀ (b : Bool) (lo hi p : ℕ), lo < p →
      decide (((lo + (if b then p else 0) + 2 * p * hi) / p) % 2 = 1) = b := by
    intro b lo hi p hlo
    have hp : 0 < p := by omega
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, decide_eq_false_iff_not]
      have h1 : (lo + 2 * p * hi) / p = 2 * hi := by
        have : lo + 2 * p * hi = lo + p * (2 * hi) := by ring
        rw [this, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hlo, zero_add]
      omega
    · simp only [↓reduceIte, decide_eq_true_eq]
      have h1 : (lo + p + 2 * p * hi) / p = 1 + 2 * hi := by
        have : lo + p + 2 * p * hi = lo + p * (1 + 2 * hi) := by ring
        rw [this, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hlo, zero_add]
      omega
  set a0 := if g 0 1 2 then 1 else 0; set a1 := if g 0 1 3 then 1 else 0
  set a2 := if g 0 1 4 then 1 else 0; set a3 := if g 0 2 3 then 1 else 0
  set a4 := if g 0 2 4 then 1 else 0; set a5 := if g 0 3 4 then 1 else 0
  set a6 := if g 1 2 3 then 1 else 0; set a7 := if g 1 2 4 then 1 else 0
  set a8 := if g 1 3 4 then 1 else 0; set a9 := if g 2 3 4 then 1 else 0
  have ha : a0 ≤ 1 ∧ a1 ≤ 1 ∧ a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1 ∧ a7 ≤ 1 ∧ a8 ≤ 1 ∧ a9 ≤ 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [a0]; split_ifs <;> omega
    · dsimp only [a1]; split_ifs <;> omega
    · dsimp only [a2]; split_ifs <;> omega
    · dsimp only [a3]; split_ifs <;> omega
    · dsimp only [a4]; split_ifs <;> omega
    · dsimp only [a5]; split_ifs <;> omega
    · dsimp only [a6]; split_ifs <;> omega
    · dsimp only [a7]; split_ifs <;> omega
    · dsimp only [a8]; split_ifs <;> omega
    · dsimp only [a9]; split_ifs <;> omega
  have hval : (encodeMask5 g).val =
      a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7 + 256 * a8 + 512 * a9 := by
    dsimp only [encodeMask5, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
    have hmul : ∀ (b : Bool) (c : ℕ), (if b then c else 0) = c * (if b then 1 else 0) := by
      intro b c; cases b <;> simp
    rw [hmul _ 2, hmul _ 4, hmul _ 8, hmul _ 16, hmul _ 32, hmul _ 64, hmul _ 128, hmul _ 256, hmul _ 512]
  have hmul' : ∀ (b : Bool) (c : ℕ), c * (if b then 1 else 0) = if b then c else 0 := by
    intro b c; cases b <;> simp
  dsimp only [maskBit]
  rw [hval]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (2 : ℕ) ^ (0 : Fin 10).val = 1 by decide]
    rw [show a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7 + 256 * a8 + 512 * a9 =
      (0 + (if g 0 1 2 then 1 else 0)) + 2 * 1 * (a1 + 2 * a2 + 4 * a3 + 8 * a4 + 16 * a5 + 32 * a6 + 64 * a7 + 128 * a8 + 256 * a9)
      by dsimp only [a0]; ring]
    exact hbit (g 0 1 2) 0 _ 1 (by omega)
  · rw [show (2 : ℕ) ^ (1 : Fin 10).val = 2 by decide]
    rw [show a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7 + 256 * a8 + 512 * a9 =
      (a0 + (if g 0 1 3 then 2 else 0)) + 2 * 2 * (a2 + 2 * a3 + 4 * a4 + 8 * a5 + 16 * a6 + 32 * a7 + 64 * a8 + 128 * a9)
      by rw [← hmul']; dsimp only [a1]; ring]
    exact hbit (g 0 1 3) a0 _ 2 (by omega)
  · rw [show (2 : ℕ) ^ (2 : Fin 10).val = 4 by decide]
    rw [show a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7 + 256 * a8 + 512 * a9 =
      ((a0 + 2 * a1) + (if g 0 1 4 then 4 else 0)) + 2 * 4 * (a3 + 2 * a4 + 4 * a5 + 8 * a6 + 16 * a7 + 32 * a8 + 64 * a9)
      by rw [← hmul']; dsimp only [a2]; ring]
    exact hbit (g 0 1 4) (a0 + 2 * a1) _ 4 (by omega)
  · rw [show (2 : ℕ) ^ (3 : Fin 10).val = 8 by decide]
    rw [show a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7 + 256 * a8 + 512 * a9 =
      ((a0 + 2 * a1 + 4 * a2) + (if g 0 2 3 then 8 else 0)) + 2 * 8 * (a4 + 2 * a5 + 4 * a6 + 8 * a7 + 16 * a8 + 32 * a9)
      by rw [← hmul']; dsimp only [a3]; ring]
    exact hbit (g 0 2 3) (a0 + 2 * a1 + 4 * a2) _ 8 (by omega)
  · rw [show (2 : ℕ) ^ (4 : Fin 10).val = 16 by decide]
    rw [show a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7 + 256 * a8 + 512 * a9 =
      ((a0 + 2 * a1 + 4 * a2 + 8 * a3) + (if g 0 2 4 then 16 else 0)) + 2 * 16 * (a5 + 2 * a6 + 4 * a7 + 8 * a8 + 16 * a9)
      by rw [← hmul']; dsimp only [a4]; ring]
    exact hbit (g 0 2 4) (a0 + 2 * a1 + 4 * a2 + 8 * a3) _ 16 (by omega)
  · rw [show (2 : ℕ) ^ (5 : Fin 10).val = 32 by decide]
    rw [show a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7 + 256 * a8 + 512 * a9 =
      ((a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4) + (if g 0 3 4 then 32 else 0)) + 2 * 32 * (a6 + 2 * a7 + 4 * a8 + 8 * a9)
      by rw [← hmul']; dsimp only [a5]; ring]
    exact hbit (g 0 3 4) (a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4) _ 32 (by omega)
  · rw [show (2 : ℕ) ^ (6 : Fin 10).val = 64 by decide]
    rw [show a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7 + 256 * a8 + 512 * a9 =
      ((a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5) + (if g 1 2 3 then 64 else 0)) + 2 * 64 * (a7 + 2 * a8 + 4 * a9)
      by rw [← hmul']; dsimp only [a6]; ring]
    exact hbit (g 1 2 3) (a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5) _ 64 (by omega)
  · rw [show (2 : ℕ) ^ (7 : Fin 10).val = 128 by decide]
    rw [show a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7 + 256 * a8 + 512 * a9 =
      ((a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6) + (if g 1 2 4 then 128 else 0)) + 2 * 128 * (a8 + 2 * a9)
      by rw [← hmul']; dsimp only [a7]; ring]
    exact hbit (g 1 2 4) (a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6) _ 128 (by omega)
  · rw [show (2 : ℕ) ^ (8 : Fin 10).val = 256 by decide]
    rw [show a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7 + 256 * a8 + 512 * a9 =
      ((a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7) + (if g 1 3 4 then 256 else 0)) + 2 * 256 * a9
      by rw [← hmul']]
    exact hbit (g 1 3 4) (a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7) _ 256 (by omega)
  · rw [show (2 : ℕ) ^ (9 : Fin 10).val = 512 by decide]
    rw [show a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7 + 256 * a8 + 512 * a9 =
      ((a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7 + 256 * a8) + (if g 2 3 4 then 512 else 0)) + 2 * 512 * 0
      by rw [← hmul']; dsimp only [a9]; ring]
    exact hbit (g 2 3 4) (a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7 + 256 * a8) 0 512 (by omega)

/-- For any symmetric `K_4^3`-free 3-graph `g` on `Fin 5`, the 120-embedding SOS sum equals
`fastPhiMask (encodeMask5 g)` and satisfies `4800 * edges + Phi ≤ 27744`. -/
private lemma local_5vertex_sos_bound (g : Fin 5 → Fin 5 → Fin 5 → Bool)
    (hsym1 : ∀ a b c, g a b c = g b a c)
    (hsym2 : ∀ a b c, g a b c = g a c b)
    (hk4 : maskIsK4Free (encodeMask5 g) = true) :
    4800 * maskEdgeCount (encodeMask5 g) +
      ∑ f : Fin 5 ↪ Fin 5,
        sosPairScore (g (f 0) (f 1) (f 2))
          (mkFlagCode (g (f 0) (f 1) (f 3)) (g (f 0) (f 2) (f 3)) (g (f 1) (f 2) (f 3)))
          (mkFlagCode (g (f 0) (f 1) (f 4)) (g (f 0) (f 2) (f 4)) (g (f 1) (f 2) (f 4))) ≤ 27744 := by
  have hsym3 : ∀ a b c, g a b c = g c b a := fun a b c => by
    rw [hsym2 a b c, hsym1 a c b, hsym2 c a b]
  have hsym4 : ∀ a b c, g a b c = g b c a := fun a b c => by
    rw [hsym1 a b c, hsym2 b a c]
  have hsym5 : ∀ a b c, g a b c = g c a b := fun a b c => by
    rw [hsym2 a b c, hsym1 a c b]
  have hsum_eq :
      (∑ f : Fin 5 ↪ Fin 5,
        sosPairScore (g (f 0) (f 1) (f 2))
          (mkFlagCode (g (f 0) (f 1) (f 3)) (g (f 0) (f 2) (f 3)) (g (f 1) (f 2) (f 3)))
          (mkFlagCode (g (f 0) (f 1) (f 4)) (g (f 0) (f 2) (f 4)) (g (f 1) (f 2) (f 4)))) =
      fastPhiMask (encodeMask5 g) := by
    rw [← Fintype.sum_bijective perm5Emb perm5Emb_bij _ _ (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    -- Show each fiber t : Fin 10 sums to sym12Score = fastTripleScore!
    have hfiber : ∀ t : Fin 10,
        (∑ p : Fin 6, ∑ q : Fin 2,
          sosPairScore (g (perm5Fn t p q 0) (perm5Fn t p q 1) (perm5Fn t p q 2))
            (mkFlagCode (g (perm5Fn t p q 0) (perm5Fn t p q 1) (perm5Fn t p q 3))
                        (g (perm5Fn t p q 0) (perm5Fn t p q 2) (perm5Fn t p q 3))
                        (g (perm5Fn t p q 1) (perm5Fn t p q 2) (perm5Fn t p q 3)))
            (mkFlagCode (g (perm5Fn t p q 0) (perm5Fn t p q 1) (perm5Fn t p q 4))
                        (g (perm5Fn t p q 0) (perm5Fn t p q 2) (perm5Fn t p q 4))
                        (g (perm5Fn t p q 1) (perm5Fn t p q 2) (perm5Fn t p q 4)))) =
        let (a, b, c, x, y) := tripleSplit5 t
        fastTripleScore (g a b c) (g a b x) (g a c x) (g b c x) (g a b y) (g a c y) (g b c y) := by
      intro t
      rcases htr : tripleSplit5 t with ⟨a, b, c, x, y⟩
      dsimp only
      rw [← sym12Score_eq_fast]
      have h1 : g a c b = g a b c := hsym2 a c b
      have h2 : g b a c = g a b c := hsym1 b a c
      have h3 : g b c a = g a b c := (hsym4 a b c).symm
      have h4 : g c a b = g a b c := (hsym5 a b c).symm
      have h5 : g c b a = g a b c := hsym3 c b a
      have h6 : g b a x = g a b x := hsym1 b a x
      have h7 : g c a x = g a c x := hsym1 c a x
      have h8 : g c b x = g b c x := hsym1 c b x
      have h9 : g b a y = g a b y := hsym1 b a y
      have h10 : g c a y = g a c y := hsym1 c a y
      have h11 : g c b y = g b c y := hsym1 c b y
      simp only [Fin.sum_univ_six, Fin.sum_univ_two, perm5Fn, htr, sym12Score, Fin.isValue,
        ite_true, ite_false, Fin.reduceEq]
      simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    simp_rw [perm5Emb, Function.Embedding.coeFn_mk]
    calc ∑ t : Fin 10, ∑ p : Fin 6, ∑ q : Fin 2,
            sosPairScore (g (perm5Fn t p q 0) (perm5Fn t p q 1) (perm5Fn t p q 2))
              (mkFlagCode (g (perm5Fn t p q 0) (perm5Fn t p q 1) (perm5Fn t p q 3))
                          (g (perm5Fn t p q 0) (perm5Fn t p q 2) (perm5Fn t p q 3))
                          (g (perm5Fn t p q 1) (perm5Fn t p q 2) (perm5Fn t p q 3)))
              (mkFlagCode (g (perm5Fn t p q 0) (perm5Fn t p q 1) (perm5Fn t p q 4))
                          (g (perm5Fn t p q 0) (perm5Fn t p q 2) (perm5Fn t p q 4))
                          (g (perm5Fn t p q 1) (perm5Fn t p q 2) (perm5Fn t p q 4)))
        = ∑ t : Fin 10,
            let (a, b, c, x, y) := tripleSplit5 t
            fastTripleScore (g a b c) (g a b x) (g a c x) (g b c x) (g a b y) (g a c y) (g b c y) :=
          Finset.sum_congr rfl (fun t _ => hfiber t)
      _ = fastPhiMask (encodeMask5 g) := by
          rcases maskBit_encodeMask5 g with ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9⟩
          rw [sum_fin10]
          dsimp only [tripleSplit5, fastPhiMask]
          rw [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9]
          have hnorm1 : g 0 2 1 = g 0 1 2 ∧ g 0 3 1 = g 0 1 3 ∧ g 0 4 1 = g 0 1 4 ∧ g 2 4 3 = g 2 3 4 :=
            ⟨hsym2 _ _ _, hsym2 _ _ _, hsym2 _ _ _, hsym2 _ _ _⟩
          have hnorm :
              g 0 1 2 = g 0 1 2 ∧ g 0 3 2 = g 0 2 3 ∧ g 1 3 2 = g 1 2 3 ∧
              g 0 4 2 = g 0 2 4 ∧ g 1 4 2 = g 1 2 4 ∧ g 0 4 3 = g 0 3 4 ∧
              g 1 4 3 = g 1 3 4 ∧ g 2 3 1 = g 1 2 3 ∧ g 2 4 1 = g 1 2 4 ∧
              g 3 4 1 = g 1 3 4 ∧ g 3 4 2 = g 2 3 4 ∧ g 1 2 0 = g 0 1 2 ∧
              g 1 3 0 = g 0 1 3 ∧ g 2 3 0 = g 0 2 3 ∧ g 1 4 0 = g 0 1 4 ∧
              g 2 4 0 = g 0 2 4 ∧ g 3 4 0 = g 0 3 4 := by
            refine ⟨rfl, hsym2 _ _ _, hsym2 _ _ _, hsym2 _ _ _, hsym2 _ _ _, hsym2 _ _ _,
              hsym2 _ _ _, hsym5 _ _ _, hsym5 _ _ _, hsym5 _ _ _, hsym5 _ _ _, hsym5 _ _ _,
              hsym5 _ _ _, hsym5 _ _ _, hsym5 _ _ _, hsym5 _ _ _, hsym5 _ _ _⟩
          simp only [hnorm1.1, hnorm1.2.1, hnorm1.2.2.1, hnorm1.2.2.2,
            hnorm.2.1, hnorm.2.2.1, hnorm.2.2.2.1, hnorm.2.2.2.2.1, hnorm.2.2.2.2.2.1,
            hnorm.2.2.2.2.2.2.1, hnorm.2.2.2.2.2.2.2.1, hnorm.2.2.2.2.2.2.2.2.1,
            hnorm.2.2.2.2.2.2.2.2.2.1, hnorm.2.2.2.2.2.2.2.2.2.2.1,
            hnorm.2.2.2.2.2.2.2.2.2.2.2.1, hnorm.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hnorm.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hnorm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hnorm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hnorm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
  rw [hsum_eq]
  exact sos_cert_1024 (encodeMask5 g) hk4

/-- For any fixed triple `(u0, u1, u2)` and vertex set `R`, the quadratic SOS double sum is `≥ 0`. -/
private lemma sos_double_sum_nonneg {n : ℕ} (e : Fin n → Fin n → Fin n → Bool)
    (u0 u1 u2 : Fin n) (R : Finset (Fin n)) :
    (0 : ℤ) ≤ ∑ x ∈ R, ∑ y ∈ R,
      sosPairScore (e u0 u1 u2)
        (mkFlagCode (e u0 u1 x) (e u0 u2 x) (e u1 u2 x))
        (mkFlagCode (e u0 u1 y) (e u0 u2 y) (e u1 u2 y)) := by
  let fc : Fin n → Fin 8 := fun x => mkFlagCode (e u0 u1 x) (e u0 u2 x) (e u1 u2 x)
  have hsq : ∀ (v : Fin 8 → ℤ),
      ∑ x ∈ R, ∑ y ∈ R, v (fc x) * v (fc y) = (∑ x ∈ R, v (fc x)) ^ 2 := by
    intro v
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
  cases e u0 u1 u2
  · simp only [sosPairScore, Bool.false_eq_true, ↓reduceIte, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
    have h0 : 0 ≤ (∑ x ∈ R, sosV0 (fc x)) * (∑ x ∈ R, sosV0 (fc x)) := mul_self_nonneg _
    have h1 : 0 ≤ (∑ x ∈ R, sosV1 (fc x)) * (∑ x ∈ R, sosV1 (fc x)) := mul_self_nonneg _
    have h2 : 0 ≤ (∑ x ∈ R, sosV2 (fc x)) * (∑ x ∈ R, sosV2 (fc x)) := mul_self_nonneg _
    dsimp only [fc] at h0 h1 h2
    linarith
  · simp only [sosPairScore, ↓reduceIte, ← Finset.mul_sum, ← Finset.sum_mul]
    have h3 : 0 ≤ (∑ x ∈ R, sosV3 (fc x)) * (∑ x ∈ R, sosV3 (fc x)) := mul_self_nonneg _
    dsimp only [fc] at h3
    linarith

/-- Exact binomial identities needed for the finite-`n` density bound. -/
private lemma ten_mul_choose_five (n : ℕ) (_hn : 5 ≤ n) :
    10 * n.choose 5 = n.choose 3 * (n - 3).choose 2 := by
  have h1 := Nat.choose_mul (n := n) (k := 5) (s := 3) (by omega)
  have h53 : Nat.choose 5 3 = 10 := by decide
  rw [h53] at h1
  have hsub : 5 - 3 = 2 := rfl
  rw [hsub] at h1
  linarith

private lemma four_mul_choose_four (n : ℕ) (_hn : 4 ≤ n) :
    4 * n.choose 4 = n.choose 3 * (n - 3) := by
  have h1 := Nat.choose_mul (n := n) (k := 4) (s := 3) (by omega)
  have h43 : Nat.choose 4 3 = 4 := by decide
  rw [h43] at h1
  have hsub : 4 - 3 = 1 := rfl
  rw [hsub, Nat.choose_one_right] at h1
  linarith

/-- **Certified 4-Square Flag-Algebra SOS Upper Bound (Exact Finite-`n` Integer Form)**:
For **every** `n ≥ 5` and **every** `K_4^3`-free 3-uniform hypergraph `E` on `Fin n`:
`4800 * E.card * (n - 3).choose 2 ≤ 27744 * n.choose 5 + 11880 * n.choose 4`. -/
theorem ppl074_flag5_sos_finite_upper {n : ℕ} (_hn : 5 ≤ n)
    (E : Finset (Finset (Fin n)))
    (hE : ∀ e ∈ E, e.card = 3)
    (hfree : ∀ K : Finset (Fin n), K.card = 4 → ¬ K.powersetCard 3 ⊆ E) :
    4800 * E.card * (n - 3).choose 2 ≤ 27744 * n.choose 5 + 11880 * n.choose 4 := by
  classical
  let e : Fin n → Fin n → Fin n → Bool := fun a b c => decide (({a, b, c} : Finset (Fin n)) ∈ E)
  let score5 : (Fin 5 ↪ Fin n) → ℤ := fun f =>
    sosPairScore (e (f 0) (f 1) (f 2))
      (mkFlagCode (e (f 0) (f 1) (f 3)) (e (f 0) (f 2) (f 3)) (e (f 1) (f 2) (f 3)))
      (mkFlagCode (e (f 0) (f 1) (f 4)) (e (f 0) (f 2) (f 4)) (e (f 1) (f 2) (f 4)))
  let score4 : (Fin 4 ↪ Fin n) → ℤ := fun f =>
    sosPairScore (e (f 0) (f 1) (f 2))
      (mkFlagCode (e (f 0) (f 1) (f 3)) (e (f 0) (f 2) (f 3)) (e (f 1) (f 2) (f 3)))
      (mkFlagCode (e (f 0) (f 1) (f 3)) (e (f 0) (f 2) (f 3)) (e (f 1) (f 2) (f 3)))
  -- Step 1: Total SOS sum over all embeddings `f3 : Fin 3 ↪ Fin n` is ≥ 0, and splits into Off + Diag!
  have hSOS_nonneg : (0 : ℤ) ≤ (∑ f5 : Fin 5 ↪ Fin n, score5 f5) +
      (∑ f4 : Fin 4 ↪ Fin n, score4 f4) := by
    have hsum3 : (0 : ℤ) ≤ ∑ f3 : Fin 3 ↪ Fin n,
        ∑ x ∈ Finset.univ \ (Finset.univ.image f3),
        ∑ y ∈ Finset.univ \ (Finset.univ.image f3),
          sosPairScore (e (f3 0) (f3 1) (f3 2))
            (mkFlagCode (e (f3 0) (f3 1) x) (e (f3 0) (f3 2) x) (e (f3 1) (f3 2) x))
            (mkFlagCode (e (f3 0) (f3 1) y) (e (f3 0) (f3 2) y) (e (f3 1) (f3 2) y)) :=
      Finset.sum_nonneg fun f3 _ => sos_double_sum_nonneg e (f3 0) (f3 1) (f3 2) _
    -- Split inner double sum over x, y into x ≠ y (Off) + x = y (Diag)!
    have hsplit_inner : ∀ f3 : Fin 3 ↪ Fin n,
        (∑ x ∈ Finset.univ \ (Finset.univ.image f3),
         ∑ y ∈ Finset.univ \ (Finset.univ.image f3),
          sosPairScore (e (f3 0) (f3 1) (f3 2))
            (mkFlagCode (e (f3 0) (f3 1) x) (e (f3 0) (f3 2) x) (e (f3 1) (f3 2) x))
            (mkFlagCode (e (f3 0) (f3 1) y) (e (f3 0) (f3 2) y) (e (f3 1) (f3 2) y))) =
        (∑ x ∈ Finset.univ \ (Finset.univ.image f3),
         ∑ y ∈ (Finset.univ \ (Finset.univ.image f3)).erase x,
          sosPairScore (e (f3 0) (f3 1) (f3 2))
            (mkFlagCode (e (f3 0) (f3 1) x) (e (f3 0) (f3 2) x) (e (f3 1) (f3 2) x))
            (mkFlagCode (e (f3 0) (f3 1) y) (e (f3 0) (f3 2) y) (e (f3 1) (f3 2) y))) +
        (∑ x ∈ Finset.univ \ (Finset.univ.image f3),
          sosPairScore (e (f3 0) (f3 1) (f3 2))
            (mkFlagCode (e (f3 0) (f3 1) x) (e (f3 0) (f3 2) x) (e (f3 1) (f3 2) x))
            (mkFlagCode (e (f3 0) (f3 1) x) (e (f3 0) (f3 2) x) (e (f3 1) (f3 2) x))) := by
      intro f3
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [add_comm, Finset.add_sum_erase (s := Finset.univ \ Finset.univ.image f3)
        (f := fun y => sosPairScore (e (f3 0) (f3 1) (f3 2))
          (mkFlagCode (e (f3 0) (f3 1) x) (e (f3 0) (f3 2) x) (e (f3 1) (f3 2) x))
          (mkFlagCode (e (f3 0) (f3 1) y) (e (f3 0) (f3 2) y) (e (f3 1) (f3 2) y))) hx]
    simp_rw [hsplit_inner, Finset.sum_add_distrib] at hsum3
    -- Biject Diag with Fin 4 ↪ Fin n!
    have hDiag_eq : (∑ f3 : Fin 3 ↪ Fin n,
        ∑ x ∈ Finset.univ \ (Finset.univ.image f3),
          sosPairScore (e (f3 0) (f3 1) (f3 2))
            (mkFlagCode (e (f3 0) (f3 1) x) (e (f3 0) (f3 2) x) (e (f3 1) (f3 2) x))
            (mkFlagCode (e (f3 0) (f3 1) x) (e (f3 0) (f3 2) x) (e (f3 1) (f3 2) x))) =
        ∑ f4 : Fin 4 ↪ Fin n, score4 f4 := by
      rw [Finset.sum_sigma' (Finset.univ : Finset (Fin 3 ↪ Fin n))
        (fun f3 => Finset.univ \ Finset.univ.image f3)]
      refine Finset.sum_bij
        (fun p hp =>
          ⟨fun i => match i with | 0 => p.1 0 | 1 => p.1 1 | 2 => p.1 2 | 3 => p.2, by
            have hnot : p.2 ∉ Finset.univ.image p.1 := (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hp).2).2
            intro i j hij
            fin_cases i <;> fin_cases j <;> dsimp only [Fin.isValue] at hij ⊢
            all_goals first
              | rfl
              | exact absurd (p.1.injective hij) (by decide)
              | exact absurd (Finset.mem_image_of_mem p.1 (Finset.mem_univ _)) (by rw [hij]; exact hnot)
              | exact absurd (Finset.mem_image_of_mem p.1 (Finset.mem_univ _)) (by rw [← hij]; exact hnot)⟩)
        (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro p1 hp1 p2 hp2 heq
        have h0 : p1.1 0 = p2.1 0 := congrArg (fun f : Fin 4 ↪ Fin n => f 0) heq
        have h1 : p1.1 1 = p2.1 1 := congrArg (fun f : Fin 4 ↪ Fin n => f 1) heq
        have h2 : p1.1 2 = p2.1 2 := congrArg (fun f : Fin 4 ↪ Fin n => f 2) heq
        have h3 : p1.2 = p2.2 := congrArg (fun f : Fin 4 ↪ Fin n => f 3) heq
        have hf : p1.1 = p2.1 := by apply DFunLike.ext; intro i; fin_cases i <;> assumption
        exact Sigma.ext hf (heq_of_eq h3)
      · intro f4 _
        let f3 : Fin 3 ↪ Fin n := ⟨fun i => f4 i.castSucc, fun i j h => Fin.castSucc_injective 3 (f4.injective h)⟩
        refine ⟨⟨f3, f4 3⟩, ?_, ?_⟩
        · rw [Finset.mem_sigma]
          refine ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
          have : i.castSucc = (3 : Fin 4) := f4.injective hi
          fin_cases i <;> simp at this
        · apply DFunLike.ext; intro i; fin_cases i <;> rfl
      · intro p _; rfl
    -- Biject Off with Fin 5 ↪ Fin n!
    have hOff_eq : (∑ f3 : Fin 3 ↪ Fin n,
        ∑ x ∈ Finset.univ \ (Finset.univ.image f3),
        ∑ y ∈ (Finset.univ \ (Finset.univ.image f3)).erase x,
          sosPairScore (e (f3 0) (f3 1) (f3 2))
            (mkFlagCode (e (f3 0) (f3 1) x) (e (f3 0) (f3 2) x) (e (f3 1) (f3 2) x))
            (mkFlagCode (e (f3 0) (f3 1) y) (e (f3 0) (f3 2) y) (e (f3 1) (f3 2) y))) =
        ∑ f5 : Fin 5 ↪ Fin n, score5 f5 := by
      have hsig1 : ∀ f3 : Fin 3 ↪ Fin n,
          (∑ x ∈ Finset.univ \ (Finset.univ.image f3),
           ∑ y ∈ (Finset.univ \ (Finset.univ.image f3)).erase x,
            sosPairScore (e (f3 0) (f3 1) (f3 2))
              (mkFlagCode (e (f3 0) (f3 1) x) (e (f3 0) (f3 2) x) (e (f3 1) (f3 2) x))
              (mkFlagCode (e (f3 0) (f3 1) y) (e (f3 0) (f3 2) y) (e (f3 1) (f3 2) y))) =
          ∑ xy ∈ (Finset.univ \ (Finset.univ.image f3)).sigma
              (fun x => (Finset.univ \ (Finset.univ.image f3)).erase x),
            sosPairScore (e (f3 0) (f3 1) (f3 2))
              (mkFlagCode (e (f3 0) (f3 1) xy.1) (e (f3 0) (f3 2) xy.1) (e (f3 1) (f3 2) xy.1))
              (mkFlagCode (e (f3 0) (f3 1) xy.2) (e (f3 0) (f3 2) xy.2) (e (f3 1) (f3 2) xy.2)) :=
        fun f3 => Finset.sum_sigma' _ _ _
      rw [Finset.sum_congr rfl (fun f3 _ => hsig1 f3)]
      rw [Finset.sum_sigma' (Finset.univ : Finset (Fin 3 ↪ Fin n))
        (fun f3 => (Finset.univ \ (Finset.univ.image f3)).sigma
          (fun x => (Finset.univ \ (Finset.univ.image f3)).erase x))
        (fun f3 xy => sosPairScore (e (f3 0) (f3 1) (f3 2))
          (mkFlagCode (e (f3 0) (f3 1) xy.1) (e (f3 0) (f3 2) xy.1) (e (f3 1) (f3 2) xy.1))
          (mkFlagCode (e (f3 0) (f3 1) xy.2) (e (f3 0) (f3 2) xy.2) (e (f3 1) (f3 2) xy.2)))]
      refine Finset.sum_bij
        (fun p hp =>
          ⟨fun i => match i with | 0 => p.1 0 | 1 => p.1 1 | 2 => p.1 2 | 3 => p.2.1 | 4 => p.2.2, by
            rw [Finset.mem_sigma, Finset.mem_sigma] at hp
            have hxnot : p.2.1 ∉ Finset.univ.image p.1 := (Finset.mem_sdiff.mp hp.2.1).2
            have hyer := Finset.mem_erase.mp hp.2.2
            have hynot : p.2.2 ∉ Finset.univ.image p.1 := (Finset.mem_sdiff.mp hyer.2).2
            have hyx : p.2.2 ≠ p.2.1 := hyer.1
            intro i j hij
            fin_cases i <;> fin_cases j <;> dsimp only [Fin.isValue] at hij ⊢
            all_goals first
              | rfl
              | exact absurd (p.1.injective hij) (by decide)
              | exact absurd (Finset.mem_image_of_mem p.1 (Finset.mem_univ _)) (by rw [hij]; exact hxnot)
              | exact absurd (Finset.mem_image_of_mem p.1 (Finset.mem_univ _)) (by rw [← hij]; exact hxnot)
              | exact absurd (Finset.mem_image_of_mem p.1 (Finset.mem_univ _)) (by rw [hij]; exact hynot)
              | exact absurd (Finset.mem_image_of_mem p.1 (Finset.mem_univ _)) (by rw [← hij]; exact hynot)
              | exact absurd hij hyx.symm
              | exact absurd hij hyx⟩)
        (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro p1 _ p2 _ heq
        have h0 : p1.1 0 = p2.1 0 := congrArg (fun f : Fin 5 ↪ Fin n => f 0) heq
        have h1 : p1.1 1 = p2.1 1 := congrArg (fun f : Fin 5 ↪ Fin n => f 1) heq
        have h2 : p1.1 2 = p2.1 2 := congrArg (fun f : Fin 5 ↪ Fin n => f 2) heq
        have h3 : p1.2.1 = p2.2.1 := congrArg (fun f : Fin 5 ↪ Fin n => f 3) heq
        have h4 : p1.2.2 = p2.2.2 := congrArg (fun f : Fin 5 ↪ Fin n => f 4) heq
        have hf : p1.1 = p2.1 := by apply DFunLike.ext; intro i; fin_cases i <;> assumption
        have hp2 : p1.2 = p2.2 := Sigma.ext h3 (heq_of_eq h4)
        exact Sigma.ext hf (heq_of_eq hp2)
      · intro f5 _
        let f3 : Fin 3 ↪ Fin n := ⟨fun i => f5 ⟨i.val, by omega⟩, fun i j h => by
          have := congrArg Fin.val (f5.injective h); exact Fin.ext this⟩
        refine ⟨⟨f3, ⟨f5 3, f5 4⟩⟩, ?_, ?_⟩
        · rw [Finset.mem_sigma, Finset.mem_sigma]
          refine ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩,
            Finset.mem_erase.mpr ⟨fun h => absurd (f5.injective h) (by decide),
              Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩⟩
          · intro hmem; rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
            have := congrArg Fin.val (f5.injective hi); dsimp at this; omega
          · intro hmem; rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
            have := congrArg Fin.val (f5.injective hi); dsimp at this; omega
        · apply DFunLike.ext; intro i; fin_cases i <;> rfl
      · intro p _; rfl
    rw [hOff_eq, hDiag_eq] at hsum3
    exact hsum3
  -- Step 2: Upper bound Diag ≤ 495 * 24 * n.choose 4 = 11880 * n.choose 4!
  have hDiag_le : (∑ f4 : Fin 4 ↪ Fin n, score4 f4) ≤ 11880 * (n.choose 4 : ℤ) := by
    have hterm : ∀ f4 : Fin 4 ↪ Fin n, score4 f4 ≤ 495 := fun f4 =>
      sosPairScore_diag_le _ _
    calc (∑ f4 : Fin 4 ↪ Fin n, score4 f4)
        ≤ ∑ _f4 : Fin 4 ↪ Fin n, (495 : ℤ) := Finset.sum_le_sum fun f4 _ => hterm f4
      _ = ((Fintype.card (Fin 4 ↪ Fin n) : ℕ) : ℤ) * 495 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 11880 * (n.choose 4 : ℤ) := by
          rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
            Nat.descFactorial_eq_factorial_mul_choose]
          have hf4 : Nat.factorial 4 = 24 := by decide
          rw [hf4]; push_cast; ring
  -- Step 3: Group Off over A ∈ powersetCard 5 univ and apply local_5vertex_sos_bound!
  have hOff_bound : 4800 * ((E.card * (n - 3).choose 2 : ℕ) : ℤ) +
      (∑ f5 : Fin 5 ↪ Fin n, score5 f5) ≤ 27744 * (n.choose 5 : ℤ) := by
    let P5 := ((Finset.univ : Finset (Fin n)).powersetCard 5).attach
    let embA : {s : Finset (Fin n) // s ∈ (Finset.univ : Finset (Fin n)).powersetCard 5} →
        (Fin 5 ↪ Fin n) :=
      fun A => (A.1.orderIsoOfFin (Finset.mem_powersetCard.mp A.2).2).toEquiv.toEmbedding.trans
        (Function.Embedding.subtype _)
    let gA : {s : Finset (Fin n) // s ∈ (Finset.univ : Finset (Fin n)).powersetCard 5} →
        Fin 5 → Fin 5 → Fin 5 → Bool :=
      fun A a b c => e (embA A a) (embA A b) (embA A c)
    -- 3a: Sum of score5 over all Fin 5 ↪ Fin n equals sum over A ∈ P5 of sum over π : Fin 5 ↪ Fin 5!
    have hOff_group : (∑ f5 : Fin 5 ↪ Fin n, score5 f5) =
        ∑ A ∈ P5, ∑ π : Fin 5 ↪ Fin 5, score5 (π.trans (embA A)) := by
      symm
      rw [← Finset.sum_product']
      refine Finset.sum_bij (fun p _ => p.2.trans (embA p.1))
        (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro p1 _ p2 _ heq
        have himg : ∀ (A : {s : Finset (Fin n) // s ∈ (Finset.univ : Finset (Fin n)).powersetCard 5})
            (π : Fin 5 ↪ Fin 5), Finset.univ.image (π.trans (embA A)) = A.1 := by
          intro A π
          have hπ_surj : Finset.univ.image π = Finset.univ :=
            Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
              (by rw [Finset.card_image_of_injective _ π.injective])
          have hemb_img : Finset.univ.image (embA A) = A.1 := by
            ext x
            simp only [Finset.mem_image, Finset.mem_univ, true_and, embA,
              Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
              Function.Embedding.coe_subtype, OrderIso.coe_toEquiv]
            constructor
            · rintro ⟨i, rfl⟩; exact ((A.1.orderIsoOfFin (Finset.mem_powersetCard.mp A.2).2) i).2
            · intro hx
              let iso := A.1.orderIsoOfFin (Finset.mem_powersetCard.mp A.2).2
              exact ⟨iso.symm ⟨x, hx⟩, congrArg Subtype.val (iso.apply_symm_apply ⟨x, hx⟩)⟩
          calc Finset.univ.image (π.trans (embA A))
              = (Finset.univ.image π).image (embA A) := by
                ext x; simp [Function.Embedding.trans_apply]
            _ = Finset.univ.image (embA A) := by rw [hπ_surj]
            _ = A.1 := hemb_img
        have hA_eq : p1.1 = p2.1 := Subtype.ext (by rw [← himg p1.1 p1.2, ← himg p2.1 p2.2, heq])
        rcases p1 with ⟨A1, π1⟩; rcases p2 with ⟨A2, π2⟩
        dsimp only at hA_eq
        subst hA_eq
        have hπ_eq : π1 = π2 := by
          apply DFunLike.ext; intro i
          have hi : (embA A1) (π1 i) = (embA A1) (π2 i) :=
            congrArg (fun f : Fin 5 ↪ Fin n => f i) heq
          exact (embA A1).injective hi
        exact Prod.ext rfl hπ_eq
      · intro f5 _
        let A0 : Finset (Fin n) := Finset.univ.image f5
        have hA0_card : A0.card = 5 := by
          rw [Finset.card_image_of_injective _ f5.injective, Finset.card_univ, Fintype.card_fin]
        have hA0_mem : A0 ∈ (Finset.univ : Finset (Fin n)).powersetCard 5 :=
          Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hA0_card⟩
        let A : {s : Finset (Fin n) // s ∈ (Finset.univ : Finset (Fin n)).powersetCard 5} :=
          ⟨A0, hA0_mem⟩
        let iso := A.1.orderIsoOfFin (Finset.mem_powersetCard.mp A.2).2
        let π : Fin 5 ↪ Fin 5 :=
          ⟨fun i => iso.symm ⟨f5 i, Finset.mem_image_of_mem f5 (Finset.mem_univ i)⟩,
           fun i j h => f5.injective (congrArg Subtype.val (iso.symm.injective h))⟩
        refine ⟨(A, π), Finset.mem_product.mpr ⟨Finset.mem_attach _ _, Finset.mem_univ _⟩, ?_⟩
        apply DFunLike.ext; intro i
        simp only [Function.Embedding.trans_apply, embA, Equiv.toEmbedding_apply,
          Function.Embedding.coe_subtype, OrderIso.coe_toEquiv, π]
        exact congrArg Subtype.val
          (iso.apply_symm_apply ⟨f5 i, Finset.mem_image_of_mem f5 (Finset.mem_univ i)⟩)
      · intro _ _; rfl
    -- 3b: Each A ∈ P5 has maskIsK4Free = true and maskEdgeCount = (E.filter (· ⊆ A.1)).card!
    have hlocal : ∀ A ∈ P5,
        4800 * ((E.filter (fun s => s ⊆ A.1)).card : ℤ) +
          (∑ π : Fin 5 ↪ Fin 5, score5 (π.trans (embA A))) ≤ 27744 := by
      intro A _
      have hsym1 : ∀ a b c : Fin 5, gA A a b c = gA A b a c := by
        intro a b c; dsimp only [gA, e]
        have hset : ({embA A a, embA A b, embA A c} : Finset (Fin n)) =
            {embA A b, embA A a, embA A c} := by ext t; simp; tauto
        rw [hset]
      have hsym2 : ∀ a b c : Fin 5, gA A a b c = gA A a c b := by
        intro a b c; dsimp only [gA, e]
        have hset : ({embA A a, embA A b, embA A c} : Finset (Fin n)) =
            {embA A a, embA A c, embA A b} := by ext t; simp; tauto
        rw [hset]
      have hk4 : maskIsK4Free (encodeMask5 (gA A)) = true := by
        rcases maskBit_encodeMask5 (gA A) with ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9⟩
        have hno4 : ∀ (i0 i1 i2 i3 : Fin 5), i0 ≠ i1 → i0 ≠ i2 → i0 ≠ i3 → i1 ≠ i2 → i1 ≠ i3 → i2 ≠ i3 →
            Bool.not (gA A i0 i1 i2 && gA A i0 i1 i3 && gA A i0 i2 i3 && gA A i1 i2 i3) = true := by
          intro i0 i1 i2 i3 h01 h02 h03 h12 h13 h23
          by_contra hbad
          have htrue : (gA A i0 i1 i2 && gA A i0 i1 i3 && gA A i0 i2 i3 && gA A i1 i2 i3) = true := by
            cases hb : (gA A i0 i1 i2 && gA A i0 i1 i3 && gA A i0 i2 i3 && gA A i1 i2 i3)
            · exfalso; apply hbad; rw [hb]; rfl
            · rfl
          simp only [Bool.and_eq_true] at htrue
          rcases htrue with ⟨⟨⟨h012, h013⟩, h023⟩, h123⟩
          simp only [gA, e, decide_eq_true_eq] at h012 h013 h023 h123
          let Q : Finset (Fin 5) := {i0, i1, i2, i3}
          have hQ4 : Q.card = 4 := by
            dsimp only [Q]
            rw [Finset.card_insert_of_notMem (by simp [h01, h02, h03]),
              Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
          let K : Finset (Fin n) := Q.map (embA A)
          have hK4 : K.card = 4 := by rw [Finset.card_map, hQ4]
          apply hfree K hK4
          intro s hs
          rw [Finset.mem_powersetCard] at hs
          have hdiff : (K \ s).card = 1 := by rw [Finset.card_sdiff_of_subset hs.1, hK4, hs.2]
          obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdiff
          have hvm : v ∈ K \ s := hv ▸ Finset.mem_singleton_self v
          rw [Finset.mem_sdiff] at hvm
          have hs_eq : s = K.erase v := by
            ext x; simp only [Finset.mem_erase]
            constructor
            · intro hx; exact ⟨fun h => hvm.2 (h ▸ hx), hs.1 hx⟩
            · rintro ⟨hxv, hxK⟩
              by_contra hxs
              have : x ∈ K \ s := Finset.mem_sdiff.mpr ⟨hxK, hxs⟩
              rw [hv, Finset.mem_singleton] at this
              exact hxv this
          rw [hs_eq]
          have hvK := hvm.1
          simp only [K, Q, Finset.mem_map, Finset.mem_insert, Finset.mem_singleton] at hvK
          rcases hvK with ⟨j, hj, rfl⟩
          rcases hj with hj | hj | hj | hj
          · rw [hj]
            have : K.erase (embA A i0) = {embA A i1, embA A i2, embA A i3} := by
              ext x; simp only [K, Q, Finset.mem_erase, Finset.mem_map, Finset.mem_insert,
                Finset.mem_singleton]
              constructor
              · rintro ⟨hne, t, ht, rfl⟩
                rcases ht with ht | ht | ht | ht
                · exact absurd (by rw [ht]) hne
                · exact Or.inl (by rw [ht])
                · exact Or.inr (Or.inl (by rw [ht]))
                · exact Or.inr (Or.inr (by rw [ht]))
              · rintro (rfl | rfl | rfl)
                · exact ⟨fun h => h01 ((embA A).injective h).symm, i1, Or.inr (Or.inl rfl), rfl⟩
                · exact ⟨fun h => h02 ((embA A).injective h).symm, i2, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
                · exact ⟨fun h => h03 ((embA A).injective h).symm, i3, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
            rwa [this]
          · rw [hj]
            have : K.erase (embA A i1) = {embA A i0, embA A i2, embA A i3} := by
              ext x; simp only [K, Q, Finset.mem_erase, Finset.mem_map, Finset.mem_insert,
                Finset.mem_singleton]
              constructor
              · rintro ⟨hne, t, ht, rfl⟩
                rcases ht with ht | ht | ht | ht
                · exact Or.inl (by rw [ht])
                · exact absurd (by rw [ht]) hne
                · exact Or.inr (Or.inl (by rw [ht]))
                · exact Or.inr (Or.inr (by rw [ht]))
              · rintro (rfl | rfl | rfl)
                · exact ⟨fun h => h01 ((embA A).injective h), i0, Or.inl rfl, rfl⟩
                · exact ⟨fun h => h12 ((embA A).injective h).symm, i2, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
                · exact ⟨fun h => h13 ((embA A).injective h).symm, i3, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
            rwa [this]
          · rw [hj]
            have : K.erase (embA A i2) = {embA A i0, embA A i1, embA A i3} := by
              ext x; simp only [K, Q, Finset.mem_erase, Finset.mem_map, Finset.mem_insert,
                Finset.mem_singleton]
              constructor
              · rintro ⟨hne, t, ht, rfl⟩
                rcases ht with ht | ht | ht | ht
                · exact Or.inl (by rw [ht])
                · exact Or.inr (Or.inl (by rw [ht]))
                · exact absurd (by rw [ht]) hne
                · exact Or.inr (Or.inr (by rw [ht]))
              · rintro (rfl | rfl | rfl)
                · exact ⟨fun h => h02 ((embA A).injective h), i0, Or.inl rfl, rfl⟩
                · exact ⟨fun h => h12 ((embA A).injective h), i1, Or.inr (Or.inl rfl), rfl⟩
                · exact ⟨fun h => h23 ((embA A).injective h).symm, i3, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
            rwa [this]
          · rw [hj]
            have : K.erase (embA A i3) = {embA A i0, embA A i1, embA A i2} := by
              ext x; simp only [K, Q, Finset.mem_erase, Finset.mem_map, Finset.mem_insert,
                Finset.mem_singleton]
              constructor
              · rintro ⟨hne, t, ht, rfl⟩
                rcases ht with ht | ht | ht | ht
                · exact Or.inl (by rw [ht])
                · exact Or.inr (Or.inl (by rw [ht]))
                · exact Or.inr (Or.inr (by rw [ht]))
                · exact absurd (by rw [ht]) hne
              · rintro (rfl | rfl | rfl)
                · exact ⟨fun h => h03 ((embA A).injective h), i0, Or.inl rfl, rfl⟩
                · exact ⟨fun h => h13 ((embA A).injective h), i1, Or.inr (Or.inl rfl), rfl⟩
                · exact ⟨fun h => h23 ((embA A).injective h), i2, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
            rwa [this]
        dsimp only [maskIsK4Free]
        rw [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9]
        simp only [Bool.and_eq_true]
        refine ⟨⟨⟨⟨hno4 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
                  hno4 0 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
                hno4 0 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
              hno4 0 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
            hno4 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
      have hedge_eq : maskEdgeCount (encodeMask5 (gA A)) = ((E.filter (fun s => s ⊆ A.1)).card : ℤ) := by
        have hbij_e : (E.filter (fun s => s ⊆ A.1)).card =
            ((Finset.univ : Finset (Fin 10)).filter (fun t =>
              let (a, b, c, _, _) := tripleSplit5 t; gA A a b c = true)).card := by
          symm
          refine Finset.card_bij
            (fun t _ => let (a, b, c, _, _) := tripleSplit5 t; {embA A a, embA A b, embA A c})
            ?_ ?_ ?_
          · intro t ht
            rw [Finset.mem_filter] at ht ⊢
            rcases htr : tripleSplit5 t with ⟨a, b, c, x, y⟩
            simp only [htr] at ht ⊢
            simp only [gA, e, decide_eq_true_eq] at ht
            refine ⟨ht.2, ?_⟩
            intro v hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl | rfl <;>
              exact ((A.1.orderIsoOfFin (Finset.mem_powersetCard.mp A.2).2) _).2
          · intro t1 _ t2 _ heq
            have hdistinct : ∀ t1 t2 : Fin 10, t1 ≠ t2 →
                let (a1, b1, c1, _, _) := tripleSplit5 t1
                let (a2, b2, c2, _, _) := tripleSplit5 t2
                ({a1, b1, c1} : Finset (Fin 5)) ≠ {a2, b2, c2} := by decide
            by_contra hne
            have hne5 := hdistinct t1 t2 hne
            rcases htr1 : tripleSplit5 t1 with ⟨a1, b1, c1, x1, y1⟩
            rcases htr2 : tripleSplit5 t2 with ⟨a2, b2, c2, x2, y2⟩
            simp only [htr1, htr2] at heq hne5
            apply hne5
            ext i
            have hi : embA A i ∈ ({embA A a1, embA A b1, embA A c1} : Finset (Fin n)) ↔
                embA A i ∈ ({embA A a2, embA A b2, embA A c2} : Finset (Fin n)) := by rw [heq]
            simp only [Finset.mem_insert, Finset.mem_singleton, (embA A).injective.eq_iff] at hi ⊢
            exact hi
          · intro s hs
            rw [Finset.mem_filter] at hs
            let s5 : Finset (Fin 5) := Finset.univ.filter (fun i => embA A i ∈ s)
            have hs5_map : s5.map (embA A) = s := by
              ext x
              simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, s5]
              constructor
              · rintro ⟨i, hi, rfl⟩; exact hi
              · intro hxs
                have hxA : x ∈ A.1 := hs.2 hxs
                let iso := A.1.orderIsoOfFin (Finset.mem_powersetCard.mp A.2).2
                refine ⟨iso.symm ⟨x, hxA⟩, ?_, ?_⟩
                · have hval : embA A (iso.symm ⟨x, hxA⟩) = x := by
                    simp only [embA, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
                      Function.Embedding.coe_subtype, OrderIso.coe_toEquiv]
                    exact congrArg Subtype.val (iso.apply_symm_apply ⟨x, hxA⟩)
                  rwa [hval]
                · simp only [embA, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
                    Function.Embedding.coe_subtype, OrderIso.coe_toEquiv]
                  exact congrArg Subtype.val (iso.apply_symm_apply ⟨x, hxA⟩)
            have hs5_card : s5.card = 3 := by
              have := hE s hs.1; rw [← hs5_map, Finset.card_map] at this; exact this
            have hex_t : ∀ U : Finset (Fin 5), U.card = 3 →
                ∃ t : Fin 10, let (a, b, c, _, _) := tripleSplit5 t; ({a, b, c} : Finset (Fin 5)) = U := by
              decide
            obtain ⟨t, ht⟩ := hex_t s5 hs5_card
            rcases htr : tripleSplit5 t with ⟨a, b, c, x, y⟩
            simp only [htr] at ht
            have hseq : ({embA A a, embA A b, embA A c} : Finset (Fin n)) = s := by
              rw [← hs5_map, ← ht]
              ext v; simp
            refine ⟨t, ?_, by simp only [htr]; exact hseq⟩
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            simp only [htr]; dsimp only [gA, e]
            rw [hseq]; exact decide_eq_true hs.1
        rw [hbij_e, Finset.card_filter]
        have htoNat : ∀ t : Fin 10,
            (if (let (a, b, c, _, _) := tripleSplit5 t; gA A a b c = true) then (1 : ℕ) else 0) =
            (let (a, b, c, _, _) := tripleSplit5 t; (gA A a b c).toNat) := by
          intro t
          rcases tripleSplit5 t with ⟨a, b, c, _, _⟩
          dsimp only; cases gA A a b c <;> rfl
        rw [Finset.sum_congr rfl (fun t _ => htoNat t)]
        rcases maskBit_encodeMask5 (gA A) with ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9⟩
        dsimp only [maskEdgeCount]
        rw [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9]
        rw [sum_fin10]
        dsimp only [tripleSplit5]
        have hbZ : ∀ b : Bool, (if b = true then (1 : ℤ) else 0) = (b.toNat : ℤ) := by
          intro b; cases b <;> rfl
        push_cast
        simp_rw [hbZ]
      have hloc := local_5vertex_sos_bound (gA A) hsym1 hsym2 hk4
      rw [hedge_eq] at hloc
      exact hloc
    -- 3c: Double-count ∑ A ∈ P5, (E.filter (· ⊆ A.1)).card = E.card * (n - 3).choose 2!
    have hsum_edges : ∑ A ∈ P5, (E.filter (fun s => s ⊆ A.1)).card = E.card * (n - 3).choose 2 := by
      have h1 : ∑ A ∈ P5, (E.filter (fun s => s ⊆ A.1)).card =
          ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard 5, (E.filter (fun s => s ⊆ A)).card :=
        Finset.sum_attach ((Finset.univ : Finset (Fin n)).powersetCard 5)
          (fun A => (E.filter (fun s => s ⊆ A)).card)
      rw [h1]
      calc ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard 5, (E.filter (fun s => s ⊆ A)).card
          = ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard 5,
              ∑ s ∈ E, if s ⊆ A then 1 else 0 := by
            refine Finset.sum_congr rfl fun A _ => Finset.card_filter _ _
        _ = ∑ s ∈ E, ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard 5,
              if s ⊆ A then 1 else 0 := Finset.sum_comm
        _ = ∑ s ∈ E, (n - 3).choose 2 := by
            refine Finset.sum_congr rfl fun s hs => ?_
            rw [← Finset.card_filter]
            have hbij : ((Finset.univ \ s).powersetCard 2).card =
                (((Finset.univ : Finset (Fin n)).powersetCard 5).filter (fun A => s ⊆ A)).card := by
              refine Finset.card_bij (fun p _ => p ∪ s) ?_ ?_ ?_
              · intro p hp
                rw [Finset.mem_powersetCard] at hp
                have hdisj : Disjoint p s := Finset.disjoint_left.mpr fun x hxp =>
                  (Finset.mem_sdiff.mp (hp.1 hxp)).2
                rw [Finset.mem_filter, Finset.mem_powersetCard]
                exact ⟨⟨Finset.subset_univ _, by
                  rw [Finset.card_union_of_disjoint hdisj, hp.2, hE s hs]⟩,
                  Finset.subset_union_right⟩
              · intro p1 hp1 p2 hp2 heq
                rw [Finset.mem_powersetCard] at hp1 hp2
                have hd1 : Disjoint p1 s := Finset.disjoint_left.mpr fun x hx =>
                  (Finset.mem_sdiff.mp (hp1.1 hx)).2
                have hd2 : Disjoint p2 s := Finset.disjoint_left.mpr fun x hx =>
                  (Finset.mem_sdiff.mp (hp2.1 hx)).2
                have h := congrArg (fun U => U \ s) heq
                rwa [Finset.union_sdiff_cancel_right hd1, Finset.union_sdiff_cancel_right hd2] at h
              · intro A hA
                rw [Finset.mem_filter, Finset.mem_powersetCard] at hA
                refine ⟨A \ s, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.sdiff_union_of_subset hA.2⟩
                · intro x hx; rw [Finset.mem_sdiff] at hx ⊢; exact ⟨Finset.mem_univ x, hx.2⟩
                · rw [Finset.card_sdiff_of_subset hA.2, hA.1.2, hE s hs]
            rw [← hbij, Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ s),
              Finset.card_univ, Fintype.card_fin, hE s hs]
        _ = E.card * (n - 3).choose 2 := by rw [Finset.sum_const, smul_eq_mul]
    have hsum_loc := Finset.sum_le_sum hlocal
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hOff_group, Finset.sum_const, nsmul_eq_mul] at hsum_loc
    have hP5_card : P5.card = n.choose 5 := by
      rw [Finset.card_attach, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    have hsum_edgesZ : (∑ A ∈ P5, ((E.filter (fun s => s ⊆ A.1)).card : ℤ)) =
        ((E.card * (n - 3).choose 2 : ℕ) : ℤ) := by
      exact_mod_cast hsum_edges
    rw [hsum_edgesZ, hP5_card] at hsum_loc
    linarith
  have hZ : (4800 : ℤ) * ((E.card * (n - 3).choose 2 : ℕ) : ℤ) ≤
      27744 * (n.choose 5 : ℤ) + 11880 * (n.choose 4 : ℤ) := by linarith
  have hNat : 4800 * (E.card * (n - 3).choose 2) ≤ 27744 * n.choose 5 + 11880 * n.choose 4 := by
    exact_mod_cast hZ
  linarith

/-- **Explicit Finite-`n` Density Upper Bound (`289 / 500 + (99 / 80) / (n - 4)`)**:
For every `n ≥ 5` and every `K_4^3`-free 3-uniform hypergraph `E` on `Fin n`:
`E.card / n.choose 3 ≤ 289 / 500 + (99 / 80) / (n - 4)`. -/
theorem ppl074_flag5_sos_density_finite {n : ℕ} (hn : 5 ≤ n)
    (E : Finset (Finset (Fin n)))
    (hE : ∀ e ∈ E, e.card = 3)
    (hfree : ∀ K : Finset (Fin n), K.card = 4 → ¬ K.powersetCard 3 ⊆ E) :
    (E.card : ℝ) / (n.choose 3 : ℝ) ≤ (289 / 500 : ℝ) + (99 / 80 : ℝ) / ((n : ℝ) - 4) := by
  have hfin := ppl074_flag5_sos_finite_upper hn E hE hfree
  have hfinR : (4800 : ℝ) * (E.card : ℝ) * ((n - 3).choose 2 : ℝ) ≤
      27744 * (n.choose 5 : ℝ) + 11880 * (n.choose 4 : ℝ) := by exact_mod_cast hfin
  have h5 : (10 : ℝ) * (n.choose 5 : ℝ) = (n.choose 3 : ℝ) * ((n - 3).choose 2 : ℝ) := by
    exact_mod_cast ten_mul_choose_five n hn
  have h4 : (4 : ℝ) * (n.choose 4 : ℝ) = (n.choose 3 : ℝ) * ((n - 3 : ℕ) : ℝ) := by
    exact_mod_cast four_mul_choose_four n (by omega)
  have h2 : (2 : ℝ) * ((n - 3).choose 2 : ℝ) = ((n - 3 : ℕ) : ℝ) * ((n - 4 : ℕ) : ℝ) := by
    have := choose_two_mul_two (n - 3)
    have hsub : n - 3 - 1 = n - 4 := by omega
    rw [hsub] at this
    have hR : ((n - 3).choose 2 : ℝ) * 2 = ((n - 3 : ℕ) : ℝ) * ((n - 4 : ℕ) : ℝ) := by
      exact_mod_cast this
    linarith
  have hn3_pos : (0 : ℝ) < (n.choose 3 : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : 3 ≤ n)
  have hc2_pos : (0 : ℝ) < ((n - 3).choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ n - 3)
  have hn4_eq : ((n - 4 : ℕ) : ℝ) = (n : ℝ) - 4 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hn4_pos : (0 : ℝ) < (n : ℝ) - 4 := by
    have : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [div_le_iff₀ hn3_pos]
  have hstep : (E.card : ℝ) * (4800 * ((n - 3).choose 2 : ℝ)) ≤
      ((289 / 500 : ℝ) + (99 / 80 : ℝ) / ((n : ℝ) - 4)) * (n.choose 3 : ℝ) *
        (4800 * ((n - 3).choose 2 : ℝ)) := by
    have hR1 : 27744 * (n.choose 5 : ℝ) = (289 / 500 : ℝ) * (n.choose 3 : ℝ) * (4800 * ((n - 3).choose 2 : ℝ)) := by
      linarith [h5]
    have hR2 : 11880 * (n.choose 4 : ℝ) =
        ((99 / 80 : ℝ) / ((n : ℝ) - 4)) * (n.choose 3 : ℝ) * (4800 * ((n - 3).choose 2 : ℝ)) := by
      have hmul : ((99 / 80 : ℝ) / ((n : ℝ) - 4)) * (4800 * ((n - 3).choose 2 : ℝ)) =
          2970 * ((n - 3 : ℕ) : ℝ) := by
        rw [div_mul_eq_mul_div, div_eq_iff (ne_of_gt hn4_pos), ← hn4_eq]
        linarith [h2]
      calc 11880 * (n.choose 4 : ℝ)
          = 2970 * (4 * (n.choose 4 : ℝ)) := by ring
        _ = 2970 * ((n.choose 3 : ℝ) * ((n - 3 : ℕ) : ℝ)) := by rw [h4]
        _ = (2970 * ((n - 3 : ℕ) : ℝ)) * (n.choose 3 : ℝ) := by ring
        _ = (((99 / 80 : ℝ) / ((n : ℝ) - 4)) * (4800 * ((n - 3).choose 2 : ℝ))) * (n.choose 3 : ℝ) := by
            rw [← hmul]
        _ = ((99 / 80 : ℝ) / ((n : ℝ) - 4)) * (n.choose 3 : ℝ) * (4800 * ((n - 3).choose 2 : ℝ)) := by
            ring
    linarith [hfinR, hR1, hR2]
  exact le_of_mul_le_mul_right hstep (by positivity : (0 : ℝ) < 4800 * ((n - 3).choose 2 : ℝ))

/-- Strict ordering of certified SOS constant `289 / 500 = 0.578` below Chung–Lu `(3 + √17) / 12`,
de Caen `5 / 8`, and de Caen `2 / 3`. -/
theorem ppl074_upper_beats_chung_lu_const :
    (289 / 500 : ℝ) < (3 + Real.sqrt 17) / 12 ∧
    (3 + Real.sqrt 17) / 12 < (5 / 8 : ℝ) ∧
    (5 / 8 : ℝ) < (2 / 3 : ℝ) := by
  have hsq17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hnn17 : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg 17
  refine ⟨?_, ?_, by norm_num⟩
  · nlinarith [hsq17, hnn17]
  · nlinarith [hsq17, hnn17]

/-- **Capstone Theorem — Certified Turán Density Sandwich Beating Chung–Lu & de Caen**:
The Turán density `π(K_4^3) = lim_{n → ∞} ex_3(n, K_4^3) / n.choose 3` exists and satisfies
`5 / 9 ≤ π(K_4^3) ≤ 289 / 500 < (3 + √17) / 12 < 5 / 8`. -/
theorem ppl074_density_sandwich_beats_chung_lu :
    ∃ π : ℝ,
      Filter.Tendsto
        (fun n : ℕ =>
          ((sSup {m : ℕ | ∃ E : Finset (Finset (Fin n)),
            (∀ e ∈ E, e.card = 3) ∧
            (∀ K : Finset (Fin n), K.card = 4 → ¬ K.powersetCard 3 ⊆ E) ∧
            E.card = m} : ℕ) : ℝ) / (n.choose 3 : ℝ))
        Filter.atTop (nhds π) ∧
      (5 / 9 : ℝ) ≤ π ∧
      π ≤ (289 / 500 : ℝ) ∧
      π < (3 + Real.sqrt 17) / 12 ∧
      π < (5 / 8 : ℝ) := by
  obtain ⟨π, _, htend⟩ := ppl074_turan_density_exists 3 4 (by omega) (by omega)
  let d : ℕ → ℝ := fun n =>
    ((sSup {m : ℕ | ∃ E : Finset (Finset (Fin n)),
      (∀ e ∈ E, e.card = 3) ∧
      (∀ K : Finset (Fin n), K.card = 4 → ¬ K.powersetCard 3 ⊆ E) ∧
      E.card = m} : ℕ) : ℝ) / (n.choose 3 : ℝ)
  have hlow : ∀ᶠ n : ℕ in Filter.atTop, (5 / 9 : ℝ) ≤ d n := by
    filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    obtain ⟨E, hE, hfree, h9⟩ := ppl074_turan_lower_all_n n
    have hle : E.card ≤ sSup {m : ℕ | ∃ E' : Finset (Finset (Fin n)),
        (∀ e ∈ E', e.card = 3) ∧
        (∀ K : Finset (Fin n), K.card = 4 → ¬ K.powersetCard 3 ⊆ E') ∧
        E'.card = m} :=
      le_csSup (ex_set_bddAbove n 3 4) ⟨E, hE, hfree, rfl⟩
    have hpos : (0 : ℝ) < (n.choose 3 : ℝ) := by exact_mod_cast Nat.choose_pos hn
    have h9R : (5 : ℝ) * (n.choose 3 : ℝ) ≤ 9 * (E.card : ℝ) := by exact_mod_cast h9
    have hleR : (E.card : ℝ) ≤ ((sSup {m : ℕ | ∃ E' : Finset (Finset (Fin n)),
        (∀ e ∈ E', e.card = 3) ∧
        (∀ K : Finset (Fin n), K.card = 4 → ¬ K.powersetCard 3 ⊆ E') ∧
        E'.card = m} : ℕ) : ℝ) := by exact_mod_cast hle
    dsimp only [d]
    rw [le_div_iff₀ hpos]
    linarith
  have hpi_ge : (5 / 9 : ℝ) ≤ π := ge_of_tendsto htend hlow
  have hup_ev : ∀ᶠ n : ℕ in Filter.atTop, d n ≤ (289 / 500 : ℝ) + (99 / 80 : ℝ) / ((n : ℝ) - 4) := by
    filter_upwards [Filter.eventually_ge_atTop 5] with n hn
    obtain ⟨E, hE, hfree, hcard⟩ := ex_attained n 3 4 (by omega)
    dsimp only [d]
    rw [← hcard]
    exact ppl074_flag5_sos_density_finite hn E hE hfree
  have hlim_rhs : Filter.Tendsto (fun n : ℕ => (289 / 500 : ℝ) + (99 / 80 : ℝ) / ((n : ℝ) - 4))
      Filter.atTop (nhds (289 / 500 : ℝ)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) - 4) Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
    have h2 : Filter.Tendsto (fun n : ℕ => (99 / 80 : ℝ) / ((n : ℝ) - 4)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop h1
    simpa using tendsto_const_nhds.add h2
  have hpi_le : π ≤ (289 / 500 : ℝ) := le_of_tendsto_of_tendsto htend hlim_rhs hup_ev
  obtain ⟨hcl, hdc, _⟩ := ppl074_upper_beats_chung_lu_const
  exact ⟨π, htend, hpi_ge, hpi_le, lt_of_le_of_lt hpi_le hcl,
    lt_trans (lt_of_le_of_lt hpi_le hcl) hdc⟩

end PPL074
