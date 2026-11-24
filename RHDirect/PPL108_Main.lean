/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

/-!
# PPL 108 & PPL 111 (Nanongkai — `v`-Hinted Mv & OMv Conjectures)

## Scope & Honest Labeling
This file formalizes a comprehensive pure-Mathlib milestone (`0` `sorry`, `0` custom definitions
in any public theorem signature) for **PPL 108** (`v`-Hinted Mv Conjecture, Conjecture 5.2 of
van den Brand–Nanongkai–Saranurak, FOCS 2019, `arXiv:1905.05067`, €300) and **PPL 111**
(Online Matrix–Vector Multiplication Conjecture, Henzinger–Krinninger–Nanongkai–Saranurak,
STOC 2015, `arXiv:1511.06773`, €500).

**BOTH the full Word-RAM `v`-Hinted Mv Conjecture (PPL 108) and the full Word-RAM OMv Conjecture
(PPL 111) REMAIN OPEN.** This file does **not** claim to prove or disprove either full Word-RAM
conjecture (indeed, cell-probe upper bounds by Larsen–Williams SODA 2017 and
Chakraborty–Kamma–Larsen STOC 2018 rule out purely information-theoretic cell-probe proofs of
the Word-RAM OMv and `v`-Hinted Mv conjectures).

Instead, this file establishes complete, self-contained, pure-Mathlib formalizations of:
1. **Exact Information-Theoretic Storage, Adaptive Query, and Online Cell-Probe Lower Bounds**
   (`ppl108_mv_storage_lower_bound`, `ppl108_umv_no_preproc_adaptive_query_lower_bound`,
   `ppl108_omv_adaptive_cell_probe_lower_bound`).
2. **Sharp Log-Free Succinct Adaptive Cell-Probe Lower Bound for Rectangular Boolean `Mv` &
   `v`-Hinted `Mv`** (`ppl108_boolean_mv_succinct_cell_probe_lower_bound`,
   `ppl108_boolean_mv_succinct_tradeoff`): generalizes Chakraborty–Kamma–Larsen (STOC 2018)
   from square `n × n` to arbitrary rectangular `m × c` Boolean matrices, proving
   `m * c ≤ 210 * t * (r / m + 1)` for all `4 * (r / m + 1) ≤ c` (yielding `t * r = Ω(n^3)` for
   square `Mv` and `t * r = Ω(n^{2+τ})` for `v`-Hinted `Mv` with `m = n, c = n^τ`, matching
   the CKL18 block upper bound up to constants with zero log factors).
3. **Sharp Log-Free Succinct Adaptive Cell-Probe Lower Bound for Rectangular `𝔽₂`-`Mv`**
   (`ppl108_f2_mv_succinct_cell_probe_lower_bound`): via Gilbert–Varshamov linear codes and a
   Kraft equivalence-class partition, proves `18 * r ≥ m * c ∨ 10 * t ≥ m * c ∨ 40 * r * t ≥ m^2 * c`
   for all `m ≥ 1, c ≥ 5`.
4. **Exact Four-Russians / Block-Precomputation `O(m c / log n)` Upper Bound**
   (`ppl108_four_russians_mv_upper_bound`, `ppl108_four_russians_log_speedup`), formalizing
   vdBNS19 Theorem `thm:matrixVectorAppendix`.
5. **Exact Combinatorial Reductions Linking `OMv`, `OuMv`, `uMv`, `Mv`, and `v`-Hinted `Mv`**
   (`ppl108_mv_to_vhinted_mv_block_reduction`, `ppl108_umv_to_symmetric_indep_set_reduction`,
   `ppl108_omv_to_square_oumv_reduction`), including the exact HKNS15 adaptive row-deletion +
   binary-search witness reduction from `OMv` to square `OuMv`.
-/

namespace PPL108

open scoped BigOperators

/-! ### Section 1: Exact Storage, No-Preprocessing Adaptive `uMv`, and Online Cell-Probe Bounds -/

/-- **PPL 108 / PPL 111 Exact Information-Theoretic Storage Lower Bound for Boolean `Mv`:**
Any data structure encoding an `m × c` Boolean matrix into `S` cells of `w` bits that correctly
answers Boolean matrix-vector queries `(M v)_i = ∃ j, M i j ∧ v j` must use at least `m * c`
total bits of storage (`m * c ≤ S * w`). In particular, for `v`-Hinted `Mv` (`m = n, c = t`),
storage is at least `n * t` bits. -/
theorem ppl108_mv_storage_lower_bound (m c S w : ℕ)
    (enc : Matrix (Fin m) (Fin c) Bool → (Fin S → Fin (2 ^ w)))
    (dec : (Fin S → Fin (2 ^ w)) → (Fin c → Bool) → (Fin m → Bool))
    (hcorr : ∀ (M : Matrix (Fin m) (Fin c) Bool) (v : Fin c → Bool) (i : Fin m),
      dec (enc M) v i = true ↔ ∃ j : Fin c, M i j = true ∧ v j = true) :
    m * c ≤ S * w := by
  have hinj : Function.Injective enc := by
    intro M₁ M₂ hEq
    ext i j
    let e_j : Fin c → Bool := fun k => decide (k = j)
    have h1 := hcorr M₁ e_j i
    have h2 := hcorr M₂ e_j i
    rw [hEq] at h1
    have hiff : (∃ k : Fin c, M₁ i k = true ∧ e_j k = true) ↔
        (∃ k : Fin c, M₂ i k = true ∧ e_j k = true) := h1.symm.trans h2
    have h1' : (∃ k : Fin c, M₁ i k = true ∧ e_j k = true) ↔ M₁ i j = true := by
      constructor
      · rintro ⟨k, hk1, hk2⟩
        have hkj : k = j := of_decide_eq_true hk2
        rwa [← hkj]
      · intro h
        exact ⟨j, h, decide_eq_true rfl⟩
    have h2' : (∃ k : Fin c, M₂ i k = true ∧ e_j k = true) ↔ M₂ i j = true := by
      constructor
      · rintro ⟨k, hk1, hk2⟩
        have hkj : k = j := of_decide_eq_true hk2
        rwa [← hkj]
      · intro h
        exact ⟨j, h, decide_eq_true rfl⟩
    exact Bool.eq_iff_iff.mpr ((h1'.symm.trans hiff).trans h2')
  have hcard : Fintype.card (Matrix (Fin m) (Fin c) Bool) ≤
      Fintype.card (Fin S → Fin (2 ^ w)) := Fintype.card_le_of_injective enc hinj
  have hLcard : Fintype.card (Matrix (Fin m) (Fin c) Bool) = 2 ^ (m * c) := by
    rw [Fintype.card_congr (Matrix.of.symm)]
    simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Fintype.card_bool, ← pow_mul, mul_comm]
  have hRcard : Fintype.card (Fin S → Fin (2 ^ w)) = 2 ^ (S * w) := by
    simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul, mul_comm]
  rw [hLcard, hRcard] at hcard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

private def visitedCoords {m c : ℕ} (next : List Bool → Fin m × Fin c)
    (M : Matrix (Fin m) (Fin c) Bool) : ℕ → List Bool × Finset (Fin m × Fin c)
  | 0 => ([], ∅)
  | k + 1 =>
    let res := visitedCoords next M k
    let p := next res.1
    (M p.1 p.2 :: res.1, insert p res.2)

private lemma visitedCoords_fst {m c : ℕ} (next : List Bool → Fin m × Fin c)
    (M : Matrix (Fin m) (Fin c) Bool) (k : ℕ) :
    (visitedCoords next M k).1 =
      (fun hist : List Bool => M (next hist).1 (next hist).2 :: hist)^[k] [] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [visitedCoords, Function.iterate_succ_apply', ih]

private lemma visitedCoords_card_le {m c : ℕ} (next : List Bool → Fin m × Fin c)
    (M : Matrix (Fin m) (Fin c) Bool) (k : ℕ) :
    (visitedCoords next M k).2.card ≤ k := by
  induction k with
  | zero => simp [visitedCoords]
  | succ k ih =>
    simp only [visitedCoords]
    exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ih)

private lemma visitedCoords_agree {m c : ℕ} (next : List Bool → Fin m × Fin c)
    (M₁ M₂ : Matrix (Fin m) (Fin c) Bool) (k : ℕ)
    (hagree : ∀ p ∈ (visitedCoords next M₁ k).2, M₁ p.1 p.2 = M₂ p.1 p.2) :
    (visitedCoords next M₁ k).1 = (visitedCoords next M₂ k).1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hsub : ∀ p ∈ (visitedCoords next M₁ k).2, M₁ p.1 p.2 = M₂ p.1 p.2 := by
      intro p hp
      exact hagree p (Finset.mem_insert_of_mem hp)
    have hprev := ih hsub
    have hcur : M₁ (next (visitedCoords next M₁ k).1).1 (next (visitedCoords next M₁ k).1).2 =
        M₂ (next (visitedCoords next M₁ k).1).1 (next (visitedCoords next M₁ k).1).2 :=
      hagree _ (Finset.mem_insert_self _ _)
    simp only [visitedCoords, ← hprev, hcur]

/-- **PPL 108 / PPL 111 Exact No-Preprocessing Adaptive Query Lower Bound for Boolean `uMv`:**
Any deterministic adaptive bit-probe algorithm making `t` probes to `M : Matrix (Fin m) (Fin c) Bool`
that correctly decides Boolean `uMv` at `u = 1, v = 1` (`∃ i j, M i j = true`) must probe all
`m * c` entries (`m * c ≤ t`). -/
theorem ppl108_umv_no_preproc_adaptive_query_lower_bound (m c t : ℕ)
    (next : List Bool → Fin m × Fin c)
    (out : List Bool → Bool)
    (hcorr : ∀ M : Matrix (Fin m) (Fin c) Bool,
      out ((fun hist : List Bool => M (next hist).1 (next hist).2 :: hist)^[t] []) = true ↔
        ∃ i : Fin m, ∃ j : Fin c, M i j = true) :
    m * c ≤ t := by
  by_contra hlt
  push Not at hlt
  let M₀ : Matrix (Fin m) (Fin c) Bool := fun _ _ => false
  let S := (visitedCoords next M₀ t).2
  have hScard : S.card < Fintype.card (Fin m × Fin c) := by
    have hle : S.card ≤ t := visitedCoords_card_le next M₀ t
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    omega
  have hne : (Finset.univ \ S).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsub : (Finset.univ : Finset (Fin m × Fin c)) ⊆ S := Finset.sdiff_eq_empty_iff_subset.mp hempty
    have hge : Fintype.card (Fin m × Fin c) ≤ S.card := by
      simpa using Finset.card_le_card hsub
    omega
  obtain ⟨⟨i₀, j₀⟩, hp⟩ := hne
  have hnotmem : (i₀, j₀) ∉ S := (Finset.mem_sdiff.mp hp).2
  let M₁ : Matrix (Fin m) (Fin c) Bool := fun i j => decide (i = i₀ ∧ j = j₀)
  have hagree : ∀ p ∈ S, M₀ p.1 p.2 = M₁ p.1 p.2 := by
    intro p hpS
    have hne' : p ≠ (i₀, j₀) := fun h => hnotmem (h ▸ hpS)
    have hnot : ¬ (p.1 = i₀ ∧ p.2 = j₀) := by
      rintro ⟨h1, h2⟩
      exact hne' (Prod.ext h1 h2)
    simp only [M₀, M₁]
    exact (decide_eq_false hnot).symm
  have hhist : (visitedCoords next M₀ t).1 = (visitedCoords next M₁ t).1 :=
    visitedCoords_agree next M₀ M₁ t hagree
  rw [visitedCoords_fst, visitedCoords_fst] at hhist
  have h0 : out ((fun hist : List Bool => M₀ (next hist).1 (next hist).2 :: hist)^[t] []) = false := by
    cases h : out ((fun hist : List Bool => M₀ (next hist).1 (next hist).2 :: hist)^[t] [])
    · rfl
    · exfalso
      obtain ⟨i, j, hij⟩ := (hcorr M₀).mp h
      simp [M₀] at hij
  have h1 : out ((fun hist : List Bool => M₁ (next hist).1 (next hist).2 :: hist)^[t] []) = true := by
    exact (hcorr M₁).mpr ⟨i₀, j₀, by simp [M₁]⟩
  rw [← hhist, h0] at h1
  exact Bool.false_ne_true h1

private lemma iter_list_length {α : Type*} (f : List α → α) (q : ℕ) :
    ((fun hist : List α => f hist :: hist)^[q] []).length = q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [Function.iterate_succ_apply', List.length_cons, ih]

/-- **PPL 108 / PPL 111 Unconditional Adaptive Cell-Probe Lower Bound for Preprocessed `Mv` / `OMv`:**
Even with arbitrary unbounded preprocessing of `M : Matrix (Fin m) (Fin c) Bool` (`1 ≤ c`) into
`S` cells of `w` bits, any adaptive deterministic `q`-cell-probe query algorithm computing Boolean
`Mv` must satisfy `m ≤ q * w`. Consequently, answering `k` online queries with probe budgets
`q_1, ..., q_k` requires `k * m ≤ (∑ i : Fin k, q i) * w`. -/
theorem ppl108_omv_adaptive_cell_probe_lower_bound (m c S w q : ℕ) (hc : 1 ≤ c)
    (enc : Matrix (Fin m) (Fin c) Bool → (Fin S → Fin (2 ^ w)))
    (next : (Fin c → Bool) → List (Fin (2 ^ w)) → Fin S)
    (out : (Fin c → Bool) → List (Fin (2 ^ w)) → (Fin m → Bool))
    (hcorr : ∀ (M : Matrix (Fin m) (Fin c) Bool) (v : Fin c → Bool) (i : Fin m),
      out v ((fun hist : List (Fin (2 ^ w)) => enc M (next v hist) :: hist)^[q] []) i = true ↔
        ∃ j : Fin c, M i j = true ∧ v j = true) :
    m ≤ q * w := by
  let v₀ : Fin c → Bool := fun j => decide (j.val = 0)
  let decodeHist : (Fin q → Fin (2 ^ w)) → (Fin m → Bool) :=
    fun f => out v₀ (List.ofFn f)
  have hsurj : Function.Surjective decodeHist := by
    intro y
    let M : Matrix (Fin m) (Fin c) Bool := fun i j => if j.val = 0 then y i else false
    let hist := (fun hist : List (Fin (2 ^ w)) => enc M (next v₀ hist) :: hist)^[q] []
    have hlen : hist.length = q := iter_list_length (fun h => enc M (next v₀ h)) q
    let f : Fin q → Fin (2 ^ w) := fun idx => hist.get (idx.cast hlen.symm)
    refine ⟨f, ?_⟩
    have hofFn : List.ofFn f = hist := by
      apply List.ext_getElem
      · simp [hlen]
      · intro n h1 h2
        simp [f]
    ext i
    dsimp only [decodeHist]
    rw [hofFn]
    have hci := hcorr M v₀ i
    apply Bool.eq_iff_iff.mpr
    rw [hci]
    constructor
    · rintro ⟨j, hj1, hj2⟩
      have hj0 : j.val = 0 := of_decide_eq_true hj2
      simpa [M, hj0] using hj1
    · intro hyi
      exact ⟨⟨0, hc⟩, by simp [M, hyi], by simp [v₀]⟩
  have hcard : Fintype.card (Fin m → Bool) ≤ Fintype.card (Fin q → Fin (2 ^ w)) :=
    Fintype.card_le_of_surjective decodeHist hsurj
  simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_bool] at hcard
  rw [← pow_mul, mul_comm w q] at hcard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

/-! ### Section 2: Sharp Log-Free Succinct Adaptive Cell-Probe Lower Bound for Boolean `Mv` -/

private lemma powerset_sum_pow {α : Type*} [Fintype α] [DecidableEq α] (x : ℝ) :
    ∑ s ∈ (Finset.univ : Finset α).powerset, x ^ s.card = (1 + x) ^ Fintype.card α := by
  have h := Finset.prod_add (fun _ : α => x) (fun _ : α => (1 : ℝ)) (Finset.univ : Finset α)
  simp only [Finset.prod_const, Finset.card_univ, one_pow, mul_one] at h
  rw [add_comm (1 : ℝ) x, h]

private lemma exp_half_le_two : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
  have h1 : Real.exp (1 : ℝ) < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hsq : Real.exp ((1 : ℝ) / 2) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos ((1 : ℝ) / 2)]

private def blockMat {m c b L : ℕ} (f : Fin m × Fin b → Fin L) :
    Matrix (Fin m) (Fin c) Bool :=
  fun i j =>
    if h : j.val / L < b then
      decide (j.val % L = (f (i, ⟨j.val / L, h⟩)).val)
    else false

private lemma blockMat_injective {m c b L : ℕ} (hL : 0 < L) (hbL : b * L ≤ c) :
    Function.Injective (@blockMat m c b L) := by
  intro f₁ f₂ hEq
  ext ⟨i, s⟩
  have hjlt : s.val * L + (f₁ (i, s)).val < c := by
    have h1 : s.val * L + (f₁ (i, s)).val < (s.val + 1) * L := by
      rw [Nat.add_mul, one_mul]
      exact Nat.add_lt_add_left (f₁ (i, s)).isLt _
    have h2 : (s.val + 1) * L ≤ b * L := Nat.mul_le_mul_right L s.isLt
    omega
  let j : Fin c := ⟨s.val * L + (f₁ (i, s)).val, hjlt⟩
  have hdiv : j.val / L = s.val := by
    dsimp only [j]
    rw [mul_comm s.val L, Nat.mul_add_div hL, Nat.div_eq_of_lt (f₁ (i, s)).isLt, add_zero]
  have hmod : j.val % L = (f₁ (i, s)).val := by
    dsimp only [j]
    rw [mul_comm s.val L, Nat.mul_add_mod, Nat.mod_eq_of_lt (f₁ (i, s)).isLt]
  have hval := congrFun (congrFun hEq i) j
  have hltb : j.val / L < b := by rw [hdiv]; exact s.isLt
  simp only [blockMat, dif_pos hltb] at hval
  have htrue : decide (j.val % L = (f₁ (i, ⟨j.val / L, hltb⟩)).val) = true := by
    refine decide_eq_true ?_
    have hs : (⟨j.val / L, hltb⟩ : Fin b) = s := Fin.ext hdiv
    rw [hs, hmod]
  rw [htrue] at hval
  have hEq2 : j.val % L = (f₂ (i, ⟨j.val / L, hltb⟩)).val := of_decide_eq_true hval.symm
  have hs : (⟨j.val / L, hltb⟩ : Fin b) = s := Fin.ext hdiv
  rw [hs, hmod] at hEq2
  exact hEq2

private lemma blockMat_unique_true {m c b L : ℕ}
    (f : Fin m × Fin b → Fin L) (i : Fin m) (j : Fin c)
    (htrue : blockMat f i j = true) :
    ∃ h : j.val / L < b, (f (i, ⟨j.val / L, h⟩)).val = j.val % L := by
  dsimp only [blockMat] at htrue
  split_ifs at htrue with h
  · exact ⟨h, (of_decide_eq_true htrue).symm⟩

private lemma blockMat_at {m c b L : ℕ} (hL : 0 < L) (hbL : b * L ≤ c)
    (f : Fin m × Fin b → Fin L) (i : Fin m) (s : Fin b) (p : Fin L) :
    let hj : s.val * L + p.val < c := by
      have h1 : (s.val + 1) * L ≤ b * L := Nat.mul_le_mul_right L s.isLt
      nlinarith [p.isLt]
    blockMat f i ⟨s.val * L + p.val, hj⟩ = decide (p = f (i, s)) := by
  intro hj
  have hdiv : (s.val * L + p.val) / L = s.val := by
    rw [mul_comm s.val L, Nat.mul_add_div hL, Nat.div_eq_of_lt p.isLt, add_zero]
  have hmod : (s.val * L + p.val) % L = p.val := by
    rw [mul_comm s.val L, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]
  have hltb : (s.val * L + p.val) / L < b := by rw [hdiv]; exact s.isLt
  simp only [blockMat, dif_pos hltb]
  have hs : (⟨(s.val * L + p.val) / L, hltb⟩ : Fin b) = s := Fin.ext hdiv
  rw [hs, hmod]
  exact decide_eq_decide.mpr (by rw [Fin.ext_iff])

private lemma exists_boolean_query_family {m c b L : ℕ} (hb : 1 ≤ b) (hL : 4 ≤ L) (hbL : b * L ≤ c) :
    ∃ (K : ℕ) (V : Fin K → (Fin c → Bool)),
      K ≤ 21 * b ∧
      ∀ (f₀ : Fin m × Fin b → Fin L) (i : Fin m) (s : Fin b),
        (Finset.univ.filter fun p : Fin L =>
          ∀ a : Fin K,
            (∀ hj : s.val * L + p.val < c, V a ⟨s.val * L + p.val, hj⟩ = true →
              ∃ j : Fin c, blockMat f₀ i j = true ∧ V a j = true)).card ≤ L / 4 := by
  have hLpos : 0 < L := by omega
  by_cases hcase : 8 * b ≤ L
  · -- Case 1: 8 * b ≤ L. Take K = 8 * b, partition Fin L by p % K.
    let K := 8 * b
    have hKpos : 0 < K := by omega
    let V : Fin K → (Fin c → Bool) := fun a j =>
      decide (j.val < b * L ∧ (j.val % L) % K = a.val)
    refine ⟨K, V, by omega, fun f₀ i s => ?_⟩
    let A : Finset (Fin K) :=
      Finset.univ.image (fun s' : Fin b => ⟨(f₀ (i, s')).val % K, Nat.mod_lt _ hKpos⟩)
    have hAcard : A.card ≤ b := by
      exact le_trans Finset.card_image_le (by simp)
    let S := Finset.univ.filter fun p : Fin L =>
      ∀ a : Fin K,
        (∀ hj : s.val * L + p.val < c, V a ⟨s.val * L + p.val, hj⟩ = true →
          ∃ j : Fin c, blockMat f₀ i j = true ∧ V a j = true)
    have hSsub : S ⊆ A.biUnion (fun a => Finset.univ.filter (fun p : Fin L => p.val % K = a.val)) := by
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      let a : Fin K := ⟨p.val % K, Nat.mod_lt _ hKpos⟩
      have hjlt : s.val * L + p.val < c := by
        have h1 : (s.val + 1) * L ≤ b * L := Nat.mul_le_mul_right L s.isLt
        nlinarith [p.isLt]
      have hjltbL : s.val * L + p.val < b * L := by
        have h1 : (s.val + 1) * L ≤ b * L := Nat.mul_le_mul_right L s.isLt
        nlinarith [p.isLt]
      have hVa : V a ⟨s.val * L + p.val, hjlt⟩ = true := by
        refine decide_eq_true ⟨hjltbL, ?_⟩
        dsimp only
        rw [mul_comm s.val L, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]
      obtain ⟨j, hjM, hjV⟩ := hp' a hjlt hVa
      obtain ⟨hjb, hf0⟩ := blockMat_unique_true f₀ i j hjM
      have hmod := (of_decide_eq_true hjV).2
      rw [← hf0] at hmod
      refine Finset.mem_biUnion.mpr ⟨a, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
      exact Finset.mem_image.mpr ⟨⟨j.val / L, hjb⟩, Finset.mem_univ _, Fin.ext hmod⟩
    have hfiber : ∀ a : Fin K,
        (Finset.univ.filter (fun p : Fin L => p.val % K = a.val)).card ≤ (L - 1) / K + 1 := by
      intro a
      let T := Finset.univ.filter (fun p : Fin L => p.val % K = a.val)
      have hinj : Set.InjOn (fun p : Fin L => (⟨p.val / K, by
          have : p.val ≤ L - 1 := by omega
          exact Nat.lt_succ_of_le (Nat.div_le_div_right this)⟩ : Fin ((L - 1) / K + 1))) T := by
        intro p₁ hp₁ p₂ hp₂ hdiv
        have h1 := (Finset.mem_filter.mp hp₁).2
        have h2 := (Finset.mem_filter.mp hp₂).2
        have hd : p₁.val / K = p₂.val / K := congrArg Fin.val hdiv
        exact Fin.ext (by
          have e1 := Nat.div_add_mod p₁.val K
          have e2 := Nat.div_add_mod p₂.val K
          dsimp only [K] at e1 e2 hd h1 h2 ⊢
          nlinarith)
      have hle := Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
      simpa using hle
    have hScard : S.card ≤ A.card * ((L - 1) / K + 1) := by
      calc S.card
        _ ≤ (A.biUnion (fun a => Finset.univ.filter (fun p : Fin L => p.val % K = a.val))).card :=
            Finset.card_le_card hSsub
        _ ≤ ∑ a ∈ A, (Finset.univ.filter (fun p : Fin L => p.val % K = a.val)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _a ∈ A, ((L - 1) / K + 1) := Finset.sum_le_sum fun a _ => hfiber a
        _ = A.card * ((L - 1) / K + 1) := by simp
    have hmul : A.card * ((L - 1) / K + 1) ≤ b * ((L - 1) / K + 1) :=
      Nat.mul_le_mul_right _ hAcard
    have harith : b * ((L - 1) / K + 1) ≤ L / 4 := by
      have hq : K * ((L - 1) / K) ≤ L - 1 := Nat.mul_div_le (L - 1) K
      have hq' : 8 * b * ((L - 1) / K) ≤ L - 1 := by simpa [K] using hq
      have h4 : 4 * (b * ((L - 1) / K + 1)) ≤ L := by
        have h1 : 4 * (b * ((L - 1) / K + 1)) = 4 * b * ((L - 1) / K) + 4 * b := by ring
        have h2 : 8 * b * ((L - 1) / K) = 2 * (4 * b * ((L - 1) / K)) := by ring
        omega
      omega
    exact le_trans hScard (le_trans hmul harith)
  · -- Case 2: L < 8 * b and 4 ≤ L. Group blocks into groups of size g_max = L / 4 ≥ 1.
    let g_max := L / 4
    have hgpos : 1 ≤ g_max := by dsimp only [g_max]; omega
    let G := (b + g_max - 1) / g_max
    have hGpos : 1 ≤ G := by
      have : g_max ≤ b + g_max - 1 := by omega
      exact (Nat.le_div_iff_mul_le hgpos).mpr (by omega)
    let K := G * L
    have hKle : K ≤ 21 * b := by
      have hGub : G ≤ b / g_max + 1 := by
        have hrem : g_max * (b / g_max) + b % g_max = b := Nat.div_add_mod b g_max
        have hmod : b % g_max < g_max := Nat.mod_lt b hgpos
        have hlt : b + g_max - 1 < (b / g_max + 2) * g_max := by
          have : (b / g_max + 2) * g_max = g_max * (b / g_max) + 2 * g_max := by ring
          omega
        have hdiv : G < b / g_max + 2 := (Nat.div_lt_iff_lt_mul hgpos).mpr hlt
        omega
      have hLub : L ≤ 7 * g_max := by dsimp only [g_max]; omega
      have hmul1 : K ≤ (b / g_max + 1) * (7 * g_max) := Nat.mul_le_mul hGub hLub
      have hdivb : (b / g_max) * g_max ≤ b := Nat.div_mul_le_self b g_max
      have hg_lt : g_max < 2 * b := by dsimp only [g_max]; omega
      nlinarith
    let V : Fin K → (Fin c → Bool) := fun a j =>
      decide (j.val < b * L ∧ (j.val / L) / g_max = a.val / L ∧ j.val % L = a.val % L)
    refine ⟨K, V, hKle, fun f₀ i s => ?_⟩
    let g := s.val / g_max
    have hglt : g < G := by
      have h1 : s.val ≤ b - 1 := by omega
      have h2 : g * g_max ≤ b - 1 := le_trans (Nat.div_mul_le_self s.val g_max) h1
      have h3 : (g + 1) * g_max ≤ b + g_max - 1 := by
        have : (g + 1) * g_max = g * g_max + g_max := by ring
        omega
      have h4 : g + 1 ≤ G := (Nat.le_div_iff_mul_le hgpos).mpr h3
      omega
    let Grp : Finset (Fin b) := Finset.univ.filter (fun s' : Fin b => s'.val / g_max = g)
    have hGrpCard : Grp.card ≤ g_max := by
      have hinj : Set.InjOn (fun s' : Fin b => (⟨s'.val % g_max, Nat.mod_lt _ hgpos⟩ : Fin g_max)) Grp := by
        intro s₁ hs₁ s₂ hs₂ hmod
        have h1 := (Finset.mem_filter.mp hs₁).2
        have h2 := (Finset.mem_filter.mp hs₂).2
        have hm' : s₁.val % g_max = s₂.val % g_max := congrArg Fin.val hmod
        exact Fin.ext (by
          have e1 := Nat.div_add_mod s₁.val g_max
          have e2 := Nat.div_add_mod s₂.val g_max
          nlinarith)
      have hle := Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
      simpa using hle
    let S := Finset.univ.filter fun p : Fin L =>
      ∀ a : Fin K,
        (∀ hj : s.val * L + p.val < c, V a ⟨s.val * L + p.val, hj⟩ = true →
          ∃ j : Fin c, blockMat f₀ i j = true ∧ V a j = true)
    have hSsub : S ⊆ Grp.image (fun s' : Fin b => f₀ (i, s')) := by
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      have halt : g * L + p.val < K := by
        have h1 : (g + 1) * L ≤ G * L := Nat.mul_le_mul_right L hglt
        dsimp only [K]
        nlinarith [p.isLt]
      let a : Fin K := ⟨g * L + p.val, halt⟩
      have hjlt : s.val * L + p.val < c := by
        have h1 : (s.val + 1) * L ≤ b * L := Nat.mul_le_mul_right L s.isLt
        nlinarith [p.isLt]
      have hjltbL : s.val * L + p.val < b * L := by
        have h1 : (s.val + 1) * L ≤ b * L := Nat.mul_le_mul_right L s.isLt
        nlinarith [p.isLt]
      have hVa : V a ⟨s.val * L + p.val, hjlt⟩ = true := by
        refine decide_eq_true ⟨hjltbL, ?_, ?_⟩
        · dsimp only [a]
          rw [mul_comm s.val L, Nat.mul_add_div hLpos, Nat.div_eq_of_lt p.isLt, add_zero,
              mul_comm g L, Nat.mul_add_div hLpos, Nat.div_eq_of_lt p.isLt, add_zero]
        · dsimp only [a]
          rw [mul_comm s.val L, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt,
              mul_comm g L, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]
      obtain ⟨j, hjM, hjV⟩ := hp' a hjlt hVa
      obtain ⟨hjb, hf0⟩ := blockMat_unique_true f₀ i j hjM
      obtain ⟨_, hgEq, hmEq⟩ := of_decide_eq_true hjV
      dsimp only [a] at hgEq hmEq
      rw [mul_comm g L, Nat.mul_add_div hLpos, Nat.div_eq_of_lt p.isLt, add_zero] at hgEq
      rw [mul_comm g L, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt] at hmEq
      refine Finset.mem_image.mpr ⟨⟨j.val / L, hjb⟩, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgEq⟩
      · exact Fin.ext (by rw [hf0, hmEq])
    exact le_trans (Finset.card_le_card hSsub) (le_trans Finset.card_image_le hGrpCard)

/-- State for deduplicating simulation across `K` adaptive `t`-probe queries. -/
private structure SimState (m c : ℕ) where
  fresh : List (Fin m × Fin c)
  curHist : List Bool

/-- Run `step` global probes (`0 .. K*t`) using an actual matrix `M`. -/
private def runReal {m c K : ℕ} (t : ℕ)
    (nextStep : Fin K → List Bool → Fin m × Fin c)
    (M : Matrix (Fin m) (Fin c) Bool) : ℕ → SimState m c
  | 0 => ⟨[], []⟩
  | s + 1 =>
    let st := runReal t nextStep M s
    if h : s < K * t then
      let a : Fin K := ⟨s / t, by
        have ht : 0 < t := by
          by_contra ht0
          have : t = 0 := by omega
          subst this; simp at h
        exact (Nat.div_lt_iff_lt_mul ht).mpr h⟩
      let h0 := if s % t = 0 then [] else st.curHist
      let coord := nextStep a h0
      let fresh' := if coord ∈ st.fresh then st.fresh else st.fresh ++ [coord]
      let bit := M coord.1 coord.2
      ⟨fresh', bit :: h0⟩
    else st

/-- Emulate `step` global probes (`0 .. K*t`) using ONLY the subset `K1 ⊆ Fin (K*t)` of fresh
probe indices whose matrix entry is `true`. -/
private def runEmu {m c K : ℕ} (t : ℕ)
    (nextStep : Fin K → List Bool → Fin m × Fin c)
    (K1 : Finset (Fin (K * t))) : ℕ → SimState m c
  | 0 => ⟨[], []⟩
  | s + 1 =>
    let st := runEmu t nextStep K1 s
    if h : s < K * t then
      let a : Fin K := ⟨s / t, by
        have ht : 0 < t := by
          by_contra ht0
          have : t = 0 := by omega
          subst this; simp at h
        exact (Nat.div_lt_iff_lt_mul ht).mpr h⟩
      let h0 := if s % t = 0 then [] else st.curHist
      let coord := nextStep a h0
      let idx := st.fresh.idxOf coord
      let fresh' := if coord ∈ st.fresh then st.fresh else st.fresh ++ [coord]
      let bit := if hidx : idx < K * t then decide (⟨idx, hidx⟩ ∈ K1) else false
      ⟨fresh', bit :: h0⟩
    else st

private lemma runReal_fresh_length_le {m c K : ℕ} (t : ℕ)
    (nextStep : Fin K → List Bool → Fin m × Fin c)
    (M : Matrix (Fin m) (Fin c) Bool) (s : ℕ) :
    (runReal t nextStep M s).fresh.length ≤ s := by
  induction s with
  | zero => simp [runReal]
  | succ s ih =>
    simp only [runReal]
    split_ifs <;> simp_all <;> omega

private lemma runReal_fresh_nodup {m c K : ℕ} (t : ℕ)
    (nextStep : Fin K → List Bool → Fin m × Fin c)
    (M : Matrix (Fin m) (Fin c) Bool) (s : ℕ) :
    (runReal t nextStep M s).fresh.Nodup := by
  induction s with
  | zero => simp [runReal]
  | succ s ih =>
    simp only [runReal]
    by_cases h1 : s < K * t
    · simp only [dif_pos h1]
      set st := runReal t nextStep M s
      set a : Fin K := ⟨s / t, (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero fun ht0 => by simp [ht0] at h1)).mpr h1⟩
      set coord := nextStep a (if s % t = 0 then [] else st.curHist)
      by_cases h2 : coord ∈ st.fresh
      · simp only [if_pos h2]; exact ih
      · simp only [if_neg h2]
        exact List.nodup_append.mpr ⟨ih, List.nodup_singleton _, fun x hx y hy => by
          rw [List.mem_singleton.mp hy]
          intro hEq; exact h2 (hEq ▸ hx)⟩
    · simp only [dif_neg h1]; exact ih

private lemma runReal_fresh_prefix {m c K : ℕ} (t : ℕ)
    (nextStep : Fin K → List Bool → Fin m × Fin c)
    (M : Matrix (Fin m) (Fin c) Bool) {s₁ s₂ : ℕ} (hle : s₁ ≤ s₂) :
    (runReal t nextStep M s₁).fresh <+: (runReal t nextStep M s₂).fresh := by
  induction hle with
  | refl => exact List.prefix_refl _
  | @step k _ ih =>
    refine ih.trans ?_
    simp only [runReal]
    by_cases h1 : k < K * t
    · simp only [dif_pos h1]
      set a : Fin K := ⟨k / t, (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero fun ht0 => by simp [ht0] at h1)).mpr h1⟩
      by_cases h2 : nextStep a (if k % t = 0 then [] else (runReal t nextStep M k).curHist) ∈
          (runReal t nextStep M k).fresh
      · simp only [if_pos h2]; exact List.prefix_refl _
      · simp only [if_neg h2]; exact List.prefix_append _ _
    · simp only [dif_neg h1]; exact List.prefix_refl _

private lemma runReal_hist_pos {m c K : ℕ} (t : ℕ)
    (nextStep : Fin K → List Bool → Fin m × Fin c)
    (M : Matrix (Fin m) (Fin c) Bool) (a : Fin K) (j : ℕ) (hj : j < t) :
    (runReal t nextStep M (a.val * t + j + 1)).curHist =
      (fun hist : List Bool => M (nextStep a hist).1 (nextStep a hist).2 :: hist)^[j + 1] [] := by
  induction j with
  | zero =>
    have ht : 0 < t := by omega
    have hlt : a.val * t < K * t := Nat.mul_lt_mul_of_pos_right a.isLt ht
    simp only [runReal, dif_pos hlt]
    have hdiv : (a.val * t) / t = a.val := Nat.mul_div_cancel a.val ht
    have hmod : (a.val * t) % t = 0 := Nat.mul_mod_left a.val t
    have ha : (⟨(a.val * t) / t, (Nat.div_lt_iff_lt_mul ht).mpr hlt⟩ : Fin K) = a := Fin.ext hdiv
    simp [hmod, ha]
  | succ j ih =>
    have ht : 0 < t := by omega
    have hlt : a.val * t + (j + 1) < K * t := by
      have h1 : (a.val + 1) * t ≤ K * t := Nat.mul_le_mul_right t a.isLt
      nlinarith
    have hprev := ih (by omega)
    have hstep : runReal t nextStep M (a.val * t + (j + 1) + 1) =
        let st := runReal t nextStep M (a.val * t + (j + 1))
        let a' : Fin K := ⟨(a.val * t + (j + 1)) / t, (Nat.div_lt_iff_lt_mul ht).mpr hlt⟩
        let h0 := if (a.val * t + (j + 1)) % t = 0 then [] else st.curHist
        let coord := nextStep a' h0
        let fresh' := if coord ∈ st.fresh then st.fresh else st.fresh ++ [coord]
        ⟨fresh', M coord.1 coord.2 :: h0⟩ := by
      rw [runReal, dif_pos hlt]
    rw [hstep]
    dsimp only
    have hdiv : (a.val * t + (j + 1)) / t = a.val := by
      rw [mul_comm a.val t, Nat.mul_add_div ht, Nat.div_eq_of_lt hj, add_zero]
    have hmod : (a.val * t + (j + 1)) % t ≠ 0 := by
      rw [mul_comm a.val t, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
      omega
    have ha : (⟨(a.val * t + (j + 1)) / t, (Nat.div_lt_iff_lt_mul ht).mpr hlt⟩ : Fin K) = a := Fin.ext hdiv
    simp only [if_neg hmod, ha]
    have hprev' : (runReal t nextStep M (a.val * t + (j + 1))).curHist =
        (fun hist : List Bool => M (nextStep a hist).1 (nextStep a hist).2 :: hist)^[j + 1] [] := by
      simpa [Nat.add_assoc] using hprev
    rw [hprev']
    exact (Function.iterate_succ_apply' (fun hist : List Bool => M (nextStep a hist).1 (nextStep a hist).2 :: hist) (j + 1) []).symm

private def trueFreshSet {m c K : ℕ} (t : ℕ)
    (nextStep : Fin K → List Bool → Fin m × Fin c)
    (M : Matrix (Fin m) (Fin c) Bool) : Finset (Fin (K * t)) :=
  let fl := (runReal t nextStep M (K * t)).fresh
  Finset.univ.filter fun idx =>
    if h : idx.val < fl.length then
      let p := fl[idx.val]'h
      M p.1 p.2 = true
    else false

private lemma list_idxOf_of_not_mem {α : Type*} [BEq α] [LawfulBEq α] (l : List α) (x : α)
    (hx : x ∉ l) : l.idxOf x = l.length := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hne : hd ≠ x := fun h => hx (by simp [h])
    have htl : x ∉ tl := fun h => hx (List.mem_cons_of_mem _ h)
    simp [List.idxOf_cons, beq_eq_false_iff_ne.mpr hne, ih htl]

private lemma runEmu_eq_runReal {m c K : ℕ} (t : ℕ)
    (nextStep : Fin K → List Bool → Fin m × Fin c)
    (M : Matrix (Fin m) (Fin c) Bool) (s : ℕ) (hs : s ≤ K * t) :
    runEmu t nextStep (trueFreshSet t nextStep M) s = runReal t nextStep M s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have hlt : s < K * t := by omega
    have hprev := ih (by omega)
    simp only [runEmu, runReal, dif_pos hlt, hprev]
    set st := runReal t nextStep M s
    set a : Fin K := ⟨s / t, (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero fun ht0 => by simp [ht0] at hlt)).mpr hlt⟩
    set h0 := if s % t = 0 then [] else st.curHist
    set coord := nextStep a h0
    set fl := (runReal t nextStep M (K * t)).fresh
    set fresh' := if coord ∈ st.fresh then st.fresh else st.fresh ++ [coord]
    have hpref : fresh' <+: fl := by
      have hstep_eq : (runReal t nextStep M (s + 1)).fresh = fresh' := by
        simp [runReal, dif_pos hlt, st, a, h0, coord, fresh']
      rw [← hstep_eq]
      exact runReal_fresh_prefix t nextStep M hs
    have hidx_lt_fresh' : st.fresh.idxOf coord < fresh'.length := by
      dsimp only [fresh']
      split_ifs with hmem
      · exact List.idxOf_lt_length_iff.mpr hmem
      · rw [list_idxOf_of_not_mem st.fresh coord hmem, List.length_append, List.length_singleton]
        omega
    have hget_fresh' : fresh'[st.fresh.idxOf coord]'hidx_lt_fresh' = coord := by
      dsimp only [fresh']
      split_ifs with hmem
      · exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hmem)
      · have hlen : st.fresh.idxOf coord = st.fresh.length := list_idxOf_of_not_mem st.fresh coord hmem
        simp [hlen]
    have hidx_lt_fl : st.fresh.idxOf coord < fl.length :=
      lt_of_lt_of_le hidx_lt_fresh' hpref.length_le
    have hfl_len : fl.length ≤ K * t := runReal_fresh_length_le t nextStep M (K * t)
    have hidx_lt_Q : st.fresh.idxOf coord < K * t := lt_of_lt_of_le hidx_lt_fl hfl_len
    have hget_fl : fl[st.fresh.idxOf coord]'hidx_lt_fl = coord := by
      calc fl[st.fresh.idxOf coord]'hidx_lt_fl
        _ = fresh'[st.fresh.idxOf coord]'hidx_lt_fresh' := (List.IsPrefix.getElem hpref hidx_lt_fresh').symm
        _ = coord := hget_fresh'
    have hbit : (if hidx : st.fresh.idxOf coord < K * t then
        decide (⟨st.fresh.idxOf coord, hidx⟩ ∈ trueFreshSet t nextStep M) else false) =
        M coord.1 coord.2 := by
      rw [dif_pos hidx_lt_Q]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, trueFreshSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [dif_pos hidx_lt_fl, hget_fl]
    rw [hbit]

/-- **PPL 108 / PPL 111 Sharp Log-Free Succinct Adaptive Cell-Probe Lower Bound (Boolean `Mv`):**
Generalizing Chakraborty–Kamma–Larsen (STOC 2018) from square `n × n` to arbitrary rectangular
`m × c` Boolean matrices (covering both square `Mv`/`OMv` with `m = c = n` and rectangular
`v`-Hinted `Mv` with `m = n, c = n^τ`):
If a succinct data structure stores `r` bits of redundancy (`enc : Matrix → Fin (2 ^ r)`) and an
adaptive deterministic `t`-bit-probe query algorithm computes Boolean `Mv` for all `M` and `v`,
then whenever `4 * (r / m + 1) ≤ c`,
`m * c ≤ 210 * t * (r / m + 1)`. -/
theorem ppl108_boolean_mv_succinct_cell_probe_lower_bound (m c r t : ℕ)
    (hm : 1 ≤ m) (hc : 4 * (r / m + 1) ≤ c)
    (enc : Matrix (Fin m) (Fin c) Bool → Fin (2 ^ r))
    (next : Fin (2 ^ r) → (Fin c → Bool) → List Bool → Fin m × Fin c)
    (out : Fin (2 ^ r) → (Fin c → Bool) → List Bool → (Fin m → Bool))
    (hcorr : ∀ (M : Matrix (Fin m) (Fin c) Bool) (v : Fin c → Bool) (i : Fin m),
      out (enc M) v ((fun hist : List Bool =>
        M (next (enc M) v hist).1 (next (enc M) v hist).2 :: hist)^[t] []) i = true ↔
        ∃ j : Fin c, M i j = true ∧ v j = true) :
    m * c ≤ 210 * t * (r / m + 1) := by
  let b := r / m + 1
  have hb : 1 ≤ b := Nat.succ_le_succ (Nat.zero_le _)
  have hmb_gt_r : r < m * b := by
    dsimp only [b]
    have hdiv := Nat.div_add_mod r m
    have hmod := Nat.mod_lt r (by omega : 0 < m)
    nlinarith
  let L := c / b
  have hL4 : 4 ≤ L := (Nat.le_div_iff_mul_le hb).mpr hc
  have hLpos : 0 < L := by omega
  have hbL : b * L ≤ c := Nat.mul_div_le c b
  -- Step 1: Pigeonhole on enc ∘ blockMat to get a large fiber F with constant redundancy ρ₀.
  have hcard_dom : Fintype.card (Fin m × Fin b → Fin L) = L ^ (m * b) := by
    simp [Fintype.card_pi, Finset.prod_const, Fintype.card_prod, Fintype.card_fin]
  have hsum_fib : ∑ ρ : Fin (2 ^ r),
      (Finset.univ.filter fun f : Fin m × Fin b → Fin L => enc (blockMat f) = ρ).card =
      L ^ (m * b) := by
    rw [← hcard_dom, ← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)).symm
  have hnonempty_R : (Finset.univ : Finset (Fin (2 ^ r))).Nonempty := by
    refine ⟨⟨0, Nat.two_pow_pos r⟩, Finset.mem_univ _⟩
  obtain ⟨ρ₀, _, hρ₀_max⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (2 ^ r)))
    (fun ρ => (Finset.univ.filter fun f : Fin m × Fin b → Fin L => enc (blockMat f) = ρ).card)
    hnonempty_R
  let F := Finset.univ.filter fun f : Fin m × Fin b → Fin L => enc (blockMat f) = ρ₀
  have hF_lower : L ^ (m * b) ≤ F.card * 2 ^ r := by
    calc L ^ (m * b)
      _ = ∑ ρ : Fin (2 ^ r),
            (Finset.univ.filter fun f : Fin m × Fin b → Fin L => enc (blockMat f) = ρ).card :=
          hsum_fib.symm
      _ ≤ ∑ _ρ : Fin (2 ^ r), F.card := Finset.sum_le_sum fun ρ _ => hρ₀_max ρ (Finset.mem_univ _)
      _ = 2 ^ r * F.card := by simp
      _ = F.card * 2 ^ r := mul_comm _ _
  -- Step 2: Handle t = 0 cleanly (impossible since 4^(m*b) > 2^r, wait: L ≥ 4 and K queries!).
  -- Actually let's handle t = 0 directly first, or let the unified proof handle t ≥ 1!
  by_cases ht0 : t = 0
  · exfalso
    subst ht0
    obtain ⟨K, V, _, hV⟩ := exists_boolean_query_family (m := m) hb hL4 hbL
    have hF_ne : F.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty, Finset.card_empty, zero_mul] at hF_lower
      exact absurd hF_lower (not_le.mpr (pow_pos hLpos _))
    obtain ⟨f₀, hf₀⟩ := hF_ne
    have hf₀_enc : enc (blockMat f₀) = ρ₀ := (Finset.mem_filter.mp hf₀).2
    -- Every f ∈ F has the same empty history, hence same responses on all V a!
    let allow : Fin m × Fin b → Finset (Fin L) := fun x =>
      Finset.univ.filter fun p : Fin L =>
        ∀ a : Fin K, ∀ hj : x.2.val * L + p.val < c, V a ⟨x.2.val * L + p.val, hj⟩ = true →
          ∃ j : Fin c, blockMat f₀ x.1 j = true ∧ V a j = true
    have hFsub : F ⊆ Fintype.piFinset allow := by
      intro f hf
      have hf_enc : enc (blockMat f) = ρ₀ := (Finset.mem_filter.mp hf).2
      rw [Fintype.mem_piFinset]
      intro ⟨i, s⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a hj hVa => ?_⟩
      have h1 := hcorr (blockMat f) (V a) i
      have h2 := hcorr (blockMat f₀) (V a) i
      rw [hf_enc] at h1; rw [hf₀_enc] at h2
      simp only [Function.iterate_zero, id_eq] at h1 h2
      have h1' : ∃ j : Fin c, blockMat f i j = true ∧ V a j = true := by
        refine ⟨⟨s.val * L + (f (i, s)).val, hj⟩, ?_, hVa⟩
        rw [blockMat_at hLpos hbL]
        simp
      exact h2.mp (h1.mpr h1')
    have hF_upper : F.card ≤ (L / 4) ^ (m * b) := by
      calc F.card
        _ ≤ (Fintype.piFinset allow).card := Finset.card_le_card hFsub
        _ = ∏ x : Fin m × Fin b, (allow x).card := Fintype.card_piFinset allow
        _ ≤ ∏ _x : Fin m × Fin b, (L / 4) := Finset.prod_le_prod' fun x _ => hV f₀ x.1 x.2
        _ = (L / 4) ^ (m * b) := by simp [Fintype.card_prod]
    have h4L : 4 * (L / 4) ≤ L := Nat.mul_div_le L 4
    have hpow : (L / 4) ^ (m * b) * 4 ^ (m * b) ≤ L ^ (m * b) := by
      rw [← mul_pow, mul_comm]
      exact Nat.pow_le_pow_left h4L _
    have h2r : 2 ^ r < 4 ^ (m * b) := by
      have : 4 ^ (m * b) = 2 ^ (2 * (m * b)) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      rw [this]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    have hFpos : 0 < F.card := Finset.card_pos.mpr ⟨f₀, hf₀⟩
    have hcontra : F.card * 2 ^ r < L ^ (m * b) := by
      calc F.card * 2 ^ r
        _ < F.card * 4 ^ (m * b) := Nat.mul_lt_mul_of_pos_left h2r hFpos
        _ ≤ (L / 4) ^ (m * b) * 4 ^ (m * b) := Nat.mul_le_mul_right _ hF_upper
        _ ≤ L ^ (m * b) := hpow
    omega
  -- Step 3: Main case t ≥ 1.
  have htpos : 1 ≤ t := by omega
  obtain ⟨K, V, hKle, hV⟩ := exists_boolean_query_family (m := m) hb hL4 hbL
  let Q := K * t
  let nextStep : Fin K → List Bool → Fin m × Fin c := fun a hist => next ρ₀ (V a) hist
  let key : (Fin m × Fin b → Fin L) → Finset (Fin Q) :=
    fun f => trueFreshSet t nextStep (blockMat f)
  -- Bound each fiber F_{K1} = { f ∈ F | key f = K1 }
  have hfiber_bound : ∀ K1 ∈ (Finset.univ : Finset (Fin Q)).powerset,
      ((F.filter fun f => key f = K1).card : ℝ) ≤
        ((L : ℝ) / 4) ^ (m * b) * (4 / (L : ℝ)) ^ K1.card := by
    intro K1 _
    set FK := F.filter fun f => key f = K1
    by_cases hne : FK.Nonempty
    · obtain ⟨f₀, hf₀⟩ := hne
      have hf₀F : f₀ ∈ F := (Finset.mem_filter.mp hf₀).1
      have hf₀_enc : enc (blockMat f₀) = ρ₀ := (Finset.mem_filter.mp hf₀F).2
      have hf₀_key : key f₀ = K1 := (Finset.mem_filter.mp hf₀).2
      let fl₀ := (runReal t nextStep (blockMat f₀) Q).fresh
      have hfl₀_nodup : fl₀.Nodup := runReal_fresh_nodup t nextStep (blockMat f₀) Q
      -- Every idx ∈ K1 points to a valid coordinate in fl₀ where blockMat f₀ is true.
      have hidx_mem : ∀ idx ∈ K1,
          ∃ (h1 : idx.val < fl₀.length),
            let p := fl₀[idx.val]'h1
            ∃ (h2 : p.2.val / L < b), (f₀ (p.1, ⟨p.2.val / L, h2⟩)).val = p.2.val % L := by
        intro idx hidx
        rw [← hf₀_key] at hidx
        dsimp only [key, trueFreshSet] at hidx
        have hpred := (Finset.mem_filter.mp hidx).2
        split_ifs at hpred with h1
        · obtain ⟨h2, hval⟩ := blockMat_unique_true f₀ _ _ hpred
          exact ⟨h1, h2, hval⟩
      -- Build the pinned set of blocks Pinned ⊆ Fin m × Fin b of cardinality K1.card.
      let pinMap : Fin Q → Option (Fin m × Fin b) := fun idx =>
        if h1 : idx.val < fl₀.length then
          let p := fl₀[idx.val]'h1
          if h2 : p.2.val / L < b then some (p.1, ⟨p.2.val / L, h2⟩) else none
        else none
      let Pinned : Finset (Fin m × Fin b) :=
        Finset.univ.filter fun x => ∃ idx ∈ K1, pinMap idx = some x
      have hpin_card : Pinned.card = K1.card := by
        have hbij : ∃ g : { idx // idx ∈ K1 } → { x // x ∈ Pinned }, Function.Bijective g := by
          let g : { idx // idx ∈ K1 } → { x // x ∈ Pinned } := fun ⟨idx, hidx⟩ =>
            let h := hidx_mem idx hidx
            let h1 := h.choose
            let h2 := h.choose_spec.choose
            let p := fl₀[idx.val]'h1
            ⟨(p.1, ⟨p.2.val / L, h2⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              ⟨idx, hidx, by simp [pinMap, dif_pos h1, dif_pos h2, p]⟩⟩⟩
          refine ⟨g, ?_, ?_⟩
          · -- Injective: distinct idx₁, idx₂ in K1 give distinct entries of fl₀ (Nodup),
            -- hence distinct blocks since blockMat f₀ has at most one `true` per block!
            rintro ⟨idx₁, h₁⟩ ⟨idx₂, h₂⟩ hEq
            have hEq' : (g ⟨idx₁, h₁⟩).1 = (g ⟨idx₂, h₂⟩).1 := congrArg Subtype.val hEq
            dsimp only [g] at hEq'
            set h1a := (hidx_mem idx₁ h₁).choose
            set h2a := (hidx_mem idx₁ h₁).choose_spec.choose
            have hvala := (hidx_mem idx₁ h₁).choose_spec.choose_spec
            set h1b := (hidx_mem idx₂ h₂).choose
            set h2b := (hidx_mem idx₂ h₂).choose_spec.choose
            have hvalb := (hidx_mem idx₂ h₂).choose_spec.choose_spec
            have hrow : (fl₀[idx₁.val]'h1a).1 = (fl₀[idx₂.val]'h1b).1 :=
              congrArg (fun x : Fin m × Fin b => x.1) hEq'
            have hblk : (fl₀[idx₁.val]'h1a).2.val / L = (fl₀[idx₂.val]'h1b).2.val / L :=
              congrArg (fun x : Fin m × Fin b => x.2.val) hEq'
            have hmod : (fl₀[idx₁.val]'h1a).2.val % L = (fl₀[idx₂.val]'h1b).2.val % L := by
              rw [← hvala, ← hvalb, hEq']
            have hcol : (fl₀[idx₁.val]'h1a).2 = (fl₀[idx₂.val]'h1b).2 := Fin.ext (by
              have e1 := Nat.div_add_mod (fl₀[idx₁.val]'h1a).2.val L
              have e2 := Nat.div_add_mod (fl₀[idx₂.val]'h1b).2.val L
              nlinarith)
            have hpEq : fl₀[idx₁.val]'h1a = fl₀[idx₂.val]'h1b := Prod.ext hrow hcol
            have hidxEq : idx₁.val = idx₂.val :=
              (List.Nodup.getElem_inj_iff hfl₀_nodup).mp hpEq
            exact Subtype.ext (Fin.ext hidxEq)
          · -- Surjective
            rintro ⟨x, hx⟩
            obtain ⟨idx, hidx, hpm⟩ := (Finset.mem_filter.mp hx).2
            refine ⟨⟨idx, hidx⟩, Subtype.ext ?_⟩
            dsimp only [g]
            set h1 := (hidx_mem idx hidx).choose
            set h2 := (hidx_mem idx hidx).choose_spec.choose
            simp only [pinMap, dif_pos h1, dif_pos h2] at hpm
            exact Option.some.inj hpm
        obtain ⟨g, hbij⟩ := hbij
        have hc1 := Fintype.card_of_bijective hbij
        simpa [Fintype.card_coe] using hc1.symm
      have hK1_le_mb : K1.card ≤ m * b := by
        rw [← hpin_card]
        calc Pinned.card ≤ Fintype.card (Fin m × Fin b) := Finset.card_le_univ Pinned
          _ = m * b := by simp [Fintype.card_prod]
      -- For every f ∈ FK: (1) on Pinned, f x = f₀ x; (2) on all x, f x ∈ allow x.
      let allow : Fin m × Fin b → Finset (Fin L) := fun x =>
        if x ∈ Pinned then {f₀ x}
        else Finset.univ.filter fun p : Fin L =>
          ∀ a : Fin K, ∀ hj : x.2.val * L + p.val < c, V a ⟨x.2.val * L + p.val, hj⟩ = true →
            ∃ j : Fin c, blockMat f₀ x.1 j = true ∧ V a j = true
      have hFK_sub : FK ⊆ Fintype.piFinset allow := by
        intro f hf
        have hfF : f ∈ F := (Finset.mem_filter.mp hf).1
        have hf_enc : enc (blockMat f) = ρ₀ := (Finset.mem_filter.mp hfF).2
        have hf_key : key f = K1 := (Finset.mem_filter.mp hf).2
        -- Both f and f₀ agree with runEmu K1 at every step s ≤ Q!
        have hrun_eq : ∀ s ≤ Q, runReal t nextStep (blockMat f) s = runReal t nextStep (blockMat f₀) s := by
          intro s hs
          rw [← runEmu_eq_runReal t nextStep (blockMat f) s hs,
              ← runEmu_eq_runReal t nextStep (blockMat f₀) s hs]
          change runEmu t nextStep (key f) s = runEmu t nextStep (key f₀) s
          rw [hf_key, hf₀_key]
        rw [Fintype.mem_piFinset]
        intro ⟨i, s⟩
        dsimp only [allow]
        split_ifs with hpin
        · -- Pinned block: f (i, s) = f₀ (i, s)
          rw [Finset.mem_singleton]
          obtain ⟨idx, hidx, hpm⟩ := (Finset.mem_filter.mp hpin).2
          set h1 := (hidx_mem idx hidx).choose
          set h2 := (hidx_mem idx hidx).choose_spec.choose
          have hval0 := (hidx_mem idx hidx).choose_spec.choose_spec
          simp only [pinMap, dif_pos h1, dif_pos h2] at hpm
          have hxEq := Option.some.inj hpm
          have hidx_f : idx ∈ trueFreshSet t nextStep (blockMat f) := by
            change idx ∈ key f; rw [hf_key]; exact hidx
          have hfl_eq : (runReal t nextStep (blockMat f) Q).fresh = fl₀ :=
            congrArg SimState.fresh (hrun_eq Q le_rfl)
          dsimp only [trueFreshSet] at hidx_f
          have hpred := (Finset.mem_filter.mp hidx_f).2
          rw [hfl_eq, dif_pos h1] at hpred
          obtain ⟨h2', hvalf⟩ := blockMat_unique_true f _ _ hpred
          have hp_eq : ((fl₀[idx.val]'h1).1, (⟨(fl₀[idx.val]'h1).2.val / L, h2⟩ : Fin b)) = (i, s) := hxEq
          have hp_eq' : ((fl₀[idx.val]'h1).1, (⟨(fl₀[idx.val]'h1).2.val / L, h2'⟩ : Fin b)) = (i, s) := hxEq
          rw [hp_eq] at hval0
          rw [hp_eq'] at hvalf
          exact Fin.ext (hvalf.trans hval0.symm)
        · -- Unpinned block: f (i, s) satisfies all query responses of f₀!
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a hj hVa => ?_⟩
          have h1 := hcorr (blockMat f) (V a) i
          have h2 := hcorr (blockMat f₀) (V a) i
          rw [hf_enc] at h1; rw [hf₀_enc] at h2
          -- Histories at step a.val * t + (t - 1) + 1 = (a.val + 1) * t agree!
          have hstep_le : a.val * t + (t - 1) + 1 ≤ Q := by
            have h1' : (a.val + 1) * t ≤ K * t := Nat.mul_le_mul_right t a.isLt
            have h2' : a.val * t + (t - 1) + 1 = (a.val + 1) * t := by
              rw [Nat.add_mul, one_mul]; omega
            dsimp only [Q]; omega
          have hhist_f := runReal_hist_pos t nextStep (blockMat f) a (t - 1) (by omega)
          have hhist_f0 := runReal_hist_pos t nextStep (blockMat f₀) a (t - 1) (by omega)
          have hhist_eq : (runReal t nextStep (blockMat f) (a.val * t + (t - 1) + 1)).curHist =
              (runReal t nextStep (blockMat f₀) (a.val * t + (t - 1) + 1)).curHist :=
            congrArg SimState.curHist (hrun_eq _ hstep_le)
          rw [hhist_f, hhist_f0, show t - 1 + 1 = t by omega] at hhist_eq
          dsimp only [nextStep] at hhist_eq
          rw [hhist_eq] at h1
          have h1' : ∃ j : Fin c, blockMat f i j = true ∧ V a j = true := by
            refine ⟨⟨s.val * L + (f (i, s)).val, hj⟩, ?_, hVa⟩
            rw [blockMat_at hLpos hbL]
            simp
          exact h2.mp (h1.mpr h1')
      have hFK_card_nat : FK.card ≤ (L / 4) ^ (m * b - K1.card) := by
        calc FK.card
          _ ≤ (Fintype.piFinset allow).card := Finset.card_le_card hFK_sub
          _ = ∏ x : Fin m × Fin b, (allow x).card := Fintype.card_piFinset allow
          _ ≤ ∏ x : Fin m × Fin b, (if x ∈ Pinned then 1 else L / 4) := by
              refine Finset.prod_le_prod' fun x _ => ?_
              dsimp only [allow]
              split_ifs
              · simp
              · exact hV f₀ x.1 x.2
          _ = (∏ _x ∈ Pinned, 1) * (∏ _x ∈ Finset.univ \ Pinned, (L / 4)) := by
              rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ Pinned)]
              congr 1
              · refine Finset.prod_congr (by ext x; simp) (fun x hx => ?_)
                have hx' : x ∈ Pinned := by simpa using hx
                simp [hx']
              · refine Finset.prod_congr (by ext x; simp) (fun x hx => ?_)
                have hx' : x ∉ Pinned := by simpa using hx
                simp [hx']
          _ = (L / 4) ^ (m * b - K1.card) := by
              rw [Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ _),
                Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hpin_card]
      -- Convert to ℝ: (L / 4) ^ (m*b - K1.card) ≤ (L/4 : ℝ)^(m*b) * (4/L : ℝ)^K1.card
      have hL_real_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
      have hdiv4 : ((L / 4 : ℕ) : ℝ) ≤ (L : ℝ) / 4 := by
        have h4 : (4 * (L / 4) : ℕ) ≤ L := Nat.mul_div_le L 4
        have h4r : (4 : ℝ) * ((L / 4 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast h4
        linarith
      calc (FK.card : ℝ)
        _ ≤ (((L / 4 : ℕ) : ℝ)) ^ (m * b - K1.card) := by exact_mod_cast hFK_card_nat
        _ ≤ ((L : ℝ) / 4) ^ (m * b - K1.card) := pow_le_pow_left₀ (by positivity) hdiv4 _
        _ = ((L : ℝ) / 4) ^ (m * b) * (4 / (L : ℝ)) ^ K1.card := by
            have hne0 : ((L : ℝ) / 4) ≠ 0 := by positivity
            have hsplit : m * b = (m * b - K1.card) + K1.card := (Nat.sub_add_cancel hK1_le_mb).symm
            conv_rhs => rw [hsplit, pow_add]
            rw [mul_assoc, ← mul_pow]
            have hinv : ((L : ℝ) / 4) * (4 / (L : ℝ)) = 1 := by field_simp
            rw [hinv, one_pow, mul_one]
    · -- Empty fiber: 0 ≤ rhs
      have hemp : FK = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [hemp, Finset.card_empty, Nat.cast_zero]
      positivity
  -- Step 4: Sum over all K1 ∈ powerset univ and apply binomial + exponential bound!
  have hF_sum : (F.card : ℝ) = ∑ K1 ∈ (Finset.univ : Finset (Fin Q)).powerset,
      ((F.filter fun f => key f = K1).card : ℝ) := by
    have hnat : F.card = ∑ K1 ∈ (Finset.univ : Finset (Fin Q)).powerset,
        (F.filter fun f => key f = K1).card :=
      Finset.card_eq_sum_card_fiberwise (fun f _ => Finset.mem_powerset.mpr (Finset.subset_univ _))
    exact_mod_cast hnat
  have hF_real_ub : (F.card : ℝ) ≤ ((L : ℝ) / 4) ^ (m * b) * (1 + 4 / (L : ℝ)) ^ Q := by
    calc (F.card : ℝ)
      _ = ∑ K1 ∈ (Finset.univ : Finset (Fin Q)).powerset,
            ((F.filter fun f => key f = K1).card : ℝ) := hF_sum
      _ ≤ ∑ K1 ∈ (Finset.univ : Finset (Fin Q)).powerset,
            ((L : ℝ) / 4) ^ (m * b) * (4 / (L : ℝ)) ^ K1.card :=
          Finset.sum_le_sum hfiber_bound
      _ = ((L : ℝ) / 4) ^ (m * b) *
            ∑ K1 ∈ (Finset.univ : Finset (Fin Q)).powerset, (4 / (L : ℝ)) ^ K1.card := by
          rw [← Finset.mul_sum]
      _ = ((L : ℝ) / 4) ^ (m * b) * (1 + 4 / (L : ℝ)) ^ Q := by
          rw [powerset_sum_pow, Fintype.card_fin]
  -- Combine hF_lower and hF_real_ub: 2 ^ (m * b) ≤ (1 + 4 / L) ^ Q ≤ exp (4 * Q / L)
  have hL_real_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have h2pow_le : (2 : ℝ) ^ (m * b) ≤ (1 + 4 / (L : ℝ)) ^ Q := by
    have hFl : (L : ℝ) ^ (m * b) ≤ (F.card : ℝ) * (2 : ℝ) ^ r := by exact_mod_cast hF_lower
    have h2r_le : (2 : ℝ) ^ r ≤ (2 : ℝ) ^ (m * b) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) (le_of_lt hmb_gt_r)
    have hcomb : (L : ℝ) ^ (m * b) ≤
        ((L : ℝ) / 4) ^ (m * b) * (1 + 4 / (L : ℝ)) ^ Q * (2 : ℝ) ^ (m * b) := by
      calc (L : ℝ) ^ (m * b)
        _ ≤ (F.card : ℝ) * (2 : ℝ) ^ r := hFl
        _ ≤ (F.card : ℝ) * (2 : ℝ) ^ (m * b) := mul_le_mul_of_nonneg_left h2r_le (by positivity)
        _ ≤ (((L : ℝ) / 4) ^ (m * b) * (1 + 4 / (L : ℝ)) ^ Q) * (2 : ℝ) ^ (m * b) :=
            mul_le_mul_of_nonneg_right hF_real_ub (by positivity)
    have hdiv_pow : ((L : ℝ) / 4) ^ (m * b) = (L : ℝ) ^ (m * b) / (4 : ℝ) ^ (m * b) :=
      div_pow _ _ _
    have h4_eq : (4 : ℝ) ^ (m * b) = (2 : ℝ) ^ (m * b) * (2 : ℝ) ^ (m * b) := by
      rw [← mul_pow]; norm_num
    rw [hdiv_pow, h4_eq] at hcomb
    have hLpow_pos : (0 : ℝ) < (L : ℝ) ^ (m * b) := by positivity
    have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (m * b) := by positivity
    have hsimp : (L : ℝ) ^ (m * b) / ((2 : ℝ) ^ (m * b) * (2 : ℝ) ^ (m * b)) *
        (1 + 4 / (L : ℝ)) ^ Q * (2 : ℝ) ^ (m * b) =
        (L : ℝ) ^ (m * b) * ((1 + 4 / (L : ℝ)) ^ Q / (2 : ℝ) ^ (m * b)) := by
      field_simp
    rw [hsimp] at hcomb
    have h1le : (1 : ℝ) ≤ (1 + 4 / (L : ℝ)) ^ Q / (2 : ℝ) ^ (m * b) := by
      nlinarith
    exact (one_le_div h2pow_pos).mp h1le
  have hexp_l : Real.exp (((m * b : ℕ) : ℝ) / 2) ≤ (2 : ℝ) ^ (m * b) := by
    have hrew : Real.exp (((m * b : ℕ) : ℝ) / 2) = (Real.exp ((1 : ℝ) / 2)) ^ (m * b) := by
      rw [← Real.exp_nat_mul]
      congr 1; ring
    rw [hrew]
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) exp_half_le_two (m * b)
  have hexp_r : (1 + 4 / (L : ℝ)) ^ Q ≤ Real.exp (4 * (Q : ℝ) / (L : ℝ)) := by
    have h1 : 1 + 4 / (L : ℝ) ≤ Real.exp (4 / (L : ℝ)) := by
      linarith [Real.add_one_le_exp (4 / (L : ℝ))]
    calc (1 + 4 / (L : ℝ)) ^ Q
      _ ≤ (Real.exp (4 / (L : ℝ))) ^ Q := pow_le_pow_left₀ (by positivity) h1 Q
      _ = Real.exp ((Q : ℝ) * (4 / (L : ℝ))) := (Real.exp_nat_mul _ Q).symm
      _ = Real.exp (4 * (Q : ℝ) / (L : ℝ)) := by congr 1; ring
  have hexp_both : ((m * b : ℕ) : ℝ) / 2 ≤ 4 * (Q : ℝ) / (L : ℝ) :=
    Real.exp_le_exp.mp (le_trans hexp_l (le_trans h2pow_le hexp_r))
  -- Cancel b > 0 and clear denominators: m * L ≤ 168 * t, hence m * c ≤ 210 * t * b!
  have hQ_le_real : (Q : ℝ) ≤ 21 * (b : ℝ) * (t : ℝ) := by
    have : Q ≤ 21 * b * t := Nat.mul_le_mul_right t hKle
    exact_mod_cast this
  have hb_real_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hmL_real : (m : ℝ) * (L : ℝ) ≤ 168 * (t : ℝ) := by
    have h1 : ((m : ℝ) * (b : ℝ)) * (L : ℝ) ≤ 8 * (Q : ℝ) := by
      have h2 : ((m * b : ℕ) : ℝ) / 2 * (L : ℝ) ≤ 4 * (Q : ℝ) :=
        (le_div_iff₀ hL_real_pos).mp hexp_both
      push_cast at h2
      linarith
    have h3 : (m : ℝ) * (L : ℝ) * (b : ℝ) ≤ 168 * (t : ℝ) * (b : ℝ) := by nlinarith
    exact le_of_mul_le_mul_right h3 hb_real_pos
  have hmL : m * L ≤ 168 * t := by exact_mod_cast hmL_real
  -- Since 4 ≤ L and c < b * (L + 1), we have 4 * c ≤ 5 * b * L!
  have h4c : 4 * c ≤ 5 * (b * L) := by
    have hrem : c < b * (L + 1) := by
      have := Nat.div_add_mod c b
      have := Nat.mod_lt c hb
      dsimp only [L]
      nlinarith
    nlinarith
  have h4mc : 4 * (m * c) ≤ 5 * b * (m * L) := by nlinarith
  have hfin : 4 * (m * c) ≤ 4 * (210 * t * b) := by nlinarith
  dsimp only [b] at hfin
  omega

/-- **PPL 108 / PPL 111 Succinct Boolean `Mv` Tradeoff Corollary (`t * r = Ω(m² c)`):**
Immediate clean form separating the small-redundancy (`r < m`) and medium-redundancy (`m ≤ r`)
regimes:
- If `r < m`: `m * c ≤ 210 * t` (matching `t = Ω(n²)` for square `Mv`, `Ω(n^{1+τ})` for `v`-Hinted `Mv`).
- If `m ≤ r`: `m ^ 2 * c ≤ 420 * t * r` (matching `t * r = Ω(n³)` for square `Mv`, `Ω(n^{2+τ})` for `v`-Hinted `Mv`). -/
theorem ppl108_boolean_mv_succinct_tradeoff (m c r t : ℕ)
    (hm : 1 ≤ m) (hc : 4 * (r / m + 1) ≤ c)
    (enc : Matrix (Fin m) (Fin c) Bool → Fin (2 ^ r))
    (next : Fin (2 ^ r) → (Fin c → Bool) → List Bool → Fin m × Fin c)
    (out : Fin (2 ^ r) → (Fin c → Bool) → List Bool → (Fin m → Bool))
    (hcorr : ∀ (M : Matrix (Fin m) (Fin c) Bool) (v : Fin c → Bool) (i : Fin m),
      out (enc M) v ((fun hist : List Bool =>
        M (next (enc M) v hist).1 (next (enc M) v hist).2 :: hist)^[t] []) i = true ↔
        ∃ j : Fin c, M i j = true ∧ v j = true) :
    (r < m → m * c ≤ 210 * t) ∧ (m ≤ r → m ^ 2 * c ≤ 420 * t * r) := by
  have hmain := ppl108_boolean_mv_succinct_cell_probe_lower_bound m c r t hm hc enc next out hcorr
  constructor
  · intro hlt
    rw [Nat.div_eq_of_lt hlt] at hmain
    simpa using hmain
  · intro hle
    have hdiv : m * (r / m) ≤ r := Nat.mul_div_le r m
    have hmul : m * (r / m + 1) ≤ 2 * r := by nlinarith
    have hstep : m * (m * c) ≤ m * (210 * t * (r / m + 1)) := Nat.mul_le_mul_left m hmain
    nlinarith

/-! ### Section 3: Sharp Log-Free Succinct Adaptive Cell-Probe Lower Bound for `𝔽₂`-`Mv` -/

/-- Existence of a binary linear code `[c, k, c/5 + 1]₂` (explicit Gilbert–Varshamov bound). -/
private lemma exists_gv_code (c : ℕ) (hc : 5 ≤ c) :
    ∀ k ≤ c / 5, ∃ V : Matrix (Fin k) (Fin c) (ZMod 2),
      ∀ u : Fin k → ZMod 2, u ≠ 0 →
        c / 5 + 1 ≤ (Finset.univ.filter fun j : Fin c => V.vecMul u j ≠ 0).card := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun i => i.elim0, fun u hu => ?_⟩
    exfalso; apply hu; ext i; exact i.elim0
  | succ k ih =>
    intro hk
    obtain ⟨V, hV⟩ := ih (by omega)
    let d := c / 5
    -- Bound the Hamming ball of radius d in (Fin c → ZMod 2).
    let ball0 : Finset (Fin c → ZMod 2) :=
      Finset.univ.filter fun v => (Finset.univ.filter fun j : Fin c => v j ≠ 0).card ≤ d
    have hball_card : (ball0.card : ℝ) ^ 5 < (2 : ℝ) ^ (4 * c) := by
      -- Map v ↦ supp(v) injects ball0 into powerset of Fin c filtered by card ≤ d.
      let supp : (Fin c → ZMod 2) → Finset (Fin c) :=
        fun v => Finset.univ.filter fun j => v j ≠ 0
      have hsupp_inj : Function.Injective supp := by
        intro v₁ v₂ hEq
        ext j
        have hmem : (v₁ j ≠ 0) ↔ (v₂ j ≠ 0) := by
          have := Finset.ext_iff.mp hEq j
          simpa [supp] using this
        have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        rcases h01 (v₁ j) with h1 | h1 <;> rcases h01 (v₂ j) with h2 | h2 <;> simp_all
      have hcard_le : (ball0.card : ℝ) ≤
          ∑ s ∈ (Finset.univ : Finset (Fin c)).powerset.filter (fun s => s.card ≤ d), (1 : ℝ) := by
        have hsub : ball0.image supp ⊆ (Finset.univ : Finset (Fin c)).powerset.filter (fun s => s.card ≤ d) := by
          intro s hs
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
          exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
            (Finset.mem_filter.mp hv).2⟩
        have hnat : ball0.card ≤ ((Finset.univ : Finset (Fin c)).powerset.filter (fun s => s.card ≤ d)).card := by
          rw [← Finset.card_image_of_injective ball0 hsupp_inj]
          exact Finset.card_le_card hsub
        simpa using (Nat.cast_le (α := ℝ)).mpr hnat
      have hpow_bound : (1 / 5 : ℝ) ^ d * (ball0.card : ℝ) ≤ (6 / 5 : ℝ) ^ c := by
        calc (1 / 5 : ℝ) ^ d * (ball0.card : ℝ)
          _ ≤ (1 / 5 : ℝ) ^ d *
                ∑ s ∈ (Finset.univ : Finset (Fin c)).powerset.filter (fun s => s.card ≤ d), (1 : ℝ) :=
              mul_le_mul_of_nonneg_left hcard_le (by positivity)
          _ = ∑ s ∈ (Finset.univ : Finset (Fin c)).powerset.filter (fun s => s.card ≤ d),
                (1 / 5 : ℝ) ^ d := by rw [Finset.mul_sum]; simp
          _ ≤ ∑ s ∈ (Finset.univ : Finset (Fin c)).powerset.filter (fun s => s.card ≤ d),
                (1 / 5 : ℝ) ^ s.card := by
              refine Finset.sum_le_sum fun s hs => ?_
              exact pow_le_pow_of_le_one (by positivity) (by norm_num) (Finset.mem_filter.mp hs).2
          _ ≤ ∑ s ∈ (Finset.univ : Finset (Fin c)).powerset, (1 / 5 : ℝ) ^ s.card :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
          _ = (1 + 1 / 5 : ℝ) ^ c := by rw [powerset_sum_pow, Fintype.card_fin]
          _ = (6 / 5 : ℝ) ^ c := by norm_num
      have hball_le : (ball0.card : ℝ) ≤ (5 : ℝ) ^ d * (6 / 5 : ℝ) ^ c := by
        have h1 : (5 : ℝ) ^ d * ((1 / 5 : ℝ) ^ d * (ball0.card : ℝ)) ≤ (5 : ℝ) ^ d * (6 / 5 : ℝ) ^ c :=
          mul_le_mul_of_nonneg_left hpow_bound (by positivity)
        have hinv : (5 : ℝ) ^ d * (1 / 5 : ℝ) ^ d = 1 := by
          rw [← mul_pow]; norm_num
        linarith [show (5 : ℝ) ^ d * ((1 / 5 : ℝ) ^ d * (ball0.card : ℝ)) = (ball0.card : ℝ) by
          rw [← mul_assoc, hinv, one_mul]]
      have h5d : 5 * d ≤ c := Nat.mul_div_le c 5
      calc (ball0.card : ℝ) ^ 5
        _ ≤ ((5 : ℝ) ^ d * (6 / 5 : ℝ) ^ c) ^ 5 := pow_le_pow_left₀ (by positivity) hball_le 5
        _ = (5 : ℝ) ^ (5 * d) * ((6 / 5 : ℝ) ^ 5) ^ c := by
            rw [mul_pow, ← pow_mul, mul_comm d 5]
            congr 1
            rw [← pow_mul, mul_comm c 5, pow_mul]
        _ ≤ (5 : ℝ) ^ c * ((6 / 5 : ℝ) ^ 5) ^ c := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact pow_le_pow_right₀ (by norm_num) h5d
        _ = ((5 : ℝ) * (6 / 5 : ℝ) ^ 5) ^ c := by rw [← mul_pow]
        _ < (16 : ℝ) ^ c := by
            refine pow_lt_pow_left₀ (by norm_num) (by positivity) (by omega)
        _ = (2 : ℝ) ^ (4 * c) := by
            rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, ← pow_mul]
    -- Total covered vectors by balls around row-space of V is ≤ 2^k * ball0.card < 2^c!
    let spanSet : Finset (Fin c → ZMod 2) := Finset.univ.image (fun u : Fin k → ZMod 2 => V.vecMul u)
    let bad : Finset (Fin c → ZMod 2) :=
      spanSet.biUnion fun w => ball0.image (fun e => w + e)
    have hbad_lt : bad.card < Fintype.card (Fin c → ZMod 2) := by
      have hcard_bad : bad.card ≤ 2 ^ k * ball0.card := by
        calc bad.card
          _ ≤ ∑ w ∈ spanSet, (ball0.image (fun e => w + e)).card := Finset.card_biUnion_le
          _ ≤ ∑ _w ∈ spanSet, ball0.card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
          _ = spanSet.card * ball0.card := by simp
          _ ≤ 2 ^ k * ball0.card := by
              refine Nat.mul_le_mul_right _ ?_
              calc spanSet.card ≤ Fintype.card (Fin k → ZMod 2) := Finset.card_image_le
                _ = 2 ^ k := by simp [Fintype.card_pi, ZMod.card]
      have h5k : 5 * k + 5 ≤ c := by omega
      have hlt_r : ((2 ^ k * ball0.card : ℕ) : ℝ) ^ 5 < ((2 ^ c : ℕ) : ℝ) ^ 5 := by
        push_cast
        rw [mul_pow, ← pow_mul, mul_comm k 5, ← pow_mul, mul_comm c 5]
        calc (2 : ℝ) ^ (5 * k) * (ball0.card : ℝ) ^ 5
          _ < (2 : ℝ) ^ (5 * k) * (2 : ℝ) ^ (4 * c) :=
              mul_lt_mul_of_pos_left hball_card (by positivity)
          _ = (2 : ℝ) ^ (5 * k + 4 * c) := (pow_add _ _ _).symm
          _ < (2 : ℝ) ^ (5 * c) := pow_lt_pow_right₀ (by norm_num) (by omega)
      have hlt_nat : 2 ^ k * ball0.card < 2 ^ c := by
        by_contra hge
        push Not at hge
        have h5le : ((2 ^ c : ℕ) : ℝ) ^ 5 ≤ ((2 ^ k * ball0.card : ℕ) : ℝ) ^ 5 :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast hge) 5
        linarith
      have hdom : Fintype.card (Fin c → ZMod 2) = 2 ^ c := by simp [Fintype.card_pi, ZMod.card]
      omega
    have hgood_ne : (Finset.univ \ bad).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hsub : (Finset.univ : Finset (Fin c → ZMod 2)) ⊆ bad := Finset.sdiff_eq_empty_iff_subset.mp hempty
      have := Finset.card_le_card hsub
      simp only [Finset.card_univ] at this
      omega
    obtain ⟨v_new, hv_mem⟩ := hgood_ne
    have hv_notbad : v_new ∉ bad := (Finset.mem_sdiff.mp hv_mem).2
    -- Append v_new as the last row of V!
    let V' : Matrix (Fin (k + 1)) (Fin c) (ZMod 2) :=
      fun i j => if h : i.val < k then V ⟨i.val, h⟩ j else v_new j
    refine ⟨V', fun u hu => ?_⟩
    let u_init : Fin k → ZMod 2 := fun i => u i.castSucc
    let u_last : ZMod 2 := u (Fin.last k)
    have hvm : V'.vecMul u = V.vecMul u_init + u_last • v_new := by
      ext j
      simp only [Matrix.vecMul, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Fin.sum_univ_castSucc, V', u_init, u_last]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp [Fin.val_castSucc, i.isLt]
      · simp [Fin.val_last]
    rw [hvm]
    have hlast01 : u_last = 0 ∨ u_last = 1 := by
      have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      exact h01 u_last
    rcases hlast01 with hlast | hlast
    · -- u_last = 0: u_init must be nonzero, apply IH!
      have hinit_ne : u_init ≠ 0 := by
        intro h0
        apply hu
        ext i
        refine Fin.lastCases ?_ ?_ i
        · exact hlast
        · intro i'
          exact congrFun h0 i'
      simpa [hlast] using hV u_init hinit_ne
    · -- u_last = 1: V.vecMul u_init + v_new has weight > d since v_new ∉ bad!
      rw [hlast, one_smul]
      by_contra hlt
      push Not at hlt
      have he_mem : V.vecMul u_init + v_new ∈ ball0 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      have hv_in_bad : v_new ∈ bad := by
        refine Finset.mem_biUnion.mpr ⟨V.vecMul u_init,
          Finset.mem_image.mpr ⟨u_init, Finset.mem_univ _, rfl⟩,
          Finset.mem_image.mpr ⟨V.vecMul u_init + v_new, he_mem, ?_⟩⟩
        ext j
        simp only [Pi.add_apply]
        have hchar : ∀ x y : ZMod 2, x + (x + y) = y := by decide
        exact hchar (V.vecMul u_init j) (v_new j)
      exact hv_notbad hv_in_bad

/-- Row kernel bound: if every nonzero `uᵀ V` has weight ≥ d and `|P| < d`, then the kernel of
`d ↦ V *ᵥ d` restricted to vectors vanishing on `P` has size `2 ^ (c - |P| - k)`. -/
private lemma row_kernel_card_mul_pow {k c d : ℕ}
    (V : Matrix (Fin k) (Fin c) (ZMod 2))
    (hdist : ∀ u : Fin k → ZMod 2, u ≠ 0 →
      d ≤ (Finset.univ.filter fun j : Fin c => V.vecMul u j ≠ 0).card)
    (P : Finset (Fin c)) (hP : P.card < d) :
    2 ^ k * (Finset.univ.filter fun x : Fin c → ZMod 2 =>
      (∀ j ∈ P, x j = 0) ∧ V.mulVec x = 0).card = 2 ^ (c - P.card) := by
  let Q := { j : Fin c // j ∉ P }
  let T : (Q → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
    { toFun := fun x ℓ => ∑ j : Q, V ℓ j.1 * x j
      map_add' := fun x y => by ext ℓ; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        ext ℓ
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring }
  -- Prove T is surjective: otherwise its range has a nonzero complement / linear functional!
  have hsurj : Function.Surjective T := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨W, hcomp⟩ := Submodule.exists_isCompl (LinearMap.range T)
    have hWne : W ≠ ⊥ := by
      intro hbot
      rw [hbot] at hcomp
      exact hne (eq_top_of_isCompl_bot hcomp)
    obtain ⟨w₀, hw₀W, hw₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    -- Build a linear functional φ : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 vanishing on range T with φ w₀ ≠ 0!
    -- Project onto W via Submodule.linearProjOfIsCompl, then apply a functional on W nonzero at w₀.
    let projW : (Fin k → ZMod 2) →ₗ[ZMod 2] W :=
      Submodule.projectionOnto W (LinearMap.range T) hcomp.symm
    let bW := Module.Basis.ofVectorSpace (ZMod 2) W
    have hw_sub_ne : (⟨w₀, hw₀W⟩ : W) ≠ 0 := by simpa [Subtype.ext_iff] using hw₀ne
    have hcoord_ne : ∃ idx, bW.coord idx ⟨w₀, hw₀W⟩ ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hw_sub_ne
      apply bW.repr.injective
      ext idx
      simpa [Module.Basis.coord_apply] using hall idx
    obtain ⟨idx, hψ⟩ := hcoord_ne
    let ψ : W →ₗ[ZMod 2] ZMod 2 := bW.coord idx
    let φ : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 := ψ.comp projW
    have hφ_range : ∀ y ∈ LinearMap.range T, φ y = 0 := by
      intro y hy
      dsimp only [φ, LinearMap.comp_apply]
      have hproj : projW y = 0 := Submodule.projectionOnto_apply_right hcomp.symm ⟨y, hy⟩
      rw [hproj, map_zero]
    have hφ_w0 : φ w₀ ≠ 0 := by
      dsimp only [φ, LinearMap.comp_apply]
      have hproj : projW w₀ = ⟨w₀, hw₀W⟩ :=
        Submodule.projectionOnto_apply_left hcomp.symm ⟨w₀, hw₀W⟩
      rw [hproj]; exact hψ
    let u : Fin k → ZMod 2 := fun ℓ => φ (Pi.single ℓ 1)
    have hu_ne : u ≠ 0 := by
      intro hu0
      apply hφ_w0
      have hw_exp : w₀ = ∑ ℓ : Fin k, w₀ ℓ • Pi.single ℓ (1 : ZMod 2) := by
        ext ℓ
        simp [Pi.single_apply]
      rw [hw_exp, map_sum]
      refine Finset.sum_eq_zero fun ℓ _ => ?_
      rw [map_smul]
      have h0 : φ (Pi.single ℓ 1) = 0 := congrFun hu0 ℓ
      simp [h0]
    -- Show V.vecMul u vanishes outside P!
    have hvan : ∀ j : Q, V.vecMul u j.1 = 0 := by
      intro j
      have hT := hφ_range (T (Pi.single j 1)) ⟨Pi.single j 1, rfl⟩
      have hTj : T (Pi.single j 1) = fun ℓ => V ℓ j.1 := by
        ext ℓ
        simp [T, Pi.single_apply]
      rw [hTj] at hT
      have hexp : (fun ℓ => V ℓ j.1) = ∑ ℓ : Fin k, V ℓ j.1 • Pi.single ℓ (1 : ZMod 2) := by
        ext ℓ; simp [Pi.single_apply]
      rw [hexp, map_sum] at hT
      simp only [map_smul] at hT
      have hsum : V.vecMul u j.1 = ∑ ℓ : Fin k, V ℓ j.1 • φ (Pi.single ℓ 1) := by
        simp [Matrix.vecMul, dotProduct, u, mul_comm]
      rw [hsum]
      exact hT
    have hsub : (Finset.univ.filter fun j : Fin c => V.vecMul u j ≠ 0) ⊆ P := by
      intro j hj
      by_contra hjnot
      exact (Finset.mem_filter.mp hj).2 (hvan ⟨j, hjnot⟩)
    have hle := Finset.card_le_card hsub
    have hge := hdist u hu_ne
    omega
  -- Since T is surjective linear, all fibers have equal size |ker T|, so 2^k * |ker T| = |Q → ZMod 2|!
  have hfib_eq : ∀ y : Fin k → ZMod 2,
      (Finset.univ.filter fun x : Q → ZMod 2 => T x = y).card =
      (Finset.univ.filter fun x : Q → ZMod 2 => T x = 0).card := by
    intro y
    obtain ⟨x₀, hx₀⟩ := hsurj y
    refine Finset.card_bij (fun x _ => x - x₀) ?_ ?_ ?_
    · intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [map_sub, (Finset.mem_filter.mp hx).2, hx₀, sub_self]
    · intro x₁ _ x₂ _ hEq
      exact sub_left_injective hEq
    · intro z hz
      refine ⟨z + x₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, add_sub_cancel_right z x₀⟩
      rw [map_add, (Finset.mem_filter.mp hz).2, hx₀, zero_add]
  have htot : Fintype.card (Q → ZMod 2) =
      2 ^ k * (Finset.univ.filter fun x : Q → ZMod 2 => T x = 0).card := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := T) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    simp only [hfib_eq, Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
      ZMod.card, Fintype.card_fin, smul_eq_mul]
  -- Biject ker T with { x : Fin c → ZMod 2 | (∀ j ∈ P, x j = 0) ∧ V.mulVec x = 0 }.
  have hker_eq : (Finset.univ.filter fun x : Fin c → ZMod 2 =>
      (∀ j ∈ P, x j = 0) ∧ V.mulVec x = 0).card =
      (Finset.univ.filter fun x : Q → ZMod 2 => T x = 0).card := by
    refine Finset.card_bij (fun x _ j => x j.1) ?_ ?_ ?_
    · intro x hx
      obtain ⟨hP0, hMV0⟩ := (Finset.mem_filter.mp hx).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      ext ℓ
      have h0 : (V.mulVec x) ℓ = 0 := congrFun hMV0 ℓ
      dsimp only [T, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      rw [← h0, Matrix.mulVec, dotProduct]
      symm
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ \ P))]
      · refine Finset.sum_bij (fun j hj => (⟨j, (Finset.mem_sdiff.mp hj).2⟩ : Q)) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro _ _ _ _ h; exact congrArg Subtype.val h
        · intro j _; exact ⟨j.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, j.2⟩, rfl⟩
        · intro _ _; rfl
      · intro j _ hjnot
        have hjP : j ∈ P := by
          by_contra hjn; exact hjnot (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjn⟩)
        simp [hP0 j hjP]
    · intro x₁ hx₁ x₂ hx₂ hEq
      ext j
      by_cases hj : j ∈ P
      · rw [(Finset.mem_filter.mp hx₁).2.1 j hj, (Finset.mem_filter.mp hx₂).2.1 j hj]
      · exact congrFun hEq ⟨j, hj⟩
    · intro z hz
      let x : Fin c → ZMod 2 := fun j => if hj : j ∈ P then 0 else z ⟨j, hj⟩
      refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
      · intro j hj; simp [x, hj]
      · ext ℓ
        have hT0 : T z ℓ = 0 := congrFun (Finset.mem_filter.mp hz).2 ℓ
        simp only [Pi.zero_apply]
        rw [← hT0]
        dsimp only [T, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct]
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ \ P))]
        · refine Finset.sum_bij (fun j hj => (⟨j, (Finset.mem_sdiff.mp hj).2⟩ : Q)) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro _ _ _ _ h; exact congrArg Subtype.val h
          · intro j _; exact ⟨j.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, j.2⟩, rfl⟩
          · intro j hj; simp [x, (Finset.mem_sdiff.mp hj).2]
        · intro j _ hjnot
          have hjP : j ∈ P := by
            by_contra hjn; exact hjnot (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjn⟩)
          simp [x, hjP]
      · ext ⟨j, hj⟩; simp [x, hj]
  have hQcard : Fintype.card (Q → ZMod 2) = 2 ^ (c - P.card) := by
    have hq : Fintype.card Q = c - P.card := by
      have : Fintype.card Q = (Finset.univ \ P).card := by
        rw [Fintype.card_subtype]
        congr 1; ext j; simp
      rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ P), Finset.card_univ, Fintype.card_fin]
    simp [Fintype.card_pi, ZMod.card, hq]
  rw [hker_eq, ← htot, hQcard]

/-- Probe coordinates collected during `t` adaptive steps over `ZMod 2`. -/
private def visitedF2 {m c : ℕ} (next : List (ZMod 2) → Fin m × Fin c)
    (M : Matrix (Fin m) (Fin c) (ZMod 2)) : ℕ → List (ZMod 2) × Finset (Fin m × Fin c)
  | 0 => ([], ∅)
  | s + 1 =>
    let res := visitedF2 next M s
    let p := next res.1
    (M p.1 p.2 :: res.1, insert p res.2)

private lemma visitedF2_fst {m c : ℕ} (next : List (ZMod 2) → Fin m × Fin c)
    (M : Matrix (Fin m) (Fin c) (ZMod 2)) (s : ℕ) :
    (visitedF2 next M s).1 =
      (fun hist : List (ZMod 2) => M (next hist).1 (next hist).2 :: hist)^[s] [] := by
  induction s with
  | zero => rfl
  | succ s ih => simp only [visitedF2, Function.iterate_succ_apply', ih]

private lemma visitedF2_card_le {m c : ℕ} (next : List (ZMod 2) → Fin m × Fin c)
    (M : Matrix (Fin m) (Fin c) (ZMod 2)) (s : ℕ) :
    (visitedF2 next M s).2.card ≤ s := by
  induction s with
  | zero => simp [visitedF2]
  | succ s ih =>
    simp only [visitedF2]
    exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ih)

private lemma visitedF2_agree {m c : ℕ} (next : List (ZMod 2) → Fin m × Fin c)
    (M₁ M₂ : Matrix (Fin m) (Fin c) (ZMod 2)) (s : ℕ)
    (hagree : ∀ p ∈ (visitedF2 next M₁ s).2, M₁ p.1 p.2 = M₂ p.1 p.2) :
    visitedF2 next M₁ s = visitedF2 next M₂ s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have hprev := ih (fun p hp => hagree p (Finset.mem_insert_of_mem hp))
    have hcur : M₁ (next (visitedF2 next M₁ s).1).1 (next (visitedF2 next M₁ s).1).2 =
        M₂ (next (visitedF2 next M₁ s).1).1 (next (visitedF2 next M₁ s).1).2 :=
      hagree _ (Finset.mem_insert_self _ _)
    simp only [visitedF2, ← hprev, hcur]

/-- **PPL 108 / PPL 111 Sharp Log-Free Succinct Adaptive Cell-Probe Lower Bound (`𝔽₂`-`Mv`):**
Via Gilbert–Varshamov linear codes and a Kraft equivalence-class partition:
For any `m ≥ 1, c ≥ 5`, any succinct adaptive `t`-bit-probe data structure with `r` bits of
redundancy computing `M *ᵥ v` over `ZMod 2` satisfies:
`18 * r ≥ m * c ∨ 10 * t ≥ m * c ∨ 40 * r * t ≥ m ^ 2 * c`.
For square `n × n` matrices this yields `r = Ω(n²) ∨ t = Ω(n²) ∨ r * t = Ω(n³)`;
for `v`-Hinted `Mv` dimensions (`m = n, c = n^τ`) it yields `r = Ω(n^{1+τ}) ∨ t = Ω(n^{1+τ}) ∨ r * t = Ω(n^{2+τ})`. -/
theorem ppl108_f2_mv_succinct_cell_probe_lower_bound (m c r t : ℕ)
    (hm : 1 ≤ m) (hc : 5 ≤ c)
    (enc : Matrix (Fin m) (Fin c) (ZMod 2) → Fin (2 ^ r))
    (next : Fin (2 ^ r) → (Fin c → ZMod 2) → List (ZMod 2) → Fin m × Fin c)
    (out : Fin (2 ^ r) → (Fin c → ZMod 2) → List (ZMod 2) → (Fin m → ZMod 2))
    (hcorr : ∀ (M : Matrix (Fin m) (Fin c) (ZMod 2)) (v : Fin c → ZMod 2),
      out (enc M) v ((fun hist : List (ZMod 2) =>
        M (next (enc M) v hist).1 (next (enc M) v hist).2 :: hist)^[t] []) = M.mulVec v) :
    18 * r ≥ m * c ∨ 10 * t ≥ m * c ∨ 40 * r * t ≥ m ^ 2 * c := by
  let d := c / 5 + 1
  -- Core tradeoff lemma for any 1 ≤ k ≤ c / 5 with 2 * k * t ≤ m * d: gives m * k ≤ 2 * r!
  have hcore : ∀ k : ℕ, k ≤ c / 5 → 2 * k * t ≤ m * d → m * k ≤ 2 * r := by
    intro k hkle hkt
    obtain ⟨V, hVdist⟩ := exists_gv_code c hc k hkle
    -- Pigeonhole on enc to find fiber F with |F| * 2^r ≥ 2^(m*c)
    have hcard_M : Fintype.card (Matrix (Fin m) (Fin c) (ZMod 2)) = 2 ^ (m * c) := by
      rw [Fintype.card_congr (Matrix.of.symm)]
      simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ZMod.card, ← pow_mul, mul_comm]
    have hsum_fib : ∑ ρ : Fin (2 ^ r),
        (Finset.univ.filter fun M : Matrix (Fin m) (Fin c) (ZMod 2) => enc M = ρ).card =
        2 ^ (m * c) := by
      rw [← hcard_M, ← Finset.card_univ]
      exact (Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)).symm
    obtain ⟨ρ₀, _, hρ₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (2 ^ r)))
      (fun ρ => (Finset.univ.filter fun M : Matrix (Fin m) (Fin c) (ZMod 2) => enc M = ρ).card)
      ⟨⟨0, Nat.two_pow_pos r⟩, Finset.mem_univ _⟩
    let F := Finset.univ.filter fun M : Matrix (Fin m) (Fin c) (ZMod 2) => enc M = ρ₀
    have hF_lower : 2 ^ (m * c) ≤ F.card * 2 ^ r := by
      calc 2 ^ (m * c)
        _ = ∑ ρ : Fin (2 ^ r),
              (Finset.univ.filter fun M : Matrix (Fin m) (Fin c) (ZMod 2) => enc M = ρ).card :=
            hsum_fib.symm
        _ ≤ ∑ _ρ : Fin (2 ^ r), F.card := Finset.sum_le_sum fun ρ _ => hρ₀ ρ (Finset.mem_univ _)
        _ = F.card * 2 ^ r := by simp [mul_comm]
    -- Define combined probe set P(M) across V 0, ..., V (k-1)
    let P : Matrix (Fin m) (Fin c) (ZMod 2) → Finset (Fin m × Fin c) := fun M =>
      Finset.univ.biUnion fun ℓ : Fin k => (visitedF2 (next ρ₀ (V ℓ)) M t).2
    have hP_card : ∀ M, (P M).card ≤ k * t := by
      intro M
      calc (P M).card
        _ ≤ ∑ ℓ : Fin k, (visitedF2 (next ρ₀ (V ℓ)) M t).2.card := Finset.card_biUnion_le
        _ ≤ ∑ _ℓ : Fin k, t := Finset.sum_le_sum fun ℓ _ => visitedF2_card_le _ _ _
        _ = k * t := by simp
    -- Path consistency: if M₁, M₂ agree on P M₁, then P M₂ = P M₁ and all query histories agree!
    have hpath : ∀ M₁ M₂, (∀ p ∈ P M₁, M₁ p.1 p.2 = M₂ p.1 p.2) →
        P M₂ = P M₁ ∧ ∀ ℓ : Fin k,
          (visitedF2 (next ρ₀ (V ℓ)) M₁ t).1 = (visitedF2 (next ρ₀ (V ℓ)) M₂ t).1 := by
      intro M₁ M₂ hag
      have hℓ : ∀ ℓ : Fin k, visitedF2 (next ρ₀ (V ℓ)) M₁ t = visitedF2 (next ρ₀ (V ℓ)) M₂ t := by
        intro ℓ
        exact visitedF2_agree _ M₁ M₂ t (fun p hp => hag p (Finset.mem_biUnion.mpr ⟨ℓ, Finset.mem_univ _, hp⟩))
      refine ⟨?_, fun ℓ => congrArg Prod.fst (hℓ ℓ)⟩
      dsimp only [P]
      refine Finset.biUnion_congr rfl fun ℓ _ => (congrArg Prod.snd (hℓ ℓ)).symm
    -- Define equivalence classes C(M) = { M' | ∀ p ∈ P M, M' p = M p }
    let C : Matrix (Fin m) (Fin c) (ZMod 2) → Finset (Matrix (Fin m) (Fin c) (ZMod 2)) :=
      fun M => Finset.univ.filter fun M' => ∀ p ∈ P M, M' p.1 p.2 = M p.1 p.2
    have hC_self : ∀ M, M ∈ C M := fun M => Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ => rfl⟩
    have hC_eq_of_mem : ∀ M₁ M₂, M₂ ∈ C M₁ → C M₂ = C M₁ := by
      intro M₁ M₂ hmem
      have hag : ∀ p ∈ P M₁, M₁ p.1 p.2 = M₂ p.1 p.2 := fun p hp => ((Finset.mem_filter.mp hmem).2 p hp).symm
      have hPeq := (hpath M₁ M₂ hag).1
      ext M₃
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, hPeq]
      constructor
      · intro h p hp; rw [h p hp, ← hag p hp]
      · intro h p hp; rw [h p hp, hag p hp]
    -- Cardinality of C(M) is ∏ i, 2 ^ (c - |P_i(M)|)
    have hC_card : ∀ M, (C M).card =
        ∏ i : Fin m, 2 ^ (c - (Finset.univ.filter fun j : Fin c => (i, j) ∈ P M).card) := by
      intro M
      let allowRow : Fin m → Finset (Fin c → ZMod 2) := fun i =>
        Finset.univ.filter fun row => ∀ j : Fin c, (i, j) ∈ P M → row j = M i j
      have hC_eq : (C M).card = (Fintype.piFinset allowRow).card := by
        refine Finset.card_bij (fun M' _ => Matrix.of.symm M') ?_ ?_ ?_
        · intro M' hM'
          rw [Fintype.mem_piFinset]
          intro i
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hij => ?_⟩
          exact (Finset.mem_filter.mp hM').2 (i, j) hij
        · intro M₁ _ M₂ _ hEq
          exact Matrix.of.symm.injective hEq
        · intro f hf
          rw [Fintype.mem_piFinset] at hf
          refine ⟨Matrix.of f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun ⟨i, j⟩ hij => ?_⟩, rfl⟩
          exact (Finset.mem_filter.mp (hf i)).2 j hij
      rw [hC_eq, Fintype.card_piFinset]
      refine Finset.prod_congr rfl fun i _ => ?_
      let Pi := Finset.univ.filter fun j : Fin c => (i, j) ∈ P M
      have hrow_card : (allowRow i).card = 2 ^ (c - Pi.card) := by
        -- Translate by M i to count functions vanishing on Pi!
        have hbij : (allowRow i).card =
            (Finset.univ.filter fun row : Fin c → ZMod 2 => ∀ j ∈ Pi, row j = 0).card := by
          refine Finset.card_bij (fun row _ => row - M i) ?_ ?_ ?_
          · intro row hrow
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => ?_⟩
            have := (Finset.mem_filter.mp hrow).2 j (Finset.mem_filter.mp hj).2
            simp [this]
          · intro r₁ _ r₂ _ h; exact sub_left_injective h
          · intro row hrow
            refine ⟨row + M i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => ?_⟩,
              add_sub_cancel_right row (M i)⟩
            have h0 := (Finset.mem_filter.mp hrow).2 j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
            simp [h0]
        rw [hbij]
        -- Biject with { j : Fin c // j ∉ Pi } → ZMod 2
        let Q := { j : Fin c // j ∉ Pi }
        have hbij2 : (Finset.univ.filter fun row : Fin c → ZMod 2 => ∀ j ∈ Pi, row j = 0).card =
            Fintype.card (Q → ZMod 2) := by
          rw [← Finset.card_univ]
          refine Finset.card_bij (fun row _ j => row j.1) (fun _ _ => Finset.mem_univ _) ?_ ?_
          · intro r₁ hr₁ r₂ hr₂ hEq
            ext j
            by_cases hj : j ∈ Pi
            · rw [(Finset.mem_filter.mp hr₁).2 j hj, (Finset.mem_filter.mp hr₂).2 j hj]
            · exact congrFun hEq ⟨j, hj⟩
          · intro z _
            refine ⟨fun j => if hj : j ∈ Pi then 0 else z ⟨j, hj⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => by simp [hj]⟩,
              by ext ⟨j, hj⟩; simp [hj]⟩
        rw [hbij2]
        have hq : Fintype.card Q = c - Pi.card := by
          have : Fintype.card Q = (Finset.univ \ Pi).card := by
            rw [Fintype.card_subtype]; congr 1; ext j; simp
          rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        simp [Fintype.card_pi, ZMod.card, hq]
      exact hrow_card
    -- Per-class bound: 2 ^ ((m + 1) / 2 * k) * (F ∩ C₀).card ≤ C₀.card for every class C₀!
    let g_min := (m + 1) / 2
    have hclass_bound : ∀ C₀ ∈ Finset.univ.image C,
        2 ^ (g_min * k) * (F ∩ C₀).card ≤ C₀.card := by
      intro C₀ hC₀
      by_cases hne : (F ∩ C₀).Nonempty
      · obtain ⟨M₀, hM₀⟩ := hne
        have hM₀F : M₀ ∈ F := (Finset.mem_inter.mp hM₀).1
        have hM₀C : M₀ ∈ C₀ := (Finset.mem_inter.mp hM₀).2
        have hM₀_enc : enc M₀ = ρ₀ := (Finset.mem_filter.mp hM₀F).2
        obtain ⟨M₁, _, rfl⟩ := Finset.mem_image.mp hC₀
        have hCeq : C M₀ = C M₁ := hC_eq_of_mem M₁ M₀ hM₀C
        rw [← hCeq]
        -- Every M' ∈ F ∩ C M₀ has D = M' - M₀ vanishing on P M₀ and V *ᵥ (D i) = 0 for all rows i!
        let rowKer : Fin m → Finset (Fin c → ZMod 2) := fun i =>
          Finset.univ.filter fun x =>
            (∀ j ∈ (Finset.univ.filter fun j : Fin c => (i, j) ∈ P M₀), x j = 0) ∧ V.mulVec x = 0
        have hFC_le : (F ∩ C M₀).card ≤ ∏ i : Fin m, (rowKer i).card := by
          rw [← Fintype.card_piFinset]
          refine Finset.card_le_card_of_injOn (fun M' => Matrix.of.symm (M' - M₀)) ?_ ?_
          · intro M' hM'
            have hM'F : M' ∈ F := (Finset.mem_inter.mp hM').1
            have hM'C : M' ∈ C M₀ := (Finset.mem_inter.mp hM').2
            have hM'_enc : enc M' = ρ₀ := (Finset.mem_filter.mp hM'F).2
            have hag : ∀ p ∈ P M₀, M₀ p.1 p.2 = M' p.1 p.2 :=
              fun p hp => ((Finset.mem_filter.mp hM'C).2 p hp).symm
            have hhist_eq := (hpath M₀ M' hag).2
            rw [Finset.mem_coe, Fintype.mem_piFinset]
            intro i
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
            · intro j hj
              have hp : (i, j) ∈ P M₀ := (Finset.mem_filter.mp hj).2
              simp [Matrix.sub_apply, hag (i, j) hp]
            · ext ℓ
              have h1 := hcorr M₀ (V ℓ)
              have h2 := hcorr M' (V ℓ)
              rw [hM₀_enc] at h1; rw [hM'_enc] at h2
              have hh := hhist_eq ℓ
              rw [visitedF2_fst, visitedF2_fst] at hh
              rw [← hh, h1] at h2
              have hrow_eq : (M'.mulVec (V ℓ)) i = (M₀.mulVec (V ℓ)) i := congrFun h2.symm i
              simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hrow_eq ⊢
              have hsub_val : ∀ j : Fin c, (Matrix.of.symm (M' - M₀)) i j = M' i j - M₀ i j := fun _ => rfl
              simp only [hsub_val]
              have : ∑ j : Fin c, V ℓ j * (M' i j - M₀ i j) =
                  (∑ j : Fin c, M' i j * V ℓ j) - (∑ j : Fin c, M₀ i j * V ℓ j) := by
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun j _ => by ring
              rw [this, hrow_eq, sub_self]
          · intro M₁' _ M₂' _ hEq
            exact sub_left_injective (Matrix.of.symm.injective hEq)
        -- Count good rows (those with |P_i(M₀)| < d): at least g_min = (m + 1) / 2!
        let Pi : Fin m → Finset (Fin c) := fun i =>
          Finset.univ.filter fun j : Fin c => (i, j) ∈ P M₀
        let goodRows : Finset (Fin m) := Finset.univ.filter fun i => (Pi i).card < d
        have hsum_Pi : ∑ i : Fin m, (Pi i).card = (P M₀).card := by
          have h1 : P M₀ = (Finset.univ : Finset (Fin m)).biUnion
              (fun i => (Pi i).map ⟨fun j => (i, j), fun _ _ h => (Prod.mk.inj h).2⟩) := by
            ext ⟨i, j⟩
            simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map,
              Pi, Finset.mem_filter]
            constructor
            · intro h; exact ⟨i, j, h, rfl⟩
            · rintro ⟨a, b, hab, hEq⟩
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
              exact hab
          rw [h1, Finset.card_biUnion]
          · refine Finset.sum_congr rfl fun i _ => (Finset.card_map _).symm
          · intro i₁ _ i₂ _ hne
            show Disjoint _ _
            rw [Finset.disjoint_left]
            intro p hp1 hp2
            obtain ⟨j₁, _, rfl⟩ := Finset.mem_map.mp hp1
            obtain ⟨j₂, _, hEq⟩ := Finset.mem_map.mp hp2
            exact hne (Prod.mk.inj hEq).1.symm
        have hgood_ge : g_min ≤ goodRows.card := by
          let badRows := Finset.univ \ goodRows
          have hbad_sum : badRows.card * d ≤ (P M₀).card := by
            calc badRows.card * d
              _ = ∑ _i ∈ badRows, d := by simp
              _ ≤ ∑ i ∈ badRows, (Pi i).card := by
                  refine Finset.sum_le_sum fun i hi => ?_
                  have hnot : i ∉ goodRows := (Finset.mem_sdiff.mp hi).2
                  simp only [goodRows, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
                  exact hnot
              _ ≤ ∑ i : Fin m, (Pi i).card :=
                  Finset.sum_le_sum_of_subset (Finset.subset_univ _)
              _ = (P M₀).card := hsum_Pi
          have hbad_le : badRows.card * d ≤ k * t := le_trans hbad_sum (hP_card M₀)
          have hdpos : 0 < d := by dsimp only [d]; omega
          have h2bad : 2 * badRows.card ≤ m := by
            have : (2 * badRows.card) * d ≤ m * d := by nlinarith
            exact Nat.le_of_mul_le_mul_right this hdpos
          have hsplit : badRows.card + goodRows.card = m := by
            have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ goodRows)
            simpa [badRows] using this
          dsimp only [g_min]
          omega
        -- Multiply row bounds: 2^(goodRows.card * k) * ∏ (rowKer i).card ≤ ∏ 2^(c - |Pi i|) = |C M₀|!
        have hrow_le : ∀ i : Fin m,
            (if i ∈ goodRows then 2 ^ k else 1) * (rowKer i).card ≤ 2 ^ (c - (Pi i).card) := by
          intro i
          split_ifs with hgi
          · have hlt : (Pi i).card < d := (Finset.mem_filter.mp hgi).2
            exact le_of_eq (row_kernel_card_mul_pow V hVdist (Pi i) hlt)
          · rw [one_mul]
            let Q := { j : Fin c // j ∉ Pi i }
            have hle : (rowKer i).card ≤ Fintype.card (Q → ZMod 2) := by
              rw [← Finset.card_univ]
              refine Finset.card_le_card_of_injOn (fun x j => x j.1) (fun _ _ => Finset.mem_univ _) ?_
              intro x₁ hx₁ x₂ hx₂ hEq
              ext j
              by_cases hj : j ∈ Pi i
              · rw [(Finset.mem_filter.mp hx₁).2.1 j hj, (Finset.mem_filter.mp hx₂).2.1 j hj]
              · exact congrFun hEq ⟨j, hj⟩
            have hQcard : Fintype.card (Q → ZMod 2) = 2 ^ (c - (Pi i).card) := by
              have hq : Fintype.card Q = c - (Pi i).card := by
                have : Fintype.card Q = (Finset.univ \ Pi i).card := by
                  rw [Fintype.card_subtype]; congr 1; ext j; simp
                rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
              simp [Fintype.card_pi, ZMod.card, hq]
            rwa [hQcard] at hle
        have hprod_bound : (∏ i : Fin m, (if i ∈ goodRows then 2 ^ k else 1)) *
            (∏ i : Fin m, (rowKer i).card) ≤ (C M₀).card := by
          rw [← Finset.prod_mul_distrib, hC_card M₀]
          exact Finset.prod_le_prod' fun i _ => hrow_le i
        have hprod_good : ∏ i : Fin m, (if i ∈ goodRows then 2 ^ k else 1) = 2 ^ (goodRows.card * k) := by
          rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ goodRows)]
          have h1 : ∏ i ∈ Finset.univ.filter (· ∈ goodRows), (if i ∈ goodRows then 2 ^ k else 1) =
              (2 ^ k) ^ goodRows.card := by
            have heq1 : Finset.univ.filter (· ∈ goodRows) = goodRows := by ext x; simp
            rw [heq1]
            calc ∏ i ∈ goodRows, (if i ∈ goodRows then 2 ^ k else 1)
              _ = ∏ _i ∈ goodRows, (2 ^ k) := Finset.prod_congr rfl fun x hx => if_pos hx
              _ = (2 ^ k) ^ goodRows.card := Finset.prod_const _
          have h2 : ∏ i ∈ Finset.univ.filter (· ∉ goodRows), (if i ∈ goodRows then 2 ^ k else 1) = 1 := by
            refine Finset.prod_eq_one fun x hx => ?_
            have : x ∉ goodRows := (Finset.mem_filter.mp hx).2
            exact if_neg this
          rw [h1, h2, mul_one, ← pow_mul, mul_comm]
        rw [hprod_good] at hprod_bound
        calc 2 ^ (g_min * k) * (F ∩ C M₀).card
          _ ≤ 2 ^ (goodRows.card * k) * (F ∩ C M₀).card :=
              Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right k hgood_ge))
          _ ≤ 2 ^ (goodRows.card * k) * (∏ i : Fin m, (rowKer i).card) :=
              Nat.mul_le_mul_left _ hFC_le
          _ ≤ (C M₀).card := hprod_bound
      · have hemp : F ∩ C₀ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        rw [hemp, Finset.card_empty, mul_zero]
        exact Nat.zero_le _
    -- Sum over all pairwise-disjoint equivalence classes in (univ.image C)!
    let Classes := (Finset.univ : Finset (Matrix (Fin m) (Fin c) (ZMod 2))).image C
    have hdisj : (Classes : Set (Finset (Matrix (Fin m) (Fin c) (ZMod 2)))).PairwiseDisjoint id := by
      intro C₁ h₁ C₂ h₂ hne
      obtain ⟨M₁, _, rfl⟩ := Finset.mem_image.mp h₁
      obtain ⟨M₂, _, rfl⟩ := Finset.mem_image.mp h₂
      show Disjoint (C M₁) (C M₂)
      rw [Finset.disjoint_left]
      intro M hM1 hM2
      exact hne ((hC_eq_of_mem M₁ M hM1).symm.trans (hC_eq_of_mem M₂ M hM2))
    have hunion : Classes.biUnion id = Finset.univ := by
      ext M
      simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
      exact ⟨C M, Finset.mem_image.mpr ⟨M, Finset.mem_univ _, rfl⟩, hC_self M⟩
    have hF_sum : ∑ C₀ ∈ Classes, (F ∩ C₀).card = F.card := by
      have hdisjF : (Classes : Set _).PairwiseDisjoint (fun C₀ => F ∩ C₀) :=
        fun C₁ h₁ C₂ h₂ hne => (hdisj h₁ h₂ hne).mono Finset.inter_subset_right Finset.inter_subset_right
      rw [← Finset.card_biUnion hdisjF]
      congr 1
      ext M
      simp only [Finset.mem_biUnion, Finset.mem_inter]
      constructor
      · rintro ⟨_, _, hMF, _⟩; exact hMF
      · intro hMF
        exact ⟨C M, Finset.mem_image.mpr ⟨M, Finset.mem_univ _, rfl⟩, hMF, hC_self M⟩
    have hC_sum : ∑ C₀ ∈ Classes, C₀.card = 2 ^ (m * c) := by
      change ∑ C₀ ∈ Classes, (id C₀).card = 2 ^ (m * c)
      rw [← Finset.card_biUnion hdisj, hunion, Finset.card_univ, hcard_M]
    have htot_le : 2 ^ (g_min * k) * F.card ≤ 2 ^ (m * c) := by
      calc 2 ^ (g_min * k) * F.card
        _ = 2 ^ (g_min * k) * ∑ C₀ ∈ Classes, (F ∩ C₀).card := by rw [hF_sum]
        _ = ∑ C₀ ∈ Classes, 2 ^ (g_min * k) * (F ∩ C₀).card := by rw [Finset.mul_sum]
        _ ≤ ∑ C₀ ∈ Classes, C₀.card := Finset.sum_le_sum hclass_bound
        _ = 2 ^ (m * c) := hC_sum
    have hpow_le : 2 ^ (g_min * k) * 2 ^ (m * c) ≤ 2 ^ (m * c) * 2 ^ r := by
      calc 2 ^ (g_min * k) * 2 ^ (m * c)
        _ ≤ 2 ^ (g_min * k) * (F.card * 2 ^ r) := Nat.mul_le_mul_left _ hF_lower
        _ = (2 ^ (g_min * k) * F.card) * 2 ^ r := by ring
        _ ≤ 2 ^ (m * c) * 2 ^ r := Nat.mul_le_mul_right _ htot_le
    have hpow_gk : 2 ^ (g_min * k) ≤ 2 ^ r :=
      Nat.le_of_mul_le_mul_right (by linarith) (Nat.two_pow_pos (m * c))
    have hgk_le_r : g_min * k ≤ r := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow_gk
    have hm_le_2g : m ≤ 2 * g_min := by dsimp only [g_min]; omega
    nlinarith
  -- Optimize k to conclude the trichotomy!
  by_cases ht0 : t = 0
  · left
    have h1 := hcore (c / 5) le_rfl (by simp [ht0])
    have hc9 : c ≤ 9 * (c / 5) := by omega
    nlinarith
  · have htpos : 1 ≤ t := by omega
    let k₀ := min (c / 5) ((m * d) / (2 * t))
    have hk0_le : k₀ ≤ c / 5 := min_le_left _ _
    have hk0_kt : 2 * k₀ * t ≤ m * d := by
      have h1 : k₀ ≤ (m * d) / (2 * t) := min_le_right _ _
      have h2 : k₀ * (2 * t) ≤ m * d := le_trans (Nat.mul_le_mul_right _ h1) (Nat.div_mul_le_self _ _)
      linarith
    have hmk0 := hcore k₀ hk0_le hk0_kt
    by_cases hmin : c / 5 ≤ (m * d) / (2 * t)
    · left
      have hk0_eq : k₀ = c / 5 := min_eq_left hmin
      rw [hk0_eq] at hmk0
      have hc9 : c ≤ 9 * (c / 5) := by omega
      nlinarith
    · push Not at hmin
      have hk0_eq : k₀ = (m * d) / (2 * t) := min_eq_right (le_of_lt hmin)
      by_cases hk0_zero : k₀ = 0
      · right; left
        rw [hk0_eq] at hk0_zero
        have hlt : m * d < 2 * t := by
          by_contra hge
          push Not at hge
          have hpos : 1 ≤ (m * d) / (2 * t) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
          omega
        have h5d : c < 5 * d := by dsimp only [d]; omega
        nlinarith
      · right; right
        have hk0_pos : 1 ≤ k₀ := Nat.pos_of_ne_zero hk0_zero
        have hdiv_gt : m * d < (k₀ + 1) * (2 * t) := by
          rw [hk0_eq]
          have hrem := Nat.div_add_mod (m * d) (2 * t)
          have hmod := Nat.mod_lt (m * d) (by omega : 0 < 2 * t)
          nlinarith
        have h4kt : m * d ≤ 4 * k₀ * t := by nlinarith
        have h5d : c < 5 * d := by dsimp only [d]; omega
        nlinarith

/-! ### Section 4: Exact Four-Russians / Block-Precomputation `O(m c / log n)` Upper Bound -/

/-- **PPL 108 / PPL 111 Exact Four-Russians Block-Precomputation Upper Bound:**
For any `m × c` Boolean matrix `M` and block width `b ≥ 1` (with `B = (c + b - 1) / b` blocks),
there exists a preprocessed table `T : Fin B → (Fin b → Bool) → (Fin m → Bool)` (total size
`m * B * 2^b` bits) and a matrix-independent slicing map `slice : (Fin c → Bool) → Fin B → (Fin b → Bool)`
such that every Boolean matrix-vector product `M v` is computed exactly by taking the Boolean OR of
only `B` table entries per row (`m * B` Boolean table lookups in total). -/
theorem ppl108_four_russians_mv_upper_bound (m c b : ℕ) (hb : 1 ≤ b)
    (M : Matrix (Fin m) (Fin c) Bool) :
    ∃ (T : Fin ((c + b - 1) / b) → (Fin b → Bool) → (Fin m → Bool)),
      ∀ (v : Fin c → Bool) (i : Fin m),
        (∃ j : Fin c, M i j = true ∧ v j = true) ↔
          ∃ s : Fin ((c + b - 1) / b),
            T s (fun o : Fin b => if h : s.val * b + o.val < c then v ⟨s.val * b + o.val, h⟩ else false) i = true := by
  let B := (c + b - 1) / b
  let T : Fin B → (Fin b → Bool) → (Fin m → Bool) := fun s pat i =>
    decide (∃ o : Fin b, ∃ h : s.val * b + o.val < c, M i ⟨s.val * b + o.val, h⟩ = true ∧ pat o = true)
  refine ⟨T, fun v i => ?_⟩
  constructor
  · rintro ⟨j, hM, hv⟩
    have hs_lt : j.val / b < B := by
      have h1 : j.val ≤ c - 1 := by omega
      have h2 : (j.val / b) * b ≤ c - 1 := le_trans (Nat.div_mul_le_self j.val b) h1
      have h3 : (j.val / b + 1) * b ≤ c + b - 1 := by
        have : (j.val / b + 1) * b = (j.val / b) * b + b := by ring
        omega
      have h4 : j.val / b + 1 ≤ B := (Nat.le_div_iff_mul_le hb).mpr h3
      omega
    let s : Fin B := ⟨j.val / b, hs_lt⟩
    let o : Fin b := ⟨j.val % b, Nat.mod_lt j.val hb⟩
    have hEq : s.val * b + o.val = j.val := by
      dsimp only [s, o]
      rw [mul_comm]
      exact Nat.div_add_mod j.val b
    have hlt : s.val * b + o.val < c := by rw [hEq]; exact j.isLt
    refine ⟨s, ?_⟩
    dsimp only [T]
    refine decide_eq_true ⟨o, hlt, ?_, ?_⟩
    · have hj : (⟨s.val * b + o.val, hlt⟩ : Fin c) = j := Fin.ext hEq
      rwa [hj]
    · rw [dif_pos hlt]
      have hj : (⟨s.val * b + o.val, hlt⟩ : Fin c) = j := Fin.ext hEq
      rwa [hj]
  · rintro ⟨s, hT⟩
    dsimp only [T] at hT
    obtain ⟨o, hlt, hM, hv⟩ := of_decide_eq_true hT
    rw [dif_pos hlt] at hv
    exact ⟨⟨s.val * b + o.val, hlt⟩, hM, hv⟩

/-- **PPL 108 / PPL 111 Four-Russians `O(m c / log n)` Speedup & Polynomial Preprocessing (vdBNS19 Theorem `thm:matrixVectorAppendix`):**
For any `n ≥ 4`, choosing block width `b = Nat.log 2 n / 2` gives `b ≥ 1` and `B = (c + b - 1) / b`
satisfying simultaneously:
1. Sublinear-root table blowup `(2 ^ b) ^ 2 ≤ n` (so `2 ^ b ≤ √n`, giving strictly polynomial
   preprocessing `O(m c √n)` in Phase 1 of `v`-Hinted `Mv` and in `Mv`/`OMv`), and
2. Logarithmic query speedup `B * Nat.log 2 n ≤ 3 * (c + Nat.log 2 n)` (yielding `m * B = O(m c / log n)`
   Boolean table lookups per query, with zero computation in Phase 2 of `v`-Hinted `Mv`). -/
theorem ppl108_four_russians_log_speedup (c n : ℕ) (hn : 4 ≤ n) :
    let b := Nat.log 2 n / 2
    let B := (c + b - 1) / b
    1 ≤ b ∧ (2 ^ b) ^ 2 ≤ n ∧ B * Nat.log 2 n ≤ 3 * (c + Nat.log 2 n) := by
  intro b B
  have hlog2 : 2 ≤ Nat.log 2 n := by
    have h2 : 2 ^ 2 ≤ n := by omega
    exact (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr h2
  have hb1 : 1 ≤ b := by dsimp only [b]; omega
  have hpow : (2 ^ b) ^ 2 ≤ n := by
    rw [← pow_mul]
    have h2b : b * 2 ≤ Nat.log 2 n := by dsimp only [b]; omega
    calc 2 ^ (b * 2)
      _ ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by omega) h2b
      _ ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hspeed : B * Nat.log 2 n ≤ 3 * (c + Nat.log 2 n) := by
    have hBub : B ≤ c / b + 1 := by
      have hrem : b * (c / b) + c % b = c := Nat.div_add_mod c b
      have hmod : c % b < b := Nat.mod_lt c hb1
      have hlt : c + b - 1 < (c / b + 2) * b := by
        have : (c / b + 2) * b = b * (c / b) + 2 * b := by ring
        omega
      have hdiv : B < c / b + 2 := (Nat.div_lt_iff_lt_mul hb1).mpr hlt
      omega
    have hlog_le : Nat.log 2 n ≤ 3 * b := by dsimp only [b]; omega
    have hmul : B * Nat.log 2 n ≤ (c / b + 1) * (3 * b) := Nat.mul_le_mul hBub hlog_le
    have hcb : (c / b) * b ≤ c := Nat.div_mul_le_self c b
    have hblog : b ≤ Nat.log 2 n := by dsimp only [b]; omega
    nlinarith
  exact ⟨hb1, hpow, hspeed⟩

/-! ### Section 5: Exact Combinatorial Reductions (`Mv`, `v`-Hinted `Mv`, `OMv`, `OuMv`, `IndepSet`) -/

/-- **PPL 108 Reduction (`Mv` breaks `v`-Hinted `Mv`, vdBNS19 Appendix Theorem):**
Every `n × t` Boolean matrix `M` (`1 ≤ t`) decomposes into `k = (n + t - 1) / t` square `t × t`
Boolean matrices `blocks : Fin k → Matrix (Fin t) (Fin t) Bool` such that for EVERY hint matrix
`V : Matrix (Fin t) (Fin n) Bool`, query index `q : Fin n`, and row `i : Fin n`, the `i`-th entry
of `M V_{:, q}` equals the `(i % t)`-th entry of `blocks (i / t) * V_{:, q}`.
Thus any `O(t^{2 - ε})` algorithm for square `t × t` Boolean `Mv` (with polynomial preprocessing)
solves `v`-Hinted `Mv` with zero Phase 2 computation and `O((n / t) * t^{2 - ε}) = O(n t^{1 - ε})`
Phase 3 time, refuting Conjecture 5.2 (PPL 108). -/
theorem ppl108_mv_to_vhinted_mv_block_reduction (n t : ℕ) (ht : 1 ≤ t)
    (M : Matrix (Fin n) (Fin t) Bool) :
    ∃ blocks : Fin ((n + t - 1) / t) → Matrix (Fin t) (Fin t) Bool,
      ((n + t - 1) / t) * t < n + t ∧
      ∀ (V : Matrix (Fin t) (Fin n) Bool) (q i : Fin n) (hi : i.val / t < (n + t - 1) / t),
        (∃ j : Fin t, M i j = true ∧ V j q = true) ↔
          (∃ j : Fin t, blocks ⟨i.val / t, hi⟩ ⟨i.val % t, Nat.mod_lt i.val ht⟩ j = true ∧ V j q = true) := by
  let k := (n + t - 1) / t
  let blocks : Fin k → Matrix (Fin t) (Fin t) Bool := fun s r j =>
    if h : s.val * t + r.val < n then M ⟨s.val * t + r.val, h⟩ j else false
  refine ⟨blocks, ?_, fun V q i hi => ?_⟩
  · have hdiv : k * t ≤ n + t - 1 := Nat.div_mul_le_self (n + t - 1) t
    dsimp only [k] at hdiv
    omega
  · have hEq : (i.val / t) * t + i.val % t = i.val := by
      rw [mul_comm]; exact Nat.div_add_mod i.val t
    have hlt : (i.val / t) * t + i.val % t < n := by rw [hEq]; exact i.isLt
    have hrow : (⟨(i.val / t) * t + i.val % t, hlt⟩ : Fin n) = i := Fin.ext hEq
    refine exists_congr fun j => ?_
    simp only [blocks, dif_pos hlt, hrow]

/-- **PPL 111 Exact Reduction (`uMv` ↔ Symmetric Loopless Independent Set / Edge Query, HKNS15 Theorem `equiv ouMv`):**
Every rectangular `m × n` Boolean `uMv` instance `(M, u, v)` reduces 1-to-1 to a symmetric loopless
`(m + n) × (m + n)` quadratic form `wᵀ A w` (where `w = (u, v)` is NOT an independent set in the
undirected bipartite graph `A` iff `uᵀ M v = true`). -/
theorem ppl108_umv_to_symmetric_indep_set_reduction (m n : ℕ)
    (M : Matrix (Fin m) (Fin n) Bool) :
    ∃ A : Matrix (Fin (m + n)) (Fin (m + n)) Bool,
      (∀ a b : Fin (m + n), A a b = A b a) ∧
      (∀ a : Fin (m + n), A a a = false) ∧
      ∀ (u : Fin m → Bool) (v : Fin n → Bool),
        let w : Fin (m + n) → Bool := fun x =>
          if h : x.val < m then u ⟨x.val, h⟩ else v ⟨x.val - m, by omega⟩
        (∃ i : Fin m, ∃ j : Fin n, u i = true ∧ M i j = true ∧ v j = true) ↔
          (∃ a b : Fin (m + n), w a = true ∧ A a b = true ∧ w b = true) := by
  let A : Matrix (Fin (m + n)) (Fin (m + n)) Bool := fun a b =>
    if ha : a.val < m then
      if hb : b.val < m then false else M ⟨a.val, ha⟩ ⟨b.val - m, by omega⟩
    else
      if hb : b.val < m then M ⟨b.val, hb⟩ ⟨a.val - m, by omega⟩ else false
  refine ⟨A, ?_, ?_, fun u v => ?_⟩
  · intro a b
    dsimp only [A]
    split_ifs <;> rfl
  · intro a
    dsimp only [A]
    split_ifs <;> rfl
  · dsimp only
    constructor
    · rintro ⟨i, j, hu, hM, hv⟩
      let a : Fin (m + n) := ⟨i.val, by omega⟩
      let b : Fin (m + n) := ⟨m + j.val, by omega⟩
      refine ⟨a, b, ?_, ?_, ?_⟩
      · simp [a, i.isLt, hu]
      · have hnot : ¬ (m + j.val < m) := by omega
        have hsub : (⟨m + j.val - m, by omega⟩ : Fin n) = j := Fin.ext (by dsimp only; omega)
        simp only [A, a, b, dif_pos i.isLt, dif_neg hnot, hsub, hM]
      · have hnot : ¬ (m + j.val < m) := by omega
        have hsub : (⟨m + j.val - m, by omega⟩ : Fin n) = j := Fin.ext (by dsimp only; omega)
        simp only [b, dif_neg hnot, hsub, hv]
    · rintro ⟨a, b, hwa, hA, hwb⟩
      dsimp only [A] at hA
      by_cases ha : a.val < m
      · by_cases hb : b.val < m
        · simp [dif_pos ha, dif_pos hb] at hA
        · rw [dif_pos ha, dif_neg hb] at hA
          rw [dif_pos ha] at hwa
          rw [dif_neg hb] at hwb
          exact ⟨⟨a.val, ha⟩, ⟨b.val - m, by omega⟩, hwa, hA, hwb⟩
      · by_cases hb : b.val < m
        · rw [dif_neg ha, dif_pos hb] at hA
          rw [dif_neg ha] at hwa
          rw [dif_pos hb] at hwb
          exact ⟨⟨b.val, hb⟩, ⟨a.val - m, by omega⟩, hwb, hA, hwa⟩
        · simp [dif_neg ha, dif_neg hb] at hA

/-- State for the HKNS15 adaptive row-deletion + binary-search witness algorithm on one row-block
of `s` rows across `g` column-blocks of size `s × s`. -/
private structure RowSearchState (s : ℕ) where
  colBlk : ℕ
  found : Fin s → Bool
  searching : Bool
  lo : ℕ
  hi : ℕ

/-- Next `(colBlk, uMask)` query issued by a row-block state (independent of the matrix `M`!). -/
private def rowQuery {g s : ℕ} (hg : 0 < g) (st : RowSearchState s) : Fin g × (Fin s → Bool) :=
  if h : st.colBlk < g then
    if st.searching then
      let mid := (st.lo + st.hi) / 2
      (⟨st.colBlk, h⟩, fun r => !st.found r && decide (st.lo ≤ r.val ∧ r.val < mid))
    else
      (⟨st.colBlk, h⟩, fun r => !st.found r)
  else
    (⟨0, hg⟩, fun _ => false)

/-- Deterministic state update given the single Boolean answer `ans` from the `s × s` `uMv` oracle. -/
private def rowStep (g : ℕ) {s : ℕ} (st : RowSearchState s) (ans : Bool) : RowSearchState s :=
  if st.colBlk < g then
    if st.searching then
      let mid := (st.lo + st.hi) / 2
      if ans then
        if mid - st.lo ≤ 1 then
          ⟨st.colBlk, fun r => if r.val = st.lo then true else st.found r, false, 0, s⟩
        else
          ⟨st.colBlk, st.found, true, st.lo, mid⟩
      else
        if st.hi - mid ≤ 1 then
          ⟨st.colBlk, fun r => if r.val = mid then true else st.found r, false, 0, s⟩
        else
          ⟨st.colBlk, st.found, true, mid, st.hi⟩
    else
      if ans then
        if s ≤ 1 then
          ⟨st.colBlk, fun r => if r.val = 0 then true else st.found r, false, 0, s⟩
        else
          ⟨st.colBlk, st.found, true, 0, s⟩
      else
        ⟨st.colBlk + 1, st.found, false, 0, s⟩
  else st

private def rowInit (s : ℕ) : RowSearchState s :=
  ⟨0, fun _ => false, false, 0, s⟩

private def rowUnfound {s : ℕ} (st : RowSearchState s) : ℕ :=
  (Finset.univ.filter fun r : Fin s => st.found r = false).card

private def rowPot (g s : ℕ) (st : RowSearchState s) : ℕ :=
  if st.searching then
    (g - st.colBlk) + (rowUnfound st - 1) * (Nat.clog 2 s + 1) + Nat.clog 2 (st.hi - st.lo)
  else
    (g - st.colBlk) + rowUnfound st * (Nat.clog 2 s + 1)

private lemma rowUnfound_mark {s : ℕ} (found : Fin s → Bool) (r₀ : Fin s) (hr₀ : found r₀ = false) :
    (Finset.univ.filter fun r : Fin s => (if r.val = r₀.val then true else found r) = false).card + 1 =
      (Finset.univ.filter fun r : Fin s => found r = false).card := by
  let S := Finset.univ.filter fun r : Fin s => found r = false
  let S' := Finset.univ.filter fun r : Fin s => (if r.val = r₀.val then true else found r) = false
  have hmem : r₀ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr₀⟩
  have hEq : S' = S.erase r₀ := by
    ext r
    simp only [S', S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases h : r = r₀
    · subst h; simp
    · have hval : r.val ≠ r₀.val := fun hv => h (Fin.ext hv)
      simp [h, hval]
  change S'.card + 1 = S.card
  rw [hEq, Finset.card_erase_add_one hmem]

/-- Invariant for one row-block `a : Fin g` with row-block matrix slice `B : Fin g → Fin s → Bool`
representing `B b r = (∃ c : Fin s, M (a, r) (b, c) ∧ v (b, c))`. -/
private def RowInv {g s : ℕ} (B : Fin g → Fin s → Bool) (st : RowSearchState s) : Prop :=
  st.colBlk ≤ g ∧
  (∀ r : Fin s, st.found r = true → ∃ b : Fin g, B b r = true) ∧
  (∀ (b : Fin g), b.val < st.colBlk → ∀ r : Fin s, st.found r = false → B b r = false) ∧
  (st.searching = true →
    ∃ hcb : st.colBlk < g, st.lo + 2 ≤ st.hi ∧ st.hi ≤ s ∧
    ∃ r : Fin s, st.lo ≤ r.val ∧ r.val < st.hi ∧ st.found r = false ∧
      B ⟨st.colBlk, hcb⟩ r = true)

private lemma rowStep_preserves_and_decreases {g s : ℕ} (hg : 0 < g) (hs : 1 ≤ s)
    (B : Fin g → Fin s → Bool) (st : RowSearchState s) (hinv : RowInv B st) :
    let q := rowQuery hg st
    let ans : Bool := decide (∃ r : Fin s, q.2 r = true ∧ B q.1 r = true)
    let st' := rowStep g st ans
    RowInv B st' ∧ (st.colBlk < g → rowPot g s st' < rowPot g s st) := by
  intro q ans st'
  rcases hinv with ⟨hcb_le, hsound, hcomp, hsearch⟩
  by_cases hcb : st.colBlk < g
  · by_cases hsr : st.searching = true
    · -- Searching mode
      obtain ⟨_, hlo2, hhi_le, r_wit, hr_lo, hr_hi, hr_unfound, hr_B⟩ := hsearch hsr
      let mid := (st.lo + st.hi) / 2
      have hmid_gt : st.lo < mid := by dsimp only [mid]; omega
      have hmid_lt : mid < st.hi := by dsimp only [mid]; omega
      have hq_eq : q = (⟨st.colBlk, hcb⟩, fun r => !st.found r && decide (st.lo ≤ r.val ∧ r.val < mid)) := by
        simp [q, rowQuery, dif_pos hcb, hsr, mid]
      have hclog_pos : 1 ≤ Nat.clog 2 (st.hi - st.lo) := by
        have : 1 < st.hi - st.lo := by omega
        rw [Nat.clog_of_one_lt (by omega : 1 < 2) this]
        omega
      have hunf_pos : 1 ≤ rowUnfound st := by
        refine Finset.card_pos.mpr ⟨r_wit, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr_unfound⟩⟩
      by_cases hans : ans = true
      · -- Witness lies in [lo, mid)
        have hleft_wit : ∃ r : Fin s, st.lo ≤ r.val ∧ r.val < mid ∧ st.found r = false ∧
            B ⟨st.colBlk, hcb⟩ r = true := by
          dsimp only [ans] at hans
          obtain ⟨r, hqr, hBr⟩ := of_decide_eq_true hans
          rw [hq_eq] at hqr hBr
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hqr
          exact ⟨r, hqr.2.1, hqr.2.2, hqr.1, hBr⟩
        obtain ⟨rL, hrL_lo, hrL_mid, hrL_unf, hrL_B⟩ := hleft_wit
        by_cases hlen : mid - st.lo ≤ 1
        · -- Found exact witness rL with rL.val = st.lo!
          have hrL_eq : rL.val = st.lo := by omega
          have hst'_eq : st' = ⟨st.colBlk, fun r => if r.val = st.lo then true else st.found r, false, 0, s⟩ := by
            simp only [st', rowStep, if_pos hcb, if_pos hsr, if_pos hans, if_pos hlen, mid]
          rw [hst'_eq]
          refine ⟨⟨hcb_le, ?_, ?_, fun h => Bool.noConfusion h⟩, fun _ => ?_⟩
          · intro r hr
            by_cases hreq : r.val = st.lo
            · have : r = rL := Fin.ext (by omega)
              exact ⟨⟨st.colBlk, hcb⟩, this ▸ hrL_B⟩
            · simp only [if_neg hreq] at hr
              exact hsound r hr
          · intro b hb r hr
            by_cases hreq : r.val = st.lo
            · simp [hreq] at hr
            · simp only [if_neg hreq] at hr
              exact hcomp b hb r hr
          · simp only [rowPot, if_pos hsr, Bool.false_eq_true, ↓reduceIte]
            have hunf_eq : rowUnfound ⟨st.colBlk, fun r => if r.val = st.lo then true else st.found r, false, 0, s⟩ + 1 =
                rowUnfound st := by
              simpa [rowUnfound, hrL_eq] using rowUnfound_mark st.found rL hrL_unf
            have hsub : rowUnfound ⟨st.colBlk, fun r => if r.val = st.lo then true else st.found r, false, 0, s⟩ =
                rowUnfound st - 1 := by omega
            rw [hsub]
            omega
        · -- Continue binary search on [lo, mid)
          have hst'_eq : st' = ⟨st.colBlk, st.found, true, st.lo, mid⟩ := by
            simp only [st', rowStep, if_pos hcb, if_pos hsr, if_pos hans, if_neg hlen, mid]
          rw [hst'_eq]
          refine ⟨⟨hcb_le, hsound, hcomp, fun _ => ⟨hcb, by dsimp only; omega, by dsimp only; omega, rL, hrL_lo, hrL_mid, hrL_unf, hrL_B⟩⟩, fun _ => ?_⟩
          simp only [rowPot, if_pos hsr, ↓reduceIte, rowUnfound]
          have hclog_lt : Nat.clog 2 (mid - st.lo) < Nat.clog 2 (st.hi - st.lo) := by
            have h1 : 1 < st.hi - st.lo := by omega
            rw [Nat.clog_of_one_lt (by omega : 1 < 2) h1]
            have hle : mid - st.lo ≤ (st.hi - st.lo + 1) / 2 := by dsimp only [mid]; omega
            exact Nat.lt_succ_of_le (Nat.clog_mono_right 2 hle)
          omega
      · -- ans = false: no witness in [lo, mid), so r_wit MUST lie in [mid, hi)!
        have hansF : ans = false := Bool.eq_false_iff.mpr hans
        have hno_left : ∀ r : Fin s, st.lo ≤ r.val → r.val < mid → st.found r = false →
            B ⟨st.colBlk, hcb⟩ r = false := by
          intro r h1 h2 h3
          cases hB : B ⟨st.colBlk, hcb⟩ r
          · rfl
          · exfalso
            apply hans
            dsimp only [ans]
            refine decide_eq_true ⟨r, ?_, ?_⟩
            · rw [hq_eq]; simp [h1, h2, h3]
            · rw [hq_eq]; exact hB
        have hr_ge_mid : mid ≤ r_wit.val := by
          by_contra hlt
          have hF := hno_left r_wit hr_lo (by omega) hr_unfound
          rw [hr_B] at hF; cases hF
        by_cases hlen : st.hi - mid ≤ 1
        · -- Found exact witness r_wit with r_wit.val = mid!
          have hr_eq : r_wit.val = mid := by omega
          have hst'_eq : st' = ⟨st.colBlk, fun r => if r.val = mid then true else st.found r, false, 0, s⟩ := by
            simp only [st', rowStep, if_pos hcb, if_pos hsr, hansF, Bool.false_eq_true, ↓reduceIte, if_pos hlen, mid]
          rw [hst'_eq]
          refine ⟨⟨hcb_le, ?_, ?_, fun h => Bool.noConfusion h⟩, fun _ => ?_⟩
          · intro r hr
            by_cases hreq : r.val = mid
            · have : r = r_wit := Fin.ext (by omega)
              exact ⟨⟨st.colBlk, hcb⟩, this ▸ hr_B⟩
            · simp only [if_neg hreq] at hr
              exact hsound r hr
          · intro b hb r hr
            by_cases hreq : r.val = mid
            · simp [hreq] at hr
            · simp only [if_neg hreq] at hr
              exact hcomp b hb r hr
          · simp only [rowPot, if_pos hsr, Bool.false_eq_true, ↓reduceIte]
            have hunf_eq : rowUnfound ⟨st.colBlk, fun r => if r.val = mid then true else st.found r, false, 0, s⟩ + 1 =
                rowUnfound st := by
              simpa [rowUnfound, hr_eq] using rowUnfound_mark st.found r_wit hr_unfound
            have hsub : rowUnfound ⟨st.colBlk, fun r => if r.val = mid then true else st.found r, false, 0, s⟩ =
                rowUnfound st - 1 := by omega
            rw [hsub]
            omega
        · -- Continue binary search on [mid, hi)
          have hst'_eq : st' = ⟨st.colBlk, st.found, true, mid, st.hi⟩ := by
            simp only [st', rowStep, if_pos hcb, if_pos hsr, hansF, Bool.false_eq_true, ↓reduceIte, if_neg hlen, mid]
          rw [hst'_eq]
          refine ⟨⟨hcb_le, hsound, hcomp, fun _ => ⟨hcb, by dsimp only; omega, hhi_le, r_wit, hr_ge_mid, hr_hi, hr_unfound, hr_B⟩⟩, fun _ => ?_⟩
          simp only [rowPot, if_pos hsr, ↓reduceIte, rowUnfound]
          have hclog_lt : Nat.clog 2 (st.hi - mid) < Nat.clog 2 (st.hi - st.lo) := by
            have h1 : 1 < st.hi - st.lo := by omega
            rw [Nat.clog_of_one_lt (by omega : 1 < 2) h1]
            have hle : st.hi - mid ≤ (st.hi - st.lo + 1) / 2 := by dsimp only [mid]; omega
            exact Nat.lt_succ_of_le (Nat.clog_mono_right 2 hle)
          omega
    · -- Non-searching mode: testing full active mask on block colBlk
      have hsrF : st.searching = false := Bool.eq_false_iff.mpr hsr
      have hq_eq : q = (⟨st.colBlk, hcb⟩, fun r => !st.found r) := by
        simp [q, rowQuery, dif_pos hcb, hsrF]
      by_cases hans : ans = true
      · -- Witness exists in block colBlk!
        have hans' : decide (∃ r : Fin s, q.2 r = true ∧ B q.1 r = true) = true := hans
        obtain ⟨r_wit, hqr, hBr⟩ := of_decide_eq_true hans'
        rw [hq_eq] at hqr hBr
        simp only [Bool.not_eq_true'] at hqr
        have hunf_pos : 1 ≤ rowUnfound st :=
          Finset.card_pos.mpr ⟨r_wit, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqr⟩⟩
        by_cases hs1 : s ≤ 1
        · have hr0 : r_wit.val = 0 := by omega
          have hst'_eq : st' = ⟨st.colBlk, fun r => if r.val = 0 then true else st.found r, false, 0, s⟩ := by
            simp only [st', rowStep, if_pos hcb, hsrF, Bool.false_eq_true, ↓reduceIte, if_pos hans, if_pos hs1]
          rw [hst'_eq]
          refine ⟨⟨hcb_le, ?_, ?_, fun h => Bool.noConfusion h⟩, fun _ => ?_⟩
          · intro r hr
            by_cases hreq : r.val = 0
            · have : r = r_wit := Fin.ext (by omega)
              exact ⟨⟨st.colBlk, hcb⟩, this ▸ hBr⟩
            · simp only [if_neg hreq] at hr
              exact hsound r hr
          · intro b hb r hr
            by_cases hreq : r.val = 0
            · simp [hreq] at hr
            · simp only [if_neg hreq] at hr
              exact hcomp b hb r hr
          · simp only [rowPot, hsrF, Bool.false_eq_true, ↓reduceIte]
            have hunf_eq : rowUnfound ⟨st.colBlk, fun r => if r.val = 0 then true else st.found r, false, 0, s⟩ + 1 =
                rowUnfound st := by
              simpa [rowUnfound, hr0] using rowUnfound_mark st.found r_wit hqr
            nlinarith
        · -- s ≥ 2: enter binary search on [0, s)!
          have hst'_eq : st' = ⟨st.colBlk, st.found, true, 0, s⟩ := by
            simp only [st', rowStep, if_pos hcb, hsrF, Bool.false_eq_true, ↓reduceIte, if_pos hans, if_neg hs1]
          rw [hst'_eq]
          refine ⟨⟨hcb_le, hsound, hcomp, fun _ => ⟨hcb, by dsimp only; omega, le_rfl, r_wit, Nat.zero_le _, r_wit.isLt, hqr, hBr⟩⟩, fun _ => ?_⟩
          simp only [rowPot, hsrF, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero]
          have hmul : rowUnfound st * (Nat.clog 2 s + 1) =
              (rowUnfound st - 1) * (Nat.clog 2 s + 1) + (Nat.clog 2 s + 1) := by
            cases h : rowUnfound st with
            | zero => omega
            | succ k => simp [Nat.succ_mul]
          have hsame : rowUnfound ⟨st.colBlk, st.found, true, 0, s⟩ = rowUnfound st := rfl
          rw [hsame]
          omega
      · -- ans = false: advance colBlk by 1!
        have hansF : ans = false := Bool.eq_false_iff.mpr hans
        have hno_blk : ∀ r : Fin s, st.found r = false → B ⟨st.colBlk, hcb⟩ r = false := by
          intro r hr
          cases hB : B ⟨st.colBlk, hcb⟩ r
          · rfl
          · exfalso
            apply hans
            dsimp only [ans]
            refine decide_eq_true ⟨r, ?_, ?_⟩
            · rw [hq_eq]; simp [hr]
            · rw [hq_eq]; exact hB
        have hst'_eq : st' = ⟨st.colBlk + 1, st.found, false, 0, s⟩ := by
          simp only [st', rowStep, if_pos hcb, hsrF, hansF, Bool.false_eq_true, ↓reduceIte]
        rw [hst'_eq]
        refine ⟨⟨by dsimp only; omega, hsound, ?_, fun h => Bool.noConfusion h⟩, fun _ => ?_⟩
        · intro b hb r hr
          dsimp only at hb
          by_cases hlt : b.val < st.colBlk
          · exact hcomp b hlt r hr
          · have hEq : b = ⟨st.colBlk, hcb⟩ := Fin.ext (by dsimp only; omega)
            rw [hEq]
            exact hno_blk r hr
        · simp only [rowPot, hsrF, Bool.false_eq_true, ↓reduceIte]
          have hsame : rowUnfound ⟨st.colBlk + 1, st.found, false, 0, s⟩ = rowUnfound st := rfl
          rw [hsame]
          omega
  · -- Already finished (colBlk = g): state unchanged
    have hst'_eq : st' = st := by simp only [st', rowStep, if_neg hcb]
    rw [hst'_eq]
    exact ⟨⟨hcb_le, hsound, hcomp, hsearch⟩, fun h => absurd h hcb⟩

/-- Replay a chronological list of oracle answers for one row-block. -/
private def replayRow (g : ℕ) {s : ℕ} (answers : List Bool) : RowSearchState s :=
  answers.foldl (rowStep g) (rowInit s)

private lemma replayRow_inv_and_pot {g s : ℕ} (hg : 0 < g) (hs : 1 ≤ s)
    (B : Fin g → Fin s → Bool) (k : ℕ) :
    let hist := (fun h : List Bool =>
      let st := replayRow g (s := s) h.reverse
      let q := rowQuery hg st
      decide (∃ r : Fin s, q.2 r = true ∧ B q.1 r = true) :: h)^[k] []
    let st := replayRow g (s := s) hist.reverse
    RowInv B st ∧ (st.colBlk = g ∨ rowPot g s st + k ≤ g + s * (Nat.clog 2 s + 1)) := by
  induction k with
  | zero =>
    dsimp only [Function.iterate_zero, id_eq, List.reverse_nil, replayRow, List.foldl_nil]
    refine ⟨⟨Nat.zero_le _, fun _ h => Bool.noConfusion h, fun _ hb => by simp [rowInit] at hb, fun h => Bool.noConfusion h⟩, ?_⟩
    right
    simp [rowPot, rowInit, rowUnfound]
  | succ k ih =>
    dsimp only
    set hist := (fun h : List Bool =>
      let st := replayRow g (s := s) h.reverse
      let q := rowQuery hg st
      decide (∃ r : Fin s, q.2 r = true ∧ B q.1 r = true) :: h)^[k] []
    set st := replayRow g (s := s) hist.reverse
    set q := rowQuery hg st
    set ans : Bool := decide (∃ r : Fin s, q.2 r = true ∧ B q.1 r = true)
    have hstep_hist : (fun h : List Bool =>
        let st := replayRow g (s := s) h.reverse
        let q := rowQuery hg st
        decide (∃ r : Fin s, q.2 r = true ∧ B q.1 r = true) :: h)^[k + 1] [] = ans :: hist := by
      rw [Function.iterate_succ_apply']
    have hstep_st : replayRow g (s := s) (ans :: hist).reverse = rowStep g st ans := by
      simp only [replayRow, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, st]
    rw [hstep_hist, hstep_st]
    have hih : RowInv B st ∧ (st.colBlk = g ∨ rowPot g s st + k ≤ g + s * (Nat.clog 2 s + 1)) := ih
    obtain ⟨hinv, hpot⟩ := hih
    have hstep_res : RowInv B (rowStep g st ans) ∧ (st.colBlk < g → rowPot g s (rowStep g st ans) < rowPot g s st) :=
      rowStep_preserves_and_decreases hg hs B st hinv
    obtain ⟨hinv', hdec⟩ := hstep_res
    refine ⟨hinv', ?_⟩
    by_cases hcb : st.colBlk < g
    · have hlt := hdec hcb
      rcases hpot with hdone | hle
      · omega
      · right; omega
    · have hdone : st.colBlk = g := by have := hinv.1; omega
      left
      simp [rowStep, hdone]

/-- **PPL 111 Exact Adaptive Reduction (`OMv` → Square `OuMv`, HKNS15 STOC 2015 Theorem `ouMv hard`):**
For any `g, s ≥ 1`, let `Q = g * (g + s * (Nat.clog 2 s + 1))`.
There exist matrix-independent adaptive oracle query/output functions `(ask, ans)` that interact
with ANY `(g * s) × (g * s)` Boolean matrix `M` **solely** through `Q` adaptive calls to the
`s × s` square block `uMv` oracle `(a, b, u, w) ↦ ∃ r c : Fin s, u r ∧ M (a*s + r, b*s + c) ∧ w c`,
and compute the exact Boolean matrix-vector product `M v` for every `v : Fin (g * s) → Bool`.
Setting `g = s = √n` yields `Q = O(n log n)` calls to `√n × √n` square `uMv`, proving that any
`O(n^{2 - ε})` algorithm for square `OuMv` refutes the `OMv` Conjecture (PPL 111). -/
theorem ppl108_omv_to_square_oumv_reduction (g s : ℕ) (hg : 1 ≤ g) (hs : 1 ≤ s) :
    let Q := g * (g + s * (Nat.clog 2 s + 1))
    ∃ (ask : (Fin (g * s) → Bool) → List Bool → Fin g × Fin g × (Fin s → Bool) × (Fin s → Bool))
      (ans : (Fin (g * s) → Bool) → List Bool → (Fin (g * s) → Bool)),
      ∀ (M : Matrix (Fin (g * s)) (Fin (g * s)) Bool) (v : Fin (g * s) → Bool) (i : Fin (g * s)),
        let oracle : Fin g × Fin g × (Fin s → Bool) × (Fin s → Bool) → Bool := fun q =>
          decide (∃ r c : Fin s,
            q.2.2.1 r = true ∧
            M ⟨q.1.val * s + r.val, by
                have h1 : (q.1.val + 1) * s ≤ g * s := Nat.mul_le_mul_right s q.1.isLt
                nlinarith [r.isLt]⟩
              ⟨q.2.1.val * s + c.val, by
                have h1 : (q.2.1.val + 1) * s ≤ g * s := Nat.mul_le_mul_right s q.2.1.isLt
                nlinarith [c.isLt]⟩ = true ∧
            q.2.2.2 c = true)
        ans v ((fun hist : List Bool => oracle (ask v hist) :: hist)^[Q] []) i = true ↔
          ∃ j : Fin (g * s), M i j = true ∧ v j = true := by
  intro Q
  have hgpos : 0 < g := by omega
  have hspos : 0 < s := by omega
  let qRow := g + s * (Nat.clog 2 s + 1)
  have hqRow_pos : 0 < qRow := by dsimp only [qRow]; omega
  let vSlice : (Fin (g * s) → Bool) → Fin g → Fin s → Bool := fun v b c =>
    v ⟨b.val * s + c.val, by
      have h1 : (b.val + 1) * s ≤ g * s := Nat.mul_le_mul_right s b.isLt
      nlinarith [c.isLt]⟩
  -- ask decodes which row-block `a = hist.length / qRow` is active and replays its slice of `hist.reverse`!
  let ask : (Fin (g * s) → Bool) → List Bool → Fin g × Fin g × (Fin s → Bool) × (Fin s → Bool) :=
    fun v hist =>
      let step := hist.length
      if h : step < Q then
        let a : Fin g := ⟨step / qRow, (Nat.div_lt_iff_lt_mul hqRow_pos).mpr h⟩
        let localHist := (hist.reverse.drop (a.val * qRow))
        let st := replayRow g (s := s) localHist
        let q := rowQuery hgpos st
        (a, q.1, q.2, vSlice v q.1)
      else
        (⟨0, hgpos⟩, ⟨0, hgpos⟩, fun _ => false, fun _ => false)
  let ans : (Fin (g * s) → Bool) → List Bool → (Fin (g * s) → Bool) := fun _ hist i =>
    let a : Fin g := ⟨i.val / s, (Nat.div_lt_iff_lt_mul hspos).mpr i.isLt⟩
    let r : Fin s := ⟨i.val % s, Nat.mod_lt i.val hspos⟩
    let slice := (hist.reverse.drop (a.val * qRow)).take qRow
    (replayRow g (s := s) slice).found r
  refine ⟨ask, ans, fun M v i => ?_⟩
  intro oracle
  let stepFn : List Bool → List Bool := fun hist => oracle (ask v hist) :: hist
  have hlen_step : ∀ k, (stepFn^[k] []).length = k := fun k => iter_list_length (fun h => oracle (ask v h)) k
  -- Helper: row-block summary B a b r = ∃ c, M (a*s + r, b*s + c) ∧ v (b*s + c)
  let B : Fin g → Fin g → Fin s → Bool := fun a b r =>
    decide (∃ c : Fin s,
      M ⟨a.val * s + r.val, by
          have h1 : (a.val + 1) * s ≤ g * s := Nat.mul_le_mul_right s a.isLt
          nlinarith [r.isLt]⟩
        ⟨b.val * s + c.val, by
          have h1 : (b.val + 1) * s ≤ g * s := Nat.mul_le_mul_right s b.isLt
          nlinarith [c.isLt]⟩ = true ∧
      vSlice v b c = true)
  -- For each row-block `a : Fin g` and `k ≤ qRow`, the suffix of `(stepFn^[a*qRow + k] []).reverse`
  -- starting at `a * qRow` equals the standalone `k`-step row-block history!
  let rowStepFn : Fin g → List Bool → List Bool := fun a h =>
    let st := replayRow g (s := s) h.reverse
    let q := rowQuery hgpos st
    decide (∃ r : Fin s, q.2 r = true ∧ B a q.1 r = true) :: h
  have hprefix_rev : ∀ m₁ m₂, m₁ ≤ m₂ → (stepFn^[m₁] []).reverse <+: (stepFn^[m₂] []).reverse := by
    intro m₁ m₂ hle
    induction hle with
    | refl => exact List.prefix_refl _
    | @step k _ ih =>
      refine ih.trans ?_
      rw [Function.iterate_succ_apply']
      simp only [stepFn, List.reverse_cons]
      exact List.prefix_append _ _
  have hblock_match : ∀ (a : Fin g) (k : ℕ), k ≤ qRow →
      (stepFn^[a.val * qRow + k] []).reverse.drop (a.val * qRow) = ((rowStepFn a)^[k] []).reverse := by
    intro a k
    induction k with
    | zero =>
      intro _
      have hlen : (stepFn^[a.val * qRow] []).reverse.length = a.val * qRow := by
        rw [List.length_reverse, hlen_step]
      simp [List.drop_eq_nil_of_le (le_of_eq hlen)]
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hltQ : a.val * qRow + k < Q := by
        have h1 : (a.val + 1) * qRow ≤ Q := Nat.mul_le_mul_right qRow a.isLt
        have h2 : a.val * qRow + k < (a.val + 1) * qRow := by
          rw [Nat.add_mul, one_mul]
          omega
        exact lt_of_lt_of_le h2 h1
      have hlen_cur : (stepFn^[a.val * qRow + k] []).length = a.val * qRow + k := hlen_step _
      have hdiv : (a.val * qRow + k) / qRow = a.val := by
        rw [mul_comm a.val qRow, Nat.mul_add_div hqRow_pos, Nat.div_eq_of_lt (by omega), add_zero]
      have horacle_eq : oracle (ask v (stepFn^[a.val * qRow + k] [])) =
          decide (∃ r : Fin s,
            (rowQuery hgpos (replayRow g (s := s) ((rowStepFn a)^[k] []).reverse)).2 r = true ∧
            B a (rowQuery hgpos (replayRow g (s := s) ((rowStepFn a)^[k] []).reverse)).1 r = true) := by
        dsimp only [ask]
        rw [hlen_cur, dif_pos hltQ]
        simp only [hdiv]
        rw [hprev]
        dsimp only [oracle, B]
        refine decide_eq_decide.mpr ?_
        constructor
        · rintro ⟨r, c, hr, hM, hv⟩
          exact ⟨r, hr, decide_eq_true ⟨c, hM, hv⟩⟩
        · rintro ⟨r, hr, hB⟩
          obtain ⟨c, hM, hv⟩ := of_decide_eq_true hB
          exact ⟨r, c, hr, hM, hv⟩
      have hstep1 : stepFn^[a.val * qRow + (k + 1)] [] =
          oracle (ask v (stepFn^[a.val * qRow + k] [])) :: stepFn^[a.val * qRow + k] [] := by
        rw [← Nat.add_assoc, Function.iterate_succ_apply']
      rw [hstep1, List.reverse_cons, List.drop_append_of_le_length (by rw [List.length_reverse, hlen_cur]; omega),
          hprev, horacle_eq]
      rw [Function.iterate_succ_apply']
      simp only [rowStepFn, List.reverse_cons]
  -- Now extract slice for row-block `a = i.val / s`!
  let a : Fin g := ⟨i.val / s, (Nat.div_lt_iff_lt_mul hspos).mpr i.isLt⟩
  let r : Fin s := ⟨i.val % s, Nat.mod_lt i.val hspos⟩
  have hleQ : a.val * qRow + qRow ≤ Q := by
    have : (a.val + 1) * qRow ≤ g * qRow := Nat.mul_le_mul_right qRow a.isLt
    dsimp only [Q, qRow] at this ⊢
    nlinarith
  have hslice_eq : ((stepFn^[Q] []).reverse.drop (a.val * qRow)).take qRow =
      ((rowStepFn a)^[qRow] []).reverse := by
    have hpref := hprefix_rev (a.val * qRow + qRow) Q hleQ
    obtain ⟨tail, htail⟩ := hpref
    rw [← htail, List.drop_append_of_le_length (by rw [List.length_reverse, hlen_step]; omega),
        hblock_match a qRow le_rfl]
    have hlen_row : ((rowStepFn a)^[qRow] []).reverse.length = qRow := by
      rw [List.length_reverse]
      exact iter_list_length _ qRow
    rw [List.take_append_of_le_length (le_of_eq hlen_row.symm), List.take_of_length_le (le_of_eq hlen_row)]
  -- Apply replayRow_inv_and_pot at k = qRow!
  obtain ⟨hinv, hpot⟩ := replayRow_inv_and_pot hgpos hs (B a) qRow
  set stFin := replayRow g (s := s) ((rowStepFn a)^[qRow] []).reverse
  have hdone : stFin.colBlk = g := by
    rcases hpot with hdone | hle
    · exact hdone
    · have hpot0 : rowPot g s stFin = 0 := by dsimp only [qRow] at hle; omega
      by_contra hne
      have hcb_lt : stFin.colBlk < g := by have := hinv.1; omega
      have : 0 < rowPot g s stFin := by
        dsimp only [rowPot]
        split_ifs <;> omega
      omega
  dsimp only [ans]
  change (replayRow g (s := s) (((stepFn^[Q] []).reverse.drop (a.val * qRow)).take qRow)).found r = true ↔ _
  rw [hslice_eq]
  change stFin.found r = true ↔ _
  have hrow_idx : (⟨a.val * s + r.val, by
      have h1 : (a.val + 1) * s ≤ g * s := Nat.mul_le_mul_right s a.isLt
      nlinarith [r.isLt]⟩ : Fin (g * s)) = i := by
    apply Fin.ext
    dsimp only [a, r]
    rw [mul_comm]
    exact Nat.div_add_mod i.val s
  constructor
  · intro hfound
    obtain ⟨b, hB⟩ := hinv.2.1 r hfound
    dsimp only [B] at hB
    obtain ⟨c, hM, hv⟩ := of_decide_eq_true hB
    rw [hrow_idx] at hM
    exact ⟨⟨b.val * s + c.val, by
      have h1 : (b.val + 1) * s ≤ g * s := Nat.mul_le_mul_right s b.isLt
      nlinarith [c.isLt]⟩, hM, hv⟩
  · rintro ⟨j, hM, hv⟩
    let b : Fin g := ⟨j.val / s, (Nat.div_lt_iff_lt_mul hspos).mpr j.isLt⟩
    let c : Fin s := ⟨j.val % s, Nat.mod_lt j.val hspos⟩
    have hj_idx : (⟨b.val * s + c.val, by
        have h1 : (b.val + 1) * s ≤ g * s := Nat.mul_le_mul_right s b.isLt
        nlinarith [c.isLt]⟩ : Fin (g * s)) = j := by
      apply Fin.ext
      dsimp only [b, c]
      rw [mul_comm]
      exact Nat.div_add_mod j.val s
    have hBtrue : B a b r = true := by
      dsimp only [B]
      refine decide_eq_true ⟨c, ?_, ?_⟩
      · rw [hrow_idx, hj_idx]; exact hM
      · dsimp only [vSlice]; rw [hj_idx]; exact hv
    cases hf : stFin.found r
    · exfalso
      have hBfalse := hinv.2.2.1 b (by rw [hdone]; exact b.isLt) r hf
      rw [hBtrue] at hBfalse; cases hBfalse
    · rfl

end PPL108
