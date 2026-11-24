/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Computability.DFA
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import RHDirect.Arith4Ext_AutomataCombinatorics
import RHDirect.Arith4Ext_AnalyticNT

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# PPL 161 — Shallit Open Problem #1: Deterministic Separating Words (`sep(n)`)

Formalization of deterministic finite automaton (DFA) word-separation upper bounds,
lower bounds, structural/combinatorial separators, and exact small-`n` values.

All public `theorem` signatures use **100% pure Mathlib types** (`DFA α (Fin m)`, `M.accepts`,
`List α`, `Real.log`, `Real.sqrt`, etc.) with **0 custom or private definitions** in any public
signature, **0 `sorry`**, **0 custom axioms**, and **0 `native_decide`**.

## Main Public Theorems (`namespace PPL161`)
1. `ppl161_prime_modulus_sqrt_log_upper`:
   Algebraic `𝔽₂[X]` prime-modulus cyclotomic separator (`m ≤ 8192 √(n log n)` for all `n ≥ 2`).
2. `ppl161_odd_cyclotomic_sqrt_upper`:
   Robson (1996) permutation-DFA odd-cyclotomic separator (`m ≤ 130 √n` for all `n ≥ 1`,
   with bijective transition maps, sharpening `O(√(n log n))` by `√(log n)`).
3. `ppl161_unequal_length_log_upper`:
   `O(log n)` cyclic length-mod-`p` separator for distinct-length words (`≤ n`).
4. `ppl161_general_le_sqrt_upper`:
   Combined `O(√n)` separator for all distinct words of length `≤ n` (`n ≥ 1`).
5. `ppl161_fine_wilf_periodic_separator`:
   Fine–Wilf periodic-word separator (`≤ p + q - gcd(p, q) + 2` states).
6. `ppl161_kmp_factor_separator`:
   Explicit `(|v| + 1)`-state KMP factor-presence DFA separator.
7. `ppl161_spaced_sub_sqrt_separator`:
   Sub-`√n` separator (`O(√(n / 2^k))`) for `2^k`-spaced mismatch sets via `𝔽₂[X]` cyclotomics.
8. `ppl161_desw_log_lower_bound`:
   Demaine–Eisenstat–Shallit–Wilson (2011) `Ω(log n)` lower bound (`Real.log n / 24 < d` for all `n ≥ 4`),
   realized by explicit Hamming-distance-2 binary words via `lcm(1..t)` unary pumping.
9. `ppl161_hamming_weight_log_separator`:
   `O(log Δ)` separator for words with distinct Hamming weights (`Δ = ||w|_1 - |x|_1|`, giving `O(log h)` when weights differ).
10. `ppl161_hamming_odd_two_state`:
    Exact `2`-state parity separator whenever Hamming distance is odd.
11. `ppl161_hamming_dist_upper`:
    `O(h log n)` separator for binary words of Hamming distance `h` (matching `Ω(log n)` at `h = 2`).
12. `ppl161_exact_sep_one`, `ppl161_exact_sep_two`, `ppl161_exact_sep_three`,
    `ppl161_exact_sep_four_lower`, `ppl161_exact_sep_four_upper`:
    Exact small-`n` separation numbers `sep(1) = sep(2) = sep(3) = 2` and `sep(4) = 3` (`0` `native_decide`).
-/

namespace PPL161

open Finset Polynomial

/-! ## Section 1: Core DFA Constructions & Alphabet Reduction (Private) -/

private def mapDFA {α Q₁ Q₂ : Type*} (e : Q₁ ≃ Q₂) (M : DFA α Q₁) : DFA α Q₂ where
  step q a := e (M.step (e.symm q) a)
  start := e M.start
  accept := e.symm ⁻¹' M.accept

private lemma mapDFA_evalFrom {α Q₁ Q₂ : Type*} (e : Q₁ ≃ Q₂) (M : DFA α Q₁) :
    ∀ (q : Q₁) (u : List α), (mapDFA e M).evalFrom (e q) u = e (M.evalFrom q u)
  | _, [] => rfl
  | q, a :: u => by
    simp only [DFA.evalFrom, List.foldl_cons, mapDFA]
    rw [Equiv.symm_apply_apply]
    exact mapDFA_evalFrom e M (M.step q a) u

private lemma mapDFA_accepts {α Q₁ Q₂ : Type*} (e : Q₁ ≃ Q₂) (M : DFA α Q₁) (u : List α) :
    u ∈ (mapDFA e M).accepts ↔ u ∈ M.accepts := by
  change (mapDFA e M).evalFrom (e M.start) u ∈ (e.symm ⁻¹' M.accept) ↔
    M.evalFrom M.start u ∈ M.accept
  rw [mapDFA_evalFrom, Set.mem_preimage, Equiv.symm_apply_apply]

private lemma mapDFA_bijective {α Q₁ Q₂ : Type*} (e : Q₁ ≃ Q₂) (M : DFA α Q₁)
    (hbij : ∀ a : α, Function.Bijective (fun q => M.step q a)) :
    ∀ a : α, Function.Bijective (fun q => (mapDFA e M).step q a) := by
  intro a
  change Function.Bijective (e ∘ (fun q => M.step q a) ∘ e.symm)
  exact e.bijective.comp ((hbij a).comp e.symm.bijective)

private def pullbackDFA {α β Q : Type*} (f : α → β) (M : DFA β Q) : DFA α Q where
  step q a := M.step q (f a)
  start := M.start
  accept := M.accept

private lemma pullbackDFA_evalFrom {α β Q : Type*} (f : α → β) (M : DFA β Q) :
    ∀ (q : Q) (u : List α), (pullbackDFA f M).evalFrom q u = M.evalFrom q (u.map f)
  | _, [] => rfl
  | q, a :: u => by
    simp only [DFA.evalFrom, List.foldl_cons, List.map_cons, pullbackDFA]
    exact pullbackDFA_evalFrom f M (M.step q (f a)) u

private lemma pullbackDFA_accepts {α β Q : Type*} (f : α → β) (M : DFA β Q) (u : List α) :
    u ∈ (pullbackDFA f M).accepts ↔ u.map f ∈ M.accepts := by
  change (pullbackDFA f M).evalFrom M.start u ∈ M.accept ↔
    M.evalFrom M.start (u.map f) ∈ M.accept
  rw [pullbackDFA_evalFrom]

private lemma pullbackDFA_bijective {α β Q : Type*} (f : α → β) (M : DFA β Q)
    (hbij : ∀ b : β, Function.Bijective (fun q => M.step q b)) :
    ∀ a : α, Function.Bijective (fun q => (pullbackDFA f M).step q a) :=
  fun a => hbij (f a)

private lemma exists_bool_projection {α : Type*} {w x : List α}
    (hlen : w.length = x.length) (hne : w ≠ x) :
    ∃ f : α → Bool, w.map f ≠ x.map f ∧ (w.map f).length = w.length ∧ (x.map f).length = x.length := by
  classical
  have hdiff : ∃ i : ℕ, ∃ hiw : i < w.length, ∃ hix : i < x.length, w[i] ≠ x[i] := by
    by_contra hall
    push Not at hall
    apply hne
    exact List.ext_getElem hlen fun i hiw hix => hall i hiw hix
  rcases hdiff with ⟨i, hiw, hix, hne_i⟩
  let f : α → Bool := fun c => decide (c = w[i])
  refine ⟨f, ?_, List.length_map f, List.length_map f⟩
  intro heq
  have hi_eq := congrArg (fun l => l[i]?) heq
  rw [List.getElem?_map, List.getElem?_map,
      List.getElem?_eq_getElem hiw, List.getElem?_eq_getElem hix] at hi_eq
  simp only [Option.map_some, Option.some.injEq, f] at hi_eq
  simp [decide_eq_false (Ne.symm hne_i)] at hi_eq

private lemma dfa_evalFrom_append {α Q : Type*} (M : DFA α Q) (q : Q) (u v : List α) :
    M.evalFrom q (u ++ v) = M.evalFrom (M.evalFrom q u) v := by
  simp [DFA.evalFrom, List.foldl_append]

private lemma dfa_eval_append {α Q : Type*} (M : DFA α Q) (u v : List α) :
    M.eval (u ++ v) = M.evalFrom (M.eval u) v :=
  dfa_evalFrom_append M M.start u v

private lemma dfa_sep_of_eval_ne {α Q : Type*} (M : DFA α Q) {u v : List α}
    (hne : M.eval u ≠ M.eval v) :
    ∃ M' : DFA α Q, u ∈ M'.accepts ↔ v ∉ M'.accepts := by
  let M' : DFA α Q := {
    step := M.step
    start := M.start
    accept := {M.eval u}
  }
  refine ⟨M', ?_⟩
  change M.eval u ∈ ({M.eval u} : Set Q) ↔ M.eval v ∉ ({M.eval u} : Set Q)
  simp [hne.symm]

/-- Position-checking DFA on `Fin (i + 3)`: accepts iff `u[i]? = some a`. -/
private def posCheckDFA {α : Type*} [DecidableEq α] (i : ℕ) (a : α) : DFA α (Fin (i + 3)) where
  step q c :=
    if h : q.1 < i then
      ⟨q.1 + 1, by omega⟩
    else if q.1 = i then
      if c = a then ⟨i + 1, by omega⟩ else ⟨i + 2, by omega⟩
    else
      q
  start := ⟨0, by omega⟩
  accept := {⟨i + 1, by omega⟩}

private lemma posCheckDFA_eval_lt {α : Type*} [DecidableEq α] (i : ℕ) (a : α) :
    ∀ (u : List α) (hlen : u.length ≤ i),
      (posCheckDFA i a).eval u = ⟨u.length, by omega⟩ := by
  intro u
  induction u using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton u b ih =>
    intro hlen
    have hlen' : u.length + 1 ≤ i := by simpa using hlen
    rw [dfa_eval_append, ih (by omega)]
    change (posCheckDFA i a).step ⟨u.length, by omega⟩ b = ⟨(u ++ [b]).length, by omega⟩
    have hlt : u.length < i := by omega
    simp [posCheckDFA, hlt]

private lemma posCheckDFA_sink {α : Type*} [DecidableEq α] (i : ℕ) (a : α)
    (q : Fin (i + 3)) (hq : i + 1 ≤ q.1) :
    ∀ v : List α, (posCheckDFA i a).evalFrom q v = q
  | [] => rfl
  | b :: v => by
    change (posCheckDFA i a).evalFrom ((posCheckDFA i a).step q b) v = q
    have h1 : ¬ q.1 < i := by omega
    have h2 : q.1 ≠ i := by omega
    have hs : (posCheckDFA i a).step q b = q := by simp [posCheckDFA, h1, h2]
    rw [hs]
    exact posCheckDFA_sink i a q hq v

private lemma posCheckDFA_accepts_iff {α : Type*} [DecidableEq α] (i : ℕ) (a : α)
    (u : List α) (hi : i < u.length) :
    u ∈ (posCheckDFA i a).accepts ↔ u[i] = a := by
  have hdecomp : u = u.take i ++ [u[i]] ++ u.drop (i + 1) := by
    calc u = u.take i ++ u.drop i := (List.take_append_drop i u).symm
      _ = u.take i ++ (u[i] :: u.drop (i + 1)) := by rw [List.drop_eq_getElem_cons hi]
      _ = u.take i ++ [u[i]] ++ u.drop (i + 1) := by simp
  change (posCheckDFA i a).eval u ∈ (posCheckDFA i a).accept ↔ u[i] = a
  conv_lhs => rw [hdecomp]
  rw [dfa_eval_append, dfa_eval_append]
  have htake_len : (u.take i).length = i := List.length_take_of_le (by omega)
  rw [posCheckDFA_eval_lt i a (u.take i) (by omega)]
  have hstep : (posCheckDFA i a).evalFrom ⟨(u.take i).length, by omega⟩ [u[i]] =
      if u[i] = a then ⟨i + 1, by omega⟩ else ⟨i + 2, by omega⟩ := by
    change (posCheckDFA i a).step ⟨(u.take i).length, by omega⟩ u[i] = _
    simp [posCheckDFA, htake_len]
  rw [hstep]
  split_ifs with h
  · rw [posCheckDFA_sink i a ⟨i + 1, by omega⟩ (by simp) (u.drop (i + 1))]
    simp [posCheckDFA, h]
  · rw [posCheckDFA_sink i a ⟨i + 2, by omega⟩ (by simp) (u.drop (i + 1))]
    simp [posCheckDFA, h]

/-- Length-modulo-`p` cyclic DFA on `Fin p` (permutation DFA). -/
private def lenModDFA {α : Type*} (p : ℕ) (hp : 0 < p) (r : Fin p) : DFA α (Fin p) where
  step q _ := ⟨(q.1 + 1) % p, Nat.mod_lt _ hp⟩
  start := ⟨0, hp⟩
  accept := {r}

private lemma lenModDFA_eval {α : Type*} (p : ℕ) (hp : 0 < p) (r : Fin p) :
    ∀ u : List α, (lenModDFA p hp r).eval u = ⟨u.length % p, Nat.mod_lt _ hp⟩ := by
  intro u
  induction u using List.reverseRecOn with
  | nil => simp [DFA.eval, DFA.evalFrom, lenModDFA]
  | append_singleton u b ih =>
    rw [dfa_eval_append, ih]
    change (lenModDFA p hp r).step ⟨u.length % p, Nat.mod_lt _ hp⟩ b =
      ⟨(u ++ [b]).length % p, Nat.mod_lt _ hp⟩
    ext
    simp [lenModDFA, Nat.add_mod]

private lemma lenModDFA_accepts_iff {α : Type*} (p : ℕ) (hp : 0 < p) (r : Fin p) (u : List α) :
    u ∈ (lenModDFA p hp r).accepts ↔ u.length % p = r.1 := by
  change (lenModDFA p hp r).eval u ∈ ({r} : Set (Fin p)) ↔ u.length % p = r.1
  rw [lenModDFA_eval]
  simp [Fin.ext_iff]

/-- `true`-count modulo `p` DFA on `Fin p` (permutation DFA). -/
private def countModDFA (p : ℕ) (hp : 0 < p) (r : Fin p) : DFA Bool (Fin p) where
  step q b := if b then ⟨(q.1 + 1) % p, Nat.mod_lt _ hp⟩ else q
  start := ⟨0, hp⟩
  accept := {r}

private lemma countModDFA_eval (p : ℕ) (hp : 0 < p) (r : Fin p) :
    ∀ u : List Bool, (countModDFA p hp r).eval u = ⟨(u.count true) % p, Nat.mod_lt _ hp⟩ := by
  intro u
  induction u using List.reverseRecOn with
  | nil => simp [DFA.eval, DFA.evalFrom, countModDFA]
  | append_singleton u b ih =>
    rw [dfa_eval_append, ih]
    change (countModDFA p hp r).step ⟨(u.count true) % p, Nat.mod_lt _ hp⟩ b =
      ⟨((u ++ [b]).count true) % p, Nat.mod_lt _ hp⟩
    ext
    cases b <;> simp [countModDFA, List.count_append, Nat.add_mod]

private lemma countModDFA_accepts_iff (p : ℕ) (hp : 0 < p) (r : Fin p) (u : List Bool) :
    u ∈ (countModDFA p hp r).accepts ↔ (u.count true) % p = r.1 := by
  change (countModDFA p hp r).eval u ∈ ({r} : Set (Fin p)) ↔ (u.count true) % p = r.1
  rw [countModDFA_eval]
  simp [Fin.ext_iff]

/-- Cyclic parity DFA on `Fin m × Bool` (`2 * m` states, bijective transitions):
computes `(u.length % m, XOR_{i < u.length, i % m = r} u[i])`. -/
private def cyclicParityProdDFA (m : ℕ) (hm : 0 < m) (r : Fin m) : DFA Bool (Fin m × Bool) where
  step q b := (⟨(q.1.1 + 1) % m, Nat.mod_lt _ hm⟩, xor q.2 (decide (q.1 = r) && b))
  start := (⟨0, hm⟩, false)
  accept := { q | q.2 = true }

private def boolToF2 : Bool → ZMod 2
  | false => 0
  | true => 1

private lemma boolToF2_inj : Function.Injective boolToF2 := by
  intro a b h
  cases a <;> cases b <;> simp [boolToF2] at h ⊢

private lemma boolToF2_xor (a b : Bool) :
    boolToF2 (xor a b) = boolToF2 a + boolToF2 b := by
  cases a <;> cases b <;> decide

private lemma cyclicParityProdDFA_bijective (m : ℕ) (hm : 0 < m) (r : Fin m) :
    ∀ b : Bool, Function.Bijective (fun q => (cyclicParityProdDFA m hm r).step q b) := by
  intro b
  let inv : Fin m × Bool → Fin m × Bool := fun q =>
    let prev : Fin m := ⟨(q.1.1 + m - 1) % m, Nat.mod_lt _ hm⟩
    (prev, xor q.2 (decide (prev = r) && b))
  refine Function.bijective_iff_has_inverse.mpr ⟨inv, ?_, ?_⟩
  · intro ⟨⟨k, hk⟩, par⟩
    have hprev : (⟨((k + 1) % m + m - 1) % m, Nat.mod_lt _ hm⟩ : Fin m) = ⟨k, hk⟩ := by
      apply Fin.ext
      change ((k + 1) % m + m - 1) % m = k
      by_cases hk1 : k + 1 < m
      · rw [Nat.mod_eq_of_lt hk1]
        have h1 : k + 1 + m - 1 = k + m := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
      · have hkm : k + 1 = m := by omega
        rw [hkm, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
        omega
    simp only [cyclicParityProdDFA, inv]
    ext
    · exact congrArg Fin.val hprev
    · rw [hprev]
      cases par <;> cases (decide (⟨k, hk⟩ = r) && b) <;> rfl
  · intro ⟨⟨k, hk⟩, par⟩
    have hnext : (⟨((k + m - 1) % m + 1) % m, Nat.mod_lt _ hm⟩ : Fin m) = ⟨k, hk⟩ := by
      apply Fin.ext
      change ((k + m - 1) % m + 1) % m = k
      by_cases hk0 : k = 0
      · subst hk0
        rw [zero_add, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
        have h1 : m - 1 + 1 = m := by omega
        rw [h1, Nat.mod_self]
      · have h1 : k + m - 1 = (k - 1) + m := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : k - 1 < m)]
        have h2 : k - 1 + 1 = k := by omega
        rw [h2, Nat.mod_eq_of_lt hk]
    simp only [cyclicParityProdDFA, inv]
    ext
    · exact congrArg Fin.val hnext
    · cases par <;> cases (decide ((⟨(k + m - 1) % m, Nat.mod_lt _ hm⟩ : Fin m) = r) && b) <;> rfl

private lemma cyclicParityProdDFA_eval (m : ℕ) (hm : 0 < m) (r : Fin m) (u : List Bool) :
    ((cyclicParityProdDFA m hm r).eval u).1.1 = u.length % m ∧
      boolToF2 ((cyclicParityProdDFA m hm r).eval u).2 =
        ∑ i ∈ (Finset.range u.length).filter (fun i => i % m = r.1),
          boolToF2 (u[i]?.getD false) := by
  induction u using List.reverseRecOn with
  | nil =>
    simp [DFA.eval, DFA.evalFrom, cyclicParityProdDFA, boolToF2]
  | append_singleton u b ih =>
    rw [dfa_eval_append]
    set q := (cyclicParityProdDFA m hm r).eval u
    change ((cyclicParityProdDFA m hm r).step q b).1.1 = (u ++ [b]).length % m ∧
      boolToF2 ((cyclicParityProdDFA m hm r).step q b).2 =
        ∑ i ∈ (Finset.range (u ++ [b]).length).filter (fun i => i % m = r.1),
          boolToF2 ((u ++ [b])[i]?.getD false)
    rw [List.length_append, List.length_singleton]
    refine ⟨?_, ?_⟩
    · change (q.1.1 + 1) % m = (u.length + 1) % m
      rw [ih.1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    · change boolToF2 (xor q.2 (decide (q.1 = r) && b)) = _
      rw [boolToF2_xor, ih.2, Finset.range_add_one, Finset.filter_insert]
      have hnotmem : u.length ∉ (Finset.range u.length).filter (fun i => i % m = r.1) := by
        simp
      have hcongr :
          ∑ i ∈ (Finset.range u.length).filter (fun i => i % m = r.1),
              boolToF2 ((u ++ [b])[i]?.getD false) =
            ∑ i ∈ (Finset.range u.length).filter (fun i => i % m = r.1),
              boolToF2 (u[i]?.getD false) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hilt : i < u.length := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
        rw [List.getElem?_append_left hilt]
      have hcond : decide (q.1 = r) = decide (u.length % m = r.1) := by
        simp [Fin.ext_iff, ih.1]
      rw [hcond]
      by_cases hmod : u.length % m = r.1
      · rw [if_pos hmod, Finset.sum_insert hnotmem, hcongr]
        have hlast : (u ++ [b])[u.length]? = some b := by
          rw [List.getElem?_append_right le_rfl, Nat.sub_self]
          rfl
        rw [hlast, Option.getD_some, decide_eq_true hmod, Bool.true_and, add_comm]
      · rw [if_neg hmod, hcongr, decide_eq_false hmod, Bool.false_and]
        simp [boolToF2]

private noncomputable def cyclicParityDFA (m : ℕ) (hm : 0 < m) (r : Fin m) : DFA Bool (Fin (2 * m)) :=
  let e : (Fin m × Bool) ≃ Fin (2 * m) :=
    (Equiv.prodComm (Fin m) Bool).trans
      ((Equiv.prodCongr (Fintype.equivFinOfCardEq (by simp : Fintype.card Bool = 2)) (Equiv.refl _)).trans
        finProdFinEquiv)
  mapDFA e (cyclicParityProdDFA m hm r)

private lemma cyclicParityDFA_bijective (m : ℕ) (hm : 0 < m) (r : Fin m) :
    ∀ b : Bool, Function.Bijective (fun q => (cyclicParityDFA m hm r).step q b) := by
  dsimp [cyclicParityDFA]
  exact mapDFA_bijective _ _ (cyclicParityProdDFA_bijective m hm r)

private lemma cyclicParityDFA_separates_of_sum_ne (m : ℕ) (hm : 0 < m) (r : Fin m)
    (w x : List Bool)
    (hne :
      ∑ i ∈ (Finset.range w.length).filter (fun i => i % m = r.1), boolToF2 (w[i]?.getD false) ≠
      ∑ i ∈ (Finset.range x.length).filter (fun i => i % m = r.1), boolToF2 (x[i]?.getD false)) :
    w ∈ (cyclicParityDFA m hm r).accepts ↔ x ∉ (cyclicParityDFA m hm r).accepts := by
  dsimp [cyclicParityDFA]
  rw [mapDFA_accepts, mapDFA_accepts]
  have hw := (cyclicParityProdDFA_eval m hm r w).2
  have hx := (cyclicParityProdDFA_eval m hm r x).2
  have hbne : ((cyclicParityProdDFA m hm r).eval w).2 ≠ ((cyclicParityProdDFA m hm r).eval x).2 := by
    intro heq
    apply hne
    rw [← hw, ← hx, heq]
  change ((cyclicParityProdDFA m hm r).eval w).2 = true ↔
    ¬ (((cyclicParityProdDFA m hm r).eval x).2 = true)
  cases h1 : ((cyclicParityProdDFA m hm r).eval w).2 <;>
    cases h2 : ((cyclicParityProdDFA m hm r).eval x).2 <;> simp_all

/-! ## Section 2: `𝔽₂[X]` Cyclotomic Divisibility & Elementary Number Theory Helpers -/

private noncomputable def wordPoly (u : List Bool) : Polynomial (ZMod 2) :=
  ∑ i ∈ Finset.range u.length, Polynomial.C (boolToF2 (u[i]?.getD false)) * Polynomial.X ^ i

private lemma wordPoly_coeff (u : List Bool) (i : ℕ) :
    (wordPoly u).coeff i = if i < u.length then boolToF2 (u[i]?.getD false) else 0 := by
  simp only [wordPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hi : i < u.length
  · rw [if_pos hi, Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      rw [if_neg hbi.symm]
    · intro hi'
      exact False.elim (hi' (Finset.mem_range.mpr hi))
  · rw [if_neg hi, Finset.sum_eq_zero]
    intro b hb
    have hlt : b < u.length := Finset.mem_range.mp hb
    rw [if_neg (by omega)]

private lemma wordPoly_ne_of_ne {w x : List Bool} (hlen : w.length = x.length) (hne : w ≠ x) :
    wordPoly w - wordPoly x ≠ 0 := by
  intro hzero
  have heq : wordPoly w = wordPoly x := sub_eq_zero.mp hzero
  apply hne
  refine List.ext_getElem hlen fun i hiw hix => ?_
  have hc := congrArg (fun P => P.coeff i) heq
  rw [wordPoly_coeff, wordPoly_coeff, if_pos hiw, if_pos hix,
      List.getElem?_eq_getElem hiw, List.getElem?_eq_getElem hix] at hc
  exact boolToF2_inj hc

private lemma wordPoly_sub_natDegree_lt {w x : List Bool} {n : ℕ}
    (hw : w.length = n) (hx : x.length = n) (hn : 0 < n) :
    (wordPoly w - wordPoly x).natDegree < n := by
  by_cases h0 : wordPoly w - wordPoly x = 0
  · rw [h0, Polynomial.natDegree_zero]; exact hn
  · refine (Polynomial.natDegree_lt_iff_degree_lt h0).mpr ?_
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    rw [Polynomial.coeff_sub, wordPoly_coeff, wordPoly_coeff,
        if_neg (by omega), if_neg (by omega), sub_self]

private lemma X_pow_sub_one_dvd_of_residue_sum_zero {n m : ℕ} (hm : 0 < m)
    (P : Polynomial (ZMod 2))
    (hsupp : ∀ i, n ≤ i → P.coeff i = 0)
    (hres : ∀ r : Fin m, ∑ i ∈ (Finset.range n).filter (fun i => i % m = r.1), P.coeff i = 0) :
    (Polynomial.X ^ m - 1 : Polynomial (ZMod 2)) ∣ P := by
  have hP : P = ∑ i ∈ Finset.range n, Polynomial.C (P.coeff i) * Polynomial.X ^ i := by
    ext k
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero]
    by_cases hk : k < n
    · rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hbk; rw [if_neg hbk.symm]
      · intro hk'; exact False.elim (hk' (Finset.mem_range.mpr hk))
    · rw [hsupp k (by omega), Finset.sum_eq_zero]
      intro b hb
      have hbn : b < n := Finset.mem_range.mp hb
      rw [if_neg (by omega)]
  have hrem_zero :
      ∑ i ∈ Finset.range n, Polynomial.C (P.coeff i) * Polynomial.X ^ (i % m) = 0 := by
    have hfiber :
        ∑ i ∈ Finset.range n, Polynomial.C (P.coeff i) * Polynomial.X ^ (i % m) =
          ∑ r : Fin m, ∑ i ∈ (Finset.range n).filter (fun i => i % m = r.1),
            Polynomial.C (P.coeff i) * Polynomial.X ^ (i % m) := by
      symm
      rw [← Finset.sum_biUnion]
      · congr 1
        ext i
        simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
        constructor
        · rintro ⟨_, hi, _⟩; exact hi
        · intro hi; exact ⟨⟨i % m, Nat.mod_lt i hm⟩, hi, rfl⟩
      · intro r₁ _ r₂ _ hne
        change Disjoint ((Finset.range n).filter (fun i => i % m = r₁.1))
          ((Finset.range n).filter (fun i => i % m = r₂.1))
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        have h1 := (Finset.mem_filter.mp hi1).2
        have h2 := (Finset.mem_filter.mp hi2).2
        exact hne (Fin.ext (h1.symm.trans h2))
    rw [hfiber]
    refine Finset.sum_eq_zero fun r _ => ?_
    have hcongr :
        ∑ i ∈ (Finset.range n).filter (fun i => i % m = r.1),
            Polynomial.C (P.coeff i) * Polynomial.X ^ (i % m) =
          (∑ i ∈ (Finset.range n).filter (fun i => i % m = r.1),
            Polynomial.C (P.coeff i)) * Polynomial.X ^ r.1 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2]
    rw [hcongr, ← map_sum, hres r, map_zero, zero_mul]
  have hdiff : P = ∑ i ∈ Finset.range n,
      Polynomial.C (P.coeff i) * (Polynomial.X ^ i - Polynomial.X ^ (i % m)) := by
    calc P = P - 0 := (sub_zero P).symm
      _ = (∑ i ∈ Finset.range n, Polynomial.C (P.coeff i) * Polynomial.X ^ i) -
          (∑ i ∈ Finset.range n, Polynomial.C (P.coeff i) * Polynomial.X ^ (i % m)) := by
            rw [← hP, hrem_zero]
      _ = ∑ i ∈ Finset.range n,
          (Polynomial.C (P.coeff i) * Polynomial.X ^ i -
            Polynomial.C (P.coeff i) * Polynomial.X ^ (i % m)) := by
            rw [← Finset.sum_sub_distrib]
      _ = _ := Finset.sum_congr rfl fun i _ => by ring
  rw [hdiff]
  refine Finset.dvd_sum fun i _ => ?_
  apply dvd_mul_of_dvd_right
  have hpow : (Polynomial.X : Polynomial (ZMod 2)) ^ i =
      Polynomial.X ^ (i % m) * (Polynomial.X ^ m) ^ (i / m) := by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  have hfac : (Polynomial.X ^ i - Polynomial.X ^ (i % m) : Polynomial (ZMod 2)) =
      Polynomial.X ^ (i % m) * ((Polynomial.X ^ m) ^ (i / m) - 1 ^ (i / m)) := by
    rw [hpow, one_pow]
    ring
  rw [hfac]
  exact dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow (Polynomial.X ^ m) 1 (i / m)) _

/-- In `𝔽₂[X]`, `X^N - 1` is coprime to its derivative whenever `N` is odd. -/
private lemma X_pow_sub_one_coprime_deriv_F2 {N : ℕ} (hodd : N % 2 = 1) :
    IsCoprime (Polynomial.X ^ N - 1 : Polynomial (ZMod 2))
      (Polynomial.derivative (Polynomial.X ^ N - 1 : Polynomial (ZMod 2))) := by
  have hNpos : 1 ≤ N := by omega
  have hcast : (N : ZMod 2) = 1 := by
    have h1 : (N : ZMod 2) = ((N % 2 : ℕ) : ZMod 2) := (ZMod.natCast_mod N 2).symm
    rw [h1, hodd]
    simp
  have hderiv : Polynomial.derivative (Polynomial.X ^ N - 1 : Polynomial (ZMod 2)) =
      Polynomial.X ^ (N - 1) := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_one,
        sub_zero, hcast, map_one, one_mul]
  rw [hderiv]
  refine ⟨-1, Polynomial.X, ?_⟩
  have hpow : Polynomial.X * (Polynomial.X : Polynomial (ZMod 2)) ^ (N - 1) = Polynomial.X ^ N := by
    rw [← pow_succ', show N - 1 + 1 = N by omega]
  rw [hpow]
  ring

/-- Distinct odd-index cyclotomic polynomials are pairwise coprime in `𝔽₂[X]`. -/
private lemma cyclotomic_isCoprime_F2 {a b : ℕ}
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hne : a ≠ b) :
    IsCoprime (Polynomial.cyclotomic a (ZMod 2)) (Polynomial.cyclotomic b (ZMod 2)) := by
  let N := Nat.lcm a b
  have ha_pos : 0 < a := by omega
  have hb_pos : 0 < b := by omega
  have hN_pos : 0 < N := Nat.lcm_pos ha_pos hb_pos
  have hN_odd : N % 2 = 1 := by
    by_contra hnot
    have heven : 2 ∣ N := by omega
    have h2ab : 2 ∣ a * b := heven.trans (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a))
    rcases Nat.prime_two.dvd_mul.mp h2ab with h2a | h2b <;> omega
  have hprod : ∏ d ∈ N.divisors, Polynomial.cyclotomic d (ZMod 2) = Polynomial.X ^ N - 1 :=
    Polynomial.prod_cyclotomic_eq_X_pow_sub_one hN_pos (ZMod 2)
  have ha_mem : a ∈ N.divisors := Nat.mem_divisors.mpr ⟨Nat.dvd_lcm_left a b, hN_pos.ne'⟩
  have hb_mem : b ∈ N.divisors := Nat.mem_divisors.mpr ⟨Nat.dvd_lcm_right a b, hN_pos.ne'⟩
  have hsub : ({a, b} : Finset ℕ) ⊆ N.divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> assumption
  have hdvd_pair : Polynomial.cyclotomic a (ZMod 2) * Polynomial.cyclotomic b (ZMod 2) ∣
      (Polynomial.X ^ N - 1 : Polynomial (ZMod 2)) := by
    have hpair : ∏ d ∈ ({a, b} : Finset ℕ), Polynomial.cyclotomic d (ZMod 2) =
        Polynomial.cyclotomic a (ZMod 2) * Polynomial.cyclotomic b (ZMod 2) :=
      Finset.prod_pair hne
    rw [← hprod, ← hpair]
    exact Finset.prod_dvd_prod_of_subset {a, b} N.divisors (fun d => Polynomial.cyclotomic d (ZMod 2)) hsub
  rcases hdvd_pair with ⟨h, hh⟩
  rcases X_pow_sub_one_coprime_deriv_F2 hN_odd with ⟨u, v, huv⟩
  let g := EuclideanDomain.gcd (Polynomial.cyclotomic a (ZMod 2)) (Polynomial.cyclotomic b (ZMod 2))
  have hga : g ∣ Polynomial.cyclotomic a (ZMod 2) := EuclideanDomain.gcd_dvd_left _ _
  have hgb : g ∣ Polynomial.cyclotomic b (ZMod 2) := EuclideanDomain.gcd_dvd_right _ _
  have hgP : g ∣ (Polynomial.X ^ N - 1 : Polynomial (ZMod 2)) := by
    rw [hh]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hga _) _
  have hgP' : g ∣ Polynomial.derivative (Polynomial.X ^ N - 1 : Polynomial (ZMod 2)) := by
    rw [hh, Polynomial.derivative_mul, Polynomial.derivative_mul]
    have h1 : g ∣ Polynomial.derivative (Polynomial.cyclotomic a (ZMod 2)) *
        Polynomial.cyclotomic b (ZMod 2) * h :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hgb _) _
    have h2 : g ∣ Polynomial.cyclotomic a (ZMod 2) *
        Polynomial.derivative (Polynomial.cyclotomic b (ZMod 2)) * h :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hga _) _
    have h3 : g ∣ Polynomial.cyclotomic a (ZMod 2) * Polynomial.cyclotomic b (ZMod 2) *
        Polynomial.derivative h :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hga _) _
    have hadd : (Polynomial.derivative (Polynomial.cyclotomic a (ZMod 2)) *
          Polynomial.cyclotomic b (ZMod 2) +
        Polynomial.cyclotomic a (ZMod 2) *
          Polynomial.derivative (Polynomial.cyclotomic b (ZMod 2))) * h +
        Polynomial.cyclotomic a (ZMod 2) * Polynomial.cyclotomic b (ZMod 2) *
          Polynomial.derivative h =
        (Polynomial.derivative (Polynomial.cyclotomic a (ZMod 2)) *
            Polynomial.cyclotomic b (ZMod 2) * h +
          Polynomial.cyclotomic a (ZMod 2) *
            Polynomial.derivative (Polynomial.cyclotomic b (ZMod 2)) * h) +
        Polynomial.cyclotomic a (ZMod 2) * Polynomial.cyclotomic b (ZMod 2) *
          Polynomial.derivative h := by ring
    rw [hadd]
    exact dvd_add (dvd_add h1 h2) h3
  have hg1 : g ∣ (1 : Polynomial (ZMod 2)) := by
    rw [← huv]
    exact dvd_add (dvd_mul_of_dvd_right hgP u) (dvd_mul_of_dvd_right hgP' v)
  rcases hg1 with ⟨q, hq⟩
  refine ⟨q * EuclideanDomain.gcdA (Polynomial.cyclotomic a (ZMod 2)) (Polynomial.cyclotomic b (ZMod 2)),
          q * EuclideanDomain.gcdB (Polynomial.cyclotomic a (ZMod 2)) (Polynomial.cyclotomic b (ZMod 2)), ?_⟩
  have hbez := EuclideanDomain.gcd_eq_gcd_ab (Polynomial.cyclotomic a (ZMod 2))
    (Polynomial.cyclotomic b (ZMod 2))
  calc
    q * EuclideanDomain.gcdA (Polynomial.cyclotomic a (ZMod 2)) (Polynomial.cyclotomic b (ZMod 2)) *
        Polynomial.cyclotomic a (ZMod 2) +
      q * EuclideanDomain.gcdB (Polynomial.cyclotomic a (ZMod 2)) (Polynomial.cyclotomic b (ZMod 2)) *
        Polynomial.cyclotomic b (ZMod 2)
      = q * (Polynomial.cyclotomic a (ZMod 2) *
          EuclideanDomain.gcdA (Polynomial.cyclotomic a (ZMod 2)) (Polynomial.cyclotomic b (ZMod 2)) +
        Polynomial.cyclotomic b (ZMod 2) *
          EuclideanDomain.gcdB (Polynomial.cyclotomic a (ZMod 2)) (Polynomial.cyclotomic b (ZMod 2))) := by ring
    _ = q * g := by rw [← hbez]
    _ = g * q := mul_comm _ _
    _ = 1 := hq.symm

/-- Master `𝔽₂[X]` cyclotomic degree lower bound: if `X^m - 1 ∣ P` for every `m ∈ S`
(a set of odd positive integers) and `P ≠ 0`, then `∑_{m ∈ S} φ(m) ≤ P.natDegree`. -/
private lemma sum_totient_le_natDegree_of_dvd_F2 (S : Finset ℕ)
    (hodd : ∀ m ∈ S, m % 2 = 1)
    {P : Polynomial (ZMod 2)} (hP : P ≠ 0)
    (hdvd : ∀ m ∈ S, (Polynomial.X ^ m - 1 : Polynomial (ZMod 2)) ∣ P) :
    ∑ m ∈ S, Nat.totient m ≤ P.natDegree := by
  have hcyc_dvd : ∀ m ∈ S, Polynomial.cyclotomic m (ZMod 2) ∣ P := by
    intro m hm
    have hm_pos : 0 < m := by have := hodd m hm; omega
    have h1 : Polynomial.cyclotomic m (ZMod 2) ∣ (Polynomial.X ^ m - 1 : Polynomial (ZMod 2)) :=
      Polynomial.cyclotomic.dvd_X_pow_sub_one m (ZMod 2)
    exact h1.trans (hdvd m hm)
  have hcop : (S : Set ℕ).Pairwise (fun a b =>
      IsCoprime (Polynomial.cyclotomic a (ZMod 2)) (Polynomial.cyclotomic b (ZMod 2))) := by
    intro a ha b hb hne
    exact cyclotomic_isCoprime_F2 (hodd a ha) (hodd b hb) hne
  have hprod_dvd : (∏ m ∈ S, Polynomial.cyclotomic m (ZMod 2)) ∣ P :=
    Finset.prod_dvd_of_coprime hcop hcyc_dvd
  have hdeg_le : (∏ m ∈ S, Polynomial.cyclotomic m (ZMod 2)).natDegree ≤ P.natDegree :=
    Polynomial.natDegree_le_of_dvd hprod_dvd hP
  have hmonic : ∀ m ∈ S, (Polynomial.cyclotomic m (ZMod 2)).Monic :=
    fun m _ => Polynomial.cyclotomic.monic m (ZMod 2)
  rw [Polynomial.natDegree_prod_of_monic _ _ hmonic] at hdeg_le
  have htot : ∑ m ∈ S, (Polynomial.cyclotomic m (ZMod 2)).natDegree = ∑ m ∈ S, Nat.totient m := by
    refine Finset.sum_congr rfl fun m _ => ?_
    exact Polynomial.natDegree_cyclotomic m (ZMod 2)
  rw [htot] at hdeg_le
  exact hdeg_le

/-! ## Section 3: Analytic & Elementary Number Theory Bounds (Private) -/

/-- Exact sum of odd integers `≤ M`: `∑_{k ≤ M, k odd} k = ((M + 1) / 2)^2`. -/
private lemma sum_odd_Icc (M : ℕ) :
    ∑ k ∈ (Finset.Icc 1 M).filter (fun d => d % 2 = 1), k = ((M + 1) / 2) ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hIcc : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnot : M + 1 ∉ (Finset.Icc 1 M).filter (fun d => d % 2 = 1) := by simp
    rw [hIcc, Finset.filter_insert]
    by_cases hodd : (M + 1) % 2 = 1
    · rw [if_pos hodd, Finset.sum_insert hnot, ih]
      have hk : M + 1 = 2 * ((M + 1) / 2) + 1 := by omega
      have hdiv : (M + 1 + 1) / 2 = (M + 1) / 2 + 1 := by omega
      rw [hdiv]
      nlinarith
    · rw [if_neg hodd, ih]
      have hdiv : (M + 1 + 1) / 2 = (M + 1) / 2 := by omega
      rw [hdiv]

/-- Divisor-sum decomposition of odd integers `≤ M`:
`∑_{k ≤ M, k odd} k = ∑_{q ≤ M, q odd} ∑_{d ≤ M/q, d odd} φ(d)`. -/
private lemma sum_odd_eq_sum_odd_totient (M : ℕ) :
    ∑ k ∈ (Finset.Icc 1 M).filter (fun d => d % 2 = 1), k =
      ∑ q ∈ (Finset.Icc 1 M).filter (fun d => d % 2 = 1),
        ∑ d ∈ (Finset.Icc 1 (M / q)).filter (fun d => d % 2 = 1), Nat.totient d := by
  have h1 :
      ∑ k ∈ (Finset.Icc 1 M).filter (fun d => d % 2 = 1), k =
        ∑ k ∈ (Finset.Icc 1 M).filter (fun d => d % 2 = 1), ∑ d ∈ k.divisors, Nat.totient d := by
    refine Finset.sum_congr rfl fun k _ => (Nat.sum_totient k).symm
  rw [h1, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun x _ => ⟨x.1 / x.2, x.2⟩)
    (fun y _ => ⟨y.1 * y.2, y.2⟩)
    (fun x hx => ?_)
    (fun y hy => ?_)
    (fun x hx => ?_)
    (fun y hy => ?_)
    (fun _ _ => rfl)
  · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors] at hx ⊢
    rcases hx with ⟨⟨⟨hx1, hxM⟩, hxodd⟩, ⟨hdvd, _⟩⟩
    have hd_pos : 0 < x.2 := Nat.pos_of_dvd_of_pos hdvd hx1
    have hmul : x.2 * (x.1 / x.2) = x.1 := Nat.mul_div_cancel' hdvd
    have hq_pos : 0 < x.1 / x.2 := Nat.div_pos (Nat.le_of_dvd hx1 hdvd) hd_pos
    have hq_le : x.1 / x.2 ≤ M := le_trans (Nat.div_le_self x.1 x.2) hxM
    have hd_odd : x.2 % 2 = 1 := by
      by_contra h
      have h2d : 2 ∣ x.2 := by omega
      have h2x : 2 ∣ x.1 := h2d.trans hdvd
      omega
    have hq_odd : (x.1 / x.2) % 2 = 1 := by
      by_contra h
      have h2q : 2 ∣ (x.1 / x.2) := by omega
      have h2x : 2 ∣ x.1 := by rw [← hmul]; exact dvd_mul_of_dvd_right h2q _
      omega
    have hd_le : x.2 ≤ M / (x.1 / x.2) :=
      (Nat.le_div_iff_mul_le hq_pos).mpr (by rw [hmul]; exact hxM)
    exact ⟨⟨⟨hq_pos, hq_le⟩, hq_odd⟩, ⟨⟨hd_pos, hd_le⟩, hd_odd⟩⟩
  · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors] at hy ⊢
    rcases hy with ⟨⟨⟨hq1, _⟩, hqodd⟩, ⟨⟨hd1, hd_le⟩, hdodd⟩⟩
    have hmul_le : y.1 * y.2 ≤ M := by
      have := (Nat.le_div_iff_mul_le hq1).mp hd_le
      rwa [mul_comm] at this
    have hmul_pos : 0 < y.1 * y.2 := Nat.mul_pos hq1 hd1
    have hmul_odd : (y.1 * y.2) % 2 = 1 := by
      rw [Nat.mul_mod, hqodd, hdodd]
    exact ⟨⟨⟨hmul_pos, hmul_le⟩, hmul_odd⟩, ⟨dvd_mul_left y.2 y.1, hmul_pos.ne'⟩⟩
  · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors] at hx
    ext
    · exact Nat.div_mul_cancel hx.2.1
    · rfl
  · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hy
    ext
    · exact Nat.mul_div_cancel y.1 hy.2.1.1
    · rfl

private lemma sum_inv_odd_sq_le (K : ℕ) :
    ∑ j ∈ Finset.Icc 1 K, (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 4 := by
  have hterm : ∀ j ∈ Finset.Icc 1 K,
      (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 ≤
        (1 / 4 : ℝ) * (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ)) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hj1_pos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have hodd_pos : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) := by positivity
    have hdiff : (1 / 4 : ℝ) * (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ)) =
        1 / (4 * (j : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
      push_cast; field_simp [hj_pos.ne', (show (j : ℝ) + 1 ≠ 0 by linarith)]; ring
    rw [hdiff, div_le_div_iff₀ (pow_pos hodd_pos 2) (by positivity)]
    push_cast
    nlinarith
  have htel : ∀ m : ℕ, 1 ≤ m →
      ∑ j ∈ Finset.Icc 1 m, (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ)) = 1 - 1 / ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      have hnot : m + 1 ∉ Finset.Icc 1 m := by simp
      rw [hIcc, Finset.sum_insert hnot, ih]
      ring
  by_cases hK : 1 ≤ K
  · calc
      ∑ j ∈ Finset.Icc 1 K, (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ) ^ 2
        ≤ ∑ j ∈ Finset.Icc 1 K, (1 / 4 : ℝ) * (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = (1 / 4 : ℝ) * (1 - 1 / ((K + 1 : ℕ) : ℝ)) := by rw [← Finset.mul_sum, htel K hK]
      _ ≤ 1 / 4 := by
          have : 0 ≤ (1 : ℝ) / ((K + 1 : ℕ) : ℝ) := by positivity
          linarith
  · have hK0 : K = 0 := by omega
    simp [hK0]

/-- Elementary lower bound on odd totient sum: for all `M ≥ 64`,
`∑_{d ≤ M, d odd} φ(d) ≥ M^2 / 8`. -/
private lemma sum_odd_totient_ge {M : ℕ} (hM : 64 ≤ M) :
    ((M : ℝ) ^ 2) / 8 ≤
      ((∑ d ∈ (Finset.Icc 1 M).filter (fun d => d % 2 = 1), Nat.totient d : ℕ) : ℝ) := by
  set O := (Finset.Icc 1 M).filter (fun d => d % 2 = 1)
  have h1_mem : 1 ∈ O := by simp [O]; omega
  have hdecomp := sum_odd_eq_sum_odd_totient M
  have hsplit :
      ∑ q ∈ O, ∑ d ∈ (Finset.Icc 1 (M / q)).filter (fun d => d % 2 = 1), Nat.totient d =
        (∑ d ∈ O, Nat.totient d) +
          ∑ q ∈ O.erase 1, ∑ d ∈ (Finset.Icc 1 (M / q)).filter (fun d => d % 2 = 1), Nat.totient d := by
    rw [← Finset.add_sum_erase _ _ h1_mem]
    simp [O]
  rw [sum_odd_Icc M, hsplit] at hdecomp
  have hdecomp_r :
      (((M + 1) / 2 : ℕ) : ℝ) ^ 2 =
        ((∑ d ∈ O, Nat.totient d : ℕ) : ℝ) +
          ∑ q ∈ O.erase 1,
            ((∑ d ∈ (Finset.Icc 1 (M / q)).filter (fun d => d % 2 = 1), Nat.totient d : ℕ) : ℝ) := by
    have hc := congrArg (fun n : ℕ => (n : ℝ)) hdecomp
    rw [Nat.cast_pow, Nat.cast_add] at hc
    rw [hc]
    congr 1
    exact Nat.cast_sum _ _
  have hM_r : (64 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlhs_ge : (M : ℝ) ^ 2 / 4 ≤ (((M + 1) / 2 : ℕ) : ℝ) ^ 2 := by
    have hhalf : (M : ℝ) / 2 ≤ (((M + 1) / 2 : ℕ) : ℝ) := by
      have hnat : M ≤ 2 * ((M + 1) / 2) := by omega
      have hreal : (M : ℝ) ≤ 2 * (((M + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      linarith
    nlinarith
  set K : ℕ := (M - 1) / 2
  have hK1 : 1 ≤ K := by omega
  have hbij_tail :
      ∑ q ∈ O.erase 1,
          ((∑ d ∈ (Finset.Icc 1 (M / q)).filter (fun d => d % 2 = 1), Nat.totient d : ℕ) : ℝ) ≤
        ∑ j ∈ Finset.Icc 1 K,
          ((M : ℝ) ^ 2 / (4 * ((2 * j + 1 : ℕ) : ℝ) ^ 2) +
            (M : ℝ) / (2 * ((2 * j + 1 : ℕ) : ℝ)) + 1 / 4) := by
    have hset_eq : O.erase 1 = (Finset.Icc 1 K).image (fun j => 2 * j + 1) := by
      ext q
      simp only [O, Finset.mem_erase, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨hq1, ⟨_, hqM⟩, hqodd⟩
        exact ⟨(q - 1) / 2, ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨j, ⟨hj1, hjK⟩, rfl⟩
        exact ⟨by omega, ⟨by omega, by omega⟩, by omega⟩
    rw [hset_eq, Finset.sum_image (fun a _ b _ h => by omega)]
    refine Finset.sum_le_sum fun j _ => ?_
    set q := 2 * j + 1
    have hq_pos : (0 : ℝ) < (q : ℝ) := by positivity
    have htot_le :
        ∑ d ∈ (Finset.Icc 1 (M / q)).filter (fun d => d % 2 = 1), Nat.totient d ≤
          ((M / q + 1) / 2) ^ 2 := by
      rw [← sum_odd_Icc (M / q)]
      exact Finset.sum_le_sum fun d _ => Nat.totient_le d
    have htot_r :
        ((∑ d ∈ (Finset.Icc 1 (M / q)).filter (fun d => d % 2 = 1), Nat.totient d : ℕ) : ℝ) ≤
          (((M / q + 1) / 2 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast htot_le
    have hdiv_le : (((M / q + 1) / 2 : ℕ) : ℝ) ≤ (M : ℝ) / (2 * (q : ℝ)) + 1 / 2 := by
      have h1 : (((M / q + 1) / 2 : ℕ) : ℝ) ≤ ((M / q + 1 : ℕ) : ℝ) / 2 := by
        have hnat : 2 * ((M / q + 1) / 2) ≤ M / q + 1 := by omega
        have hreal : 2 * (((M / q + 1) / 2 : ℕ) : ℝ) ≤ ((M / q + 1 : ℕ) : ℝ) := by
          exact_mod_cast hnat
        linarith
      have h2 : ((M / q : ℕ) : ℝ) ≤ (M : ℝ) / (q : ℝ) := Nat.cast_div_le
      have hdiv_eq : ((M : ℝ) / (q : ℝ)) / 2 = (M : ℝ) / (2 * (q : ℝ)) := by ring
      push_cast at h1
      linarith
    have hnonneg : (0 : ℝ) ≤ (((M / q + 1) / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc
      ((∑ d ∈ (Finset.Icc 1 (M / q)).filter (fun d => d % 2 = 1), Nat.totient d : ℕ) : ℝ)
        ≤ (((M / q + 1) / 2 : ℕ) : ℝ) ^ 2 := htot_r
      _ ≤ ((M : ℝ) / (2 * (q : ℝ)) + 1 / 2) ^ 2 := by nlinarith
      _ = (M : ℝ) ^ 2 / (4 * (q : ℝ) ^ 2) + (M : ℝ) / (2 * (q : ℝ)) + 1 / 4 := by
          field_simp [hq_pos.ne']
          ring
  have hsum1 :
      ∑ j ∈ Finset.Icc 1 K, (M : ℝ) ^ 2 / (4 * ((2 * j + 1 : ℕ) : ℝ) ^ 2) ≤ (M : ℝ) ^ 2 / 16 := by
    have heq : ∑ j ∈ Finset.Icc 1 K, (M : ℝ) ^ 2 / (4 * ((2 * j + 1 : ℕ) : ℝ) ^ 2) =
        ((M : ℝ) ^ 2 / 4) * ∑ j ∈ Finset.Icc 1 K, (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [heq]
    have hle := sum_inv_odd_sq_le K
    nlinarith
  have hsum2 :
      ∑ j ∈ Finset.Icc 1 K, (M : ℝ) / (2 * ((2 * j + 1 : ℕ) : ℝ)) ≤
        ((M : ℝ) / 4) * (Real.log (M : ℝ) + 1) := by
    have hterm_le : ∀ j ∈ Finset.Icc 1 K,
        (M : ℝ) / (2 * ((2 * j + 1 : ℕ) : ℝ)) ≤ ((M : ℝ) / 4) * ((1 : ℝ) / (j : ℝ)) := by
      intro j hj
      have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      have hodd_pos : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) := by positivity
      rw [show ((M : ℝ) / 4) * ((1 : ℝ) / (j : ℝ)) = (M : ℝ) / (4 * (j : ℝ)) by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      nlinarith
    have hK_le_M : (K : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : K ≤ M)
    have hharm := (Arith4Ext.AnalyticNT.harmonic_sum_log_bounds hK1).2
    have hlog_le : Real.log (K : ℝ) ≤ Real.log (M : ℝ) :=
      Real.log_le_log (by exact_mod_cast hK1) hK_le_M
    calc
      ∑ j ∈ Finset.Icc 1 K, (M : ℝ) / (2 * ((2 * j + 1 : ℕ) : ℝ))
        ≤ ∑ j ∈ Finset.Icc 1 K, ((M : ℝ) / 4) * ((1 : ℝ) / (j : ℝ)) := Finset.sum_le_sum hterm_le
      _ = ((M : ℝ) / 4) * ∑ j ∈ Finset.Icc 1 K, (1 : ℝ) / (j : ℝ) := by rw [← Finset.mul_sum]
      _ ≤ ((M : ℝ) / 4) * (Real.log (K : ℝ) + 1) := by gcongr
      _ ≤ ((M : ℝ) / 4) * (Real.log (M : ℝ) + 1) := by gcongr
  have hsum3 : ∑ _j ∈ Finset.Icc 1 K, (1 / 4 : ℝ) ≤ (M : ℝ) / 8 := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hK2 : (K : ℝ) ≤ (M : ℝ) / 2 := by
      have hnat : 2 * K ≤ M := by omega
      have hreal : 2 * (K : ℝ) ≤ (M : ℝ) := by exact_mod_cast hnat
      linarith
    have hcard : ((K + 1 - 1 : ℕ) : ℝ) = (K : ℝ) := by simp
    rw [hcard]
    linarith
  have htail_total :
      ∑ q ∈ O.erase 1,
          ((∑ d ∈ (Finset.Icc 1 (M / q)).filter (fun d => d % 2 = 1), Nat.totient d : ℕ) : ℝ) ≤
        (M : ℝ) ^ 2 / 16 + ((M : ℝ) / 4) * (Real.log (M : ℝ) + 1) + (M : ℝ) / 8 := by
    refine hbij_tail.trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    linarith
  have hlog_bound : Real.log (M : ℝ) + 3 / 2 ≤ (M : ℝ) / 4 := by
    have hsqrt_pos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hlog_sqrt : Real.log (Real.sqrt (M : ℝ)) ≤ Real.sqrt (M : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos hsqrt_pos
    have hlog_M : Real.log (M : ℝ) = 2 * Real.log (Real.sqrt (M : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.log_rpow (by linarith : (0 : ℝ) < (M : ℝ))]
      ring
    have h8_le : (8 : ℝ) ≤ Real.sqrt (M : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]
      linarith
    have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt (by linarith)
    nlinarith
  have hmid : ((M : ℝ) / 4) * (Real.log (M : ℝ) + 1) + (M : ℝ) / 8 ≤ (M : ℝ) ^ 2 / 16 := by
    have heq : ((M : ℝ) / 4) * (Real.log (M : ℝ) + 1) + (M : ℝ) / 8 =
        ((M : ℝ) / 4) * (Real.log (M : ℝ) + 3 / 2) := by ring
    rw [heq]
    nlinarith
  linarith

private lemma log_two_bounds : (2 / 3 : ℝ) < Real.log 2 ∧ Real.log 2 < 1 := by
  have hlt1 : Real.log 2 < 1 := by
    have h2 : (2 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0); linarith
    calc Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) h2
      _ = 1 := Real.log_exp 1
  have hgt : (2 / 3 : ℝ) < Real.log 2 := by
    have hexp_lt : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
    have hpow : (Real.exp 1) ^ 2 < (2 : ℝ) ^ 3 := by
      have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      nlinarith
    have hlog := Real.log_lt_log (pow_pos (Real.exp_pos 1) 2) hpow
    rw [Real.log_pow, Real.log_exp, Real.log_pow] at hlog
    push_cast at hlog
    linarith
  exact ⟨hgt, hlt1⟩

/-- Explicit Chebyshev `θ(M) ≥ M / 4` for all `M ≥ 4096`. -/
private lemma chebyshevTheta_ge_quarter {M : ℕ} (hM : 4096 ≤ M) :
    (M : ℝ) / 4 ≤ Arith4Ext.AnalyticNT.chebyshevTheta (M : ℝ) := by
  have hM_r : (4096 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hth := Arith4Ext.AnalyticNT.chebyshevTheta_ge_explicit (x := (M : ℝ)) (by linarith)
  have hlog2 := log_two_bounds
  have hsqrt_ge : (64 : ℝ) ≤ Real.sqrt (M : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt (by linarith)
  have hlog_M1 : Real.log ((M : ℝ) + 1) ≤ Real.sqrt (M : ℝ) := by
    have h1 : Real.log ((M : ℝ) + 1) = 2 * Real.log (Real.sqrt ((M : ℝ) + 1)) := by
      rw [Real.sqrt_eq_rpow, Real.log_rpow (by linarith)]
      ring
    have h2 : Real.log (((M : ℝ) + 1) / 4) ≤ ((M : ℝ) + 1) / 4 - 1 :=
      Real.log_le_sub_one_of_pos (by linarith)
    have h3 : Real.log (Real.sqrt ((M : ℝ) + 1) / 4) ≤ Real.sqrt ((M : ℝ) + 1) / 4 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h3
    have hlog4 : Real.log 4 < 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    have hs1 : Real.sqrt ((M : ℝ) + 1) ≤ Real.sqrt (M : ℝ) + 1 := by
      have h0 : 0 ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith, by nlinarith⟩
    linarith
  nlinarith

/-- Explicit prime-interval lower bound: for all `M ≥ 4096`,
`∑_{3 ≤ p ≤ M, p prime} (p - 1) ≥ M^2 / (40 log M)`. -/
private lemma sum_odd_primes_pred_ge {M : ℕ} (hM : 4096 ≤ M) :
    (M : ℝ) ^ 2 / (40 * Real.log (M : ℝ)) ≤
      ((∑ p ∈ (Finset.Icc 3 M).filter Nat.Prime, (p - 1) : ℕ) : ℝ) := by
  have hM_r : (4096 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlog2 := log_two_bounds
  have hth_hi := Arith4Ext.AnalyticNT.chebyshevTheta_ge_explicit (x := (M : ℝ)) (by linarith)
  have hth_lo := Arith4Ext.AnalyticNT.chebyshevTheta_le_two_log_two_mul (x := (M : ℝ) / 4) (by linarith)
  have hsqrt_ge : (64 : ℝ) ≤ Real.sqrt (M : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt (by linarith)
  have hlog_M1 : Real.log ((M : ℝ) + 1) ≤ Real.sqrt (M : ℝ) := by
    have h1 : Real.log ((M : ℝ) + 1) = 2 * Real.log (Real.sqrt ((M : ℝ) + 1)) := by
      rw [Real.sqrt_eq_rpow, Real.log_rpow (by linarith)]
      ring
    have h3 : Real.log (Real.sqrt ((M : ℝ) + 1) / 4) ≤ Real.sqrt ((M : ℝ) + 1) / 4 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h3
    have hlog4 : Real.log 4 < 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    have hs1 : Real.sqrt ((M : ℝ) + 1) ≤ Real.sqrt (M : ℝ) + 1 := by
      have h0 : 0 ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith, by nlinarith⟩
    linarith
  have hdiff_ge : (M : ℝ) / 8 ≤
      Arith4Ext.AnalyticNT.chebyshevTheta (M : ℝ) -
        Arith4Ext.AnalyticNT.chebyshevTheta ((M : ℝ) / 4) := by
    nlinarith
  set q : ℕ := ⌊(M : ℝ) / 4⌋₊
  have hq_le_M : q ≤ M := by
    have hfl : (q : ℝ) ≤ (M : ℝ) / 4 := Nat.floor_le (by linarith)
    have : (q : ℝ) ≤ (M : ℝ) := by linarith
    exact_mod_cast this
  have hq_ge : 1024 ≤ q := Nat.le_floor (by linarith)
  have hsplit_set :
      (Finset.Icc 1 M).filter Nat.Prime =
        (Finset.Icc 1 q).filter Nat.Prime ∪ (Finset.Ioc q M).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hp1, hpM⟩, hp⟩
      by_cases hpq : p ≤ q
      · exact Or.inl ⟨⟨hp1, hpq⟩, hp⟩
      · exact Or.inr ⟨⟨by omega, hpM⟩, hp⟩
    · rintro (⟨⟨hp1, hpq⟩, hp⟩ | ⟨⟨hpq, hpM⟩, hp⟩)
      · exact ⟨⟨hp1, hpq.trans hq_le_M⟩, hp⟩
      · exact ⟨⟨by omega, hpM⟩, hp⟩
  have hdisj : Disjoint ((Finset.Icc 1 q).filter Nat.Prime) ((Finset.Ioc q M).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp1 hp2
    omega
  have hth_diff_eq :
      Arith4Ext.AnalyticNT.chebyshevTheta (M : ℝ) -
        Arith4Ext.AnalyticNT.chebyshevTheta ((M : ℝ) / 4) =
          ∑ p ∈ (Finset.Ioc q M).filter Nat.Prime, Real.log (p : ℝ) := by
    simp only [Arith4Ext.AnalyticNT.chebyshevTheta, Nat.floor_natCast]
    change (∑ p ∈ (Finset.Icc 1 M).filter Nat.Prime, Real.log (p : ℝ)) -
      (∑ p ∈ (Finset.Icc 1 q).filter Nat.Prime, Real.log (p : ℝ)) = _
    rw [hsplit_set, Finset.sum_union hdisj, add_sub_cancel_left]
  have hlogM_pos : 0 < Real.log (M : ℝ) := Real.log_pos (by linarith)
  have hcard_ge :
      (M : ℝ) / (8 * Real.log (M : ℝ)) ≤
        (((Finset.Ioc q M).filter Nat.Prime).card : ℝ) := by
    have hsum_le : ∑ p ∈ (Finset.Ioc q M).filter Nat.Prime, Real.log (p : ℝ) ≤
        (((Finset.Ioc q M).filter Nat.Prime).card : ℝ) * Real.log (M : ℝ) := by
      calc
        ∑ p ∈ (Finset.Ioc q M).filter Nat.Prime, Real.log (p : ℝ)
          ≤ ∑ _p ∈ (Finset.Ioc q M).filter Nat.Prime, Real.log (M : ℝ) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp_mem := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
            exact Real.log_le_log (by exact_mod_cast (by omega : 0 < p)) (by exact_mod_cast hp_mem.2)
        _ = (((Finset.Ioc q M).filter Nat.Prime).card : ℝ) * Real.log (M : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    rw [hth_diff_eq] at hdiff_ge
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hsub_Icc : (Finset.Ioc q M).filter Nat.Prime ⊆ (Finset.Icc 3 M).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
  have hpred_ge : ∀ p ∈ (Finset.Ioc q M).filter Nat.Prime,
      (M : ℝ) / 5 ≤ ((p - 1 : ℕ) : ℝ) := by
    intro p hp
    have hpq : q + 1 ≤ p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    have hq_gt : (M : ℝ) / 4 - 1 < (q : ℝ) := by
      have := Nat.lt_floor_add_one ((M : ℝ) / 4)
      linarith
    have hp_cast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]; norm_num
    have hpq_r : (q : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hpq
    rw [hp_cast]
    linarith
  calc
    (M : ℝ) ^ 2 / (40 * Real.log (M : ℝ))
      = ((M : ℝ) / 5) * ((M : ℝ) / (8 * Real.log (M : ℝ))) := by ring
    _ ≤ ((M : ℝ) / 5) * (((Finset.Ioc q M).filter Nat.Prime).card : ℝ) := by gcongr
    _ = ∑ _p ∈ (Finset.Ioc q M).filter Nat.Prime, ((M : ℝ) / 5) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ p ∈ (Finset.Ioc q M).filter Nat.Prime, ((p - 1 : ℕ) : ℝ) := Finset.sum_le_sum hpred_ge
    _ ≤ ∑ p ∈ (Finset.Icc 3 M).filter Nat.Prime, ((p - 1 : ℕ) : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub_Icc fun _ _ _ => Nat.cast_nonneg _
    _ = ((∑ p ∈ (Finset.Icc 3 M).filter Nat.Prime, (p - 1) : ℕ) : ℝ) := by rw [Nat.cast_sum]

/-- Explicit small prime not dividing a positive integer `K`:
`∃ p prime, ¬ p ∣ K ∧ p ≤ 4 log K + 4098`. -/
private lemma exists_prime_not_dvd_explicit {K : ℕ} (hK : 1 ≤ K) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ K ∧ (p : ℝ) ≤ 4 * Real.log (K : ℝ) + 4098 := by
  set M : ℕ := max 4096 (Nat.ceil (4 * Real.log (K : ℝ) + 1))
  have hM4096 : 4096 ≤ M := le_max_left _ _
  have hM_ge : 4 * Real.log (K : ℝ) + 1 ≤ (M : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 4096 _)
  have hM_le : (M : ℝ) ≤ 4 * Real.log (K : ℝ) + 4098 := by
    rcases le_total 4096 (Nat.ceil (4 * Real.log (K : ℝ) + 1)) with h | h
    · rw [show M = Nat.ceil (4 * Real.log (K : ℝ) + 1) from max_eq_right h]
      have hlog_nn : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK)
      have hlt := Nat.ceil_lt_add_one (by linarith : 0 ≤ 4 * Real.log (K : ℝ) + 1)
      linarith
    · rw [show M = 4096 from max_eq_left h]
      have hlog_nn : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK)
      norm_num
      linarith
  have hnot_all : ¬ ∀ p ∈ (Finset.Icc 1 M).filter Nat.Prime, p ∣ K := by
    intro hall
    have hprod_dvd : (∏ p ∈ (Finset.Icc 1 M).filter Nat.Prime, p) ∣ K := by
      refine Finset.prod_primes_dvd K (fun p hp => (Finset.mem_filter.mp hp).2.prime) hall
    have hprod_le : ∏ p ∈ (Finset.Icc 1 M).filter Nat.Prime, p ≤ K :=
      Nat.le_of_dvd hK hprod_dvd
    have hprod_pos : (0 : ℝ) < ((∏ p ∈ (Finset.Icc 1 M).filter Nat.Prime, p : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos (s := (Finset.Icc 1 M).filter Nat.Prime)
        fun p hp => (Finset.mem_filter.mp hp).2.pos
    have hlog_prod :
        Arith4Ext.AnalyticNT.chebyshevTheta (M : ℝ) =
          Real.log ((∏ p ∈ (Finset.Icc 1 M).filter Nat.Prime, p : ℕ) : ℝ) := by
      simp only [Arith4Ext.AnalyticNT.chebyshevTheta, Nat.floor_natCast]
      rw [Nat.cast_prod, Real.log_prod]
      intro p hp
      exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
    have hth_le : Arith4Ext.AnalyticNT.chebyshevTheta (M : ℝ) ≤ Real.log (K : ℝ) := by
      rw [hlog_prod]
      exact Real.log_le_log hprod_pos (by exact_mod_cast hprod_le)
    have hth_ge := chebyshevTheta_ge_quarter hM4096
    linarith
  push Not at hnot_all
  rcases hnot_all with ⟨p, hp, hndvd⟩
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp
  exact ⟨p, hp.2, hndvd, (by exact_mod_cast hp.1.2 : (p : ℝ) ≤ (M : ℝ)).trans hM_le⟩

/-! ## Section 4: Pillar 1 — Algebraic `𝔽₂[X]` Prime-Modulus `O(√(n log n))` & Robson (1996) `O(√n)` Permutation-DFA Upper Bounds -/

/-- **Pillar 1A — Prime-Modulus `𝔽₂[X]` Cyclotomic DFA Separator (`O(√(n log n))`):**
For every alphabet `α`, every `n ≥ 2`, and every two distinct length-`n` words `w, x : List α`,
there exists a DFA on `Fin m` separating `w` and `x` with `m ≤ 8192 √(n log n)`
(explicitly realized by a `2p`-state cyclic parity DFA for an odd prime `p`). -/
theorem ppl161_prime_modulus_sqrt_log_upper {α : Type*} {n : ℕ} (hn : 2 ≤ n)
    (w x : List α) (hw : w.length = n) (hx : x.length = n) (hne : w ≠ x) :
    ∃ (m : ℕ) (M : DFA α (Fin m)),
      (m : ℝ) ≤ 8192 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ∧
      (w ∈ M.accepts ↔ x ∉ M.accepts) := by
  obtain ⟨f, hfne, hfw, hfx⟩ := exists_bool_projection (hw.trans hx.symm) hne
  let w' := w.map f
  let x' := x.map f
  have hw' : w'.length = n := by simpa [w'] using hfw.trans hw
  have hx' : x'.length = n := by simpa [x'] using hfx.trans hx
  set M : ℕ := max 4096 (Nat.ceil (30 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))))
  have hM4096 : 4096 ≤ M := le_max_left _ _
  have hlog2 := log_two_bounds
  have hn_r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn_ge : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn_r
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hsqrt_ge1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hM_le : (M : ℝ) ≤ 4096 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    rcases le_total 4096 (Nat.ceil (30 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))) with h | h
    · rw [show M = Nat.ceil (30 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) from max_eq_right h]
      have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ 30 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
      linarith
    · rw [show M = 4096 from max_eq_left h]
      rw [Nat.cast_ofNat]
      nlinarith
  have hn_lt_sum : (n : ℝ) ≤ (M : ℝ) ^ 2 / (40 * Real.log (M : ℝ)) := by
    have hM_ge30 : 30 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (M : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 4096 _)
    have hlogM_pos : 0 < Real.log (M : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < M))
    rw [le_div_iff₀ (by positivity)]
    rcases le_total 4096 (Nat.ceil (30 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))) with h | h
    · have hMeq : M = Nat.ceil (30 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) := max_eq_right h
      have hM_ub : (M : ℝ) ≤ 31 * (n : ℝ) := by
        have hlt : (M : ℝ) < 30 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1 := by
          rw [hMeq]; exact Nat.ceil_lt_add_one (by positivity)
        have hlog_le_n : Real.log (n : ℝ) ≤ (n : ℝ) := by
          have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (n : ℝ)); linarith
        have hsqrt_le_n : Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (n : ℝ) := by
          rw [Real.sqrt_le_iff]
          exact ⟨by linarith, by nlinarith⟩
        nlinarith
      have hlogM_le : Real.log (M : ℝ) ≤ 7 * Real.log (n : ℝ) := by
        have h1 : Real.log (M : ℝ) ≤ Real.log (31 * (n : ℝ)) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) hM_ub
        rw [Real.log_mul (by norm_num) (by linarith)] at h1
        have hlog31 : Real.log 31 ≤ 4 := by
          have hexp : (31 : ℝ) ≤ Real.exp 4 := by
            have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
            have hpow : (2.7 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 := by gcongr
            rw [← Real.exp_nat_mul] at hpow
            norm_num at hpow ⊢
            linarith
          calc Real.log 31 ≤ Real.log (Real.exp 4) := Real.log_le_log (by norm_num) hexp
            _ = 4 := Real.log_exp 4
        nlinarith
      have hM2 : 900 * ((n : ℝ) * Real.log (n : ℝ)) ≤ (M : ℝ) ^ 2 := by
        have hsq : Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ^ 2 = (n : ℝ) * Real.log (n : ℝ) :=
          Real.sq_sqrt (by positivity)
        nlinarith
      nlinarith
    · have hMeq : M = 4096 := max_eq_left h
      have hM_val : (M : ℝ) = 4096 := by exact_mod_cast hMeq
      have hlog4096 : Real.log 4096 < 12 := by
        rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]
        push_cast; linarith
      have hn_small : (n : ℝ) ≤ 30000 := by
        have hsq : Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ^ 2 = (n : ℝ) * Real.log (n : ℝ) :=
          Real.sq_sqrt (by positivity)
        have h30 : 30 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ 4096 := by linarith
        have hprod : 900 * ((n : ℝ) * Real.log (n : ℝ)) ≤ 4096 ^ 2 := by nlinarith
        nlinarith
      rw [hM_val]
      nlinarith
  let P : Polynomial (ZMod 2) := wordPoly w' - wordPoly x'
  have hP_ne : P ≠ 0 := wordPoly_ne_of_ne (hw'.trans hx'.symm) hfne
  have hP_deg : P.natDegree < n := wordPoly_sub_natDegree_lt hw' hx' (by omega)
  let S := (Finset.Icc 3 M).filter Nat.Prime
  have hS_odd : ∀ p ∈ S, p % 2 = 1 := by
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hp
    rcases hp.2.eq_two_or_odd with rfl | hodd
    · omega
    · exact hodd
  have hsum_ge : (n : ℝ) ≤ ((∑ p ∈ S, Nat.totient p : ℕ) : ℝ) := by
    have heq : ∑ p ∈ S, Nat.totient p = ∑ p ∈ S, (p - 1) :=
      Finset.sum_congr rfl fun p hp => Nat.totient_prime (Finset.mem_filter.mp hp).2
    rw [heq]
    exact hn_lt_sum.trans (sum_odd_primes_pred_ge hM4096)
  have hnot_all_dvd : ¬ ∀ p ∈ S, (Polynomial.X ^ p - 1 : Polynomial (ZMod 2)) ∣ P := by
    intro hall
    have hle := sum_totient_le_natDegree_of_dvd_F2 S hS_odd hP_ne hall
    have hle_r : ((∑ p ∈ S, Nat.totient p : ℕ) : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hle
    have hdeg_r : (P.natDegree : ℝ) < (n : ℝ) := by exact_mod_cast hP_deg
    linarith
  push Not at hnot_all_dvd
  rcases hnot_all_dvd with ⟨p, hpS, hndvd⟩
  have hp_mem := Finset.mem_filter.mp hpS
  have hp_pos : 0 < p := hp_mem.2.pos
  have hP_supp : ∀ i, n ≤ i → P.coeff i = 0 := by
    intro i hi
    simp only [P, Polynomial.coeff_sub, wordPoly_coeff, hw', hx']
    rw [if_neg (by omega), if_neg (by omega), sub_self]
  have hex_r : ∃ r : Fin p,
      ∑ i ∈ (Finset.range n).filter (fun i => i % p = r.1), P.coeff i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hndvd (X_pow_sub_one_dvd_of_residue_sum_zero hp_pos P hP_supp hall)
  rcases hex_r with ⟨r, hr⟩
  have hsum_ne :
      ∑ i ∈ (Finset.range w'.length).filter (fun i => i % p = r.1), boolToF2 (w'[i]?.getD false) ≠
      ∑ i ∈ (Finset.range x'.length).filter (fun i => i % p = r.1), boolToF2 (x'[i]?.getD false) := by
    intro heq
    apply hr
    have hcoeff_sum :
        ∑ i ∈ (Finset.range n).filter (fun i => i % p = r.1), P.coeff i =
          (∑ i ∈ (Finset.range w'.length).filter (fun i => i % p = r.1), boolToF2 (w'[i]?.getD false)) -
          (∑ i ∈ (Finset.range x'.length).filter (fun i => i % p = r.1), boolToF2 (x'[i]?.getD false)) := by
      rw [hw', hx', ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hilt : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      simp only [P, Polynomial.coeff_sub, wordPoly_coeff, hw', hx', if_pos hilt]
    rw [hcoeff_sum, heq, sub_self]
  refine ⟨2 * p, pullbackDFA f (cyclicParityDFA p hp_pos r), ?_, ?_⟩
  · have hpM : (p : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hp_mem.1).2
    push_cast
    linarith
  · rw [pullbackDFA_accepts, pullbackDFA_accepts]
    exact cyclicParityDFA_separates_of_sum_ne p hp_pos r w' x' hsum_ne

/-- **Pillar 1B — Robson (1996) `O(√n)` Odd-Cyclotomic Permutation-DFA Separator:**
For every alphabet `α`, every `n ≥ 1`, and every two distinct length-`n` words `w, x : List α`,
there exists a **permutation DFA** (bijective transition function for every letter) on `Fin m`
separating `w` and `x` with `m ≤ 130 √n` (sharpening `O(√(n log n))` by `√(log n)`). -/
theorem ppl161_odd_cyclotomic_sqrt_upper {α : Type*} {n : ℕ} (hn : 1 ≤ n)
    (w x : List α) (hw : w.length = n) (hx : x.length = n) (hne : w ≠ x) :
    ∃ (m : ℕ) (M : DFA α (Fin m)),
      (m : ℝ) ≤ 130 * Real.sqrt (n : ℝ) ∧
      (∀ a : α, Function.Bijective (fun q => M.step q a)) ∧
      (w ∈ M.accepts ↔ x ∉ M.accepts) := by
  obtain ⟨f, hfne, hfw, hfx⟩ := exists_bool_projection (hw.trans hx.symm) hne
  let w' := w.map f
  let x' := x.map f
  have hw' : w'.length = n := by simpa [w'] using hfw.trans hw
  have hx' : x'.length = n := by simpa [x'] using hfx.trans hx
  set M : ℕ := max 64 (Nat.ceil (Real.sqrt (8 * (n : ℝ))))
  have hM64 : 64 ≤ M := le_max_left _ _
  have hn_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsqrt_ge1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hM_le : (M : ℝ) ≤ 65 * Real.sqrt (n : ℝ) := by
    rcases le_total 64 (Nat.ceil (Real.sqrt (8 * (n : ℝ)))) with h | h
    · rw [show M = Nat.ceil (Real.sqrt (8 * (n : ℝ))) from max_eq_right h]
      have hlt := Nat.ceil_lt_add_one (Real.sqrt_nonneg (8 * (n : ℝ)))
      have h8 : Real.sqrt (8 * (n : ℝ)) ≤ 3 * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_mul (by norm_num)]
        have hsqrt8 : Real.sqrt 8 ≤ 3 := by rw [Real.sqrt_le_iff]; norm_num
        nlinarith
      linarith
    · rw [show M = 64 from max_eq_left h]
      norm_num
      nlinarith
  have hn_le_M2 : (n : ℝ) ≤ (M : ℝ) ^ 2 / 8 := by
    have hM_ge : Real.sqrt (8 * (n : ℝ)) ≤ (M : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 64 _))
    have hsq : Real.sqrt (8 * (n : ℝ)) ^ 2 = 8 * (n : ℝ) := Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg (8 * (n : ℝ))]
  let P : Polynomial (ZMod 2) := wordPoly w' - wordPoly x'
  have hP_ne : P ≠ 0 := wordPoly_ne_of_ne (hw'.trans hx'.symm) hfne
  have hP_deg : P.natDegree < n := wordPoly_sub_natDegree_lt hw' hx' (by omega)
  let S := (Finset.Icc 1 M).filter (fun d => d % 2 = 1)
  have hS_odd : ∀ d ∈ S, d % 2 = 1 := fun d hd => (Finset.mem_filter.mp hd).2
  have hsum_ge : (n : ℝ) ≤ ((∑ d ∈ S, Nat.totient d : ℕ) : ℝ) :=
    hn_le_M2.trans (sum_odd_totient_ge hM64)
  have hnot_all_dvd : ¬ ∀ d ∈ S, (Polynomial.X ^ d - 1 : Polynomial (ZMod 2)) ∣ P := by
    intro hall
    have hle := sum_totient_le_natDegree_of_dvd_F2 S hS_odd hP_ne hall
    have hle_r : ((∑ d ∈ S, Nat.totient d : ℕ) : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hle
    have hdeg_r : (P.natDegree : ℝ) < (n : ℝ) := by exact_mod_cast hP_deg
    linarith
  push Not at hnot_all_dvd
  rcases hnot_all_dvd with ⟨d, hdS, hndvd⟩
  have hd_mem := Finset.mem_filter.mp hdS
  have hd_pos : 0 < d := (Finset.mem_Icc.mp hd_mem.1).1
  have hP_supp : ∀ i, n ≤ i → P.coeff i = 0 := by
    intro i hi
    simp only [P, Polynomial.coeff_sub, wordPoly_coeff, hw', hx']
    rw [if_neg (by omega), if_neg (by omega), sub_self]
  have hex_r : ∃ r : Fin d,
      ∑ i ∈ (Finset.range n).filter (fun i => i % d = r.1), P.coeff i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hndvd (X_pow_sub_one_dvd_of_residue_sum_zero hd_pos P hP_supp hall)
  rcases hex_r with ⟨r, hr⟩
  have hsum_ne :
      ∑ i ∈ (Finset.range w'.length).filter (fun i => i % d = r.1), boolToF2 (w'[i]?.getD false) ≠
      ∑ i ∈ (Finset.range x'.length).filter (fun i => i % d = r.1), boolToF2 (x'[i]?.getD false) := by
    intro heq
    apply hr
    have hcoeff_sum :
        ∑ i ∈ (Finset.range n).filter (fun i => i % d = r.1), P.coeff i =
          (∑ i ∈ (Finset.range w'.length).filter (fun i => i % d = r.1), boolToF2 (w'[i]?.getD false)) -
          (∑ i ∈ (Finset.range x'.length).filter (fun i => i % d = r.1), boolToF2 (x'[i]?.getD false)) := by
      rw [hw', hx', ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hilt : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      simp only [P, Polynomial.coeff_sub, wordPoly_coeff, hw', hx', if_pos hilt]
    rw [hcoeff_sum, heq, sub_self]
  refine ⟨2 * d, pullbackDFA f (cyclicParityDFA d hd_pos r), ?_,
    pullbackDFA_bijective f _ (cyclicParityDFA_bijective d hd_pos r), ?_⟩
  · have hdM : (d : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd_mem.1).2
    push_cast
    linarith
  · rw [pullbackDFA_accepts, pullbackDFA_accepts]
    exact cyclicParityDFA_separates_of_sum_ne d hd_pos r w' x' hsum_ne

/-- **Unequal-Length `O(log n)` Separator:**
Any two words `w, x : List α` of unequal lengths `≤ n` (`n ≥ 2`) are separated by a cyclic
length-mod-`p` DFA with `p ≤ 4 log n + 4098` states. -/
theorem ppl161_unequal_length_log_upper {α : Type*} {n : ℕ} (_hn : 2 ≤ n)
    (w x : List α) (hw : w.length ≤ n) (hx : x.length ≤ n) (hne : w.length ≠ x.length) :
    ∃ (p : ℕ) (M : DFA α (Fin p)),
      (p : ℝ) ≤ 4 * Real.log (n : ℝ) + 4098 ∧
      (w ∈ M.accepts ↔ x ∉ M.accepts) := by
  let Δ := if w.length < x.length then x.length - w.length else w.length - x.length
  have hΔ_pos : 1 ≤ Δ := by dsimp [Δ]; split_ifs <;> omega
  have hΔ_le : Δ ≤ n := by dsimp [Δ]; split_ifs <;> omega
  obtain ⟨p, hp_prime, hndvd, hp_le⟩ := exists_prime_not_dvd_explicit hΔ_pos
  have hmod_ne : w.length % p ≠ x.length % p := by
    intro hmod
    apply hndvd
    dsimp [Δ]
    split_ifs with hlt
    · exact (Nat.modEq_iff_dvd' (Nat.le_of_lt hlt)).mp hmod
    · exact (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
  let r : Fin p := ⟨w.length % p, Nat.mod_lt _ hp_prime.pos⟩
  refine ⟨p, lenModDFA p hp_prime.pos r, ?_, ?_⟩
  · have hlog_le : Real.log (Δ : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by exact_mod_cast hΔ_pos) (by exact_mod_cast hΔ_le)
    linarith
  · rw [lenModDFA_accepts_iff, lenModDFA_accepts_iff]
    simp [r, hmod_ne.symm]

/-- **General `≤ n` Length `O(√n)` Separator:**
Every two distinct words `w, x : List α` of length at most `n` (`n ≥ 1`) are separated by
a DFA on `Fin m` with `m ≤ 4110 √n` states. -/
theorem ppl161_general_le_sqrt_upper {α : Type*} {n : ℕ} (hn : 1 ≤ n)
    (w x : List α) (hw : w.length ≤ n) (hx : x.length ≤ n) (hne : w ≠ x) :
    ∃ (m : ℕ) (M : DFA α (Fin m)),
      (m : ℝ) ≤ 4110 * Real.sqrt (n : ℝ) ∧
      (w ∈ M.accepts ↔ x ∉ M.accepts) := by
  by_cases hlen : w.length = x.length
  · have hpos : 1 ≤ w.length := by
      rcases Nat.eq_zero_or_pos w.length with h0 | hpos
      · exfalso
        have hw0 : w = [] := List.length_eq_zero_iff.mp h0
        have hx0 : x = [] := List.length_eq_zero_iff.mp (by omega)
        exact hne (hw0.trans hx0.symm)
      · exact hpos
    obtain ⟨m, M, hm, _, hsep⟩ := ppl161_odd_cyclotomic_sqrt_upper hpos w x rfl hlen.symm hne
    refine ⟨m, M, ?_, hsep⟩
    have hsqrt_le : Real.sqrt (w.length : ℝ) ≤ Real.sqrt (n : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hw)
    linarith
  · by_cases hn2 : 2 ≤ n
    · obtain ⟨p, M, hp, hsep⟩ := ppl161_unequal_length_log_upper hn2 w x hw hx hlen
      refine ⟨p, M, ?_, hsep⟩
      have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
      have hsqrt_ge1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
        rw [Real.le_sqrt (by norm_num) (by exact_mod_cast (by omega : 0 ≤ n))]
        exact_mod_cast hn
      have hlog_le : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
        have h1 := Real.log_le_sub_one_of_pos hsqrt_pos
        have h2 : Real.log (n : ℝ) = 2 * Real.log (Real.sqrt (n : ℝ)) := by
          rw [Real.sqrt_eq_rpow, Real.log_rpow (by exact_mod_cast hn : (0 : ℝ) < (n : ℝ))]
          ring
        linarith
      linarith
    · have hn1 : n = 1 := by omega
      subst hn1
      let r : Fin 2 := ⟨w.length % 2, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨2, lenModDFA 2 (by norm_num) r, by norm_num, ?_⟩
      rw [lenModDFA_accepts_iff, lenModDFA_accepts_iff]
      have : w.length % 2 ≠ x.length % 2 := by omega
      simp [r, this.symm]

/-! ## Section 5: Pillar 2 — Fine–Wilf Periodic, KMP Factor, & `2^k`-Spaced Sub-`√n` Separators -/

/-- **Fine–Wilf Periodic Word Separator:**
If `w, x : List α` are distinct length-`n` words having positive periods `p` and `q` respectively,
then they differ at some position `i < p + q - gcd(p, q)` and are separated by a DFA on
`Fin (p + q - gcd(p, q) + 2)`. -/
theorem ppl161_fine_wilf_periodic_separator {α : Type*} {n p q : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (w x : List α) (hw : w.length = n) (hx : x.length = n) (hne : w ≠ x)
    (hper_w : ∀ i : ℕ, i + p < w.length → w[i]? = w[i + p]?)
    (hper_x : ∀ i : ℕ, i + q < x.length → x[i]? = x[i + q]?) :
    ∃ (m : ℕ) (M : DFA α (Fin m)),
      m ≤ p + q - Nat.gcd p q + 2 ∧
      (w ∈ M.accepts ↔ x ∉ M.accepts) := by
  classical
  let L := p + q - Nat.gcd p q
  have hdiff_lt : ∃ i : ℕ, i < L ∧ i < n ∧ w[i]? ≠ x[i]? := by
    by_contra hall
    push Not at hall
    by_cases hnL : n ≤ L
    · apply hne
      apply List.ext_getElem?
      intro i
      by_cases hi : i < n
      · exact hall i (by omega) hi
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    · push Not at hnL
      have htake_eq : w.take L = x.take L := by
        apply List.ext_getElem?
        intro i
        by_cases hi : i < L
        · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi]
          exact hall i hi (by omega)
        · rw [List.getElem?_eq_none (by rw [List.length_take]; omega),
              List.getElem?_eq_none (by rw [List.length_take]; omega)]
      let u := w.take L
      have hu_len : u.length = L := List.length_take_of_le (by omega)
      have hu_p : Arith4Ext.AutomataCombinatorics.HasPeriod u p :=
        Arith4Ext.AutomataCombinatorics.hasPeriod_take hper_w
      have hu_q : Arith4Ext.AutomataCombinatorics.HasPeriod u q := by
        dsimp [u]; rw [htake_eq]
        exact Arith4Ext.AutomataCombinatorics.hasPeriod_take hper_x
      let d := Nat.gcd p q
      have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left q hp
      have hu_d : Arith4Ext.AutomataCombinatorics.HasPeriod u d :=
        Arith4Ext.AutomataCombinatorics.fine_wilf u hp hq hu_p hu_q (by omega)
      have hd_le_p : d ≤ p := Nat.le_of_dvd hp (Nat.gcd_dvd_left p q)
      have hd_le_q : d ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right p q)
      have hp_le_L : p ≤ L := by dsimp [L]; omega
      have hq_le_L : q ≤ L := by dsimp [L]; omega
      have hmod_w : ∀ i < n, w[i]? = w[i % d]? := by
        intro i hi
        have hstep_p : w[i]? = w[i % p]? := by
          have h1 : i = i % p + (i / p) * p := by
            have := Nat.mod_add_div i p; linarith [mul_comm p (i / p)]
          have h2 := Arith4Ext.AutomataCombinatorics.hasPeriod_mul hper_w (i / p) (i % p)
            (by rw [← h1, hw]; exact hi)
          rw [← h1] at h2
          exact h2.symm
        have hip_lt_L : i % p < L := (Nat.mod_lt i hp).trans_le hp_le_L
        have hmod_mod : (i % p) % d = i % d := Nat.mod_mod_of_dvd i (Nat.gcd_dvd_left p q)
        have hstep_d : u[i % p]? = u[(i % p) % d]? := by
          have h1 : i % p = (i % p) % d + ((i % p) / d) * d := by
            have := Nat.mod_add_div (i % p) d; linarith [mul_comm d ((i % p) / d)]
          have h2 := Arith4Ext.AutomataCombinatorics.hasPeriod_mul hu_d ((i % p) / d) ((i % p) % d)
            (by rw [← h1, hu_len]; exact hip_lt_L)
          rw [← h1] at h2
          exact h2.symm
        have hid_lt_L : i % d < L := (Nat.mod_lt i hd_pos).trans_le (hd_le_p.trans hp_le_L)
        rw [hstep_p, ← List.getElem?_take_of_lt hip_lt_L, hstep_d, hmod_mod,
            List.getElem?_take_of_lt hid_lt_L]
      have hmod_x : ∀ i < n, x[i]? = x[i % d]? := by
        intro i hi
        have hstep_q : x[i]? = x[i % q]? := by
          have h1 : i = i % q + (i / q) * q := by
            have := Nat.mod_add_div i q; linarith [mul_comm q (i / q)]
          have h2 := Arith4Ext.AutomataCombinatorics.hasPeriod_mul hper_x (i / q) (i % q)
            (by rw [← h1, hx]; exact hi)
          rw [← h1] at h2
          exact h2.symm
        have hiq_lt_L : i % q < L := (Nat.mod_lt i hq).trans_le hq_le_L
        have hmod_mod : (i % q) % d = i % d := Nat.mod_mod_of_dvd i (Nat.gcd_dvd_right p q)
        have hstep_d : u[i % q]? = u[(i % q) % d]? := by
          have h1 : i % q = (i % q) % d + ((i % q) / d) * d := by
            have := Nat.mod_add_div (i % q) d; linarith [mul_comm d ((i % q) / d)]
          have h2 := Arith4Ext.AutomataCombinatorics.hasPeriod_mul hu_d ((i % q) / d) ((i % q) % d)
            (by rw [← h1, hu_len]; exact hiq_lt_L)
          rw [← h1] at h2
          exact h2.symm
        have hid_lt_L : i % d < L := (Nat.mod_lt i hd_pos).trans_le (hd_le_q.trans hq_le_L)
        rw [hstep_q, ← List.getElem?_take_of_lt hiq_lt_L, ← htake_eq]
        change u[i % q]? = x[i % d]?
        rw [hstep_d, hmod_mod]
        dsimp only [u]
        rw [htake_eq, List.getElem?_take_of_lt hid_lt_L]
      apply hne
      apply List.ext_getElem?
      intro i
      by_cases hi : i < n
      · rw [hmod_w i hi, hmod_x i hi]
        have hid_lt_L : i % d < L := (Nat.mod_lt i hd_pos).trans_le (hd_le_p.trans hp_le_L)
        exact hall (i % d) hid_lt_L (by omega)
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  rcases hdiff_lt with ⟨i, hiL, hin, hne_i⟩
  have hiw : i < w.length := by omega
  have hix : i < x.length := by omega
  refine ⟨i + 3, posCheckDFA i w[i], by dsimp [L] at hiL; omega, ?_⟩
  rw [posCheckDFA_accepts_iff i w[i] w hiw, posCheckDFA_accepts_iff i w[i] x hix]
  have hne_el : x[i] ≠ w[i] := by
    intro heq
    apply hne_i
    rw [List.getElem?_eq_getElem hiw, List.getElem?_eq_getElem hix, heq]
  simp [hne_el]

/-- Explicit KMP factor-presence DFA on `Fin (v.length + 1)`:
state `v.length` is an accepting sink; state `s < v.length` tracks the maximum `t < v.length`
such that `v.take t <:+ u`. -/
private noncomputable def kmpStep {α : Type*} (v : List α) (s : Fin (v.length + 1)) (a : α) :
    Fin (v.length + 1) := by
  classical
  exact
    if s.1 = v.length then
      ⟨v.length, Nat.lt_succ_self _⟩
    else
      let cand := (Finset.range (v.length + 1)).filter (fun t => v.take t <:+ (v.take s.1 ++ [a]))
      have h0 : 0 ∈ cand := by
        simp [cand]
      have hmax_mem : cand.max' ⟨0, h0⟩ ∈ cand := Finset.max'_mem cand ⟨0, h0⟩
      ⟨cand.max' ⟨0, h0⟩, Finset.mem_range.mp (Finset.mem_filter.mp hmax_mem).1⟩

private noncomputable def kmpDFA {α : Type*} (v : List α) : DFA α (Fin (v.length + 1)) where
  step := kmpStep v
  start := ⟨0, Nat.zero_lt_succ _⟩
  accept := {⟨v.length, Nat.lt_succ_self _⟩}

private lemma kmpDFA_invariant {α : Type*} (v : List α) (hv : v ≠ []) :
    ∀ u : List α,
      (v <:+: u → (kmpDFA v).eval u = ⟨v.length, Nat.lt_succ_self _⟩) ∧
      (¬ v <:+: u →
        ((kmpDFA v).eval u).1 < v.length ∧
        v.take ((kmpDFA v).eval u).1 <:+ u ∧
        ∀ t ≤ v.length, v.take t <:+ u → t ≤ ((kmpDFA v).eval u).1) := by
  intro u
  induction u using List.reverseRecOn with
  | nil =>
    refine ⟨?_, ?_⟩
    · intro hinf
      rcases hinf with ⟨s, t, hst⟩
      have : v.length = 0 := by
        have hlen := congrArg List.length hst
        rw [List.length_append, List.length_append, List.length_nil] at hlen
        omega
      exact False.elim (hv (List.length_eq_zero_iff.mp this))
    · intro _
      have hv_pos : 0 < v.length := List.length_pos_iff.mpr hv
      refine ⟨hv_pos, by simp [DFA.eval, DFA.evalFrom, kmpDFA], ?_⟩
      intro t ht hsuf
      rcases hsuf with ⟨p, hp⟩
      have hlen := congrArg List.length hp
      rw [List.length_append, List.length_take_of_le ht, List.length_nil] at hlen
      simp [DFA.eval, DFA.evalFrom, kmpDFA]
      omega
  | append_singleton u a ih =>
    classical
    rw [dfa_eval_append]
    change (v <:+: (u ++ [a]) → kmpStep v ((kmpDFA v).eval u) a = ⟨v.length, Nat.lt_succ_self _⟩) ∧
      (¬ v <:+: (u ++ [a]) →
        (kmpStep v ((kmpDFA v).eval u) a).1 < v.length ∧
        v.take (kmpStep v ((kmpDFA v).eval u) a).1 <:+ (u ++ [a]) ∧
        ∀ t ≤ v.length, v.take t <:+ (u ++ [a]) → t ≤ (kmpStep v ((kmpDFA v).eval u) a).1)
    by_cases hinf_u : v <:+: u
    · have hev : (kmpDFA v).eval u = ⟨v.length, Nat.lt_succ_self _⟩ := ih.1 hinf_u
      have hinf_ua : v <:+: (u ++ [a]) := by
        rcases hinf_u with ⟨p, q, rfl⟩
        exact ⟨p, q ++ [a], by simp [List.append_assoc]⟩
      refine ⟨fun _ => by simp [kmpStep, hev], fun hnot => False.elim (hnot hinf_ua)⟩
    · obtain ⟨hs_lt, hs_suf, hs_max⟩ := ih.2 hinf_u
      set s := ((kmpDFA v).eval u).1
      have hs_ne : s ≠ v.length := ne_of_lt hs_lt
      have hsuf_iff : ∀ t ≤ v.length,
          (v.take t <:+ (u ++ [a])) ↔ (v.take t <:+ (v.take s ++ [a])) := by
        intro t ht
        rcases t with _ | t
        · simp
        · have ht_lt : t < v.length := by omega
          have htake_succ : v.take (t + 1) = v.take t ++ [v[t]] := List.take_succ_eq_append_getElem ht_lt
          rw [htake_succ]
          constructor
          · intro h
            rcases h with ⟨p, hp⟩
            rw [← List.append_assoc] at hp
            have hlast := List.append_inj_right' hp (by simp)
            have hinit := List.append_inj_left' hp (by simp)
            have ha_eq : v[t] = a := by simpa using hlast
            have ht_suf : v.take t <:+ u := ⟨p, hinit⟩
            have hts : t ≤ s := hs_max t (by omega) ht_suf
            have ht_suf_s : v.take t <:+ v.take s := by
              rcases hs_suf with ⟨ps, hps⟩
              have hlen_t : (v.take t).length = t := List.length_take_of_le (by omega)
              have hlen_s : (v.take s).length = s := List.length_take_of_le (by omega)
              have hdrop : (v.take s).drop (s - t) = v.take t := by
                have hu1 : u.drop (u.length - t) = v.take t := by
                  rw [← hinit, List.length_append, hlen_t, Nat.add_sub_cancel, List.drop_left]
                have hu2 : u.drop (u.length - s) = v.take s := by
                  rw [← hps, List.length_append, hlen_s, Nat.add_sub_cancel, List.drop_left]
                have hle_u : s ≤ u.length := by
                  have := congrArg List.length hps; rw [List.length_append, hlen_s] at this; omega
                rw [← hu2, List.drop_drop, show u.length - s + (s - t) = u.length - t by omega, hu1]
              exact ⟨(v.take s).take (s - t), by rw [← hdrop, List.take_append_drop]⟩
            rcases ht_suf_s with ⟨q, hq⟩
            exact ⟨q, by rw [← List.append_assoc, hq, ha_eq]⟩
          · intro h
            rcases h with ⟨q, hq⟩
            rcases hs_suf with ⟨ps, hps⟩
            exact ⟨ps ++ q, by rw [List.append_assoc, hq, ← List.append_assoc, hps]⟩
      let cand := (Finset.range (v.length + 1)).filter (fun t => v.take t <:+ (v.take s ++ [a]))
      have h0 : 0 ∈ cand := by simp [cand]
      let m := cand.max' ⟨0, h0⟩
      have hm_eq : (kmpStep v ((kmpDFA v).eval u) a).1 = m := by
        simp [kmpStep, hs_ne, s, m, cand]
      have hm_mem : m ∈ cand := Finset.max'_mem cand ⟨0, h0⟩
      have hm_le : m ≤ v.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hm_mem).1)
      have hm_suf : v.take m <:+ (u ++ [a]) :=
        (hsuf_iff m hm_le).mpr (Finset.mem_filter.mp hm_mem).2
      have hm_max : ∀ t ≤ v.length, v.take t <:+ (u ++ [a]) → t ≤ m := by
        intro t ht htsuf
        have ht_mem : t ∈ cand := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
          (hsuf_iff t ht).mp htsuf⟩
        exact Finset.le_max' cand t ht_mem
      have hinf_iff : v <:+: (u ++ [a]) ↔ v <:+ (u ++ [a]) := by
        constructor
        · rintro ⟨p, q, hpq⟩
          rcases q with _ | ⟨b, q'⟩
          · exact ⟨p, by simpa using hpq⟩
          · exfalso
            have hq_ne : b :: q' ≠ [] := List.cons_ne_nil _ _
            have hinit : p ++ v ++ (b :: q').dropLast = u := by
              have hdl := congrArg List.dropLast hpq
              rw [List.dropLast_append_of_ne_nil hq_ne, List.dropLast_concat] at hdl
              exact hdl
            exact hinf_u ⟨p, (b :: q').dropLast, hinit⟩
        · rintro ⟨p, hp⟩
          exact ⟨p, [], by simpa using hp⟩
      refine ⟨?_, ?_⟩
      · intro hinf_ua
        have hvsuf : v.take v.length <:+ (u ++ [a]) := by
          rw [List.take_length]; exact hinf_iff.mp hinf_ua
        have hvle : v.length ≤ m := hm_max v.length le_rfl hvsuf
        apply Fin.ext
        change (kmpStep v ((kmpDFA v).eval u) a).1 = v.length
        rw [hm_eq]
        omega
      · intro hninf_ua
        have hm_lt : m < v.length := by
          rcases lt_or_eq_of_le hm_le with hlt | heq
          · exact hlt
          · exfalso
            apply hninf_ua
            rw [hinf_iff]
            rw [heq, List.take_length] at hm_suf
            exact hm_suf
        rw [hm_eq]
        exact ⟨hm_lt, hm_suf, hm_max⟩

/-- **KMP Short-Factor DFA Separator:**
If a nonempty factor `v : List α` occurs as a contiguous infix (`v <:+: w`) in `w` and not in `x`
(or vice versa), then an explicit DFA on `Fin (v.length + 1)` separates `w` and `x`. -/
theorem ppl161_kmp_factor_separator {α : Type*} (v w x : List α)
    (hv : v ≠ []) (hdiff : (v <:+: w) ↔ ¬ (v <:+: x)) :
    ∃ M : DFA α (Fin (v.length + 1)), w ∈ M.accepts ↔ x ∉ M.accepts := by
  refine ⟨kmpDFA v, ?_⟩
  have hacc : ∀ u : List α, u ∈ (kmpDFA v).accepts ↔ v <:+: u := by
    intro u
    change (kmpDFA v).eval u = ⟨v.length, Nat.lt_succ_self _⟩ ↔ v <:+: u
    constructor
    · intro heq
      by_contra hnot
      have hlt := ((kmpDFA_invariant v hv u).2 hnot).1
      rw [heq] at hlt
      exact lt_irrefl _ hlt
    · exact (kmpDFA_invariant v hv u).1
  rw [hacc w, hacc x]
  exact hdiff

/-- **`2^k`-Spaced Sub-`√n` Separator (`O(√(n / 2^k))`):**
If `w, x : List α` are distinct length-`n` words whose mismatch indices all lie in a single
congruence class modulo `2^k` (i.e. `∀ i < n, w[i]? ≠ x[i]? → i % 2^k = r₀`),
then `w` and `x` are separated by a permutation DFA on `Fin m` with
`m ≤ 130 * √(n / 2^k + 1)` states (e.g., `O(n^{1/3})` when `2^k ≈ n^{1/3}`). -/
theorem ppl161_spaced_sub_sqrt_separator {α : Type*} {n k r₀ : ℕ}
    (w x : List α) (hw : w.length = n) (hx : x.length = n) (hne : w ≠ x)
    (hspaced : ∀ i : ℕ, i < n → w[i]? ≠ x[i]? → i % (2 ^ k) = r₀) :
    ∃ (m : ℕ) (M : DFA α (Fin m)),
      (m : ℝ) ≤ 130 * Real.sqrt ((n / (2 ^ k) + 1 : ℕ) : ℝ) ∧
      (∀ a : α, Function.Bijective (fun q => M.step q a)) ∧
      (w ∈ M.accepts ↔ x ∉ M.accepts) := by
  obtain ⟨f, hfne, hfw, hfx⟩ := exists_bool_projection (hw.trans hx.symm) hne
  let w' := w.map f
  let x' := x.map f
  have hw' : w'.length = n := by simpa [w'] using hfw.trans hw
  have hx' : x'.length = n := by simpa [x'] using hfx.trans hx
  let L := 2 ^ k
  have hL_pos : 0 < L := pow_pos (by norm_num) k
  let qn := n / L + 1
  have hqn_pos : 1 ≤ qn := Nat.succ_le_succ (Nat.zero_le _)
  have hr₀_lt : r₀ < L := by
    have hdiff : ∃ i < n, w[i]? ≠ x[i]? := by
      by_contra hall
      push Not at hall
      apply hne
      apply List.ext_getElem?
      intro i
      by_cases hi : i < n
      · exact hall i hi
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    rcases hdiff with ⟨i, hin, hnei⟩
    rw [← hspaced i hin hnei]
    exact Nat.mod_lt i hL_pos
  -- Build compressed words of length `qn` sampling indices `r₀ + j * L`
  let wC : List Bool := List.ofFn (fun j : Fin qn => (w'[r₀ + j.1 * L]?).getD false)
  let xC : List Bool := List.ofFn (fun j : Fin qn => (x'[r₀ + j.1 * L]?).getD false)
  have hwC : wC.length = qn := List.length_ofFn
  have hxC : xC.length = qn := List.length_ofFn
  have hC_ne : wC ≠ xC := by
    intro heq
    apply hfne
    apply List.ext_getElem?
    intro i
    by_cases hi : i < n
    · by_cases hwx : w[i]? = x[i]?
      · simp only [List.getElem?_map, hwx]
      · have hmod := hspaced i hi hwx
        let j := i / L
        have hj_lt : j < qn := by
          have : i / L ≤ n / L := Nat.div_le_div_right (Nat.le_of_lt hi)
          omega
        have hi_eq : r₀ + j * L = i := by
          dsimp [j]; rw [← hmod, mul_comm]; exact Nat.mod_add_div i L
        have hj_eq := congrArg (fun l => l[j]?) heq
        rw [List.getElem?_eq_getElem (by rw [hwC]; exact hj_lt),
            List.getElem?_eq_getElem (by rw [hxC]; exact hj_lt)] at hj_eq
        simp only [wC, xC, List.getElem_ofFn, Option.some.injEq, hi_eq] at hj_eq
        rw [List.getElem?_eq_getElem (by omega : i < w'.length),
            List.getElem?_eq_getElem (by omega : i < x'.length)] at hj_eq ⊢
        simpa using congrArg some hj_eq
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  set M : ℕ := max 64 (Nat.ceil (Real.sqrt (8 * (qn : ℝ))))
  have hM64 : 64 ≤ M := le_max_left _ _
  have hM_le : (M : ℝ) ≤ 65 * Real.sqrt (qn : ℝ) := by
    have hqn_r : (1 : ℝ) ≤ (qn : ℝ) := by exact_mod_cast hqn_pos
    have hsqrt_ge1 : (1 : ℝ) ≤ Real.sqrt (qn : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    rcases le_total 64 (Nat.ceil (Real.sqrt (8 * (qn : ℝ)))) with h | h
    · rw [show M = Nat.ceil (Real.sqrt (8 * (qn : ℝ))) from max_eq_right h]
      have hlt := Nat.ceil_lt_add_one (Real.sqrt_nonneg (8 * (qn : ℝ)))
      have h8 : Real.sqrt (8 * (qn : ℝ)) ≤ 3 * Real.sqrt (qn : ℝ) := by
        rw [Real.sqrt_mul (by norm_num)]
        have hsqrt8 : Real.sqrt 8 ≤ 3 := by rw [Real.sqrt_le_iff]; norm_num
        nlinarith
      linarith
    · rw [show M = 64 from max_eq_left h]
      norm_num
      nlinarith
  have hqn_le_M2 : (qn : ℝ) ≤ (M : ℝ) ^ 2 / 8 := by
    have hM_ge : Real.sqrt (8 * (qn : ℝ)) ≤ (M : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 64 _))
    have hsq : Real.sqrt (8 * (qn : ℝ)) ^ 2 = 8 * (qn : ℝ) :=
      Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg (8 * (qn : ℝ))]
  let PC : Polynomial (ZMod 2) := wordPoly wC - wordPoly xC
  have hPC_ne : PC ≠ 0 := wordPoly_ne_of_ne (hwC.trans hxC.symm) hC_ne
  have hPC_deg : PC.natDegree < qn := wordPoly_sub_natDegree_lt hwC hxC hqn_pos
  let S := (Finset.Icc 1 M).filter (fun d => d % 2 = 1)
  have hS_odd : ∀ d ∈ S, d % 2 = 1 := fun d hd => (Finset.mem_filter.mp hd).2
  have hnot_all_dvd : ¬ ∀ d ∈ S, (Polynomial.X ^ d - 1 : Polynomial (ZMod 2)) ∣ PC := by
    intro hall
    have hle := sum_totient_le_natDegree_of_dvd_F2 S hS_odd hPC_ne hall
    have hle_r : ((∑ d ∈ S, Nat.totient d : ℕ) : ℝ) ≤ (PC.natDegree : ℝ) := by exact_mod_cast hle
    have hdeg_r : (PC.natDegree : ℝ) < (qn : ℝ) := by exact_mod_cast hPC_deg
    have hsum_ge := hqn_le_M2.trans (sum_odd_totient_ge hM64)
    linarith
  push Not at hnot_all_dvd
  rcases hnot_all_dvd with ⟨d, hdS, hndvd⟩
  have hd_mem := Finset.mem_filter.mp hdS
  have hd_pos : 0 < d := (Finset.mem_Icc.mp hd_mem.1).1
  have hd_odd : d % 2 = 1 := hd_mem.2
  have hPC_supp : ∀ j, qn ≤ j → PC.coeff j = 0 := by
    intro j hj
    simp only [PC, Polynomial.coeff_sub, wordPoly_coeff, hwC, hxC]
    rw [if_neg (by omega), if_neg (by omega), sub_self]
  have hex_rC : ∃ rC : Fin d,
      ∑ j ∈ (Finset.range qn).filter (fun j => j % d = rC.1), PC.coeff j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hndvd (X_pow_sub_one_dvd_of_residue_sum_zero hd_pos PC hPC_supp hall)
  rcases hex_rC with ⟨rC, hrC⟩
  -- Map residue `rC` to `r = (r₀ + rC * L) % d`; since `d` is odd and `L = 2^k`, `Nat.Coprime d L`!
  have hcop : Nat.Coprime L d := by
    dsimp [L]
    exact (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hd_odd)).pow_left k
  let r : Fin d := ⟨(r₀ + rC.1 * L) % d, Nat.mod_lt _ hd_pos⟩
  have hsum_eq_C :
      (∑ i ∈ (Finset.range n).filter (fun i => i % d = r.1),
        (boolToF2 (w'[i]?.getD false) - boolToF2 (x'[i]?.getD false))) =
      ∑ j ∈ (Finset.range qn).filter (fun j => j % d = rC.1), PC.coeff j := by
    have hfilter_zero :
        ∑ i ∈ (Finset.range n).filter (fun i => i % d = r.1),
          (boolToF2 (w'[i]?.getD false) - boolToF2 (x'[i]?.getD false)) =
        ∑ i ∈ ((Finset.range n).filter (fun i => i % d = r.1)).filter (fun i => i % L = r₀),
          (boolToF2 (w'[i]?.getD false) - boolToF2 (x'[i]?.getD false)) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun i hi hni => ?_
      have hi_lt : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      have hne_mod : i % L ≠ r₀ := fun hmod => hni (Finset.mem_filter.mpr ⟨hi, hmod⟩)
      have hwx : w[i]? = x[i]? := by
        by_contra hne_i
        exact hne_mod (hspaced i hi_lt hne_i)
      have hwx' : w'[i]? = x'[i]? := by simp only [w', x', List.getElem?_map, hwx]
      rw [hwx', sub_self]
    rw [hfilter_zero]
    have hC_filter :
        ∑ j ∈ (Finset.range qn).filter (fun j => j % d = rC.1), PC.coeff j =
        ∑ j ∈ ((Finset.range qn).filter (fun j => j % d = rC.1)).filter (fun j => r₀ + j * L < n),
          PC.coeff j := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun j hj hnj => ?_
      have hj_lt : j < qn := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hge : n ≤ r₀ + j * L := by
        by_contra hlt; push Not at hlt; exact hnj (Finset.mem_filter.mpr ⟨hj, hlt⟩)
      simp only [PC, Polynomial.coeff_sub, wordPoly_coeff, hwC, hxC, if_pos hj_lt]
      rw [List.getElem?_eq_getElem (by rw [hwC]; exact hj_lt),
          List.getElem?_eq_getElem (by rw [hxC]; exact hj_lt)]
      simp only [wC, xC, List.getElem_ofFn, Option.getD_some]
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega), sub_self]
    rw [hC_filter]
    refine Finset.sum_bij'
      (fun i _ => i / L)
      (fun j _ => r₀ + j * L)
      (fun i hi => ?_)
      (fun j hj => ?_)
      (fun i hi => ?_)
      (fun j hj => ?_)
      (fun i hi => ?_)
    · simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
      rcases hi with ⟨⟨hi_n, hi_d⟩, hi_L⟩
      have hi_eq : r₀ + (i / L) * L = i := by
        rw [← hi_L, mul_comm]; exact Nat.mod_add_div i L
      have hj_qn : i / L < qn := by
        have : i / L ≤ n / L := Nat.div_le_div_right (Nat.le_of_lt hi_n)
        omega
      have hcong : (i / L) * L ≡ rC.1 * L [MOD d] := by
        have h1 : r₀ + (i / L) * L ≡ r₀ + rC.1 * L [MOD d] := by
          change (r₀ + (i / L) * L) % d = (r₀ + rC.1 * L) % d
          rw [hi_eq, hi_d]
        exact Nat.ModEq.add_left_cancel' r₀ h1
      have hj_mod : (i / L) % d = rC.1 := by
        have h2 : i / L ≡ rC.1 [MOD d] := Nat.ModEq.cancel_right_of_coprime hcop.symm hcong
        change (i / L) % d = rC.1 % d at h2
        rwa [Nat.mod_eq_of_lt rC.isLt] at h2
      exact ⟨⟨hj_qn, hj_mod⟩, by rw [hi_eq]; exact hi_n⟩
    · simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      rcases hj with ⟨⟨_, hj_d⟩, hj_n⟩
      have hmod_L : (r₀ + j * L) % L = r₀ := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr₀_lt]
      have hmod_d : (r₀ + j * L) % d = r.1 := by
        have h1 : j ≡ rC.1 [MOD d] := by
          change j % d = rC.1 % d
          rw [hj_d, Nat.mod_eq_of_lt rC.isLt]
        exact Nat.ModEq.add_left r₀ (Nat.ModEq.mul_right L h1)
      exact ⟨⟨hj_n, hmod_d⟩, hmod_L⟩
    · simp only [Finset.mem_filter] at hi
      rw [← hi.2, mul_comm]; exact Nat.mod_add_div i L
    · rw [Nat.add_mul_div_right _ _ hL_pos, Nat.div_eq_of_lt hr₀_lt, zero_add]
    · simp only [Finset.mem_filter, Finset.mem_range] at hi
      rcases hi with ⟨⟨hi_n, _⟩, hi_L⟩
      have hj_qn : i / L < qn := by
        have : i / L ≤ n / L := Nat.div_le_div_right (Nat.le_of_lt hi_n)
        omega
      have hi_eq : r₀ + (i / L) * L = i := by
        rw [← hi_L, mul_comm]; exact Nat.mod_add_div i L
      have hwC_at : wC[i / L]? = some (w'[i]?.getD false) := by
        rw [List.getElem?_eq_getElem (by rw [hwC]; exact hj_qn)]
        simp only [wC, List.getElem_ofFn, hi_eq]
      have hxC_at : xC[i / L]? = some (x'[i]?.getD false) := by
        rw [List.getElem?_eq_getElem (by rw [hxC]; exact hj_qn)]
        simp only [xC, List.getElem_ofFn, hi_eq]
      simp only [PC, Polynomial.coeff_sub, wordPoly_coeff, hwC, hxC, if_pos hj_qn,
        hwC_at, hxC_at, Option.getD_some]
  have hsum_ne :
      ∑ i ∈ (Finset.range w'.length).filter (fun i => i % d = r.1), boolToF2 (w'[i]?.getD false) ≠
      ∑ i ∈ (Finset.range x'.length).filter (fun i => i % d = r.1), boolToF2 (x'[i]?.getD false) := by
    intro heq
    apply hrC
    rw [hw', hx'] at heq
    rw [← hsum_eq_C, Finset.sum_sub_distrib, heq, sub_self]
  refine ⟨2 * d, pullbackDFA f (cyclicParityDFA d hd_pos r), ?_,
    pullbackDFA_bijective f _ (cyclicParityDFA_bijective d hd_pos r), ?_⟩
  · have hdM : (d : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd_mem.1).2
    have hqn_eq : (qn : ℝ) = ((n / (2 ^ k) + 1 : ℕ) : ℝ) := rfl
    rw [hqn_eq] at hM_le
    rw [Nat.cast_mul, Nat.cast_ofNat]
    linarith
  · rw [pullbackDFA_accepts, pullbackDFA_accepts]
    exact cyclicParityDFA_separates_of_sum_ne d hd_pos r w' x' hsum_ne

/-! ## Section 6: Pillar 3 — Demaine–Eisenstat–Shallit–Wilson (2011) `Ω(log n)` Lower Bound -/

private lemma lcm_Icc_eq_prod_prime_pow (t : ℕ) :
    Finset.lcm (Finset.Icc 1 t) id =
      ∏ p ∈ (Finset.Icc 1 t).filter Nat.Prime, p ^ (Nat.log p t) := by
  let L := Finset.lcm (Finset.Icc 1 t) id
  let P := ∏ p ∈ (Finset.Icc 1 t).filter Nat.Prime, p ^ (Nat.log p t)
  have hP_pos : 0 < P :=
    Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.mp hp).2.pos _
  have hL_pos : 0 < L := by
    by_cases ht : t = 0
    · subst ht; simp [L]
    · have h1 : 1 ∈ Finset.Icc 1 t := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
      have hne : L ≠ 0 := by
        intro h0
        have := Finset.lcm_eq_zero_iff.mp h0
        rcases this with ⟨k, hk, hk0⟩
        have := (Finset.mem_Icc.mp hk).1
        simp only [id_eq] at hk0
        omega
      omega
  apply Nat.dvd_antisymm
  · refine Finset.lcm_dvd fun k hk => ?_
    have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
    have hk_le : k ≤ t := (Finset.mem_Icc.mp hk).2
    have hfac := Nat.prod_factorization_pow_eq_self hk_pos.ne'
    rw [Finsupp.prod, Nat.support_factorization] at hfac
    rw [← hfac]
    have hsub : k.primeFactors ⊆ (Finset.Icc 1 t).filter Nat.Prime := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hdvd := Nat.dvd_of_mem_primeFactors hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨hp_prime.pos, (Nat.le_of_dvd hk_pos hdvd).trans hk_le⟩, hp_prime⟩
    have hdvd_sub :
        (∏ p ∈ k.primeFactors, p ^ (k.factorization p)) ∣
          ∏ p ∈ k.primeFactors, p ^ (Nat.log p t) := by
      refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hpow_le : p ^ (k.factorization p) ≤ t :=
        (Nat.le_of_dvd hk_pos (Nat.ordProj_dvd k p)).trans hk_le
      have hlog_ge : k.factorization p ≤ Nat.log p t :=
        (Nat.le_log_iff_pow_le hp_prime.one_lt (by omega : t ≠ 0)).mpr hpow_le
      exact pow_dvd_pow p hlog_ge
    exact hdvd_sub.trans (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
  · have hprod_dvd_nat : ∀ (S : Finset ℕ) (f : ℕ → ℕ),
        (S : Set ℕ).Pairwise (fun p q => Nat.Coprime (f p) (f q)) →
        (∀ p ∈ S, f p ∣ L) → (∏ p ∈ S, f p) ∣ L := by
      intro S f
      induction S using Finset.cons_induction with
      | empty => intro _ _; simp
      | cons a s ha ih =>
        intro hcop hdvd
        rw [Finset.prod_cons]
        have ha_dvd : f a ∣ L := hdvd a (Finset.mem_cons_self a s)
        have hs_dvd : (∏ p ∈ s, f p) ∣ L :=
          ih (hcop.mono (by intro x hx; exact Finset.mem_cons_of_mem hx))
            (fun p hp => hdvd p (Finset.mem_cons_of_mem hp))
        have hcp : Nat.Coprime (f a) (∏ p ∈ s, f p) :=
          Nat.Coprime.prod_right fun p hp =>
            hcop (Finset.mem_cons_self a s) (Finset.mem_cons_of_mem hp) (fun h => ha (h ▸ hp))
        exact hcp.mul_dvd_of_dvd_of_dvd ha_dvd hs_dvd
    refine hprod_dvd_nat _ _ ?_ ?_
    · intro p hp q hq hne
      have hcp := (Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hne
      exact (hcp.pow_left _).pow_right _
    · intro p hp
      have hp_prime := (Finset.mem_filter.mp hp).2
      have hpt : p ≤ t := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      have ht_ne : t ≠ 0 := by have := hp_prime.pos; omega
      have hpow_mem : p ^ Nat.log p t ∈ Finset.Icc 1 t :=
        Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp_prime.pos, Nat.pow_log_le_self p ht_ne⟩
      exact Finset.dvd_lcm hpow_mem

private lemma lcm_Icc_le_exp_six (t : ℕ) :
    ((Finset.lcm (Finset.Icc 1 t) id : ℕ) : ℝ) ≤ Real.exp (6 * (t : ℝ)) := by
  by_cases ht2 : t < 2
  · interval_cases t
    · simp
    · norm_num
  · push Not at ht2
    have ht_r : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht2
    have hlogt_pos : 0 < Real.log (t : ℝ) := Real.log_pos (by linarith)
    have hL_pos : (0 : ℝ) < ((Finset.lcm (Finset.Icc 1 t) id : ℕ) : ℝ) := by
      rw [lcm_Icc_eq_prod_prime_pow]
      exact_mod_cast Finset.prod_pos (s := (Finset.Icc 1 t).filter Nat.Prime)
        fun p hp => pow_pos (Finset.mem_filter.mp hp).2.pos _
    have hlog_eq : Real.log ((Finset.lcm (Finset.Icc 1 t) id : ℕ) : ℝ) =
        Arith4Ext.AnalyticNT.chebyshevPsi (t : ℝ) := by
      rw [lcm_Icc_eq_prod_prime_pow, Arith4Ext.AnalyticNT.chebyshevPsi_nat_eq_sum_primes,
          Nat.cast_prod, Real.log_prod]
      · refine Finset.sum_congr rfl fun p _ => ?_
        rw [Nat.cast_pow, Real.log_pow]
      · intro p hp
        exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (Finset.mem_filter.mp hp).2.ne_zero)
    have hpsi_le : Arith4Ext.AnalyticNT.chebyshevPsi (t : ℝ) ≤ 6 * (t : ℝ) := by
      rw [Arith4Ext.AnalyticNT.chebyshevPsi_nat_eq_sum_primes]
      have hsum_le :
          ∑ p ∈ (Finset.Icc 1 t).filter Nat.Prime, (Nat.log p t : ℝ) * Real.log (p : ℝ) ≤
            (Arith4Ext.AnalyticNT.primePi (t : ℝ) : ℝ) * Real.log (t : ℝ) := by
        simp only [Arith4Ext.AnalyticNT.primePi, Nat.floor_natCast]
        calc
          ∑ p ∈ (Finset.Icc 1 t).filter Nat.Prime, (Nat.log p t : ℝ) * Real.log (p : ℝ)
            ≤ ∑ _p ∈ (Finset.Icc 1 t).filter Nat.Prime, Real.log (t : ℝ) := by
              refine Finset.sum_le_sum fun p hp => ?_
              have hp_prime := (Finset.mem_filter.mp hp).2
              have hpow : p ^ Nat.log p t ≤ t := Nat.pow_log_le_self p (by omega)
              have hle := Real.log_le_log (by exact_mod_cast pow_pos hp_prime.pos _)
                (by exact_mod_cast hpow : ((p ^ Nat.log p t : ℕ) : ℝ) ≤ (t : ℝ))
              rw [Nat.cast_pow, Real.log_pow] at hle
              exact hle
          _ = (((Finset.Icc 1 t).filter Nat.Prime).card : ℝ) * Real.log (t : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hpi := Arith4Ext.AnalyticNT.primePi_le_explicit ht_r
      have hpi_mul : (Arith4Ext.AnalyticNT.primePi (t : ℝ) : ℝ) * Real.log (t : ℝ) ≤
          (4 * Real.log 2 + 2) * (t : ℝ) := by
        have := mul_le_mul_of_nonneg_right hpi hlogt_pos.le
        rwa [div_mul_cancel₀ _ hlogt_pos.ne'] at this
      have hlog2 := log_two_bounds.2
      nlinarith
    rw [← Real.exp_log hL_pos]
    exact Real.exp_le_exp.mpr (by rw [hlog_eq]; exact hpsi_le)

/-- **Pillar 3 — Demaine–Eisenstat–Shallit–Wilson (2011) `Ω(log n)` Lower Bound:**
For every `n ≥ 4`, there exist two distinct binary words `w, x : List Bool` of exact length `n`
(differing in only `2` positions, i.e. Hamming distance `2`) such that EVERY DFA `M : DFA Bool (Fin d)`
separating `w` and `x` requires `(d : ℝ) > Real.log n / 24` states. -/
theorem ppl161_desw_log_lower_bound {n : ℕ} (hn : 4 ≤ n) :
    ∃ w x : List Bool,
      w.length = n ∧ x.length = n ∧ w ≠ x ∧
      ((Finset.range n).filter (fun i => w[i]? ≠ x[i]?)).card = 2 ∧
      ∀ (d : ℕ) (M : DFA Bool (Fin d)),
        (w ∈ M.accepts ↔ x ∉ M.accepts) → Real.log (n : ℝ) / 24 < (d : ℝ) := by
  let t : ℕ := max 1 ⌊Real.log (n : ℝ) / 12⌋₊
  have ht1 : 1 ≤ t := le_max_left _ _
  let L : ℕ := Finset.lcm (Finset.Icc 1 t) id
  have hL_pos : 1 ≤ L := by
    have h1 : 1 ∈ Finset.Icc 1 t := Finset.mem_Icc.mpr ⟨le_rfl, ht1⟩
    have hne : L ≠ 0 := by
      intro h0
      rcases Finset.lcm_eq_zero_iff.mp h0 with ⟨k, hk, hk0⟩
      have := (Finset.mem_Icc.mp hk).1
      simp only [id_eq] at hk0
      omega
    omega
  have hlen_le : 2 * t + L + 1 ≤ n := by
    rcases le_total 1 ⌊Real.log (n : ℝ) / 12⌋₊ with h | h
    · have ht_eq : t = ⌊Real.log (n : ℝ) / 12⌋₊ := max_eq_right h
      have h6t : 6 * (t : ℝ) ≤ Real.log (n : ℝ) / 2 := by
        have hfl : (t : ℝ) ≤ Real.log (n : ℝ) / 12 := by
          rw [ht_eq]
          exact Nat.floor_le (by
            have : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
            linarith)
        linarith
      have hexp_le : Real.exp (6 * (t : ℝ)) ≤ Real.sqrt (n : ℝ) := by
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hlog_sqrt : Real.log (Real.sqrt (n : ℝ)) = Real.log (n : ℝ) / 2 := by
          rw [Real.sqrt_eq_rpow, Real.log_rpow hn_pos]; ring
        rw [← Real.exp_log (Real.sqrt_pos.mpr hn_pos), hlog_sqrt]
        exact Real.exp_le_exp.mpr h6t
      have h2t1_le : (2 * (t : ℝ) + 1) ≤ Real.exp (6 * (t : ℝ)) := by
        have := Real.add_one_le_exp (6 * (t : ℝ))
        linarith
      have hL_le : (L : ℝ) ≤ Real.exp (6 * (t : ℝ)) := lcm_Icc_le_exp_six t
      have h2sqrt : 2 * Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
        have hnr : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hsqrt_ge2 : (2 : ℝ) ≤ Real.sqrt (n : ℝ) := by
          rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
        have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt (by linarith)
        nlinarith
      have hreal : ((2 * t + L + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
        push_cast; linarith
      exact_mod_cast hreal
    · have ht_eq : t = 1 := max_eq_left h
      have hL1 : L = 1 := by dsimp [L]; rw [ht_eq]; decide
      omega
  let r : ℕ := n - (2 * t + L + 1)
  let w : List Bool := List.replicate t false ++ [true] ++ List.replicate (t + L + r) false
  let x : List Bool := List.replicate (t + L) false ++ [true] ++ List.replicate (t + r) false
  have hw_len : w.length = n := by simp [w, r]; omega
  have hx_len : x.length = n := by simp [x, r]; omega
  have hw_get : ∀ i < n, w[i]? = some (decide (i = t)) := by
    intro i hi
    simp only [w]
    by_cases hilt : i < t
    · rw [List.append_assoc, List.getElem?_append_left (by simp; omega),
          List.getElem?_replicate, if_pos hilt, decide_eq_false (by omega)]
    · by_cases hieq : i = t
      · subst hieq
        rw [List.append_assoc, List.getElem?_append_right (by simp), List.length_replicate,
            Nat.sub_self]
        simp
      · rw [List.append_assoc, List.getElem?_append_right (by simp; omega), List.length_replicate]
        have hpos : 1 ≤ i - t := by omega
        rw [List.getElem?_append_right (by simp; omega), List.length_singleton,
            List.getElem?_replicate, if_pos (by omega), decide_eq_false (by omega)]
  have hx_get : ∀ i < n, x[i]? = some (decide (i = t + L)) := by
    intro i hi
    simp only [x]
    by_cases hilt : i < t + L
    · rw [List.append_assoc, List.getElem?_append_left (by simp; omega),
          List.getElem?_replicate, if_pos hilt, decide_eq_false (by omega)]
    · by_cases hieq : i = t + L
      · subst hieq
        rw [List.append_assoc, List.getElem?_append_right (by simp), List.length_replicate,
            Nat.sub_self]
        simp
      · rw [List.append_assoc, List.getElem?_append_right (by simp; omega), List.length_replicate]
        have hpos : 1 ≤ i - (t + L) := by omega
        rw [List.getElem?_append_right (by simp; omega), List.length_singleton,
            List.getElem?_replicate, if_pos (by omega), decide_eq_false (by omega)]
  have hne : w ≠ x := by
    intro heq
    have ht_lt : t < n := by omega
    have h1 := congrArg (fun l => l[t]?) heq
    rw [hw_get t ht_lt, hx_get t ht_lt] at h1
    simp only [Option.some.injEq] at h1
    have hneq : decide (t = t + L) = false := decide_eq_false (by omega)
    rw [hneq] at h1
    simp at h1
  have hham2 : ((Finset.range n).filter (fun i => w[i]? ≠ x[i]?)).card = 2 := by
    have hset : (Finset.range n).filter (fun i => w[i]? ≠ x[i]?) = {t, t + L} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hin, hnei⟩
        rw [hw_get i hin, hx_get i hin] at hnei
        by_contra hnot
        push Not at hnot
        rw [decide_eq_false hnot.1, decide_eq_false hnot.2] at hnei
        exact hnei rfl
      · rintro (rfl | rfl)
        · refine ⟨by omega, ?_⟩
          rw [hw_get t (by omega), hx_get t (by omega)]
          simp [show L ≠ 0 by omega]
        · refine ⟨by omega, ?_⟩
          rw [hw_get (t + L) (by omega), hx_get (t + L) (by omega)]
          simp [show L ≠ 0 by omega]
    rw [hset, Finset.card_pair (by omega : t ≠ t + L)]
  refine ⟨w, x, hw_len, hx_len, hne, hham2, ?_⟩
  intro d M hsep
  have hd_gt : t < d := by
    by_contra hle
    push Not at hle
    have h1 := Arith4Ext.AutomataCombinatorics.dfa_unary_block_lcm_eq hle M
      (List.replicate t false ++ [true]) [] false (t + r) (by omega)
    have h2 := Arith4Ext.AutomataCombinatorics.dfa_unary_block_lcm_eq hle M
      [] ([true] ++ List.replicate (t + r) false) false t (by omega)
    simp only [List.append_nil, List.nil_append] at h1 h2
    have hw_eq : List.replicate t false ++ [true] ++ List.replicate (t + r + L) false = w := by
      simp [w, show t + r + L = t + L + r by omega]
    have hx_eq : List.replicate (t + L) false ++ ([true] ++ List.replicate (t + r) false) = x := by
      simp [x, List.append_assoc]
    have hmid_eq : List.replicate t false ++ ([true] ++ List.replicate (t + r) false) =
        List.replicate t false ++ [true] ++ List.replicate (t + r) false := by
      simp [List.append_assoc]
    rw [hw_eq] at h1
    rw [hx_eq, hmid_eq] at h2
    have hiff : w ∈ M.accepts ↔ x ∈ M.accepts := h1.trans h2.symm
    tauto
  have ht_ge_log : Real.log (n : ℝ) / 24 ≤ (t : ℝ) := by
    by_cases hbig : 2 ≤ Real.log (n : ℝ) / 12
    · have hfl : Real.log (n : ℝ) / 12 - 1 < (⌊Real.log (n : ℝ) / 12⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one (Real.log (n : ℝ) / 12); linarith
      have htle : (⌊Real.log (n : ℝ) / 12⌋₊ : ℝ) ≤ (t : ℝ) := by exact_mod_cast le_max_right 1 _
      linarith
    · have ht1_r : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
      linarith
  have hd_gt_r : (t : ℝ) < (d : ℝ) := by exact_mod_cast hd_gt
  linarith

/-! ## Section 7: Pillar 4 — Hamming-Weight, Odd-Hamming, General Hamming-Distance & Exact Small-`n` Bounds -/

/-- **Hamming-Weight `O(log Δ)` Separator:**
Whenever two binary words `w, x : List Bool` have distinct Hamming weights
(`w.count true ≠ x.count true`, difference `Δ = |w.count true - x.count true|`),
there is a cyclic `true`-counter DFA on `Fin p` separating `w` and `x` with
`p ≤ 4 * Real.log Δ + 4098` states (in particular `O(log h)` when Hamming distance is `h`). -/
theorem ppl161_hamming_weight_log_separator (w x : List Bool)
    (hne : w.count true ≠ x.count true) :
    ∃ (p : ℕ) (M : DFA Bool (Fin p)),
      (p : ℝ) ≤ 4 * Real.log ((if w.count true < x.count true
        then x.count true - w.count true
        else w.count true - x.count true : ℕ) : ℝ) + 4098 ∧
      (w ∈ M.accepts ↔ x ∉ M.accepts) := by
  let Δ := if w.count true < x.count true then x.count true - w.count true else w.count true - x.count true
  have hΔ_pos : 1 ≤ Δ := by dsimp [Δ]; split_ifs <;> omega
  obtain ⟨p, hp_prime, hndvd, hp_le⟩ := exists_prime_not_dvd_explicit hΔ_pos
  have hmod_ne : w.count true % p ≠ x.count true % p := by
    intro hmod
    apply hndvd
    dsimp [Δ]
    split_ifs with hlt
    · exact (Nat.modEq_iff_dvd' (Nat.le_of_lt hlt)).mp hmod
    · exact (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
  let r : Fin p := ⟨w.count true % p, Nat.mod_lt _ hp_prime.pos⟩
  refine ⟨p, countModDFA p hp_prime.pos r, hp_le, ?_⟩
  rw [countModDFA_accepts_iff, countModDFA_accepts_iff]
  simp [r, hmod_ne.symm]

/-- **Exact `2`-State Odd-Hamming Separator:**
Whenever two equal-length binary words `w, x : List Bool` have ODD Hamming distance,
they are separated by a `2`-state parity DFA (`Fin 2`). -/
theorem ppl161_hamming_odd_two_state {n : ℕ} (w x : List Bool)
    (hw : w.length = n) (hx : x.length = n)
    (hodd : ((Finset.range n).filter (fun i => w[i]? ≠ x[i]?)).card % 2 = 1) :
    ∃ M : DFA Bool (Fin 2), w ∈ M.accepts ↔ x ∉ M.accepts := by
  refine ⟨cyclicParityDFA 1 (by norm_num) ⟨0, by norm_num⟩, ?_⟩
  apply cyclicParityDFA_separates_of_sum_ne
  intro heq
  have hdiff_sum :
      ∑ i ∈ Finset.range n, (boolToF2 (w[i]?.getD false) - boolToF2 (x[i]?.getD false)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hf : ∀ m, (Finset.range m).filter (fun i => i % 1 = 0) = Finset.range m := by
      intro m; ext i; simp [Nat.mod_one]
    rw [hf w.length, hf x.length, hw, hx] at heq
    rw [heq, sub_self]
  have hcard_eq :
      ∑ i ∈ Finset.range n, (boolToF2 (w[i]?.getD false) - boolToF2 (x[i]?.getD false)) =
        ((((Finset.range n).filter (fun i => w[i]? ≠ x[i]?)).card : ℕ) : ZMod 2) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hilt : i < n := Finset.mem_range.mp hi
    rw [List.getElem?_eq_getElem (by omega : i < w.length),
        List.getElem?_eq_getElem (by omega : i < x.length)]
    cases w[i] <;> cases x[i] <;> decide
  rw [hcard_eq] at hdiff_sum
  have hmod : ((((Finset.range n).filter (fun i => w[i]? ≠ x[i]?)).card : ℕ) : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, hodd]; simp
  rw [hmod] at hdiff_sum
  exact one_ne_zero hdiff_sum

/-- **General Hamming-Distance `O(h log n)` Separator:**
For every `n ≥ 2` and every two distinct length-`n` binary words `w, x : List Bool` at Hamming
distance `h`, there exists a `2p`-state cyclic parity DFA separating `w` and `x` with
`2 * p ≤ 8 * h * log n + 8196` (matching the DESW `Ω(log n)` lower bound at `h = 2`). -/
theorem ppl161_hamming_dist_upper {n : ℕ} (hn : 2 ≤ n) (w x : List Bool)
    (hw : w.length = n) (hx : x.length = n) (hne : w ≠ x) :
    ∃ (m : ℕ) (M : DFA Bool (Fin m)),
      (m : ℝ) ≤ 8 * (((Finset.range n).filter (fun i => w[i]? ≠ x[i]?)).card : ℝ) *
        Real.log (n : ℝ) + 8196 ∧
      (w ∈ M.accepts ↔ x ∉ M.accepts) := by
  let D := (Finset.range n).filter (fun i => w[i]? ≠ x[i]?)
  have hD_nonempty : D.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hne
    apply List.ext_getElem?
    intro i
    by_cases hi : i < n
    · by_contra hnei
      have : i ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hnei⟩
      rw [hempty] at this
      exact Finset.notMem_empty i this
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  let i₀ := D.min' hD_nonempty
  have hi₀_mem : i₀ ∈ D := Finset.min'_mem D hD_nonempty
  have hi₀_lt : i₀ < n := Finset.mem_range.mp (Finset.mem_filter.mp hi₀_mem).1
  let K : ℕ := ∏ j ∈ D.erase i₀, (j - i₀)
  have hK_pos : 1 ≤ K := by
    have hpos : 0 < K := Finset.prod_pos fun j hj => by
      have hj_mem : j ∈ D := Finset.mem_of_mem_erase hj
      have hj_ne : j ≠ i₀ := (Finset.mem_erase.mp hj).1
      have hj_ge : i₀ ≤ j := Finset.min'_le D j hj_mem
      omega
    omega
  have hK_le : K ≤ n ^ D.card := by
    calc
      K = ∏ j ∈ D.erase i₀, (j - i₀) := rfl
      _ ≤ ∏ _j ∈ D.erase i₀, n := Finset.prod_le_prod' fun j hj => by
          have hj_lt : j < n := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)).1
          omega
      _ = n ^ (D.erase i₀).card := by rw [Finset.prod_const]
      _ ≤ n ^ D.card := Nat.pow_le_pow_right (by omega) (Finset.card_erase_le)
  obtain ⟨p, hp_prime, hndvd, hp_le⟩ := exists_prime_not_dvd_explicit hK_pos
  have hisol : ∀ j ∈ D, j % p = i₀ % p → j = i₀ := by
    intro j hj hmod
    by_contra hne_j
    have hj_ge : i₀ ≤ j := Finset.min'_le D j hj
    have hdvd_diff : p ∣ (j - i₀) := (Nat.modEq_iff_dvd' hj_ge).mp hmod.symm
    have hdvd_K : p ∣ K := hdvd_diff.trans (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hne_j, hj⟩))
    exact hndvd hdvd_K
  let r : Fin p := ⟨i₀ % p, Nat.mod_lt _ hp_prime.pos⟩
  have hsum_ne :
      ∑ i ∈ (Finset.range w.length).filter (fun i => i % p = r.1), boolToF2 (w[i]?.getD false) ≠
      ∑ i ∈ (Finset.range x.length).filter (fun i => i % p = r.1), boolToF2 (x[i]?.getD false) := by
    intro heq
    rw [hw, hx] at heq
    have hdiff0 :
        ∑ i ∈ (Finset.range n).filter (fun i => i % p = r.1),
          (boolToF2 (w[i]?.getD false) - boolToF2 (x[i]?.getD false)) = 0 := by
      rw [Finset.sum_sub_distrib, heq, sub_self]
    have hsingle :
        ∑ i ∈ (Finset.range n).filter (fun i => i % p = r.1),
          (boolToF2 (w[i]?.getD false) - boolToF2 (x[i]?.getD false)) =
        boolToF2 (w[i₀]?.getD false) - boolToF2 (x[i₀]?.getD false) := by
      refine Finset.sum_eq_single i₀ ?_ ?_
      · intro j hj hjne
        have hj_lt : j < n := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        have hj_mod : j % p = i₀ % p := (Finset.mem_filter.mp hj).2
        have hwx : w[j]? = x[j]? := by
          by_contra hne_wx
          exact hjne (hisol j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj_lt, hne_wx⟩) hj_mod)
        rw [hwx, sub_self]
      · intro hi₀_nmem
        exact False.elim (hi₀_nmem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi₀_lt, rfl⟩))
    rw [hsingle] at hdiff0
    have hwi0 : w[i₀]?.getD false = x[i₀]?.getD false := boolToF2_inj (sub_eq_zero.mp hdiff0)
    have hne_i0 : w[i₀]? ≠ x[i₀]? := (Finset.mem_filter.mp hi₀_mem).2
    rw [List.getElem?_eq_getElem (by omega : i₀ < w.length),
        List.getElem?_eq_getElem (by omega : i₀ < x.length)] at hwi0 hne_i0
    exact hne_i0 (congrArg some hwi0)
  refine ⟨2 * p, cyclicParityDFA p hp_prime.pos r, ?_,
    cyclicParityDFA_separates_of_sum_ne p hp_prime.pos r w x hsum_ne⟩
  have hlogK : Real.log (K : ℝ) ≤ (D.card : ℝ) * Real.log (n : ℝ) := by
    have hle := Real.log_le_log (by exact_mod_cast hK_pos : (0 : ℝ) < (K : ℝ))
      (by exact_mod_cast hK_le : (K : ℝ) ≤ ((n ^ D.card : ℕ) : ℝ))
    rw [Nat.cast_pow, Real.log_pow] at hle
    exact hle
  push_cast
  linarith

/-! ## Section 8: Exact Small-`n` Separation Numbers (`0` `native_decide`) -/

/-- **Exact `sep(1) = 2`:** No 1-state DFA separates any two words, while every two distinct
length-1 words over any alphabet `α` are separated by a 2-state DFA. -/
theorem ppl161_exact_sep_one {α : Type*} :
    (∀ (M : DFA α (Fin 1)) (w x : List α), ¬ (w ∈ M.accepts ↔ x ∉ M.accepts)) ∧
    (∀ (w x : List α), w.length = 1 → x.length = 1 → w ≠ x →
      ∃ M : DFA α (Fin 2), w ∈ M.accepts ↔ x ∉ M.accepts) := by
  classical
  constructor
  · intro M w x hsep
    have heval : M.eval w = M.eval x := Subsingleton.elim _ _
    have hiff : w ∈ M.accepts ↔ x ∈ M.accepts := by
      change M.eval w ∈ M.accept ↔ M.eval x ∈ M.accept
      rw [heval]
    tauto
  · intro w x hw hx hne
    rcases List.length_eq_one_iff.mp hw with ⟨a, rfl⟩
    rcases List.length_eq_one_iff.mp hx with ⟨b, rfl⟩
    have hab : a ≠ b := fun h => hne (by subst h; rfl)
    let M : DFA α (Fin 2) := {
      step := fun _ c => if c = a then 1 else 0
      start := 0
      accept := {1}
    }
    refine ⟨M, ?_⟩
    change M.eval [a] ∈ ({1} : Set (Fin 2)) ↔ M.eval [b] ∉ ({1} : Set (Fin 2))
    simp [M, DFA.eval, DFA.evalFrom, hab.symm]

/-- **Exact `sep(2) = 2`:** Every two distinct length-2 words over any alphabet `α`
are separated by a 2-state DFA. -/
theorem ppl161_exact_sep_two {α : Type*} (w x : List α)
    (hw : w.length = 2) (hx : x.length = 2) (hne : w ≠ x) :
    ∃ M : DFA α (Fin 2), w ∈ M.accepts ↔ x ∉ M.accepts := by
  classical
  rcases w with _ | ⟨a₁, _ | ⟨a₂, _ | _⟩⟩ <;> simp at hw
  rcases x with _ | ⟨b₁, _ | ⟨b₂, _ | _⟩⟩ <;> simp at hx
  by_cases h2 : a₂ ≠ b₂
  · let M : DFA α (Fin 2) := {
      step := fun _ c => if c = a₂ then 1 else 0
      start := 0
      accept := {1}
    }
    refine ⟨M, ?_⟩
    change M.eval [a₁, a₂] ∈ ({1} : Set (Fin 2)) ↔ M.eval [b₁, b₂] ∉ ({1} : Set (Fin 2))
    simp [M, DFA.eval, DFA.evalFrom, h2.symm]
  · push Not at h2
    subst h2
    have h1 : a₁ ≠ b₁ := fun h => hne (by subst h; rfl)
    by_cases ha12 : a₁ = a₂
    · subst ha12
      -- `[a₁, a₁]` vs `[b₁, a₁]` with `b₁ ≠ a₁`: "all letters equal `a₁`"
      let M : DFA α (Fin 2) := {
        step := fun q c => if q = 0 ∧ c = a₁ then 0 else 1
        start := 0
        accept := {0}
      }
      refine ⟨M, ?_⟩
      change M.eval [a₁, a₁] ∈ ({0} : Set (Fin 2)) ↔ M.eval [b₁, a₁] ∉ ({0} : Set (Fin 2))
      simp [M, DFA.eval, DFA.evalFrom, h1.symm]
    · -- `a₁ ≠ a₂` and `a₁ ≠ b₁`: mark seeing `a₁` on state `0`, keep `1` on `a₂`
      let M : DFA α (Fin 2) := {
        step := fun q c =>
          if q = 0 then (if c = a₁ then 1 else 0)
          else (if c = a₂ then 1 else 0)
        start := 0
        accept := {1}
      }
      refine ⟨M, ?_⟩
      change M.eval [a₁, a₂] ∈ ({1} : Set (Fin 2)) ↔ M.eval [b₁, a₂] ∉ ({1} : Set (Fin 2))
      simp [M, DFA.eval, DFA.evalFrom, h1.symm, Ne.symm ha12]

/-- **Exact `sep(3) = 2`:** Every two distinct length-3 words over any alphabet `α`
are separated by a 2-state DFA. -/
theorem ppl161_exact_sep_three {α : Type*} (w x : List α)
    (hw : w.length = 3) (hx : x.length = 3) (hne : w ≠ x) :
    ∃ M : DFA α (Fin 2), w ∈ M.accepts ↔ x ∉ M.accepts := by
  obtain ⟨f, hfne, hfw, hfx⟩ := exists_bool_projection (hw.trans hx.symm) hne
  have hbool : ∀ u v : List Bool, u.length = 3 → v.length = 3 → u ≠ v →
      ∃ M : DFA Bool (Fin 2), u ∈ M.accepts ↔ v ∉ M.accepts := by
    intro u v hu hv huv
    rcases u with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, _ | _⟩⟩⟩ <;> simp at hu
    rcases v with _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | _⟩⟩⟩ <;> simp at hv
    let M_last : DFA Bool (Fin 2) := {
      step := fun _ b => if b then 1 else 0
      start := 0
      accept := {1}
    }
    let M_par : DFA Bool (Fin 2) := {
      step := fun q b => if b then (if q = 0 then 1 else 0) else q
      start := 0
      accept := {1}
    }
    let M_all0 : DFA Bool (Fin 2) := {
      step := fun q b => if q = 0 ∧ b = false then 0 else 1
      start := 0
      accept := {0}
    }
    let M_all1 : DFA Bool (Fin 2) := {
      step := fun q b => if q = 0 ∧ b = true then 0 else 1
      start := 0
      accept := {0}
    }
    let M_swap0 : DFA Bool (Fin 2) := {
      step := fun q b => if b then 0 else (if q = 0 then 1 else 0)
      start := 0
      accept := {1}
    }
    let M_swap1 : DFA Bool (Fin 2) := {
      step := fun q b => if b then (if q = 0 then 1 else 0) else 0
      start := 0
      accept := {1}
    }
    cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃
    all_goals first
      | exact False.elim (huv rfl)
      | exact dfa_sep_of_eval_ne M_last (by decide)
      | exact dfa_sep_of_eval_ne M_par (by decide)
      | exact dfa_sep_of_eval_ne M_all0 (by decide)
      | exact dfa_sep_of_eval_ne M_all1 (by decide)
      | exact dfa_sep_of_eval_ne M_swap0 (by decide)
      | exact dfa_sep_of_eval_ne M_swap1 (by decide)
  obtain ⟨M, hsep⟩ := hbool (w.map f) (x.map f) (hfw.trans hw) (hfx.trans hx) hfne
  refine ⟨pullbackDFA f M, ?_⟩
  rw [pullbackDFA_accepts, pullbackDFA_accepts]
  exact hsep

/-- **Exact `sep(4) ≥ 3` Lower Bound (`0` `native_decide`):**
The length-4 binary words `[false, false, true, false]` (`0010`) and `[true, false, false, false]`
(`1000`) cannot be separated by ANY 2-state DFA `M : DFA Bool (Fin 2)`. -/
theorem ppl161_exact_sep_four_lower :
    ∃ w x : List Bool, w.length = 4 ∧ x.length = 4 ∧ w ≠ x ∧
      ∀ M : DFA Bool (Fin 2), ¬ (w ∈ M.accepts ↔ x ∉ M.accepts) := by
  refine ⟨[false, false, true, false], [true, false, false, false], rfl, rfl, by decide, ?_⟩
  intro M hsep
  have heval : M.eval [false, false, true, false] = M.eval [true, false, false, false] := by
    change M.step (M.step (M.step (M.step M.start false) false) true) false =
      M.step (M.step (M.step (M.step M.start true) false) false) false
    generalize hs : M.start = s
    generalize h00 : M.step 0 false = f00
    generalize h10 : M.step 1 false = f10
    generalize h01 : M.step 0 true = f01
    generalize h11 : M.step 1 true = f11
    fin_cases s <;> fin_cases f00 <;> fin_cases f10 <;> fin_cases f01 <;> fin_cases f11 <;>
      simp_all
  have hiff : [false, false, true, false] ∈ M.accepts ↔ [true, false, false, false] ∈ M.accepts := by
    change M.eval [false, false, true, false] ∈ M.accept ↔
      M.eval [true, false, false, false] ∈ M.accept
    rw [heval]
  tauto

/-- **Exact `sep(4) ≤ 3` Upper Bound (`0` `native_decide`):**
Every two distinct length-4 words over any alphabet `α` are separated by a 3-state DFA,
establishing `sep(4) = 3`. -/
theorem ppl161_exact_sep_four_upper {α : Type*} (w x : List α)
    (hw : w.length = 4) (hx : x.length = 4) (hne : w ≠ x) :
    ∃ M : DFA α (Fin 3), w ∈ M.accepts ↔ x ∉ M.accepts := by
  obtain ⟨f, hfne, hfw, hfx⟩ := exists_bool_projection (hw.trans hx.symm) hne
  have hbool : ∀ u v : List Bool, u.length = 4 → v.length = 4 → u ≠ v →
      ∃ M : DFA Bool (Fin 3), u ∈ M.accepts ↔ v ∉ M.accepts := by
    intro u v hu hv huv
    rcases u with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, _ | ⟨a₄, _ | _⟩⟩⟩⟩ <;> simp at hu
    rcases v with _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨b₄, _ | _⟩⟩⟩⟩ <;> simp at hv
    let M_pos0 : DFA Bool (Fin 3) := {
      step := fun q b => if q = 0 then (if b then 1 else 2) else q
      start := 0
      accept := {1}
    }
    let M_last : DFA Bool (Fin 3) := {
      step := fun _ b => if b then 1 else 0
      start := 0
      accept := {1}
    }
    let M_par : DFA Bool (Fin 3) := {
      step := fun q b => if b then (if q = 0 then 1 else 0) else q
      start := 0
      accept := {1}
    }
    let M_mod3 : DFA Bool (Fin 3) := {
      step := fun q b => if b then ⟨(q.1 + 1) % 3, Nat.mod_lt _ (by norm_num)⟩ else q
      start := 0
      accept := {0}
    }
    let M_01 : DFA Bool (Fin 3) := {
      step := fun q b =>
        if q = 2 then 2
        else if q = 1 then (if b then 2 else 1)
        else (if b then 0 else 1)
      start := 0
      accept := {2}
    }
    let M_10 : DFA Bool (Fin 3) := {
      step := fun q b =>
        if q = 2 then 2
        else if q = 1 then (if b then 1 else 2)
        else (if b then 1 else 0)
      start := 0
      accept := {2}
    }
    let M_11 : DFA Bool (Fin 3) := {
      step := fun q b =>
        if q = 2 then 2
        else if q = 1 then (if b then 2 else 0)
        else (if b then 1 else 0)
      start := 0
      accept := {2}
    }
    let M_00 : DFA Bool (Fin 3) := {
      step := fun q b =>
        if q = 2 then 2
        else if q = 1 then (if b then 0 else 2)
        else (if b then 0 else 1)
      start := 0
      accept := {2}
    }
    let M_trail0 : DFA Bool (Fin 3) := {
      step := fun q b => if b then 0 else ⟨(q.1 + 1) % 3, Nat.mod_lt _ (by norm_num)⟩
      start := 0
      accept := {1}
    }
    let M_trail1 : DFA Bool (Fin 3) := {
      step := fun q b => if b then ⟨(q.1 + 1) % 3, Nat.mod_lt _ (by norm_num)⟩ else 0
      start := 0
      accept := {1}
    }
    cases a₁ <;> cases a₂ <;> cases a₃ <;> cases a₄ <;>
      cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄
    all_goals first
      | exact False.elim (huv rfl)
      | exact dfa_sep_of_eval_ne M_pos0 (by decide)
      | exact dfa_sep_of_eval_ne M_last (by decide)
      | exact dfa_sep_of_eval_ne M_par (by decide)
      | exact dfa_sep_of_eval_ne M_mod3 (by decide)
      | exact dfa_sep_of_eval_ne M_01 (by decide)
      | exact dfa_sep_of_eval_ne M_10 (by decide)
      | exact dfa_sep_of_eval_ne M_11 (by decide)
      | exact dfa_sep_of_eval_ne M_00 (by decide)
      | exact dfa_sep_of_eval_ne M_trail0 (by decide)
      | exact dfa_sep_of_eval_ne M_trail1 (by decide)
  obtain ⟨M, hsep⟩ := hbool (w.map f) (x.map f) (hfw.trans hw) (hfx.trans hx) hfne
  refine ⟨pullbackDFA f M, ?_⟩
  rw [pullbackDFA_accepts, pullbackDFA_accepts]
  exact hsep

end PPL161
