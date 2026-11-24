/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Computability.DFA
import Mathlib.Computability.NFA
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-!
# PPL 121 (Shallit Open Problem #4): Unconditional Theorems and Extremal Witnesses on `sep(w, x) / nsep(w, x)`

## Honest Scope Notice
PPL 121 (Shallit Open Problem #4 — whether `sep(w, x) = O(nsep(w, x))`, £50) remains **OPEN**.
The current best asymptotic lower bound in the literature is Nicol (August 2026, `arXiv:2608.30928`),
achieving `sep / nsep = Ω(log L / (log log L)^2)`.

This module formalizes four clean, unconditional results in pure Mathlib (`DFA` and `NFA`,
with zero custom or private definitions appearing in any public theorem signature):

1. **`determinization_ceiling` (`sep ≤ 2 ^ nsep`):**
   Every `m`-state NFA separating `w` and `x` determinizes via `NFA.toDFA` to a
   `2 ^ m`-state DFA separating `w` and `x`.
2. **`two_state_reversal_to_three_state` (`T₂^{op} ∈ HSP(T₃)`):**
   For every alphabet `α` and words `w, x : List α`, if a `2`-state DFA separates `w.reverse`
   and `x.reverse`, then some `3`-state DFA separates `w` and `x`.
3. **Exact `L = 10` Subset-Construction Ceiling Witness (`sep = 4 = 2^2`, `nsep = 2`, `sep(w^R, x^R) = 3`):**
   For `w = 010^8` and `x = 0^7 1 0^2` (without `native_decide`), we prove:
   - `l10_witness_nsep_le_two`: separated by an explicit `2`-state `NFA Bool (Fin 2)`;
   - `l10_witness_rev_sep_le_three`: reversals separated by an explicit `3`-state `DFA Bool (Fin 3)`;
   - `l10_witness_sep_ge_four`: indistinguishable by every `DFA Bool (Fin 3)`.
4. **DESW (2011) Quadratic Separation-Ratio Family (`desw_quadratic_gap`, `unbounded_sep_nsep_ratio`):**
   For every `k ≥ 3`, setting `t = k * (k - 1)` and `L = lcm(1..t)`, the equal-length words
   `w_k = 0^{t - 1 + L} 1^{t - 1}` and `x_k = 0^{t - 1} 1^{t - 1 + L}` satisfy:
   - `nsep(w_k, x_k) ≤ 2 * k + 1` via a `(2k + 1)`-state Frobenius `(k, k + 1)` NFA;
   - `sep(w_k, x_k) > k * (k - 1)` against every DFA on `Fin d` (`d ≤ k * (k - 1)`).
   In particular, for every `C : ℕ`, there exist equal-length binary words separated by an
   `m`-state NFA (`m ≥ 1`) that no `(C * m)`-state DFA can separate (`sep / nsep` is unbounded).
-/

namespace PPL121Ratio

/-! ## Section 1: Determinization Ceiling (`sep ≤ 2 ^ nsep`) -/

section Determinization

private def mapDFA {α Q₁ Q₂ : Type*} (e : Q₁ ≃ Q₂) (M : DFA α Q₁) : DFA α Q₂ where
  step q a := e (M.step (e.symm q) a)
  start := e M.start
  accept := e.symm ⁻¹' M.accept

private lemma mapDFA_evalFrom {α Q₁ Q₂ : Type*} (e : Q₁ ≃ Q₂) (M : DFA α Q₁) :
    ∀ (q : Q₁) (u : List α), (mapDFA e M).evalFrom (e q) u = e (M.evalFrom q u)
  | q, [] => rfl
  | q, a :: u => by
    simp only [DFA.evalFrom, List.foldl_cons, mapDFA]
    rw [Equiv.symm_apply_apply]
    exact mapDFA_evalFrom e M (M.step q a) u

private lemma mapDFA_accepts {α Q₁ Q₂ : Type*} (e : Q₁ ≃ Q₂) (M : DFA α Q₁) (u : List α) :
    u ∈ (mapDFA e M).accepts ↔ u ∈ M.accepts := by
  change (mapDFA e M).evalFrom (e M.start) u ∈ (e.symm ⁻¹' M.accept) ↔
    M.evalFrom M.start u ∈ M.accept
  rw [mapDFA_evalFrom, Set.mem_preimage, Equiv.symm_apply_apply]

/-- **Determinization Ceiling (`sep ≤ 2 ^ nsep`):**
If an `m`-state NFA separates `w` and `x`, then some `(2 ^ m)`-state DFA separates `w` and `x`. -/
theorem determinization_ceiling {α : Type*} (m : ℕ) (w x : List α)
    (h : ∃ N : NFA α (Fin m), w ∈ N.accepts ↔ x ∉ N.accepts) :
    ∃ M : DFA α (Fin (2 ^ m)), w ∈ M.accepts ↔ x ∉ M.accepts := by
  classical
  rcases h with ⟨N, hsep⟩
  let e : Set (Fin m) ≃ Fin (2 ^ m) := Fintype.equivFinOfCardEq (by simp)
  refine ⟨mapDFA e N.toDFA, ?_⟩
  rw [mapDFA_accepts, mapDFA_accepts, NFA.toDFA_correct]
  exact hsep

end Determinization

/-! ## Section 2: Exact `2 → 3` Reversal Theorem (`T₂^{op} ∈ HSP(T₃)`) -/

section ReversalTwoToThree

private def revD1 {α : Type*} (M : DFA α (Fin 2)) : DFA α (Fin 3) where
  start := 0
  step q a :=
    let s0 := M.step 0 a
    let s1 := M.step 1 a
    if s0 = 0 ∧ s1 = 1 then q
    else if s0 = 1 ∧ s1 = 0 then (if q = 0 then 0 else if q = 1 then 2 else 1)
    else if s0 = 0 ∧ s1 = 0 then (if q = 0 then 1 else q)
    else (if q = 0 then 1 else if q = 1 then 2 else 1)
  accept := {2}

private def revD2 {α : Type*} (M : DFA α (Fin 2)) : DFA α (Fin 2) where
  start := 0
  step q a :=
    let s0 := M.step 0 a
    let s1 := M.step 1 a
    if (s0 = 0 ∧ s1 = 1) ∨ (s0 = 0 ∧ s1 = 0) then q
    else (if q = 0 then 1 else 0)
  accept := {1}

private lemma dfa_evalFrom_append {α Q : Type*} (M : DFA α Q) (q : Q) (u v : List α) :
    M.evalFrom q (u ++ v) = M.evalFrom (M.evalFrom q u) v := by
  simp [DFA.evalFrom, List.foldl_append]

private lemma revD1_D2_invariant {α : Type*} (M : DFA α (Fin 2)) :
    ∀ u : List α,
      let f0 := M.evalFrom 0 u.reverse
      let f1 := M.evalFrom 1 u.reverse
      let d1 := (revD1 M).eval u
      let d2 := (revD2 M).eval u
      (f0 = 0 ∧ f1 = 1 ∧ d1 = 0 ∧ d2 = 0) ∨
      (f0 = 1 ∧ f1 = 0 ∧ d1 = 0 ∧ d2 = 1) ∨
      (f0 = 0 ∧ f1 = 0 ∧ ((d1 = 1 ∧ d2 = 0) ∨ (d1 = 2 ∧ d2 = 1))) ∨
      (f0 = 1 ∧ f1 = 1 ∧ ((d1 = 1 ∧ d2 = 1) ∨ (d1 = 2 ∧ d2 = 0))) := by
  intro u
  induction u using List.reverseRecOn with
  | nil =>
    simp [DFA.eval, DFA.evalFrom, revD1, revD2]
  | append_singleton u a ih =>
    dsimp only at ih ⊢
    have hf0 : M.evalFrom 0 (u ++ [a]).reverse = M.evalFrom (M.step 0 a) u.reverse := by
      simp [DFA.evalFrom]
    have hf1 : M.evalFrom 1 (u ++ [a]).reverse = M.evalFrom (M.step 1 a) u.reverse := by
      simp [DFA.evalFrom]
    have hd1 : (revD1 M).eval (u ++ [a]) = (revD1 M).step ((revD1 M).eval u) a := by
      simp [DFA.eval, DFA.evalFrom]
    have hd2 : (revD2 M).eval (u ++ [a]) = (revD2 M).step ((revD2 M).eval u) a := by
      simp [DFA.eval, DFA.evalFrom]
    rw [hf0, hf1, hd1, hd2]
    rcases ih with ⟨h0, h1, hd1', hd2'⟩ | ⟨h0, h1, hd1', hd2'⟩ |
      ⟨h0, h1, (⟨hd1', hd2'⟩ | ⟨hd1', hd2'⟩)⟩ | ⟨h0, h1, (⟨hd1', hd2'⟩ | ⟨hd1', hd2'⟩)⟩
    all_goals
      rw [hd1', hd2']
      dsimp only [revD1, revD2]
      generalize hs0 : M.step 0 a = s0
      generalize hs1 : M.step 1 a = s1
      fin_cases s0 <;> fin_cases s1 <;> simp [h0, h1]

private lemma revD1_D2_determines_f0 {α : Type*} (M : DFA α (Fin 2)) (u : List α) :
    M.evalFrom 0 u.reverse = 0 ↔
      xor (decide ((revD1 M).eval u = 2)) (decide ((revD2 M).eval u = 1)) = false := by
  have hinv := revD1_D2_invariant M u
  dsimp only at hinv
  rcases hinv with ⟨h0, _, hd1, hd2⟩ | ⟨h0, _, hd1, hd2⟩ |
    ⟨h0, _, (⟨hd1, hd2⟩ | ⟨hd1, hd2⟩)⟩ | ⟨h0, _, (⟨hd1, hd2⟩ | ⟨hd1, hd2⟩)⟩ <;>
    simp [h0, hd1, hd2]

private def liftFin2toFin3 {α : Type*} (M : DFA α (Fin 2)) : DFA α (Fin 3) where
  start := Fin.castLE (by omega) M.start
  step q a :=
    if h : q.1 < 2 then Fin.castLE (by omega) (M.step ⟨q.1, h⟩ a) else 2
  accept := Fin.castLE (by omega) '' M.accept

private lemma liftFin2toFin3_step {α : Type*} (M : DFA α (Fin 2)) (q : Fin 2) (a : α) :
    (liftFin2toFin3 M).step (Fin.castLE (by omega) q) a =
      Fin.castLE (by omega) (M.step q a) := by
  change (if h : (Fin.castLE (by omega : 2 ≤ 3) q).1 < 2 then
      Fin.castLE (by omega) (M.step ⟨_, h⟩ a) else 2) = Fin.castLE (by omega) (M.step q a)
  have hq : (Fin.castLE (by omega : 2 ≤ 3) q).1 < 2 := q.isLt
  rw [dif_pos hq]
  rfl

private lemma liftFin2toFin3_evalFrom {α : Type*} (M : DFA α (Fin 2)) :
    ∀ (q : Fin 2) (u : List α),
      (liftFin2toFin3 M).evalFrom (Fin.castLE (by omega) q) u =
        Fin.castLE (by omega) (M.evalFrom q u)
  | q, [] => rfl
  | q, a :: u => by
    change (liftFin2toFin3 M).evalFrom ((liftFin2toFin3 M).step (Fin.castLE (by omega) q) a) u =
      Fin.castLE (by omega) (M.evalFrom (M.step q a) u)
    rw [liftFin2toFin3_step]
    exact liftFin2toFin3_evalFrom M (M.step q a) u

private lemma liftFin2toFin3_accepts {α : Type*} (M : DFA α (Fin 2)) (u : List α) :
    u ∈ (liftFin2toFin3 M).accepts ↔ u ∈ M.accepts := by
  change (liftFin2toFin3 M).evalFrom (Fin.castLE (by omega) M.start) u ∈
      (Fin.castLE (by omega) '' M.accept) ↔
    M.evalFrom M.start u ∈ M.accept
  rw [liftFin2toFin3_evalFrom, Set.mem_image]
  constructor
  · rintro ⟨q, hq, hEq⟩
    have hq' : q = M.evalFrom M.start u := Fin.ext (by simpa using congrArg Fin.val hEq)
    exact hq' ▸ hq
  · intro hq
    exact ⟨M.evalFrom M.start u, hq, rfl⟩

/-- **Exact `2 → 3` Reversal Theorem (`T₂^{op} ∈ HSP(T₃)`):**
For any alphabet `α` and any `w, x : List α`, if a `2`-state DFA separates `w.reverse`
and `x.reverse`, then some `3`-state DFA separates `w` and `x`. -/
theorem two_state_reversal_to_three_state {α : Type*} (w x : List α)
    (h : ∃ M : DFA α (Fin 2), w.reverse ∈ M.accepts ↔ x.reverse ∉ M.accepts) :
    ∃ D : DFA α (Fin 3), w ∈ D.accepts ↔ x ∉ D.accepts := by
  rcases h with ⟨M, hsep⟩
  have hne : M.eval w.reverse ≠ M.eval x.reverse := by
    intro heq
    have hw : w.reverse ∈ M.accepts ↔ M.eval w.reverse ∈ M.accept := Iff.rfl
    have hx : x.reverse ∈ M.accepts ↔ M.eval x.reverse ∈ M.accept := Iff.rfl
    simp [hw, hx, heq] at hsep
  obtain ⟨M', hM'0, hne'⟩ : ∃ M' : DFA α (Fin 2), M'.start = 0 ∧
      M'.evalFrom 0 w.reverse ≠ M'.evalFrom 0 x.reverse := by
    by_cases hs : M.start = 0
    · exact ⟨M, hs, by simpa [DFA.eval, hs] using hne⟩
    · have hs1 : M.start = 1 := by omega
      let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
      refine ⟨mapDFA e M, ?_, ?_⟩
      · change e M.start = 0
        rw [hs1]; rfl
      · have hstart : (mapDFA e M).start = e M.start := rfl
        have hw' := mapDFA_evalFrom e M M.start w.reverse
        have hx' := mapDFA_evalFrom e M M.start x.reverse
        have he1 : e M.start = 0 := by rw [hs1]; rfl
        rw [he1] at hw' hx'
        rw [hw', hx']
        exact e.injective.ne hne
  have hbit :
      (M'.evalFrom 0 w.reverse = 0) ↔ ¬ (M'.evalFrom 0 x.reverse = 0) := by
    generalize hr1 : M'.evalFrom 0 w.reverse = r1 at hne' ⊢
    generalize hr2 : M'.evalFrom 0 x.reverse = r2 at hne' ⊢
    fin_cases r1 <;> fin_cases r2 <;> simp_all
  rw [revD1_D2_determines_f0 M' w, revD1_D2_determines_f0 M' x] at hbit
  by_cases hd1 : ((revD1 M').eval w = 2) ↔ ¬ ((revD1 M').eval x = 2)
  · refine ⟨revD1 M', ?_⟩
    change (revD1 M').eval w ∈ ({2} : Set (Fin 3)) ↔ (revD1 M').eval x ∉ ({2} : Set (Fin 3))
    simpa only [Set.mem_singleton_iff] using hd1
  · have hd2 : ((revD2 M').eval w = 1) ↔ ¬ ((revD2 M').eval x = 1) := by
      cases hbw1 : decide ((revD1 M').eval w = 2) <;>
        cases hbx1 : decide ((revD1 M').eval x = 2) <;>
        cases hbw2 : decide ((revD2 M').eval w = 1) <;>
        cases hbx2 : decide ((revD2 M').eval x = 1) <;>
        simp_all
    refine ⟨liftFin2toFin3 (revD2 M'), ?_⟩
    rw [liftFin2toFin3_accepts, liftFin2toFin3_accepts]
    change (revD2 M').eval w ∈ ({1} : Set (Fin 2)) ↔ (revD2 M').eval x ∉ ({1} : Set (Fin 2))
    simpa only [Set.mem_singleton_iff] using hd2

end ReversalTwoToThree

/-! ## Section 3: Exact `L = 10` Subset-Construction Ceiling Witness -/

section WitnessL10

private def nfaL10 : NFA Bool (Fin 2) where
  start := {0}
  accept := {0}
  step q c :=
    match q, c with
    | 0, false => {1}
    | 0, true => {0}
    | 1, false => {0, 1}
    | 1, true => ∅

private def dfaRevL10 : DFA Bool (Fin 3) where
  start := 0
  step q c := if c then 0 else if q = 0 then 1 else 2
  accept := {1}

private def eval3 (a b c q : Fin 3) : Fin 3 :=
  if q = 0 then a else if q = 1 then b else c

private lemma fin3_iter_laws :
    ∀ a b c : Fin 3,
      (∀ q : Fin 3, (eval3 a b c)^[8] q = (eval3 a b c)^[2] q) ∧
      (∀ s : Fin 3, (eval3 a b c)^[7] s = (eval3 a b c)^[1] s ∨
        ∀ u : Fin 3, (eval3 a b c)^[2] u = (eval3 a b c)^[2] s) := by
  decide

private lemma fin3_fun_laws (f : Fin 3 → Fin 3) :
    (∀ q : Fin 3, f^[8] q = f^[2] q) ∧
    (∀ s : Fin 3, f^[7] s = f^[1] s ∨ ∀ u : Fin 3, f^[2] u = f^[2] s) := by
  have hf : f = eval3 (f 0) (f 1) (f 2) := by
    ext q
    fin_cases q <;> rfl
  rw [hf]
  exact fin3_iter_laws (f 0) (f 1) (f 2)

private lemma dfa_eval_w10 (M : DFA Bool (Fin 3)) :
    M.eval [false, true, false, false, false, false, false, false, false, false] =
      (fun q => M.step q false)^[8] (M.step ((fun q => M.step q false)^[1] M.start) true) := by
  rfl

private lemma dfa_eval_x10 (M : DFA Bool (Fin 3)) :
    M.eval [false, false, false, false, false, false, false, true, false, false] =
      (fun q => M.step q false)^[2] (M.step ((fun q => M.step q false)^[7] M.start) true) := by
  rfl

/-- **Exact `L = 10` Witness (`nsep ≤ 2`):**
`w = 010^8` and `x = 0^7 1 0^2` are separated by an explicit `2`-state NFA. -/
theorem l10_witness_nsep_le_two :
    ∃ N : NFA Bool (Fin 2),
      [false, true, false, false, false, false, false, false, false, false] ∈ N.accepts ↔
      [false, false, false, false, false, false, false, true, false, false] ∉ N.accepts := by
  refine ⟨nfaL10, ?_⟩
  have hstep_0_f : nfaL10.stepSet {0} false = {1} := by
    ext q; fin_cases q <;> simp [NFA.stepSet, nfaL10]
  have hstep_1_t : nfaL10.stepSet {1} true = ∅ := by
    ext q; fin_cases q <;> simp [NFA.stepSet, nfaL10]
  have hstep_1_f : nfaL10.stepSet {1} false = {0, 1} := by
    ext q; fin_cases q <;> simp [NFA.stepSet, nfaL10]
  have hstep_01_f : nfaL10.stepSet {0, 1} false = {0, 1} := by
    ext q; fin_cases q <;> simp [NFA.stepSet, nfaL10]
  have hstep_01_t : nfaL10.stepSet {0, 1} true = {0} := by
    ext q; fin_cases q <;> simp [NFA.stepSet, nfaL10]
  have hstep_emp : ∀ c, nfaL10.stepSet ∅ c = ∅ := by
    intro c; ext q; simp [NFA.stepSet]
  have hev_emp : ∀ u, nfaL10.evalFrom ∅ u = ∅ := by
    intro u
    induction u with
    | nil => rfl
    | cons c u ih => rw [NFA.evalFrom_cons, hstep_emp, ih]
  have hs0 : nfaL10.start = {0} := rfl
  have hw : nfaL10.evalFrom nfaL10.start [false, true, false, false, false, false, false, false, false, false] = ∅ := by
    rw [hs0, NFA.evalFrom_cons, hstep_0_f, NFA.evalFrom_cons, hstep_1_t, hev_emp]
  have hx : nfaL10.evalFrom nfaL10.start [false, false, false, false, false, false, false, true, false, false] = {0, 1} := by
    rw [hs0, NFA.evalFrom_cons, hstep_0_f, NFA.evalFrom_cons, hstep_1_f,
      NFA.evalFrom_cons, hstep_01_f, NFA.evalFrom_cons, hstep_01_f,
      NFA.evalFrom_cons, hstep_01_f, NFA.evalFrom_cons, hstep_01_f,
      NFA.evalFrom_cons, hstep_01_f, NFA.evalFrom_cons, hstep_01_t,
      NFA.evalFrom_cons, hstep_0_f, NFA.evalFrom_cons, hstep_1_f, NFA.evalFrom_nil]
  have hw_not : [false, true, false, false, false, false, false, false, false, false] ∉ nfaL10.accepts := by
    rw [NFA.mem_accepts]
    change ¬ ∃ s ∈ nfaL10.accept, s ∈ nfaL10.evalFrom nfaL10.start _
    rw [hw]
    simp
  have hx_mem : [false, false, false, false, false, false, false, true, false, false] ∈ nfaL10.accepts := by
    rw [NFA.mem_accepts]
    change ∃ s ∈ nfaL10.accept, s ∈ nfaL10.evalFrom nfaL10.start _
    rw [hx]
    exact ⟨0, by simp [nfaL10], by simp⟩
  simp [hw_not, hx_mem]

/-- **Exact `L = 10` Witness (`sep(w^R, x^R) ≤ 3`):**
The reversals of `010^8` and `0^7 1 0^2` are separated by a `3`-state DFA. -/
theorem l10_witness_rev_sep_le_three :
    ∃ D : DFA Bool (Fin 3),
      [false, true, false, false, false, false, false, false, false, false].reverse ∈ D.accepts ↔
      [false, false, false, false, false, false, false, true, false, false].reverse ∉ D.accepts := by
  refine ⟨dfaRevL10, ?_⟩
  have hw : dfaRevL10.eval [false, true, false, false, false, false, false, false, false, false].reverse = 1 := rfl
  have hx : dfaRevL10.eval [false, false, false, false, false, false, false, true, false, false].reverse = 2 := rfl
  change dfaRevL10.eval _ ∈ dfaRevL10.accept ↔ dfaRevL10.eval _ ∉ dfaRevL10.accept
  rw [hw, hx]
  simp [dfaRevL10]

/-- **Exact `L = 10` Witness (`sep ≥ 4`, hitting the `2^2` subset-construction ceiling):**
No `3`-state DFA can separate `010^8` and `0^7 1 0^2`. -/
theorem l10_witness_sep_ge_four :
    ∀ M : DFA Bool (Fin 3),
      [false, true, false, false, false, false, false, false, false, false] ∈ M.accepts ↔
      [false, false, false, false, false, false, false, true, false, false] ∈ M.accepts := by
  intro M
  have hlaws := fin3_fun_laws (fun q => M.step q false)
  have heval_eq :
      M.eval [false, true, false, false, false, false, false, false, false, false] =
      M.eval [false, false, false, false, false, false, false, true, false, false] := by
    rw [dfa_eval_w10, dfa_eval_x10]
    rw [hlaws.1]
    rcases hlaws.2 M.start with h7 | hconst
    · rw [h7]
    · simp_rw [hconst]
  change M.eval _ ∈ M.accept ↔ M.eval _ ∈ M.accept
  rw [heval_eq]

end WitnessL10

/-! ## Section 4: DESW (2011) Quadratic Gap and Unbounded `sep / nsep` Ratio -/

section DESWFamily

private lemma dfa_evalFrom_replicate {α Q : Type*} (M : DFA α Q) (c : α) :
    ∀ (n : ℕ) (q : Q), M.evalFrom q (List.replicate n c) = (fun r => M.step r c)^[n] q
  | 0, q => by simp [DFA.evalFrom]
  | n + 1, q => by
    rw [List.replicate_succ]
    change M.evalFrom (M.step q c) (List.replicate n c) = (fun r => M.step r c)^[n + 1] q
    rw [Function.iterate_succ_apply]
    exact dfa_evalFrom_replicate M c n (M.step q c)

private lemma fin_iter_cycle {d : ℕ} (f : Fin d → Fin d) (s : Fin d) :
    ∃ i j : ℕ, i < j ∧ j ≤ d ∧ f^[i] s = f^[j] s := by
  have hlt : Fintype.card (Fin d) < Fintype.card (Fin (d + 1)) := by simp
  obtain ⟨r1, r2, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun r : Fin (d + 1) => f^[r.1] s) hlt
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h12 | h21
  · exact ⟨r1.1, r2.1, h12, Nat.le_of_lt_succ r2.isLt, heq⟩
  · exact ⟨r2.1, r1.1, h21, Nat.le_of_lt_succ r1.isLt, heq.symm⟩

private lemma iter_add_period_mul {α : Type*} (f : α → α) (s : α) (i p : ℕ)
    (hp : f^[i] s = f^[i + p] s) :
    ∀ m : ℕ, f^[i + m * p] s = f^[i] s
  | 0 => by simp
  | m + 1 => by
    have h1 : i + (m + 1) * p = m * p + (i + p) := by ring
    have h2 : m * p + i = i + m * p := by ring
    rw [h1, Function.iterate_add_apply, ← hp, ← Function.iterate_add_apply, h2]
    exact iter_add_period_mul f s i p hp m

private lemma fin_iter_add_lcm {d t : ℕ} (hd : d ≤ t) (f : Fin d → Fin d) (s : Fin d)
    (L : ℕ) (hL : ∀ p ∈ Finset.Icc 1 t, p ∣ L) (n : ℕ) (hn : t - 1 ≤ n) :
    f^[n + L] s = f^[n] s := by
  obtain ⟨i, j, hij, hjd, heq⟩ := fin_iter_cycle f s
  let p := j - i
  have hp_pos : 1 ≤ p := by omega
  have hp_le : p ≤ t := by omega
  have hp_mem : p ∈ Finset.Icc 1 t := Finset.mem_Icc.mpr ⟨hp_pos, hp_le⟩
  obtain ⟨q, hq⟩ := hL p hp_mem
  have hjp : i + p = j := by omega
  have hp_eq : f^[i] s = f^[i + p] s := hjp ▸ heq
  have hi_le : i ≤ t - 1 := by omega
  have hi_n : i ≤ n := le_trans hi_le hn
  have hdecomp : n + L = (n - i) + (i + q * p) := by
    rw [hq, mul_comm p q]
    omega
  have hn_decomp : n = (n - i) + i := by omega
  rw [hdecomp, Function.iterate_add_apply, iter_add_period_mul f s i p hp_eq q,
    ← Function.iterate_add_apply, ← hn_decomp]

private lemma dfa_desw_indistinguishable (k d : ℕ) (hk : 3 ≤ k) (hd : d ≤ k * (k - 1))
    (M : DFA Bool (Fin d)) :
    let t := k * (k - 1)
    let L := Finset.lcm (Finset.Icc 1 t) id
    M.eval (List.replicate (t - 1 + L) false ++ List.replicate (t - 1) true) =
      M.eval (List.replicate (t - 1) false ++ List.replicate (t - 1 + L) true) := by
  intro t L
  have hk1 : 2 ≤ k - 1 := by omega
  have ht_pos : 1 ≤ t := by
    change 1 ≤ k * (k - 1)
    nlinarith
  have hL : ∀ p ∈ Finset.Icc 1 t, p ∣ L := fun p hp => Finset.dvd_lcm hp
  have hfalse :
      M.evalFrom M.start (List.replicate (t - 1 + L) false) =
        M.evalFrom M.start (List.replicate (t - 1) false) := by
    rw [dfa_evalFrom_replicate, dfa_evalFrom_replicate]
    exact fin_iter_add_lcm hd (fun r => M.step r false) M.start L hL (t - 1) le_rfl
  rw [DFA.eval, dfa_evalFrom_append, dfa_evalFrom_append, hfalse]
  set q := M.evalFrom M.start (List.replicate (t - 1) false)
  rw [dfa_evalFrom_replicate, dfa_evalFrom_replicate]
  exact (fin_iter_add_lcm hd (fun r => M.step r true) q L hL (t - 1) le_rfl).symm

private def frobNFA (k : ℕ) (hk : 1 ≤ k) : NFA Bool (Fin (2 * k + 1)) where
  start := {⟨0, by omega⟩, ⟨k, by omega⟩}
  accept := {⟨k, by omega⟩}
  step s c :=
    if c then
      if s.1 = k then {⟨k, by omega⟩} else ∅
    else
      if h : s.1 < k then
        if s.1 + 1 = k then {⟨0, by omega⟩, ⟨k, by omega⟩}
        else {⟨s.1 + 1, by omega⟩}
      else
        {⟨k + (s.1 - k + 1) % (k + 1), by
          have := Nat.mod_lt (s.1 - k + 1) (by omega : 0 < k + 1)
          omega⟩}

private lemma replicate_succ_eq {α : Type*} (n : ℕ) (a : α) :
    List.replicate (n + 1) a = List.replicate n a ++ [a] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, ih, ← List.cons_append, ← List.replicate_succ, ih]

private lemma frobNFA_evalFrom_append {k : ℕ} {hk : 1 ≤ k} (S : Set (Fin (2 * k + 1)))
    (u v : List Bool) :
    (frobNFA k hk).evalFrom S (u ++ v) = (frobNFA k hk).evalFrom ((frobNFA k hk).evalFrom S u) v := by
  induction u generalizing S with
  | nil => simp [NFA.evalFrom]
  | cons a u ih =>
    simp only [List.cons_append, NFA.evalFrom_cons]
    exact ih _

private lemma frobNFA_forward (k : ℕ) (hk : 1 ≤ k) :
    ∀ (n : ℕ) (s : Fin (2 * k + 1)),
      s ∈ (frobNFA k hk).evalFrom (frobNFA k hk).start (List.replicate n false) →
      (s.1 < k → s.1 = n % k) ∧
      (k ≤ s.1 → ∃ a b : ℕ, a * k + b = n ∧ s.1 - k = b % (k + 1))
  | 0, s, hs => by
    simp only [List.replicate_zero, NFA.evalFrom_nil, frobNFA, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · constructor
      · intro _; simp
      · intro h; simp at h; omega
    · constructor
      · intro h; simp at h
      · intro _; exact ⟨0, 0, by simp, by simp⟩
  | n + 1, s', hs' => by
    rw [replicate_succ_eq, frobNFA_evalFrom_append, NFA.evalFrom_cons, NFA.evalFrom_nil,
      NFA.mem_stepSet] at hs'
    rcases hs' with ⟨s, hs, hs_step⟩
    have ih := frobNFA_forward k hk n s hs
    by_cases hsk : s.1 < k
    · have hsn : s.1 = n % k := ih.1 hsk
      have hstep : s' ∈ (frobNFA k hk).step s false := hs_step
      simp only [frobNFA, Bool.false_eq_true, ↓reduceIte, hsk, ↓reduceDIte] at hstep
      by_cases hs1 : s.1 + 1 = k
      · simp only [hs1, ↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff] at hstep
        have hdvd : k ∣ n + 1 := by
          refine ⟨n / k + 1, ?_⟩
          have hmod := Nat.div_add_mod n k
          rw [Nat.mul_add_one]
          omega
        rcases hstep with rfl | rfl
        · constructor
          · intro _; exact (Nat.mod_eq_zero_of_dvd hdvd).symm
          · intro h; simp at h; omega
        · constructor
          · intro h; simp at h
          · intro _
            rcases hdvd with ⟨a, ha⟩
            exact ⟨a, 0, by rw [ha, mul_comm]; simp, by simp⟩
      · simp only [hs1, ↓reduceIte, Set.mem_singleton_iff] at hstep
        subst hstep
        constructor
        · intro _
          have hlt : s.1 + 1 < k := by omega
          calc s.1 + 1 = n % k + 1 := by rw [hsn]
            _ = (n + 1) % k := by
              rw [Nat.add_mod]
              have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
              rw [h1]
              exact (Nat.mod_eq_of_lt (by omega)).symm
        · intro h; simp at h; omega
    · obtain ⟨a, b, hab, hsb⟩ := ih.2 (by omega)
      have hstep : s' ∈ (frobNFA k hk).step s false := hs_step
      simp only [frobNFA, Bool.false_eq_true, ↓reduceIte, hsk, ↓reduceDIte,
        Set.mem_singleton_iff] at hstep
      subst hstep
      constructor
      · intro h; simp at h
      · intro _
        refine ⟨a, b + 1, by omega, ?_⟩
        simp only [Nat.add_sub_cancel_left]
        rw [hsb, Nat.add_mod (b % (k + 1)) 1 (k + 1), Nat.mod_mod, ← Nat.add_mod]

private lemma frobNFA_R0_not_in_x (k : ℕ) (hk : 3 ≤ k) :
    let t := k * (k - 1)
    ⟨k, by omega⟩ ∉ (frobNFA k (by omega)).evalFrom (frobNFA k (by omega)).start
      (List.replicate (t - 1) false) := by
  intro t hmem
  have hk1 : 2 ≤ k - 1 := by omega
  have ht_pos : 1 ≤ k * (k - 1) := by nlinarith
  have h := (frobNFA_forward k (by omega) (t - 1) ⟨k, by omega⟩ hmem).2 (le_refl k)
  rcases h with ⟨a, b, hab, hbmod⟩
  simp only [Nat.sub_self] at hbmod
  have hdvd : k + 1 ∣ b := Nat.dvd_of_mod_eq_zero hbmod.symm
  rcases hdvd with ⟨c, rfl⟩
  have ht_eq : k * (k - 1) - 1 + k + (k + 1) = k * (k + 1) := by
    zify [show 1 ≤ k by omega, ht_pos]
    ring
  have hsum : (a + 1) * k + (c + 1) * (k + 1) = k * (k + 1) := by
    calc (a + 1) * k + (c + 1) * (k + 1)
        = (a * k + (k + 1) * c) + k + (k + 1) := by ring
      _ = (k * (k - 1) - 1) + k + (k + 1) := by rw [hab]
      _ = k * (k + 1) := ht_eq
  have hpk : k ∣ (c + 1) * (k + 1) := ⟨k + 1 - (a + 1), by
    have hle : a + 1 ≤ k + 1 := by nlinarith
    zify [hle]; linarith⟩
  have hcop : Nat.Coprime k (k + 1) := by
    rw [add_comm, Nat.coprime_add_self_right]
    simp
  have hk_dvd_c1 : k ∣ c + 1 := hcop.dvd_of_dvd_mul_right hpk
  rcases hk_dvd_c1 with ⟨m, hm⟩
  have hm_pos : 1 ≤ m := by
    rcases m with _ | m
    · simp at hm
    · omega
  have hbig : k * (k + 1) < (a + 1) * k + (c + 1) * (k + 1) := by
    rw [hm]
    nlinarith
  omega

private lemma frobNFA_walk_k_step (k : ℕ) (hk : 1 ≤ k) (S : Set (Fin (2 * k + 1)))
    (hL0 : ⟨0, by omega⟩ ∈ S) :
    ∀ (r : ℕ) (hr : r < k),
      ⟨r, by omega⟩ ∈ (frobNFA k hk).evalFrom S (List.replicate r false)
  | 0, _ => by simpa [NFA.evalFrom] using hL0
  | r + 1, hr => by
    rw [replicate_succ_eq, frobNFA_evalFrom_append, NFA.evalFrom_cons, NFA.evalFrom_nil,
      NFA.mem_stepSet]
    refine ⟨⟨r, by omega⟩, frobNFA_walk_k_step k hk S hL0 r (by omega), ?_⟩
    simp [frobNFA, show r < k by omega, show r + 1 ≠ k by omega]

private lemma frobNFA_reach_mul_k (k : ℕ) (hk : 1 ≤ k) :
    ∀ a : ℕ,
      ⟨0, by omega⟩ ∈ (frobNFA k hk).evalFrom (frobNFA k hk).start (List.replicate (a * k) false) ∧
      ⟨k, by omega⟩ ∈ (frobNFA k hk).evalFrom (frobNFA k hk).start (List.replicate (a * k) false)
  | 0 => by simp [NFA.evalFrom, frobNFA]
  | a + 1 => by
    have ih := frobNFA_reach_mul_k k hk a
    have hmul : (a + 1) * k = a * k + (k - 1 + 1) := by
      rw [Nat.succ_mul]
      omega
    rw [hmul, List.replicate_add, frobNFA_evalFrom_append,
      replicate_succ_eq, frobNFA_evalFrom_append, NFA.evalFrom_cons, NFA.evalFrom_nil]
    have hk1 := frobNFA_walk_k_step k hk _ ih.1 (k - 1) (by omega)
    constructor
    · rw [NFA.mem_stepSet]
      refine ⟨⟨k - 1, by omega⟩, hk1, ?_⟩
      simp [frobNFA, show k - 1 < k by omega, show k - 1 + 1 = k by omega]
    · rw [NFA.mem_stepSet]
      refine ⟨⟨k - 1, by omega⟩, hk1, ?_⟩
      simp [frobNFA, show k - 1 < k by omega, show k - 1 + 1 = k by omega]

private lemma frobNFA_walk_R_step (k : ℕ) (hk : 1 ≤ k) (S : Set (Fin (2 * k + 1)))
    (hR0 : ⟨k, by omega⟩ ∈ S) :
    ∀ r : ℕ,
      ⟨k + r % (k + 1), by have := Nat.mod_lt r (by omega : 0 < k + 1); omega⟩ ∈
        (frobNFA k hk).evalFrom S (List.replicate r false)
  | 0 => by simpa [NFA.evalFrom] using hR0
  | r + 1 => by
    rw [replicate_succ_eq, frobNFA_evalFrom_append, NFA.evalFrom_cons, NFA.evalFrom_nil,
      NFA.mem_stepSet]
    refine ⟨⟨k + r % (k + 1), by have := Nat.mod_lt r (by omega : 0 < k + 1); omega⟩,
      frobNFA_walk_R_step k hk S hR0 r, ?_⟩
    simp only [frobNFA, Bool.false_eq_true, ↓reduceIte, not_lt_of_ge (Nat.le_add_right k _),
      ↓reduceDIte, Set.mem_singleton_iff]
    ext
    simp only [Nat.add_sub_cancel_left]
    rw [Nat.add_mod r 1 (k + 1), Nat.add_mod (r % (k + 1)) 1 (k + 1), Nat.mod_mod]

private lemma chicken_mcnugget_succ (k n : ℕ) (hk : 1 ≤ k) (hn : k * (k - 1) ≤ n) :
    ∃ a b : ℕ, a * k + b * (k + 1) = n := by
  let q := n / k
  let b := n % k
  have hnb : k * q + b = n := Nat.div_add_mod n k
  have hb_lt : b < k := Nat.mod_lt n (by omega)
  have hbq : b ≤ q := by
    by_contra hlt
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · omega
      · have : b = 0 := by omega
        omega
      · omega
    have hb_le : b ≤ k - 1 := by omega
    have hq_le : q ≤ k - 2 := by omega
    have h1 : k * q + b ≤ k * (k - 2) + (k - 1) :=
      Nat.add_le_add (Nat.mul_le_mul_left k hq_le) hb_le
    have h2 : k * (k - 2) + (k - 1) < k * (k - 1) := by
      zify [hk, hk2]; linarith
    omega
  refine ⟨q - b, b, ?_⟩
  zify [hbq]
  nlinarith

private lemma frobNFA_true_keep {k : ℕ} {hk : 1 ≤ k} (S : Set (Fin (2 * k + 1)))
    (hR0 : ⟨k, by omega⟩ ∈ S) :
    ∀ m : ℕ, ⟨k, by omega⟩ ∈ (frobNFA k hk).evalFrom S (List.replicate m true)
  | 0 => by simpa [NFA.evalFrom] using hR0
  | m + 1 => by
    rw [List.replicate_succ, NFA.evalFrom_cons]
    refine frobNFA_true_keep _ ?_ m
    rw [NFA.mem_stepSet]
    exact ⟨⟨k, by omega⟩, hR0, by simp [frobNFA]⟩

private lemma frobNFA_true_kill {k : ℕ} {hk : 1 ≤ k} (S : Set (Fin (2 * k + 1)))
    (hno : ⟨k, by omega⟩ ∉ S) (m : ℕ) (hm : 1 ≤ m) :
    (frobNFA k hk).evalFrom S (List.replicate m true) = ∅ := by
  cases m with
  | zero => omega
  | succ m =>
    rw [List.replicate_succ, NFA.evalFrom_cons]
    have hstep : (frobNFA k hk).stepSet S true = ∅ := by
      ext s
      simp only [NFA.mem_stepSet, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro q hq hstep_q
      simp only [frobNFA, ↓reduceIte] at hstep_q
      split_ifs at hstep_q with hqk
      · have hq_eq : q = ⟨k, by omega⟩ := Fin.ext hqk
        exact hno (hq_eq ▸ hq)
      · exact hstep_q
    rw [hstep]
    clear hstep hno hm
    induction m with
    | zero => simp [NFA.evalFrom]
    | succ m ih =>
      rw [List.replicate_succ, NFA.evalFrom_cons]
      have hemp : (frobNFA k hk).stepSet ∅ true = ∅ := by
        ext s; simp [NFA.stepSet]
      rw [hemp]
      exact ih

/-- **DESW (2011) Quadratic Separation-Ratio Family:**
For every `k ≥ 3`, there exist equal-length binary words `w, x : List Bool` separated by a
`(2k + 1)`-state NFA (`nsep ≤ 2k + 1`), yet indistinguishable by every `d`-state DFA for
every `d ≤ k * (k - 1)` (`sep > k * (k - 1)`), with length bounded by
`2 * (k * (k - 1)) + Nat.factorial (k * (k - 1))`. -/
theorem desw_quadratic_gap (k : ℕ) (hk : 3 ≤ k) :
    ∃ w x : List Bool, w.length = x.length ∧
      w.length ≤ 2 * (k * (k - 1)) + Nat.factorial (k * (k - 1)) ∧
      (∃ N : NFA Bool (Fin (2 * k + 1)), w ∈ N.accepts ↔ x ∉ N.accepts) ∧
      (∀ d : ℕ, d ≤ k * (k - 1) → ∀ M : DFA Bool (Fin d),
        w ∈ M.accepts ↔ x ∈ M.accepts) := by
  let t := k * (k - 1)
  let L := Finset.lcm (Finset.Icc 1 t) id
  let w := List.replicate (t - 1 + L) false ++ List.replicate (t - 1) true
  let x := List.replicate (t - 1) false ++ List.replicate (t - 1 + L) true
  have hk1 : 2 ≤ k - 1 := by omega
  have ht_pos : 1 ≤ t := by
    change 1 ≤ k * (k - 1)
    nlinarith
  have ht_mem : t ∈ Finset.Icc 1 t := Finset.mem_Icc.mpr ⟨ht_pos, le_rfl⟩
  have hL_pos : 1 ≤ L := by
    by_contra h0
    have hL0 : L = 0 := by omega
    have hprod_ne : ∏ i ∈ Finset.Icc 1 t, i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i hi => by
        have := (Finset.mem_Icc.mp hi).1; omega)
    have hdvd_prod : L ∣ ∏ i ∈ Finset.Icc 1 t, i :=
      Finset.lcm_dvd (fun i hi => Finset.dvd_prod_of_mem id hi)
    rw [hL0, zero_dvd_iff] at hdvd_prod
    exact hprod_ne hdvd_prod
  have ht_le_L : t ≤ L := Nat.le_of_dvd hL_pos (Finset.dvd_lcm ht_mem)
  have hL_le_fac : L ≤ Nat.factorial t := by
    have hfac_pos : 0 < Nat.factorial t := Nat.factorial_pos t
    have hprod_eq : ∀ n : ℕ, ∏ i ∈ Finset.Icc 1 n, i = Nat.factorial n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hset : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
          ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hset, Finset.prod_insert (by simp), ih, Nat.factorial_succ]
    have hdvd_fac : L ∣ Nat.factorial t := by
      rw [← hprod_eq t]
      exact Finset.lcm_dvd (fun i hi => Finset.dvd_prod_of_mem id hi)
    exact Nat.le_of_dvd hfac_pos hdvd_fac
  have hlen : w.length = x.length := by
    simp [w, x]; omega
  refine ⟨w, x, hlen, ?_, ?_, ?_⟩
  · dsimp only [w, t]
    simp only [List.length_append, List.length_replicate]
    change L ≤ Nat.factorial (k * (k - 1)) at hL_le_fac
    omega
  · refine ⟨frobNFA k (by omega), ?_⟩
    have hn_ge : k * (k - 1) ≤ t - 1 + L := by
      change k * (k - 1) ≤ k * (k - 1) - 1 + L
      change k * (k - 1) ≤ L at ht_le_L
      omega
    obtain ⟨a, b, hab⟩ := chicken_mcnugget_succ k (t - 1 + L) (by omega) hn_ge
    have hw_reach_false : ⟨k, by omega⟩ ∈ (frobNFA k (by omega)).evalFrom
        (frobNFA k (by omega)).start (List.replicate (t - 1 + L) false) := by
      rw [← hab, List.replicate_add, frobNFA_evalFrom_append]
      have h1 := (frobNFA_reach_mul_k k (by omega) a).2
      have h2 := frobNFA_walk_R_step k (by omega) _ h1 (b * (k + 1))
      simpa [Nat.mul_mod_left] using h2
    have hw_acc : w ∈ (frobNFA k (by omega)).accepts := by
      rw [NFA.mem_accepts]
      refine ⟨⟨k, by omega⟩, by simp [frobNFA], ?_⟩
      change ⟨k, by omega⟩ ∈ (frobNFA k (by omega)).evalFrom (frobNFA k (by omega)).start w
      dsimp only [w]
      rw [frobNFA_evalFrom_append]
      exact frobNFA_true_keep _ hw_reach_false (t - 1)
    have hx_not_reach : ⟨k, by omega⟩ ∉ (frobNFA k (by omega)).evalFrom
        (frobNFA k (by omega)).start (List.replicate (t - 1) false) :=
      frobNFA_R0_not_in_x k hk
    have hx_not_acc : x ∉ (frobNFA k (by omega)).accepts := by
      rw [NFA.mem_accepts]
      change ¬ ∃ s ∈ (frobNFA k (by omega)).accept,
        s ∈ (frobNFA k (by omega)).evalFrom (frobNFA k (by omega)).start x
      dsimp only [x]
      rw [frobNFA_evalFrom_append, frobNFA_true_kill _ hx_not_reach (t - 1 + L) (by omega)]
      simp
    simp [hw_acc, hx_not_acc]
  · intro d hd M
    have heq := dfa_desw_indistinguishable k d hk hd M
    change M.eval w ∈ M.accept ↔ M.eval x ∈ M.accept
    rw [heq]

/-- **Unbounded `sep / nsep` Ratio:**
For every `C : ℕ`, there exist equal-length binary words `w, x : List Bool` and `m ≥ 1`
such that some `m`-state NFA separates `w` and `x`, yet NO `(C * m)`-state DFA can separate them. -/
theorem unbounded_sep_nsep_ratio (C : ℕ) :
    ∃ w x : List Bool, w.length = x.length ∧
      ∃ m : ℕ, 1 ≤ m ∧
        (∃ N : NFA Bool (Fin m), w ∈ N.accepts ↔ x ∉ N.accepts) ∧
        (∀ M : DFA Bool (Fin (C * m)), w ∈ M.accepts ↔ x ∈ M.accepts) := by
  let k := 2 * C + 3
  have hk : 3 ≤ k := by omega
  obtain ⟨w, x, hlen, _, hNFA, hDFA⟩ := desw_quadratic_gap k hk
  refine ⟨w, x, hlen, 2 * k + 1, by omega, hNFA, ?_⟩
  have hle : C * (2 * k + 1) ≤ k * (k - 1) := by
    dsimp [k]
    nlinarith
  exact hDFA (C * (2 * k + 1)) hle

end DESWFamily

end PPL121Ratio
