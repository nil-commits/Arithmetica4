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
# Arithmetica4 Extension: Combinatorics on Words & Finite Automata Engine (`Arith4Ext.AutomataCombinatorics`)

Clean, general, non-vacuous Tier A reusable library built 100% from scratch on targeted
Mathlib imports (`0` monolithic `import Mathlib`, `0` Tier C imports, `0` custom axioms).

## Exported API Summary (`namespace Arith4Ext.AutomataCombinatorics`)
1. **Fine–Wilf Periodicity Engine:**
   - `HasPeriod w p` (`hasPeriod_iff_getElem`, `hasPeriod_mul`, `hasPeriod_drop`)
   - `fine_wilf`: `HasPeriod w p → HasPeriod w q → p + q - Nat.gcd p q ≤ w.length → HasPeriod w (Nat.gcd p q)`
   - `fine_wilf_tight`: infinite witness family `p = n, q = n + 1` of length `p + q - 2` failing period `1`.
2. **Lyndon–Schützenberger Word Commutation & Primitive Roots:**
   - `lyndon_schutzenberger_comm`: `u ++ v = v ++ u ↔ ∃ r a b, u = (replicate a r).flatten ∧ v = (replicate b r).flatten`
   - `lyndon_schutzenberger_power_comm`: `m ≥ 1 → n ≥ 1 → u^m = v^n → u ++ v = v ++ u`
   - `IsPrimitive r`, `primitive_root_exists`, `primitive_root_unique`
3. **Myhill–Nerode Fooling-Set Lower Bounds & Determinization Ceiling:**
   - `myhill_nerode_fooling_set`: `m` pairwise `L`-distinguishable words force `m ≤ k` for any `DFA α (Fin k)` accepting `L`
   - `no_small_dfa_of_fooling_set`: `k < m` impossibility corollary
   - `nfa_determinization_dfa` (`Fin m` NFA → `Fin (2 ^ m)` DFA with identical `accepts`), `sep_le_two_pow_nsep`
4. **Explicit Closure & Product Automata:**
   - `prodDFA`, `dfa_inter_closure`, `dfa_union_closure`, `dfa_symmDiff_closure` (`Fin (m₁ * m₂)`)
   - `complDFA`, `dfa_compl_closure` (`Fin m`)
   - `revNFA`, `nfa_reversal_closure` (`Fin m`), `dfa_reversal_closure` (`Fin (2 ^ m)`)
5. **Regular & Unary-Cycle Pumping Lemmas:**
   - `dfa_pumping_lemma`: standard `Fin m` DFA pumping lemma with `x.length + y.length ≤ m`, `1 ≤ y.length`
   - `dfa_unary_lcm_pump`, `dfa_unary_block_lcm_eq`: exact `lcm(1..t)` unary-block pumping invariance
-/

namespace Arith4Ext.AutomataCombinatorics

/-! ## Section 1: Fine–Wilf Periodicity Lemma & Tightness -/

section FineWilf

/-- `w` has period `p` if every index `i` with `i + p < w.length` satisfies `w[i]? = w[i + p]?`. -/
def HasPeriod {α : Type*} (w : List α) (p : ℕ) : Prop :=
  ∀ i : ℕ, i + p < w.length → w[i]? = w[i + p]?

theorem hasPeriod_iff_getElem {α : Type*} (w : List α) (p : ℕ) :
    HasPeriod w p ↔
      ∀ (i : ℕ) (hi1 : i < w.length) (hi2 : i + p < w.length), w[i] = w[i + p] := by
  constructor
  · intro h i hi1 hi2
    have hq := h i hi2
    rw [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] at hq
    exact Option.some.inj hq
  · intro h i hi2
    have hi1 : i < w.length := by omega
    rw [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2]
    exact congrArg some (h i hi1 hi2)

theorem hasPeriod_mul {α : Type*} {w : List α} {p : ℕ} (hp : HasPeriod w p) :
    ∀ (k i : ℕ), i + k * p < w.length → w[i]? = w[i + k * p]?
  | 0, i, _ => by simp
  | k + 1, i, hi => by
    have h1 : i + (k + 1) * p = (i + k * p) + p := by ring
    rw [h1] at hi ⊢
    have hlo : i + k * p < w.length := by omega
    rw [hasPeriod_mul hp k i hlo, hp (i + k * p) hi]

theorem hasPeriod_drop {α : Type*} {w : List α} {p k : ℕ} (hp : HasPeriod w p) :
    HasPeriod (w.drop k) p := by
  intro i hi
  rw [List.length_drop] at hi
  rw [List.getElem?_drop, List.getElem?_drop]
  have h1 : k + (i + p) = (k + i) + p := by ring
  rw [h1]
  exact hp (k + i) (by omega)

theorem hasPeriod_take {α : Type*} {w : List α} {p k : ℕ} (hp : HasPeriod w p) :
    HasPeriod (w.take k) p := by
  intro i hi
  rw [List.length_take] at hi
  have hi1 : i < k := by omega
  have hi2 : i + p < k := by omega
  rw [List.getElem?_take_of_lt hi1, List.getElem?_take_of_lt hi2]
  exact hp i (by omega)

private lemma fine_wilf_aux {α : Type*} (w : List α) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q)
    (hper_p : HasPeriod w p) (hper_q : HasPeriod w q)
    (hlen : p + q - Nat.gcd p q ≤ w.length) :
    HasPeriod w (Nat.gcd p q) := by
  rcases lt_trichotomy p q with hpq | rfl | hqp
  · let q' := q - p
    have hq'_pos : 0 < q' := by omega
    have hgcd : Nat.gcd p q' = Nat.gcd p q := by
      have hq_eq : q = q' + p := by omega
      rw [hq_eq, Nat.gcd_add_self_right]
    have hper_drop_p : HasPeriod (w.drop p) p := hasPeriod_drop hper_p
    have hper_drop_q' : HasPeriod (w.drop p) q' := by
      intro j hj
      rw [List.length_drop] at hj
      rw [List.getElem?_drop, List.getElem?_drop]
      have hjq : j + q < w.length := by omega
      have hjp : p + j = j + p := by ring
      have hjqp : p + (j + q') = j + q := by omega
      rw [hjp, hjqp, ← hper_p j (by omega), hper_q j hjq]
    have hlen_drop : p + q' - Nat.gcd p q' ≤ (w.drop p).length := by
      rw [List.length_drop, hgcd]
      omega
    have hdrop_gcd : HasPeriod (w.drop p) (Nat.gcd p q) := by
      rw [← hgcd]
      exact fine_wilf_aux (w.drop p) p q' hp hq'_pos
        hper_drop_p hper_drop_q' hlen_drop
    have hd_pos : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left q hp
    have hd_dvd_p : Nat.gcd p q ∣ p := Nat.gcd_dvd_left p q
    have hd_dvd_q' : Nat.gcd p q ∣ q' := by rw [← hgcd]; exact Nat.gcd_dvd_right p q'
    have hd_le_q' : Nat.gcd p q ≤ q' := Nat.le_of_dvd hq'_pos hd_dvd_q'
    have h2p_le : 2 * p ≤ w.length := by omega
    rcases hd_dvd_p with ⟨m, hm⟩
    have hm_pos : 1 ≤ m := by
      rcases m with _ | m
      · simp at hm; omega
      · omega
    have hmul_p : Nat.gcd p q + (m - 1) * Nat.gcd p q = p := by
      calc Nat.gcd p q + (m - 1) * Nat.gcd p q
          = (1 + (m - 1)) * Nat.gcd p q := by ring
        _ = m * Nat.gcd p q := by rw [show 1 + (m - 1) = m by omega]
        _ = Nat.gcd p q * m := mul_comm _ _
        _ = p := hm.symm
    intro i hi
    by_cases hip : p ≤ i
    · have hi' : (i - p) + Nat.gcd p q < (w.drop p).length := by
        rw [List.length_drop]; omega
      have hres := hdrop_gcd (i - p) hi'
      rw [List.getElem?_drop, List.getElem?_drop] at hres
      have ha : p + (i - p) = i := by omega
      have hb : p + (i - p + Nat.gcd p q) = i + Nat.gcd p q := by omega
      rw [ha, hb] at hres
      exact hres
    · by_cases hidp : i + Nat.gcd p q < p
      · have hi1 : i + p < w.length := by omega
        have hi2 : (i + Nat.gcd p q) + p < w.length := by omega
        have hdrop_res := hdrop_gcd i (by rw [List.length_drop]; omega)
        rw [List.getElem?_drop, List.getElem?_drop] at hdrop_res
        have ha : p + i = i + p := by ring
        have hb : p + (i + Nat.gcd p q) = (i + Nat.gcd p q) + p := by ring
        rw [ha, hb] at hdrop_res
        rw [hper_p i hi1, hper_p (i + Nat.gcd p q) hi2, hdrop_res]
      · have h1 : p ≤ i + Nat.gcd p q := by omega
        have h2 : i + p < w.length := by omega
        have h3 : (i + Nat.gcd p q - p) + (m - 1) * Nat.gcd p q < (w.drop p).length := by
          rw [List.length_drop]
          omega
        have hdrop_mul := hasPeriod_mul hdrop_gcd (m - 1) (i + Nat.gcd p q - p) h3
        rw [List.getElem?_drop, List.getElem?_drop] at hdrop_mul
        have ha : p + (i + Nat.gcd p q - p) = i + Nat.gcd p q := by omega
        have hb : p + (i + Nat.gcd p q - p + (m - 1) * Nat.gcd p q) = i + p := by omega
        rw [ha, hb] at hdrop_mul
        rw [hper_p i h2, hdrop_mul]
  · simp [Nat.gcd_self, hper_p]
  · rw [Nat.gcd_comm]
    have hlen' : q + p - Nat.gcd q p ≤ w.length := by
      rw [Nat.gcd_comm]; omega
    exact fine_wilf_aux w q p hq hp hper_q hper_p hlen'
termination_by 2 * (p + q) + (if p ≤ q then 0 else 1)
decreasing_by all_goals (try split_ifs) <;> omega

/-- **Fine–Wilf Periodicity Theorem:**
If `w` has positive periods `p` and `q` and `p + q - Nat.gcd p q ≤ w.length`,
then `w` has period `Nat.gcd p q`. -/
theorem fine_wilf {α : Type*} (w : List α) {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (hper_p : HasPeriod w p) (hper_q : HasPeriod w q)
    (hlen : p + q - Nat.gcd p q ≤ w.length) :
    HasPeriod w (Nat.gcd p q) :=
  fine_wilf_aux w p q hp hq hper_p hper_q hlen

/-- **Tightness of Fine–Wilf:**
For every `n ≥ 2`, there exists a Boolean word of length `2 * n - 1 = n + (n + 1) - 2`
having periods `n` and `n + 1` (`gcd = 1`), yet NOT period `1`. -/
theorem fine_wilf_tight (n : ℕ) (hn : 2 ≤ n) :
    ∃ w : List Bool, w.length = n + (n + 1) - 2 ∧
      HasPeriod w n ∧ HasPeriod w (n + 1) ∧ ¬ HasPeriod w 1 := by
  let w : List Bool := List.ofFn (fun i : Fin (2 * n - 1) => decide (i.1 ≠ n - 1))
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · simp [w]; omega
  · intro i hi
    rw [List.length_ofFn] at hi
    have hi1 : i < 2 * n - 1 := by omega
    rw [List.getElem?_eq_getElem (by simpa [w] using hi1),
        List.getElem?_eq_getElem (by simpa [w] using hi)]
    simp only [w, List.getElem_ofFn, Option.some.injEq, decide_eq_decide]
    constructor <;> intro h <;> omega
  · intro i hi
    rw [List.length_ofFn] at hi
    have hi1 : i < 2 * n - 1 := by omega
    rw [List.getElem?_eq_getElem (by simpa [w] using hi1),
        List.getElem?_eq_getElem (by simpa [w] using hi)]
    simp only [w, List.getElem_ofFn, Option.some.injEq, decide_eq_decide]
    constructor <;> intro h <;> omega
  · intro hper
    have hi : (n - 1) + 1 < w.length := by simp [w]; omega
    have hq := hper (n - 1) hi
    have hlt1 : n - 1 < w.length := by simp [w]; omega
    rw [List.getElem?_eq_getElem hlt1, List.getElem?_eq_getElem hi] at hq
    simp [w] at hq

end FineWilf

/-! ## Section 2: Lyndon–Schützenberger Word Commutation & Primitive Roots -/

section WordCommutation

private lemma list_eq_replicate_flatten_of_period {α : Type*} :
    ∀ (k : ℕ) (w : List α) (d : ℕ),
      0 < d → HasPeriod w d → w.length = k * d →
      w = (List.replicate k (w.take d)).flatten
  | 0, w, d, _, _, hlen => by
    simp at hlen
    subst hlen
    rfl
  | k + 1, w, d, hd, hper, hlen => by
    have hlen_ge : d ≤ w.length := by rw [hlen, Nat.succ_mul]; omega
    have htake : (w.take d).length = d := List.length_take_of_le hlen_ge
    have hdrop_len : (w.drop d).length = k * d := by
      rw [List.length_drop, hlen, Nat.succ_mul]; omega
    have hdrop_per : HasPeriod (w.drop d) d := hasPeriod_drop hper
    have hdrop_eq := list_eq_replicate_flatten_of_period k (w.drop d) d hd hdrop_per hdrop_len
    have htake_drop : (w.drop d).take d = w.take d ∨ k = 0 := by
      rcases k with _ | k
      · right; rfl
      · left
        apply List.ext_getElem?
        intro i
        by_cases hid : i < d
        · rw [List.getElem?_take_of_lt hid, List.getElem?_take_of_lt hid, List.getElem?_drop]
          have hsum : d + i = i + d := by ring
          have h2d : 2 * d ≤ w.length := by rw [hlen]; nlinarith
          rw [hsum]
          exact (hper i (by omega)).symm
        · have h1 : ((w.drop d).take d).length ≤ i := by
            rw [List.length_take]; omega
          have h2 : (w.take d).length ≤ i := by
            rw [htake]; omega
          rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]
    rw [List.replicate_succ, List.flatten_cons]
    rcases htake_drop with htd | rfl
    · rw [htd] at hdrop_eq
      rw [← hdrop_eq, List.take_append_drop]
    · have hdrop0 : w.drop d = [] := List.length_eq_zero_iff.mp (by simpa using hdrop_len)
      have hfull : w.take d = w := List.take_of_length_le (by rw [hlen]; omega)
      rw [hdrop0] at hdrop_eq
      simp [hfull]

private lemma comm_hasPeriod_left {α : Type*} {u v : List α} (h : u ++ v = v ++ u) :
    HasPeriod (u ++ v) u.length := by
  intro i hi
  rw [List.length_append] at hi
  have hiv : i < v.length := by omega
  have h1 : (u ++ v)[i + u.length]? = v[i]? := by
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel]
  have h2 : (v ++ u)[i]? = v[i]? := List.getElem?_append_left hiv
  rw [h1, ← h2, ← h]

/-- **Lyndon–Schützenberger Word Commutation Theorem:**
Two words `u, v : List α` commute (`u ++ v = v ++ u`) iff both are integer powers
of a common word `r : List α`. -/
theorem lyndon_schutzenberger_comm {α : Type*} (u v : List α) :
    u ++ v = v ++ u ↔
      ∃ (r : List α) (a b : ℕ),
        u = (List.replicate a r).flatten ∧ v = (List.replicate b r).flatten := by
  constructor
  · intro hcomm
    by_cases hu : u = []
    · subst hu
      exact ⟨v, 0, 1, by simp, by simp⟩
    · by_cases hv : v = []
      · subst hv
        exact ⟨u, 1, 0, by simp, by simp⟩
      · have hu_pos : 0 < u.length := List.length_pos_iff.mpr hu
        have hv_pos : 0 < v.length := List.length_pos_iff.mpr hv
        have hpu : HasPeriod (u ++ v) u.length := comm_hasPeriod_left hcomm
        have hpv : HasPeriod (u ++ v) v.length := by
          rw [hcomm]
          exact comm_hasPeriod_left hcomm.symm
        let d := Nat.gcd u.length v.length
        have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left v.length hu_pos
        have hlen : u.length + v.length - d ≤ (u ++ v).length := by
          rw [List.length_append]; omega
        have hpd : HasPeriod (u ++ v) d := fine_wilf (u ++ v) hu_pos hv_pos hpu hpv hlen
        let r := (u ++ v).take d
        rcases Nat.gcd_dvd_left u.length v.length with ⟨a, ha⟩
        rcases Nat.gcd_dvd_right u.length v.length with ⟨b, hb⟩
        have ha' : u.length = a * d := by rw [ha, mul_comm]
        have hb' : v.length = b * d := by rw [hb, mul_comm]
        have hu_per : HasPeriod u d := by
          simpa [List.take_left] using (hasPeriod_take (k := u.length) hpd)
        have hv_per : HasPeriod v d := by
          have h1 : (u ++ v).drop u.length = v := List.drop_left
          simpa [h1] using (hasPeriod_drop (k := u.length) hpd)
        have hu_eq := list_eq_replicate_flatten_of_period a u d hd_pos hu_per ha'
        have hv_eq := list_eq_replicate_flatten_of_period b v d hd_pos hv_per hb'
        have hr_u : u.take d = r := by
          dsimp [r]
          rw [List.take_append_of_le_length (Nat.le_of_dvd hu_pos (Nat.gcd_dvd_left _ _))]
        have hr_v : v.take d = r := by
          have hv_eq' : v.take d = (v ++ u).take d :=
            (List.take_append_of_le_length (Nat.le_of_dvd hv_pos (Nat.gcd_dvd_right _ _))).symm
          rw [hv_eq', ← hcomm]
        rw [hr_u] at hu_eq
        rw [hr_v] at hv_eq
        exact ⟨r, a, b, hu_eq, hv_eq⟩
  · rintro ⟨r, a, b, rfl, rfl⟩
    rw [← List.flatten_append, ← List.flatten_append, ← List.replicate_add,
        ← List.replicate_add, add_comm a b]

/-- A word `r : List α` is primitive if it is non-empty and not a nontrivial integer power. -/
def IsPrimitive {α : Type*} (r : List α) : Prop :=
  r ≠ [] ∧ ∀ (p : List α) (k : ℕ), r = (List.replicate k p).flatten → k = 1

private lemma length_replicate_flatten {α : Type*} (k : ℕ) (p : List α) :
    (List.replicate k p).flatten.length = k * p.length := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [List.replicate_succ, ih, Nat.succ_mul, add_comm]

private lemma replicate_mul_flatten {α : Type*} (k₁ k₂ : ℕ) (r : List α) :
    (List.replicate k₁ (List.replicate k₂ r).flatten).flatten =
      (List.replicate (k₁ * k₂) r).flatten := by
  induction k₁ with
  | zero => simp
  | succ k₁ ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul,
        add_comm (k₁ * k₂) k₂, List.replicate_add, List.flatten_append]

/-- **Primitive Root Existence:**
Every non-empty word `w` is a positive power `k ≥ 1` of a primitive word `r`. -/
theorem primitive_root_exists {α : Type*} (w : List α) (hw : w ≠ []) :
    ∃ (r : List α) (k : ℕ), IsPrimitive r ∧ 1 ≤ k ∧ w = (List.replicate k r).flatten := by
  classical
  let P : ℕ → Prop := fun m => 0 < m ∧ ∃ r : List α, ∃ k : ℕ,
    r.length = m ∧ 1 ≤ k ∧ w = (List.replicate k r).flatten
  have hex : ∃ m, P m := ⟨w.length, List.length_pos_iff.mpr hw, w, 1, rfl, le_rfl, by simp⟩
  let m := Nat.find hex
  have hm : P m := Nat.find_spec hex
  rcases hm with ⟨hm_pos, r, k, hr_len, hk, hwk⟩
  have hr_pos : 0 < r.length := by rw [hr_len]; exact hm_pos
  refine ⟨r, k, ⟨List.length_pos_iff.mp hr_pos, ?_⟩, hk, hwk⟩
  intro p j hrj
  rcases j with _ | j
  · simp at hrj
    rw [hrj] at hr_pos
    simp at hr_pos
  · rcases j with _ | j
    · rfl
    · have hp_pos : 0 < p.length := by
        have hlen_r := congrArg List.length hrj
        rw [length_replicate_flatten] at hlen_r
        rcases Nat.eq_zero_or_pos p.length with hp0 | hp_pos
        · simp [hp0] at hlen_r
          rw [hlen_r] at hr_pos
          simp at hr_pos
        · exact hp_pos
      have hlen_r : r.length = (j + 2) * p.length := by
        rw [hrj, length_replicate_flatten]
      have hp_lt_r : p.length < r.length := by
        have : 2 ≤ j + 2 := by omega
        nlinarith
      have hp_lt : p.length < m := by rw [← hr_len]; exact hp_lt_r
      have hsub : w = (List.replicate (k * (j + 2)) p).flatten := by
        rw [hwk, hrj, replicate_mul_flatten]
      have hP_p : P p.length := ⟨hp_pos, p, k * (j + 2), rfl, Nat.mul_pos hk (by omega), hsub⟩
      exact absurd hP_p (Nat.find_min hex hp_lt)

private lemma replicate_flatten_comm {α : Type*} (k : ℕ) (r : List α) :
    r ++ (List.replicate k r).flatten = (List.replicate k r).flatten ++ r := by
  have h1 : r = (List.replicate 1 r).flatten := by simp
  calc r ++ (List.replicate k r).flatten
      = (List.replicate 1 r).flatten ++ (List.replicate k r).flatten := by rw [← h1]
    _ = (List.replicate (1 + k) r).flatten := by rw [← List.flatten_append, ← List.replicate_add]
    _ = (List.replicate (k + 1) r).flatten := by rw [add_comm]
    _ = (List.replicate k r).flatten ++ (List.replicate 1 r).flatten := by
        rw [List.replicate_add, List.flatten_append]
    _ = (List.replicate k r).flatten ++ r := by rw [← h1]

/-- **Primitive Root Uniqueness:**
If two primitive words have equal positive powers, the primitive bases and exponents coincide. -/
theorem primitive_root_unique {α : Type*} {r₁ r₂ : List α} {k₁ k₂ : ℕ}
    (h1 : IsPrimitive r₁) (h2 : IsPrimitive r₂) (hk1 : 1 ≤ k₁) (hk2 : 1 ≤ k₂)
    (heq : (List.replicate k₁ r₁).flatten = (List.replicate k₂ r₂).flatten) :
    r₁ = r₂ ∧ k₁ = k₂ := by
  have hlen1 : r₁.length = r₁.length := rfl
  have hr1_len : 0 < r₁.length := List.length_pos_iff.mpr h1.1
  have hr2_len : 0 < r₂.length := List.length_pos_iff.mpr h2.1
  have hr_eq : r₁ = r₂ := by
    by_cases hk1_1 : k₁ = 1
    · subst hk1_1
      simp only [List.replicate_one, List.flatten_singleton] at heq
      have := h1.2 r₂ k₂ heq
      subst this
      simpa using heq
    · by_cases hk2_1 : k₂ = 1
      · subst hk2_1
        simp only [List.replicate_one, List.flatten_singleton] at heq
        have := h2.2 r₁ k₁ heq.symm
        subst this
        simpa using heq
      · let w := (List.replicate k₁ r₁).flatten
        have hw_len1 : w.length = k₁ * r₁.length := length_replicate_flatten k₁ r₁
        have hw_len2 : w.length = k₂ * r₂.length := by
          dsimp [w]; rw [heq, length_replicate_flatten]
        have hper1 : HasPeriod w r₁.length := by
          intro i hi
          have hcomm : r₁ ++ w = w ++ r₁ := replicate_flatten_comm k₁ r₁
          have h1 : (r₁ ++ w)[i + r₁.length]? = w[i]? := by
            rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel]
          have h2 : (w ++ r₁)[i + r₁.length]? = w[i + r₁.length]? :=
            List.getElem?_append_left hi
          rw [← h1, hcomm, h2]
        have hper2 : HasPeriod w r₂.length := by
          intro i hi
          have hcomm : r₂ ++ w = w ++ r₂ := by
            dsimp [w]; rw [heq]; exact replicate_flatten_comm k₂ r₂
          have h1 : (r₂ ++ w)[i + r₂.length]? = w[i]? := by
            rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel]
          have h2 : (w ++ r₂)[i + r₂.length]? = w[i + r₂.length]? :=
            List.getElem?_append_left hi
          rw [← h1, hcomm, h2]
        have hle_sum : r₁.length + r₂.length ≤ w.length := by
          have ha : 2 ≤ k₁ := by omega
          have hb : 2 ≤ k₂ := by omega
          have h2a : 2 * r₁.length ≤ w.length := by rw [hw_len1]; exact Nat.mul_le_mul_right _ ha
          have h2b : 2 * r₂.length ≤ w.length := by rw [hw_len2]; exact Nat.mul_le_mul_right _ hb
          omega
        let d := Nat.gcd r₁.length r₂.length
        have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left r₂.length hr1_len
        have hpd : HasPeriod w d :=
          fine_wilf w hr1_len hr2_len hper1 hper2 (by omega)
        rcases Nat.gcd_dvd_left r₁.length r₂.length with ⟨a, ha⟩
        rcases Nat.gcd_dvd_right r₁.length r₂.length with ⟨b, hb⟩
        have hr1_le : r₁.length ≤ w.length := by rw [hw_len1]; exact Nat.le_mul_of_pos_left _ hk1
        have hr2_le : r₂.length ≤ w.length := by rw [hw_len2]; exact Nat.le_mul_of_pos_left _ hk2
        have hr1_eq_take : r₁ = w.take r₁.length := by
          have hk1_succ : k₁ = (k₁ - 1) + 1 := by omega
          dsimp [w]
          rw [hk1_succ, add_comm (k₁ - 1) 1, List.replicate_add, List.flatten_append,
              List.replicate_one, List.flatten_singleton, List.take_left]
        have hr2_eq_take : r₂ = w.take r₂.length := by
          have hk2_succ : k₂ = (k₂ - 1) + 1 := by omega
          dsimp [w]
          rw [heq, hk2_succ, add_comm (k₂ - 1) 1, List.replicate_add, List.flatten_append,
              List.replicate_one, List.flatten_singleton, List.take_left]
        have hr1_per : HasPeriod r₁ d := by rw [hr1_eq_take]; exact hasPeriod_take hpd
        have hr2_per : HasPeriod r₂ d := by rw [hr2_eq_take]; exact hasPeriod_take hpd
        have hr1_pow := list_eq_replicate_flatten_of_period a r₁ d hd_pos hr1_per (by rw [ha, mul_comm])
        have hr2_pow := list_eq_replicate_flatten_of_period b r₂ d hd_pos hr2_per (by rw [hb, mul_comm])
        have ha1 : a = 1 := h1.2 _ a hr1_pow
        have hb1 : b = 1 := h2.2 _ b hr2_pow
        subst ha1; subst hb1
        simp only [List.replicate_one, List.flatten_singleton] at hr1_pow hr2_pow
        have htake1 : r₁.take d = w.take d := by
          rw [hr1_eq_take, List.take_take, min_eq_left (Nat.le_of_dvd hr1_len (Nat.gcd_dvd_left _ _))]
        have htake2 : r₂.take d = w.take d := by
          rw [hr2_eq_take, List.take_take, min_eq_left (Nat.le_of_dvd hr2_len (Nat.gcd_dvd_right _ _))]
        rw [hr1_pow, hr2_pow, htake1, htake2]
  refine ⟨hr_eq, ?_⟩
  subst hr_eq
  have hlen := congrArg List.length heq
  rw [length_replicate_flatten, length_replicate_flatten] at hlen
  exact Nat.mul_right_cancel hr1_len hlen

/-- **Lyndon–Schützenberger Power Commutation:**
If two positive powers `(replicate m u).flatten` and `(replicate n v).flatten` are equal,
then `u` and `v` commute (`u ++ v = v ++ u`). -/
theorem lyndon_schutzenberger_power_comm {α : Type*} {u v : List α} {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n)
    (heq : (List.replicate m u).flatten = (List.replicate n v).flatten) :
    u ++ v = v ++ u := by
  by_cases hu : u = []
  · subst hu; simp
  · by_cases hv : v = []
    · subst hv; simp
    · obtain ⟨r₁, a, h1, ha, hua⟩ := primitive_root_exists u hu
      obtain ⟨r₂, b, h2, hb, hvb⟩ := primitive_root_exists v hv
      have htot : (List.replicate (m * a) r₁).flatten = (List.replicate (n * b) r₂).flatten := by
        rw [← replicate_mul_flatten m a r₁, ← replicate_mul_flatten n b r₂, ← hua, ← hvb, heq]
      have hr : r₁ = r₂ ∧ m * a = n * b :=
        primitive_root_unique h1 h2 (Nat.mul_pos hm ha) (Nat.mul_pos hn hb) htot
      rw [lyndon_schutzenberger_comm]
      exact ⟨r₁, a, b, hua, hr.1 ▸ hvb⟩

end WordCommutation

/-! ## Section 3: Myhill–Nerode Fooling-Set Lower Bounds & Determinization Ceiling -/

section MyhillNerode

private lemma dfa_evalFrom_append {α Q : Type*} (M : DFA α Q) (q : Q) (u v : List α) :
    M.evalFrom q (u ++ v) = M.evalFrom (M.evalFrom q u) v := by
  simp [DFA.evalFrom, List.foldl_append]

/-- **Myhill–Nerode Fooling-Set Lower Bound:**
If `m` words `F 0, ..., F (m - 1)` are pairwise distinguishable with respect to `L`,
then any `DFA α (Fin k)` recognizing `L` satisfies `m ≤ k`. -/
theorem myhill_nerode_fooling_set {α : Type*} (L : Set (List α)) {m k : ℕ}
    (F : Fin m → List α)
    (hdist : ∀ i j : Fin m, i ≠ j →
      ∃ z : List α, (F i ++ z ∈ L ↔ F j ++ z ∉ L))
    (M : DFA α (Fin k)) (hrec : M.accepts = L) :
    m ≤ k := by
  have hinj : Function.Injective (fun i : Fin m => M.eval (F i)) := by
    intro i j heq
    by_contra hij
    obtain ⟨z, hz⟩ := hdist i j hij
    have heval : M.eval (F i ++ z) = M.eval (F j ++ z) := by
      simp only [DFA.eval, dfa_evalFrom_append]
      exact congrArg (fun q => M.evalFrom q z) heq
    have hi_iff : F i ++ z ∈ L ↔ M.eval (F i ++ z) ∈ M.accept := by
      rw [← hrec]; rfl
    have hj_iff : F j ++ z ∈ L ↔ M.eval (F j ++ z) ∈ M.accept := by
      rw [← hrec]; rfl
    rw [hi_iff, hj_iff, heval] at hz
    tauto
  simpa using Fintype.card_le_of_injective _ hinj

/-- **Fooling-Set Impossibility Corollary:**
No `k`-state DFA with `k < m` recognizes a language admitting a size-`m` fooling set. -/
theorem no_small_dfa_of_fooling_set {α : Type*} (L : Set (List α)) {m k : ℕ}
    (F : Fin m → List α)
    (hdist : ∀ i j : Fin m, i ≠ j →
      ∃ z : List α, (F i ++ z ∈ L ↔ F j ++ z ∉ L))
    (hk : k < m) (M : DFA α (Fin k)) :
    M.accepts ≠ L := by
  intro hrec
  have := myhill_nerode_fooling_set L F hdist M hrec
  omega

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

/-- **NFA Determinization on `Fin (2 ^ m)`:**
Every `m`-state NFA determinizes to an equivalent `(2 ^ m)`-state DFA. -/
theorem nfa_determinization_dfa {α : Type*} {m : ℕ} (N : NFA α (Fin m)) :
    ∃ M : DFA α (Fin (2 ^ m)), M.accepts = N.accepts := by
  classical
  let e : Set (Fin m) ≃ Fin (2 ^ m) := Fintype.equivFinOfCardEq (by simp)
  refine ⟨mapDFA e N.toDFA, ?_⟩
  ext u
  rw [mapDFA_accepts, NFA.toDFA_correct]

/-- **Separation Determinization Ceiling (`sep ≤ 2 ^ nsep`):**
If an `m`-state NFA separates `w` and `x`, then some `(2 ^ m)`-state DFA separates `w` and `x`. -/
theorem sep_le_two_pow_nsep {α : Type*} (m : ℕ) (w x : List α)
    (h : ∃ N : NFA α (Fin m), w ∈ N.accepts ↔ x ∉ N.accepts) :
    ∃ M : DFA α (Fin (2 ^ m)), w ∈ M.accepts ↔ x ∉ M.accepts := by
  rcases h with ⟨N, hsep⟩
  obtain ⟨M, hacc⟩ := nfa_determinization_dfa N
  refine ⟨M, ?_⟩
  rw [hacc]
  exact hsep

end MyhillNerode

/-! ## Section 4: Explicit Closure & Product Automata -/

section ClosureAutomata

/-- Product of two DFAs with an arbitrary accepting predicate on `Q₁ × Q₂`. -/
def prodDFA {α Q₁ Q₂ : Type*} (M₁ : DFA α Q₁) (M₂ : DFA α Q₂) (acc : Set (Q₁ × Q₂)) :
    DFA α (Q₁ × Q₂) where
  step q a := (M₁.step q.1 a, M₂.step q.2 a)
  start := (M₁.start, M₂.start)
  accept := acc

theorem prodDFA_evalFrom {α Q₁ Q₂ : Type*} (M₁ : DFA α Q₁) (M₂ : DFA α Q₂)
    (acc : Set (Q₁ × Q₂)) :
    ∀ (q₁ : Q₁) (q₂ : Q₂) (u : List α),
      (prodDFA M₁ M₂ acc).evalFrom (q₁, q₂) u = (M₁.evalFrom q₁ u, M₂.evalFrom q₂ u)
  | _, _, [] => rfl
  | q₁, q₂, a :: u => by
    simp only [DFA.evalFrom, List.foldl_cons, prodDFA]
    exact prodDFA_evalFrom M₁ M₂ acc (M₁.step q₁ a) (M₂.step q₂ a) u

private theorem prodDFA_accepts {α Q₁ Q₂ : Type*} (M₁ : DFA α Q₁) (M₂ : DFA α Q₂)
    (acc : Set (Q₁ × Q₂)) (u : List α) :
    u ∈ (prodDFA M₁ M₂ acc).accepts ↔ (M₁.eval u, M₂.eval u) ∈ acc := by
  change (prodDFA M₁ M₂ acc).evalFrom (M₁.start, M₂.start) u ∈ acc ↔
    (M₁.evalFrom M₁.start u, M₂.evalFrom M₂.start u) ∈ acc
  rw [prodDFA_evalFrom]

/-- **DFA Intersection Closure (`m₁ * m₂` states):**
The intersection of languages of an `m₁`-state and `m₂`-state DFA is recognized by an `(m₁ * m₂)`-state DFA. -/
theorem dfa_inter_closure {α : Type*} {m₁ m₂ : ℕ}
    (M₁ : DFA α (Fin m₁)) (M₂ : DFA α (Fin m₂)) :
    ∃ M : DFA α (Fin (m₁ * m₂)), ∀ u : List α, u ∈ M.accepts ↔ u ∈ M₁.accepts ∧ u ∈ M₂.accepts := by
  let P := prodDFA M₁ M₂ { q | q.1 ∈ M₁.accept ∧ q.2 ∈ M₂.accept }
  refine ⟨mapDFA finProdFinEquiv P, fun u => ?_⟩
  rw [mapDFA_accepts, prodDFA_accepts]
  rfl

/-- **DFA Union Closure (`m₁ * m₂` states):**
The union of languages of an `m₁`-state and `m₂`-state DFA is recognized by an `(m₁ * m₂)`-state DFA. -/
theorem dfa_union_closure {α : Type*} {m₁ m₂ : ℕ}
    (M₁ : DFA α (Fin m₁)) (M₂ : DFA α (Fin m₂)) :
    ∃ M : DFA α (Fin (m₁ * m₂)), ∀ u : List α, u ∈ M.accepts ↔ u ∈ M₁.accepts ∨ u ∈ M₂.accepts := by
  let P := prodDFA M₁ M₂ { q | q.1 ∈ M₁.accept ∨ q.2 ∈ M₂.accept }
  refine ⟨mapDFA finProdFinEquiv P, fun u => ?_⟩
  rw [mapDFA_accepts, prodDFA_accepts]
  rfl

/-- **DFA Symmetric Difference Closure (`m₁ * m₂` states):** -/
theorem dfa_symmDiff_closure {α : Type*} {m₁ m₂ : ℕ}
    (M₁ : DFA α (Fin m₁)) (M₂ : DFA α (Fin m₂)) :
    ∃ M : DFA α (Fin (m₁ * m₂)), M.accepts = symmDiff M₁.accepts M₂.accepts := by
  let P := prodDFA M₁ M₂ { q | (q.1 ∈ M₁.accept ∧ q.2 ∉ M₂.accept) ∨
    (q.2 ∈ M₂.accept ∧ q.1 ∉ M₁.accept) }
  refine ⟨mapDFA finProdFinEquiv P, ?_⟩
  ext u
  rw [mapDFA_accepts, prodDFA_accepts]
  rfl

/-- Complement of a DFA (`(M.accepts)ᶜ`), preserving the state set `Q`. -/
def complDFA {α Q : Type*} (M : DFA α Q) : DFA α Q where
  step := M.step
  start := M.start
  accept := (M.accept)ᶜ

/-- **DFA Complement Closure:** -/
theorem dfa_compl_closure {α Q : Type*} (M : DFA α Q) :
    (complDFA M).accepts = (M.accepts)ᶜ := by
  ext u
  rfl

/-- Reversal of an NFA (`accept` and `start` swapped, transition relation transposed). -/
def revNFA {α Q : Type*} (N : NFA α Q) : NFA α Q where
  step q a := { s | q ∈ N.step s a }
  start := N.accept
  accept := N.start

private lemma nfa_evalFrom_append {α Q : Type*} (N : NFA α Q) (S : Set Q) (u v : List α) :
    N.evalFrom S (u ++ v) = N.evalFrom (N.evalFrom S u) v := by
  induction u generalizing S with
  | nil => simp [NFA.evalFrom]
  | cons a u ih =>
    simp only [List.cons_append, NFA.evalFrom_cons]
    exact ih _

private lemma revNFA_evalFrom_duality {α Q : Type*} (N : NFA α Q) :
    ∀ (u : List α) (A B : Set Q),
      (∃ b ∈ B, b ∈ (revNFA N).evalFrom A u) ↔ (∃ a ∈ A, a ∈ N.evalFrom B u.reverse)
  | [], A, B => by
    simp only [NFA.evalFrom_nil, List.reverse_nil]
    constructor
    · rintro ⟨b, hbB, hbA⟩; exact ⟨b, hbA, hbB⟩
    · rintro ⟨a, haA, haB⟩; exact ⟨a, haB, haA⟩
  | a :: u, A, B => by
    rw [NFA.evalFrom_cons, List.reverse_cons, nfa_evalFrom_append, NFA.evalFrom_cons,
        NFA.evalFrom_nil]
    rw [revNFA_evalFrom_duality N u ((revNFA N).stepSet A a) B]
    constructor
    · rintro ⟨x, hx, hxN⟩
      rw [NFA.mem_stepSet] at hx
      rcases hx with ⟨y, hyA, hyx⟩
      change y ∈ N.step x a at hyx
      refine ⟨y, hyA, ?_⟩
      rw [NFA.mem_stepSet]
      exact ⟨x, hxN, hyx⟩
    · rintro ⟨y, hyA, hyN⟩
      rw [NFA.mem_stepSet] at hyN
      rcases hyN with ⟨x, hxN, hxy⟩
      refine ⟨x, ?_, hxN⟩
      rw [NFA.mem_stepSet]
      exact ⟨y, hyA, hxy⟩

/-- **NFA Reversal Closure (exact `m` states):**
Reversing an `m`-state NFA yields an `m`-state NFA recognizing `{ u | u.reverse ∈ N.accepts }`. -/
theorem nfa_reversal_closure {α Q : Type*} (N : NFA α Q) :
    ∀ u : List α, u ∈ (revNFA N).accepts ↔ u.reverse ∈ N.accepts := by
  intro u
  rw [NFA.mem_accepts, NFA.mem_accepts]
  change (∃ b ∈ N.start, b ∈ (revNFA N).evalFrom N.accept u) ↔
    ∃ a ∈ N.accept, a ∈ N.evalFrom N.start u.reverse
  exact revNFA_evalFrom_duality N u N.accept N.start

/-- **DFA Reversal Closure (`2 ^ m` states):**
The reversal of the language of any `m`-state DFA is recognized by a `(2 ^ m)`-state DFA. -/
theorem dfa_reversal_closure {α : Type*} {m : ℕ} (M : DFA α (Fin m)) :
    ∃ D : DFA α (Fin (2 ^ m)), ∀ u : List α, u ∈ D.accepts ↔ u.reverse ∈ M.accepts := by
  let N : NFA α (Fin m) := {
    step := fun q a => {M.step q a}
    start := {M.start}
    accept := M.accept
  }
  have hN_eval : ∀ (q : Fin m) (u : List α), N.evalFrom {q} u = {M.evalFrom q u} := by
    intro q u
    induction u generalizing q with
    | nil => simp [NFA.evalFrom, DFA.evalFrom]
    | cons a u ih =>
      rw [NFA.evalFrom_cons, DFA.evalFrom, List.foldl_cons]
      have hs : N.stepSet {q} a = {M.step q a} := by
        ext s; simp [N]
      rw [hs]
      exact ih (M.step q a)
  have hN_acc : ∀ u : List α, u ∈ N.accepts ↔ u ∈ M.accepts := by
    intro u
    rw [NFA.mem_accepts]
    change (∃ s ∈ M.accept, s ∈ N.evalFrom {M.start} u) ↔ M.eval u ∈ M.accept
    rw [hN_eval M.start u]
    simp [DFA.eval]
  obtain ⟨D, hD⟩ := nfa_determinization_dfa (revNFA N)
  refine ⟨D, fun u => ?_⟩
  rw [hD, nfa_reversal_closure, hN_acc]

end ClosureAutomata

/-! ## Section 5: Regular & Unary-Cycle Pumping Lemmas -/

section PumpingLemmas

private lemma replicate_flatten_append_evalFrom {α Q : Type*} (M : DFA α Q) (q : Q)
    (y : List α) (hy : M.evalFrom q y = q) :
    ∀ n : ℕ, M.evalFrom q (List.replicate n y).flatten = q
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, dfa_evalFrom_append, hy]
    exact replicate_flatten_append_evalFrom M q y hy n

/-- **Regular DFA Pumping Lemma (`Fin m`):**
Every word `w ∈ M.accepts` of length `m ≤ w.length` decomposes as `w = x ++ y ++ z`
with `x.length + y.length ≤ m`, `1 ≤ y.length`, and `x ++ y^n ++ z ∈ M.accepts` for all `n : ℕ`. -/
theorem dfa_pumping_lemma {α : Type*} {m : ℕ} (M : DFA α (Fin m))
    (w : List α) (hw : w ∈ M.accepts) (hlen : m ≤ w.length) :
    ∃ x y z : List α,
      w = x ++ y ++ z ∧
      x.length + y.length ≤ m ∧
      1 ≤ y.length ∧
      ∀ n : ℕ, x ++ (List.replicate n y).flatten ++ z ∈ M.accepts := by
  have hlt : Fintype.card (Fin m) < Fintype.card (Fin (m + 1)) := by simp
  obtain ⟨r1, r2, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun r : Fin (m + 1) => M.eval (w.take r.1)) hlt
  obtain ⟨i, j, hij, hjm, heq_ij⟩ :
      ∃ i j : ℕ, i < j ∧ j ≤ m ∧ M.eval (w.take i) = M.eval (w.take j) := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h12 | h21
    · exact ⟨r1.1, r2.1, h12, Nat.le_of_lt_succ r2.isLt, heq⟩
    · exact ⟨r2.1, r1.1, h21, Nat.le_of_lt_succ r1.isLt, heq.symm⟩
  let x := w.take i
  let y := (w.take j).drop i
  let z := w.drop j
  have hij_le : i ≤ j := Nat.le_of_lt hij
  have hxy : x ++ y = w.take j := by
    dsimp [x, y]
    have hti : List.take i w = List.take i (List.take j w) := by
      rw [List.take_take, min_eq_left hij_le]
    rw [hti]
    exact List.take_append_drop i (w.take j)
  have hxyz : w = x ++ y ++ z := by
    rw [hxy]
    exact (List.take_append_drop j w).symm
  have hx_len : x.length = i := List.length_take_of_le (by omega)
  have hxy_len : (x ++ y).length = j := by
    rw [hxy]
    exact List.length_take_of_le (by omega)
  have hy_len : y.length = j - i := by
    rw [List.length_append] at hxy_len
    omega
  have hloop : M.evalFrom (M.eval x) y = M.eval x := by
    change M.evalFrom (M.evalFrom M.start x) y = M.eval x
    rw [← dfa_evalFrom_append]
    change M.eval (x ++ y) = M.eval x
    rw [hxy]
    exact heq_ij.symm
  refine ⟨x, y, z, hxyz, by rw [← List.length_append, hxy_len]; exact hjm, by omega, ?_⟩
  intro n
  change M.eval (x ++ (List.replicate n y).flatten ++ z) ∈ M.accept
  rw [DFA.eval, dfa_evalFrom_append, dfa_evalFrom_append,
      replicate_flatten_append_evalFrom M (M.evalFrom M.start x) y hloop n]
  change M.evalFrom (M.eval x) z ∈ M.accept
  rw [heq_ij]
  change M.evalFrom (M.evalFrom M.start (w.take j)) z ∈ M.accept
  rw [← dfa_evalFrom_append]
  have htz : w.take j ++ z = w := List.take_append_drop j w
  change M.eval (w.take j ++ z) ∈ M.accept
  rw [htz]
  exact hw

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

/-- **Unary-Cycle `lcm(1..t)` Pumping Lemma:**
For any `d`-state DFA (`d ≤ t`), any state `q : Fin d`, any letter `c : α`,
any `n ≥ t - 1`, and any multiple `L` of every `p ∈ [1, t]` (e.g. `Finset.lcm (Finset.Icc 1 t) id`),
reading `n + L` copies of `c` lands in the exact same state as reading `n` copies of `c`. -/
theorem dfa_unary_lcm_pump {α : Type*} {d t : ℕ} (hd : d ≤ t) (M : DFA α (Fin d))
    (q : Fin d) (c : α) (L : ℕ) (hL : ∀ p ∈ Finset.Icc 1 t, p ∣ L)
    (n : ℕ) (hn : t - 1 ≤ n) :
    M.evalFrom q (List.replicate (n + L) c) = M.evalFrom q (List.replicate n c) := by
  rw [dfa_evalFrom_replicate, dfa_evalFrom_replicate]
  obtain ⟨i, j, hij, hjd, heq⟩ := fin_iter_cycle (fun r => M.step r c) q
  let p := j - i
  have hp_mem : p ∈ Finset.Icc 1 t := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  obtain ⟨m, hm⟩ := hL p hp_mem
  have hjp : i + p = j := by omega
  have hp_eq : (fun r => M.step r c)^[i] q = (fun r => M.step r c)^[i + p] q := hjp ▸ heq
  have hi_le : i ≤ n := by omega
  have hdecomp : n + L = (n - i) + (i + m * p) := by
    rw [hm, mul_comm p m]
    omega
  have hn_decomp : n = (n - i) + i := by omega
  rw [hdecomp, Function.iterate_add_apply,
      iter_add_period_mul (fun r => M.step r c) q i p hp_eq m,
      ← Function.iterate_add_apply, ← hn_decomp]

/-- **Unary Block `lcm(1..t)` Acceptance Invariance:**
Inserting `Finset.lcm (Finset.Icc 1 t) id` copies of `c` into any unary block of length
`n ≥ t - 1` leaves acceptance invariant for every `d`-state DFA (`d ≤ t`). -/
theorem dfa_unary_block_lcm_eq {α : Type*} {d t : ℕ} (hd : d ≤ t) (M : DFA α (Fin d))
    (u v : List α) (c : α) (n : ℕ) (hn : t - 1 ≤ n) :
    let L := Finset.lcm (Finset.Icc 1 t) id
    u ++ List.replicate (n + L) c ++ v ∈ M.accepts ↔
      u ++ List.replicate n c ++ v ∈ M.accepts := by
  intro L
  have hL : ∀ p ∈ Finset.Icc 1 t, p ∣ L := fun p hp => Finset.dvd_lcm hp
  change M.eval (u ++ List.replicate (n + L) c ++ v) ∈ M.accept ↔
    M.eval (u ++ List.replicate n c ++ v) ∈ M.accept
  rw [DFA.eval, dfa_evalFrom_append, dfa_evalFrom_append,
      dfa_evalFrom_append, dfa_evalFrom_append,
      dfa_unary_lcm_pump hd M (M.evalFrom M.start u) c L hL n hn]

end PumpingLemmas

end Arith4Ext.AutomataCombinatorics
