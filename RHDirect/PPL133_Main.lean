/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-!
# PPL 133 (Erdős Problem #1052 — Unitary Perfect Numbers `A002827`):
# Sharp Exponential Upper Bound Improving Goto (2007), Exact 2-Adic Structure,
# Verification of All Five Known Examples, and Unconditional Bounded-`ω` / Bounded-`v₂` Finiteness

**Scope Notice (Genuine Unconditional Improvement & Structural Milestones — NOT Full Finiteness):**
Erdős Problem #1052 (`erdosproblems.com/1052`, Guy Problem B3, $10 prize) asks whether there are
only finitely many unitary perfect numbers (OEIS `A002827`). The full finiteness conjecture
remains **OPEN**.

This file formalizes the following **unconditional** theorems using the pure-Mathlib unitary
divisor predicate `d ∣ n ∧ Nat.Coprime d (n / d)` (matching `FormalConjectures/ErdosProblems/1052.lean`,
with zero custom definitions in the final public theorem signatures):

1. **Exact Multiplicative Formula (`unitaryDivisorSum_eq_prod`, `isUnitaryPerfect_iff_prod_eq`):**
   For every `n > 0`, `σ*(n) = ∏_{p ∈ n.primeFactors} (p^(v_p(n)) + 1)`, so `n` is unitary perfect
   iff `0 < n` and `∏_{p ∈ n.primeFactors} (p^(v_p(n)) + 1) = 2 * n`.
2. **All Five Known Unitary Perfect Numbers Verified Without `sorry`:**
   `6`, `60`, `90`, `87360`, and the 24-digit fifth unitary perfect number
   `146361946186458562560000 = 2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313`.
3. **Subbarao–Warren (1966) Parity & Exact 2-Adic Structural Laws:**
   - Every unitary perfect number is even (`even_of_isUnitaryPerfect`).
   - Exact 2-adic balance (`sum_v2_odd_components_eq`):
     `∑_{p ∈ n.primeFactors.erase 2} (p^(v_p(n)) + 1).factorization 2 = v_2(n) + 1`.
   - Component-count bound (`omega_le_v2_add_two`): `ω(n) ≤ v_2(n) + 2`.
   - Seed divisibility (`two_pow_add_one_dvd_odd_part`): `(2^(v_2(n)) + 1) ∣ (n / 2^(v_2(n)))`,
     hence `2^(2 * v_2(n)) < n`, `Odd (v_2(n)) → 3 ∣ n`, and `v_2(n) % 6 = 3 → 9 ∣ n`.
4. **NEW Sharp Exponential Upper Bound Strictly Improving Goto (2007):**
   Takeshi Goto (2007, *Rocky Mountain J. Math.* 37(5), 1557–1576) proved `n < 2^(2^(ω(n)))`
   (also formalized here as `goto_upper_bound`). By combining the 2-adic bound `v_2(n) ≥ ω(n) - 2`,
   parity cancellation of odd components `q_i + 1`, Cook's majorization lemma (proved cleanly via
   `Real.log_le_sub_one_of_pos` and Abel summation), and Nielsen's Lemma 1, we prove unconditionally:
   - **`sharper_upper_bound_ne_90`**: For **every** unitary perfect number `n ≠ 90` (in particular
     every UPN with `ω(n) ≥ 4` or `v_2(n) ≥ 2`),
     `n < 3^(2^(ω(n) - 1)) = (√3)^(2^(ω(n)))` (cutting the double-exponential base from `2` to
     `√3 ≈ 1.73205`, a super-exponential improvement factor of `(4/3)^(2^(ω(n) - 1))`, with `n = 90`
     being the unique exception since `90 > 81 = 3^4`).
   - **`sharper_upper_bound_of_three_five_exact`**: If `v_3(n) = 1`, `v_5(n) = 1`, and `ω(n) ≥ 3`,
     then `n < 3 * 5^(2^(ω(n) - 2))` (double-exponential base `5^(1/4) ≈ 1.49535`).
5. **Complete Small-`v_2` and Small-`ω` Classifications & Unconditional Finiteness:**
   - Complete classifications: `v_2(n) = 1 ↔ n ∈ {6, 90}`, `v_2(n) = 2 ↔ n = 60`,
     `v_2(n) ≠ 3`, `v_2(n) ≤ 3 ↔ n ∈ {6, 60, 90}`, `ω(n) ≤ 3 ↔ n ∈ {6, 60, 90}`.
   - Explicit `v_2`-bound `n < 3^(2^(v_2(n) + 1))` (for `v_2(n) ≥ 2`) and unconditional finiteness
     of `{n | IsUPN n ∧ ω(n) ≤ K}` and `{n | IsUPN n ∧ v_2(n) ≤ A}` for every `K, A : ℕ`.
-/

namespace PPL133

/-! ## Section 1: Multiplicative Formula for the Unitary Divisor Sum `σ*(n)` -/

section MultiplicativeFormula

private lemma prod_primePow_dvd {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ) (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p) ∣ n := by
  have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn
  conv_rhs => rw [← hself]
  exact Finset.prod_dvd_prod_of_subset S n.primeFactors (fun p => p ^ n.factorization p) hS

private lemma prod_primePow_mul_sdiff {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p) * (∏ p ∈ n.primeFactors \ S, p ^ n.factorization p) = n := by
  have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn
  rw [mul_comm, Finset.prod_sdiff hS, hself]

private lemma coprime_prod_primePow_sdiff {n : ℕ} (S : Finset ℕ) (hS : S ⊆ n.primeFactors) :
    Nat.Coprime (∏ p ∈ S, p ^ n.factorization p)
      (∏ q ∈ n.primeFactors \ S, q ^ n.factorization q) := by
  refine Nat.coprime_prod_left_iff.mpr fun p hp => ?_
  refine Nat.coprime_prod_right_iff.mpr fun q hq => ?_
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors (hS hp)
  have hq_mem : q ∈ n.primeFactors := (Finset.mem_sdiff.mp hq).1
  have hq_not : q ∉ S := (Finset.mem_sdiff.mp hq).2
  have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_mem
  have hne : p ≠ q := fun h => hq_not (h ▸ hp)
  exact ((hp_prime.coprime_iff_not_dvd.mpr fun h =>
    hne ((Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp h)).pow_left _).pow_right _

private lemma prod_primePow_pos {n : ℕ} (S : Finset ℕ) (hS : S ⊆ n.primeFactors) :
    0 < ∏ p ∈ S, p ^ n.factorization p := by
  refine Finset.prod_pos fun p hp => ?_
  exact pow_pos (Nat.prime_of_mem_primeFactors (hS hp)).pos _

private lemma prod_primePow_unitary {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) :
    let d := ∏ p ∈ S, p ^ n.factorization p
    d ∣ n ∧ Nat.Coprime d (n / d) := by
  intro d
  have hmul : d * (∏ p ∈ n.primeFactors \ S, p ^ n.factorization p) = n :=
    prod_primePow_mul_sdiff hn S hS
  have hd_pos : 0 < d := prod_primePow_pos S hS
  have hdiv : n / d = ∏ p ∈ n.primeFactors \ S, p ^ n.factorization p := by
    conv_lhs => rw [← hmul]
    exact Nat.mul_div_cancel_left _ hd_pos
  refine ⟨⟨_, hmul.symm⟩, ?_⟩
  rw [hdiv]
  exact coprime_prod_primePow_sdiff S hS

private lemma unitary_eq_prod_primeFactors {n d : ℕ} (hn : n ≠ 0) (hd : d ∣ n)
    (hcop : Nat.Coprime d (n / d)) :
    d = ∏ p ∈ d.primeFactors, p ^ n.factorization p := by
  have hd_ne : d ≠ 0 := by
    intro h0
    subst h0
    exact hn (zero_dvd_iff.mp hd)
  have hnd_ne : n / d ≠ 0 := by
    intro h0
    have hmul : d * (n / d) = n := Nat.mul_div_cancel' hd
    rw [h0, mul_zero] at hmul
    exact hn hmul.symm
  have hself : ∏ p ∈ d.primeFactors, p ^ d.factorization p = d := by
    simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hd_ne
  conv_lhs => rw [← hself]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hmul : d * (n / d) = n := Nat.mul_div_cancel' hd
  have hfac : n.factorization p = d.factorization p + (n / d).factorization p := by
    conv_lhs => rw [← hmul]
    rw [Nat.factorization_mul hd_ne hnd_ne, Finsupp.add_apply]
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd_d : p ∣ d := Nat.dvd_of_mem_primeFactors hp
  have hp_not_dvd_nd : ¬ p ∣ (n / d) := by
    intro hpd
    have hpg : p ∣ Nat.gcd d (n / d) := Nat.dvd_gcd hp_dvd_d hpd
    rw [hcop.gcd_eq_one] at hpg
    exact hp_prime.not_dvd_one hpg
  have hnd_zero : (n / d).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hp_not_dvd_nd
  rw [hfac, hnd_zero, add_zero]

private lemma primeFactors_prod_primePow {n : ℕ} (_hn : n ≠ 0) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p).primeFactors = S := by
  ext p
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp_prime, hp_dvd, _⟩
    obtain ⟨q, hqS, hpq⟩ := hp_prime.prime.exists_mem_finset_dvd hp_dvd
    have hp_dvd_q : p ∣ q := hp_prime.dvd_of_dvd_pow hpq
    have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactors (hS hqS)
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp hp_dvd_q
    exact heq ▸ hqS
  · intro hpS
    have hp_mem : p ∈ n.primeFactors := hS hpS
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
    have hpos : 0 < n.factorization p :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ hp_mem))
    have hne : (∏ q ∈ S, q ^ n.factorization q) ≠ 0 := Nat.ne_of_gt (prod_primePow_pos S hS)
    refine ⟨hp_prime, ?_, hne⟩
    exact dvd_trans (dvd_pow_self p (Nat.ne_of_gt hpos))
      (Finset.dvd_prod_of_mem (fun q => q ^ n.factorization q) hpS)

/-- Exact multiplicative formula for the sum of all unitary divisors of `n > 0`. -/
theorem unitaryDivisorSum_eq_prod (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d =
      ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hbij :
      ∑ d ∈ (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d =
        ∑ S ∈ n.primeFactors.powerset, ∏ p ∈ S, p ^ n.factorization p := by
    symm
    refine Finset.sum_bij (fun S _ => ∏ p ∈ S, p ^ n.factorization p) ?_ ?_ ?_ ?_
    · intro S hS
      rw [Finset.mem_powerset] at hS
      rw [Finset.mem_filter, Finset.mem_Ico]
      have hu := prod_primePow_unitary hn0 S hS
      have hpos := prod_primePow_pos S hS
      have hle : (∏ p ∈ S, p ^ n.factorization p) ≤ n := Nat.le_of_dvd hn hu.1
      exact ⟨⟨hpos, Nat.lt_succ_of_le hle⟩, hu⟩
    · intro S₁ hS₁ S₂ hS₂ heq
      rw [Finset.mem_powerset] at hS₁ hS₂
      have h1 := primeFactors_prod_primePow hn0 S₁ hS₁
      have h2 := primeFactors_prod_primePow hn0 S₂ hS₂
      rw [← h1, ← h2, heq]
    · intro d hd
      rw [Finset.mem_filter, Finset.mem_Ico] at hd
      refine ⟨d.primeFactors, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        exact Nat.primeFactors_mono hd.2.1 hn0
      · exact (unitary_eq_prod_primeFactors hn0 hd.2.1 hd.2.2).symm
    · intro _ _
      rfl
  rw [hbij]
  have hprod : ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) =
      ∑ S ∈ n.primeFactors.powerset, ∏ p ∈ S, p ^ n.factorization p := by
    simpa [add_comm] using
      (Finset.prod_one_add (s := n.primeFactors) (f := fun p => p ^ n.factorization p))
  exact hprod.symm

/-- Splitting off the improper unitary divisor `n` from all unitary divisors in `[1, n]`. -/
theorem unitaryDivisorSum_eq_proper_add (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d =
      (∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d) + n := by
  have hIco : Finset.Ico 1 (n + 1) = insert n (Finset.Ico 1 n) := by
    ext d
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  have hn_mem : n ∣ n ∧ Nat.Coprime n (n / n) := by
    rw [Nat.div_self hn]
    exact ⟨dvd_refl n, Nat.coprime_one_right n⟩
  have hn_not_mem : n ∉ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)) := by
    simp [Finset.mem_filter, Finset.mem_Ico]
  rw [hIco, Finset.filter_insert, if_pos hn_mem, Finset.sum_insert hn_not_mem, add_comm]

/-- Fundamental equivalence: `n` is a unitary perfect number (sum of proper unitary divisors equals
`n`, with `0 < n`) if and only if `0 < n` and `∏_{p ∈ n.primeFactors} (p^(v_p(n)) + 1) = 2 * n`. -/
theorem isUnitaryPerfect_iff_prod_eq (n : ℕ) :
    (∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) ↔
      (0 < n ∧ ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) = 2 * n) := by
  constructor
  · rintro ⟨hsum, hpos⟩
    refine ⟨hpos, ?_⟩
    rw [← unitaryDivisorSum_eq_prod n hpos, unitaryDivisorSum_eq_proper_add n hpos, hsum]
    omega
  · rintro ⟨hpos, hprod⟩
    refine ⟨?_, hpos⟩
    have h1 := unitaryDivisorSum_eq_prod n hpos
    have h2 := unitaryDivisorSum_eq_proper_add n hpos
    rw [h2] at h1
    omega

end MultiplicativeFormula

/-! ## Section 2: Fast Verification of All Five Known Unitary Perfect Numbers -/

section KnownExamples

private lemma prime_dvd_list_prod {p : ℕ} (hp : Nat.Prime p) :
    ∀ {L : List ℕ}, p ∣ L.prod → ∃ x ∈ L, p ∣ x
  | [], h => absurd h hp.not_dvd_one
  | a :: L, h => by
      rw [List.prod_cons] at h
      rcases hp.dvd_mul.mp h with ha | hL
      · exact ⟨a, by simp, ha⟩
      · rcases prime_dvd_list_prod hp hL with ⟨x, hx, hpx⟩
        exact ⟨x, by simp [hx], hpx⟩

private lemma prod_unitary_of_list {n : ℕ} (L : List (ℕ × ℕ))
    (hprimes : ∀ pe ∈ L, Nat.Prime pe.1 ∧ 0 < pe.2)
    (hnodup : (L.map Prod.fst).Nodup)
    (hprod : (L.map (fun pe => pe.1 ^ pe.2)).prod = n) :
    0 < n ∧
      n.primeFactors = (L.map Prod.fst).toFinset ∧
      ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) =
        (L.map (fun pe => pe.1 ^ pe.2 + 1)).prod := by
  have hpos : 0 < n := by
    rw [← hprod]
    exact List.prod_pos fun x hx => by
      rcases List.mem_map.mp hx with ⟨pe, hpe, rfl⟩
      exact pow_pos (hprimes pe hpe).1.pos pe.2
  have hn0 : n ≠ 0 := Nat.ne_of_gt hpos
  have hfac_eq : ∀ pe ∈ L, n.factorization pe.1 = pe.2 := by
    intro pe hpe
    have hpe_prime := (hprimes pe hpe).1
    have hperm : ∀ (M : List (ℕ × ℕ)),
        (∀ x ∈ M, Nat.Prime x.1 ∧ 0 < x.2) →
        (M.map Prod.fst).Nodup →
        ∀ p : ℕ, Nat.Prime p →
          (M.map (fun x : ℕ × ℕ => x.1 ^ x.2)).prod.factorization p =
            (M.map (fun x : ℕ × ℕ => if x.1 = p then x.2 else 0)).sum := by
      intro M hMp hMnd p hp
      induction M with
      | nil => simp
      | cons a M ih =>
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        have ha_pos : a.1 ^ a.2 ≠ 0 :=
          Nat.ne_of_gt (pow_pos (hMp a (by simp)).1.pos a.2)
        have hM_pos : (M.map (fun x : ℕ × ℕ => x.1 ^ x.2)).prod ≠ 0 :=
          Nat.ne_of_gt (List.prod_pos fun y hy => by
            rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
            exact pow_pos (hMp x (by simp [hx])).1.pos x.2)
        rw [Nat.factorization_mul ha_pos hM_pos, Finsupp.add_apply,
          Nat.Prime.factorization_pow (hMp a (by simp)).1, Finsupp.single_apply]
        have ih' := ih (fun x hx => hMp x (by simp [hx])) (List.nodup_cons.mp hMnd).2
        rw [ih']
    rw [← hprod, hperm L hprimes hnodup pe.1 hpe_prime]
    clear hprod hpos hn0 hperm
    induction L with
    | nil => cases hpe
    | cons a M ih =>
      simp only [List.map_cons, List.sum_cons]
      have hnd := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hpe with hpe_eq | hpeM
      · subst hpe_eq
        simp only [↓reduceIte]
        have hzero : (M.map (fun x : ℕ × ℕ => if x.1 = pe.1 then x.2 else 0)).sum = 0 := by
          apply List.sum_eq_zero
          intro y hy
          rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
          split_ifs with hx1
          · exfalso
            exact hnd.1 (List.mem_map.mpr ⟨x, hx, hx1⟩)
          · rfl
        omega
      · have hne : a.1 ≠ pe.1 := by
          intro h
          exact hnd.1 (List.mem_map.mpr ⟨pe, hpeM, h.symm⟩)
        simp only [hne, ↓reduceIte, zero_add]
        exact ih (fun x hx => hprimes x (by simp [hx])) hnd.2 hpeM
  have hpf : n.primeFactors = (L.map Prod.fst).toFinset := by
    ext p
    rw [Nat.mem_primeFactors, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨hp_prime, hp_dvd, _⟩
      rw [← hprod] at hp_dvd
      obtain ⟨x, hx_mem, hp_dvd_x⟩ := prime_dvd_list_prod hp_prime hp_dvd
      rcases List.mem_map.mp hx_mem with ⟨pe, hpe, rfl⟩
      have hp_dvd_pe : p ∣ pe.1 := hp_prime.dvd_of_dvd_pow hp_dvd_x
      have heq : p = pe.1 := (Nat.prime_dvd_prime_iff_eq hp_prime (hprimes pe hpe).1).mp hp_dvd_pe
      exact ⟨pe, hpe, heq.symm⟩
    · rintro ⟨pe, hpe, rfl⟩
      refine ⟨(hprimes pe hpe).1, ?_, hn0⟩
      rw [← hprod]
      exact dvd_trans (dvd_pow_self pe.1 (Nat.ne_of_gt (hprimes pe hpe).2))
        (List.dvd_prod (List.mem_map.mpr ⟨pe, hpe, rfl⟩))
  refine ⟨hpos, hpf, ?_⟩
  rw [hpf]
  clear hpf hprod hpos hn0
  induction L with
  | nil => simp
  | cons a M ih =>
    simp only [List.map_cons, List.toFinset_cons, List.prod_cons]
    have hnd := List.nodup_cons.mp hnodup
    have hnot : a.1 ∉ (M.map Prod.fst).toFinset := by
      simpa [List.mem_toFinset] using hnd.1
    rw [Finset.prod_insert hnot]
    rw [hfac_eq a (by simp)]
    rw [ih (fun x hx => hprimes x (by simp [hx])) hnd.2 (fun x hx => hfac_eq x (by simp [hx]))]

/-- 1st known unitary perfect number: `6 = 2 * 3`. -/
theorem isUnitaryPerfect_6 :
    ∑ d ∈ (Finset.Ico 1 6).filter (fun d => d ∣ 6 ∧ Nat.Coprime d (6 / d)), d = 6 ∧ 0 < 6 := by
  rw [isUnitaryPerfect_iff_prod_eq]
  have h := prod_unitary_of_list (n := 6) [(2, 1), (3, 1)]
    (by intro pe hpe; simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
        rcases hpe with rfl | rfl <;> norm_num)
    (by decide)
    (by norm_num)
  exact ⟨h.1, by rw [h.2.2]; norm_num⟩

/-- 2nd known unitary perfect number: `60 = 2^2 * 3 * 5`. -/
theorem isUnitaryPerfect_60 :
    ∑ d ∈ (Finset.Ico 1 60).filter (fun d => d ∣ 60 ∧ Nat.Coprime d (60 / d)), d = 60 ∧ 0 < 60 := by
  rw [isUnitaryPerfect_iff_prod_eq]
  have h := prod_unitary_of_list (n := 60) [(2, 2), (3, 1), (5, 1)]
    (by intro pe hpe; simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
        rcases hpe with rfl | rfl | rfl <;> norm_num)
    (by decide)
    (by norm_num)
  exact ⟨h.1, by rw [h.2.2]; norm_num⟩

/-- 3rd known unitary perfect number: `90 = 2 * 3^2 * 5`. -/
theorem isUnitaryPerfect_90 :
    ∑ d ∈ (Finset.Ico 1 90).filter (fun d => d ∣ 90 ∧ Nat.Coprime d (90 / d)), d = 90 ∧ 0 < 90 := by
  rw [isUnitaryPerfect_iff_prod_eq]
  have h := prod_unitary_of_list (n := 90) [(2, 1), (3, 2), (5, 1)]
    (by intro pe hpe; simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
        rcases hpe with rfl | rfl | rfl <;> norm_num)
    (by decide)
    (by norm_num)
  exact ⟨h.1, by rw [h.2.2]; norm_num⟩

/-- 4th known unitary perfect number: `87360 = 2^6 * 3 * 5 * 7 * 13`. -/
theorem isUnitaryPerfect_87360 :
    ∑ d ∈ (Finset.Ico 1 87360).filter (fun d => d ∣ 87360 ∧ Nat.Coprime d (87360 / d)), d =
      87360 ∧ 0 < 87360 := by
  rw [isUnitaryPerfect_iff_prod_eq]
  have h := prod_unitary_of_list (n := 87360) [(2, 6), (3, 1), (5, 1), (7, 1), (13, 1)]
    (by intro pe hpe; simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
        rcases hpe with rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by decide)
    (by norm_num)
  exact ⟨h.1, by rw [h.2.2]; norm_num⟩

/-- 5th known unitary perfect number (Wall 1975):
`146361946186458562560000 = 2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313`. -/
theorem isUnitaryPerfect_146361946186458562560000 :
    ∑ d ∈ (Finset.Ico 1 146361946186458562560000).filter
        (fun d => d ∣ 146361946186458562560000 ∧ Nat.Coprime d (146361946186458562560000 / d)), d =
      146361946186458562560000 ∧ 0 < 146361946186458562560000 := by
  rw [isUnitaryPerfect_iff_prod_eq]
  have h := prod_unitary_of_list (n := 146361946186458562560000)
    [(2, 18), (3, 1), (5, 4), (7, 1), (11, 1), (13, 1),
     (19, 1), (37, 1), (79, 1), (109, 1), (157, 1), (313, 1)]
    (by intro pe hpe; simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
        rcases hpe with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          norm_num)
    (by decide)
    (by norm_num)
  exact ⟨h.1, by rw [h.2.2]; norm_num⟩

end KnownExamples

/-! ## Section 3: Parity & Exact 2-Adic Structural Laws (Subbarao–Warren 1966 + Exact Balance) -/

section ParityAndTwoAdic

private lemma odd_primePow_add_one_even {p e : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    2 ∣ (p ^ e + 1) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpow : Odd (p ^ e) := hodd.pow
  rcases hpow with ⟨k, hk⟩
  exact ⟨k + 1, by omega⟩

private lemma two_pow_add_one_odd {a : ℕ} (ha : 1 ≤ a) : Odd (2 ^ a + 1) := by
  have hdvd : 2 ∣ 2 ^ a := dvd_pow_self 2 (by omega)
  rcases hdvd with ⟨k, hk⟩
  exact ⟨k, by omega⟩

/-- Subbarao–Warren (1966): Every unitary perfect number is even (no odd unitary perfect numbers
exist). -/
theorem even_of_isUnitaryPerfect (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) :
    Even n := by
  rw [isUnitaryPerfect_iff_prod_eq] at hn
  rcases hn with ⟨hpos, hprod⟩
  by_contra hnot
  have hodd : Odd n := Nat.not_even_iff_odd.mp hnot
  have h2not : 2 ∉ n.primeFactors := by
    intro h2
    have h2dvd : 2 ∣ n := Nat.dvd_of_mem_primeFactors h2
    exact hnot (even_iff_two_dvd.mpr h2dvd)
  have hcard_le : n.primeFactors.card ≤ 1 := by
    by_contra hgt
    have hge2 : 2 ≤ n.primeFactors.card := by omega
    have h4dvd : 2 ^ n.primeFactors.card ∣ ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) := by
      have hconst : 2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by
        rw [Finset.prod_const]
      rw [hconst]
      refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp2 : p ≠ 2 := fun h => h2not (h ▸ hp)
      exact odd_primePow_add_one_even hp_prime hp2
    rw [hprod] at h4dvd
    have h4 : 4 ∣ 2 * n := dvd_trans (pow_dvd_pow 2 hge2) h4dvd
    rcases h4 with ⟨k, hk⟩
    rcases hodd with ⟨m, hm⟩
    omega
  have hcard_ne0 : n.primeFactors.card ≠ 0 := by
    intro h0
    have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp h0
    rw [hempty, Finset.prod_empty] at hprod
    omega
  have hcard1 : n.primeFactors.card = 1 := by omega
  rcases Finset.card_eq_one.mp hcard1 with ⟨p, hp⟩
  have hself : ∏ q ∈ n.primeFactors, q ^ n.factorization q = n := by
    simpa [Finsupp.prod, Nat.support_factorization] using
      Nat.prod_factorization_pow_eq_self (Nat.ne_of_gt hpos)
  have hp_mem : p ∈ n.primeFactors := hp.symm ▸ Finset.mem_singleton_self p
  have hp_prime := Nat.prime_of_mem_primeFactors hp_mem
  have he_pos : 1 ≤ n.factorization p :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ hp_mem))
  have hge2 : 2 ≤ p ^ n.factorization p := le_trans hp_prime.two_le (Nat.le_self_pow (by omega) p)
  rw [hp, Finset.prod_singleton] at hprod hself
  omega

/-- Every unitary perfect number has `2 ∈ n.primeFactors` and `1 ≤ n.factorization 2`. -/
theorem one_le_v2_of_isUnitaryPerfect (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) :
    1 ≤ n.factorization 2 := by
  have heven := even_of_isUnitaryPerfect n hn
  have h2dvd : 2 ∣ n := even_iff_two_dvd.mp heven
  have h2mem : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2dvd, Nat.ne_of_gt hn.2⟩
  exact Nat.pos_of_ne_zero
    (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ h2mem))

/-- Exact 2-adic valuation balance for unitary perfect numbers:
`∑_{p ∈ n.primeFactors.erase 2} v_2(p^(v_p(n)) + 1) = v_2(n) + 1`. -/
theorem sum_v2_odd_components_eq (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) :
    ∑ p ∈ n.primeFactors.erase 2, (p ^ n.factorization p + 1).factorization 2 =
      n.factorization 2 + 1 := by
  have hv2_ge := one_le_v2_of_isUnitaryPerfect n hn
  rw [isUnitaryPerfect_iff_prod_eq] at hn
  rcases hn with ⟨hpos, hprod⟩
  have hn0 : n ≠ 0 := Nat.ne_of_gt hpos
  have h2mem : 2 ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega
  have hsplit : (2 ^ n.factorization 2 + 1) *
      ∏ p ∈ n.primeFactors.erase 2, (p ^ n.factorization p + 1) = 2 * n := by
    rw [← hprod]
    exact Finset.mul_prod_erase n.primeFactors (fun p => p ^ n.factorization p + 1) h2mem
  have hleft_ne : (2 ^ n.factorization 2 + 1) ≠ 0 := by positivity
  have hright_ne : (∏ p ∈ n.primeFactors.erase 2, (p ^ n.factorization p + 1)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p _ => by positivity
  have hfac_eq := congrArg (fun m => m.factorization 2) hsplit
  rw [Nat.factorization_mul hleft_ne hright_ne, Finsupp.add_apply,
      Nat.factorization_mul (by norm_num) hn0, Finsupp.add_apply] at hfac_eq
  have h2_odd : (2 ^ n.factorization 2 + 1).factorization 2 = 0 := by
    refine Nat.factorization_eq_zero_of_not_dvd ?_
    intro hd
    rcases two_pow_add_one_odd hv2_ge with ⟨k, hk⟩
    rcases hd with ⟨m, hm⟩
    omega
  have h2_two : (2 : ℕ).factorization 2 = 1 := by
    rw [Nat.Prime.factorization_self Nat.prime_two]
  have hprod_fac : (∏ p ∈ n.primeFactors.erase 2, (p ^ n.factorization p + 1)).factorization 2 =
      ∑ p ∈ n.primeFactors.erase 2, (p ^ n.factorization p + 1).factorization 2 := by
    rw [Nat.factorization_prod (fun p _ => by positivity), Finsupp.finsetSum_apply]
  rw [h2_odd, zero_add, hprod_fac, h2_two] at hfac_eq
  omega

/-- Sharp component-count bound: for every unitary perfect number `n`,
`ω(n) ≤ v_2(n) + 2` (equivalently `v_2(n) ≥ ω(n) - 2`). -/
theorem omega_le_v2_add_two (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) :
    n.primeFactors.card ≤ n.factorization 2 + 2 := by
  have hv2_ge := one_le_v2_of_isUnitaryPerfect n hn
  have hbal := sum_v2_odd_components_eq n hn
  have h2mem : 2 ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega
  have hcard_le : (n.primeFactors.erase 2).card ≤
      ∑ p ∈ n.primeFactors.erase 2, (p ^ n.factorization p + 1).factorization 2 := by
    calc
      (n.primeFactors.erase 2).card
          = ∑ _p ∈ n.primeFactors.erase 2, 1 := by simp
      _ ≤ ∑ p ∈ n.primeFactors.erase 2, (p ^ n.factorization p + 1).factorization 2 := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp_ne2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
            have hp_prime : Nat.Prime p :=
              Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hp).2
            have hd2 : 2 ∣ (p ^ n.factorization p + 1) := odd_primePow_add_one_even hp_prime hp_ne2
            have hmem2 : 2 ∈ (p ^ n.factorization p + 1).primeFactors :=
              Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd2, by positivity⟩
            exact Nat.pos_of_ne_zero
              (Finsupp.mem_support_iff.mp ((Nat.support_factorization _).symm ▸ hmem2))
  have hcard_erase : (n.primeFactors.erase 2).card + 1 = n.primeFactors.card :=
    Finset.card_erase_add_one h2mem
  omega

/-- Seed divisibility law: for every unitary perfect number `n`,
`2^(v_2(n)) + 1` divides the odd part `n / 2^(v_2(n))`, and consequently `2^(2 * v_2(n)) < n`. -/
theorem two_pow_add_one_dvd_odd_part (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) :
    (2 ^ n.factorization 2 + 1) ∣ (n / 2 ^ n.factorization 2) ∧
      2 ^ (2 * n.factorization 2) < n := by
  have hv2_ge := one_le_v2_of_isUnitaryPerfect n hn
  rw [isUnitaryPerfect_iff_prod_eq] at hn
  rcases hn with ⟨hpos, hprod⟩
  have h2mem : 2 ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega
  have hsplit : (2 ^ n.factorization 2 + 1) *
      ∏ p ∈ n.primeFactors.erase 2, (p ^ n.factorization p + 1) = 2 * n := by
    rw [← hprod]
    exact Finset.mul_prod_erase n.primeFactors (fun p => p ^ n.factorization p + 1) h2mem
  have hdvd_pow : 2 ^ n.factorization 2 ∣ n := Nat.ordProj_dvd n 2
  have hmul_odd : 2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) = n :=
    Nat.mul_div_cancel' hdvd_pow
  have h2n_eq : 2 * n = 2 ^ (n.factorization 2 + 1) * (n / 2 ^ n.factorization 2) := by
    rw [pow_succ', mul_assoc, hmul_odd]
  have hdvd_2n : (2 ^ n.factorization 2 + 1) ∣ 2 ^ (n.factorization 2 + 1) * (n / 2 ^ n.factorization 2) := by
    rw [← h2n_eq]
    exact ⟨_, hsplit.symm⟩
  have hcop : Nat.Coprime (2 ^ n.factorization 2 + 1) (2 ^ (n.factorization 2 + 1)) := by
    refine Nat.Coprime.pow_right _ ?_
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro hd
    rcases two_pow_add_one_odd hv2_ge with ⟨k, hk⟩
    rcases hd with ⟨m, hm⟩
    omega
  have hdvd_odd : (2 ^ n.factorization 2 + 1) ∣ (n / 2 ^ n.factorization 2) :=
    hcop.dvd_of_dvd_mul_left hdvd_2n
  have hodd_pos : 0 < n / 2 ^ n.factorization 2 := by
    by_contra h0
    have hz : n / 2 ^ n.factorization 2 = 0 := Nat.eq_zero_of_not_pos h0
    rw [hz, mul_zero] at hmul_odd
    exact absurd hmul_odd.symm (Nat.ne_of_gt hpos)
  have hle_odd : 2 ^ n.factorization 2 + 1 ≤ n / 2 ^ n.factorization 2 :=
    Nat.le_of_dvd hodd_pos hdvd_odd
  refine ⟨hdvd_odd, ?_⟩
  calc
    2 ^ (2 * n.factorization 2)
        = 2 ^ n.factorization 2 * 2 ^ n.factorization 2 := by rw [two_mul, pow_add]
    _ < 2 ^ n.factorization 2 * (2 ^ n.factorization 2 + 1) := by
          exact Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self _) (by positivity)
    _ ≤ 2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) :=
          Nat.mul_le_mul_left _ hle_odd
    _ = n := hmul_odd

/-- If `v_2(n)` is odd, then `3 ∣ n` (since `3 ∣ 2^(2m+1) + 1 ∣ n / 2^(v_2(n))`). -/
theorem three_dvd_of_odd_v2 (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n)
    (hodd : Odd (n.factorization 2)) : 3 ∣ n := by
  have hdvd := (two_pow_add_one_dvd_odd_part n hn).1
  rcases hodd with ⟨m, hm⟩
  have hpow : ∀ k : ℕ, 2 ^ (2 * k + 1) % 3 = 2 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have : 2 ^ (2 * (k + 1) + 1) = 4 * 2 ^ (2 * k + 1) := by ring
      rw [this, Nat.mul_mod, ih]
  have h3dvd : 3 ∣ (2 ^ n.factorization 2 + 1) := by
    rw [hm]
    refine Nat.dvd_of_mod_eq_zero ?_
    rw [Nat.add_mod, hpow m]
  exact dvd_trans (dvd_trans h3dvd hdvd) (Nat.div_dvd_of_dvd (Nat.ordProj_dvd n 2))

/-- If `v_2(n) ≡ 3 (mod 6)`, then `9 ∣ n` (since `9 ∣ 2^(6m+3) + 1 ∣ n / 2^(v_2(n))`). -/
theorem nine_dvd_of_v2_mod_six_eq_three (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n)
    (hmod : n.factorization 2 % 6 = 3) : 9 ∣ n := by
  have hdvd := (two_pow_add_one_dvd_odd_part n hn).1
  have hm : n.factorization 2 = 6 * (n.factorization 2 / 6) + 3 := by omega
  have h9dvd : 9 ∣ (2 ^ n.factorization 2 + 1) := by
    rw [hm]
    set k := n.factorization 2 / 6
    have hpow : 2 ^ (6 * k + 3) % 9 = 8 := by
      induction k with
      | zero => norm_num
      | succ k ih =>
        have : 2 ^ (6 * (k + 1) + 3) = 64 * 2 ^ (6 * k + 3) := by ring
        rw [this, Nat.mul_mod, ih]
    exact Nat.dvd_of_mod_eq_zero (by omega)
  exact dvd_trans (dvd_trans h9dvd hdvd) (Nat.div_dvd_of_dvd (Nat.ordProj_dvd n 2))

end ParityAndTwoAdic

/-! ## Section 4: Elementary Cook Majorization & Nielsen (2003) Lemma 1 -/

section MajorizationAndNielsen

/-- Elementary 1-variable concavity bound (proved purely from `Real.log_le_sub_one_of_pos`):
for all real `x > 1` and `y > 1`,
`log (1 - 1 / x) - log (1 - 1 / y) ≥ (1 / (x - 1)) * (log x - log y)`. -/
private lemma log_one_sub_inv_sub_ge {x y : ℝ} (hx : 1 < x) (hy : 1 < y) :
    (1 / (x - 1)) * (Real.log x - Real.log y) ≤
      Real.log (1 - 1 / x) - Real.log (1 - 1 / y) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hxm1 : 0 < x - 1 := by linarith
  have hym1 : 0 < y - 1 := by linarith
  have h1x : 0 < 1 - 1 / x := by
    rw [sub_pos, div_lt_one hx0]
    exact hx
  have h1y : 0 < 1 - 1 / y := by
    rw [sub_pos, div_lt_one hy0]
    exact hy
  have hstep1 : Real.log ((1 - 1 / y) / (1 - 1 / x)) ≤ (1 - 1 / y) / (1 - 1 / x) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos h1y h1x)
  rw [Real.log_div (ne_of_gt h1y) (ne_of_gt h1x)] at hstep1
  have halg : (1 - 1 / y) / (1 - 1 / x) - 1 = (1 / (x - 1)) * (1 - x / y) := by
    field_simp [ne_of_gt hx0, ne_of_gt hy0, ne_of_gt hxm1]
    ring
  rw [halg] at hstep1
  have hstep2 : Real.log (x / y) ≤ x / y - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
  rw [Real.log_div (ne_of_gt hx0) (ne_of_gt hy0)] at hstep2
  have hstep3 : (1 / (x - 1)) * (1 - x / y) ≤ (1 / (x - 1)) * (Real.log y - Real.log x) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  linarith

/-- Discrete Abel summation (summation by parts) on `Finset.range r`. -/
private lemma abel_sum_nonneg_pos (r : ℕ) (hr : 1 ≤ r) (w d : ℕ → ℝ)
    (hw_pos : ∀ i < r, 0 < w i)
    (hw_anti : ∀ i, i + 1 < r → w (i + 1) ≤ w i)
    (hS_nonneg : ∀ u ≤ r, 0 ≤ ∑ i ∈ Finset.range u, d i)
    (hS_pos : 0 < ∑ i ∈ Finset.range r, d i) :
    0 < ∑ i ∈ Finset.range r, w i * d i := by
  have hpart : ∀ m, 1 ≤ m → m ≤ r →
      ∑ i ∈ Finset.range m, w i * d i =
        w (m - 1) * (∑ i ∈ Finset.range m, d i) +
          ∑ u ∈ Finset.range (m - 1), (w u - w (u + 1)) * (∑ i ∈ Finset.range (u + 1), d i) := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      intro hmr
      cases m with
      | zero => simp
      | succ m =>
        have ih' := ih (by omega) (by omega)
        rw [Finset.sum_range_succ, ih']
        have hsplit : ∑ i ∈ Finset.range (m + 2), d i =
            (∑ i ∈ Finset.range (m + 1), d i) + d (m + 1) := Finset.sum_range_succ d (m + 1)
        have hrange : ∑ u ∈ Finset.range (m + 1),
              (w u - w (u + 1)) * (∑ i ∈ Finset.range (u + 1), d i) =
            (∑ u ∈ Finset.range m, (w u - w (u + 1)) * (∑ i ∈ Finset.range (u + 1), d i)) +
              (w m - w (m + 1)) * (∑ i ∈ Finset.range (m + 1), d i) :=
          Finset.sum_range_succ _ m
        simp only [Nat.add_sub_cancel] at ih' ⊢
        rw [hsplit, hrange]
        ring
  rw [hpart r hr (le_refl r)]
  have h1 : 0 < w (r - 1) * (∑ i ∈ Finset.range r, d i) :=
    mul_pos (hw_pos (r - 1) (by omega)) hS_pos
  have h2 : 0 ≤ ∑ u ∈ Finset.range (r - 1),
      (w u - w (u + 1)) * (∑ i ∈ Finset.range (u + 1), d i) := by
    refine Finset.sum_nonneg fun u hu => ?_
    rw [Finset.mem_range] at hu
    apply mul_nonneg
    · linarith [hw_anti u (by omega)]
    · exact hS_nonneg (u + 1) (by omega)
  linarith

/-- Cook's Majorization Lemma (proved purely via `Real.log_le_sub_one_of_pos` and Abel summation):
if `x` is monotone on `0..r-1`, `x_i, y_i ≥ 2`, `∏_{i<u} y_i ≤ ∏_{i<u} x_i` for all `u ≤ r`,
and `∏_{i<r} y_i < ∏_{i<r} x_i`, then `∏_{i<r} (1 - 1/y_i) < ∏_{i<r} (1 - 1/x_i)`. -/
private lemma cook_majorization (r : ℕ) (hr : 1 ≤ r) (x y : ℕ → ℕ)
    (hx_mono : ∀ i j, i ≤ j → j < r → x i ≤ x j)
    (hx_ge : ∀ i < r, 2 ≤ x i) (hy_ge : ∀ i < r, 2 ≤ y i)
    (hpref : ∀ u ≤ r, ∏ i ∈ Finset.range u, y i ≤ ∏ i ∈ Finset.range u, x i)
    (hstrict : ∏ i ∈ Finset.range r, y i < ∏ i ∈ Finset.range r, x i) :
    ∏ i ∈ Finset.range r, (1 - 1 / (y i : ℝ)) <
      ∏ i ∈ Finset.range r, (1 - 1 / (x i : ℝ)) := by
  have hx_gt1 : ∀ i < r, (1 : ℝ) < (x i : ℝ) := fun i hi => by
    have := hx_ge i hi
    exact_mod_cast (by omega : 1 < x i)
  have hy_gt1 : ∀ i < r, (1 : ℝ) < (y i : ℝ) := fun i hi => by
    have := hy_ge i hi
    exact_mod_cast (by omega : 1 < y i)
  have h1x_pos : ∀ i < r, (0 : ℝ) < 1 - 1 / (x i : ℝ) := fun i hi => by
    rw [sub_pos, div_lt_one (by linarith [hx_gt1 i hi])]
    exact hx_gt1 i hi
  have h1y_pos : ∀ i < r, (0 : ℝ) < 1 - 1 / (y i : ℝ) := fun i hi => by
    rw [sub_pos, div_lt_one (by linarith [hy_gt1 i hi])]
    exact hy_gt1 i hi
  have hPx_pos : 0 < ∏ i ∈ Finset.range r, (1 - 1 / (x i : ℝ)) :=
    Finset.prod_pos fun i hi => h1x_pos i (Finset.mem_range.mp hi)
  have hPy_pos : 0 < ∏ i ∈ Finset.range r, (1 - 1 / (y i : ℝ)) :=
    Finset.prod_pos fun i hi => h1y_pos i (Finset.mem_range.mp hi)
  rw [← Real.log_lt_log_iff hPy_pos hPx_pos]
  rw [Real.log_prod (fun i hi => ne_of_gt (h1y_pos i (Finset.mem_range.mp hi))),
      Real.log_prod (fun i hi => ne_of_gt (h1x_pos i (Finset.mem_range.mp hi)))]
  have hsum_log : ∀ u ≤ r,
      ∑ i ∈ Finset.range u, (Real.log (x i : ℝ) - Real.log (y i : ℝ)) =
        Real.log ((∏ i ∈ Finset.range u, x i : ℕ) : ℝ) -
          Real.log ((∏ i ∈ Finset.range u, y i : ℕ) : ℝ) := by
    intro u hu
    rw [Finset.sum_sub_distrib]
    have hx_ne : ∀ i ∈ Finset.range u, (x i : ℝ) ≠ 0 := fun i hi =>
      ne_of_gt (by linarith [hx_gt1 i (lt_of_lt_of_le (Finset.mem_range.mp hi) hu)])
    have hy_ne : ∀ i ∈ Finset.range u, (y i : ℝ) ≠ 0 := fun i hi =>
      ne_of_gt (by linarith [hy_gt1 i (lt_of_lt_of_le (Finset.mem_range.mp hi) hu)])
    push_cast
    rw [Real.log_prod hx_ne, Real.log_prod hy_ne]
  have habel : 0 < ∑ i ∈ Finset.range r,
      (1 / ((x i : ℝ) - 1)) * (Real.log (x i : ℝ) - Real.log (y i : ℝ)) := by
    refine abel_sum_nonneg_pos r hr (fun i => 1 / ((x i : ℝ) - 1))
      (fun i => Real.log (x i : ℝ) - Real.log (y i : ℝ)) ?_ ?_ ?_ ?_
    · intro i hi
      have := hx_gt1 i hi
      positivity
    · intro i hi
      have hle : (x i : ℝ) ≤ (x (i + 1) : ℝ) := by
        exact_mod_cast hx_mono i (i + 1) (Nat.le_succ i) hi
      have hpos1 : (0 : ℝ) < (x i : ℝ) - 1 := by linarith [hx_gt1 i (by omega)]
      exact one_div_le_one_div_of_le hpos1 (by linarith)
    · intro u hu
      rw [hsum_log u hu, sub_nonneg]
      have hy_prod_pos : (0 : ℝ) < ((∏ i ∈ Finset.range u, y i : ℕ) : ℝ) := by
        exact_mod_cast Finset.prod_pos fun i hi =>
          lt_of_lt_of_le (by omega : 0 < 2) (hy_ge i (lt_of_lt_of_le (Finset.mem_range.mp hi) hu))
      apply Real.log_le_log hy_prod_pos
      exact_mod_cast hpref u hu
    · rw [hsum_log r (le_refl r), sub_pos]
      have hy_prod_pos : (0 : ℝ) < ((∏ i ∈ Finset.range r, y i : ℕ) : ℝ) := by
        exact_mod_cast Finset.prod_pos fun i hi =>
          lt_of_lt_of_le (by omega : 0 < 2) (hy_ge i (Finset.mem_range.mp hi))
      apply Real.log_lt_log hy_prod_pos
      exact_mod_cast hstrict
  have hcomp :
      ∑ i ∈ Finset.range r, (1 / ((x i : ℝ) - 1)) * (Real.log (x i : ℝ) - Real.log (y i : ℝ)) ≤
        ∑ i ∈ Finset.range r, (Real.log (1 - 1 / (x i : ℝ)) - Real.log (1 - 1 / (y i : ℝ))) := by
    refine Finset.sum_le_sum fun i hi => ?_
    exact log_one_sub_inv_sub_ge (hx_gt1 i (Finset.mem_range.mp hi))
      (hy_gt1 i (Finset.mem_range.mp hi))
  rw [Finset.sum_sub_distrib] at hcomp
  linarith

/-- Exact geometric-product identity for the Sylvester–Fermat comparison sequence:
`a * ∏_{i < u} ((a + 1)^(2^i) + 1) = (a + 1)^(2^u) - 1` (for `a ≥ 1`). -/
private lemma sylvester_prefix_prod (a u : ℕ) :
    a * (∏ i ∈ Finset.range u, ((a + 1) ^ (2 ^ i) + 1)) + 1 = (a + 1) ^ (2 ^ u) := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, pow_succ, pow_mul]
    have h1 : a * (∏ i ∈ Finset.range u, ((a + 1) ^ (2 ^ i) + 1)) = (a + 1) ^ (2 ^ u) - 1 := by
      omega
    have hge1 : 1 ≤ (a + 1) ^ (2 ^ u) := Nat.one_le_pow _ _ (by omega)
    set M := (a + 1) ^ (2 ^ u)
    zify [hge1] at h1 ⊢
    rw [h1]
    ring

/-- Exact sum of powers of 2: `∑_{i < u} 2^i + 1 = 2^u`. -/
private lemma sum_two_pow_range (u : ℕ) : (∑ i ∈ Finset.range u, 2 ^ i) + 1 = 2 ^ u := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- Exact product of `(1 - 1/n_i)` for the Sylvester–Fermat sequence:
`n_i = (a + 1)^(2^i) + 1` (`i < r - 1`), `n_{r-1} = (a + 1)^(2^(r-1))`. -/
private lemma sylvester_one_sub_inv_prod (a r : ℕ) (ha : 1 ≤ a) (hr : 1 ≤ r) :
    let n : ℕ → ℕ := fun i => if i < r - 1 then (a + 1) ^ (2 ^ i) + 1 else (a + 1) ^ (2 ^ (r - 1))
    ∏ i ∈ Finset.range r, (1 - 1 / (n i : ℝ)) = (a : ℝ) / ((a + 1 : ℕ) : ℝ) := by
  intro n
  have hterm : ∀ i < r, (1 : ℝ) - 1 / (n i : ℝ) = ((n i - 1 : ℕ) : ℝ) / (n i : ℝ) := by
    intro i hi
    have hni_ge : 2 ≤ n i := by
      dsimp only [n]
      split_ifs
      · have : 1 ≤ (a + 1) ^ (2 ^ i) := Nat.one_le_pow _ _ (by omega)
        omega
      · calc
          2 ≤ a + 1 := by omega
          _ = (a + 1) ^ 1 := (pow_one _).symm
          _ ≤ (a + 1) ^ (2 ^ (r - 1)) := Nat.pow_le_pow_right (by omega) (Nat.one_le_pow _ _ (by omega))
    have hni_pos : (0 : ℝ) < (n i : ℝ) := by exact_mod_cast (by omega : 0 < n i)
    rw [Nat.cast_sub (by omega : 1 ≤ n i), Nat.cast_one]
    field_simp [ne_of_gt hni_pos]
  rw [Finset.prod_congr rfl (fun i hi => hterm i (Finset.mem_range.mp hi)), Finset.prod_div_distrib]
  have hsplit_num : ∏ i ∈ Finset.range r, ((n i - 1 : ℕ) : ℝ) =
      (∏ i ∈ Finset.range (r - 1), (((a + 1) ^ (2 ^ i) : ℕ) : ℝ)) *
        (((a + 1) ^ (2 ^ (r - 1)) - 1 : ℕ) : ℝ) := by
    have hr' : r = (r - 1) + 1 := by omega
    conv_lhs => rw [hr', Finset.prod_range_succ]
    have hpre : ∏ i ∈ Finset.range (r - 1), ((n i - 1 : ℕ) : ℝ) =
        ∏ i ∈ Finset.range (r - 1), (((a + 1) ^ (2 ^ i) : ℕ) : ℝ) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hilt : i < r - 1 := Finset.mem_range.mp hi
      simp [n, hilt]
    have hlast : n (r - 1) - 1 = (a + 1) ^ (2 ^ (r - 1)) - 1 := by simp [n]
    rw [hpre, hlast]
  have hsplit_den : ∏ i ∈ Finset.range r, (n i : ℝ) =
      (∏ i ∈ Finset.range (r - 1), (((a + 1) ^ (2 ^ i) + 1 : ℕ) : ℝ)) *
        (((a + 1) ^ (2 ^ (r - 1)) : ℕ) : ℝ) := by
    have hr' : r = (r - 1) + 1 := by omega
    conv_lhs => rw [hr', Finset.prod_range_succ]
    have hpre : ∏ i ∈ Finset.range (r - 1), (n i : ℝ) =
        ∏ i ∈ Finset.range (r - 1), (((a + 1) ^ (2 ^ i) + 1 : ℕ) : ℝ) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hilt : i < r - 1 := Finset.mem_range.mp hi
      simp [n, hilt]
    have hlast : n (r - 1) = (a + 1) ^ (2 ^ (r - 1)) := by simp [n]
    rw [hpre, hlast]
  rw [hsplit_num, hsplit_den]
  have hnum_pow : ∏ i ∈ Finset.range (r - 1), (((a + 1) ^ (2 ^ i) : ℕ) : ℝ) =
      ((a + 1 : ℕ) : ℝ) ^ (∑ i ∈ Finset.range (r - 1), 2 ^ i) := by
    simp only [Nat.cast_pow]
    rw [Finset.prod_pow_eq_pow_sum]
  have hden_id : (a : ℝ) * (∏ i ∈ Finset.range (r - 1), (((a + 1) ^ (2 ^ i) + 1 : ℕ) : ℝ)) =
      (((a + 1) ^ (2 ^ (r - 1)) - 1 : ℕ) : ℝ) := by
    have hnat := sylvester_prefix_prod a (r - 1)
    have hge1 : 1 ≤ (a + 1) ^ (2 ^ (r - 1)) := Nat.one_le_pow _ _ (by omega)
    have hsub : a * (∏ i ∈ Finset.range (r - 1), ((a + 1) ^ (2 ^ i) + 1)) =
        (a + 1) ^ (2 ^ (r - 1)) - 1 := by omega
    have hcast : ((a * (∏ i ∈ Finset.range (r - 1), ((a + 1) ^ (2 ^ i) + 1)) : ℕ) : ℝ) =
        (((a + 1) ^ (2 ^ (r - 1)) - 1 : ℕ) : ℝ) := by exact_mod_cast hsub
    simpa [Nat.cast_mul, Nat.cast_prod] using hcast
  have hpow_split : (((a + 1) ^ (2 ^ (r - 1)) : ℕ) : ℝ) =
      ((a + 1 : ℕ) : ℝ) ^ (∑ i ∈ Finset.range (r - 1), 2 ^ i) * ((a + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, ← pow_succ, sum_two_pow_range (r - 1)]
  have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have ha1_pos : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < a + 1)
  have hM_pos : (0 : ℝ) < (((a + 1) ^ (2 ^ (r - 1)) - 1 : ℕ) : ℝ) := by
    have : 2 ≤ (a + 1) ^ (2 ^ (r - 1)) := by
      calc
        2 ≤ a + 1 := by omega
        _ = (a + 1) ^ 1 := (pow_one _).symm
        _ ≤ (a + 1) ^ (2 ^ (r - 1)) :=
          Nat.pow_le_pow_right (by omega) (Nat.one_le_pow _ _ (by omega))
    exact_mod_cast (by omega : 0 < (a + 1) ^ (2 ^ (r - 1)) - 1)
  have hP_pos : (0 : ℝ) < ∏ i ∈ Finset.range (r - 1), (((a + 1) ^ (2 ^ i) + 1 : ℕ) : ℝ) :=
    Finset.prod_pos fun i _ => by positivity
  have hpow_pos : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) ^ (∑ i ∈ Finset.range (r - 1), 2 ^ i) := by
    positivity
  rw [hnum_pow, hpow_split, ← hden_id]
  field_simp [ne_of_gt ha_pos, ne_of_gt ha1_pos, ne_of_gt hP_pos, ne_of_gt hpow_pos]

/-- Nielsen (2003), Lemma 1 (fully self-contained proof):
if `r ≥ 1`, `a, b ≥ 1`, `x : ℕ → ℕ` is monotone on `0..r-1` with `x_i ≥ 2`,
`∏_{i < r} (1 - 1/x_i) ≤ a/b`, and `a/b < ∏_{i < u} (1 - 1/x_i)` for all `u < r`,
then `a * ∏_{i < r} x_i < (a + 1)^(2^r)`. -/
theorem nielsen_product_bound :
    ∀ r : ℕ, 1 ≤ r →
      ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b →
      ∀ (x : ℕ → ℕ),
        (∀ i j, i ≤ j → j < r → x i ≤ x j) →
        (∀ i < r, 2 ≤ x i) →
        (∏ i ∈ Finset.range r, (1 - 1 / (x i : ℝ))) ≤ (a : ℝ) / (b : ℝ) →
        (∀ u < r, (a : ℝ) / (b : ℝ) < ∏ i ∈ Finset.range u, (1 - 1 / (x i : ℝ))) →
        a * (∏ i ∈ Finset.range r, x i) < (a + 1) ^ (2 ^ r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr a b ha hb x hx_mono hx_ge hle hgt
    have hab : a < b := by
      have h0 := hgt 0 (by omega)
      simp only [Finset.range_zero, Finset.prod_empty] at h0
      have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
      have hlt : (a : ℝ) < (b : ℝ) := (div_lt_one hb_pos).mp h0
      exact_mod_cast hlt
    by_cases hr1 : r = 1
    · subst hr1
      simp only [Finset.range_one, Finset.prod_singleton, pow_one] at hle ⊢
      have hx0 : 2 ≤ x 0 := hx_ge 0 (by omega)
      have hx0_pos : (0 : ℝ) < (x 0 : ℝ) := by exact_mod_cast (by omega : 0 < x 0)
      have hb_ge : a + 1 ≤ b := by omega
      have hfrac : (a : ℝ) / (b : ℝ) ≤ (a : ℝ) / ((a + 1 : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact_mod_cast hb_ge
      have h1 : (1 : ℝ) - 1 / (x 0 : ℝ) ≤ 1 - 1 / ((a + 1 : ℕ) : ℝ) := by
        have hrew : (a : ℝ) / ((a + 1 : ℕ) : ℝ) = 1 - 1 / ((a + 1 : ℕ) : ℝ) := by
          have ha1 : ((a + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          push_cast
          field_simp [ha1]
          ring
        linarith
      have hinv : 1 / ((a + 1 : ℕ) : ℝ) ≤ 1 / (x 0 : ℝ) := by linarith
      have hx_le : (x 0 : ℝ) ≤ ((a + 1 : ℕ) : ℝ) :=
        (one_div_le_one_div (by positivity) hx0_pos).mp hinv
      have hx_le_nat : x 0 ≤ a + 1 := by exact_mod_cast hx_le
      calc
        a * x 0 ≤ a * (a + 1) := Nat.mul_le_mul_left a hx_le_nat
        _ < (a + 1) * (a + 1) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        _ = (a + 1) ^ 2 := by ring
    · have hr2 : 2 ≤ r := by omega
      let n : ℕ → ℕ := fun i =>
        if i < r - 1 then (a + 1) ^ (2 ^ i) + 1 else (a + 1) ^ (2 ^ (r - 1))
      by_contra hcontra
      push Not at hcontra
      by_cases hex : ∃ u, 1 ≤ u ∧ u < r ∧
          ∏ i ∈ Finset.range u, x i ≤ ∏ i ∈ Finset.range u, n i
      · rcases hex with ⟨u, hu1, hur, hxu⟩
        have hn_pref : ∏ i ∈ Finset.range u, n i =
            ∏ i ∈ Finset.range u, ((a + 1) ^ (2 ^ i) + 1) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have hilt : i < r - 1 := by
            have := Finset.mem_range.mp hi
            omega
          simp [n, hilt]
        rw [hn_pref] at hxu
        set a' := a * (∏ i ∈ Finset.range u, x i)
        set b' := b * (∏ i ∈ Finset.range u, (x i - 1))
        have ha'_le : a' + 1 ≤ (a + 1) ^ (2 ^ u) := by
          have h1 := sylvester_prefix_prod a u
          have h2 : a' ≤ a * (∏ i ∈ Finset.range u, ((a + 1) ^ (2 ^ i) + 1)) :=
            Nat.mul_le_mul_left a hxu
          omega
        have ha'_pos : 1 ≤ a' := by
          apply Nat.mul_pos ha
          exact Finset.prod_pos fun i hi =>
            lt_of_lt_of_le (by omega : 0 < 2) (hx_ge i (by have := Finset.mem_range.mp hi; omega))
        have hb'_pos : 1 ≤ b' := by
          apply Nat.mul_pos hb
          exact Finset.prod_pos fun i hi => by
            have := hx_ge i (by have := Finset.mem_range.mp hi; omega)
            omega
        have hpref_prod :
            ∏ i ∈ Finset.range u, (1 - 1 / (x i : ℝ)) =
              ((∏ i ∈ Finset.range u, (x i - 1) : ℕ) : ℝ) /
                ((∏ i ∈ Finset.range u, x i : ℕ) : ℝ) := by
          push_cast
          rw [← Finset.prod_div_distrib]
          refine Finset.prod_congr rfl fun i hi => ?_
          have hxi := hx_ge i (by have := Finset.mem_range.mp hi; omega)
          have hxi_pos : (0 : ℝ) < (x i : ℝ) := by exact_mod_cast (by omega : 0 < x i)
          rw [Nat.cast_sub (by omega : 1 ≤ x i), Nat.cast_one]
          field_simp [ne_of_gt hxi_pos]
        have hpref_pos : 0 < ∏ i ∈ Finset.range u, (1 - 1 / (x i : ℝ)) := by
          refine Finset.prod_pos fun i hi => ?_
          have hxi := hx_ge i (by have := Finset.mem_range.mp hi; omega)
          have hxi_gt1 : (1 : ℝ) < (x i : ℝ) := by exact_mod_cast (by omega : 1 < x i)
          rw [sub_pos, div_lt_one (by linarith)]
          exact hxi_gt1
        have hratio : (a' : ℝ) / (b' : ℝ) =
            ((a : ℝ) / (b : ℝ)) / (∏ i ∈ Finset.range u, (1 - 1 / (x i : ℝ))) := by
          rw [hpref_prod]
          have h1 : ((∏ i ∈ Finset.range u, x i : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt (Finset.prod_pos fun i hi =>
              lt_of_lt_of_le (by omega : 0 < 2) (hx_ge i (by have := Finset.mem_range.mp hi; omega)))
          have h2 : ((∏ i ∈ Finset.range u, (x i - 1) : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt (Finset.prod_pos fun i hi => by
              have := hx_ge i (by have := Finset.mem_range.mp hi; omega); omega)
          have hb_ne : (b : ℝ) ≠ 0 := by positivity
          dsimp only [a', b']
          push_cast
          field_simp [h1, h2, hb_ne]
        have hsplit_all : ∀ m, m ≤ r - u →
            ∏ i ∈ Finset.range (u + m), (1 - 1 / (x i : ℝ)) =
              (∏ i ∈ Finset.range u, (1 - 1 / (x i : ℝ))) *
                ∏ j ∈ Finset.range m, (1 - 1 / (x (u + j) : ℝ)) := by
          intro m _
          rw [Finset.prod_range_add]
        have hle_tail : ∏ j ∈ Finset.range (r - u), (1 - 1 / (x (u + j) : ℝ)) ≤
            (a' : ℝ) / (b' : ℝ) := by
          rw [hratio, le_div_iff₀ hpref_pos, mul_comm]
          have h := hsplit_all (r - u) (le_refl _)
          have hur_eq : u + (r - u) = r := by omega
          rw [hur_eq] at h
          linarith
        have hgt_tail : ∀ v < r - u,
            (a' : ℝ) / (b' : ℝ) < ∏ j ∈ Finset.range v, (1 - 1 / (x (u + j) : ℝ)) := by
          intro v hv
          rw [hratio, div_lt_iff₀ hpref_pos, mul_comm]
          have h := hsplit_all v (by omega)
          rw [← h]
          exact hgt (u + v) (by omega)
        have hih := ih (r - u) (by omega) (by omega) a' b' ha'_pos hb'_pos (fun j => x (u + j))
          (fun i j hij hj => hx_mono (u + i) (u + j) (by omega) (by omega))
          (fun j hj => hx_ge (u + j) (by omega))
          hle_tail hgt_tail
        have hprod_split : a * (∏ i ∈ Finset.range r, x i) =
            a' * (∏ j ∈ Finset.range (r - u), x (u + j)) := by
          have hur_eq : u + (r - u) = r := by omega
          conv_lhs => rw [← hur_eq, Finset.prod_range_add]
          dsimp only [a']
          ring
        rw [hprod_split] at hcontra
        have hbound : (a' + 1) ^ (2 ^ (r - u)) ≤ (a + 1) ^ (2 ^ r) := by
          calc
            (a' + 1) ^ (2 ^ (r - u))
                ≤ ((a + 1) ^ (2 ^ u)) ^ (2 ^ (r - u)) := Nat.pow_le_pow_left ha'_le _
            _ = (a + 1) ^ (2 ^ u * 2 ^ (r - u)) := by rw [← pow_mul]
            _ = (a + 1) ^ (2 ^ r) := by
                  rw [← pow_add]
                  have : u + (r - u) = r := by omega
                  rw [this]
        omega
      · push Not at hex
        have hpref_n : ∀ u ≤ r, ∏ i ∈ Finset.range u, n i ≤ ∏ i ∈ Finset.range u, x i := by
          intro u hu
          by_cases hu0 : u = 0
          · subst hu0; simp
          · by_cases hur : u < r
            · exact Nat.le_of_lt (hex u (by omega) hur)
            · have hueq : u = r := by omega
              rw [hueq]
              have hn_all : a * (∏ i ∈ Finset.range r, n i) < (a + 1) ^ (2 ^ r) := by
                have hr' : r = (r - 1) + 1 := by omega
                conv_lhs => rw [hr', Finset.prod_range_succ]
                have hpre : ∏ i ∈ Finset.range (r - 1), n i =
                    ∏ i ∈ Finset.range (r - 1), ((a + 1) ^ (2 ^ i) + 1) := by
                  refine Finset.prod_congr rfl fun i hi => ?_
                  simp [n, Finset.mem_range.mp hi]
                have hlast : n (r - 1) = (a + 1) ^ (2 ^ (r - 1)) := by simp [n]
                rw [hpre, hlast, ← mul_assoc]
                have h1 := sylvester_prefix_prod a (r - 1)
                have hlt : a * (∏ i ∈ Finset.range (r - 1), ((a + 1) ^ (2 ^ i) + 1)) <
                    (a + 1) ^ (2 ^ (r - 1)) := by omega
                calc
                  a * (∏ i ∈ Finset.range (r - 1), ((a + 1) ^ (2 ^ i) + 1)) *
                      (a + 1) ^ (2 ^ (r - 1))
                      < (a + 1) ^ (2 ^ (r - 1)) * (a + 1) ^ (2 ^ (r - 1)) :=
                        Nat.mul_lt_mul_of_pos_right hlt (by positivity)
                  _ = (a + 1) ^ (2 ^ r) := by
                        rw [← pow_add, ← two_mul, ← pow_succ']
                        have : r - 1 + 1 = r := by omega
                        rw [this]
              have hax_gt : a * (∏ i ∈ Finset.range r, n i) < a * (∏ i ∈ Finset.range r, x i) :=
                lt_of_lt_of_le hn_all hcontra
              exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_left hax_gt)
        have hstrict_n : ∏ i ∈ Finset.range r, n i < ∏ i ∈ Finset.range r, x i := by
          have hr' : r = (r - 1) + 1 := by omega
          have hn_all : a * (∏ i ∈ Finset.range r, n i) < (a + 1) ^ (2 ^ r) := by
            conv_lhs => rw [hr', Finset.prod_range_succ]
            have hpre : ∏ i ∈ Finset.range (r - 1), n i =
                ∏ i ∈ Finset.range (r - 1), ((a + 1) ^ (2 ^ i) + 1) := by
              refine Finset.prod_congr rfl fun i hi => ?_
              simp [n, Finset.mem_range.mp hi]
            have hlast : n (r - 1) = (a + 1) ^ (2 ^ (r - 1)) := by simp [n]
            rw [hpre, hlast, ← mul_assoc]
            have h1 := sylvester_prefix_prod a (r - 1)
            have hlt : a * (∏ i ∈ Finset.range (r - 1), ((a + 1) ^ (2 ^ i) + 1)) <
                (a + 1) ^ (2 ^ (r - 1)) := by omega
            calc
              a * (∏ i ∈ Finset.range (r - 1), ((a + 1) ^ (2 ^ i) + 1)) *
                  (a + 1) ^ (2 ^ (r - 1))
                  < (a + 1) ^ (2 ^ (r - 1)) * (a + 1) ^ (2 ^ (r - 1)) :=
                    Nat.mul_lt_mul_of_pos_right hlt (by positivity)
              _ = (a + 1) ^ (2 ^ r) := by
                    rw [← pow_add, ← two_mul, ← pow_succ']
                    have : r - 1 + 1 = r := by omega
                    rw [this]
          exact Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le hn_all hcontra)
        have hn_ge2 : ∀ i < r, 2 ≤ n i := by
          intro i _
          dsimp only [n]
          split_ifs
          · have : 1 ≤ (a + 1) ^ (2 ^ i) := Nat.one_le_pow _ _ (by omega)
            omega
          · calc
              2 ≤ a + 1 := by omega
              _ = (a + 1) ^ 1 := (pow_one _).symm
              _ ≤ (a + 1) ^ (2 ^ (r - 1)) :=
                Nat.pow_le_pow_right (by omega) (Nat.one_le_pow _ _ (by omega))
        have hmaj := cook_majorization r hr x n hx_mono hx_ge hn_ge2 hpref_n hstrict_n
        have hsylv := sylvester_one_sub_inv_prod a r ha hr
        have hfrac : (a : ℝ) / (b : ℝ) ≤ (a : ℝ) / ((a + 1 : ℕ) : ℝ) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact_mod_cast (by omega : a + 1 ≤ b)
        linarith

end MajorizationAndNielsen

/-! ## Section 5: Goto (2007) Upper Bound & NEW Sharper Exponential Upper Bound `3^(2^(ω(n)-1))` -/

section UpperBounds

private lemma finset_prod_range_eq_list_prod (m : ℕ) (g : ℕ → ℕ) :
    ∏ i ∈ Finset.range m, g i = ((List.range m).map g).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, List.range_succ, List.map_append, List.prod_append, ih]
    simp

/-- Sorted prime-power components `q_i + 1` of a unitary perfect number `n`. -/
private lemma sorted_components_of_upn (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) :
    let k := n.primeFactors.card
    ∃ (x : ℕ → ℕ),
      2 ≤ k ∧
      (∀ i j, i ≤ j → j < k → x i ≤ x j) ∧
      (∀ i < k, 3 ≤ x i) ∧
      (∀ i < k, 2 ≤ n.factorization 2 → 4 ≤ x i) ∧
      (∏ i ∈ Finset.range k, x i = 2 * n) ∧
      (∏ i ∈ Finset.range k, (x i - 1) = n) ∧
      (∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) = (1 : ℝ) / 2) ∧
      (∀ u, 2 ≤ u → u ≤ k → 2 ∣ ∏ i ∈ Finset.range u, x i) := by
  intro k
  have hv2_ge := one_le_v2_of_isUnitaryPerfect n hn
  rw [isUnitaryPerfect_iff_prod_eq] at hn
  rcases hn with ⟨hpos, hprod⟩
  have hn0 : n ≠ 0 := Nat.ne_of_gt hpos
  have h2mem : 2 ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk_le1 : n.primeFactors.card ≤ 1 := by omega
    have hcard_ge1 : 1 ≤ n.primeFactors.card := Finset.one_le_card.mpr ⟨2, h2mem⟩
    have hcard1 : n.primeFactors.card = 1 := by omega
    rcases Finset.card_eq_one.mp hcard1 with ⟨p, hp⟩
    have hp2 : p = 2 := by
      have : 2 ∈ ({p} : Finset ℕ) := hp ▸ h2mem
      exact (Finset.mem_singleton.mp this).symm
    subst hp2
    have hself : ∏ q ∈ n.primeFactors, q ^ n.factorization q = n := by
      simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn0
    have hge2 : 2 ≤ 2 ^ n.factorization 2 := Nat.le_self_pow (by omega) 2
    rw [hp, Finset.prod_singleton] at hprod hself
    omega
  -- Map `n.primeFactors` to the Finset of components `q_p + 1 = p^(v_p(n)) + 1`.
  let f : ℕ → ℕ := fun p => p ^ n.factorization p + 1
  have hf_inj : Set.InjOn f (n.primeFactors : Set ℕ) := by
    intro p₁ hp₁ p₂ hp₂ heq
    dsimp only [f] at heq
    have hpow_eq : p₁ ^ n.factorization p₁ = p₂ ^ n.factorization p₂ := by omega
    have hp₁' : Nat.Prime p₁ := Nat.prime_of_mem_primeFactors hp₁
    have hp₂' : Nat.Prime p₂ := Nat.prime_of_mem_primeFactors hp₂
    have he₁ : 0 < n.factorization p₁ :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ hp₁))
    have hdvd : p₁ ∣ p₂ ^ n.factorization p₂ := by
      rw [← hpow_eq]
      exact dvd_pow_self p₁ (Nat.ne_of_gt he₁)
    exact (Nat.prime_dvd_prime_iff_eq hp₁' hp₂').mp (hp₁'.dvd_of_dvd_pow hdvd)
  let S : Finset ℕ := n.primeFactors.image f
  have hS_card : S.card = k := Finset.card_image_of_injOn hf_inj
  let L : List ℕ := S.sort (· ≤ ·)
  have hL_len : L.length = k := by rw [Finset.length_sort, hS_card]
  have hL_sorted : L.Pairwise (· ≤ ·) := Finset.pairwise_sort S (· ≤ ·)
  have hL_nodup : L.Nodup := Finset.sort_nodup S (· ≤ ·)
  let x : ℕ → ℕ := fun i => L.getD i 0
  have hx_mem : ∀ i < k, x i ∈ S := by
    intro i hi
    have hiL : i < L.length := by omega
    have hget : x i = L[i]'hiL := by simp [x, List.getD_eq_getElem?_getD, hiL]
    rw [hget]
    exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hiL)
  have hx_mono : ∀ i j, i ≤ j → j < k → x i ≤ x j := by
    intro i j hij hj
    by_cases heq : i = j
    · subst heq; exact le_refl _
    · have hlt : i < j := by omega
      have hiL : i < L.length := by omega
      have hjL : j < L.length := by omega
      have hgi : x i = L[i]'hiL := by simp [x, List.getD_eq_getElem?_getD, hiL]
      have hgj : x j = L[j]'hjL := by simp [x, List.getD_eq_getElem?_getD, hjL]
      rw [hgi, hgj]
      exact List.pairwise_iff_getElem.mp hL_sorted i j hiL hjL hlt
  have hx_ge3 : ∀ i < k, 3 ≤ x i := by
    intro i hi
    rcases Finset.mem_image.mp (hx_mem i hi) with ⟨p, hp, hpeq⟩
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have he_pos : 1 ≤ n.factorization p :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ hp))
    have hpow_ge : 2 ≤ p ^ n.factorization p :=
      le_trans hp_prime.two_le (Nat.le_self_pow (by omega) p)
    dsimp only [f] at hpeq
    omega
  have hx_ge4 : ∀ i < k, 2 ≤ n.factorization 2 → 4 ≤ x i := by
    intro i hi hv2
    rcases Finset.mem_image.mp (hx_mem i hi) with ⟨p, hp, hpeq⟩
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have he_pos : 1 ≤ n.factorization p :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ hp))
    dsimp only [f] at hpeq
    by_cases hp2 : p = 2
    · subst hp2
      have hpow4 : 4 ≤ 2 ^ n.factorization 2 := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n.factorization 2 := Nat.pow_le_pow_right (by omega) hv2
      omega
    · have hp3 : 3 ≤ p := by
        have := hp_prime.two_le
        omega
      have hpow3 : 3 ≤ p ^ n.factorization p := le_trans hp3 (Nat.le_self_pow (by omega) p)
      omega
  have hprod_range_L : ∀ (g : ℕ → ℕ),
      ∏ i ∈ Finset.range k, g (x i) = ∏ y ∈ S, g y := by
    intro g
    have hL_prod : (L.map g).prod = ∏ y ∈ S, g y := by
      have hto : L.toFinset = S := by
        ext y
        simp [L]
      rw [← hto, List.prod_toFinset _ hL_nodup]
    rw [← hL_prod]
    have hfin : ∏ i ∈ Finset.range k, g (x i) = (L.map g).prod := by
      have hL_eq : L.map g = (List.range k).map (fun i => g (x i)) := by
        apply List.ext_getElem
        · simp [hL_len]
        · intro i h1 h2
          simp only [List.getElem_map, List.getElem_range]
          have hiL : i < L.length := by simpa using h1
          simp [x, List.getD_eq_getElem?_getD, hiL]
      rw [hL_eq, ← finset_prod_range_eq_list_prod]
    exact hfin
  have hx_prod : ∏ i ∈ Finset.range k, x i = 2 * n := by
    have h1 := hprod_range_L (fun y => y)
    rw [h1, Finset.prod_image (fun a ha b hb hab => hf_inj ha hb hab)]
    exact hprod
  have hx_sub_prod : ∏ i ∈ Finset.range k, (x i - 1) = n := by
    rw [hprod_range_L (fun y => y - 1)]
    rw [Finset.prod_image (fun a ha b hb hab => hf_inj ha hb hab)]
    have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
      simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn0
    simpa [f] using hself
  have hx_rat : ∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) = (1 : ℝ) / 2 := by
    have hterm : ∀ i ∈ Finset.range k,
        (1 : ℝ) - 1 / (x i : ℝ) = ((x i - 1 : ℕ) : ℝ) / (x i : ℝ) := by
      intro i hi
      have h3 := hx_ge3 i (Finset.mem_range.mp hi)
      have hpos_x : (0 : ℝ) < (x i : ℝ) := by exact_mod_cast (by omega : 0 < x i)
      rw [Nat.cast_sub (by omega : 1 ≤ x i), Nat.cast_one]
      field_simp [ne_of_gt hpos_x]
    rw [Finset.prod_congr rfl hterm, Finset.prod_div_distrib]
    have hnum : ∏ i ∈ Finset.range k, ((x i - 1 : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast hx_sub_prod
    have hden : ∏ i ∈ Finset.range k, (x i : ℝ) = ((2 * n : ℕ) : ℝ) := by
      exact_mod_cast hx_prod
    rw [hnum, hden]
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    push_cast
    field_simp [ne_of_gt hn_pos]
  have hx_even_prefix : ∀ u, 2 ≤ u → u ≤ k → 2 ∣ ∏ i ∈ Finset.range u, x i := by
    intro u hu2 huk
    -- Among x 0 and x 1 (distinct because L is Nodup), at most one equals f 2 = 2^(v_2(n)) + 1.
    have h0_lt : 0 < L.length := by omega
    have h1_lt : 1 < L.length := by omega
    have hx0_ne_x1 : x 0 ≠ x 1 := by
      have h0 : x 0 = L[0]'h0_lt := by simp [x, List.getD_eq_getElem?_getD, h0_lt]
      have h1 : x 1 = L[1]'h1_lt := by simp [x, List.getD_eq_getElem?_getD, h1_lt]
      rw [h0, h1]
      intro heq
      have hfin : (⟨0, h0_lt⟩ : Fin L.length) = ⟨1, h1_lt⟩ :=
        (List.nodup_iff_injective_getElem.mp hL_nodup) heq
      simp at hfin
    have heven_of_ne_f2 : ∀ i < k, x i ≠ f 2 → 2 ∣ x i := by
      intro i hi hne
      rcases Finset.mem_image.mp (hx_mem i hi) with ⟨p, hp, hpeq⟩
      have hp2 : p ≠ 2 := fun h => hne (by rw [← hpeq, h])
      rw [← hpeq]
      exact odd_primePow_add_one_even (Nat.prime_of_mem_primeFactors hp) hp2
    by_cases h0eq : x 0 = f 2
    · have h1ne : x 1 ≠ f 2 := fun h => hx0_ne_x1 (h0eq.trans h.symm)
      have h2dvd1 : 2 ∣ x 1 := heven_of_ne_f2 1 (by omega) h1ne
      exact dvd_trans h2dvd1 (Finset.dvd_prod_of_mem x (Finset.mem_range.mpr (by omega)))
    · have h2dvd0 : 2 ∣ x 0 := heven_of_ne_f2 0 (by omega) h0eq
      exact dvd_trans h2dvd0 (Finset.dvd_prod_of_mem x (Finset.mem_range.mpr (by omega)))
  exact ⟨x, hk2, hx_mono, hx_ge3, hx_ge4, hx_prod, hx_sub_prod, hx_rat, hx_even_prefix⟩

/-- Strict prefix product inequality: if `∏_{i < k} (1 - 1/x_i) = c` and `x_i ≥ 2`, then
`c < ∏_{i < u} (1 - 1/x_i)` for every `u < k`. -/
private lemma prefix_prod_gt_of_eq (k : ℕ) (x : ℕ → ℕ) (hx_ge : ∀ i < k, 2 ≤ x i)
    (u : ℕ) (hu : u < k) :
    ∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) <
      ∏ i ∈ Finset.range u, (1 - 1 / (x i : ℝ)) := by
  have hk_eq : k = u + (k - u) := by omega
  conv_lhs => rw [hk_eq, Finset.prod_range_add]
  have hpre_pos : 0 < ∏ i ∈ Finset.range u, (1 - 1 / (x i : ℝ)) := by
    refine Finset.prod_pos fun i hi => ?_
    have hxi : (1 : ℝ) < (x i : ℝ) := by
      exact_mod_cast (by have := hx_ge i (by have := Finset.mem_range.mp hi; omega); omega : 1 < x i)
    rw [sub_pos, div_lt_one (by linarith)]
    exact hxi
  have htail_lt1 : ∏ j ∈ Finset.range (k - u), (1 - 1 / (x (u + j) : ℝ)) < 1 := by
    have h1 : ∀ j ∈ Finset.range (k - u), (1 : ℝ) - 1 / (x (u + j) : ℝ) < 1 := by
      intro j hj
      have hpos : (0 : ℝ) < 1 / (x (u + j) : ℝ) := by
        have := hx_ge (u + j) (by have := Finset.mem_range.mp hj; omega)
        positivity
      linarith
    have h0 : ∀ j ∈ Finset.range (k - u), (0 : ℝ) < 1 - 1 / (x (u + j) : ℝ) := by
      intro j hj
      have hxi : (1 : ℝ) < (x (u + j) : ℝ) := by
        exact_mod_cast (by have := hx_ge (u + j) (by have := Finset.mem_range.mp hj; omega); omega : 1 < x (u + j))
      rw [sub_pos, div_lt_one (by linarith)]
      exact hxi
    have hne : (Finset.range (k - u)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
    calc
      ∏ j ∈ Finset.range (k - u), (1 - 1 / (x (u + j) : ℝ))
          < ∏ _j ∈ Finset.range (k - u), (1 : ℝ) :=
            Finset.prod_lt_prod_of_nonempty h0 (fun j hj => h1 j hj) hne
      _ = 1 := by simp
  calc
    (∏ i ∈ Finset.range u, (1 - 1 / (x i : ℝ))) *
        (∏ j ∈ Finset.range (k - u), (1 - 1 / (x (u + j) : ℝ)))
        < (∏ i ∈ Finset.range u, (1 - 1 / (x i : ℝ))) * 1 :=
          mul_lt_mul_of_pos_left htail_lt1 hpre_pos
    _ = ∏ i ∈ Finset.range u, (1 - 1 / (x i : ℝ)) := mul_one _

/-- **Goto (2007) Upper Bound (First Lean 4 Formalization):**
For every unitary perfect number `n`, `n < 2^(2^(ω(n)))` (in fact `2 * n < 2^(2^(ω(n)))`). -/
theorem goto_upper_bound (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) :
    n < 2 ^ (2 ^ n.primeFactors.card) := by
  rcases sorted_components_of_upn n hn with
    ⟨x, hk2, hx_mono, hx_ge3, _, hx_prod, _, hx_rat, _⟩
  have hge2 : ∀ i < n.primeFactors.card, 2 ≤ x i := fun i hi => le_trans (by omega) (hx_ge3 i hi)
  have hnb := nielsen_product_bound n.primeFactors.card (by omega) 1 2 (by omega) (by omega) x
    hx_mono hge2 (by simpa using le_of_eq hx_rat)
    (fun u hu => by simpa [← hx_rat] using prefix_prod_gt_of_eq n.primeFactors.card x hge2 u hu)
  rw [one_mul, hx_prod] at hnb
  have h11 : (1 + 1 : ℕ) = 2 := by norm_num
  rw [h11] at hnb
  omega

/-- **NEW SHARP EXPONENTIAL UPPER BOUND (Strictly Improving Goto 2007):**
For every unitary perfect number `n` with `v_2(n) ≥ 2` (which holds automatically whenever
`ω(n) ≥ 4`), we have
`n < 3^(2^(ω(n) - 1)) = (√3)^(2^(ω(n)))`,
reducing the double-exponential base from Goto's `2` to `√3 ≈ 1.73205`. -/
theorem sharper_upper_bound_of_v2_ge_two (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n)
    (hv2 : 2 ≤ n.factorization 2) :
    n < 3 ^ (2 ^ (n.primeFactors.card - 1)) := by
  rcases sorted_components_of_upn n hn with
    ⟨x, hk2, hx_mono, hx_ge3, hx_ge4, hx_prod, hx_sub_prod, hx_rat, hx_even⟩
  set k := n.primeFactors.card
  have hx_ge4' : ∀ i < k, 4 ≤ x i := fun i hi => hx_ge4 i hi hv2
  have hx_ge2 : ∀ i < k, 2 ≤ x i := fun i hi => le_trans (by omega) (hx_ge3 i hi)
  -- First rule out k = 2 (when x_0, x_1 ≥ 4, (1 - 1/x_0)(1 - 1/x_1) ≥ (3/4)(3/4) = 9/16 > 1/2).
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have hk_eq2 : k = 2 := by omega
    have h0 := hx_ge4' 0 (by omega)
    have h1 := hx_ge4' 1 (by omega)
    have hrat2 : (1 - 1 / (x 0 : ℝ)) * (1 - 1 / (x 1 : ℝ)) = 1 / 2 := by
      have := hx_rat
      rw [hk_eq2, Finset.prod_range_succ, Finset.prod_range_one] at this
      exact this
    have hb0 : (3 : ℝ) / 4 ≤ 1 - 1 / (x 0 : ℝ) := by
      have : (4 : ℝ) ≤ (x 0 : ℝ) := by exact_mod_cast h0
      have : 1 / (x 0 : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) this
      linarith
    have hb1 : (3 : ℝ) / 4 ≤ 1 - 1 / (x 1 : ℝ) := by
      have : (4 : ℝ) ≤ (x 1 : ℝ) := by exact_mod_cast h1
      have : 1 / (x 1 : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) this
      linarith
    have hmul : ((3 : ℝ) / 4) * ((3 : ℝ) / 4) ≤ (1 - 1 / (x 0 : ℝ)) * (1 - 1 / (x 1 : ℝ)) :=
      mul_le_mul hb0 hb1 (by norm_num) (by linarith)
    linarith
  -- Comparison sequence y: y 0 = 4, y i = 3^(2^(i-1)) + 1 (1 ≤ i < k - 1), y (k - 1) = 3^(2^(k - 2)).
  let y : ℕ → ℕ := fun i =>
    if i = 0 then 4
    else if i < k - 1 then 3 ^ (2 ^ (i - 1)) + 1
    else 3 ^ (2 ^ (k - 2))
  have hy_ge2 : ∀ i < k, 2 ≤ y i := by
    intro i _
    dsimp only [y]
    split_ifs
    · omega
    · have : 1 ≤ 3 ^ (2 ^ (i - 1)) := Nat.one_le_pow _ _ (by omega)
      omega
    · calc
        2 ≤ 3 := by omega
        _ = 3 ^ 1 := (pow_one _).symm
        _ ≤ 3 ^ (2 ^ (k - 2)) := Nat.pow_le_pow_right (by omega) (Nat.one_le_pow _ _ (by omega))
  -- Prefix products of y for 2 ≤ u < k: ∏_{i < u} y i = 2 * (3^(2^(u - 1)) - 1).
  have hy_pref : ∀ u, 2 ≤ u → u < k →
      ∏ i ∈ Finset.range u, y i = 2 * (3 ^ (2 ^ (u - 1)) - 1) := by
    intro u hu2 huk
    have hu_eq : u = 1 + (u - 1) := by omega
    conv_lhs => rw [hu_eq, Finset.prod_range_add]
    simp only [Finset.range_one, Finset.prod_singleton, y, ↓reduceIte]
    have htail : ∏ j ∈ Finset.range (u - 1), y (1 + j) =
        ∏ j ∈ Finset.range (u - 1), (3 ^ (2 ^ j) + 1) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjlt := Finset.mem_range.mp hj
      have hlt : 1 + j < k - 1 := by omega
      simp [y, hlt]
    rw [htail]
    have hs := sylvester_prefix_prod 2 (u - 1)
    norm_num at hs
    have hge1 : 1 ≤ 3 ^ (2 ^ (u - 1)) := Nat.one_le_pow _ _ (by omega)
    omega
  -- Exact value of ∏_{i < k} (1 - 1 / y i) = 1 / 2.
  have hy_rat : ∏ i ∈ Finset.range k, (1 - 1 / (y i : ℝ)) = (1 : ℝ) / 2 := by
    have hk_eq : k = 1 + (k - 1) := by omega
    rw [hk_eq, Finset.prod_range_add]
    simp only [Finset.range_one, Finset.prod_singleton, y, ↓reduceIte]
    have htail : ∏ j ∈ Finset.range (k - 1), (1 - 1 / (y (1 + j) : ℝ)) =
        ∏ j ∈ Finset.range (k - 1),
          (1 - 1 / ((if j < (k - 1) - 1 then (2 + 1) ^ (2 ^ j) + 1 else (2 + 1) ^ (2 ^ ((k - 1) - 1)) : ℕ) : ℝ)) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hne0 : 1 + j ≠ 0 := by omega
      have hiff : (1 + j < k - 1) ↔ (j < (k - 1) - 1) := by omega
      have hsub : k - 2 = (k - 1) - 1 := by omega
      simp only [y, hne0, ↓reduceIte, hiff, hsub, Nat.add_sub_cancel_left]
    rw [htail, sylvester_one_sub_inv_prod 2 (k - 1) (by omega) (by omega)]
    norm_num
  -- Total product of y is strictly less than 2 * 3^(2^(k - 1)).
  have hy_all_lt : ∏ i ∈ Finset.range k, y i < 2 * 3 ^ (2 ^ (k - 1)) := by
    have hk_eq : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk_eq, Finset.prod_range_succ]
    have hlast : y (k - 1) = 3 ^ (2 ^ (k - 2)) := by
      have hne0 : k - 1 ≠ 0 := by omega
      simp [y, hne0]
    rw [hy_pref (k - 1) (by omega) (by omega), hlast]
    have hsub_lt : 3 ^ (2 ^ (k - 2)) - 1 < 3 ^ (2 ^ (k - 2)) :=
      Nat.sub_lt (by positivity) (by omega)
    have hpow_eq : 3 ^ (2 ^ (k - 2)) * 3 ^ (2 ^ (k - 2)) = 3 ^ (2 ^ (k - 1)) := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      have : k - 2 + 1 = k - 1 := by omega
      rw [this]
    have h1 : k - 1 - 1 = k - 2 := by omega
    rw [h1]
    calc
      2 * (3 ^ (2 ^ (k - 2)) - 1) * 3 ^ (2 ^ (k - 2))
          < 2 * 3 ^ (2 ^ (k - 2)) * 3 ^ (2 ^ (k - 2)) := by
            rw [mul_assoc, mul_assoc]
            exact Nat.mul_lt_mul_of_pos_left
              (Nat.mul_lt_mul_of_pos_right hsub_lt (by positivity)) (by omega)
      _ = 2 * 3 ^ (2 ^ (k - 1)) := by rw [mul_assoc, hpow_eq]
  -- Now prove n < 3^(2^(k - 1)) by contradiction!
  by_contra hcontra
  push Not at hcontra
  by_cases hex : ∃ u, 1 ≤ u ∧ u < k ∧
      ∏ i ∈ Finset.range u, x i ≤ ∏ i ∈ Finset.range u, y i
  · rcases hex with ⟨u, hu1, huk, hxu⟩
    by_cases hu_eq1 : u = 1
    · subst hu_eq1
      simp only [Finset.range_one, Finset.prod_singleton, y, ↓reduceIte] at hxu
      have hx0_eq4 : x 0 = 4 := le_antisymm hxu (hx_ge4' 0 (by omega))
      -- Peel off x 0 = 4: remaining k - 1 factors have product (1/2) / (3/4) = 2/3.
      have hsplit : ∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) =
          (1 - 1 / (x 0 : ℝ)) * ∏ j ∈ Finset.range (k - 1), (1 - 1 / (x (1 + j) : ℝ)) := by
        have hk_eq : k = 1 + (k - 1) := by omega
        conv_lhs => rw [hk_eq, Finset.prod_range_add, Finset.range_one, Finset.prod_singleton]
      have htail_rat : ∏ j ∈ Finset.range (k - 1), (1 - 1 / (x (1 + j) : ℝ)) = (2 : ℝ) / 3 := by
        rw [hsplit, hx0_eq4] at hx_rat
        push_cast at hx_rat
        linarith
      have hnb := nielsen_product_bound (k - 1) (by omega) 2 3 (by omega) (by omega)
        (fun j => x (1 + j))
        (fun i j hij hj => hx_mono (1 + i) (1 + j) (by omega) (by omega))
        (fun j hj => hx_ge2 (1 + j) (by omega))
        (by push_cast; exact le_of_eq htail_rat)
        (fun v hv => by
          push_cast
          rw [← htail_rat]
          exact prefix_prod_gt_of_eq (k - 1) (fun j => x (1 + j))
            (fun j hj => hx_ge2 (1 + j) (by omega)) v hv)
      have hprod_split : 2 * n = 4 * ∏ j ∈ Finset.range (k - 1), x (1 + j) := by
        rw [← hx_prod]
        have hk_eq : k = 1 + (k - 1) := by omega
        conv_lhs => rw [hk_eq, Finset.prod_range_add, Finset.range_one, Finset.prod_singleton, hx0_eq4]
      have h21 : (2 + 1 : ℕ) = 3 := by norm_num
      rw [h21] at hnb
      omega
    · have hu2 : 2 ≤ u := by omega
      rw [hy_pref u hu2 huk] at hxu
      have h2dvd : 2 ∣ ∏ i ∈ Finset.range u, x i := hx_even u hu2 (le_of_lt huk)
      rcases h2dvd with ⟨a', ha'eq⟩
      set b' := ∏ i ∈ Finset.range u, (x i - 1)
      have ha'_pos : 1 ≤ a' := by
        have hpos : 0 < ∏ i ∈ Finset.range u, x i :=
          Finset.prod_pos fun i hi =>
            lt_of_lt_of_le (by omega : 0 < 2) (hx_ge2 i (by have := Finset.mem_range.mp hi; omega))
        omega
      have hb'_pos : 1 ≤ b' :=
        Nat.succ_le_of_lt (Finset.prod_pos fun i hi => by
          have := hx_ge2 i (by have := Finset.mem_range.mp hi; omega)
          omega)
      have ha'_le : a' + 1 ≤ 3 ^ (2 ^ (u - 1)) := by
        have : 1 ≤ 3 ^ (2 ^ (u - 1)) := Nat.one_le_pow _ _ (by omega)
        omega
      have hpref_prod :
          ∏ i ∈ Finset.range u, (1 - 1 / (x i : ℝ)) = (b' : ℝ) / ((2 * a' : ℕ) : ℝ) := by
        rw [← ha'eq]
        dsimp only [b']
        push_cast
        rw [← Finset.prod_div_distrib]
        refine Finset.prod_congr rfl fun i hi => ?_
        have hxi := hx_ge2 i (by have := Finset.mem_range.mp hi; omega)
        have hxi_pos : (0 : ℝ) < (x i : ℝ) := by exact_mod_cast (by omega : 0 < x i)
        rw [Nat.cast_sub (by omega : 1 ≤ x i), Nat.cast_one]
        field_simp [ne_of_gt hxi_pos]
      have hsplit : ∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) =
          (∏ i ∈ Finset.range u, (1 - 1 / (x i : ℝ))) *
            ∏ j ∈ Finset.range (k - u), (1 - 1 / (x (u + j) : ℝ)) := by
        have hk_eq : k = u + (k - u) := by omega
        conv_lhs => rw [hk_eq, Finset.prod_range_add]
      have htail_rat : ∏ j ∈ Finset.range (k - u), (1 - 1 / (x (u + j) : ℝ)) =
          (a' : ℝ) / (b' : ℝ) := by
        rw [hsplit, hpref_prod] at hx_rat
        have ha'_ne : (a' : ℝ) ≠ 0 := by positivity
        have hb'_ne : (b' : ℝ) ≠ 0 := by positivity
        push_cast at hx_rat
        have h := congrArg (fun t => t * ((2 : ℝ) * (a' : ℝ) / (b' : ℝ))) hx_rat
        have hL : (b' : ℝ) / (2 * (a' : ℝ)) *
            (∏ j ∈ Finset.range (k - u), (1 - 1 / (x (u + j) : ℝ))) *
            (2 * (a' : ℝ) / (b' : ℝ)) =
            ∏ j ∈ Finset.range (k - u), (1 - 1 / (x (u + j) : ℝ)) := by
          field_simp [ha'_ne, hb'_ne]
        have hR : (1 : ℝ) / 2 * (2 * (a' : ℝ) / (b' : ℝ)) = (a' : ℝ) / (b' : ℝ) := by
          field_simp [hb'_ne]
        linarith
      have hnb := nielsen_product_bound (k - u) (by omega) a' b' ha'_pos hb'_pos
        (fun j => x (u + j))
        (fun i j hij hj => hx_mono (u + i) (u + j) (by omega) (by omega))
        (fun j hj => hx_ge2 (u + j) (by omega))
        (le_of_eq htail_rat)
        (fun v hv => by
          rw [← htail_rat]
          exact prefix_prod_gt_of_eq (k - u) (fun j => x (u + j))
            (fun j hj => hx_ge2 (u + j) (by omega)) v hv)
      have hprod_eq_n : a' * ∏ j ∈ Finset.range (k - u), x (u + j) = n := by
        have hk_eq : k = u + (k - u) := by omega
        have h2n : 2 * n = (2 * a') * ∏ j ∈ Finset.range (k - u), x (u + j) := by
          rw [← hx_prod, ← ha'eq]
          conv_lhs => rw [hk_eq, Finset.prod_range_add]
        rw [mul_assoc] at h2n
        omega
      have hpow_le : (a' + 1) ^ (2 ^ (k - u)) ≤ 3 ^ (2 ^ (k - 1)) := by
        calc
          (a' + 1) ^ (2 ^ (k - u))
              ≤ (3 ^ (2 ^ (u - 1))) ^ (2 ^ (k - u)) := Nat.pow_le_pow_left ha'_le _
          _ = 3 ^ (2 ^ (u - 1) * 2 ^ (k - u)) := by rw [← pow_mul]
          _ = 3 ^ (2 ^ (k - 1)) := by
                rw [← pow_add]
                have : (u - 1) + (k - u) = k - 1 := by omega
                rw [this]
      omega
  · push Not at hex
    have hpref_y : ∀ u ≤ k, ∏ i ∈ Finset.range u, y i ≤ ∏ i ∈ Finset.range u, x i := by
      intro u hu
      by_cases hu0 : u = 0
      · subst hu0; simp
      · by_cases huk : u < k
        · exact Nat.le_of_lt (hex u (by omega) huk)
        · have hueq : u = k := by omega
          subst hueq
          rw [hx_prod]
          exact Nat.le_of_lt (lt_of_lt_of_le hy_all_lt (Nat.mul_le_mul_left 2 hcontra))
    have hstrict_y : ∏ i ∈ Finset.range k, y i < ∏ i ∈ Finset.range k, x i := by
      rw [hx_prod]
      exact lt_of_lt_of_le hy_all_lt (Nat.mul_le_mul_left 2 hcontra)
    have hmaj := cook_majorization k (by omega) x y hx_mono hx_ge2 hy_ge2 hpref_y hstrict_y
    linarith

/-- Corollary: Every unitary perfect number `n` with `ω(n) ≥ 4` satisfies
`n < 3^(2^(ω(n) - 1))`. -/
theorem sharper_upper_bound_of_omega_ge_four (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n)
    (hω : 4 ≤ n.primeFactors.card) :
    n < 3 ^ (2 ^ (n.primeFactors.card - 1)) := by
  have hle := omega_le_v2_add_two n hn
  exact sharper_upper_bound_of_v2_ge_two n hn (by omega)

/-- Further refinement when `3 ‖ n` and `5 ‖ n` (base `5^(1/4) ≈ 1.49535`):
for every unitary perfect number `n` with `v_3(n) = 1`, `v_5(n) = 1`, and `ω(n) ≥ 3`,
`n < 3 * 5^(2^(ω(n) - 2))`. -/
theorem sharper_upper_bound_of_three_five_exact (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n)
    (hv3 : n.factorization 3 = 1) (hv5 : n.factorization 5 = 1)
    (hω : 3 ≤ n.primeFactors.card) :
    n < 3 * 5 ^ (2 ^ (n.primeFactors.card - 2)) := by
  rw [isUnitaryPerfect_iff_prod_eq] at hn
  rcases hn with ⟨hpos, hprod⟩
  have hn0 : n ≠ 0 := Nat.ne_of_gt hpos
  have h3mem : 3 ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
  have h5mem : 5 ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
  let T := (n.primeFactors.erase 3).erase 5
  have h5_in : 5 ∈ n.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨by omega, h5mem⟩
  have hT_card : T.card = n.primeFactors.card - 2 := by
    have h1 := Finset.card_erase_add_one h5_in
    have h2 := Finset.card_erase_add_one h3mem
    change T.card + 1 = (n.primeFactors.erase 3).card at h1
    omega
  have h24_eq : 24 * (∏ p ∈ T, (p ^ n.factorization p + 1)) = 2 * n := by
    have hsplit1 := Finset.mul_prod_erase n.primeFactors (fun p => p ^ n.factorization p + 1) h3mem
    have hsplit2 := Finset.mul_prod_erase (n.primeFactors.erase 3)
      (fun p => p ^ n.factorization p + 1) h5_in
    rw [hv3] at hsplit1
    rw [hv5] at hsplit2
    have : (3 ^ 1 + 1) * ((5 ^ 1 + 1) * ∏ p ∈ T, (p ^ n.factorization p + 1)) = 2 * n := by
      rw [hsplit2, hsplit1, hprod]
    linarith
  have h15_eq : 15 * (∏ p ∈ T, p ^ n.factorization p) = n := by
    have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
      simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn0
    have hsplit1 := Finset.mul_prod_erase n.primeFactors (fun p => p ^ n.factorization p) h3mem
    have hsplit2 := Finset.mul_prod_erase (n.primeFactors.erase 3)
      (fun p => p ^ n.factorization p) h5_in
    rw [hv3] at hsplit1
    rw [hv5] at hsplit2
    have : 3 ^ 1 * (5 ^ 1 * ∏ p ∈ T, p ^ n.factorization p) = n := by
      rw [hsplit2, hsplit1, hself]
    linarith
  -- Sort the components `{p^(v_p(n)) + 1 | p ∈ T}` and apply `nielsen_product_bound` with a = 4, b = 5.
  let f : ℕ → ℕ := fun p => p ^ n.factorization p + 1
  have hT_sub : T ⊆ n.primeFactors :=
    Finset.Subset.trans (Finset.erase_subset 5 _) (Finset.erase_subset 3 _)
  have hf_inj : Set.InjOn f (T : Set ℕ) := by
    intro p₁ hp₁ p₂ hp₂ heq
    dsimp only [f] at heq
    have hpow_eq : p₁ ^ n.factorization p₁ = p₂ ^ n.factorization p₂ := by omega
    have hp₁' := Nat.prime_of_mem_primeFactors (hT_sub hp₁)
    have hp₂' := Nat.prime_of_mem_primeFactors (hT_sub hp₂)
    have he₁ : 0 < n.factorization p₁ :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ hT_sub hp₁))
    have hdvd : p₁ ∣ p₂ ^ n.factorization p₂ := by
      rw [← hpow_eq]; exact dvd_pow_self p₁ (Nat.ne_of_gt he₁)
    exact (Nat.prime_dvd_prime_iff_eq hp₁' hp₂').mp (hp₁'.dvd_of_dvd_pow hdvd)
  let S := T.image f
  set r := T.card
  have hr1 : 1 ≤ r := by omega
  have hS_card : S.card = r := Finset.card_image_of_injOn hf_inj
  let L := S.sort (· ≤ ·)
  have hL_len : L.length = r := by rw [Finset.length_sort, hS_card]
  have hL_sorted : L.Pairwise (· ≤ ·) := Finset.pairwise_sort S (· ≤ ·)
  have hL_nodup : L.Nodup := Finset.sort_nodup S (· ≤ ·)
  let x : ℕ → ℕ := fun i => L.getD i 0
  have hx_mem : ∀ i < r, x i ∈ S := by
    intro i hi
    have hiL : i < L.length := by omega
    have hget : x i = L[i]'hiL := by simp [x, List.getD_eq_getElem?_getD, hiL]
    rw [hget]
    exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hiL)
  have hx_mono : ∀ i j, i ≤ j → j < r → x i ≤ x j := by
    intro i j hij hj
    by_cases heq : i = j
    · subst heq; exact le_refl _
    · have hiL : i < L.length := by omega
      have hjL : j < L.length := by omega
      have hgi : x i = L[i]'hiL := by simp [x, List.getD_eq_getElem?_getD, hiL]
      have hgj : x j = L[j]'hjL := by simp [x, List.getD_eq_getElem?_getD, hjL]
      rw [hgi, hgj]
      exact List.pairwise_iff_getElem.mp hL_sorted i j hiL hjL (by omega)
  have hx_ge2 : ∀ i < r, 2 ≤ x i := by
    intro i hi
    rcases Finset.mem_image.mp (hx_mem i hi) with ⟨p, hp, hpeq⟩
    have hp_prime := Nat.prime_of_mem_primeFactors (hT_sub hp)
    have he_pos : 1 ≤ n.factorization p :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ hT_sub hp))
    have hpow_ge : 2 ≤ p ^ n.factorization p :=
      le_trans hp_prime.two_le (Nat.le_self_pow (by omega) p)
    dsimp only [f] at hpeq
    omega
  have hprod_range_L : ∀ (g : ℕ → ℕ), ∏ i ∈ Finset.range r, g (x i) = ∏ y ∈ S, g y := by
    intro g
    have hL_prod : (L.map g).prod = ∏ y ∈ S, g y := by
      have hto : L.toFinset = S := by ext y; simp [L]
      rw [← hto, List.prod_toFinset _ hL_nodup]
    rw [← hL_prod]
    have hL_eq : L.map g = (List.range r).map (fun i => g (x i)) := by
      apply List.ext_getElem
      · simp [hL_len]
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range]
        have hiL : i < L.length := by simpa using h1
        simp [x, List.getD_eq_getElem?_getD, hiL]
    rw [hL_eq, ← finset_prod_range_eq_list_prod]
  have hx_prod : ∏ i ∈ Finset.range r, x i = ∏ p ∈ T, (p ^ n.factorization p + 1) := by
    have h1 := hprod_range_L (fun y => y)
    rw [h1]
    exact Finset.prod_image (fun a ha b hb hab => hf_inj ha hb hab)
  have hx_sub_prod : ∏ i ∈ Finset.range r, (x i - 1) = ∏ p ∈ T, p ^ n.factorization p := by
    rw [hprod_range_L (fun y => y - 1)]
    have himg : ∏ y ∈ T.image f, (y - 1) = ∏ p ∈ T, (f p - 1) :=
      Finset.prod_image (fun a ha b hb hab => hf_inj ha hb hab)
    simpa [S, f] using himg
  have hx_rat : ∏ i ∈ Finset.range r, (1 - 1 / (x i : ℝ)) = (4 : ℝ) / 5 := by
    have hterm : ∀ i ∈ Finset.range r,
        (1 : ℝ) - 1 / (x i : ℝ) = ((x i - 1 : ℕ) : ℝ) / (x i : ℝ) := by
      intro i hi
      have h2 := hx_ge2 i (Finset.mem_range.mp hi)
      have hpos_x : (0 : ℝ) < (x i : ℝ) := by exact_mod_cast (by omega : 0 < x i)
      rw [Nat.cast_sub (by omega : 1 ≤ x i), Nat.cast_one]
      field_simp [ne_of_gt hpos_x]
    rw [Finset.prod_congr rfl hterm, Finset.prod_div_distrib]
    have hnum : ∏ i ∈ Finset.range r, ((x i - 1 : ℕ) : ℝ) =
        ((∏ p ∈ T, p ^ n.factorization p : ℕ) : ℝ) := by exact_mod_cast hx_sub_prod
    have hden : ∏ i ∈ Finset.range r, (x i : ℝ) =
        ((∏ p ∈ T, (p ^ n.factorization p + 1) : ℕ) : ℝ) := by exact_mod_cast hx_prod
    rw [hnum, hden]
    have h15r : (15 : ℝ) * ((∏ p ∈ T, p ^ n.factorization p : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast h15_eq
    have h24r : (24 : ℝ) * ((∏ p ∈ T, (p ^ n.factorization p + 1) : ℕ) : ℝ) = 2 * (n : ℝ) := by
      exact_mod_cast h24_eq
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    have hden_pos : (0 : ℝ) < ((∏ p ∈ T, (p ^ n.factorization p + 1) : ℕ) : ℝ) := by linarith
    rw [div_eq_div_iff (ne_of_gt hden_pos) (by norm_num)]
    linarith
  have hnb := nielsen_product_bound r hr1 4 5 (by omega) (by omega) x hx_mono hx_ge2
    (by push_cast; exact le_of_eq hx_rat)
    (fun u hu => by push_cast; rw [← hx_rat]; exact prefix_prod_gt_of_eq r x hx_ge2 u hu)
  rw [hx_prod] at hnb
  have hreq : r = n.primeFactors.card - 2 := hT_card
  rw [hreq] at hnb
  have h41 : (4 + 1 : ℕ) = 5 := by norm_num
  rw [h41] at hnb
  omega

end UpperBounds

/-! ## Section 6: Complete Small-`v_2` & Small-`ω` Classifications, `n ≠ 90` Bound, and Unconditional Finiteness -/

section ClassificationsAndFiniteness

private lemma odd_prime_pow_ge_three {p e : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (he : 1 ≤ e) :
    3 ≤ p ^ e := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  exact le_trans hp3 (Nat.le_self_pow (by omega) p)

/-- Complete classification for `v_2(n) = 1`:
`n` is a unitary perfect number with `v_2(n) = 1` iff `n = 6` or `n = 90`. -/
theorem classify_v2_eq_one (n : ℕ) :
    ((∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) ∧
      n.factorization 2 = 1) ↔
      (n = 6 ∨ n = 90) := by
  constructor
  · rintro ⟨hn, hv2⟩
    have hbal := sum_v2_odd_components_eq n hn
    have hdvd3 := (two_pow_add_one_dvd_odd_part n hn).1
    have h3dvd_n : 3 ∣ n := by
      have hdiv := Nat.div_dvd_of_dvd (Nat.ordProj_dvd n 2)
      rw [hv2] at hdvd3 hdiv
      exact dvd_trans hdvd3 hdiv
    rw [hv2] at hbal
    rw [isUnitaryPerfect_iff_prod_eq] at hn
    rcases hn with ⟨hpos, hprod⟩
    have hn0 : n ≠ 0 := Nat.ne_of_gt hpos
    have h2mem : 2 ∈ n.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
    have h3mem : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3dvd_n, hn0⟩
    have hcard_odd : (n.primeFactors.erase 2).card ≤ 2 := by
      have h1 : (n.primeFactors.erase 2).card ≤
          ∑ p ∈ n.primeFactors.erase 2, (p ^ n.factorization p + 1).factorization 2 := by
        calc
          (n.primeFactors.erase 2).card = ∑ _p ∈ n.primeFactors.erase 2, 1 := by simp
          _ ≤ _ := Finset.sum_le_sum fun p hp => by
            have hp_ne2 := (Finset.mem_erase.mp hp).1
            have hp_prime := Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hp).2
            have hd2 := odd_primePow_add_one_even (e := n.factorization p) hp_prime hp_ne2
            have hmem2 : 2 ∈ (p ^ n.factorization p + 1).primeFactors :=
              Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd2, by positivity⟩
            exact Nat.pos_of_ne_zero
              (Finsupp.mem_support_iff.mp ((Nat.support_factorization _).symm ▸ hmem2))
      omega
    have h3_in : 3 ∈ n.primeFactors.erase 2 := Finset.mem_erase.mpr ⟨by omega, h3mem⟩
    have hcard_ge1 : 1 ≤ (n.primeFactors.erase 2).card := Finset.one_le_card.mpr ⟨3, h3_in⟩
    have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
      simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn0
    by_cases hc1 : (n.primeFactors.erase 2).card = 1
    · rcases Finset.card_eq_one.mp hc1 with ⟨p, hp⟩
      have hp3 : p = 3 := by
        have : 3 ∈ ({p} : Finset ℕ) := hp ▸ h3_in
        exact (Finset.mem_singleton.mp this).symm
      subst hp3
      have hpf_eq : n.primeFactors = {2, 3} := by
        have h := Finset.insert_erase h2mem
        rw [hp] at h
        exact h.symm
      rw [hpf_eq, Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3), hv2] at hprod hself
      omega
    · have hc2 : (n.primeFactors.erase 2).card = 2 := by omega
      have hcard_rem : ((n.primeFactors.erase 2).erase 3).card = 1 := by
        have := Finset.card_erase_add_one h3_in
        omega
      rcases Finset.card_eq_one.mp hcard_rem with ⟨q, hq⟩
      have hq_mem : q ∈ n.primeFactors.erase 2 := by
        have : q ∈ (n.primeFactors.erase 2).erase 3 := hq.symm ▸ Finset.mem_singleton_self q
        exact (Finset.mem_erase.mp this).2
      have hq_ne3 : q ≠ 3 := by
        have : q ∈ (n.primeFactors.erase 2).erase 3 := hq.symm ▸ Finset.mem_singleton_self q
        exact (Finset.mem_erase.mp this).1
      have hq_ne2 : q ≠ 2 := (Finset.mem_erase.mp hq_mem).1
      have hq_pf : q ∈ n.primeFactors := (Finset.mem_erase.mp hq_mem).2
      have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_pf
      have hq_ge5 : 5 ≤ q := by
        have h2 := hq_prime.two_le
        have hnot4 : q ≠ 4 := fun h => by subst h; norm_num at hq_prime
        omega
      have heq_e2 : n.primeFactors.erase 2 = {3, q} := by
        have h := Finset.insert_erase h3_in
        rw [hq] at h
        exact h.symm
      have hpf_eq : n.primeFactors = {2, 3, q} := by
        have h := Finset.insert_erase h2mem
        rw [heq_e2] at h
        exact h.symm
      rw [hpf_eq] at hprod hself
      have h2not : (2 : ℕ) ∉ ({3, q} : Finset ℕ) := by
        simp [hq_ne2.symm]
      rw [Finset.prod_insert h2not, Finset.prod_pair hq_ne3.symm, hv2] at hprod hself
      -- Now 3 * (3^e3 + 1) * (q^eq + 1) = 2 * (2 * 3^e3 * q^eq) = 4 * 3^e3 * q^eq
      set A := 3 ^ n.factorization 3
      set B := q ^ n.factorization q
      have hAB : 3 * (A + 1) * (B + 1) = 4 * A * B := by
        have h1 : 3 * ((A + 1) * (B + 1)) = 2 * n := by simpa [A, B] using hprod
        have h2 : 2 * (A * B) = n := by simpa [A, B] using hself
        linarith
      -- Also from hbal: (A + 1).factorization 2 + (B + 1).factorization 2 = 2, so each is 1!
      rw [heq_e2, Finset.sum_pair hq_ne3.symm] at hbal
      change (A + 1).factorization 2 + (B + 1).factorization 2 = 1 + 1 at hbal
      have hA_v2 : 1 ≤ (A + 1).factorization 2 := by
        have hd2 : 2 ∣ (A + 1) :=
          odd_primePow_add_one_even (e := n.factorization 3) Nat.prime_three (by omega)
        have hmem2 : 2 ∈ (A + 1).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd2, by positivity⟩
        exact Nat.pos_of_ne_zero
          (Finsupp.mem_support_iff.mp ((Nat.support_factorization _).symm ▸ hmem2))
      have hB_v2 : 1 ≤ (B + 1).factorization 2 := by
        have hd2 : 2 ∣ (B + 1) :=
          odd_primePow_add_one_even (e := n.factorization q) hq_prime hq_ne2
        have hmem2 : 2 ∈ (B + 1).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd2, by positivity⟩
        exact Nat.pos_of_ne_zero
          (Finsupp.mem_support_iff.mp ((Nat.support_factorization _).symm ▸ hmem2))
      have hA_v2_eq1 : (A + 1).factorization 2 = 1 := by omega
      have hA_ne3 : A ≠ 3 := by
        intro h3
        rw [h3] at hA_v2_eq1
        have h4eq : (3 + 1 : ℕ).factorization 2 = 2 := by
          have : (3 + 1 : ℕ) = 2 ^ 2 := by norm_num
          rw [this, Nat.Prime.factorization_pow Nat.prime_two]
          simp
        omega
      have he3_pos : 1 ≤ n.factorization 3 :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ h3mem))
      have he3_ge2 : 2 ≤ n.factorization 3 := by
        by_contra hlt
        have he3_1 : n.factorization 3 = 1 := by omega
        exact hA_ne3 (by dsimp only [A]; rw [he3_1]; norm_num)
      have hA_ge9 : 9 ≤ A := by
        calc
          9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ n.factorization 3 := Nat.pow_le_pow_right (by omega) he3_ge2
      have heq_pos : 1 ≤ n.factorization q :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ hq_pf))
      have hB_ge5 : 5 ≤ B := le_trans hq_ge5 (Nat.le_self_pow (by omega) q)
      -- From 3*(A+1)*(B+1) = 4*A*B, rewrite as A*B = 3*A + 3*B + 3:
      -- Since A ≥ 9: 9*B ≤ A*B = 3*A + 3*B + 3 => no, rewrite (A - 3)*(B - 3) = 12!
      -- Wait: A*B - 3*A - 3*B = 3 => (A - 3)*(B - 3) = 12!
      have hfact : (A - 3) * (B - 3) = 12 := by
        zify [show 3 ≤ A by omega, show 3 ≤ B by omega]
        linarith
      -- Since A ≥ 9, A - 3 ≥ 6; since B ≥ 5, B - 3 ≥ 2. Thus A - 3 = 6 and B - 3 = 2!
      have hA_eq9 : A = 9 := by nlinarith
      have hB_eq5 : B = 5 := by nlinarith
      right
      rw [← hself]
      change 2 * (A * B) = 90
      rw [hA_eq9, hB_eq5]
  · rintro (rfl | rfl)
    · refine ⟨isUnitaryPerfect_6, ?_⟩
      have : (6 : ℕ) = 2 ^ 1 * 3 := by norm_num
      rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two]
      have h3 : (3 : ℕ).factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)
      simp [h3]
    · refine ⟨isUnitaryPerfect_90, ?_⟩
      have : (90 : ℕ) = 2 ^ 1 * 45 := by norm_num
      rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two]
      have h45 : (45 : ℕ).factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)
      simp [h45]

/-- Complete classification for `v_2(n) = 2`:
`n` is a unitary perfect number with `v_2(n) = 2` iff `n = 60`. -/
theorem classify_v2_eq_two (n : ℕ) :
    ((∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) ∧
      n.factorization 2 = 2) ↔
      n = 60 := by
  constructor
  · rintro ⟨hn, hv2⟩
    have hbal := sum_v2_odd_components_eq n hn
    have hdvd5 := (two_pow_add_one_dvd_odd_part n hn).1
    have h5dvd_n : 5 ∣ n := by
      have hdiv := Nat.div_dvd_of_dvd (Nat.ordProj_dvd n 2)
      rw [hv2] at hdvd5 hdiv
      exact dvd_trans hdvd5 hdiv
    rw [hv2] at hbal
    rw [isUnitaryPerfect_iff_prod_eq] at hn
    rcases hn with ⟨hpos, hprod⟩
    have hn0 : n ≠ 0 := Nat.ne_of_gt hpos
    have h2mem : 2 ∈ n.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
    have h5mem : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h5dvd_n, hn0⟩
    have h5_in : 5 ∈ n.primeFactors.erase 2 := Finset.mem_erase.mpr ⟨by omega, h5mem⟩
    have hcard_odd : (n.primeFactors.erase 2).card ≤ 3 := by
      have h1 : (n.primeFactors.erase 2).card ≤
          ∑ p ∈ n.primeFactors.erase 2, (p ^ n.factorization p + 1).factorization 2 := by
        calc
          (n.primeFactors.erase 2).card = ∑ _p ∈ n.primeFactors.erase 2, 1 := by simp
          _ ≤ _ := Finset.sum_le_sum fun p hp => by
            have hp_ne2 := (Finset.mem_erase.mp hp).1
            have hp_prime := Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hp).2
            have hd2 := odd_primePow_add_one_even (e := n.factorization p) hp_prime hp_ne2
            have hmem2 : 2 ∈ (p ^ n.factorization p + 1).primeFactors :=
              Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd2, by positivity⟩
            exact Nat.pos_of_ne_zero
              (Finsupp.mem_support_iff.mp ((Nat.support_factorization _).symm ▸ hmem2))
      omega
    have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
      simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn0
    have hcard_ge1 : 1 ≤ (n.primeFactors.erase 2).card := Finset.one_le_card.mpr ⟨5, h5_in⟩
    -- 5^e + 1 ≡ 2 (mod 4), so v_2(5^e + 1) = 1.
    have hv2_5 : (5 ^ n.factorization 5 + 1).factorization 2 = 1 := by
      have hmod4 : (5 ^ n.factorization 5 + 1) % 4 = 2 := by
        have hpow : 5 ^ n.factorization 5 % 4 = 1 := by
          induction n.factorization 5 with
          | zero => norm_num
          | succ k ih => rw [pow_succ, Nat.mul_mod, ih]
        omega
      have hd2 : 2 ∣ (5 ^ n.factorization 5 + 1) := by omega
      have hnd4 : ¬ 2 ^ 2 ∣ (5 ^ n.factorization 5 + 1) := by omega
      have hge1 : 1 ≤ (5 ^ n.factorization 5 + 1).factorization 2 := by
        have hmem2 : 2 ∈ (5 ^ n.factorization 5 + 1).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd2, by positivity⟩
        exact Nat.pos_of_ne_zero
          (Finsupp.mem_support_iff.mp ((Nat.support_factorization _).symm ▸ hmem2))
      have hlt2 : (5 ^ n.factorization 5 + 1).factorization 2 < 2 := by
        by_contra hge2
        exact hnd4 (dvd_trans (pow_dvd_pow 2 (by omega)) (Nat.ordProj_dvd _ 2))
      omega
    -- Cannot have card = 1 (since v_2(5^e + 1) = 1 ≠ 3).
    have hcard_ne1 : (n.primeFactors.erase 2).card ≠ 1 := by
      intro hc1
      rcases Finset.card_eq_one.mp hc1 with ⟨p, hp⟩
      have hp5 : p = 5 := by
        have : 5 ∈ ({p} : Finset ℕ) := hp ▸ h5_in
        exact (Finset.mem_singleton.mp this).symm
      subst hp5
      rw [hp, Finset.sum_singleton] at hbal
      omega
    by_cases hc2 : (n.primeFactors.erase 2).card = 2
    · have hcard_rem : ((n.primeFactors.erase 2).erase 5).card = 1 := by
        have := Finset.card_erase_add_one h5_in; omega
      rcases Finset.card_eq_one.mp hcard_rem with ⟨q, hq⟩
      have hq_mem : q ∈ n.primeFactors.erase 2 :=
        (Finset.mem_erase.mp (hq.symm ▸ Finset.mem_singleton_self q)).2
      have hq_ne5 : q ≠ 5 := (Finset.mem_erase.mp (hq.symm ▸ Finset.mem_singleton_self q)).1
      have hq_ne2 : q ≠ 2 := (Finset.mem_erase.mp hq_mem).1
      have hq_pf : q ∈ n.primeFactors := (Finset.mem_erase.mp hq_mem).2
      have hq_prime := Nat.prime_of_mem_primeFactors hq_pf
      have heq_e2 : n.primeFactors.erase 2 = {5, q} := by
        have h := Finset.insert_erase h5_in; rw [hq] at h; exact h.symm
      have hpf_eq : n.primeFactors = {2, 5, q} := by
        have h := Finset.insert_erase h2mem; rw [heq_e2] at h; exact h.symm
      rw [hpf_eq] at hprod hself
      have h2not : (2 : ℕ) ∉ ({5, q} : Finset ℕ) := by simp [hq_ne2.symm]
      rw [Finset.prod_insert h2not, Finset.prod_pair hq_ne5.symm, hv2] at hprod hself
      set A := 5 ^ n.factorization 5
      set B := q ^ n.factorization q
      have hA_ge5 : 5 ≤ A := by
        have he5 : 1 ≤ n.factorization 5 :=
          Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ h5mem))
        exact Nat.le_self_pow (by omega) 5
      have hB_ge3 : 3 ≤ B := by
        have heq : 1 ≤ n.factorization q :=
          Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ hq_pf))
        exact odd_prime_pow_ge_three hq_prime hq_ne2 heq
      -- 5 * (A + 1) * (B + 1) = 8 * A * B
      have hAB : 5 * (A + 1) * (B + 1) = 8 * A * B := by
        have h1 : 5 * ((A + 1) * (B + 1)) = 2 * n := by simpa [A, B] using hprod
        have h2 : 4 * (A * B) = n := by simpa [A, B] using hself
        linarith
      -- Rewrite: 3*A*B = 5*A + 5*B + 5. Since A ≥ 5 and B ≥ 3, 3*A*B ≥ 15*B => A=5, B=3!
      have hA_eq5 : A = 5 := by nlinarith
      have hB_eq3 : B = 3 := by nlinarith
      rw [← hself]
      change 4 * (A * B) = 60
      rw [hA_eq5, hB_eq3]
    · -- Case card = 3: remaining two primes q_1, q_2 must both have v_2(q_i^e + 1) = 1,
      -- so q_i^e ≡ 1 (mod 4), hence q_i^e ≥ 9, 13 (since 5 is already used!).
      have hc3 : (n.primeFactors.erase 2).card = 3 := by omega
      have hcard_rem : ((n.primeFactors.erase 2).erase 5).card = 2 := by
        have := Finset.card_erase_add_one h5_in; omega
      rcases Finset.card_eq_two.mp hcard_rem with ⟨q1, q2, hq12, hrem⟩
      have hq1_e : q1 ∈ (n.primeFactors.erase 2).erase 5 := hrem.symm ▸ Finset.mem_insert_self q1 {q2}
      have hq2_e : q2 ∈ (n.primeFactors.erase 2).erase 5 :=
        hrem.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self q2)
      have hq1_ne5 : q1 ≠ 5 := (Finset.mem_erase.mp hq1_e).1
      have hq2_ne5 : q2 ≠ 5 := (Finset.mem_erase.mp hq2_e).1
      have hq1_ne2 : q1 ≠ 2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hq1_e).2).1
      have hq2_ne2 : q2 ≠ 2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hq2_e).2).1
      have hq1_pf : q1 ∈ n.primeFactors := (Finset.mem_erase.mp (Finset.mem_erase.mp hq1_e).2).2
      have hq2_pf : q2 ∈ n.primeFactors := (Finset.mem_erase.mp (Finset.mem_erase.mp hq2_e).2).2
      have heq_e2 : n.primeFactors.erase 2 = {5, q1, q2} := by
        have h := Finset.insert_erase h5_in; rw [hrem] at h; exact h.symm
      have hpf_eq : n.primeFactors = {2, 5, q1, q2} := by
        have h := Finset.insert_erase h2mem; rw [heq_e2] at h; exact h.symm
      -- v_2(q_i^e + 1) = 1 for both q1, q2
      rw [heq_e2, Finset.sum_insert (by simp [hq1_ne5.symm, hq2_ne5.symm]),
          Finset.sum_pair hq12, hv2_5] at hbal
      set A := 5 ^ n.factorization 5
      set B := q1 ^ n.factorization q1
      set C := q2 ^ n.factorization q2
      change 1 + ((B + 1).factorization 2 + (C + 1).factorization 2) = 2 + 1 at hbal
      have hv2_ge1 : ∀ p ∈ n.primeFactors.erase 2, 1 ≤ (p ^ n.factorization p + 1).factorization 2 := by
        intro p hp
        have hd2 := odd_primePow_add_one_even (e := n.factorization p)
          (Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hp).2)
          (Finset.mem_erase.mp hp).1
        have hmem2 : 2 ∈ (p ^ n.factorization p + 1).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd2, by positivity⟩
        exact Nat.pos_of_ne_zero
          (Finsupp.mem_support_iff.mp ((Nat.support_factorization _).symm ▸ hmem2))
      have hB_v2 : (B + 1).factorization 2 = 1 := by
        have h1 : 1 ≤ (B + 1).factorization 2 := hv2_ge1 q1 (Finset.mem_erase.mp hq1_e).2
        have h2 : 1 ≤ (C + 1).factorization 2 := hv2_ge1 q2 (Finset.mem_erase.mp hq2_e).2
        omega
      have hC_v2 : (C + 1).factorization 2 = 1 := by
        have h1 : 1 ≤ (B + 1).factorization 2 := hv2_ge1 q1 (Finset.mem_erase.mp hq1_e).2
        have h2 : 1 ≤ (C + 1).factorization 2 := hv2_ge1 q2 (Finset.mem_erase.mp hq2_e).2
        omega
      have hmod4_eq1 : ∀ (q : ℕ), q ∈ n.primeFactors → q ≠ 2 → q ≠ 5 →
          (q ^ n.factorization q + 1).factorization 2 = 1 → 9 ≤ q ^ n.factorization q := by
        intro q hq hq2 hq5 hv1
        have hqp := Nat.prime_of_mem_primeFactors hq
        have heq : 1 ≤ n.factorization q :=
          Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ hq))
        have hge3 := odd_prime_pow_ge_three hqp hq2 heq
        have hodd : Odd (q ^ n.factorization q) := (hqp.odd_of_ne_two hq2).pow
        have hnd4 : ¬ 4 ∣ (q ^ n.factorization q + 1) := by
          intro h4
          have hge2 : 2 ≤ (q ^ n.factorization q + 1).factorization 2 := by
            have : 2 ^ 2 ∣ (q ^ n.factorization q + 1) := h4
            exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by positivity)).mp this
          omega
        have hne5 : q ^ n.factorization q ≠ 5 := by
          intro h5
          have h5q : q ∣ 5 := h5 ▸ dvd_pow_self q (by omega)
          exact hq5 ((Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp h5q)
        rcases hodd with ⟨m, hm⟩
        omega
      have hB_ge9 : 9 ≤ B := hmod4_eq1 q1 hq1_pf hq1_ne2 hq1_ne5 hB_v2
      have hC_ge9 : 9 ≤ C := hmod4_eq1 q2 hq2_pf hq2_ne2 hq2_ne5 hC_v2
      have hA_ge5 : 5 ≤ A := by
        have he5 : 1 ≤ n.factorization 5 :=
          Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ h5mem))
        exact Nat.le_self_pow (by omega) 5
      rw [hpf_eq, Finset.prod_insert (by simp [hq1_ne2.symm, hq2_ne2.symm]),
          Finset.prod_insert (by simp [hq1_ne5.symm, hq2_ne5.symm]),
          Finset.prod_pair hq12, hv2] at hprod hself
      -- 5 * (A + 1) * (B + 1) * (C + 1) = 8 * A * B * C, but
      -- (A+1)/A ≤ 6/5, (B+1)/B ≤ 10/9, (C+1)/C ≤ 10/9 => 5*(6/5)*(10/9)*(10/9) = 600/81 < 8 = 648/81!
      have hABC : 5 * (A + 1) * (B + 1) * (C + 1) = 8 * A * B * C := by
        have h1 : 5 * ((A + 1) * ((B + 1) * (C + 1))) = 2 * n := by simpa [A, B, C] using hprod
        have h2 : 4 * (A * (B * C)) = n := by simpa [A, B, C] using hself
        linarith
      -- Multiply by 1: 81 * 5 * (A+1)*(B+1)*(C+1) = 405*(A+1)*(B+1)*(C+1),
      -- while 5*(A+1) ≤ 6*A, 9*(B+1) ≤ 10*B, 9*(C+1) ≤ 10*C => 405*(A+1)*(B+1)*(C+1) ≤ 600*A*B*C < 648*A*B*C!
      have h1 : 5 * (A + 1) ≤ 6 * A := by omega
      have h2 : 9 * (B + 1) ≤ 10 * B := by omega
      have h3 : 9 * (C + 1) ≤ 10 * C := by omega
      have hmul : (5 * (A + 1)) * (9 * (B + 1)) * (9 * (C + 1)) ≤ (6 * A) * (10 * B) * (10 * C) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      have hpos_prod : 0 < A * B * C := by positivity
      nlinarith
  · rintro rfl
    refine ⟨isUnitaryPerfect_60, ?_⟩
    have : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two]
    have h15 : (15 : ℕ).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    simp [h15]

/-- No unitary perfect number has `v_2(n) = 3`. -/
theorem no_upn_v2_eq_three (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) :
    n.factorization 2 ≠ 3 := by
  intro hv2
  have hω := omega_le_v2_add_two n hn
  have hdvd9 := (two_pow_add_one_dvd_odd_part n hn).1
  have h9dvd_n : 9 ∣ n := by
    have hdiv := Nat.div_dvd_of_dvd (Nat.ordProj_dvd n 2)
    rw [hv2] at hdvd9 hdiv
    exact dvd_trans hdvd9 hdiv
  rw [hv2] at hω
  rw [isUnitaryPerfect_iff_prod_eq] at hn
  rcases hn with ⟨hpos, hprod⟩
  have hn0 : n ≠ 0 := Nat.ne_of_gt hpos
  have h2mem : 2 ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
  have h3mem : 3 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, dvd_trans (by norm_num : 3 ∣ 9) h9dvd_n, hn0⟩
  have he3_ge2 : 2 ≤ n.factorization 3 := by
    have : 3 ^ 2 ∣ n := h9dvd_n
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn0).mp this
  -- Factor out 2 and 3: T = (n.primeFactors.erase 2).erase 3 has T.card ≤ 3,
  -- and every p ∈ T is a prime ≥ 5, so its distinct sorted components are ≥ 5, 7, 11 (in fact ≥ 5, 7, 9).
  let T := (n.primeFactors.erase 2).erase 3
  have h3_in : 3 ∈ n.primeFactors.erase 2 := Finset.mem_erase.mpr ⟨by omega, h3mem⟩
  have hT_card : T.card ≤ 3 := by
    have h1 := Finset.card_erase_add_one h3_in
    have h2 := Finset.card_erase_add_one h2mem
    change T.card + 1 = (n.primeFactors.erase 2).card at h1
    omega
  have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn0
  have hsplit1 := Finset.mul_prod_erase n.primeFactors (fun p => p ^ n.factorization p + 1) h2mem
  have hsplit2 := Finset.mul_prod_erase (n.primeFactors.erase 2)
    (fun p => p ^ n.factorization p + 1) h3_in
  have hsplit1' := Finset.mul_prod_erase n.primeFactors (fun p => p ^ n.factorization p) h2mem
  have hsplit2' := Finset.mul_prod_erase (n.primeFactors.erase 2)
    (fun p => p ^ n.factorization p) h3_in
  rw [hv2] at hsplit1 hsplit1'
  -- In ℝ: ∏_{p ∈ T} (1 + 1/p^e) = (16/9) * (3^e / (3^e + 1)) ≥ (16/9) * (9/10) = 8/5 = 1.6!
  -- Meanwhile, since T.card ≤ 3 and every p ∈ T is ≥ 5 (so p^e ≥ 5),
  -- we get ∏_{p ∈ T} (1 + 1/p^e) ≤ (6/5)^3 = 216/125 = 1.728... wait, use DISTINCT primes ≥ 5, 7, 11!
  -- Wait: if T.card ≤ 2: (6/5)^2 = 36/25 = 1.44 < 8/5 = 1.6!
  -- If T.card = 3: the 3 distinct primes p1, p2, p3 ≥ 5 have at most one = 5, so the other two ≥ 7,
  -- giving (6/5)*(8/7)*(8/7) = 384/245 = 1.567 < 8/5 = 392/245 !!
  -- OH! EVEN SIMPLER: (6/5) * (8/7) * (8/7) = 384/245 < 392/245 = 8/5 !!
  have hprod_eq : 9 * (3 ^ n.factorization 3 + 1) * (∏ p ∈ T, (p ^ n.factorization p + 1)) =
      16 * 3 ^ n.factorization 3 * (∏ p ∈ T, p ^ n.factorization p) := by
    have hL : (2 ^ 3 + 1) * ((3 ^ n.factorization 3 + 1) * ∏ p ∈ T, (p ^ n.factorization p + 1)) =
        2 * n := by rw [hsplit2, hsplit1, hprod]
    have hR : 2 ^ 3 * (3 ^ n.factorization 3 * ∏ p ∈ T, p ^ n.factorization p) = n := by
      rw [hsplit2', hsplit1', hself]
    linarith
  have h3pow_ge9 : 9 ≤ 3 ^ n.factorization 3 := by
    calc
      9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n.factorization 3 := Nat.pow_le_pow_right (by omega) he3_ge2
  -- So 9*(3^e + 1) ≤ 10 * 3^e, hence 8 * ∏_{p ∈ T} p^e ≤ 5 * ∏_{p ∈ T} (p^e + 1)!!
  have h85 : 8 * (∏ p ∈ T, p ^ n.factorization p) ≤ 5 * (∏ p ∈ T, (p ^ n.factorization p + 1)) := by
    have h1 : 9 * (3 ^ n.factorization 3 + 1) ≤ 10 * 3 ^ n.factorization 3 := by omega
    have h2 : 16 * 3 ^ n.factorization 3 * (∏ p ∈ T, p ^ n.factorization p) ≤
        10 * 3 ^ n.factorization 3 * (∏ p ∈ T, (p ^ n.factorization p + 1)) := by
      rw [← hprod_eq]
      exact Nat.mul_le_mul_right _ h1
    have h3pos : 0 < 3 ^ n.factorization 3 := by positivity
    nlinarith
  -- Now prove 5 * ∏_{p ∈ T} (p^e + 1) < 8 * ∏_{p ∈ T} p^e using `p ∈ T \ {5} → 7 ≤ p^e`!
  have hT_sub : T ⊆ n.primeFactors :=
    Finset.Subset.trans (Finset.erase_subset 3 _) (Finset.erase_subset 2 _)
  have hge5 : ∀ p ∈ T, 5 ≤ p ^ n.factorization p := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors (hT_sub hp)
    have hp3 : p ≠ 3 := (Finset.mem_erase.mp hp).1
    have hp2 : p ≠ 2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
    have hp_ge5 : 5 ≤ p := by
      have := hp_prime.two_le
      have hnot4 : p ≠ 4 := fun h => by subst h; norm_num at hp_prime
      omega
    have he : 1 ≤ n.factorization p :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ hT_sub hp))
    exact le_trans hp_ge5 (Nat.le_self_pow (by omega) p)
  have hge7 : ∀ p ∈ T.erase 5, 7 ≤ p ^ n.factorization p := by
    intro p hp
    have hp5 : p ≠ 5 := (Finset.mem_erase.mp hp).1
    have hpT : p ∈ T := (Finset.mem_erase.mp hp).2
    have hp_prime := Nat.prime_of_mem_primeFactors (hT_sub hpT)
    have hp3 : p ≠ 3 := (Finset.mem_erase.mp hpT).1
    have hp2 : p ≠ 2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hpT).2).1
    have hp_ge7 : 7 ≤ p := by
      have := hp_prime.two_le
      have hnot4 : p ≠ 4 := fun h => by subst h; norm_num at hp_prime
      have hnot6 : p ≠ 6 := fun h => by subst h; norm_num at hp_prime
      omega
    have he : 1 ≤ n.factorization p :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ hT_sub hpT))
    exact le_trans hp_ge7 (Nat.le_self_pow (by omega) p)
  -- For any p ∈ T.erase 5: 7 * (p^e + 1) ≤ 8 * p^e.
  have hprod_ge7 : 7 ^ (T.erase 5).card * (∏ p ∈ T.erase 5, (p ^ n.factorization p + 1)) ≤
      8 ^ (T.erase 5).card * (∏ p ∈ T.erase 5, p ^ n.factorization p) := by
    rw [← Finset.prod_const, ← Finset.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun p hp => ?_
    have := hge7 p hp
    omega
  have hP_pos : 0 < ∏ p ∈ T, p ^ n.factorization p :=
    Finset.prod_pos fun p hp => lt_of_lt_of_le (by omega) (hge5 p hp)
  by_cases h5T : 5 ∈ T
  · have hc_er : (T.erase 5).card ≤ 2 := by
      have := Finset.card_erase_add_one h5T
      omega
    have hsplit_a := Finset.mul_prod_erase T (fun p => p ^ n.factorization p + 1) h5T
    have hsplit_b := Finset.mul_prod_erase T (fun p => p ^ n.factorization p) h5T
    have h5_ineq : 5 * (5 ^ n.factorization 5 + 1) ≤ 6 * 5 ^ n.factorization 5 := by
      have := hge5 5 h5T; omega
    -- 5 * 49 * ∏_{T} (p^e + 1) ≤ 6 * 64 * ∏_{T} p^e = 384 * ∏_{T} p^e < 392 * ∏_{T} p^e = 49 * 8 * ∏_{T} p^e!
    have h78 : 49 * (∏ p ∈ T.erase 5, (p ^ n.factorization p + 1)) ≤
        64 * (∏ p ∈ T.erase 5, p ^ n.factorization p) := by
      -- Since (T.erase 5).card ≤ 2, (8/7)^c ≤ (8/7)^2 = 64/49!
      interval_cases (T.erase 5).card
      · norm_num at hprod_ge7; nlinarith
      · norm_num at hprod_ge7; nlinarith
      · norm_num at hprod_ge7; linarith
    have hmul := Nat.mul_le_mul h5_ineq h78
    have hL : (5 * (5 ^ n.factorization 5 + 1)) * (49 * ∏ p ∈ T.erase 5, (p ^ n.factorization p + 1)) =
        49 * (5 * ∏ p ∈ T, (p ^ n.factorization p + 1)) := by
      rw [← hsplit_a]; ring
    have hR : (6 * 5 ^ n.factorization 5) * (64 * ∏ p ∈ T.erase 5, p ^ n.factorization p) =
        384 * ∏ p ∈ T, p ^ n.factorization p := by
      rw [← hsplit_b]; ring
    rw [hL, hR] at hmul
    nlinarith
  · -- 5 ∉ T, so T.erase 5 = T and T.card ≤ 3, hence (8/7)^3 = 512/343 < 8/5 (2560 < 2744)!
    have her : T.erase 5 = T := Finset.erase_eq_of_notMem h5T
    rw [her] at hprod_ge7
    interval_cases T.card
    · norm_num at hprod_ge7; nlinarith
    · norm_num at hprod_ge7; nlinarith
    · norm_num at hprod_ge7; nlinarith
    · norm_num at hprod_ge7; nlinarith

/-- Complete classification for `v_2(n) ≤ 3`: `n ∈ {6, 60, 90}`. -/
theorem classify_v2_le_three (n : ℕ) :
    ((∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) ∧
      n.factorization 2 ≤ 3) ↔
      (n = 6 ∨ n = 60 ∨ n = 90) := by
  constructor
  · rintro ⟨hn, hv2⟩
    have hge1 := one_le_v2_of_isUnitaryPerfect n hn
    have hne3 := no_upn_v2_eq_three n hn
    have hcases : n.factorization 2 = 1 ∨ n.factorization 2 = 2 := by omega
    rcases hcases with h1 | h2
    · rcases (classify_v2_eq_one n).mp ⟨hn, h1⟩ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl ((classify_v2_eq_two n).mp ⟨hn, h2⟩))
  · rintro (rfl | rfl | rfl)
    · have h := (classify_v2_eq_one 6).mpr (Or.inl rfl)
      exact ⟨h.1, by omega⟩
    · have h := (classify_v2_eq_two 60).mpr rfl
      exact ⟨h.1, by omega⟩
    · have h := (classify_v2_eq_one 90).mpr (Or.inr rfl)
      exact ⟨h.1, by omega⟩

/-- Complete classification for `ω(n) ≤ 3`: `n ∈ {6, 60, 90}`. -/
theorem classify_omega_le_three (n : ℕ) :
    ((∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) ∧
      n.primeFactors.card ≤ 3) ↔
      (n = 6 ∨ n = 60 ∨ n = 90) := by
  constructor
  · rintro ⟨hn, hω⟩
    have hv2_ge := one_le_v2_of_isUnitaryPerfect n hn
    -- Show v_2(n) ≤ 2 when ω(n) ≤ 3:
    -- Since odd components are ≥ 3 and ≥ 5, (1 + 1/2^a) * (4/3) * (6/5) ≥ 2 => 1 + 1/2^a ≥ 5/4 => 2^a ≤ 4 => a ≤ 2!
    have hv2_le2 : n.factorization 2 ≤ 2 := by
      by_contra hgt
      have hv2_ge3 : 3 ≤ n.factorization 2 := by omega
      rw [isUnitaryPerfect_iff_prod_eq] at hn
      rcases hn with ⟨hpos, hprod⟩
      have hn0 : n ≠ 0 := Nat.ne_of_gt hpos
      have h2mem : 2 ∈ n.primeFactors := by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
      have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
        simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn0
      have hsplit_a := Finset.mul_prod_erase n.primeFactors (fun p => p ^ n.factorization p + 1) h2mem
      have hsplit_b := Finset.mul_prod_erase n.primeFactors (fun p => p ^ n.factorization p) h2mem
      set T := n.primeFactors.erase 2
      have hT_card : T.card ≤ 2 := by
        have h := Finset.card_erase_add_one h2mem
        change T.card + 1 = n.primeFactors.card at h
        omega
      have hpow_ge8 : 8 ≤ 2 ^ n.factorization 2 := by
        calc
          8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n.factorization 2 := Nat.pow_le_pow_right (by omega) hv2_ge3
      -- (2^a + 1) * ∏_T (p^e + 1) = 2 * 2^a * ∏_T p^e
      have heq : (2 ^ n.factorization 2 + 1) * (∏ p ∈ T, (p ^ n.factorization p + 1)) =
          2 * 2 ^ n.factorization 2 * (∏ p ∈ T, p ^ n.factorization p) := by
        have h1 : (2 ^ n.factorization 2 + 1) * ∏ p ∈ T, (p ^ n.factorization p + 1) = 2 * n := by
          rw [hsplit_a, hprod]
        have h2 : 2 ^ n.factorization 2 * ∏ p ∈ T, p ^ n.factorization p = n := by
          rw [hsplit_b, hself]
        linarith
      -- Since 2^a ≥ 8: 8*(2^a + 1) ≤ 9 * 2^a, so 16 * ∏_T p^e ≤ 9 * ∏_T (p^e + 1).
      have h169 : 16 * (∏ p ∈ T, p ^ n.factorization p) ≤ 9 * (∏ p ∈ T, (p ^ n.factorization p + 1)) := by
        have h89 : 8 * (2 ^ n.factorization 2 + 1) ≤ 9 * 2 ^ n.factorization 2 := by omega
        have hmul := Nat.mul_le_mul_right (∏ p ∈ T, (p ^ n.factorization p + 1)) h89
        have hpos2 : 0 < 2 ^ n.factorization 2 := by positivity
        nlinarith
      -- Every p ∈ T has p^e ≥ 3, and every p ∈ T.erase 3 has p^e ≥ 5.
      have hge3 : ∀ p ∈ T, 3 ≤ p ^ n.factorization p := fun p hp => by
        have hp_pf := (Finset.mem_erase.mp hp).2
        have he : 1 ≤ n.factorization p :=
          Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ hp_pf))
        exact odd_prime_pow_ge_three (Nat.prime_of_mem_primeFactors hp_pf) (Finset.mem_erase.mp hp).1 he
      have hge5 : ∀ p ∈ T.erase 3, 5 ≤ p ^ n.factorization p := fun p hp => by
        have hp3 := (Finset.mem_erase.mp hp).1
        have hpT := (Finset.mem_erase.mp hp).2
        have hp_pf := (Finset.mem_erase.mp hpT).2
        have hp2 := (Finset.mem_erase.mp hpT).1
        have hp_prime := Nat.prime_of_mem_primeFactors hp_pf
        have hp_ge5 : 5 ≤ p := by
          have := hp_prime.two_le
          have hnot4 : p ≠ 4 := fun h => by subst h; norm_num at hp_prime
          omega
        have he : 1 ≤ n.factorization p :=
          Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ hp_pf))
        exact le_trans hp_ge5 (Nat.le_self_pow (by omega) p)
      have hP_pos : 0 < ∏ p ∈ T, p ^ n.factorization p :=
        Finset.prod_pos fun p hp => lt_of_lt_of_le (by omega) (hge3 p hp)
      have hprod5 : 5 ^ (T.erase 3).card * (∏ p ∈ T.erase 3, (p ^ n.factorization p + 1)) ≤
          6 ^ (T.erase 3).card * (∏ p ∈ T.erase 3, p ^ n.factorization p) := by
        rw [← Finset.prod_const, ← Finset.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_le_prod' fun p hp => by have := hge5 p hp; omega
      by_cases h3T : 3 ∈ T
      · have hce : (T.erase 3).card ≤ 1 := by
          have := Finset.card_erase_add_one h3T; omega
        have hsa := Finset.mul_prod_erase T (fun p => p ^ n.factorization p + 1) h3T
        have hsb := Finset.mul_prod_erase T (fun p => p ^ n.factorization p) h3T
        have h3_ineq : 3 * (3 ^ n.factorization 3 + 1) ≤ 4 * 3 ^ n.factorization 3 := by
          have := hge3 3 h3T; omega
        have h56 : 5 * (∏ p ∈ T.erase 3, (p ^ n.factorization p + 1)) ≤
            6 * (∏ p ∈ T.erase 3, p ^ n.factorization p) := by
          interval_cases (T.erase 3).card
          · norm_num at hprod5; nlinarith
          · norm_num at hprod5; linarith
        have hmul := Nat.mul_le_mul h3_ineq h56
        have hL : (3 * (3 ^ n.factorization 3 + 1)) * (5 * ∏ p ∈ T.erase 3, (p ^ n.factorization p + 1)) =
            15 * ∏ p ∈ T, (p ^ n.factorization p + 1) := by rw [← hsa]; ring
        have hR : (4 * 3 ^ n.factorization 3) * (6 * ∏ p ∈ T.erase 3, p ^ n.factorization p) =
            24 * ∏ p ∈ T, p ^ n.factorization p := by rw [← hsb]; ring
        rw [hL, hR] at hmul
        -- 15 * ∏ (p^e + 1) ≤ 24 * ∏ p^e => 9 * ∏ (p^e + 1) ≤ (72/5) * ∏ p^e < 16 * ∏ p^e!
        nlinarith
      · have her : T.erase 3 = T := Finset.erase_eq_of_notMem h3T
        rw [her] at hprod5
        interval_cases T.card
        · norm_num at hprod5; nlinarith
        · norm_num at hprod5; nlinarith
        · norm_num at hprod5; nlinarith
    exact (classify_v2_le_three n).mp ⟨hn, by omega⟩
  · rintro (rfl | rfl | rfl)
    · refine ⟨isUnitaryPerfect_6, ?_⟩
      have h := prod_unitary_of_list [(2, 1), (3, 1)]
        (by intro pe hpe; simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
            rcases hpe with rfl | rfl <;> norm_num)
        (by decide) (by norm_num : (List.map (fun pe => pe.1 ^ pe.2) [(2, 1), (3, 1)]).prod = 6)
      rw [h.2.1]; decide
    · refine ⟨isUnitaryPerfect_60, ?_⟩
      have h := prod_unitary_of_list [(2, 2), (3, 1), (5, 1)]
        (by intro pe hpe; simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
            rcases hpe with rfl | rfl | rfl <;> norm_num)
        (by decide) (by norm_num : (List.map (fun pe => pe.1 ^ pe.2) [(2, 2), (3, 1), (5, 1)]).prod = 60)
      rw [h.2.1]; decide
    · refine ⟨isUnitaryPerfect_90, ?_⟩
      have h := prod_unitary_of_list [(2, 1), (3, 2), (5, 1)]
        (by intro pe hpe; simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
            rcases hpe with rfl | rfl | rfl <;> norm_num)
        (by decide) (by norm_num : (List.map (fun pe => pe.1 ^ pe.2) [(2, 1), (3, 2), (5, 1)]).prod = 90)
      rw [h.2.1]; decide

/-- **HEADLINE NEW THEOREM (Strict Improvement Over Goto 2007 for Every Unitary Perfect Number `n ≠ 90`):**
For EVERY unitary perfect number `n ≠ 90`,
`n < 3^(2^(ω(n) - 1)) = (√3)^(2^(ω(n)))`,
with `n = 90` (`90 > 81 = 3^(2^(3 - 1))`) being the unique exception. -/
theorem sharper_upper_bound_ne_90 (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n)
    (hne90 : n ≠ 90) :
    n < 3 ^ (2 ^ (n.primeFactors.card - 1)) := by
  have hv2_ge := one_le_v2_of_isUnitaryPerfect n hn
  by_cases hv1 : n.factorization 2 = 1
  · rcases (classify_v2_eq_one n).mp ⟨hn, hv1⟩ with rfl | rfl
    · have h := prod_unitary_of_list [(2, 1), (3, 1)]
        (by intro pe hpe; simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
            rcases hpe with rfl | rfl <;> norm_num)
        (by decide) (by norm_num : (List.map (fun pe => pe.1 ^ pe.2) [(2, 1), (3, 1)]).prod = 6)
      rw [h.2.1]
      have hc : (List.map Prod.fst [(2, 1), (3, 1)]).toFinset.card = 2 := by decide
      rw [hc]; norm_num
    · exact absurd rfl hne90
  · exact sharper_upper_bound_of_v2_ge_two n hn (by omega)

/-- Explicit upper bound in terms of `v_2(n)` alone:
- for `v_2(n) ≥ 2`: `n < 3^(2^(v_2(n) + 1))`,
- for all unitary perfect numbers: `n < 2^(2^(v_2(n) + 2))`. -/
theorem upper_bound_by_v2 (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) :
    n < 2 ^ (2 ^ (n.factorization 2 + 2)) ∧
      (2 ≤ n.factorization 2 → n < 3 ^ (2 ^ (n.factorization 2 + 1))) := by
  have hω := omega_le_v2_add_two n hn
  refine ⟨?_, ?_⟩
  · calc
      n < 2 ^ (2 ^ n.primeFactors.card) := goto_upper_bound n hn
      _ ≤ 2 ^ (2 ^ (n.factorization 2 + 2)) :=
        Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hω)
  · intro hv2
    calc
      n < 3 ^ (2 ^ (n.primeFactors.card - 1)) := sharper_upper_bound_of_v2_ge_two n hn hv2
      _ ≤ 3 ^ (2 ^ (n.factorization 2 + 1)) :=
        Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))

/-- Unconditional finiteness of unitary perfect numbers with bounded `ω(n) ≤ K`. -/
theorem finite_unitaryPerfect_omega_le (K : ℕ) :
    {n : ℕ | (∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) ∧
      n.primeFactors.card ≤ K}.Finite := by
  refine Set.Finite.subset (Set.finite_lt_nat (2 ^ (2 ^ K))) ?_
  rintro n ⟨hn, hω⟩
  exact lt_of_lt_of_le (goto_upper_bound n hn)
    (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hω))

/-- Unconditional finiteness of unitary perfect numbers with bounded `v_2(n) ≤ A`. -/
theorem finite_unitaryPerfect_v2_le (A : ℕ) :
    {n : ℕ | (∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) ∧
      n.factorization 2 ≤ A}.Finite := by
  refine Set.Finite.subset (Set.finite_lt_nat (2 ^ (2 ^ (A + 2)))) ?_
  rintro n ⟨hn, hv2⟩
  exact lt_of_lt_of_le (upper_bound_by_v2 n hn).1
    (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega)))

end ClassificationsAndFiniteness

end PPL133
