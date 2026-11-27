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
import RHDirect.PPL133_Main

set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

/-!
# PPL 133 (Erdős Problem #1052 — Unitary Perfect Numbers `A002827`):
# Unconditional `√2` Double-Exponential Upper Bound `n < 2^(2^(ω(n)-1))`
# and Complete `ω(n) ≤ 5` Classification

**Scope Notice (New Unconditional World-Record Bound & Classification — Full Finiteness Open):**
Erdős Problem #1052 (`erdosproblems.com/1052`, Guy Problem B3) asks whether there are only
finitely many unitary perfect numbers (OEIS `A002827`). The full finiteness conjecture remains
**OPEN**.

Building on `RHDirect.PPL133_Main` (`3^(2^(ω(n)-1))` for `n ≠ 90`), this module establishes on
pure Mathlib (`0` `sorry`, `0` custom axioms, `0` `native_decide`):

1. **Complete `ω(n) ≤ 5` Classification (`omega_ne_four`, `classify_omega_eq_five`,
   `classify_omega_le_five`):**
   - There is **no** unitary perfect number with `ω(n) = 4`.
   - `n = 87360` is the **unique** unitary perfect number with `ω(n) = 5`.
   - Consequently, `{n | IsUPN n ∧ ω(n) ≤ 5} = {6, 60, 90, 87360}`.
2. **New Unconditional `√2` Upper Bound (`sqrt_two_upper_bound_of_omega_ge_six`,
   `sqrt_two_upper_bound_ne_small`, `sqrt_two_upper_bound_gt_87360`):**
   - For **every** unitary perfect number `n` with `ω(n) ≥ 6` (equivalently `n ∉ {6, 60, 90, 87360}`,
     or `n > 87360`),
     `n < 2^(2^(ω(n) - 1)) = (√2)^(2^(ω(n)))`,
     cutting the double-exponential base from Goto (2007)'s `2` and `PPL133_Main`'s `√3 ≈ 1.73205`
     down to `√2 ≈ 1.41421` (literally halving Goto's exponent).
-/

namespace PPL133_SqrtTwo

/-! ## Section 1: Strengthened Prime-Power Decomposition & Gap Lemmas -/

section PrimePowerGaps

/-- An integer divisible by two distinct primes cannot be a prime power `p^e`. -/
private lemma not_prime_pow_of_two_primes {q₁ q₂ m p e : ℕ}
    (hq₁ : Nat.Prime q₁) (hq₂ : Nat.Prime q₂) (hne : q₁ ≠ q₂)
    (hd₁ : q₁ ∣ m) (hd₂ : q₂ ∣ m) (hp : Nat.Prime p) (hpe : p ^ e = m) : False := by
  subst hpe
  have h1 : q₁ = p := (Nat.prime_dvd_prime_iff_eq hq₁ hp).mp (hq₁.dvd_of_dvd_pow hd₁)
  have h2 : q₂ = p := (Nat.prime_dvd_prime_iff_eq hq₂ hp).mp (hq₂.dvd_of_dvd_pow hd₂)
  exact hne (h1.trans h2.symm)

private lemma finset_prod_range_eq_list_prod (m : ℕ) (g : ℕ → ℕ) :
    ∏ i ∈ Finset.range m, g i = ((List.range m).map g).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, List.range_succ, List.map_append, List.prod_append, ih]
    simp

private lemma odd_primePow_add_one_even {p e : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    2 ∣ (p ^ e + 1) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpow : Odd (p ^ e) := hodd.pow
  rcases hpow with ⟨k, hk⟩
  exact ⟨k + 1, by omega⟩

/-- Strengthened sorted prime-power component decomposition for a UPN `n` with `v_2(n) ≥ 4`,
exposing both the strictly increasing components `x_i` and their distinct prime bases `p_i`. -/
private lemma sorted_primePow_components_of_upn (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n)
    (hv2 : 4 ≤ n.factorization 2) :
    let k := n.primeFactors.card
    ∃ (x p e : ℕ → ℕ),
      2 ≤ k ∧
      (∀ i j, i < j → j < k → x i < x j) ∧
      (∀ i j, i ≤ j → j < k → x i ≤ x j) ∧
      (∀ i < k, Nat.Prime (p i) ∧ 1 ≤ e i ∧ x i = (p i) ^ (e i) + 1) ∧
      (∀ i j, i < k → j < k → i ≠ j → p i ≠ p j) ∧
      (∀ i < k, p i = 2 → 4 ≤ e i) ∧
      (∀ i < k, p i ≠ 2 → Even (x i)) ∧
      (∏ i ∈ Finset.range k, x i = 2 * n) ∧
      (∏ i ∈ Finset.range k, (x i - 1) = n) ∧
      (∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) = (1 : ℝ) / 2) := by
  intro k
  rw [PPL133.isUnitaryPerfect_iff_prod_eq] at hn
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
    rcases Finset.card_eq_one.mp hcard1 with ⟨q, hq⟩
    have hq2 : q = 2 := by
      have : 2 ∈ ({q} : Finset ℕ) := hq ▸ h2mem
      exact (Finset.mem_singleton.mp this).symm
    subst hq2
    have hself : ∏ r ∈ n.primeFactors, r ^ n.factorization r = n := by
      simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn0
    have hge2 : 2 ≤ 2 ^ n.factorization 2 := Nat.le_self_pow (by omega) 2
    rw [hq, Finset.prod_singleton] at hprod hself
    omega
  let f : ℕ → ℕ := fun q => q ^ n.factorization q + 1
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
  have hx_lt : ∀ i j, i < j → j < k → x i < x j := by
    intro i j hij hj
    have hiL : i < L.length := by omega
    have hjL : j < L.length := by omega
    have hgi : x i = L[i]'hiL := by simp [x, List.getD_eq_getElem?_getD, hiL]
    have hgj : x j = L[j]'hjL := by simp [x, List.getD_eq_getElem?_getD, hjL]
    have hle : x i ≤ x j := by
      rw [hgi, hgj]
      exact List.pairwise_iff_getElem.mp hL_sorted i j hiL hjL hij
    have hne : x i ≠ x j := by
      rw [hgi, hgj]
      intro heq
      have hfin : (⟨i, hiL⟩ : Fin L.length) = ⟨j, hjL⟩ :=
        (List.nodup_iff_injective_getElem.mp hL_nodup) heq
      simp only [Fin.mk.injEq] at hfin
      omega
    omega
  have hx_mono : ∀ i j, i ≤ j → j < k → x i ≤ x j := by
    intro i j hij hj
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · exact le_of_lt (hx_lt i j hlt hj)
  have hx_ex : ∀ i < k, ∃ q ∈ n.primeFactors, q ^ n.factorization q + 1 = x i := by
    intro i hi
    exact Finset.mem_image.mp (hx_mem i hi)
  let p : ℕ → ℕ := fun i => if hi : i < k then Classical.choose (hx_ex i hi) else 2
  let e : ℕ → ℕ := fun i => n.factorization (p i)
  have hp_mem : ∀ i (hi : i < k), p i ∈ n.primeFactors := fun i hi => by
    simp only [p, hi, ↓reduceDIte]
    exact (Classical.choose_spec (hx_ex i hi)).1
  have hp_eq : ∀ i (hi : i < k), (p i) ^ (e i) + 1 = x i := fun i hi => by
    simp only [e, p, hi, ↓reduceDIte]
    exact (Classical.choose_spec (hx_ex i hi)).2
  have hp_info : ∀ i < k, Nat.Prime (p i) ∧ 1 ≤ e i ∧ x i = (p i) ^ (e i) + 1 := by
    intro i hi
    have hmem := hp_mem i hi
    refine ⟨Nat.prime_of_mem_primeFactors hmem, ?_, (hp_eq i hi).symm⟩
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Nat.support_factorization n).symm ▸ hmem))
  have hp_inj : ∀ i j, i < k → j < k → i ≠ j → p i ≠ p j := by
    intro i j hi hj hne heq
    have h1 := (hp_info i hi).2.2
    have h2 := (hp_info j hj).2.2
    have hxe : x i = x j := by
      rw [h1, h2]
      dsimp only [e]
      rw [heq]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd hxe (ne_of_lt (hx_lt i j hlt hj))
    · exact absurd hxe.symm (ne_of_lt (hx_lt j i hgt hi))
  have hp_two : ∀ i < k, p i = 2 → 4 ≤ e i := by
    intro i _ hpi
    dsimp only [e]
    rw [hpi]
    exact hv2
  have hp_even : ∀ i < k, p i ≠ 2 → Even (x i) := by
    intro i hi hne2
    rw [(hp_info i hi).2.2]
    exact even_iff_two_dvd.mpr (odd_primePow_add_one_even (hp_info i hi).1 hne2)
  have hprod_range_L : ∀ (g : ℕ → ℕ),
      ∏ i ∈ Finset.range k, g (x i) = ∏ y ∈ S, g y := by
    intro g
    have hL_prod : (L.map g).prod = ∏ y ∈ S, g y := by
      have hto : L.toFinset = S := by ext y; simp [L]
      rw [← hto, List.prod_toFinset _ hL_nodup]
    rw [← hL_prod]
    have hL_eq : L.map g = (List.range k).map (fun i => g (x i)) := by
      apply List.ext_getElem
      · simp [hL_len]
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range]
        have hiL : i < L.length := by simpa using h1
        simp [x, List.getD_eq_getElem?_getD, hiL]
    rw [hL_eq, ← finset_prod_range_eq_list_prod]
  have hx_prod : ∏ i ∈ Finset.range k, x i = 2 * n := by
    rw [hprod_range_L (fun y => y), Finset.prod_image (fun a ha b hb hab => hf_inj ha hb hab)]
    exact hprod
  have hx_sub_prod : ∏ i ∈ Finset.range k, (x i - 1) = n := by
    rw [hprod_range_L (fun y => y - 1), Finset.prod_image (fun a ha b hb hab => hf_inj ha hb hab)]
    have hself : ∏ q ∈ n.primeFactors, q ^ n.factorization q = n := by
      simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn0
    simpa [f] using hself
  have hx_rat : ∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) = (1 : ℝ) / 2 := by
    have hterm : ∀ i ∈ Finset.range k,
        (1 : ℝ) - 1 / (x i : ℝ) = ((x i - 1 : ℕ) : ℝ) / (x i : ℝ) := by
      intro i hi
      rcases hp_info i (Finset.mem_range.mp hi) with ⟨hp, he, hxi⟩
      have hpow : 2 ≤ (p i) ^ (e i) := le_trans hp.two_le (Nat.le_self_pow (by omega) (p i))
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
  exact ⟨x, p, e, hk2, hx_lt, hx_mono, hp_info, hp_inj, hp_two, hp_even,
    hx_prod, hx_sub_prod, hx_rat⟩

private lemma x_ge_four {k : ℕ} {x p e : ℕ → ℕ}
    (hp_info : ∀ i < k, Nat.Prime (p i) ∧ 1 ≤ e i ∧ x i = (p i) ^ (e i) + 1)
    (hp_two : ∀ i < k, p i = 2 → 4 ≤ e i)
    {i : ℕ} (hi : i < k) : 4 ≤ x i := by
  rcases hp_info i hi with ⟨hp, he, hxi⟩
  by_cases h2 : p i = 2
  · have h4 : 4 ≤ e i := hp_two i hi h2
    have : 2 ^ 4 ≤ (p i) ^ (e i) := by rw [h2]; exact Nat.pow_le_pow_right (by omega) h4
    omega
  · have hp3 : 3 ≤ p i := by have := hp.two_le; omega
    have : 3 ≤ (p i) ^ (e i) := le_trans hp3 (Nat.le_self_pow (by omega) (p i))
    omega

private lemma x_even_of_lt_17 {k : ℕ} {x p e : ℕ → ℕ}
    (hp_info : ∀ i < k, Nat.Prime (p i) ∧ 1 ≤ e i ∧ x i = (p i) ^ (e i) + 1)
    (hp_two : ∀ i < k, p i = 2 → 4 ≤ e i)
    (hp_even : ∀ i < k, p i ≠ 2 → Even (x i))
    {i : ℕ} (hi : i < k) (hlt : x i < 17) : Even (x i) := by
  by_cases h2 : p i = 2
  · exfalso
    have h4 : 4 ≤ e i := hp_two i hi h2
    have hxi := (hp_info i hi).2.2
    have h16 : 16 ≤ (p i) ^ (e i) := by
      rw [h2]
      exact le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by omega) h4)
    omega
  · exact hp_even i hi h2

private lemma x_ne_10_of_x0_eq_4 {k : ℕ} {x p e : ℕ → ℕ}
    (hk : 1 ≤ k)
    (hp_info : ∀ i < k, Nat.Prime (p i) ∧ 1 ≤ e i ∧ x i = (p i) ^ (e i) + 1)
    (hp_inj : ∀ i j, i < k → j < k → i ≠ j → p i ≠ p j)
    (hx0 : x 0 = 4) {i : ℕ} (hi0 : 0 < i) (hik : i < k) : x i ≠ 10 := by
  intro hxi10
  rcases hp_info 0 (by omega) with ⟨hp0, he0, hx0_eq⟩
  rcases hp_info i hik with ⟨hpi, hei, hxi_eq⟩
  have hp0_3 : p 0 = 3 := by
    have h3 : 3 = (p 0) ^ (e 0) := by omega
    have h3d : 3 ∣ (p 0) ^ (e 0) := ⟨1, by omega⟩
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp0).mp
      (Nat.prime_three.dvd_of_dvd_pow h3d)).symm
  have hpi_3 : p i = 3 := by
    have h9 : 9 = (p i) ^ (e i) := by omega
    have h3d : 3 ∣ (p i) ^ (e i) := ⟨3, by omega⟩
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpi).mp
      (Nat.prime_three.dvd_of_dvd_pow h3d)).symm
  exact hp_inj 0 i (by omega) hik (by omega) (hp0_3.trans hpi_3.symm)

private lemma x_ne_16 {k : ℕ} {x p e : ℕ → ℕ}
    (hp_info : ∀ i < k, Nat.Prime (p i) ∧ 1 ≤ e i ∧ x i = (p i) ^ (e i) + 1)
    {i : ℕ} (hi : i < k) : x i ≠ 16 := by
  intro h16
  rcases hp_info i hi with ⟨hp, _, hxi⟩
  exact not_prime_pow_of_two_primes (q₁ := 3) (q₂ := 5) (m := 15) (e := e i)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)

private lemma x_ne_21 {k : ℕ} {x p e : ℕ → ℕ}
    (hp_info : ∀ i < k, Nat.Prime (p i) ∧ 1 ≤ e i ∧ x i = (p i) ^ (e i) + 1)
    {i : ℕ} (hi : i < k) : x i ≠ 21 := by
  intro h21
  rcases hp_info i hi with ⟨hp, _, hxi⟩
  exact not_prime_pow_of_two_primes (q₁ := 2) (q₂ := 5) (m := 20) (e := e i)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)

private lemma x_ne_385 {k : ℕ} {x p e : ℕ → ℕ}
    (hp_info : ∀ i < k, Nat.Prime (p i) ∧ 1 ≤ e i ∧ x i = (p i) ^ (e i) + 1)
    {i : ℕ} (hi : i < k) : x i ≠ 385 := by
  intro h385
  rcases hp_info i hi with ⟨hp, _, hxi⟩
  exact not_prime_pow_of_two_primes (q₁ := 2) (q₂ := 3) (m := 384) (e := e i)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)

private lemma x_ne_29953 {k : ℕ} {x p e : ℕ → ℕ}
    (hp_info : ∀ i < k, Nat.Prime (p i) ∧ 1 ≤ e i ∧ x i = (p i) ^ (e i) + 1)
    {i : ℕ} (hi : i < k) : x i ≠ 29953 := by
  intro h29953
  rcases hp_info i hi with ⟨hp, _, hxi⟩
  exact not_prime_pow_of_two_primes (q₁ := 2) (q₂ := 3) (m := 29952) (e := e i)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)

private lemma x_gap_386_401 {k : ℕ} {x p e : ℕ → ℕ}
    (hp_info : ∀ i < k, Nat.Prime (p i) ∧ 1 ≤ e i ∧ x i = (p i) ^ (e i) + 1)
    {i : ℕ} (hi : i < k) (hlo : 386 ≤ x i) (hhi : x i ≤ 401) :
    x i = 390 ∨ x i = 398 := by
  rcases hp_info i hi with ⟨hp, _, hxi⟩
  interval_cases hval : x i
  · exfalso; exact not_prime_pow_of_two_primes (q₁ := 5) (q₂ := 7) (m := 385) (e := e i)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)
  · exfalso; exact not_prime_pow_of_two_primes (q₁ := 2) (q₂ := 193) (m := 386) (e := e i)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)
  · exfalso; exact not_prime_pow_of_two_primes (q₁ := 3) (q₂ := 43) (m := 387) (e := e i)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)
  · exfalso; exact not_prime_pow_of_two_primes (q₁ := 2) (q₂ := 97) (m := 388) (e := e i)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)
  · left; rfl
  · exfalso; exact not_prime_pow_of_two_primes (q₁ := 2) (q₂ := 3) (m := 390) (e := e i)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)
  · exfalso; exact not_prime_pow_of_two_primes (q₁ := 17) (q₂ := 23) (m := 391) (e := e i)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)
  · exfalso; exact not_prime_pow_of_two_primes (q₁ := 2) (q₂ := 7) (m := 392) (e := e i)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)
  · exfalso; exact not_prime_pow_of_two_primes (q₁ := 3) (q₂ := 131) (m := 393) (e := e i)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)
  · exfalso; exact not_prime_pow_of_two_primes (q₁ := 2) (q₂ := 197) (m := 394) (e := e i)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)
  · exfalso; exact not_prime_pow_of_two_primes (q₁ := 5) (q₂ := 79) (m := 395) (e := e i)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)
  · exfalso; exact not_prime_pow_of_two_primes (q₁ := 2) (q₂ := 3) (m := 396) (e := e i)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)
  · right; rfl
  · exfalso; exact not_prime_pow_of_two_primes (q₁ := 2) (q₂ := 199) (m := 398) (e := e i)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)
  · exfalso; exact not_prime_pow_of_two_primes (q₁ := 3) (q₂ := 7) (m := 399) (e := e i)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)
  · exfalso; exact not_prime_pow_of_two_primes (q₁ := 2) (q₂ := 5) (m := 400) (e := e i)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp (by omega)

private lemma even_prod_prefix {k : ℕ} {x p : ℕ → ℕ}
    (hp_inj : ∀ i j, i < k → j < k → i ≠ j → p i ≠ p j)
    (hp_even : ∀ i < k, p i ≠ 2 → Even (x i))
    {u : ℕ} (hu2 : 2 ≤ u) (huk : u ≤ k) :
    2 ∣ ∏ i ∈ Finset.range u, x i := by
  by_cases h0 : p 0 = 2
  · have h1 : p 1 ≠ 2 := fun h => hp_inj 0 1 (by omega) (by omega) (by omega) (h0.trans h.symm)
    have hd1 : 2 ∣ x 1 := even_iff_two_dvd.mp (hp_even 1 (by omega) h1)
    exact dvd_trans hd1 (Finset.dvd_prod_of_mem x (Finset.mem_range.mpr (by omega)))
  · have hd0 : 2 ∣ x 0 := even_iff_two_dvd.mp (hp_even 0 (by omega) h0)
    exact dvd_trans hd0 (Finset.dvd_prod_of_mem x (Finset.mem_range.mpr (by omega)))

end PrimePowerGaps

/-! ## Section 2: Cook Majorization & Unified Multi-Step Cook–Nielsen Engine -/

section MultistepCookNielsen

private lemma log_one_sub_inv_sub_ge {x y : ℝ} (hx : 1 < x) (hy : 1 < y) :
    (1 / (x - 1)) * (Real.log x - Real.log y) ≤
      Real.log (1 - 1 / x) - Real.log (1 - 1 / y) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hxm1 : 0 < x - 1 := by linarith
  have h1x : 0 < 1 - 1 / x := by rw [sub_pos, div_lt_one hx0]; exact hx
  have h1y : 0 < 1 - 1 / y := by rw [sub_pos, div_lt_one hy0]; exact hy
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

private lemma sylvester_prefix_prod (a u : ℕ) :
    a * (∏ i ∈ Finset.range u, ((a + 1) ^ (2 ^ i) + 1)) + 1 = (a + 1) ^ (2 ^ u) := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, pow_succ, pow_mul]
    have h1 : a * (∏ i ∈ Finset.range u, ((a + 1) ^ (2 ^ i) + 1)) = (a + 1) ^ (2 ^ u) - 1 := by
      omega
    have hge1 : 1 ≤ (a + 1) ^ (2 ^ u) := Nat.one_le_pow _ _ (by omega)
    zify [hge1] at h1 ⊢
    rw [h1]
    ring

private lemma sum_two_pow_range (u : ℕ) : (∑ i ∈ Finset.range u, 2 ^ i) + 1 = 2 ^ u := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

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
  have hP_pos : (0 : ℝ) < ∏ i ∈ Finset.range (r - 1), (((a + 1) ^ (2 ^ i) + 1 : ℕ) : ℝ) :=
    Finset.prod_pos fun i _ => by positivity
  have hpow_pos : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) ^ (∑ i ∈ Finset.range (r - 1), 2 ^ i) := by
    positivity
  rw [hnum_pow, hpow_split, ← hden_id]
  field_simp [ne_of_gt ha_pos, ne_of_gt ha1_pos, ne_of_gt hP_pos, ne_of_gt hpow_pos]

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

/-- **Unified Multi-Step Cook–Nielsen Bounding Engine:**
Given `r > t ≥ 1`, `∏_{j<r} (1 - 1/z_j) = a/b`, and lower bounds `z_j ≥ M_j` for `j < t`,
either no strict prefix `t < u < r` undercuts the Sylvester-Cook comparison sequence `y`
(yielding the full Cook bound), or some prefix `u` undercuts `y` (yielding Nielsen's bound on
the tail with divisor cancellation `d`). -/
private theorem multistep_cook_nielsen
    (r t a b d A C : ℕ) (M z : ℕ → ℕ)
    (ht : 1 ≤ t) (hr : t < r) (ha : 1 ≤ a) (hab : a < b) (hd : 1 ≤ d)
    (hA : 1 ≤ A) (hC : 1 ≤ C)
    (hz_mono : ∀ i j, i ≤ j → j < r → z i ≤ z j)
    (hz_ge2 : ∀ j < r, 2 ≤ z j)
    (hM_ge2 : ∀ j < t, 2 ≤ M j)
    (hz_geM : ∀ j < t, M j ≤ z j)
    (hz_rat : ∏ j ∈ Finset.range r, (1 - 1 / (z j : ℝ)) = (a : ℝ) / (b : ℝ))
    (hA_ge : (a : ℝ) / (b : ℝ) ≤
      (∏ j ∈ Finset.range t, (1 - 1 / (M j : ℝ))) * ((A : ℝ) / ((A + 1 : ℕ) : ℝ)))
    (hC_ge : a * (∏ j ∈ Finset.range t, M j) ≤ d * A * C)
    (hd_div : ∀ u, t < u → u < r → d ∣ ∏ j ∈ Finset.range u, z j ∧ d ∣ b) :
    A * (∏ j ∈ Finset.range r, z j) < (∏ j ∈ Finset.range t, M j) * (A + 1) ^ (2 ^ (r - t)) ∨
    (t + 1 < r ∧ a * (∏ j ∈ Finset.range r, z j) < d * (C * (A + 1) ^ 2) ^ (2 ^ (r - t - 1))) := by
  let y : ℕ → ℕ := fun j =>
    if j < t then M j
    else if j < r - 1 then (A + 1) ^ (2 ^ (j - t)) + 1
    else (A + 1) ^ (2 ^ (r - t - 1))
  have hy_ge2 : ∀ j < r, 2 ≤ y j := by
    intro j hj
    dsimp only [y]
    split_ifs with h1 h2
    · exact hM_ge2 j h1
    · have : 1 ≤ (A + 1) ^ (2 ^ (j - t)) := Nat.one_le_pow _ _ (by omega)
      omega
    · calc
        2 ≤ A + 1 := by omega
        _ = (A + 1) ^ 1 := (pow_one _).symm
        _ ≤ (A + 1) ^ (2 ^ (r - t - 1)) :=
          Nat.pow_le_pow_right (by omega) (Nat.one_le_pow _ _ (by omega))
  have hy_rat : ∏ j ∈ Finset.range r, (1 - 1 / (y j : ℝ)) =
      (∏ j ∈ Finset.range t, (1 - 1 / (M j : ℝ))) * ((A : ℝ) / ((A + 1 : ℕ) : ℝ)) := by
    have hr_eq : r = t + (r - t) := by omega
    conv_lhs => rw [hr_eq, Finset.prod_range_add]
    have hpre : ∏ j ∈ Finset.range t, (1 - 1 / (y j : ℝ)) =
        ∏ j ∈ Finset.range t, (1 - 1 / (M j : ℝ)) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjt : j < t := Finset.mem_range.mp hj
      simp [y, hjt]
    have htail : ∏ j ∈ Finset.range (r - t), (1 - 1 / (y (t + j) : ℝ)) =
        (A : ℝ) / ((A + 1 : ℕ) : ℝ) := by
      have heq : ∏ j ∈ Finset.range (r - t), (1 - 1 / (y (t + j) : ℝ)) =
          ∏ j ∈ Finset.range (r - t),
            (1 - 1 / ((if j < (r - t) - 1 then (A + 1) ^ (2 ^ j) + 1
              else (A + 1) ^ (2 ^ ((r - t) - 1)) : ℕ) : ℝ)) := by
        refine Finset.prod_congr rfl fun j hj => ?_
        have hjlt := Finset.mem_range.mp hj
        have hnot : ¬ (t + j < t) := by omega
        have hiff : (t + j < r - 1) ↔ (j < (r - t) - 1) := by omega
        have hsub : r - t - 1 = (r - t) - 1 := by omega
        simp only [y, hnot, ↓reduceIte, hiff, Nat.add_sub_cancel_left]
      rw [heq]
      exact sylvester_one_sub_inv_prod A (r - t) hA (by omega)
    rw [hpre, htail]
  have hy_pref : ∀ u, t < u → u < r →
      A * ∏ j ∈ Finset.range u, y j = (∏ j ∈ Finset.range t, M j) * ((A + 1) ^ (2 ^ (u - t)) - 1) := by
    intro u hut hur
    have hu_eq : u = t + (u - t) := by omega
    conv_lhs => rw [hu_eq, Finset.prod_range_add]
    have hpre : ∏ j ∈ Finset.range t, y j = ∏ j ∈ Finset.range t, M j := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjt : j < t := Finset.mem_range.mp hj
      simp [y, hjt]
    have htail : ∏ j ∈ Finset.range (u - t), y (t + j) =
        ∏ j ∈ Finset.range (u - t), ((A + 1) ^ (2 ^ j) + 1) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjlt := Finset.mem_range.mp hj
      have hnot : ¬ (t + j < t) := by omega
      have hlt : t + j < r - 1 := by omega
      simp [y, hnot, hlt]
    rw [hpre, htail]
    have hs := sylvester_prefix_prod A (u - t)
    have h1 : A * ∏ j ∈ Finset.range (u - t), ((A + 1) ^ (2 ^ j) + 1) =
        (A + 1) ^ (2 ^ (u - t)) - 1 := by omega
    calc
      A * ((∏ j ∈ Finset.range t, M j) * ∏ j ∈ Finset.range (u - t), ((A + 1) ^ (2 ^ j) + 1))
          = (∏ j ∈ Finset.range t, M j) * (A * ∏ j ∈ Finset.range (u - t), ((A + 1) ^ (2 ^ j) + 1)) := by
              ring
      _ = (∏ j ∈ Finset.range t, M j) * ((A + 1) ^ (2 ^ (u - t)) - 1) := by rw [h1]
  have hy_all_lt : A * ∏ j ∈ Finset.range r, y j <
      (∏ j ∈ Finset.range t, M j) * (A + 1) ^ (2 ^ (r - t)) := by
    have hr_eq : r = (r - 1) + 1 := by omega
    conv_lhs => rw [hr_eq, Finset.prod_range_succ]
    have hlast : y (r - 1) = (A + 1) ^ (2 ^ (r - t - 1)) := by
      have h1 : ¬ (r - 1 < t) := by omega
      simp [y, h1]
    have hprod_pre : A * ∏ j ∈ Finset.range (r - 1), y j <
        (∏ j ∈ Finset.range t, M j) * (A + 1) ^ (2 ^ (r - t - 1)) := by
      by_cases hrt1 : r - 1 = t
      · rw [hrt1]
        have hpre : ∏ j ∈ Finset.range t, y j = ∏ j ∈ Finset.range t, M j := by
          refine Finset.prod_congr rfl fun j hj => by simp [y, Finset.mem_range.mp hj]
        rw [hpre, show r - t - 1 = 0 by omega, pow_zero, pow_one]
        have hM_pos : 0 < ∏ j ∈ Finset.range t, M j :=
          Finset.prod_pos fun j hj => by have := hM_ge2 j (Finset.mem_range.mp hj); omega
        nlinarith
      · have hut : t < r - 1 := by omega
        rw [hy_pref (r - 1) hut (by omega)]
        have hsub : r - 1 - t = r - t - 1 := by omega
        rw [hsub]
        have hpow_pos : 1 ≤ (A + 1) ^ (2 ^ (r - t - 1)) := Nat.one_le_pow _ _ (by omega)
        have hM_pos : 0 < ∏ j ∈ Finset.range t, M j :=
          Finset.prod_pos fun j hj => by have := hM_ge2 j (Finset.mem_range.mp hj); omega
        exact Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hpow_pos (by omega)) hM_pos
    have hpow_eq : (A + 1) ^ (2 ^ (r - t - 1)) * (A + 1) ^ (2 ^ (r - t - 1)) =
        (A + 1) ^ (2 ^ (r - t)) := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      have : r - t - 1 + 1 = r - t := by omega
      rw [this]
    calc
      A * ((∏ j ∈ Finset.range (r - 1), y j) * y (r - 1))
          = (A * ∏ j ∈ Finset.range (r - 1), y j) * (A + 1) ^ (2 ^ (r - t - 1)) := by
              rw [hlast]; ring
      _ < ((∏ j ∈ Finset.range t, M j) * (A + 1) ^ (2 ^ (r - t - 1))) * (A + 1) ^ (2 ^ (r - t - 1)) :=
            Nat.mul_lt_mul_of_pos_right hprod_pre (by positivity)
      _ = (∏ j ∈ Finset.range t, M j) * (A + 1) ^ (2 ^ (r - t)) := by rw [mul_assoc, hpow_eq]
  by_cases hex : ∃ u, t < u ∧ u < r ∧
      ∏ j ∈ Finset.range u, z j < ∏ j ∈ Finset.range u, y j
  · rcases hex with ⟨u, hut, hur, hzu⟩
    right
    refine ⟨by omega, ?_⟩
    rcases hd_div u hut hur with ⟨hd_z, hd_b⟩
    rcases hd_z with ⟨Pu, hPu⟩
    rcases hd_b with ⟨b0, hb0⟩
    have hPu_pos : 1 ≤ Pu := by
      have hz_pos : 0 < ∏ j ∈ Finset.range u, z j :=
        Finset.prod_pos fun j hj => by
          have := hz_ge2 j (by have := Finset.mem_range.mp hj; omega); omega
      rw [hPu] at hz_pos
      exact Nat.pos_of_mul_pos_left hz_pos
    have hb0_pos : 1 ≤ b0 := by
      have hb_pos : 0 < b := by omega
      rw [hb0] at hb_pos
      exact Nat.pos_of_mul_pos_left hb_pos
    set a' := a * Pu
    set b' := b0 * ∏ j ∈ Finset.range u, (z j - 1)
    have ha'_pos : 1 ≤ a' := Nat.mul_pos ha hPu_pos
    have hb'_pos : 1 ≤ b' := by
      refine Nat.mul_pos hb0_pos (Finset.prod_pos fun j hj => ?_)
      have := hz_ge2 j (by have := Finset.mem_range.mp hj; omega)
      omega
    have hpref_prod :
        ∏ j ∈ Finset.range u, (1 - 1 / (z j : ℝ)) =
          ((∏ j ∈ Finset.range u, (z j - 1) : ℕ) : ℝ) / ((d * Pu : ℕ) : ℝ) := by
      rw [← hPu]
      push_cast
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hzj := hz_ge2 j (by have := Finset.mem_range.mp hj; omega)
      have hzj_pos : (0 : ℝ) < (z j : ℝ) := by exact_mod_cast (by omega : 0 < z j)
      rw [Nat.cast_sub (by omega : 1 ≤ z j), Nat.cast_one]
      field_simp [ne_of_gt hzj_pos]
    have hsplit : ∏ j ∈ Finset.range r, (1 - 1 / (z j : ℝ)) =
        (∏ j ∈ Finset.range u, (1 - 1 / (z j : ℝ))) *
          ∏ j ∈ Finset.range (r - u), (1 - 1 / (z (u + j) : ℝ)) := by
      have hr_eq : r = u + (r - u) := by omega
      conv_lhs => rw [hr_eq, Finset.prod_range_add]
    have htail_rat : ∏ j ∈ Finset.range (r - u), (1 - 1 / (z (u + j) : ℝ)) =
        (a' : ℝ) / (b' : ℝ) := by
      rw [hsplit, hpref_prod, hb0] at hz_rat
      have hd_ne : (d : ℝ) ≠ 0 := by positivity
      have hPu_ne : (Pu : ℝ) ≠ 0 := by positivity
      have hb0_ne : (b0 : ℝ) ≠ 0 := by positivity
      have hQ_ne : ((∏ j ∈ Finset.range u, (z j - 1) : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Finset.prod_pos fun j hj => by
          have := hz_ge2 j (by have := Finset.mem_range.mp hj; omega); omega))
      have hDPu_ne : ((d * Pu : ℕ) : ℝ) ≠ 0 := by positivity
      have hQ_ne' : (∏ j ∈ Finset.range u, ((z j - 1 : ℕ) : ℝ)) ≠ 0 := by
        simpa using hQ_ne
      have h1 := congrArg (fun t => t * (((d * Pu : ℕ) : ℝ) / ((∏ j ∈ Finset.range u, (z j - 1) : ℕ) : ℝ))) hz_rat
      have hL : (((∏ j ∈ Finset.range u, (z j - 1) : ℕ) : ℝ) / ((d * Pu : ℕ) : ℝ) *
          ∏ j ∈ Finset.range (r - u), (1 - 1 / (z (u + j) : ℝ))) *
          (((d * Pu : ℕ) : ℝ) / ((∏ j ∈ Finset.range u, (z j - 1) : ℕ) : ℝ)) =
          ∏ j ∈ Finset.range (r - u), (1 - 1 / (z (u + j) : ℝ)) := by
        field_simp [hDPu_ne, hQ_ne]
      have hR : ((a : ℝ) / ((d * b0 : ℕ) : ℝ)) *
          (((d * Pu : ℕ) : ℝ) / ((∏ j ∈ Finset.range u, (z j - 1) : ℕ) : ℝ)) =
          (a' : ℝ) / (b' : ℝ) := by
        dsimp only [a', b']
        push_cast
        field_simp [hd_ne, hb0_ne, hQ_ne']
      rw [← hL, h1, hR]
    have ha'_lt : a' + 1 ≤ C * (A + 1) ^ (2 ^ (u - t)) := by
      have h1 : d * A * a' = a * A * ∏ j ∈ Finset.range u, z j := by
        dsimp only [a']; rw [hPu]; ring
      have h2 : a * A * ∏ j ∈ Finset.range u, z j < a * (A * ∏ j ∈ Finset.range u, y j) := by
        rw [mul_assoc]
        exact Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left hzu hA) ha
      rw [hy_pref u hut hur] at h2
      have h3 : a * ((∏ j ∈ Finset.range t, M j) * ((A + 1) ^ (2 ^ (u - t)) - 1)) ≤
          d * A * C * ((A + 1) ^ (2 ^ (u - t)) - 1) := by
        calc
          a * ((∏ j ∈ Finset.range t, M j) * ((A + 1) ^ (2 ^ (u - t)) - 1))
              = (a * ∏ j ∈ Finset.range t, M j) * ((A + 1) ^ (2 ^ (u - t)) - 1) := by ring
          _ ≤ (d * A * C) * ((A + 1) ^ (2 ^ (u - t)) - 1) :=
                Nat.mul_le_mul_right _ hC_ge
          _ = d * A * C * ((A + 1) ^ (2 ^ (u - t)) - 1) := by ring
      have hlt_mul : d * A * a' < d * A * (C * ((A + 1) ^ (2 ^ (u - t)) - 1)) := by
        calc
          d * A * a' < a * ((∏ j ∈ Finset.range t, M j) * ((A + 1) ^ (2 ^ (u - t)) - 1)) := by
            omega
          _ ≤ d * A * C * ((A + 1) ^ (2 ^ (u - t)) - 1) := h3
          _ = d * A * (C * ((A + 1) ^ (2 ^ (u - t)) - 1)) := by ring
      have hdA_pos : 0 < d * A := Nat.mul_pos hd hA
      have ha'_lt_sub : a' < C * ((A + 1) ^ (2 ^ (u - t)) - 1) :=
        Nat.lt_of_mul_lt_mul_left hlt_mul
      have hpow_ge1 : 1 ≤ (A + 1) ^ (2 ^ (u - t)) := Nat.one_le_pow _ _ (by omega)
      have hC_sub : C * ((A + 1) ^ (2 ^ (u - t)) - 1) + 1 ≤ C * (A + 1) ^ (2 ^ (u - t)) := by
        zify [hpow_ge1]
        nlinarith
      omega
    have hnb := PPL133.nielsen_product_bound (r - u) (by omega) a' b' ha'_pos hb'_pos
      (fun j => z (u + j))
      (fun i j hij hj => hz_mono (u + i) (u + j) (by omega) (by omega))
      (fun j hj => hz_ge2 (u + j) (by omega))
      (le_of_eq htail_rat)
      (fun v hv => by
        rw [← htail_rat]
        exact prefix_prod_gt_of_eq (r - u) (fun j => z (u + j))
          (fun j hj => hz_ge2 (u + j) (by omega)) v hv)
    have hsplit_z : a * ∏ j ∈ Finset.range r, z j =
        d * (a' * ∏ j ∈ Finset.range (r - u), z (u + j)) := by
      have hr_eq : r = u + (r - u) := by omega
      conv_lhs => rw [hr_eq, Finset.prod_range_add, hPu]
      dsimp only [a']
      ring
    have hpow_bound : (a' + 1) ^ (2 ^ (r - u)) ≤ (C * (A + 1) ^ 2) ^ (2 ^ (r - t - 1)) := by
      have h1 : (a' + 1) ^ (2 ^ (r - u)) ≤ (C * (A + 1) ^ (2 ^ (u - t))) ^ (2 ^ (r - u)) :=
        Nat.pow_le_pow_left ha'_lt _
      have h2 : (C * (A + 1) ^ (2 ^ (u - t))) ^ (2 ^ (r - u)) =
          C ^ (2 ^ (r - u)) * (A + 1) ^ (2 ^ (r - t)) := by
        rw [mul_pow, ← pow_mul, ← pow_add]
        have : (u - t) + (r - u) = r - t := by omega
        rw [this]
      have h3 : C ^ (2 ^ (r - u)) ≤ C ^ (2 ^ (r - t - 1)) :=
        Nat.pow_le_pow_right hC (Nat.pow_le_pow_right (by omega) (by omega))
      have h4 : (A + 1) ^ (2 ^ (r - t)) = ((A + 1) ^ 2) ^ (2 ^ (r - t - 1)) := by
        rw [← pow_mul, ← pow_succ']
        have : r - t - 1 + 1 = r - t := by omega
        rw [this]
      calc
        (a' + 1) ^ (2 ^ (r - u))
            ≤ C ^ (2 ^ (r - u)) * (A + 1) ^ (2 ^ (r - t)) := h1.trans_eq h2
        _ ≤ C ^ (2 ^ (r - t - 1)) * ((A + 1) ^ 2) ^ (2 ^ (r - t - 1)) := by
              rw [h4]
              exact Nat.mul_le_mul_right _ h3
        _ = (C * (A + 1) ^ 2) ^ (2 ^ (r - t - 1)) := (mul_pow _ _ _).symm
    rw [hsplit_z]
    exact Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le hnb hpow_bound) hd
  · push Not at hex
    left
    by_contra hge
    push Not at hge
    have hpref_y : ∀ u ≤ r, ∏ j ∈ Finset.range u, y j ≤ ∏ j ∈ Finset.range u, z j := by
      intro u hu
      by_cases hut : u ≤ t
      · refine Finset.prod_le_prod' fun j hj => ?_
        have hjt : j < t := lt_of_lt_of_le (Finset.mem_range.mp hj) hut
        simp only [y, hjt, ↓reduceIte]
        exact hz_geM j hjt
      · by_cases hur : u < r
        · exact hex u (by omega) hur
        · have hueq : u = r := by omega
          have hy_lt_z : ∏ j ∈ Finset.range u, y j < ∏ j ∈ Finset.range u, z j := by
            rw [hueq]
            have : A * ∏ j ∈ Finset.range r, y j < A * ∏ j ∈ Finset.range r, z j :=
              lt_of_lt_of_le hy_all_lt hge
            exact Nat.lt_of_mul_lt_mul_left this
          exact le_of_lt hy_lt_z
    have hstrict_y : ∏ j ∈ Finset.range r, y j < ∏ j ∈ Finset.range r, z j := by
      have : A * ∏ j ∈ Finset.range r, y j < A * ∏ j ∈ Finset.range r, z j :=
        lt_of_lt_of_le hy_all_lt hge
      exact Nat.lt_of_mul_lt_mul_left this
    have hmaj := cook_majorization r (by omega) z y hz_mono hz_ge2 hy_ge2 hpref_y hstrict_y
    rw [hy_rat, hz_rat] at hmaj
    linarith

/-- Induction helper: once `P * B^(2^e₀) ≤ Q * 2^(2^(e₀ + s))` and `B ≤ 2^(2^s)`,
the inequality propagates to all `e ≥ e₀`. -/
private lemma two_pow_bound_of_base (P Q B s e₀ e : ℕ)
    (hB : B ≤ 2 ^ (2 ^ s))
    (hbase : P * B ^ (2 ^ e₀) ≤ Q * 2 ^ (2 ^ (e₀ + s)))
    (he : e₀ ≤ e) :
    P * B ^ (2 ^ e) ≤ Q * 2 ^ (2 ^ (e + s)) := by
  induction e, he using Nat.le_induction with
  | base => exact hbase
  | succ m hm ih =>
    have hpowB : B ^ (2 ^ (m + 1)) = B ^ (2 ^ m) * B ^ (2 ^ m) := by
      rw [← pow_add, ← two_mul, ← pow_succ']
    have hpow2 : 2 ^ (2 ^ (m + 1 + s)) = 2 ^ (2 ^ (m + s)) * 2 ^ (2 ^ (m + s)) := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      congr 2; omega
    have hB_m : B ^ (2 ^ m) ≤ 2 ^ (2 ^ (m + s)) := by
      calc
        B ^ (2 ^ m) ≤ (2 ^ (2 ^ s)) ^ (2 ^ m) := Nat.pow_le_pow_left hB _
        _ = 2 ^ (2 ^ s * 2 ^ m) := by rw [← pow_mul]
        _ = 2 ^ (2 ^ (m + s)) := by rw [← pow_add, add_comm]
    calc
      P * B ^ (2 ^ (m + 1))
          = (P * B ^ (2 ^ m)) * B ^ (2 ^ m) := by rw [hpowB, mul_assoc]
      _ ≤ (Q * 2 ^ (2 ^ (m + s))) * 2 ^ (2 ^ (m + s)) := Nat.mul_le_mul ih hB_m
      _ = Q * 2 ^ (2 ^ (m + 1 + s)) := by rw [mul_assoc, ← hpow2]

end MultistepCookNielsen

/-! ## Section 3: Complete Classification for `ω(n) ≤ 5` -/

section SmallOmegaClassification

/-- Helper: if `n` is a UPN with `v_2(n) ≥ 4` and `ω(n) = k`, then `x` cannot satisfy
the strict lower bounds `[6, 8, 10, 12]` at `k = 4`, etc.; more generally, if
`∏_{i<k} (1 - 1/M_i) > 1/2` while `M_i ≤ x_i`, we get an immediate contradiction. -/
private lemma prod_one_sub_inv_le_of_le {k : ℕ} (M x : ℕ → ℕ)
    (hM_ge2 : ∀ i < k, 2 ≤ M i) (hMx : ∀ i < k, M i ≤ x i) :
    ∏ i ∈ Finset.range k, (1 - 1 / (M i : ℝ)) ≤ ∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) := by
  refine Finset.prod_le_prod ?_ ?_
  · intro i hi
    have hMi := hM_ge2 i (Finset.mem_range.mp hi)
    have hpos : (0 : ℝ) < (M i : ℝ) := by exact_mod_cast (by omega : 0 < M i)
    have h1 : (1 : ℝ) / (M i : ℝ) ≤ 1 := (div_le_one hpos).mpr (by exact_mod_cast (by omega : 1 ≤ M i))
    linarith
  · intro i hi
    have hlt := Finset.mem_range.mp hi
    have hMi := hM_ge2 i hlt
    have hle := hMx i hlt
    have hMi_pos : (0 : ℝ) < (M i : ℝ) := by exact_mod_cast (by omega : 0 < M i)
    have hle_r : (M i : ℝ) ≤ (x i : ℝ) := by exact_mod_cast hle
    have hdiv := one_div_le_one_div_of_le hMi_pos hle_r
    linarith

/-- There is **no** unitary perfect number with `ω(n) = 4`. -/
theorem omega_ne_four (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) :
    n.primeFactors.card ≠ 4 := by
  intro hω
  have hv2_ge4 : 4 ≤ n.factorization 2 := by
    by_contra hlt
    have hle3 : n.factorization 2 ≤ 3 := by omega
    rcases (PPL133.classify_v2_le_three n).mp ⟨hn, hle3⟩ with rfl | rfl | rfl
    · have := ((PPL133.classify_omega_le_three 6).mpr (Or.inl rfl)).2; omega
    · have := ((PPL133.classify_omega_le_three 60).mpr (Or.inr (Or.inl rfl))).2; omega
    · have := ((PPL133.classify_omega_le_three 90).mpr (Or.inr (Or.inr rfl))).2; omega
  rcases sorted_primePow_components_of_upn n hn hv2_ge4 with
    ⟨x, p, e, _, hx_lt, _, hp_info, hp_inj, hp_two, hp_even, _, _, hx_rat⟩
  rw [hω] at hx_lt hp_info hp_inj hp_two hp_even hx_rat
  have hge4 : ∀ i < 4, 4 ≤ x i := fun i hi => x_ge_four hp_info hp_two hi
  have heven : ∀ i < 4, x i < 17 → Even (x i) := fun i hi => x_even_of_lt_17 hp_info hp_two hp_even hi
  have h1_2 : (1 : ℝ) / 2 =
      (1 - (x 0 : ℝ)⁻¹) * (1 - (x 1 : ℝ)⁻¹) * (1 - (x 2 : ℝ)⁻¹) * (1 - (x 3 : ℝ)⁻¹) := by
    have hr := hx_rat.symm
    simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, one_div] at hr
    simpa using hr
  -- Split on x 0 = 4 vs x 0 ≥ 6
  by_cases hx0_4 : x 0 = 4
  · have hx1_ge6 : 6 ≤ x 1 := by
      have hlt01 := hx_lt 0 1 (by omega) (by omega)
      by_contra hlt
      have hx1_5 : x 1 = 5 := by omega
      exact absurd (heven 1 (by omega) (by omega)) (by rw [hx1_5]; decide)
    by_cases hx1_6 : x 1 = 6
    · have hx2_ge8 : 8 ≤ x 2 := by
        have hlt12 := hx_lt 1 2 (by omega) (by omega)
        by_contra hlt
        have hx2_7 : x 2 = 7 := by omega
        exact absurd (heven 2 (by omega) (by omega)) (by rw [hx2_7]; decide)
      -- Even with x = [4, 6, 8, 12], product is (3/4)*(5/6)*(7/8)*(11/12) = 385/768 > 1/2!
      have hx3_ge12 : 12 ≤ x 3 := by
        have hlt23 := hx_lt 2 3 (by omega) (by omega)
        by_contra hlt
        have hlt11 : x 3 ≤ 11 := by omega
        have hev3 : x 3 % 2 = 0 := Nat.even_iff.mp (heven 3 (by omega) (by omega))
        have hne10 : x 3 ≠ 10 := x_ne_10_of_x0_eq_4 (by omega) hp_info hp_inj hx0_4 (by omega) (by omega)
        omega
      let M : ℕ → ℕ := fun i => match i with | 0 => 4 | 1 => 6 | 2 => 8 | _ => 12
      have hM2 : ∀ i < 4, 2 ≤ M i := fun i hi => by interval_cases i <;> decide
      have hMx : ∀ i < 4, M i ≤ x i := fun i hi => by
        interval_cases i <;> simp [M] <;> omega
      have hle := prod_one_sub_inv_le_of_le M x hM2 hMx
      simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, M] at hle
      norm_num at hle
      linarith
    · -- x 0 = 4, x 1 ≥ 8 ⇒ x 2 ≥ 12 (since 10 forbidden), x 3 ≥ 14
      have hx1_ge8 : 8 ≤ x 1 := by
        by_contra hlt
        have hx1_7 : x 1 = 7 := by omega
        exact absurd (heven 1 (by omega) (by omega)) (by rw [hx1_7]; decide)
      have hx2_ge12 : 12 ≤ x 2 := by
        have hlt12 := hx_lt 1 2 (by omega) (by omega)
        by_contra hlt
        have h11 : x 2 ≤ 11 := by omega
        have hev2 : x 2 % 2 = 0 := Nat.even_iff.mp (heven 2 (by omega) (by omega))
        have hne10 : x 2 ≠ 10 := x_ne_10_of_x0_eq_4 (by omega) hp_info hp_inj hx0_4 (i := 2) (by omega) (by omega)
        omega
      have hx3_ge14 : 14 ≤ x 3 := by
        have hlt23 := hx_lt 2 3 (by omega) (by omega)
        by_contra hlt
        have hx3_13 : x 3 = 13 := by omega
        exact absurd (heven 3 (by omega) (by omega)) (by rw [hx3_13]; decide)
      let M : ℕ → ℕ := fun i => match i with | 0 => 4 | 1 => 8 | 2 => 12 | _ => 14
      have hM2 : ∀ i < 4, 2 ≤ M i := fun i hi => by interval_cases i <;> decide
      have hMx : ∀ i < 4, M i ≤ x i := fun i hi => by
        interval_cases i <;> simp [M] <;> omega
      have hle := prod_one_sub_inv_le_of_le M x hM2 hMx
      simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, M] at hle
      norm_num at hle
      linarith
  · -- x 0 ≥ 6 ⇒ x ≥ [6, 8, 10, 12] ⇒ product ≥ 5/6 * 7/8 * 9/10 * 11/12 > 1/2
    have hx0_ge6 : 6 ≤ x 0 := by
      have h0 := hge4 0 (by omega)
      by_contra hlt
      have hx0_5 : x 0 = 5 := by omega
      exact absurd (heven 0 (by omega) (by omega)) (by rw [hx0_5]; decide)
    have hx1_ge8 : 8 ≤ x 1 := by
      have hlt01 := hx_lt 0 1 (by omega) (by omega)
      by_contra hlt
      have hx1_7 : x 1 = 7 := by omega
      exact absurd (heven 1 (by omega) (by omega)) (by rw [hx1_7]; decide)
    have hx2_ge10 : 10 ≤ x 2 := by
      have hlt12 := hx_lt 1 2 (by omega) (by omega)
      by_contra hlt
      have hx2_9 : x 2 = 9 := by omega
      exact absurd (heven 2 (by omega) (by omega)) (by rw [hx2_9]; decide)
    have hx3_ge12 : 12 ≤ x 3 := by
      have hlt23 := hx_lt 2 3 (by omega) (by omega)
      by_contra hlt
      have hx3_11 : x 3 = 11 := by omega
      exact absurd (heven 3 (by omega) (by omega)) (by rw [hx3_11]; decide)
    let M : ℕ → ℕ := fun i => match i with | 0 => 6 | 1 => 8 | 2 => 10 | _ => 12
    have hM2 : ∀ i < 4, 2 ≤ M i := fun i hi => by interval_cases i <;> decide
    have hMx : ∀ i < 4, M i ≤ x i := fun i hi => by
      interval_cases i <;> simp [M] <;> omega
    have hle := prod_one_sub_inv_le_of_le M x hM2 hMx
    simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, M] at hle
    norm_num at hle
    linarith

/-- Complete classification for `ω(n) = 5`: `n = 87360` is the unique unitary perfect number
with 5 distinct prime factors. -/
theorem classify_omega_eq_five (n : ℕ) :
    ((∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) ∧
      n.primeFactors.card = 5) ↔
      n = 87360 := by
  constructor
  · rintro ⟨hn, hω⟩
    have hv2_ge4 : 4 ≤ n.factorization 2 := by
      by_contra hlt
      have hle3 : n.factorization 2 ≤ 3 := by omega
      rcases (PPL133.classify_v2_le_three n).mp ⟨hn, hle3⟩ with rfl | rfl | rfl
      · have := ((PPL133.classify_omega_le_three 6).mpr (Or.inl rfl)).2; omega
      · have := ((PPL133.classify_omega_le_three 60).mpr (Or.inr (Or.inl rfl))).2; omega
      · have := ((PPL133.classify_omega_le_three 90).mpr (Or.inr (Or.inr rfl))).2; omega
    rcases sorted_primePow_components_of_upn n hn hv2_ge4 with
      ⟨x, p, e, _, hx_lt, _, hp_info, hp_inj, hp_two, hp_even, hx_prod, _, hx_rat⟩
    rw [hω] at hx_lt hp_info hp_inj hp_two hp_even hx_prod hx_rat
    have hge4 : ∀ i < 5, 4 ≤ x i := fun i hi => x_ge_four hp_info hp_two hi
    have heven : ∀ i < 5, x i < 17 → Even (x i) := fun i hi => x_even_of_lt_17 hp_info hp_two hp_even hi
    have h1_2 : (1 : ℝ) / 2 =
        (1 - (x 0 : ℝ)⁻¹) * (1 - (x 1 : ℝ)⁻¹) * (1 - (x 2 : ℝ)⁻¹) *
          (1 - (x 3 : ℝ)⁻¹) * (1 - (x 4 : ℝ)⁻¹) := by
      have hr := hx_rat.symm
      simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, one_div] at hr
      simpa using hr
    by_cases hx0_4 : x 0 = 4
    · have hx1_ge6 : 6 ≤ x 1 := by
        have hlt01 := hx_lt 0 1 (by omega) (by omega)
        by_contra hlt
        have hx1_5 : x 1 = 5 := by omega
        exact absurd (heven 1 (by omega) (by omega)) (by rw [hx1_5]; decide)
      by_cases hx1_6 : x 1 = 6
      · have hx2_ge8 : 8 ≤ x 2 := by
          have hlt12 := hx_lt 1 2 (by omega) (by omega)
          by_contra hlt
          have hx2_7 : x 2 = 7 := by omega
          exact absurd (heven 2 (by omega) (by omega)) (by rw [hx2_7]; decide)
        by_cases hx2_8 : x 2 = 8
        · -- Now x 0 = 4, x 1 = 6, x 2 = 8. So (1-1/x 3)*(1-1/x 4) = 32/35.
          have hx3_ge12 : 12 ≤ x 3 := by
            have hlt23 := hx_lt 2 3 (by omega) (by omega)
            by_contra hlt
            have h11 : x 3 ≤ 11 := by omega
            have hev3 : x 3 % 2 = 0 := Nat.even_iff.mp (heven 3 (by omega) (by omega))
            have hne10 : x 3 ≠ 10 := x_ne_10_of_x0_eq_4 (by omega) hp_info hp_inj hx0_4 (i := 3) (by omega) (by omega)
            omega
          have hx3_ne12 : x 3 ≠ 12 := by
            intro hx3_12
            have h12 : ∏ i ∈ Finset.range 5, (1 - 1 / (x i : ℝ)) =
                (3 : ℝ) / 4 * (5 / 6) * (7 / 8) * (11 / 12) * (1 - 1 / (x 4 : ℝ)) := by
              simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul]
              rw [hx0_4, hx1_6, hx2_8, hx3_12]
              norm_num
            rw [hx_rat] at h12
            have hx4_pos : (0 : ℝ) < (x 4 : ℝ) := by exact_mod_cast (by have := hge4 4 (by omega); omega : 0 < x 4)
            have hdiv : (1 : ℝ) / (x 4 : ℝ) = 1 / 385 := by linarith
            have hx4_r : (x 4 : ℝ) = 385 := by
              have := congrArg (fun t => t * (x 4 : ℝ) * 385) hdiv
              field_simp [ne_of_gt hx4_pos] at this
              linarith
            have hx4_eq : x 4 = 385 := by exact_mod_cast hx4_r
            exact x_ne_385 hp_info (by omega) hx4_eq
          have hx3_ge14 : 14 ≤ x 3 := by
            by_contra hlt
            have hx3_13 : x 3 = 13 := by omega
            exact absurd (heven 3 (by omega) (by omega)) (by rw [hx3_13]; decide)
          -- Exact integer equation: (3 * x 3 - 35) * (3 * x 4 - 35) = 1120
          have h34_rat : (1 - 1 / (x 3 : ℝ)) * (1 - 1 / (x 4 : ℝ)) = (32 : ℝ) / 35 := by
            have hsplit : ∏ i ∈ Finset.range 5, (1 - 1 / (x i : ℝ)) =
                (1 - 1 / (x 0 : ℝ)) * (1 - 1 / (x 1 : ℝ)) * (1 - 1 / (x 2 : ℝ)) *
                  ((1 - 1 / (x 3 : ℝ)) * (1 - 1 / (x 4 : ℝ))) := by
              simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul]
              ring
            rw [hx_rat, hx0_4, hx1_6, hx2_8] at hsplit
            norm_num at hsplit
            simp only [one_div] at hsplit ⊢
            linarith
          have h34_int : ((3 * (x 3 : ℤ) - 35) * (3 * (x 4 : ℤ) - 35)) = 1120 := by
            have hx3_pos : (0 : ℝ) < (x 3 : ℝ) := by
              exact_mod_cast (by have := hge4 3 (by omega); omega : 0 < x 3)
            have hx4_pos : (0 : ℝ) < (x 4 : ℝ) := by
              exact_mod_cast (by have := hge4 4 (by omega); omega : 0 < x 4)
            have hr : (3 * (x 3 : ℝ) - 35) * (3 * (x 4 : ℝ) - 35) = 1120 := by
              have h1 := congrArg (fun t => 315 * (x 3 : ℝ) * (x 4 : ℝ) * t) h34_rat
              field_simp [ne_of_gt hx3_pos, ne_of_gt hx4_pos] at h1
              linarith
            have hr' : (((3 * (x 3 : ℤ) - 35) * (3 * (x 4 : ℤ) - 35) : ℤ) : ℝ) = ((1120 : ℤ) : ℝ) := by
              push_cast; exact hr
            exact_mod_cast hr'
          have hx3_lt4 := hx_lt 3 4 (by omega) (by omega)
          have hx3_le22 : x 3 ≤ 22 := by
            by_contra hgt
            have h1 : (34 : ℤ) ≤ 3 * (x 3 : ℤ) - 35 := by omega
            have h2 : (34 : ℤ) ≤ 3 * (x 4 : ℤ) - 35 := by omega
            nlinarith
          interval_cases hx3_val : x 3
          · -- x 3 = 14 ⇒ x 4 = 65 ⇒ n = 87360
            have hx4_val : x 4 = 65 := by omega
            simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul] at hx_prod
            rw [hx0_4, hx1_6, hx2_8, hx3_val, hx4_val] at hx_prod
            omega
          · exfalso; exact absurd (heven 3 (by omega) (by omega)) (by rw [hx3_val]; decide)
          · exfalso; exact x_ne_16 hp_info (i := 3) (by omega) hx3_val
          · -- x 3 = 17 ⇒ x 4 = 35, both odd ⇒ p 3 = 2 = p 4, contradiction!
            exfalso
            have hx4_val : x 4 = 35 := by omega
            have hp3_2 : p 3 = 2 := by
              by_contra hne2
              have := hp_even 3 (by omega) hne2
              rw [hx3_val] at this; revert this; decide
            have hp4_2 : p 4 = 2 := by
              by_contra hne2
              have := hp_even 4 (by omega) hne2
              rw [hx4_val] at this; revert this; decide
            exact hp_inj 3 4 (by omega) (by omega) (by omega) (hp3_2.trans hp4_2.symm)
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
          · exfalso; exact x_ne_21 hp_info (i := 3) (by omega) hx3_val
          · exfalso; omega
        · -- x 0 = 4, x 1 = 6, x 2 ≥ 12 ⇒ x ≥ [4, 6, 12, 14, 17] ⇒ prod > 1/2
          have hx2_ge12 : 12 ≤ x 2 := by
            by_contra hlt
            have h11 : x 2 ≤ 11 := by omega
            have hev2 : x 2 % 2 = 0 := Nat.even_iff.mp (heven 2 (by omega) (by omega))
            have hne10 : x 2 ≠ 10 := x_ne_10_of_x0_eq_4 (by omega) hp_info hp_inj hx0_4 (i := 2) (by omega) (by omega)
            omega
          have hx3_ge14 : 14 ≤ x 3 := by
            have hlt23 := hx_lt 2 3 (by omega) (by omega)
            by_contra hlt
            have hx3_13 : x 3 = 13 := by omega
            exact absurd (heven 3 (by omega) (by omega)) (by rw [hx3_13]; decide)
          have hx4_ge17 : 17 ≤ x 4 := by
            have hlt34 := hx_lt 3 4 (by omega) (by omega)
            by_contra hlt
            have h16 : x 4 ≤ 16 := by omega
            have hev4 : x 4 % 2 = 0 := Nat.even_iff.mp (heven 4 (by omega) (by omega))
            have hne16 : x 4 ≠ 16 := x_ne_16 hp_info (i := 4) (by omega)
            omega
          let M : ℕ → ℕ := fun i => match i with | 0 => 4 | 1 => 6 | 2 => 12 | 3 => 14 | _ => 17
          have hM2 : ∀ i < 5, 2 ≤ M i := fun i hi => by interval_cases i <;> decide
          have hMx : ∀ i < 5, M i ≤ x i := fun i hi => by
            interval_cases i <;> simp [M] <;> omega
          have hle := prod_one_sub_inv_le_of_le M x hM2 hMx
          simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, M] at hle
          norm_num at hle
          linarith
      · -- x 0 = 4, x 1 ≥ 8 ⇒ x ≥ [4, 8, 12, 14, 17] ⇒ prod > 1/2
        have hx1_ge8 : 8 ≤ x 1 := by
          by_contra hlt
          have hx1_7 : x 1 = 7 := by omega
          exact absurd (heven 1 (by omega) (by omega)) (by rw [hx1_7]; decide)
        have hx2_ge12 : 12 ≤ x 2 := by
          have hlt12 := hx_lt 1 2 (by omega) (by omega)
          by_contra hlt
          have h11 : x 2 ≤ 11 := by omega
          have hev2 : x 2 % 2 = 0 := Nat.even_iff.mp (heven 2 (by omega) (by omega))
          have hne10 : x 2 ≠ 10 := x_ne_10_of_x0_eq_4 (by omega) hp_info hp_inj hx0_4 (i := 2) (by omega) (by omega)
          omega
        have hx3_ge14 : 14 ≤ x 3 := by
          have hlt23 := hx_lt 2 3 (by omega) (by omega)
          by_contra hlt
          have hx3_13 : x 3 = 13 := by omega
          exact absurd (heven 3 (by omega) (by omega)) (by rw [hx3_13]; decide)
        have hx4_ge17 : 17 ≤ x 4 := by
          have hlt34 := hx_lt 3 4 (by omega) (by omega)
          by_contra hlt
          have h16 : x 4 ≤ 16 := by omega
          have hev4 : x 4 % 2 = 0 := Nat.even_iff.mp (heven 4 (by omega) (by omega))
          have hne16 : x 4 ≠ 16 := x_ne_16 hp_info (i := 4) (by omega)
          omega
        let M : ℕ → ℕ := fun i => match i with | 0 => 4 | 1 => 8 | 2 => 12 | 3 => 14 | _ => 17
        have hM2 : ∀ i < 5, 2 ≤ M i := fun i hi => by interval_cases i <;> decide
        have hMx : ∀ i < 5, M i ≤ x i := fun i hi => by
          interval_cases i <;> simp [M] <;> omega
        have hle := prod_one_sub_inv_le_of_le M x hM2 hMx
        simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, M] at hle
        norm_num at hle
        linarith
    · -- x 0 ≥ 6 ⇒ x ≥ [6, 8, 10, 12, 14] ⇒ prod > 1/2
      have hx0_ge6 : 6 ≤ x 0 := by
        have h0 := hge4 0 (by omega)
        by_contra hlt
        have hx0_5 : x 0 = 5 := by omega
        exact absurd (heven 0 (by omega) (by omega)) (by rw [hx0_5]; decide)
      have hx1_ge8 : 8 ≤ x 1 := by
        have hlt01 := hx_lt 0 1 (by omega) (by omega)
        by_contra hlt
        have hx1_7 : x 1 = 7 := by omega
        exact absurd (heven 1 (by omega) (by omega)) (by rw [hx1_7]; decide)
      have hx2_ge10 : 10 ≤ x 2 := by
        have hlt12 := hx_lt 1 2 (by omega) (by omega)
        by_contra hlt
        have hx2_9 : x 2 = 9 := by omega
        exact absurd (heven 2 (by omega) (by omega)) (by rw [hx2_9]; decide)
      have hx3_ge12 : 12 ≤ x 3 := by
        have hlt23 := hx_lt 2 3 (by omega) (by omega)
        by_contra hlt
        have hx3_11 : x 3 = 11 := by omega
        exact absurd (heven 3 (by omega) (by omega)) (by rw [hx3_11]; decide)
      have hx4_ge14 : 14 ≤ x 4 := by
        have hlt34 := hx_lt 3 4 (by omega) (by omega)
        by_contra hlt
        have hx4_13 : x 4 = 13 := by omega
        exact absurd (heven 4 (by omega) (by omega)) (by rw [hx4_13]; decide)
      let M : ℕ → ℕ := fun i => match i with | 0 => 6 | 1 => 8 | 2 => 10 | 3 => 12 | _ => 14
      have hM2 : ∀ i < 5, 2 ≤ M i := fun i hi => by interval_cases i <;> decide
      have hMx : ∀ i < 5, M i ≤ x i := fun i hi => by
        interval_cases i <;> simp [M] <;> omega
      have hle := prod_one_sub_inv_le_of_le M x hM2 hMx
      simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, M] at hle
      norm_num at hle
      linarith
  · rintro rfl
    refine ⟨PPL133.isUnitaryPerfect_87360, ?_⟩
    have hpf : (87360 : ℕ).primeFactors = {2, 3, 5, 7, 13} := by
      have h87 : (87360 : ℕ) = 2 ^ 6 * 3 * 5 * 7 * 13 := by norm_num
      have hne0 : (87360 : ℕ) ≠ 0 := by decide
      apply Finset.ext
      intro q
      rw [Nat.mem_primeFactors]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hq, hdvd, _⟩
        rw [h87] at hdvd
        have h1 : q ∣ 2 ^ 6 ∨ q ∣ 3 * 5 * 7 * 13 :=
          hq.dvd_mul.mp (by simpa [mul_assoc] using hdvd)
        rcases h1 with h2 | hrest
        · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2)
        · have h2 : q ∣ 3 ∨ q ∣ 5 * 7 * 13 := hq.dvd_mul.mp (by simpa [mul_assoc] using hrest)
          rcases h2 with h3 | hrest2
          · right; left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
          · have h3 : q ∣ 5 ∨ q ∣ 7 * 13 := hq.dvd_mul.mp (by simpa [mul_assoc] using hrest2)
            rcases h3 with h5 | hrest3
            · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp h5
            · have h4 : q ∣ 7 ∨ q ∣ 13 := hq.dvd_mul.mp hrest3
              rcases h4 with h7 | h13
              · right; right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h7
              · right; right; right; right; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h13
      · rintro (rfl | rfl | rfl | rfl | rfl) <;> refine ⟨by norm_num, by norm_num, hne0⟩
    rw [hpf]
    decide

/-- Complete classification for `ω(n) ≤ 5`: `n ∈ {6, 60, 90, 87360}`. -/
theorem classify_omega_le_five (n : ℕ) :
    ((∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n) ∧
      n.primeFactors.card ≤ 5) ↔
      (n = 6 ∨ n = 60 ∨ n = 90 ∨ n = 87360) := by
  constructor
  · rintro ⟨hn, hω⟩
    by_cases h5 : n.primeFactors.card = 5
    · exact Or.inr (Or.inr (Or.inr ((classify_omega_eq_five n).mp ⟨hn, h5⟩)))
    · have hne4 := omega_ne_four n hn
      have hle3 : n.primeFactors.card ≤ 3 := by omega
      rcases (PPL133.classify_omega_le_three n).mp ⟨hn, hle3⟩ with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · have h := (PPL133.classify_omega_le_three 6).mpr (Or.inl rfl)
      exact ⟨h.1, by omega⟩
    · have h := (PPL133.classify_omega_le_three 60).mpr (Or.inr (Or.inl rfl))
      exact ⟨h.1, by omega⟩
    · have h := (PPL133.classify_omega_le_three 90).mpr (Or.inr (Or.inr rfl))
      exact ⟨h.1, by omega⟩
    · have h := (classify_omega_eq_five 87360).mpr rfl
      exact ⟨h.1, by omega⟩

end SmallOmegaClassification

/-! ## Section 4: The Seven Exhaustive Branches for `ω(n) ≥ 6` -/

section SevenBranches

/-- Peel a prefix of length `m < k` from `(x, k)` with `∏_{i<k} (1 - 1/x_i) = 1/2`
and `∏_{i<k} x_i = 2 * n`. -/
private lemma peel_prefix {k m n a b : ℕ} {x : ℕ → ℕ}
    (hm : m < k)
    (hx_ge : ∀ i < k, 2 ≤ x i)
    (hx_prod : ∏ i ∈ Finset.range k, x i = 2 * n)
    (hx_rat : ∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) = (1 : ℝ) / 2)
    (hab : a * (2 * ∏ i ∈ Finset.range m, (x i - 1)) = b * (∏ i ∈ Finset.range m, x i))
    (hb : 1 ≤ b) :
    (∏ j ∈ Finset.range (k - m), (1 - 1 / (x (m + j) : ℝ)) = (a : ℝ) / (b : ℝ)) ∧
    ((∏ i ∈ Finset.range m, x i) * (∏ j ∈ Finset.range (k - m), x (m + j)) = 2 * n) := by
  have hsplit_x : (∏ i ∈ Finset.range m, x i) * (∏ j ∈ Finset.range (k - m), x (m + j)) = 2 * n := by
    have hk_eq : k = m + (k - m) := by omega
    rw [← hx_prod]
    conv_rhs => rw [hk_eq, Finset.prod_range_add]
  refine ⟨?_, hsplit_x⟩
  have hsplit_r :
      (∏ i ∈ Finset.range m, (1 - 1 / (x i : ℝ))) *
        (∏ j ∈ Finset.range (k - m), (1 - 1 / (x (m + j) : ℝ))) = (1 : ℝ) / 2 := by
    have hk_eq : k = m + (k - m) := by omega
    rw [← hx_rat]
    conv_rhs => rw [hk_eq, Finset.prod_range_add]
  have hpre :
      ∏ i ∈ Finset.range m, (1 - 1 / (x i : ℝ)) =
        ((∏ i ∈ Finset.range m, (x i - 1) : ℕ) : ℝ) / ((∏ i ∈ Finset.range m, x i : ℕ) : ℝ) := by
    push_cast
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hxi := hx_ge i (by have := Finset.mem_range.mp hi; omega)
    have hxi_pos : (0 : ℝ) < (x i : ℝ) := by exact_mod_cast (by omega : 0 < x i)
    rw [Nat.cast_sub (by omega : 1 ≤ x i), Nat.cast_one]
    field_simp [ne_of_gt hxi_pos]
  rw [hpre] at hsplit_r
  have hP_pos : (0 : ℝ) < ((∏ i ∈ Finset.range m, x i : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun i hi => by
      have := hx_ge i (by have := Finset.mem_range.mp hi; omega); omega
  have hQ_pos : (0 : ℝ) < ((∏ i ∈ Finset.range m, (x i - 1) : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun i hi => by
      have := hx_ge i (by have := Finset.mem_range.mp hi; omega); omega
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hab_r : (a : ℝ) * (2 * ((∏ i ∈ Finset.range m, (x i - 1) : ℕ) : ℝ)) =
      (b : ℝ) * ((∏ i ∈ Finset.range m, x i : ℕ) : ℝ) := by
    exact_mod_cast hab
  have h1 := congrArg (fun t => t * ((∏ i ∈ Finset.range m, x i : ℕ) : ℝ) /
      ((∏ i ∈ Finset.range m, (x i - 1) : ℕ) : ℝ)) hsplit_r
  have hL : (((∏ i ∈ Finset.range m, (x i - 1) : ℕ) : ℝ) / ((∏ i ∈ Finset.range m, x i : ℕ) : ℝ)) *
      (∏ j ∈ Finset.range (k - m), (1 - 1 / (x (m + j) : ℝ))) *
      ((∏ i ∈ Finset.range m, x i : ℕ) : ℝ) / ((∏ i ∈ Finset.range m, (x i - 1) : ℕ) : ℝ) =
      ∏ j ∈ Finset.range (k - m), (1 - 1 / (x (m + j) : ℝ)) := by
    field_simp [ne_of_gt hP_pos, ne_of_gt hQ_pos]
  have hR : ((1 : ℝ) / 2) * ((∏ i ∈ Finset.range m, x i : ℕ) : ℝ) /
      ((∏ i ∈ Finset.range m, (x i - 1) : ℕ) : ℝ) = (a : ℝ) / (b : ℝ) := by
    field_simp [ne_of_gt hQ_pos, ne_of_gt hb_pos]
    linarith
  linarith

private lemma branch1_x0_ge_6 {k n : ℕ} {x p : ℕ → ℕ}
    (hk : 6 ≤ k)
    (hx_mono : ∀ i j, i ≤ j → j < k → x i ≤ x j)
    (hx_ge2 : ∀ i < k, 2 ≤ x i)
    (hp_inj : ∀ i j, i < k → j < k → i ≠ j → p i ≠ p j)
    (hp_even : ∀ i < k, p i ≠ 2 → Even (x i))
    (hx_prod : ∏ i ∈ Finset.range k, x i = 2 * n)
    (hx_rat : ∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) = (1 : ℝ) / 2)
    (h0 : 6 ≤ x 0) (h1 : 8 ≤ x 1) (h2 : 10 ≤ x 2)
    (h3 : 12 ≤ x 3) (h4 : 14 ≤ x 4) (h5 : 17 ≤ x 5) :
    n < 2 ^ (2 ^ (k - 1)) := by
  let M : ℕ → ℕ := fun i => match i with
    | 0 => 6 | 1 => 8 | 2 => 10 | 3 => 12 | 4 => 14 | _ => 17
  have hM2 : ∀ i < 6, 2 ≤ M i := fun i hi => by interval_cases i <;> decide
  have hMx : ∀ i < 6, M i ≤ x i := fun i hi => by interval_cases i <;> simp [M] <;> omega
  have hk7 : 7 ≤ k := by
    by_contra hlt
    have hk6 : k = 6 := by omega
    subst hk6
    have hle := prod_one_sub_inv_le_of_le M x hM2 hMx
    rw [hx_rat] at hle
    simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, M] at hle
    norm_num at hle
  have hprodM : ∏ j ∈ Finset.range 6, M j = 1370880 := by
    simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, M]
    norm_num
  have hres := multistep_cook_nielsen k 6 1 2 2 20 34272 M x
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hx_mono hx_ge2 hM2 hMx (by push_cast; exact hx_rat)
    (by simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, M]; norm_num)
    (by rw [hprodM])
    (fun u hu6 huk => ⟨even_prod_prefix hp_inj hp_even (by omega) (by omega), dvd_rfl⟩)
  rcases hres with hfull | ⟨hk8, hfail⟩
  · rw [hprodM, hx_prod] at hfull
    rw [show (20 + 1 : ℕ) = 21 by norm_num] at hfull
    have hpow : 1370880 * 21 ^ (2 ^ (k - 6)) ≤ 40 * 2 ^ (2 ^ (k - 1)) := by
      have h := two_pow_bound_of_base 1370880 40 21 5 1 (k - 6)
        (by norm_num) (by norm_num) (by omega)
      rwa [show k - 6 + 5 = k - 1 by omega] at h
    have hlt := lt_of_lt_of_le hfull hpow
    omega
  · rw [hx_prod] at hfail
    rw [show (20 + 1 : ℕ) = 21 by norm_num] at hfail
    have hpow : (34272 * 21 ^ 2) ^ (2 ^ (k - 7)) ≤ 2 ^ (2 ^ (k - 1)) := by
      have h := two_pow_bound_of_base 1 1 (34272 * 21 ^ 2) 6 1 (k - 7)
        (by norm_num) (by norm_num) (by omega)
      simp only [one_mul] at h
      rwa [show k - 7 + 6 = k - 1 by omega] at h
    have hsub : k - 6 - 1 = k - 7 := by omega
    rw [hsub] at hfail
    have hlt := lt_of_lt_of_le hfail (Nat.mul_le_mul_left 2 hpow)
    omega

private lemma branch2_4_ge8 {k n : ℕ} {x : ℕ → ℕ}
    (hk : 6 ≤ k)
    (hx_mono : ∀ i j, i ≤ j → j < k → x i ≤ x j)
    (hx_ge2 : ∀ i < k, 2 ≤ x i)
    (hx_prod : ∏ i ∈ Finset.range k, x i = 2 * n)
    (hx_rat : ∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) = (1 : ℝ) / 2)
    (hx0 : x 0 = 4) (h1 : 8 ≤ x 1) (h2 : 12 ≤ x 2) (h3 : 14 ≤ x 3) (h4 : 17 ≤ x 4) :
    n < 2 ^ (2 ^ (k - 1)) := by
  have hpeel := peel_prefix (m := 1) (a := 2) (b := 3) (n := n) (by omega) hx_ge2 hx_prod hx_rat
    (by simp [hx0]) (by norm_num)
  have hz_rat := hpeel.1
  have hz_prod : 4 * ∏ j ∈ Finset.range (k - 1), x (1 + j) = 2 * n := by
    simpa [hx0] using hpeel.2
  let M : ℕ → ℕ := fun j => match j with | 0 => 8 | 1 => 12 | 2 => 14 | _ => 17
  have hM2 : ∀ j < 4, 2 ≤ M j := fun j hj => by interval_cases j <;> decide
  have hMz : ∀ j < 4, M j ≤ x (1 + j) := fun j hj => by interval_cases j <;> simp [M] <;> omega
  have hprodM : ∏ j ∈ Finset.range 4, M j = 22848 := by
    simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, M]; norm_num
  have hres := multistep_cook_nielsen (k - 1) 4 2 3 1 20 2285 M (fun j => x (1 + j))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun i j hij hj => hx_mono (1 + i) (1 + j) (by omega) (by omega))
    (fun j hj => hx_ge2 (1 + j) (by omega)) hM2 hMz hz_rat
    (by simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, M]; norm_num)
    (by rw [hprodM]; norm_num)
    (fun u _ _ => ⟨one_dvd _, one_dvd _⟩)
  rcases hres with hfull | ⟨hk6, hfail⟩
  · rw [hprodM] at hfull
    rw [show (20 + 1 : ℕ) = 21 by norm_num] at hfull
    have hpow : (4 * 22848) * 21 ^ (2 ^ (k - 5)) ≤ 40 * 2 ^ (2 ^ (k - 1)) := by
      have h := two_pow_bound_of_base (4 * 22848) 40 21 4 1 (k - 5)
        (by norm_num) (by norm_num) (by omega)
      rwa [show k - 5 + 4 = k - 1 by omega] at h
    have hsub : k - 1 - 4 = k - 5 := by omega
    rw [hsub] at hfull
    have hfull2 : 20 * (2 * n) < (4 * 22848) * 21 ^ (2 ^ (k - 5)) := by
      calc 20 * (2 * n) = 4 * (20 * ∏ j ∈ Finset.range (k - 1), x (1 + j)) := by rw [← hz_prod]; ring
        _ < 4 * (22848 * 21 ^ (2 ^ (k - 5))) := Nat.mul_lt_mul_of_pos_left hfull (by omega)
        _ = (4 * 22848) * 21 ^ (2 ^ (k - 5)) := by ring
    have hlt := lt_of_lt_of_le hfull2 hpow
    omega
  · rw [show (20 + 1 : ℕ) = 21 by norm_num] at hfail
    have hpow : 4 * (2285 * 21 ^ 2) ^ (2 ^ (k - 6)) ≤ 4 * 2 ^ (2 ^ (k - 1)) := by
      have h := two_pow_bound_of_base 4 4 (2285 * 21 ^ 2) 5 1 (k - 6)
        (by norm_num) (by norm_num) (by omega)
      rwa [show k - 6 + 5 = k - 1 by omega] at h
    have hsub : k - 1 - 4 - 1 = k - 6 := by omega
    rw [hsub] at hfail
    have hfail2 : 2 * (2 * n) < 4 * (2285 * 21 ^ 2) ^ (2 ^ (k - 6)) := by
      calc 2 * (2 * n) = 4 * (2 * ∏ j ∈ Finset.range (k - 1), x (1 + j)) := by rw [← hz_prod]; ring
        _ < 4 * (1 * (2285 * 21 ^ 2) ^ (2 ^ (k - 6))) := Nat.mul_lt_mul_of_pos_left hfail (by omega)
        _ = 4 * (2285 * 21 ^ 2) ^ (2 ^ (k - 6)) := by ring
    have hlt := lt_of_lt_of_le hfail2 hpow
    omega

private lemma branch3_4_6_ge12 {k n : ℕ} {x : ℕ → ℕ}
    (hk : 6 ≤ k)
    (hx_mono : ∀ i j, i ≤ j → j < k → x i ≤ x j)
    (hx_ge2 : ∀ i < k, 2 ≤ x i)
    (hx_prod : ∏ i ∈ Finset.range k, x i = 2 * n)
    (hx_rat : ∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) = (1 : ℝ) / 2)
    (hx0 : x 0 = 4) (hx1 : x 1 = 6) (h2 : 12 ≤ x 2) (h3 : 14 ≤ x 3) (h4 : 17 ≤ x 4) :
    n < 2 ^ (2 ^ (k - 1)) := by
  have hpeel := peel_prefix (m := 2) (a := 4) (b := 5) (n := n) (by omega) hx_ge2 hx_prod hx_rat
    (by simp [Finset.prod_range_succ, hx0, hx1]) (by norm_num)
  have hz_rat := hpeel.1
  have hz_prod : 24 * ∏ j ∈ Finset.range (k - 2), x (2 + j) = 2 * n := by
    simpa [Finset.prod_range_succ, hx0, hx1] using hpeel.2
  let M : ℕ → ℕ := fun j => match j with | 0 => 12 | 1 => 14 | _ => 17
  have hM2 : ∀ j < 3, 2 ≤ M j := fun j hj => by interval_cases j <;> decide
  have hMz : ∀ j < 3, M j ≤ x (2 + j) := fun j hj => by interval_cases j <;> simp [M] <;> omega
  have hprodM : ∏ j ∈ Finset.range 3, M j = 2856 := by
    simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, M]; norm_num
  have hres := multistep_cook_nielsen (k - 2) 3 4 5 1 714 16 M (fun j => x (2 + j))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun i j hij hj => hx_mono (2 + i) (2 + j) (by omega) (by omega))
    (fun j hj => hx_ge2 (2 + j) (by omega)) hM2 hMz hz_rat
    (by simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, M]; norm_num)
    (by rw [hprodM])
    (fun u _ _ => ⟨one_dvd _, one_dvd _⟩)
  rcases hres with hfull | ⟨hk6, hfail⟩
  · rw [hprodM] at hfull
    rw [show (714 + 1 : ℕ) = 715 by norm_num] at hfull
    have hpow : (24 * 2856) * 715 ^ (2 ^ (k - 5)) ≤ (2 * 714) * 2 ^ (2 ^ (k - 1)) := by
      have h := two_pow_bound_of_base (24 * 2856) (2 * 714) 715 4 1 (k - 5)
        (by norm_num) (by norm_num) (by omega)
      rwa [show k - 5 + 4 = k - 1 by omega] at h
    have hsub : k - 2 - 3 = k - 5 := by omega
    rw [hsub] at hfull
    have hfull2 : 714 * (2 * n) < (24 * 2856) * 715 ^ (2 ^ (k - 5)) := by
      calc 714 * (2 * n) = 24 * (714 * ∏ j ∈ Finset.range (k - 2), x (2 + j)) := by rw [← hz_prod]; ring
        _ < 24 * (2856 * 715 ^ (2 ^ (k - 5))) := Nat.mul_lt_mul_of_pos_left hfull (by omega)
        _ = (24 * 2856) * 715 ^ (2 ^ (k - 5)) := by ring
    have hlt := lt_of_lt_of_le hfull2 hpow
    omega
  · rw [show (714 + 1 : ℕ) = 715 by norm_num] at hfail
    have hpow : 24 * (16 * 715 ^ 2) ^ (2 ^ (k - 6)) ≤ 8 * 2 ^ (2 ^ (k - 1)) := by
      have h := two_pow_bound_of_base 24 8 (16 * 715 ^ 2) 5 1 (k - 6)
        (by norm_num) (by norm_num) (by omega)
      rwa [show k - 6 + 5 = k - 1 by omega] at h
    have hsub : k - 2 - 3 - 1 = k - 6 := by omega
    rw [hsub] at hfail
    have hfail2 : 4 * (2 * n) < 24 * (16 * 715 ^ 2) ^ (2 ^ (k - 6)) := by
      calc 4 * (2 * n) = 24 * (4 * ∏ j ∈ Finset.range (k - 2), x (2 + j)) := by rw [← hz_prod]; ring
        _ < 24 * (1 * (16 * 715 ^ 2) ^ (2 ^ (k - 6))) := Nat.mul_lt_mul_of_pos_left hfail (by omega)
        _ = 24 * (16 * 715 ^ 2) ^ (2 ^ (k - 6)) := by ring
    have hlt := lt_of_lt_of_le hfail2 hpow
    omega

private lemma branch4_4_6_8_ge14 {k n : ℕ} {x : ℕ → ℕ}
    (hk : 6 ≤ k)
    (hx_mono : ∀ i j, i ≤ j → j < k → x i ≤ x j)
    (hx_ge2 : ∀ i < k, 2 ≤ x i)
    (hx_prod : ∏ i ∈ Finset.range k, x i = 2 * n)
    (hx_rat : ∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) = (1 : ℝ) / 2)
    (hx0 : x 0 = 4) (hx1 : x 1 = 6) (hx2 : x 2 = 8) (h3 : 14 ≤ x 3) :
    n < 2 ^ (2 ^ (k - 1)) := by
  have hpeel := peel_prefix (m := 3) (a := 32) (b := 35) (n := n) (by omega) hx_ge2 hx_prod hx_rat
    (by simp [Finset.prod_range_succ, hx0, hx1, hx2]) (by norm_num)
  have hz_rat := hpeel.1
  have hz_prod : 192 * ∏ j ∈ Finset.range (k - 3), x (3 + j) = 2 * n := by
    simpa [Finset.prod_range_succ, hx0, hx1, hx2] using hpeel.2
  let M : ℕ → ℕ := fun _ => 14
  have hM2 : ∀ j < 1, 2 ≤ M j := fun _ _ => by decide
  have hMz : ∀ j < 1, M j ≤ x (3 + j) := fun j hj => by
    have : j = 0 := by omega
    subst this; simpa [M] using h3
  have hprodM : ∏ j ∈ Finset.range 1, M j = 14 := by simp [M]
  have hres := multistep_cook_nielsen (k - 3) 1 32 35 1 64 7 M (fun j => x (3 + j))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun i j hij hj => hx_mono (3 + i) (3 + j) (by omega) (by omega))
    (fun j hj => hx_ge2 (3 + j) (by omega)) hM2 hMz hz_rat
    (by simp [M]; norm_num)
    (by rw [hprodM])
    (fun u _ _ => ⟨one_dvd _, one_dvd _⟩)
  rcases hres with hfull | ⟨hk5, hfail⟩
  · rw [hprodM] at hfull
    rw [show (64 + 1 : ℕ) = 65 by norm_num] at hfull
    have hpow : (192 * 14) * 65 ^ (2 ^ (k - 4)) ≤ (2 * 64) * 2 ^ (2 ^ (k - 1)) := by
      have h := two_pow_bound_of_base (192 * 14) (2 * 64) 65 3 2 (k - 4)
        (by norm_num) (by norm_num) (by omega)
      rwa [show k - 4 + 3 = k - 1 by omega] at h
    have hsub : k - 3 - 1 = k - 4 := by omega
    rw [hsub] at hfull
    have hfull2 : 64 * (2 * n) < (192 * 14) * 65 ^ (2 ^ (k - 4)) := by
      calc 64 * (2 * n) = 192 * (64 * ∏ j ∈ Finset.range (k - 3), x (3 + j)) := by rw [← hz_prod]; ring
        _ < 192 * (14 * 65 ^ (2 ^ (k - 4))) := Nat.mul_lt_mul_of_pos_left hfull (by omega)
        _ = (192 * 14) * 65 ^ (2 ^ (k - 4)) := by ring
    have hlt := lt_of_lt_of_le hfull2 hpow
    omega
  · rw [show (64 + 1 : ℕ) = 65 by norm_num] at hfail
    have hpow : 192 * (7 * 65 ^ 2) ^ (2 ^ (k - 5)) ≤ 64 * 2 ^ (2 ^ (k - 1)) := by
      have h := two_pow_bound_of_base 192 64 (7 * 65 ^ 2) 4 1 (k - 5)
        (by norm_num) (by norm_num) (by omega)
      rwa [show k - 5 + 4 = k - 1 by omega] at h
    have hsub : k - 3 - 1 - 1 = k - 5 := by omega
    rw [hsub] at hfail
    have hfail2 : 32 * (2 * n) < 192 * (7 * 65 ^ 2) ^ (2 ^ (k - 5)) := by
      calc 32 * (2 * n) = 192 * (32 * ∏ j ∈ Finset.range (k - 3), x (3 + j)) := by rw [← hz_prod]; ring
        _ < 192 * (1 * (7 * 65 ^ 2) ^ (2 ^ (k - 5))) := Nat.mul_lt_mul_of_pos_left hfail (by omega)
        _ = 192 * (7 * 65 ^ 2) ^ (2 ^ (k - 5)) := by ring
    have hlt := lt_of_lt_of_le hfail2 hpow
    omega

private lemma branch5a_4_6_8_12_390 {k n : ℕ} {x p e : ℕ → ℕ}
    (hk : 6 ≤ k)
    (hx_mono : ∀ i j, i ≤ j → j < k → x i ≤ x j)
    (hx_ge2 : ∀ i < k, 2 ≤ x i)
    (hp_info : ∀ i < k, Nat.Prime (p i) ∧ 1 ≤ e i ∧ x i = (p i) ^ (e i) + 1)
    (hx_prod : ∏ i ∈ Finset.range k, x i = 2 * n)
    (hx_rat : ∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) = (1 : ℝ) / 2)
    (hx0 : x 0 = 4) (hx1 : x 1 = 6) (hx2 : x 2 = 8) (hx3 : x 3 = 12) (hx4 : x 4 = 390) :
    n < 2 ^ (2 ^ (k - 1)) := by
  have hpeel := peel_prefix (m := 5) (a := 29952) (b := 29953) (n := n) (by omega) hx_ge2 hx_prod hx_rat
    (by simp [Finset.prod_range_succ, hx0, hx1, hx2, hx3, hx4]) (by norm_num)
  have hz_rat := hpeel.1
  have hz_prod : 898560 * ∏ j ∈ Finset.range (k - 5), x (5 + j) = 2 * n := by
    have h := hpeel.2
    simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul] at h
    rw [hx0, hx1, hx2, hx3, hx4] at h
    simpa using h
  have hk7 : 7 ≤ k := by
    by_contra hlt
    have hk6 : k = 6 := by omega
    rw [hk6] at hz_rat
    simp only [show 6 - 5 = 1 by omega, Finset.range_one, Finset.prod_singleton] at hz_rat
    have hx5_pos : (0 : ℝ) < (x 5 : ℝ) := by
      exact_mod_cast (by have := hx_ge2 5 (by omega); omega : 0 < x 5)
    have h1 := congrArg (fun t => 29953 * (x 5 : ℝ) * t) hz_rat
    field_simp [ne_of_gt hx5_pos] at h1
    push_cast at h1
    have hx5_r : (x 5 : ℝ) = 29953 := by linarith
    have hx5_eq : x 5 = 29953 := by exact_mod_cast hx5_r
    exact x_ne_29953 hp_info (by omega) hx5_eq
  have hnb := PPL133.nielsen_product_bound (k - 5) (by omega) 29952 29953 (by norm_num) (by norm_num)
    (fun j => x (5 + j))
    (fun i j hij hj => hx_mono (5 + i) (5 + j) (by omega) (by omega))
    (fun j hj => hx_ge2 (5 + j) (by omega))
    (by rw [hz_rat])
    (fun u hu => by
      have hgt := prefix_prod_gt_of_eq (k - 5) (fun j => x (5 + j))
        (fun j hj => hx_ge2 (5 + j) (by omega)) u hu
      rw [hz_rat] at hgt
      simpa using hgt)
  have hn_eq : n = 15 * (29952 * ∏ j ∈ Finset.range (k - 5), x (5 + j)) := by omega
  have hpow : 15 * 29953 ^ (2 ^ (k - 5)) ≤ 2 ^ (2 ^ (k - 1)) := by
    have h := two_pow_bound_of_base 15 1 29953 4 2 (k - 5)
      (by norm_num) (by norm_num) (by omega)
    simp only [one_mul] at h
    rwa [show k - 5 + 4 = k - 1 by omega] at h
  calc
    n = 15 * (29952 * ∏ j ∈ Finset.range (k - 5), x (5 + j)) := hn_eq
    _ < 15 * 29953 ^ (2 ^ (k - 5)) := Nat.mul_lt_mul_of_pos_left hnb (by omega)
    _ ≤ 2 ^ (2 ^ (k - 1)) := hpow

private lemma branch5b1_4_6_8_12_398 {k n : ℕ} {x : ℕ → ℕ}
    (hk : 6 ≤ k)
    (hx_mono : ∀ i j, i ≤ j → j < k → x i ≤ x j)
    (hx_ge2 : ∀ i < k, 2 ≤ x i)
    (hx_prod : ∏ i ∈ Finset.range k, x i = 2 * n)
    (hx_rat : ∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) = (1 : ℝ) / 2)
    (hx0 : x 0 = 4) (hx1 : x 1 = 6) (hx2 : x 2 = 8) (hx3 : x 3 = 12) (hx4 : x 4 = 398) :
    n < 2 ^ (2 ^ (k - 1)) := by
  have hpeel := peel_prefix (m := 5) (a := 152832) (b := 152845) (n := n) (by omega) hx_ge2 hx_prod hx_rat
    (by simp [Finset.prod_range_succ, hx0, hx1, hx2, hx3, hx4]) (by norm_num)
  have hz_rat := hpeel.1
  have hz_prod : 916992 * ∏ j ∈ Finset.range (k - 5), x (5 + j) = 2 * n := by
    have h := hpeel.2
    simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul] at h
    rw [hx0, hx1, hx2, hx3, hx4] at h
    simpa using h
  have hk7 : 7 ≤ k := by
    by_contra hlt
    have hk6 : k = 6 := by omega
    rw [hk6] at hz_rat
    simp only [show 6 - 5 = 1 by omega, Finset.range_one, Finset.prod_singleton] at hz_rat
    have hx5_pos : (0 : ℝ) < (x 5 : ℝ) := by
      exact_mod_cast (by have := hx_ge2 5 (by omega); omega : 0 < x 5)
    have h1 := congrArg (fun t => 152845 * (x 5 : ℝ) * t) hz_rat
    field_simp [ne_of_gt hx5_pos] at h1
    push_cast at h1
    have h13 : (13 : ℝ) * (x 5 : ℝ) = 152845 := by linarith
    have h13n : 13 * x 5 = 152845 := by exact_mod_cast h13
    omega
  have hx5_ge : 11758 ≤ x 5 := by
    have hgt := prefix_prod_gt_of_eq (k - 5) (fun j => x (5 + j))
      (fun j hj => hx_ge2 (5 + j) (by omega)) 1 (by omega)
    rw [hz_rat, Finset.range_one, Finset.prod_singleton] at hgt
    have hx5_pos : (0 : ℝ) < (x 5 : ℝ) := by
      exact_mod_cast (by have := hx_ge2 5 (by omega); omega : 0 < x 5)
    have h1 := (mul_lt_mul_iff_right₀ hx5_pos).mpr hgt
    have h13 : (13 : ℝ) * (x 5 : ℝ) > 152845 := by
      field_simp [ne_of_gt hx5_pos] at h1
      push_cast at h1
      linarith
    have h13n : 152845 < 13 * x 5 := by exact_mod_cast h13
    omega
  let M : ℕ → ℕ := fun _ => 11758
  have hM2 : ∀ j < 1, 2 ≤ M j := fun _ _ => by decide
  have hMz : ∀ j < 1, M j ≤ x (5 + j) := fun j hj => by
    have : j = 0 := by omega
    subst this; simpa [M] using hx5_ge
  have hprodM : ∏ j ∈ Finset.range 1, M j = 11758 := by simp [M]
  have hres := multistep_cook_nielsen (k - 5) 1 152832 152845 1 199666518 9 M (fun j => x (5 + j))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun i j hij hj => hx_mono (5 + i) (5 + j) (by omega) (by omega))
    (fun j hj => hx_ge2 (5 + j) (by omega)) hM2 hMz hz_rat
    (by simp [M]; norm_num)
    (by rw [hprodM]; norm_num)
    (fun u _ _ => ⟨one_dvd _, one_dvd _⟩)
  rcases hres with hfull | ⟨hk8, hfail⟩
  · rw [hprodM] at hfull
    rw [show (199666518 + 1 : ℕ) = 199666519 by norm_num] at hfull
    have hpow : (916992 * 11758) * 199666519 ^ (2 ^ (k - 6)) ≤
        (2 * 199666518) * 2 ^ (2 ^ (k - 1)) := by
      have h := two_pow_bound_of_base (916992 * 11758) (2 * 199666518) 199666519 5 1 (k - 6)
        (by norm_num) (by norm_num) (by omega)
      rwa [show k - 6 + 5 = k - 1 by omega] at h
    have hsub : k - 5 - 1 = k - 6 := by omega
    rw [hsub] at hfull
    have hfull2 : 199666518 * (2 * n) < (916992 * 11758) * 199666519 ^ (2 ^ (k - 6)) := by
      calc 199666518 * (2 * n) =
            916992 * (199666518 * ∏ j ∈ Finset.range (k - 5), x (5 + j)) := by rw [← hz_prod]; ring
        _ < 916992 * (11758 * 199666519 ^ (2 ^ (k - 6))) := Nat.mul_lt_mul_of_pos_left hfull (by omega)
        _ = (916992 * 11758) * 199666519 ^ (2 ^ (k - 6)) := by ring
    have hlt := lt_of_lt_of_le hfull2 hpow
    omega
  · rw [show (199666518 + 1 : ℕ) = 199666519 by norm_num] at hfail
    have hpow : 916992 * (9 * 199666519 ^ 2) ^ (2 ^ (k - 7)) ≤
        (2 * 152832) * 2 ^ (2 ^ (k - 1)) := by
      have h := two_pow_bound_of_base 916992 (2 * 152832) (9 * 199666519 ^ 2) 6 1 (k - 7)
        (by norm_num) (by norm_num) (by omega)
      rwa [show k - 7 + 6 = k - 1 by omega] at h
    have hsub : k - 5 - 1 - 1 = k - 7 := by omega
    rw [hsub] at hfail
    have hfail2 : 152832 * (2 * n) < 916992 * (9 * 199666519 ^ 2) ^ (2 ^ (k - 7)) := by
      calc 152832 * (2 * n) =
            916992 * (152832 * ∏ j ∈ Finset.range (k - 5), x (5 + j)) := by rw [← hz_prod]; ring
        _ < 916992 * (1 * (9 * 199666519 ^ 2) ^ (2 ^ (k - 7))) :=
            Nat.mul_lt_mul_of_pos_left hfail (by omega)
        _ = 916992 * (9 * 199666519 ^ 2) ^ (2 ^ (k - 7)) := by ring
    have hlt := lt_of_lt_of_le hfail2 hpow
    omega

private lemma branch5b2_4_6_8_12_ge402 {k n : ℕ} {x : ℕ → ℕ}
    (hk : 6 ≤ k)
    (hx_mono : ∀ i j, i ≤ j → j < k → x i ≤ x j)
    (hx_ge2 : ∀ i < k, 2 ≤ x i)
    (hx_prod : ∏ i ∈ Finset.range k, x i = 2 * n)
    (hx_rat : ∏ i ∈ Finset.range k, (1 - 1 / (x i : ℝ)) = (1 : ℝ) / 2)
    (hx0 : x 0 = 4) (hx1 : x 1 = 6) (hx2 : x 2 = 8) (hx3 : x 3 = 12) (h4 : 402 ≤ x 4) :
    n < 2 ^ (2 ^ (k - 1)) := by
  have hpeel := peel_prefix (m := 4) (a := 384) (b := 385) (n := n) (by omega) hx_ge2 hx_prod hx_rat
    (by simp [Finset.prod_range_succ, hx0, hx1, hx2, hx3]) (by norm_num)
  have hz_rat := hpeel.1
  have hz_prod : 2304 * ∏ j ∈ Finset.range (k - 4), x (4 + j) = 2 * n := by
    have h := hpeel.2
    simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul] at h
    rw [hx0, hx1, hx2, hx3] at h
    simpa using h
  let M : ℕ → ℕ := fun _ => 402
  have hM2 : ∀ j < 1, 2 ≤ M j := fun _ _ => by decide
  have hMz : ∀ j < 1, M j ≤ x (4 + j) := fun j hj => by
    have : j = 0 := by omega
    subst this; simpa [M] using h4
  have hprodM : ∏ j ∈ Finset.range 1, M j = 402 := by simp [M]
  have hres := multistep_cook_nielsen (k - 4) 1 384 385 1 9081 17 M (fun j => x (4 + j))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun i j hij hj => hx_mono (4 + i) (4 + j) (by omega) (by omega))
    (fun j hj => hx_ge2 (4 + j) (by omega)) hM2 hMz hz_rat
    (by simp [M]; norm_num)
    (by rw [hprodM]; norm_num)
    (fun u _ _ => ⟨one_dvd _, one_dvd _⟩)
  rcases hres with hfull | ⟨hk7, hfail⟩
  · rw [hprodM] at hfull
    rw [show (9081 + 1 : ℕ) = 9082 by norm_num] at hfull
    have hpow : (2304 * 402) * 9082 ^ (2 ^ (k - 5)) ≤ (2 * 9081) * 2 ^ (2 ^ (k - 1)) := by
      have h := two_pow_bound_of_base (2304 * 402) (2 * 9081) 9082 4 1 (k - 5)
        (by norm_num) (by norm_num) (by omega)
      rwa [show k - 5 + 4 = k - 1 by omega] at h
    have hsub : k - 4 - 1 = k - 5 := by omega
    rw [hsub] at hfull
    have hfull2 : 9081 * (2 * n) < (2304 * 402) * 9082 ^ (2 ^ (k - 5)) := by
      calc 9081 * (2 * n) = 2304 * (9081 * ∏ j ∈ Finset.range (k - 4), x (4 + j)) := by rw [← hz_prod]; ring
        _ < 2304 * (402 * 9082 ^ (2 ^ (k - 5))) := Nat.mul_lt_mul_of_pos_left hfull (by omega)
        _ = (2304 * 402) * 9082 ^ (2 ^ (k - 5)) := by ring
    have hlt := lt_of_lt_of_le hfull2 hpow
    omega
  · rw [show (9081 + 1 : ℕ) = 9082 by norm_num] at hfail
    have hpow : 2304 * (17 * 9082 ^ 2) ^ (2 ^ (k - 6)) ≤ (2 * 384) * 2 ^ (2 ^ (k - 1)) := by
      have h := two_pow_bound_of_base 2304 (2 * 384) (17 * 9082 ^ 2) 5 1 (k - 6)
        (by norm_num) (by norm_num) (by omega)
      rwa [show k - 6 + 5 = k - 1 by omega] at h
    have hsub : k - 4 - 1 - 1 = k - 6 := by omega
    rw [hsub] at hfail
    have hfail2 : 384 * (2 * n) < 2304 * (17 * 9082 ^ 2) ^ (2 ^ (k - 6)) := by
      calc 384 * (2 * n) = 2304 * (384 * ∏ j ∈ Finset.range (k - 4), x (4 + j)) := by rw [← hz_prod]; ring
        _ < 2304 * (1 * (17 * 9082 ^ 2) ^ (2 ^ (k - 6))) := Nat.mul_lt_mul_of_pos_left hfail (by omega)
        _ = 2304 * (17 * 9082 ^ 2) ^ (2 ^ (k - 6)) := by ring
    have hlt := lt_of_lt_of_le hfail2 hpow
    omega

end SevenBranches

/-! ## Section 5: Headline Unconditional `√2` Upper Bounds -/

section HeadlineTheorems

/-- **MAIN NEW WORLD-RECORD UPPER BOUND (PPL 133 / Erdős Problem #1052):**
For **every** unitary perfect number `n` with `ω(n) ≥ 6`,
`n < 2^(2^(ω(n) - 1)) = (√2)^(2^(ω(n)))`,
halving the exponent of Goto (2007) `n < 2^(2^(ω(n)))` and beating `PPL133_Main`'s
`n < 3^(2^(ω(n) - 1))` (`√3` base). -/
theorem sqrt_two_upper_bound_of_omega_ge_six (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n)
    (hω : 6 ≤ n.primeFactors.card) :
    n < 2 ^ (2 ^ (n.primeFactors.card - 1)) := by
  have hv2_ge4 : 4 ≤ n.factorization 2 := by
    by_contra hlt
    have hle3 : n.factorization 2 ≤ 3 := by omega
    rcases (PPL133.classify_v2_le_three n).mp ⟨hn, hle3⟩ with rfl | rfl | rfl
    · have := ((PPL133.classify_omega_le_three 6).mpr (Or.inl rfl)).2; omega
    · have := ((PPL133.classify_omega_le_three 60).mpr (Or.inr (Or.inl rfl))).2; omega
    · have := ((PPL133.classify_omega_le_three 90).mpr (Or.inr (Or.inr rfl))).2; omega
  rcases sorted_primePow_components_of_upn n hn hv2_ge4 with
    ⟨x, p, e, _, hx_lt, hx_mono, hp_info, hp_inj, hp_two, hp_even, hx_prod, _, hx_rat⟩
  set k := n.primeFactors.card
  have hge4 : ∀ i < k, 4 ≤ x i := fun i hi => x_ge_four hp_info hp_two hi
  have hx_ge2 : ∀ i < k, 2 ≤ x i := fun i hi => le_trans (by omega) (hge4 i hi)
  have heven : ∀ i < k, x i < 17 → Even (x i) := fun i hi => x_even_of_lt_17 hp_info hp_two hp_even hi
  by_cases hx0_4 : x 0 = 4
  · have hx1_ge6 : 6 ≤ x 1 := by
      have hlt01 := hx_lt 0 1 (by omega) (by omega)
      have h4 := hge4 0 (by omega)
      by_contra hlt
      have hx1_5 : x 1 = 5 := by omega
      exact absurd (heven 1 (by omega) (by omega)) (by rw [hx1_5]; decide)
    by_cases hx1_6 : x 1 = 6
    · have hx2_ge8 : 8 ≤ x 2 := by
        have hlt12 := hx_lt 1 2 (by omega) (by omega)
        by_contra hlt
        have hx2_7 : x 2 = 7 := by omega
        exact absurd (heven 2 (by omega) (by omega)) (by rw [hx2_7]; decide)
      by_cases hx2_8 : x 2 = 8
      · have hx3_ge12 : 12 ≤ x 3 := by
          have hlt23 := hx_lt 2 3 (by omega) (by omega)
          by_contra hlt
          have h11 : x 3 ≤ 11 := by omega
          have hev3 : x 3 % 2 = 0 := Nat.even_iff.mp (heven 3 (by omega) (by omega))
          have hne10 : x 3 ≠ 10 := x_ne_10_of_x0_eq_4 (by omega) hp_info hp_inj hx0_4 (i := 3) (by omega) (by omega)
          omega
        by_cases hx3_12 : x 3 = 12
        · -- x 4 ≥ 386 from prefix product < 1/2!
          have hx4_ge386 : 386 ≤ x 4 := by
            have hlt := prefix_prod_gt_of_eq k x hx_ge2 5 (by omega)
            rw [hx_rat] at hlt
            have h5 : ∏ i ∈ Finset.range 5, (1 - 1 / (x i : ℝ)) =
                (385 : ℝ) / 768 * (1 - 1 / (x 4 : ℝ)) := by
              simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul]
              rw [hx0_4, hx1_6, hx2_8, hx3_12]
              norm_num
            rw [h5] at hlt
            have hx4_pos : (0 : ℝ) < (x 4 : ℝ) := by exact_mod_cast (by have := hge4 4 (by omega); omega : 0 < x 4)
            have h1 := (mul_lt_mul_iff_right₀ hx4_pos).mpr hlt
            have hr : (385 : ℝ) < (x 4 : ℝ) := by
              field_simp [ne_of_gt hx4_pos] at h1
              linarith
            have hnat : 385 < x 4 := by exact_mod_cast hr
            omega
          by_cases hx4_le401 : x 4 ≤ 401
          · rcases x_gap_386_401 hp_info (by omega) hx4_ge386 hx4_le401 with hx4_390 | hx4_398
            · exact branch5a_4_6_8_12_390 hω hx_mono hx_ge2 hp_info hx_prod hx_rat
                hx0_4 hx1_6 hx2_8 hx3_12 hx4_390
            · exact branch5b1_4_6_8_12_398 hω hx_mono hx_ge2 hx_prod hx_rat
                hx0_4 hx1_6 hx2_8 hx3_12 hx4_398
          · exact branch5b2_4_6_8_12_ge402 hω hx_mono hx_ge2 hx_prod hx_rat
              hx0_4 hx1_6 hx2_8 hx3_12 (by omega)
        · have hx3_ge14 : 14 ≤ x 3 := by
            by_contra hlt
            have hx3_13 : x 3 = 13 := by omega
            exact absurd (heven 3 (by omega) (by omega)) (by rw [hx3_13]; decide)
          exact branch4_4_6_8_ge14 hω hx_mono hx_ge2 hx_prod hx_rat hx0_4 hx1_6 hx2_8 hx3_ge14
      · have hx2_ge12 : 12 ≤ x 2 := by
          by_contra hlt
          have h11 : x 2 ≤ 11 := by omega
          have hev2 : x 2 % 2 = 0 := Nat.even_iff.mp (heven 2 (by omega) (by omega))
          have hne10 : x 2 ≠ 10 := x_ne_10_of_x0_eq_4 (by omega) hp_info hp_inj hx0_4 (i := 2) (by omega) (by omega)
          omega
        have hx3_ge14 : 14 ≤ x 3 := by
          have hlt23 := hx_lt 2 3 (by omega) (by omega)
          by_contra hlt
          have hx3_13 : x 3 = 13 := by omega
          exact absurd (heven 3 (by omega) (by omega)) (by rw [hx3_13]; decide)
        have hx4_ge17 : 17 ≤ x 4 := by
          have hlt34 := hx_lt 3 4 (by omega) (by omega)
          by_contra hlt
          have h16 : x 4 ≤ 16 := by omega
          have hev4 : x 4 % 2 = 0 := Nat.even_iff.mp (heven 4 (by omega) (by omega))
          have hne16 : x 4 ≠ 16 := x_ne_16 hp_info (i := 4) (by omega)
          omega
        exact branch3_4_6_ge12 hω hx_mono hx_ge2 hx_prod hx_rat hx0_4 hx1_6 hx2_ge12 hx3_ge14 hx4_ge17
    · have hx1_ge8 : 8 ≤ x 1 := by
        by_contra hlt
        have hx1_7 : x 1 = 7 := by omega
        exact absurd (heven 1 (by omega) (by omega)) (by rw [hx1_7]; decide)
      have hx2_ge12 : 12 ≤ x 2 := by
        have hlt12 := hx_lt 1 2 (by omega) (by omega)
        by_contra hlt
        have h11 : x 2 ≤ 11 := by omega
        have hev2 : x 2 % 2 = 0 := Nat.even_iff.mp (heven 2 (by omega) (by omega))
        have hne10 : x 2 ≠ 10 := x_ne_10_of_x0_eq_4 (by omega) hp_info hp_inj hx0_4 (i := 2) (by omega) (by omega)
        omega
      have hx3_ge14 : 14 ≤ x 3 := by
        have hlt23 := hx_lt 2 3 (by omega) (by omega)
        by_contra hlt
        have hx3_13 : x 3 = 13 := by omega
        exact absurd (heven 3 (by omega) (by omega)) (by rw [hx3_13]; decide)
      have hx4_ge17 : 17 ≤ x 4 := by
        have hlt34 := hx_lt 3 4 (by omega) (by omega)
        by_contra hlt
        have h16 : x 4 ≤ 16 := by omega
        have hev4 : x 4 % 2 = 0 := Nat.even_iff.mp (heven 4 (by omega) (by omega))
        have hne16 : x 4 ≠ 16 := x_ne_16 hp_info (i := 4) (by omega)
        omega
      exact branch2_4_ge8 hω hx_mono hx_ge2 hx_prod hx_rat hx0_4 hx1_ge8 hx2_ge12 hx3_ge14 hx4_ge17
  · have hx0_ge6 : 6 ≤ x 0 := by
      have h0 := hge4 0 (by omega)
      by_contra hlt
      have hx0_5 : x 0 = 5 := by omega
      exact absurd (heven 0 (by omega) (by omega)) (by rw [hx0_5]; decide)
    have hx1_ge8 : 8 ≤ x 1 := by
      have hlt01 := hx_lt 0 1 (by omega) (by omega)
      by_contra hlt
      have hx1_7 : x 1 = 7 := by omega
      exact absurd (heven 1 (by omega) (by omega)) (by rw [hx1_7]; decide)
    have hx2_ge10 : 10 ≤ x 2 := by
      have hlt12 := hx_lt 1 2 (by omega) (by omega)
      by_contra hlt
      have hx2_9 : x 2 = 9 := by omega
      exact absurd (heven 2 (by omega) (by omega)) (by rw [hx2_9]; decide)
    have hx3_ge12 : 12 ≤ x 3 := by
      have hlt23 := hx_lt 2 3 (by omega) (by omega)
      by_contra hlt
      have hx3_11 : x 3 = 11 := by omega
      exact absurd (heven 3 (by omega) (by omega)) (by rw [hx3_11]; decide)
    have hx4_ge14 : 14 ≤ x 4 := by
      have hlt34 := hx_lt 3 4 (by omega) (by omega)
      by_contra hlt
      have hx4_13 : x 4 = 13 := by omega
      exact absurd (heven 4 (by omega) (by omega)) (by rw [hx4_13]; decide)
    have hx5_ge17 : 17 ≤ x 5 := by
      have hlt45 := hx_lt 4 5 (by omega) (by omega)
      by_contra hlt
      have h16 : x 5 ≤ 16 := by omega
      have hev5 : x 5 % 2 = 0 := Nat.even_iff.mp (heven 5 (by omega) (by omega))
      have hne16 : x 5 ≠ 16 := x_ne_16 hp_info (i := 5) (by omega)
      omega
    exact branch1_x0_ge_6 hω hx_mono hx_ge2 hp_inj hp_even hx_prod hx_rat
      hx0_ge6 hx1_ge8 hx2_ge10 hx3_ge12 hx4_ge14 hx5_ge17

/-- Every unitary perfect number `n ∉ {6, 60, 90, 87360}` satisfies
`n < 2^(2^(ω(n) - 1))`. -/
theorem sqrt_two_upper_bound_ne_small (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n)
    (hne : n ≠ 6 ∧ n ≠ 60 ∧ n ≠ 90 ∧ n ≠ 87360) :
    n < 2 ^ (2 ^ (n.primeFactors.card - 1)) := by
  have hge6 : 6 ≤ n.primeFactors.card := by
    by_contra hlt
    rcases (classify_omega_le_five n).mp ⟨hn, by omega⟩ with rfl | rfl | rfl | rfl
    · exact hne.1 rfl
    · exact hne.2.1 rfl
    · exact hne.2.2.1 rfl
    · exact hne.2.2.2 rfl
  exact sqrt_two_upper_bound_of_omega_ge_six n hn hge6

/-- Every unitary perfect number `n > 87360` satisfies
`n < 2^(2^(ω(n) - 1)) = (√2)^(2^(ω(n)))`. -/
theorem sqrt_two_upper_bound_gt_87360 (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n)
    (hgt : 87360 < n) :
    n < 2 ^ (2 ^ (n.primeFactors.card - 1)) :=
  sqrt_two_upper_bound_ne_small n hn ⟨by omega, by omega, by omega, by omega⟩

end HeadlineTheorems

end PPL133_SqrtTwo
