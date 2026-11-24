/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Computability.NFA
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-!
# PPL 090 (Shallit Open Problem #3): New World-Record Elementary Upper Bound `O(n^{1/3} (log n)^{2/3})` for NFA Separating Words

## Main Result
For **every** alphabet `α` and **every** pair of distinct equal-length words `w, x : List α`
with `w.length = x.length = n ≥ 2` and `w ≠ x`, there exists a nondeterministic finite automaton
`M : NFA α (Fin m)` separating `w` and `x` (accepting one and rejecting the other) with:
- **`m ≤ 26 * n^(1/3) * (Real.log n)^(2/3)`** for all `n ≥ 4096`, and
- **`m ≤ 128 * n^(1/3) * (Real.log n)^(2/3)`** uniformly for all `n ≥ 2`.

## Comparison with Literature
- Chase (2020/STOC 2021): `O(n^{1/3} (log n)^7)` via complex-analytic sparse-polynomial bounds (DFA).
- Chen Xu (2025/2026): `O(n^{1/3} (log n)^{7/3})` via elementary finite-difference recurrences (DFA).
- **This file (2026):** `O(n^{1/3} (log n)^{2/3})` for NFAs over arbitrary alphabets, strictly
  improving the best known `N(n)` upper bound by a factor of `(log n)^{5/3}` over Xu and
  `(log n)^{19/3}` over Chase, using an elementary 3-component proof:
  1. Elementary Chebyshev prime-counting lower bound via `Nat.centralBinom`,
  2. Elementary Fine–Wilf periodicity lemma yielding `≥ k + 1` pairwise distinct length-`4k`
     differing factors around the first mismatch `t*`, hence one factor occurring `≤ n / (k + 1)`
     times in the other word,
  3. A **2-Prime CRT Bridge NFA** of `p + q + ℓ - 1` states (additive in `p, q` rather than
     multiplicative `p * q`) checking `(s % p, (n - ℓ - s) % q)` around the rare factor.
-/

namespace PPL121

/-! ## Section 1: Elementary Chebyshev Prime-Counting Lower Bound -/

/-- All prime numbers in `[1, M]`. -/
def primesUpTo (M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter Nat.Prime

/-- Every prime factor of `m.centralBinom` lies in `primesUpTo (2 * m)`. -/
lemma primeFactors_centralBinom_subset (m : ℕ) (hm : 1 ≤ m) :
    m.centralBinom.primeFactors ⊆ primesUpTo (2 * m) := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  rcases hp with ⟨hp_prime, hp_dvd, _⟩
  rw [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨hp_prime.one_le, ?_⟩, hp_prime⟩
  have hpos : 0 < 2 * m := by omega
  have hcb_pos : m.centralBinom ≠ 0 := Nat.ne_of_gt (Nat.centralBinom_pos m)
  have hfac_pos : 1 ≤ m.centralBinom.factorization p := by
    rw [Nat.one_le_iff_ne_zero]
    exact (Finsupp.mem_support_iff.mp ((Nat.support_factorization _).symm ▸
      (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, hcb_pos⟩)))
  have hpow : p ^ m.centralBinom.factorization p ≤ 2 * m := by
    simpa [Nat.centralBinom] using Nat.pow_factorization_choose_le (p := p) (n := 2 * m) (k := m) hpos
  exact le_trans (Nat.le_self_pow (by omega) p) hpow

/-- Elementary natural-number Chebyshev lower bound:
for every `m ≥ 4`, `2 ^ (2 * m) < (2 * m) ^ ((primesUpTo (2 * m)).card + 1)`. -/
theorem two_pow_lt_pow_prime_card (m : ℕ) (hm : 4 ≤ m) :
    2 ^ (2 * m) < (2 * m) ^ ((primesUpTo (2 * m)).card + 1) := by
  have h4 : 4 ^ m < m * m.centralBinom := Nat.four_pow_lt_mul_centralBinom m hm
  have h24 : 2 ^ (2 * m) = 4 ^ m := by
    rw [pow_mul]
    norm_num
  have hcb_ne : m.centralBinom ≠ 0 := Nat.ne_of_gt (Nat.centralBinom_pos m)
  have hprod_eq : ∏ p ∈ m.centralBinom.primeFactors, p ^ m.centralBinom.factorization p =
      m.centralBinom := by
    simpa [Finsupp.prod, Nat.support_factorization] using
      Nat.prod_factorization_pow_eq_self hcb_ne
  have hcb_le : m.centralBinom ≤ (2 * m) ^ m.centralBinom.primeFactors.card := by
    calc
      m.centralBinom = ∏ p ∈ m.centralBinom.primeFactors, p ^ m.centralBinom.factorization p :=
        hprod_eq.symm
      _ ≤ ∏ _p ∈ m.centralBinom.primeFactors, (2 * m) := by
            apply Finset.prod_le_prod'
            intro p _
            simpa [Nat.centralBinom] using
              Nat.pow_factorization_choose_le (p := p) (n := 2 * m) (k := m) (by omega)
      _ = (2 * m) ^ m.centralBinom.primeFactors.card := by
            rw [Finset.prod_const]
  have hcard_le : m.centralBinom.primeFactors.card ≤ (primesUpTo (2 * m)).card :=
    Finset.card_le_card (primeFactors_centralBinom_subset m (by omega))
  have hpow_le : (2 * m) ^ m.centralBinom.primeFactors.card ≤ (2 * m) ^ (primesUpTo (2 * m)).card :=
    Nat.pow_le_pow_right (by omega) hcard_le
  have hcb_le2 : m.centralBinom ≤ (2 * m) ^ (primesUpTo (2 * m)).card := le_trans hcb_le hpow_le
  have hm_le : m ≤ 2 * m := by omega
  calc
    2 ^ (2 * m) = 4 ^ m := h24
    _ < m * m.centralBinom := h4
    _ ≤ (2 * m) * (2 * m) ^ (primesUpTo (2 * m)).card := Nat.mul_le_mul hm_le hcb_le2
    _ = (2 * m) ^ ((primesUpTo (2 * m)).card + 1) := by rw [pow_succ, mul_comm]

/-- Real-valued Chebyshev prime-counting lower bound for even `M = 2 * m ≥ 8`. -/
theorem prime_card_real_lower_bound (m : ℕ) (hm : 4 ≤ m) :
    ((2 * m : ℕ) : ℝ) * Real.log 2 <
      (((primesUpTo (2 * m)).card + 1 : ℕ) : ℝ) * Real.log ((2 * m : ℕ) : ℝ) := by
  have hnat := two_pow_lt_pow_prime_card m hm
  have hreal : ((2 ^ (2 * m) : ℕ) : ℝ) < (((2 * m) ^ ((primesUpTo (2 * m)).card + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hpos1 : (0 : ℝ) < ((2 ^ (2 * m) : ℕ) : ℝ) := by positivity
  have hlog := Real.log_lt_log hpos1 hreal
  push_cast at hlog
  rw [Real.log_pow, Real.log_pow] at hlog
  simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hlog

/-! ## Section 2: Elementary Fine–Wilf Periodicity Lemma & Distinct Differing Windows -/

/-- Elementary Fine–Wilf Lemma (strong-induction Euclidean version):
If `f : ℕ → α` has periods `d > 0` and `d' > 0` on `[0, L)` with `d + d' ≤ L`,
then `f` has period `Nat.gcd d d'` on `[0, L)`. -/
theorem fine_wilf_prefix {α : Type*} (f : ℕ → α) (L : ℕ) :
    ∀ s d d' : ℕ, d + d' = s → 0 < d → 0 < d' → d + d' ≤ L →
      (∀ i, i + d < L → f (i + d) = f i) →
      (∀ i, i + d' < L → f (i + d') = f i) →
      ∀ i, i + Nat.gcd d d' < L → f (i + Nat.gcd d d') = f i := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro d d' hs hd hd' hle hper_d hper_d'
    by_cases heq : d = d'
    · subst heq
      simpa [Nat.gcd_self] using hper_d
    · rcases lt_or_gt_of_ne heq with hlt | hgt
      · -- d < d', let r = d' - d > 0
        set r := d' - d with hr_def
        have hr_pos : 0 < r := by omega
        have hper_r : ∀ i, i + r < L → f (i + r) = f i := by
          intro i hir
          by_cases hcase : i + d' < L
          · have h1 : f (i + r + d) = f (i + r) := hper_d (i + r) (by omega)
            have h2 : i + r + d = i + d' := by omega
            have h3 : f (i + d') = f i := hper_d' i hcase
            rw [h2] at h1
            exact h1.symm.trans h3
          · have hid : d ≤ i := by omega
            have h1 : f ((i - d) + d) = f (i - d) := hper_d (i - d) (by omega)
            have h2 : f ((i - d) + d') = f (i - d) := hper_d' (i - d) (by omega)
            have h3 : (i - d) + d = i := by omega
            have h4 : (i - d) + d' = i + r := by omega
            rw [h3] at h1
            rw [h4] at h2
            exact h2.trans h1.symm
        have hgcd : Nat.gcd d d' = Nat.gcd d r := by
          have : d' = r + d := by omega
          rw [this, Nat.gcd_add_self_right]
        rw [hgcd]
        exact ih (d + r) (by omega) d r rfl hd hr_pos (by omega) hper_d hper_r
      · -- d' < d, let r = d - d' > 0
        set r := d - d' with hr_def
        have hr_pos : 0 < r := by omega
        have hper_r : ∀ i, i + r < L → f (i + r) = f i := by
          intro i hir
          by_cases hcase : i + d < L
          · have h1 : f (i + r + d') = f (i + r) := hper_d' (i + r) (by omega)
            have h2 : i + r + d' = i + d := by omega
            have h3 : f (i + d) = f i := hper_d i hcase
            rw [h2] at h1
            exact h1.symm.trans h3
          · have hid' : d' ≤ i := by omega
            have h1 : f ((i - d') + d') = f (i - d') := hper_d' (i - d') (by omega)
            have h2 : f ((i - d') + d) = f (i - d') := hper_d (i - d') (by omega)
            have h3 : (i - d') + d' = i := by omega
            have h4 : (i - d') + d = i + r := by omega
            rw [h3] at h1
            rw [h4] at h2
            exact h2.trans h1.symm
        have hgcd : Nat.gcd d d' = Nat.gcd r d' := by
          have : d = r + d' := by omega
          rw [this, Nat.gcd_add_self_left]
        rw [hgcd]
        exact ih (r + d') (by omega) r d' rfl hr_pos hd' (by omega) hper_r hper_d'

/-- Stepping by multiples of a period `g` preserves `f` on `[0, L)`. -/
lemma periodic_mul {α : Type*} (f : ℕ → α) (L g : ℕ)
    (hper : ∀ i, i + g < L → f (i + g) = f i) :
    ∀ q i, i + q * g < L → f (i + q * g) = f i := by
  intro q
  induction q with
  | zero =>
    intro i _
    simp
  | succ q ih =>
    intro i hi
    have h1 : f (i + q * g + g) = f (i + q * g) := hper (i + q * g) (by
      have : i + (q + 1) * g = i + q * g + g := by ring
      omega)
    have h2 : f (i + q * g) = f i := ih i (by
      have : i + (q + 1) * g = i + q * g + g := by ring
      omega)
    have h3 : i + (q + 1) * g = i + q * g + g := by ring
    rw [h3]
    exact h1.trans h2

/-- A length-`4k` window of `w` shifted left from `t*` by `r`. -/
def winAt {α : Type*} (w : List α) (tStar k r : ℕ) : List α :=
  (w.drop (tStar - r)).take (4 * k)

lemma winAt_length {α : Type*} (w : List α) (tStar k r : ℕ)
    (_hr : r ≤ tStar) (hhi : tStar - r + 4 * k ≤ w.length) :
    (winAt w tStar k r).length = 4 * k := by
  simp [winAt, List.length_take, List.length_drop]
  omega

lemma winAt_getElem {α : Type*} (w : List α) (tStar k r j : ℕ)
    (hj : j < 4 * k) (hr : r ≤ tStar) (hhi : tStar - r + 4 * k ≤ w.length) :
    (winAt w tStar k r)[j]'(by rw [winAt_length w tStar k r hr hhi]; exact hj) =
      w[tStar - r + j]'(by omega) := by
  simp [winAt]

/-- Equal windows `winAt w t* k r₁ = winAt w t* k r₂` with `2k ≤ r₁ < r₂ ≤ 3k`
imply period `d = r₂ - r₁ ∈ [1, k]` on `[t* - 2k, t*]`. -/
lemma period_of_winAt_eq {α : Type*} (w : List α) (tStar k r₁ r₂ : ℕ)
    (hk : 1 ≤ k) (htlo : 4 * k ≤ tStar) (hthi : tStar + 4 * k ≤ w.length)
    (hr₁ : r₁ ∈ Finset.Icc (2 * k) (3 * k))
    (hr₂ : r₂ ∈ Finset.Icc (2 * k) (3 * k))
    (hlt : r₁ < r₂)
    (heq : winAt w tStar k r₁ = winAt w tStar k r₂) :
    let d := r₂ - r₁
    (∀ (i : ℕ) (hi : i + d < 2 * k),
      w[tStar - 2 * k + (i + d)]'(by omega) = w[tStar - 2 * k + i]'(by omega)) ∧
    w[tStar]'(by omega) = w[tStar - d]'(by omega) := by
  rw [Finset.mem_Icc] at hr₁ hr₂
  intro d
  have hpoint : ∀ (j : ℕ) (hj : j < 4 * k),
      w[tStar - r₁ + j]'(by omega) = w[tStar - r₂ + j]'(by omega) := by
    intro j hj
    have h1 := winAt_getElem w tStar k r₁ j hj (by omega) (by omega)
    have h2 := winAt_getElem w tStar k r₂ j hj (by omega) (by omega)
    have h3 : (winAt w tStar k r₁)[j]'(by rw [winAt_length w tStar k r₁ (by omega) (by omega)]; exact hj) =
              (winAt w tStar k r₂)[j]'(by rw [winAt_length w tStar k r₂ (by omega) (by omega)]; exact hj) := by
      simp only [heq]
    rw [← h1, ← h2]
    exact h3
  constructor
  · intro i hi
    set j := (r₂ - 2 * k) + i with hj_def
    have hj_lt : j < 4 * k := by omega
    have h := hpoint j hj_lt
    have he1 : tStar - r₁ + j = tStar - 2 * k + (i + d) := by omega
    have he2 : tStar - r₂ + j = tStar - 2 * k + i := by omega
    simpa [he1, he2] using h
  · set j := r₁ with hj_def
    have hj_lt : j < 4 * k := by omega
    have h := hpoint j hj_lt
    have he1 : tStar - r₁ + j = tStar := by omega
    have he2 : tStar - r₂ + j = tStar - d := by omega
    simpa [he1, he2] using h

/-- **Distinct Windows Theorem:**
At the first differing index `t*` between `w` and `x` (with `4k ≤ t*` and `t* + 4k ≤ n`),
either `r ↦ winAt w t* k r` is injective on `Icc (2k) (3k)` (giving `k + 1` distinct factors of `w`),
or `r ↦ winAt x t* k r` is injective on `Icc (2k) (3k)` (giving `k + 1` distinct factors of `x`). -/
theorem exists_injective_windows {α : Type*} (w x : List α) (n tStar k : ℕ)
    (hwlen : w.length = n) (hxlen : x.length = n)
    (hk : 1 ≤ k) (htlo : 4 * k ≤ tStar) (hthi : tStar + 4 * k ≤ n)
    (hagree : ∀ (i : ℕ) (hi : i < tStar), w[i]'(by omega) = x[i]'(by omega))
    (hdiff : w[tStar]'(by omega) ≠ x[tStar]'(by omega)) :
    Set.InjOn (winAt w tStar k) (Finset.Icc (2 * k) (3 * k) : Set ℕ) ∨
    Set.InjOn (winAt x tStar k) (Finset.Icc (2 * k) (3 * k) : Set ℕ) := by
  by_contra hboth
  push Not at hboth
  rcases hboth with ⟨hnotw, hnotx⟩
  rw [Set.InjOn] at hnotw hnotx
  push Not at hnotw hnotx
  rcases hnotw with ⟨a₁, ha₁, a₂, ha₂, hwa, hne_a⟩
  rcases hnotx with ⟨b₁, hb₁, b₂, hb₂, hxb, hne_b⟩
  have ⟨r₁, r₂, hr₁, hr₂, hrlt, hwr⟩ :
      ∃ r₁ r₂, r₁ ∈ Finset.Icc (2 * k) (3 * k) ∧ r₂ ∈ Finset.Icc (2 * k) (3 * k) ∧
        r₁ < r₂ ∧ winAt w tStar k r₁ = winAt w tStar k r₂ := by
    rcases lt_or_gt_of_ne hne_a with h | h
    · exact ⟨a₁, a₂, ha₁, ha₂, h, hwa⟩
    · exact ⟨a₂, a₁, ha₂, ha₁, h, hwa.symm⟩
  have ⟨s₁, s₂, hs₁, hs₂, hslt, hxs⟩ :
      ∃ s₁ s₂, s₁ ∈ Finset.Icc (2 * k) (3 * k) ∧ s₂ ∈ Finset.Icc (2 * k) (3 * k) ∧
        s₁ < s₂ ∧ winAt x tStar k s₁ = winAt x tStar k s₂ := by
    rcases lt_or_gt_of_ne hne_b with h | h
    · exact ⟨b₁, b₂, hb₁, hb₂, h, hxb⟩
    · exact ⟨b₂, b₁, hb₂, hb₁, h, hxb.symm⟩
  have hpw := period_of_winAt_eq w tStar k r₁ r₂ hk htlo (by omega) hr₁ hr₂ hrlt hwr
  have hpx := period_of_winAt_eq x tStar k s₁ s₂ hk htlo (by omega) hs₁ hs₂ hslt hxs
  set d := r₂ - r₁ with hd_def
  set d' := s₂ - s₁ with hd'_def
  rw [Finset.mem_Icc] at hr₁ hr₂ hs₁ hs₂
  have hd_pos : 0 < d := by omega
  have hd'_pos : 0 < d' := by omega
  have hd_le : d ≤ k := by omega
  have hd'_le : d' ≤ k := by omega
  -- Define total function f : ℕ → α agreeing with w (and x) on [tStar - 2*k, tStar)
  let fallback : α := w[0]'(by omega)
  let f : ℕ → α := fun i => w.getD (tStar - 2 * k + i) fallback
  have hf_w : ∀ (i : ℕ) (hi : i < 2 * k), f i = w[tStar - 2 * k + i]'(by omega) := by
    intro i hi
    simp [f, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : tStar - 2 * k + i < w.length)]
  have hf_x : ∀ (i : ℕ) (hi : i < 2 * k), f i = x[tStar - 2 * k + i]'(by omega) := by
    intro i hi
    rw [hf_w i hi]
    exact hagree (tStar - 2 * k + i) (by omega)
  have hper_d : ∀ i, i + d < 2 * k → f (i + d) = f i := by
    intro i hi
    rw [hf_w (i + d) hi, hf_w i (by omega)]
    exact hpw.1 i hi
  have hper_d' : ∀ i, i + d' < 2 * k → f (i + d') = f i := by
    intro i hi
    rw [hf_x (i + d') hi, hf_x i (by omega)]
    exact hpx.1 i hi
  set g := Nat.gcd d d' with hg_def
  have hper_g := fine_wilf_prefix f (2 * k) (d + d') d d' rfl hd_pos hd'_pos (by omega) hper_d hper_d'
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d' hd_pos
  have hg_dvd_d : g ∣ d := Nat.gcd_dvd_left d d'
  have hg_dvd_d' : g ∣ d' := Nat.gcd_dvd_right d d'
  rcases hg_dvd_d with ⟨q, hq⟩
  rcases hg_dvd_d' with ⟨q', hq'⟩
  have hq_pos : 1 ≤ q := by
    by_contra hq0
    have : q = 0 := by omega
    subst this
    simp at hq
    omega
  have hq'_pos : 1 ≤ q' := by
    by_contra hq0
    have : q' = 0 := by omega
    subst this
    simp at hq'
    omega
  -- Compare f (2*k - d) and f (2*k - g) using period g
  have hstep_w : f (2 * k - g) = f (2 * k - d) := by
    have hmul := periodic_mul f (2 * k) g hper_g (q - 1) (2 * k - d) (by
      have h1 : (q - 1) * g + g = q * g := by
        have := Nat.sub_add_cancel hq_pos
        calc (q - 1) * g + g = (q - 1 + 1) * g := by ring
        _ = q * g := by rw [this]
      have h2 : d = q * g := by rw [hq, mul_comm]
      omega)
    have heq_idx : 2 * k - d + (q - 1) * g = 2 * k - g := by
      have h1 : (q - 1) * g + g = q * g := by
        have := Nat.sub_add_cancel hq_pos
        calc (q - 1) * g + g = (q - 1 + 1) * g := by ring
        _ = q * g := by rw [this]
      have h2 : d = q * g := by rw [hq, mul_comm]
      omega
    simpa [heq_idx] using hmul
  have hstep_x : f (2 * k - g) = f (2 * k - d') := by
    have hmul := periodic_mul f (2 * k) g hper_g (q' - 1) (2 * k - d') (by
      have h1 : (q' - 1) * g + g = q' * g := by
        have := Nat.sub_add_cancel hq'_pos
        calc (q' - 1) * g + g = (q' - 1 + 1) * g := by ring
        _ = q' * g := by rw [this]
      have h2 : d' = q' * g := by rw [hq', mul_comm]
      omega)
    have heq_idx : 2 * k - d' + (q' - 1) * g = 2 * k - g := by
      have h1 : (q' - 1) * g + g = q' * g := by
        have := Nat.sub_add_cancel hq'_pos
        calc (q' - 1) * g + g = (q' - 1 + 1) * g := by ring
        _ = q' * g := by rw [this]
      have h2 : d' = q' * g := by rw [hq', mul_comm]
      omega
    simpa [heq_idx] using hmul
  have hw_eq : w[tStar]'(by omega) = f (2 * k - g) := by
    rw [hpw.2, hstep_w, hf_w (2 * k - d) (by omega)]
    have : tStar - 2 * k + (2 * k - d) = tStar - d := by omega
    simp [this, d]
  have hx_eq : x[tStar]'(by omega) = f (2 * k - g) := by
    rw [hpx.2, hstep_x, hf_x (2 * k - d') (by omega)]
    have : tStar - 2 * k + (2 * k - d') = tStar - d' := by omega
    simp [this, d']
  exact hdiff (hw_eq.trans hx_eq.symm)

/-- Averaging lemma: if `k + 1` distinct length-`4k` factors of `a` cover `t*` (where `a[t*] ≠ b[t*]`),
then at least one of them occurs at position `t` in `a` (`t + 4k ≤ n`), differs from `b` at `t`,
and has at most `n / (k + 1)` occurrences in `b`. -/
theorem exists_rare_differing_factor {α : Type*} [DecidableEq α]
    (a b : List α) (n tStar k : ℕ)
    (halen : a.length = n) (hblen : b.length = n)
    (hk : 1 ≤ k) (htlo : 4 * k ≤ tStar) (hthi : tStar + 4 * k ≤ n)
    (hdiff : a[tStar]'(by omega) ≠ b[tStar]'(by omega))
    (hinj : Set.InjOn (winAt a tStar k) (Finset.Icc (2 * k) (3 * k) : Set ℕ)) :
    ∃ t : ℕ, t + 4 * k ≤ n ∧
      (a.drop t).take (4 * k) ≠ (b.drop t).take (4 * k) ∧
      (k + 1) * ((Finset.range (n - 4 * k + 1)).filter
        (fun s => (b.drop s).take (4 * k) = (a.drop t).take (4 * k))).card ≤ n := by
  let I : Finset ℕ := Finset.Icc (2 * k) (3 * k)
  let occ : ℕ → Finset ℕ := fun r =>
    (Finset.range (n - 4 * k + 1)).filter (fun s => (b.drop s).take (4 * k) = winAt a tStar k r)
  have hI_card : I.card = k + 1 := by
    simp [I, Nat.card_Icc]
    omega
  have hdisj : Set.PairwiseDisjoint (I : Set ℕ) occ := by
    intro r₁ hr₁ r₂ hr₂ hne
    change Disjoint (occ r₁) (occ r₂)
    rw [Finset.disjoint_left]
    intro s hs₁ hs₂
    simp only [occ, Finset.mem_filter] at hs₁ hs₂
    have heq : winAt a tStar k r₁ = winAt a tStar k r₂ := hs₁.2.symm.trans hs₂.2
    exact hne (hinj hr₁ hr₂ heq)
  have hsum_le : ∑ r ∈ I, (occ r).card ≤ n := by
    rw [← Finset.card_biUnion hdisj]
    have hsub : I.biUnion occ ⊆ Finset.range (n - 4 * k + 1) := by
      intro s hs
      rw [Finset.mem_biUnion] at hs
      rcases hs with ⟨r, _, hsr⟩
      exact (Finset.mem_filter.mp hsr).1
    calc
      (I.biUnion occ).card ≤ (Finset.range (n - 4 * k + 1)).card := Finset.card_le_card hsub
      _ = n - 4 * k + 1 := Finset.card_range _
      _ ≤ n := by omega
  have hI_nonempty : I.Nonempty := ⟨2 * k, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  obtain ⟨r₀, hr₀, hr₀_min⟩ := Finset.exists_min_image I (fun r => (occ r).card) hI_nonempty
  have hmul_le : (k + 1) * (occ r₀).card ≤ n := by
    calc
      (k + 1) * (occ r₀).card = I.card * (occ r₀).card := by rw [hI_card]
      _ = ∑ _r ∈ I, (occ r₀).card := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ r ∈ I, (occ r).card := Finset.sum_le_sum (fun r hr => hr₀_min r hr)
      _ ≤ n := hsum_le
  rw [Finset.mem_Icc] at hr₀
  refine ⟨tStar - r₀, by omega, ?_, hmul_le⟩
  intro heq
  have h1 := winAt_getElem a tStar k r₀ r₀ (by omega) (by omega) (by omega)
  have h2 := winAt_getElem b tStar k r₀ r₀ (by omega) (by omega) (by omega)
  have h3 : (winAt a tStar k r₀)[r₀]'(by rw [winAt_length a tStar k r₀ (by omega) (by omega)]; omega) =
            (winAt b tStar k r₀)[r₀]'(by rw [winAt_length b tStar k r₀ (by omega) (by omega)]; omega) := by
    simp only [winAt, heq]
  rw [h1, h2] at h3
  have he4 : tStar - r₀ + r₀ = tStar := by omega
  simp only [he4] at h3
  exact hdiff h3

/-! ## Section 3: Prime-Pair Avoidance via `Finset.offDiag` -/

/-- A product of distinct primes dividing `D` divides `D`. -/
lemma prod_primes_dvd {D : ℕ} (T : Finset ℕ)
    (hp : ∀ p ∈ T, Nat.Prime p) (hdvd : ∀ p ∈ T, p ∣ D) :
    ∏ p ∈ T, p ∣ D := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha_prime : Nat.Prime a := hp a (Finset.mem_insert_self a s)
    have ha_dvd : a ∣ D := hdvd a (Finset.mem_insert_self a s)
    have hs_dvd : ∏ p ∈ s, p ∣ D := ih
      (fun p h => hp p (Finset.mem_insert_of_mem h))
      (fun p h => hdvd p (Finset.mem_insert_of_mem h))
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
      apply Nat.Coprime.prod_right
      intro p hp_s
      have hp_prime : Nat.Prime p := hp p (Finset.mem_insert_of_mem hp_s)
      have hne : a ≠ p := fun h => ha (h ▸ hp_s)
      exact (Nat.coprime_primes ha_prime hp_prime).mpr hne
    exact hcop.mul_dvd_of_dvd_of_dvd ha_dvd hs_dvd

/-- **Prime-Pair Avoidance Lemma:**
Given `S ⊆ range n`, `t < n` with `t ∉ S`, `lo ^ 4 ≥ n`, and `P = (Ioc lo M).filter Nat.Prime`,
if `6 * S.card < P.card * (P.card - 1)`, then there exist distinct primes `p, q ∈ P`
such that no `s ∈ S` has both `p ∣ |s - t|` and `q ∣ |s - t|`. -/
theorem exists_avoiding_prime_pair (n lo M t : ℕ) (S : Finset ℕ)
    (hS : ∀ s ∈ S, s < n) (ht : t < n) (ht_not : t ∉ S)
    (hlo : n ≤ lo ^ 4)
    (hcard : 6 * S.card < ((Finset.Ioc lo M).filter Nat.Prime).card *
      (((Finset.Ioc lo M).filter Nat.Prime).card - 1)) :
    let P := (Finset.Ioc lo M).filter Nat.Prime
    ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧
      ∀ s ∈ S, ¬(s % p = t % p ∧ s % q = t % q) := by
  intro P
  let divs : ℕ → Finset ℕ := fun s => P.filter (fun p => p ∣ Int.natAbs ((s : ℤ) - t))
  have hdivs_le : ∀ s ∈ S, (divs s).card ≤ 3 := by
    intro s hs
    have hne : s ≠ t := fun h => ht_not (h ▸ hs)
    have hs_lt : s < n := hS s hs
    set D := Int.natAbs ((s : ℤ) - t) with hD_def
    have hD_pos : 0 < D := by
      rw [hD_def, Int.natAbs_pos]
      omega
    have hD_lt : D < n := by
      rw [hD_def]
      omega
    have hprod_dvd : ∏ p ∈ divs s, p ∣ D := prod_primes_dvd (divs s)
      (fun p hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2)
      (fun p hp => (Finset.mem_filter.mp hp).2)
    have hprod_le : ∏ p ∈ divs s, p ≤ D := Nat.le_of_dvd hD_pos hprod_dvd
    have hlo_pow : lo ^ (divs s).card ≤ ∏ p ∈ divs s, p := by
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod'
      intro p hp
      have hp_lo : lo < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
      omega
    by_contra hgt
    have h4 : 4 ≤ (divs s).card := by omega
    have hlo_pos : 1 ≤ lo := by
      by_contra h0
      have : lo = 0 := by omega
      subst this
      simp at hlo
      omega
    have hpow4 : lo ^ 4 ≤ lo ^ (divs s).card := Nat.pow_le_pow_right hlo_pos h4
    omega
  let bad : Finset (ℕ × ℕ) := S.biUnion (fun s => (divs s).offDiag)
  have hbad_sub : bad ⊆ P.offDiag := by
    intro pq hpq
    rw [Finset.mem_biUnion] at hpq
    rcases hpq with ⟨s, _, hpq_s⟩
    rw [Finset.mem_offDiag] at hpq_s ⊢
    exact ⟨(Finset.mem_filter.mp hpq_s.1).1, (Finset.mem_filter.mp hpq_s.2.1).1, hpq_s.2.2⟩
  have hbad_card : bad.card ≤ 6 * S.card := by
    calc
      bad.card ≤ ∑ s ∈ S, ((divs s).offDiag).card := Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ S, 6 := by
        apply Finset.sum_le_sum
        intro s hs
        rw [Finset.offDiag_card]
        have h3 := hdivs_le s hs
        set c := (divs s).card
        interval_cases c <;> norm_num
      _ = 6 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hoff_card : P.offDiag.card = P.card * (P.card - 1) := by
    rw [Finset.offDiag_card]
    have : P.card * P.card - P.card = P.card * (P.card - 1) := by
      cases P.card with
      | zero => simp
      | succ c => simp [Nat.mul_succ]
    exact this
  have hlt : bad.card < P.offDiag.card := by
    rw [hoff_card]
    exact lt_of_le_of_lt hbad_card hcard
  have hdiff_ne : (P.offDiag \ bad).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : P.offDiag ⊆ bad := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  obtain ⟨⟨p, q⟩, hpq⟩ := hdiff_ne
  rw [Finset.mem_sdiff, Finset.mem_offDiag] at hpq
  rcases hpq with ⟨⟨hpP, hqP, hne⟩, hnotbad⟩
  refine ⟨p, hpP, q, hqP, hne, ?_⟩
  intro s hs ⟨hmp, hmq⟩
  apply hnotbad
  rw [Finset.mem_biUnion]
  refine ⟨s, hs, ?_⟩
  rw [Finset.mem_offDiag]
  have hdvd_of_mod : ∀ m : ℕ, s % m = t % m → m ∣ Int.natAbs ((s : ℤ) - t) := by
    intro m hm
    have h1 : ((s : ℤ) - t) % (m : ℤ) = 0 := by
      have hs' : (s : ℤ) % (m : ℤ) = (t : ℤ) % (m : ℤ) := by exact_mod_cast hm
      rw [Int.sub_emod, hs', sub_self, Int.zero_emod]
    have h2 : (m : ℤ) ∣ ((s : ℤ) - t) := Int.dvd_of_emod_eq_zero h1
    exact Int.natCast_dvd.mp h2
  exact ⟨Finset.mem_filter.mpr ⟨hpP, hdvd_of_mod p hmp⟩,
         Finset.mem_filter.mpr ⟨hqP, hdvd_of_mod q hmq⟩, hne⟩

/-! ## Section 4: Pure-Mathlib Separating NFA Constructions -/

/-- Reindex an `NFA α σ` along an equivalence `e : σ ≃ τ` preserving its accepted language. -/
def reindexNFA {α σ τ : Type*} (M : NFA α σ) (e : σ ≃ τ) : NFA α τ where
  step t a := e '' M.step (e.symm t) a
  start := e '' M.start
  accept := e '' M.accept

lemma stepSet_reindexNFA {α σ τ : Type*} (M : NFA α σ) (e : σ ≃ τ) (S : Set σ) (a : α) :
    (reindexNFA M e).stepSet (e '' S) a = e '' (M.stepSet S a) := by
  ext y
  simp only [NFA.mem_stepSet, reindexNFA, Set.mem_image]
  constructor
  · rintro ⟨t, ⟨s, hs, rfl⟩, ⟨s', hs', rfl⟩⟩
    rw [Equiv.symm_apply_apply] at hs'
    exact ⟨s', ⟨s, hs, hs'⟩, rfl⟩
  · rintro ⟨s', ⟨s, hs, hs'⟩, rfl⟩
    refine ⟨e s, ⟨s, hs, rfl⟩, ⟨s', ?_, rfl⟩⟩
    simpa [Equiv.symm_apply_apply] using hs'

lemma evalFrom_reindexNFA {α σ τ : Type*} (M : NFA α σ) (e : σ ≃ τ) (S : Set σ) (y : List α) :
    (reindexNFA M e).evalFrom (e '' S) y = e '' (M.evalFrom S y) := by
  induction y using List.reverseRecOn with
  | nil => simp [NFA.evalFrom_nil]
  | append_singleton ys a ih =>
    rw [NFA.evalFrom_append, NFA.evalFrom_singleton, ih, stepSet_reindexNFA,
        ← NFA.evalFrom_singleton, ← NFA.evalFrom_append]

lemma mem_accepts_reindexNFA {α σ τ : Type*} (M : NFA α σ) (e : σ ≃ τ) (y : List α) :
    y ∈ (reindexNFA M e).accepts ↔ y ∈ M.accepts := by
  rw [NFA.mem_accepts, NFA.mem_accepts]
  have hst : (reindexNFA M e).start = e '' M.start := rfl
  have hacc : (reindexNFA M e).accept = e '' M.accept := rfl
  rw [hst, hacc, evalFrom_reindexNFA]
  constructor
  · rintro ⟨t, ⟨s, hs, rfl⟩, ⟨s', hs', heq⟩⟩
    have := e.injective heq
    subst this
    exact ⟨s', hs, hs'⟩
  · rintro ⟨s, hs, hs'⟩
    exact ⟨e s, ⟨s, hs, rfl⟩, ⟨s, hs', rfl⟩⟩

/-! ### Construction A: `(t + 2)`-state Prefix NFA checking `y[t] = c` -/

/-- A `(t + 2)`-state NFA accepting `y` iff `t < y.length ∧ y[t] = c`. -/
def prefixNFA {α : Type*} [DecidableEq α] (t : ℕ) (c : α) : NFA α (Fin (t + 2)) where
  step s a :=
    if h : s.val < t then {⟨s.val + 1, by omega⟩}
    else if s.val = t then if a = c then {⟨t + 1, by omega⟩} else ∅
    else {⟨t + 1, by omega⟩}
  start := {⟨0, by omega⟩}
  accept := {⟨t + 1, by omega⟩}

lemma prefixNFA_evalFrom_short {α : Type*} [DecidableEq α] (t : ℕ) (c : α) (y : List α) (hy : y.length ≤ t) :
    (prefixNFA t c).evalFrom {⟨0, by omega⟩} y = {⟨y.length, by omega⟩} := by
  induction y using List.reverseRecOn with
  | nil => simp [NFA.evalFrom_nil]
  | append_singleton ys a ih =>
    have hys : ys.length < t := by simp at hy; omega
    rw [NFA.evalFrom_append, NFA.evalFrom_singleton, ih (by omega)]
    ext s
    simp [prefixNFA, hys]

lemma prefixNFA_evalFrom_sink {α : Type*} [DecidableEq α] (t : ℕ) (c : α) (y : List α) :
    (prefixNFA t c).evalFrom {⟨t + 1, by omega⟩} y = {⟨t + 1, by omega⟩} := by
  induction y using List.reverseRecOn with
  | nil => simp [NFA.evalFrom_nil]
  | append_singleton ys a ih =>
    rw [NFA.evalFrom_append, NFA.evalFrom_singleton, ih]
    ext s
    simp [prefixNFA]

lemma prefixNFA_evalFrom_empty {α : Type*} [DecidableEq α] (t : ℕ) (c : α) (y : List α) :
    (prefixNFA t c).evalFrom ∅ y = ∅ := by
  induction y using List.reverseRecOn with
  | nil => simp [NFA.evalFrom_nil]
  | append_singleton ys a ih =>
    rw [NFA.evalFrom_append, NFA.evalFrom_singleton, ih]
    ext s
    simp

lemma mem_accepts_prefixNFA {α : Type*} [DecidableEq α] (t : ℕ) (c : α) (y : List α) (hy : t < y.length) :
    y ∈ (prefixNFA t c).accepts ↔ y[t]'hy = c := by
  have hsplit : y = y.take t ++ [y[t]'hy] ++ y.drop (t + 1) := by
    have h2 : y.drop t = y[t]'hy :: y.drop (t + 1) := List.drop_eq_getElem_cons hy
    calc y = y.take t ++ y.drop t := (List.take_append_drop t y).symm
    _ = y.take t ++ (y[t]'hy :: y.drop (t + 1)) := by rw [h2]
    _ = y.take t ++ [y[t]'hy] ++ y.drop (t + 1) := by simp
  have htakelen : (y.take t).length = t := by simp [List.length_take]; omega
  rw [NFA.mem_accepts]
  conv_lhs => rw [hsplit]
  rw [NFA.evalFrom_append, NFA.evalFrom_append]
  have hstart : (prefixNFA t c).start = {⟨0, by omega⟩} := rfl
  rw [hstart, prefixNFA_evalFrom_short t c (y.take t) (by omega)]
  have hmid_fin : (⟨(y.take t).length, by omega⟩ : Fin (t + 2)) = ⟨t, by omega⟩ := by
    ext; exact htakelen
  rw [hmid_fin, NFA.evalFrom_singleton]
  have hstep : (prefixNFA t c).stepSet {⟨t, by omega⟩} (y[t]'hy) =
      if y[t]'hy = c then {⟨t + 1, by omega⟩} else ∅ := by
    ext s
    simp [prefixNFA]
  rw [hstep]
  by_cases hEq : y[t]'hy = c
  · rw [if_pos hEq, prefixNFA_evalFrom_sink]
    simp [hEq, prefixNFA]
  · rw [if_neg hEq, prefixNFA_evalFrom_empty]
    simp [hEq, prefixNFA]

/-! ### Construction B: `(d + 1)`-state Suffix NFA checking `y[y.length - d] = c` -/

/-- A `(d + 1)`-state NFA (`d ≥ 1`) accepting `y` iff `d ≤ y.length ∧ y[y.length - d] = c`. -/
def suffixNFA {α : Type*} [DecidableEq α] (d : ℕ) (hd : 1 ≤ d) (c : α) : NFA α (Fin (d + 1)) where
  step s a :=
    if s.val = 0 then
      {⟨0, by omega⟩} ∪ (if a = c then {⟨1, by omega⟩} else ∅)
    else if h : s.val < d then
      {⟨s.val + 1, by omega⟩}
    else
      ∅
  start := {⟨0, by omega⟩}
  accept := {⟨d, by omega⟩}

lemma suffixNFA_evalFrom_iff {α : Type*} [DecidableEq α] (d : ℕ) (hd : 1 ≤ d) (c : α) (y : List α) :
    (⟨0, by omega⟩ ∈ (suffixNFA d hd c).evalFrom (suffixNFA d hd c).start y) ∧
    (∀ (j : ℕ) (hj1 : 1 ≤ j) (hjd : j ≤ d),
      ⟨j, by omega⟩ ∈ (suffixNFA d hd c).evalFrom (suffixNFA d hd c).start y ↔
        ∃ hlen : j ≤ y.length, y[y.length - j]'(by omega) = c) := by
  induction y using List.reverseRecOn with
  | nil =>
    constructor
    · simp [NFA.evalFrom_nil, suffixNFA]
    · intro j hj1 hjd
      constructor
      · intro h
        rw [NFA.evalFrom_nil] at h
        have hv : j = 0 := congrArg Fin.val (Set.mem_singleton_iff.mp h)
        omega
      · rintro ⟨hlen, _⟩
        simp at hlen; omega
  | append_singleton ys a ih =>
    rcases ih with ⟨ih0, ihj⟩
    have hstep_eq : ∀ s : Fin (d + 1),
        s ∈ (suffixNFA d hd c).evalFrom (suffixNFA d hd c).start (ys ++ [a]) ↔
          ∃ t ∈ (suffixNFA d hd c).evalFrom (suffixNFA d hd c).start ys,
            s ∈ (suffixNFA d hd c).step t a := by
      intro s
      rw [NFA.evalFrom_append, NFA.evalFrom_singleton, NFA.mem_stepSet]
    constructor
    · rw [hstep_eq]
      refine ⟨⟨0, by omega⟩, ih0, ?_⟩
      simp [suffixNFA]
    · intro j hj1 hjd
      rw [hstep_eq]
      by_cases hj_one : j = 1
      · subst hj_one
        constructor
        · rintro ⟨t, _, hstep⟩
          change (⟨1, by omega⟩ : Fin (d + 1)) ∈ (if t.val = 0 then _ else if h : t.val < d then _ else ∅) at hstep
          by_cases ht0 : t.val = 0
          · rw [if_pos ht0] at hstep
            rcases hstep with h0 | h1
            · have : (1 : ℕ) = 0 := congrArg Fin.val (Set.mem_singleton_iff.mp h0)
              omega
            · split_ifs at h1 with hac
              · refine ⟨by simp, ?_⟩
                simp [hac]
              · simp at h1
          · rw [if_neg ht0] at hstep
            by_cases htd : t.val < d
            · rw [dif_pos htd] at hstep
              have : 1 = t.val + 1 := congrArg Fin.val (Set.mem_singleton_iff.mp hstep)
              omega
            · rw [dif_neg htd] at hstep
              exact False.elim hstep
        · rintro ⟨_, hchar⟩
          have hac : a = c := by simpa using hchar
          refine ⟨⟨0, by omega⟩, ih0, ?_⟩
          simp [suffixNFA, hac]
      · have hj2 : 2 ≤ j := by omega
        constructor
        · rintro ⟨t, ht_in, hstep⟩
          change (⟨j, by omega⟩ : Fin (d + 1)) ∈ (if t.val = 0 then _ else if h : t.val < d then _ else ∅) at hstep
          by_cases ht0 : t.val = 0
          · rw [if_pos ht0] at hstep
            rcases hstep with h0 | h1
            · have : j = 0 := congrArg Fin.val (Set.mem_singleton_iff.mp h0); omega
            · split_ifs at h1 with hac
              · have : j = 1 := congrArg Fin.val (Set.mem_singleton_iff.mp h1); omega
              · simp at h1
          · rw [if_neg ht0] at hstep
            by_cases htd : t.val < d
            · rw [dif_pos htd] at hstep
              have htv : t.val = j - 1 := by
                have hval := congrArg Fin.val (Set.mem_singleton_iff.mp hstep)
                dsimp only at hval
                omega
              have ht_eq : t = ⟨j - 1, by omega⟩ := by ext; exact htv
              rw [ht_eq] at ht_in
              obtain ⟨hlen, hch⟩ := (ihj (j - 1) (by omega) (by omega)).mp ht_in
              refine ⟨by simp; omega, ?_⟩
              have hidx_lt : (ys ++ [a]).length - j < ys.length := by simp; omega
              rw [List.getElem_append_left hidx_lt]
              have hidx_eq : (ys ++ [a]).length - j = ys.length - (j - 1) := by simp; omega
              simp only [hidx_eq]
              exact hch
            · rw [dif_neg htd] at hstep
              exact False.elim hstep
        · rintro ⟨hlen, hch⟩
          have hlen' : j - 1 ≤ ys.length := by simp at hlen; omega
          have hidx_lt : (ys ++ [a]).length - j < ys.length := by simp at hlen ⊢; omega
          rw [List.getElem_append_left hidx_lt] at hch
          have hidx_eq : (ys ++ [a]).length - j = ys.length - (j - 1) := by simp; omega
          have hch' : ys[ys.length - (j - 1)]'(by omega) = c := by
            simp only [hidx_eq] at hch
            exact hch
          have hprev := (ihj (j - 1) (by omega) (by omega)).mpr ⟨hlen', hch'⟩
          refine ⟨⟨j - 1, by omega⟩, hprev, ?_⟩
          change (⟨j, by omega⟩ : Fin (d + 1)) ∈ (if (j - 1) = 0 then _ else if h : j - 1 < d then _ else ∅)
          rw [if_neg (by omega), dif_pos (by omega)]
          rw [Set.mem_singleton_iff]
          ext; simp; omega

lemma mem_accepts_suffixNFA {α : Type*} [DecidableEq α] (d : ℕ) (hd : 1 ≤ d) (c : α) (y : List α)
    (hlen : d ≤ y.length) :
    y ∈ (suffixNFA d hd c).accepts ↔ y[y.length - d]'(by omega) = c := by
  rw [NFA.mem_accepts]
  have hacc : (suffixNFA d hd c).accept = {⟨d, by omega⟩} := rfl
  simp only [hacc, Set.mem_singleton_iff, exists_eq_left]
  rw [(suffixNFA_evalFrom_iff d hd c y).2 d hd le_rfl]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hlen, h⟩⟩

/-! ### Construction C: `(p + (ℓ - 1) + q)`-state 2-Prime CRT Bridge NFA -/

/-- State type for the 2-Prime CRT Bridge NFA: left `p`-cycle, middle `(ℓ - 1)`-chain, right `q`-cycle. -/
inductive BridgeState (p ell q : ℕ) where
  | left (i : Fin p)
  | mid (j : Fin (ell - 1))
  | right (k : Fin q)
  deriving DecidableEq

/-- Explicit equivalence `BridgeState p ell q ≃ Fin (p + (ell - 1) + q)`. -/
def bridgeStateEquiv (p ell q : ℕ) : BridgeState p ell q ≃ Fin (p + (ell - 1) + q) :=
  let e1 : BridgeState p ell q ≃ (Fin p ⊕ Fin (ell - 1)) ⊕ Fin q :=
    { toFun := fun s => match s with
        | .left i => Sum.inl (Sum.inl i)
        | .mid j => Sum.inl (Sum.inr j)
        | .right k => Sum.inr k
      invFun := fun s => match s with
        | Sum.inl (Sum.inl i) => .left i
        | Sum.inl (Sum.inr j) => .mid j
        | Sum.inr k => .right k
      left_inv := fun s => by cases s <;> rfl
      right_inv := fun s => by rcases s with (i | j) | k <;> rfl }
  e1.trans ((finSumFinEquiv.sumCongr (Equiv.refl (Fin q))).trans finSumFinEquiv)

/-- The 2-Prime CRT Bridge NFA with `p + (u.length - 1) + q` states.
Counts prefix length `s` mod `p` on the left cycle, matches `u` across the middle chain,
and counts remaining suffix length `y.length - (s + u.length)` mod `q` on the right cycle. -/
def bridgeNFA {α : Type*} [DecidableEq α] (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (u : List α) (hu : 1 ≤ u.length) (r₁ : ℕ) (r₂ : ℕ) (hr₂ : r₂ < q) :
    NFA α (BridgeState p u.length q) where
  step s a := match s with
    | .left i =>
      {BridgeState.left ⟨(i.val + 1) % p, Nat.mod_lt _ (by omega)⟩} ∪
      (if i.val = r₁ ∧ a = u[0]'(by omega) then
        if h : 1 < u.length then {BridgeState.mid ⟨0, by omega⟩}
        else {BridgeState.right ⟨0, by omega⟩}
      else ∅)
    | .mid j =>
      if a = u[j.val + 1]'(by omega) then
        if h : j.val + 1 < u.length - 1 then {BridgeState.mid ⟨j.val + 1, h⟩}
        else {BridgeState.right ⟨0, by omega⟩}
      else ∅
    | .right k =>
      {BridgeState.right ⟨(k.val + 1) % q, Nat.mod_lt _ (by omega)⟩}
  start := {BridgeState.left ⟨0, by omega⟩}
  accept := {BridgeState.right ⟨r₂, hr₂⟩}

/-- Helper: extending a matching suffix by one character. -/
lemma drop_append_singleton_eq_take {α : Type*} (ys u : List α) (a : α) (s m : ℕ)
    (hsm : s + m = ys.length) (hmu : m < u.length)
    (hdrop : ys.drop s = u.take m) (ha : a = u[m]'hmu) :
    (ys ++ [a]).drop s = u.take (m + 1) := by
  rw [List.drop_append_of_le_length (by omega), hdrop, ha]
  rw [List.take_add_one, List.getElem?_eq_getElem hmu]
  simp

lemma drop_append_singleton_iff {α : Type*} (ys u : List α) (a : α) (s m : ℕ)
    (hsm : s + m = ys.length) (hmu : m < u.length) :
    (ys ++ [a]).drop s = u.take (m + 1) ↔
      ys.drop s = u.take m ∧ a = u[m]'hmu := by
  constructor
  · intro h
    rw [List.drop_append_of_le_length (by omega)] at h
    rw [List.take_add_one, List.getElem?_eq_getElem hmu, Option.toList_some] at h
    have hlen1 : (ys.drop s).length = m := by simp; omega
    have hlen2 : (u.take m).length = m := by simp; omega
    have hpair := List.append_inj h (by rw [hlen1, hlen2])
    exact ⟨hpair.1, List.singleton_injective hpair.2⟩
  · rintro ⟨h1, h2⟩
    exact drop_append_singleton_eq_take ys u a s m hsm hmu h1 h2

/-- Exact reachability characterization of `bridgeNFA` on any input word `y`. -/
theorem bridgeNFA_evalFrom_iff {α : Type*} [DecidableEq α] (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (u : List α) (hu : 1 ≤ u.length) (r₁ r₂ : ℕ) (hr₂ : r₂ < q) (y : List α) :
    let M := bridgeNFA p q hp hq u hu r₁ r₂ hr₂
    (∀ i : Fin p, BridgeState.left i ∈ M.evalFrom M.start y ↔ i.val = y.length % p) ∧
    (∀ j : Fin (u.length - 1), BridgeState.mid j ∈ M.evalFrom M.start y ↔
      ∃ s, s + (j.val + 1) = y.length ∧ s % p = r₁ ∧ y.drop s = u.take (j.val + 1)) ∧
    (∀ k : Fin q, BridgeState.right k ∈ M.evalFrom M.start y ↔
      ∃ s, s + u.length ≤ y.length ∧ s % p = r₁ ∧
        (y.drop s).take u.length = u ∧ (y.length - (s + u.length)) % q = k.val) := by
  intro M
  induction y using List.reverseRecOn with
  | nil =>
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simp [M, bridgeNFA, NFA.evalFrom_nil]
      constructor
      · intro h; rw [h]
      · intro h; ext; exact h
    · intro j
      simp [M, bridgeNFA, NFA.evalFrom_nil]
    · intro k
      constructor
      · intro h; simp [M, bridgeNFA, NFA.evalFrom_nil] at h
      · rintro ⟨s, hs, _⟩; simp only [List.length_nil] at hs; omega
  | append_singleton ys a ih =>
    rcases ih with ⟨ihL, ihM, ihR⟩
    have hstep_iff : ∀ st : BridgeState p u.length q,
        st ∈ M.evalFrom M.start (ys ++ [a]) ↔
          ∃ t ∈ M.evalFrom M.start ys, st ∈ M.step t a := by
      intro st
      rw [NFA.evalFrom_append, NFA.evalFrom_singleton, NFA.mem_stepSet]
    refine ⟨?_, ?_, ?_⟩
    · -- Case 1: left i
      intro i
      rw [hstep_iff]
      constructor
      · rintro ⟨t, ht, hst⟩
        cases t with
        | left i' =>
          have hi' := (ihL i').mp ht
          simp only [M, bridgeNFA, Set.mem_union, Set.mem_singleton_iff] at hst
          rcases hst with h1 | h2
          · have hv : i.val = (i'.val + 1) % p := by
              have := BridgeState.left.inj h1
              exact congrArg Fin.val this
            rw [hv, hi', List.length_append, List.length_singleton, Nat.mod_add_mod]
          · split_ifs at h2 <;> simp at h2
        | mid j' =>
          simp only [M, bridgeNFA] at hst
          split_ifs at hst <;> simp at hst
        | right k' =>
          simp only [M, bridgeNFA, Set.mem_singleton_iff] at hst
          cases hst
      · intro hi
        refine ⟨BridgeState.left ⟨ys.length % p, Nat.mod_lt _ (by omega)⟩,
          (ihL _).mpr rfl, ?_⟩
        simp only [M, bridgeNFA, Set.mem_union, Set.mem_singleton_iff]
        left
        congr 1
        ext
        rw [hi, List.length_append, List.length_singleton]
        change (ys.length + 1) % p = (ys.length % p + 1) % p
        rw [Nat.mod_add_mod]
    · -- Case 2: mid j
      intro j
      rw [hstep_iff]
      by_cases hj0 : j.val = 0
      · constructor
        · rintro ⟨t, ht, hst⟩
          cases t with
          | left i' =>
            have hi' := (ihL i').mp ht
            simp only [M, bridgeNFA, Set.mem_union, Set.mem_singleton_iff] at hst
            rcases hst with h1 | h2
            · cases h1
            · split_ifs at h2 with hc1 hc2
              · refine ⟨ys.length, by simp [hj0], ?_, ?_⟩
                · rw [← hi']; exact hc1.1
                · rw [hj0]
                  have h1 := drop_append_singleton_eq_take ys u a ys.length 0 (by omega) (by omega)
                    (by simp) hc1.2
                  simpa using h1
              · simp at h2
              · simp at h2
          | mid j' =>
            simp only [M, bridgeNFA] at hst
            split_ifs at hst with hc1 hc2
            · simp only [Set.mem_singleton_iff] at hst
              have hv : j.val = j'.val + 1 := congrArg Fin.val (BridgeState.mid.inj hst)
              omega
            · simp at hst
            · simp at hst
          | right k' =>
            simp only [M, bridgeNFA, Set.mem_singleton_iff] at hst
            cases hst
        · rintro ⟨s, hslen, hsmod, hdrop⟩
          have hs_eq : s = ys.length := by simp [hj0] at hslen; omega
          subst hs_eq
          have ha_eq : a = u[0]'(by omega) := by
            rw [hj0] at hdrop
            have h1 := (drop_append_singleton_iff ys u a ys.length 0 (by omega) (by omega)).mp hdrop
            exact h1.2
          have h1lt : 1 < u.length := by have := j.isLt; omega
          refine ⟨BridgeState.left ⟨ys.length % p, Nat.mod_lt _ (by omega)⟩,
            (ihL _).mpr rfl, ?_⟩
          simp only [M, bridgeNFA, Set.mem_union, Set.mem_singleton_iff]
          right
          rw [if_pos ⟨hsmod, ha_eq⟩, dif_pos h1lt]
          simp only [Set.mem_singleton_iff]
          congr 1
          ext; exact hj0
      · -- j.val ≥ 1
        have hjpos : 1 ≤ j.val := by omega
        constructor
        · rintro ⟨t, ht, hst⟩
          cases t with
          | left i' =>
            simp only [M, bridgeNFA, Set.mem_union, Set.mem_singleton_iff] at hst
            rcases hst with h1 | h2
            · cases h1
            · split_ifs at h2 with hc1 hc2
              · simp only [Set.mem_singleton_iff] at h2
                have hv : j.val = 0 := congrArg Fin.val (BridgeState.mid.inj h2)
                omega
              · simp at h2
              · simp at h2
          | mid j' =>
            simp only [M, bridgeNFA] at hst
            split_ifs at hst with hc1 hc2
            · simp only [Set.mem_singleton_iff] at hst
              have hj'v : j'.val + 1 = j.val := (congrArg Fin.val (BridgeState.mid.inj hst)).symm
              obtain ⟨s, hslen, hsmod, hdrop⟩ := (ihM j').mp ht
              refine ⟨s, by simp; omega, hsmod, ?_⟩
              have hdrop' : ys.drop s = u.take j.val := by rwa [← hj'v]
              have ha' : a = u[j.val]'(by have := j.isLt; omega) := by
                simpa [hj'v] using hc1
              exact drop_append_singleton_eq_take ys u a s j.val (by omega) (by have := j.isLt; omega)
                hdrop' ha'
            · simp at hst
            · simp at hst
          | right k' =>
            simp only [M, bridgeNFA, Set.mem_singleton_iff] at hst
            cases hst
        · rintro ⟨s, hslen, hsmod, hdrop⟩
          have hslen' : s + j.val = ys.length := by simp at hslen; omega
          have hpair := (drop_append_singleton_iff ys u a s j.val hslen' (by have := j.isLt; omega)).mp hdrop
          let j' : Fin (u.length - 1) := ⟨j.val - 1, by have := j.isLt; omega⟩
          have hj'_succ : j'.val + 1 = j.val := by simp [j']; omega
          have hprev : BridgeState.mid j' ∈ M.evalFrom M.start ys :=
            (ihM j').mpr ⟨s, by omega, hsmod, by simpa [hj'_succ] using hpair.1⟩
          refine ⟨BridgeState.mid j', hprev, ?_⟩
          simp only [M, bridgeNFA]
          have hc1 : a = u[j'.val + 1]'(by omega) := by simpa [hj'_succ] using hpair.2
          have hc2 : j'.val + 1 < u.length - 1 := by have := j.isLt; omega
          rw [if_pos hc1, dif_pos hc2]
          simp only [Set.mem_singleton_iff]
          congr 1
          ext; exact hj'_succ.symm
    · -- Case 3: right k
      intro k
      rw [hstep_iff]
      constructor
      · rintro ⟨t, ht, hst⟩
        cases t with
        | left i' =>
          have hi' := (ihL i').mp ht
          simp only [M, bridgeNFA, Set.mem_union, Set.mem_singleton_iff] at hst
          rcases hst with h1 | h2
          · cases h1
          · split_ifs at h2 with hc1 hc2
            · simp at h2
            · simp only [Set.mem_singleton_iff] at h2
              have hk0 : k.val = 0 := congrArg Fin.val (BridgeState.right.inj h2)
              have hu1 : u.length = 1 := by omega
              refine ⟨ys.length, by simp; omega, by rw [← hi']; exact hc1.1, ?_, ?_⟩
              · have hdrop := drop_append_singleton_eq_take ys u a ys.length 0 (by omega) (by omega)
                  (by simp) hc1.2
                have htake : u.take 1 = u := by
                  rw [List.take_of_length_le (by omega)]
                rw [hu1, List.take_of_length_le (by simp), hdrop, htake]
              · simp [hu1, hk0]
            · simp at h2
        | mid j' =>
          simp only [M, bridgeNFA] at hst
          split_ifs at hst with hc1 hc2
          · simp at hst
          · simp only [Set.mem_singleton_iff] at hst
            have hk0 : k.val = 0 := congrArg Fin.val (BridgeState.right.inj hst)
            have hj'last : j'.val + 1 = u.length - 1 := by have := j'.isLt; omega
            obtain ⟨s, hslen, hsmod, hdrop⟩ := (ihM j').mp ht
            refine ⟨s, by simp; omega, hsmod, ?_, ?_⟩
            · have hdrop' := drop_append_singleton_eq_take ys u a s (j'.val + 1) hslen
                (by omega) hdrop hc1
              have hlen_eq : j'.val + 1 + 1 = u.length := by omega
              rw [hlen_eq, List.take_of_length_le le_rfl] at hdrop'
              rw [hdrop', List.take_of_length_le le_rfl]
            · have hzero : (ys ++ [a]).length - (s + u.length) = 0 := by simp; omega
              rw [hzero, Nat.zero_mod, hk0]
          · simp at hst
        | right k' =>
          simp only [M, bridgeNFA, Set.mem_singleton_iff] at hst
          have hk_eq : k.val = (k'.val + 1) % q := congrArg Fin.val (BridgeState.right.inj hst)
          obtain ⟨s, hsle, hsmod, htake, hqmod⟩ := (ihR k').mp ht
          refine ⟨s, by simp; omega, hsmod, ?_, ?_⟩
          · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
            exact htake
          · have hsub : (ys ++ [a]).length - (s + u.length) = (ys.length - (s + u.length)) + 1 := by
              simp; omega
            rw [hsub, hk_eq, ← hqmod, Nat.mod_add_mod]
      · rintro ⟨s, hsle, hsmod, htake, hqmod⟩
        by_cases hlt : s + u.length ≤ ys.length
        · -- Already entered right cycle during ys
          let k' : Fin q := ⟨(ys.length - (s + u.length)) % q, Nat.mod_lt _ (by omega)⟩
          have htake' : (ys.drop s).take u.length = u := by
            rw [List.drop_append_of_le_length (by omega),
                List.take_append_of_le_length (by simp; omega)] at htake
            exact htake
          have hprev : BridgeState.right k' ∈ M.evalFrom M.start ys :=
            (ihR k').mpr ⟨s, hlt, hsmod, htake', rfl⟩
          refine ⟨BridgeState.right k', hprev, ?_⟩
          simp only [M, bridgeNFA, Set.mem_singleton_iff]
          congr 1
          ext
          rw [← hqmod]
          have hsub : (ys ++ [a]).length - (s + u.length) = (ys.length - (s + u.length)) + 1 := by
            simp; omega
          rw [hsub]
          change (ys.length - (s + u.length) + 1) % q = ((ys.length - (s + u.length)) % q + 1) % q
          rw [Nat.mod_add_mod]
        · -- Entering right cycle on the last symbol `a`
          have hseq : s + u.length = ys.length + 1 := by simp at hsle; omega
          have hk0 : k.val = 0 := by
            have : (ys ++ [a]).length - (s + u.length) = 0 := by simp; omega
            rw [this, Nat.zero_mod] at hqmod
            exact hqmod.symm
          have hdrop_eq : (ys ++ [a]).drop s = u := by
            have hlen_drop : ((ys ++ [a]).drop s).length = u.length := by simp; omega
            have := htake
            rwa [List.take_of_length_le (by omega)] at this
          by_cases hu1 : u.length = 1
          · have hs_eq : s = ys.length := by omega
            subst hs_eq
            have htake1 : u.take 1 = u := List.take_of_length_le (by omega)
            have hpair := (drop_append_singleton_iff ys u a ys.length 0 (by omega) (by omega)).mp
              (by rw [htake1]; exact hdrop_eq)
            refine ⟨BridgeState.left ⟨ys.length % p, Nat.mod_lt _ (by omega)⟩,
              (ihL _).mpr rfl, ?_⟩
            simp only [M, bridgeNFA, Set.mem_union, Set.mem_singleton_iff]
            right
            rw [if_pos ⟨hsmod, hpair.2⟩, dif_neg (by omega)]
            simp only [Set.mem_singleton_iff]
            congr 1; ext; exact hk0
          · have h1lt : 1 < u.length := by omega
            let j' : Fin (u.length - 1) := ⟨u.length - 2, by omega⟩
            have hj'_succ : j'.val + 1 = u.length - 1 := by simp [j']; omega
            have hpair := (drop_append_singleton_iff ys u a s (u.length - 1) (by omega) (by omega)).mp
              (by
                have : u.length - 1 + 1 = u.length := by omega
                rwa [this, List.take_of_length_le le_rfl])
            have hprev : BridgeState.mid j' ∈ M.evalFrom M.start ys :=
              (ihM j').mpr ⟨s, by omega, hsmod, by simpa [hj'_succ] using hpair.1⟩
            refine ⟨BridgeState.mid j', hprev, ?_⟩
            simp only [M, bridgeNFA]
            have hc1 : a = u[j'.val + 1]'(by omega) := by simpa [hj'_succ] using hpair.2
            rw [if_pos hc1, dif_neg (by omega)]
            simp only [Set.mem_singleton_iff]
            congr 1; ext; exact hk0

/-- Acceptance characterization of the 2-Prime CRT Bridge NFA. -/
theorem mem_accepts_bridgeNFA {α : Type*} [DecidableEq α] (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (u : List α) (hu : 1 ≤ u.length) (r₁ r₂ : ℕ) (hr₂ : r₂ < q) (y : List α) :
    y ∈ (bridgeNFA p q hp hq u hu r₁ r₂ hr₂).accepts ↔
      ∃ s, s + u.length ≤ y.length ∧ s % p = r₁ ∧
        (y.drop s).take u.length = u ∧ (y.length - (s + u.length)) % q = r₂ := by
  rw [NFA.mem_accepts]
  have hacc : (bridgeNFA p q hp hq u hu r₁ r₂ hr₂).accept = {BridgeState.right ⟨r₂, hr₂⟩} := rfl
  simp only [hacc, Set.mem_singleton_iff, exists_eq_left]
  exact (bridgeNFA_evalFrom_iff p q hp hq u hu r₁ r₂ hr₂ y).2.2 ⟨r₂, hr₂⟩

/-- **Separation Theorem for the 2-Prime CRT Bridge NFA:**
Given `a, b : List α` of length `n`, a position `t` with `t + ℓ ≤ n` (`ℓ ≥ 1`), and primes/moduli
`p, q ≥ 1` such that no occurrence `s` of `u = (a.drop t).take ℓ` in `b` satisfies both
`s % p = t % p` and `s % q = t % q`, the reindexed bridge NFA on `Fin (p + (ℓ - 1) + q)`
accepts `a` and rejects `b`. -/
theorem exists_bridgeNFA_separating {α : Type*} [DecidableEq α] (a b : List α) (n t ell p q : ℕ)
    (halen : a.length = n) (hblen : b.length = n)
    (hell : 1 ≤ ell) (ht : t + ell ≤ n) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (havoid : ∀ s, s + ell ≤ n → (b.drop s).take ell = (a.drop t).take ell →
      ¬(s % p = t % p ∧ s % q = t % q)) :
    ∃ M : NFA α (Fin (p + (ell - 1) + q)), a ∈ M.accepts ∧ b ∉ M.accepts := by
  set u := (a.drop t).take ell with hu_def
  have hulen : u.length = ell := by simp [hu_def, List.length_take, List.length_drop]; omega
  have hu1 : 1 ≤ u.length := by omega
  let r₁ := t % p
  let r₂ := (n - (t + ell)) % q
  have hr₂ : r₂ < q := Nat.mod_lt _ (by omega)
  let M₀ := bridgeNFA p q hp hq u hu1 r₁ r₂ hr₂
  let e : BridgeState p u.length q ≃ Fin (p + (ell - 1) + q) :=
    (bridgeStateEquiv p u.length q).trans (Fin.castOrderIso (by rw [hulen])).toEquiv
  refine ⟨reindexNFA M₀ e, ?_, ?_⟩
  · rw [mem_accepts_reindexNFA, mem_accepts_bridgeNFA]
    exact ⟨t, by omega, rfl, by rw [hulen], by simp [halen, hulen, r₂]⟩
  · rw [mem_accepts_reindexNFA, mem_accepts_bridgeNFA]
    rintro ⟨s, hsle, hsmodp, htake, hsmodq⟩
    have hq_eq : s % q = t % q := by
      have h1 : (n - (s + ell)) % q = (n - (t + ell)) % q := by
        simpa [hblen, hulen, r₂] using hsmodq
      have hz : ((n - (s + ell) : ℕ) : ℤ) % (q : ℤ) = ((n - (t + ell) : ℕ) : ℤ) % (q : ℤ) := by
        exact_mod_cast h1
      have hsub : (((s : ℤ) - (t : ℤ)) % (q : ℤ)) = 0 := by
        have heq_z : (s : ℤ) - (t : ℤ) = ((n - (t + ell) : ℕ) : ℤ) - ((n - (s + ell) : ℕ) : ℤ) := by
          omega
        rw [heq_z, Int.sub_emod, hz, sub_self, Int.zero_emod]
      have hmod_z : (s : ℤ) % (q : ℤ) = (t : ℤ) % (q : ℤ) :=
        Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hsub
      exact_mod_cast hmod_z
    rw [hulen, hu_def] at htake
    exact havoid s (by omega) htake ⟨hsmodp, hq_eq⟩

/-! ## Section 5: Analytic Bounds & World-Record NFA Separating Words Theorems -/

/-- Two distinct equal-length lists have a least differing index `t*`. -/
lemma exists_first_diff {α : Type*} [DecidableEq α] (w x : List α)
    (hlen : w.length = x.length) (hne : w ≠ x) :
    ∃ (tStar : ℕ) (ht : tStar < w.length),
      (∀ (i : ℕ) (hi : i < tStar), w[i]'(by omega) = x[i]'(by omega)) ∧
      w[tStar]'ht ≠ x[tStar]'(by omega) := by
  have hex : ∃ i, ∃ hi : i < w.length, w[i]'hi ≠ x[i]'(by omega) := by
    by_contra hall
    push Not at hall
    apply hne
    exact List.ext_getElem hlen (fun i hi1 hi2 => hall i hi1)
  let tStar := Nat.find hex
  have hspec := Nat.find_spec hex
  rcases hspec with ⟨ht, hdiff⟩
  refine ⟨tStar, ht, ?_, hdiff⟩
  intro i hi
  by_contra hne_i
  exact Nat.find_min hex hi ⟨by omega, hne_i⟩

/-- Elementary bound: `log x ≤ 4 * x^(1/4)` for all `x ≥ 1`. -/
lemma log_le_four_mul_rpow_quarter {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 4 * x ^ ((1 : ℝ) / 4) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have h1 : Real.log (x ^ ((1 : ℝ) / 4)) ≤ x ^ ((1 : ℝ) / 4) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_rpow hxpos] at h1
  linarith

/-- Elementary bound: `x^(1/3) * (log x)^(2/3) ≤ 3 * x^(1/2)` for all `x ≥ 1`. -/
lemma scale_le_three_mul_sqrt {x : ℝ} (hx : 1 ≤ x) :
    x ^ ((1 : ℝ) / 3) * (Real.log x) ^ ((2 : ℝ) / 3) ≤ 3 * x ^ ((1 : ℝ) / 2) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog4 : Real.log x ≤ 4 * x ^ ((1 : ℝ) / 4) := log_le_four_mul_rpow_quarter hx
  have hlhs_nn : 0 ≤ x ^ ((1 : ℝ) / 3) * (Real.log x) ^ ((2 : ℝ) / 3) := by positivity
  have hrhs_nn : 0 ≤ 3 * x ^ ((1 : ℝ) / 2) := by positivity
  rw [← pow_le_pow_iff_left₀ hlhs_nn hrhs_nn (show 3 ≠ 0 by decide)]
  have h1 : (x ^ ((1 : ℝ) / 3) * (Real.log x) ^ ((2 : ℝ) / 3)) ^ 3 = x * (Real.log x) ^ 2 := by
    rw [mul_pow]
    have ha : (x ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    have hb : ((Real.log x) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = (Real.log x) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlog_nn]
      norm_num
    rw [ha, hb]
  have h2 : (3 * x ^ ((1 : ℝ) / 2)) ^ 3 = 27 * x ^ ((3 : ℝ) / 2) := by
    rw [mul_pow]
    have hc : (x ^ ((1 : ℝ) / 2)) ^ (3 : ℕ) = x ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    rw [hc]; norm_num
  have h3 : (Real.log x) ^ 2 ≤ 16 * x ^ ((1 : ℝ) / 2) := by
    have hsq : (Real.log x) ^ 2 ≤ (4 * x ^ ((1 : ℝ) / 4)) ^ 2 :=
      pow_le_pow_left₀ hlog_nn hlog4 2
    have hpow : (4 * x ^ ((1 : ℝ) / 4)) ^ 2 = 16 * x ^ ((1 : ℝ) / 2) := by
      rw [mul_pow]
      have : (x ^ ((1 : ℝ) / 4)) ^ (2 : ℕ) = x ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        norm_num
      rw [this]; norm_num
    linarith
  have h4 : x * x ^ ((1 : ℝ) / 2) = x ^ ((3 : ℝ) / 2) := by
    calc x * x ^ ((1 : ℝ) / 2) = x ^ (1 : ℝ) * x ^ ((1 : ℝ) / 2) := by rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + (1 : ℝ) / 2) := (Real.rpow_add hxpos _ _).symm
      _ = x ^ ((3 : ℝ) / 2) := by norm_num
  rw [h1, h2]
  have h5 : x * (Real.log x) ^ 2 ≤ 16 * x ^ ((3 : ℝ) / 2) := by
    calc x * (Real.log x) ^ 2 ≤ x * (16 * x ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = 16 * (x * x ^ ((1 : ℝ) / 2)) := by ring
      _ = 16 * x ^ ((3 : ℝ) / 2) := by rw [h4]
  have hxp : 0 ≤ x ^ ((3 : ℝ) / 2) := by positivity
  linarith

/-- Elementary bound: `2/3 < log 2`. -/
lemma two_thirds_lt_log_two : (2 : ℝ) / 3 < Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

/-- For `n ≥ 4096`, `8 ≤ (n : ℝ)^(1/4)`. -/
lemma eight_le_rpow_quarter {n : ℕ} (hn : 4096 ≤ n) :
    (8 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
  have hn_r : (4096 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [← pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 8) (by positivity) (show 4 ≠ 0 by decide)]
  have hpow : ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  rw [hpow]
  norm_num
  linarith

/-- For `n ≥ 4096`, `64 ≤ (n : ℝ)^(1/2)`. -/
lemma sixtyfour_le_rpow_half {n : ℕ} (hn : 4096 ≤ n) :
    (64 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
  have hn_r : (4096 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [← pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 64) (by positivity) (show 2 ≠ 0 by decide)]
  have hpow : ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  rw [hpow]
  norm_num
  linarith

/-- For `n ≥ 4096`, `8 ≤ log n`. -/
lemma eight_le_log {n : ℕ} (hn : 4096 ≤ n) : (8 : ℝ) ≤ Real.log (n : ℝ) := by
  have h1 : (2 : ℝ) ^ (12 : ℕ) ≤ (n : ℝ) := by
    have : 2 ^ 12 ≤ n := by omega
    exact_mod_cast this
  have h2 : Real.log ((2 : ℝ) ^ (12 : ℕ)) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  norm_num at h2
  have h3 := two_thirds_lt_log_two
  linarith

/-- For `n ≥ 4096`, `lo + 1 ≤ 2 * (n^(1/3) / (log n)^(1/3))` where `lo = ⌈n^(1/4)⌉`. -/
lemma lo_add_one_le_two_Q {n : ℕ} (hn : 4096 ≤ n) :
    ((Nat.ceil ((n : ℝ) ^ ((1 : ℝ) / 4)) : ℕ) : ℝ) + 1 ≤
      2 * ((n : ℝ) ^ ((1 : ℝ) / 3) / (Real.log (n : ℝ)) ^ ((1 : ℝ) / 3)) := by
  have hn_r : (4096 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog_pos : (0 : ℝ) < Real.log (n : ℝ) := by linarith [eight_le_log hn]
  have hy8 : (8 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := eight_le_rpow_quarter hn
  set y := (n : ℝ) ^ ((1 : ℝ) / 4) with hy_def
  have hceil : ((Nat.ceil y : ℕ) : ℝ) < y + 1 := Nat.ceil_lt_add_one (by linarith)
  have hlo2 : ((Nat.ceil y : ℕ) : ℝ) + 1 ≤ y + 2 := by linarith
  have hlhs_nn : (0 : ℝ) ≤ ((Nat.ceil y : ℕ) : ℝ) + 1 := by positivity
  have hrhs_nn : (0 : ℝ) ≤ 2 * ((n : ℝ) ^ ((1 : ℝ) / 3) / (Real.log (n : ℝ)) ^ ((1 : ℝ) / 3)) := by
    positivity
  rw [← pow_le_pow_iff_left₀ hlhs_nn hrhs_nn (show 3 ≠ 0 by decide)]
  have hpoly : (y + 2) ^ 3 ≤ 2 * y ^ 3 := by
    have : 2 * y ^ 3 - (y + 2) ^ 3 = (y - 8) * (y ^ 2 + 2 * y + 4) + 24 := by ring
    nlinarith
  have hy3 : y ^ (3 : ℕ) = (n : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [hy_def, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hlog4 : Real.log (n : ℝ) ≤ 4 * y := log_le_four_mul_rpow_quarter (by linarith)
  have hy4 : (n : ℝ) ^ ((3 : ℝ) / 4) * y = (n : ℝ) := by
    rw [hy_def, ← Real.rpow_add hn_pos]
    norm_num
  have hrhs_cube : (2 * ((n : ℝ) ^ ((1 : ℝ) / 3) / (Real.log (n : ℝ)) ^ ((1 : ℝ) / 3))) ^ 3 =
      8 * (n : ℝ) / Real.log (n : ℝ) := by
    rw [mul_pow, div_pow]
    have ha : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    have hb : ((Real.log (n : ℝ)) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = Real.log (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    rw [ha, hb]; ring
  rw [hrhs_cube, le_div_iff₀ hlog_pos]
  calc
    (((Nat.ceil y : ℕ) : ℝ) + 1) ^ 3 * Real.log (n : ℝ)
        ≤ (y + 2) ^ 3 * Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlhs_nn hlo2 3) (by linarith)
    _ ≤ (2 * y ^ 3) * (4 * y) :=
          mul_le_mul hpoly hlog4 (by linarith) (by positivity)
    _ = 8 * ((n : ℝ) ^ ((3 : ℝ) / 4) * y) := by rw [hy3]; ring
    _ = 8 * (n : ℝ) := by rw [hy4]

/-- Prime-interval cardinality lower bound from `primesUpTo M` and `lo`. -/
lemma primesUpTo_card_le_Ioc_add (lo M : ℕ) :
    (primesUpTo M).card ≤ ((Finset.Ioc lo M).filter Nat.Prime).card + lo := by
  have hsub : primesUpTo M ⊆ (Finset.Ioc lo M).filter Nat.Prime ∪ Finset.Icc 1 lo := by
    intro p hp
    rw [primesUpTo, Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
    by_cases h : p ≤ lo
    · right; exact ⟨hp.1.1, h⟩
    · left; exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
  calc
    (primesUpTo M).card ≤ ((Finset.Ioc lo M).filter Nat.Prime ∪ Finset.Icc 1 lo).card :=
      Finset.card_le_card hsub
    _ ≤ ((Finset.Ioc lo M).filter Nat.Prime).card + (Finset.Icc 1 lo).card :=
      Finset.card_union_le _ _
    _ = ((Finset.Ioc lo M).filter Nat.Prime).card + lo := by simp [Nat.card_Icc]

/-- **World-Record NFA Separating Words Upper Bound (Large `n ≥ 4096`, explicit constant `26`):**
For any alphabet `α` and any two distinct equal-length words `w, x : List α` of length `n ≥ 4096`,
there exists a pure-Mathlib `M : NFA α (Fin m)` separating `w` and `x` with
`m ≤ 26 * n^(1/3) * (Real.log n)^(2/3)`. -/
theorem ppl090_nfa_separating_words_large
    {α : Type*} (w x : List α)
    (hlen : w.length = x.length) (hne : w ≠ x) (hn : 4096 ≤ w.length) :
    ∃ (m : ℕ) (M : NFA α (Fin m)),
      ((w ∈ M.accepts ∧ x ∉ M.accepts) ∨ (x ∈ M.accepts ∧ w ∉ M.accepts)) ∧
      (m : ℝ) ≤ 26 * (w.length : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (w.length : ℝ)) ^ ((2 : ℝ) / 3) := by
  classical
  set n := w.length with hn_def
  have hn_r : (4096 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog_ge8 : (8 : ℝ) ≤ Real.log (n : ℝ) := eight_le_log hn
  have hlog_pos : (0 : ℝ) < Real.log (n : ℝ) := by linarith
  set scale : ℝ := (n : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) with hscale_def
  have hscale_ge64 : (64 : ℝ) ≤ scale := by
    have ha : (16 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [← pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 16) (by positivity) (show 3 ≠ 0 by decide)]
      have : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = (n : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
      rw [this]; norm_num; linarith
    have hb : (4 : ℝ) ≤ (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) := by
      rw [← pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 4) (by positivity) (show 3 ≠ 0 by decide)]
      have : ((Real.log (n : ℝ)) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = (Real.log (n : ℝ)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
      rw [this]; nlinarith
    calc (64 : ℝ) = 16 * 4 := by norm_num
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) :=
          mul_le_mul ha hb (by norm_num) (by positivity)
  have hscale_le_sqrt : scale ≤ 3 * (n : ℝ) ^ ((1 : ℝ) / 2) := scale_le_three_mul_sqrt (by linarith)
  set k : ℕ := Nat.floor (scale / 4) with hk_def
  have hk_ge16 : 16 ≤ k := by
    rw [hk_def]
    exact Nat.le_floor (by norm_num; linarith)
  have hk_ge1 : 1 ≤ k := by omega
  have hk_le_real : (k : ℝ) ≤ scale / 4 := Nat.floor_le (by linarith)
  have hk_gt_real : scale / 4 < (k : ℝ) + 1 := Nat.lt_floor_add_one (scale / 4)
  have h8k_le_n : 8 * k ≤ n := by
    have h1 : ((8 * k : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      have hsqrt : (64 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := sixtyfour_le_rpow_half hn
      have hsq : ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = (n : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
      nlinarith
    exact_mod_cast h1
  -- Find first differing index t*
  obtain ⟨tStar, htStar_lt, hagree, hdiff⟩ := exists_first_diff w x hlen hne
  -- Case 1: t* < 4 * k -> Prefix NFA
  by_cases hcase1 : tStar < 4 * k
  · refine ⟨tStar + 2, prefixNFA tStar (w[tStar]'htStar_lt), Or.inl ⟨?_, ?_⟩, ?_⟩
    · rw [mem_accepts_prefixNFA tStar _ w htStar_lt]
    · rw [mem_accepts_prefixNFA tStar _ x (by omega)]
      exact hdiff.symm
    · have h1 : ((tStar + 2 : ℕ) : ℝ) ≤ (4 * (k : ℝ) + 1) := by
        have : tStar + 2 ≤ 4 * k + 1 := by omega
        exact_mod_cast this
      have h2 : 4 * (k : ℝ) ≤ scale := by linarith
      rw [show 26 * (n : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) = 26 * scale by
        rw [hscale_def]; ring]
      linarith
  -- Case 2: n < t* + 4 * k -> Suffix NFA
  by_cases hcase2 : n < tStar + 4 * k
  · set d := n - tStar with hd_def
    have hd1 : 1 ≤ d := by omega
    have hd_le : d ≤ 4 * k := by omega
    refine ⟨d + 1, suffixNFA d hd1 (w[tStar]'htStar_lt), Or.inl ⟨?_, ?_⟩, ?_⟩
    · rw [mem_accepts_suffixNFA d hd1 _ w (by omega)]
      have heq : w.length - d = tStar := by omega
      simp only [heq]
    · rw [mem_accepts_suffixNFA d hd1 _ x (by omega)]
      have heq : x.length - d = tStar := by omega
      simp only [heq]
      exact hdiff.symm
    · have h1 : ((d + 1 : ℕ) : ℝ) ≤ 4 * (k : ℝ) + 1 := by
        have : d + 1 ≤ 4 * k + 1 := by omega
        exact_mod_cast this
      have h2 : 4 * (k : ℝ) ≤ scale := by linarith
      rw [show 26 * (n : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) = 26 * scale by
        rw [hscale_def]; ring]
      linarith
  -- Case 3: 4 * k ≤ t* and t* + 4 * k ≤ n -> Fine-Wilf + Prime-Pair Avoidance + 2-Prime CRT Bridge NFA
  have htlo : 4 * k ≤ tStar := by omega
  have hthi : tStar + 4 * k ≤ n := by omega
  -- Analytic prime parameters: lo = ⌈n^(1/4)⌉, mHalf = ⌈6 * scale⌉, M = 2 * mHalf
  set lo : ℕ := Nat.ceil ((n : ℝ) ^ ((1 : ℝ) / 4)) with hlo_def
  set mHalf : ℕ := Nat.ceil (6 * scale) with hmHalf_def
  set M : ℕ := 2 * mHalf with hM_def
  have hmHalf_ge4 : 4 ≤ mHalf := by
    have h1 : (4 : ℝ) ≤ (mHalf : ℝ) := le_trans (by linarith) (Nat.le_ceil _)
    exact_mod_cast h1
  have hM_ge : 12 * scale ≤ (M : ℝ) := by
    have h1 : 6 * scale ≤ (mHalf : ℝ) := Nat.le_ceil _
    rw [hM_def]; push_cast; linarith
  have hM_le : (M : ℝ) ≤ 12 * scale + 2 := by
    have h1 : (mHalf : ℝ) < 6 * scale + 1 := Nat.ceil_lt_add_one (by linarith)
    rw [hM_def]; push_cast; linarith
  have hM_le_n : M ≤ n := by
    have h1 : (M : ℝ) ≤ (n : ℝ) := by
      have hsqrt : (64 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := sixtyfour_le_rpow_half hn
      have hsq : ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = (n : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
      nlinarith
    exact_mod_cast h1
  have hlo4 : n ≤ lo ^ 4 := by
    have h1 : (n : ℝ) ≤ ((lo : ℝ) ^ 4) := by
      have hle : (n : ℝ) ^ ((1 : ℝ) / 4) ≤ (lo : ℝ) := Nat.le_ceil _
      have hpow : ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = (n : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
      rw [← hpow]
      exact pow_le_pow_left₀ (by positivity) hle 4
    exact_mod_cast h1
  -- Show P = (Ioc lo M).filter Nat.Prime has P.card * (P.card - 1) > 6 * (n / (k + 1))
  set P : Finset ℕ := (Finset.Ioc lo M).filter Nat.Prime with hP_def
  set Q : ℝ := (n : ℝ) ^ ((1 : ℝ) / 3) / (Real.log (n : ℝ)) ^ ((1 : ℝ) / 3) with hQ_def
  have hQ_pos : 0 < Q := by positivity
  have hQ_ge1 : (1 : ℝ) ≤ Q := by
    rw [hQ_def, one_le_div (by positivity)]
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (show 3 ≠ 0 by decide)]
    have ha : ((Real.log (n : ℝ)) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = Real.log (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    have hb : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    rw [ha, hb]
    linarith [Real.log_le_sub_one_of_pos hn_pos]
  have hscale_div_log : scale / Real.log (n : ℝ) = Q := by
    rw [div_eq_iff (ne_of_gt hlog_pos), hscale_def, hQ_def]
    have h1 : (Real.log (n : ℝ)) ^ ((1 : ℝ) / 3) ≠ 0 := ne_of_gt (by positivity)
    rw [div_mul_eq_mul_div, eq_div_iff h1]
    have h2 : (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / 3) = Real.log (n : ℝ) := by
      rw [← Real.rpow_add hlog_pos]; norm_num
    calc (n : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / 3)
        = (n : ℝ) ^ ((1 : ℝ) / 3) * ((Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / 3)) := by ring
      _ = (n : ℝ) ^ ((1 : ℝ) / 3) * Real.log (n : ℝ) := by rw [h2]
  have hP_ge_6Q : 6 * Q ≤ (P.card : ℝ) := by
    have hcheb := prime_card_real_lower_bound mHalf hmHalf_ge4
    have hlogM_le : Real.log ((2 * mHalf : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hM_le_n
    have hM_pos : (0 : ℝ) < ((2 * mHalf : ℕ) : ℝ) := by positivity
    have h8Q : 8 * Q * Real.log (n : ℝ) < ((2 * mHalf : ℕ) : ℝ) * Real.log 2 := by
      have h1 : 8 * Q * Real.log (n : ℝ) = 8 * scale := by
        rw [← hscale_div_log]; field_simp
      rw [h1]
      have h2 := two_thirds_lt_log_two
      have h3 : 12 * scale ≤ ((2 * mHalf : ℕ) : ℝ) := by simpa [hM_def] using hM_ge
      nlinarith
    have hcard_le : ((primesUpTo (2 * mHalf)).card : ℝ) ≤ (P.card : ℝ) + (lo : ℝ) := by
      exact_mod_cast primesUpTo_card_le_Ioc_add lo M
    have hstep1 : 8 * Q * Real.log (n : ℝ) < ((P.card : ℝ) + ((lo : ℝ) + 1)) * Real.log (n : ℝ) := by
      calc 8 * Q * Real.log (n : ℝ)
          < ((2 * mHalf : ℕ) : ℝ) * Real.log 2 := h8Q
        _ < (((primesUpTo (2 * mHalf)).card + 1 : ℕ) : ℝ) * Real.log ((2 * mHalf : ℕ) : ℝ) := hcheb
        _ ≤ (((primesUpTo (2 * mHalf)).card + 1 : ℕ) : ℝ) * Real.log (n : ℝ) :=
            mul_le_mul_of_nonneg_left hlogM_le (by positivity)
        _ ≤ ((P.card : ℝ) + ((lo : ℝ) + 1)) * Real.log (n : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            push_cast; linarith
    have hstep2 : 8 * Q < (P.card : ℝ) + ((lo : ℝ) + 1) :=
      lt_of_mul_lt_mul_right hstep1 (by linarith)
    have hlo_ub : (lo : ℝ) + 1 ≤ 2 * Q := lo_add_one_le_two_Q hn
    linarith
  have hQ_sq : (n : ℝ) / scale = Q ^ 2 := by
    rw [div_eq_iff (by positivity : scale ≠ 0), hscale_def, hQ_def, div_pow]
    have h1 : ((Real.log (n : ℝ)) ^ ((1 : ℝ) / 3)) ^ 2 = (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    have h2 : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 3) = (n : ℝ) := by
      have ha : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ (2 : ℕ) = (n : ℝ) ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
      rw [ha, ← Real.rpow_add hn_pos]; norm_num
    have hne_log : (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) ≠ 0 := ne_of_gt (by positivity)
    rw [h1]
    calc (n : ℝ) = ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 3) := h2.symm
      _ = ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 / (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) *
            ((n : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3)) := by
            field_simp [hne_log]
  -- Helper: given an injective side (a, b), build the separating CRT bridge NFA
  have hbuild : ∀ (a b : List α) (halen : a.length = n) (hblen : b.length = n),
      a[tStar]'(by omega) ≠ b[tStar]'(by omega) →
      Set.InjOn (winAt a tStar k) (Finset.Icc (2 * k) (3 * k) : Set ℕ) →
      ∃ (m : ℕ) (M_nfa : NFA α (Fin m)),
        (a ∈ M_nfa.accepts ∧ b ∉ M_nfa.accepts) ∧
        (m : ℝ) ≤ 26 * (n : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) := by
    intro a b halen hblen hab_diff hinj
    obtain ⟨t, ht_le, hwin_ne, hocc_le⟩ :=
      exists_rare_differing_factor a b n tStar k halen hblen hk_ge1 htlo hthi hab_diff hinj
    set S : Finset ℕ := (Finset.range (n - 4 * k + 1)).filter
      (fun s => (b.drop s).take (4 * k) = (a.drop t).take (4 * k)) with hS_def
    have hS_lt : ∀ s ∈ S, s < n := by
      intro s hs
      have := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
      omega
    have ht_not : t ∉ S := by
      intro ht_in
      have := (Finset.mem_filter.mp ht_in).2
      exact hwin_ne this.symm
    have hP_pos : 1 ≤ P.card := by
      have : (1 : ℝ) ≤ (P.card : ℝ) := by linarith
      exact_mod_cast this
    have hcard_ineq : 6 * S.card < P.card * (P.card - 1) := by
      have hreal : ((6 * S.card : ℕ) : ℝ) < ((P.card * (P.card - 1) : ℕ) : ℝ) := by
        have hS_ub : (6 : ℝ) * (S.card : ℝ) < 24 * Q ^ 2 := by
          have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
          have h1 : ((k : ℝ) + 1) * (S.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hocc_le
          have h2 : (S.card : ℝ) ≤ (n : ℝ) / ((k : ℝ) + 1) := (le_div_iff₀' hk1_pos).mpr h1
          have h3 : (n : ℝ) / ((k : ℝ) + 1) < (n : ℝ) / (scale / 4) :=
            div_lt_div_of_pos_left hn_pos (by linarith) hk_gt_real
          have h4 : (n : ℝ) / (scale / 4) = 4 * ((n : ℝ) / scale) := by ring
          rw [h4, hQ_sq] at h3
          linarith
        have hP_lb : 30 * Q ^ 2 ≤ ((P.card * (P.card - 1) : ℕ) : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_sub hP_pos, Nat.cast_one]
          nlinarith
        have hS_cast : ((6 * S.card : ℕ) : ℝ) = (6 : ℝ) * (S.card : ℝ) := by push_cast; rfl
        rw [hS_cast]
        nlinarith
      exact_mod_cast hreal
    obtain ⟨p, hpP, q, hqP, _, havoid_S⟩ :=
      exists_avoiding_prime_pair n lo M t S hS_lt (by omega) ht_not hlo4 hcard_ineq
    have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hpP).2
    have hq_prime : Nat.Prime q := (Finset.mem_filter.mp hqP).2
    have hp_le : p ≤ M := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpP).1).2
    have hq_le : q ≤ M := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hqP).1).2
    have havoid : ∀ s, s + 4 * k ≤ n → (b.drop s).take (4 * k) = (a.drop t).take (4 * k) →
        ¬(s % p = t % p ∧ s % q = t % q) := by
      intro s hsle htake
      apply havoid_S s
      rw [hS_def, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, htake⟩
    obtain ⟨M_nfa, ha_acc, hb_rej⟩ :=
      exists_bridgeNFA_separating a b n t (4 * k) p q halen hblen (by omega) ht_le
        hp_prime.one_le hq_prime.one_le havoid
    refine ⟨p + (4 * k - 1) + q, M_nfa, ⟨ha_acc, hb_rej⟩, ?_⟩
    have hm_le : p + (4 * k - 1) + q ≤ 2 * M + 4 * k := by omega
    have hm_r : ((p + (4 * k - 1) + q : ℕ) : ℝ) ≤ 2 * (M : ℝ) + 4 * (k : ℝ) := by
      exact_mod_cast hm_le
    rw [show 26 * (n : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) = 26 * scale by
      rw [hscale_def]; ring]
    linarith
  -- Apply Distinct Windows Theorem (Fine-Wilf)
  rcases exists_injective_windows w x n tStar k rfl hlen.symm hk_ge1 htlo hthi hagree hdiff with
    hinj_w | hinj_x
  · obtain ⟨m, M_nfa, hsep, hm⟩ := hbuild w x rfl hlen.symm hdiff hinj_w
    exact ⟨m, M_nfa, Or.inl hsep, hm⟩
  · obtain ⟨m, M_nfa, hsep, hm⟩ := hbuild x w hlen.symm rfl hdiff.symm hinj_x
    exact ⟨m, M_nfa, Or.inr hsep, hm⟩

/-- Helper: for `2 ≤ n < 4096`, `n + 1 ≤ 128 * n^(1/3) * (Real.log n)^(2/3)`. -/
lemma small_n_bound {n : ℕ} (hn2 : 2 ≤ n) (hnlt : n < 4096) :
    ((n + 1 : ℕ) : ℝ) ≤ 128 * (n : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn_ge2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hlog2 : (2 : ℝ) / 3 < Real.log 2 := two_thirds_lt_log_two
  have hlog_pos : (0 : ℝ) < Real.log (n : ℝ) := by
    have : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn_ge2
    linarith
  have hlhs_nn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hrhs_nn : (0 : ℝ) ≤ 128 * (n : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3) := by
    positivity
  rw [← pow_le_pow_iff_left₀ hlhs_nn hrhs_nn (show 3 ≠ 0 by decide)]
  have hrhs_cube : (128 * (n : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3)) ^ 3 =
      (128 : ℝ) ^ 3 * (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    rw [mul_pow, mul_pow]
    have ha : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    have hb : ((Real.log (n : ℝ)) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = (Real.log (n : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    rw [ha, hb]
  rw [hrhs_cube]
  have hlog_pow2 : ∀ e : ℕ, 2 ^ e ≤ n → (e : ℝ) * ((2 : ℝ) / 3) ≤ Real.log (n : ℝ) := by
    intro e he
    have h1 : ((2 : ℝ) ^ e) ≤ (n : ℝ) := by exact_mod_cast he
    have h2 : Real.log ((2 : ℝ) ^ e) ≤ Real.log (n : ℝ) := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    have h3 : (e : ℝ) * ((2 : ℝ) / 3) ≤ (e : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  by_cases h64 : n < 64
  · have hlog_lb : (2 : ℝ) / 3 ≤ Real.log (n : ℝ) := by
      simpa using hlog_pow2 1 (by omega)
    have hn_ub : ((n + 1 : ℕ) : ℝ) ≤ 64 := by exact_mod_cast (show n + 1 ≤ 64 by omega)
    have hsq : ((2 : ℝ) / 3) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := pow_le_pow_left₀ (by norm_num) hlog_lb 2
    nlinarith [pow_le_pow_left₀ hlhs_nn hn_ub 3]
  · by_cases h512 : n < 512
    · have hlog_lb : (4 : ℝ) ≤ Real.log (n : ℝ) := by
        have := hlog_pow2 6 (by omega); norm_num at this; linarith
      have hn_lb : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 64 ≤ n by omega)
      have hn_ub : ((n + 1 : ℕ) : ℝ) ≤ 512 := by exact_mod_cast (show n + 1 ≤ 512 by omega)
      have hsq : (16 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by nlinarith
      have h3 : ((n + 1 : ℕ) : ℝ) ^ 3 ≤ 512 ^ 3 := pow_le_pow_left₀ hlhs_nn hn_ub 3
      nlinarith
    · by_cases h1024 : n < 1024
      · have hlog_lb : (6 : ℝ) ≤ Real.log (n : ℝ) := by
          have := hlog_pow2 9 (by omega); norm_num at this; linarith
        have hn_lb : (512 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 512 ≤ n by omega)
        have hn_ub : ((n + 1 : ℕ) : ℝ) ≤ 1024 := by exact_mod_cast (show n + 1 ≤ 1024 by omega)
        have hsq : (36 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by nlinarith
        have h3 : ((n + 1 : ℕ) : ℝ) ^ 3 ≤ 1024 ^ 3 := pow_le_pow_left₀ hlhs_nn hn_ub 3
        nlinarith
      · have hlog_lb : (20 : ℝ) / 3 ≤ Real.log (n : ℝ) := by
          have := hlog_pow2 10 (by omega); norm_num at this; linarith
        have hn_lb : (1024 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1024 ≤ n by omega)
        have hn_ub : ((n + 1 : ℕ) : ℝ) ≤ 4096 := by exact_mod_cast (show n + 1 ≤ 4096 by omega)
        have hsq : (400 : ℝ) / 9 ≤ (Real.log (n : ℝ)) ^ 2 := by nlinarith
        have h3 : ((n + 1 : ℕ) : ℝ) ^ 3 ≤ 4096 ^ 3 := pow_le_pow_left₀ hlhs_nn hn_ub 3
        nlinarith

/-- **Main Pure-Mathlib World-Record Theorem (PPL 090 / Shallit Open Problem #3):**
For **every** alphabet `α` and **every** pair of distinct equal-length words `w, x : List α`
of length `n ≥ 2`, there exists an NFA `M : NFA α (Fin m)` separating `w` and `x`
with at most `128 * n^(1/3) * (Real.log n)^(2/3)` states. -/
theorem ppl090_nfa_separating_words_bound
    {α : Type*} (w x : List α)
    (hlen : w.length = x.length) (hne : w ≠ x) (hn : 2 ≤ w.length) :
    ∃ (m : ℕ) (M : NFA α (Fin m)),
      ((w ∈ M.accepts ∧ x ∉ M.accepts) ∨ (x ∈ M.accepts ∧ w ∉ M.accepts)) ∧
      (m : ℝ) ≤ 128 * (w.length : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (w.length : ℝ)) ^ ((2 : ℝ) / 3) := by
  classical
  by_cases hbig : 4096 ≤ w.length
  · obtain ⟨m, M, hsep, hm⟩ := ppl090_nfa_separating_words_large w x hlen hne hbig
    refine ⟨m, M, hsep, ?_⟩
    have hlog_nn : 0 ≤ Real.log (w.length : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ w.length))
    have hprod_nn : 0 ≤ (w.length : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (w.length : ℝ)) ^ ((2 : ℝ) / 3) := by
      positivity
    linarith
  · obtain ⟨tStar, htStar_lt, _, hdiff⟩ := exists_first_diff w x hlen hne
    refine ⟨tStar + 2, prefixNFA tStar (w[tStar]'htStar_lt), Or.inl ⟨?_, ?_⟩, ?_⟩
    · rw [mem_accepts_prefixNFA tStar _ w htStar_lt]
    · rw [mem_accepts_prefixNFA tStar _ x (by omega)]
      exact hdiff.symm
    · have h1 : ((tStar + 2 : ℕ) : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show tStar + 2 ≤ w.length + 1 by omega)
      exact le_trans h1 (small_n_bound hn (by omega))

end PPL121
