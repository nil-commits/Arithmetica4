import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# PPL 036 (Shallit #9 — Morphic Word Shifted Hankel Determinants) — Partial Structural & Barrier Milestone

**Honest Scope Notice (PPL 036 REMAINS OPEN):**
- **PPL 036 (Shallit #9, $100):** Let `(a_i)_{i ≥ 0}` be the fixed point of `μ : 1 ↦ 12, 2 ↦ 23, 3 ↦ 14, 4 ↦ 32` (`a 0 = 1, a 1 = 2, a 2 = 2, a 3 = 3, ...`). Does every shifted Hankel matrix `H_n^{(k)} = (a_{k + i + j})_{0 ≤ i, j < n}` have nonzero determinant for all `k ≥ 0` and `n ≥ 1`? Remains **OPEN**.
- This file formalizes the unconditionally proved algebraic, combinatorial, and modular barrier theorems from `scripts/ppl036_findings.md` using **pure Mathlib signatures only** (`0` custom or `private` definitions in any public theorem signature).

## Verified Theorems
1. `ppl036_existence_uniqueness`: Existence and uniqueness of the fixed point `a : ℕ → ℕ` satisfying `a 0 = 1`, `a (2 * i) = μ₀ (a i)`, and `a (2 * i + 1) = μ₁ (a i)`.
2. `ppl036_alphabet_and_modular_laws`: For all `i : ℕ`, `a i ∈ ({1, 2, 3, 4} : Finset ℕ)`, exact mod-2 pairing `(a (2 * i) + a (2 * i + 1)) % 2 = 1`, and exact mod-3 shift `a (2 * i + 1) % 3 = (a i + 1) % 3`.
3. `ppl036_factor2_and_forbidden_pairs`: Exact classification of all length-2 factors `(a i, a (i + 1))` into the `9`-pair set `P₂`, implying `(1, 1)`, `(3, 3)`, and `(4, 4)` never occur.
4. `ppl036_over_Q_linear_obstruction`: The `4 × 4` matrix `[1, x, μ₀(x), μ₁(x)]_{x ∈ {1,2,3,4}}` over `ℚ` has determinant `6 ≠ 0`, obstructing any nontrivial `ℚ`-linear relation linking `1, a_i, a_{2i}, a_{2i+1}`.
5. `ppl036_char2_frobenius_deg8`: Over `𝔽₂[[X]] = PowerSeries (ZMod 2)`, `F = PowerSeries.mk (fun i => (a i : ZMod 2))` satisfies the exact degree-8 Frobenius equation `X + (1 + X) ^ 2 * F + (1 + X) ^ 3 * F ^ 2 + X ^ 2 * (1 + X) ^ 3 * (F ^ 4 + F ^ 8) = 0`.
6. `ppl036_hankel_1_2_3_nonvanishing`: Universal shifted Hankel nonvanishing `det H_n^{(k)} ≠ 0` for ALL `k : ℕ` and `n ∈ {1, 2, 3}`, proved unconditionally via length-3 factor classification (zero `native_decide`).
7. `ppl036_modular_vanishing_barriers`: Explicit zero-`native_decide` witnesses proving `det H_n^{(k)} ≡ 0 [MOD p]` occurs for `p = 2` (`k = 1, n = 1`), `p = 3` (`k = 3, n = 1`), and `p = 5` (`k = 2, n = 2`).
-/

private def mu0 (x : ℕ) : ℕ :=
  if x = 1 then 1 else if x = 2 then 2 else if x = 3 then 1 else 3

private def mu1 (x : ℕ) : ℕ :=
  if x = 1 then 2 else if x = 2 then 3 else if x = 3 then 4 else 2

private def seqA : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    if (n + 1) % 2 = 0 then mu0 (seqA ((n + 1) / 2)) else mu1 (seqA ((n + 1) / 2))

private lemma seqA_zero : seqA 0 = 1 := by simp [seqA]

private lemma seqA_even (i : ℕ) : seqA (2 * i) = mu0 (seqA i) := by
  cases i with
  | zero => simp [seqA_zero, mu0]
  | succ m =>
    have hpos : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    have hmod : (2 * m + 1 + 1) % 2 = 0 := by omega
    have hdiv : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    conv_lhs => rw [hpos, seqA]
    simp [hmod, hdiv]

private lemma seqA_odd (i : ℕ) : seqA (2 * i + 1) = mu1 (seqA i) := by
  have hmod : (2 * i + 1) % 2 = 1 := by omega
  have hdiv : (2 * i + 1) / 2 = i := by omega
  conv_lhs => rw [seqA]
  simp [hmod, hdiv]

private lemma eq_of_recurrence
    (a b : ℕ → ℕ)
    (ha0 : a 0 = 1)
    (ha : ∀ i : ℕ, a (2 * i) = mu0 (a i) ∧ a (2 * i + 1) = mu1 (a i))
    (hb0 : b 0 = 1)
    (hb : ∀ i : ℕ, b (2 * i) = mu0 (b i) ∧ b (2 * i + 1) = mu1 (b i)) :
    a = b := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [ha0, hb0]
    | succ m =>
      rcases Nat.even_or_odd (m + 1) with ⟨i, hi⟩ | ⟨i, hi⟩
      · have hi' : m + 1 = 2 * i := by omega
        have hlt : i < m + 1 := by omega
        rw [hi', (ha i).1, (hb i).1, ih i hlt]
      · have hi' : m + 1 = 2 * i + 1 := by omega
        have hlt : i < m + 1 := by omega
        rw [hi', (ha i).2, (hb i).2, ih i hlt]

theorem ppl036_existence_uniqueness :
    (∃ a : ℕ → ℕ,
      (a 0 = 1 ∧
        ∀ i : ℕ,
          a (2 * i) = (if a i = 1 then 1 else if a i = 2 then 2 else if a i = 3 then 1 else 3) ∧
          a (2 * i + 1) = (if a i = 1 then 2 else if a i = 2 then 3 else if a i = 3 then 4 else 2))) ∧
    (∀ a b : ℕ → ℕ,
      (a 0 = 1 ∧
        ∀ i : ℕ,
          a (2 * i) = (if a i = 1 then 1 else if a i = 2 then 2 else if a i = 3 then 1 else 3) ∧
          a (2 * i + 1) = (if a i = 1 then 2 else if a i = 2 then 3 else if a i = 3 then 4 else 2)) →
      (b 0 = 1 ∧
        ∀ i : ℕ,
          b (2 * i) = (if b i = 1 then 1 else if b i = 2 then 2 else if b i = 3 then 1 else 3) ∧
          b (2 * i + 1) = (if b i = 1 then 2 else if b i = 2 then 3 else if b i = 3 then 4 else 2)) →
      a = b) := by
  refine ⟨⟨seqA, seqA_zero, fun i => ⟨seqA_even i, seqA_odd i⟩⟩, ?_⟩
  intro a b ha hb
  exact eq_of_recurrence a b ha.1 ha.2 hb.1 hb.2

private lemma seq_alphabet
    (a : ℕ → ℕ)
    (ha0 : a 0 = 1)
    (ha : ∀ i : ℕ, a (2 * i) = mu0 (a i) ∧ a (2 * i + 1) = mu1 (a i))
    (i : ℕ) :
    a i = 1 ∨ a i = 2 ∨ a i = 3 ∨ a i = 4 := by
  induction i using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => left; exact ha0
    | succ m =>
      rcases Nat.even_or_odd (m + 1) with ⟨j, hj⟩ | ⟨j, hj⟩
      · have hj' : m + 1 = 2 * j := by omega
        have hlt : j < m + 1 := by omega
        rw [hj', (ha j).1]
        rcases ih j hlt with h | h | h | h <;> simp [mu0, h]
      · have hj' : m + 1 = 2 * j + 1 := by omega
        have hlt : j < m + 1 := by omega
        rw [hj', (ha j).2]
        rcases ih j hlt with h | h | h | h <;> simp [mu1, h]

theorem ppl036_alphabet_and_modular_laws
    (a : ℕ → ℕ)
    (ha0 : a 0 = 1)
    (ha : ∀ i : ℕ,
      a (2 * i) = (if a i = 1 then 1 else if a i = 2 then 2 else if a i = 3 then 1 else 3) ∧
      a (2 * i + 1) = (if a i = 1 then 2 else if a i = 2 then 3 else if a i = 3 then 4 else 2)) :
    (∀ i : ℕ, a i ∈ ({1, 2, 3, 4} : Finset ℕ)) ∧
    (∀ i : ℕ, (a (2 * i) + a (2 * i + 1)) % 2 = 1) ∧
    (∀ i : ℕ, a (2 * i + 1) % 3 = (a i + 1) % 3) := by
  have ha' : ∀ i : ℕ, a (2 * i) = mu0 (a i) ∧ a (2 * i + 1) = mu1 (a i) := ha
  have hmem := seq_alphabet a ha0 ha'
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases hmem i with h | h | h | h <;> simp [h]
  · intro i
    rw [(ha' i).1, (ha' i).2]
    rcases hmem i with h | h | h | h <;> simp [mu0, mu1, h]
  · intro i
    rw [(ha' i).2]
    rcases hmem i with h | h | h | h <;> simp [mu1, h]

private def factor2Prop (p : ℕ × ℕ) : Prop :=
  p = (1, 2) ∨ p = (1, 4) ∨ p = (2, 1) ∨ p = (2, 2) ∨ p = (2, 3) ∨
  p = (3, 1) ∨ p = (3, 2) ∨ p = (4, 1) ∨ p = (4, 2)

private lemma seq_factor2
    (a : ℕ → ℕ)
    (ha0 : a 0 = 1)
    (ha : ∀ i : ℕ, a (2 * i) = mu0 (a i) ∧ a (2 * i + 1) = mu1 (a i))
    (i : ℕ) :
    factor2Prop (a i, a (i + 1)) := by
  have hmem := seq_alphabet a ha0 ha
  induction i using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hj' : n = 2 * j := by omega
      have hsucc : n + 1 = 2 * j + 1 := by omega
      have ha_n : a n = mu0 (a j) := by rw [hj', (ha j).1]
      have ha_n1 : a (n + 1) = mu1 (a j) := by rw [hsucc, (ha j).2]
      rw [ha_n, ha_n1]
      rcases hmem j with h | h | h | h <;> simp [factor2Prop, mu0, mu1, h]
    · have hj' : n = 2 * j + 1 := by omega
      have hsucc : n + 1 = 2 * (j + 1) := by omega
      have hlt : j < n := by omega
      have ha_n : a n = mu1 (a j) := by rw [hj', (ha j).2]
      have ha_n1 : a (n + 1) = mu0 (a (j + 1)) := by rw [hsucc, (ha (j + 1)).1]
      rw [ha_n, ha_n1]
      rcases ih j hlt with h | h | h | h | h | h | h | h | h <;>
        · simp only [Prod.mk.injEq] at h
          simp [factor2Prop, mu0, mu1, h.1, h.2]

theorem ppl036_factor2_and_forbidden_pairs
    (a : ℕ → ℕ)
    (ha0 : a 0 = 1)
    (ha : ∀ i : ℕ,
      a (2 * i) = (if a i = 1 then 1 else if a i = 2 then 2 else if a i = 3 then 1 else 3) ∧
      a (2 * i + 1) = (if a i = 1 then 2 else if a i = 2 then 3 else if a i = 3 then 4 else 2)) :
    (∀ i : ℕ,
      (a i, a (i + 1)) ∈
        ({(1, 2), (1, 4), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (4, 1), (4, 2)} :
          Finset (ℕ × ℕ))) ∧
    (∀ i : ℕ, ¬(a i = 1 ∧ a (i + 1) = 1)) ∧
    (∀ i : ℕ, ¬(a i = 3 ∧ a (i + 1) = 3)) ∧
    (∀ i : ℕ, ¬(a i = 4 ∧ a (i + 1) = 4)) := by
  have hf2 := seq_factor2 a ha0 ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rcases hf2 i with h | h | h | h | h | h | h | h | h <;> simp [h]
  · intro i ⟨h1, h2⟩
    have hp : (a i, a (i + 1)) = (1, 1) := Prod.ext h1 h2
    rcases hf2 i with h | h | h | h | h | h | h | h | h <;> rw [h] at hp <;> simp at hp
  · intro i ⟨h1, h2⟩
    have hp : (a i, a (i + 1)) = (3, 3) := Prod.ext h1 h2
    rcases hf2 i with h | h | h | h | h | h | h | h | h <;> rw [h] at hp <;> simp at hp
  · intro i ⟨h1, h2⟩
    have hp : (a i, a (i + 1)) = (4, 4) := Prod.ext h1 h2
    rcases hf2 i with h | h | h | h | h | h | h | h | h <;> rw [h] at hp <;> simp at hp

theorem ppl036_over_Q_linear_obstruction :
    let M : Matrix (Fin 4) (Fin 4) ℚ :=
      !![1, 1, 1, 2;
         1, 2, 2, 3;
         1, 3, 1, 4;
         1, 4, 3, 2]
    M.det = 6 ∧
    M.det ≠ 0 ∧
    (∀ c₀ c₁ c₂ c₃ : ℚ,
      (∀ x : ℕ, x ∈ ({1, 2, 3, 4} : Finset ℕ) →
        c₀ + c₁ * (x : ℚ) +
        c₂ * ((if x = 1 then 1 else if x = 2 then 2 else if x = 3 then 1 else 3 : ℕ) : ℚ) +
        c₃ * ((if x = 1 then 2 else if x = 2 then 3 else if x = 3 then 4 else 2 : ℕ) : ℚ) = 0) →
      c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0) := by
  intro M
  have hdet : M.det = 6 := by
    rw [Matrix.det_succ_row_zero]
    simp [M, Fin.sum_univ_four, Fin.succAbove, Matrix.det_fin_three]
    norm_num
  refine ⟨hdet, ?_, ?_⟩
  · rw [hdet]; norm_num
  · intro c₀ c₁ c₂ c₃ h
    have h1 := h 1 (by simp)
    have h2 := h 2 (by simp)
    have h3 := h 3 (by simp)
    have h4 := h 4 (by simp)
    simp at h1 h2 h3 h4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

private lemma zmod2_two_eq_zero : (2 : ZMod 2) = 0 := rfl

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

private lemma zmod2_sq_eq (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

private lemma ps_two_eq_zero : (2 : PowerSeries (ZMod 2)) = 0 := by
  ext n
  have h2 : (2 : PowerSeries (ZMod 2)) = PowerSeries.C (2 : ZMod 2) := rfl
  rw [h2, PowerSeries.coeff_C]
  split_ifs <;> simp [zmod2_two_eq_zero]

private lemma ps_add_sq (u v : PowerSeries (ZMod 2)) : (u + v) ^ 2 = u ^ 2 + v ^ 2 := by
  have h2 : (2 : PowerSeries (ZMod 2)) = 0 := ps_two_eq_zero
  calc
    (u + v) ^ 2 = u ^ 2 + 2 * (u * v) + v ^ 2 := by ring
    _ = u ^ 2 + v ^ 2 := by simp [h2]

private lemma ps_coeff_X_pow_mul (k n : ℕ) (G : PowerSeries (ZMod 2)) :
    PowerSeries.coeff n (PowerSeries.X ^ k * G) =
      if k ≤ n then PowerSeries.coeff (n - k) G else 0 := by
  rw [PowerSeries.coeff_mul]
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    rw [Finset.sum_eq_single (k, n - k)]
    · simp
    · intro p _ hne
      have hp : p.1 ≠ k := by
        intro h1
        apply hne
        ext
        · exact h1
        · have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp ‹_›
          omega
      simp [PowerSeries.coeff_X_pow, hp]
    · intro hnot
      exfalso
      apply hnot
      exact Finset.mem_antidiagonal.mpr (by omega)
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro p hp
    have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    have hne : p.1 ≠ k := by omega
    simp [PowerSeries.coeff_X_pow, hne]

private lemma ps_coeff_sq (G : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (G ^ 2) =
      if n % 2 = 0 then PowerSeries.coeff (n / 2) G else 0 := by
  rw [sq, PowerSeries.coeff_mul]
  let c : ℕ → ZMod 2 := fun k => PowerSeries.coeff k G
  let S := Finset.antidiagonal n
  have hsplit :
      (∑ p ∈ S, c p.1 * c p.2) =
        (∑ p ∈ S.filter (fun p => p.1 = p.2), c p.1 * c p.2) +
        (∑ p ∈ S.filter (fun p => p.1 ≠ p.2), c p.1 * c p.2) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p.1 = p.2)]
  have hne_split :
      (∑ p ∈ S.filter (fun p => p.1 ≠ p.2), c p.1 * c p.2) =
        (∑ p ∈ S.filter (fun p => p.1 < p.2), c p.1 * c p.2) +
        (∑ p ∈ S.filter (fun p => p.2 < p.1), c p.1 * c p.2) := by
    have hunion :
        S.filter (fun p => p.1 ≠ p.2) =
          S.filter (fun p => p.1 < p.2) ∪ S.filter (fun p => p.2 < p.1) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_union]
      by_cases hp : p ∈ S <;> simp [hp]
    have hdisj :
        Disjoint (S.filter (fun p => p.1 < p.2)) (S.filter (fun p => p.2 < p.1)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter] at hp1 hp2
      omega
    rw [hunion, Finset.sum_union hdisj]
  have hswap :
      (∑ p ∈ S.filter (fun p => p.2 < p.1), c p.1 * c p.2) =
        ∑ p ∈ S.filter (fun p => p.1 < p.2), c p.1 * c p.2 := by
    apply Finset.sum_bij (fun p _ => (p.2, p.1))
    · intro p hp
      simp only [S, Finset.mem_filter, Finset.mem_antidiagonal] at hp ⊢
      omega
    · intro p1 _ p2 _ h
      ext <;> simp_all
    · intro q hq
      refine ⟨(q.2, q.1), ?_, ?_⟩
      · simp only [S, Finset.mem_filter, Finset.mem_antidiagonal] at hq ⊢
        omega
      · ext <;> rfl
    · intro p _
      exact mul_comm (c p.1) (c p.2)
  have hcancel : (∑ p ∈ S.filter (fun p => p.1 ≠ p.2), c p.1 * c p.2) = 0 := by
    rw [hne_split, hswap, zmod2_add_self]
  change (∑ p ∈ S, c p.1 * c p.2) = _
  rw [hsplit, hcancel, add_zero]
  by_cases heven : n % 2 = 0
  · rw [if_pos heven]
    have hfilt : S.filter (fun p => p.1 = p.2) = {(n / 2, n / 2)} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton, Prod.ext_iff, S]
      omega
    rw [hfilt, Finset.sum_singleton]
    exact zmod2_sq_eq (c (n / 2))
  · rw [if_neg heven]
    have hfilt : S.filter (fun p => p.1 = p.2) = ∅ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.notMem_empty, iff_false, S]
      omega
    rw [hfilt, Finset.sum_empty]

private lemma zmod2_val_eq_add_eq3
    (a : ℕ → ℕ)
    (ha0 : a 0 = 1)
    (ha : ∀ i : ℕ, a (2 * i) = mu0 (a i) ∧ a (2 * i + 1) = mu1 (a i)) :
    (∀ k : ℕ, ((a (2 * k) : ZMod 2) + (a k : ZMod 2)) =
      if a (2 * k) = 3 then (1 : ZMod 2) else 0) ∧
    (∀ k : ℕ, (a (2 * k + 1) : ZMod 2) =
      if a (2 * k + 1) = 3 then (1 : ZMod 2) else 0) := by
  have hmem := seq_alphabet a ha0 ha
  refine ⟨?_, ?_⟩
  · intro k
    rw [(ha k).1]
    rcases hmem k with h | h | h | h <;> simp [mu0, h] <;> decide
  · intro k
    rw [(ha k).2]
    rcases hmem k with h | h | h | h <;> simp [mu1, h] <;> decide

theorem ppl036_char2_frobenius_deg8
    (a : ℕ → ℕ)
    (ha0 : a 0 = 1)
    (ha : ∀ i : ℕ,
      a (2 * i) = (if a i = 1 then 1 else if a i = 2 then 2 else if a i = 3 then 1 else 3) ∧
      a (2 * i + 1) = (if a i = 1 then 2 else if a i = 2 then 3 else if a i = 3 then 4 else 2)) :
    let F : PowerSeries (ZMod 2) := PowerSeries.mk fun i => (a i : ZMod 2)
    PowerSeries.X + (1 + PowerSeries.X) ^ 2 * F + (1 + PowerSeries.X) ^ 3 * F ^ 2 +
      PowerSeries.X ^ 2 * (1 + PowerSeries.X) ^ 3 * (F ^ 4 + F ^ 8) = 0 := by
  intro F
  let I3 : PowerSeries (ZMod 2) := PowerSeries.mk fun i => if a i = 3 then (1 : ZMod 2) else 0
  have ha' : ∀ i : ℕ, a (2 * i) = mu0 (a i) ∧ a (2 * i + 1) = mu1 (a i) := ha
  have hmem := seq_alphabet a ha0 ha'
  have hpair := zmod2_val_eq_add_eq3 a ha0 ha'
  have hI3_eq : F + F ^ 2 = I3 := by
    ext n
    rw [map_add, ps_coeff_sq]
    simp only [F, I3, PowerSeries.coeff_mk]
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hk' : n = 2 * k := by omega
      have hmod : n % 2 = 0 := by omega
      have hdiv : n / 2 = k := by omega
      rw [if_pos hmod, hdiv, hk']
      exact hpair.1 k
    · have hk' : n = 2 * k + 1 := by omega
      have hmod : n % 2 ≠ 0 := by omega
      rw [if_neg hmod, add_zero, hk']
      exact hpair.2 k
  have hF48 : F ^ 4 + F ^ 8 = I3 ^ 4 := by
    rw [← hI3_eq]
    have hp2 : (F + F ^ 2) ^ 2 = F ^ 2 + F ^ 4 := by
      rw [ps_add_sq]
      ring
    have hp4 : (F + F ^ 2) ^ 4 = ((F + F ^ 2) ^ 2) ^ 2 := by ring
    rw [hp4, hp2, ps_add_sq]
    ring
  rw [hF48]
  have h1X2 : ((1 : PowerSeries (ZMod 2)) + PowerSeries.X) ^ 2 = 1 + PowerSeries.X ^ 2 := by
    rw [ps_add_sq, one_pow]
  have h1X3 : ((1 : PowerSeries (ZMod 2)) + PowerSeries.X) ^ 3 =
      1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 := by
    have h2 : (2 : PowerSeries (ZMod 2)) = 0 := ps_two_eq_zero
    calc
      ((1 : PowerSeries (ZMod 2)) + PowerSeries.X) ^ 3 =
          1 + (1 + 2) * PowerSeries.X + (1 + 2) * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 := by
        ring
      _ = 1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 := by
        simp [h2]
  have hX2_1X3 : (PowerSeries.X : PowerSeries (ZMod 2)) ^ 2 * (1 + PowerSeries.X) ^ 3 =
      PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + PowerSeries.X ^ 4 + PowerSeries.X ^ 5 := by
    rw [h1X3]
    ring
  rw [h1X2, hX2_1X3, h1X3]
  have hI3_4 : ∀ m : ℕ, PowerSeries.coeff m (I3 ^ 4) =
      if m % 4 = 0 then (if a (m / 4) = 3 then (1 : ZMod 2) else 0) else 0 := by
    intro m
    have hp4 : I3 ^ 4 = (I3 ^ 2) ^ 2 := by ring
    rw [hp4, ps_coeff_sq]
    by_cases hm2 : m % 2 = 0
    · rw [if_pos hm2, ps_coeff_sq]
      by_cases hm4 : m % 4 = 0
      · have hhalf : (m / 2) % 2 = 0 := by omega
        have hdiv : (m / 2) / 2 = m / 4 := by omega
        rw [if_pos hm4, if_pos hhalf, hdiv]
        simp [I3]
      · have hhalf : (m / 2) % 2 ≠ 0 := by omega
        rw [if_neg hm4, if_neg hhalf]
    · have hm4 : m % 4 ≠ 0 := by omega
      rw [if_neg hm2, if_neg hm4]
  let f : ℕ → ZMod 2 := fun k => (a k : ZMod 2)
  let g : ℕ → ZMod 2 := fun k => if a k = 3 then 1 else 0
  have h4m_0 : ∀ k : ℕ, a (2 * k) ≠ 4 := by
    intro k
    rw [(ha' k).1]
    rcases hmem k with h | h | h | h <;> simp [mu0, h]
  have hf_even : ∀ k : ℕ, f (2 * k) = f k + g (2 * k) := by
    intro k
    have hp := hpair.1 k
    have hadd : f (2 * k) + f k + f k = g (2 * k) + f k := by
      change (a (2 * k) : ZMod 2) + (a k : ZMod 2) + (a k : ZMod 2) = _
      rw [hp]
    have h0 : f k + f k = 0 := zmod2_add_self (f k)
    calc
      f (2 * k) = f (2 * k) + (f k + f k) := by rw [h0, add_zero]
      _ = f (2 * k) + f k + f k := by ring
      _ = g (2 * k) + f k := hadd
      _ = f k + g (2 * k) := add_comm _ _
  have hf_odd : ∀ k : ℕ, f (2 * k + 1) = 1 + f (2 * k) := by
    intro k
    have hp : f (2 * k) + f (2 * k + 1) = 1 := by
      simp only [f]
      rw [(ha' k).1, (ha' k).2]
      rcases hmem k with h | h | h | h <;> simp [mu0, mu1, h] <;> decide
    calc
      f (2 * k + 1) = (f (2 * k) + f (2 * k)) + f (2 * k + 1) := by
        rw [zmod2_add_self (f (2 * k)), zero_add]
      _ = f (2 * k) + (f (2 * k) + f (2 * k + 1)) := by ring
      _ = f (2 * k) + 1 := by rw [hp]
      _ = 1 + f (2 * k) := add_comm _ _
  have hg4_0 : ∀ k : ℕ, g (4 * k) = 0 := by
    intro k
    have h4k : 4 * k = 2 * (2 * k) := by omega
    simp only [g]
    rw [h4k, (ha' (2 * k)).1]
    have h2k_ne4 := h4m_0 k
    rcases hmem (2 * k) with h | h | h | h
    · simp [mu0, h]
    · simp [mu0, h]
    · simp [mu0, h]
    · exact absurd h h2k_ne4
  have hg4_2 : ∀ k : ℕ, g (4 * k + 2) = g k := by
    intro k
    have h4k2 : 4 * k + 2 = 2 * (2 * k + 1) := by omega
    simp only [g]
    rw [h4k2, (ha' (2 * k + 1)).1, (ha' k).2]
    rcases hmem k with h | h | h | h <;> simp [mu0, mu1, h]
  have ha1 : a 1 = 2 := by
    have h1 : (1 : ℕ) = 2 * 0 + 1 := rfl
    rw [h1, (ha' 0).2, ha0]
    rfl
  have ha2 : a 2 = 2 := by
    have h2 : (2 : ℕ) = 2 * 1 := rfl
    rw [h2, (ha' 1).1, ha1]
    rfl
  have ha3 : a 3 = 3 := by
    have h3 : (3 : ℕ) = 2 * 1 + 1 := rfl
    rw [h3, (ha' 1).2, ha1]
    rfl
  have hf0 : f 0 = 1 := by simp [f, ha0]
  have hf1 : f 1 = 0 := by simp [f, ha1]; decide
  have hf2 : f 2 = 0 := by simp [f, ha2]; decide
  have hf3 : f 3 = 1 := by simp [f, ha3]; decide
  have h4 : a 4 = 2 := by
    have h4' : (4 : ℕ) = 2 * 2 := rfl
    rw [h4', (ha' 2).1, ha2]; rfl
  have hf4 : f 4 = 0 := by simp [f, h4]; decide
  have hX_mul : ∀ (m : ℕ) (G : PowerSeries (ZMod 2)),
      PowerSeries.coeff m (PowerSeries.X * G) =
        if 1 ≤ m then PowerSeries.coeff (m - 1) G else 0 := by
    intro m G
    rw [← pow_one (PowerSeries.X : PowerSeries (ZMod 2))]
    exact ps_coeff_X_pow_mul 1 m G
  have hF_eval : ∀ k : ℕ, PowerSeries.coeff k F = f k := by
    intro k
    simp [F, f]
  ext n
  have hexp :
      PowerSeries.X + (1 + PowerSeries.X ^ 2) * F +
        (1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3) * F ^ 2 +
        (PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + PowerSeries.X ^ 4 + PowerSeries.X ^ 5) * I3 ^ 4 =
      PowerSeries.X + F + PowerSeries.X ^ 2 * F +
        (F ^ 2 + PowerSeries.X * F ^ 2 + PowerSeries.X ^ 2 * F ^ 2 + PowerSeries.X ^ 3 * F ^ 2) +
        (PowerSeries.X ^ 2 * I3 ^ 4 + PowerSeries.X ^ 3 * I3 ^ 4 +
          PowerSeries.X ^ 4 * I3 ^ 4 + PowerSeries.X ^ 5 * I3 ^ 4) := by
    ring
  rw [hexp]
  simp only [map_add, map_zero, PowerSeries.coeff_X, ps_coeff_X_pow_mul, hX_mul,
    ps_coeff_sq, hI3_4]
  simp only [hF_eval]
  rcases Nat.lt_trichotomy n 4 with hlt | heq | hgt
  · interval_cases n
    · simp [hf0, zmod2_add_self]
    · simp [hf0, hf1]; exact zmod2_add_self 1
    · simp [hf0, hf1, hf2, ha0, zmod2_add_self]
    · simp [hf0, hf1, hf3, ha0, zmod2_add_self]
  · subst heq
    simp [hf1, hf2, hf4, ha0]
  · have hm : ∃ m r : ℕ, n = 4 * (m + 1) + r ∧ r < 4 := by
      refine ⟨n / 4 - 1, n % 4, ?_, Nat.mod_lt n (by decide)⟩
      omega
    rcases hm with ⟨m, r, hn, hr⟩
    subst hn
    interval_cases r
    · simp only [add_zero]
      have hc1 : ¬ (4 * (m + 1) = 1) := by omega
      have h2le : 2 ≤ 4 * (m + 1) := by omega
      have h3le : 3 ≤ 4 * (m + 1) := by omega
      have h4le : 4 ≤ 4 * (m + 1) := by omega
      have h5le : 5 ≤ 4 * (m + 1) := by omega
      have h1le : 1 ≤ 4 * (m + 1) := by omega
      simp only [hc1, ↓reduceIte, h2le, h3le, h4le, h5le, h1le]
      have hm_ev : (4 * (m + 1)) % 2 = 0 := by omega
      have hm1_odd : (4 * (m + 1) - 1) % 2 ≠ 0 := by omega
      have hm2_ev : (4 * (m + 1) - 2) % 2 = 0 := by omega
      have hm3_odd : (4 * (m + 1) - 3) % 2 ≠ 0 := by omega
      have hm2_4 : (4 * (m + 1) - 2) % 4 ≠ 0 := by omega
      have hm3_4 : (4 * (m + 1) - 3) % 4 ≠ 0 := by omega
      have hm4_4 : (4 * (m + 1) - 4) % 4 = 0 := by omega
      have hm5_4 : (4 * (m + 1) - 5) % 4 ≠ 0 := by omega
      simp only [hm_ev, hm1_odd, hm2_ev, hm3_odd, hm2_4, hm3_4, hm4_4, hm5_4, ↓reduceIte]
      have hd1 : (4 * (m + 1)) / 2 = 2 * (m + 1) := by omega
      have hd2 : (4 * (m + 1) - 2) / 2 = 2 * m + 1 := by omega
      have hd4 : (4 * (m + 1) - 4) / 4 = m := by omega
      have heq42 : 4 * (m + 1) - 2 = 2 * (2 * m + 1) := by omega
      have heq4 : 4 * (m + 1) = 2 * (2 * (m + 1)) := by omega
      rw [hd1, hd2, hd4, heq42, heq4, hf_even (2 * (m + 1)), hf_even (2 * m + 1)]
      have hgz : g (2 * (2 * (m + 1))) = 0 := by
        have h4eq : 2 * (2 * (m + 1)) = 4 * (m + 1) := by omega
        rw [h4eq]; exact hg4_0 (m + 1)
      have hgm : g (2 * (2 * m + 1)) = g m := by
        have h4eq : 2 * (2 * m + 1) = 4 * m + 2 := by omega
        rw [h4eq]; exact hg4_2 m
      rw [hgz, hgm]
      calc
        _ = (f (2 * (m + 1)) + f (2 * (m + 1))) + (f (2 * m + 1) + f (2 * m + 1)) +
              (g m + g m) := by dsimp only [g]; ring
        _ = 0 := by simp [zmod2_add_self]
    · have hc1 : ¬ (4 * (m + 1) + 1 = 1) := by omega
      have h2le : 2 ≤ 4 * (m + 1) + 1 := by omega
      have h3le : 3 ≤ 4 * (m + 1) + 1 := by omega
      have h4le : 4 ≤ 4 * (m + 1) + 1 := by omega
      have h5le : 5 ≤ 4 * (m + 1) + 1 := by omega
      have h1le : 1 ≤ 4 * (m + 1) + 1 := by omega
      simp only [hc1, ↓reduceIte, h2le, h3le, h4le, h5le, h1le]
      have hm_odd : (4 * (m + 1) + 1) % 2 ≠ 0 := by omega
      have hm1_ev : (4 * (m + 1) + 1 - 1) % 2 = 0 := by omega
      have hm2_odd : (4 * (m + 1) + 1 - 2) % 2 ≠ 0 := by omega
      have hm3_ev : (4 * (m + 1) + 1 - 3) % 2 = 0 := by omega
      have hm2_4 : (4 * (m + 1) + 1 - 2) % 4 ≠ 0 := by omega
      have hm3_4 : (4 * (m + 1) + 1 - 3) % 4 ≠ 0 := by omega
      have hm4_4 : (4 * (m + 1) + 1 - 4) % 4 ≠ 0 := by omega
      have hm5_4 : (4 * (m + 1) + 1 - 5) % 4 = 0 := by omega
      simp only [hm_odd, hm1_ev, hm2_odd, hm3_ev, hm2_4, hm3_4, hm4_4, hm5_4, ↓reduceIte]
      have hd1 : (4 * (m + 1) + 1 - 1) / 2 = 2 * (m + 1) := by omega
      have hd3 : (4 * (m + 1) + 1 - 3) / 2 = 2 * m + 1 := by omega
      have hd5 : (4 * (m + 1) + 1 - 5) / 4 = m := by omega
      have heq3 : 4 * (m + 1) + 1 - 2 = 2 * (2 * m + 1) + 1 := by omega
      have heq5 : 4 * (m + 1) + 1 = 2 * (2 * (m + 1)) + 1 := by omega
      rw [hd1, hd3, hd5, heq3, heq5, hf_odd (2 * (m + 1)), hf_odd (2 * m + 1),
        hf_even (2 * (m + 1)), hf_even (2 * m + 1)]
      have hgz : g (2 * (2 * (m + 1))) = 0 := by
        have h4eq : 2 * (2 * (m + 1)) = 4 * (m + 1) := by omega
        rw [h4eq]; exact hg4_0 (m + 1)
      have hgm : g (2 * (2 * m + 1)) = g m := by
        have h4eq : 2 * (2 * m + 1) = 4 * m + 2 := by omega
        rw [h4eq]; exact hg4_2 m
      rw [hgz, hgm]
      calc
        _ = ((1 : ZMod 2) + 1) + (f (2 * (m + 1)) + f (2 * (m + 1))) +
              (f (2 * m + 1) + f (2 * m + 1)) + (g m + g m) := by dsimp only [g]; ring
        _ = 0 := by simp [zmod2_add_self]
    · have hc1 : ¬ (4 * (m + 1) + 2 = 1) := by omega
      have h2le : 2 ≤ 4 * (m + 1) + 2 := by omega
      have h3le : 3 ≤ 4 * (m + 1) + 2 := by omega
      have h4le : 4 ≤ 4 * (m + 1) + 2 := by omega
      have h5le : 5 ≤ 4 * (m + 1) + 2 := by omega
      have h1le : 1 ≤ 4 * (m + 1) + 2 := by omega
      simp only [hc1, ↓reduceIte, h2le, h3le, h4le, h5le, h1le]
      have hm_ev : (4 * (m + 1) + 2) % 2 = 0 := by omega
      have hm1_odd : (4 * (m + 1) + 2 - 1) % 2 ≠ 0 := by omega
      have hm2_ev : (4 * (m + 1) + 2 - 2) % 2 = 0 := by omega
      have hm3_odd : (4 * (m + 1) + 2 - 3) % 2 ≠ 0 := by omega
      have hm2_4 : (4 * (m + 1) + 2 - 2) % 4 = 0 := by omega
      have hm3_4 : (4 * (m + 1) + 2 - 3) % 4 ≠ 0 := by omega
      have hm4_4 : (4 * (m + 1) + 2 - 4) % 4 ≠ 0 := by omega
      have hm5_4 : (4 * (m + 1) + 2 - 5) % 4 ≠ 0 := by omega
      simp only [hm_ev, hm1_odd, hm2_ev, hm3_odd, hm2_4, hm3_4, hm4_4, hm5_4, ↓reduceIte]
      have hd0 : (4 * (m + 1) + 2) / 2 = 2 * (m + 1) + 1 := by omega
      have hd2 : (4 * (m + 1) + 2 - 2) / 2 = 2 * (m + 1) := by omega
      have hd2_4 : (4 * (m + 1) + 2 - 2) / 4 = m + 1 := by omega
      have heq4 : 4 * (m + 1) + 2 - 2 = 2 * (2 * (m + 1)) := by omega
      have heq6 : 4 * (m + 1) + 2 = 2 * (2 * (m + 1) + 1) := by omega
      rw [hd0, hd2, hd2_4, heq4, heq6, hf_even (2 * (m + 1) + 1), hf_even (2 * (m + 1))]
      have hgz : g (2 * (2 * (m + 1))) = 0 := by
        have h4eq : 2 * (2 * (m + 1)) = 4 * (m + 1) := by omega
        rw [h4eq]; exact hg4_0 (m + 1)
      have hgm : g (2 * (2 * (m + 1) + 1)) = g (m + 1) := by
        have h4eq : 2 * (2 * (m + 1) + 1) = 4 * (m + 1) + 2 := by omega
        rw [h4eq]; exact hg4_2 (m + 1)
      rw [hgz, hgm]
      calc
        _ = (f (2 * (m + 1) + 1) + f (2 * (m + 1) + 1)) + (f (2 * (m + 1)) + f (2 * (m + 1))) +
              (g (m + 1) + g (m + 1)) := by dsimp only [g]; ring
        _ = 0 := by simp [zmod2_add_self]
    · have hc1 : ¬ (4 * (m + 1) + 3 = 1) := by omega
      have h2le : 2 ≤ 4 * (m + 1) + 3 := by omega
      have h3le : 3 ≤ 4 * (m + 1) + 3 := by omega
      have h4le : 4 ≤ 4 * (m + 1) + 3 := by omega
      have h5le : 5 ≤ 4 * (m + 1) + 3 := by omega
      have h1le : 1 ≤ 4 * (m + 1) + 3 := by omega
      simp only [hc1, ↓reduceIte, h2le, h3le, h4le, h5le, h1le]
      have hm_odd : (4 * (m + 1) + 3) % 2 ≠ 0 := by omega
      have hm1_ev : (4 * (m + 1) + 3 - 1) % 2 = 0 := by omega
      have hm2_odd : (4 * (m + 1) + 3 - 2) % 2 ≠ 0 := by omega
      have hm3_ev : (4 * (m + 1) + 3 - 3) % 2 = 0 := by omega
      have hm2_4 : (4 * (m + 1) + 3 - 2) % 4 ≠ 0 := by omega
      have hm3_4 : (4 * (m + 1) + 3 - 3) % 4 = 0 := by omega
      have hm4_4 : (4 * (m + 1) + 3 - 4) % 4 ≠ 0 := by omega
      have hm5_4 : (4 * (m + 1) + 3 - 5) % 4 ≠ 0 := by omega
      simp only [hm_odd, hm1_ev, hm2_odd, hm3_ev, hm2_4, hm3_4, hm4_4, hm5_4, ↓reduceIte]
      have hd1 : (4 * (m + 1) + 3 - 1) / 2 = 2 * (m + 1) + 1 := by omega
      have hd3 : (4 * (m + 1) + 3 - 3) / 2 = 2 * (m + 1) := by omega
      have hd3_4 : (4 * (m + 1) + 3 - 3) / 4 = m + 1 := by omega
      have heq5 : 4 * (m + 1) + 3 - 2 = 2 * (2 * (m + 1)) + 1 := by omega
      have heq7 : 4 * (m + 1) + 3 = 2 * (2 * (m + 1) + 1) + 1 := by omega
      rw [hd1, hd3, hd3_4, heq5, heq7, hf_odd (2 * (m + 1) + 1), hf_odd (2 * (m + 1)),
        hf_even (2 * (m + 1) + 1), hf_even (2 * (m + 1))]
      have hgz : g (2 * (2 * (m + 1))) = 0 := by
        have h4eq : 2 * (2 * (m + 1)) = 4 * (m + 1) := by omega
        rw [h4eq]; exact hg4_0 (m + 1)
      have hgm : g (2 * (2 * (m + 1) + 1)) = g (m + 1) := by
        have h4eq : 2 * (2 * (m + 1) + 1) = 4 * (m + 1) + 2 := by omega
        rw [h4eq]; exact hg4_2 (m + 1)
      rw [hgz, hgm]
      calc
        _ = ((1 : ZMod 2) + 1) + (f (2 * (m + 1) + 1) + f (2 * (m + 1) + 1)) +
              (f (2 * (m + 1)) + f (2 * (m + 1))) + (g (m + 1) + g (m + 1)) := by
          dsimp only [g]; ring
        _ = 0 := by simp [zmod2_add_self]

private def factor3Prop (t : ℕ × ℕ × ℕ) : Prop :=
  t = (1, 2, 2) ∨ t = (1, 2, 3) ∨ t = (1, 4, 1) ∨ t = (1, 4, 2) ∨ t = (2, 1, 2) ∨
  t = (2, 2, 3) ∨ t = (2, 3, 1) ∨ t = (2, 3, 2) ∨ t = (3, 1, 2) ∨ t = (3, 1, 4) ∨
  t = (3, 2, 1) ∨ t = (3, 2, 2) ∨ t = (3, 2, 3) ∨ t = (4, 1, 2) ∨ t = (4, 2, 3)

private lemma seq_factor3
    (a : ℕ → ℕ)
    (ha0 : a 0 = 1)
    (ha : ∀ i : ℕ, a (2 * i) = mu0 (a i) ∧ a (2 * i + 1) = mu1 (a i))
    (k : ℕ) :
    factor3Prop (a k, a (k + 1), a (k + 2)) := by
  have hf2 := seq_factor2 a ha0 ha
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hj0 : k = 2 * j := by omega
    have hj1 : k + 1 = 2 * j + 1 := by omega
    have hj2 : k + 2 = 2 * (j + 1) := by omega
    have ha0' : a k = mu0 (a j) := by rw [hj0, (ha j).1]
    have ha1' : a (k + 1) = mu1 (a j) := by rw [hj1, (ha j).2]
    have ha2' : a (k + 2) = mu0 (a (j + 1)) := by rw [hj2, (ha (j + 1)).1]
    rw [ha0', ha1', ha2']
    rcases hf2 j with h | h | h | h | h | h | h | h | h <;>
      · simp only [Prod.mk.injEq] at h
        simp [factor3Prop, mu0, mu1, h.1, h.2]
  · have hj0 : k = 2 * j + 1 := by omega
    have hj1 : k + 1 = 2 * (j + 1) := by omega
    have hj2 : k + 2 = 2 * (j + 1) + 1 := by omega
    have ha0' : a k = mu1 (a j) := by rw [hj0, (ha j).2]
    have ha1' : a (k + 1) = mu0 (a (j + 1)) := by rw [hj1, (ha (j + 1)).1]
    have ha2' : a (k + 2) = mu1 (a (j + 1)) := by rw [hj2, (ha (j + 1)).2]
    rw [ha0', ha1', ha2']
    rcases hf2 j with h | h | h | h | h | h | h | h | h <;>
      · simp only [Prod.mk.injEq] at h
        simp [factor3Prop, mu0, mu1, h.1, h.2]

theorem ppl036_hankel_1_2_3_nonvanishing
    (a : ℕ → ℕ)
    (ha0 : a 0 = 1)
    (ha : ∀ i : ℕ,
      a (2 * i) = (if a i = 1 then 1 else if a i = 2 then 2 else if a i = 3 then 1 else 3) ∧
      a (2 * i + 1) = (if a i = 1 then 2 else if a i = 2 then 3 else if a i = 3 then 4 else 2)) :
    ∀ k : ℕ,
      (Matrix.of (fun i j : Fin 1 => (a (k + i.1 + j.1) : ℤ))).det ≠ 0 ∧
      (Matrix.of (fun i j : Fin 2 => (a (k + i.1 + j.1) : ℤ))).det ≠ 0 ∧
      (Matrix.of (fun i j : Fin 3 => (a (k + i.1 + j.1) : ℤ))).det ≠ 0 := by
  have ha' : ∀ i : ℕ, a (2 * i) = mu0 (a i) ∧ a (2 * i + 1) = mu1 (a i) := ha
  have hmem := seq_alphabet a ha0 ha'
  have hf3 := seq_factor3 a ha0 ha'
  intro k
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_unique]
    simp only [Matrix.of_apply, Fin.default_eq_zero, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero]
    rcases hmem k with h | h | h | h <;> simp [h]
  · rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Fin.val_zero, Fin.val_one, add_zero]
    rcases hf3 k with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      · simp only [Prod.mk.injEq] at h
        rw [h.1, h.2.1, h.2.2]
        norm_num
  · rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Fin.val_zero, Fin.val_one, Fin.val_two, add_zero]
    have hidx2 : k + 0 + 2 = k + 2 := by omega
    have hidx12 : k + 1 + 2 = k + 3 := by omega
    have hidx22 : k + 2 + 2 = k + 4 := by omega
    simp only [hidx2, hidx12, hidx22]
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hk0 : a k = mu0 (a j) := by
        have : k = 2 * j := by omega
        rw [this, (ha' j).1]
      have hk1 : a (k + 1) = mu1 (a j) := by
        have : k + 1 = 2 * j + 1 := by omega
        rw [this, (ha' j).2]
      have hk2 : a (k + 2) = mu0 (a (j + 1)) := by
        have : k + 2 = 2 * (j + 1) := by omega
        rw [this, (ha' (j + 1)).1]
      have hk3 : a (k + 3) = mu1 (a (j + 1)) := by
        have : k + 3 = 2 * (j + 1) + 1 := by omega
        rw [this, (ha' (j + 1)).2]
      have hk4 : a (k + 4) = mu0 (a (j + 2)) := by
        have : k + 4 = 2 * (j + 2) := by omega
        rw [this, (ha' (j + 2)).1]
      rw [hk0, hk1, hk2, hk3, hk4]
      rcases hf3 j with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        · simp only [Prod.mk.injEq] at h
          simp [mu0, mu1, h.1, h.2.1, h.2.2]
    · have hk0 : a k = mu1 (a j) := by
        have : k = 2 * j + 1 := by omega
        rw [this, (ha' j).2]
      have hk1 : a (k + 1) = mu0 (a (j + 1)) := by
        have : k + 1 = 2 * (j + 1) := by omega
        rw [this, (ha' (j + 1)).1]
      have hk2 : a (k + 2) = mu1 (a (j + 1)) := by
        have : k + 2 = 2 * (j + 1) + 1 := by omega
        rw [this, (ha' (j + 1)).2]
      have hk3 : a (k + 3) = mu0 (a (j + 2)) := by
        have : k + 3 = 2 * (j + 2) := by omega
        rw [this, (ha' (j + 2)).1]
      have hk4 : a (k + 4) = mu1 (a (j + 2)) := by
        have : k + 4 = 2 * (j + 2) + 1 := by omega
        rw [this, (ha' (j + 2)).2]
      rw [hk0, hk1, hk2, hk3, hk4]
      rcases hf3 j with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        · simp only [Prod.mk.injEq] at h
          simp [mu0, mu1, h.1, h.2.1, h.2.2]

theorem ppl036_modular_vanishing_barriers
    (a : ℕ → ℕ)
    (ha0 : a 0 = 1)
    (ha : ∀ i : ℕ,
      a (2 * i) = (if a i = 1 then 1 else if a i = 2 then 2 else if a i = 3 then 1 else 3) ∧
      a (2 * i + 1) = (if a i = 1 then 2 else if a i = 2 then 3 else if a i = 3 then 4 else 2)) :
    ∀ p ∈ ({2, 3, 5} : Finset ℕ),
      ∃ k n : ℕ, 1 ≤ n ∧
        (p : ℤ) ∣ (Matrix.of (fun i j : Fin n => (a (k + i.1 + j.1) : ℤ))).det := by
  have ha' : ∀ i : ℕ, a (2 * i) = mu0 (a i) ∧ a (2 * i + 1) = mu1 (a i) := ha
  have ha1 : a 1 = 2 := by
    have h1 : (1 : ℕ) = 2 * 0 + 1 := rfl
    rw [h1, (ha' 0).2, ha0]; rfl
  have ha2 : a 2 = 2 := by
    have h2 : (2 : ℕ) = 2 * 1 := rfl
    rw [h2, (ha' 1).1, ha1]; rfl
  have ha3 : a 3 = 3 := by
    have h3 : (3 : ℕ) = 2 * 1 + 1 := rfl
    rw [h3, (ha' 1).2, ha1]; rfl
  have ha4 : a 4 = 2 := by
    have h4 : (4 : ℕ) = 2 * 2 := rfl
    rw [h4, (ha' 2).1, ha2]; rfl
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · refine ⟨1, 1, le_rfl, ?_⟩
    rw [Matrix.det_unique]
    simp [ha1]
  · refine ⟨3, 1, le_rfl, ?_⟩
    rw [Matrix.det_unique]
    simp [ha3]
  · refine ⟨2, 2, by decide, ?_⟩
    rw [Matrix.det_fin_two]
    simp [ha2, ha3, ha4]

