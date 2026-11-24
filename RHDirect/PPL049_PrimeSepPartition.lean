import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# PPL 049 (Kimberling #12): Unconditional Bertrand Partition Theorem & Structural Barriers

## Honest Scope Notice
This module formalizes **original unconditional structural and barrier theorems** toward
**PPL 049 (Clark Kimberling #12, $25 → OEIS donation, OEIS A129258 / A129259)**:
*"In Kimberling's prime-separator array, prove or disprove that the successive differences in
the first row are bounded."*

**This is NOT a solution to the open boundedness prize problem.** Proving whether
`T(1, n+1) - T(1, n)` is unbounded remains open and encounters the Chowla/Liouville
consecutive-runs barrier (illustrated formally by our `ZMod 3` multiplicative partition model).

## Verbatim Definition (Kimberling #12 / PPL 049)
Decree `T(1, 1) = 1`. For `n ≥ 1`, let `S(n) = { T(i, j) | 1 ≤ i ≤ n, 1 ≤ j ≤ n }`:
- `T(1, n + 1)` is the least positive integer not in `S(n)`;
- `T(n + 1, 1)` is the least positive integer not in `S(n) ∪ {T(1, n + 1)}`;
- `T(m, n + 1) = T(m, 1) * T(1, n + 1)` and `T(n + 1, m) = T(n + 1, 1) * T(1, m)`
  for all `1 ≤ m ≤ n + 1`.

## Main Exported Results (Zero `sorry`, Zero Custom Axioms, Pure Mathlib)
1. **Existence & Uniqueness (`kimberlingPrimeSep_exists_unique`):**
   There exists a unique array `T` on `ℤ_{≥ 1} × ℤ_{≥ 1}` satisfying the verbatim Kimberling #12
   specification `IsKimberlingPrimeSepArray T`, and `T i j = T i 1 * T 1 j` for all `i, j ≥ 1`.
2. **Unconditional Bertrand Partition Theorem (`bertrand_partition_theorem`):**
   For any `T` satisfying `IsKimberlingPrimeSepArray T`, letting
   `R = { T(1, j) | j ≥ 2 }`, `C = { T(i, 1) | i ≥ 2 }`, `C · R = { c * r | c ∈ C, r ∈ R }`:
   - Strict interleaving: `T(1, n) < T(n, 1) < T(1, n + 1)` for all `n ≥ 2`.
   - Unconditional Bertrand step bounds (via Mathlib's `Nat.exists_prime_lt_and_le_two_mul`):
     `T(n, 1) < 2 * T(1, n)` and `T(1, n + 1) < 2 * T(n, 1)` (hence `T(1, n + 1) < 4 * T(1, n)`).
   - Exact three-way disjoint partition: `ℤ_{≥ 2} = R ⊔ C ⊔ (C · R)`.
   - Prime separation: every prime `p` lies in `R ⊔ C`.
3. **Unique Alternating Partition / Online Greedy Sieve Equivalence
   (`kimberling_iff_alternating_partition`):**
   `(R, C)` is the *unique* pair of subsets of `ℤ_{≥ 2}` forming a three-way disjoint partition
   `ℤ_{≥ 2} = R ⊔ C ⊔ (C · R)` with alternating balance `|R ∩ [2, m]| - |C ∩ [2, m]| ∈ {0, 1}`.
4. **Prime-Separation Gap & Counting Corollaries
   (`at_most_one_prime_between_row1`, `row1_count_ge_half_prime_count`):**
   No open interval `(T(1, n), T(1, n + 1))` contains two primes, and for all `X`,
   `π(X) ≤ 2 * |R ∩ [2, X]|` and `π(X) ≤ 2 * |C ∩ [2, X]| + 1`.
5. **Exact Small-Value Witnesses (`kimberling_small_values`):**
   First 8 entries of row 1 (`1, 2, 4, 7, 9, 13, 15, 18`, matching OEIS A129259) and first 7
   entries of column 1 (`1, 3, 5, 8, 11, 14, 17`).
6. **Barrier Theorem 1 — Multiplicative `ZMod 3` Partition Models
   (`zmod3_multiplicative_partition_model`, `omegaMod3_positive_lower_density`):**
   Every completely additive `φ : ℕ → ZMod 3` nonvanishing on primes induces a three-way
   partition `ℤ_{≥ 2} = R' ⊔ C' ⊔ (C' · R')` containing all primes in `R' ⊔ C'`; for
   `φ(n) = Ω(n) mod 3`, both `R'` and `C'` have positive lower density (`≥ X / 16`).
7. **Barrier Theorem 2 — No Local CRT / Divisibility Forcing
   (`no_local_divisibility_forcing`):**
   For every `d ≥ 1`, prime `p ∤ d`, and multiplicatively consistent 3-coloring on the divisors
   of `d`, there exists a consistent extension to the divisors of `d * p` where `d * p` survives
   outside `C · R`.
-/

namespace PPL049_PrimeSepPartition

open Finset

/-! ## Section 1: Exact Verbatim Specification of Kimberling's Prime-Separator Array -/

/-- Membership in the `n × n` principal block `S(n) = { T(i, j) | 1 ≤ i ≤ n, 1 ≤ j ≤ n }`. -/
def InBlock (T : ℕ → ℕ → ℕ) (n x : ℕ) : Prop :=
  ∃ i j : ℕ, 1 ≤ i ∧ i ≤ n ∧ 1 ≤ j ∧ j ≤ n ∧ T i j = x

/-- Exact verbatim specification of Clark Kimberling's Prime-Separator Array `T(i, j)`
(Kimberling #12, PPL 049, OEIS A129258 / A129259), 1-indexed for `i ≥ 1, j ≥ 1`:
- `T 1 1 = 1`
- For every `n ≥ 1`, letting `S(n) = { T(i, j) | 1 ≤ i ≤ n, 1 ≤ j ≤ n }`:
  * `T 1 (n + 1)` is the least positive integer not in `S(n)`;
  * `T (n + 1) 1` is the least positive integer not in `S(n) ∪ {T 1 (n + 1)}`;
  * `T m (n + 1) = T m 1 * T 1 (n + 1)` and `T (n + 1) m = T (n + 1) 1 * T 1 m`
    for all `1 ≤ m ≤ n + 1`. -/
def IsKimberlingPrimeSepArray (T : ℕ → ℕ → ℕ) : Prop :=
  T 1 1 = 1 ∧
  ∀ n : ℕ, 1 ≤ n →
    -- T(1, n+1) is the least positive integer not in S(n)
    (1 ≤ T 1 (n + 1) ∧ ¬ InBlock T n (T 1 (n + 1)) ∧
      ∀ x : ℕ, 1 ≤ x → ¬ InBlock T n x → T 1 (n + 1) ≤ x) ∧
    -- T(n+1, 1) is the least positive integer not in S(n) ∪ {T(1, n+1)}
    (1 ≤ T (n + 1) 1 ∧ ¬ InBlock T n (T (n + 1) 1) ∧ T (n + 1) 1 ≠ T 1 (n + 1) ∧
      ∀ x : ℕ, 1 ≤ x → ¬ InBlock T n x → x ≠ T 1 (n + 1) → T (n + 1) 1 ≤ x) ∧
    -- Multiplicative border rules for 1 ≤ m ≤ n + 1
    (∀ m : ℕ, 1 ≤ m → m ≤ n + 1 →
      T m (n + 1) = T m 1 * T 1 (n + 1) ∧ T (n + 1) m = T (n + 1) 1 * T 1 m)

/-- Every entry `T(i, j)` (`i, j ≥ 1`) factors as `T(i, 1) * T(1, j)`. -/
theorem kimberling_mul_eq {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) :
    T i j = T i 1 * T 1 j := by
  by_cases hij : i = 1 ∧ j = 1
  · rcases hij with ⟨rfl, rfl⟩
    simp [hT.1]
  · by_cases hle : i ≤ j
    · have hj2 : 2 ≤ j := by omega
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = n + 1 := ⟨j - 1, by omega⟩
      have hn : 1 ≤ n := by omega
      exact ((hT.2 n hn).2.2 i hi hle).1
    · have hi2 : 2 ≤ i := by omega
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = n + 1 := ⟨i - 1, by omega⟩
      have hn : 1 ≤ n := by omega
      exact ((hT.2 n hn).2.2 j hj (by omega)).2

/-- Any two arrays satisfying `IsKimberlingPrimeSepArray` agree on all `i, j ≥ 1`. -/
theorem kimberling_unique {T₁ T₂ : ℕ → ℕ → ℕ}
    (hT₁ : IsKimberlingPrimeSepArray T₁) (hT₂ : IsKimberlingPrimeSepArray T₂) :
    ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → T₁ i j = T₂ i j := by
  suffices hblock : ∀ n : ℕ, 1 ≤ n →
      ∀ i j : ℕ, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → T₁ i j = T₂ i j by
    intro i j hi hj
    exact hblock (max i j) (le_trans hi (le_max_left i j)) i j hi (le_max_left i j) hj
      (le_max_right i j)
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      intro i j hi1 hi2 hj1 hj2
      have hi : i = 1 := by omega
      have hj : j = 1 := by omega
      subst hi; subst hj
      rw [hT₁.1, hT₂.1]
    · have hk1 : 1 ≤ k := by omega
      have hih := ih hk1
      have hinS : ∀ x : ℕ, InBlock T₁ k x ↔ InBlock T₂ k x := by
        intro x
        constructor
        · rintro ⟨i, j, hi1, hik, hj1, hjk, hEq⟩
          exact ⟨i, j, hi1, hik, hj1, hjk, (hih i j hi1 hik hj1 hjk).symm.trans hEq⟩
        · rintro ⟨i, j, hi1, hik, hj1, hjk, hEq⟩
          exact ⟨i, j, hi1, hik, hj1, hjk, (hih i j hi1 hik hj1 hjk).trans hEq⟩
      have hr : T₁ 1 (k + 1) = T₂ 1 (k + 1) := by
        have h1 := (hT₁.2 k hk1).1
        have h2 := (hT₂.2 k hk1).1
        apply le_antisymm
        · exact h1.2.2 (T₂ 1 (k + 1)) h2.1 (fun h => h2.2.1 ((hinS _).mp h))
        · exact h2.2.2 (T₁ 1 (k + 1)) h1.1 (fun h => h1.2.1 ((hinS _).mpr h))
      have hc : T₁ (k + 1) 1 = T₂ (k + 1) 1 := by
        have h1 := (hT₁.2 k hk1).2.1
        have h2 := (hT₂.2 k hk1).2.1
        apply le_antisymm
        · exact h1.2.2.2 (T₂ (k + 1) 1) h2.1 (fun h => h2.2.1 ((hinS _).mp h))
            (by rw [hr]; exact h2.2.2.1)
        · exact h2.2.2.2 (T₁ (k + 1) 1) h1.1 (fun h => h1.2.1 ((hinS _).mpr h))
            (by rw [← hr]; exact h1.2.2.1)
      intro i j hi1 hik hj1 hjk
      rw [kimberling_mul_eq hT₁ hi1 hj1, kimberling_mul_eq hT₂ hi1 hj1]
      have hci : T₁ i 1 = T₂ i 1 := by
        by_cases hi : i ≤ k
        · exact hih i 1 hi1 hi le_rfl hk1
        · have : i = k + 1 := by omega
          subst this; exact hc
      have hrj : T₁ 1 j = T₂ 1 j := by
        by_cases hj : j ≤ k
        · exact hih 1 j le_rfl hk1 hj1 hj
        · have : j = k + 1 := by omega
          subst this; exact hr
      rw [hci, hrj]

/-! ## Section 2: Computable Construction & Existence Proof -/

private lemma sdiff_Icc_nonempty (s : Finset ℕ) :
    ((Finset.Icc 1 (s.card + 1)) \ s).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have hsub : Finset.Icc 1 (s.card + 1) ⊆ s := Finset.sdiff_eq_empty_iff_subset.mp h
  have hcard : (Finset.Icc 1 (s.card + 1)).card ≤ s.card := Finset.card_le_card hsub
  simp only [Nat.card_Icc] at hcard
  omega

/-- Least positive integer (`≥ 1`) not belonging to a finite set `s : Finset ℕ`. -/
def leastPosNotIn (s : Finset ℕ) : ℕ :=
  ((Finset.Icc 1 (s.card + 1)) \ s).min' (sdiff_Icc_nonempty s)

lemma leastPosNotIn_pos (s : Finset ℕ) : 1 ≤ leastPosNotIn s := by
  have hmem := Finset.min'_mem ((Finset.Icc 1 (s.card + 1)) \ s) (sdiff_Icc_nonempty s)
  exact (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hmem).1).1

lemma leastPosNotIn_not_mem (s : Finset ℕ) : leastPosNotIn s ∉ s := by
  have hmem := Finset.min'_mem ((Finset.Icc 1 (s.card + 1)) \ s) (sdiff_Icc_nonempty s)
  exact (Finset.mem_sdiff.mp hmem).2

lemma leastPosNotIn_le (s : Finset ℕ) {m : ℕ} (hm1 : 1 ≤ m) (hms : m ∉ s) :
    leastPosNotIn s ≤ m := by
  by_cases hle : m ≤ s.card + 1
  · exact Finset.min'_le _ m (Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hle⟩, hms⟩)
  · have hmem := Finset.min'_mem ((Finset.Icc 1 (s.card + 1)) \ s) (sdiff_Icc_nonempty s)
    have hbd : leastPosNotIn s ≤ s.card + 1 :=
      (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hmem).1).2
    omega

/-- All pairwise products `c * r` from a prefix list of `(row1, col1)` pairs. -/
def blockProducts (hist : List (ℕ × ℕ)) : Finset ℕ :=
  (hist.flatMap fun ci => hist.map fun rj => ci.2 * rj.1).toFinset

/-- One step of the Kimberling #12 array recursion given the prefix history. -/
def rcStep (hist : List (ℕ × ℕ)) : ℕ × ℕ :=
  let S := blockProducts hist
  let r := leastPosNotIn S
  let c := leastPosNotIn (insert r S)
  (r, c)

/-- Computable prefix list `[(r₀, c₀), ..., (rₙ, cₙ)]` (0-indexed; `r₀ = c₀ = 1`). -/
def rcHist : ℕ → List (ℕ × ℕ)
  | 0 => [(1, 1)]
  | n + 1 => rcHist n ++ [rcStep (rcHist n)]

private lemma rcHist_ne_nil (n : ℕ) : rcHist n ≠ [] := by
  cases n with
  | zero => simp [rcHist]
  | succ k => simp [rcHist]

/-- Canonical 0-indexed first row (`row1 0 = 1, row1 1 = 2, row1 2 = 4, ...`). -/
def row1 (n : ℕ) : ℕ := ((rcHist n).getLast (rcHist_ne_nil n)).1

/-- Canonical 0-indexed first column (`col1 0 = 1, col1 1 = 3, col1 2 = 5, ...`). -/
def col1 (n : ℕ) : ℕ := ((rcHist n).getLast (rcHist_ne_nil n)).2

private lemma row1_zero : row1 0 = 1 := rfl
private lemma col1_zero : col1 0 = 1 := rfl

private lemma row1_succ (n : ℕ) :
    row1 (n + 1) = leastPosNotIn (blockProducts (rcHist n)) := by
  simp [row1, rcHist, rcStep]

private lemma col1_succ (n : ℕ) :
    col1 (n + 1) = leastPosNotIn (insert (row1 (n + 1)) (blockProducts (rcHist n))) := by
  simp [col1, row1, rcHist, rcStep]

private lemma mem_rcHist_iff (n : ℕ) (x : ℕ × ℕ) :
    x ∈ rcHist n ↔ ∃ k : ℕ, k ≤ n ∧ x = (row1 k, col1 k) := by
  induction n with
  | zero =>
    simp only [rcHist, List.mem_singleton, Nat.le_zero, exists_eq_left, row1_zero, col1_zero]
  | succ m ih =>
    rw [rcHist, List.mem_append, List.mem_singleton, ih]
    have hlast : rcStep (rcHist m) = (row1 (m + 1), col1 (m + 1)) := by
      ext <;> simp [row1, col1, rcHist]
    rw [hlast]
    constructor
    · rintro (⟨k, hkm, rfl⟩ | rfl)
      · exact ⟨k, Nat.le_succ_of_le hkm, rfl⟩
      · exact ⟨m + 1, le_rfl, rfl⟩
    · rintro ⟨k, hkm, rfl⟩
      rcases Nat.of_le_succ hkm with hlt | rfl
      · exact Or.inl ⟨k, hlt, rfl⟩
      · exact Or.inr rfl

private lemma mem_blockProducts_rcHist (n x : ℕ) :
    x ∈ blockProducts (rcHist n) ↔
      ∃ i j : ℕ, i ≤ n ∧ j ≤ n ∧ col1 i * row1 j = x := by
  simp only [blockProducts, List.mem_toFinset, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨ci, hci, rj, hrj, rfl⟩
    rcases (mem_rcHist_iff n ci).mp hci with ⟨i, hin, rfl⟩
    rcases (mem_rcHist_iff n rj).mp hrj with ⟨j, hjn, rfl⟩
    exact ⟨i, j, hin, hjn, rfl⟩
  · rintro ⟨i, j, hin, hjn, rfl⟩
    exact ⟨(row1 i, col1 i), (mem_rcHist_iff n _).mpr ⟨i, hin, rfl⟩,
      (row1 j, col1 j), (mem_rcHist_iff n _).mpr ⟨j, hjn, rfl⟩, rfl⟩

/-- Canonical 1-indexed Kimberling Prime-Separator Array `T(i, j) = col1(i - 1) * row1(j - 1)`. -/
def kimberlingT (i j : ℕ) : ℕ := col1 (i - 1) * row1 (j - 1)

private lemma kimberlingT_inBlock_iff {n : ℕ} (hn : 1 ≤ n) (x : ℕ) :
    InBlock kimberlingT n x ↔ x ∈ blockProducts (rcHist (n - 1)) := by
  rw [InBlock, mem_blockProducts_rcHist]
  constructor
  · rintro ⟨i, j, hi1, hin, hj1, hjn, rfl⟩
    exact ⟨i - 1, j - 1, by omega, by omega, rfl⟩
  · rintro ⟨i, j, hin, hjn, hEq⟩
    exact ⟨i + 1, j + 1, by omega, by omega, by omega, by omega, by
      simpa [kimberlingT] using hEq⟩

/-- The canonical construction `kimberlingT` satisfies the verbatim Kimberling #12 axioms. -/
theorem kimberlingT_isKimberlingPrimeSepArray :
    IsKimberlingPrimeSepArray kimberlingT := by
  refine ⟨by simp [kimberlingT, row1_zero, col1_zero], ?_⟩
  intro n hn
  have h1n : kimberlingT 1 (n + 1) = row1 n := by
    simp [kimberlingT, col1_zero]
  have hn1 : kimberlingT (n + 1) 1 = col1 n := by
    simp [kimberlingT, row1_zero]
  have hrow_eq : row1 n = leastPosNotIn (blockProducts (rcHist (n - 1))) := by
    have : n = (n - 1) + 1 := by omega
    conv_lhs => rw [this]
    exact row1_succ (n - 1)
  have hcol_eq : col1 n =
      leastPosNotIn (insert (row1 n) (blockProducts (rcHist (n - 1)))) := by
    have : n = (n - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [col1_succ (n - 1), ← this]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [h1n, hrow_eq]; exact leastPosNotIn_pos _
    · rw [kimberlingT_inBlock_iff hn, h1n, hrow_eq]; exact leastPosNotIn_not_mem _
    · intro x hx1 hxnot
      rw [kimberlingT_inBlock_iff hn] at hxnot
      rw [h1n, hrow_eq]
      exact leastPosNotIn_le _ hx1 hxnot
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hn1, hcol_eq]; exact leastPosNotIn_pos _
    · rw [kimberlingT_inBlock_iff hn, hn1, hcol_eq]
      intro hmem
      exact leastPosNotIn_not_mem _ (Finset.mem_insert_of_mem hmem)
    · rw [hn1, h1n, hcol_eq]
      intro hEq
      have hnot := leastPosNotIn_not_mem (insert (row1 n) (blockProducts (rcHist (n - 1))))
      rw [hEq] at hnot
      exact hnot (Finset.mem_insert_self _ _)
    · intro x hx1 hxnot hxne
      rw [kimberlingT_inBlock_iff hn] at hxnot
      rw [h1n] at hxne
      rw [hn1, hcol_eq]
      exact leastPosNotIn_le _ hx1 (by simp [Finset.mem_insert, hxne, hxnot])
  · intro m hm1 _
    constructor
    · simp [kimberlingT, row1_zero, col1_zero]
    · simp [kimberlingT, row1_zero, col1_zero]

/-- **Existence and Uniqueness** of Kimberling's Prime-Separator Array. -/
theorem kimberlingPrimeSep_exists_unique :
    ∃ T : ℕ → ℕ → ℕ, IsKimberlingPrimeSepArray T ∧
      ∀ T' : ℕ → ℕ → ℕ, IsKimberlingPrimeSepArray T' →
        ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → T' i j = T i j :=
  ⟨kimberlingT, kimberlingT_isKimberlingPrimeSepArray,
    fun _ hT' => kimberling_unique hT' kimberlingT_isKimberlingPrimeSepArray⟩

/-! ## Section 3: Strict Interleaving, Monotonicity & Covering -/

lemma row1_ge_two {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n : ℕ} (hn : 2 ≤ n) : 2 ≤ T 1 n := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have hpos := (hT.2 k hk).1.1
  have hnot := (hT.2 k hk).1.2.1
  have hne1 : T 1 (k + 1) ≠ 1 := by
    intro hEq
    exact hnot ⟨1, 1, le_rfl, hk, le_rfl, hk, by rw [hT.1, hEq]⟩
  omega

lemma col1_ge_two {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n : ℕ} (hn : 2 ≤ n) : 2 ≤ T n 1 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have hpos := (hT.2 k hk).2.1.1
  have hnot := (hT.2 k hk).2.1.2.1
  have hne1 : T (k + 1) 1 ≠ 1 := by
    intro hEq
    exact hnot ⟨1, 1, le_rfl, hk, le_rfl, hk, by rw [hT.1, hEq]⟩
  omega

/-- For every `n ≥ 2`, `T(1, n) < T(n, 1)`. -/
theorem row1_lt_col1 {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n : ℕ} (hn : 2 ≤ n) : T 1 n < T n 1 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have hle : T 1 (k + 1) ≤ T (k + 1) 1 :=
    (hT.2 k hk).1.2.2 (T (k + 1) 1) (hT.2 k hk).2.1.1 (hT.2 k hk).2.1.2.1
  have hne : T (k + 1) 1 ≠ T 1 (k + 1) := (hT.2 k hk).2.1.2.2.1
  omega

/-- Every positive integer `≤ T(n, 1)` already lies in `S(n)`. -/
lemma inBlock_of_le_col1 {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n : ℕ} (hn : 1 ≤ n) {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ T n 1) :
    InBlock T n m := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hgt
  · rw [hT.1] at hmle
    have hm : m = 1 := by omega
    subst hm
    exact ⟨1, 1, le_rfl, le_rfl, le_rfl, le_rfl, hT.1⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
    have hk : 1 ≤ k := by omega
    by_cases hmc : m = T (k + 1) 1
    · exact ⟨k + 1, 1, by omega, le_rfl, le_rfl, by omega, hmc.symm⟩
    · by_cases hmr : m = T 1 (k + 1)
      · exact ⟨1, k + 1, le_rfl, by omega, by omega, le_rfl, hmr.symm⟩
      · by_contra hnot
        have hnotk : ¬ InBlock T k m := fun ⟨i, j, hi1, hik, hj1, hjk, hEq⟩ =>
          hnot ⟨i, j, hi1, by omega, hj1, by omega, hEq⟩
        have hge : T (k + 1) 1 ≤ m := (hT.2 k hk).2.1.2.2.2 m hm1 hnotk hmr
        omega

/-- For every `n ≥ 1`, `T(n, 1) < T(1, n + 1)`. -/
theorem col1_lt_row1_succ {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n : ℕ} (hn : 1 ≤ n) : T n 1 < T 1 (n + 1) := by
  exact Nat.lt_of_not_ge fun hle =>
    (hT.2 n hn).1.2.1 (inBlock_of_le_col1 hT hn (hT.2 n hn).1.1 hle)

lemma row1_le_col1 {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n : ℕ} (hn : 1 ≤ n) : T 1 n ≤ T n 1 := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hgt
  · exact le_rfl
  · exact le_of_lt (row1_lt_col1 hT hgt)

lemma row1_lt_row1_succ {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n : ℕ} (hn : 1 ≤ n) : T 1 n < T 1 (n + 1) :=
  lt_of_le_of_lt (row1_le_col1 hT hn) (col1_lt_row1_succ hT hn)

lemma col1_lt_col1_succ {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n : ℕ} (hn : 1 ≤ n) : T n 1 < T (n + 1) 1 :=
  lt_trans (col1_lt_row1_succ hT hn) (row1_lt_col1 hT (by omega))

/-- Row 1 is strictly increasing on `n ≥ 1`. -/
theorem row1_strictMono_on {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) : T 1 a < T 1 b := by
  induction b with
  | zero => omega
  | succ k ih =>
    by_cases hak : a = k
    · subst hak; exact row1_lt_row1_succ hT ha
    · exact lt_trans (ih (by omega)) (row1_lt_row1_succ hT (by omega))

/-- Column 1 is strictly increasing on `n ≥ 1`. -/
theorem col1_strictMono_on {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) : T a 1 < T b 1 := by
  induction b with
  | zero => omega
  | succ k ih =>
    by_cases hak : a = k
    · subst hak; exact col1_lt_col1_succ hT ha
    · exact lt_trans (ih (by omega)) (col1_lt_col1_succ hT (by omega))

lemma row1_mono_on {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : T 1 a ≤ T 1 b := by
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (row1_strictMono_on hT ha hlt)

lemma col1_mono_on {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : T a 1 ≤ T b 1 := by
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (col1_strictMono_on hT ha hlt)

lemma col1_ge_index {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n : ℕ} (hn : 1 ≤ n) : n ≤ T n 1 := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk; rw [hT.1]
    · have hk1 : 1 ≤ k := by omega
      have h1 := ih hk1
      have h2 := col1_lt_col1_succ hT hk1
      omega

lemma row1_ge_index {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n : ℕ} (hn : 1 ≤ n) : n ≤ T 1 n := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk; rw [hT.1]
    · have hk1 : 1 ≤ k := by omega
      have h1 := ih hk1
      have h2 := row1_lt_row1_succ hT hk1
      omega

/-- The sets `R` and `C` of entries `≥ 2` in row 1 and column 1 are disjoint. -/
theorem disjoint_row1_col1 {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T) :
    Disjoint {x : ℕ | ∃ j : ℕ, 2 ≤ j ∧ T 1 j = x}
             {x : ℕ | ∃ i : ℕ, 2 ≤ i ∧ T i 1 = x} := by
  rw [Set.disjoint_left]
  rintro x ⟨j, hj, rfl⟩ ⟨i, hi, hEq⟩
  by_cases hji : j ≤ i
  · have h1 : T 1 j ≤ T 1 i := row1_mono_on hT (by omega) hji
    have h2 : T 1 i < T i 1 := row1_lt_col1 hT hi
    omega
  · have hij : i + 1 ≤ j := by omega
    have h1 : T i 1 < T 1 (i + 1) := col1_lt_row1_succ hT (by omega)
    have h2 : T 1 (i + 1) ≤ T 1 j := row1_mono_on hT (by omega) hij
    omega

/-- Every integer `m ≥ 2` belongs to `R ∪ C ∪ (C · R)`. -/
theorem cover_ge_two {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {m : ℕ} (hm : 2 ≤ m) :
    (∃ j : ℕ, 2 ≤ j ∧ T 1 j = m) ∨
    (∃ i : ℕ, 2 ≤ i ∧ T i 1 = m) ∨
    (∃ i j : ℕ, 2 ≤ i ∧ 2 ≤ j ∧ T i 1 * T 1 j = m) := by
  have hin : InBlock T m m :=
    inBlock_of_le_col1 hT (by omega) (by omega) (col1_ge_index hT (by omega))
  rcases hin with ⟨i, j, hi1, _, hj1, _, hEq⟩
  rw [kimberling_mul_eq hT hi1 hj1] at hEq
  by_cases hi : i = 1
  · subst hi
    rw [hT.1, one_mul] at hEq
    by_cases hj : j = 1
    · subst hj; rw [hT.1] at hEq; omega
    · exact Or.inl ⟨j, by omega, hEq⟩
  · by_cases hj : j = 1
    · subst hj
      rw [hT.1, mul_one] at hEq
      exact Or.inr (Or.inl ⟨i, by omega, hEq⟩)
    · exact Or.inr (Or.inr ⟨i, j, by omega, by omega, hEq⟩)

/-! ## Section 4: The Unconditional Bertrand Partition Theorem -/

/-- No prime strictly exceeding `T(n, 1)` can lie in the `n × n` block `S(n)`. -/
lemma prime_not_inBlock_of_gt_col1 {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n p : ℕ} (hn : 1 ≤ n) (hp : Nat.Prime p) (hgt : T n 1 < p) :
    ¬ InBlock T n p := by
  rintro ⟨i, j, hi1, hin, hj1, hjn, hEq⟩
  rw [kimberling_mul_eq hT hi1 hj1] at hEq
  by_cases hi : i = 1
  · subst hi
    rw [hT.1, one_mul] at hEq
    have h1 : T 1 j ≤ T 1 n := row1_mono_on hT hj1 hjn
    have h2 : T 1 n ≤ T n 1 := row1_le_col1 hT hn
    omega
  · by_cases hj : j = 1
    · subst hj
      rw [hT.1, mul_one] at hEq
      have h1 : T i 1 ≤ T n 1 := col1_mono_on hT hi1 hin
      omega
    · have hci : 2 ≤ T i 1 := col1_ge_two hT (by omega)
      have hrj : 2 ≤ T 1 j := row1_ge_two hT (by omega)
      have hne1 : T i 1 ≠ 1 := by omega
      have hne2 : T 1 j ≠ 1 := by omega
      rcases hp.eq_one_or_self_of_dvd (T i 1) ⟨T 1 j, hEq.symm⟩ with h1 | hself
      · exact hne1 h1
      · rw [hself] at hEq
        have hpos : 0 < p := hp.pos
        have : p * 1 < p * T 1 j := Nat.mul_lt_mul_of_pos_left (by omega) hpos
        omega

/-- **Bertrand Step Bound I:** For all `n ≥ 2`, `T(n, 1) < 2 * T(1, n)`. -/
theorem col1_lt_two_mul_row1 {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n : ℕ} (hn : 2 ≤ n) : T n 1 < 2 * T 1 n := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have hr2 : 2 ≤ T 1 (k + 1) := row1_ge_two hT hn
  obtain ⟨p, hp, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (T 1 (k + 1)) (by omega)
  have hp_lt : p < 2 * T 1 (k + 1) := by
    by_contra hge
    have hpeq : p = 2 * T 1 (k + 1) := by omega
    have h2dvd : 2 ∣ p := ⟨T 1 (k + 1), hpeq⟩
    rcases hp.eq_one_or_self_of_dvd 2 h2dvd with h1 | h2
    · omega
    · omega
  have hgt_col : T k 1 < p := lt_trans (col1_lt_row1_succ hT hk) hlt
  have hnotS : ¬ InBlock T k p := prime_not_inBlock_of_gt_col1 hT hk hp hgt_col
  have hcol_le : T (k + 1) 1 ≤ p :=
    (hT.2 k hk).2.1.2.2.2 p (by linarith [hp.two_le]) hnotS (by omega)
  exact lt_of_le_of_lt hcol_le hp_lt

/-- **Bertrand Step Bound II:** For all `n ≥ 2`, `T(1, n + 1) < 2 * T(n, 1)`. -/
theorem row1_succ_lt_two_mul_col1 {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n : ℕ} (hn : 2 ≤ n) : T 1 (n + 1) < 2 * T n 1 := by
  have hc2 : 2 ≤ T n 1 := col1_ge_two hT hn
  obtain ⟨p, hp, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (T n 1) (by omega)
  have hp_lt : p < 2 * T n 1 := by
    by_contra hge
    have hpeq : p = 2 * T n 1 := by omega
    have h2dvd : 2 ∣ p := ⟨T n 1, hpeq⟩
    rcases hp.eq_one_or_self_of_dvd 2 h2dvd with h1 | h2
    · omega
    · omega
  have hnotS : ¬ InBlock T n p := prime_not_inBlock_of_gt_col1 hT (by omega) hp hlt
  have hrow_le : T 1 (n + 1) ≤ p :=
    (hT.2 n (by omega)).1.2.2 p (by linarith [hp.two_le]) hnotS
  exact lt_of_le_of_lt hrow_le hp_lt

/-- **Row-1 Ratio Bound:** For all `n ≥ 2`, `T(1, n + 1) < 4 * T(1, n)`. -/
theorem row1_succ_lt_four_mul_row1 {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n : ℕ} (hn : 2 ≤ n) : T 1 (n + 1) < 4 * T 1 n := by
  have h1 := row1_succ_lt_two_mul_col1 hT hn
  have h2 := col1_lt_two_mul_row1 hT hn
  omega

/-- `R` is disjoint from `C · R` (elementary). -/
theorem disjoint_row1_CR {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T) :
    Disjoint {x : ℕ | ∃ j : ℕ, 2 ≤ j ∧ T 1 j = x}
             {x : ℕ | ∃ c ∈ {y : ℕ | ∃ i : ℕ, 2 ≤ i ∧ T i 1 = y},
                      ∃ r ∈ {y : ℕ | ∃ j : ℕ, 2 ≤ j ∧ T 1 j = y}, c * r = x} := by
  rw [Set.disjoint_left]
  rintro x ⟨n, hn, rfl⟩ ⟨c, ⟨i, hi, rfl⟩, r, ⟨j, hj, rfl⟩, hEq⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have hci2 : 2 ≤ T i 1 := col1_ge_two hT hi
  have hrj2 : 2 ≤ T 1 j := row1_ge_two hT hj
  have hci_lt : T i 1 < T 1 (k + 1) := by
    have : T i 1 * 1 < T i 1 * T 1 j := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    omega
  have hrj_lt : T 1 j < T 1 (k + 1) := by
    have : 1 * T 1 j < T i 1 * T 1 j := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    omega
  have hik : i ≤ k := by
    by_contra hgt
    have hge : T (k + 1) 1 ≤ T i 1 := col1_mono_on hT (by omega) (by omega)
    have hlt : T 1 (k + 1) < T (k + 1) 1 := row1_lt_col1 hT hn
    omega
  have hjk : j ≤ k := by
    by_contra hgt
    have hge : T 1 (k + 1) ≤ T 1 j := row1_mono_on hT (by omega) (by omega)
    omega
  have hin : InBlock T k (T 1 (k + 1)) :=
    ⟨i, j, by omega, hik, by omega, hjk, by rw [kimberling_mul_eq hT (by omega) (by omega), hEq]⟩
  exact (hT.2 k hk).1.2.1 hin

/-- `C` is disjoint from `C · R` (proved unconditionally via Bertrand's Postulate). -/
theorem disjoint_col1_CR {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T) :
    Disjoint {x : ℕ | ∃ i : ℕ, 2 ≤ i ∧ T i 1 = x}
             {x : ℕ | ∃ c ∈ {y : ℕ | ∃ i : ℕ, 2 ≤ i ∧ T i 1 = y},
                      ∃ r ∈ {y : ℕ | ∃ j : ℕ, 2 ≤ j ∧ T 1 j = y}, c * r = x} := by
  rw [Set.disjoint_left]
  rintro x ⟨n, hn, rfl⟩ ⟨c, ⟨i, hi, rfl⟩, r, ⟨j, hj, rfl⟩, hEq⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have hci2 : 2 ≤ T i 1 := col1_ge_two hT hi
  have hrj2 : 2 ≤ T 1 j := row1_ge_two hT hj
  have hci_lt : T i 1 < T (k + 1) 1 := by
    have : T i 1 * 1 < T i 1 * T 1 j := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    omega
  have hik : i ≤ k := by
    by_contra hgt
    have hge : T (k + 1) 1 ≤ T i 1 := col1_mono_on hT (by omega) (by omega)
    omega
  by_cases hjk : j ≤ k
  · have hin : InBlock T k (T (k + 1) 1) :=
      ⟨i, j, by omega, hik, by omega, hjk,
        by rw [kimberling_mul_eq hT (by omega) (by omega), hEq]⟩
    exact (hT.2 k hk).2.1.2.1 hin
  · have hrj_ge : T 1 (k + 1) ≤ T 1 j := row1_mono_on hT (by omega) (by omega)
    have hprod_ge : 2 * T 1 (k + 1) ≤ T i 1 * T 1 j :=
      Nat.mul_le_mul hci2 hrj_ge
    have hbert : T (k + 1) 1 < 2 * T 1 (k + 1) := col1_lt_two_mul_row1 hT hn
    omega

/-- Every prime belongs to `R ⊔ C` (justifying Kimberling's "prime-separator" name). -/
theorem prime_mem_R_or_C {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {p : ℕ} (hp : Nat.Prime p) :
    (∃ j : ℕ, 2 ≤ j ∧ T 1 j = p) ∨ (∃ i : ℕ, 2 ≤ i ∧ T i 1 = p) := by
  rcases cover_ge_two hT hp.two_le with hR | hC | ⟨i, j, hi, hj, hEq⟩
  · exact Or.inl hR
  · exact Or.inr hC
  · exfalso
    have hci : 2 ≤ T i 1 := col1_ge_two hT hi
    have hrj : 2 ≤ T 1 j := row1_ge_two hT hj
    rcases hp.eq_one_or_self_of_dvd (T i 1) ⟨T 1 j, hEq.symm⟩ with h1 | hself
    · omega
    · rw [hself] at hEq
      have : p * 1 < p * T 1 j := Nat.mul_lt_mul_of_pos_left (by omega) hp.pos
      omega

/-- **Main Exported Theorem — Unconditional Bertrand Partition Theorem for PPL 049 (Kimberling #12).**

For any array `T : ℕ → ℕ → ℕ` satisfying the verbatim Kimberling #12 specification
`IsKimberlingPrimeSepArray T`, letting `R = { T(1, j) | j ≥ 2 }`, `C = { T(i, 1) | i ≥ 2 }`,
and `CR = { c * r | c ∈ C, r ∈ R }`:
1. Strict interleaving: `T(1, n) < T(n, 1) < T(1, n + 1)` for all `n ≥ 2`.
2. Unconditional Bertrand bounds: `T(n, 1) < 2 * T(1, n)` and `T(1, n + 1) < 2 * T(n, 1)` for `n ≥ 2`.
3. Exact three-way disjoint partition of `ℤ_{≥ 2}`:
   `R`, `C`, `CR` are pairwise disjoint and cover every `m ≥ 2`.
4. Every prime `p` lies in `R ⊔ C`. -/
theorem bertrand_partition_theorem
    (T : ℕ → ℕ → ℕ) (hT : IsKimberlingPrimeSepArray T) :
    let R : Set ℕ := {x | ∃ j : ℕ, 2 ≤ j ∧ T 1 j = x}
    let C : Set ℕ := {x | ∃ i : ℕ, 2 ≤ i ∧ T i 1 = x}
    let CR : Set ℕ := {x | ∃ c ∈ C, ∃ r ∈ R, c * r = x}
    (∀ n : ℕ, 2 ≤ n → T 1 n < T n 1 ∧ T n 1 < T 1 (n + 1)) ∧
    (∀ n : ℕ, 2 ≤ n → T n 1 < 2 * T 1 n ∧ T 1 (n + 1) < 2 * T n 1) ∧
    Disjoint R C ∧ Disjoint R CR ∧ Disjoint C CR ∧
    (∀ m : ℕ, 2 ≤ m → m ∈ R ∨ m ∈ C ∨ m ∈ CR) ∧
    (∀ p : ℕ, Nat.Prime p → p ∈ R ∨ p ∈ C) := by
  refine ⟨?_, ?_, disjoint_row1_col1 hT, disjoint_row1_CR hT, disjoint_col1_CR hT, ?_, ?_⟩
  · intro n hn
    exact ⟨row1_lt_col1 hT hn, col1_lt_row1_succ hT (by omega)⟩
  · intro n hn
    exact ⟨col1_lt_two_mul_row1 hT hn, row1_succ_lt_two_mul_col1 hT hn⟩
  · intro m hm
    rcases cover_ge_two hT hm with hR | hC | ⟨i, j, hi, hj, hEq⟩
    · exact Or.inl hR
    · exact Or.inr (Or.inl hC)
    · exact Or.inr (Or.inr ⟨T i 1, ⟨i, hi, rfl⟩, T 1 j, ⟨j, hj, rfl⟩, hEq⟩)
  · intro p hp
    exact prime_mem_R_or_C hT hp

/-! ## Section 5: Alternating Balance & Uniqueness (Online Greedy Sieve Equivalence) -/

/-- Exact counting helper: for a strictly increasing sequence `f` with `f 0 ≥ 2` and `f k ≥ k + 2`,
the number of elements of `{f k | k : ℕ}` in `[2, m]` equals the unique index `K` with
`∀ k < K, f k ≤ m` and `m < f K`. -/
private lemma exists_prefix_card_of_strictMono
    (f : ℕ → ℕ) (hmono : ∀ a b : ℕ, a < b → f a < f b) (hge : ∀ k : ℕ, k + 2 ≤ f k)
    (m : ℕ) :
    ∃ K : ℕ,
      (∀ k : ℕ, k < K → f k ≤ m) ∧ m < f K ∧
      ∀ [DecidablePred (fun x : ℕ => ∃ k : ℕ, f k = x)],
        ((Finset.Icc 2 m).filter (fun x : ℕ => ∃ k : ℕ, f k = x)).card = K := by
  classical
  have hex : ∃ k : ℕ, m < f k := ⟨m, by have := hge m; omega⟩
  let K : ℕ := Nat.find hex
  have hK_gt : m < f K := Nat.find_spec hex
  have hK_lt : ∀ k : ℕ, k < K → f k ≤ m := by
    intro k hk
    have hnot : ¬ (m < f k) := Nat.find_min hex hk
    omega
  refine ⟨K, hK_lt, hK_gt, ?_⟩
  intro inst
  have hset : (Finset.Icc 2 m).filter (fun x : ℕ => ∃ k : ℕ, f k = x) =
      (Finset.range K).image f := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hxm⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ?_, rfl⟩
      by_contra hgeK
      have hle : K ≤ k := Nat.le_of_not_lt hgeK
      have hf : f K ≤ f k := by
        rcases Nat.eq_or_lt_of_le hle with rfl | hlt
        · exact le_rfl
        · exact le_of_lt (hmono K k hlt)
      omega
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨by have := hge k; omega, hK_lt k hk⟩, ⟨k, rfl⟩⟩
  rw [hset, Finset.card_image_of_injective]
  · exact Finset.card_range K
  · intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ne_of_lt (hmono a b hlt) hab
    · exact ne_of_gt (hmono b a hgt) hab

/-- **Exact Alternating Balance:** For every `m : ℕ`, the counts of `R` and `C` in `[2, m]`
satisfy `|R ∩ [2, m]| = |C ∩ [2, m]|` or `|R ∩ [2, m]| = |C ∩ [2, m]| + 1`. -/
theorem alternating_balance {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    (m : ℕ)
    [DecidablePred (fun x : ℕ => ∃ j : ℕ, 2 ≤ j ∧ T 1 j = x)]
    [DecidablePred (fun x : ℕ => ∃ i : ℕ, 2 ≤ i ∧ T i 1 = x)] :
    ((Finset.Icc 2 m).filter (fun x : ℕ => ∃ j : ℕ, 2 ≤ j ∧ T 1 j = x)).card =
      ((Finset.Icc 2 m).filter (fun x : ℕ => ∃ i : ℕ, 2 ≤ i ∧ T i 1 = x)).card ∨
    ((Finset.Icc 2 m).filter (fun x : ℕ => ∃ j : ℕ, 2 ≤ j ∧ T 1 j = x)).card =
      ((Finset.Icc 2 m).filter (fun x : ℕ => ∃ i : ℕ, 2 ≤ i ∧ T i 1 = x)).card + 1 := by
  let fR : ℕ → ℕ := fun k => T 1 (k + 2)
  let fC : ℕ → ℕ := fun k => T (k + 2) 1
  have hR_mono : ∀ a b : ℕ, a < b → fR a < fR b :=
    fun a b hab => row1_strictMono_on hT (by omega) (by omega)
  have hC_mono : ∀ a b : ℕ, a < b → fC a < fC b :=
    fun a b hab => col1_strictMono_on hT (by omega) (by omega)
  have hR_ge : ∀ k : ℕ, k + 2 ≤ fR k := fun k => row1_ge_index hT (by omega)
  have hC_ge : ∀ k : ℕ, k + 2 ≤ fC k := fun k => col1_ge_index hT (by omega)
  obtain ⟨KR, hKR_lt, hKR_gt, hKR_card⟩ :=
    exists_prefix_card_of_strictMono fR hR_mono hR_ge m
  obtain ⟨KC, hKC_lt, hKC_gt, hKC_card⟩ :=
    exists_prefix_card_of_strictMono fC hC_mono hC_ge m
  have hEqR : ((Finset.Icc 2 m).filter (fun x : ℕ => ∃ j : ℕ, 2 ≤ j ∧ T 1 j = x)).card = KR := by
    classical
    have hf : (Finset.Icc 2 m).filter (fun x : ℕ => ∃ j : ℕ, 2 ≤ j ∧ T 1 j = x) =
        (Finset.Icc 2 m).filter (fun x : ℕ => ∃ k : ℕ, fR k = x) := by
      ext x
      simp only [Finset.mem_filter, fR]
      refine and_congr_right fun _ => ?_
      constructor
      · rintro ⟨j, hj, rfl⟩; exact ⟨j - 2, by congr 1; omega⟩
      · rintro ⟨k, rfl⟩; exact ⟨k + 2, by omega, rfl⟩
    rw [hf]
    exact hKR_card
  have hEqC : ((Finset.Icc 2 m).filter (fun x : ℕ => ∃ i : ℕ, 2 ≤ i ∧ T i 1 = x)).card = KC := by
    classical
    have hf : (Finset.Icc 2 m).filter (fun x : ℕ => ∃ i : ℕ, 2 ≤ i ∧ T i 1 = x) =
        (Finset.Icc 2 m).filter (fun x : ℕ => ∃ k : ℕ, fC k = x) := by
      ext x
      simp only [Finset.mem_filter, fC]
      refine and_congr_right fun _ => ?_
      constructor
      · rintro ⟨i, hi, rfl⟩; exact ⟨i - 2, by congr 1; omega⟩
      · rintro ⟨k, rfl⟩; exact ⟨k + 2, by omega, rfl⟩
    rw [hf]
    exact hKC_card
  rw [hEqR, hEqC]
  have hKC_le_KR : KC ≤ KR := by
    by_contra hlt
    have h1 : fR KR < fC KR := row1_lt_col1 hT (by omega)
    have h2 : fC KR ≤ m := hKC_lt KR (by omega)
    omega
  have hKR_le_KC_succ : KR ≤ KC + 1 := by
    by_contra hlt
    have h1 : fC KC < fR (KC + 1) := col1_lt_row1_succ hT (by omega)
    have h2 : fR (KC + 1) ≤ m := hKR_lt (KC + 1) (by omega)
    omega
  omega

/-- Specification of an alternating three-way multiplicative partition of `ℤ_{≥ 2}`
(equivalently, the online greedy sieve definition of `(R, C)`). -/
def IsAlternatingPartition (R C : Set ℕ) : Prop :=
  (∀ x ∈ R, 2 ≤ x) ∧
  (∀ x ∈ C, 2 ≤ x) ∧
  Disjoint R C ∧
  Disjoint R {x : ℕ | ∃ c ∈ C, ∃ r ∈ R, c * r = x} ∧
  Disjoint C {x : ℕ | ∃ c ∈ C, ∃ r ∈ R, c * r = x} ∧
  (∀ m : ℕ, 2 ≤ m → m ∈ R ∨ m ∈ C ∨ ∃ c ∈ C, ∃ r ∈ R, c * r = m) ∧
  (∀ m : ℕ, ∀ [DecidablePred (· ∈ R)] [DecidablePred (· ∈ C)],
    ((Finset.Icc 2 m).filter (· ∈ R)).card = ((Finset.Icc 2 m).filter (· ∈ C)).card ∨
    ((Finset.Icc 2 m).filter (· ∈ R)).card = ((Finset.Icc 2 m).filter (· ∈ C)).card + 1)

/-- **Uniqueness of the Alternating Partition:** Any two alternating three-way partitions
of `ℤ_{≥ 2}` are identical. -/
theorem alternating_partition_unique {R₁ C₁ R₂ C₂ : Set ℕ}
    (h₁ : IsAlternatingPartition R₁ C₁) (h₂ : IsAlternatingPartition R₂ C₂) :
    R₁ = R₂ ∧ C₁ = C₂ := by
  classical
  rcases h₁ with ⟨hR₁_ge, hC₁_ge, hRC₁, hRCR₁, hCCR₁, hcov₁, hbal₁⟩
  rcases h₂ with ⟨hR₂_ge, hC₂_ge, hRC₂, hRCR₂, hCCR₂, hcov₂, hbal₂⟩
  suffices hpt : ∀ m : ℕ, (m ∈ R₁ ↔ m ∈ R₂) ∧ (m ∈ C₁ ↔ m ∈ C₂) by
    exact ⟨Set.ext fun m => (hpt m).1, Set.ext fun m => (hpt m).2⟩
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hm2 : m < 2
    · exact ⟨⟨fun h => absurd (hR₁_ge m h) (by omega), fun h => absurd (hR₂_ge m h) (by omega)⟩,
             ⟨fun h => absurd (hC₁_ge m h) (by omega), fun h => absurd (hC₂_ge m h) (by omega)⟩⟩
    · have hm : 2 ≤ m := by omega
      have hCR_iff : (∃ c ∈ C₁, ∃ r ∈ R₁, c * r = m) ↔ (∃ c ∈ C₂, ∃ r ∈ R₂, c * r = m) := by
        constructor
        · rintro ⟨c, hc, r, hr, hEq⟩
          have hc2 : 2 ≤ c := hC₁_ge c hc
          have hr2 : 2 ≤ r := hR₁_ge r hr
          have hc_lt : c < m := by
            have : c * 1 < c * r := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
            omega
          have hr_lt : r < m := by
            have : 1 * r < c * r := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
            omega
          exact ⟨c, (ih c hc_lt).2.mp hc, r, (ih r hr_lt).1.mp hr, hEq⟩
        · rintro ⟨c, hc, r, hr, hEq⟩
          have hc2 : 2 ≤ c := hC₂_ge c hc
          have hr2 : 2 ≤ r := hR₂_ge r hr
          have hc_lt : c < m := by
            have : c * 1 < c * r := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
            omega
          have hr_lt : r < m := by
            have : 1 * r < c * r := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
            omega
          exact ⟨c, (ih c hc_lt).2.mpr hc, r, (ih r hr_lt).1.mpr hr, hEq⟩
      by_cases hCR : ∃ c ∈ C₁, ∃ r ∈ R₁, c * r = m
      · have hCR₂ : ∃ c ∈ C₂, ∃ r ∈ R₂, c * r = m := hCR_iff.mp hCR
        have h1R : m ∉ R₁ := Set.disjoint_right.mp hRCR₁ hCR
        have h1C : m ∉ C₁ := Set.disjoint_right.mp hCCR₁ hCR
        have h2R : m ∉ R₂ := Set.disjoint_right.mp hRCR₂ hCR₂
        have h2C : m ∉ C₂ := Set.disjoint_right.mp hCCR₂ hCR₂
        exact ⟨⟨fun h => absurd h h1R, fun h => absurd h h2R⟩,
               ⟨fun h => absurd h h1C, fun h => absurd h h2C⟩⟩
      · have hCR₂ : ¬ ∃ c ∈ C₂, ∃ r ∈ R₂, c * r = m := fun h => hCR (hCR_iff.mpr h)
        have hprevR : ((Finset.Icc 2 (m - 1)).filter (· ∈ R₁)).card =
            ((Finset.Icc 2 (m - 1)).filter (· ∈ R₂)).card := by
          congr 1
          ext x
          simp only [Finset.mem_filter, Finset.mem_Icc]
          refine and_congr_right fun hx => (ih x (by omega)).1
        have hprevC : ((Finset.Icc 2 (m - 1)).filter (· ∈ C₁)).card =
            ((Finset.Icc 2 (m - 1)).filter (· ∈ C₂)).card := by
          congr 1
          ext x
          simp only [Finset.mem_filter, Finset.mem_Icc]
          refine and_congr_right fun hx => (ih x (by omega)).2
        have hIcc : Finset.Icc 2 m = insert m (Finset.Icc 2 (m - 1)) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hm_not : m ∉ Finset.Icc 2 (m - 1) := by
          simp only [Finset.mem_Icc]; omega
        have hcard_step : ∀ (S : Set ℕ),
            ((Finset.Icc 2 m).filter (· ∈ S)).card =
              ((Finset.Icc 2 (m - 1)).filter (· ∈ S)).card + (if m ∈ S then 1 else 0) := by
          intro S
          rw [hIcc, Finset.filter_insert]
          split_ifs with hmS
          · rw [Finset.card_insert_of_notMem (by simp [hm_not])]
          · omega
        have h1_bal_prev := hbal₁ (m - 1)
        have h1_bal_now := hbal₁ m
        have h2_bal_now := hbal₂ m
        rw [hcard_step R₁, hcard_step C₁] at h1_bal_now
        rw [hcard_step R₂, hcard_step C₂, ← hprevR, ← hprevC] at h2_bal_now
        have h1_or : m ∈ R₁ ∨ m ∈ C₁ := by
          rcases hcov₁ m hm with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hCR
        have h2_or : m ∈ R₂ ∨ m ∈ C₂ := by
          rcases hcov₂ m hm with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hCR₂
        have h1_not_both : ¬ (m ∈ R₁ ∧ m ∈ C₁) :=
          fun ⟨hR, hC⟩ => Set.disjoint_left.mp hRC₁ hR hC
        have h2_not_both : ¬ (m ∈ R₂ ∧ m ∈ C₂) :=
          fun ⟨hR, hC⟩ => Set.disjoint_left.mp hRC₂ hR hC
        rcases h1_bal_prev with heq | hsucc
        · -- Equal counts before m: m MUST enter R in both partitions
          have h1R : m ∈ R₁ := by
            rcases h1_or with hR | hC
            · exact hR
            · exfalso
              have hnotR : m ∉ R₁ := fun hR => h1_not_both ⟨hR, hC⟩
              simp only [if_neg hnotR, if_pos hC] at h1_bal_now
              omega
          have h2R : m ∈ R₂ := by
            rcases h2_or with hR | hC
            · exact hR
            · exfalso
              have hnotR : m ∉ R₂ := fun hR => h2_not_both ⟨hR, hC⟩
              simp only [if_neg hnotR, if_pos hC] at h2_bal_now
              omega
          have h1nC : m ∉ C₁ := fun hC => h1_not_both ⟨h1R, hC⟩
          have h2nC : m ∉ C₂ := fun hC => h2_not_both ⟨h2R, hC⟩
          exact ⟨⟨fun _ => h2R, fun _ => h1R⟩,
                 ⟨fun h => absurd h h1nC, fun h => absurd h h2nC⟩⟩
        · -- R leads C by 1 before m: m MUST enter C in both partitions
          have h1C : m ∈ C₁ := by
            rcases h1_or with hR | hC
            · exfalso
              have hnotC : m ∉ C₁ := fun hC => h1_not_both ⟨hR, hC⟩
              simp only [if_pos hR, if_neg hnotC] at h1_bal_now
              omega
            · exact hC
          have h2C : m ∈ C₂ := by
            rcases h2_or with hR | hC
            · exfalso
              have hnotC : m ∉ C₂ := fun hC => h2_not_both ⟨hR, hC⟩
              simp only [if_pos hR, if_neg hnotC] at h2_bal_now
              omega
            · exact hC
          have h1nR : m ∉ R₁ := fun hR => h1_not_both ⟨hR, h1C⟩
          have h2nR : m ∉ R₂ := fun hR => h2_not_both ⟨hR, h2C⟩
          exact ⟨⟨fun h => absurd h h1nR, fun h => absurd h h2nR⟩,
                 ⟨fun _ => h2C, fun _ => h1C⟩⟩

/-- **Complete Equivalence (`kimberling_iff_alternating_partition`):**
A pair of sets `(R', C')` satisfies the online alternating 3-way partition axioms if and only if
`R'` and `C'` are the row-1 and column-1 sets (entries `≥ 2`) of Kimberling's array `T`. -/
theorem kimberling_iff_alternating_partition
    (T : ℕ → ℕ → ℕ) (hT : IsKimberlingPrimeSepArray T) (R' C' : Set ℕ) :
    IsAlternatingPartition R' C' ↔
      R' = {x : ℕ | ∃ j : ℕ, 2 ≤ j ∧ T 1 j = x} ∧
      C' = {x : ℕ | ∃ i : ℕ, 2 ≤ i ∧ T i 1 = x} := by
  have hTC : IsAlternatingPartition
      {x : ℕ | ∃ j : ℕ, 2 ≤ j ∧ T 1 j = x}
      {x : ℕ | ∃ i : ℕ, 2 ≤ i ∧ T i 1 = x} := by
    have hbert := bertrand_partition_theorem T hT
    refine ⟨?_, ?_, hbert.2.2.1, hbert.2.2.2.1, hbert.2.2.2.2.1, ?_, ?_⟩
    · rintro x ⟨j, hj, rfl⟩; exact row1_ge_two hT hj
    · rintro x ⟨i, hi, rfl⟩; exact col1_ge_two hT hi
    · intro m hm
      rcases hbert.2.2.2.2.2.1 m hm with hR | hC | ⟨c, hc, r, hr, hEq⟩
      · exact Or.inl hR
      · exact Or.inr (Or.inl hC)
      · exact Or.inr (Or.inr ⟨c, hc, r, hr, hEq⟩)
    · intro m instR instC
      exact @alternating_balance T hT m instR instC
  constructor
  · intro h'
    exact alternating_partition_unique h' hTC
  · rintro ⟨rfl, rfl⟩
    exact hTC

/-! ## Section 6: Prime-Separation Gap & Counting Corollaries -/

/-- **At Most One Prime Between Consecutive Row-1 Elements:**
For any `n ≥ 2` and any two primes `p < q` with `T(1, n) < p`, we have `T(1, n + 1) ≤ q`.
In particular, no open interval `(T(1, n), T(1, n + 1))` contains two distinct primes. -/
theorem at_most_one_prime_between_row1
    {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n p q : ℕ} (hn : 2 ≤ n) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h1 : T 1 n < p) (h2 : p < q) :
    T 1 (n + 1) ≤ q := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have hp_notS : ¬ InBlock T k p :=
    prime_not_inBlock_of_gt_col1 hT hk hp (lt_trans (col1_lt_row1_succ hT hk) h1)
  have hcol_le_p : T (k + 1) 1 ≤ p :=
    (hT.2 k hk).2.1.2.2.2 p (by linarith [hp.two_le]) hp_notS (by omega)
  have hq_notS : ¬ InBlock T (k + 1) q :=
    prime_not_inBlock_of_gt_col1 hT (by omega) hq (lt_of_le_of_lt hcol_le_p h2)
  exact (hT.2 (k + 1) (by omega)).1.2.2 q (by linarith [hq.two_le]) hq_notS

/-- **Prime-Counting Lower Bounds on `R` and `C`:**
For every `X : ℕ`, letting `π(X) = |{ p ∈ [2, X] | Nat.Prime p }|`,
`π(X) ≤ 2 * |R ∩ [2, X]|` and `π(X) ≤ 2 * |C ∩ [2, X]| + 1`. -/
theorem row1_count_ge_half_prime_count
    {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T) (X : ℕ)
    [DecidablePred (fun x : ℕ => ∃ j : ℕ, 2 ≤ j ∧ T 1 j = x)]
    [DecidablePred (fun x : ℕ => ∃ i : ℕ, 2 ≤ i ∧ T i 1 = x)] :
    ((Finset.Icc 2 X).filter Nat.Prime).card ≤
      2 * ((Finset.Icc 2 X).filter (fun x : ℕ => ∃ j : ℕ, 2 ≤ j ∧ T 1 j = x)).card ∧
    ((Finset.Icc 2 X).filter Nat.Prime).card ≤
      2 * ((Finset.Icc 2 X).filter (fun x : ℕ => ∃ i : ℕ, 2 ≤ i ∧ T i 1 = x)).card + 1 := by
  have hsub : (Finset.Icc 2 X).filter Nat.Prime ⊆
      (Finset.Icc 2 X).filter (fun x : ℕ => ∃ j : ℕ, 2 ≤ j ∧ T 1 j = x) ∪
      (Finset.Icc 2 X).filter (fun x : ℕ => ∃ i : ℕ, 2 ≤ i ∧ T i 1 = x) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_union] at hp ⊢
    rcases prime_mem_R_or_C hT hp.2 with hR | hC
    · exact Or.inl ⟨hp.1, hR⟩
    · exact Or.inr ⟨hp.1, hC⟩
  have hcard_le : ((Finset.Icc 2 X).filter Nat.Prime).card ≤
      ((Finset.Icc 2 X).filter (fun x : ℕ => ∃ j : ℕ, 2 ≤ j ∧ T 1 j = x)).card +
      ((Finset.Icc 2 X).filter (fun x : ℕ => ∃ i : ℕ, 2 ≤ i ∧ T i 1 = x)).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hbal := alternating_balance hT X
  omega

/-! ## Section 7: Exact Small-Value Witnesses (OEIS A129258 / A129259) -/

private lemma row1_eq_of_spec {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n v : ℕ} (hn : 1 ≤ n) (hv1 : 1 ≤ v) (hnot : ¬ InBlock T n v)
    (hlt : ∀ x : ℕ, 1 ≤ x → x < v → InBlock T n x) :
    T 1 (n + 1) = v := by
  have hle : T 1 (n + 1) ≤ v := (hT.2 n hn).1.2.2 v hv1 hnot
  by_contra hne
  exact (hT.2 n hn).1.2.1 (hlt (T 1 (n + 1)) (hT.2 n hn).1.1 (by omega))

private lemma col1_eq_of_spec {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T)
    {n v : ℕ} (hn : 1 ≤ n) (hv1 : 1 ≤ v) (hnot : ¬ InBlock T n v) (hne : v ≠ T 1 (n + 1))
    (hlt : ∀ x : ℕ, 1 ≤ x → x < v → x ≠ T 1 (n + 1) → InBlock T n x) :
    T (n + 1) 1 = v := by
  have hle : T (n + 1) 1 ≤ v := (hT.2 n hn).2.1.2.2.2 v hv1 hnot hne
  by_contra hneq
  exact (hT.2 n hn).2.1.2.1
    (hlt (T (n + 1) 1) (hT.2 n hn).2.1.1 (by omega) (hT.2 n hn).2.1.2.2.1)

/-- **Exact Small-Value Witnesses** for any array satisfying `IsKimberlingPrimeSepArray T`:
Row 1 (`A129259`): `1, 2, 4, 7, 9, 13, 15, 18`;
Column 1: `1, 3, 5, 8, 11, 14, 17`;
and initial off-border products `T(2,2) = 6, T(3,2) = 10, T(2,3) = 12, T(4,2) = 16, T(3,3) = 20`. -/
theorem kimberling_small_values {T : ℕ → ℕ → ℕ} (hT : IsKimberlingPrimeSepArray T) :
    (T 1 1 = 1 ∧ T 1 2 = 2 ∧ T 1 3 = 4 ∧ T 1 4 = 7 ∧
     T 1 5 = 9 ∧ T 1 6 = 13 ∧ T 1 7 = 15 ∧ T 1 8 = 18) ∧
    (T 2 1 = 3 ∧ T 3 1 = 5 ∧ T 4 1 = 8 ∧ T 5 1 = 11 ∧ T 6 1 = 14 ∧ T 7 1 = 17) ∧
    (T 2 2 = 6 ∧ T 3 2 = 10 ∧ T 2 3 = 12 ∧ T 4 2 = 16 ∧ T 3 3 = 20) := by
  have h11 : T 1 1 = 1 := hT.1
  -- Step n = 1: T(1,2) = 2, T(2,1) = 3
  have hr2 : T 1 2 = 2 := row1_eq_of_spec hT (by omega) (by omega)
    (by
      rintro ⟨i, j, hi1, hi2, hj1, hj2, hEq⟩
      have hi : i = 1 := by omega
      have hj : j = 1 := by omega
      subst hi; subst hj; omega)
    (fun x hx1 hlt => ⟨1, 1, le_rfl, le_rfl, le_rfl, le_rfl, by omega⟩)
  have hc2 : T 2 1 = 3 := col1_eq_of_spec hT (by omega) (by omega)
    (by
      rintro ⟨i, j, hi1, hi2, hj1, hj2, hEq⟩
      have hi : i = 1 := by omega
      have hj : j = 1 := by omega
      subst hi; subst hj; omega)
    (by change 3 ≠ T 1 2; omega)
    (fun x hx1 hlt hne => by
      change x ≠ T 1 2 at hne
      exact ⟨1, 1, le_rfl, le_rfl, le_rfl, le_rfl, by omega⟩)
  have h22 : T 2 2 = 6 := by
    rw [kimberling_mul_eq hT (by omega) (by omega), hc2, hr2]
  -- Step n = 2: T(1,3) = 4, T(3,1) = 5
  have hr3 : T 1 3 = 4 := row1_eq_of_spec hT (by omega) (by omega)
    (by
      rintro ⟨i, j, hi1, hi2, hj1, hj2, hEq⟩
      rw [kimberling_mul_eq hT hi1 hj1] at hEq
      interval_cases i <;> interval_cases j <;> simp_all)
    (fun x hx1 hlt => inBlock_of_le_col1 hT (by omega) hx1 (by omega))
  have hc3 : T 3 1 = 5 := col1_eq_of_spec hT (by omega) (by omega)
    (by
      rintro ⟨i, j, hi1, hi2, hj1, hj2, hEq⟩
      rw [kimberling_mul_eq hT hi1 hj1] at hEq
      interval_cases i <;> interval_cases j <;> simp_all)
    (by change 5 ≠ T 1 3; omega)
    (fun x hx1 hlt hne => by
      change x ≠ T 1 3 at hne
      exact inBlock_of_le_col1 hT (by omega) hx1 (by omega))
  have h32 : T 3 2 = 10 := by
    rw [kimberling_mul_eq hT (by omega) (by omega), hc3, hr2]
  have h23 : T 2 3 = 12 := by
    rw [kimberling_mul_eq hT (by omega) (by omega), hc2, hr3]
  have h33 : T 3 3 = 20 := by
    rw [kimberling_mul_eq hT (by omega) (by omega), hc3, hr3]
  -- Step n = 3: T(1,4) = 7, T(4,1) = 8
  have hr4 : T 1 4 = 7 := row1_eq_of_spec hT (by omega) (by omega)
    (by
      rintro ⟨i, j, hi1, hi2, hj1, hj2, hEq⟩
      rw [kimberling_mul_eq hT hi1 hj1] at hEq
      interval_cases i <;> interval_cases j <;> simp_all)
    (fun x hx1 hlt => by
      by_cases hx : x ≤ 5
      · exact inBlock_of_le_col1 hT (by omega) hx1 (by omega)
      · have : x = 6 := by omega
        subst this
        exact ⟨2, 2, by omega, by omega, by omega, by omega, h22⟩)
  have hc4 : T 4 1 = 8 := col1_eq_of_spec hT (by omega) (by omega)
    (by
      rintro ⟨i, j, hi1, hi2, hj1, hj2, hEq⟩
      rw [kimberling_mul_eq hT hi1 hj1] at hEq
      interval_cases i <;> interval_cases j <;> simp_all)
    (by change 8 ≠ T 1 4; omega)
    (fun x hx1 hlt hne => by
      change x ≠ T 1 4 at hne
      by_cases hx : x ≤ 5
      · exact inBlock_of_le_col1 hT (by omega) hx1 (by omega)
      · have : x = 6 := by omega
        subst this
        exact ⟨2, 2, by omega, by omega, by omega, by omega, h22⟩)
  have h42 : T 4 2 = 16 := by
    rw [kimberling_mul_eq hT (by omega) (by omega), hc4, hr2]
  -- Step n = 4: T(1,5) = 9, T(5,1) = 11
  have hr5 : T 1 5 = 9 := row1_eq_of_spec hT (by omega) (by omega)
    (by
      rintro ⟨i, j, hi1, hi2, hj1, hj2, hEq⟩
      rw [kimberling_mul_eq hT hi1 hj1] at hEq
      interval_cases i <;> interval_cases j <;> simp_all)
    (fun x hx1 hlt => inBlock_of_le_col1 hT (by omega) hx1 (by omega))
  have hc5 : T 5 1 = 11 := col1_eq_of_spec hT (by omega) (by omega)
    (by
      rintro ⟨i, j, hi1, hi2, hj1, hj2, hEq⟩
      rw [kimberling_mul_eq hT hi1 hj1] at hEq
      interval_cases i <;> interval_cases j <;> simp_all)
    (by change 11 ≠ T 1 5; omega)
    (fun x hx1 hlt hne => by
      change x ≠ T 1 5 at hne
      by_cases hx : x ≤ 8
      · exact inBlock_of_le_col1 hT (by omega) hx1 (by omega)
      · have : x = 10 := by omega
        subst this
        exact ⟨3, 2, by omega, by omega, by omega, by omega, h32⟩)
  -- Step n = 5: T(1,6) = 13, T(6,1) = 14
  have hr6 : T 1 6 = 13 := row1_eq_of_spec hT (by omega) (by omega)
    (prime_not_inBlock_of_gt_col1 hT (by omega) (by decide : Nat.Prime 13) (by omega))
    (fun x hx1 hlt => by
      by_cases hx : x ≤ 11
      · exact inBlock_of_le_col1 hT (by omega) hx1 (by omega)
      · have : x = 12 := by omega
        subst this
        exact ⟨2, 3, by omega, by omega, by omega, by omega, h23⟩)
  have hc6 : T 6 1 = 14 := col1_eq_of_spec hT (by omega) (by omega)
    (by
      rintro ⟨i, j, hi1, hi2, hj1, hj2, hEq⟩
      rw [kimberling_mul_eq hT hi1 hj1] at hEq
      interval_cases i <;> interval_cases j <;> simp_all)
    (by change 14 ≠ T 1 6; omega)
    (fun x hx1 hlt hne => by
      change x ≠ T 1 6 at hne
      by_cases hx : x ≤ 11
      · exact inBlock_of_le_col1 hT (by omega) hx1 (by omega)
      · have : x = 12 := by omega
        subst this
        exact ⟨2, 3, by omega, by omega, by omega, by omega, h23⟩)
  -- Step n = 6: T(1,7) = 15, T(7,1) = 17
  have hr7 : T 1 7 = 15 := row1_eq_of_spec hT (by omega) (by omega)
    (by
      rintro ⟨i, j, hi1, hi2, hj1, hj2, hEq⟩
      rw [kimberling_mul_eq hT hi1 hj1] at hEq
      interval_cases i <;> interval_cases j <;> simp_all)
    (fun x hx1 hlt => inBlock_of_le_col1 hT (by omega) hx1 (by omega))
  have hc7 : T 7 1 = 17 := col1_eq_of_spec hT (by omega) (by omega)
    (prime_not_inBlock_of_gt_col1 hT (by omega) (by decide : Nat.Prime 17) (by omega))
    (by change 17 ≠ T 1 7; omega)
    (fun x hx1 hlt hne => by
      change x ≠ T 1 7 at hne
      by_cases hx : x ≤ 14
      · exact inBlock_of_le_col1 hT (by omega) hx1 (by omega)
      · have : x = 16 := by omega
        subst this
        exact ⟨4, 2, by omega, by omega, by omega, by omega, h42⟩)
  -- Step n = 7: T(1,8) = 18
  have hr8 : T 1 8 = 18 := row1_eq_of_spec hT (by omega) (by omega)
    (by
      rintro ⟨i, j, hi1, hi2, hj1, hj2, hEq⟩
      rw [kimberling_mul_eq hT hi1 hj1] at hEq
      interval_cases i <;> interval_cases j <;> simp_all)
    (fun x hx1 hlt => inBlock_of_le_col1 hT (by omega) hx1 (by omega))
  exact ⟨⟨h11, hr2, hr3, hr4, hr5, hr6, hr7, hr8⟩,
         ⟨hc2, hc3, hc4, hc5, hc6, hc7⟩,
         ⟨h22, h32, h23, h42, h33⟩⟩

/-! ## Section 8: Barrier Theorem 1 — Multiplicative `ZMod 3` Partition Models -/

private lemma zmod3_cases (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  have hv : x.val < 3 := ZMod.val_lt x
  have hcast : (x.val : ZMod 3) = x := ZMod.natCast_zmod_val x
  rw [← hcast]
  interval_cases x.val
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- **Multiplicative `ZMod 3` Partition Model (Barrier Theorem 1A):**
For *any* completely additive map `φ : ℕ → ZMod 3` nonvanishing on all primes, the fiber sets
`R' = { n ≥ 2 | φ(n) = 1 }` and `C' = { n ≥ 2 | φ(n) = 2 }` satisfy the exact same
multiplicative partition equation `ℤ_{≥ 2} = R' ⊔ C' ⊔ (C' · R')` with all primes in `R' ⊔ C'`.
Hence the multiplicative partition equation alone cannot distinguish Kimberling's `(R, C)` from
positive-density completely multiplicative models. -/
theorem zmod3_multiplicative_partition_model
    (φ : ℕ → ZMod 3)
    (hadd : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → φ (a * b) = φ a + φ b)
    (hprime : ∀ p : ℕ, Nat.Prime p → φ p ≠ 0) :
    let R' : Set ℕ := {n | 2 ≤ n ∧ φ n = 1}
    let C' : Set ℕ := {n | 2 ≤ n ∧ φ n = 2}
    let CR' : Set ℕ := {x | ∃ c ∈ C', ∃ r ∈ R', c * r = x}
    Disjoint R' C' ∧ Disjoint R' CR' ∧ Disjoint C' CR' ∧
    (∀ m : ℕ, 2 ≤ m → m ∈ R' ∨ m ∈ C' ∨ m ∈ CR') ∧
    (∀ p : ℕ, Nat.Prime p → p ∈ R' ∨ p ∈ C') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro n ⟨_, h1⟩ ⟨_, h2⟩
    have : (1 : ZMod 3) ≠ 2 := by decide
    exact this (h1.symm.trans h2)
  · rw [Set.disjoint_left]
    rintro x ⟨_, hx1⟩ ⟨c, ⟨hc2, hφc⟩, r, ⟨hr2, hφr⟩, rfl⟩
    have h0 : φ (c * r) = 0 := by
      rw [hadd c r (by omega) (by omega), hφc, hφr]; decide
    have : (1 : ZMod 3) ≠ 0 := by decide
    exact this (hx1.symm.trans h0)
  · rw [Set.disjoint_left]
    rintro x ⟨_, hx2⟩ ⟨c, ⟨hc2, hφc⟩, r, ⟨hr2, hφr⟩, rfl⟩
    have h0 : φ (c * r) = 0 := by
      rw [hadd c r (by omega) (by omega), hφc, hφr]; decide
    have : (2 : ZMod 3) ≠ 0 := by decide
    exact this (hx2.symm.trans h0)
  · intro m hm
    rcases zmod3_cases (φ m) with h0 | h1 | h2
    · right; right
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
      rcases hpdvd with ⟨k, hmk⟩
      have hk0 : k ≠ 0 := by intro hk; subst hk; simp at hmk; omega
      have hk1 : k ≠ 1 := by
        intro hk; subst hk; simp only [mul_one] at hmk
        exact hprime p hp (hmk ▸ h0)
      have hk2 : 2 ≤ k := by omega
      have hsum : φ p + φ k = 0 := by
        rw [← hadd p k hp.ne_zero hk0, ← hmk, h0]
      rcases zmod3_cases (φ p) with hp0 | hp1 | hp2
      · exact absurd hp0 (hprime p hp)
      · have hφk : φ k = 2 := by
          rw [hp1] at hsum
          rcases zmod3_cases (φ k) with hk' | hk' | hk' <;> rw [hk'] at hsum
          · exfalso; exact (by decide : (1 : ZMod 3) + 0 ≠ 0) hsum
          · exfalso; exact (by decide : (1 : ZMod 3) + 1 ≠ 0) hsum
          · exact hk'
        exact ⟨k, ⟨hk2, hφk⟩, p, ⟨hp.two_le, hp1⟩, by rw [mul_comm, ← hmk]⟩
      · have hφk : φ k = 1 := by
          rw [hp2] at hsum
          rcases zmod3_cases (φ k) with hk' | hk' | hk' <;> rw [hk'] at hsum
          · exfalso; exact (by decide : (2 : ZMod 3) + 0 ≠ 0) hsum
          · exact hk'
          · exfalso; exact (by decide : (2 : ZMod 3) + 2 ≠ 0) hsum
        exact ⟨p, ⟨hp.two_le, hp2⟩, k, ⟨hk2, hφk⟩, hmk.symm⟩
    · exact Or.inl ⟨hm, h1⟩
    · exact Or.inr (Or.inl ⟨hm, h2⟩)
  · intro p hp
    rcases zmod3_cases (φ p) with hp0 | hp1 | hp2
    · exact absurd hp0 (hprime p hp)
    · exact Or.inl ⟨hp.two_le, hp1⟩
    · exact Or.inr ⟨hp.two_le, hp2⟩

/-- Total number of prime factors with multiplicity modulo 3: `Ω(n) mod 3`. -/
def omegaMod3 (n : ℕ) : ZMod 3 := (n.primeFactorsList.length : ZMod 3)

lemma omegaMod3_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    omegaMod3 (a * b) = omegaMod3 a + omegaMod3 b := by
  simp only [omegaMod3]
  have hlen : (a * b).primeFactorsList.length =
      a.primeFactorsList.length + b.primeFactorsList.length := by
    rw [(Nat.perm_primeFactorsList_mul ha hb).length_eq, List.length_append]
  rw [hlen, Nat.cast_add]

lemma omegaMod3_prime {p : ℕ} (hp : Nat.Prime p) : omegaMod3 p = 1 := by
  simp [omegaMod3, Nat.primeFactorsList_prime hp]

private lemma odd_pow2_inj {a b k₁ k₂ : ℕ}
    (h : 2 ^ a * (2 * k₁ + 1) = 2 ^ b * (2 * k₂ + 1)) :
    a = b ∧ k₁ = k₂ := by
  have hpow : ∀ {d x y : ℕ}, 1 ≤ d → 2 * x + 1 ≠ 2 ^ d * (2 * y + 1) := by
    intro d x y hd hEq
    have h2dvd : 2 ∣ 2 ^ d * (2 * y + 1) :=
      dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
    rw [← hEq] at h2dvd
    omega
  by_cases hab : a < b
  · exfalso
    have hEq : 2 * k₁ + 1 = 2 ^ (b - a) * (2 * k₂ + 1) := by
      have hmul : 2 ^ a * (2 * k₁ + 1) = 2 ^ a * (2 ^ (b - a) * (2 * k₂ + 1)) := by
        rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (le_of_lt hab), h]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) hmul
    exact hpow (by omega) hEq
  · by_cases hba : b < a
    · exfalso
      have hEq : 2 * k₂ + 1 = 2 ^ (a - b) * (2 * k₁ + 1) := by
        have hmul : 2 ^ b * (2 * k₂ + 1) = 2 ^ b * (2 ^ (a - b) * (2 * k₁ + 1)) := by
          rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (le_of_lt hba), h]
        exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) hmul
      exact hpow (by omega) hEq
    · have haeq : a = b := by omega
      subst haeq
      have hmul := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega : 0 < 2)) h
      exact ⟨rfl, by omega⟩

private lemma omegaMod3_pow2_mul (a m : ℕ) (hm : m ≠ 0) :
    omegaMod3 (2 ^ a * m) = (a : ZMod 3) + omegaMod3 m := by
  induction a with
  | zero => simp
  | succ k ih =>
    have hpow : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by ring
    rw [hpow, omegaMod3_mul (by omega) (mul_ne_zero (pow_ne_zero k (by omega)) hm),
      omegaMod3_prime Nat.prime_two, ih, Nat.cast_add, Nat.cast_one]
    ring

/-- **Positive Lower Density of the `Ω(n) mod 3` Partition Model (Barrier Theorem 1B):**
For `R' = { n ≥ 2 | Ω(n) ≡ 1 (mod 3) }` and `C' = { n ≥ 2 | Ω(n) ≡ 2 (mod 3) }`,
`(R', C')` satisfies the exact three-way partition `ℤ_{≥ 2} = R' ⊔ C' ⊔ (C' · R')` with all
primes in `R' ⊔ C'`, and for every `X : ℕ`:
`X / 16 ≤ |R' ∩ [2, X]|` and `X / 16 ≤ |C' ∩ [2, X]|`. -/
theorem omegaMod3_positive_lower_density :
    let R' : Set ℕ := {n | 2 ≤ n ∧ omegaMod3 n = 1}
    let C' : Set ℕ := {n | 2 ≤ n ∧ omegaMod3 n = 2}
    let CR' : Set ℕ := {x | ∃ c ∈ C', ∃ r ∈ R', c * r = x}
    Disjoint R' C' ∧ Disjoint R' CR' ∧ Disjoint C' CR' ∧
    (∀ m : ℕ, 2 ≤ m → m ∈ R' ∨ m ∈ C' ∨ m ∈ CR') ∧
    (∀ p : ℕ, Nat.Prime p → p ∈ R' ∨ p ∈ C') ∧
    (∀ X : ℕ,
      X / 16 ≤ ((Finset.Icc 2 X).filter (fun n => 2 ≤ n ∧ omegaMod3 n = 1)).card ∧
      X / 16 ≤ ((Finset.Icc 2 X).filter (fun n => 2 ≤ n ∧ omegaMod3 n = 2)).card) := by
  have hmodel := zmod3_multiplicative_partition_model omegaMod3
    (fun a b ha hb => omegaMod3_mul ha hb)
    (fun p hp => by rw [omegaMod3_prime hp]; decide)
  refine ⟨hmodel.1, hmodel.2.1, hmodel.2.2.1, hmodel.2.2.2.1, hmodel.2.2.2.2, ?_⟩
  have hdens : ∀ (t : ZMod 3) (X : ℕ),
      X / 16 ≤ ((Finset.Icc 2 X).filter (fun n => 2 ≤ n ∧ omegaMod3 n = t)).card := by
    intro t X
    let expOf : ℕ → ℕ := fun k =>
      if (1 : ZMod 3) + omegaMod3 (2 * k + 1) = t then 1
      else if (2 : ZMod 3) + omegaMod3 (2 * k + 1) = t then 2
      else 3
    let f : ℕ → ℕ := fun k => 2 ^ (expOf k) * (2 * k + 1)
    have hf_inj : Function.Injective f := by
      intro k₁ k₂ hEq
      exact (odd_pow2_inj hEq).2
    have hexp_ge : ∀ k : ℕ, 1 ≤ expOf k := by
      intro k; dsimp only [expOf]; split_ifs <;> omega
    have hexp_le : ∀ k : ℕ, expOf k ≤ 3 := by
      intro k; dsimp only [expOf]; split_ifs <;> omega
    have hf_om : ∀ k : ℕ, omegaMod3 (f k) = t := by
      intro k
      dsimp only [f]
      rw [omegaMod3_pow2_mul (expOf k) (2 * k + 1) (by omega)]
      dsimp only [expOf]
      split_ifs with h1 h2
      · simpa using h1
      · simpa using h2
      · rcases zmod3_cases (omegaMod3 (2 * k + 1)) with h | h | h <;>
        rcases zmod3_cases t with ht | ht | ht <;>
        simp only [h, ht] at h1 h2 ⊢ <;>
        first | decide | exact absurd (by decide) h1 | exact absurd (by decide) h2
    have hsub : (Finset.range (X / 16)).image f ⊆
        (Finset.Icc 2 X).filter (fun n => 2 ≤ n ∧ omegaMod3 n = t) := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨k, hk, rfl⟩
      rw [Finset.mem_range] at hk
      simp only [Finset.mem_filter, Finset.mem_Icc]
      have hge1 : 1 ≤ expOf k := hexp_ge k
      have hle3 : expOf k ≤ 3 := hexp_le k
      have hpow_ge : 2 ≤ 2 ^ (expOf k) := by
        have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hge1
        simpa using this
      have hpow_le : 2 ^ (expOf k) ≤ 8 := by
        have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hle3
        simpa using this
      have hfk_ge : 2 ≤ f k := by
        dsimp only [f]
        have : 2 * 1 ≤ 2 ^ (expOf k) * (2 * k + 1) := Nat.mul_le_mul hpow_ge (by omega)
        omega
      have hfk_le : f k ≤ X := by
        dsimp only [f]
        have h1 : 2 ^ (expOf k) * (2 * k + 1) ≤ 8 * (2 * k + 1) :=
          Nat.mul_le_mul_right _ hpow_le
        have h2 : 8 * (2 * k + 1) ≤ 16 * (k + 1) := by omega
        have h3 : 16 * (k + 1) ≤ 16 * (X / 16) := Nat.mul_le_mul_left 16 (by omega)
        have h4 : 16 * (X / 16) ≤ X := Nat.mul_div_le X 16
        omega
      exact ⟨⟨hfk_ge, hfk_le⟩, hfk_ge, hf_om k⟩
    calc
      X / 16 = (Finset.range (X / 16)).card := (Finset.card_range _).symm
      _ = ((Finset.range (X / 16)).image f).card := (Finset.card_image_of_injective _ hf_inj).symm
      _ ≤ ((Finset.Icc 2 X).filter (fun n => 2 ≤ n ∧ omegaMod3 n = t)).card :=
        Finset.card_le_card hsub
  intro X
  exact ⟨hdens 1 X, hdens 2 X⟩

/-! ## Section 9: Barrier Theorem 2 — No Local CRT / Divisibility Forcing -/

/-- Three-class color of an integer `≥ 2` in a partition `ℤ_{≥ 2} = R ⊔ C ⊔ (C · R)`. -/
inductive TriColor
  | R
  | C
  | CR
  deriving DecidableEq

/-- A 3-coloring `χ` is multiplicatively consistent on the divisors `≥ 2` of `d` if every
divisor `a ≥ 2` of `d` has color `CR` iff it factors as `b * c` with `b, c ≥ 2`, `χ b = C`,
and `χ c = R`. -/
def IsConsistentOnDivisors (d : ℕ) (χ : ℕ → TriColor) : Prop :=
  ∀ a : ℕ, 2 ≤ a → a ∣ d →
    (χ a = TriColor.CR ↔
      ∃ b c : ℕ, 2 ≤ b ∧ 2 ≤ c ∧ b * c = a ∧ χ b = TriColor.C ∧ χ c = TriColor.R)

open Classical in
/-- Adversary coloring on `p`-multiples `{ a * p | a ∣ d }`: whenever `a * p` is not forced into
`CR`, copy the color of its complementary divisor `d / a` (defaulting to `R`), preventing
`d * p` from ever acquiring a complementary `(C, R)` factor pair. -/
private noncomputable def adversaryPsiP (d : ℕ) (χ : ℕ → TriColor) (a : ℕ) : TriColor :=
  if _ : a = 0 then TriColor.R
  else
    if ∃ b : ℕ, ∃ _hb : 2 ≤ b, b ∣ a ∧
        ((χ b = TriColor.C ∧ adversaryPsiP d χ (a / b) = TriColor.R) ∨
         (χ b = TriColor.R ∧ adversaryPsiP d χ (a / b) = TriColor.C)) then
      TriColor.CR
    else if a < d ∧ χ (d / a) = TriColor.C then
      TriColor.C
    else
      TriColor.R
termination_by a
decreasing_by
  exact Nat.div_lt_self (by omega) (by omega)

/-- **No Local CRT / Divisibility Forcing (Barrier Theorem 2):**
For every `d ≥ 1`, every prime `p` not dividing `d`, and every multiplicatively consistent
3-coloring `χ` on the divisors of `d`, there exists a multiplicatively consistent extension `ψ`
on the divisors of `d * p` agreeing with `χ` on all divisors of `d` such that `ψ (d * p) ≠ CR`.
Hence no local divisibility/CRT pattern on `D(d)` can ever force `d * p` into `C · R`. -/
theorem no_local_divisibility_forcing
    {d p : ℕ} (hd : 1 ≤ d) (hp : Nat.Prime p) (hpnd : ¬ p ∣ d)
    {χ : ℕ → TriColor} (hχ : IsConsistentOnDivisors d χ) :
    ∃ ψ : ℕ → TriColor,
      (∀ a : ℕ, 2 ≤ a → a ∣ d → ψ a = χ a) ∧
      IsConsistentOnDivisors (d * p) ψ ∧
      ψ (d * p) ≠ TriColor.CR := by
  classical
  let ψ : ℕ → TriColor := fun x => if p ∣ x then adversaryPsiP d χ (x / p) else χ x
  have hψ_dvd : ∀ a : ℕ, a ∣ d → ψ a = χ a := by
    intro a had
    have hnp : ¬ p ∣ a := fun hpa => hpnd (dvd_trans hpa had)
    simp [ψ, hnp]
  have hψ_mul_p : ∀ a : ℕ, ψ (a * p) = adversaryPsiP d χ a := by
    intro a
    have hpd : p ∣ a * p := dvd_mul_left p a
    simp [ψ, hpd, Nat.mul_div_cancel a hp.pos]
  have hpsiP_eq_CR : ∀ a : ℕ, 1 ≤ a →
      (adversaryPsiP d χ a = TriColor.CR ↔
        ∃ b : ℕ, 2 ≤ b ∧ b ∣ a ∧
          ((χ b = TriColor.C ∧ adversaryPsiP d χ (a / b) = TriColor.R) ∨
           (χ b = TriColor.R ∧ adversaryPsiP d χ (a / b) = TriColor.C))) := by
    intro a ha
    conv_lhs => rw [adversaryPsiP]
    have ha0 : a ≠ 0 := by omega
    simp only [dif_neg ha0]
    split_ifs with h1 h2
    · exact ⟨fun _ => by rcases h1 with ⟨b, hb, h⟩; exact ⟨b, hb, h⟩, fun _ => rfl⟩
    · constructor
      · intro h; cases h
      · rintro ⟨b, hb, h⟩; exact absurd ⟨b, hb, h⟩ h1
    · constructor
      · intro h; cases h
      · rintro ⟨b, hb, h⟩; exact absurd ⟨b, hb, h⟩ h1
  refine ⟨ψ, fun a _ had => hψ_dvd a had, ?_, ?_⟩
  · intro x hx2 hxdp
    by_cases hpx : p ∣ x
    · rcases hpx with ⟨a, rfl⟩
      have ha1 : 1 ≤ a := by
        by_contra h0
        have : a = 0 := by omega
        subst this; simp at hx2
      have had : a ∣ d := by
        rw [mul_comm] at hxdp
        exact (Nat.mul_dvd_mul_iff_right hp.pos).mp hxdp
      rw [mul_comm p a, hψ_mul_p a, hpsiP_eq_CR a ha1]
      constructor
      · rintro ⟨b, hb2, hba, ⟨hcb, hrq⟩ | ⟨hrb, hcq⟩⟩
        · have hbd : b ∣ d := dvd_trans hba had
          have hq1 : 1 ≤ a / b := Nat.div_pos (Nat.le_of_dvd (by omega) hba) (by omega)
          have hqp2 : 2 ≤ (a / b) * p := by
            have : 1 * 2 ≤ (a / b) * p := Nat.mul_le_mul hq1 hp.two_le
            omega
          refine ⟨b, (a / b) * p, hb2, hqp2, ?_, ?_, ?_⟩
          · rw [← mul_assoc, Nat.mul_div_cancel' hba]
          · rw [hψ_dvd b hbd]; exact hcb
          · rw [hψ_mul_p (a / b)]; exact hrq
        · have hbd : b ∣ d := dvd_trans hba had
          have hq1 : 1 ≤ a / b := Nat.div_pos (Nat.le_of_dvd (by omega) hba) (by omega)
          have hqp2 : 2 ≤ (a / b) * p := by
            have : 1 * 2 ≤ (a / b) * p := Nat.mul_le_mul hq1 hp.two_le
            omega
          refine ⟨(a / b) * p, b, hqp2, hb2, ?_, ?_, ?_⟩
          · rw [mul_comm ((a / b) * p) b, ← mul_assoc, Nat.mul_div_cancel' hba]
          · rw [hψ_mul_p (a / b)]; exact hcq
          · rw [hψ_dvd b hbd]; exact hrb
      · rintro ⟨u, v, hu2, hv2, huv, hψu, hψv⟩
        have hpdvd_uv : p ∣ u * v := by rw [huv]; exact dvd_mul_left p a
        have hnotboth : ¬ (p ∣ u ∧ p ∣ v) := by
          rintro ⟨⟨u', rfl⟩, ⟨v', rfl⟩⟩
          have hpa : p ∣ a := by
            refine ⟨u' * v', ?_⟩
            have : (p * u') * (p * v') = p * (p * (u' * v')) := by ring
            have hEq : p * (p * (u' * v')) = p * a := by rw [← this, huv, mul_comm]
            exact (Nat.mul_left_cancel hp.pos hEq).symm
          exact hpnd (dvd_trans hpa had)
        rcases hp.dvd_mul.mp hpdvd_uv with hpu | hpv
        · have hnpv : ¬ p ∣ v := fun h => hnotboth ⟨hpu, h⟩
          rcases hpu with ⟨u', rfl⟩
          have hEq_a : u' * v = a := by
            have : p * (u' * v) = p * a := by
              calc
                p * (u' * v) = (p * u') * v := by ring
                _ = a * p := huv
                _ = p * a := mul_comm a p
            exact Nat.mul_left_cancel hp.pos this
          have hva : v ∣ a := ⟨u', by rw [mul_comm, hEq_a]⟩
          have hvd : v ∣ d := dvd_trans hva had
          have hu'_eq : a / v = u' := by
            rw [← hEq_a, Nat.mul_div_cancel u' (by omega)]
          have hψu' : adversaryPsiP d χ (a / v) = TriColor.C := by
            rw [hu'_eq, ← hψ_mul_p u', mul_comm u' p]; exact hψu
          have hχv : χ v = TriColor.R := by rw [← hψ_dvd v hvd]; exact hψv
          exact ⟨v, hv2, hva, Or.inr ⟨hχv, hψu'⟩⟩
        · have hnpu : ¬ p ∣ u := fun h => hnotboth ⟨h, hpv⟩
          rcases hpv with ⟨v', rfl⟩
          have hEq_a : u * v' = a := by
            have : p * (u * v') = p * a := by
              calc
                p * (u * v') = u * (p * v') := by ring
                _ = a * p := huv
                _ = p * a := mul_comm a p
            exact Nat.mul_left_cancel hp.pos this
          have hua : u ∣ a := ⟨v', hEq_a.symm⟩
          have hud : u ∣ d := dvd_trans hua had
          have hv'_eq : a / u = v' := by
            rw [← hEq_a, Nat.mul_div_cancel_left v' (by omega)]
          have hψv' : adversaryPsiP d χ (a / u) = TriColor.R := by
            rw [hv'_eq, ← hψ_mul_p v', mul_comm v' p]; exact hψv
          have hχu : χ u = TriColor.C := by rw [← hψ_dvd u hud]; exact hψu
          exact ⟨u, hu2, hua, Or.inl ⟨hχu, hψv'⟩⟩
    · have hcop : Nat.Coprime x p := (hp.coprime_iff_not_dvd.mpr hpx).symm
      have hxd : x ∣ d := hcop.dvd_of_dvd_mul_right hxdp
      rw [hψ_dvd x hxd, hχ x hx2 hxd]
      constructor
      · rintro ⟨b, c, hb2, hc2, hbc, hcb, hrc⟩
        have hbd : b ∣ d := dvd_trans ⟨c, hbc.symm⟩ hxd
        have hcd : c ∣ d := dvd_trans ⟨b, by rw [mul_comm, hbc]⟩ hxd
        exact ⟨b, c, hb2, hc2, hbc, by rw [hψ_dvd b hbd]; exact hcb, by rw [hψ_dvd c hcd]; exact hrc⟩
      · rintro ⟨b, c, hb2, hc2, hbc, hcb, hrc⟩
        have hbd : b ∣ d := dvd_trans ⟨c, hbc.symm⟩ hxd
        have hcd : c ∣ d := dvd_trans ⟨b, by rw [mul_comm, hbc]⟩ hxd
        exact ⟨b, c, hb2, hc2, hbc, by rw [← hψ_dvd b hbd]; exact hcb, by rw [← hψ_dvd c hcd]; exact hrc⟩
  · -- Prove ψ (d * p) ≠ CR
    intro hCR
    rw [hψ_mul_p d, hpsiP_eq_CR d hd] at hCR
    rcases hCR with ⟨b, hb2, hbd, hcase⟩
    let a : ℕ := d / b
    have ha1 : 1 ≤ a := Nat.div_pos (Nat.le_of_dvd (by omega) hbd) (by omega)
    have ha0 : a ≠ 0 := by omega
    have ha_lt : a < d := Nat.div_lt_self (by omega) (by omega)
    have hda : d / a = b := by
      have hab : a * b = d := Nat.div_mul_cancel hbd
      rw [← hab, Nat.mul_div_cancel_left b (by omega)]
    have hnotCR : adversaryPsiP d χ a ≠ TriColor.CR := by
      intro h
      rcases hcase with ⟨_, hr⟩ | ⟨_, hc⟩
      · rw [h] at hr; cases hr
      · rw [h] at hc; cases hc
    have hnotForc : ¬ (∃ b' : ℕ, ∃ _hb' : 2 ≤ b', b' ∣ a ∧
        ((χ b' = TriColor.C ∧ adversaryPsiP d χ (a / b') = TriColor.R) ∨
         (χ b' = TriColor.R ∧ adversaryPsiP d χ (a / b') = TriColor.C))) := by
      rintro ⟨b', hb', hdiv, hcol⟩
      apply hnotCR
      exact (hpsiP_eq_CR a ha1).mpr ⟨b', hb', hdiv, hcol⟩
    have hval : adversaryPsiP d χ a =
        if χ b = TriColor.C then TriColor.C else TriColor.R := by
      conv_lhs => rw [adversaryPsiP]
      simp only [dif_neg ha0, if_neg hnotForc, ha_lt, true_and, hda]
    rcases hcase with ⟨hcb, hra⟩ | ⟨hrb, hca⟩
    · rw [if_pos hcb] at hval
      rw [hval] at hra
      cases hra
    · have hneC : χ b ≠ TriColor.C := by rw [hrb]; intro h; cases h
      rw [if_neg hneC] at hval
      rw [hval] at hca
      cases hca

end PPL049_PrimeSepPartition
