import Prize.PPL176_UpperSharp
import Prize.PPL176_UpperCoprimeDual

/-!
# PPL 176 — Erdős Problem #708: Unconditional Upper-Bound Capstone

This capstone module packages our complete unconditional upper-bound & duality theory
for **Erdős Problem #708** (Erdős–Surányi 1959, \$100 open problem) from:
- `Prize.PPL176_UpperCore` (interval divisibility, `ℤ → ℕ` reduction, Top-`r` prime covering,
  `ω(a)` sum bound, exact `2n` bound for `ω(a) ≤ 2` sets including all semiprimes);
- `Prize.PPL176_UpperBinPack` (prime-power bin-packing with zero floor loss, exact `2n` bound
  for `max(A) ≥ 8 n^3` and `max(A) ≤ 2n`, exact `3n` bound for `max(A) ≥ 9 n^2`, general
  `k n` bound whenever `(k n)^(k+1) ≤ (max A)^(k-1)`);
- `Prize.PPL176_UpperGlobal` (finite Dirichlet exponential sum bound, Jensen exponential
  valuation bound, consecutive-block covering, global `O(n √(log n))` bound);
- `Prize.PPL176_UpperSharp` (general-base Dirichlet–Jensen block covering, unconditional
  global `O(n √(log n / log log n))` bound for ALL `n`, ALL `A ⊆ [2, ∞)`, ALL intervals
  `I ⊂ ℕ` and `I ⊂ ℤ`, plus LP Weak Duality Certificate).
-/

open scoped BigOperators Nat

namespace PPL176

/-- Canonical Erdős Problem #708 upper-bound predicate (`g(n) ≤ k`):
    for EVERY finite nonempty set `A ⊆ [2, ∞) ∩ ℕ` of cardinality `n` and EVERY interval
    `I = {m + 1, ..., m + max(A)}` of `max(A)` consecutive positive integers, there exists
    `B ⊆ I` with `|B| ≤ k` and `∏ a ∈ A, a ∣ ∏ b ∈ B, b`. -/
def Erdos708UpperBound (n k : ℕ) : Prop :=
  ∀ (A : Finset ℕ) (hA : A.Nonempty), A.card = n → (∀ a ∈ A, 2 ≤ a) →
    ∀ m : ℕ, ∃ B ⊆ Finset.Icc (m + 1) (m + A.max' hA),
      B.card ≤ k ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b)

/-- Canonical integer-interval Erdős Problem #708 upper-bound predicate (`I ⊂ ℤ`):
    for EVERY finite nonempty set `A ⊆ [2, ∞) ∩ ℕ` of cardinality `n` and EVERY interval
    `I = {m, m + 1, ..., m + max(A) - 1} ⊂ ℤ`, there exists `B ⊆ I` with `|B| ≤ k`
    and `((∏ a ∈ A, a : ℕ) : ℤ) ∣ ∏ b ∈ B, b`. -/
def Erdos708UpperBoundInt (n k : ℕ) : Prop :=
  ∀ (A : Finset ℕ) (hA : A.Nonempty), A.card = n → (∀ a ∈ A, 2 ≤ a) →
    ∀ m : ℤ, ∃ B ⊆ Finset.Ico m (m + (A.max' hA : ℤ)),
      B.card ≤ k ∧ ((∏ a ∈ A, a : ℕ) : ℤ) ∣ (∏ b ∈ B, b)

/-- Exact equivalence between `A.sup id` and `A.max' hA` for nonempty `A : Finset ℕ`. -/
lemma sup_id_eq_max' {A : Finset ℕ} (hA : A.Nonempty) : A.sup id = A.max' hA := by
  apply le_antisymm
  · rw [Finset.sup_le_iff]
    intro a ha
    exact Finset.le_max' A a ha
  · exact Finset.le_sup (f := id) (Finset.max'_mem A hA)

/-- **Unconditional `O(n √(log n))` Global Upper Bound** on `Erdos708UpperBound`. -/
theorem erdos708_upper_sqrt_log (n : ℕ) :
    Erdos708UpperBound n (3 * max 12 (Nat.sqrt (2 * Nat.log 2 n + 2) + 1) * n) := by
  intro A hA hcard hge2 m
  have h1 : ∀ a ∈ A, 1 ≤ a := fun a ha => le_trans (by norm_num) (hge2 a ha)
  have hcov := erdos708_global_sqrt_log h1 m
  simpa [Erdos708Covers, Erdos708Interval, sup_id_eq_max' hA, hcard] using hcov

/-- **Unconditional `O(n √(log n / log log n))` Global Upper Bound** on `Erdos708UpperBound`. -/
theorem erdos708_upper_sqrt_log_div_loglog (n : ℕ) :
    Erdos708UpperBound n
      (24 * max 16 (Nat.sqrt (Nat.log 2 n / max 1 (Nat.log 2 (Nat.log 2 n))) + 1) * n) := by
  intro A hA hcard hge2 m
  have h1 : ∀ a ∈ A, 1 ≤ a := fun a ha => le_trans (by norm_num) (hge2 a ha)
  have hcov := erdos708_global_sqrt_log_div_loglog h1 m
  simpa [Erdos708Covers, Erdos708Interval, sup_id_eq_max' hA, hcard] using hcov

/-- **Unconditional `O(n √(log n / log log n))` Global Upper Bound on ALL Integer Intervals `I ⊂ ℤ`**. -/
theorem erdos708_upper_sqrt_log_div_loglog_int (n : ℕ) :
    Erdos708UpperBoundInt n
      (24 * max 16 (Nat.sqrt (Nat.log 2 n / max 1 (Nat.log 2 (Nat.log 2 n))) + 1) * n) := by
  intro A hA hcard hge2 m
  have h1 : ∀ a ∈ A, 1 ≤ a := fun a ha => le_trans (by norm_num) (hge2 a ha)
  have hk : 1 ≤ 24 * max 16 (Nat.sqrt (Nat.log 2 A.card / max 1 (Nat.log 2 (Nat.log 2 A.card))) + 1) * A.card := by
    have hcard_pos : 1 ≤ A.card := Finset.card_pos.mpr hA
    have hmax : 16 ≤ max 16 (Nat.sqrt (Nat.log 2 A.card / max 1 (Nat.log 2 (Nat.log 2 A.card))) + 1) :=
      le_max_left _ _
    nlinarith
  have hcov := erdos708CoversInt_of_nat hA hge2 hk
    (fun x => erdos708_global_sqrt_log_div_loglog h1 x) m
  simpa [Erdos708CoversInt, sup_id_eq_max' hA, hcard] using hcov

/-- **Exact `2n` Upper Bound in All Three Resolved Regimes**:
    1. Small maximum (`max(A) ≤ 2 n`);
    2. Large maximum (`max(A) ≥ 8 n^3`);
    3. Semiprimes / `ω(a) ≤ 2` (`∀ a ∈ A, a.primeFactors.card ≤ 2`). -/
theorem erdos708_two_n_three_regimes {A : Finset ℕ} (hA : ∀ a ∈ A, 2 ≤ a)
    (hcase : A.sup id ≤ 2 * A.card ∨ 8 * A.card ^ 3 ≤ A.sup id ∨ ∀ a ∈ A, a.primeFactors.card ≤ 2)
    (m : ℕ) :
    Erdos708Covers A m (2 * A.card) := by
  have h1 : ∀ a ∈ A, 1 ≤ a := fun a ha => le_trans (by norm_num) (hA a ha)
  rcases hcase with hle | hge | hω
  · exact erdos708_two_n_of_le_2n h1 m hle
  · exact erdos708_two_n_of_ge_8n3 h1 m hge
  · exact erdos708_two_n_of_omega_le_two h1 hω m

/-- **Master Unconditional Upper-Bound Capstone for PPL 176 (Erdős Problem #708)**:
    Packages all unconditional upper bounds (both `ℕ` and `ℤ` intervals), sharp `2n`/`3n`/`kn`
    regimes, and the LP Weak Duality Certificate. -/
theorem ppl176_upper_master_summary :
    (∀ (A : Finset ℕ), (∀ a ∈ A, 2 ≤ a) →
      (A.sup id ≤ 2 * A.card ∨ 8 * A.card ^ 3 ≤ A.sup id ∨ ∀ a ∈ A, a.primeFactors.card ≤ 2) →
      ∀ m : ℕ, Erdos708Covers A m (2 * A.card)) ∧
    (∀ (A : Finset ℕ), (∀ a ∈ A, 2 ≤ a) → 9 * A.card ^ 2 ≤ A.sup id →
      ∀ m : ℕ, Erdos708Covers A m (3 * A.card)) ∧
    (∀ (A : Finset ℕ) (m k : ℕ), (∀ a ∈ A, 2 ≤ a) → 2 ≤ k →
      (k * A.card) ^ (k + 1) ≤ (A.sup id) ^ (k - 1) →
      Erdos708Covers A m (k * A.card)) ∧
    (∀ n : ℕ, Erdos708UpperBound n
      (3 * max 12 (Nat.sqrt (2 * Nat.log 2 n + 2) + 1) * n)) ∧
    (∀ n : ℕ, Erdos708UpperBound n
      (24 * max 16 (Nat.sqrt (Nat.log 2 n / max 1 (Nat.log 2 (Nat.log 2 n))) + 1) * n)) ∧
    (∀ n : ℕ, Erdos708UpperBoundInt n
      (24 * max 16 (Nat.sqrt (Nat.log 2 n / max 1 (Nat.log 2 (Nat.log 2 n))) + 1) * n)) := by
  refine ⟨fun A hA hc m => erdos708_two_n_three_regimes hA hc m,
    fun A hA hge m => erdos708_three_n_of_ge_9n2 (fun a ha => le_trans (by norm_num) (hA a ha)) m hge,
    fun A m k hA hk hM => erdos708_binpack_kn (fun a ha => le_trans (by norm_num) (hA a ha)) m k hk hM,
    erdos708_upper_sqrt_log,
    erdos708_upper_sqrt_log_div_loglog,
    erdos708_upper_sqrt_log_div_loglog_int⟩

/-- **`4n` Upper Bound for `M ≥ n²`** (3× sharper than Haoyu Chen's Sept 2026 Lean 4 record
    `12n`, and 9× lower threshold than `9 n²`). -/
theorem erdos708_four_n_ge_n2 {A : Finset ℕ} (hA : A.Nonempty) (hge2 : ∀ a ∈ A, 2 ≤ a)
    (hM : A.card ^ 2 ≤ A.max' hA) (m : ℕ) :
    ∃ B ⊆ Finset.Icc (m + 1) (m + A.max' hA),
      B.card ≤ 4 * A.card ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) := by
  have h1 : ∀ a ∈ A, 1 ≤ a := fun a ha => le_trans (by norm_num) (hge2 a ha)
  have hcov := erdos708_four_n_of_ge_n2 h1 m (by rwa [sup_id_eq_max' hA])
  simpa [Erdos708Covers, Erdos708Interval, sup_id_eq_max' hA] using hcov

/-- **`5n` Upper Bound for `M ≥ n^{7/4}`** (3× sharper than Haoyu Chen's Sept 2026 Lean 4
    record `15n`). -/
theorem erdos708_five_n_ge_n74 {A : Finset ℕ} (hA : A.Nonempty) (hge2 : ∀ a ∈ A, 2 ≤ a)
    (hM : A.card ^ 7 ≤ (A.max' hA) ^ 4) (m : ℕ) :
    ∃ B ⊆ Finset.Icc (m + 1) (m + A.max' hA),
      B.card ≤ 5 * A.card ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) := by
  have h1 : ∀ a ∈ A, 1 ≤ a := fun a ha => le_trans (by norm_num) (hge2 a ha)
  have hcov := erdos708_five_n_of_ge_n74 h1 m (by rwa [sup_id_eq_max' hA])
  simpa [Erdos708Covers, Erdos708Interval, sup_id_eq_max' hA] using hcov

/-- **`5n` Upper Bound for `M ≥ n^{5/3}`** (`|A|⁵ ≤ (max A)³`). -/
theorem erdos708_five_n_ge_n53 {A : Finset ℕ} (hA : A.Nonempty) (hge2 : ∀ a ∈ A, 2 ≤ a)
    (hM : A.card ^ 5 ≤ (A.max' hA) ^ 3) (m : ℕ) :
    ∃ B ⊆ Finset.Icc (m + 1) (m + A.max' hA),
      B.card ≤ 5 * A.card ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) := by
  have h1 : ∀ a ∈ A, 1 ≤ a := fun a ha => le_trans (by norm_num) (hge2 a ha)
  have hcov := erdos708_five_n_of_ge_n53 h1 m (by rwa [sup_id_eq_max' hA])
  simpa [Erdos708Covers, Erdos708Interval, sup_id_eq_max' hA] using hcov

/-- **`6n` Upper Bound for `M ≥ n^{3/2}`** (`|A|³ ≤ (max A)²`). -/
theorem erdos708_six_n_ge_n32 {A : Finset ℕ} (hA : A.Nonempty) (hge2 : ∀ a ∈ A, 2 ≤ a)
    (hM : A.card ^ 3 ≤ (A.max' hA) ^ 2) (m : ℕ) :
    ∃ B ⊆ Finset.Icc (m + 1) (m + A.max' hA),
      B.card ≤ 6 * A.card ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) := by
  have h1 : ∀ a ∈ A, 1 ≤ a := fun a ha => le_trans (by norm_num) (hge2 a ha)
  have hcov := erdos708_six_n_of_ge_n32 h1 m (by rwa [sup_id_eq_max' hA])
  simpa [Erdos708Covers, Erdos708Interval, sup_id_eq_max' hA] using hcov

/-- **Prefactor-Free Polynomial-Regime Bound (`M ≥ n^{1 + 1/k} → |B| ≤ (2k + 2) n`)**
    over arbitrary integer intervals `I ⊂ ℤ`. -/
theorem erdos708_two_k_plus_two_ge_root_int {A : Finset ℕ} (hA : A.Nonempty)
    (hge2 : ∀ a ∈ A, 2 ≤ a) (k : ℕ) (hk : 1 ≤ k)
    (hM : A.card ^ (k + 1) ≤ (A.max' hA) ^ k) (m : ℤ) :
    ∃ B ⊆ Finset.Ico m (m + (A.max' hA : ℤ)),
      B.card ≤ (2 * k + 2) * A.card ∧ ((∏ a ∈ A, a : ℕ) : ℤ) ∣ (∏ b ∈ B, b) := by
  have hcov := erdos708_coprime_dual_unit_int hA hge2 m k hk (by rwa [sup_id_eq_max' hA])
  simpa [Erdos708CoversInt, sup_id_eq_max' hA] using hcov

#print axioms erdos708_upper_sqrt_log
#print axioms erdos708_upper_sqrt_log_div_loglog
#print axioms erdos708_upper_sqrt_log_div_loglog_int
#print axioms erdos708_two_n_three_regimes
#print axioms erdos708_four_n_ge_n2
#print axioms erdos708_five_n_ge_n74
#print axioms erdos708_five_n_ge_n53
#print axioms erdos708_six_n_ge_n32
#print axioms erdos708_two_k_plus_two_ge_root_int
#print axioms ppl176_upper_master_summary

end PPL176
