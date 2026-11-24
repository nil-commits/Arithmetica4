import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

/-!
# PPL 049 (Kimberling #12 — Prime-Separator First-Row Gaps): Partial Structural Milestone

**Scope Notice (Partial Milestone — NOT the full open conjecture):**
Kimberling Problem #12 (OEIS `A129258`/`A129259`, asking whether the first-row differences
`T(1, n + 1) - T(1, n)` in Kimberling's Prime-Separator Array are bounded) remains **OPEN**.
This file formalizes the unconditionally proved structural results and the three exact proof
barriers documented in `scripts/ppl049_findings.md`:

1. **Exact Definition, Strict Interleaving & Maximality (§2.1–2.2):**
   - `kimRow n` (`T(1, n)`), `kimCol n` (`T(n, 1)`), and `kimT i j` (`T(i, j)`) matching the
     primary definition (`T(1,1) = 1`, greedy mex alternating row/column, `T(m, n) = T(m, 1) * T(1, n)`
     for `m, n ≥ 2`).
   - `kim_strict_interleaving`: `1 < kimRow n < kimCol n < kimRow (n + 1)` for all `n ≥ 2`.
   - `kimCol_le_two_mul_kimRow`: `kimCol n ≤ 2 * kimRow n` via Bertrand's postulate.
   - `kim_exact_partition`: `ℕ_{≥ 2} = R' ⊔ C' ⊔ (C' · R')` (disjoint union + exact maximality).
   - `kim_prime_inclusion` & `kim_semiprime_dichotomy`.
2. **Bounded Discrepancy & Dirichlet Convergence (§2.3):**
   - `kim_partial_sum_bounds` & `kim_discrepancy_le_one`: `∑_{m=2}^N kimSign m ∈ {0, 1}` and
     `|∑ m ∈ Finset.Icc a b, kimSign m| ≤ 1` for all `2 ≤ a ≤ b`.
   - `kim_dirichlet_real_converges`: for all real `σ > 0`, the partial sums of
     `∑_{m=2}^∞ kimSign m * m^(-σ)` converge to a limit `L` with `0 < L < 2^(-σ)`.
   - `kim_dirichlet_complex_converges`: partial sums of `∑_{m=2}^∞ kimSign m * (m : ℂ)^(-s)`
     converge for all `0 < s.re`.
3. **Three Exact Proof-Barrier Theorems (§3):**
   - **Barrier 1 (`barrier1_*`):** Periodic mod-7 model (`R_dir ≡ 3, 4`, `C_dir ≡ 2, 5 mod 7`) with
     disjoint products `C_dir · R_dir ≡ 1, 6 (mod 7)`, bounded gaps (`≤ 6` and `≤ 4`), strict
     discrepancy `≤ 1`, and exact equal density `2 / 7`.
   - **Barrier 2 (`barrier2_*`):** Balanced mod-3 completely multiplicative model for ANY prime
     partition `P_R ⊔ P_C`, proving disjointness, prime inclusion, exact maximality
     `ℕ_{≥ 2} = R₂ ⊔ C₂ ⊔ (C₂ · R₂)`, unconditional positive lower density, and (for the alternating
     prime-index partition `p_{2k} ∈ P_R`, `p_{2k+1} ∈ P_C`) divergent prime reciprocals on both sides.
   - **Barrier 3 (`barrier3_*`):** Finite-prefix immunity for every `M ≥ 2`: extending Kimberling's
     exact `(R', C', P)` classification on `[2, M]` to a full partition `ℕ_{≥ 2} = R'_M ⊔ C'_M ⊔ (C'_M · R'_M)`
     containing all primes and achieving explicit positive lower density on both `R'_M` and `C'_M`.
-/

namespace PPL049

section KimberlingArray

private lemma mexNotIn_nonempty (S : Finset ℕ) :
    ((Finset.Icc 1 (S.card + 1)).filter (· ∉ S)).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
  have hsub : Finset.Icc 1 (S.card + 1) ⊆ S := fun x hx => by
    by_contra hnot
    exact hne hx hnot
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  omega

/-- Least positive integer not in `S : Finset ℕ`. -/
def mexNotIn (S : Finset ℕ) : ℕ :=
  ((Finset.Icc 1 (S.card + 1)).filter (· ∉ S)).min' (mexNotIn_nonempty S)

lemma mexNotIn_pos (S : Finset ℕ) : 1 ≤ mexNotIn S := by
  have hmem := Finset.min'_mem ((Finset.Icc 1 (S.card + 1)).filter (· ∉ S)) (mexNotIn_nonempty S)
  rw [Finset.mem_filter, Finset.mem_Icc] at hmem
  exact hmem.1.1

lemma mexNotIn_notMem (S : Finset ℕ) : mexNotIn S ∉ S := by
  have hmem := Finset.min'_mem ((Finset.Icc 1 (S.card + 1)).filter (· ∉ S)) (mexNotIn_nonempty S)
  rw [Finset.mem_filter] at hmem
  exact hmem.2

lemma lt_mexNotIn_mem {S : Finset ℕ} {m : ℕ} (hm1 : 1 ≤ m) (hmlt : m < mexNotIn S) :
    m ∈ S := by
  have hmem := Finset.min'_mem ((Finset.Icc 1 (S.card + 1)).filter (· ∉ S)) (mexNotIn_nonempty S)
  rw [Finset.mem_filter, Finset.mem_Icc] at hmem
  have hbd : mexNotIn S ≤ S.card + 1 := hmem.1.2
  by_contra hnot
  have hm_in : m ∈ (Finset.Icc 1 (S.card + 1)).filter (· ∉ S) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, by omega⟩, hnot⟩
  have hle : mexNotIn S ≤ m := Finset.min'_le _ m hm_in
  omega

lemma mexNotIn_le_of_notMem {S : Finset ℕ} {m : ℕ} (hm1 : 1 ≤ m) (hm_not : m ∉ S) :
    mexNotIn S ≤ m := by
  by_contra hgt
  exact hm_not (lt_mexNotIn_mem hm1 (not_le.mp hgt))

lemma mexNotIn_lt_mexNotIn_insert (S : Finset ℕ) :
    mexNotIn S < mexNotIn (insert (mexNotIn S) S) := by
  set a := mexNotIn S
  set b := mexNotIn (insert a S)
  have hb1 : 1 ≤ b := mexNotIn_pos (insert a S)
  have hbnot : b ∉ insert a S := mexNotIn_notMem (insert a S)
  rw [Finset.mem_insert, not_or] at hbnot
  by_contra hle
  have hlt : b < a := lt_of_le_of_ne (not_lt.mp hle) hbnot.1
  exact hbnot.2 (lt_mexNotIn_mem hb1 hlt)

/-- Inductive state `(row1, col1, S(n))` of Kimberling's Prime-Separator Array at stage `n`. -/
def kimState : ℕ → (ℕ → ℕ) × (ℕ → ℕ) × Finset ℕ
  | 0 => (fun _ => 0, fun _ => 0, ∅)
  | 1 => (fun k => if k = 1 then 1 else 0, fun k => if k = 1 then 1 else 0, {1})
  | n + 2 =>
    let st := kimState (n + 1)
    let r := st.1
    let c := st.2.1
    let S := st.2.2
    let r_new := mexNotIn S
    let c_new := mexNotIn (insert r_new S)
    let r' := fun k => if k = n + 2 then r_new else r k
    let c' := fun k => if k = n + 2 then c_new else c k
    let S' :=
      insert r_new (insert c_new S) ∪
        ((Finset.Icc 2 (n + 1)).image (fun m => c m * r_new)) ∪
        ((Finset.Icc 2 (n + 1)).image (fun m => c_new * r m)) ∪
        {c_new * r_new}
    (r', c', S')

/-- First row `T(1, n)` of Kimberling's Prime-Separator Array (`kimRow 1 = 1`). -/
def kimRow (n : ℕ) : ℕ := (kimState n).1 n

/-- First column `T(n, 1)` of Kimberling's Prime-Separator Array (`kimCol 1 = 1`). -/
def kimCol (n : ℕ) : ℕ := (kimState n).2.1 n

/-- Full Kimberling Prime-Separator Array `T(i, j)` (`0` when `i = 0 ∨ j = 0`). -/
def kimT (i j : ℕ) : ℕ :=
  if i = 0 ∨ j = 0 then 0
  else if i = 1 ∧ j = 1 then 1
  else if i = 1 then kimRow j
  else if j = 1 then kimCol i
  else kimCol i * kimRow j

lemma kimState_stable : ∀ n k, k ≤ n →
    (kimState n).1 k = kimRow k ∧ (kimState n).2.1 k = kimCol k := by
  intro n
  induction n with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by omega
    exact ⟨rfl, rfl⟩
  | succ m ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · exact ⟨rfl, rfl⟩
    · cases m with
      | zero =>
        obtain rfl : k = 0 := by omega
        simp [kimState, kimRow, kimCol]
      | succ p =>
        have hk' : k ≤ p + 1 := by omega
        obtain ⟨hr, hc⟩ := ih k hk'
        have hne : k ≠ p + 2 := by omega
        dsimp [kimState]
        simp [hne, hr, hc]

lemma kimRow_one : kimRow 1 = 1 := rfl
lemma kimCol_one : kimCol 1 = 1 := rfl

lemma kimRow_succ_eq {n : ℕ} (hn : 1 ≤ n) :
    kimRow (n + 1) = mexNotIn (kimState n).2.2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp [kimRow, kimState]

lemma kimCol_succ_eq {n : ℕ} (hn : 1 ≤ n) :
    kimCol (n + 1) = mexNotIn (insert (kimRow (n + 1)) (kimState n).2.2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp [kimCol, kimRow, kimState]

lemma kimState_S_subset_succ (n : ℕ) (hn : 1 ≤ n) :
    (kimState n).2.2 ⊆ (kimState (n + 1)).2.2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  intro x hx
  dsimp [kimState]
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)

lemma kimState_S_mono {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (kimState a).2.2 ⊆ (kimState b).2.2 := by
  induction b, hab using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ k hk ih => exact Finset.Subset.trans ih (kimState_S_subset_succ k (by omega))

lemma kimState_S_eq_grid : ∀ n, 1 ≤ n →
    (kimState n).2.2 = ((Finset.Icc 1 n) ×ˢ (Finset.Icc 1 n)).image (fun ij => kimT ij.1 ij.2) := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      ext x
      simp [kimState, kimT]
    | succ p =>
      have ihm := ih (by omega)
      have hst_r : ∀ k ≤ p + 1, (kimState (p + 1)).1 k = kimRow k :=
        fun k hk => (kimState_stable (p + 1) k hk).1
      have hst_c : ∀ k ≤ p + 1, (kimState (p + 1)).2.1 k = kimCol k :=
        fun k hk => (kimState_stable (p + 1) k hk).2
      ext x
      dsimp [kimState]
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_product, Finset.mem_Icc]
      constructor
      · intro hx
        rcases hx with ((hx | hx) | hx) | hx
        · rcases hx with rfl | rfl | hx
          · refine ⟨(1, p + 2), ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ?_⟩
            simp [kimT, kimRow_succ_eq (by omega : 1 ≤ p + 1)]
          · refine ⟨(p + 2, 1), ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ?_⟩
            simp [kimT, kimCol_succ_eq (by omega : 1 ≤ p + 1), kimRow_succ_eq (by omega : 1 ≤ p + 1)]
          · rw [ihm] at hx
            rcases Finset.mem_image.mp hx with ⟨⟨i, j⟩, hij, rfl⟩
            rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hij
            exact ⟨(i, j), ⟨⟨hij.1.1, by omega⟩, ⟨hij.2.1, by omega⟩⟩, rfl⟩
        · rcases hx with ⟨m, hm, rfl⟩
          refine ⟨(m, p + 2), ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ?_⟩
          have hm0 : m ≠ 0 := by omega
          have hm1 : m ≠ 1 := by omega
          simp [kimT, hm0, hm1, hst_c m (by omega), kimRow_succ_eq (by omega : 1 ≤ p + 1)]
        · rcases hx with ⟨m, hm, rfl⟩
          refine ⟨(p + 2, m), ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ?_⟩
          have hm0 : m ≠ 0 := by omega
          have hm1 : m ≠ 1 := by omega
          simp [kimT, hm0, hm1, hst_r m (by omega), kimCol_succ_eq (by omega : 1 ≤ p + 1),
            kimRow_succ_eq (by omega : 1 ≤ p + 1)]
        · rcases hx with rfl
          refine ⟨(p + 2, p + 2), ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ?_⟩
          simp [kimT, kimCol_succ_eq (by omega : 1 ≤ p + 1), kimRow_succ_eq (by omega : 1 ≤ p + 1)]
      · rintro ⟨⟨i, j⟩, ⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩, rfl⟩
        rcases eq_or_lt_of_le hi2 with rfl | hi_lt <;>
        rcases eq_or_lt_of_le hj2 with rfl | hj_lt
        · right
          simp [kimT, kimCol_succ_eq (by omega : 1 ≤ p + 1), kimRow_succ_eq (by omega : 1 ≤ p + 1)]
        · rcases eq_or_lt_of_le hj1 with rfl | hj_gt1
          · left; left; left; right; left
            simp [kimT, kimCol_succ_eq (by omega : 1 ≤ p + 1), kimRow_succ_eq (by omega : 1 ≤ p + 1)]
          · left; right
            refine ⟨j, ⟨by omega, by omega⟩, ?_⟩
            have hj0 : j ≠ 0 := by omega
            have hj1' : j ≠ 1 := by omega
            simp [kimT, hj0, hj1', hst_r j (by omega), kimCol_succ_eq (by omega : 1 ≤ p + 1),
              kimRow_succ_eq (by omega : 1 ≤ p + 1)]
        · rcases eq_or_lt_of_le hi1 with rfl | hi_gt1
          · left; left; left; left
            simp [kimT, kimRow_succ_eq (by omega : 1 ≤ p + 1)]
          · left; left; right
            refine ⟨i, ⟨by omega, by omega⟩, ?_⟩
            have hi0 : i ≠ 0 := by omega
            have hi1' : i ≠ 1 := by omega
            simp [kimT, hi0, hi1', hst_c i (by omega), kimRow_succ_eq (by omega : 1 ≤ p + 1)]
        · left; left; left; right; right
          rw [ihm]
          exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_product.mpr
            ⟨Finset.mem_Icc.mpr ⟨hi1, by omega⟩, Finset.mem_Icc.mpr ⟨hj1, by omega⟩⟩, rfl⟩

lemma kimCol_mem_S {n : ℕ} (hn : 1 ≤ n) : kimCol n ∈ (kimState n).2.2 := by
  rw [kimState_S_eq_grid n hn]
  refine Finset.mem_image.mpr ⟨(n, 1), Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hn, le_rfl⟩, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩, ?_⟩
  by_cases hn1 : n = 1
  · subst hn1; simp [kimT, kimCol_one]
  · simp [kimT, hn1, show n ≠ 0 by omega]

lemma kimRow_mem_S {n : ℕ} (hn : 1 ≤ n) : kimRow n ∈ (kimState n).2.2 := by
  rw [kimState_S_eq_grid n hn]
  refine Finset.mem_image.mpr ⟨(1, n), Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨le_rfl, hn⟩, Finset.mem_Icc.mpr ⟨hn, le_rfl⟩⟩, ?_⟩
  by_cases hn1 : n = 1
  · subst hn1; simp [kimT, kimRow_one]
  · simp [kimT, hn1, show n ≠ 0 by omega]

lemma Icc_le_kimCol_subset_S : ∀ n, 1 ≤ n →
    ∀ m, 1 ≤ m → m ≤ kimCol n → m ∈ (kimState n).2.2 := by
  intro n hn m hm1 hmle
  rcases eq_or_lt_of_le hmle with rfl | hmlt
  · exact kimCol_mem_S hn
  · cases n with
    | zero => omega
    | succ p =>
      cases p with
      | zero => rw [kimCol_one] at hmlt; omega
      | succ q =>
        rw [kimCol_succ_eq (by omega)] at hmlt
        have hmem := lt_mexNotIn_mem hm1 hmlt
        rcases Finset.mem_insert.mp hmem with rfl | hmem'
        · exact kimRow_mem_S (by omega)
        · exact kimState_S_subset_succ (q + 1) (by omega) hmem'

/-- Theorem 1.1 (Strict Interleaving): For every `n ≥ 2`, `1 < T(1, n) < T(n, 1) < T(1, n + 1)`. -/
theorem kim_strict_interleaving {n : ℕ} (hn : 2 ≤ n) :
    1 < kimRow n ∧ kimRow n < kimCol n ∧ kimCol n < kimRow (n + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm1 : 1 ≤ m := by omega
  have h1r : 1 < kimRow (m + 1) := by
    rw [kimRow_succ_eq hm1]
    have h1S : 1 ∈ (kimState m).2.2 := by
      have := kimRow_mem_S (by omega : 1 ≤ 1)
      rw [kimRow_one] at this
      exact kimState_S_mono (by omega : 1 ≤ 1) hm1 this
    have hne : 1 ≠ mexNotIn (kimState m).2.2 := fun h =>
      mexNotIn_notMem (kimState m).2.2 (h ▸ h1S)
    have hpos := mexNotIn_pos (kimState m).2.2
    omega
  have hrc : kimRow (m + 1) < kimCol (m + 1) := by
    rw [kimRow_succ_eq hm1, kimCol_succ_eq hm1, kimRow_succ_eq hm1]
    exact mexNotIn_lt_mexNotIn_insert (kimState m).2.2
  have hcr : kimCol (m + 1) < kimRow (m + 2) := by
    rw [kimRow_succ_eq (by omega : 1 ≤ m + 1)]
    by_contra hle
    have hle' : mexNotIn (kimState (m + 1)).2.2 ≤ kimCol (m + 1) := not_lt.mp hle
    have hpos := mexNotIn_pos (kimState (m + 1)).2.2
    have hmem := Icc_le_kimCol_subset_S (m + 1) (by omega) _ hpos hle'
    exact mexNotIn_notMem (kimState (m + 1)).2.2 hmem
  exact ⟨h1r, hrc, hcr⟩

lemma kimRow_strictMono {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) : kimRow a < kimRow b := by
  induction b, hab using Nat.le_induction with
  | base =>
    have h := kim_strict_interleaving ha
    exact lt_trans h.2.1 h.2.2
  | succ k hk ih =>
    have h := kim_strict_interleaving (by omega : 2 ≤ k)
    exact lt_trans ih (lt_trans h.2.1 h.2.2)

lemma kimCol_strictMono {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) : kimCol a < kimCol b := by
  induction b, hab using Nat.le_induction with
  | base =>
    have h1 := kim_strict_interleaving ha
    have h2 := kim_strict_interleaving (by omega : 2 ≤ a + 1)
    exact lt_trans h1.2.2 h2.2.1
  | succ k hk ih =>
    have h := kim_strict_interleaving (by omega : 2 ≤ k)
    have h' := kim_strict_interleaving (by omega : 2 ≤ k + 1)
    exact lt_trans ih (lt_trans h.2.2 h'.2.1)

lemma kimRow_le_of_le {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) : kimRow a ≤ kimRow b := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact (kimRow_strictMono ha hlt).le

lemma kimCol_le_of_le {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) : kimCol a ≤ kimCol b := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact (kimCol_strictMono ha hlt).le

lemma ge_of_two_le_kimRow {n : ℕ} (hn : 2 ≤ n) : n ≤ kimRow n := by
  induction n, hn using Nat.le_induction with
  | base => exact (kim_strict_interleaving le_rfl).1
  | succ k hk ih =>
    have h := kim_strict_interleaving hk
    have h' := lt_trans h.2.1 h.2.2
    omega

/-- Small base values: `kimRow 2 = 2` and `kimCol 2 = 3`. -/
lemma kimRow_two : kimRow 2 = 2 := by
  rw [kimRow_succ_eq (by omega : 1 ≤ 1)]
  have h1 : 1 ∈ (kimState 1).2.2 := by simp [kimState]
  have h2 : 2 ∉ (kimState 1).2.2 := by simp [kimState]
  have hle := mexNotIn_le_of_notMem (by omega : 1 ≤ 2) h2
  have hpos := mexNotIn_pos (kimState 1).2.2
  have hne : mexNotIn (kimState 1).2.2 ≠ 1 := by
    intro h; apply mexNotIn_notMem (kimState 1).2.2; rw [h]; exact h1
  omega

lemma kimCol_two : kimCol 2 = 3 := by
  rw [kimCol_succ_eq (by omega : 1 ≤ 1), kimRow_two]
  have h1 : 1 ∈ insert 2 (kimState 1).2.2 := by simp [kimState]
  have h2 : 2 ∈ insert 2 (kimState 1).2.2 := by simp [kimState]
  have h3 : 3 ∉ insert 2 (kimState 1).2.2 := by simp [kimState]
  have hle := mexNotIn_le_of_notMem (by omega : 1 ≤ 3) h3
  have hpos := mexNotIn_pos (insert 2 (kimState 1).2.2)
  have hne1 : mexNotIn (insert 2 (kimState 1).2.2) ≠ 1 := by
    intro h; apply mexNotIn_notMem (insert 2 (kimState 1).2.2); rw [h]; exact h1
  have hne2 : mexNotIn (insert 2 (kimState 1).2.2) ≠ 2 := by
    intro h; apply mexNotIn_notMem (insert 2 (kimState 1).2.2); rw [h]; exact h2
  omega

lemma three_le_kimCol {n : ℕ} (hn : 2 ≤ n) : 3 ≤ kimCol n := by
  rw [← kimCol_two]
  exact kimCol_le_of_le (le_rfl : 2 ≤ 2) hn

/-- By Bertrand's postulate, every prime in `(r_n, 2 * r_n]` avoids `S(n-1) ∪ {r_n}`, so
`T(n, 1) ≤ 2 * T(1, n) < 3 * T(1, n)` for all `n ≥ 2`. -/
theorem kimCol_le_two_mul_kimRow {n : ℕ} (hn : 2 ≤ n) : kimCol n ≤ 2 * kimRow n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Nat.succ_eq_add_one] at hn ⊢
  have hm1 : 1 ≤ m := by omega
  have hr_pos : kimRow (m + 1) ≠ 0 := by
    have := (kim_strict_interleaving hn).1; omega
  obtain ⟨p, hp_prime, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul (kimRow (m + 1)) hr_pos
  have hp_not_mem : p ∉ insert (kimRow (m + 1)) (kimState m).2.2 := by
    rw [Finset.mem_insert, not_or]
    refine ⟨hp_gt.ne', ?_⟩
    rw [kimState_S_eq_grid m hm1, Finset.mem_image]
    rintro ⟨⟨i, j⟩, hij, hij_eq⟩
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hij
    by_cases hi1 : i = 1
    · subst hi1
      by_cases hj1 : j = 1
      · subst hj1
        simp [kimT] at hij_eq
        exact hp_prime.ne_one hij_eq.symm
      · have hj2 : 2 ≤ j := by omega
        simp [kimT, show j ≠ 0 by omega, hj1] at hij_eq
        have hlt : kimRow j < kimRow (m + 1) := kimRow_strictMono hj2 (by omega)
        omega
    · by_cases hj1 : j = 1
      · subst hj1
        have hi2 : 2 ≤ i := by omega
        simp [kimT, show i ≠ 0 by omega, hi1] at hij_eq
        have hci : kimCol i ≤ kimCol m := kimCol_le_of_le hi2 hij.1.2
        have hm2 : 2 ≤ m := by omega
        have hcm := (kim_strict_interleaving hm2).2.2
        omega
      · have hi2 : 2 ≤ i := by omega
        have hj2 : 2 ≤ j := by omega
        simp [kimT, show i ≠ 0 by omega, hi1, show j ≠ 0 by omega, hj1] at hij_eq
        have hci : 3 ≤ kimCol i := three_le_kimCol hi2
        have hrj : 2 ≤ kimRow j := (kim_strict_interleaving hj2).1
        have hmul : ¬ Nat.Prime (kimCol i * kimRow j) :=
          Nat.not_prime_mul (by omega) (by omega)
        exact hmul (hij_eq ▸ hp_prime)
  rw [kimCol_succ_eq hm1]
  have hle := mexNotIn_le_of_notMem hp_prime.one_lt.le hp_not_mem
  omega

/-- Predicates for `R'`, `C'`, and `P = C' · R'`. -/
def IsRow (m : ℕ) : Prop := ∃ n, 2 ≤ n ∧ kimRow n = m
def IsCol (m : ℕ) : Prop := ∃ n, 2 ≤ n ∧ kimCol n = m
def IsProd (m : ℕ) : Prop := ∃ c r, IsCol c ∧ IsRow r ∧ c * r = m

lemma isRow_not_isCol {m : ℕ} (hR : IsRow m) (hC : IsCol m) : False := by
  rcases hR with ⟨a, ha, rfl⟩
  rcases hC with ⟨b, hb, heq⟩
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have hrb := kimRow_strictMono ha hlt
    have hcb := (kim_strict_interleaving hb).2.1
    omega
  · have := (kim_strict_interleaving ha).2.1
    omega
  · have hcb := (kim_strict_interleaving hb).2.2
    have hrba := kimRow_le_of_le (by omega : 2 ≤ b + 1) (by omega : b + 1 ≤ a)
    omega

lemma isRow_not_isProd {m : ℕ} (hR : IsRow m) (hP : IsProd m) : False := by
  rcases hR with ⟨k, hk, rfl⟩
  rcases hP with ⟨c, r, ⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, heq⟩
  have hrj := (kim_strict_interleaving hj).1
  have hci := three_le_kimCol hi
  rcases le_total k (max i j) with hle | hgt
  · rcases le_max_iff.mp hle with hki | hkj
    · have hck : kimCol k ≤ kimCol i := kimCol_le_of_le hk hki
      have hrk := (kim_strict_interleaving hk).2.1
      have hmul : kimCol i * 2 ≤ kimCol i * kimRow j :=
        Nat.mul_le_mul_left (kimCol i) (by omega : 2 ≤ kimRow j)
      omega
    · have hrk : kimRow k ≤ kimRow j := kimRow_le_of_le hk hkj
      have hmul : 3 * kimRow j ≤ kimCol i * kimRow j := Nat.mul_le_mul_right _ hci
      omega
  · rcases eq_or_lt_of_le hgt with heqk | hlt_max
    · rcases max_cases i j with ⟨hm, _⟩ | ⟨hm, _⟩
      · have hki : k = i := heqk.symm.trans hm
        have hck : kimCol k ≤ kimCol i := by rw [hki]
        have hrk := (kim_strict_interleaving hk).2.1
        have hmul : kimCol i * 2 ≤ kimCol i * kimRow j :=
          Nat.mul_le_mul_left (kimCol i) (by omega : 2 ≤ kimRow j)
        omega
      · have hkj : k = j := heqk.symm.trans hm
        have hrk : kimRow k ≤ kimRow j := by rw [hkj]
        have hmul : 3 * kimRow j ≤ kimCol i * kimRow j := Nat.mul_le_mul_right _ hci
        omega
    · have hk1 : 1 ≤ k - 1 := by omega
      have hmax_le : max i j ≤ k - 1 := by omega
      have hmem_ij : kimCol i * kimRow j ∈ (kimState (max i j)).2.2 := by
        rw [kimState_S_eq_grid (max i j) (by omega)]
        refine Finset.mem_image.mpr ⟨(i, j), Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨by omega, le_max_left _ _⟩,
           Finset.mem_Icc.mpr ⟨by omega, le_max_right _ _⟩⟩, ?_⟩
        simp [kimT, show i ≠ 0 by omega, show i ≠ 1 by omega, show j ≠ 0 by omega, show j ≠ 1 by omega]
      have hmem_k1 : kimCol i * kimRow j ∈ (kimState (k - 1)).2.2 :=
        kimState_S_mono (by omega) hmax_le hmem_ij
      have hrk_eq : kimRow k = mexNotIn (kimState (k - 1)).2.2 := by
        rw [show k = (k - 1) + 1 by omega]
        exact kimRow_succ_eq hk1
      rw [heq, hrk_eq] at hmem_k1
      exact mexNotIn_notMem (kimState (k - 1)).2.2 hmem_k1

lemma isCol_not_isProd {m : ℕ} (hC : IsCol m) (hP : IsProd m) : False := by
  rcases hC with ⟨k, hk, rfl⟩
  rcases hP with ⟨c, r, ⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, heq⟩
  have hrj := (kim_strict_interleaving hj).1
  have hci := three_le_kimCol hi
  rcases le_total k (max i j) with hle | hgt
  · rcases le_max_iff.mp hle with hki | hkj
    · have hck : kimCol k ≤ kimCol i := kimCol_le_of_le hk hki
      have hmul : kimCol i * 2 ≤ kimCol i * kimRow j :=
        Nat.mul_le_mul_left (kimCol i) (by omega : 2 ≤ kimRow j)
      omega
    · have hck : kimCol k ≤ 2 * kimRow j := by
        calc
          kimCol k ≤ kimCol j := kimCol_le_of_le hk hkj
          _ ≤ 2 * kimRow j := kimCol_le_two_mul_kimRow hj
      have hmul : 3 * kimRow j ≤ kimCol i * kimRow j := Nat.mul_le_mul_right _ hci
      omega
  · rcases eq_or_lt_of_le hgt with heqk | hlt_max
    · rcases max_cases i j with ⟨hm, _⟩ | ⟨hm, _⟩
      · have hki : k = i := heqk.symm.trans hm
        have hck : kimCol k ≤ kimCol i := by rw [hki]
        have hmul : kimCol i * 2 ≤ kimCol i * kimRow j :=
          Nat.mul_le_mul_left (kimCol i) (by omega : 2 ≤ kimRow j)
        omega
      · have hkj : k = j := heqk.symm.trans hm
        have hck : kimCol k ≤ 2 * kimRow j := by
          rw [hkj]; exact kimCol_le_two_mul_kimRow hj
        have hmul : 3 * kimRow j ≤ kimCol i * kimRow j := Nat.mul_le_mul_right _ hci
        omega
    · have hk1 : 1 ≤ k - 1 := by omega
      have hmax_le : max i j ≤ k - 1 := by omega
      have hmem_ij : kimCol i * kimRow j ∈ (kimState (max i j)).2.2 := by
        rw [kimState_S_eq_grid (max i j) (by omega)]
        refine Finset.mem_image.mpr ⟨(i, j), Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨by omega, le_max_left _ _⟩,
           Finset.mem_Icc.mpr ⟨by omega, le_max_right _ _⟩⟩, ?_⟩
        simp [kimT, show i ≠ 0 by omega, show i ≠ 1 by omega, show j ≠ 0 by omega, show j ≠ 1 by omega]
      have hmem_k1 : kimCol i * kimRow j ∈ insert (kimRow k) (kimState (k - 1)).2.2 :=
        Finset.mem_insert_of_mem (kimState_S_mono (by omega) hmax_le hmem_ij)
      have hck_eq : kimCol k = mexNotIn (insert (kimRow k) (kimState (k - 1)).2.2) := by
        rw [show k = (k - 1) + 1 by omega]
        exact kimCol_succ_eq hk1
      rw [heq, hck_eq] at hmem_k1
      exact mexNotIn_notMem (insert (kimRow k) (kimState (k - 1)).2.2) hmem_k1

/-- Theorem 1.2 (Exact Partition & Maximality): Every `m ≥ 2` belongs to exact one of
`IsRow m`, `IsCol m`, or `IsProd m` (`C' · R'`). -/
theorem kim_exact_partition {m : ℕ} (hm : 2 ≤ m) :
    (IsRow m ∨ IsCol m ∨ IsProd m) ∧
    ¬ (IsRow m ∧ IsCol m) ∧ ¬ (IsRow m ∧ IsProd m) ∧ ¬ (IsCol m ∧ IsProd m) := by
  have hdisj : ¬ (IsRow m ∧ IsCol m) ∧ ¬ (IsRow m ∧ IsProd m) ∧ ¬ (IsCol m ∧ IsProd m) :=
    ⟨fun ⟨h1, h2⟩ => isRow_not_isCol h1 h2,
     fun ⟨h1, h2⟩ => isRow_not_isProd h1 h2,
     fun ⟨h1, h2⟩ => isCol_not_isProd h1 h2⟩
  refine ⟨?_, hdisj⟩
  have hm_le_row : m ≤ kimRow m := ge_of_two_le_kimRow hm
  have hm_le_col : m ≤ kimCol m := le_trans hm_le_row (kim_strict_interleaving hm).2.1.le
  have hmem : m ∈ (kimState m).2.2 := Icc_le_kimCol_subset_S m (by omega) m (by omega) hm_le_col
  rw [kimState_S_eq_grid m (by omega), Finset.mem_image] at hmem
  rcases hmem with ⟨⟨i, j⟩, hij, hij_eq⟩
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hij
  by_cases hi1 : i = 1
  · subst hi1
    by_cases hj1 : j = 1
    · subst hj1; simp [kimT] at hij_eq; omega
    · simp [kimT, show j ≠ 0 by omega, hj1] at hij_eq
      exact Or.inl ⟨j, by omega, hij_eq⟩
  · by_cases hj1 : j = 1
    · subst hj1
      simp [kimT, show i ≠ 0 by omega, hi1] at hij_eq
      exact Or.inr (Or.inl ⟨i, by omega, hij_eq⟩)
    · simp [kimT, show i ≠ 0 by omega, hi1, show j ≠ 0 by omega, hj1] at hij_eq
      exact Or.inr (Or.inr ⟨kimCol i, kimRow j, ⟨i, by omega, rfl⟩, ⟨j, by omega, rfl⟩, hij_eq⟩)

/-- Theorem 1.3 (Prime Inclusion): Every prime `p` lies in `R' ∪ C'`. -/
theorem kim_prime_inclusion {p : ℕ} (hp : p.Prime) : IsRow p ∨ IsCol p := by
  rcases (kim_exact_partition hp.two_le).1 with hR | hC | hP
  · exact Or.inl hR
  · exact Or.inr hC
  · exfalso
    rcases hP with ⟨c, r, ⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, heq⟩
    have hc : 2 ≤ kimCol i := by have := three_le_kimCol hi; omega
    have hr : 2 ≤ kimRow j := (kim_strict_interleaving hj).1
    exact Nat.not_prime_mul (by omega) (by omega) (heq ▸ hp)

/-- Theorem 1.4 (Semiprime Dichotomy): For primes `p, q`, `p * q ∈ P` iff one lies in `C'` and
the other in `R'`. -/
theorem kim_semiprime_dichotomy {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    IsProd (p * q) ↔ (IsRow p ∧ IsCol q) ∨ (IsCol p ∧ IsRow q) := by
  constructor
  · rintro ⟨c, r, hc, hr, heq⟩
    have hc2 : 2 ≤ c := by rcases hc with ⟨i, hi, rfl⟩; have := three_le_kimCol hi; omega
    have hr2 : 2 ≤ r := by rcases hr with ⟨j, hj, rfl⟩; exact (kim_strict_interleaving hj).1
    have hc_dvd : c ∣ p * q := ⟨r, heq.symm⟩
    rcases Nat.dvd_mul.mp hc_dvd with ⟨a, b, hap, hbq, rfl⟩
    rcases hp.eq_one_or_self_of_dvd a hap with ha1 | ha_eq <;>
    rcases hq.eq_one_or_self_of_dvd b hbq with hb1 | hb_eq
    · rw [ha1, hb1] at hc2; omega
    · rw [ha1, hb_eq, one_mul] at hc heq
      have hr_eq : r = p := mul_left_cancel₀ hq.ne_zero (by linarith [mul_comm p q])
      subst hr_eq; exact Or.inl ⟨hr, hc⟩
    · rw [ha_eq, hb1, mul_one] at hc heq
      have hr_eq : r = q := mul_left_cancel₀ hp.ne_zero heq
      subst hr_eq; exact Or.inr ⟨hc, hr⟩
    · rw [ha_eq, hb_eq] at heq
      exfalso
      have h1 : p * q * 1 < p * q * r := Nat.mul_lt_mul_of_pos_left (by omega) (Nat.mul_pos hp.pos hq.pos)
      omega
  · rintro (⟨hpR, hqC⟩ | ⟨hpC, hqR⟩)
    · exact ⟨q, p, hqC, hpR, mul_comm q p⟩
    · exact ⟨p, q, hpC, hqR, rfl⟩

end KimberlingArray

section DiscrepancyAndDirichlet

open scoped Topology Classical
open Filter

/-- Alternating sign function `f(m) = +1` on `R'`, `-1` on `C'`, `0` on `P` (and `0` for `m < 2`). -/
noncomputable def kimSign (m : ℕ) : ℝ :=
  if IsRow m then 1 else if IsCol m then -1 else 0

/-- Combined strictly increasing enumeration `u(k)` of `R' ∪ C'` (`k = 0, 1, ...`). -/
def kimU (k : ℕ) : ℕ :=
  if k % 2 = 0 then kimRow (k / 2 + 2) else kimCol (k / 2 + 2)

lemma kimU_step_lt (k : ℕ) : kimU k < kimU (k + 1) := by
  unfold kimU
  rcases Nat.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have h1 : (t + t) % 2 = 0 := by omega
    have h2 : (t + t + 1) % 2 = 1 := by omega
    have d1 : (t + t) / 2 = t := by omega
    have d2 : (t + t + 1) / 2 = t := by omega
    rw [h1, h2, d1, d2]
    exact (kim_strict_interleaving (by omega : 2 ≤ t + 2)).2.1
  · have h1 : (2 * t + 1) % 2 = 1 := by omega
    have h2 : (2 * t + 1 + 1) % 2 = 0 := by omega
    have d1 : (2 * t + 1) / 2 = t := by omega
    have d2 : (2 * t + 1 + 1) / 2 = t + 1 := by omega
    rw [h1, h2, d1, d2]
    simpa [Nat.add_assoc] using (kim_strict_interleaving (by omega : 2 ≤ t + 2)).2.2

lemma kimU_strictMono : StrictMono kimU :=
  strictMono_nat_of_lt_succ kimU_step_lt

lemma le_kimU (k : ℕ) : k + 2 ≤ kimU k := by
  induction k with
  | zero =>
    simp [kimU, kimRow_two]
  | succ k ih =>
    have := kimU_step_lt k
    omega

lemma kimU_even_iff (m : ℕ) : IsRow m ↔ ∃ k, Even k ∧ kimU k = m := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨2 * (n - 2), ⟨n - 2, by omega⟩, ?_⟩
    unfold kimU
    have hmod : (2 * (n - 2)) % 2 = 0 := by omega
    have hdiv : (2 * (n - 2)) / 2 + 2 = n := by omega
    rw [if_pos hmod, hdiv]
  · rintro ⟨k, ⟨t, rfl⟩, rfl⟩
    unfold kimU
    have hmod : (t + t) % 2 = 0 := by omega
    rw [if_pos hmod]
    exact ⟨(t + t) / 2 + 2, by omega, rfl⟩

lemma kimU_odd_iff (m : ℕ) : IsCol m ↔ ∃ k, Odd k ∧ kimU k = m := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨2 * (n - 2) + 1, ⟨n - 2, rfl⟩, ?_⟩
    unfold kimU
    have hmod : (2 * (n - 2) + 1) % 2 = 1 := by omega
    have hdiv : (2 * (n - 2) + 1) / 2 + 2 = n := by omega
    rw [if_neg (by omega : ¬ (2 * (n - 2) + 1) % 2 = 0), hdiv]
  · rintro ⟨k, ⟨t, rfl⟩, rfl⟩
    unfold kimU
    have hmod : ¬ (2 * t + 1) % 2 = 0 := by omega
    rw [if_neg hmod]
    exact ⟨(2 * t + 1) / 2 + 2, by omega, rfl⟩

lemma kimSign_eq_sum_even_odd (N : ℕ) :
    ∑ m ∈ Finset.Icc 2 N, kimSign m =
      ∑ k ∈ (Finset.range (N + 1)).filter (fun k => kimU k ≤ N),
        (if Even k then (1 : ℝ) else -1) := by
  have himg_split : ∀ m ∈ Finset.Icc 2 N,
      kimSign m =
        ∑ k ∈ (Finset.range (N + 1)).filter (fun k => kimU k ≤ N),
          (if kimU k = m then if Even k then (1 : ℝ) else -1 else 0) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    by_cases hR : IsRow m
    · have hC : ¬ IsCol m := fun h => isRow_not_isCol hR h
      obtain ⟨k, hk_even, rfl⟩ := (kimU_even_iff m).mp hR
      have hk_mem : k ∈ (Finset.range (N + 1)).filter (fun j => kimU j ≤ N) := by
        rw [Finset.mem_filter, Finset.mem_range]
        have := le_kimU k
        exact ⟨by omega, hm.2⟩
      rw [Finset.sum_eq_single k]
      · simp [kimSign, hR, hk_even]
      · intro j _ hjne
        have : kimU j ≠ kimU k := fun heq => hjne (kimU_strictMono.injective heq)
        simp [this]
      · intro hnot; exact absurd hk_mem hnot
    · by_cases hC : IsCol m
      · obtain ⟨k, hk_odd, rfl⟩ := (kimU_odd_iff m).mp hC
        have hk_not_even : ¬ Even k := Nat.not_even_iff_odd.mpr hk_odd
        have hk_mem : k ∈ (Finset.range (N + 1)).filter (fun j => kimU j ≤ N) := by
          rw [Finset.mem_filter, Finset.mem_range]
          have := le_kimU k
          exact ⟨by omega, hm.2⟩
        rw [Finset.sum_eq_single k]
        · simp [kimSign, hR, hC, hk_not_even]
        · intro j _ hjne
          have : kimU j ≠ kimU k := fun heq => hjne (kimU_strictMono.injective heq)
          simp [this]
        · intro hnot; exact absurd hk_mem hnot
      · have hzero : ∀ k, kimU k ≠ m := by
          intro k heq
          rcases Nat.even_or_odd k with hk_even | hk_odd
          · exact hR ((kimU_even_iff m).mpr ⟨k, hk_even, heq⟩)
          · exact hC ((kimU_odd_iff m).mpr ⟨k, hk_odd, heq⟩)
        rw [kimSign, if_neg hR, if_neg hC]
        simp [hzero]
  rw [Finset.sum_congr rfl himg_split, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hk
  have hk2 : 2 ≤ kimU k := by have := le_kimU k; omega
  have hmem : kimU k ∈ Finset.Icc 2 N := Finset.mem_Icc.mpr ⟨hk2, hk.2⟩
  rw [Finset.sum_eq_single (kimU k)]
  · simp
  · intro m _ hmne; simp [Ne.symm hmne]
  · intro hnot; exact absurd hmem hnot

private lemma alternating_sum_range (K : ℕ) :
    ∑ k ∈ Finset.range K, (if Even k then (1 : ℝ) else -1) =
      if Even K then 0 else 1 := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hk : Even k
    · have hk1 : ¬ Even (k + 1) := by rwa [Nat.even_add_one, not_not]
      simp [hk, hk1]
    · have hk1 : Even (k + 1) := by rwa [Nat.even_add_one]
      simp [hk, hk1]

/-- Theorem 2.1 (Partial Sums & Discrepancy `≤ 1`): For all `N`, `∑ m ∈ Icc 2 N, kimSign m ∈ {0, 1}`,
and for all `2 ≤ a`, `|∑ m ∈ Icc a b, kimSign m| ≤ 1`. -/
theorem kim_partial_sum_bounds (N : ℕ) :
    ∑ m ∈ Finset.Icc 2 N, kimSign m = 0 ∨ ∑ m ∈ Finset.Icc 2 N, kimSign m = 1 := by
  rw [kimSign_eq_sum_even_odd]
  set S := (Finset.range (N + 1)).filter (fun k => kimU k ≤ N)
  have hS_eq : S = Finset.range S.card := by
    by_cases hne : S = ∅
    · simp [hne]
    · have hdown : ∀ a b, b ∈ S → a < b → a ∈ S := by
        intro a b hb hab
        rw [Finset.mem_filter, Finset.mem_range] at hb ⊢
        exact ⟨by omega, le_trans (kimU_strictMono hab).le hb.2⟩
      have hsub : Finset.range S.card ⊆ S := by
        intro x hx
        rw [Finset.mem_range] at hx
        by_contra hnot
        have hlt_all : ∀ b ∈ S, b < x := by
          intro b hb
          by_contra hle
          rcases eq_or_lt_of_le (not_lt.mp hle) with rfl | hlt
          · exact hnot hb
          · exact hnot (hdown x b hb hlt)
        have hSsub : S ⊆ Finset.range x := fun b hb => Finset.mem_range.mpr (hlt_all b hb)
        have hcard := Finset.card_le_card hSsub
        rw [Finset.card_range] at hcard
        omega
      exact (Finset.eq_of_subset_of_card_le hsub (by simp)).symm
  rw [hS_eq, alternating_sum_range]
  by_cases hE : Even S.card <;> simp [hE]

theorem kim_discrepancy_le_one {a b : ℕ} (ha : 2 ≤ a) :
    |∑ m ∈ Finset.Icc a b, kimSign m| ≤ 1 := by
  rcases lt_or_ge b a with hlt | hle
  · have : Finset.Icc a b = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this, Finset.sum_empty, abs_zero]
    norm_num
  · have hsplit : Finset.Icc 2 b = Finset.Icc 2 (a - 1) ∪ Finset.Icc a b := by
      ext m
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    have hdisj : Disjoint (Finset.Icc 2 (a - 1)) (Finset.Icc a b) := by
      rw [Finset.disjoint_left]
      intro m hm1 hm2
      rw [Finset.mem_Icc] at hm1 hm2
      omega
    have hsum : ∑ m ∈ Finset.Icc 2 b, kimSign m =
        ∑ m ∈ Finset.Icc 2 (a - 1), kimSign m + ∑ m ∈ Finset.Icc a b, kimSign m := by
      rw [hsplit, Finset.sum_union hdisj]
    have h1 := kim_partial_sum_bounds b
    have h2 := kim_partial_sum_bounds (a - 1)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    · rw [h1, h2] at hsum
      rw [abs_le]
      constructor <;> linarith

private lemma sum_Ico_sub_tel (g : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ m ∈ Finset.Ico a b, (g m - g (m + 1)) = g a - g b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ k hle ih =>
    have hIco : Finset.Ico a (k + 1) = insert k (Finset.Ico a k) := by
      ext m; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hnot : k ∉ Finset.Ico a k := by simp
    rw [hIco, Finset.sum_insert hnot, ih]
    ring

private lemma abel_summation_by_parts {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → ℝ) (g : ℕ → E) (a b : ℕ) (ha2 : 2 ≤ a) (hab : a ≤ b) :
    ∑ m ∈ Finset.Icc a b, f m • g m =
      (∑ m ∈ Finset.Ico a b, (∑ k ∈ Finset.Icc 2 m, f k) • (g m - g (m + 1))) +
        (∑ k ∈ Finset.Icc 2 b, f k) • g b -
        (∑ k ∈ Finset.Icc 2 (a - 1), f k) • g a := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton, Finset.Ico_self, Finset.sum_empty, zero_add]
    have hsplit : Finset.Icc 2 a = insert a (Finset.Icc 2 (a - 1)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : a ∉ Finset.Icc 2 (a - 1) := by
      simp only [Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert hnot, add_smul]
    abel
  | succ k hle ih =>
    have hIcc : Finset.Icc a (k + 1) = insert (k + 1) (Finset.Icc a k) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hIco : Finset.Ico a (k + 1) = insert k (Finset.Ico a k) := by
      ext m; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hIcc2 : Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot1 : k + 1 ∉ Finset.Icc a k := by simp
    have hnot2 : k ∉ Finset.Ico a k := by simp
    have hnot3 : k + 1 ∉ Finset.Icc 2 k := by simp
    rw [hIcc, Finset.sum_insert hnot1, ih, hIco, Finset.sum_insert hnot2,
      hIcc2, Finset.sum_insert hnot3, add_smul, smul_sub]
    abel

private lemma partial_sum_kimSign_bound {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b)
    (g : ℕ → ℝ) (hg_nonneg : ∀ m, 0 ≤ g m) (hg_anti : ∀ m, a ≤ m → g (m + 1) ≤ g m) :
    |∑ m ∈ Finset.Icc a b, kimSign m * g m| ≤ g a := by
  have hab_eq := abel_summation_by_parts kimSign g a b ha hab
  simp only [smul_eq_mul] at hab_eq
  rw [hab_eq]
  set S : ℕ → ℝ := fun m => ∑ k ∈ Finset.Icc 2 m, kimSign k
  have hS01 : ∀ m, 0 ≤ S m ∧ S m ≤ 1 := fun m => by
    rcases kim_partial_sum_bounds m with h | h <;> dsimp [S] <;> rw [h] <;> norm_num
  have hsum_lo : 0 ≤ ∑ m ∈ Finset.Ico a b, S m * (g m - g (m + 1)) := by
    refine Finset.sum_nonneg fun m hm => ?_
    rw [Finset.mem_Ico] at hm
    exact mul_nonneg (hS01 m).1 (sub_nonneg.mpr (hg_anti m hm.1))
  have hsum_hi : ∑ m ∈ Finset.Ico a b, S m * (g m - g (m + 1)) ≤ g a - g b := by
    calc
      ∑ m ∈ Finset.Ico a b, S m * (g m - g (m + 1))
          ≤ ∑ m ∈ Finset.Ico a b, (g m - g (m + 1)) := by
            refine Finset.sum_le_sum fun m hm => ?_
            rw [Finset.mem_Ico] at hm
            have hdiff : 0 ≤ g m - g (m + 1) := sub_nonneg.mpr (hg_anti m hm.1)
            calc
              S m * (g m - g (m + 1)) ≤ 1 * (g m - g (m + 1)) :=
                mul_le_mul_of_nonneg_right (hS01 m).2 hdiff
              _ = g m - g (m + 1) := one_mul _
      _ = g a - g b := sum_Ico_sub_tel g a b hab
  have hb_lo : 0 ≤ S b * g b := mul_nonneg (hS01 b).1 (hg_nonneg b)
  have hb_hi : S b * g b ≤ g b := by
    calc
      S b * g b ≤ 1 * g b := mul_le_mul_of_nonneg_right (hS01 b).2 (hg_nonneg b)
      _ = g b := one_mul _
  have ha_lo : 0 ≤ S (a - 1) * g a := mul_nonneg (hS01 (a - 1)).1 (hg_nonneg a)
  have ha_hi : S (a - 1) * g a ≤ g a := by
    calc
      S (a - 1) * g a ≤ 1 * g a := mul_le_mul_of_nonneg_right (hS01 (a - 1)).2 (hg_nonneg a)
      _ = g a := one_mul _
  rw [abs_le]
  constructor <;> linarith

/-- Theorem 2.2 (Real Dirichlet Convergence & Positivity/Upper Bound):
For every real `σ > 0`, the conditionally convergent alternating Dirichlet series
`F(σ) = ∑_{m=2}^∞ kimSign m * m^(-σ)` converges to a limit `L ∈ (0, 2^(-σ))`. -/
theorem kim_dirichlet_real_converges {σ : ℝ} (hσ : 0 < σ) :
    ∃ L : ℝ,
      Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc 2 N, kimSign m * (m : ℝ) ^ (-σ)) atTop (𝓝 L) ∧
      0 < L ∧ L < (2 : ℝ) ^ (-σ) := by
  set F : ℕ → ℝ := fun N => ∑ m ∈ Finset.Icc 2 N, kimSign m * (m : ℝ) ^ (-σ)
  set g : ℕ → ℝ := fun m => (m : ℝ) ^ (-σ)
  have hg_nonneg : ∀ m, 0 ≤ g m := fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hg_anti : ∀ m, 1 ≤ m → g (m + 1) ≤ g m := fun m hm => by
    dsimp [g]
    have hm_pos : (0 : ℝ) < m := by positivity
    have hle : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
    exact Real.rpow_le_rpow_of_nonpos hm_pos hle (by linarith)
  have htend_g : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) ^ σ)⁻¹) atTop (𝓝 0) :=
      (tendsto_rpow_atTop hσ).comp tendsto_natCast_atTop_atTop |>.inv_tendsto_atTop
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [g]
    rw [Real.rpow_neg (by positivity)]
  have hcauchy : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    rw [Metric.tendsto_atTop] at htend_g
    obtain ⟨N, hN⟩ := htend_g ε hε
    refine ⟨max N 2, fun p hp q hq => ?_⟩
    wlog hpq : p ≤ q generalizing p q
    · rw [dist_comm]; exact this q hq p hp (le_of_not_ge hpq)
    rcases eq_or_lt_of_le hpq with rfl | hlt
    · simpa using hε
    · have hsplit : Finset.Icc 2 q = Finset.Icc 2 p ∪ Finset.Icc (p + 1) q := by
        ext m; simp only [Finset.mem_union, Finset.mem_Icc]; omega
      have hdisj : Disjoint (Finset.Icc 2 p) (Finset.Icc (p + 1) q) := by
        rw [Finset.disjoint_left]; intro m hm1 hm2
        rw [Finset.mem_Icc] at hm1 hm2; omega
      have hdiff : F q - F p = ∑ m ∈ Finset.Icc (p + 1) q, kimSign m * g m := by
        dsimp [F]
        rw [hsplit, Finset.sum_union hdisj, add_sub_cancel_left]
      rw [Real.dist_eq, abs_sub_comm, hdiff]
      have hbd := partial_sum_kimSign_bound (by omega : 2 ≤ p + 1) (by omega : p + 1 ≤ q) g
        hg_nonneg (fun m hm => hg_anti m (by omega))
      have hNp : dist (g (p + 1)) 0 < ε := hN (p + 1) (by omega)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hg_nonneg (p + 1))] at hNp
      linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hS1 : ∑ k ∈ Finset.Icc 2 1, kimSign k = 0 := by simp
  have hkim2 : IsRow 2 := ⟨2, le_rfl, kimRow_two⟩
  have hkim3 : IsCol 3 := ⟨2, le_rfl, kimCol_two⟩
  have hS2 : ∑ k ∈ Finset.Icc 2 2, kimSign k = 1 := by
    rw [Finset.Icc_self, Finset.sum_singleton, kimSign, if_pos hkim2]
  have hS3 : ∑ k ∈ Finset.Icc 2 3, kimSign k = 0 := by
    have hI : Finset.Icc 2 3 = {2, 3} := by decide
    have h3not : ¬ IsRow 3 := fun h => isRow_not_isCol h hkim3
    rw [hI, Finset.sum_pair (by decide), kimSign, if_pos hkim2, kimSign, if_neg h3not, if_pos hkim3]
    norm_num
  have hFN_bounds : ∀ N, 4 ≤ N → g 2 - g 3 ≤ F N ∧ F N ≤ g 2 - (g 3 - g 4) := by
    intro N hN4
    have hab := abel_summation_by_parts kimSign g 2 N le_rfl (by omega)
    simp only [smul_eq_mul] at hab
    change F N = (∑ m ∈ Finset.Ico 2 N, (∑ k ∈ Finset.Icc 2 m, kimSign k) * (g m - g (m + 1))) +
      (∑ k ∈ Finset.Icc 2 N, kimSign k) * g N - (∑ k ∈ Finset.Icc 2 1, kimSign k) * g 2 at hab
    rw [hS1, zero_mul, sub_zero] at hab
    set S : ℕ → ℝ := fun m => ∑ k ∈ Finset.Icc 2 m, kimSign k
    have hS01 : ∀ m, 0 ≤ S m ∧ S m ≤ 1 := fun m => by
      rcases kim_partial_sum_bounds m with h | h <;> dsimp [S] <;> rw [h] <;> norm_num
    have hIco_split : Finset.Ico 2 N = insert 2 (insert 3 (Finset.Ico 4 N)) := by
      ext m; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have h2not : 2 ∉ insert 3 (Finset.Ico 4 N) := by simp
    have h3not : 3 ∉ Finset.Ico 4 N := by simp
    rw [hIco_split, Finset.sum_insert h2not, Finset.sum_insert h3not] at hab
    have hS2' : ∑ k ∈ Finset.Icc 2 2, kimSign k = 1 := hS2
    have hS3' : ∑ k ∈ Finset.Icc 2 3, kimSign k = 0 := hS3
    rw [hS2', hS3', one_mul, zero_mul, zero_add] at hab
    have hrest_nonneg : 0 ≤ ∑ m ∈ Finset.Ico 4 N, S m * (g m - g (m + 1)) := by
      refine Finset.sum_nonneg fun m hm => ?_
      rw [Finset.mem_Ico] at hm
      exact mul_nonneg (hS01 m).1 (sub_nonneg.mpr (hg_anti m (by omega)))
    have hrest_le : ∑ m ∈ Finset.Ico 4 N, S m * (g m - g (m + 1)) ≤ g 4 - g N := by
      calc
        ∑ m ∈ Finset.Ico 4 N, S m * (g m - g (m + 1))
            ≤ ∑ m ∈ Finset.Ico 4 N, (g m - g (m + 1)) := by
              refine Finset.sum_le_sum fun m hm => ?_
              rw [Finset.mem_Ico] at hm
              have hdiff := sub_nonneg.mpr (hg_anti m (by omega))
              calc
                S m * (g m - g (m + 1)) ≤ 1 * (g m - g (m + 1)) :=
                  mul_le_mul_of_nonneg_right (hS01 m).2 hdiff
                _ = g m - g (m + 1) := one_mul _
        _ = g 4 - g N := sum_Ico_sub_tel g 4 N hN4
    have hSN_nonneg : 0 ≤ S N * g N := mul_nonneg (hS01 N).1 (hg_nonneg N)
    have hSN_le : S N * g N ≤ g N := by
      calc
        S N * g N ≤ 1 * g N := mul_le_mul_of_nonneg_right (hS01 N).2 (hg_nonneg N)
        _ = g N := one_mul _
    dsimp [S] at hrest_nonneg hrest_le hSN_nonneg hSN_le
    constructor <;> linarith
  have hL_lo : g 2 - g 3 ≤ L :=
    ge_of_tendsto hL (eventually_atTop.mpr ⟨4, fun N hN => (hFN_bounds N hN).1⟩)
  have hL_hi : L ≤ g 2 - (g 3 - g 4) :=
    le_of_tendsto hL (eventually_atTop.mpr ⟨4, fun N hN => (hFN_bounds N hN).2⟩)
  have hg23 : g 3 < g 2 := by
    dsimp [g]; exact Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) (by linarith)
  have hg34 : g 4 < g 3 := by
    dsimp [g]; exact Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) (by linarith)
  dsimp [g] at hL_lo hL_hi hg23 hg34
  norm_num at hL_lo hL_hi hg23 hg34
  exact ⟨L, hL, by linarith, by linarith⟩

/-- Theorem 2.3 (Complex Dirichlet Convergence for `Re(s) > 0`):
For every `s : ℂ` with `0 < s.re`, the Dirichlet series `∑_{m=2}^∞ kimSign m * (m : ℂ)^(-s)`
converges. -/
theorem kim_dirichlet_complex_converges {s : ℂ} (hs : 0 < s.re) :
    ∃ L : ℂ, Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc 2 N, (kimSign m : ℂ) * (m : ℂ) ^ (-s))
      atTop (𝓝 L) := by
  set F : ℕ → ℂ := fun N => ∑ m ∈ Finset.Icc 2 N, (kimSign m : ℂ) * (m : ℂ) ^ (-s)
  set g : ℕ → ℂ := fun m => (m : ℂ) ^ (-s)
  have hdiff_bound : ∀ m : ℕ, 1 ≤ m → ‖g m - g (m + 1)‖ ≤ ‖s‖ * (m : ℝ) ^ (-s.re - 1) := by
    intro m hm
    have hconv : Convex ℝ (Set.Icc (m : ℝ) ((m + 1 : ℕ) : ℝ)) := convex_Icc _ _
    have hderiv : ∀ t ∈ Set.Icc (m : ℝ) ((m + 1 : ℕ) : ℝ),
        HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) (-s * (t : ℂ) ^ (-s - 1)) t := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le (by positivity) ht.1
      have hslit : (t : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr ht_pos
      have hcp := ((hasDerivAt_id (t : ℂ)).cpow_const hslit (c := -s)).comp_ofReal
      simpa using hcp
    have hbound : ∀ t ∈ Set.Icc (m : ℝ) ((m + 1 : ℕ) : ℝ),
        ‖-s * (t : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * (m : ℝ) ^ (-s.re - 1) := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le (by positivity) ht.1
      rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
      exact Real.rpow_le_rpow_of_nonpos (by positivity) ht.1 (by linarith)
    have hmv := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hderiv t ht).hasDerivWithinAt) hbound
      (Set.left_mem_Icc.mpr (by exact_mod_cast Nat.le_succ m))
      (Set.right_mem_Icc.mpr (by exact_mod_cast Nat.le_succ m))
    have hsub_len : ‖((m + 1 : ℕ) : ℝ) - (m : ℝ)‖ = 1 := by
      push_cast; simp
    have hnorm_symm : ‖g m - g (m + 1)‖ = ‖(g (m + 1) - g m)‖ := norm_sub_rev _ _
    dsimp [g] at hnorm_symm ⊢
    rw [hnorm_symm]
    calc
      ‖((m + 1 : ℕ) : ℂ) ^ (-s) - (m : ℂ) ^ (-s)‖
          ≤ ‖s‖ * (m : ℝ) ^ (-s.re - 1) * ‖((m + 1 : ℕ) : ℝ) - (m : ℝ)‖ := by
            simpa using hmv
      _ = ‖s‖ * (m : ℝ) ^ (-s.re - 1) := by rw [hsub_len, mul_one]
  have hs_sum : Summable (fun m : ℕ => ‖s‖ * (m : ℝ) ^ (-s.re - 1)) := by
    have h1 : Summable (fun m : ℕ => ((m : ℝ) ^ (s.re + 1))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by linarith)
    refine (h1.mul_left ‖s‖).congr fun m => ?_
    rw [← Real.rpow_neg (Nat.cast_nonneg m), show -(s.re + 1) = -s.re - 1 by ring]
  have hnorm_g_tend : Tendsto (fun m : ℕ => ‖g m‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) ^ s.re)⁻¹) atTop (𝓝 0) :=
      (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop |>.inv_tendsto_atTop
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    dsimp [g]
    have hm_pos : (0 : ℝ) < m := by positivity
    symm
    rw [show (m : ℂ) = ((m : ℝ) : ℂ) by norm_cast, Complex.norm_cpow_eq_rpow_re_of_pos hm_pos,
      Complex.neg_re, Real.rpow_neg hm_pos.le]
  have hcauchy : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have htail := (summable_iff_vanishing_norm.mp hs_sum) (ε / 3) (by linarith)
    have hnorm_ev : ∀ᶠ n in atTop, ‖g n‖ < ε / 3 :=
      hnorm_g_tend.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3))
    rw [eventually_atTop] at hnorm_ev
    obtain ⟨N₁, hN₁⟩ := hnorm_ev
    obtain ⟨S₀, hS₀⟩ := htail
    set N := max (max N₁ 2) (S₀.sup id + 1)
    refine ⟨N, fun p hp q hq => ?_⟩
    wlog hpq : p ≤ q generalizing p q
    · rw [dist_comm]; exact this q hq p hp (le_of_not_ge hpq)
    rcases eq_or_lt_of_le hpq with rfl | hlt
    · simpa using hε
    · have hsplit : Finset.Icc 2 q = Finset.Icc 2 p ∪ Finset.Icc (p + 1) q := by
        ext m; simp only [Finset.mem_union, Finset.mem_Icc]; omega
      have hdisj : Disjoint (Finset.Icc 2 p) (Finset.Icc (p + 1) q) := by
        rw [Finset.disjoint_left]; intro m hm1 hm2
        rw [Finset.mem_Icc] at hm1 hm2; omega
      have hdiff : F q - F p = ∑ m ∈ Finset.Icc (p + 1) q, kimSign m • g m := by
        dsimp [F]
        rw [hsplit, Finset.sum_union hdisj, add_sub_cancel_left]
      rw [dist_eq_norm, norm_sub_rev, hdiff]
      have hab := abel_summation_by_parts kimSign g (p + 1) q (by omega) (by omega)
      rw [hab]
      set S : ℕ → ℝ := fun m => ∑ k ∈ Finset.Icc 2 m, kimSign k
      have hS_norm : ∀ m, |S m| ≤ 1 := fun m => by
        rcases kim_partial_sum_bounds m with h | h <;> dsimp [S] <;> rw [h] <;> norm_num
      have h1 : ‖∑ m ∈ Finset.Ico (p + 1) q, S m • (g m - g (m + 1))‖ ≤
          ∑ m ∈ Finset.Ico (p + 1) q, ‖s‖ * (m : ℝ) ^ (-s.re - 1) := by
        calc
          ‖∑ m ∈ Finset.Ico (p + 1) q, S m • (g m - g (m + 1))‖
              ≤ ∑ m ∈ Finset.Ico (p + 1) q, ‖S m • (g m - g (m + 1))‖ := norm_sum_le _ _
          _ ≤ ∑ m ∈ Finset.Ico (p + 1) q, ‖s‖ * (m : ℝ) ^ (-s.re - 1) := by
              refine Finset.sum_le_sum fun m hm => ?_
              rw [Finset.mem_Ico] at hm
              rw [norm_smul, Real.norm_eq_abs]
              calc
                |S m| * ‖g m - g (m + 1)‖ ≤ 1 * ‖g m - g (m + 1)‖ :=
                  mul_le_mul_of_nonneg_right (hS_norm m) (norm_nonneg _)
                _ = ‖g m - g (m + 1)‖ := one_mul _
                _ ≤ ‖s‖ * (m : ℝ) ^ (-s.re - 1) := hdiff_bound m (by omega)
      have hdisj_S0 : Disjoint (Finset.Ico (p + 1) q) S₀ := by
        rw [Finset.disjoint_left]
        intro m hm2 hm1
        rw [Finset.mem_Ico] at hm2
        have hle := Finset.le_sup (f := id) hm1
        dsimp at hle
        omega
      have htail_bd : ∑ m ∈ Finset.Ico (p + 1) q, ‖s‖ * (m : ℝ) ^ (-s.re - 1) < ε / 3 := by
        have := hS₀ (Finset.Ico (p + 1) q) hdisj_S0
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun m _ =>
          mul_nonneg (norm_nonneg s) (Real.rpow_nonneg (Nat.cast_nonneg m) _))] at this
        exact this
      have h2 : ‖S q • g q‖ < ε / 3 := by
        rw [norm_smul, Real.norm_eq_abs]
        have := hN₁ q (by omega)
        nlinarith [hS_norm q, norm_nonneg (g q)]
      have h3 : ‖S p • g (p + 1)‖ < ε / 3 := by
        rw [norm_smul, Real.norm_eq_abs]
        have := hN₁ (p + 1) (by omega)
        nlinarith [hS_norm p, norm_nonneg (g (p + 1))]
      have htri : ‖(∑ m ∈ Finset.Ico (p + 1) q, S m • (g m - g (m + 1))) + S q • g q - S p • g (p + 1)‖ ≤
          ‖∑ m ∈ Finset.Ico (p + 1) q, S m • (g m - g (m + 1))‖ + ‖S q • g q‖ + ‖S p • g (p + 1)‖ := by
        calc
          ‖(∑ m ∈ Finset.Ico (p + 1) q, S m • (g m - g (m + 1))) + S q • g q - S p • g (p + 1)‖
              ≤ ‖(∑ m ∈ Finset.Ico (p + 1) q, S m • (g m - g (m + 1))) + S q • g q‖ + ‖S p • g (p + 1)‖ :=
                norm_sub_le _ _
          _ ≤ ‖∑ m ∈ Finset.Ico (p + 1) q, S m • (g m - g (m + 1))‖ + ‖S q • g q‖ + ‖S p • g (p + 1)‖ := by
                gcongr; exact norm_add_le _ _
      dsimp [S] at h1 h2 h3 htri
      rw [show p + 1 - 1 = p by omega]
      simp only [Complex.real_smul] at *
      linarith
  exact cauchySeq_tendsto_of_complete hcauchy

end DiscrepancyAndDirichlet

section Barrier1_Mod7

/-- Periodic cubic-character countermodel mod `7`: `R_dir ≡ 3, 4 (mod 7)`, `C_dir ≡ 2, 5 (mod 7)`. -/
def Rdir (m : ℕ) : Prop := 2 ≤ m ∧ (m % 7 = 3 ∨ m % 7 = 4)
def Cdir (m : ℕ) : Prop := 2 ≤ m ∧ (m % 7 = 2 ∨ m % 7 = 5)

instance : DecidablePred Rdir := fun m => inferInstanceAs (Decidable (2 ≤ m ∧ (m % 7 = 3 ∨ m % 7 = 4)))
instance : DecidablePred Cdir := fun m => inferInstanceAs (Decidable (2 ≤ m ∧ (m % 7 = 2 ∨ m % 7 = 5)))

theorem barrier1_disjoint (m : ℕ) : ¬ (Rdir m ∧ Cdir m) := by
  rintro ⟨⟨_, hR⟩, ⟨_, hC⟩⟩
  omega

theorem barrier1_prod_disjoint {c r : ℕ} (hc : Cdir c) (hr : Rdir r) :
    ¬ Rdir (c * r) ∧ ¬ Cdir (c * r) := by
  have hmod : (c * r) % 7 = ((c % 7) * (r % 7)) % 7 := Nat.mul_mod c r 7
  rcases hc.2 with hc' | hc' <;> rcases hr.2 with hr' | hr' <;>
  · rw [hc', hr'] at hmod
    norm_num at hmod
    constructor <;> rintro ⟨_, h⟩ <;> omega

theorem barrier1_bounded_gaps :
    (∀ m, Rdir m → ∃ m', m < m' ∧ m' ≤ m + 6 ∧ Rdir m') ∧
    (∀ m, Cdir m → ∃ m', m < m' ∧ m' ≤ m + 4 ∧ Cdir m') := by
  constructor
  · rintro m ⟨hm, hm3 | hm4⟩
    · exact ⟨m + 1, by omega, by omega, ⟨by omega, Or.inr (by omega)⟩⟩
    · exact ⟨m + 6, by omega, by omega, ⟨by omega, Or.inl (by omega)⟩⟩
  · rintro m ⟨hm, hm2 | hm5⟩
    · exact ⟨m + 3, by omega, by omega, ⟨by omega, Or.inr (by omega)⟩⟩
    · exact ⟨m + 4, by omega, by omega, ⟨by omega, Or.inl (by omega)⟩⟩

private lemma barrier1_period_count (q : ℕ) :
    ((Finset.Icc 1 (7 * q)).filter Rdir).card = 2 * q ∧
    ((Finset.Icc 1 (7 * q)).filter Cdir).card = 2 * q := by
  induction q with
  | zero => simp
  | succ k ih =>
    have hsplit : Finset.Icc 1 (7 * (k + 1)) =
        Finset.Icc 1 (7 * k) ∪ Finset.Icc (7 * k + 1) (7 * k + 7) := by
      ext m; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hdisj : Disjoint (Finset.Icc 1 (7 * k)) (Finset.Icc (7 * k + 1) (7 * k + 7)) := by
      rw [Finset.disjoint_left]; intro m hm1 hm2
      rw [Finset.mem_Icc] at hm1 hm2; omega
    have hblockR : ((Finset.Icc (7 * k + 1) (7 * k + 7)).filter Rdir).card = 2 := by
      have hset : (Finset.Icc (7 * k + 1) (7 * k + 7)).filter Rdir = {7 * k + 3, 7 * k + 4} := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
          Finset.mem_singleton, Rdir]; omega
      rw [hset, Finset.card_pair (by omega)]
    have hblockC : ((Finset.Icc (7 * k + 1) (7 * k + 7)).filter Cdir).card = 2 := by
      have hset : (Finset.Icc (7 * k + 1) (7 * k + 7)).filter Cdir = {7 * k + 2, 7 * k + 5} := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
          Finset.mem_singleton, Cdir]; omega
      rw [hset, Finset.card_pair (by omega)]
    rw [hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      Finset.filter_union,
      Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      ih.1, ih.2, hblockR, hblockC]
    omega

theorem barrier1_discrepancy_le_one (x : ℕ) :
    Int.natAbs ((((Finset.Icc 1 x).filter Rdir).card : ℤ) - ((Finset.Icc 1 x).filter Cdir).card) ≤ 1 := by
  set q := x / 7
  set r := x % 7
  have hqr : x = 7 * q + r := (Nat.div_add_mod x 7).symm
  have hr : r < 7 := Nat.mod_lt x (by omega)
  have hsplit : Finset.Icc 1 x = Finset.Icc 1 (7 * q) ∪ Finset.Icc (7 * q + 1) (7 * q + r) := by
    ext m; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 (7 * q)) (Finset.Icc (7 * q + 1) (7 * q + r)) := by
    rw [Finset.disjoint_left]; intro m hm1 hm2
    rw [Finset.mem_Icc] at hm1 hm2; omega
  have hper := barrier1_period_count q
  rw [hsplit, Finset.filter_union,
    Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
    Finset.filter_union,
    Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
    hper.1, hper.2]
  have hrem : Int.natAbs ((((Finset.Icc (7 * q + 1) (7 * q + r)).filter Rdir).card : ℤ) -
      ((Finset.Icc (7 * q + 1) (7 * q + r)).filter Cdir).card) ≤ 1 := by
    interval_cases hr_val : r
    · simp
    · have h1 : (Finset.Icc (7 * q + 1) (7 * q + 1)).filter Rdir = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro m hm; simp only [Finset.mem_Icc] at hm; simp [Rdir]; omega
      have h2 : (Finset.Icc (7 * q + 1) (7 * q + 1)).filter Cdir = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro m hm; simp only [Finset.mem_Icc] at hm; simp [Cdir]; omega
      rw [h1, h2]; simp
    · have h1 : (Finset.Icc (7 * q + 1) (7 * q + 2)).filter Rdir = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro m hm; simp only [Finset.mem_Icc] at hm; simp [Rdir]; omega
      have h2 : (Finset.Icc (7 * q + 1) (7 * q + 2)).filter Cdir = {7 * q + 2} := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, Cdir]; omega
      rw [h1, h2]; simp
    · have h1 : (Finset.Icc (7 * q + 1) (7 * q + 3)).filter Rdir = {7 * q + 3} := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, Rdir]; omega
      have h2 : (Finset.Icc (7 * q + 1) (7 * q + 3)).filter Cdir = {7 * q + 2} := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, Cdir]; omega
      rw [h1, h2]; simp
    · have h1 : (Finset.Icc (7 * q + 1) (7 * q + 4)).filter Rdir = {7 * q + 3, 7 * q + 4} := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
          Finset.mem_singleton, Rdir]; omega
      have h2 : (Finset.Icc (7 * q + 1) (7 * q + 4)).filter Cdir = {7 * q + 2} := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, Cdir]; omega
      rw [h1, h2, Finset.card_pair (by omega), Finset.card_singleton]; decide
    · have h1 : (Finset.Icc (7 * q + 1) (7 * q + 5)).filter Rdir = {7 * q + 3, 7 * q + 4} := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
          Finset.mem_singleton, Rdir]; omega
      have h2 : (Finset.Icc (7 * q + 1) (7 * q + 5)).filter Cdir = {7 * q + 2, 7 * q + 5} := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
          Finset.mem_singleton, Cdir]; omega
      rw [h1, h2, Finset.card_pair (by omega), Finset.card_pair (by omega)]; decide
    · have h1 : (Finset.Icc (7 * q + 1) (7 * q + 6)).filter Rdir = {7 * q + 3, 7 * q + 4} := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
          Finset.mem_singleton, Rdir]; omega
      have h2 : (Finset.Icc (7 * q + 1) (7 * q + 6)).filter Cdir = {7 * q + 2, 7 * q + 5} := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
          Finset.mem_singleton, Cdir]; omega
      rw [h1, h2, Finset.card_pair (by omega), Finset.card_pair (by omega)]; decide
  omega

theorem barrier1_equal_density :
    Filter.Tendsto (fun x : ℕ => (((Finset.Icc 1 x).filter Rdir).card : ℝ) / (x : ℝ))
      Filter.atTop (nhds (2 / 7 : ℝ)) ∧
    Filter.Tendsto (fun x : ℕ => (((Finset.Icc 1 x).filter Cdir).card : ℝ) / (x : ℝ))
      Filter.atTop (nhds (2 / 7 : ℝ)) := by
  have hcardR : ∀ x : ℕ, (((Finset.Icc 1 x).filter Rdir).card : ℝ) ≤ 2 * ((x : ℝ) / 7) + 2 ∧
      2 * ((x : ℝ) / 7) - 2 ≤ (((Finset.Icc 1 x).filter Rdir).card : ℝ) := by
    intro x
    have hx_lo : 7 * (x / 7) ≤ x := Nat.mul_div_le x 7
    have hx_hi : x ≤ 7 * (x / 7 + 1) := by omega
    have hmono1 := Finset.card_le_card
      (Finset.filter_subset_filter Rdir (Finset.Icc_subset_Icc_right hx_lo : Finset.Icc 1 (7 * (x / 7)) ⊆ Finset.Icc 1 x))
    have hmono2 := Finset.card_le_card
      (Finset.filter_subset_filter Rdir (Finset.Icc_subset_Icc_right hx_hi : Finset.Icc 1 x ⊆ Finset.Icc 1 (7 * (x / 7 + 1))))
    rw [(barrier1_period_count (x / 7)).1] at hmono1
    rw [(barrier1_period_count (x / 7 + 1)).1] at hmono2
    have h1 : (2 : ℝ) * ((x / 7 : ℕ) : ℝ) ≤ ((Finset.Icc 1 x).filter Rdir).card := by exact_mod_cast hmono1
    have h2 : (((Finset.Icc 1 x).filter Rdir).card : ℝ) ≤ 2 * (((x / 7 : ℕ) : ℝ) + 1) := by exact_mod_cast hmono2
    have hdiv1 : ((x / 7 : ℕ) : ℝ) ≤ (x : ℝ) / 7 := by
      have : ((x / 7 : ℕ) : ℝ) * 7 ≤ x := by exact_mod_cast (by omega : (x / 7) * 7 ≤ x)
      linarith
    have hdiv2 : (x : ℝ) / 7 - 1 < ((x / 7 : ℕ) : ℝ) := by
      have : (x : ℝ) < ((x / 7 : ℕ) : ℝ) * 7 + 7 := by exact_mod_cast (by omega : x < (x / 7) * 7 + 7)
      linarith
    constructor <;> linarith
  have hcardC : ∀ x : ℕ, (((Finset.Icc 1 x).filter Cdir).card : ℝ) ≤ 2 * ((x : ℝ) / 7) + 2 ∧
      2 * ((x : ℝ) / 7) - 2 ≤ (((Finset.Icc 1 x).filter Cdir).card : ℝ) := by
    intro x
    have hx_lo : 7 * (x / 7) ≤ x := Nat.mul_div_le x 7
    have hx_hi : x ≤ 7 * (x / 7 + 1) := by omega
    have hmono1 := Finset.card_le_card
      (Finset.filter_subset_filter Cdir (Finset.Icc_subset_Icc_right hx_lo : Finset.Icc 1 (7 * (x / 7)) ⊆ Finset.Icc 1 x))
    have hmono2 := Finset.card_le_card
      (Finset.filter_subset_filter Cdir (Finset.Icc_subset_Icc_right hx_hi : Finset.Icc 1 x ⊆ Finset.Icc 1 (7 * (x / 7 + 1))))
    rw [(barrier1_period_count (x / 7)).2] at hmono1
    rw [(barrier1_period_count (x / 7 + 1)).2] at hmono2
    have h1 : (2 : ℝ) * ((x / 7 : ℕ) : ℝ) ≤ ((Finset.Icc 1 x).filter Cdir).card := by exact_mod_cast hmono1
    have h2 : (((Finset.Icc 1 x).filter Cdir).card : ℝ) ≤ 2 * (((x / 7 : ℕ) : ℝ) + 1) := by exact_mod_cast hmono2
    have hdiv1 : ((x / 7 : ℕ) : ℝ) ≤ (x : ℝ) / 7 := by
      have : ((x / 7 : ℕ) : ℝ) * 7 ≤ x := by exact_mod_cast (by omega : (x / 7) * 7 ≤ x)
      linarith
    have hdiv2 : (x : ℝ) / 7 - 1 < ((x / 7 : ℕ) : ℝ) := by
      have : (x : ℝ) < ((x / 7 : ℕ) : ℝ) * 7 + 7 := by exact_mod_cast (by omega : x < (x / 7) * 7 + 7)
      linarith
    constructor <;> linarith
  have htend_inv : Filter.Tendsto (fun x : ℕ => (2 : ℝ) / 7 - 2 / (x : ℝ)) Filter.atTop (nhds (2 / 7 : ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (2 : ℝ) / 7)).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop tendsto_natCast_atTop_atTop))
  have htend_inv2 : Filter.Tendsto (fun x : ℕ => (2 : ℝ) / 7 + 2 / (x : ℝ)) Filter.atTop (nhds (2 / 7 : ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (2 : ℝ) / 7)).add
      ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop tendsto_natCast_atTop_atTop))
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' htend_inv htend_inv2 ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 1] with x hx
      have hx_pos : (0 : ℝ) < x := by positivity
      have hdiv : (2 * ((x : ℝ) / 7) - 2) / (x : ℝ) = 2 / 7 - 2 / (x : ℝ) := by field_simp
      linarith [div_le_div_of_nonneg_right (hcardR x).2 hx_pos.le]
    · filter_upwards [Filter.eventually_ge_atTop 1] with x hx
      have hx_pos : (0 : ℝ) < x := by positivity
      have hdiv : (2 * ((x : ℝ) / 7) + 2) / (x : ℝ) = 2 / 7 + 2 / (x : ℝ) := by field_simp
      linarith [div_le_div_of_nonneg_right (hcardR x).1 hx_pos.le]
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' htend_inv htend_inv2 ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 1] with x hx
      have hx_pos : (0 : ℝ) < x := by positivity
      have hdiv : (2 * ((x : ℝ) / 7) - 2) / (x : ℝ) = 2 / 7 - 2 / (x : ℝ) := by field_simp
      linarith [div_le_div_of_nonneg_right (hcardC x).2 hx_pos.le]
    · filter_upwards [Filter.eventually_ge_atTop 1] with x hx
      have hx_pos : (0 : ℝ) < x := by positivity
      have hdiv : (2 * ((x : ℝ) / 7) + 2) / (x : ℝ) = 2 / 7 + 2 / (x : ℝ) := by field_simp
      linarith [div_le_div_of_nonneg_right (hcardC x).1 hx_pos.le]

end Barrier1_Mod7

section Barrier2_Mod3

open scoped Classical

/-- Completely multiplicative mod-3 exponent function `v(m)` associated to any prime partition
`(P_R, Primes \ P_R)`. -/
noncomputable def v3 (P_R : ℕ → Prop) (m : ℕ) : ZMod 3 :=
  ∑ p ∈ m.primeFactors, if P_R p then (m.factorization p : ZMod 3) else -(m.factorization p : ZMod 3)

def R2 (P_R : ℕ → Prop) (m : ℕ) : Prop := 2 ≤ m ∧ v3 P_R m = 1
def C2 (P_R : ℕ → Prop) (m : ℕ) : Prop := 2 ≤ m ∧ v3 P_R m = 2
def P2 (P_R : ℕ → Prop) (m : ℕ) : Prop := 2 ≤ m ∧ v3 P_R m = 0

lemma v3_mul (P_R : ℕ → Prop) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    v3 P_R (m * n) = v3 P_R m + v3 P_R n := by
  unfold v3
  rw [Nat.primeFactors_mul hm hn, Nat.factorization_mul hm hn]
  have h1 : ∀ p ∈ m.primeFactors ∪ n.primeFactors,
      (if P_R p then ((m.factorization + n.factorization) p : ZMod 3)
       else -((m.factorization + n.factorization) p : ZMod 3)) =
      (if P_R p then (m.factorization p : ZMod 3) else -(m.factorization p : ZMod 3)) +
      (if P_R p then (n.factorization p : ZMod 3) else -(n.factorization p : ZMod 3)) := by
    intro p _
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add]
    by_cases hp : P_R p <;> simp [hp, add_comm]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  have hm_sum : ∑ p ∈ m.primeFactors ∪ n.primeFactors,
      (if P_R p then (m.factorization p : ZMod 3) else -(m.factorization p : ZMod 3)) =
      ∑ p ∈ m.primeFactors,
        (if P_R p then (m.factorization p : ZMod 3) else -(m.factorization p : ZMod 3)) := by
    refine (Finset.sum_subset Finset.subset_union_left fun p _ hp_not => ?_).symm
    have hz : m.factorization p = 0 := Finsupp.notMem_support_iff.mp (Nat.support_factorization m ▸ hp_not)
    simp [hz]
  have hn_sum : ∑ p ∈ m.primeFactors ∪ n.primeFactors,
      (if P_R p then (n.factorization p : ZMod 3) else -(n.factorization p : ZMod 3)) =
      ∑ p ∈ n.primeFactors,
        (if P_R p then (n.factorization p : ZMod 3) else -(n.factorization p : ZMod 3)) := by
    refine (Finset.sum_subset Finset.subset_union_right fun p _ hp_not => ?_).symm
    have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp (Nat.support_factorization n ▸ hp_not)
    simp [hz]
  rw [hm_sum, hn_sum]

private lemma zmod3_cases (z : ZMod 3) : z = 0 ∨ z = 1 ∨ z = 2 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

lemma v3_prime (P_R : ℕ → Prop) {p : ℕ} (hp : p.Prime) :
    v3 P_R p = if P_R p then 1 else 2 := by
  unfold v3
  rw [hp.primeFactors, Finset.sum_singleton, hp.factorization_self]
  by_cases h : P_R p
  · simp [h]
  · simp [h]; decide

theorem barrier2_partition_and_primes (P_R : ℕ → Prop) :
    (∀ m, 2 ≤ m → (R2 P_R m ∨ C2 P_R m ∨ P2 P_R m) ∧
      ¬ (R2 P_R m ∧ C2 P_R m) ∧ ¬ (R2 P_R m ∧ P2 P_R m) ∧ ¬ (C2 P_R m ∧ P2 P_R m)) ∧
    (∀ p, p.Prime → R2 P_R p ∨ C2 P_R p) := by
  constructor
  · intro m hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases zmod3_cases (v3 P_R m) with hv | hv | hv
      · exact Or.inr (Or.inr ⟨hm, hv⟩)
      · exact Or.inl ⟨hm, hv⟩
      · exact Or.inr (Or.inl ⟨hm, hv⟩)
    · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩; rw [h1] at h2; revert h2; decide
    · rintro ⟨⟨_, h1⟩, ⟨_, h0⟩⟩; rw [h1] at h0; revert h0; decide
    · rintro ⟨⟨_, h2⟩, ⟨_, h0⟩⟩; rw [h2] at h0; revert h0; decide
  · intro p hp
    have hvp := v3_prime P_R hp
    by_cases h : P_R p
    · exact Or.inl ⟨hp.two_le, by simp [hvp, h]⟩
    · exact Or.inr ⟨hp.two_le, by simp [hvp, h]⟩

/-- Theorem 3.2 (Exact Maximality of Balanced Mod-3 Model):
For ANY prime partition `P_R`, `ℕ_{≥ 2} = R₂ ⊔ C₂ ⊔ (C₂ · R₂)` identically. -/
theorem barrier2_exact_maximality (P_R : ℕ → Prop) {m : ℕ} (hm : 2 ≤ m) :
    P2 P_R m ↔ ∃ c r, C2 P_R c ∧ R2 P_R r ∧ c * r = m := by
  constructor
  · rintro ⟨_, hvm⟩
    set p := m.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpm : p ∣ m := Nat.minFac_dvd m
    set q := m / p
    have hpq : p * q = m := Nat.mul_div_cancel' hpm
    have hq_ne : q ≠ 0 := by intro hq0; rw [hq0, mul_zero] at hpq; omega
    have hq_ge1 : 1 ≤ q := Nat.pos_of_ne_zero hq_ne
    by_cases hq1 : q = 1
    · rw [hq1, mul_one] at hpq
      rw [← hpq] at hvm
      have hvp := v3_prime P_R hp
      rw [hvp] at hvm
      by_cases hPR : P_R p <;> simp [hPR] at hvm
      exact absurd hvm (by decide)
    · have hq2 : 2 ≤ q := by omega
      have hadd := v3_mul P_R hp.ne_zero hq_ne
      rw [hpq, hvm] at hadd
      have hvp := v3_prime P_R hp
      by_cases hPR : P_R p
      · have hvp1 : v3 P_R p = 1 := by simp [hvp, hPR]
        have hvq2 : v3 P_R q = 2 := by
          have : (1 : ZMod 3) + v3 P_R q = 0 := by rw [← hvp1]; exact hadd.symm
          rcases zmod3_cases (v3 P_R q) with hq | hq | hq
          · rw [hq] at this; exact absurd this (by decide)
          · rw [hq] at this; exact absurd this (by decide)
          · exact hq
        exact ⟨q, p, ⟨hq2, hvq2⟩, ⟨hp.two_le, hvp1⟩, by rw [mul_comm, hpq]⟩
      · have hvp2 : v3 P_R p = 2 := by simp [hvp, hPR]
        have hvq1 : v3 P_R q = 1 := by
          have : (2 : ZMod 3) + v3 P_R q = 0 := by rw [← hvp2]; exact hadd.symm
          rcases zmod3_cases (v3 P_R q) with hq | hq | hq
          · rw [hq] at this; exact absurd this (by decide)
          · exact hq
          · rw [hq] at this; exact absurd this (by decide)
        exact ⟨p, q, ⟨hp.two_le, hvp2⟩, ⟨hq2, hvq1⟩, hpq⟩
  · rintro ⟨c, r, ⟨hc2, hvc⟩, ⟨hr2, hvr⟩, rfl⟩
    refine ⟨by nlinarith, ?_⟩
    rw [v3_mul P_R (by omega) (by omega), hvc, hvr]
    decide

private lemma coprime_add_mul_one (q K : ℕ) : Nat.Coprime (q * K + 1) K := by
  rw [Nat.coprime_iff_gcd_eq_one]
  refine Nat.eq_one_of_dvd_one ?_
  have hd1 : Nat.gcd (q * K + 1) K ∣ q * K + 1 := Nat.gcd_dvd_left _ _
  have hd2 : Nat.gcd (q * K + 1) K ∣ K := Nat.gcd_dvd_right _ _
  exact (Nat.dvd_add_right (dvd_mul_of_dvd_right hd2 q)).mp hd1

private lemma mod3_triple_pick (P_R : ℕ → Prop) (p₀ : ℕ) (hp₀ : p₀.Prime)
    (U : Finset ℕ) (hU_ge2 : ∀ u ∈ U, 2 ≤ u) (hU_cop : ∀ u ∈ U, Nat.Coprime u p₀)
    (target : ZMod 3) :
    ∃ f : ℕ → ℕ, (∀ u ∈ U, f u < 3 ∧ v3 P_R (u * p₀ ^ f u) = target) ∧
      Set.InjOn (fun u => u * p₀ ^ f u) U := by
  have hvp₀ : v3 P_R p₀ = 1 ∨ v3 P_R p₀ = 2 := by
    have := v3_prime P_R hp₀; by_cases h : P_R p₀ <;> simp [this, h]
  have hinj : ∀ u₁ ∈ U, ∀ a₁ < 3, ∀ u₂ ∈ U, ∀ a₂ < 3,
      u₁ * p₀ ^ a₁ = u₂ * p₀ ^ a₂ → u₁ = u₂ ∧ a₁ = a₂ := by
    intro u₁ hu1 a₁ _ u₂ hu2 a₂ _ heq
    have hu1_pos : u₁ ≠ 0 := by have := hU_ge2 u₁ hu1; omega
    have hu2_pos : u₂ ≠ 0 := by have := hU_ge2 u₂ hu2; omega
    have hnot1 : ¬ p₀ ∣ u₁ := fun hdvd =>
      hp₀.ne_one (Nat.dvd_one.mp ((hU_cop u₁ hu1) ▸ Nat.dvd_gcd hdvd dvd_rfl))
    have hnot2 : ¬ p₀ ∣ u₂ := fun hdvd =>
      hp₀.ne_one (Nat.dvd_one.mp ((hU_cop u₂ hu2) ▸ Nat.dvd_gcd hdvd dvd_rfl))
    have hv1 : padicValNat p₀ (u₁ * p₀ ^ a₁) = a₁ := by
      have : Fact p₀.Prime := ⟨hp₀⟩
      rw [padicValNat.mul hu1_pos (pow_ne_zero a₁ hp₀.ne_zero),
        padicValNat.eq_zero_of_not_dvd hnot1, zero_add, padicValNat.prime_pow]
    have hv2 : padicValNat p₀ (u₂ * p₀ ^ a₂) = a₂ := by
      have : Fact p₀.Prime := ⟨hp₀⟩
      rw [padicValNat.mul hu2_pos (pow_ne_zero a₂ hp₀.ne_zero),
        padicValNat.eq_zero_of_not_dvd hnot2, zero_add, padicValNat.prime_pow]
    have ha : a₁ = a₂ := by rw [← hv1, heq, hv2]
    subst ha
    exact ⟨Nat.mul_right_cancel (pow_pos hp₀.pos a₁) heq, rfl⟩
  have hvp_sq : v3 P_R p₀ * v3 P_R p₀ = 1 := by
    rcases hvp₀ with h | h <;> rw [h] <;> decide
  have hpick : ∀ u ∈ U, ∃ a < 3, v3 P_R (u * p₀ ^ a) = target := by
    intro u hu
    have hu_pos : u ≠ 0 := by have := hU_ge2 u hu; omega
    have hvpow : ∀ a : ℕ, v3 P_R (u * p₀ ^ a) = v3 P_R u + (a : ZMod 3) * v3 P_R p₀ := by
      intro a
      induction a with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ← mul_assoc,
          v3_mul P_R (mul_ne_zero hu_pos (pow_ne_zero k hp₀.ne_zero)) hp₀.ne_zero,
          ih, Nat.cast_add, Nat.cast_one]
        ring
    set az : ZMod 3 := (target - v3 P_R u) * v3 P_R p₀
    refine ⟨az.val, ZMod.val_lt az, ?_⟩
    rw [hvpow, ZMod.natCast_zmod_val az]
    calc v3 P_R u + (target - v3 P_R u) * v3 P_R p₀ * v3 P_R p₀
        = v3 P_R u + (target - v3 P_R u) * (v3 P_R p₀ * v3 P_R p₀) := by ring
      _ = target := by rw [hvp_sq]; ring
  let f : ℕ → ℕ := fun u => if hu : u ∈ U then Classical.choose (hpick u hu) else 0
  have hf_spec : ∀ u ∈ U, f u < 3 ∧ v3 P_R (u * p₀ ^ f u) = target := by
    intro u hu
    dsimp [f]
    rw [dif_pos hu]
    exact Classical.choose_spec (hpick u hu)
  refine ⟨f, hf_spec, fun u₁ hu1 u₂ hu2 heq => ?_⟩
  exact (hinj u₁ hu1 (f u₁) (hf_spec u₁ hu1).1 u₂ hu2 (f u₂) (hf_spec u₂ hu2).1 heq).1

/-- Unconditional explicit positive lower density `≥ 1/12` (for `N ≥ 24`) for both `R₂` and `C₂`
for ANY prime partition `P_R`. -/
theorem barrier2_positive_lower_density (P_R : ℕ → Prop) {N : ℕ} (hN : 24 ≤ N) :
    N / 12 ≤ ((Finset.Icc 2 N).filter (R2 P_R)).card ∧
    N / 12 ≤ ((Finset.Icc 2 N).filter (C2 P_R)).card := by
  let U := (Finset.Icc 1 (N / 10)).image (fun q => 2 * q + 1)
  have hU_card : U.card = N / 10 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega), Nat.card_Icc]
    omega
  have hU_ge2 : ∀ u ∈ U, 2 ≤ u := by
    intro u hu; rcases Finset.mem_image.mp hu with ⟨q, hq, rfl⟩
    rw [Finset.mem_Icc] at hq; omega
  have hU_cop : ∀ u ∈ U, Nat.Coprime u 2 := by
    intro u hu; rcases Finset.mem_image.mp hu with ⟨q, _, rfl⟩
    rw [mul_comm]
    exact coprime_add_mul_one q 2
  have hU_bd : ∀ u ∈ U, u * 2 ^ 2 ≤ N := by
    intro u hu; rcases Finset.mem_image.mp hu with ⟨q, hq, rfl⟩
    rw [Finset.mem_Icc] at hq; omega
  have htarget : ∀ target : ZMod 3,
      N / 12 ≤ ((Finset.Icc 2 N).filter (fun m => 2 ≤ m ∧ v3 P_R m = target)).card := by
    intro target
    obtain ⟨f, hf_spec, hf_inj⟩ := mod3_triple_pick P_R 2 Nat.prime_two U hU_ge2 hU_cop target
    have hcard : U.card = (U.image (fun u => u * 2 ^ f u)).card :=
      (Finset.card_image_of_injOn hf_inj).symm
    have hle_img : (U.image (fun u => u * 2 ^ f u)).card ≤
        ((Finset.Icc 2 N).filter (fun m => 2 ≤ m ∧ v3 P_R m = target)).card := by
      refine Finset.card_le_card fun z hz => ?_
      rcases Finset.mem_image.mp hz with ⟨u, hu, rfl⟩
      rcases hf_spec u hu with ⟨hflt, hv⟩
      have hu2 := hU_ge2 u hu
      have hpow_le : 2 ^ f u ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
      have hpow_pos : 1 ≤ 2 ^ f u := Nat.one_le_pow _ _ (by omega)
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by nlinarith, le_trans (Nat.mul_le_mul_left u hpow_le) (hU_bd u hu)⟩, ⟨by nlinarith, hv⟩⟩
    have h12_10 : N / 12 ≤ N / 10 := Nat.div_le_div_left (by omega) (by omega)
    omega
  have hR_eq : (Finset.Icc 2 N).filter (R2 P_R) =
      (Finset.Icc 2 N).filter (fun m => 2 ≤ m ∧ v3 P_R m = 1) :=
    Finset.filter_congr fun _ _ => Iff.rfl
  have hC_eq : (Finset.Icc 2 N).filter (C2 P_R) =
      (Finset.Icc 2 N).filter (fun m => 2 ≤ m ∧ v3 P_R m = 2) :=
    Finset.filter_congr fun _ _ => Iff.rfl
  rw [hR_eq, hC_eq]
  exact ⟨htarget 1, htarget 2⟩

/-- Explicit 50/50 alternating-index prime partition (`p_{2k} ∈ P_R`, `p_{2k+1} ∈ P_C`). -/
noncomputable def altPrimePart (p : ℕ) : Prop :=
  p.Prime ∧ Even (Nat.count Nat.Prime p)

/-- Theorem 3.3 (Divergent Prime Reciprocals on Both Sides of Balanced Mod-3 Model):
For `altPrimePart`, both `∑_{p ∈ R₂ ∩ Primes} 1/p` and `∑_{p ∈ C₂ ∩ Primes} 1/p` diverge. -/
theorem barrier2_alt_divergent_prime_reciprocals :
    ¬ Summable (fun p : ℕ => if R2 altPrimePart p ∧ p.Prime then (1 : ℝ) / p else 0) ∧
    ¬ Summable (fun p : ℕ => if C2 altPrimePart p ∧ p.Prime then (1 : ℝ) / p else 0) := by
  set p := Nat.nth Nat.Prime
  have hp_prime : ∀ k, (p k).Prime := fun k => Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k
  have hp_strict : StrictMono p := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hp_count : ∀ k, Nat.count Nat.Prime (p k) = k :=
    fun k => Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime k
  have hnot_all : ¬ Summable (fun p : Nat.Primes => (1 : ℝ) / p) :=
    Nat.Primes.not_summable_one_div
  have hnot_k : ¬ Summable (fun k : ℕ => (1 : ℝ) / (p k : ℝ)) := by
    intro hsum
    apply hnot_all
    let e : ℕ ≃ Nat.Primes :=
      ⟨fun k => ⟨p k, hp_prime k⟩,
       fun q => Nat.count Nat.Prime q.1,
       fun k => hp_count k,
       fun q => Subtype.ext (Nat.nth_count q.2)⟩
    have hcomp : ((fun q : Nat.Primes => (1 : ℝ) / q) ∘ e) = (fun k : ℕ => (1 : ℝ) / (p k : ℝ)) := by
      ext k; dsimp [e]; rfl
    exact (Equiv.summable_iff e).mp (by rw [hcomp]; exact hsum)
  have heven_not : ¬ Summable (fun k : ℕ => (1 : ℝ) / (p (2 * k) : ℝ)) := by
    intro heven
    have hodd : Summable (fun k : ℕ => (1 : ℝ) / (p (2 * k + 1) : ℝ)) := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) heven
      have hlt : p (2 * k) < p (2 * k + 1) := hp_strict (by omega)
      have hpos : (0 : ℝ) < p (2 * k) := by exact_mod_cast (hp_prime (2 * k)).pos
      have hle : (p (2 * k) : ℝ) ≤ (p (2 * k + 1) : ℝ) := by exact_mod_cast hlt.le
      exact one_div_le_one_div_of_le hpos hle
    have hsplit : ∀ M : ℕ, ∑ i ∈ Finset.range (2 * M), (1 : ℝ) / (p i : ℝ) =
        ∑ k ∈ Finset.range M, ((1 : ℝ) / (p (2 * k) : ℝ) + (1 : ℝ) / (p (2 * k + 1) : ℝ)) := by
      intro M
      induction M with
      | zero => simp
      | succ k ih =>
        rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
          Finset.sum_range_succ, add_assoc]
    apply hnot_k
    refine summable_of_sum_range_le (c := (∑' k, (1 : ℝ) / (p (2 * k) : ℝ)) +
        ∑' k, (1 : ℝ) / (p (2 * k + 1) : ℝ)) (fun k => by positivity) fun N => ?_
    calc ∑ i ∈ Finset.range N, (1 : ℝ) / (p i : ℝ)
        ≤ ∑ i ∈ Finset.range (2 * N), (1 : ℝ) / (p i : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun _ _ _ => by positivity
      _ = ∑ k ∈ Finset.range N, (1 : ℝ) / (p (2 * k) : ℝ) +
            ∑ k ∈ Finset.range N, (1 : ℝ) / (p (2 * k + 1) : ℝ) := by
          rw [hsplit N, Finset.sum_add_distrib]
      _ ≤ (∑' k, (1 : ℝ) / (p (2 * k) : ℝ)) + ∑' k, (1 : ℝ) / (p (2 * k + 1) : ℝ) :=
          add_le_add (heven.sum_le_tsum _ (fun _ _ => by positivity))
            (hodd.sum_le_tsum _ (fun _ _ => by positivity))
  have hodd_not : ¬ Summable (fun k : ℕ => (1 : ℝ) / (p (2 * k + 1) : ℝ)) := by
    intro hodd
    have heven_tail : Summable (fun k : ℕ => (1 : ℝ) / (p (2 * (k + 1)) : ℝ)) := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hodd
      have hlt : p (2 * k + 1) < p (2 * (k + 1)) := hp_strict (by omega)
      have hpos : (0 : ℝ) < p (2 * k + 1) := by exact_mod_cast (hp_prime (2 * k + 1)).pos
      have hle : (p (2 * k + 1) : ℝ) ≤ (p (2 * (k + 1)) : ℝ) := by exact_mod_cast hlt.le
      exact one_div_le_one_div_of_le hpos hle
    have heven : Summable (fun k : ℕ => (1 : ℝ) / (p (2 * k) : ℝ)) :=
      (summable_nat_add_iff 1).mp heven_tail
    exact heven_not heven
  constructor
  · intro hsum
    apply heven_not
    have hcomp : Summable (fun k : ℕ =>
        if R2 altPrimePart (p (2 * k)) ∧ (p (2 * k)).Prime then (1 : ℝ) / (p (2 * k) : ℝ) else 0) :=
      hsum.comp_injective (fun a b h => by
        have := hp_strict.injective h; omega)
    refine hcomp.congr fun k => ?_
    have hpk := hp_prime (2 * k)
    have hR : R2 altPrimePart (p (2 * k)) := by
      refine ⟨hpk.two_le, ?_⟩
      rw [v3_prime altPrimePart hpk]
      have halt : altPrimePart (p (2 * k)) := ⟨hpk, by rw [hp_count]; exact even_two_mul k⟩
      simp [halt]
    simp [hR, hpk]
  · intro hsum
    apply hodd_not
    have hcomp : Summable (fun k : ℕ =>
        if C2 altPrimePart (p (2 * k + 1)) ∧ (p (2 * k + 1)).Prime then (1 : ℝ) / (p (2 * k + 1) : ℝ) else 0) :=
      hsum.comp_injective (fun a b h => by
        have := hp_strict.injective h; omega)
    refine hcomp.congr fun k => ?_
    have hpk := hp_prime (2 * k + 1)
    have hC : C2 altPrimePart (p (2 * k + 1)) := by
      refine ⟨hpk.two_le, ?_⟩
      rw [v3_prime altPrimePart hpk]
      have hnot : ¬ altPrimePart (p (2 * k + 1)) := by
        rintro ⟨_, hev⟩
        rw [hp_count] at hev
        exact (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)) hev
      simp [hnot]
    simp [hC, hpk]

end Barrier2_Mod3

section Barrier3_FinitePrefixImmunity

open scoped Classical

/-- An integer `m ≥ 1` is `M`-rough if every prime dividing `m` exceeds `M`. -/
def IsMRough (M m : ℕ) : Prop := 1 ≤ m ∧ ∀ p, p.Prime → p ∣ m → M < p

lemma isMRough_of_coprime_fac {M m : ℕ} (hm : 1 ≤ m) (hcop : Nat.Coprime m (Nat.factorial M)) :
    IsMRough M m := by
  refine ⟨hm, fun p hp hpm => ?_⟩
  by_contra hle
  have hpfac : p ∣ Nat.factorial M := Nat.dvd_factorial hp.pos (not_lt.mp hle)
  have hdvd : p ∣ Nat.gcd m (Nat.factorial M) := Nat.dvd_gcd hpm hpfac
  rw [hcop] at hdvd
  exact hp.ne_one (Nat.dvd_one.mp hdvd)

lemma isMRough_dvd {M m d : ℕ} (hm : IsMRough M m) (hd1 : 1 ≤ d) (hdm : d ∣ m) :
    IsMRough M d :=
  ⟨hd1, fun p hp hpd => hm.2 p hp (dvd_trans hpd hdm)⟩

lemma isMRough_mul {M a b : ℕ} (ha : IsMRough M a) (hb : IsMRough M b) :
    IsMRough M (a * b) := by
  refine ⟨by nlinarith [ha.1, hb.1], fun p hp hpm => ?_⟩
  rcases hp.dvd_mul.mp hpm with hpa | hpb
  · exact ha.2 p hp hpa
  · exact hb.2 p hp hpb

lemma gt_of_isMRough_ge_two {M m : ℕ} (hm2 : 2 ≤ m) (hrough : IsMRough M m) : M < m := by
  have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
  have hdvd : m.minFac ∣ m := Nat.minFac_dvd m
  have hgt : M < m.minFac := hrough.2 m.minFac hp hdvd
  have hle : m.minFac ≤ m := Nat.minFac_le (by omega)
  omega

/-- Inductive extension `0 = P, 1 = R', 2 = C'` of Kimberling's exact classification on `[2, M]`
to all `m ≥ 2`, matching `v3 P_R` on `M`-rough numbers. -/
noncomputable def barrier3Class (M : ℕ) (P_R : ℕ → Prop) : ℕ → Fin 3
  | m =>
    if m ≤ M then
      if IsRow m then 1 else if IsCol m then 2 else 0
    else if IsMRough M m then
      if v3 P_R m = 1 then 1 else if v3 P_R m = 2 then 2 else 0
    else
      if ∃ c : {c : ℕ // 1 < c ∧ c < m}, c.1 ∣ m ∧
          barrier3Class M P_R c.1 = 2 ∧ barrier3Class M P_R (m / c.1) = 1
      then 0 else 1
termination_by m => m
decreasing_by
  · exact c.2.2
  · exact Nat.div_lt_self (by omega) c.2.1

def R3 (M : ℕ) (P_R : ℕ → Prop) (m : ℕ) : Prop := 2 ≤ m ∧ barrier3Class M P_R m = 1
def C3 (M : ℕ) (P_R : ℕ → Prop) (m : ℕ) : Prop := 2 ≤ m ∧ barrier3Class M P_R m = 2
def P3 (M : ℕ) (P_R : ℕ → Prop) (m : ℕ) : Prop := 2 ≤ m ∧ barrier3Class M P_R m = 0

lemma barrier3Class_unfold (M : ℕ) (P_R : ℕ → Prop) (m : ℕ) :
    barrier3Class M P_R m =
      if m ≤ M then
        if IsRow m then 1 else if IsCol m then 2 else 0
      else if IsMRough M m then
        if v3 P_R m = 1 then 1 else if v3 P_R m = 2 then 2 else 0
      else
        if ∃ c : {c : ℕ // 1 < c ∧ c < m}, c.1 ∣ m ∧
            barrier3Class M P_R c.1 = 2 ∧ barrier3Class M P_R (m / c.1) = 1
        then 0 else 1 := by
  rw [barrier3Class]

/-- Theorem 3.4 (Finite-Prefix Immunity for Every `M ≥ 2`):
Every finite prefix `[2, M]` of Kimberling's array embeds identically into a full partition
`ℕ_{≥ 2} = R₃ ⊔ C₃ ⊔ (C₃ · R₃)` containing all primes and having explicit positive lower density
on both `R₃` and `C₃`. -/
theorem barrier3_finite_prefix_immunity {M : ℕ} (_hM : 2 ≤ M) (P_R : ℕ → Prop) :
    (∀ m, 2 ≤ m → m ≤ M →
      ((R3 M P_R m ↔ IsRow m) ∧ (C3 M P_R m ↔ IsCol m) ∧ (P3 M P_R m ↔ IsProd m))) ∧
    (∀ m, 2 ≤ m → (R3 M P_R m ∨ C3 M P_R m ∨ P3 M P_R m) ∧
      ¬ (R3 M P_R m ∧ C3 M P_R m) ∧ ¬ (R3 M P_R m ∧ P3 M P_R m) ∧ ¬ (C3 M P_R m ∧ P3 M P_R m)) ∧
    (∀ p, p.Prime → R3 M P_R p ∨ C3 M P_R p) ∧
    (∀ m, 2 ≤ m → (P3 M P_R m ↔ ∃ c r, C3 M P_R c ∧ R3 M P_R r ∧ c * r = m)) := by
  have hprefix : ∀ m, 2 ≤ m → m ≤ M →
      (R3 M P_R m ↔ IsRow m) ∧ (C3 M P_R m ↔ IsCol m) ∧ (P3 M P_R m ↔ IsProd m) := by
    intro m hm hmM
    have heq := barrier3Class_unfold M P_R m
    rw [if_pos hmM] at heq
    have hpart := kim_exact_partition hm
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · rintro ⟨_, h1⟩; rw [heq] at h1
        by_cases hR : IsRow m <;> simp [hR] at h1
        · exact hR
        · by_cases hC : IsCol m <;> simp [hC] at h1
      · intro hR
        refine ⟨hm, ?_⟩; rw [heq, if_pos hR]
    · constructor
      · rintro ⟨_, h2⟩; rw [heq] at h2
        by_cases hR : IsRow m <;> simp [hR] at h2
        by_cases hC : IsCol m <;> simp [hC] at h2
        exact hC
      · intro hC
        have hnotR : ¬ IsRow m := fun h => hpart.2.1 ⟨h, hC⟩
        refine ⟨hm, ?_⟩; rw [heq, if_neg hnotR, if_pos hC]
    · constructor
      · rintro ⟨_, h0⟩; rw [heq] at h0
        by_cases hR : IsRow m <;> simp [hR] at h0
        by_cases hC : IsCol m <;> simp [hC] at h0
        rcases hpart.1 with h | h | h
        · exact absurd h hR
        · exact absurd h hC
        · exact h
      · intro hP
        have hnotR : ¬ IsRow m := fun h => hpart.2.2.1 ⟨h, hP⟩
        have hnotC : ¬ IsCol m := fun h => hpart.2.2.2 ⟨h, hP⟩
        refine ⟨hm, ?_⟩; rw [heq, if_neg hnotR, if_neg hnotC]
  have hpart_all : ∀ m, 2 ≤ m → (R3 M P_R m ∨ C3 M P_R m ∨ P3 M P_R m) ∧
      ¬ (R3 M P_R m ∧ C3 M P_R m) ∧ ¬ (R3 M P_R m ∧ P3 M P_R m) ∧ ¬ (C3 M P_R m ∧ P3 M P_R m) := by
    intro m hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · match h : barrier3Class M P_R m with
      | 0 => exact Or.inr (Or.inr ⟨hm, h⟩)
      | 1 => exact Or.inl ⟨hm, h⟩
      | 2 => exact Or.inr (Or.inl ⟨hm, h⟩)
    · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩; rw [h1] at h2; revert h2; decide
    · rintro ⟨⟨_, h1⟩, ⟨_, h0⟩⟩; rw [h1] at h0; revert h0; decide
    · rintro ⟨⟨_, h2⟩, ⟨_, h0⟩⟩; rw [h2] at h0; revert h0; decide
  have hprimes : ∀ p, p.Prime → R3 M P_R p ∨ C3 M P_R p := by
    intro p hp
    rcases le_or_gt p M with hpM | hpM
    · rcases kim_prime_inclusion hp with hR | hC
      · exact Or.inl ((hprefix p hp.two_le hpM).1.mpr hR)
      · exact Or.inr ((hprefix p hp.two_le hpM).2.1.mpr hC)
    · have hrough : IsMRough M p := ⟨hp.one_lt.le, fun q hq hqp => by
        rw [(hp.eq_one_or_self_of_dvd q hqp).resolve_left hq.ne_one]; exact hpM⟩
      have heq := barrier3Class_unfold M P_R p
      rw [if_neg (by omega), if_pos hrough] at heq
      have hvp := v3_prime P_R hp
      by_cases hPR : P_R p
      · exact Or.inl ⟨hp.two_le, by rw [heq, if_pos (by simp [hvp, hPR])]⟩
      · exact Or.inr ⟨hp.two_le, by
          have h2 : v3 P_R p = 2 := by simp [hvp, hPR]
          rw [heq, if_neg (by rw [h2]; decide), if_pos h2]⟩
  have hmax : ∀ m, 2 ≤ m → (P3 M P_R m ↔ ∃ c r, C3 M P_R c ∧ R3 M P_R r ∧ c * r = m) := by
    intro m hm
    rcases le_or_gt m M with hmM | hmM
    · rw [(hprefix m hm hmM).2.2]
      constructor
      · rintro ⟨c, r, hc, hr, rfl⟩
        have hc2 : 2 ≤ c := by rcases hc with ⟨i, hi, rfl⟩; have := three_le_kimCol hi; omega
        have hr2 : 2 ≤ r := by rcases hr with ⟨j, hj, rfl⟩; exact (kim_strict_interleaving hj).1
        have hcM : c ≤ M := le_trans (Nat.le_mul_of_pos_right c (by omega)) hmM
        have hrM : r ≤ M := le_trans (Nat.le_mul_of_pos_left r (by omega)) hmM
        exact ⟨c, r, (hprefix c hc2 hcM).2.1.mpr hc, (hprefix r hr2 hrM).1.mpr hr, rfl⟩
      · rintro ⟨c, r, ⟨hc2, hc⟩, ⟨hr2, hr⟩, rfl⟩
        have hcM : c ≤ M := le_trans (Nat.le_mul_of_pos_right c (by omega)) hmM
        have hrM : r ≤ M := le_trans (Nat.le_mul_of_pos_left r (by omega)) hmM
        exact ⟨c, r, (hprefix c hc2 hcM).2.1.mp ⟨hc2, hc⟩, (hprefix r hr2 hrM).1.mp ⟨hr2, hr⟩, rfl⟩
    · by_cases hrough : IsMRough M m
      · have heq := barrier3Class_unfold M P_R m
        rw [if_neg (by omega), if_pos hrough] at heq
        have hm_P3_iff : P3 M P_R m ↔ P2 P_R m := by
          constructor
          · rintro ⟨_, h0⟩
            refine ⟨hm, ?_⟩
            rw [heq] at h0
            rcases zmod3_cases (v3 P_R m) with hv | hv | hv
            · exact hv
            · rw [hv] at h0; exact absurd h0 (by decide)
            · rw [hv] at h0; exact absurd h0 (by decide)
          · rintro ⟨_, hv0⟩
            refine ⟨hm, ?_⟩
            rw [heq, hv0]; decide
        rw [hm_P3_iff, barrier2_exact_maximality P_R hm]
        constructor
        · rintro ⟨c, r, ⟨hc2, hvc⟩, ⟨hr2, hvr⟩, rfl⟩
          have hc_rough : IsMRough M c := isMRough_dvd hrough (by omega) ⟨r, rfl⟩
          have hr_rough : IsMRough M r := isMRough_dvd hrough (by omega) ⟨c, mul_comm c r⟩
          have hcM : M < c := gt_of_isMRough_ge_two hc2 hc_rough
          have hrM : M < r := gt_of_isMRough_ge_two hr2 hr_rough
          have hc_eq := barrier3Class_unfold M P_R c
          rw [if_neg (by omega), if_pos hc_rough, hvc] at hc_eq
          have hr_eq := barrier3Class_unfold M P_R r
          rw [if_neg (by omega), if_pos hr_rough, hvr] at hr_eq
          exact ⟨c, r, ⟨hc2, by rw [hc_eq]; decide⟩, ⟨hr2, by rw [hr_eq]; decide⟩, rfl⟩
        · rintro ⟨c, r, ⟨hc2, hc⟩, ⟨hr2, hr⟩, rfl⟩
          have hc_rough : IsMRough M c := isMRough_dvd hrough (by omega) ⟨r, rfl⟩
          have hr_rough : IsMRough M r := isMRough_dvd hrough (by omega) ⟨c, mul_comm c r⟩
          have hcM : M < c := gt_of_isMRough_ge_two hc2 hc_rough
          have hrM : M < r := gt_of_isMRough_ge_two hr2 hr_rough
          have hc_eq := barrier3Class_unfold M P_R c
          rw [if_neg (by omega), if_pos hc_rough] at hc_eq
          have hr_eq := barrier3Class_unfold M P_R r
          rw [if_neg (by omega), if_pos hr_rough] at hr_eq
          have hvc : v3 P_R c = 2 := by
            rw [hc_eq] at hc
            rcases zmod3_cases (v3 P_R c) with hv | hv | hv
            · rw [hv] at hc; exact absurd hc (by decide)
            · rw [hv] at hc; exact absurd hc (by decide)
            · exact hv
          have hvr : v3 P_R r = 1 := by
            rw [hr_eq] at hr
            rcases zmod3_cases (v3 P_R r) with hv | hv | hv
            · rw [hv] at hr; exact absurd hr (by decide)
            · exact hv
            · rw [hv] at hr; exact absurd hr (by decide)
          exact ⟨c, r, ⟨hc2, hvc⟩, ⟨hr2, hvr⟩, rfl⟩
      · have heq := barrier3Class_unfold M P_R m
        rw [if_neg (by omega), if_neg hrough] at heq
        constructor
        · rintro ⟨_, h0⟩
          rw [heq] at h0
          split_ifs at h0 with hex
          · rcases hex with ⟨⟨c, hc1, hcm⟩, hcdvd, hc2, hmq⟩
            have hr2 : 2 ≤ m / c := by
              rcases eq_or_ne (m / c) 0 with h0' | hne
              · rw [Nat.div_eq_zero_iff] at h0'
                rcases h0' with hc0 | hlt'; omega; omega
              · by_contra hlt2
                have h1 : m / c = 1 :=
                  Nat.le_antisymm (Nat.lt_succ_iff.mp (not_le.mp hlt2)) (Nat.pos_of_ne_zero hne)
                have hm_eq : m = c * (m / c) := (Nat.mul_div_cancel' hcdvd).symm
                rw [h1, mul_one] at hm_eq
                omega
            exact ⟨c, m / c, ⟨by omega, hc2⟩, ⟨hr2, hmq⟩, Nat.mul_div_cancel' hcdvd⟩
          · exact absurd h0 (by decide)
        · rintro ⟨c, r, ⟨hc2, hc⟩, ⟨hr2, hr⟩, rfl⟩
          refine ⟨hm, ?_⟩
          rw [heq, if_pos]
          have hcm : c < c * r := lt_mul_of_one_lt_right (by omega) (by omega)
          exact ⟨⟨c, by omega, hcm⟩, ⟨r, rfl⟩, hc,
            by simpa [Nat.mul_div_cancel_left r (by omega : 0 < c)] using hr⟩
  exact ⟨hprefix, hpart_all, hprimes, hmax⟩

/-- Explicit positive lower density of `R3 M P_R` and `C3 M P_R` for every `M ≥ 2`. -/
theorem barrier3_positive_lower_density {M : ℕ} (hM : 2 ≤ M) (P_R : ℕ → Prop) :
    ∃ (c_num c_den N₀ : ℕ), 0 < c_num ∧ 0 < c_den ∧
      ∀ N, N₀ ≤ N →
        N / c_den ≤ ((Finset.Icc 2 N).filter (R3 M P_R)).card ∧
        N / c_den ≤ ((Finset.Icc 2 N).filter (C3 M P_R)).card := by
  obtain ⟨p₀, hp₀_gt, hp₀_prime⟩ := Nat.exists_infinite_primes (M + 1)
  set K := Nat.factorial M * p₀
  have hK_pos : 0 < K := Nat.mul_pos (Nat.factorial_pos M) hp₀_prime.pos
  set D := K * p₀ ^ 2
  have hD_pos : 0 < D := Nat.mul_pos hK_pos (pow_pos hp₀_prime.pos 2)
  refine ⟨1, 2 * D, 2 * D, by norm_num, by positivity, fun N hN => ?_⟩
  let U := (Finset.Icc 1 (N / (2 * D))).image (fun q => q * K + 1)
  have hU_card : U.card = N / (2 * D) := by
    rw [Finset.card_image_of_injective _ (fun a b h => by
      have : a * K = b * K := by omega
      exact Nat.mul_right_cancel hK_pos this), Nat.card_Icc]
    exact Nat.add_sub_cancel (N / (2 * D)) 1
  have hU_ge2 : ∀ u ∈ U, 2 ≤ u := by
    intro u hu; rcases Finset.mem_image.mp hu with ⟨q, hq, rfl⟩
    rw [Finset.mem_Icc] at hq
    have : 1 ≤ q * K := Nat.mul_pos hq.1 hK_pos
    omega
  have hU_cop_K : ∀ u ∈ U, Nat.Coprime u K := by
    intro u hu; rcases Finset.mem_image.mp hu with ⟨q, _, rfl⟩
    exact coprime_add_mul_one q K
  have hU_cop_p0 : ∀ u ∈ U, Nat.Coprime u p₀ := fun u hu =>
    (hU_cop_K u hu).coprime_dvd_right (dvd_mul_left p₀ (Nat.factorial M))
  have hU_cop_fac : ∀ u ∈ U, Nat.Coprime u (Nat.factorial M) := fun u hu =>
    (hU_cop_K u hu).coprime_dvd_right (dvd_mul_right (Nat.factorial M) p₀)
  have hU_bd : ∀ u ∈ U, u * p₀ ^ 2 ≤ N := by
    intro u hu; rcases Finset.mem_image.mp hu with ⟨q, hq, rfl⟩
    rw [Finset.mem_Icc] at hq
    have h1 : (q * K + 1) * p₀ ^ 2 = q * D + p₀ ^ 2 := by dsimp [D]; ring
    have hqD : q * D ≤ (N / (2 * D)) * D := Nat.mul_le_mul_right D hq.2
    have h2 : (N / (2 * D)) * (2 * D) ≤ N := Nat.div_mul_le_self N (2 * D)
    have hq_ge1 : 1 ≤ N / (2 * D) := Nat.div_pos hN (by omega)
    have h_step : (N / (2 * D)) * D + D ≤ (N / (2 * D)) * (2 * D) := by nlinarith
    have hp0_le : p₀ ^ 2 ≤ D := by
      calc p₀ ^ 2 = 1 * p₀ ^ 2 := (one_mul _).symm
      _ ≤ K * p₀ ^ 2 := Nat.mul_le_mul_right _ hK_pos
    linarith
  have hp0_rough : IsMRough M p₀ := ⟨hp₀_prime.one_lt.le, fun q hq hqp => by
    rw [(hp₀_prime.eq_one_or_self_of_dvd q hqp).resolve_left hq.ne_one]; omega⟩
  have hrough_pow : ∀ u ∈ U, ∀ a, IsMRough M (u * p₀ ^ a) := by
    intro u hu a
    refine isMRough_mul (isMRough_of_coprime_fac (by have := hU_ge2 u hu; omega) (hU_cop_fac u hu)) ?_
    induction a with
    | zero => exact ⟨le_rfl, fun q hq hq1 => absurd (Nat.dvd_one.mp hq1) hq.ne_one⟩
    | succ k ih => rw [pow_succ]; exact isMRough_mul ih hp0_rough
  have htarget : ∀ (tZ : ZMod 3) (tF : Fin 3),
      (∀ x, v3 P_R x = tZ → (if v3 P_R x = 1 then (1 : Fin 3) else if v3 P_R x = 2 then 2 else 0) = tF) →
      N / (2 * D) ≤ ((Finset.Icc 2 N).filter (fun m => 2 ≤ m ∧ barrier3Class M P_R m = tF)).card := by
    intro tZ tF hcond
    obtain ⟨f, hf_spec, hf_inj⟩ := mod3_triple_pick P_R p₀ hp₀_prime U hU_ge2 hU_cop_p0 tZ
    have hcard : U.card = (U.image (fun u => u * p₀ ^ f u)).card :=
      (Finset.card_image_of_injOn hf_inj).symm
    rw [← hU_card, hcard]
    refine Finset.card_le_card fun z hz => ?_
    rcases Finset.mem_image.mp hz with ⟨u, hu, rfl⟩
    rcases hf_spec u hu with ⟨hflt, hv⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hpow_le : p₀ ^ f u ≤ p₀ ^ 2 := Nat.pow_le_pow_right hp₀_prime.pos (by omega)
    have hu2 := hU_ge2 u hu
    have hpow1 : 1 ≤ p₀ ^ f u := Nat.one_le_pow _ _ hp₀_prime.pos
    have hrough_z := hrough_pow u hu (f u)
    have hgtM : M < u * p₀ ^ f u := gt_of_isMRough_ge_two (by nlinarith) hrough_z
    have hclass := barrier3Class_unfold M P_R (u * p₀ ^ f u)
    rw [if_neg (by omega), if_pos hrough_z] at hclass
    refine ⟨⟨by nlinarith, le_trans (Nat.mul_le_mul_left u hpow_le) (hU_bd u hu)⟩,
      ⟨by nlinarith, by rw [hclass]; exact hcond _ hv⟩⟩
  have hR_eq : (Finset.Icc 2 N).filter (R3 M P_R) =
      (Finset.Icc 2 N).filter (fun m => 2 ≤ m ∧ barrier3Class M P_R m = 1) :=
    Finset.filter_congr fun _ _ => Iff.rfl
  have hC_eq : (Finset.Icc 2 N).filter (C3 M P_R) =
      (Finset.Icc 2 N).filter (fun m => 2 ≤ m ∧ barrier3Class M P_R m = 2) :=
    Finset.filter_congr fun _ _ => Iff.rfl
  rw [hR_eq, hC_eq]
  exact ⟨htarget 1 1 (fun _ hv => by rw [hv]; decide),
    htarget 2 2 (fun _ hv => by rw [hv]; decide)⟩

end Barrier3_FinitePrefixImmunity

end PPL049
