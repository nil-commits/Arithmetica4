import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# RHDirect.Stage9PartitionPentagonal

**UNCONDITIONAL JACOBI TRIPLE PRODUCT IDENTITY, EULER'S PENTAGONAL NUMBER THEOREM,
EULER'S `p(n)` RECURRENCE & ODD=DISTINCT THEOREM, JACOBI'S CUBE IDENTITY,
AND RAMANUJAN'S PARTITION CONGRUENCES `5 ∣ p(5n + 4)` & `7 ∣ p(7n + 5)`**
in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` assumptions).

## Main Unconditional Results

1. **Concrete Partition Generating Function & Euler's Odd = Distinct Theorem**:
   - `partCount (n : ℕ) := Fintype.card (Nat.Partition n)`, `partSeries : PowerSeries ℤ`,
     and formal Euler product `eulerPhiSeries : PowerSeries ℤ` stabilized by `∏_{k=1}^N (1 - X^k)`.
   - `partSeries_mul_eulerPhi_eq_one`: `partSeries * eulerPhiSeries = 1` in `PowerSeries ℤ`.
   - `card_odd_partitions_eq_card_distinct_partitions`:
     `(Nat.Partition.odds n).card = (Nat.Partition.distincts n).card`.

2. **Unconditional Jacobi Triple Product Identity (`0` Assumptions)**:
   - `jacobi_triple_product_coeff`: for every `N : ℕ`, `k : ℤ`, and `M` with `N ≤ 2 * M`,
     the `(q^N z^k)`-coefficient of
     `∏_{n=1}^M (1 - q^{2n})(1 + z q^{2n-1})(1 + z⁻¹ q^{2n-1})`
     equals `1` if `N = k^2` and `0` otherwise.

3. **Unconditional Euler Pentagonal Number Theorem, `p(n)` Recurrences, & Jacobi Cube Identity**:
   - `euler_pentagonal_theorem`:
     `PowerSeries.coeff N eulerPhiSeries = if h : ∃ k : ℤ, (N : ℤ) = k * (3 * k - 1) / 2 then (-1 : ℤ) ^ (Classical.choose h).natAbs else 0`.
   - `partition_pentagonal_recurrence`: Euler's exact signed pentagonal recurrence for `p(N)`.
   - `partition_divisor_sum_recurrence`: `n * partCount n = ∑ k ∈ Icc 1 n, σ₁(k) * partCount (n - k)`.
   - `jacobi_cube_identity`:
     `PowerSeries.coeff N (eulerPhiSeries ^ 3) = if h : ∃ k : ℕ, N = k * (k + 1) / 2 then (-1 : ℤ) ^ (Classical.choose h) * (2 * (Classical.choose h : ℤ) + 1) else 0`.

4. **Unconditional Ramanujan Partition Congruences (`0` Assumptions)**:
   - `ramanujan_partition_mod_5`: `∀ n : ℕ, 5 ∣ partCount (5 * n + 4)`.
   - `ramanujan_partition_mod_7`: `∀ n : ℕ, 7 ∣ partCount (7 * n + 5)`.
-/

open Finset BigOperators

namespace RHDirect.Stage9PartitionPentagonal

noncomputable section

/-! ## Section 1: Concrete Partition Function, Formal Euler Product, `P · Φ = 1`, Odd = Distinct -/

section PartitionGeneratingFunction

/-- The concrete integer partition function `p(n) = #{partitions of n}`. -/
def partCount (n : ℕ) : ℕ :=
  Fintype.card (Nat.Partition n)

/-- The integer partition generating function `P(q) = ∑_{n ≥ 0} p(n) q^n ∈ ℤ⟦q⟧`. -/
def partSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => (partCount n : ℤ)

/-- The `N`-th partial Euler product `∏_{k=1}^{N} (1 - q^k) ∈ ℤ⟦q⟧`. -/
def eulerPhiPartial (N : ℕ) : PowerSeries ℤ :=
  ∏ k ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ k)

/-- Exact coefficient of `f * X^k` in any commutative ring. -/
private lemma coeff_mul_X_pow_eq {R : Type*} [CommRing R] (f : PowerSeries R) (n k : ℕ) :
    PowerSeries.coeff n (f * PowerSeries.X ^ k) =
      if k ≤ n then PowerSeries.coeff (n - k) f else 0 := by
  rw [PowerSeries.coeff_mul]
  split_ifs with hkn
  · rw [Finset.sum_eq_single (n - k, k)]
    · simp [PowerSeries.coeff_X_pow]
    · intro x hx hne
      have hxb : x.2 ≠ k := by
        intro h2
        apply hne
        have hsum := Finset.mem_antidiagonal.mp hx
        ext
        · dsimp; omega
        · exact h2
      simp [PowerSeries.coeff_X_pow, hxb]
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_antidiagonal]
      omega
  · refine Finset.sum_eq_zero fun x hx => ?_
    have hsum := Finset.mem_antidiagonal.mp hx
    have hxb : x.2 ≠ k := by omega
    simp [PowerSeries.coeff_X_pow, hxb]

/-- Exact coefficient of `f * (1 - X^k)`. -/
private lemma coeff_mul_one_sub_X_pow {R : Type*} [CommRing R] (f : PowerSeries R) (n k : ℕ) :
    PowerSeries.coeff n (f * (1 - PowerSeries.X ^ k)) =
      PowerSeries.coeff n f - if k ≤ n then PowerSeries.coeff (n - k) f else 0 := by
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow_eq]

/-- Multiplying by `1 - X^k` with `k > n` leaves `coeff n` unchanged. -/
private lemma coeff_mul_one_sub_X_pow_of_lt {R : Type*} [CommRing R] (f : PowerSeries R)
    {n k : ℕ} (h : n < k) :
    PowerSeries.coeff n (f * (1 - PowerSeries.X ^ k)) = PowerSeries.coeff n f := by
  rw [coeff_mul_one_sub_X_pow, if_neg (by omega), sub_zero]

/-- Multiplying by `1 + X^k` with `k > n` leaves `coeff n` unchanged. -/
private lemma coeff_mul_one_add_X_pow_of_lt {R : Type*} [CommRing R] (f : PowerSeries R)
    {n k : ℕ} (h : n < k) :
    PowerSeries.coeff n (f * (1 + PowerSeries.X ^ k)) = PowerSeries.coeff n f := by
  rw [mul_add, mul_one, map_add, coeff_mul_X_pow_eq, if_neg (by omega), add_zero]

/-- `eulerPhiPartial (M + 1) = eulerPhiPartial M * (1 - X^(M + 1))`. -/
lemma eulerPhiPartial_succ (M : ℕ) :
    eulerPhiPartial (M + 1) = eulerPhiPartial M * (1 - PowerSeries.X ^ (M + 1)) := by
  unfold eulerPhiPartial
  have hIcc : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc, Finset.prod_insert (by simp), mul_comm]

/-- Stabilization of `eulerPhiPartial`: for `N ≤ M`, `coeff N (eulerPhiPartial M)` is independent of `M`. -/
lemma coeff_eulerPhiPartial_eq_of_le {N M : ℕ} (h : N ≤ M) :
    PowerSeries.coeff N (eulerPhiPartial M) = PowerSeries.coeff N (eulerPhiPartial N) := by
  induction M, h using Nat.le_induction with
  | base => rfl
  | succ k hNk ih =>
    rw [eulerPhiPartial_succ, coeff_mul_one_sub_X_pow_of_lt _ (by omega), ih]

/-- The formal Euler product `Φ(q) = ∏_{k ≥ 1} (1 - q^k) ∈ ℤ⟦q⟧`, defined via stabilized partial products. -/
def eulerPhiSeries : PowerSeries ℤ :=
  PowerSeries.mk fun N => PowerSeries.coeff N (eulerPhiPartial N)

/-- For every `M ≥ N`, `coeff N eulerPhiSeries = coeff N (eulerPhiPartial M)`. -/
theorem coeff_eulerPhiSeries_eq_partial {N M : ℕ} (h : N ≤ M) :
    PowerSeries.coeff N eulerPhiSeries = PowerSeries.coeff N (eulerPhiPartial M) := by
  simp only [eulerPhiSeries, PowerSeries.coeff_mk]
  exact (coeff_eulerPhiPartial_eq_of_le h).symm

/-- Constant term of `eulerPhiSeries` is `1`. -/
theorem coeff_zero_eulerPhiSeries : PowerSeries.coeff 0 eulerPhiSeries = 1 := by
  rw [coeff_eulerPhiSeries_eq_partial (le_refl 0)]
  simp [eulerPhiPartial]

/-- Constant term of `partSeries` is `1`. -/
theorem coeff_zero_partSeries : PowerSeries.coeff 0 partSeries = 1 := by
  simp [partSeries, partCount]

/-- Number of partitions of `n` with all parts `≤ N`. -/
private def partCountLe (N n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter (fun p => ∀ a ∈ p.parts, a ≤ N)).card

/-- Generating function of partitions with all parts `≤ N`. -/
private def partSeriesLe (N : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (partCountLe N n : ℤ)

private lemma partCountLe_zero (n : ℕ) : partCountLe 0 n = if n = 0 then 1 else 0 := by
  unfold partCountLe
  split_ifs with hn
  · subst hn
    have hfilt : (Finset.univ : Finset (Nat.Partition 0)).filter (fun p => ∀ a ∈ p.parts, a ≤ 0) =
        Finset.univ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      intro a ha
      rw [Nat.Partition.partition_zero_parts p] at ha
      exact (Multiset.notMem_zero a ha).elim
    rw [hfilt, Finset.card_univ, Fintype.card_unique]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _
    push Not
    have hne : p.parts ≠ 0 := by
      intro h0
      have hsum := p.parts_sum
      rw [h0, Multiset.sum_zero] at hsum
      exact hn hsum.symm
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
    exact ⟨a, ha, p.parts_pos ha⟩

private lemma partSeriesLe_zero : partSeriesLe 0 = 1 := by
  ext n
  simp [partSeriesLe, partCountLe_zero, PowerSeries.coeff_one]

private lemma partCountLe_eq_partCount {N n : ℕ} (h : n ≤ N) :
    partCountLe N n = partCount n := by
  unfold partCountLe partCount
  have hfilt : (Finset.univ : Finset (Nat.Partition n)).filter (fun p => ∀ a ∈ p.parts, a ≤ N) =
      Finset.univ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    intro a ha
    exact le_trans (Nat.Partition.le_of_mem_parts ha) h
  rw [hfilt, Finset.card_univ]

private lemma partSeriesLe_succ_mul (N : ℕ) :
    partSeriesLe (N + 1) * (1 - PowerSeries.X ^ (N + 1)) = partSeriesLe N := by
  ext n
  rw [coeff_mul_one_sub_X_pow]
  simp only [partSeriesLe, PowerSeries.coeff_mk]
  split_ifs with hle
  · let S : Finset (Nat.Partition n) :=
      (Finset.univ : Finset (Nat.Partition n)).filter (fun p => ∀ a ∈ p.parts, a ≤ N + 1)
    let S1 : Finset (Nat.Partition n) := S.filter (fun p => N + 1 ∉ p.parts)
    let S2 : Finset (Nat.Partition n) := S.filter (fun p => N + 1 ∈ p.parts)
    have hS_card : S.card = S1.card + S2.card := by
      have hunion : S = S1 ∪ S2 := by
        ext p
        simp only [Finset.mem_union, Finset.mem_filter, S1, S2]
        tauto
      have hdisj : Disjoint S1 S2 := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h1 h2
      rw [hunion, Finset.card_union_of_disjoint hdisj]
    have hS1 : S1.card = partCountLe N n := by
      unfold partCountLe
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S1, S]
      constructor
      · rintro ⟨hle', hnot⟩ a ha
        have h1 := hle' a ha
        have h2 : a ≠ N + 1 := fun heq => hnot (heq ▸ ha)
        omega
      · intro hle'
        refine ⟨fun a ha => le_trans (hle' a ha) (Nat.le_succ N), fun hmem => ?_⟩
        have := hle' (N + 1) hmem
        omega
    have hS2 : S2.card = partCountLe (N + 1) (n - (N + 1)) := by
      unfold partCountLe
      let e := Nat.Partition.partitionWithPartEquiv (n := n) (a := N + 1) (by omega) hle
      refine Finset.card_bij (fun p hp => e ⟨p, (Finset.mem_filter.mp hp).2⟩) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro a ha
        rw [Nat.Partition.partitionWithPartEquiv_apply_parts] at ha
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2 a (Multiset.mem_of_mem_erase ha)
      · intro p1 hp1 p2 hp2 heq
        have hinj := e.injective heq
        exact congrArg Subtype.val hinj
      · intro q hq
        refine ⟨(e.symm q).1, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, S2, S]
          have hparts : (e.symm q).1.parts = (N + 1) ::ₘ q.parts :=
            Nat.Partition.partitionWithPartEquiv_symm_apply_parts (by omega) hle q
          refine ⟨fun a ha => ?_, ?_⟩
          · rw [hparts, Multiset.mem_cons] at ha
            rcases ha with rfl | ha'
            · exact le_refl _
            · exact (Finset.mem_filter.mp hq).2 a ha'
          · rw [hparts]
            exact Multiset.mem_cons_self _ _
        · exact e.apply_symm_apply q
    change (S.card : ℤ) - (partCountLe (N + 1) (n - (N + 1)) : ℤ) = (partCountLe N n : ℤ)
    rw [hS_card, hS1, hS2]
    push_cast
    ring
  · rw [sub_zero]
    have hn : n ≤ N := by omega
    rw [partCountLe_eq_partCount (le_trans hn (Nat.le_succ N)), partCountLe_eq_partCount hn]

private lemma partSeriesLe_mul_eulerPhiPartial (N : ℕ) :
    partSeriesLe N * eulerPhiPartial N = 1 := by
  induction N with
  | zero => simp [partSeriesLe_zero, eulerPhiPartial]
  | succ k ih =>
    rw [eulerPhiPartial_succ]
    calc partSeriesLe (k + 1) * (eulerPhiPartial k * (1 - PowerSeries.X ^ (k + 1)))
        = (partSeriesLe (k + 1) * (1 - PowerSeries.X ^ (k + 1))) * eulerPhiPartial k := by ring
      _ = partSeriesLe k * eulerPhiPartial k := by rw [partSeriesLe_succ_mul]
      _ = 1 := ih

/-- **FUNDAMENTAL PARTITION GENERATING FUNCTION IDENTITY**:
`partSeries * eulerPhiSeries = 1` in `PowerSeries ℤ`! -/
theorem partSeries_mul_eulerPhi_eq_one : partSeries * eulerPhiSeries = 1 := by
  ext n
  have h1 : PowerSeries.coeff n (partSeries * eulerPhiSeries) =
      PowerSeries.coeff n (partSeriesLe n * eulerPhiPartial n) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hsum := Finset.mem_antidiagonal.mp hx
    have hx1 : x.1 ≤ n := by omega
    have hx2 : x.2 ≤ n := by omega
    congr 1
    · simp only [partSeries, partSeriesLe, PowerSeries.coeff_mk]
      rw [partCountLe_eq_partCount hx1]
    · exact coeff_eulerPhiSeries_eq_partial hx2
  rw [h1, partSeriesLe_mul_eulerPhiPartial]

/-- **EULER'S ODD = DISTINCT PARTITION THEOREM**:
the number of partitions of `n` into odd parts equals the number of partitions of `n`
into distinct parts. -/
theorem card_odd_partitions_eq_card_distinct_partitions (n : ℕ) :
    (Nat.Partition.odds n).card = (Nat.Partition.distincts n).card :=
  Nat.Partition.card_odds_eq_card_distincts n

end PartitionGeneratingFunction

/-! ## Section 2: Unconditional Jacobi Triple Product Identity (`jacobi_triple_product_coeff`) -/

section JacobiTripleProduct

/-- Bivariate Laurent polynomial ring `ℤ[q, q⁻¹, z, z⁻¹]`. -/
abbrev LaurentQZ := AddMonoidAlgebra ℤ (ℤ × ℤ)

/-- Monomial `q^a z^b` in `LaurentQZ`. -/
def qzMon (a b : ℤ) : LaurentQZ :=
  AddMonoidAlgebra.single (a, b) 1

private lemma qzMon_zero : qzMon 0 0 = 1 := rfl

private lemma qzMon_mul (a₁ b₁ a₂ b₂ : ℤ) :
    qzMon a₁ b₁ * qzMon a₂ b₂ = qzMon (a₁ + a₂) (b₁ + b₂) := by
  simp [qzMon, AddMonoidAlgebra.single_mul_single]

private lemma coeff_mul_qzMon (f : LaurentQZ) (a b x y : ℤ) :
    (f * qzMon a b).coeff (x, y) = f.coeff (x - a, y - b) := by
  rw [qzMon, AddMonoidAlgebra.coeff_mul]
  trans (f.coeff.sum fun p v => if p + (a, b) = (x, y) then v else 0)
  · refine Finsupp.sum_congr fun p _ => ?_
    rw [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]
    simp
  · rw [Finsupp.sum]
    by_cases hmem : (x - a, y - b) ∈ f.coeff.support
    · rw [Finset.sum_eq_single (x - a, y - b)]
      · simp [Prod.mk_add_mk]
      · intro p _ hne
        rw [if_neg]
        intro heq
        apply hne
        have h1 : p.1 + a = x := congrArg Prod.fst heq
        have h2 : p.2 + b = y := congrArg Prod.snd heq
        ext <;> dsimp <;> omega
      · intro hnot; exact (hnot hmem).elim
    · rw [Finset.sum_eq_zero]
      · exact (Finsupp.notMem_support_iff.mp hmem).symm
      · intro p hp
        rw [if_neg]
        intro heq
        apply hmem
        have h1 : p.1 + a = x := congrArg Prod.fst heq
        have h2 : p.2 + b = y := congrArg Prod.snd heq
        have hp_eq : p = (x - a, y - b) := by ext <;> dsimp <;> omega
        exact hp_eq ▸ hp

private lemma coeff_qzMon_mul (a b : ℤ) (f : LaurentQZ) (x y : ℤ) :
    (qzMon a b * f).coeff (x, y) = f.coeff (x - a, y - b) := by
  rw [mul_comm, coeff_mul_qzMon]

/-- The `M`-th partial double product `∏_{n=1}^{M} (1 + z q^{2n-1})(1 + z⁻¹ q^{2n-1})`. -/
def jacobiDoublePartial (M : ℕ) : LaurentQZ :=
  ∏ n ∈ Finset.Icc 1 M,
    (1 + qzMon (2 * (n : ℤ) - 1) 1) * (1 + qzMon (2 * (n : ℤ) - 1) (-1))

/-- The `M`-th partial Jacobi triple product
`∏_{n=1}^{M} (1 - q^{2n})(1 + z q^{2n-1})(1 + z⁻¹ q^{2n-1})`. -/
def jacobiTriplePartial (M : ℕ) : LaurentQZ :=
  (∏ n ∈ Finset.Icc 1 M, (1 - qzMon (2 * (n : ℤ)) 0)) * jacobiDoublePartial M

lemma jacobiDoublePartial_succ (M : ℕ) :
    jacobiDoublePartial (M + 1) =
      jacobiDoublePartial M *
        ((1 + qzMon (2 * (M : ℤ) + 1) 1) * (1 + qzMon (2 * (M : ℤ) + 1) (-1))) := by
  unfold jacobiDoublePartial
  have hIcc : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hIcc, Finset.prod_insert (by simp), mul_comm]
  push_cast
  ring_nf

private lemma coeff_jacobiDoublePartial_succ (M : ℕ) (a b : ℤ) :
    (jacobiDoublePartial (M + 1)).coeff (a, b) =
      (jacobiDoublePartial M).coeff (a, b) +
      (jacobiDoublePartial M).coeff (a - (2 * (M : ℤ) + 1), b - 1) +
      (jacobiDoublePartial M).coeff (a - (2 * (M : ℤ) + 1), b + 1) +
      (jacobiDoublePartial M).coeff (a - (4 * (M : ℤ) + 2), b) := by
  rw [jacobiDoublePartial_succ]
  have hexp : (1 + qzMon (2 * (M : ℤ) + 1) 1) * (1 + qzMon (2 * (M : ℤ) + 1) (-1)) =
      1 + qzMon (2 * (M : ℤ) + 1) 1 + qzMon (2 * (M : ℤ) + 1) (-1) + qzMon (4 * (M : ℤ) + 2) 0 := by
    have hmul : qzMon (2 * (M : ℤ) + 1) 1 * qzMon (2 * (M : ℤ) + 1) (-1) =
        qzMon (4 * (M : ℤ) + 2) 0 := by
      rw [qzMon_mul]; congr 1; ring
    calc (1 + qzMon (2 * (M : ℤ) + 1) 1) * (1 + qzMon (2 * (M : ℤ) + 1) (-1))
        = 1 + qzMon (2 * (M : ℤ) + 1) 1 + qzMon (2 * (M : ℤ) + 1) (-1) +
            qzMon (2 * (M : ℤ) + 1) 1 * qzMon (2 * (M : ℤ) + 1) (-1) := by ring
      _ = 1 + qzMon (2 * (M : ℤ) + 1) 1 + qzMon (2 * (M : ℤ) + 1) (-1) +
            qzMon (4 * (M : ℤ) + 2) 0 := by rw [hmul]
  rw [hexp, mul_add, mul_add, mul_add, mul_one]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_mul_qzMon,
    sub_neg_eq_add, sub_zero]

/-- Sharp quadratic support bound for `jacobiDoublePartial M`:
every nonzero `(a, b)` satisfies `|b| ≤ M` and `b^2 ≤ a`! -/
private lemma jacobiDoublePartial_support_bound (M : ℕ) (a b : ℤ)
    (h : (jacobiDoublePartial M).coeff (a, b) ≠ 0) :
    |b| ≤ (M : ℤ) ∧ b ^ 2 ≤ a := by
  induction M generalizing a b with
  | zero =>
    have h0 : jacobiDoublePartial 0 = qzMon 0 0 := by simp [jacobiDoublePartial, qzMon_zero]
    rw [h0, qzMon, AddMonoidAlgebra.coeff_single] at h
    have hab : (a, b) = (0, 0) := by
      by_contra hne
      exact h (Finsupp.single_eq_of_ne hne)
    rcases Prod.mk.inj hab with ⟨rfl, rfl⟩
    simp
  | succ M ih =>
    rw [coeff_jacobiDoublePartial_succ] at h
    by_cases h1 : (jacobiDoublePartial M).coeff (a, b) ≠ 0
    · obtain ⟨hb, ha⟩ := ih a b h1
      exact ⟨by omega, ha⟩
    · by_cases h2 : (jacobiDoublePartial M).coeff (a - (2 * (M : ℤ) + 1), b - 1) ≠ 0
      · obtain ⟨hb, ha⟩ := ih _ _ h2
        rw [abs_le] at hb ⊢
        push_cast
        constructor
        · constructor <;> omega
        · nlinarith
      · by_cases h3 : (jacobiDoublePartial M).coeff (a - (2 * (M : ℤ) + 1), b + 1) ≠ 0
        · obtain ⟨hb, ha⟩ := ih _ _ h3
          rw [abs_le] at hb ⊢
          push_cast
          constructor
          · constructor <;> omega
          · nlinarith
        · have h4 : (jacobiDoublePartial M).coeff (a - (4 * (M : ℤ) + 2), b) ≠ 0 := by
            push Not at h1 h2 h3
            rw [h1, h2, h3] at h
            simpa using h
          obtain ⟨hb, ha⟩ := ih _ _ h4
          push_cast
          exact ⟨by omega, by linarith⟩

private lemma jacobiDoublePartial_eq_zero_of_neg (M : ℕ) {a : ℤ} (ha : a < 0) (b : ℤ) :
    (jacobiDoublePartial M).coeff (a, b) = 0 := by
  by_contra hne
  have ⟨_, hsq⟩ := jacobiDoublePartial_support_bound M a b hne
  nlinarith

/-- Stabilization of `jacobiDoublePartial M` for `a ≤ 2 * M`. -/
private lemma jacobiDoublePartial_eq_of_le {M M' : ℕ} (hMM' : M ≤ M') {a : ℤ}
    (ha : a ≤ 2 * (M : ℤ)) (b : ℤ) :
    (jacobiDoublePartial M').coeff (a, b) = (jacobiDoublePartial M).coeff (a, b) := by
  induction M', hMM' using Nat.le_induction with
  | base => rfl
  | succ k hMk ih =>
    rw [coeff_jacobiDoublePartial_succ,
      jacobiDoublePartial_eq_zero_of_neg k (a := a - (2 * (k : ℤ) + 1)) (by omega),
      jacobiDoublePartial_eq_zero_of_neg k (a := a - (2 * (k : ℤ) + 1)) (by omega),
      jacobiDoublePartial_eq_zero_of_neg k (a := a - (4 * (k : ℤ) + 2)) (by omega)]
    simp only [add_zero]
    exact ih

/-- The `z^k`-coefficient power series `c_k(q) ∈ ℤ⟦q⟧` of `∏_{n ≥ 1} (1 + z q^{2n-1})(1 + z⁻¹ q^{2n-1})`. -/
private def jacobiC (k : ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun N => (jacobiDoublePartial N).coeff ((N : ℤ), k)

private lemma coeff_jacobiC_eq {N M : ℕ} (h : (N : ℤ) ≤ 2 * (M : ℤ)) (k : ℤ) :
    PowerSeries.coeff N (jacobiC k) = (jacobiDoublePartial M).coeff ((N : ℤ), k) := by
  simp only [jacobiC, PowerSeries.coeff_mk]
  by_cases hNM : N ≤ M
  · exact (jacobiDoublePartial_eq_of_le hNM (by omega) k).symm
  · exact jacobiDoublePartial_eq_of_le (by omega) h k

/-- Symmetry `c_{-k}(q) = c_k(q)` by `z ↔ z⁻¹`. -/
private lemma jacobiC_neg (k : ℤ) : jacobiC (-k) = jacobiC k := by
  let flipZ : ℤ × ℤ →+ ℤ × ℤ :=
    { toFun := fun p => (p.1, -p.2)
      map_zero' := by ext <;> simp
      map_add' := fun p q => by
        apply Prod.ext
        · rfl
        · dsimp; ring }
  have hflip_inj : Function.Injective flipZ := by
    intro p q h
    have h1 : (flipZ p).1 = (flipZ q).1 := congrArg Prod.fst h
    have h2 : (flipZ p).2 = (flipZ q).2 := congrArg Prod.snd h
    dsimp [flipZ] at h1 h2
    ext <;> omega
  have hfix : ∀ M, AddMonoidAlgebra.mapDomainRingHom ℤ flipZ (jacobiDoublePartial M) =
      jacobiDoublePartial M := by
    intro M
    unfold jacobiDoublePartial
    rw [map_prod]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [map_mul, map_add, map_add, map_one, mul_comm]
    simp only [qzMon, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
      flipZ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, neg_neg]
  apply PowerSeries.ext
  intro N
  simp only [jacobiC, PowerSeries.coeff_mk]
  have hN := congrFun (congrArg (fun x => (AddMonoidAlgebra.coeff x : ℤ × ℤ → ℤ)) (hfix N))
    ((N : ℤ), k)
  rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain] at hN
  have heval : (Finsupp.mapDomain flipZ (jacobiDoublePartial N).coeff) (flipZ ((N : ℤ), -k)) =
      (jacobiDoublePartial N).coeff ((N : ℤ), -k) :=
    Finsupp.mapDomain_apply hflip_inj (jacobiDoublePartial N).coeff ((N : ℤ), -k)
  have hpt : flipZ ((N : ℤ), -k) = ((N : ℤ), k) := by ext <;> simp [flipZ]
  rw [hpt] at heval
  rw [← heval, hN]

/-- Helper: index shift on `Icc 2 (M + 1)`. -/
private lemma prod_Icc_shift (M : ℕ) (f : ℕ → LaurentQZ) :
    ∏ n ∈ Finset.Icc 2 (M + 1), f n = ∏ n ∈ Finset.Icc 1 M, f (n + 1) := by
  refine Finset.prod_nbij' (fun n => n - 1) (fun n => n + 1) ?_ ?_ ?_ ?_ ?_
  · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
  · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
  · intro n hn; simp only [Finset.mem_Icc] at hn; omega
  · intro n _; omega
  · intro n hn; simp only [Finset.mem_Icc] at hn; congr 1; omega

/-- Helper: product of elements supported in `a ≥ 0` is supported in `a ≥ 0`. -/
private lemma mul_eq_zero_of_neg {f g : LaurentQZ}
    (hf : ∀ a b, a < 0 → f.coeff (a, b) = 0) (hg : ∀ a b, a < 0 → g.coeff (a, b) = 0)
    {a : ℤ} (ha : a < 0) (b : ℤ) :
    (f * g).coeff (a, b) = 0 := by
  rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Finsupp.sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  split_ifs with heq
  · have h1 : p.1 + q.1 = a := congrArg Prod.fst heq
    by_cases hp1 : p.1 < 0
    · rw [hf p.1 p.2 hp1, zero_mul]
    · have hq1 : q.1 < 0 := by omega
      rw [hg q.1 q.2 hq1, mul_zero]
  · rfl

private lemma one_add_qzMon_eq_zero_of_neg {c : ℤ} (hc : 0 ≤ c) (d : ℤ)
    {a : ℤ} (ha : a < 0) (b : ℤ) :
    (1 + qzMon c d).coeff (a, b) = 0 := by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ← qzMon_zero, qzMon, qzMon,
    AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single,
    Finsupp.single_eq_of_ne (by intro h; have := congrArg Prod.fst h; dsimp at this; omega),
    Finsupp.single_eq_of_ne (by intro h; have := congrArg Prod.fst h; dsimp at this; omega),
    add_zero]

private lemma prod_one_add_qzMon_eq_zero_of_neg {s : Finset ℕ} {c : ℕ → ℤ} {d : ℤ}
    (hc : ∀ n ∈ s, 0 ≤ c n) {a : ℤ} (ha : a < 0) (b : ℤ) :
    (∏ n ∈ s, (1 + qzMon (c n) d)).coeff (a, b) = 0 := by
  classical
  induction s using Finset.induction_on generalizing a b with
  | empty =>
    rw [Finset.prod_empty, ← qzMon_zero, qzMon, AddMonoidAlgebra.coeff_single]
    exact Finsupp.single_eq_of_ne (by intro h; have := congrArg Prod.fst h; dsimp at this; omega)
  | insert x s hx ih =>
    rw [Finset.prod_insert hx]
    exact mul_eq_zero_of_neg
      (fun a' b' ha' => one_add_qzMon_eq_zero_of_neg (hc x (Finset.mem_insert_self _ _)) d ha' b')
      (fun a' b' ha' => ih (fun n hn => hc n (Finset.mem_insert_of_mem hn)) ha' b')
      ha b

/-- **Shift Recurrence**: `jacobiC (k + 1) = jacobiC k * X^(2*k + 1)` for every `k : ℕ`! -/
private lemma jacobiC_succ (k : ℕ) :
    jacobiC ((k : ℤ) + 1) = jacobiC (k : ℤ) * PowerSeries.X ^ (2 * k + 1) := by
  let shiftMap : ℤ × ℤ →+ ℤ × ℤ :=
    { toFun := fun p => (p.1 + 2 * p.2, p.2)
      map_zero' := by ext <;> simp
      map_add' := fun p q => by
        apply Prod.ext
        · dsimp; ring
        · rfl }
  have hshift_inj : Function.Injective shiftMap := by
    intro p q h
    have h1 : (shiftMap p).1 = (shiftMap q).1 := congrArg Prod.fst h
    have h2 : (shiftMap p).2 = (shiftMap q).2 := congrArg Prod.snd h
    dsimp [shiftMap] at h1 h2
    ext <;> omega
  let Φ : LaurentQZ →+* LaurentQZ := AddMonoidAlgebra.mapDomainRingHom ℤ shiftMap
  have hB_prod : ∀ M : ℕ, 1 ≤ M →
      qzMon 1 1 * Φ (jacobiDoublePartial M) =
        (1 + qzMon 1 1) *
          (∏ n ∈ Finset.Icc 1 M, (1 + qzMon (2 * (n : ℤ) + 1) 1)) *
          (∏ n ∈ Finset.Icc 1 (M - 1), (1 + qzMon (2 * (n : ℤ) - 1) (-1))) := by
    intro M hM
    unfold jacobiDoublePartial
    rw [Finset.prod_mul_distrib, map_mul, map_prod, map_prod]
    have h1 : ∏ n ∈ Finset.Icc 1 M, Φ (1 + qzMon (2 * (n : ℤ) - 1) 1) =
        ∏ n ∈ Finset.Icc 1 M, (1 + qzMon (2 * (n : ℤ) + 1) 1) := by
      refine Finset.prod_congr rfl fun n _ => ?_
      simp only [Φ, map_add, map_one, qzMon, AddMonoidAlgebra.mapDomainRingHom_apply,
        AddMonoidAlgebra.mapDomain_single, shiftMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      have hpt : (2 * (n : ℤ) - 1 + 2 * 1, (1 : ℤ)) = (2 * (n : ℤ) + 1, 1) := by
        apply Prod.ext
        · ring
        · rfl
      rw [hpt]
    have h2 : ∏ n ∈ Finset.Icc 1 M, Φ (1 + qzMon (2 * (n : ℤ) - 1) (-1)) =
        (1 + qzMon (-1) (-1)) * ∏ n ∈ Finset.Icc 1 (M - 1), (1 + qzMon (2 * (n : ℤ) - 1) (-1)) := by
      have hIcc : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.prod_insert (by simp)]
      congr 1
      · simp only [Φ, map_add, map_one, qzMon, AddMonoidAlgebra.mapDomainRingHom_apply,
          AddMonoidAlgebra.mapDomain_single, shiftMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        have hpt : (2 * ((1 : ℕ) : ℤ) - 1 + 2 * -1, (-1 : ℤ)) = (-1, -1) := by ext <;> norm_num
        rw [hpt]
      · have hM1 : M = (M - 1) + 1 := by omega
        rw [hM1, prod_Icc_shift (M - 1) (fun n => Φ (1 + qzMon (2 * (n : ℤ) - 1) (-1)))]
        refine Finset.prod_congr rfl fun n _ => ?_
        simp only [Φ, map_add, map_one, qzMon, AddMonoidAlgebra.mapDomainRingHom_apply,
          AddMonoidAlgebra.mapDomain_single, shiftMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        push_cast
        have hpt : (2 * ((n : ℤ) + 1) - 1 + -2, (-1 : ℤ)) = (2 * (n : ℤ) - 1, -1) := by
          apply Prod.ext
          · ring
          · rfl
        rw [hpt]
    rw [h1, h2]
    have hqz : qzMon 1 1 * (1 + qzMon (-1) (-1)) = 1 + qzMon 1 1 := by
      rw [mul_add, mul_one, qzMon_mul]
      have : qzMon (1 + -1) (1 + -1) = 1 := by norm_num [qzMon_zero]
      rw [this, add_comm]
    calc qzMon 1 1 * ((∏ n ∈ Finset.Icc 1 M, (1 + qzMon (2 * (n : ℤ) + 1) 1)) *
            ((1 + qzMon (-1) (-1)) * ∏ n ∈ Finset.Icc 1 (M - 1), (1 + qzMon (2 * (n : ℤ) - 1) (-1))))
        = (qzMon 1 1 * (1 + qzMon (-1) (-1))) *
            (∏ n ∈ Finset.Icc 1 M, (1 + qzMon (2 * (n : ℤ) + 1) 1)) *
            (∏ n ∈ Finset.Icc 1 (M - 1), (1 + qzMon (2 * (n : ℤ) - 1) (-1))) := by ring
      _ = _ := by rw [hqz]
  have hB_eq : ∀ M : ℕ, 1 ≤ M →
      (1 + qzMon (2 * (M : ℤ) - 1) (-1)) * (qzMon 1 1 * Φ (jacobiDoublePartial M)) =
        (1 + qzMon (2 * (M : ℤ) + 1) 1) * jacobiDoublePartial M := by
    intro M hM
    rw [hB_prod M hM]
    unfold jacobiDoublePartial
    rw [Finset.prod_mul_distrib]
    have hpos : (1 + qzMon 1 1) * (∏ n ∈ Finset.Icc 1 M, (1 + qzMon (2 * (n : ℤ) + 1) 1)) =
        (1 + qzMon (2 * (M : ℤ) + 1) 1) * (∏ n ∈ Finset.Icc 1 M, (1 + qzMon (2 * (n : ℤ) - 1) 1)) := by
      have hL : Finset.Icc 1 (M + 1) = insert 1 (Finset.Icc 2 (M + 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hR : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hprod : ∏ n ∈ Finset.Icc 1 (M + 1), (1 + qzMon (2 * (n : ℤ) - 1) 1) =
          ∏ n ∈ Finset.Icc 1 (M + 1), (1 + qzMon (2 * (n : ℤ) - 1) 1) := rfl
      conv_lhs at hprod => rw [hL, Finset.prod_insert (by simp)]
      conv_rhs at hprod => rw [hR, Finset.prod_insert (by simp)]
      rw [prod_Icc_shift M (fun n => 1 + qzMon (2 * (n : ℤ) - 1) 1)] at hprod
      have hshift_eq : (∏ n ∈ Finset.Icc 1 M, (1 + qzMon (2 * ((n + 1 : ℕ) : ℤ) - 1) 1)) =
          ∏ n ∈ Finset.Icc 1 M, (1 + qzMon (2 * (n : ℤ) + 1) 1) := by
        refine Finset.prod_congr rfl fun n _ => ?_; push_cast; ring_nf
      rw [hshift_eq] at hprod
      have h1 : (2 * ((1 : ℕ) : ℤ) - 1) = 1 := by norm_num
      have hM1 : (2 * ((M + 1 : ℕ) : ℤ) - 1) = 2 * (M : ℤ) + 1 := by push_cast; ring
      rw [h1, hM1] at hprod
      exact hprod
    have hneg : (1 + qzMon (2 * (M : ℤ) - 1) (-1)) *
        (∏ n ∈ Finset.Icc 1 (M - 1), (1 + qzMon (2 * (n : ℤ) - 1) (-1))) =
        ∏ n ∈ Finset.Icc 1 M, (1 + qzMon (2 * (n : ℤ) - 1) (-1)) := by
      have hIcc : Finset.Icc 1 M = insert M (Finset.Icc 1 (M - 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.prod_insert (by simp only [Finset.mem_Icc]; omega)]
    calc (1 + qzMon (2 * (M : ℤ) - 1) (-1)) *
            ((1 + qzMon 1 1) * (∏ n ∈ Finset.Icc 1 M, (1 + qzMon (2 * (n : ℤ) + 1) 1)) *
              (∏ n ∈ Finset.Icc 1 (M - 1), (1 + qzMon (2 * (n : ℤ) - 1) (-1))))
        = ((1 + qzMon 1 1) * (∏ n ∈ Finset.Icc 1 M, (1 + qzMon (2 * (n : ℤ) + 1) 1))) *
            ((1 + qzMon (2 * (M : ℤ) - 1) (-1)) *
              (∏ n ∈ Finset.Icc 1 (M - 1), (1 + qzMon (2 * (n : ℤ) - 1) (-1)))) := by ring
      _ = ((1 + qzMon (2 * (M : ℤ) + 1) 1) *
            (∏ n ∈ Finset.Icc 1 M, (1 + qzMon (2 * (n : ℤ) - 1) 1))) *
            (∏ n ∈ Finset.Icc 1 M, (1 + qzMon (2 * (n : ℤ) - 1) (-1))) := by rw [hpos, hneg]
      _ = _ := by ring
  apply PowerSeries.ext
  intro N
  rw [coeff_mul_X_pow_eq]
  let M : ℕ := N + 1
  have hM1 : 1 ≤ M := by omega
  have hB_neg : ∀ a b, a < 0 → (qzMon 1 1 * Φ (jacobiDoublePartial M)).coeff (a, b) = 0 := by
    intro a b ha
    rw [hB_prod M hM1]
    refine mul_eq_zero_of_neg
      (fun a' b' ha' => mul_eq_zero_of_neg
        (fun a'' b'' ha'' => one_add_qzMon_eq_zero_of_neg (by norm_num) 1 ha'' b'')
        (fun a'' b'' ha'' => prod_one_add_qzMon_eq_zero_of_neg (fun n hn => by
          have := (Finset.mem_Icc.mp hn).1; omega) ha'' b'')
        ha' b')
      (fun a' b' ha' => prod_one_add_qzMon_eq_zero_of_neg (fun n hn => by
        have := (Finset.mem_Icc.mp hn).1; omega) ha' b')
      ha b
  have hident := congrFun
    (congrArg (fun x => (AddMonoidAlgebra.coeff x : ℤ × ℤ → ℤ)) (hB_eq M hM1))
    ((N : ℤ), (k : ℤ) + 1)
  have hLHS : ((1 + qzMon (2 * (M : ℤ) - 1) (-1)) * (qzMon 1 1 * Φ (jacobiDoublePartial M))).coeff
      ((N : ℤ), (k : ℤ) + 1) =
      (qzMon 1 1 * Φ (jacobiDoublePartial M)).coeff ((N : ℤ), (k : ℤ) + 1) := by
    rw [add_mul, one_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      coeff_qzMon_mul (2 * (M : ℤ) - 1) (-1),
      hB_neg ((N : ℤ) - (2 * (M : ℤ) - 1)) _ (by omega), add_zero]
  have hRHS : ((1 + qzMon (2 * (M : ℤ) + 1) 1) * jacobiDoublePartial M).coeff
      ((N : ℤ), (k : ℤ) + 1) =
      (jacobiDoublePartial M).coeff ((N : ℤ), (k : ℤ) + 1) := by
    rw [add_mul, one_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      coeff_qzMon_mul (2 * (M : ℤ) + 1) 1,
      jacobiDoublePartial_eq_zero_of_neg M (a := (N : ℤ) - (2 * (M : ℤ) + 1)) (by omega), add_zero]
  rw [hLHS, hRHS] at hident
  have hBeval : (qzMon 1 1 * Φ (jacobiDoublePartial M)).coeff ((N : ℤ), (k : ℤ) + 1) =
      (jacobiDoublePartial M).coeff ((N : ℤ) - (2 * (k : ℤ) + 1), (k : ℤ)) := by
    rw [coeff_qzMon_mul]
    dsimp only [Φ]
    rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain]
    have hpt : shiftMap ((N : ℤ) - (2 * (k : ℤ) + 1), (k : ℤ)) =
        ((N : ℤ) - 1, (k : ℤ) + 1 - 1) := by
      ext <;> dsimp [shiftMap] <;> ring
    rw [← hpt]
    exact Finsupp.mapDomain_apply hshift_inj (jacobiDoublePartial M).coeff _
  rw [hBeval] at hident
  rw [coeff_jacobiC_eq (M := M) (by dsimp [M]; omega), ← hident]
  split_ifs with hle
  · rw [coeff_jacobiC_eq (M := M) (by dsimp [M]; omega)]
    congr 2
    omega
  · exact jacobiDoublePartial_eq_zero_of_neg M (by omega) (k : ℤ)

/-- **Closed form for `c_k(q)`**: for every `k : ℤ`, `jacobiC k = jacobiC 0 * X^(k.natAbs ^ 2)`! -/
private lemma jacobiC_eq (k : ℤ) :
    jacobiC k = jacobiC 0 * PowerSeries.X ^ (k.natAbs ^ 2) := by
  have hnat : ∀ m : ℕ, jacobiC (m : ℤ) = jacobiC 0 * PowerSeries.X ^ (m ^ 2) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      push_cast
      rw [jacobiC_succ, ih, mul_assoc, ← pow_add]
      congr 2
      ring
  rcases Int.natAbs_eq k with hk | hk
  · conv_lhs => rw [hk]
    exact hnat k.natAbs
  · have hneg : k = -(k.natAbs : ℤ) := by omega
    conv_lhs => rw [hneg, jacobiC_neg]
    exact hnat k.natAbs

/-- Evaluation ring homomorphism `LaurentQZ →+* AddMonoidAlgebra R ℤ` at `z = u` (`u : Rˣ`). -/
private def evalZHom {R : Type*} [CommRing R] (u : Rˣ) :
    LaurentQZ →+* AddMonoidAlgebra R ℤ :=
  AddMonoidAlgebra.lift ℤ (AddMonoidAlgebra R ℤ) (ℤ × ℤ)
    { toFun := fun p => AddMonoidAlgebra.single (Multiplicative.toAdd p).1
        ((u ^ (Multiplicative.toAdd p).2 : Rˣ) : R)
      map_one' := by
        simp [AddMonoidAlgebra.one_def]
      map_mul' := fun p q => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, zpow_add, Units.val_mul,
          AddMonoidAlgebra.single_mul_single] }

private lemma evalZHom_qzMon {R : Type*} [CommRing R] (u : Rˣ) (a b : ℤ) :
    evalZHom u (qzMon a b) = AddMonoidAlgebra.single a ((u ^ b : Rˣ) : R) := by
  simp [evalZHom, qzMon]

private lemma coeff_evalZHom {R : Type*} [CommRing R] (u : Rˣ) (f : LaurentQZ) (a : ℤ) :
    (evalZHom u f).coeff a =
      f.coeff.sum fun p v => if p.1 = a then (v : R) * ((u ^ p.2 : Rˣ) : R) else 0 := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  simp only [Finsupp.sum, map_sum]
  have hcoeff_sum : ∀ (s : Finset (ℤ × ℤ)) (g : ℤ × ℤ → AddMonoidAlgebra R ℤ),
      (∑ p ∈ s, g p).coeff a = ∑ p ∈ s, (g p).coeff a := by
    intro s g
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, ih]
  rw [hcoeff_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hsingle : AddMonoidAlgebra.single p (f.coeff p) = (f.coeff p : ℤ) • qzMon p.1 p.2 := by
    simp [qzMon, AddMonoidAlgebra.smul_single]
  rw [hsingle, map_zsmul, evalZHom_qzMon, AddMonoidAlgebra.smul_single, zsmul_eq_mul,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- Formal theta series `∑_{k ∈ ℤ} u^k q^{k^2} ∈ R⟦q⟧` for a unit `u : Rˣ`. -/
private def thetaUnitSeries {R : Type*} [CommRing R] (u : Rˣ) : PowerSeries R :=
  PowerSeries.mk fun m =>
    ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), if (m : ℤ) = k ^ 2 then ((u ^ k : Rˣ) : R) else 0

/-- Evaluation of `jacobiDoublePartial M` at `z = u` matches `jacobiC 0 * thetaUnitSeries u` up to degree `M`. -/
private lemma coeff_evalZHom_jacobiDoublePartial {R : Type*} [CommRing R] (u : Rˣ)
    {N M : ℕ} (hNM : N ≤ M) :
    (evalZHom u (jacobiDoublePartial M)).coeff (N : ℤ) =
      PowerSeries.coeff N (PowerSeries.map (Int.castRingHom R) (jacobiC 0) * thetaUnitSeries u) := by
  rw [coeff_evalZHom]
  have hsum_eq : (jacobiDoublePartial M).coeff.sum (fun p v =>
      if p.1 = (N : ℤ) then (v : R) * ((u ^ p.2 : Rˣ) : R) else 0) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (((jacobiDoublePartial M).coeff ((N : ℤ), k) : ℤ) : R) * ((u ^ k : Rˣ) : R) := by
    rw [Finsupp.sum]
    have hsub : (jacobiDoublePartial M).coeff.support.filter (fun p => p.1 = (N : ℤ)) ⊆
        (Finset.Icc (-(N : ℤ)) (N : ℤ)).image (fun k => ((N : ℤ), k)) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hsupp, hp1⟩
      have hne : (jacobiDoublePartial M).coeff p ≠ 0 := Finsupp.mem_support_iff.mp hsupp
      have ⟨_, hsq⟩ := jacobiDoublePartial_support_bound M p.1 p.2 hne
      rw [hp1] at hsq
      refine Finset.mem_image.mpr ⟨p.2, Finset.mem_Icc.mpr ?_, by ext <;> simp [hp1]⟩
      have habs : |p.2| ≤ (N : ℤ) := by nlinarith [sq_abs p.2, abs_nonneg p.2]
      exact abs_le.mp habs
    rw [← Finset.sum_filter]
    rw [Finset.sum_subset hsub]
    · rw [Finset.sum_image]
      intro x _ y _ hxy
      exact congrArg Prod.snd hxy
    · intro p hp hnot
      rcases Finset.mem_image.mp hp with ⟨k, _, rfl⟩
      have h0 : (jacobiDoublePartial M).coeff ((N : ℤ), k) = 0 := by
        by_contra hne
        exact hnot (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, rfl⟩)
      simp [h0]
  rw [hsum_eq]
  have hterm : ∀ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (((jacobiDoublePartial M).coeff ((N : ℤ), k) : ℤ) : R) * ((u ^ k : Rˣ) : R) =
        if k.natAbs ^ 2 ≤ N then
          ((PowerSeries.coeff (N - k.natAbs ^ 2) (jacobiC 0) : ℤ) : R) * ((u ^ k : Rˣ) : R)
        else 0 := by
    intro k _
    rw [← coeff_jacobiC_eq (M := M) (by omega), jacobiC_eq, coeff_mul_X_pow_eq]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm]
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (PowerSeries.map (Int.castRingHom R) (jacobiC 0)) *
      PowerSeries.coeff b (thetaUnitSeries u))]
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom, thetaUnitSeries, PowerSeries.coeff_mk,
    Finset.mul_sum]
  trans ∑ a ∈ Finset.range (N + 1), ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      if ((N - a : ℕ) : ℤ) = k ^ 2 then
        ((PowerSeries.coeff a (jacobiC 0) : ℤ) : R) * ((u ^ k : Rˣ) : R)
      else 0
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsq : ((k.natAbs ^ 2 : ℕ) : ℤ) = k ^ 2 := by
      rw [Nat.cast_pow, Int.natAbs_sq]
    split_ifs with hle
    · rw [Finset.sum_eq_single (N - k.natAbs ^ 2)]
      · rw [if_pos (by omega)]
      · intro a ha hne
        rw [if_neg]
        intro heq
        apply hne
        have ha' := Finset.mem_range.mp ha
        omega
      · intro hnot
        exfalso
        exact hnot (Finset.mem_range.mpr (by omega))
    · refine (Finset.sum_eq_zero fun a ha => ?_).symm
      rw [if_neg]
      intro heq
      have ha' := Finset.mem_range.mp ha
      omega
  · refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := Finset.mem_range.mp ha
    have hsub : Finset.Icc (-((N - a : ℕ) : ℤ)) ((N - a : ℕ) : ℤ) ⊆
        Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    symm
    rw [Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp
    · intro k _ hnot
      rw [if_neg, mul_zero]
      intro heq
      apply hnot
      simp only [Finset.mem_Icc]
      have habs : |k| ≤ ((N - a : ℕ) : ℤ) := by nlinarith [sq_abs k, abs_nonneg k]
      exact abs_le.mp habs

/-- Partial product `∏_{n=1}^M (1 - q^{2n-1})^2` in `PowerSeries ℤ`. -/
private def oddMinusSqPartial (M : ℕ) : PowerSeries ℤ :=
  ∏ n ∈ Finset.Icc 1 M, (1 - PowerSeries.X ^ (2 * n - 1)) ^ 2

private lemma oddMinusSqPartial_succ (M : ℕ) :
    oddMinusSqPartial (M + 1) =
      oddMinusSqPartial M * (1 - PowerSeries.X ^ (2 * M + 1)) ^ 2 := by
  unfold oddMinusSqPartial
  have hIcc : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hIcc, Finset.prod_insert (by simp), mul_comm]
  have h1 : 2 * (M + 1) - 1 = 2 * M + 1 := by omega
  rw [h1]

private lemma coeff_oddMinusSqPartial_eq_of_le {N M : ℕ} (h : N ≤ M) :
    PowerSeries.coeff N (oddMinusSqPartial M) = PowerSeries.coeff N (oddMinusSqPartial N) := by
  induction M, h using Nat.le_induction with
  | base => rfl
  | succ k hNk ih =>
    rw [oddMinusSqPartial_succ, sq, ← mul_assoc,
      coeff_mul_one_sub_X_pow_of_lt _ (by omega),
      coeff_mul_one_sub_X_pow_of_lt _ (by omega), ih]

private def oddMinusSqSeries : PowerSeries ℤ :=
  PowerSeries.mk fun N => PowerSeries.coeff N (oddMinusSqPartial N)

private lemma coeff_oddMinusSqSeries_eq {N M : ℕ} (h : N ≤ M) :
    PowerSeries.coeff N oddMinusSqSeries = PowerSeries.coeff N (oddMinusSqPartial M) := by
  simp only [oddMinusSqSeries, PowerSeries.coeff_mk]
  exact (coeff_oddMinusSqPartial_eq_of_le h).symm

/-- Partial product `∏_{n=1}^M (1 + q^{4n-2})` in `PowerSeries ℤ`. -/
private def mod4PlusPartial (M : ℕ) : PowerSeries ℤ :=
  ∏ n ∈ Finset.Icc 1 M, (1 + PowerSeries.X ^ (4 * n - 2))

private lemma mod4PlusPartial_succ (M : ℕ) :
    mod4PlusPartial (M + 1) =
      mod4PlusPartial M * (1 + PowerSeries.X ^ (4 * M + 2)) := by
  unfold mod4PlusPartial
  have hIcc : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hIcc, Finset.prod_insert (by simp), mul_comm]
  have h1 : 4 * (M + 1) - 2 = 4 * M + 2 := by omega
  rw [h1]

private lemma coeff_mod4PlusPartial_eq_of_le {N M : ℕ} (h : N ≤ M) :
    PowerSeries.coeff N (mod4PlusPartial M) = PowerSeries.coeff N (mod4PlusPartial N) := by
  induction M, h using Nat.le_induction with
  | base => rfl
  | succ k hNk ih =>
    rw [mod4PlusPartial_succ, coeff_mul_one_add_X_pow_of_lt _ (by omega), ih]

private def mod4PlusSeries : PowerSeries ℤ :=
  PowerSeries.mk fun N => PowerSeries.coeff N (mod4PlusPartial N)

private lemma coeff_mod4PlusSeries_eq {N M : ℕ} (h : N ≤ M) :
    PowerSeries.coeff N mod4PlusSeries = PowerSeries.coeff N (mod4PlusPartial M) := by
  simp only [mod4PlusSeries, PowerSeries.coeff_mk]
  exact (coeff_mod4PlusPartial_eq_of_le h).symm

/-- Polynomial-to-Laurent-polynomial embedding `R[X] →+* AddMonoidAlgebra R ℤ`. -/
private def polyToLaurent {R : Type*} [CommRing R] : Polynomial R →+* AddMonoidAlgebra R ℤ :=
  Polynomial.eval₂RingHom (AddMonoidAlgebra.singleZeroRingHom (R := R) (M := ℤ))
    (AddMonoidAlgebra.single 1 1)

private lemma polyToLaurent_X_pow {R : Type*} [CommRing R] (k : ℕ) :
    polyToLaurent (R := R) (Polynomial.X ^ k) = AddMonoidAlgebra.single (k : ℤ) 1 := by
  induction k with
  | zero => simp [polyToLaurent, AddMonoidAlgebra.one_def]
  | succ k ih =>
    rw [pow_succ, map_mul, ih]
    simp [polyToLaurent, AddMonoidAlgebra.single_mul_single]

private lemma coeff_polyToLaurent_nat {R : Type*} [CommRing R] (p : Polynomial R) (N : ℕ) :
    (polyToLaurent p).coeff (N : ℤ) = p.coeff N := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Polynomial.coeff_add, hp, hq]
  | monomial k r =>
    have hmon : Polynomial.monomial k r = Polynomial.C r * Polynomial.X ^ k := by
      rw [Polynomial.C_mul_X_pow_eq_monomial]
    rw [hmon, map_mul, polyToLaurent_X_pow]
    have hC : polyToLaurent (Polynomial.C r) = AddMonoidAlgebra.single (0 : ℤ) r := by
      simp [polyToLaurent]
    rw [hC, AddMonoidAlgebra.single_mul_single, zero_add, mul_one, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, Polynomial.coeff_C_mul_X_pow]
    by_cases h : k = N
    · subst h; simp
    · have h1 : (k : ℤ) ≠ (N : ℤ) := by omega
      have h2 : N ≠ k := Ne.symm h
      rw [if_neg h1, if_neg h2]

private lemma coeff_coeToPowerSeries {R : Type*} [CommRing R] (p : Polynomial R) (N : ℕ) :
    PowerSeries.coeff N (Polynomial.coeToPowerSeries.ringHom p) = p.coeff N :=
  Polynomial.coeff_coe p N

private lemma negOneUnit_zpow (b : ℤ) :
    ((((-1 : ℤˣ) ^ b : ℤˣ) : ℤ)) = (-1 : ℤ) ^ b.natAbs := by
  rcases Int.natAbs_eq b with hb | hb
  · conv_lhs => rw [hb]
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  · have hneg : b = -(b.natAbs : ℤ) := by omega
    conv_lhs => rw [hneg]
    rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    have hinv : (((-1 : ℤˣ)⁻¹ : ℤˣ) : ℤ) = -1 := by decide
    rw [hinv]

/-- Specialization at `z = -1`: `oddMinusSqSeries = jacobiC 0 * thetaUnitSeries (-1 : ℤˣ)`. -/
private lemma oddMinusSqSeries_eq :
    oddMinusSqSeries = jacobiC 0 * thetaUnitSeries (-1 : ℤˣ) := by
  apply PowerSeries.ext
  intro N
  rw [coeff_oddMinusSqSeries_eq (le_refl N)]
  have heval := coeff_evalZHom_jacobiDoublePartial (-1 : ℤˣ) (le_refl N)
  have hmap_id : PowerSeries.map (Int.castRingHom ℤ) (jacobiC 0) = jacobiC 0 := by
    apply PowerSeries.ext; intro n; simp
  rw [hmap_id] at heval
  rw [← heval]
  let P : Polynomial ℤ := ∏ n ∈ Finset.Icc 1 N, (1 - Polynomial.X ^ (2 * n - 1)) ^ 2
  have hP_ps : Polynomial.coeToPowerSeries.ringHom P = oddMinusSqPartial N := by
    dsimp only [P, oddMinusSqPartial]
    rw [map_prod]
    refine Finset.prod_congr rfl fun n _ => ?_
    simp [map_pow, map_sub, map_one]
  have hP_laur : polyToLaurent P = evalZHom (-1 : ℤˣ) (jacobiDoublePartial N) := by
    dsimp only [P, jacobiDoublePartial]
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hpow : (2 * (n : ℤ) - 1) = ((2 * n - 1 : ℕ) : ℤ) := by omega
    rw [map_pow, map_sub, map_one, polyToLaurent_X_pow,
      map_mul, map_add, map_add, map_one, evalZHom_qzMon, evalZHom_qzMon, sq, hpow,
      negOneUnit_zpow 1, negOneUnit_zpow (-1)]
    simp only [Int.natAbs_one, Int.natAbs_neg, pow_one, AddMonoidAlgebra.single_neg]
    ring
  rw [← hP_ps, coeff_coeToPowerSeries, ← coeff_polyToLaurent_nat, hP_laur]

/-- Unit `i` in `GaussianInt` (`Zsqrtd (-1)`). -/
private def gaussIUnit : GaussianIntˣ where
  val := ⟨0, 1⟩
  inv := ⟨0, -1⟩
  val_inv := by ext <;> norm_num
  inv_val := by ext <;> norm_num

private lemma gaussIUnit_zpow_add_neg (k : ℕ) :
    ((gaussIUnit ^ (k : ℤ) : GaussianIntˣ) : GaussianInt) +
      ((gaussIUnit ^ (-(k : ℤ)) : GaussianIntˣ) : GaussianInt) =
      if Even k then (2 * (-1 : ℤ) ^ (k / 2) : ℤ) else 0 := by
  have hpow : ∀ m : ℕ, ((gaussIUnit ^ (m : ℤ) : GaussianIntˣ) : GaussianInt) =
      (⟨0, 1⟩ : GaussianInt) ^ m := by
    intro m; simp [gaussIUnit]
  have hinv : ∀ m : ℕ, ((gaussIUnit ^ (-(m : ℤ)) : GaussianIntˣ) : GaussianInt) =
      (⟨0, -1⟩ : GaussianInt) ^ m := by
    intro m
    rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    rfl
  rw [hpow, hinv]
  have hsq1 : (⟨0, 1⟩ : GaussianInt) ^ 2 = (-1 : GaussianInt) := by
    rw [sq]; ext <;> norm_num
  have hsq2 : (⟨0, -1⟩ : GaussianInt) ^ 2 = (-1 : GaussianInt) := by
    rw [sq]; ext <;> norm_num
  rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · have hdiv : (r + r) / 2 = r := by omega
    rw [if_pos ⟨r, rfl⟩, hdiv, ← two_mul, pow_mul, pow_mul, hsq1, hsq2]
    push_cast
    ring
  · rw [if_neg (Nat.not_even_iff_odd.mpr ⟨r, rfl⟩), pow_succ, pow_succ, pow_mul, pow_mul,
      hsq1, hsq2]
    have hsum : (⟨0, 1⟩ : GaussianInt) + ⟨0, -1⟩ = 0 := by ext <;> norm_num
    calc (-1 : GaussianInt) ^ r * ⟨0, 1⟩ + (-1 : GaussianInt) ^ r * ⟨0, -1⟩
        = (-1 : GaussianInt) ^ r * (⟨0, 1⟩ + ⟨0, -1⟩) := by ring
      _ = 0 := by rw [hsum, mul_zero]

/-- `thetaUnitSeries gaussIUnit = map (Int.cast) (expand 4 (thetaUnitSeries (-1 : ℤˣ)))`! -/
private lemma thetaUnitSeries_gaussIUnit :
    thetaUnitSeries gaussIUnit =
      PowerSeries.map (Int.castRingHom GaussianInt)
        (PowerSeries.expand 4 (by norm_num) (thetaUnitSeries (-1 : ℤˣ))) :=
  PowerSeries.ext fun m => by
    rw [PowerSeries.coeff_map, PowerSeries.coeff_expand]
    simp only [thetaUnitSeries, PowerSeries.coeff_mk]
    by_cases hm0 : m = 0
    · subst hm0
      simp
    · by_cases hsq : ∃ r : ℕ, m = r ^ 2
      · rcases hsq with ⟨r, rfl⟩
        have hr : 0 < r := by
          by_contra h0; push Not at h0
          have hr0 : r = 0 := by omega
          subst hr0; exact hm0 rfl
        have hLHS : ∑ k ∈ Finset.Icc (-((r ^ 2 : ℕ) : ℤ)) ((r ^ 2 : ℕ) : ℤ),
            (if ((r ^ 2 : ℕ) : ℤ) = k ^ 2 then ((gaussIUnit ^ k : GaussianIntˣ) : GaussianInt) else 0) =
            ((gaussIUnit ^ (r : ℤ) : GaussianIntˣ) : GaussianInt) +
              ((gaussIUnit ^ (-(r : ℤ)) : GaussianIntˣ) : GaussianInt) := by
          have hpair : ({(r : ℤ), -(r : ℤ)} : Finset ℤ) ⊆
              Finset.Icc (-((r ^ 2 : ℕ) : ℤ)) ((r ^ 2 : ℕ) : ℤ) := by
            intro k hk
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            simp only [Finset.mem_Icc]
            push_cast
            rcases hk with rfl | rfl <;> constructor <;> nlinarith
          rw [← Finset.sum_subset hpair]
          · rw [Finset.sum_pair (by omega)]
            simp
          · intro k _ hnot
            rw [if_neg]
            intro heq
            apply hnot
            simp only [Finset.mem_insert, Finset.mem_singleton]
            have hsq' : k ^ 2 = (r : ℤ) ^ 2 := by push_cast at heq; linarith
            exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq'
        rw [hLHS, gaussIUnit_zpow_add_neg r]
        by_cases hev : Even r
        · rcases hev with ⟨s, rfl⟩
          have h4dvd : 4 ∣ (s + s) ^ 2 := ⟨s ^ 2, by ring⟩
          have hdiv : (s + s) ^ 2 / 4 = s ^ 2 := by
            have : (s + s) ^ 2 = 4 * s ^ 2 := by ring
            rw [this]; omega
          have hs : 0 < s := by omega
          rw [if_pos ⟨s, rfl⟩, if_pos h4dvd, hdiv]
          have hdiv2 : (s + s) / 2 = s := by omega
          rw [hdiv2]
          have hRHS : ∑ k ∈ Finset.Icc (-((s ^ 2 : ℕ) : ℤ)) ((s ^ 2 : ℕ) : ℤ),
              (if ((s ^ 2 : ℕ) : ℤ) = k ^ 2 then (((-1 : ℤˣ) ^ k : ℤˣ) : ℤ) else 0) =
              2 * (-1 : ℤ) ^ s := by
            have hpair : ({(s : ℤ), -(s : ℤ)} : Finset ℤ) ⊆
                Finset.Icc (-((s ^ 2 : ℕ) : ℤ)) ((s ^ 2 : ℕ) : ℤ) := by
              intro k hk
              simp only [Finset.mem_insert, Finset.mem_singleton] at hk
              simp only [Finset.mem_Icc]
              push_cast
              rcases hk with rfl | rfl <;> constructor <;> nlinarith
            rw [← Finset.sum_subset hpair]
            · rw [Finset.sum_pair (by omega)]
              simp only [Nat.cast_pow, ↓reduceIte, neg_sq, negOneUnit_zpow,
                Int.natAbs_natCast, Int.natAbs_neg]
              ring
            · intro k _ hnot
              rw [if_neg]
              intro heq
              apply hnot
              simp only [Finset.mem_insert, Finset.mem_singleton]
              have hsq' : k ^ 2 = (s : ℤ) ^ 2 := by push_cast at heq; linarith
              exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq'
          rw [hRHS]
          simp
        · have hnot4 : ¬ 4 ∣ r ^ 2 := by
            intro h4
            have h2 : 2 ∣ r ^ 2 := dvd_trans (by decide : 2 ∣ 4) h4
            have h2r : 2 ∣ r := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
            exact hev (even_iff_two_dvd.mpr h2r)
          rw [if_neg hev, if_neg hnot4, map_zero]
          simp
      · have hLHS : ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
            (if (m : ℤ) = k ^ 2 then ((gaussIUnit ^ k : GaussianIntˣ) : GaussianInt) else 0) = 0 := by
          refine Finset.sum_eq_zero fun k _ => ?_
          rw [if_neg]
          intro heq
          apply hsq
          refine ⟨k.natAbs, ?_⟩
          have hsq' : ((k.natAbs ^ 2 : ℕ) : ℤ) = k ^ 2 := by
            rw [Nat.cast_pow, Int.natAbs_sq]
          omega
        rw [hLHS]
        symm
        split_ifs with h4
        · have hsum0 : (∑ k ∈ Finset.Icc (-((m / 4 : ℕ) : ℤ)) ((m / 4 : ℕ) : ℤ),
              if ((m / 4 : ℕ) : ℤ) = k ^ 2 then (((-1 : ℤˣ) ^ k : ℤˣ) : ℤ) else 0) = 0 := by
            refine Finset.sum_eq_zero fun k _ => ?_
            rw [if_neg]
            intro heq
            apply hsq
            refine ⟨2 * k.natAbs, ?_⟩
            have hsq' : ((k.natAbs ^ 2 : ℕ) : ℤ) = k ^ 2 := by
              rw [Nat.cast_pow, Int.natAbs_sq]
            rcases h4 with ⟨q, rfl⟩
            have hq : q = k.natAbs ^ 2 := by omega
            rw [hq]; ring
          rw [hsum0, map_zero]
        · exact map_zero _

/-- Specialization at `z = i`: `mod4PlusSeries = jacobiC 0 * expand 4 (thetaUnitSeries (-1 : ℤˣ))`. -/
private lemma mod4PlusSeries_eq :
    mod4PlusSeries = jacobiC 0 * PowerSeries.expand 4 (by norm_num) (thetaUnitSeries (-1 : ℤˣ)) :=
  PowerSeries.ext fun N => by
    rw [coeff_mod4PlusSeries_eq (le_refl N)]
    have hinj : Function.Injective (Int.castRingHom GaussianInt) := by
      intro a b hab
      have := congrArg Zsqrtd.re hab
      simpa using this
    apply hinj
    have heval := coeff_evalZHom_jacobiDoublePartial gaussIUnit (le_refl N)
    rw [thetaUnitSeries_gaussIUnit, ← map_mul, PowerSeries.coeff_map] at heval
    rw [← heval]
    let P : Polynomial GaussianInt := ∏ n ∈ Finset.Icc 1 N, (1 + Polynomial.X ^ (4 * n - 2))
    have hP_ps : Polynomial.coeToPowerSeries.ringHom P =
        PowerSeries.map (Int.castRingHom GaussianInt) (mod4PlusPartial N) := by
      dsimp only [P, mod4PlusPartial]
      rw [map_prod, map_prod]
      refine Finset.prod_congr rfl fun n _ => ?_
      simp [map_add, map_one, map_pow]
    have hP_laur : polyToLaurent P = evalZHom gaussIUnit (jacobiDoublePartial N) := by
      dsimp only [P, jacobiDoublePartial]
      rw [map_prod, map_prod]
      refine Finset.prod_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [map_add, map_one, polyToLaurent_X_pow,
        map_mul, map_add, map_add, map_one, evalZHom_qzMon, evalZHom_qzMon]
      have hi1 : ((gaussIUnit ^ (1 : ℤ) : GaussianIntˣ) : GaussianInt) = ⟨0, 1⟩ := by
        simp [gaussIUnit]
      have hi2 : ((gaussIUnit ^ (-1 : ℤ) : GaussianIntˣ) : GaussianInt) = ⟨0, -1⟩ := by
        simp [gaussIUnit]
      rw [hi1, hi2]
      have hmul : AddMonoidAlgebra.single (2 * (n : ℤ) - 1) (⟨0, 1⟩ : GaussianInt) *
          AddMonoidAlgebra.single (2 * (n : ℤ) - 1) (⟨0, -1⟩ : GaussianInt) =
          AddMonoidAlgebra.single ((4 * n - 2 : ℕ) : ℤ) 1 := by
        rw [AddMonoidAlgebra.single_mul_single]
        have h1 : (2 * (n : ℤ) - 1) + (2 * (n : ℤ) - 1) = ((4 * n - 2 : ℕ) : ℤ) := by omega
        have h2 : (⟨0, 1⟩ : GaussianInt) * ⟨0, -1⟩ = 1 := by ext <;> norm_num
        rw [h1, h2]
      have hadd0 : AddMonoidAlgebra.single (2 * (n : ℤ) - 1) (⟨0, 1⟩ : GaussianInt) +
          AddMonoidAlgebra.single (2 * (n : ℤ) - 1) (⟨0, -1⟩ : GaussianInt) = 0 := by
        rw [← AddMonoidAlgebra.single_add]
        have h0 : (⟨0, 1⟩ : GaussianInt) + ⟨0, -1⟩ = 0 := by ext <;> norm_num
        rw [h0, AddMonoidAlgebra.single_zero]
      calc 1 + AddMonoidAlgebra.single ((4 * n - 2 : ℕ) : ℤ) 1
          = 1 + (AddMonoidAlgebra.single (2 * (n : ℤ) - 1) (⟨0, 1⟩ : GaussianInt) +
              AddMonoidAlgebra.single (2 * (n : ℤ) - 1) (⟨0, -1⟩ : GaussianInt)) +
              AddMonoidAlgebra.single (2 * (n : ℤ) - 1) (⟨0, 1⟩ : GaussianInt) *
                AddMonoidAlgebra.single (2 * (n : ℤ) - 1) (⟨0, -1⟩ : GaussianInt) := by
              rw [hadd0, hmul, add_zero]
        _ = (1 + AddMonoidAlgebra.single (2 * (n : ℤ) - 1) (⟨0, 1⟩ : GaussianInt)) *
              (1 + AddMonoidAlgebra.single (2 * (n : ℤ) - 1) (⟨0, -1⟩ : GaussianInt)) := by ring
    have hcoef : (Int.castRingHom GaussianInt) (PowerSeries.coeff N (mod4PlusPartial N)) =
        PowerSeries.coeff N (Polynomial.coeToPowerSeries.ringHom P) := by
      rw [hP_ps, PowerSeries.coeff_map]
    rw [hcoef, coeff_coeToPowerSeries, ← coeff_polyToLaurent_nat, hP_laur]

/-- Product identity: `mod4PlusSeries * expand 2 eulerPhiSeries = expand 4 (oddMinusSqSeries * expand 2 eulerPhiSeries)`! -/
private lemma mod4Plus_mul_eulerPhi2_eq :
    mod4PlusSeries * PowerSeries.expand 2 (by norm_num) eulerPhiSeries =
      PowerSeries.expand 4 (by norm_num) oddMinusSqSeries *
        PowerSeries.expand 4 (by norm_num) (PowerSeries.expand 2 (by norm_num) eulerPhiSeries) :=
  PowerSeries.ext fun N => by
    have hsplit : ∀ (K : ℕ) (f : ℕ → PowerSeries ℤ),
        ∏ n ∈ Finset.Icc 1 (2 * K), f n =
          (∏ j ∈ Finset.Icc 1 K, f (2 * j - 1)) * (∏ j ∈ Finset.Icc 1 K, f (2 * j)) := by
      intro K f
      induction K with
      | zero => simp
      | succ k ih =>
        have h1 : Finset.Icc 1 (2 * (k + 1)) =
            insert (2 * k + 2) (insert (2 * k + 1) (Finset.Icc 1 (2 * k))) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have h2 : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [h1, Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
          Finset.prod_insert (by simp only [Finset.mem_Icc]; omega), ih, h2,
          Finset.prod_insert (by simp), Finset.prod_insert (by simp)]
        have ha : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
        have hb : 2 * (k + 1) = 2 * k + 2 := by omega
        rw [ha, hb]; ring
    have hLHS : PowerSeries.coeff N
        (mod4PlusSeries * PowerSeries.expand 2 (by norm_num) eulerPhiSeries) =
        PowerSeries.coeff N
          (mod4PlusPartial (2 * N) * PowerSeries.expand 2 (by norm_num) (eulerPhiPartial (4 * N))) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hsum := Finset.mem_antidiagonal.mp hx
      congr 1
      · exact coeff_mod4PlusSeries_eq (by omega)
      · simp only [PowerSeries.coeff_expand]
        split_ifs with hdvd
        · exact coeff_eulerPhiSeries_eq_partial (by omega)
        · rfl
    have hRHS : PowerSeries.coeff N
        (PowerSeries.expand 4 (by norm_num) oddMinusSqSeries *
          PowerSeries.expand 4 (by norm_num) (PowerSeries.expand 2 (by norm_num) eulerPhiSeries)) =
        PowerSeries.coeff N
          (PowerSeries.expand 4 (by norm_num) (oddMinusSqPartial N) *
            PowerSeries.expand 4 (by norm_num) (PowerSeries.expand 2 (by norm_num) (eulerPhiPartial N))) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hsum := Finset.mem_antidiagonal.mp hx
      congr 1
      · simp only [PowerSeries.coeff_expand]
        split_ifs
        · exact coeff_oddMinusSqSeries_eq (by omega)
        · rfl
      · simp only [PowerSeries.coeff_expand]
        split_ifs
        · exact coeff_eulerPhiSeries_eq_partial (by omega)
        · rfl
        · rfl
    rw [hLHS, hRHS]
    have hprod_eq : mod4PlusPartial (2 * N) * PowerSeries.expand 2 (by norm_num) (eulerPhiPartial (4 * N)) =
        (PowerSeries.expand 4 (by norm_num) (oddMinusSqPartial N) *
          PowerSeries.expand 4 (by norm_num) (PowerSeries.expand 2 (by norm_num) (eulerPhiPartial N))) *
          (∏ j ∈ Finset.Icc (N + 1) (2 * N), (1 - PowerSeries.X ^ (8 * j - 4))) := by
      unfold mod4PlusPartial eulerPhiPartial oddMinusSqPartial
      rw [map_prod, map_prod, map_prod, map_prod]
      have hexp2 : ∀ k : ℕ, PowerSeries.expand 2 (by norm_num) (1 - PowerSeries.X ^ k : PowerSeries ℤ) =
          1 - PowerSeries.X ^ (2 * k) := by
        intro k; rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
      have hexp4 : ∀ k : ℕ, PowerSeries.expand 4 (by norm_num) (1 - PowerSeries.X ^ k : PowerSeries ℤ) =
          1 - PowerSeries.X ^ (4 * k) := by
        intro k; rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
      simp only [map_pow, hexp2, hexp4]
      rw [show 4 * N = 2 * (2 * N) by ring, hsplit (2 * N) (fun n => 1 - PowerSeries.X ^ (2 * n))]
      rw [hsplit N (fun j => 1 - PowerSeries.X ^ (2 * (2 * j)))]
      have hdiff : (∏ j ∈ Finset.Icc 1 (2 * N), (1 + PowerSeries.X ^ (4 * j - 2) : PowerSeries ℤ)) *
          (∏ j ∈ Finset.Icc 1 (2 * N), (1 - PowerSeries.X ^ (2 * (2 * j - 1)))) =
          ∏ j ∈ Finset.Icc 1 (2 * N), (1 - PowerSeries.X ^ (8 * j - 4)) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j hj => ?_
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        have h1 : 2 * (2 * j - 1) = 4 * j - 2 := by omega
        have h2 : (4 * j - 2) + (4 * j - 2) = 8 * j - 4 := by omega
        rw [h1]
        calc (1 + PowerSeries.X ^ (4 * j - 2) : PowerSeries ℤ) * (1 - PowerSeries.X ^ (4 * j - 2))
            = 1 - PowerSeries.X ^ (4 * j - 2) * PowerSeries.X ^ (4 * j - 2) := by ring
          _ = 1 - PowerSeries.X ^ (8 * j - 4) := by rw [← pow_add, h2]
      have hsplit_tail : ∏ j ∈ Finset.Icc 1 (2 * N), (1 - PowerSeries.X ^ (8 * j - 4) : PowerSeries ℤ) =
          (∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (8 * j - 4))) *
            (∏ j ∈ Finset.Icc (N + 1) (2 * N), (1 - PowerSeries.X ^ (8 * j - 4))) := by
        have hunion : Finset.Icc 1 (2 * N) = Finset.Icc 1 N ∪ Finset.Icc (N + 1) (2 * N) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
        have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) (2 * N)) :=
          Finset.disjoint_left.mpr fun x hx1 hx2 => by
            simp only [Finset.mem_Icc] at hx1 hx2; omega
        rw [hunion, Finset.prod_union hdisj]
      have hsq_eq : (∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (8 * j - 4) : PowerSeries ℤ)) *
          (∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (2 * (2 * (2 * j - 1))))) =
          ∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (4 * (2 * j - 1))) ^ 2 := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j hj => ?_
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        have h1 : 8 * j - 4 = 4 * (2 * j - 1) := by omega
        have h2 : 2 * (2 * (2 * j - 1)) = 4 * (2 * j - 1) := by omega
        rw [h1, h2, sq]
      have h8_eq : (∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (2 * (2 * (2 * j))) : PowerSeries ℤ)) =
          ∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (4 * (2 * j))) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        congr 2; ring
      calc (∏ j ∈ Finset.Icc 1 (2 * N), (1 + PowerSeries.X ^ (4 * j - 2) : PowerSeries ℤ)) *
              ((∏ j ∈ Finset.Icc 1 (2 * N), (1 - PowerSeries.X ^ (2 * (2 * j - 1)))) *
                ((∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (2 * (2 * (2 * j - 1))))) *
                  (∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (2 * (2 * (2 * j)))))))
          = ((∏ j ∈ Finset.Icc 1 (2 * N), (1 + PowerSeries.X ^ (4 * j - 2))) *
              (∏ j ∈ Finset.Icc 1 (2 * N), (1 - PowerSeries.X ^ (2 * (2 * j - 1))))) *
              ((∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (2 * (2 * (2 * j - 1))))) *
                (∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (2 * (2 * (2 * j)))))) := by ring
        _ = ((∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (8 * j - 4))) *
              (∏ j ∈ Finset.Icc (N + 1) (2 * N), (1 - PowerSeries.X ^ (8 * j - 4)))) *
              ((∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (2 * (2 * (2 * j - 1))))) *
                (∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (2 * (2 * (2 * j)))))) := by
              rw [hdiff, hsplit_tail]
        _ = (((∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (8 * j - 4))) *
              (∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (2 * (2 * (2 * j - 1)))))) *
              (∏ j ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ (2 * (2 * (2 * j)))))) *
              (∏ j ∈ Finset.Icc (N + 1) (2 * N), (1 - PowerSeries.X ^ (8 * j - 4))) := by ring
        _ = _ := by rw [hsq_eq, h8_eq]
    rw [hprod_eq]
    have hdrop : ∀ (s : Finset ℕ) (f : PowerSeries ℤ), (∀ j ∈ s, N < 8 * j - 4) →
        PowerSeries.coeff N (f * ∏ j ∈ s, (1 - PowerSeries.X ^ (8 * j - 4))) =
          PowerSeries.coeff N f := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro f _; simp
      | insert a s ha ih =>
        intro f hlt
        rw [Finset.prod_insert ha, mul_comm (1 - PowerSeries.X ^ (8 * a - 4)), ← mul_assoc,
          coeff_mul_one_sub_X_pow_of_lt _ (hlt a (Finset.mem_insert_self _ _)),
          ih f (fun j hj => hlt j (Finset.mem_insert_of_mem hj))]
    exact hdrop (Finset.Icc (N + 1) (2 * N)) _ fun j hj => by
      have := (Finset.mem_Icc.mp hj).1; omega

/-- If `expand 4 f = f` in `PowerSeries ℤ`, then `coeff n f = 0` for all `n ≥ 1`. -/
private lemma eq_C_of_expand_four_eq {f : PowerSeries ℤ}
    (hf : PowerSeries.expand 4 (by norm_num) f = f) :
    ∀ n : ℕ, 1 ≤ n → PowerSeries.coeff n f = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hcoeff := congrArg (PowerSeries.coeff n) hf
    rw [PowerSeries.coeff_expand] at hcoeff
    split_ifs at hcoeff with h4
    · have hdiv_pos : 1 ≤ n / 4 := by
        rcases h4 with ⟨q, rfl⟩; omega
      have hdiv_lt : n / 4 < n := Nat.div_lt_self (by omega) (by norm_num)
      rw [← hcoeff, ih (n / 4) hdiv_lt hdiv_pos]
    · exact hcoeff.symm

/-- **CORE EVALUATION**: `jacobiC 0 * expand 2 eulerPhiSeries = 1` in `PowerSeries ℤ`! -/
private lemma jacobiC_zero_mul_eulerPhi2_eq_one :
    jacobiC 0 * PowerSeries.expand 2 (by norm_num) eulerPhiSeries = 1 := by
  let eulerPhi2 : PowerSeries ℤ := PowerSeries.expand 2 (by norm_num) eulerPhiSeries
  let θ4 : PowerSeries ℤ := PowerSeries.expand 4 (by norm_num) (thetaUnitSeries (-1 : ℤˣ))
  have h1 : (jacobiC 0 * eulerPhi2) * θ4 =
      PowerSeries.expand 4 (by norm_num) (jacobiC 0 * eulerPhi2) * θ4 := by
    have hm := mod4Plus_mul_eulerPhi2_eq
    change mod4PlusSeries * eulerPhi2 =
      PowerSeries.expand 4 (by norm_num) oddMinusSqSeries *
        PowerSeries.expand 4 (by norm_num) eulerPhi2 at hm
    rw [mod4PlusSeries_eq, oddMinusSqSeries_eq, map_mul] at hm
    rw [map_mul]
    calc (jacobiC 0 * eulerPhi2) * θ4
        = (jacobiC 0 * θ4) * eulerPhi2 := by ring
      _ = PowerSeries.expand 4 (by norm_num) (jacobiC 0) * θ4 *
            PowerSeries.expand 4 (by norm_num) eulerPhi2 := hm
      _ = (PowerSeries.expand 4 (by norm_num) (jacobiC 0) *
            PowerSeries.expand 4 (by norm_num) eulerPhi2) * θ4 := by ring
  have hθ4_ne : θ4 ≠ 0 := by
    intro h0
    have hc := congrArg (PowerSeries.coeff 0) h0
    simp [θ4, PowerSeries.coeff_expand, thetaUnitSeries] at hc
  have hfix : PowerSeries.expand 4 (by norm_num) (jacobiC 0 * eulerPhi2) = jacobiC 0 * eulerPhi2 :=
    (mul_right_cancel₀ hθ4_ne h1).symm
  exact PowerSeries.ext fun n => by
    cases n with
    | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_one,
        ← PowerSeries.coeff_zero_eq_constantCoeff]
      have hc0 : PowerSeries.coeff 0 (jacobiC 0) = 1 := by
        simp [jacobiC, jacobiDoublePartial, ← qzMon_zero, qzMon, AddMonoidAlgebra.coeff_single]
      have he0 : PowerSeries.coeff 0 eulerPhi2 = 1 := by
        simp [eulerPhi2, PowerSeries.coeff_expand, coeff_zero_eulerPhiSeries]
      rw [hc0, he0, mul_one]
    | succ m =>
      rw [eq_C_of_expand_four_eq hfix (m + 1) (Nat.succ_pos m), PowerSeries.coeff_one,
        if_neg (Nat.succ_ne_zero m)]

/-- Helper: `jacobiTriplePartial M` evaluated at `(N, k)` equals `coeff N (expand 2 (eulerPhiPartial M) * jacobiC k)` when `N ≤ 2 * M`. -/
private lemma coeff_jacobiTriplePartial_eq {N M : ℕ} (hNM : (N : ℤ) ≤ 2 * (M : ℤ)) (k : ℤ) :
    (jacobiTriplePartial M).coeff ((N : ℤ), k) =
      PowerSeries.coeff N (PowerSeries.expand 2 (by norm_num) (eulerPhiPartial M) * jacobiC k) := by
  have hprod_mul : ∀ (K : ℕ) (g : LaurentQZ), (∀ a b, a < 0 → g.coeff (a, b) = 0) →
      ∀ (n : ℕ) (b : ℤ),
      ((∏ m ∈ Finset.Icc 1 K, (1 - qzMon (2 * (m : ℤ)) 0)) * g).coeff ((n : ℤ), b) =
        PowerSeries.coeff n (PowerSeries.expand 2 (by norm_num) (eulerPhiPartial K) *
          PowerSeries.mk fun r => g.coeff ((r : ℤ), b)) := by
    intro K
    induction K with
    | zero =>
      intro g _ n b
      simp [eulerPhiPartial]
    | succ K ih =>
      intro g hg n b
      have hIcc : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.prod_insert (by simp), eulerPhiPartial_succ,
        map_mul (PowerSeries.expand 2 (by norm_num)), map_sub, map_one,
        map_pow, PowerSeries.expand_X, ← pow_mul]
      rw [mul_assoc, sub_mul, one_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
        coeff_qzMon_mul, sub_zero]
      have hstep : (PowerSeries.expand 2 (by norm_num) (eulerPhiPartial K) *
          (1 - PowerSeries.X ^ (2 * (K + 1))) *
          PowerSeries.mk fun r => g.coeff ((r : ℤ), b)) =
          (PowerSeries.expand 2 (by norm_num) (eulerPhiPartial K) *
            PowerSeries.mk fun r => g.coeff ((r : ℤ), b)) *
            (1 - PowerSeries.X ^ (2 * (K + 1))) := by ring
      rw [hstep, coeff_mul_one_sub_X_pow, ih g hg n b]
      congr 1
      split_ifs with hle
      · rw [← ih g hg (n - 2 * (K + 1)) b]
        congr 2; omega
      · have hneg : ((n : ℤ) - 2 * ((K + 1 : ℕ) : ℤ)) < 0 := by omega
        have hprod_neg : ∀ a b', a < 0 →
            (∏ m ∈ Finset.Icc 1 K, (1 - qzMon (2 * (m : ℤ)) 0)).coeff (a, b') = 0 := by
          clear ih hIcc hstep hle hneg
          induction K with
          | zero =>
            intro a b' ha
            have hemp : Finset.Icc 1 0 = ∅ := by decide
            rw [hemp, Finset.prod_empty, ← qzMon_zero, qzMon, AddMonoidAlgebra.coeff_single]
            exact Finsupp.single_eq_of_ne (by intro h; have := congrArg Prod.fst h; dsimp at this; omega)
          | succ j ihj =>
            intro a b' ha
            have hI : Finset.Icc 1 (j + 1) = insert (j + 1) (Finset.Icc 1 j) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hI, Finset.prod_insert (by simp), sub_mul, one_mul, AddMonoidAlgebra.coeff_sub,
              Finsupp.sub_apply, coeff_qzMon_mul, ihj a b' ha, ihj _ _ (by omega), sub_self]
        exact mul_eq_zero_of_neg hprod_neg (fun a b' ha => hg a b' ha) hneg b
  unfold jacobiTriplePartial
  rw [hprod_mul M (jacobiDoublePartial M) (fun a b ha => jacobiDoublePartial_eq_zero_of_neg M ha b) N k]
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hsum := Finset.mem_antidiagonal.mp hx
  congr 1
  simp only [PowerSeries.coeff_mk]
  exact (coeff_jacobiC_eq (M := M) (by omega) k).symm

/-- Quadratic support bound for `jacobiTriplePartial M`:
every nonzero `(a, b)` satisfies `b^2 ≤ a`! -/
private lemma jacobiTriplePartial_support_bound (M : ℕ) (a b : ℤ)
    (h : (jacobiTriplePartial M).coeff (a, b) ≠ 0) :
    b ^ 2 ≤ a := by
  have hstep : ∀ (K : ℕ) (g : LaurentQZ),
      (∀ x y, g.coeff (x, y) ≠ 0 → y ^ 2 ≤ x) →
      ∀ x y, ((∏ m ∈ Finset.Icc 1 K, (1 - qzMon (2 * (m : ℤ)) 0)) * g).coeff (x, y) ≠ 0 →
      y ^ 2 ≤ x := by
    intro K
    induction K with
    | zero =>
      intro g hg x y hxy
      simpa using hg x y (by simpa using hxy)
    | succ K ih =>
      intro g hg x y hxy
      have hIcc : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
        ext z; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.prod_insert (by simp), mul_assoc, sub_mul, one_mul,
        AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_qzMon_mul, sub_zero] at hxy
      by_cases h1 : ((∏ m ∈ Finset.Icc 1 K, (1 - qzMon (2 * (m : ℤ)) 0)) * g).coeff (x, y) ≠ 0
      · exact ih g hg x y h1
      · have h2 : ((∏ m ∈ Finset.Icc 1 K, (1 - qzMon (2 * (m : ℤ)) 0)) * g).coeff
            (x - 2 * ((K + 1 : ℕ) : ℤ), y) ≠ 0 := by
          push Not at h1
          rw [h1, zero_sub] at hxy
          exact neg_ne_zero.mp hxy
        have hle := ih g hg _ y h2
        omega
  exact hstep M (jacobiDoublePartial M)
    (fun x y hxy => (jacobiDoublePartial_support_bound M x y hxy).2) a b h

/-- **UNCONDITIONAL JACOBI TRIPLE PRODUCT IDENTITY (`0` ASSUMPTIONS!)**:
for EVERY `N : ℕ`, `k : ℤ`, and every truncation level `M` with `N ≤ 2 * M`,
the `(q^N z^k)`-coefficient of
$$\prod_{n=1}^{M} (1 - q^{2n})(1 + z q^{2n-1})(1 + z^{-1} q^{2n-1})$$
equals `1` if `N = k^2` and `0` otherwise! -/
theorem jacobi_triple_product_coeff (N : ℕ) (k : ℤ) {M : ℕ} (hM : N ≤ 2 * M) :
    (jacobiTriplePartial M).coeff ((N : ℤ), k) = if (N : ℤ) = k ^ 2 then 1 else 0 := by
  rw [coeff_jacobiTriplePartial_eq (by exact_mod_cast hM) k]
  have hstab : PowerSeries.coeff N
      (PowerSeries.expand 2 (by norm_num) (eulerPhiPartial M) * jacobiC k) =
      PowerSeries.coeff N
        (PowerSeries.expand 2 (by norm_num) eulerPhiSeries * jacobiC k) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hsum := Finset.mem_antidiagonal.mp hx
    congr 1
    simp only [PowerSeries.coeff_expand]
    split_ifs with hdvd
    · exact (coeff_eulerPhiSeries_eq_partial (by omega)).symm
    · rfl
  rw [hstab, jacobiC_eq k]
  have hmul : PowerSeries.expand 2 (by norm_num) eulerPhiSeries *
      (jacobiC 0 * PowerSeries.X ^ (k.natAbs ^ 2)) =
      PowerSeries.X ^ (k.natAbs ^ 2) := by
    calc PowerSeries.expand 2 (by norm_num) eulerPhiSeries *
            (jacobiC 0 * PowerSeries.X ^ (k.natAbs ^ 2))
        = (jacobiC 0 * PowerSeries.expand 2 (by norm_num) eulerPhiSeries) *
            PowerSeries.X ^ (k.natAbs ^ 2) := by ring
      _ = 1 * PowerSeries.X ^ (k.natAbs ^ 2) := by rw [jacobiC_zero_mul_eulerPhi2_eq_one]
      _ = PowerSeries.X ^ (k.natAbs ^ 2) := one_mul _
  rw [hmul, PowerSeries.coeff_X_pow]
  have hsq : ((k.natAbs ^ 2 : ℕ) : ℤ) = k ^ 2 := by
    rw [Nat.cast_pow, Int.natAbs_sq]
  have hiff : (N = k.natAbs ^ 2) ↔ ((N : ℤ) = k ^ 2) := by omega
  by_cases h : N = k.natAbs ^ 2
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

end JacobiTripleProduct

/-! ## Section 3: Unconditional Euler Pentagonal Theorem, `p(n)` Recurrences, & Jacobi Cube Identity -/

section PentagonalRecurrenceAndCube

/-- Ring homomorphism `LaurentQZ →+* AddMonoidAlgebra ℤ ℤ` substituting `(q, z) ↦ (q^3, -q)`. -/
private def pentHom : LaurentQZ →+* AddMonoidAlgebra ℤ ℤ :=
  AddMonoidAlgebra.lift ℤ (AddMonoidAlgebra ℤ ℤ) (ℤ × ℤ)
    { toFun := fun p => AddMonoidAlgebra.single
        (3 * (Multiplicative.toAdd p).1 + (Multiplicative.toAdd p).2)
        ((((-1 : ℤˣ) ^ (Multiplicative.toAdd p).2 : ℤˣ) : ℤ))
      map_one' := by
        simp [AddMonoidAlgebra.one_def]
      map_mul' := fun p q => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, zpow_add, Units.val_mul,
          AddMonoidAlgebra.single_mul_single]
        congr 1; ring }

private lemma pentHom_qzMon (a b : ℤ) :
    pentHom (qzMon a b) = AddMonoidAlgebra.single (3 * a + b) (((-1 : ℤˣ) ^ b : ℤˣ) : ℤ) := by
  simp [pentHom, qzMon]

private lemma coeff_pentHom (f : LaurentQZ) (c : ℤ) :
    (pentHom f).coeff c =
      f.coeff.sum fun p v => if 3 * p.1 + p.2 = c then v * (((-1 : ℤˣ) ^ p.2 : ℤˣ) : ℤ) else 0 := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  simp only [Finsupp.sum, map_sum]
  have hcoeff_sum : ∀ (s : Finset (ℤ × ℤ)) (g : ℤ × ℤ → AddMonoidAlgebra ℤ ℤ),
      (∑ p ∈ s, g p).coeff c = ∑ p ∈ s, (g p).coeff c := by
    intro s g
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, ih]
  rw [hcoeff_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hsingle : AddMonoidAlgebra.single p (f.coeff p) = (f.coeff p : ℤ) • qzMon p.1 p.2 := by
    simp [qzMon, AddMonoidAlgebra.smul_single]
  rw [hsingle, map_zsmul, pentHom_qzMon, AddMonoidAlgebra.smul_single, zsmul_eq_mul,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp

/-- Injectivity of the generalized pentagonal map `k ↦ k * (3 * k - 1) / 2` on `ℤ`. -/
private lemma pentagonal_injective {k₁ k₂ : ℤ}
    (h : k₁ * (3 * k₁ - 1) / 2 = k₂ * (3 * k₂ - 1) / 2) : k₁ = k₂ := by
  have hev1 : 2 ∣ k₁ * (3 * k₁ - 1) := by
    rcases Int.even_or_odd k₁ with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · exact ⟨r * (3 * (r + r) - 1), by ring⟩
    · exact ⟨(2 * r + 1) * (3 * r + 1), by ring⟩
  have hev2 : 2 ∣ k₂ * (3 * k₂ - 1) := by
    rcases Int.even_or_odd k₂ with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · exact ⟨r * (3 * (r + r) - 1), by ring⟩
    · exact ⟨(2 * r + 1) * (3 * r + 1), by ring⟩
  have h2 : k₁ * (3 * k₁ - 1) = k₂ * (3 * k₂ - 1) := by omega
  have hfac : (k₁ - k₂) * (3 * (k₁ + k₂) - 1) = 0 := by linarith
  rcases mul_eq_zero.mp hfac with h0 | h0
  · omega
  · omega

private lemma two_dvd_pentagonal (k : ℤ) : 2 ∣ k * (3 * k - 1) := by
  rcases Int.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · exact ⟨r * (3 * (r + r) - 1), by ring⟩
  · exact ⟨(2 * r + 1) * (3 * r + 1), by ring⟩

open scoped Classical in
/-- **UNCONDITIONAL EULER'S PENTAGONAL NUMBER THEOREM (`0` ASSUMPTIONS!)**:
for EVERY `N : ℕ`,
$$\operatorname{coeff}_N\!\left(\prod_{m \ge 1} (1 - q^m)\right) =
  \begin{cases} (-1)^{|k|} & \text{if } N = k(3k - 1)/2 \text{ for some } k \in \mathbb{Z}, \\ 0 & \text{otherwise.} \end{cases}$$ -/
theorem euler_pentagonal_theorem (N : ℕ) :
    PowerSeries.coeff N eulerPhiSeries =
      if h : ∃ k : ℤ, (N : ℤ) = k * (3 * k - 1) / 2 then
        (-1 : ℤ) ^ (Classical.choose h).natAbs
      else 0 := by
  -- Step 1: Identify pentHom (jacobiTriplePartial N) with ∏_{m=1}^{3N} (1 - q^{2m}).
  have hpent_prod : pentHom (jacobiTriplePartial N) =
      polyToLaurent (∏ m ∈ Finset.Icc 1 (3 * N), (1 - Polynomial.X ^ (2 * m) : Polynomial ℤ)) := by
    unfold jacobiTriplePartial jacobiDoublePartial
    rw [← Finset.prod_mul_distrib, map_prod]
    have hsplit3 : ∀ (K : ℕ) (f : ℕ → AddMonoidAlgebra ℤ ℤ),
        ∏ m ∈ Finset.Icc 1 (3 * K), f m =
          ∏ n ∈ Finset.Icc 1 K, f (3 * n) * (f (3 * n - 1) * f (3 * n - 2)) := by
      intro K f
      induction K with
      | zero => simp
      | succ k ih =>
        have h1 : Finset.Icc 1 (3 * (k + 1)) =
            insert (3 * k + 3) (insert (3 * k + 2) (insert (3 * k + 1) (Finset.Icc 1 (3 * k)))) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have h2 : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [h1, Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
          Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
          Finset.prod_insert (by simp only [Finset.mem_Icc]; omega), ih, h2,
          Finset.prod_insert (by simp)]
        have hb : 3 * (k + 1) - 1 = 3 * k + 2 := by omega
        have hc : 3 * (k + 1) - 2 = 3 * k + 1 := by omega
        have ha : 3 * (k + 1) = 3 * k + 3 := by omega
        rw [hb, hc, ha]; ring
    rw [map_prod, hsplit3 N (fun m => polyToLaurent (1 - Polynomial.X ^ (2 * m) : Polynomial ℤ))]
    refine Finset.prod_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    simp only [map_mul, map_sub, map_add, map_one, pentHom_qzMon, polyToLaurent_X_pow,
      negOneUnit_zpow, Int.natAbs_zero, Int.natAbs_one, Int.natAbs_neg, pow_zero, pow_one,
      AddMonoidAlgebra.single_neg]
    have h6 : 3 * (2 * (n : ℤ)) + 0 = ((2 * (3 * n) : ℕ) : ℤ) := by omega
    have h4 : 3 * (2 * (n : ℤ) - 1) + 1 = ((2 * (3 * n - 1) : ℕ) : ℤ) := by omega
    have h2 : 3 * (2 * (n : ℤ) - 1) + -1 = ((2 * (3 * n - 2) : ℕ) : ℤ) := by omega
    rw [h6, h4, h2]
    ring
  -- Step 2: LHS at 2 * N equals coeff N eulerPhiSeries!
  have hLHS : (pentHom (jacobiTriplePartial N)).coeff ((2 * N : ℕ) : ℤ) =
      PowerSeries.coeff N eulerPhiSeries := by
    rw [hpent_prod, coeff_polyToLaurent_nat, ← coeff_coeToPowerSeries]
    have hps : Polynomial.coeToPowerSeries.ringHom
        (∏ m ∈ Finset.Icc 1 (3 * N), (1 - Polynomial.X ^ (2 * m) : Polynomial ℤ)) =
        PowerSeries.expand 2 (by norm_num) (eulerPhiPartial (3 * N)) := by
      unfold eulerPhiPartial
      rw [map_prod, map_prod]
      refine Finset.prod_congr rfl fun m _ => ?_
      rw [map_sub, map_one, map_pow, map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
      simp
    rw [hps, PowerSeries.coeff_expand_mul, coeff_eulerPhiSeries_eq_partial (M := 3 * N) (by omega)]
  -- Step 3: Evaluate RHS via coeff_pentHom + jacobi_triple_product_coeff!
  rw [← hLHS, coeff_pentHom]
  have hsum_eq : (jacobiTriplePartial N).coeff.sum (fun p v =>
      if 3 * p.1 + p.2 = ((2 * N : ℕ) : ℤ) then v * (((-1 : ℤˣ) ^ p.2 : ℤˣ) : ℤ) else 0) =
      ∑ k ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1),
        if (N : ℤ) = k * (3 * k - 1) / 2 then (-1 : ℤ) ^ k.natAbs else 0 := by
    rw [Finsupp.sum]
    have hsub : (jacobiTriplePartial N).coeff.support.filter
        (fun p => 3 * p.1 + p.2 = ((2 * N : ℕ) : ℤ)) ⊆
        (Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1)).image (fun k => (k ^ 2, -k)) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hsupp, hp_eq⟩
      have hne : (jacobiTriplePartial N).coeff p ≠ 0 := Finsupp.mem_support_iff.mp hsupp
      have hsq : p.2 ^ 2 ≤ p.1 := jacobiTriplePartial_support_bound N p.1 p.2 hne
      have hp1_nonneg : 0 ≤ p.1 := by nlinarith
      have hbb : 0 ≤ p.2 ^ 2 + p.2 := by
        rcases le_or_gt 0 p.2 with h0 | h0
        · nlinarith
        · have : p.2 ≤ -1 := by omega
          nlinarith
      have hp1_le : p.1 ≤ (N : ℤ) := by omega
      have htp := jacobi_triple_product_coeff p.1.toNat p.2 (M := N) (by omega)
      have htoNat : ((p.1.toNat : ℕ) : ℤ) = p.1 := Int.toNat_of_nonneg hp1_nonneg
      rw [htoNat] at htp
      have hp1_eq : p.1 = p.2 ^ 2 := by
        by_contra hneq
        rw [if_neg hneq] at htp
        exact hne htp
      refine Finset.mem_image.mpr ⟨-p.2, Finset.mem_Icc.mpr ?_, by ext <;> simp [hp1_eq]⟩
      have habs : |p.2| ≤ (N : ℤ) := by nlinarith [sq_abs p.2, abs_nonneg p.2]
      have hle := abs_le.mp habs
      omega
    rw [← Finset.sum_filter]
    -- Keep the `if` condition inside the summand over the super-set!
    have hsum_filter :
        ∑ p ∈ (jacobiTriplePartial N).coeff.support.filter
          (fun p => 3 * p.1 + p.2 = ((2 * N : ℕ) : ℤ)),
          (jacobiTriplePartial N).coeff p * (((-1 : ℤˣ) ^ p.2 : ℤˣ) : ℤ) =
        ∑ p ∈ (jacobiTriplePartial N).coeff.support.filter
          (fun p => 3 * p.1 + p.2 = ((2 * N : ℕ) : ℤ)),
          (if 3 * p.1 + p.2 = ((2 * N : ℕ) : ℤ) then
            (jacobiTriplePartial N).coeff p * (((-1 : ℤˣ) ^ p.2 : ℤˣ) : ℤ) else 0) :=
      Finset.sum_congr rfl fun p hp => (if_pos (Finset.mem_filter.mp hp).2).symm
    rw [hsum_filter, Finset.sum_subset hsub]
    · rw [Finset.sum_image]
      · refine Finset.sum_congr rfl fun k _ => ?_
        have hhev := two_dvd_pentagonal k
        by_cases hcond : (N : ℤ) = k * (3 * k - 1) / 2
        · have h3k : 3 * k ^ 2 + (-k) = ((2 * N : ℕ) : ℤ) := by
            have : k * (3 * k - 1) = 3 * k ^ 2 + (-k) := by ring
            omega
          have hk2_le : k ^ 2 ≤ (N : ℤ) := by
            have hkk : 0 ≤ k ^ 2 - k := by
              rcases le_or_gt 0 k with h0 | h0
              · by_cases hk0 : k = 0
                · subst hk0; norm_num
                · have : 1 ≤ k := by omega
                  nlinarith
              · nlinarith
            omega
          have htp := jacobi_triple_product_coeff (k ^ 2).toNat (-k) (M := N) (by omega)
          have htoNat : (((k ^ 2).toNat : ℕ) : ℤ) = k ^ 2 := Int.toNat_of_nonneg (sq_nonneg k)
          rw [htoNat, neg_sq, if_pos rfl] at htp
          rw [if_pos h3k, if_pos hcond, htp, one_mul, negOneUnit_zpow, Int.natAbs_neg]
        · have hne_eq : ¬ (3 * k ^ 2 + (-k) = ((2 * N : ℕ) : ℤ)) := by
            have : k * (3 * k - 1) = 3 * k ^ 2 + (-k) := by ring
            omega
          rw [if_neg hne_eq, if_neg hcond]
      · intro x _ y _ hxy
        have := congrArg Prod.snd hxy; dsimp at this; omega
    · intro p hp hnot
      rcases Finset.mem_image.mp hp with ⟨k, _, rfl⟩
      by_cases hcond : 3 * k ^ 2 + (-k) = ((2 * N : ℕ) : ℤ)
      · have h0 : (jacobiTriplePartial N).coeff (k ^ 2, -k) = 0 := by
          by_contra hne
          exact hnot (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, hcond⟩)
        rw [if_pos hcond, h0, zero_mul]
      · rw [if_neg hcond]
  rw [hsum_eq]
  split_ifs with h
  · let k₀ := Classical.choose h
    have hk₀ : (N : ℤ) = k₀ * (3 * k₀ - 1) / 2 := Classical.choose_spec h
    have hk₀_mem : k₀ ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1) := by
      rw [Finset.mem_Icc]
      have hhev := two_dvd_pentagonal k₀
      have h2N : k₀ * (3 * k₀ - 1) = 2 * (N : ℤ) := by omega
      have hkk : k₀ ^ 2 ≤ 2 * (N : ℤ) + 1 := by nlinarith
      constructor <;> nlinarith
    rw [Finset.sum_eq_single k₀]
    · rw [if_pos hk₀]
    · intro k _ hne
      rw [if_neg]
      intro hk
      exact hne (pentagonal_injective (hk.symm.trans hk₀))
    · intro hnot; exact (hnot hk₀_mem).elim
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg]
    intro hk
    exact h ⟨k, hk⟩

/-- Direct pentagonal coefficient evaluation at `k : ℤ`. -/
theorem coeff_eulerPhiSeries_pentagonal (k : ℤ) :
    PowerSeries.coeff (k * (3 * k - 1) / 2).toNat eulerPhiSeries = (-1 : ℤ) ^ k.natAbs := by
  have hnonneg : 0 ≤ k * (3 * k - 1) / 2 := by
    have hprod : 0 ≤ k * (3 * k - 1) := by
      rcases le_or_gt 0 k with h0 | h0
      · by_cases hk0 : k = 0
        · subst hk0; norm_num
        · have : 1 ≤ k := by omega
          nlinarith
      · nlinarith
    omega
  have htoNat : (((k * (3 * k - 1) / 2).toNat : ℕ) : ℤ) = k * (3 * k - 1) / 2 :=
    Int.toNat_of_nonneg hnonneg
  rw [euler_pentagonal_theorem]
  have hex : ∃ j : ℤ, (((k * (3 * k - 1) / 2).toNat : ℕ) : ℤ) = j * (3 * j - 1) / 2 :=
    ⟨k, htoNat⟩
  rw [dif_pos hex]
  have hchoose : Classical.choose hex = k :=
    pentagonal_injective ((Classical.choose_spec hex).symm.trans htoNat)
  rw [hchoose]

/-- Direct vanishing of `eulerPhiSeries` at non-pentagonal indices. -/
theorem coeff_eulerPhiSeries_of_not_pentagonal {N : ℕ}
    (h : ∀ k : ℤ, (N : ℤ) ≠ k * (3 * k - 1) / 2) :
    PowerSeries.coeff N eulerPhiSeries = 0 := by
  rw [euler_pentagonal_theorem, dif_neg]
  rintro ⟨k, hk⟩
  exact h k hk

/-- **EULER'S EXACT PENTAGONAL PARTITION RECURRENCE (`0` ASSUMPTIONS!)**:
for EVERY `N ≥ 1`,
$$p(N) = \sum_{k=1}^{N} (-1)^{k+1} \left(p\!\left(N - \frac{k(3k-1)}{2}\right) + p\!\left(N - \frac{k(3k+1)}{2}\right)\right)$$
(with terms where the pentagonal index exceeds `N` taken to be `0`). -/
theorem partition_pentagonal_recurrence {N : ℕ} (hN : 1 ≤ N) :
    (partCount N : ℤ) =
      ∑ k ∈ Finset.Icc 1 N, (-1 : ℤ) ^ (k + 1) *
        ((if k * (3 * k - 1) / 2 ≤ N then (partCount (N - k * (3 * k - 1) / 2) : ℤ) else 0) +
         (if k * (3 * k + 1) / 2 ≤ N then (partCount (N - k * (3 * k + 1) / 2) : ℤ) else 0)) := by
  have hmul : PowerSeries.coeff N (partSeries * eulerPhiSeries) = 0 := by
    rw [partSeries_mul_eulerPhi_eq_one, PowerSeries.coeff_one, if_neg (by omega)]
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a partSeries * PowerSeries.coeff b eulerPhiSeries)] at hmul
  -- Reindex a ↦ m = N - a, so sum is ∑_{m=0}^N p(N - m) * coeff m eulerPhiSeries = 0.
  have hrev : ∑ m ∈ Finset.range (N + 1),
      (partCount (N - m) : ℤ) * PowerSeries.coeff m eulerPhiSeries = 0 := by
    rw [← hmul]
    refine Finset.sum_nbij' (fun m => N - m) (fun a => N - a) ?_ ?_ ?_ ?_ ?_
    · intro m hm; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hm; omega)
    · intro a ha; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp ha; omega)
    · intro m hm; have := Finset.mem_range.mp hm; omega
    · intro a ha; have := Finset.mem_range.mp ha; omega
    · intro m hm
      have hm' := Finset.mem_range.mp hm
      have h1 : N - (N - m) = m := by omega
      simp only [partSeries, PowerSeries.coeff_mk, h1]
  -- Split off m = 0 (where coeff 0 eulerPhiSeries = 1)
  have hsplit0 : ∑ m ∈ Finset.range (N + 1),
      (partCount (N - m) : ℤ) * PowerSeries.coeff m eulerPhiSeries =
      (partCount N : ℤ) + ∑ m ∈ Finset.Icc 1 N,
        (partCount (N - m) : ℤ) * PowerSeries.coeff m eulerPhiSeries := by
    have hrange : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hrange, Finset.sum_insert (by simp), Nat.sub_zero, coeff_zero_eulerPhiSeries, mul_one]
  rw [hsplit0] at hrev
  -- Split the pentagonal sum over m ∈ Icc 1 N into positive k (m = k(3k-1)/2) and negative -k (m = k(3k+1)/2)!
  let pentPos (k : ℕ) : ℕ := k * (3 * k - 1) / 2
  let pentNeg (k : ℕ) : ℕ := k * (3 * k + 1) / 2
  have hpos_int : ∀ k : ℕ, 1 ≤ k → (pentPos k : ℤ) = (k : ℤ) * (3 * (k : ℤ) - 1) / 2 := by
    intro k hk
    dsimp only [pentPos]
    have h2 : 2 ∣ k * (3 * k - 1) := by
      rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · exact ⟨r * (3 * (r + r) - 1), by ring⟩
      · exact ⟨(2 * r + 1) * (3 * r + 1), by
          have : 3 * (2 * r + 1) - 1 = 2 * (3 * r + 1) := by omega
          rw [this]; ring⟩
    have h2z := two_dvd_pentagonal (k : ℤ)
    have hcast : ((k * (3 * k - 1) : ℕ) : ℤ) = (k : ℤ) * (3 * (k : ℤ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_mul]; norm_num
    omega
  have hneg_int : ∀ k : ℕ, 1 ≤ k → (pentNeg k : ℤ) = (-(k : ℤ)) * (3 * (-(k : ℤ)) - 1) / 2 := by
    intro k _
    dsimp only [pentNeg]
    have h2 : 2 ∣ k * (3 * k + 1) := by
      rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · exact ⟨r * (3 * (r + r) + 1), by ring⟩
      · exact ⟨(2 * r + 1) * (3 * r + 2), by ring⟩
    have h2z := two_dvd_pentagonal (-(k : ℤ))
    have hcast : ((k * (3 * k + 1) : ℕ) : ℤ) = (-(k : ℤ)) * (3 * (-(k : ℤ)) - 1) := by
      push_cast; ring
    omega
  have hpos_pos : ∀ k : ℕ, 1 ≤ k → 1 ≤ pentPos k := by
    intro k hk; dsimp only [pentPos]
    have : 2 ≤ k * (3 * k - 1) := by
      have : 2 ≤ 3 * k - 1 := by omega
      nlinarith
    omega
  have hneg_pos : ∀ k : ℕ, 1 ≤ k → 1 ≤ pentNeg k := by
    intro k hk; dsimp only [pentNeg]
    have : 4 ≤ k * (3 * k + 1) := by nlinarith
    omega
  -- Images of filtered Icc 1 N under pentPos and pentNeg are disjoint subsets of Icc 1 N!
  let A : Finset ℕ := (Finset.Icc 1 N).filter (fun k => pentPos k ≤ N)
  let B : Finset ℕ := (Finset.Icc 1 N).filter (fun k => pentNeg k ≤ N)
  have hA_sub : A.image pentPos ⊆ Finset.Icc 1 N := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨k, hk, rfl⟩
    rcases Finset.mem_filter.mp hk with ⟨hkI, hle⟩
    exact Finset.mem_Icc.mpr ⟨hpos_pos k (Finset.mem_Icc.mp hkI).1, hle⟩
  have hB_sub : B.image pentNeg ⊆ Finset.Icc 1 N := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨k, hk, rfl⟩
    rcases Finset.mem_filter.mp hk with ⟨hkI, hle⟩
    exact Finset.mem_Icc.mpr ⟨hneg_pos k (Finset.mem_Icc.mp hkI).1, hle⟩
  have hdisj : Disjoint (A.image pentPos) (B.image pentNeg) := by
    refine Finset.disjoint_left.mpr fun m hmA hmB => ?_
    rcases Finset.mem_image.mp hmA with ⟨k1, hk1, rfl⟩
    rcases Finset.mem_image.mp hmB with ⟨k2, hk2, heq⟩
    have h1 : 1 ≤ k1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk1).1).1
    have h2 : 1 ≤ k2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk2).1).1
    have hcast : (pentPos k1 : ℤ) = (pentNeg k2 : ℤ) := congrArg Nat.cast heq.symm
    rw [hpos_int k1 h1, hneg_int k2 h2] at hcast
    have hinj := pentagonal_injective hcast
    omega
  have hsum_Icc : ∑ m ∈ Finset.Icc 1 N, (partCount (N - m) : ℤ) * PowerSeries.coeff m eulerPhiSeries =
      ∑ m ∈ A.image pentPos ∪ B.image pentNeg,
        (partCount (N - m) : ℤ) * PowerSeries.coeff m eulerPhiSeries := by
    symm
    refine Finset.sum_subset (Finset.union_subset hA_sub hB_sub) fun m hm hnot => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmN : m ≤ N := (Finset.mem_Icc.mp hm).2
    have h0 : PowerSeries.coeff m eulerPhiSeries = 0 := by
      refine coeff_eulerPhiSeries_of_not_pentagonal fun k hk => ?_
      have h2z := two_dvd_pentagonal k
      rcases lt_trichotomy k 0 with hlt | rfl | hgt
      · let j : ℕ := k.natAbs
        have hj1 : 1 ≤ j := by omega
        have hkj : k = -(j : ℤ) := by omega
        have hj_eq : pentNeg j = m := by
          have h1 := hneg_int j hj1
          rw [← hkj, ← hk] at h1
          exact Int.ofNat.inj h1
        have hjN : j ≤ N := by
          have : j ≤ pentNeg j := by
            dsimp only [pentNeg]
            have : 2 * j ≤ j * (3 * j + 1) := by nlinarith
            omega
          omega
        apply hnot
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj1, hjN⟩, by omega⟩, hj_eq⟩)
      · norm_num at hk; omega
      · let j : ℕ := k.natAbs
        have hj1 : 1 ≤ j := by omega
        have hkj : k = (j : ℤ) := by omega
        have hj_eq : pentPos j = m := by
          have h1 := hpos_int j hj1
          rw [← hkj, ← hk] at h1
          exact Int.ofNat.inj h1
        have hjN : j ≤ N := by
          have : j ≤ pentPos j := by
            dsimp only [pentPos]
            have : 2 * j ≤ j * (3 * j - 1) := by
              have : 2 ≤ 3 * j - 1 := by omega
              nlinarith
            omega
          omega
        apply hnot
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj1, hjN⟩, by omega⟩, hj_eq⟩)
    rw [h0, mul_zero]
  rw [hsum_Icc, Finset.sum_union hdisj] at hrev
  -- Evaluate the two image sums!
  have hA_sum : ∑ m ∈ A.image pentPos, (partCount (N - m) : ℤ) * PowerSeries.coeff m eulerPhiSeries =
      ∑ k ∈ Finset.Icc 1 N,
        if pentPos k ≤ N then (partCount (N - pentPos k) : ℤ) * (-1 : ℤ) ^ k else 0 := by
    rw [Finset.sum_image]
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k hk => ?_
      split_ifs with hle
      · have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hcoeff := coeff_eulerPhiSeries_pentagonal (k : ℤ)
        rw [← hpos_int k hk1, Int.toNat_natCast, Int.natAbs_natCast] at hcoeff
        rw [hcoeff]
      · rfl
    · intro k1 hk1 k2 hk2 heq
      have h1 : 1 ≤ k1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk1).1).1
      have h2 : 1 ≤ k2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk2).1).1
      have hcast : (pentPos k1 : ℤ) = (pentPos k2 : ℤ) := congrArg Nat.cast heq
      rw [hpos_int k1 h1, hpos_int k2 h2] at hcast
      exact Int.ofNat.inj (pentagonal_injective hcast)
  have hB_sum : ∑ m ∈ B.image pentNeg, (partCount (N - m) : ℤ) * PowerSeries.coeff m eulerPhiSeries =
      ∑ k ∈ Finset.Icc 1 N,
        if pentNeg k ≤ N then (partCount (N - pentNeg k) : ℤ) * (-1 : ℤ) ^ k else 0 := by
    rw [Finset.sum_image]
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k hk => ?_
      split_ifs with hle
      · have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hcoeff := coeff_eulerPhiSeries_pentagonal (-(k : ℤ))
        rw [← hneg_int k hk1, Int.toNat_natCast, Int.natAbs_neg, Int.natAbs_natCast] at hcoeff
        rw [hcoeff]
      · rfl
    · intro k1 hk1 k2 hk2 heq
      have h1 : 1 ≤ k1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk1).1).1
      have h2 : 1 ≤ k2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk2).1).1
      have hcast : (pentNeg k1 : ℤ) = (pentNeg k2 : ℤ) := congrArg Nat.cast heq
      rw [hneg_int k1 h1, hneg_int k2 h2] at hcast
      have hinj := pentagonal_injective hcast
      omega
  rw [hA_sum, hB_sum, ← Finset.sum_add_distrib] at hrev
  have hneg_sum : -(∑ k ∈ Finset.Icc 1 N,
      ((if pentPos k ≤ N then (partCount (N - pentPos k) : ℤ) * (-1 : ℤ) ^ k else 0) +
       (if pentNeg k ≤ N then (partCount (N - pentNeg k) : ℤ) * (-1 : ℤ) ^ k else 0))) =
      ∑ k ∈ Finset.Icc 1 N, (-1 : ℤ) ^ (k + 1) *
        ((if pentPos k ≤ N then (partCount (N - pentPos k) : ℤ) else 0) +
         (if pentNeg k ≤ N then (partCount (N - pentNeg k) : ℤ) else 0)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ]
    split_ifs <;> ring
  linarith

/-- Formal operator `θ = q d/dq` on `ℤ⟦q⟧`. -/
private def thetaOp (f : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (n : ℤ) * PowerSeries.coeff n f

private lemma coeff_thetaOp (f : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (thetaOp f) = (n : ℤ) * PowerSeries.coeff n f := by
  simp [thetaOp]

private lemma thetaOp_one : thetaOp 1 = 0 :=
  PowerSeries.ext fun n => by
    rw [coeff_thetaOp, map_zero, PowerSeries.coeff_one]
    split_ifs with hn
    · subst hn; simp
    · simp

private lemma thetaOp_mul (f g : PowerSeries ℤ) :
    thetaOp (f * g) = thetaOp f * g + f * thetaOp g :=
  PowerSeries.ext fun n => by
    rw [coeff_thetaOp, map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hsum : (x.1 : ℤ) + (x.2 : ℤ) = (n : ℤ) := by
      exact_mod_cast Finset.mem_antidiagonal.mp hx
    rw [coeff_thetaOp, coeff_thetaOp, ← hsum]
    ring

private lemma thetaOp_one_sub_X_pow (m : ℕ) :
    thetaOp (1 - PowerSeries.X ^ m) = -((m : PowerSeries ℤ) * PowerSeries.X ^ m) :=
  PowerSeries.ext fun n => by
    rw [coeff_thetaOp, map_neg, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
    have hmul : PowerSeries.coeff n ((m : PowerSeries ℤ) * PowerSeries.X ^ m) =
        if m = n then (m : ℤ) else 0 := by
      have hm : (m : PowerSeries ℤ) = PowerSeries.C (m : ℤ) := by simp
      rw [hm, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      by_cases h : n = m
      · subst h; simp
      · have h' : m ≠ n := Ne.symm h
        rw [if_neg h, if_neg h', mul_zero]
    rw [hmul]
    by_cases hn0 : n = 0
    · subst hn0; simp
    · by_cases hnm : n = m
      · subst hnm; simp [hn0]
      · have hmn : m ≠ n := Ne.symm hnm
        simp [hn0, hnm, hmn]

/-- Geometric series `(1 - X^m)⁻¹ = ∑_{j ≥ 0} X^{m j}` in `PowerSeries ℤ` for `m ≥ 1`. -/
private def geomSeries (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if m ∣ n then 1 else 0

private lemma one_sub_X_pow_mul_geomSeries {m : ℕ} (hm : 1 ≤ m) :
    (1 - PowerSeries.X ^ m) * geomSeries m = 1 :=
  PowerSeries.ext fun n => by
    rw [mul_comm, coeff_mul_one_sub_X_pow, PowerSeries.coeff_one]
    simp only [geomSeries, PowerSeries.coeff_mk]
    by_cases hn0 : n = 0
    · subst hn0
      rw [if_pos (dvd_zero m), if_neg (by omega), sub_zero, if_pos rfl]
    · rw [if_neg hn0]
      by_cases h1 : m ∣ n
      · have hle : m ≤ n := Nat.le_of_dvd (by omega) h1
        have hsub : m ∣ n - m := by
          rcases h1 with ⟨q, hq⟩
          refine ⟨q - 1, ?_⟩
          have hq1 : 1 ≤ q := by
            by_contra h0; push Not at h0
            have hq0 : q = 0 := by omega
            subst hq0; simp at hq; omega
          have : m * (q - 1) = m * q - m := Nat.mul_sub_one m q
          omega
        rw [if_pos h1, if_pos hle, if_pos hsub, sub_self]
      · rw [if_neg h1]
        by_cases hle : m ≤ n
        · have hsub : ¬ m ∣ n - m := by
            intro hdm
            apply h1
            rcases hdm with ⟨q, hq⟩
            exact ⟨q + 1, by rw [mul_add, mul_one]; omega⟩
          rw [if_pos hle, if_neg hsub, sub_self]
        · rw [if_neg hle, sub_self]

private lemma log_deriv_prod {s : Finset ℕ} (f g : ℕ → PowerSeries ℤ)
    (hfg : ∀ m ∈ s, f m * g m = 1) :
    (∏ m ∈ s, g m) * thetaOp (∏ m ∈ s, f m) = ∑ m ∈ s, g m * thetaOp (f m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [thetaOp_one]
  | insert a s ha ih =>
    have hfa : f a * g a = 1 := hfg a (Finset.mem_insert_self _ _)
    have hprod_inv : (∏ m ∈ s, g m) * (∏ m ∈ s, f m) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun m hm => by
        rw [mul_comm]; exact hfg m (Finset.mem_insert_of_mem hm)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, thetaOp_mul]
    have ih' := ih fun m hm => hfg m (Finset.mem_insert_of_mem hm)
    calc (g a * ∏ m ∈ s, g m) * (thetaOp (f a) * ∏ m ∈ s, f m + f a * thetaOp (∏ m ∈ s, f m))
        = (g a * thetaOp (f a)) * ((∏ m ∈ s, g m) * (∏ m ∈ s, f m)) +
            (f a * g a) * ((∏ m ∈ s, g m) * thetaOp (∏ m ∈ s, f m)) := by ring
      _ = g a * thetaOp (f a) + ∑ m ∈ s, g m * thetaOp (f m) := by
            rw [hprod_inv, hfa, ih', mul_one, one_mul]

/-- **EULER'S EXACT DIVISOR-SUM PARTITION RECURRENCE (`0` ASSUMPTIONS!)**:
for EVERY `n : ℕ`,
$$n \cdot p(n) = \sum_{k=1}^{n} \sigma_1(k) \cdot p(n - k).$$ -/
theorem partition_divisor_sum_recurrence (n : ℕ) :
    n * partCount n =
      ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.sigma 1 k * partCount (n - k) := by
  have hprod_eq : ∏ m ∈ Finset.Icc 1 n, geomSeries m = partSeriesLe n := by
    have h1 : (∏ m ∈ Finset.Icc 1 n, geomSeries m) * eulerPhiPartial n = 1 := by
      unfold eulerPhiPartial
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun m hm => by
        rw [mul_comm]
        exact one_sub_X_pow_mul_geomSeries (Finset.mem_Icc.mp hm).1
    calc ∏ m ∈ Finset.Icc 1 n, geomSeries m
        = (∏ m ∈ Finset.Icc 1 n, geomSeries m) * (eulerPhiPartial n * partSeriesLe n) := by
            rw [mul_comm (eulerPhiPartial n), partSeriesLe_mul_eulerPhiPartial, mul_one]
      _ = ((∏ m ∈ Finset.Icc 1 n, geomSeries m) * eulerPhiPartial n) * partSeriesLe n := by ring
      _ = partSeriesLe n := by rw [h1, one_mul]
  have hlog := log_deriv_prod (s := Finset.Icc 1 n)
    (fun m => 1 - PowerSeries.X ^ m) geomSeries
    (fun m hm => one_sub_X_pow_mul_geomSeries (Finset.mem_Icc.mp hm).1)
  rw [hprod_eq] at hlog
  change partSeriesLe n * thetaOp (eulerPhiPartial n) =
    ∑ m ∈ Finset.Icc 1 n, geomSeries m * thetaOp (1 - PowerSeries.X ^ m) at hlog
  -- Differentiate partSeriesLe n * eulerPhiPartial n = 1 and multiply by partSeriesLe n!
  have hdiff : thetaOp (partSeriesLe n) =
      partSeriesLe n * ∑ m ∈ Finset.Icc 1 n, geomSeries m * ((m : PowerSeries ℤ) * PowerSeries.X ^ m) := by
    have h0 := congrArg thetaOp (partSeriesLe_mul_eulerPhiPartial n)
    rw [thetaOp_mul, thetaOp_one] at h0
    have hneg : ∑ m ∈ Finset.Icc 1 n, geomSeries m * thetaOp (1 - PowerSeries.X ^ m) =
        -(∑ m ∈ Finset.Icc 1 n, geomSeries m * ((m : PowerSeries ℤ) * PowerSeries.X ^ m)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [thetaOp_one_sub_X_pow, mul_neg]
    have hmul0 : partSeriesLe n *
        (thetaOp (partSeriesLe n) * eulerPhiPartial n + partSeriesLe n * thetaOp (eulerPhiPartial n)) = 0 := by
      rw [h0, mul_zero]
    have hsimp : partSeriesLe n *
        (thetaOp (partSeriesLe n) * eulerPhiPartial n + partSeriesLe n * thetaOp (eulerPhiPartial n)) =
        thetaOp (partSeriesLe n) * (partSeriesLe n * eulerPhiPartial n) +
          partSeriesLe n * (partSeriesLe n * thetaOp (eulerPhiPartial n)) := by ring
    rw [hsimp, partSeriesLe_mul_eulerPhiPartial, mul_one, hlog, hneg, mul_neg] at hmul0
    exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using hmul0)
  -- Take coeff n of both sides!
  have hcn := congrArg (PowerSeries.coeff n) hdiff
  rw [coeff_thetaOp] at hcn
  have hLHS : (n : ℤ) * PowerSeries.coeff n (partSeriesLe n) = ((n * partCount n : ℕ) : ℤ) := by
    simp only [partSeriesLe, PowerSeries.coeff_mk, partCountLe_eq_partCount (le_refl n), Nat.cast_mul]
  rw [hLHS, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a (partSeriesLe n) *
        PowerSeries.coeff b (∑ m ∈ Finset.Icc 1 n, geomSeries m * ((m : PowerSeries ℤ) * PowerSeries.X ^ m)))] at hcn
  -- Compute coeff k of the sigma1 partial series for k ≤ n!
  have hsig : ∀ k : ℕ, k ≤ n →
      PowerSeries.coeff k (∑ m ∈ Finset.Icc 1 n, geomSeries m * ((m : PowerSeries ℤ) * PowerSeries.X ^ m)) =
        if k = 0 then 0 else (ArithmeticFunction.sigma 1 k : ℤ) := by
    intro k hkn
    rw [map_sum]
    have hterm : ∀ m ∈ Finset.Icc 1 n,
        PowerSeries.coeff k (geomSeries m * ((m : PowerSeries ℤ) * PowerSeries.X ^ m)) =
          if m ∣ k ∧ 1 ≤ k then (m : ℤ) else 0 := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hcomm : geomSeries m * ((m : PowerSeries ℤ) * PowerSeries.X ^ m) =
          (PowerSeries.C (m : ℤ) * geomSeries m) * PowerSeries.X ^ m := by
        have : (m : PowerSeries ℤ) = PowerSeries.C (m : ℤ) := by simp
        rw [this]; ring
      rw [hcomm, coeff_mul_X_pow_eq]
      split_ifs with hmk hdvd hdvd2
      · rw [PowerSeries.coeff_C_mul]
        simp only [geomSeries, PowerSeries.coeff_mk]
        have hd : m ∣ k - m := by
          rcases hdvd.1 with ⟨q, hq⟩
          exact ⟨q - 1, by
            have hq1 : 1 ≤ q := by
              by_contra h0; push Not at h0
              have hq0 : q = 0 := by omega
              subst hq0; simp at hq; omega
            have : m * (q - 1) = m * q - m := Nat.mul_sub_one m q
            omega⟩
        rw [if_pos hd, mul_one]
      · rw [PowerSeries.coeff_C_mul]
        simp only [geomSeries, PowerSeries.coeff_mk]
        have hnd : ¬ m ∣ k - m := by
          intro hdm
          apply hdvd
          refine ⟨?_, by omega⟩
          rcases hdm with ⟨q, hq⟩
          exact ⟨q + 1, by rw [mul_add, mul_one]; omega⟩
        rw [if_neg hnd, mul_zero]
      · exfalso
        have : m ≤ k := Nat.le_of_dvd (by omega) hdvd2.1
        omega
      · rfl
    rw [Finset.sum_congr rfl hterm]
    split_ifs with hk0
    · subst hk0; simp
    · simp only [show 1 ≤ k by omega, and_true]
      rw [ArithmeticFunction.sigma_apply, Nat.cast_sum]
      rw [← Finset.sum_filter]
      have hfilt : (Finset.Icc 1 n).filter (fun m => m ∣ k) = k.divisors := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨_, _⟩, hd⟩; exact ⟨hd, hk0⟩
        · rintro ⟨hd, _⟩
          have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos hd (by omega)
          have hmk : m ≤ k := Nat.le_of_dvd (by omega) hd
          exact ⟨⟨hm1, le_trans hmk hkn⟩, hd⟩
      rw [hfilt]
      simp
  -- Reindex the antidiagonal sum by k = n - a!
  have hRHS : ∑ a ∈ Finset.range (n + 1),
      PowerSeries.coeff a (partSeriesLe n) *
        PowerSeries.coeff (n - a)
          (∑ m ∈ Finset.Icc 1 n, geomSeries m * ((m : PowerSeries ℤ) * PowerSeries.X ^ m)) =
      ((∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.sigma 1 k * partCount (n - k) : ℕ) : ℤ) := by
    have hreidx : ∑ a ∈ Finset.range (n + 1),
        PowerSeries.coeff a (partSeriesLe n) *
          PowerSeries.coeff (n - a)
            (∑ m ∈ Finset.Icc 1 n, geomSeries m * ((m : PowerSeries ℤ) * PowerSeries.X ^ m)) =
        ∑ k ∈ Finset.range (n + 1),
          (partCount (n - k) : ℤ) * (if k = 0 then 0 else (ArithmeticFunction.sigma 1 k : ℤ)) := by
      refine Finset.sum_nbij' (fun a => n - a) (fun k => n - k) ?_ ?_ ?_ ?_ ?_
      · intro a ha; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp ha; omega)
      · intro k hk; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega)
      · intro a ha; have := Finset.mem_range.mp ha; omega
      · intro k hk; have := Finset.mem_range.mp hk; omega
      · intro a ha
        have ha' := Finset.mem_range.mp ha
        have h1 : n - (n - a) = a := by omega
        rw [h1, hsig (n - a) (by omega)]
        simp only [partSeriesLe, PowerSeries.coeff_mk, partCountLe_eq_partCount (by omega : a ≤ n)]
    rw [hreidx]
    have hrange : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hrange, Finset.sum_insert (by simp), if_pos rfl, mul_zero, zero_add, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
    rw [if_neg hk0, Nat.cast_mul, mul_comm]
  rw [hRHS] at hcn
  exact Int.ofNat.inj hcn

/-- Ring homomorphism `LaurentQZ →+* LaurentQZ` substituting `(q, z) ↦ (q, -z q)`. -/
private def cubeHom : LaurentQZ →+* LaurentQZ :=
  AddMonoidAlgebra.lift ℤ LaurentQZ (ℤ × ℤ)
    { toFun := fun p =>
        AddMonoidAlgebra.single
          ((Multiplicative.toAdd p).1 + (Multiplicative.toAdd p).2, (Multiplicative.toAdd p).2)
          ((((-1 : ℤˣ) ^ (Multiplicative.toAdd p).2 : ℤˣ) : ℤ))
      map_one' := by
        show AddMonoidAlgebra.single ((0 : ℤ) + 0, (0 : ℤ)) (((-1 : ℤˣ) ^ (0 : ℤ) : ℤˣ) : ℤ) = 1
        simp [← qzMon_zero, qzMon]
      map_mul' := fun p q => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, zpow_add, Units.val_mul,
          AddMonoidAlgebra.single_mul_single]
        congr 1
        apply Prod.ext
        · dsimp; ring
        · rfl }

private lemma cubeHom_qzMon (a b : ℤ) :
    cubeHom (qzMon a b) = AddMonoidAlgebra.single (a + b, b) (((-1 : ℤˣ) ^ b : ℤˣ) : ℤ) := by
  simp [cubeHom, qzMon]

/-- Linear functional extracting `(z d/dz)|_{z=1}` on the `q^a`-slice of `f : LaurentQZ`. -/
private def zDerivAtOne (f : LaurentQZ) (a : ℤ) : ℤ :=
  f.coeff.sum fun p v => if p.1 = a then p.2 * v else 0

private lemma zDerivAtOne_add (f g : LaurentQZ) (a : ℤ) :
    zDerivAtOne (f + g) a = zDerivAtOne f a + zDerivAtOne g a := by
  unfold zDerivAtOne
  rw [AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index']
  · intro _; simp
  · intro p v₁ v₂; split_ifs <;> ring

private lemma zDerivAtOne_single (x y v a : ℤ) :
    zDerivAtOne (AddMonoidAlgebra.single (x, y) v) a = if x = a then y * v else 0 := by
  unfold zDerivAtOne
  rw [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]

private lemma zDerivAtOne_sub (f g : LaurentQZ) (a : ℤ) :
    zDerivAtOne (f - g) a = zDerivAtOne f a - zDerivAtOne g a := by
  have h := zDerivAtOne_add (f - g) g a
  rw [sub_add_cancel] at h
  omega

/-- Key identity: `(z d/dz)|_{z=1} [(1 - z⁻¹) * g] = g|_{z=1}` on every `q^a`-slice! -/
private lemma zDerivAtOne_one_sub_zInv_mul (g : LaurentQZ) (a : ℤ) :
    zDerivAtOne ((1 - qzMon 0 (-1)) * g) a = (evalZHom (1 : ℤˣ) g).coeff a := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single g]
  conv_rhs => rw [← AddMonoidAlgebra.sum_coeff_single g]
  simp only [Finsupp.sum, Finset.mul_sum, map_sum]
  have hL : ∀ (s : Finset (ℤ × ℤ)) (h : ℤ × ℤ → LaurentQZ),
      zDerivAtOne (∑ p ∈ s, h p) a = ∑ p ∈ s, zDerivAtOne (h p) a := by
    intro s h
    classical
    induction s using Finset.induction_on with
    | empty => simp [zDerivAtOne]
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, zDerivAtOne_add, ih]
  have hR : ∀ (s : Finset (ℤ × ℤ)) (h : ℤ × ℤ → AddMonoidAlgebra ℤ ℤ),
      (∑ p ∈ s, h p).coeff a = ∑ p ∈ s, (h p).coeff a := by
    intro s h
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, ih]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sub_mul, one_mul, zDerivAtOne_sub, zDerivAtOne_single]
  have hmul : qzMon 0 (-1) * AddMonoidAlgebra.single p (g.coeff p) =
      AddMonoidAlgebra.single (p.1, p.2 - 1) (g.coeff p) := by
    rw [qzMon, AddMonoidAlgebra.single_mul_single, one_mul]
    congr 1; ext <;> dsimp <;> omega
  rw [hmul, zDerivAtOne_single]
  have hsingle : AddMonoidAlgebra.single p (g.coeff p) = (g.coeff p : ℤ) • qzMon p.1 p.2 := by
    simp [qzMon, AddMonoidAlgebra.smul_single]
  rw [hsingle, map_zsmul, evalZHom_qzMon, one_zpow, Units.val_one, AddMonoidAlgebra.smul_single,
    zsmul_eq_mul, mul_one, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs
  · simp; ring
  · simp

private lemma zDerivAtOne_cubeHom (f : LaurentQZ) (a : ℤ) :
    zDerivAtOne (cubeHom f) a =
      f.coeff.sum fun p v =>
        if p.1 + p.2 = a then p.2 * (v * (((-1 : ℤˣ) ^ p.2 : ℤˣ) : ℤ)) else 0 := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  simp only [Finsupp.sum, map_sum]
  have hL : ∀ (s : Finset (ℤ × ℤ)) (h : ℤ × ℤ → LaurentQZ),
      zDerivAtOne (∑ p ∈ s, h p) a = ∑ p ∈ s, zDerivAtOne (h p) a := by
    intro s h
    classical
    induction s using Finset.induction_on with
    | empty => simp [zDerivAtOne]
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, zDerivAtOne_add, ih]
  rw [hL]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hsingle : AddMonoidAlgebra.single p (f.coeff p) = (f.coeff p : ℤ) • qzMon p.1 p.2 := by
    simp [qzMon, AddMonoidAlgebra.smul_single]
  rw [hsingle, map_zsmul, cubeHom_qzMon]
  have hsmul : (f.coeff p : ℤ) • AddMonoidAlgebra.single (p.1 + p.2, p.2) (((-1 : ℤˣ) ^ p.2 : ℤˣ) : ℤ) =
      AddMonoidAlgebra.single (p.1 + p.2, p.2) (f.coeff p * (((-1 : ℤˣ) ^ p.2 : ℤˣ) : ℤ)) := by
    rw [AddMonoidAlgebra.smul_single, smul_eq_mul]
  rw [hsmul, zDerivAtOne_single]

private lemma triangular_injective {k₁ k₂ : ℕ}
    (h : k₁ * (k₁ + 1) / 2 = k₂ * (k₂ + 1) / 2) : k₁ = k₂ := by
  have hev1 : 2 ∣ k₁ * (k₁ + 1) := Nat.even_mul_succ_self k₁ |>.two_dvd
  have hev2 : 2 ∣ k₂ * (k₂ + 1) := Nat.even_mul_succ_self k₂ |>.two_dvd
  have hmul : k₁ * (k₁ + 1) = k₂ * (k₂ + 1) := by omega
  nlinarith

open scoped Classical in
/-- **UNCONDITIONAL JACOBI'S CUBE IDENTITY (`0` ASSUMPTIONS!)**:
for EVERY `N : ℕ`,
$$\operatorname{coeff}_N\!\left(\prod_{m \ge 1} (1 - q^m)^3\right) =
  \begin{cases} (-1)^k (2k + 1) & \text{if } N = k(k+1)/2 \text{ for some } k \in \mathbb{N}, \\ 0 & \text{otherwise.} \end{cases}$$ -/
theorem jacobi_cube_identity (N : ℕ) :
    PowerSeries.coeff N (eulerPhiSeries ^ 3) =
      if h : ∃ k : ℕ, N = k * (k + 1) / 2 then
        (-1 : ℤ) ^ (Classical.choose h) * (2 * ((Classical.choose h : ℕ) : ℤ) + 1)
      else 0 := by
  let M : ℕ := 4 * N + 2
  have hM1 : 1 ≤ M := by omega
  -- Step 1: Factor cubeHom (jacobiTriplePartial M) = (1 - z⁻¹) * G_M!
  let G : LaurentQZ :=
    (∏ n ∈ Finset.Icc 1 M, (1 - qzMon (2 * (n : ℤ)) 0)) *
    (∏ n ∈ Finset.Icc 1 M, (1 - qzMon (2 * (n : ℤ)) 1)) *
    (∏ n ∈ Finset.Icc 1 (M - 1), (1 - qzMon (2 * (n : ℤ)) (-1)))
  have hcube_fac : cubeHom (jacobiTriplePartial M) = (1 - qzMon 0 (-1)) * G := by
    unfold jacobiTriplePartial jacobiDoublePartial
    rw [Finset.prod_mul_distrib, map_mul, map_mul, map_prod, map_prod, map_prod]
    have h1 : ∏ n ∈ Finset.Icc 1 M, cubeHom (1 - qzMon (2 * (n : ℤ)) 0) =
        ∏ n ∈ Finset.Icc 1 M, (1 - qzMon (2 * (n : ℤ)) 0) := by
      refine Finset.prod_congr rfl fun n _ => ?_
      rw [map_sub, map_one, cubeHom_qzMon]
      simp [qzMon]
    have h2 : ∏ n ∈ Finset.Icc 1 M, cubeHom (1 + qzMon (2 * (n : ℤ) - 1) 1) =
        ∏ n ∈ Finset.Icc 1 M, (1 - qzMon (2 * (n : ℤ)) 1) := by
      refine Finset.prod_congr rfl fun n _ => ?_
      rw [map_add, map_one, cubeHom_qzMon, negOneUnit_zpow, Int.natAbs_one, pow_one,
        AddMonoidAlgebra.single_neg]
      have : 2 * (n : ℤ) - 1 + 1 = 2 * (n : ℤ) := by ring
      rw [this, ← qzMon, sub_eq_add_neg]
    have h3 : ∏ n ∈ Finset.Icc 1 M, cubeHom (1 + qzMon (2 * (n : ℤ) - 1) (-1)) =
        (1 - qzMon 0 (-1)) * ∏ n ∈ Finset.Icc 1 (M - 1), (1 - qzMon (2 * (n : ℤ)) (-1)) := by
      have hIcc : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.prod_insert (by simp)]
      congr 1
      · rw [map_add, map_one, cubeHom_qzMon, negOneUnit_zpow, Int.natAbs_neg, Int.natAbs_one,
          pow_one, AddMonoidAlgebra.single_neg]
        have : 2 * ((1 : ℕ) : ℤ) - 1 + -1 = 0 := by norm_num
        rw [this, ← qzMon, sub_eq_add_neg]
      · have hM' : M = (M - 1) + 1 := by omega
        rw [hM', prod_Icc_shift (M - 1) (fun n => cubeHom (1 + qzMon (2 * (n : ℤ) - 1) (-1)))]
        refine Finset.prod_congr rfl fun n _ => ?_
        rw [map_add, map_one, cubeHom_qzMon, negOneUnit_zpow, Int.natAbs_neg, Int.natAbs_one,
          pow_one, AddMonoidAlgebra.single_neg]
        have : 2 * ((n + 1 : ℕ) : ℤ) - 1 + -1 = 2 * (n : ℤ) := by push_cast; ring
        rw [this, ← qzMon, sub_eq_add_neg]
    rw [h1, h2, h3]
    dsimp only [G]
    ring
  -- Step 2: Evaluate LHS = zDerivAtOne (cubeHom (jacobiTriplePartial M)) (2 * N) = coeff N (eulerPhiSeries^3)!
  have hLHS : zDerivAtOne (cubeHom (jacobiTriplePartial M)) ((2 * N : ℕ) : ℤ) =
      PowerSeries.coeff N (eulerPhiSeries ^ 3) := by
    rw [hcube_fac, zDerivAtOne_one_sub_zInv_mul]
    have hG1 : evalZHom (1 : ℤˣ) G =
        polyToLaurent ((∏ n ∈ Finset.Icc 1 M, (1 - Polynomial.X ^ (2 * n) : Polynomial ℤ)) ^ 2 *
          (∏ n ∈ Finset.Icc 1 (M - 1), (1 - Polynomial.X ^ (2 * n) : Polynomial ℤ))) := by
      dsimp only [G]
      rw [map_mul, map_mul, map_prod, map_prod, map_prod, map_mul, map_pow, map_prod, map_prod, sq]
      have hfac : ∀ (K : ℕ) (b : ℤ),
          ∏ n ∈ Finset.Icc 1 K, evalZHom (1 : ℤˣ) (1 - qzMon (2 * (n : ℤ)) b) =
            ∏ n ∈ Finset.Icc 1 K, polyToLaurent (1 - Polynomial.X ^ (2 * n) : Polynomial ℤ) := by
        intro K b
        refine Finset.prod_congr rfl fun n _ => ?_
        rw [map_sub, map_one, evalZHom_qzMon, one_zpow, Units.val_one, map_sub, map_one,
          polyToLaurent_X_pow]
        push_cast; rfl
      rw [hfac M 0, hfac M 1, hfac (M - 1) (-1)]
    rw [hG1, coeff_polyToLaurent_nat, ← coeff_coeToPowerSeries]
    have hps : Polynomial.coeToPowerSeries.ringHom
        ((∏ n ∈ Finset.Icc 1 M, (1 - Polynomial.X ^ (2 * n) : Polynomial ℤ)) ^ 2 *
          (∏ n ∈ Finset.Icc 1 (M - 1), (1 - Polynomial.X ^ (2 * n) : Polynomial ℤ))) =
        PowerSeries.expand 2 (by norm_num) (eulerPhiPartial M ^ 2 * eulerPhiPartial (M - 1)) := by
      unfold eulerPhiPartial
      rw [map_mul, map_pow, map_prod, map_prod, map_mul, map_pow, map_prod, map_prod]
      have hterm : ∀ k : ℕ, Polynomial.coeToPowerSeries.ringHom (1 - Polynomial.X ^ (2 * k) : Polynomial ℤ) =
          PowerSeries.expand 2 (by norm_num) (1 - PowerSeries.X ^ k) := by
        intro k
        rw [map_sub, map_one, map_pow, map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
        simp
      simp only [hterm]
    rw [hps, PowerSeries.coeff_expand_mul]
    -- Stabilize eulerPhiPartial M ^ 2 * eulerPhiPartial (M - 1) to eulerPhiSeries ^ 3 at degree N!
    have hstab : ∀ f₁ f₂ g₁ g₂ : PowerSeries ℤ,
        (∀ i ≤ N, PowerSeries.coeff i f₁ = PowerSeries.coeff i g₁) →
        (∀ i ≤ N, PowerSeries.coeff i f₂ = PowerSeries.coeff i g₂) →
        PowerSeries.coeff N (f₁ * f₂) = PowerSeries.coeff N (g₁ * g₂) := by
      intro f₁ f₂ g₁ g₂ hf hg
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hsum := Finset.mem_antidiagonal.mp hx
      rw [hf x.1 (by omega), hg x.2 (by omega)]
    rw [show eulerPhiSeries ^ 3 = eulerPhiSeries ^ 2 * eulerPhiSeries by ring]
    refine hstab _ _ _ _ ?_ (fun i hi => (coeff_eulerPhiSeries_eq_partial (by omega)).symm)
    intro i hi
    rw [sq, sq, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hsum := Finset.mem_antidiagonal.mp hx
    rw [(coeff_eulerPhiSeries_eq_partial (by omega)).symm,
      (coeff_eulerPhiSeries_eq_partial (by omega)).symm]
  -- Step 3: Evaluate RHS via zDerivAtOne_cubeHom + jacobi_triple_product_coeff!
  rw [← hLHS, zDerivAtOne_cubeHom]
  have hsum_eq : (jacobiTriplePartial M).coeff.sum (fun p v =>
      if p.1 + p.2 = ((2 * N : ℕ) : ℤ) then p.2 * (v * (((-1 : ℤˣ) ^ p.2 : ℤˣ) : ℤ)) else 0) =
      ∑ b ∈ Finset.Icc (-(2 * (N : ℤ) + 1)) (2 * (N : ℤ) + 1),
        if b ^ 2 + b = ((2 * N : ℕ) : ℤ) then b * (-1 : ℤ) ^ b.natAbs else 0 := by
    rw [Finsupp.sum]
    have hsub : (jacobiTriplePartial M).coeff.support.filter
        (fun p => p.1 + p.2 = ((2 * N : ℕ) : ℤ)) ⊆
        (Finset.Icc (-(2 * (N : ℤ) + 1)) (2 * (N : ℤ) + 1)).image (fun b => (b ^ 2, b)) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hsupp, hp_eq⟩
      have hne : (jacobiTriplePartial M).coeff p ≠ 0 := Finsupp.mem_support_iff.mp hsupp
      have hsq : p.2 ^ 2 ≤ p.1 := jacobiTriplePartial_support_bound M p.1 p.2 hne
      have hp1_nonneg : 0 ≤ p.1 := by nlinarith
      have hb_bound : |p.2| ≤ 2 * (N : ℤ) + 1 := by
        have hbb : p.2 ^ 2 + p.2 ≤ 2 * (N : ℤ) := by omega
        rw [abs_le]
        constructor <;> nlinarith
      have hp1_le : p.1 ≤ 4 * (N : ℤ) + 1 := by
        have := abs_le.mp hb_bound; omega
      have htp := jacobi_triple_product_coeff p.1.toNat p.2 (M := M) (by dsimp [M]; omega)
      have htoNat : ((p.1.toNat : ℕ) : ℤ) = p.1 := Int.toNat_of_nonneg hp1_nonneg
      rw [htoNat] at htp
      have hp1_eq : p.1 = p.2 ^ 2 := by
        by_contra hneq
        rw [if_neg hneq] at htp
        exact hne htp
      refine Finset.mem_image.mpr ⟨p.2, Finset.mem_Icc.mpr (abs_le.mp hb_bound), by ext <;> simp [hp1_eq]⟩
    rw [← Finset.sum_filter]
    have hsum_filter :
        ∑ p ∈ (jacobiTriplePartial M).coeff.support.filter (fun p => p.1 + p.2 = ((2 * N : ℕ) : ℤ)),
          p.2 * ((jacobiTriplePartial M).coeff p * (((-1 : ℤˣ) ^ p.2 : ℤˣ) : ℤ)) =
        ∑ p ∈ (jacobiTriplePartial M).coeff.support.filter (fun p => p.1 + p.2 = ((2 * N : ℕ) : ℤ)),
          (if p.1 + p.2 = ((2 * N : ℕ) : ℤ) then
            p.2 * ((jacobiTriplePartial M).coeff p * (((-1 : ℤˣ) ^ p.2 : ℤˣ) : ℤ)) else 0) :=
      Finset.sum_congr rfl fun p hp => (if_pos (Finset.mem_filter.mp hp).2).symm
    rw [hsum_filter, Finset.sum_subset hsub]
    · rw [Finset.sum_image]
      · refine Finset.sum_congr rfl fun b hb => ?_
        have hb' := Finset.mem_Icc.mp hb
        by_cases hcond : b ^ 2 + b = ((2 * N : ℕ) : ℤ)
        · have hb2_le : b ^ 2 ≤ 4 * (N : ℤ) + 1 := by omega
          have htp := jacobi_triple_product_coeff (b ^ 2).toNat b (M := M) (by dsimp [M]; omega)
          have htoNat : (((b ^ 2).toNat : ℕ) : ℤ) = b ^ 2 := Int.toNat_of_nonneg (sq_nonneg b)
          rw [htoNat, if_pos rfl] at htp
          rw [if_pos hcond, if_pos hcond, htp, one_mul, negOneUnit_zpow]
        · rw [if_neg hcond, if_neg hcond]
      · intro x _ y _ hxy; exact congrArg Prod.snd hxy
    · intro p hp hnot
      rcases Finset.mem_image.mp hp with ⟨b, _, rfl⟩
      by_cases hcond : b ^ 2 + b = ((2 * N : ℕ) : ℤ)
      · have h0 : (jacobiTriplePartial M).coeff (b ^ 2, b) = 0 := by
          by_contra hne
          exact hnot (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, hcond⟩)
        rw [if_pos hcond, h0, zero_mul, mul_zero]
      · rw [if_neg hcond]
  rw [hsum_eq]
  split_ifs with h
  · let k₀ := Classical.choose h
    have hk₀ : N = k₀ * (k₀ + 1) / 2 := Classical.choose_spec h
    have hev : 2 ∣ k₀ * (k₀ + 1) := (Nat.even_mul_succ_self k₀).two_dvd
    have h2N : ((2 * N : ℕ) : ℤ) = (k₀ : ℤ) ^ 2 + (k₀ : ℤ) := by
      have hmul : 2 * N = k₀ * (k₀ + 1) := by omega
      have hcast : ((2 * N : ℕ) : ℤ) = ((k₀ * (k₀ + 1) : ℕ) : ℤ) := congrArg Nat.cast hmul
      rw [hcast]; push_cast; ring
    have hpair : ({(k₀ : ℤ), -((k₀ : ℤ) + 1)} : Finset ℤ) ⊆
        Finset.Icc (-(2 * (N : ℤ) + 1)) (2 * (N : ℤ) + 1) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      simp only [Finset.mem_Icc]
      have h2N' : 2 * (N : ℤ) = (k₀ : ℤ) ^ 2 + (k₀ : ℤ) := by
        simpa [Nat.cast_mul] using h2N
      rcases hb with rfl | rfl <;> constructor <;> nlinarith
    rw [← Finset.sum_subset hpair]
    · rw [Finset.sum_pair (by omega)]
      have h1 : (k₀ : ℤ) ^ 2 + (k₀ : ℤ) = ((2 * N : ℕ) : ℤ) := h2N.symm
      have h2 : (-((k₀ : ℤ) + 1)) ^ 2 + (-((k₀ : ℤ) + 1)) = ((2 * N : ℕ) : ℤ) := by
        rw [h2N]; ring
      rw [if_pos h1, if_pos h2, Int.natAbs_natCast]
      have habs : (-((k₀ : ℤ) + 1)).natAbs = k₀ + 1 := by
        have : -((k₀ : ℤ) + 1) = -((k₀ + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [this, Int.natAbs_neg, Int.natAbs_natCast]
      rw [habs, pow_succ]
      ring
    · intro b _ hnot
      rw [if_neg]
      intro hb
      apply hnot
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have hfac : (b - (k₀ : ℤ)) * (b + ((k₀ : ℤ) + 1)) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with h0 | h0 <;> [left; right] <;> omega
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    intro hb
    apply h
    rcases le_or_gt 0 b with hb0 | hb0
    · refine ⟨b.natAbs, ?_⟩
      have hbe : b = (b.natAbs : ℤ) := by omega
      have hmul : b.natAbs * (b.natAbs + 1) = 2 * N := by
        have hcast : ((b.natAbs * (b.natAbs + 1) : ℕ) : ℤ) = ((2 * N : ℕ) : ℤ) := by
          rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, ← hbe]
          linarith
        exact Int.ofNat.inj hcast
      omega
    · refine ⟨(-b - 1).natAbs, ?_⟩
      have hbe : (-b - 1 : ℤ) = ((-b - 1).natAbs : ℤ) := by omega
      have hmul : (-b - 1).natAbs * ((-b - 1).natAbs + 1) = 2 * N := by
        have hcast : (((-b - 1).natAbs * ((-b - 1).natAbs + 1) : ℕ) : ℤ) = ((2 * N : ℕ) : ℤ) := by
          rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, ← hbe]
          linarith
        exact Int.ofNat.inj hcast
      omega

/-- Direct triangular coefficient evaluation of `eulerPhiSeries ^ 3`. -/
theorem coeff_eulerPhiSeries_cube_triangular (k : ℕ) :
    PowerSeries.coeff (k * (k + 1) / 2) (eulerPhiSeries ^ 3) =
      (-1 : ℤ) ^ k * (2 * (k : ℤ) + 1) := by
  rw [jacobi_cube_identity]
  have hex : ∃ j : ℕ, k * (k + 1) / 2 = j * (j + 1) / 2 := ⟨k, rfl⟩
  rw [dif_pos hex]
  have hchoose : Classical.choose hex = k :=
    triangular_injective (Classical.choose_spec hex).symm
  rw [hchoose]

/-- Direct vanishing of `eulerPhiSeries ^ 3` at non-triangular indices. -/
theorem coeff_eulerPhiSeries_cube_of_not_triangular {N : ℕ}
    (h : ∀ k : ℕ, N ≠ k * (k + 1) / 2) :
    PowerSeries.coeff N (eulerPhiSeries ^ 3) = 0 := by
  rw [jacobi_cube_identity, dif_neg]
  rintro ⟨k, hk⟩
  exact h k hk

end PentagonalRecurrenceAndCube

/-! ## Section 4: Unconditional Ramanujan Partition Congruences `5 ∣ p(5n + 4)` & `7 ∣ p(7n + 5)` -/

section RamanujanPartitionCongruences

/-- Frobenius identity in `PowerSeries (ZMod p)` for any prime `p`:
`f ^ p = PowerSeries.expand p hp.ne_zero f`. -/
private lemma powerSeries_zmod_pow_prime {p : ℕ} (hp : p.Prime) (f : PowerSeries (ZMod p)) :
    f ^ p = PowerSeries.expand p hp.ne_zero f := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (PowerSeries (ZMod p)) p :=
    ⟨fun n => by
      rw [← map_natCast PowerSeries.C, ← map_zero PowerSeries.C, PowerSeries.C_injective.eq_iff,
        CharP.cast_eq_zero_iff (ZMod p) p]⟩
  have hsum_pow : ∀ (s : Finset ℕ) (h : ℕ → PowerSeries (ZMod p)),
      (∑ i ∈ s, h i) ^ p = ∑ i ∈ s, h i ^ p := by
    intro s h
    classical
    induction s using Finset.induction_on with
    | empty => simp [zero_pow hp.ne_zero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_pow_char, ih]
  exact PowerSeries.ext fun N => by
    let g : PowerSeries (ZMod p) := PowerSeries.mk fun k => PowerSeries.coeff (k + (N + 1)) f
    have hsplit : f = (Polynomial.coeToPowerSeries.ringHom (PowerSeries.trunc (N + 1) f)) +
        PowerSeries.X ^ (N + 1) * g :=
      PowerSeries.ext fun m => by
        rw [map_add, coeff_coeToPowerSeries, PowerSeries.coeff_trunc, mul_comm, coeff_mul_X_pow_eq]
        by_cases hm : m < N + 1
        · rw [if_pos hm, if_neg (by omega), add_zero]
        · rw [if_neg hm, if_pos (by omega), zero_add]
          simp only [g, PowerSeries.coeff_mk]
          have hm' : m - (N + 1) + (N + 1) = m := by omega
          rw [hm']
    conv_lhs => rw [hsplit, add_pow_char, map_add, mul_pow, ← pow_mul]
    have htail : PowerSeries.coeff N (PowerSeries.X ^ ((N + 1) * p) * g ^ p) = 0 := by
      rw [mul_comm, coeff_mul_X_pow_eq, if_neg]
      have hp2 : 2 ≤ p := hp.two_le
      nlinarith
    rw [htail, add_zero]
    have htrunc_sum : Polynomial.coeToPowerSeries.ringHom (PowerSeries.trunc (N + 1) f) =
        ∑ i ∈ Finset.range (N + 1),
          PowerSeries.C (PowerSeries.coeff i f) * PowerSeries.X ^ i :=
      PowerSeries.ext fun m => by
        rw [coeff_coeToPowerSeries, PowerSeries.coeff_trunc, map_sum]
        by_cases hm : m < N + 1
        · rw [if_pos hm, Finset.sum_eq_single m]
          · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_pos rfl, mul_one]
          · intro i _ hne
            rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (Ne.symm hne), mul_zero]
          · intro hnot; exact (hnot (Finset.mem_range.mpr hm)).elim
        · rw [if_neg hm]
          symm
          refine Finset.sum_eq_zero fun i hi => ?_
          have hi' := Finset.mem_range.mp hi
          rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (by omega), mul_zero]
    rw [htrunc_sum, hsum_pow, map_sum, PowerSeries.coeff_expand]
    have hzmod_pow : ∀ a : ZMod p, a ^ p = a := by
      intro a
      rw [← ZMod.natCast_zmod_val a]
      induction a.val with
      | zero => simp [zero_pow hp.ne_zero]
      | succ n ih => rw [Nat.cast_succ, add_pow_char, one_pow, ih]
    have hterm : ∀ i ∈ Finset.range (N + 1),
        PowerSeries.coeff N ((PowerSeries.C (PowerSeries.coeff i f) * PowerSeries.X ^ i) ^ p) =
          if p * i = N then PowerSeries.coeff i f else 0 := by
      intro i _
      rw [mul_pow, ← map_pow, hzmod_pow, ← pow_mul, mul_comm i p,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      by_cases h : N = p * i
      · rw [if_pos h, if_pos h.symm, mul_one]
      · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
    rw [Finset.sum_congr rfl hterm]
    split_ifs with hdvd
    · rw [Finset.sum_eq_single (N / p)]
      · rw [if_pos (Nat.mul_div_cancel' hdvd)]
      · intro i _ hne
        rw [if_neg]
        intro heq
        apply hne
        have hp_pos : 0 < p := hp.pos
        have := congrArg (· / p) heq
        simpa [Nat.mul_div_cancel_left i hp_pos] using this
      · intro hnot
        exfalso
        exact hnot (Finset.mem_range.mpr (by
          have : N / p ≤ N := Nat.div_le_self N p
          omega))
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      intro heq
      exact hdvd ⟨i, heq.symm⟩

/-- Shared arithmetic-progression cancellation lemma for `P * expand p E`:
if `coeff 0 E = 1` and `coeff (p*n + r) (P * expand p E) = 0` for all `n`,
then `coeff (p*n + r) P = 0` for all `n`! -/
private lemma coeff_mod_eq_zero_of_mul_expand_eq_zero {R : Type*} [CommRing R]
    {P E : PowerSeries R} {p r : ℕ} (hp : p ≠ 0) (hr : r < p)
    (hE0 : PowerSeries.coeff 0 E = 1)
    (hzero : ∀ n : ℕ, PowerSeries.coeff (p * n + r) (P * PowerSeries.expand p hp E) = 0) :
    ∀ n : ℕ, PowerSeries.coeff (p * n + r) P = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := hzero n
    rw [PowerSeries.coeff_mul] at hn
    rw [Finset.sum_eq_single (p * n + r, 0)] at hn
    · simp only [PowerSeries.coeff_expand, dvd_zero, ↓reduceIte, Nat.zero_div, hE0, mul_one] at hn
      exact hn
    · intro x hx hne
      rw [PowerSeries.coeff_expand]
      split_ifs with hdvd
      · rcases hdvd with ⟨k, hk⟩
        have hsum := Finset.mem_antidiagonal.mp hx
        have hk0 : k ≠ 0 := by
          intro h0; subst h0
          apply hne
          ext
          · dsimp; omega
          · dsimp; omega
        have hkn : k ≤ n := by
          by_contra hgt; push Not at hgt
          have h1 : p * (n + 1) ≤ p * k := Nat.mul_le_mul_left p hgt
          have h2 : p * (n + 1) = p * n + p := by ring
          omega
        have hx1 : x.1 = p * (n - k) + r := by
          have h1 : p * (n - k) + p * k = p * n := by
            rw [← Nat.mul_add, Nat.sub_add_cancel hkn]
          omega
        rw [hx1, ih (n - k) (by omega), zero_mul]
      · rw [mul_zero]
    · intro hnot
      exfalso
      exact hnot (Finset.mem_antidiagonal.mpr (add_zero _))

/-- Modular residue constraint for Euler's pentagonal series mod 5:
if `coeff a eulerPhiSeries` is nonzero mod 5, then `a % 5 ∈ {0, 1, 2}`! -/
private lemma pentagonal_mod_five {a : ℕ}
    (h : ((PowerSeries.coeff a eulerPhiSeries : ℤ) : ZMod 5) ≠ 0) :
    a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 := by
  have hex : ∃ k : ℤ, (a : ℤ) = k * (3 * k - 1) / 2 := by
    by_contra hnot
    push Not at hnot
    have h0 := coeff_eulerPhiSeries_of_not_pentagonal hnot
    rw [h0, Int.cast_zero] at h
    exact h rfl
  rcases hex with ⟨k, hk⟩
  have h2z := two_dvd_pentagonal k
  have h2a : 2 * (a : ℤ) = k * (3 * k - 1) := by omega
  have hmod : (2 * (a : ℤ)) % 5 = (k * (3 * k - 1)) % 5 := congrArg (· % 5) h2a
  have hkm : (k * (3 * k - 1)) % 5 = ((k % 5) * (3 * (k % 5) - 1)) % 5 := by
    have hk_div : k = 5 * (k / 5) + k % 5 := (Int.mul_ediv_add_emod k 5).symm
    have hdiff : k * (3 * k - 1) - (k % 5) * (3 * (k % 5) - 1) =
        5 * ((k / 5) * (3 * k + 3 * (k % 5) - 1)) := by
      have : k - k % 5 = 5 * (k / 5) := by omega
      calc k * (3 * k - 1) - (k % 5) * (3 * (k % 5) - 1)
          = (k - k % 5) * (3 * k + 3 * (k % 5) - 1) := by ring
        _ = 5 * ((k / 5) * (3 * k + 3 * (k % 5) - 1)) := by rw [this]; ring
    omega
  rw [hkm] at hmod
  have hk_lt : k % 5 < 5 := Int.emod_lt_of_pos k (by decide)
  have hk_nn : 0 ≤ k % 5 := Int.emod_nonneg k (by decide)
  have ha_lt : a % 5 < 5 := Nat.mod_lt a (by decide)
  have ha_cast : (2 * (a : ℤ)) % 5 = (2 * ((a % 5 : ℕ) : ℤ)) % 5 := by omega
  rw [ha_cast] at hmod
  interval_cases (k % 5) <;> interval_cases (a % 5) <;> omega

/-- Modular residue constraint for Jacobi's cube series mod 5:
if `coeff b (eulerPhiSeries^3)` is nonzero mod 5, then `b % 5 ∈ {0, 1}`! -/
private lemma cube_mod_five {b : ℕ}
    (h : ((PowerSeries.coeff b (eulerPhiSeries ^ 3) : ℤ) : ZMod 5) ≠ 0) :
    b % 5 = 0 ∨ b % 5 = 1 := by
  have hex : ∃ k : ℕ, b = k * (k + 1) / 2 := by
    by_contra hnot
    push Not at hnot
    have h0 := coeff_eulerPhiSeries_cube_of_not_triangular hnot
    rw [h0, Int.cast_zero] at h
    exact h rfl
  rcases hex with ⟨k, rfl⟩
  rw [coeff_eulerPhiSeries_cube_triangular] at h
  have hnot5 : ¬ (5 ∣ 2 * k + 1) := by
    intro hdvd
    apply h
    have hcast : ((2 * (k : ℤ) + 1 : ℤ) : ZMod 5) = 0 := by
      have : ((2 * k + 1 : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff (2 * k + 1) 5).mpr hdvd
      simpa using this
    rw [Int.cast_mul, hcast, mul_zero]
  have hev : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
  have h2b : 2 * (k * (k + 1) / 2) = k * (k + 1) := Nat.mul_div_cancel' hev
  have hmod : (2 * (k * (k + 1) / 2)) % 5 = (k * (k + 1)) % 5 := congrArg (· % 5) h2b
  rw [Nat.mul_mod, Nat.mul_mod k (k + 1), Nat.add_mod k 1] at hmod
  have hk_lt : k % 5 < 5 := Nat.mod_lt k (by decide)
  have hb_lt : (k * (k + 1) / 2) % 5 < 5 := Nat.mod_lt _ (by decide)
  have hk_not2 : k % 5 ≠ 2 := by
    intro hk2
    apply hnot5
    omega
  interval_cases (k % 5) <;> interval_cases ((k * (k + 1) / 2) % 5) <;> omega

/-- Modular residue constraint for Jacobi's cube series mod 7:
if `coeff b (eulerPhiSeries^3)` is nonzero mod 7, then `b % 7 ∈ {0, 1, 3}`! -/
private lemma cube_mod_seven {b : ℕ}
    (h : ((PowerSeries.coeff b (eulerPhiSeries ^ 3) : ℤ) : ZMod 7) ≠ 0) :
    b % 7 = 0 ∨ b % 7 = 1 ∨ b % 7 = 3 := by
  have hex : ∃ k : ℕ, b = k * (k + 1) / 2 := by
    by_contra hnot
    push Not at hnot
    have h0 := coeff_eulerPhiSeries_cube_of_not_triangular hnot
    rw [h0, Int.cast_zero] at h
    exact h rfl
  rcases hex with ⟨k, rfl⟩
  rw [coeff_eulerPhiSeries_cube_triangular] at h
  have hnot7 : ¬ (7 ∣ 2 * k + 1) := by
    intro hdvd
    apply h
    have hcast : ((2 * (k : ℤ) + 1 : ℤ) : ZMod 7) = 0 := by
      have : ((2 * k + 1 : ℕ) : ZMod 7) = 0 := (ZMod.natCast_eq_zero_iff (2 * k + 1) 7).mpr hdvd
      simpa using this
    rw [Int.cast_mul, hcast, mul_zero]
  have hev : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
  have h2b : 2 * (k * (k + 1) / 2) = k * (k + 1) := Nat.mul_div_cancel' hev
  have hmod : (2 * (k * (k + 1) / 2)) % 7 = (k * (k + 1)) % 7 := congrArg (· % 7) h2b
  rw [Nat.mul_mod, Nat.mul_mod k (k + 1), Nat.add_mod k 1] at hmod
  have hk_lt : k % 7 < 7 := Nat.mod_lt k (by decide)
  have hb_lt : (k * (k + 1) / 2) % 7 < 7 := Nat.mod_lt _ (by decide)
  have hk_not3 : k % 7 ≠ 3 := by
    intro hk3
    apply hnot7
    omega
  interval_cases (k % 7) <;> interval_cases ((k * (k + 1) / 2) % 7) <;> omega

/-- **UNCONDITIONAL RAMANUJAN PARTITION CONGRUENCE MODULO `5` (`0` ASSUMPTIONS!)**:
for EVERY natural number `n : ℕ`,
$$5 \mid p(5n + 4).$$ -/
theorem ramanujan_partition_mod_5 (n : ℕ) : 5 ∣ partCount (5 * n + 4) := by
  let φ : ℤ →+* ZMod 5 := Int.castRingHom (ZMod 5)
  let P : PowerSeries (ZMod 5) := PowerSeries.map φ partSeries
  let E : PowerSeries (ZMod 5) := PowerSeries.map φ eulerPhiSeries
  have hPE : P * E = 1 := by
    dsimp only [P, E]
    rw [← map_mul, partSeries_mul_eulerPhi_eq_one, map_one]
  have hE5 : E ^ 5 = PowerSeries.expand 5 (by decide) E :=
    powerSeries_zmod_pow_prime (by decide : Nat.Prime 5) E
  have hprod : P * PowerSeries.expand 5 (by decide) E = E * E ^ 3 := by
    rw [← hE5]
    calc P * E ^ 5 = (P * E) * (E * E ^ 3) := by ring
      _ = E * E ^ 3 := by rw [hPE, one_mul]
  have hE0 : PowerSeries.coeff 0 E = 1 := by
    simp [E, PowerSeries.coeff_map, coeff_zero_eulerPhiSeries]
  have hzero : ∀ m : ℕ, PowerSeries.coeff (5 * m + 4) (P * PowerSeries.expand 5 (by decide) E) = 0 := by
    intro m
    rw [hprod, PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hsum := Finset.mem_antidiagonal.mp hx
    by_cases h1 : PowerSeries.coeff x.1 E = 0
    · rw [h1, zero_mul]
    · by_cases h2 : PowerSeries.coeff x.2 (E ^ 3) = 0
      · rw [h2, mul_zero]
      · exfalso
        have h1' : ((PowerSeries.coeff x.1 eulerPhiSeries : ℤ) : ZMod 5) ≠ 0 := by
          simpa [E, φ, PowerSeries.coeff_map] using h1
        have h2' : ((PowerSeries.coeff x.2 (eulerPhiSeries ^ 3) : ℤ) : ZMod 5) ≠ 0 := by
          have hpow : E ^ 3 = PowerSeries.map φ (eulerPhiSeries ^ 3) := by
            simp [E, map_pow]
          rw [hpow, PowerSeries.coeff_map] at h2
          simpa [φ] using h2
        have ha := pentagonal_mod_five h1'
        have hb := cube_mod_five h2'
        omega
  have hP0 := coeff_mod_eq_zero_of_mul_expand_eq_zero (p := 5) (r := 4)
    (by decide) (by decide) hE0 hzero n
  have hnat : ((partCount (5 * n + 4) : ℕ) : ZMod 5) = 0 := by
    simpa [P, φ, partSeries, PowerSeries.coeff_map] using hP0
  exact (ZMod.natCast_eq_zero_iff (partCount (5 * n + 4)) 5).mp hnat

/-- **UNCONDITIONAL RAMANUJAN PARTITION CONGRUENCE MODULO `7` (`0` ASSUMPTIONS!)**:
for EVERY natural number `n : ℕ`,
$$7 \mid p(7n + 5).$$ -/
theorem ramanujan_partition_mod_7 (n : ℕ) : 7 ∣ partCount (7 * n + 5) := by
  let φ : ℤ →+* ZMod 7 := Int.castRingHom (ZMod 7)
  let P : PowerSeries (ZMod 7) := PowerSeries.map φ partSeries
  let E : PowerSeries (ZMod 7) := PowerSeries.map φ eulerPhiSeries
  have hPE : P * E = 1 := by
    dsimp only [P, E]
    rw [← map_mul, partSeries_mul_eulerPhi_eq_one, map_one]
  have hE7 : E ^ 7 = PowerSeries.expand 7 (by decide) E :=
    powerSeries_zmod_pow_prime (by decide : Nat.Prime 7) E
  have hprod : P * PowerSeries.expand 7 (by decide) E = E ^ 3 * E ^ 3 := by
    rw [← hE7]
    calc P * E ^ 7 = (P * E) * (E ^ 3 * E ^ 3) := by ring
      _ = E ^ 3 * E ^ 3 := by rw [hPE, one_mul]
  have hE0 : PowerSeries.coeff 0 E = 1 := by
    simp [E, PowerSeries.coeff_map, coeff_zero_eulerPhiSeries]
  have hzero : ∀ m : ℕ, PowerSeries.coeff (7 * m + 5) (P * PowerSeries.expand 7 (by decide) E) = 0 := by
    intro m
    rw [hprod, PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hsum := Finset.mem_antidiagonal.mp hx
    by_cases h1 : PowerSeries.coeff x.1 (E ^ 3) = 0
    · rw [h1, zero_mul]
    · by_cases h2 : PowerSeries.coeff x.2 (E ^ 3) = 0
      · rw [h2, mul_zero]
      · exfalso
        have hpow : E ^ 3 = PowerSeries.map φ (eulerPhiSeries ^ 3) := by
          simp [E, map_pow]
        have h1' : ((PowerSeries.coeff x.1 (eulerPhiSeries ^ 3) : ℤ) : ZMod 7) ≠ 0 := by
          rw [hpow, PowerSeries.coeff_map] at h1
          simpa [φ] using h1
        have h2' : ((PowerSeries.coeff x.2 (eulerPhiSeries ^ 3) : ℤ) : ZMod 7) ≠ 0 := by
          rw [hpow, PowerSeries.coeff_map] at h2
          simpa [φ] using h2
        have ha := cube_mod_seven h1'
        have hb := cube_mod_seven h2'
        omega
  have hP0 := coeff_mod_eq_zero_of_mul_expand_eq_zero (p := 7) (r := 5)
    (by decide) (by decide) hE0 hzero n
  have hnat : ((partCount (7 * n + 5) : ℕ) : ZMod 7) = 0 := by
    simpa [P, φ, partSeries, PowerSeries.coeff_map] using hP0
  exact (ZMod.natCast_eq_zero_iff (partCount (7 * n + 5)) 7).mp hnat

end RamanujanPartitionCongruences

end

end RHDirect.Stage9PartitionPentagonal

