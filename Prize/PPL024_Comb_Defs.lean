import RHDirect.Stage8MertensTheorems
import RHDirect.Stage6EffectivePNT
import RHDirect.Stage2DirichletAP
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Prize.PPL024_Comb_Defs

Core definitions, prime-power factorization helpers, and elementary analytic number theory
lemmas supporting Thomas F. Bloom's combinatorial / Fourier proof of Zhi-Wei Sun's
prime-shifted unit fractions conjecture (PPL 024, `arXiv:2305.02689` & `arXiv:2112.03726`).

All theorems in this file are completely unconditional (0 `sorry`, 0 custom `axiom`s).
-/

noncomputable section

open Finset Filter Topology
open scoped BigOperators Classical

namespace Prize.PPL024

/-! ## Section 1: Core Definitions -/

/-- Rational reciprocal sum `R(A) = ∑_{n ∈ A} 1 / n`. -/
def recSum (A : Finset ℕ) : ℚ :=
  ∑ n ∈ A, (1 : ℚ) / (n : ℚ)

/-- Real reciprocal sum `R(A) = ∑_{n ∈ A} 1 / n`. -/
def recSumReal (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, (1 : ℝ) / (n : ℝ)

/-- Exact prime-power divisibility `q ∥ n`: `q` is a prime power, `q ∣ n`, and `gcd(q, n / q) = 1`. -/
def ppowDiv (q n : ℕ) : Prop :=
  IsPrimePow q ∧ q ∣ n ∧ Nat.Coprime q (n / q)

/-- Exact prime-power slice `A_q = {n ∈ A : q ∥ n}` (Bloom's `A_q`). -/
def exactSlice (A : Finset ℕ) (q : ℕ) : Finset ℕ :=
  A.filter (fun n => ppowDiv q n)

/-- Prime powers exactly dividing `n`: `{p^{v_p(n)} : p ∣ n}`. -/
def exactPrimePowers (n : ℕ) : Finset ℕ :=
  n.primeFactors.image (fun p => p ^ (n.factorization p))

/-- Set of all prime powers `q` with `A_q ≠ ∅` (Bloom's `𝒬_A`). -/
def ppowersInSet (A : Finset ℕ) : Finset ℕ :=
  A.biUnion exactPrimePowers

/-- Weighted reciprocal sum `R(A; q) = ∑_{n ∈ A_q} q / n` (Bloom's `R(A; q)`). -/
def recSumQ (A : Finset ℕ) (q : ℕ) : ℝ :=
  ∑ n ∈ exactSlice A q, (q : ℝ) / (n : ℝ)

/-- Number of distinct prime factors `ω(n)`. -/
def omega (n : ℕ) : ℕ :=
  n.primeFactors.card

/-- Lowest common multiple `[𝒫]` of a finite set of natural numbers. -/
def lcmSet (P : Finset ℕ) : ℕ :=
  P.lcm id

/-- `x : ℚ` is representable as a finite sum of distinct shifted-prime unit fractions `1 / (p - h)`
with `p` prime and `p > h`. -/
def ShiftedPrimeRepr (h : ℤ) (x : ℚ) : Prop :=
  ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ h < (p : ℤ)) ∧
    ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) - (h : ℚ)) = x

/-- Positive upper relative logarithmic density among primes:
`∃ δ > 0, ∀ N₀, ∃ N ≥ N₀, ∑_{p ∈ A ∩ [1, N]} 1 / p ≥ δ log log N`. -/
def HasPosUpperRelLogDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
    δ * Real.log (Real.log (N : ℝ)) ≤
      ∑ p ∈ (Finset.Icc 1 N).filter (fun n => n ∈ A), (1 : ℝ) / (p : ℝ)

/-! ## Section 2: Basic Reciprocal Sum Lemmas -/

lemma recSum_cast_real (A : Finset ℕ) : (recSum A : ℝ) = recSumReal A := by
  unfold recSum recSumReal
  push_cast
  rfl

lemma recSumReal_nonneg (A : Finset ℕ) : 0 ≤ recSumReal A :=
  Finset.sum_nonneg fun n _ => by positivity

lemma recSumReal_empty : recSumReal ∅ = 0 := by
  simp [recSumReal]

lemma recSum_empty : recSum ∅ = 0 := by
  simp [recSum]

lemma recSumReal_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    recSumReal A ≤ recSumReal B :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB fun _ _ _ => by positivity

lemma recSumReal_union_disjoint {A B : Finset ℕ} (h : Disjoint A B) :
    recSumReal (A ∪ B) = recSumReal A + recSumReal B :=
  Finset.sum_union h

lemma recSum_union_disjoint {A B : Finset ℕ} (h : Disjoint A B) :
    recSum (A ∪ B) = recSum A + recSum B :=
  Finset.sum_union h

lemma recSumReal_sdiff {A B : Finset ℕ} (hBA : B ⊆ A) :
    recSumReal (A \ B) = recSumReal A - recSumReal B := by
  have h := recSumReal_union_disjoint (A := A \ B) (B := B) disjoint_sdiff_self_left
  rw [Finset.sdiff_union_of_subset hBA] at h
  linarith

lemma recSumReal_sdiff_ge (A B : Finset ℕ) :
    recSumReal A - recSumReal B ≤ recSumReal (A \ B) := by
  have h1 : A ⊆ (A \ B) ∪ B := by
    intro x hx
    by_cases hxb : x ∈ B
    · exact Finset.mem_union_right _ hxb
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxb⟩)
  have h2 := recSumReal_mono h1
  rw [recSumReal_union_disjoint disjoint_sdiff_self_left] at h2
  linarith

lemma recSumReal_union_le (A B : Finset ℕ) :
    recSumReal (A ∪ B) ≤ recSumReal A + recSumReal B := by
  have h : A ∪ B = A ∪ (B \ A) := (Finset.union_sdiff_self_eq_union).symm
  rw [h, recSumReal_union_disjoint disjoint_sdiff_self_right]
  linarith [recSumReal_mono (Finset.sdiff_subset (s := B) (t := A))]

lemma recSumReal_biUnion_le {ι : Type*} (s : Finset ι) (f : ι → Finset ℕ) :
    recSumReal (s.biUnion f) ≤ ∑ i ∈ s, recSumReal (f i) := by
  induction s using Finset.induction with
  | empty => simp [recSumReal]
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact (recSumReal_union_le _ _).trans (add_le_add le_rfl ih)

lemma recSumReal_le_card_div {A : Finset ℕ} {M : ℝ} (hM : 0 < M)
    (hA : ∀ n ∈ A, M ≤ (n : ℝ)) :
    recSumReal A ≤ (A.card : ℝ) / M := by
  unfold recSumReal
  calc ∑ n ∈ A, (1 : ℝ) / (n : ℝ)
      ≤ ∑ _n ∈ A, (1 : ℝ) / M := by
        refine Finset.sum_le_sum fun n hn => ?_
        exact one_div_le_one_div_of_le hM (hA n hn)
    _ = (A.card : ℝ) / M := by simp [div_eq_mul_inv]

lemma recSumReal_pos_of_nonempty {A : Finset ℕ} (h0 : ∀ n ∈ A, 0 < n) (hne : A.Nonempty) :
    0 < recSumReal A := by
  obtain ⟨a, ha⟩ := hne
  have ha0 : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr (h0 a ha)
  have hle : (1 : ℝ) / (a : ℝ) ≤ recSumReal A :=
    Finset.single_le_sum (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)) (fun _ _ => by positivity) ha
  linarith [one_div_pos.mpr ha0]

lemma recSum_eq_zero_iff {A : Finset ℕ} (h0 : ∀ n ∈ A, 0 < n) :
    recSum A = 0 ↔ A = ∅ := by
  constructor
  · intro h
    by_contra hne
    have hne' : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    have hpos := recSumReal_pos_of_nonempty h0 hne'
    rw [← recSum_cast_real, h] at hpos
    simp at hpos
  · rintro rfl; simp [recSum]

/-! ## Section 3: Exact Prime-Power Divisibility & LCM Lemmas -/

lemma ppowDiv_iff_exists_primeFactor {q n : ℕ} (hn : n ≠ 0) :
    ppowDiv q n ↔ ∃ p ∈ n.primeFactors, q = p ^ (n.factorization p) := by
  constructor
  · rintro ⟨hq, hdvd, hcop⟩
    rw [isPrimePow_nat_iff] at hq
    obtain ⟨p, k, hp, hk, rfl⟩ := hq
    have hpn : p ∣ n := dvd_trans (dvd_pow_self p hk.ne') hdvd
    have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩
    refine ⟨p, hpmem, ?_⟩
    have hle : k ≤ n.factorization p := by
      have h1 := (Nat.factorization_le_iff_dvd (pow_ne_zero k hp.ne_zero) hn).mpr hdvd p
      simpa [hp.factorization_pow] using h1
    have hge : n.factorization p ≤ k := by
      by_contra hlt
      push Not at hlt
      have hpk1 : p ^ (k + 1) ∣ n :=
        (hp.pow_dvd_iff_le_factorization hn).mpr hlt
      obtain ⟨m, hm⟩ := hpk1
      have hdiv : n / p ^ k = p * m := by
        have h1 : n = p ^ k * (p * m) := by
          rw [hm, pow_succ]; ring
        rw [h1, Nat.mul_div_cancel_left _ (pow_pos hp.pos k)]
      have hpdvd1 : p ∣ p ^ k := dvd_pow_self p hk.ne'
      have hpdvd2 : p ∣ n / p ^ k := by rw [hdiv]; exact dvd_mul_right p m
      have hp1 : p ∣ 1 := by
        rw [← hcop.gcd_eq_one]
        exact Nat.dvd_gcd hpdvd1 hpdvd2
      exact hp.not_dvd_one hp1
    exact congrArg (p ^ ·) (le_antisymm hle hge)
  · rintro ⟨p, hpmem, rfl⟩
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hne0 : n.factorization p ≠ 0 := by
      exact (Finsupp.mem_support_iff.mp (by simpa [Nat.support_factorization] using hpmem))
    have hk : 0 < n.factorization p := Nat.pos_of_ne_zero hne0
    refine ⟨hp.isPrimePow.pow hk.ne', Nat.ordProj_dvd n p, ?_⟩
    have hndvd : ¬ p ∣ n / p ^ (n.factorization p) := Nat.not_dvd_ordCompl hp hn
    exact (hp.coprime_iff_not_dvd.mpr hndvd).pow_left _

lemma ppowDiv_iff_mem_exactPrimePowers {q n : ℕ} (hn : n ≠ 0) :
    ppowDiv q n ↔ q ∈ exactPrimePowers n := by
  rw [ppowDiv_iff_exists_primeFactor hn, exactPrimePowers, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩

lemma ppowDiv_pos {q n : ℕ} (h : ppowDiv q n) : 0 < q :=
  h.1.pos

lemma ppowDiv_two_le {q n : ℕ} (h : ppowDiv q n) : 2 ≤ q :=
  h.1.two_le

lemma ppowDiv_le {q n : ℕ} (hn : 0 < n) (h : ppowDiv q n) : q ≤ n :=
  Nat.le_of_dvd hn h.2.1

lemma exactPrimePowers_injOn (n : ℕ) :
    Set.InjOn (fun p => p ^ (n.factorization p)) (n.primeFactors : Set ℕ) := by
  intro p₁ hp₁ p₂ hp₂ heq
  dsimp only at heq
  have hp1_mem : p₁ ∈ n.primeFactors := hp₁
  have hp2_mem : p₂ ∈ n.primeFactors := hp₂
  have h1 : p₁.Prime := Nat.prime_of_mem_primeFactors hp1_mem
  have h2 : p₂.Prime := Nat.prime_of_mem_primeFactors hp2_mem
  have hk1 : n.factorization p₁ ≠ 0 :=
    Finsupp.mem_support_iff.mp (Nat.support_factorization n ▸ hp1_mem)
  have hdvd : p₁ ∣ p₂ ^ (n.factorization p₂) := by
    rw [← heq]; exact dvd_pow_self p₁ hk1
  have hp12 : p₁ ∣ p₂ := h1.dvd_of_dvd_pow hdvd
  exact (h2.dvd_iff_eq h1.ne_one).mp hp12 |>.symm

lemma card_exactPrimePowers (n : ℕ) : (exactPrimePowers n).card = omega n := by
  unfold exactPrimePowers omega
  exact Finset.card_image_of_injOn (exactPrimePowers_injOn n)

lemma prod_exactPrimePowers {n : ℕ} (hn : n ≠ 0) :
    ∏ q ∈ exactPrimePowers n, q = n := by
  unfold exactPrimePowers
  rw [Finset.prod_image (fun p₁ hp₁ p₂ hp₂ heq => exactPrimePowers_injOn n hp₁ hp₂ heq)]
  have h := Nat.prod_factorization_pow_eq_self hn
  rw [Finsupp.prod, Nat.support_factorization] at h
  exact h

lemma mem_ppowersInSet_iff {A : Finset ℕ} (h0 : 0 ∉ A) {q : ℕ} :
    q ∈ ppowersInSet A ↔ (exactSlice A q).Nonempty := by
  unfold ppowersInSet exactSlice
  simp only [Finset.mem_biUnion, Finset.Nonempty, Finset.mem_filter]
  constructor
  · rintro ⟨n, hn, hq⟩
    have hn0 : n ≠ 0 := fun h => h0 (h ▸ hn)
    exact ⟨n, hn, (ppowDiv_iff_mem_exactPrimePowers hn0).mpr hq⟩
  · rintro ⟨n, hn, hq⟩
    have hn0 : n ≠ 0 := fun h => h0 (h ▸ hn)
    exact ⟨n, hn, (ppowDiv_iff_mem_exactPrimePowers hn0).mp hq⟩

lemma mem_ppowersInSet_isPrimePow {A : Finset ℕ} (h0 : 0 ∉ A) {q : ℕ}
    (hq : q ∈ ppowersInSet A) : IsPrimePow q := by
  obtain ⟨n, hn⟩ := (mem_ppowersInSet_iff h0).mp hq
  exact (Finset.mem_filter.mp hn).2.1

lemma mem_ppowersInSet_pos {A : Finset ℕ} (h0 : 0 ∉ A) {q : ℕ}
    (hq : q ∈ ppowersInSet A) : 0 < q :=
  (mem_ppowersInSet_isPrimePow h0 hq).pos

lemma ppowersInSet_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    ppowersInSet A ⊆ ppowersInSet B :=
  Finset.biUnion_subset_biUnion_of_subset_left _ hAB

lemma ppowersInSet_subset_Icc {A : Finset ℕ} {N : ℕ}
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n ≤ N) :
    ppowersInSet A ⊆ Finset.Icc 1 N := by
  have h0 : 0 ∉ A := fun h => by linarith [(hA 0 h).1]
  intro q hq
  obtain ⟨n, hn⟩ := (mem_ppowersInSet_iff h0).mp hq
  obtain ⟨hnA, hqn⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_Icc.mpr ⟨hqn.1.pos, Nat.le_of_dvd (hA n hnA).1 hqn.2.1 |>.trans (hA n hnA).2⟩

lemma lcmSet_pos {P : Finset ℕ} (h0 : ∀ q ∈ P, 0 < q) : 0 < lcmSet P := by
  unfold lcmSet
  rw [Nat.pos_iff_ne_zero, Finset.lcm_ne_zero_iff]
  intro q hq
  exact (h0 q hq).ne'

lemma dvd_lcmSet {P : Finset ℕ} {q : ℕ} (hq : q ∈ P) : q ∣ lcmSet P :=
  Finset.dvd_lcm hq

lemma lcmSet_dvd {P : Finset ℕ} {m : ℕ} (h : ∀ q ∈ P, q ∣ m) : lcmSet P ∣ m :=
  Finset.lcm_dvd h

private lemma nat_prod_dvd_of_pairwise_coprime {s : Finset ℕ} {m : ℕ}
    (hcop : Set.Pairwise (s : Set ℕ) Nat.Coprime) (hdvd : ∀ q ∈ s, q ∣ m) :
    (∏ q ∈ s, q) ∣ m := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hcop_a : Nat.Coprime a (∏ q ∈ s, q) :=
      Nat.Coprime.prod_right fun q hq =>
        hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hq) (fun h => ha (h ▸ hq))
    have hs_cop : Set.Pairwise (s : Set ℕ) Nat.Coprime :=
      hcop.mono (Finset.coe_subset.mpr (Finset.subset_insert a s))
    exact hcop_a.mul_dvd_of_dvd_of_dvd (hdvd a (Finset.mem_insert_self a s))
      (ih hs_cop fun q hq => hdvd q (Finset.mem_insert_of_mem hq))

lemma lcmSet_ppowersInSet_eq {A : Finset ℕ} (h0 : 0 ∉ A) :
    lcmSet (ppowersInSet A) = A.lcm id := by
  apply Nat.dvd_antisymm
  · apply lcmSet_dvd
    intro q hq
    obtain ⟨n, hn⟩ := (mem_ppowersInSet_iff h0).mp hq
    obtain ⟨hnA, hqn⟩ := Finset.mem_filter.mp hn
    exact dvd_trans hqn.2.1 (Finset.dvd_lcm hnA)
  · apply Finset.lcm_dvd
    intro n hnA
    have hn0 : n ≠ 0 := fun h => h0 (h ▸ hnA)
    rw [← prod_exactPrimePowers hn0]
    have hcop : Set.Pairwise (exactPrimePowers n : Set ℕ) Nat.Coprime := by
      intro q₁ hq₁ q₂ hq₂ hne
      obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hq₁
      obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.mp hq₂
      have hp1 : p₁.Prime := Nat.prime_of_mem_primeFactors hp₁
      have hp2 : p₂.Prime := Nat.prime_of_mem_primeFactors hp₂
      have hpne : p₁ ≠ p₂ := fun h => hne (by subst h; rfl)
      exact ((Nat.coprime_primes hp1 hp2).mpr hpne).pow _ _
    exact nat_prod_dvd_of_pairwise_coprime hcop fun q hq =>
      dvd_lcmSet (Finset.mem_biUnion.mpr ⟨n, hnA, hq⟩)

lemma lcmSet_dvd_lcmSet_of_subset {D Q : Finset ℕ} (hDQ : D ⊆ Q) :
    lcmSet D ∣ lcmSet Q :=
  lcmSet_dvd fun _ hq => dvd_lcmSet (hDQ hq)

lemma lcmSet_le_prod {P : Finset ℕ} (h0 : ∀ q ∈ P, 0 < q) : lcmSet P ≤ ∏ q ∈ P, q := by
  induction P using Finset.induction with
  | empty => simp [lcmSet]
  | insert a s ha ih =>
    unfold lcmSet at *
    rw [Finset.lcm_insert, Finset.prod_insert ha]
    have ha0 : 0 < a := h0 a (Finset.mem_insert_self a s)
    have hs0 : ∀ q ∈ s, 0 < q := fun q hq => h0 q (Finset.mem_insert_of_mem hq)
    have hslcm0 : 0 < s.lcm id := lcmSet_pos hs0
    change Nat.lcm a (s.lcm id) ≤ a * ∏ q ∈ s, q
    calc Nat.lcm a (s.lcm id)
        ≤ a * s.lcm id := Nat.lcm_le_mul ha0 hslcm0
      _ ≤ a * ∏ q ∈ s, q := Nat.mul_le_mul_left a (ih hs0)

lemma lcmSet_div_le_prod_sdiff {Q D : Finset ℕ} (hDQ : D ⊆ Q) (h0 : ∀ q ∈ Q, 0 < q) :
    lcmSet Q / lcmSet D ≤ ∏ q ∈ Q \ D, q := by
  have hD0 : 0 < lcmSet D := lcmSet_pos fun q hq => h0 q (hDQ hq)
  have hS0 : ∀ q ∈ Q \ D, 0 < q := fun q hq => h0 q (Finset.mem_sdiff.mp hq).1
  have hmul : lcmSet Q ≤ lcmSet D * ∏ q ∈ Q \ D, q := by
    have hunion : D ∪ (Q \ D) = Q := Finset.union_sdiff_of_subset hDQ
    have hdvd : lcmSet Q ∣ lcmSet D * lcmSet (Q \ D) := by
      apply lcmSet_dvd
      intro q hq
      rw [← hunion, Finset.mem_union] at hq
      rcases hq with hqD | hqS
      · exact dvd_mul_of_dvd_left (dvd_lcmSet hqD) _
      · exact dvd_mul_of_dvd_right (dvd_lcmSet hqS) _
    have hpos : 0 < lcmSet D * lcmSet (Q \ D) :=
      Nat.mul_pos hD0 (lcmSet_pos hS0)
    calc lcmSet Q
        ≤ lcmSet D * lcmSet (Q \ D) := Nat.le_of_dvd hpos hdvd
      _ ≤ lcmSet D * ∏ q ∈ Q \ D, q := Nat.mul_le_mul_left _ (lcmSet_le_prod hS0)
  exact Nat.div_le_of_le_mul hmul

lemma recSumQ_nonneg (A : Finset ℕ) (q : ℕ) : 0 ≤ recSumQ A q :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma inv_mul_recSumQ_eq (A : Finset ℕ) {q : ℕ} (hq : q ≠ 0) :
    (1 / (q : ℝ)) * recSumQ A q = recSumReal (exactSlice A q) := by
  unfold recSumQ recSumReal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  field_simp [hq']

lemma recSumQ_mono {A B : Finset ℕ} (hAB : A ⊆ B) (q : ℕ) :
    recSumQ A q ≤ recSumQ B q := by
  unfold recSumQ exactSlice
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hAB)
    fun _ _ _ => by positivity

lemma recSumQ_sdiff_ge (A B : Finset ℕ) (q : ℕ) :
    recSumQ A q - recSumQ B q ≤ recSumQ (A \ B) q := by
  have hsub : exactSlice A q ⊆ exactSlice (A \ B) q ∪ exactSlice B q := by
    intro n hn
    simp only [exactSlice, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff] at hn ⊢
    by_cases hB : n ∈ B
    · exact Or.inr ⟨hB, hn.2⟩
    · exact Or.inl ⟨⟨hn.1, hB⟩, hn.2⟩
  have hdisj : Disjoint (exactSlice (A \ B) q) (exactSlice B q) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp h1).1).2 (Finset.mem_filter.mp h2).1
  unfold recSumQ
  have hle : ∑ n ∈ exactSlice A q, (q : ℝ) / (n : ℝ) ≤
      ∑ n ∈ exactSlice (A \ B) q ∪ exactSlice B q, (q : ℝ) / (n : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  rw [Finset.sum_union hdisj] at hle
  linarith

/-! ## Section 4: Elementary Harmonic, Mertens, Chebyshev & Divisor Bounds -/

/-- Harmonic number upper bound: `∑_{n=1}^N 1/n ≤ log N + 1` for all `N ≥ 1`. -/
lemma harmonic_le_log_add_one {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ≤ Real.log (N : ℝ) + 1 := by
  induction N with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp
    | succ k =>
      have hm1 : 1 ≤ k + 1 := by omega
      have hIcc : Finset.Icc 1 (k + 2) = insert (k + 2) (Finset.Icc 1 (k + 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp : k + 2 ∉ Finset.Icc 1 (k + 1))]
      have hih := ih hm1
      have hlog : (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ≤
          Real.log ((k + 2 : ℕ) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ) := by
        have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
        have hk2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
        rw [← Real.log_div hk2.ne' hk1.ne']
        have hstep := Real.one_sub_inv_le_log_of_pos (div_pos hk2 hk1)
        have heq : 1 - (((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ))⁻¹ =
            (1 : ℝ) / ((k + 2 : ℕ) : ℝ) := by
          push_cast; field_simp; ring
        linarith
      linarith

/-- Telescoping bound on `∑_{n=2}^N 1 / (n * (n - 1)) ≤ 1`. -/
lemma sum_inv_mul_pred_le_one (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 := by
  induction N with
  | zero => simp
  | succ m ih =>
    cases m with
    | zero => simp
    | succ k =>
      have hstep : ∀ M : ℕ, 1 ≤ M →
          ∑ n ∈ Finset.Icc 2 M, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) = 1 - 1 / (M : ℝ) := by
        intro M hM
        induction M with
        | zero => omega
        | succ r ihr =>
          cases r with
          | zero => simp
          | succ s =>
            have hIcc : Finset.Icc 2 (s + 2) = insert (s + 2) (Finset.Icc 2 (s + 1)) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hIcc, Finset.sum_insert (by simp : s + 2 ∉ Finset.Icc 2 (s + 1)), ihr (by omega)]
            rw [show ((s + 2 : ℕ) : ℝ) - 1 = ((s + 1 : ℕ) : ℝ) by push_cast; ring]
            have hs1 : ((s + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            have hs2 : ((s + 2 : ℕ) : ℝ) ≠ 0 := by positivity
            field_simp [hs1, hs2]
            push_cast
            ring
      rw [hstep (k + 2) (by omega)]
      have : (0 : ℝ) ≤ 1 / ((k + 2 : ℕ) : ℝ) := by positivity
      linarith

/-- Sum of reciprocals of non-prime prime powers `p^k` (`k ≥ 2`) up to `N` is at most `2`. -/
lemma sum_inv_nonprime_ppow_le (N : ℕ) :
    ∑ q ∈ (Finset.Icc 1 N).filter (fun q => IsPrimePow q ∧ ¬ q.Prime), (1 : ℝ) / (q : ℝ) ≤ 2 := by
  -- Every non-prime prime power `q ≤ N` is `p^k` with `p ≤ N` prime and `2 ≤ k ≤ N`.
  -- In fact `∑_{p ≤ N} ∑_{k=2}^{N} p^{-k} ≤ ∑_{p ≤ N} 1/(p(p-1)) ≤ 1`.
  have hsub : (Finset.Icc 1 N).filter (fun q => IsPrimePow q ∧ ¬ q.Prime) ⊆
      ((Finset.Icc 2 N).filter Nat.Prime).biUnion
        (fun p => (Finset.Icc 2 N).image (fun k => p ^ k)) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_biUnion, Finset.mem_image] at hq ⊢
    obtain ⟨⟨_, hqN⟩, hpp, hnp⟩ := hq
    rw [isPrimePow_nat_iff] at hpp
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk1 : k = 1 := by omega
      subst hk1
      simp at hnp
      exact hnp hp
    have hpN : p ≤ N := le_trans (Nat.le_self_pow hk.ne' p) hqN
    have hkN : k ≤ N := by
      calc k ≤ 2 ^ k := le_of_lt Nat.lt_two_pow_self
        _ ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
        _ ≤ N := hqN
    exact ⟨p, ⟨⟨hp.two_le, hpN⟩, hp⟩, k, ⟨hk2, hkN⟩, rfl⟩
  calc ∑ q ∈ (Finset.Icc 1 N).filter (fun q => IsPrimePow q ∧ ¬ q.Prime), (1 : ℝ) / (q : ℝ)
      ≤ ∑ q ∈ ((Finset.Icc 2 N).filter Nat.Prime).biUnion
            (fun p => (Finset.Icc 2 N).image (fun k => p ^ k)), (1 : ℝ) / (q : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
          ∑ q ∈ (Finset.Icc 2 N).image (fun k => p ^ k), (1 : ℝ) / (q : ℝ) :=
        recSumReal_biUnion_le _ _
    _ ≤ ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
          (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp' : p.Prime := (Finset.mem_filter.mp hp).2
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.two_le
        have hgeom : ∑ q ∈ (Finset.Icc 2 N).image (fun k => p ^ k), (1 : ℝ) / (q : ℝ) ≤
            ∑ k ∈ Finset.Icc 2 N, ((p : ℝ)⁻¹) ^ k := by
          calc ∑ q ∈ (Finset.Icc 2 N).image (fun k => p ^ k), (1 : ℝ) / (q : ℝ)
              ≤ ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / ((p ^ k : ℕ) : ℝ) :=
                Finset.sum_image_le_of_nonneg fun _ _ => by positivity
            _ = ∑ k ∈ Finset.Icc 2 N, ((p : ℝ)⁻¹) ^ k := by
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [Nat.cast_pow, one_div, inv_pow]
        refine hgeom.trans ?_
        have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
        have hr1 : (p : ℝ)⁻¹ < 1 := by
          rw [inv_lt_one_iff₀]; exact Or.inr (by linarith)
        have hsum_le : ∑ k ∈ Finset.Icc 2 N, ((p : ℝ)⁻¹) ^ k ≤
            ((p : ℝ)⁻¹) ^ 2 / (1 - (p : ℝ)⁻¹) := by
          have hsub_range : Finset.Icc 2 N ⊆ (Finset.range (N + 1)).image (· + 2) := by
            intro k hk
            simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range] at hk ⊢
            exact ⟨k - 2, by omega, by omega⟩
          calc ∑ k ∈ Finset.Icc 2 N, ((p : ℝ)⁻¹) ^ k
              ≤ ∑ k ∈ (Finset.range (N + 1)).image (· + 2), ((p : ℝ)⁻¹) ^ k :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub_range fun _ _ _ => by positivity
            _ = ∑ j ∈ Finset.range (N + 1), ((p : ℝ)⁻¹) ^ (j + 2) := by
                rw [Finset.sum_image (fun _ _ _ _ h => by omega)]
            _ = ((p : ℝ)⁻¹) ^ 2 * ∑ j ∈ Finset.range (N + 1), ((p : ℝ)⁻¹) ^ j := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun j _ => by rw [pow_add]; ring
            _ ≤ ((p : ℝ)⁻¹) ^ 2 * (1 / (1 - (p : ℝ)⁻¹)) := by
                gcongr
                rw [geom_sum_eq hr1.ne]
                have hden : 0 < 1 - (p : ℝ)⁻¹ := by linarith
                rw [show ((p : ℝ)⁻¹ ^ (N + 1) - 1) / ((p : ℝ)⁻¹ - 1) =
                    (1 - (p : ℝ)⁻¹ ^ (N + 1)) / (1 - (p : ℝ)⁻¹) by
                      rw [show (p : ℝ)⁻¹ - 1 = -(1 - (p : ℝ)⁻¹) by ring, div_neg, ← neg_div]
                      congr 1; ring]
                exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 (N + 1)]) hden.le
            _ = ((p : ℝ)⁻¹) ^ 2 / (1 - (p : ℝ)⁻¹) := by ring
        refine hsum_le.trans ?_
        have hp0 : (p : ℝ) ≠ 0 := by linarith
        have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
        have heq : ((p : ℝ)⁻¹) ^ 2 / (1 - (p : ℝ)⁻¹) = (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
          field_simp
        rw [heq]
    _ ≤ ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun n hn _ => by
          have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
          have : 0 < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
          positivity
    _ ≤ 1 := sum_inv_mul_pred_le_one N
    _ ≤ 2 := by norm_num

/-- **Mertens bound for prime powers**:
`∑_{q ≤ N, IsPrimePow q} 1/q ≤ log log N + C` for all `N ≥ 3`. -/
theorem sum_inv_ppow_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      ∑ q ∈ (Finset.Icc 1 N).filter IsPrimePow, (1 : ℝ) / (q : ℝ) ≤
        Real.log (Real.log (N : ℝ)) + C := by
  obtain ⟨C₂, hC₂, hM2⟩ := RHDirect.Stage8MertensTheorems.mertens_second_theorem
  refine ⟨|RHDirect.Stage8MertensTheorems.meisselMertensConst| + C₂ / Real.log 3 + 3,
    by positivity, fun N hN => ?_⟩
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsplit : (Finset.Icc 1 N).filter IsPrimePow =
      (Finset.Icc 1 N).filter Nat.Prime ∪
      (Finset.Icc 1 N).filter (fun q => IsPrimePow q ∧ ¬ q.Prime) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hq, hpp⟩
      by_cases hp : q.Prime
      · exact Or.inl ⟨hq, hp⟩
      · exact Or.inr ⟨hq, hpp, hp⟩
    · rintro (⟨hq, hp⟩ | ⟨hq, hpp, _⟩)
      · exact ⟨hq, hp.isPrimePow⟩
      · exact ⟨hq, hpp⟩
  have hdisj : Disjoint ((Finset.Icc 1 N).filter Nat.Prime)
      ((Finset.Icc 1 N).filter (fun q => IsPrimePow q ∧ ¬ q.Prime)) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    exact (Finset.mem_filter.mp h2).2.2 (Finset.mem_filter.mp h1).2
  rw [hsplit, Finset.sum_union hdisj]
  have hM := hM2 (N : ℝ) hN3
  rw [Nat.floor_natCast] at hM
  have hprimes : ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      Real.log (Real.log (N : ℝ)) + RHDirect.Stage8MertensTheorems.meisselMertensConst +
        C₂ / Real.log (N : ℝ) := by
    have h1 := (abs_le.mp hM).2
    have heq : ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / (p : ℝ) =
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹ := by
      simp [one_div]
    linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hdiv : C₂ / Real.log (N : ℝ) ≤ C₂ / Real.log 3 :=
    div_le_div_of_nonneg_left hC₂.le hlog3 (Real.log_le_log (by norm_num) hN3)
  have hhigh := sum_inv_nonprime_ppow_le N
  have habs : RHDirect.Stage8MertensTheorems.meisselMertensConst ≤
      |RHDirect.Stage8MertensTheorems.meisselMertensConst| := le_abs_self _
  linarith

/-- **Chebyshev LCM bound for prime powers**:
There is an absolute constant `C > 0` such that for any `X ≥ 2` and any finite set `P` of
prime powers `q ≤ X`, `[P] ≤ exp(C * X)`. -/
theorem lcmSet_ppow_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X → ∀ P : Finset ℕ,
      (∀ q ∈ P, IsPrimePow q ∧ (q : ℝ) ≤ X) →
      (lcmSet P : ℝ) ≤ Real.exp (C * X) := by
  obtain ⟨c, hc, C₀, hC₀, hpsi⟩ := RHDirect.Stage6EffectivePNT.effective_pnt_psi
  refine ⟨1 + C₀, by positivity, fun X hX P hP => ?_⟩
  -- For every prime power `q ∈ P`, `q ∣ lcm(Icc 1 ⌊X⌋₊)`.
  -- More directly: `log(lcmSet P) = ∑_{p ∈ (lcmSet P).primeFactors} v_p(lcmSet P) * log p`
  -- `≤ ∑_{n ∈ Ioc 0 ⌊X⌋₊} Λ(n) = Chebyshev.psi X ≤ (1 + C₀) * X`!
  have hP0 : ∀ q ∈ P, 0 < q := fun q hq => (hP q hq).1.pos
  have hLpos : 0 < lcmSet P := lcmSet_pos hP0
  have hLne : lcmSet P ≠ 0 := hLpos.ne'
  rw [← Real.log_le_iff_le_exp (Nat.cast_pos.mpr hLpos)]
  -- Express `log(lcmSet P)` via its prime factorization
  have hlogL : Real.log (lcmSet P : ℝ) =
      ∑ p ∈ (lcmSet P).primeFactors, ((lcmSet P).factorization p : ℝ) * Real.log (p : ℝ) := by
    have hprod_eq : ∏ p ∈ (lcmSet P).primeFactors, p ^ ((lcmSet P).factorization p) = lcmSet P := by
      have h := Nat.prod_factorization_pow_eq_self hLne
      rw [Finsupp.prod, Nat.support_factorization] at h
      exact h
    conv_lhs => rw [← hprod_eq]
    rw [Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      exact Nat.cast_ne_zero.mpr (pow_ne_zero _ hp'.ne_zero)
  rw [hlogL]
  -- For each `p ∈ (lcmSet P).primeFactors`, `p ^ v_p(lcmSet P) ≤ ⌊X⌋₊`!
  have hpow_le : ∀ p ∈ (lcmSet P).primeFactors,
      p ^ ((lcmSet P).factorization p) ≤ ⌊X⌋₊ := by
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    set k := (lcmSet P).factorization p
    have hk : 0 < k := Nat.pos_of_ne_zero
      (Finsupp.mem_support_iff.mp (Nat.support_factorization _ ▸ hp))
    -- Some `q ∈ P` must be divisible by `p^k`, otherwise `lcmSet P` wouldn't be!
    have hex : ∃ q ∈ P, p ^ k ∣ q := by
      by_contra hnone
      push Not at hnone
      -- Every `q ∈ P` has `v_p(q) ≤ k - 1`, so `p^k` cannot divide `lcmSet P`!
      have hvp : ∀ q ∈ P, q.factorization p ≤ k - 1 := by
        intro q hq
        have hq0 : q ≠ 0 := (hP0 q hq).ne'
        have hlt : q.factorization p < k := by
          by_contra hge
          push Not at hge
          exact hnone q hq ((hp'.pow_dvd_iff_le_factorization hq0).mpr hge)
        omega
      -- Therefore `lcmSet P ∣ ∏_{r ∈ (lcmSet P).primeFactors} r ^ (if r = p then k - 1 else v_r(lcmSet P))`
      set M := (lcmSet P) / p
      have hpdvdL : p ∣ lcmSet P := Nat.dvd_of_mem_primeFactors hp
      have hM : p * M = lcmSet P := Nat.mul_div_cancel' hpdvdL
      have hdvdM : lcmSet P ∣ M := by
        apply lcmSet_dvd
        intro q hq
        have hq0 : q ≠ 0 := (hP0 q hq).ne'
        have hM0 : M ≠ 0 := fun h => hLne (by rw [← hM, h, mul_zero])
        rw [← Nat.factorization_le_iff_dvd hq0 hM0]
        intro r
        have hqL : q.factorization r ≤ (lcmSet P).factorization r :=
          (Nat.factorization_le_iff_dvd hq0 hLne).mpr (dvd_lcmSet hq) r
        have hMfac : (lcmSet P).factorization r = p.factorization r + M.factorization r := by
          rw [← hM, Nat.factorization_mul hp'.ne_zero hM0, Finsupp.add_apply]
        by_cases hrp : r = p
        · subst hrp
          rw [hp'.factorization_self] at hMfac
          have := hvp q hq
          omega
        · have : p.factorization r = 0 := by
            rw [Nat.Prime.factorization hp', Finsupp.single_eq_of_ne hrp]
          omega
      have hle : lcmSet P ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero fun h =>
        hLne (by rw [← hM, h, mul_zero])) hdvdM
      have hlt : M < lcmSet P := by
        have hMpos : 0 < M := Nat.pos_of_ne_zero fun h => hLne (by rw [← hM, h, mul_zero])
        calc M = 1 * M := (one_mul M).symm
          _ < p * M := Nat.mul_lt_mul_of_pos_right hp'.one_lt hMpos
          _ = lcmSet P := hM
      omega
    obtain ⟨q, hqP, hpkq⟩ := hex
    have hqle : q ≤ ⌊X⌋₊ := Nat.le_floor (hP q hqP).2
    exact le_trans (Nat.le_of_dvd (hP0 q hqP) hpkq) hqle
  -- Now bound `∑_{p ∈ (lcmSet P).primeFactors} v_p(lcmSet P) * log p ≤ Chebyshev.psi X`!
  have hle_psi : ∑ p ∈ (lcmSet P).primeFactors,
        ((lcmSet P).factorization p : ℝ) * Real.log (p : ℝ) ≤ Chebyshev.psi X := by
    -- Each `(p, j)` with `1 ≤ j ≤ v_p(lcmSet P)` gives a distinct prime power `p^j ∈ Ioc 0 ⌊X⌋₊`
    -- with `Λ(p^j) = log p`!
    unfold Chebyshev.psi
    set S := (lcmSet P).primeFactors.biUnion (fun p =>
      (Finset.Icc 1 ((lcmSet P).factorization p)).image (fun j => p ^ j))
    have hSsub : S ⊆ Finset.Ioc 0 ⌊X⌋₊ := by
      intro m hm
      simp only [S, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Icc] at hm
      obtain ⟨p, hp, j, ⟨hj1, hjk⟩, rfl⟩ := hm
      have hp' := Nat.prime_of_mem_primeFactors hp
      exact Finset.mem_Ioc.mpr ⟨pow_pos hp'.pos j,
        (Nat.pow_le_pow_right hp'.pos hjk).trans (hpow_le p hp)⟩
    have hdisj : Set.PairwiseDisjoint ((lcmSet P).primeFactors : Set ℕ)
        (fun p => (Finset.Icc 1 ((lcmSet P).factorization p)).image (fun j => p ^ j)) := by
      intro p₁ hp₁ p₂ hp₂ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro m hm1 hm2
      obtain ⟨j₁, hj₁, rfl⟩ := Finset.mem_image.mp hm1
      obtain ⟨j₂, hj₂, heq⟩ := Finset.mem_image.mp hm2
      have hp1 := Nat.prime_of_mem_primeFactors hp₁
      have hp2 := Nat.prime_of_mem_primeFactors hp₂
      have hdvd : p₁ ∣ p₂ ^ j₂ := by
        rw [heq]; exact dvd_pow_self p₁ (by have := (Finset.mem_Icc.mp hj₁).1; omega)
      exact hne ((hp2.dvd_iff_eq hp1.ne_one).mp (hp1.dvd_of_dvd_pow hdvd)).symm
    have hsumS : ∑ m ∈ S, ArithmeticFunction.vonMangoldt m =
        ∑ p ∈ (lcmSet P).primeFactors,
          ((lcmSet P).factorization p : ℝ) * Real.log (p : ℝ) := by
      rw [Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := Nat.prime_of_mem_primeFactors hp
      rw [Finset.sum_image]
      · calc ∑ j ∈ Finset.Icc 1 ((lcmSet P).factorization p),
              ArithmeticFunction.vonMangoldt (p ^ j)
            = ∑ _j ∈ Finset.Icc 1 ((lcmSet P).factorization p), Real.log (p : ℝ) := by
              refine Finset.sum_congr rfl fun j hj => ?_
              have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
              rw [ArithmeticFunction.vonMangoldt_apply_pow hj0,
                ArithmeticFunction.vonMangoldt_apply_prime hp']
          _ = ((lcmSet P).factorization p : ℝ) * Real.log (p : ℝ) := by
              simp [Nat.card_Icc]
      · intro j₁ _ j₂ _ heq
        exact Nat.pow_right_injective hp'.two_le heq
    rw [← hsumS]
    exact Finset.sum_le_sum_of_subset_of_nonneg hSsub fun _ _ _ =>
      ArithmeticFunction.vonMangoldt_nonneg
  have hpsi_bd := (abs_le.mp (hpsi X hX)).2
  have hexp1 : Real.exp (-c * Real.sqrt (Real.log X)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have := Real.sqrt_nonneg (Real.log X)
    nlinarith
  have hC0X : C₀ * X * Real.exp (-c * Real.sqrt (Real.log X)) ≤ C₀ * X := by
    have : 0 ≤ C₀ * X := by positivity
    nlinarith
  linarith

/-- **Elementary Divisor Bound** (`d(m) ≤ N^{(2 log 2 + ε) / log log N}` for `1 ≤ m ≤ N^2`):
proved cleanly via prime-threshold splitting at `L = log N / log log N`. -/
theorem divisor_bound_sq (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 1 ≤ m → m ≤ N ^ 2 →
      (m.divisors.card : ℝ) ≤ (N : ℝ) ^ ((2 * Real.log 2 + ε) / Real.log (Real.log (N : ℝ))) := by
  -- For any `L ≥ 2` and `1 ≤ m ≤ N^2`:
  -- `d(m) = ∏_{p ∣ m} (v_p(m) + 1) = (∏_{p ≤ L} (v_p(m) + 1)) * (∏_{p > L} (v_p(m) + 1))`.
  -- For `p ≤ L`: `v_p(m) + 1 ≤ 2 * log_2(N) + 1 ≤ 4 * log N` and there are `≤ L` primes `≤ L`.
  -- For `p > L`: `v_p(m) + 1 ≤ 2^{v_p(m)}`, and `L^{∑_{p > L} v_p(m)} ≤ m ≤ N^2`,
  -- so `∑_{p > L} v_p(m) ≤ 2 * log N / log L`, so `∏_{p > L} (v_p(m) + 1) ≤ exp(2 log 2 * log N / log L)`.
  -- Choose `L = ⌊(log N) / (log log N)^2⌋₊`!
  -- Then `log L = log log N - 2 log log log N + O(1)`, so `2 log 2 / log L ≤ (2 log 2 + ε/2) / log log N`,
  -- while `L * log(4 log N) ≤ (log N / (log log N)^2) * (2 log log N) = 2 log N / log log N` — wait!
  -- We need `L * log(4 log N) = o(log N / log log N)`, so pick `L = ⌊(log N) / (log log N)^3⌋₊`!!
  -- Check! With `L = ⌊(log N) / (log log N)^3⌋₊`:
  -- (a) `L * log(4 log N) ≤ (log N / (log log N)^3) * (2 log log N) = 2 log N / (log log N)^2 = o(log N / log log N)`!
  -- (b) `log L ≥ log log N - 3 log log log N - 1`, so `2 log 2 / log L ≤ (2 log 2 + ε/2) / log log N`!
  -- Sum of both exponents is `≤ (2 log 2 + ε) / log log N`!!
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Filter `N` sufficiently large for all asymptotic comparisons
  have hLL : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hL_ratio : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (Real.log (Real.log (N : ℝ))) ^ 3)
      atTop atTop := by
    -- `log N / (log log N)^3 = exp(u) / u^3` where `u = log log N → ∞`
    have hexp : Tendsto (fun u : ℝ => Real.exp u / u ^ 3) atTop atTop := by
      simpa using Real.tendsto_exp_div_pow_atTop 3
    have hcomp := hexp.comp hLL
    refine hcomp.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    simp only [Function.comp_apply, Real.exp_log hlogpos]
  have hlog_div : Tendsto (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ))) / Real.log (Real.log (N : ℝ)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
      simpa [Real.rpow_one] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h1.comp hLL
  have hinv_LL : Tendsto (fun N : ℕ => 1 / Real.log (Real.log (N : ℝ))) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp hLL).congr fun _ => by simp [one_div]
  filter_upwards [
    eventually_ge_atTop 16,
    hLL.eventually_ge_atTop (max 4 (16 / ε)),
    hL_ratio.eventually_ge_atTop 4,
    hlog_div.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / (100 * (2 * Real.log 2 + ε)))),
    hinv_LL.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / (100 * (2 * Real.log 2 + ε))))
  ] with N hN16 hLL_ge hLr_ge hld_lt hinv_lt
  intro m hm1 hmN2
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hLL_pos : 0 < Real.log (Real.log (N : ℝ)) := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) hLL_ge)
  set LL := Real.log (Real.log (N : ℝ))
  set Lreal := Real.log (N : ℝ) / LL ^ 3
  set L : ℕ := ⌊Lreal⌋₊
  have hLreal_ge4 : 4 ≤ Lreal := hLr_ge
  have hL_ge4 : 4 ≤ L := Nat.le_floor hLreal_ge4
  have hL_le : (L : ℝ) ≤ Lreal := Nat.floor_le (by linarith)
  have hL_ge_half : Lreal / 2 ≤ (L : ℝ) := by
    have hlt := Nat.lt_floor_add_one Lreal
    linarith
  have hL_pos : (0 : ℝ) < (L : ℝ) := by positivity
  -- Take logs: we want `log(d(m)) ≤ ((2 log 2 + ε) / LL) * log N`
  have hdpos : (0 : ℝ) < (m.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  rw [Real.rpow_def_of_pos hN_pos, ← Real.log_le_iff_le_exp hdpos]
  -- Formula `m.divisors.card = ∏ p ∈ m.primeFactors, (m.factorization p + 1)`
  have hcard : m.divisors.card = ∏ p ∈ m.primeFactors, (m.factorization p + 1) :=
    Nat.card_divisors (by omega : m ≠ 0)
  rw [hcard, Nat.cast_prod, Real.log_prod]
  swap
  · intro p _; positivity
  -- Split `m.primeFactors` into `p ≤ L` and `p > L`
  have hsplit : ∑ p ∈ m.primeFactors, Real.log ((m.factorization p + 1 : ℕ) : ℝ) =
      (∑ p ∈ m.primeFactors.filter (· ≤ L), Real.log ((m.factorization p + 1 : ℕ) : ℝ)) +
      (∑ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ L), Real.log ((m.factorization p + 1 : ℕ) : ℝ)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  -- Part 1: `p ≤ L`
  have hpart1 : ∑ p ∈ m.primeFactors.filter (· ≤ L), Real.log ((m.factorization p + 1 : ℕ) : ℝ) ≤
      (ε / 2) * Real.log (N : ℝ) / LL := by
    -- Each `p ≤ L` has `2 ^ (v_p(m)) ≤ p ^ (v_p(m)) ≤ m ≤ N^2`, so `v_p(m) ≤ 2 * log N / log 2 ≤ 3 * log N`
    have hterm : ∀ p ∈ m.primeFactors.filter (· ≤ L),
        Real.log ((m.factorization p + 1 : ℕ) : ℝ) ≤ 2 * LL := by
      intro p hp
      have hp' := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
      have hpow : (2 : ℝ) ^ (m.factorization p) ≤ (N : ℝ) ^ 2 := by
        have h1 : 2 ^ (m.factorization p) ≤ p ^ (m.factorization p) :=
          Nat.pow_le_pow_left hp'.two_le _
        have h2 : p ^ (m.factorization p) ≤ m :=
          Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)
        exact_mod_cast le_trans (le_trans h1 h2) hmN2
      have hv_le : (m.factorization p : ℝ) ≤ 2 * Real.log (N : ℝ) / Real.log 2 := by
        have hlogp : Real.log ((2 : ℝ) ^ (m.factorization p)) ≤ Real.log ((N : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) hpow
        rw [Real.log_pow, Real.log_pow] at hlogp
        push_cast at hlogp
        rw [le_div_iff₀ hlog2_pos]
        linarith
      have hlog2_ge : (1 : ℝ) / 2 ≤ Real.log 2 := by
        have h := Real.log_two_gt_d9
        linarith
      have hvp1 : ((m.factorization p + 1 : ℕ) : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := by
        have hv4 : (m.factorization p : ℝ) ≤ 4 * Real.log (N : ℝ) := by
          have : 2 * Real.log (N : ℝ) / Real.log 2 ≤ 4 * Real.log (N : ℝ) := by
            rw [div_le_iff₀ hlog2_pos]; nlinarith
          linarith
        have hlogN_ge : 5 ≤ Real.log (N : ℝ) := by
          have h4 : (4 : ℝ) ≤ LL := le_trans (le_max_left _ _) hLL_ge
          have hexp : Real.exp 4 ≤ Real.log (N : ℝ) := by
            rw [← Real.exp_log hlogN_pos]; exact Real.exp_le_exp.mpr h4
          have h1 : (5 : ℝ) ≤ Real.exp 4 := by
            have := Real.add_one_le_exp (4 : ℝ); linarith
          linarith
        push_cast
        nlinarith
      calc Real.log ((m.factorization p + 1 : ℕ) : ℝ)
          ≤ Real.log ((Real.log (N : ℝ)) ^ 2) := Real.log_le_log (by positivity) hvp1
        _ = 2 * LL := by rw [Real.log_pow]; simp [LL]
    have hcard_le : (m.primeFactors.filter (· ≤ L)).card ≤ L := by
      have hsub : m.primeFactors.filter (· ≤ L) ⊆ Finset.Icc 1 L := by
        intro p hp
        have hp' := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
        exact Finset.mem_Icc.mpr ⟨hp'.pos, (Finset.mem_filter.mp hp).2⟩
      exact (Finset.card_le_card hsub).trans (by simp)
    calc ∑ p ∈ m.primeFactors.filter (· ≤ L), Real.log ((m.factorization p + 1 : ℕ) : ℝ)
        ≤ ∑ _p ∈ m.primeFactors.filter (· ≤ L), (2 * LL) := Finset.sum_le_sum hterm
      _ = ((m.primeFactors.filter (· ≤ L)).card : ℝ) * (2 * LL) := by simp
      _ ≤ (L : ℝ) * (2 * LL) := by gcongr
      _ ≤ Lreal * (2 * LL) := by gcongr
      _ = 2 * Real.log (N : ℝ) / LL ^ 2 := by
          dsimp only [Lreal]; field_simp
      _ ≤ (ε / 2) * Real.log (N : ℝ) / LL := by
          have hLL_eps : 4 / ε ≤ LL := by
            have h16 := le_trans (le_max_right _ _) hLL_ge
            have h416 : 4 / ε ≤ 16 / ε := div_le_div_of_nonneg_right (by norm_num) hε.le
            linarith
          have h4 : 2 / LL ≤ ε / 2 := by
            rw [div_le_iff₀ hLL_pos]
            have := (div_le_iff₀ hε).mp hLL_eps
            linarith
          calc 2 * Real.log (N : ℝ) / LL ^ 2
              = (2 / LL) * (Real.log (N : ℝ) / LL) := by ring
            _ ≤ (ε / 2) * (Real.log (N : ℝ) / LL) := by
                gcongr
            _ = (ε / 2) * Real.log (N : ℝ) / LL := by ring
  -- Part 2: `p > L`
  have hpart2 : ∑ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ L),
        Real.log ((m.factorization p + 1 : ℕ) : ℝ) ≤
      (2 * Real.log 2 + ε / 2) * Real.log (N : ℝ) / LL := by
    -- For each `p > L`, `v_p(m) + 1 ≤ 2 ^ (v_p(m))`, so `log(v_p(m) + 1) ≤ v_p(m) * log 2`
    have hstep1 : ∑ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ L),
          Real.log ((m.factorization p + 1 : ℕ) : ℝ) ≤
        Real.log 2 * ∑ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ L), (m.factorization p : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p _ => ?_
      have hk : ((m.factorization p + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m.factorization p) := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := m.factorization p))
      calc Real.log ((m.factorization p + 1 : ℕ) : ℝ)
          ≤ Real.log ((2 : ℝ) ^ (m.factorization p)) := Real.log_le_log (by positivity) hk
        _ = Real.log 2 * (m.factorization p : ℝ) := by rw [Real.log_pow]; ring
    -- Bound `∑_{p > L} v_p(m) ≤ 2 * log N / log L` via `L^{∑ v_p(m)} ≤ ∏ p^{v_p(m)} ≤ m ≤ N^2`
    have hlogL_pos : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
    have hsum_v : (∑ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ L), (m.factorization p : ℝ)) *
        Real.log (L : ℝ) ≤ 2 * Real.log (N : ℝ) := by
      have hprod_le : ∏ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ L), (L : ℝ) ^ (m.factorization p) ≤
          (N : ℝ) ^ 2 := by
        have h1 : ∏ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ L), L ^ (m.factorization p) ≤
            ∏ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ L), p ^ (m.factorization p) := by
          refine Finset.prod_le_prod' fun p hp => ?_
          have hgt : L < p := Nat.lt_of_not_le (Finset.mem_filter.mp hp).2
          exact Nat.pow_le_pow_left hgt.le _
        have h2 : ∏ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ L), p ^ (m.factorization p) ≤
            ∏ p ∈ m.primeFactors, p ^ (m.factorization p) :=
          Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) fun p hp _ =>
            Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hp).pos
        have h3 : ∏ p ∈ m.primeFactors, p ^ (m.factorization p) = m := by
          have h := Nat.prod_factorization_pow_eq_self (by omega : m ≠ 0)
          rw [Finsupp.prod, Nat.support_factorization] at h
          exact h
        exact_mod_cast le_trans (le_trans h1 h2) (h3.symm ▸ hmN2)
      have hlogp : Real.log (∏ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ L), (L : ℝ) ^ (m.factorization p)) ≤
          Real.log ((N : ℝ) ^ 2) :=
        Real.log_le_log (Finset.prod_pos fun _ _ => pow_pos hL_pos _) hprod_le
      rw [Real.log_prod (fun _ _ => (pow_pos hL_pos _).ne'), Real.log_pow] at hlogp
      push_cast at hlogp
      have heq : ∑ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ L), Real.log ((L : ℝ) ^ (m.factorization p)) =
          (∑ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ L), (m.factorization p : ℝ)) * Real.log (L : ℝ) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => by rw [Real.log_pow]
      linarith
    -- Now compare `2 * log 2 / log L` with `(2 * log 2 + ε/2) / LL`
    have hlogL_ge : LL * (1 - 4 * (ε / (100 * (2 * Real.log 2 + ε)))) ≤ Real.log (L : ℝ) := by
      have h1 : Real.log (Lreal / 2) ≤ Real.log (L : ℝ) :=
        Real.log_le_log (by positivity) hL_ge_half
      have h2 : Real.log (Lreal / 2) = LL - 3 * Real.log LL - Real.log 2 := by
        dsimp only [Lreal]
        rw [Real.log_div (div_pos hlogN_pos (pow_pos hLL_pos 3)).ne' (by norm_num),
          Real.log_div hlogN_pos.ne' (pow_pos hLL_pos 3).ne', Real.log_pow]
        simp [LL]
      have hlog2_lt1 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
      have h3 : 3 * Real.log LL ≤ 3 * (ε / (100 * (2 * Real.log 2 + ε))) * LL := by
        have := (div_lt_iff₀ hLL_pos).mp hld_lt
        linarith
      have h4 : Real.log 2 ≤ (ε / (100 * (2 * Real.log 2 + ε))) * LL := by
        have := (div_lt_iff₀ hLL_pos).mp hinv_lt
        linarith
      linarith
    set η := ε / (100 * (2 * Real.log 2 + ε))
    have hη_pos : 0 < η := by positivity
    have hη_small : 4 * η ≤ 1 / 2 := by
      dsimp only [η]
      rw [show 4 * (ε / (100 * (2 * Real.log 2 + ε))) =
          (4 * ε) / (100 * (2 * Real.log 2 + ε)) by ring,
        div_le_iff₀ (by positivity)]
      nlinarith
    have hratio : 2 * Real.log 2 / Real.log (L : ℝ) ≤ (2 * Real.log 2 + ε / 2) / LL := by
      have hden_pos : 0 < LL * (1 - 4 * η) := mul_pos hLL_pos (by linarith)
      calc 2 * Real.log 2 / Real.log (L : ℝ)
          ≤ 2 * Real.log 2 / (LL * (1 - 4 * η)) :=
            div_le_div_of_nonneg_left (by positivity) hden_pos hlogL_ge
        _ ≤ (2 * Real.log 2 + ε / 2) / LL := by
            rw [div_le_div_iff₀ hden_pos hLL_pos]
            have hbound : 4 * η * (2 * Real.log 2 + ε / 2) ≤ ε / 2 := by
              dsimp only [η]
              have hpos : 0 < 100 * (2 * Real.log 2 + ε) := by positivity
              have : 4 * (ε / (100 * (2 * Real.log 2 + ε))) * (2 * Real.log 2 + ε / 2) ≤
                  4 * (ε / (100 * (2 * Real.log 2 + ε))) * (2 * Real.log 2 + ε) := by
                gcongr; linarith
              have hsimp : 4 * (ε / (100 * (2 * Real.log 2 + ε))) * (2 * Real.log 2 + ε) =
                  4 * ε / 100 := by
                field_simp
              linarith
            nlinarith
    have hsum_le : ∑ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ L), (m.factorization p : ℝ) ≤
        2 * Real.log (N : ℝ) / Real.log (L : ℝ) :=
      (le_div_iff₀ hlogL_pos).mpr hsum_v
    calc ∑ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ L), Real.log ((m.factorization p + 1 : ℕ) : ℝ)
        ≤ Real.log 2 * (2 * Real.log (N : ℝ) / Real.log (L : ℝ)) :=
          hstep1.trans (mul_le_mul_of_nonneg_left hsum_le hlog2_pos.le)
      _ = (2 * Real.log 2 / Real.log (L : ℝ)) * Real.log (N : ℝ) := by ring
      _ ≤ ((2 * Real.log 2 + ε / 2) / LL) * Real.log (N : ℝ) := by gcongr
      _ = (2 * Real.log 2 + ε / 2) * Real.log (N : ℝ) / LL := by ring
  calc (∑ p ∈ m.primeFactors.filter (· ≤ L), Real.log ((m.factorization p + 1 : ℕ) : ℝ)) +
        (∑ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ L), Real.log ((m.factorization p + 1 : ℕ) : ℝ))
      ≤ (ε / 2) * Real.log (N : ℝ) / LL + (2 * Real.log 2 + ε / 2) * Real.log (N : ℝ) / LL :=
        add_le_add hpart1 hpart2
    _ = Real.log (N : ℝ) * ((2 * Real.log 2 + ε) / LL) := by ring

/-- **Dyadic Partial Summation Bound** (no integrals required):
If `#{n ∈ [1, M] : P n} ≤ α * M / log M` for all `M ≥ N₀`, then for every `N ≥ max N₀ 3`:
`∑_{n ∈ [2, N], P n} 1/n ≤ (2 / log 2) * α * (log log N + 2) + N₀`. -/
theorem dyadic_recSum_of_count_bound (P : ℕ → Prop) {α : ℝ} (hα : 0 ≤ α) {N₀ : ℕ}
    (hN₀ : 2 ≤ N₀)
    (hcnt : ∀ M : ℕ, N₀ ≤ M → (((Finset.Icc 1 M).filter P).card : ℝ) ≤ α * (M : ℝ) / Real.log (M : ℝ)) :
    ∀ N : ℕ, max N₀ 3 ≤ N →
      ∑ n ∈ (Finset.Icc 2 N).filter P, (1 : ℝ) / (n : ℝ) ≤
        (2 / Real.log 2) * α * (Real.log (Real.log (N : ℝ)) + 2) + (N₀ : ℝ) := by
  intro N hN
  have hNN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Split `[2, N]` into `[2, N₀]` and `[N₀ + 1, N]`
  have hsub : (Finset.Icc 2 N).filter P ⊆
      Finset.Icc 2 N₀ ∪
      ((Finset.Icc 1 (Nat.log 2 N)).biUnion
        (fun j => (Finset.Icc (2 ^ j) (min (2 ^ (j + 1) - 1) N)).filter (fun n => P n ∧ N₀ < n))) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    by_cases hle : n ≤ N₀
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hn.1.1, hle⟩)
    · push Not at hle
      refine Finset.mem_union_right _ ?_
      rw [Finset.mem_biUnion]
      refine ⟨Nat.log 2 n, ?_, ?_⟩
      · refine Finset.mem_Icc.mpr ⟨?_, Nat.log_mono_right hn.1.2⟩
        have : 2 ≤ n := hn.1.1
        have h1 : 1 = Nat.log 2 2 := by decide
        rw [h1]
        exact Nat.log_mono_right this
      · simp only [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.pow_log_le_self 2 (by omega), le_min ?_ hn.1.2⟩, hn.2, hle⟩
        have hlt := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
        omega
  calc ∑ n ∈ (Finset.Icc 2 N).filter P, (1 : ℝ) / (n : ℝ)
      ≤ ∑ n ∈ Finset.Icc 2 N₀ ∪
          ((Finset.Icc 1 (Nat.log 2 N)).biUnion
            (fun j => (Finset.Icc (2 ^ j) (min (2 ^ (j + 1) - 1) N)).filter (fun n => P n ∧ N₀ < n))),
            (1 : ℝ) / (n : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ (∑ n ∈ Finset.Icc 2 N₀, (1 : ℝ) / (n : ℝ)) +
        ∑ j ∈ Finset.Icc 1 (Nat.log 2 N),
          ∑ n ∈ (Finset.Icc (2 ^ j) (min (2 ^ (j + 1) - 1) N)).filter (fun n => P n ∧ N₀ < n),
            (1 : ℝ) / (n : ℝ) := by
        exact (recSumReal_union_le _ _).trans (add_le_add le_rfl (recSumReal_biUnion_le _ _))
    _ ≤ (N₀ : ℝ) + ∑ j ∈ Finset.Icc 1 (Nat.log 2 N), (2 / Real.log 2) * α / ((j : ℝ) + 1) := by
        refine add_le_add ?_ ?_
        · calc ∑ n ∈ Finset.Icc 2 N₀, (1 : ℝ) / (n : ℝ)
              ≤ ∑ _n ∈ Finset.Icc 2 N₀, (1 : ℝ) :=
                Finset.sum_le_sum fun n hn =>
                  div_le_one_of_le₀ (by exact_mod_cast (by have := (Finset.mem_Icc.mp hn).1; omega : 1 ≤ n))
                    (by positivity)
            _ = ((Finset.Icc 2 N₀).card : ℝ) := by simp
            _ ≤ (N₀ : ℝ) := by
                have : (Finset.Icc 2 N₀).card ≤ N₀ := by rw [Nat.card_Icc]; omega
                exact_mod_cast this
        · refine Finset.sum_le_sum fun j hj => ?_
          set B := (Finset.Icc (2 ^ j) (min (2 ^ (j + 1) - 1) N)).filter (fun n => P n ∧ N₀ < n)
          by_cases hB : B.Nonempty
          · obtain ⟨n₀, hn₀⟩ := hB
            have hn₀' := Finset.mem_filter.mp hn₀
            have hM_ge : N₀ ≤ 2 ^ (j + 1) := by
              have h1 := (Finset.mem_Icc.mp hn₀'.1).2
              have h2 : n₀ ≤ 2 ^ (j + 1) - 1 := le_trans h1 (min_le_left _ _)
              omega
            have hBsub : B ⊆ (Finset.Icc 1 (2 ^ (j + 1))).filter P := by
              intro n hn
              have hn' := Finset.mem_filter.mp hn
              have hI := Finset.mem_Icc.mp hn'.1
              refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hn'.2.1⟩
              · exact le_trans (Nat.one_le_pow j 2 (by omega)) hI.1
              · exact le_trans (le_trans hI.2 (min_le_left _ _)) (Nat.sub_le _ _)
            have hcardB : (B.card : ℝ) ≤ α * ((2 ^ (j + 1) : ℕ) : ℝ) / Real.log ((2 ^ (j + 1) : ℕ) : ℝ) :=
              (Nat.cast_le.mpr (Finset.card_le_card hBsub)).trans (hcnt _ hM_ge)
            calc ∑ n ∈ B, (1 : ℝ) / (n : ℝ)
                ≤ ∑ _n ∈ B, (1 : ℝ) / ((2 ^ j : ℕ) : ℝ) := by
                  refine Finset.sum_le_sum fun n hn => ?_
                  have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
                  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast h1)
              _ = (B.card : ℝ) / ((2 ^ j : ℕ) : ℝ) := by simp [div_eq_mul_inv]
              _ ≤ (α * ((2 ^ (j + 1) : ℕ) : ℝ) / Real.log ((2 ^ (j + 1) : ℕ) : ℝ)) / ((2 ^ j : ℕ) : ℝ) := by
                  gcongr
              _ = (2 / Real.log 2) * α / ((j : ℝ) + 1) := by
                  rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, pow_succ]
                  push_cast
                  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
                  have h2j : ((2 : ℝ) ^ j) ≠ 0 := by positivity
                  field_simp [hj1, h2j, hlog2_pos.ne']
          · rw [Finset.not_nonempty_iff_eq_empty.mp hB, Finset.sum_empty]
            positivity
    _ ≤ (N₀ : ℝ) + (2 / Real.log 2) * α * (Real.log (Real.log (N : ℝ)) + 2) := by
        gcongr
        set J := Nat.log 2 N
        have hJ1 : 1 ≤ J := by
          have : 1 = Nat.log 2 2 := by decide
          rw [this]; exact Nat.log_mono_right (by omega)
        have hrew : ∑ j ∈ Finset.Icc 1 J, (2 / Real.log 2) * α / ((j : ℝ) + 1) =
            (2 / Real.log 2) * α * ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / ((j : ℝ) + 1) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
        rw [hrew]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hsum_le : ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / ((j : ℝ) + 1) ≤ Real.log (J : ℝ) + 1 := by
          have h1 : ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / ((j : ℝ) + 1) ≤
              ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / (j : ℝ) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
            exact one_div_le_one_div_of_le (by positivity) (by linarith)
          exact h1.trans (harmonic_le_log_add_one hJ1)
        have hJ_le : (J : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
          have hpow : (2 : ℝ) ^ J ≤ (N : ℝ) := by
            exact_mod_cast Nat.pow_log_le_self 2 (by omega)
          have hlogp : Real.log ((2 : ℝ) ^ J) ≤ Real.log (N : ℝ) :=
            Real.log_le_log (by positivity) hpow
          rw [Real.log_pow] at hlogp
          exact (le_div_iff₀ hlog2_pos).mpr hlogp
        have hlogJ : Real.log (J : ℝ) ≤ Real.log (Real.log (N : ℝ)) + 1 := by
          have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
          calc Real.log (J : ℝ)
              ≤ Real.log (Real.log (N : ℝ) / Real.log 2) :=
                Real.log_le_log (by exact_mod_cast hJ1) hJ_le
            _ = Real.log (Real.log (N : ℝ)) - Real.log (Real.log 2) :=
                Real.log_div hlogN_pos.ne' hlog2_pos.ne'
            _ ≤ Real.log (Real.log (N : ℝ)) + 1 := by
                have h2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
                have h3 : -1 ≤ Real.log (Real.log 2) := by
                  have h4 : Real.exp (-1 : ℝ) ≤ (1 : ℝ) / 2 := by
                    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
                    have := Real.add_one_le_exp (1 : ℝ)
                    linarith
                  rw [← Real.log_exp (-1 : ℝ)]
                  exact Real.log_le_log (Real.exp_pos _) (h4.trans h2)
                linarith
        linarith
    _ = (2 / Real.log 2) * α * (Real.log (Real.log (N : ℝ)) + 2) + (N₀ : ℝ) := by ring

/-- **Euler Product Upper Bound on Rough Numbers** (used in Bloom's `lem-usingq`):
There exists an absolute constant `C > 0` such that for all `y ≥ 16`, `N : ℕ` with `y ≤ N`,
and any `k : ℝ` with `1 ≤ k`, if `D` is a finite set of positive integers `d ≤ N` whose every
exact prime-power divisor `q ∥ d` satisfies `y < q`, then
`∑ d ∈ D, k ^ (omega d) / d ≤ exp(C * k) * (log N / log y) ^ k`. -/
theorem sum_rough_k_pow_omega_div_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ), 16 ≤ y → ∀ (N : ℕ), y ≤ (N : ℝ) →
      ∀ (k : ℝ), 1 ≤ k →
      ∀ (D : Finset ℕ), (∀ d ∈ D, 1 ≤ d ∧ d ≤ N ∧ ∀ q, ppowDiv q d → y < (q : ℝ)) →
      ∑ d ∈ D, k ^ (omega d) / (d : ℝ) ≤
        Real.exp (C * k) * (Real.log (N : ℝ) / Real.log y) ^ k := by
  obtain ⟨C₂, hC₂, hM2⟩ := RHDirect.Stage8MertensTheorems.mertens_second_theorem
  refine ⟨2 * C₂ / Real.log 3 + 5, by positivity, fun y hy N hN k hk D hD => ?_⟩
  have hy3 : (3 : ℝ) ≤ y := by linarith
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := le_trans hy3 hN
  have hlog_y_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog_N_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hk_pos : 0 < k := by linarith
  -- Define for each prime `p ≤ N` the sum `S(p) = ∑_{r ∈ Icc 1 N, y < p^r} p^{-r}`.
  set P := (Finset.Icc 2 N).filter Nat.Prime
  set S : ℕ → ℝ := fun p =>
    ∑ r ∈ (Finset.Icc 1 N).filter (fun r => y < ((p ^ r : ℕ) : ℝ)), (1 : ℝ) / ((p ^ r : ℕ) : ℝ)
  have hS_nn : ∀ p, 0 ≤ S p := fun p => Finset.sum_nonneg fun _ _ => by positivity
  -- Step 1: Euler product expansion bound `∑ d ∈ D, k^{ω(d)} / d ≤ ∏_{p ∈ P} (1 + k * S p)`.
  have heuler : ∑ d ∈ D, k ^ (omega d) / (d : ℝ) ≤ ∏ p ∈ P, (1 + k * S p) := by
    -- Expand `∏ p ∈ P, (1 + k * S p) = ∑ T ∈ P.powerset, ∏ p ∈ T, (k * S p)`
    have hprod_expand : ∏ p ∈ P, (1 + k * S p) = ∑ T ∈ P.powerset, ∏ p ∈ T, (k * S p) := by
      have h := Finset.prod_add (fun p => k * S p) (fun _ : ℕ => (1 : ℝ)) P
      have hcomm : ∏ p ∈ P, (1 + k * S p) = ∏ p ∈ P, (k * S p + 1) :=
        Finset.prod_congr rfl fun p _ => add_comm _ _
      rw [hcomm, h]
      refine Finset.sum_congr rfl fun T _ => ?_
      simp [Finset.prod_const_one]
    rw [hprod_expand]
    -- Every `d ∈ D` has `d.primeFactors ∈ P.powerset`
    have hpf_mem : ∀ d ∈ D, d.primeFactors ∈ P.powerset := by
      intro d hd
      rw [Finset.mem_powerset]
      intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      have hd1 := (hD d hd).1
      have hdN := (hD d hd).2.1
      have hpN : p ≤ N := le_trans (Nat.le_of_dvd hd1 (Nat.dvd_of_mem_primeFactors hp)) hdN
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp'.two_le, hpN⟩, hp'⟩
    -- Group `D` by `d.primeFactors`
    rw [← Finset.sum_fiberwise_of_maps_to hpf_mem]
    refine Finset.sum_le_sum fun T hT => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    have hrew : ∑ d ∈ D.filter (fun d => d.primeFactors = T), k ^ (omega d) / (d : ℝ) =
        k ^ T.card * ∑ d ∈ D.filter (fun d => d.primeFactors = T), (1 : ℝ) / (d : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hEq : d.primeFactors = T := (Finset.mem_filter.mp hd).2
      unfold omega
      rw [hEq]; ring
    rw [hrew]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hk_pos.le _)
    -- Prove `∀ (T : Finset ℕ) (D' : Finset ℕ), (∀ d ∈ D', 1 ≤ d ∧ d ≤ N ∧ d.primeFactors = T ∧ ∀ q, ppowDiv q d → y < q) → ∑ d ∈ D', (1 : ℝ) / d ≤ ∏ p ∈ T, S p`
    -- by induction on `T`!
    have hT_bound : ∀ (T' : Finset ℕ) (D' : Finset ℕ),
        (∀ d ∈ D', 1 ≤ d ∧ d ≤ N ∧ d.primeFactors = T' ∧ ∀ q, ppowDiv q d → y < (q : ℝ)) →
        ∑ d ∈ D', (1 : ℝ) / (d : ℝ) ≤ ∏ p ∈ T', S p := by
      intro T'
      induction T' using Finset.induction with
      | empty =>
        intro D' hD'
        rw [Finset.prod_empty]
        have hsub1 : D' ⊆ {1} := by
          intro d hd
          rw [Finset.mem_singleton]
          have h1 := (hD' d hd).1
          have hpf := (hD' d hd).2.2.1
          have hprod := Nat.prod_factorization_pow_eq_self (by omega : d ≠ 0)
          rw [Finsupp.prod, Nat.support_factorization, hpf, Finset.prod_empty] at hprod
          exact hprod.symm
        calc ∑ d ∈ D', (1 : ℝ) / (d : ℝ)
            ≤ ∑ d ∈ ({1} : Finset ℕ), (1 : ℝ) / (d : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun _ _ _ => by positivity
          _ = 1 := by simp
      | insert p s hps ih =>
        intro D' hD'
        rw [Finset.prod_insert hps]
        set R_p := (Finset.Icc 1 N).filter (fun r => y < ((p ^ r : ℕ) : ℝ))
        have hfac_mem : ∀ d ∈ D', d.factorization p ∈ R_p := by
          intro d hd
          have hd1 := (hD' d hd).1
          have hdN := (hD' d hd).2.1
          have hpf := (hD' d hd).2.2.1
          have hpmem : p ∈ d.primeFactors := by rw [hpf]; exact Finset.mem_insert_self p s
          have hp' := Nat.prime_of_mem_primeFactors hpmem
          have hv_pos : 1 ≤ d.factorization p := by
            have hne : d.factorization p ≠ 0 :=
              Finsupp.mem_support_iff.mp (Nat.support_factorization d ▸ hpmem)
            omega
          have hv_le : d.factorization p ≤ N := by
            calc d.factorization p ≤ 2 ^ (d.factorization p) := le_of_lt Nat.lt_two_pow_self
              _ ≤ p ^ (d.factorization p) := Nat.pow_le_pow_left hp'.two_le _
              _ ≤ d := Nat.le_of_dvd hd1 (Nat.ordProj_dvd d p)
              _ ≤ N := hdN
          have hpp : ppowDiv (p ^ (d.factorization p)) d :=
            (ppowDiv_iff_exists_primeFactor (by omega)).mpr ⟨p, hpmem, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hv_pos, hv_le⟩, (hD' d hd).2.2.2 _ hpp⟩
        rw [← Finset.sum_fiberwise_of_maps_to hfac_mem]
        change ∑ r ∈ R_p, ∑ d ∈ D'.filter (fun d => d.factorization p = r), (1 : ℝ) / (d : ℝ) ≤
          (∑ r ∈ R_p, (1 : ℝ) / ((p ^ r : ℕ) : ℝ)) * ∏ q ∈ s, S q
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun r hr => ?_
        set Fr := D'.filter (fun d => d.factorization p = r)
        set D'' := Fr.image (fun d => d / p ^ r)
        have hFr_div : ∀ d ∈ Fr, p ^ r * (d / p ^ r) = d := by
          intro d hd
          have hdD := (Finset.mem_filter.mp hd).1
          have hvr : d.factorization p = r := (Finset.mem_filter.mp hd).2
          rw [← hvr]
          exact Nat.mul_div_cancel' (Nat.ordProj_dvd d p)
        have hFr_inj : Set.InjOn (fun d => d / p ^ r) (Fr : Set ℕ) := by
          intro d₁ hd₁ d₂ hd₂ heq
          dsimp only at heq
          rw [← hFr_div d₁ hd₁, ← hFr_div d₂ hd₂, heq]
        have hFr_sum : ∑ d ∈ Fr, (1 : ℝ) / (d : ℝ) =
            (1 : ℝ) / ((p ^ r : ℕ) : ℝ) * ∑ m ∈ D'', (1 : ℝ) / (m : ℝ) := by
          rw [Finset.mul_sum]
          unfold D''
          rw [Finset.sum_image hFr_inj]
          refine Finset.sum_congr rfl fun d hd => ?_
          have hmul : ((d : ℕ) : ℝ) = ((p ^ r : ℕ) : ℝ) * ((d / p ^ r : ℕ) : ℝ) := by
            exact_mod_cast (hFr_div d hd).symm
          rw [hmul]; ring
        rw [hFr_sum]
        refine mul_le_mul_of_nonneg_left (ih D'' ?_) (by positivity)
        intro m hm
        obtain ⟨d, hdFr, rfl⟩ := Finset.mem_image.mp hm
        have hdD := (Finset.mem_filter.mp hdFr).1
        have hvr : d.factorization p = r := (Finset.mem_filter.mp hdFr).2
        have hd1 := (hD' d hdD).1
        have hdN := (hD' d hdD).2.1
        have hpf := (hD' d hdD).2.2.1
        have hpmem : p ∈ d.primeFactors := by rw [hpf]; exact Finset.mem_insert_self p s
        have hp' := Nat.prime_of_mem_primeFactors hpmem
        have hmul := hFr_div d hdFr
        have hm0 : d / p ^ r ≠ 0 := fun h => by rw [h, mul_zero] at hmul; omega
        have hmN : d / p ^ r ≤ N := le_trans (Nat.div_le_self d _) hdN
        have hcop_pm : Nat.Coprime (p ^ r) (d / p ^ r) := by
          rw [← hvr]
          exact (hp'.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hp' (by omega))).pow_left _
        have hmpf : (d / p ^ r).primeFactors = s := by
          ext q
          constructor
          · intro hq
            have hq_d : q ∈ d.primeFactors := by
              have hq' := Nat.prime_of_mem_primeFactors hq
              have hmdvd : d / p ^ r ∣ d := ⟨p ^ r, by rw [mul_comm, hmul]⟩
              exact Nat.mem_primeFactors.mpr ⟨hq', dvd_trans (Nat.dvd_of_mem_primeFactors hq) hmdvd, by omega⟩
            rw [hpf, Finset.mem_insert] at hq_d
            rcases hq_d with hqp | hqs
            · exfalso
              have hq_dvd : p ∣ d / p ^ r := by
                have h1 := Nat.dvd_of_mem_primeFactors hq
                rw [hqp] at h1
                exact h1
              have hr1 : 1 ≤ r := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
              have hp1 : p ∣ 1 := by
                rw [← hcop_pm.gcd_eq_one]
                exact Nat.dvd_gcd (dvd_pow_self p (by omega)) hq_dvd
              exact hp'.not_dvd_one hp1
            · exact hqs
          · intro hqs
            have hq_d : q ∈ d.primeFactors := by rw [hpf]; exact Finset.mem_insert_of_mem hqs
            have hq' := Nat.prime_of_mem_primeFactors hq_d
            have hqne : q ≠ p := fun h => hps (h ▸ hqs)
            have hqdvd_d : q ∣ p ^ r * (d / p ^ r) := hmul.symm ▸ Nat.dvd_of_mem_primeFactors hq_d
            have hqdvd_m : q ∣ d / p ^ r :=
              ((Nat.coprime_primes hq' hp').mpr hqne).pow_right r |>.dvd_of_dvd_mul_left hqdvd_d
            exact Nat.mem_primeFactors.mpr ⟨hq', hqdvd_m, hm0⟩
        refine ⟨Nat.pos_of_ne_zero hm0, hmN, hmpf, fun q hqm => ?_⟩
        -- Show `ppowDiv q (d / p ^ r) → ppowDiv q d`
        have hqd : ppowDiv q d := by
          obtain ⟨q₀, hq₀m, rfl⟩ := (ppowDiv_iff_exists_primeFactor hm0).mp hqm
          have hq₀s : q₀ ∈ s := hmpf ▸ hq₀m
          have hq₀d : q₀ ∈ d.primeFactors := by rw [hpf]; exact Finset.mem_insert_of_mem hq₀s
          have hq₀ne : q₀ ≠ p := fun h => hps (h ▸ hq₀s)
          have hfac_eq : d.factorization q₀ = (d / p ^ r).factorization q₀ := by
            have h1 := Nat.factorization_mul (pow_ne_zero r hp'.ne_zero) hm0
            rw [hmul] at h1
            have h2 := congrFun (congrArg DFunLike.coe h1) q₀
            simp only [Finsupp.add_apply, Nat.Prime.factorization_pow hp',
              Finsupp.single_eq_of_ne hq₀ne, zero_add] at h2
            exact h2
          rw [← hfac_eq]
          exact (ppowDiv_iff_exists_primeFactor (by omega)).mpr ⟨q₀, hq₀d, rfl⟩
        exact (hD' d hdD).2.2.2 q hqd
    refine hT_bound T (D.filter (fun d => d.primeFactors = T)) fun d hd => ?_
    have hdD := (Finset.mem_filter.mp hd).1
    have hpf := (Finset.mem_filter.mp hd).2
    exact ⟨(hD d hdD).1, (hD d hdD).2.1, hpf, (hD d hdD).2.2⟩
  -- Step 2: `∏_{p ∈ P} (1 + k * S p) ≤ exp(k * ∑_{p ∈ P} S p)`
  have hexp_bound : ∏ p ∈ P, (1 + k * S p) ≤ Real.exp (k * ∑ p ∈ P, S p) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod (fun p _ => by linarith [mul_nonneg hk_pos.le (hS_nn p)])
      fun p _ => ?_
    linarith [Real.add_one_le_exp (k * S p)]
  -- Step 3: Bound `∑ p ∈ P, S p ≤ log (log N / log y) + (2 * C₂ / log 3 + 5)`
  have hsumS_le : ∑ p ∈ P, S p ≤
      Real.log (Real.log (N : ℝ) / Real.log y) + (2 * C₂ / Real.log 3 + 5) := by
    -- Split `P` into `p ≤ ⌊y⌋₊` and `⌊y⌋₊ < p`
    have hsplit : ∑ p ∈ P, S p =
        (∑ p ∈ P.filter (· ≤ ⌊y⌋₊), S p) + (∑ p ∈ P.filter (fun p => ¬ p ≤ ⌊y⌋₊), S p) :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    rw [hsplit]
    -- Helper geometric bound: for prime `p`, `∑_{r ∈ Icc m N} p^{-r} ≤ (p^{-m}) / (1 - p⁻¹)`
    have hgeom_ge1 : ∀ p : ℕ, p.Prime →
        ∑ r ∈ Finset.Icc 1 N, (1 : ℝ) / ((p ^ r : ℕ) : ℝ) ≤ (1 : ℝ) / ((p : ℝ) - 1) := by
      intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
      have hr1 : (p : ℝ)⁻¹ < 1 := by rw [inv_lt_one_iff₀]; exact Or.inr (by linarith)
      have hsub : Finset.Icc 1 N ⊆ (Finset.range (N + 1)).image (· + 1) := by
        intro r hr; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range] at hr ⊢
        exact ⟨r - 1, by omega, by omega⟩
      calc ∑ r ∈ Finset.Icc 1 N, (1 : ℝ) / ((p ^ r : ℕ) : ℝ)
          ≤ ∑ r ∈ (Finset.range (N + 1)).image (· + 1), (1 : ℝ) / ((p ^ r : ℕ) : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ = ∑ j ∈ Finset.range (N + 1), ((p : ℝ)⁻¹) ^ (j + 1) := by
            rw [Finset.sum_image (fun _ _ _ _ h => by omega)]
            refine Finset.sum_congr rfl fun j _ => by rw [Nat.cast_pow, one_div, inv_pow]
        _ = (p : ℝ)⁻¹ * ∑ j ∈ Finset.range (N + 1), ((p : ℝ)⁻¹) ^ j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by rw [pow_succ]; ring
        _ ≤ (p : ℝ)⁻¹ * (1 / (1 - (p : ℝ)⁻¹)) := by
            gcongr
            rw [geom_sum_eq hr1.ne]
            have hden : 0 < 1 - (p : ℝ)⁻¹ := by linarith
            rw [show ((p : ℝ)⁻¹ ^ (N + 1) - 1) / ((p : ℝ)⁻¹ - 1) =
                (1 - (p : ℝ)⁻¹ ^ (N + 1)) / (1 - (p : ℝ)⁻¹) by
                  rw [show (p : ℝ)⁻¹ - 1 = -(1 - (p : ℝ)⁻¹) by ring, div_neg, ← neg_div]
                  congr 1; ring]
            exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 (N + 1)]) hden.le
        _ = (1 : ℝ) / ((p : ℝ) - 1) := by
            have hp0 : (p : ℝ) ≠ 0 := by linarith
            have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
            field_simp
    have hgeom_ge2 : ∀ p : ℕ, p.Prime →
        ∑ r ∈ Finset.Icc 2 N, (1 : ℝ) / ((p ^ r : ℕ) : ℝ) ≤ (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
      intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      have hsub : Finset.Icc 2 N ⊆ (Finset.Icc 1 N).image (· + 1) := by
        intro r hr; simp only [Finset.mem_Icc, Finset.mem_image] at hr ⊢
        exact ⟨r - 1, ⟨by omega, by omega⟩, by omega⟩
      calc ∑ r ∈ Finset.Icc 2 N, (1 : ℝ) / ((p ^ r : ℕ) : ℝ)
          ≤ ∑ r ∈ (Finset.Icc 1 N).image (· + 1), (1 : ℝ) / ((p ^ r : ℕ) : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ = (1 : ℝ) / (p : ℝ) * ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / ((p ^ j : ℕ) : ℝ) := by
            rw [Finset.sum_image (fun _ _ _ _ h => by omega), Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [pow_succ, Nat.cast_mul]; ring
        _ ≤ (1 : ℝ) / (p : ℝ) * ((1 : ℝ) / ((p : ℝ) - 1)) := by
            gcongr; exact hgeom_ge1 p hp
        _ = (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
            have hp0 : (p : ℝ) ≠ 0 := by linarith
            have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
            field_simp [hp0, hp1]
    -- Part A: `p ≤ ⌊y⌋₊` ⇒ every `r` with `p^r > y` satisfies `r ≥ 2`!
    have hpartA : ∑ p ∈ P.filter (· ≤ ⌊y⌋₊), S p ≤ 1 := by
      calc ∑ p ∈ P.filter (· ≤ ⌊y⌋₊), S p
          ≤ ∑ p ∈ P.filter (· ≤ ⌊y⌋₊), (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp' := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
            have hpy : (p : ℝ) ≤ y := by
              have h1 := (Finset.mem_filter.mp hp).2
              exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by linarith))
            have hRsub : (Finset.Icc 1 N).filter (fun r => y < ((p ^ r : ℕ) : ℝ)) ⊆ Finset.Icc 2 N := by
              intro r hr
              have hr1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
              have hrN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).2
              have hry := (Finset.mem_filter.mp hr).2
              have hr2 : 2 ≤ r := by
                by_contra hlt
                have hr_eq : r = 1 := by omega
                subst hr_eq; simp at hry; linarith
              exact Finset.mem_Icc.mpr ⟨hr2, hrN⟩
            exact (Finset.sum_le_sum_of_subset_of_nonneg hRsub fun _ _ _ => by positivity).trans
              (hgeom_ge2 p hp')
        _ ≤ ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n hn _ => ?_
            · intro p hp
              exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
            · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
              have : 0 < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
              positivity
        _ ≤ 1 := sum_inv_mul_pred_le_one N
    -- Part B: `p > ⌊y⌋₊` ⇒ `S p ≤ 1 / (p - 1) = 1 / p + 1 / (p * (p - 1))`
    have hpartB : ∑ p ∈ P.filter (fun p => ¬ p ≤ ⌊y⌋₊), S p ≤
        Real.log (Real.log (N : ℝ) / Real.log y) + 2 * C₂ / Real.log 3 + 1 := by
      have hstep1 : ∑ p ∈ P.filter (fun p => ¬ p ≤ ⌊y⌋₊), S p ≤
          (∑ p ∈ P.filter (fun p => ¬ p ≤ ⌊y⌋₊), (1 : ℝ) / (p : ℝ)) +
          (∑ p ∈ P.filter (fun p => ¬ p ≤ ⌊y⌋₊), (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun p hp => ?_
        have hp' := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.two_le
        have hS_le : S p ≤ (1 : ℝ) / ((p : ℝ) - 1) :=
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => by positivity).trans (hgeom_ge1 p hp')
        have heq : (1 : ℝ) / ((p : ℝ) - 1) = (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
          field_simp; ring
        linarith
      have htail : ∑ p ∈ P.filter (fun p => ¬ p ≤ ⌊y⌋₊), (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
        refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n hn _ => ?_).trans
          (sum_inv_mul_pred_le_one N)
        · intro p hp; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
          have : 0 < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
          positivity
      -- Express `∑_{⌊y⌋₊ < p ≤ N} 1/p = mertensSum2 N - mertensSum2 y`
      have hdiff_eq : ∑ p ∈ P.filter (fun p => ¬ p ≤ ⌊y⌋₊), (1 : ℝ) / (p : ℝ) =
          (∑ p ∈ (Finset.Icc 1 ⌊(N : ℝ)⌋₊).filter Nat.Prime, (p : ℝ)⁻¹) -
          (∑ p ∈ (Finset.Icc 1 ⌊y⌋₊).filter Nat.Prime, (p : ℝ)⁻¹) := by
        have hsub_y : (Finset.Icc 1 ⌊y⌋₊).filter Nat.Prime ⊆ (Finset.Icc 1 ⌊(N : ℝ)⌋₊).filter Nat.Prime := by
          refine Finset.filter_subset_filter _ ?_
          exact Finset.Icc_subset_Icc_right (Nat.floor_mono hN)
        have hsdiff : ((Finset.Icc 1 ⌊(N : ℝ)⌋₊).filter Nat.Prime) \ ((Finset.Icc 1 ⌊y⌋₊).filter Nat.Prime) =
            P.filter (fun p => ¬ p ≤ ⌊y⌋₊) := by
          ext p
          simp only [P, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc, Nat.floor_natCast]
          constructor
          · rintro ⟨⟨⟨hp1, hpN⟩, hpr⟩, hnot⟩
            refine ⟨⟨⟨hpr.two_le, hpN⟩, hpr⟩, fun hle => hnot ⟨⟨hp1, hle⟩, hpr⟩⟩
          · rintro ⟨⟨⟨hp2, hpN⟩, hpr⟩, hgt⟩
            exact ⟨⟨⟨by omega, hpN⟩, hpr⟩, fun h => hgt h.1.2⟩
        rw [← Finset.sum_sdiff hsub_y, hsdiff]
        simp only [one_div, add_sub_cancel_right]
      have hMN := hM2 (N : ℝ) hN3
      have hMy := hM2 y hy3
      have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
      have hCN : C₂ / Real.log (N : ℝ) ≤ C₂ / Real.log 3 :=
        div_le_div_of_nonneg_left hC₂.le hlog3_pos (Real.log_le_log (by norm_num) hN3)
      have hCy : C₂ / Real.log y ≤ C₂ / Real.log 3 :=
        div_le_div_of_nonneg_left hC₂.le hlog3_pos (Real.log_le_log (by norm_num) hy3)
      have h1 := (abs_le.mp hMN).2
      have h2 := (abs_le.mp hMy).1
      rw [Real.log_div hlog_N_pos.ne' hlog_y_pos.ne']
      have h2C : C₂ / Real.log (N : ℝ) + C₂ / Real.log y ≤ 2 * C₂ / Real.log 3 := by
        have : 2 * C₂ / Real.log 3 = C₂ / Real.log 3 + C₂ / Real.log 3 := by ring
        linarith
      linarith
    linarith
  -- Step 4: Combine everything!
  calc ∑ d ∈ D, k ^ (omega d) / (d : ℝ)
      ≤ ∏ p ∈ P, (1 + k * S p) := heuler
    _ ≤ Real.exp (k * ∑ p ∈ P, S p) := hexp_bound
    _ ≤ Real.exp (k * (Real.log (Real.log (N : ℝ) / Real.log y) + (2 * C₂ / Real.log 3 + 5))) := by
        gcongr
    _ = Real.exp ((2 * C₂ / Real.log 3 + 5) * k) *
        Real.exp (k * Real.log (Real.log (N : ℝ) / Real.log y)) := by
        rw [← Real.exp_add]; congr 1; ring
    _ = Real.exp ((2 * C₂ / Real.log 3 + 5) * k) * (Real.log (N : ℝ) / Real.log y) ^ k := by
        rw [Real.rpow_def_of_pos (div_pos hlog_N_pos hlog_y_pos), mul_comm k]

end Prize.PPL024
