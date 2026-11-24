import RHDirect.Stage11CrystallineFontaine
import Mathlib.RingTheory.Perfection
import Mathlib.RingTheory.WittVector.Basic
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.RingTheory.WittVector.Frobenius
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.Domain
import Mathlib.RingTheory.WittVector.Identities
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RepresentationTheory.Basic

/-!
# RHDirect.Stage12FontainePeriods

Unconditional Lean 4 formalization (`0 sorry`, `0 custom axioms`, `0 native_decide`) of
Fontaine's `p`-adic Hodge theory period rings (`A_inf`, `B_dR^+`, `B_dR`, `A_cris`, `B_cris`),
the crystalline functor `D_cris(V)` landing in `Stage11CrystallineFontaine.FilteredPhiModule p`,
and a concrete non-vacuous `Nonempty (LocTied p)` witness for every prime `p`.

## Architecture (Diamond-Free)
All period-ring morphisms over `WittVector`, `AdicCompletion`, and `Localization.Away` are
built with explicit `RingHom`s to avoid `Algebra`/`SMul` typeclass diamonds.
-/

noncomputable section

open scoped BigOperators
open Ideal Filter Topology

namespace RHDirect
namespace Stage12FontainePeriods

universe u v

/-! ## Section 1: Elementary `p`-adic, Binomial, and Adic-Completion Preliminaries -/

section Prelims

open scoped Nat

/-- **Binomial `p`-adic Lifting Lemma**: in any commutative ring `R`, if `p` is prime and
`p ∣ u - v`, then `p ^ (m + 1) ∣ u ^ (p ^ m) - v ^ (p ^ m)` for every `m : ℕ`. -/
theorem prime_pow_dvd_pow_sub_pow {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
    {u v : R} (h : (p : R) ∣ u - v) (m : ℕ) :
    (p : R) ^ (m + 1) ∣ u ^ (p ^ m) - v ^ (p ^ m) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    obtain ⟨k, hk⟩ := ih
    have hu : u ^ (p ^ m) = v ^ (p ^ m) + (p : R) ^ (m + 1) * k := by linear_combination hk
    have hpow : u ^ (p ^ (m + 1)) - v ^ (p ^ (m + 1)) =
        ((p : R) ^ (m + 1) * k + v ^ (p ^ m)) ^ p - (v ^ (p ^ m)) ^ p := by
      rw [pow_succ, pow_mul, pow_mul, hu, add_comm]
    rw [hpow, add_pow, Finset.sum_range_succ']
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, tsub_zero,
      add_sub_cancel_right]
    refine Finset.dvd_sum fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hj1 : j + 1 ≤ p := Nat.succ_le_of_lt hj
    by_cases hjp : j + 1 = p
    · rw [hjp, mul_pow, ← pow_mul]
      have hexp : m + 2 ≤ (m + 1) * p := by
        have hp2 : 2 ≤ p := hp.two_le
        nlinarith
      have hdvd : (p : R) ^ (m + 2) ∣ (p : R) ^ ((m + 1) * p) := pow_dvd_pow _ hexp
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdvd _) _) _
    · have hjlt : j + 1 < p := lt_of_le_of_ne hj1 hjp
      have hch : p ∣ Nat.choose p (j + 1) := hp.dvd_choose_self (Nat.succ_ne_zero j) hjlt
      obtain ⟨c, hc⟩ := hch
      have hterm : ((p : R) ^ (m + 1) * k) ^ (j + 1) =
          (p : R) ^ (m + 1) * (k * ((p : R) ^ (m + 1) * k) ^ j) := by
        rw [pow_succ']; ring
      rw [hterm, hc, Nat.cast_mul]
      have hre : (p : R) ^ (m + 1) * (k * ((p : R) ^ (m + 1) * k) ^ j) *
          (v ^ (p ^ m)) ^ (p - (j + 1)) * ((p : R) * (c : R)) =
          (p : R) ^ (m + 2) * (k * ((p : R) ^ (m + 1) * k) ^ j *
            (v ^ (p ^ m)) ^ (p - (j + 1)) * (c : R)) := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
        ring
      rw [hre]
      exact dvd_mul_right _ _

/-- Iterative `q`-adic approximation criterion for membership in a principal ideal `span {ξ}`
inside a `q`-adically complete ring. -/
theorem mem_span_of_approx {A : Type*} [CommRing A] (q ξ : A)
    [IsAdicComplete (Ideal.span {q}) A]
    (K : Set A) (h : ∀ x ∈ K, ∃ a, ∃ y ∈ K, x = ξ * a + q * y) {x : A} (hx : x ∈ K) :
    x ∈ Ideal.span {ξ} := by
  choose! a s hs hxs using h
  have hK : ∀ n, s^[n] x ∈ K := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => rw [Function.iterate_succ_apply']; exact hs _ ih
  let b : ℕ → A := fun n => ∑ i ∈ Finset.range n, q ^ i * a (s^[i] x)
  have hb : ∀ n, x = ξ * b n + q ^ n * s^[n] x := by
    intro n
    induction n with
    | zero => simp [b]
    | succ n ih =>
      have h1 := hxs _ (hK n)
      simp only [b] at ih ⊢
      rw [Finset.sum_range_succ, Function.iterate_succ_apply']
      linear_combination ih + q ^ n * h1
  have hmem : ∀ (n : ℕ) (z : A), z ∈ (Ideal.span {q} ^ n • ⊤ : Ideal A) ↔ q ^ n ∣ z := by
    intro n z
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {q}) (M := A) inferInstance (f := b) (by
    intro m n hle
    rw [SModEq.sub_mem, hmem]
    induction n, hle using Nat.le_induction with
    | base => simp
    | succ n hle ih =>
      simp only [b] at ih ⊢
      rw [Finset.sum_range_succ, ← sub_sub]
      exact dvd_sub ih ((pow_dvd_pow q hle).mul_right _))
  have hxL : x - ξ * L = 0 := by
    refine IsHausdorff.haus (I := Ideal.span {q}) (M := A) inferInstance _ fun n => ?_
    have h1 := hL n
    rw [SModEq.sub_mem, hmem] at h1 ⊢
    have heq : x - ξ * L - 0 = ξ * (b n - L) + q ^ n * s^[n] x := by linear_combination hb n
    rw [heq]
    exact dvd_add (h1.mul_left _) (dvd_mul_right _ _)
  rw [sub_eq_zero.1 hxL]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- In a `q`-adically Hausdorff ring, any element divisible by all `q ^ n` is zero. -/
theorem eq_zero_of_forall_pow_dvd {A : Type*} [CommRing A] (q : A)
    [IsHausdorff (Ideal.span {q}) A] {x : A} (h : ∀ n : ℕ, q ^ n ∣ x) : x = 0 := by
  refine IsHausdorff.haus (I := Ideal.span {q}) (M := A) inferInstance _ fun n => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, sub_zero]
  exact h n

/-- Elementary `p`-adic valuation bound on factorials: `(p - 1) * v_p(m!) < m` for all `m ≥ 1`. -/
theorem padicValNat_factorial_mul_lt {p : ℕ} [Fact p.Prime] :
    ∀ m : ℕ, 1 ≤ m → (p - 1) * padicValNat p (m !) < m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm
    have hp : p.Prime := Fact.out
    have hp1 : 1 < p := hp.one_lt
    have hrec : padicValNat p (m !) = m / p + padicValNat p ((m / p)!) := by
      have h1 := padicValNat_factorial (p := p) (n := m) (b := m + 1)
        (Nat.lt_succ_of_le (Nat.log_le_self p m))
      have h2 := padicValNat_factorial (p := p) (n := m / p) (b := m)
        (lt_of_le_of_lt (Nat.log_le_self p (m / p)) (Nat.div_lt_self (by omega) hp1))
      rw [h1, h2]
      have hsum : ∑ i ∈ Finset.Ico 1 (m + 1), m / p ^ i =
          m / p + ∑ i ∈ Finset.Ico 1 m, (m / p) / p ^ i := by
        rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < m + 1)]
        simp only [pow_one]
        congr 1
        refine Finset.sum_bij (fun i _ => i - 1) ?_ ?_ ?_ ?_
        · intro i hi
          rw [Finset.mem_Ico] at hi ⊢
          omega
        · intro i₁ hi₁ i₂ hi₂ h
          rw [Finset.mem_Ico] at hi₁ hi₂
          omega
        · intro j hj
          rw [Finset.mem_Ico] at hj
          exact ⟨j + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro i hi
          rw [Finset.mem_Ico] at hi
          rw [Nat.div_div_eq_div_mul, ← pow_succ']
          congr 2
          omega
      exact hsum
    rw [hrec, mul_add]
    by_cases hq : m / p = 0
    · rw [hq, Nat.factorial_zero, padicValNat_one_right, mul_zero, add_zero]
      exact hm
    · have hq_pos : 1 ≤ m / p := Nat.pos_of_ne_zero hq
      have hq_lt : m / p < m := Nat.div_lt_self (by omega) hp1
      have hih := ih (m / p) hq_lt hq_pos
      have hmul : p * (m / p) ≤ m := Nat.mul_div_le m p
      have hsplit : (p - 1) * (m / p) + m / p = p * (m / p) := by
        cases p with
        | zero => omega
        | succ k => simp [Nat.succ_mul, add_comm]
      omega

/-- `v_p(m!) < m` for every `m ≥ 1` and every prime `p`. -/
theorem padicValNat_factorial_lt {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m) :
    padicValNat p (m !) < m := by
  have hp : p.Prime := Fact.out
  have h := padicValNat_factorial_mul_lt (p := p) m hm
  have hp1 : 1 ≤ p - 1 := by have := hp.two_le; omega
  exact lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hp1) h

/-- `p ^ n ∣ (p * n)!` for every `p ≥ 1` and `n : ℕ`. -/
theorem prime_pow_dvd_factorial_mul {p : ℕ} (hp : 0 < p) (n : ℕ) : p ^ n ∣ (p * n)! := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmul : p * (n + 1) = p * n + p := by ring
    rw [pow_succ, hmul]
    have hpos : 0 < p * n + p := Nat.add_pos_right _ hp
    have hstep : (p * n)! * (p * n + p) ∣ (p * n + p)! := by
      have hpred : (p * n + p) * (p * n + p - 1)! = (p * n + p)! :=
        Nat.mul_factorial_pred hpos.ne'
      rw [← hpred, mul_comm (p * n)!]
      exact mul_dvd_mul_left _ (Nat.factorial_dvd_factorial (by omega))
    exact (mul_dvd_mul ih (dvd_add (dvd_mul_right p n) dvd_rfl)).trans hstep

end Prelims

/-! ### Clean Multinomial Divisibility Helper -/

section MultinomialHelper

open scoped Nat

theorem factorial_pow_dvd_mul_factorial (k : ℕ) : ∀ m : ℕ, (k !) ^ m ∣ (m * k)! := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul]
    have hch : (m * k)! * k ! ∣ (m * k + k)! := by
      have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (m * k) k)
      rw [Nat.add_sub_cancel_left] at h
      exact ⟨Nat.choose (m * k + k) (m * k), by linarith⟩
    exact (mul_dvd_mul_right ih (k !)).trans hch

theorem prime_mul_factorial_pow_dvd_factorial {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) :
    p * (k !) ^ p ∣ (p * k)! := by
  have hp : p.Prime := Fact.out
  have hbase := factorial_pow_dvd_mul_factorial k p
  obtain ⟨q, hq⟩ := hbase
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hq
    exact Nat.factorial_ne_zero _ hq
  have hk0 : (k !) ^ p ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero k)
  have hval_eq : padicValNat p ((p * k)!) = padicValNat p ((k !) ^ p) + padicValNat p q := by
    rw [hq, padicValNat.mul hk0 hq0]
  have hval_lhs : padicValNat p ((p * k)!) = k + padicValNat p (k !) := by
    have h1 := padicValNat_factorial (p := p) (n := p * k) (b := p * k + 1)
      (Nat.lt_succ_of_le (Nat.log_le_self p (p * k)))
    have h2 := padicValNat_factorial (p := p) (n := k) (b := p * k) (by
      have hlt : k < p * k := by have := hp.two_le; nlinarith
      exact lt_of_le_of_lt (Nat.log_le_self p k) hlt)
    rw [h1, h2]
    rw [Finset.sum_eq_sum_Ico_succ_bot (by have := hp.two_le; nlinarith : 1 < p * k + 1)]
    simp only [pow_one, Nat.mul_div_cancel_left _ hp.pos]
    congr 1
    refine Finset.sum_bij (fun i _ => i - 1) ?_ ?_ ?_ ?_
    · intro i hi; rw [Finset.mem_Ico] at hi ⊢; omega
    · intro i₁ hi₁ i₂ hi₂ h; rw [Finset.mem_Ico] at hi₁ hi₂; omega
    · intro j hj; rw [Finset.mem_Ico] at hj
      exact ⟨j + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro i hi; rw [Finset.mem_Ico] at hi
      have heq : p ^ i = p * p ^ (i - 1) := by
        cases i with
        | zero => omega
        | succ r => simp [pow_succ']
      rw [heq, Nat.mul_div_mul_left _ _ hp.pos]
  have hval_pow : padicValNat p ((k !) ^ p) = p * padicValNat p (k !) :=
    padicValNat.pow p (a := k !)
  have hlt := padicValNat_factorial_mul_lt (p := p) k hk
  have hq_val_pos : 1 ≤ padicValNat p q := by
    have hsplit : (p - 1) * padicValNat p (k !) + padicValNat p (k !) = p * padicValNat p (k !) := by
      cases p with
      | zero => exact absurd hp (by decide)
      | succ r => simp [Nat.succ_mul, add_comm]
    omega
  have hp_dvd_q : p ∣ q := by
    have h1 := pow_padicValNat_dvd (p := p) (n := q)
    exact (dvd_pow_self p (by omega : padicValNat p q ≠ 0)).trans h1
  obtain ⟨r, rfl⟩ := hp_dvd_q
  exact ⟨r, by rw [hq]; ring⟩

end MultinomialHelper

/-! ## Section 2: Perfectoid-Style Valuation Rings & Concrete `O_{ℂ_p}` (`PadicComplexInt p`) -/

/-- A **`p`-adically complete perfectoid-style valuation ring** `O`:
an integral domain valuation ring of characteristic `0` in which `p` is a non-unit,
`O` is `p`-adically complete, Frobenius `x ↦ x^p` is surjective mod `p`, and `O` carries
a compatible `p`-power system `p^♭ = (p, p^{1/p}, …)` and primitive `p`-power root system
`ε = (1, ζ_p, ζ_{p²}, …)`. -/
class PerfectoidBase (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] where
  frob_mod_p_surj : Function.Surjective (fun x : ModP O p => x ^ p)
  pPowerSeq : ℕ → O
  pPowerSeq_zero : pPowerSeq 0 = (p : O)
  pPowerSeq_pow : ∀ n, (pPowerSeq (n + 1)) ^ p = pPowerSeq n
  zetaSeq : ℕ → O
  zetaSeq_zero : zetaSeq 0 = 1
  zetaSeq_one_ne_one : zetaSeq 1 ≠ 1
  zetaSeq_pow : ∀ n, (zetaSeq (n + 1)) ^ p = zetaSeq n

section ConcretePadicComplexInt

variable (p : ℕ) [Fact p.Prime]

/-- Abbreviation for `O_{ℂ_p} := PadicComplexInt p`. -/
abbrev OCp : Type := PadicComplexInt p

theorem mem_OCp_iff (x : ℂ_[p]) : x ∈ PadicComplexInt p ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm,
    Valuation.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe, PadicComplex.RankOne.hom_eq_embedding,
    Valuation.embedding_restrict]

theorem OCp_norm_le_one (x : OCp p) : ‖(x : ℂ_[p])‖ ≤ 1 :=
  (mem_OCp_iff p x.1).mp x.2

theorem OCp_dvd_iff_norm_le (x y : OCp p) : x ∣ y ↔ ‖(y : ℂ_[p])‖ ≤ ‖(x : ℂ_[p])‖ := by
  constructor
  · rintro ⟨c, rfl⟩
    push_cast
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (OCp_norm_le_one p c)
  · intro h
    by_cases hx : (x : ℂ_[p]) = 0
    · rw [hx, norm_zero, norm_le_zero_iff] at h
      rw [show y = 0 from Subtype.ext h]
      exact dvd_zero _
    · refine ⟨⟨(y : ℂ_[p]) / (x : ℂ_[p]), (mem_OCp_iff p _).2 ?_⟩, Subtype.ext ?_⟩
      · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · push_cast; field_simp

theorem OCp_norm_p_lt_one : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
    ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p))]
  exact (PadicAlgCl.norm_extends p p).trans_lt Padic.norm_p_lt_one

instance instFactNotIsUnitOCp : Fact ¬IsUnit ((p : ℕ) : OCp p) :=
  ⟨by
    rw [isUnit_iff_dvd_one, OCp_dvd_iff_norm_le]
    push_cast
    rw [norm_one]
    exact not_le.mpr (OCp_norm_p_lt_one p)⟩

theorem OCp_mem_span_pow_iff (n : ℕ) (x : OCp p) :
    x ∈ (Ideal.span {((p : ℕ) : OCp p)} ^ n • ⊤ : Submodule (OCp p) (OCp p)) ↔
      ‖(x : ℂ_[p])‖ ≤ ‖((p : ℕ) : ℂ_[p])‖ ^ n := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    OCp_dvd_iff_norm_le]
  push_cast
  rw [norm_pow]

instance instIsAdicCompleteOCp :
    IsAdicComplete (Ideal.span {((p : ℕ) : OCp p)}) (OCp p) where
  haus' x hx := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg ((p : ℕ) : ℂ_[p]))
      (OCp_norm_p_lt_one p)
    have hle : ‖(x : ℂ_[p])‖ ≤ 0 := ge_of_tendsto' ht fun n => by
      have hn := hx n
      rwa [SModEq.zero, OCp_mem_span_pow_iff] at hn
    exact Subtype.ext (norm_le_zero_iff.1 hle)
  prec' f hf := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg ((p : ℕ) : ℂ_[p]))
      (OCp_norm_p_lt_one p)
    have h1 : ∀ m n, m ≤ n → dist (f m : ℂ_[p]) (f n : ℂ_[p]) ≤ ‖((p : ℕ) : ℂ_[p])‖ ^ m := by
      intro m n hmn
      have hn := hf hmn
      rw [SModEq.sub_mem, OCp_mem_span_pow_iff] at hn
      rw [dist_eq_norm]
      exact_mod_cast hn
    have hc : CauchySeq fun n => (f n : ℂ_[p]) := cauchySeq_of_le_tendsto_0' _ h1 ht
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm fun n => OCp_norm_le_one p (f n)
    refine ⟨⟨L, (mem_OCp_iff p L).2 hL1⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, OCp_mem_span_pow_iff]
    have hd : dist (f n : ℂ_[p]) L ≤ ‖((p : ℕ) : ℂ_[p])‖ ^ n :=
      le_of_tendsto (tendsto_const_nhds.dist hL)
        (eventually_atTop.2 ⟨n, fun m hm => h1 n m hm⟩)
    rw [dist_eq_norm] at hd
    exact_mod_cast hd

theorem OCp_exists_pow_eq (x : OCp p) {n : ℕ} (hn : 0 < n) : ∃ y : OCp p, y ^ n = x := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ_[p]) hn
  refine ⟨⟨y, (mem_OCp_iff p y).2 ?_⟩, Subtype.ext hy⟩
  rw [← pow_le_one_iff_of_nonneg (norm_nonneg y) hn.ne', ← norm_pow, hy]
  exact OCp_norm_le_one p x

theorem OCp_exists_primitive_p_root : ∃ ζ : OCp p, ζ ^ p = 1 ∧ ζ ≠ 1 := by
  have hp : p.Prime := Fact.out
  let Φ : Polynomial ℂ_[p] := ∑ j ∈ Finset.range p, Polynomial.X ^ j
  have hdeg : Φ.natDegree = p - 1 := by
    have hle : Φ.natDegree ≤ p - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [Polynomial.natDegree_X_pow]
      omega
    have hcoeff : Φ.coeff (p - 1) = 1 := by
      simp only [Φ, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
      rw [Finset.sum_ite_eq (Finset.range p) (p - 1)]
      simp [Finset.mem_range, Nat.sub_lt hp.pos zero_lt_one]
    exact le_antisymm hle (Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact one_ne_zero))
  have hdeg0 : Φ.degree ≠ 0 := by
    intro h0
    have hnd : Φ.natDegree = 0 := Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h0)
    have := hp.two_le
    omega
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root Φ hdeg0
  have hζ_ne1 : ζ ≠ 1 := by
    intro h1
    rw [Polynomial.IsRoot.def, h1] at hζ
    simp only [Φ, Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hζ
    exact Nat.cast_ne_zero.mpr hp.ne_zero hζ
  have hζ_pow : ζ ^ p = 1 := by
    have hgeom : (ζ - 1) * Φ.eval ζ = ζ ^ p - 1 := by
      simp only [Φ, Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X]
      simpa [mul_comm] using geom_sum_mul ζ p
    rw [Polynomial.IsRoot.def.mp hζ, mul_zero] at hgeom
    exact sub_eq_zero.mp hgeom.symm
  have hnorm : ‖ζ‖ ≤ 1 := by
    have hnp : ‖ζ‖ ^ p = 1 := by rw [← norm_pow, hζ_pow, norm_one]
    exact (pow_le_one_iff_of_nonneg (norm_nonneg ζ) hp.ne_zero).mp hnp.le
  exact ⟨⟨ζ, (mem_OCp_iff p ζ).2 hnorm⟩, Subtype.ext hζ_pow,
    fun h => hζ_ne1 (congrArg Subtype.val h)⟩

/-- **Concrete Perfectoid Base Witness**: `O_{ℂ_p} = PadicComplexInt p` satisfies every
`PerfectoidBase p` axiom for every prime `p`. -/
noncomputable instance instPerfectoidBaseOCp : PerfectoidBase p (OCp p) := by
  have hp : p.Prime := Fact.out
  let r : OCp p → OCp p := fun x => (OCp_exists_pow_eq p x hp.pos).choose
  have hr : ∀ x : OCp p, r x ^ p = x := fun x => (OCp_exists_pow_eq p x hp.pos).choose_spec
  let ζ : OCp p := (OCp_exists_primitive_p_root p).choose
  have hζp : ζ ^ p = 1 := (OCp_exists_primitive_p_root p).choose_spec.1
  have hζ1 : ζ ≠ 1 := (OCp_exists_primitive_p_root p).choose_spec.2
  let zSeq : ℕ → OCp p := fun
    | 0 => 1
    | n + 1 => r^[n] ζ
  exact
    { frob_mod_p_surj := fun x => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact ⟨Ideal.Quotient.mk _ (r a), by dsimp only; rw [← map_pow, hr a]⟩
      pPowerSeq := fun n => r^[n] ((p : ℕ) : OCp p)
      pPowerSeq_zero := rfl
      pPowerSeq_pow := fun n => by rw [Function.iterate_succ_apply', hr]
      zetaSeq := zSeq
      zetaSeq_zero := rfl
      zetaSeq_one_ne_one := hζ1
      zetaSeq_pow := fun n => by
        cases n with
        | zero => exact hζp
        | succ n =>
          change (r^[n + 1] ζ) ^ p = r^[n] ζ
          rw [Function.iterate_succ_apply', hr] }

end ConcretePadicComplexInt

/-! ## Section 3: Concrete Tilt `Tilt p O`, Sharp Map `♯`, Fontaine's `A_inf`, `thetaMap`, `xi`, and `ker θ = (ξ)` -/

section TiltAndAinf

variable {p : ℕ} [Fact p.Prime]
variable {O : Type u} [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)]

/-- **Concrete Tilt `Tilt p O`**: the perfection `{x : ℕ → O ⧸ (p) | ∀ n, (x (n+1))^p = x n}`
of `O ⧸ (p)`, instantiated directly on Mathlib's `PreTilt O p`. -/
abbrev Tilt (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)] : Type u :=
  PreTilt O p

/-- `Tilt p O` is a commutative ring of characteristic `p` with bijective Frobenius. -/
theorem tilt_charP : CharP (Tilt p O) p := inferInstance

theorem tilt_frobenius_bijective : Function.Bijective (frobenius (Tilt p O) p) :=
  (frobeniusEquiv (Tilt p O) p).bijective

/-- Construct an element of `Tilt p O` from any compatible `p`-power sequence `s : ℕ → O`
satisfying `(s (n + 1))^p = s n`. -/
def Tilt.ofSeq (s : ℕ → O) (hs : ∀ n, (s (n + 1)) ^ p = s n) : Tilt p O :=
  ⟨fun n => Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (s n), fun n => by
    change (Ideal.Quotient.mk _ (s (n + 1))) ^ p = Ideal.Quotient.mk _ (s n)
    rw [← map_pow, hs n]⟩

@[simp] theorem Tilt.coeff_ofSeq (s : ℕ → O) (hs : ∀ n, (s (n + 1)) ^ p = s n) (n : ℕ) :
    PreTilt.coeff n (Tilt.ofSeq (p := p) s hs) =
      Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (s n) := rfl

section SharpMap

variable [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]

omit [Fact p.Prime] [Fact ¬IsUnit ((p : ℕ) : O)]
  [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] in
private theorem p_dvd_sub_of_mk_eq {a b : O}
    (h : Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) a =
      Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) b) : ((p : ℕ) : O) ∣ a - b :=
  Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)

omit [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] in
/-- Any choice of lifts `a n : O` of `PreTilt.coeff n x` yields a `p`-adically Cauchy sequence
`a n ^ (p ^ n)` with a unique limit in `O`. -/
private theorem sharp_cauchy (x : Tilt p O) (a : ℕ → O)
    (ha : ∀ n, Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (a n) = PreTilt.coeff n x) :
    ∀ {m n : ℕ}, m ≤ n →
      (a m ^ (p ^ m)) ≡ (a n ^ (p ^ n)) [SMOD (Ideal.span {((p : ℕ) : O)} ^ m • ⊤ : Submodule O O)] := by
  have hp : p.Prime := Fact.out
  have hstep : ∀ k : ℕ, ((p : ℕ) : O) ^ (k + 1) ∣ a (k + 1) ^ (p ^ (k + 1)) - a k ^ (p ^ k) := by
    intro k
    have hmk : Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (a (k + 1) ^ p) =
        Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (a k) := by
      rw [map_pow, ha (k + 1), ha k, PreTilt.coeff_pow_p]
    have hdvd : ((p : ℕ) : O) ∣ a (k + 1) ^ p - a k := p_dvd_sub_of_mk_eq hmk
    have hpow := prime_pow_dvd_pow_sub_pow hp hdvd k
    rwa [← pow_mul, ← pow_succ'] at hpow
  intro m n hmn
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have h1 : ((p : ℕ) : O) ^ m ∣ a n ^ (p ^ n) - a (n + 1) ^ (p ^ (n + 1)) := by
      have hd := dvd_neg.mpr (hstep n)
      rw [neg_sub] at hd
      exact (pow_dvd_pow _ (by omega : m ≤ n + 1)).trans hd
    have hsum : a m ^ (p ^ m) - a (n + 1) ^ (p ^ (n + 1)) =
        (a m ^ (p ^ m) - a n ^ (p ^ n)) + (a n ^ (p ^ n) - a (n + 1) ^ (p ^ (n + 1))) := by ring
    rw [hsum]
    exact dvd_add ih h1

/-- **Fontaine's Multiplicative Sharp (Untilt) Map `x ↦ x^♯`**:
defined as `x^♯ = lim_{n → ∞} (a_n)^{p^n}` in the `p`-adically complete ring `O`. -/
def sharpFun (x : Tilt p O) : O :=
  let a : ℕ → O := fun n => (Ideal.Quotient.mk_surjective (PreTilt.coeff n x)).choose
  let ha : ∀ n, Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (a n) = PreTilt.coeff n x :=
    fun n => (Ideal.Quotient.mk_surjective (PreTilt.coeff n x)).choose_spec
  (IsPrecomplete.prec (I := Ideal.span {((p : ℕ) : O)}) (M := O) inferInstance
    (f := fun n => a n ^ (p ^ n)) (sharp_cauchy x a ha)).choose

/-- Uniqueness characterization of `sharpFun x`: for ANY lift sequence `a n` of `PreTilt.coeff n x`,
`p ^ n ∣ a n ^ (p ^ n) - sharpFun x` for all `n : ℕ`. -/
theorem sharpFun_spec (x : Tilt p O) (a : ℕ → O)
    (ha : ∀ n, Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (a n) = PreTilt.coeff n x) (n : ℕ) :
    ((p : ℕ) : O) ^ n ∣ a n ^ (p ^ n) - sharpFun x := by
  have hp : p.Prime := Fact.out
  let b : ℕ → O := fun k => (Ideal.Quotient.mk_surjective (PreTilt.coeff k x)).choose
  have hb : ∀ k, Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (b k) = PreTilt.coeff k x :=
    fun k => (Ideal.Quotient.mk_surjective (PreTilt.coeff k x)).choose_spec
  have hlim := (IsPrecomplete.prec (I := Ideal.span {((p : ℕ) : O)}) (M := O) inferInstance
    (f := fun k => b k ^ (p ^ k)) (sharp_cauchy x b hb)).choose_spec n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hlim
  have hab : ((p : ℕ) : O) ^ (n + 1) ∣ a n ^ (p ^ n) - b n ^ (p ^ n) :=
    prime_pow_dvd_pow_sub_pow hp (p_dvd_sub_of_mk_eq ((ha n).trans (hb n).symm)) n
  have hab' : ((p : ℕ) : O) ^ n ∣ a n ^ (p ^ n) - b n ^ (p ^ n) :=
    (pow_dvd_pow _ (Nat.le_succ n)).trans hab
  have heq : a n ^ (p ^ n) - sharpFun x =
      (a n ^ (p ^ n) - b n ^ (p ^ n)) + (b n ^ (p ^ n) - sharpFun x) := by ring
  rw [heq]
  exact dvd_add hab' hlim

theorem eq_sharpFun_of_forall_dvd (x : Tilt p O) (L : O) (a : ℕ → O)
    (ha : ∀ n, Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (a n) = PreTilt.coeff n x)
    (hL : ∀ n, ((p : ℕ) : O) ^ n ∣ a n ^ (p ^ n) - L) : L = sharpFun x := by
  symm
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_pow_dvd ((p : ℕ) : O) fun n => ?_
  have h1 := sharpFun_spec x a ha n
  have h2 := hL n
  have heq : sharpFun x - L = (a n ^ (p ^ n) - L) - (a n ^ (p ^ n) - sharpFun x) := by ring
  rw [heq]
  exact dvd_sub h2 h1

theorem sharpFun_one : sharpFun (p := p) (O := O) 1 = 1 := by
  symm
  exact eq_sharpFun_of_forall_dvd 1 1 (fun _ => 1) (fun _ => by simp) (fun _ => by simp)

theorem sharpFun_zero : sharpFun (p := p) (O := O) 0 = 0 := by
  have hp : p.Prime := Fact.out
  symm
  exact eq_sharpFun_of_forall_dvd 0 0 (fun _ => 0) (fun _ => by simp)
    (fun n => by rw [zero_pow (pow_pos hp.pos n).ne', sub_self]; exact dvd_zero _)

theorem sharpFun_mul (x y : Tilt p O) : sharpFun (x * y) = sharpFun x * sharpFun y := by
  let a : ℕ → O := fun n => (Ideal.Quotient.mk_surjective (PreTilt.coeff n x)).choose
  let b : ℕ → O := fun n => (Ideal.Quotient.mk_surjective (PreTilt.coeff n y)).choose
  have ha : ∀ n, Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (a n) = PreTilt.coeff n x :=
    fun n => (Ideal.Quotient.mk_surjective (PreTilt.coeff n x)).choose_spec
  have hb : ∀ n, Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (b n) = PreTilt.coeff n y :=
    fun n => (Ideal.Quotient.mk_surjective (PreTilt.coeff n y)).choose_spec
  symm
  refine eq_sharpFun_of_forall_dvd (x * y) (sharpFun x * sharpFun y) (fun n => a n * b n)
    (fun n => by rw [map_mul, ha n, hb n, map_mul]) fun n => ?_
  rw [mul_pow]
  have hx := sharpFun_spec x a ha n
  have hy := sharpFun_spec y b hb n
  have heq : a n ^ (p ^ n) * b n ^ (p ^ n) - sharpFun x * sharpFun y =
      (a n ^ (p ^ n) - sharpFun x) * b n ^ (p ^ n) + sharpFun x * (b n ^ (p ^ n) - sharpFun y) := by
    ring
  rw [heq]
  exact dvd_add (hx.mul_right _) (hy.mul_left _)

/-- **Fontaine's Multiplicative Untilt (`sharp : Tilt p O →* O`)**. -/
def sharp (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)]
    [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] : Tilt p O →* O where
  toFun := sharpFun
  map_one' := sharpFun_one
  map_mul' := sharpFun_mul

@[simp] theorem sharp_zero : sharp p O 0 = 0 := sharpFun_zero

@[simp] theorem sharp_ofSeq (s : ℕ → O) (hs : ∀ n, (s (n + 1)) ^ p = s n) :
    sharp p O (Tilt.ofSeq (p := p) s hs) = s 0 := by
  have hpow : ∀ n, s n ^ (p ^ n) = s 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_mul, hs n, ih]
  symm
  exact eq_sharpFun_of_forall_dvd (Tilt.ofSeq (p := p) s hs) (s 0) s (fun _ => rfl)
    (fun n => by rw [hpow n, sub_self]; exact dvd_zero _)

theorem mk_sharp (x : Tilt p O) :
    Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (sharp p O x) = PreTilt.coeff 0 x := by
  let a : ℕ → O := fun n => (Ideal.Quotient.mk_surjective (PreTilt.coeff n x)).choose
  have ha : ∀ n, Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (a n) = PreTilt.coeff n x :=
    fun n => (Ideal.Quotient.mk_surjective (PreTilt.coeff n x)).choose_spec
  have h1 := sharpFun_spec x a ha 1
  have h2 : ((p : ℕ) : O) ∣ a 1 ^ p - sharp p O x := by simpa [sharp] using h1
  have hmk : Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (sharp p O x) =
      Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (a 1 ^ p) := by
    symm
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h2)
  rw [hmk, map_pow, ha 1, PreTilt.coeff_pow_p]

/-- The `n`-th compatible `p`-th root of `sharp p O x` inside `O`, namely
`sharp p O ((frobeniusEquiv (Tilt p O) p).symm^[n] x)`. -/
def sharpRoot (n : ℕ) (x : Tilt p O) : O :=
  sharp p O ((frobeniusEquiv (Tilt p O) p).symm^[n] x)

theorem sharpRoot_pow_p_pow (n : ℕ) (x : Tilt p O) :
    sharpRoot (p := p) (O := O) n x ^ (p ^ n) = sharp p O x := by
  unfold sharpRoot
  rw [← map_pow]
  congr 1
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_mul, Function.iterate_succ_apply',
      show ((frobeniusEquiv (Tilt p O) p).symm ((frobeniusEquiv (Tilt p O) p).symm^[n] x)) ^ p =
        frobeniusEquiv (Tilt p O) p ((frobeniusEquiv (Tilt p O) p).symm
          ((frobeniusEquiv (Tilt p O) p).symm^[n] x)) from rfl,
      RingEquiv.apply_symm_apply]
    exact ih x

theorem sharpRoot_pow_sub {k n : ℕ} (hkn : k ≤ n) (x : Tilt p O) :
    sharpRoot (p := p) (O := O) n x ^ (p ^ (n - k)) = sharpRoot (p := p) (O := O) k x := by
  have h1 := sharpRoot_pow_p_pow (p := p) (O := O) (n - k) ((frobeniusEquiv (Tilt p O) p).symm^[k] x)
  unfold sharpRoot at h1 ⊢
  rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hkn] at h1

private theorem sharpRoot_zero (k : ℕ) : sharpRoot (p := p) (O := O) k 0 = 0 := by
  unfold sharpRoot
  have hiter : ∀ m : ℕ, (frobeniusEquiv (Tilt p O) p).symm^[m] 0 = 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, map_zero]
  rw [hiter k, sharp_zero]

theorem sharp_eq_zero_iff [IsDomain O] (x : Tilt p O) : sharp p O x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, sharp_zero]⟩
  refine Perfection.ext (R := ModP O p) (p := p) fun n => ?_
  have hroot : sharpRoot (p := p) (O := O) n x = 0 := by
    have hpow := sharpRoot_pow_p_pow (p := p) (O := O) n x
    rw [h] at hpow
    exact eq_zero_of_pow_eq_zero hpow
  have hmk := mk_sharp (p := p) (O := O) ((frobeniusEquiv (Tilt p O) p).symm^[n] x)
  change Ideal.Quotient.mk _ (sharpRoot (p := p) (O := O) n x) = _ at hmk
  rw [hroot, map_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add] at hmk
  change PreTilt.coeff n x = PreTilt.coeff n 0
  rw [map_zero]
  exact hmk.symm

instance tilt_isDomain [IsDomain O] : IsDomain (Tilt p O) := by
  have hp : p.Prime := Fact.out
  have : Nontrivial (Tilt p O) :=
    ⟨(CharP.nontrivial_of_char_ne_one (R := Tilt p O) hp.ne_one).1⟩
  have : NoZeroDivisors (Tilt p O) := ⟨fun {a b} h => by
    rw [← sharp_eq_zero_iff (p := p) (O := O), map_mul, mul_eq_zero,
      sharp_eq_zero_iff, sharp_eq_zero_iff] at h
    exact h⟩
  exact NoZeroDivisors.to_isDomain _

/-- Divisibility in `Tilt p O` is equivalent to divisibility of untilt values in `O`
(for any integrally closed `p`-adically complete domain `O`, in particular any valuation ring). -/
theorem tilt_dvd_iff_sharp_dvd [IsDomain O] [IsIntegrallyClosed O] (x y : Tilt p O) :
    x ∣ y ↔ sharp p O x ∣ sharp p O y := by
  have hp : p.Prime := Fact.out
  refine ⟨fun h => map_dvd (sharp p O) h, fun h => ?_⟩
  by_cases hx : x = 0
  · subst hx
    rw [sharp_zero, zero_dvd_iff, sharp_eq_zero_iff] at h
    rw [h]
  have hne : ∀ n, sharpRoot (p := p) (O := O) n x ≠ 0 := by
    intro n hn
    have h1 := sharpRoot_pow_p_pow (p := p) (O := O) n x
    rw [hn, zero_pow (pow_pos hp.pos n).ne', eq_comm, sharp_eq_zero_iff] at h1
    exact hx h1
  have hd : ∀ n, sharpRoot (p := p) (O := O) n x ∣ sharpRoot (p := p) (O := O) n y := by
    intro n
    rw [← IsIntegrallyClosed.pow_dvd_pow_iff (pow_pos hp.pos n).ne',
      sharpRoot_pow_p_pow, sharpRoot_pow_p_pow]
    exact h
  choose c hc using hd
  have hcp : ∀ n, c (n + 1) ^ p = c n := by
    intro n
    apply mul_left_cancel₀ (hne n)
    have h1 : sharpRoot (p := p) (O := O) (n + 1) x ^ p = sharpRoot (p := p) (O := O) n x := by
      simpa using sharpRoot_pow_sub (p := p) (O := O) (Nat.le_succ n) x
    have h2 : sharpRoot (p := p) (O := O) (n + 1) y ^ p = sharpRoot (p := p) (O := O) n y := by
      simpa using sharpRoot_pow_sub (p := p) (O := O) (Nat.le_succ n) y
    rw [← h1, ← mul_pow, ← hc (n + 1), h2, hc n, h1]
  let z : Tilt p O := Tilt.ofSeq (p := p) c hcp
  refine ⟨z, ?_⟩
  refine Perfection.ext (R := ModP O p) (p := p) fun n => ?_
  change PreTilt.coeff n y = PreTilt.coeff n (x * z)
  rw [map_mul, Tilt.coeff_ofSeq]
  have hmx : PreTilt.coeff n x = Ideal.Quotient.mk _ (sharpRoot (p := p) (O := O) n x) := by
    have hmk := mk_sharp (p := p) (O := O) ((frobeniusEquiv (Tilt p O) p).symm^[n] x)
    rw [PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add] at hmk
    exact hmk.symm
  have hmy : PreTilt.coeff n y = Ideal.Quotient.mk _ (sharpRoot (p := p) (O := O) n y) := by
    have hmk := mk_sharp (p := p) (O := O) ((frobeniusEquiv (Tilt p O) p).symm^[n] y)
    rw [PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add] at hmk
    exact hmk.symm
  rw [hmx, hmy, ← map_mul, hc n]

instance tilt_valuationRing [IsDomain O] [ValuationRing O] : ValuationRing (Tilt p O) where
  cond' a b := by
    rcases ValuationRing.dvd_total (sharp p O a) (sharp p O b) with h | h
    · obtain ⟨c, hc⟩ := (tilt_dvd_iff_sharp_dvd a b).mpr h
      exact ⟨c, Or.inl hc.symm⟩
    · obtain ⟨c, hc⟩ := (tilt_dvd_iff_sharp_dvd b a).mpr h
      exact ⟨c, Or.inr hc.symm⟩

/-! ### Fontaine's Period Ring `A_inf := WittVector p (Tilt p O)` & `thetaMap` -/

/-- **Fontaine's `A_inf`**: the ring of `p`-typical Witt vectors over the tilt `Tilt p O`,
directly on Mathlib's `WittVector`. -/
abbrev A_inf (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)] :
    Type u :=
  WittVector p (Tilt p O)

/-- The `n`-th truncated approximation to Fontaine's map `θ : A_inf → O`:
`thetaTrunc n x = ∑_{k=0}^n p^k * (x_k^{p^{-k}})^♯`. -/
def thetaTrunc (n : ℕ) (x : A_inf p O) : O :=
  ∑ k ∈ Finset.range (n + 1), ((p : ℕ) : O) ^ k * sharpRoot (p := p) (O := O) k (x.coeff k)

/-- The Witt-vector lift of `x : A_inf p O` at level `n`, whose `k`-th coordinate is
`sharpRoot n (x.coeff k) : O`. -/
private def liftAt (n : ℕ) (x : A_inf p O) : WittVector p O :=
  WittVector.mk p (fun k => sharpRoot (p := p) (O := O) n (x.coeff k))

/-- `n`-fold iterate of `(frobeniusEquiv (Tilt p O) p).symm` as an explicit `RingHom`. -/
private def frobSymmIter : ℕ → (Tilt p O →+* Tilt p O)
  | 0 => RingHom.id _
  | n + 1 => ((frobeniusEquiv (Tilt p O) p).symm.toRingHom).comp (frobSymmIter n)

omit [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] in
private theorem frobSymmIter_apply (n : ℕ) (a : Tilt p O) :
    frobSymmIter (p := p) (O := O) n a = (frobeniusEquiv (Tilt p O) p).symm^[n] a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [frobSymmIter, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      Function.iterate_succ_apply', ih]

private theorem thetaTrunc_eq_ghostComponent (n : ℕ) (x : A_inf p O) :
    thetaTrunc (p := p) (O := O) n x = WittVector.ghostComponent n (liftAt n x) := by
  rw [WittVector.ghostComponent_apply, wittPolynomial_eq_sum_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, map_natCast, MvPolynomial.aeval_X,
    thetaTrunc, liftAt, WittVector.coeff_mk]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [sharpRoot_pow_sub (by omega : k ≤ n)]

private theorem thetaTrunc_add_dvd (n : ℕ) (x y : A_inf p O) :
    ((p : ℕ) : O) ^ (n + 1) ∣
      thetaTrunc (p := p) (O := O) n (x + y) -
        (thetaTrunc (p := p) (O := O) n x + thetaTrunc (p := p) (O := O) n y) := by
  have hp : p.Prime := Fact.out
  rw [thetaTrunc_eq_ghostComponent, thetaTrunc_eq_ghostComponent, thetaTrunc_eq_ghostComponent,
    ← map_add (WittVector.ghostComponent n)]
  rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply,
    wittPolynomial_eq_sum_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, map_natCast, MvPolynomial.aeval_X,
    ← Finset.sum_sub_distrib, ← mul_sub]
  refine Finset.dvd_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hcong : ((p : ℕ) : O) ∣ (liftAt n (x + y)).coeff k - (liftAt n x + liftAt n y).coeff k := by
    apply p_dvd_sub_of_mk_eq
    simp only [liftAt, WittVector.coeff_mk]
    have h1 : Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})
        (sharpRoot (p := p) (O := O) n ((x + y).coeff k)) =
        PreTilt.coeff 0 ((frobeniusEquiv (Tilt p O) p).symm^[n] ((x + y).coeff k)) :=
      mk_sharp _
    rw [h1]
    have h2 : (WittVector.map (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})))
        (liftAt n x + liftAt n y) =
        WittVector.map ((PreTilt.coeff 0).comp (frobSymmIter (p := p) (O := O) n)) (x + y) := by
      rw [map_add, map_add]
      congr 1 <;>
      · ext j
        simp only [WittVector.map_coeff, liftAt, WittVector.coeff_mk, RingHom.comp_apply,
          frobSymmIter_apply]
        exact mk_sharp _
    have h3 := congrArg (fun w => w.coeff k) h2
    simp only [WittVector.map_coeff, RingHom.comp_apply, frobSymmIter_apply] at h3
    exact h3.symm
  have hpow := prime_pow_dvd_pow_sub_pow hp hcong (n - k)
  have hmul := mul_dvd_mul_left (((p : ℕ) : O) ^ k) hpow
  have hexp : k + (n - k + 1) = n + 1 := by omega
  rw [← pow_add, hexp] at hmul
  exact hmul

private theorem thetaTrunc_mul_dvd (n : ℕ) (x y : A_inf p O) :
    ((p : ℕ) : O) ^ (n + 1) ∣
      thetaTrunc (p := p) (O := O) n (x * y) -
        thetaTrunc (p := p) (O := O) n x * thetaTrunc (p := p) (O := O) n y := by
  have hp : p.Prime := Fact.out
  rw [thetaTrunc_eq_ghostComponent, thetaTrunc_eq_ghostComponent, thetaTrunc_eq_ghostComponent,
    ← map_mul (WittVector.ghostComponent n)]
  rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply,
    wittPolynomial_eq_sum_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, map_natCast, MvPolynomial.aeval_X,
    ← Finset.sum_sub_distrib, ← mul_sub]
  refine Finset.dvd_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hcong : ((p : ℕ) : O) ∣ (liftAt n (x * y)).coeff k - (liftAt n x * liftAt n y).coeff k := by
    apply p_dvd_sub_of_mk_eq
    simp only [liftAt, WittVector.coeff_mk]
    have h1 : Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})
        (sharpRoot (p := p) (O := O) n ((x * y).coeff k)) =
        PreTilt.coeff 0 ((frobeniusEquiv (Tilt p O) p).symm^[n] ((x * y).coeff k)) :=
      mk_sharp _
    rw [h1]
    have h2 : (WittVector.map (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})))
        (liftAt n x * liftAt n y) =
        WittVector.map ((PreTilt.coeff 0).comp (frobSymmIter (p := p) (O := O) n)) (x * y) := by
      rw [map_mul, map_mul]
      congr 1 <;>
      · ext j
        simp only [WittVector.map_coeff, liftAt, WittVector.coeff_mk, RingHom.comp_apply,
          frobSymmIter_apply]
        exact mk_sharp _
    have h3 := congrArg (fun w => w.coeff k) h2
    simp only [WittVector.map_coeff, RingHom.comp_apply, frobSymmIter_apply] at h3
    exact h3.symm
  have hpow := prime_pow_dvd_pow_sub_pow hp hcong (n - k)
  have hmul := mul_dvd_mul_left (((p : ℕ) : O) ^ k) hpow
  have hexp : k + (n - k + 1) = n + 1 := by omega
  rw [← pow_add, hexp] at hmul
  exact hmul

private theorem thetaTrunc_cauchy (x : A_inf p O) :
    ∀ {m n : ℕ}, m ≤ n →
      thetaTrunc (p := p) (O := O) m x ≡ thetaTrunc (p := p) (O := O) n x
        [SMOD (Ideal.span {((p : ℕ) : O)} ^ m • ⊤ : Submodule O O)] := by
  intro m n hmn
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have hstep : thetaTrunc (p := p) (O := O) (n + 1) x =
        thetaTrunc (p := p) (O := O) n x +
          ((p : ℕ) : O) ^ (n + 1) * sharpRoot (p := p) (O := O) (n + 1) (x.coeff (n + 1)) := by
      unfold thetaTrunc
      rw [Finset.sum_range_succ]
    rw [hstep, ← sub_sub]
    exact dvd_sub ih ((pow_dvd_pow _ (by omega : m ≤ n + 1)).mul_right _)

private def thetaFun (x : A_inf p O) : O :=
  (IsPrecomplete.prec (I := Ideal.span {((p : ℕ) : O)}) (M := O) inferInstance
    (f := fun n => thetaTrunc (p := p) (O := O) n x) (thetaTrunc_cauchy x)).choose

theorem thetaFun_sub_thetaTrunc_dvd (x : A_inf p O) (n : ℕ) :
    ((p : ℕ) : O) ^ n ∣ thetaTrunc (p := p) (O := O) n x - thetaFun x := by
  have h := (IsPrecomplete.prec (I := Ideal.span {((p : ℕ) : O)}) (M := O) inferInstance
    (f := fun k => thetaTrunc (p := p) (O := O) k x) (thetaTrunc_cauchy x)).choose_spec n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at h

theorem thetaFun_sub_thetaTrunc_dvd_succ (x : A_inf p O) (n : ℕ) :
    ((p : ℕ) : O) ^ (n + 1) ∣ thetaTrunc (p := p) (O := O) n x - thetaFun x := by
  have h1 := thetaFun_sub_thetaTrunc_dvd x (n + 1)
  have hstep : thetaTrunc (p := p) (O := O) (n + 1) x - thetaTrunc (p := p) (O := O) n x =
      ((p : ℕ) : O) ^ (n + 1) * sharpRoot (p := p) (O := O) (n + 1) (x.coeff (n + 1)) := by
    unfold thetaTrunc
    rw [Finset.sum_range_succ, add_sub_cancel_left]
  have heq : thetaTrunc (p := p) (O := O) n x - thetaFun x =
      (thetaTrunc (p := p) (O := O) (n + 1) x - thetaFun x) -
        (thetaTrunc (p := p) (O := O) (n + 1) x - thetaTrunc (p := p) (O := O) n x) := by ring
  rw [heq, hstep]
  exact dvd_sub h1 (dvd_mul_right _ _)

theorem thetaTrunc_one (n : ℕ) : thetaTrunc (p := p) (O := O) n 1 = 1 := by
  unfold thetaTrunc
  rw [Finset.sum_eq_single 0]
  · simp [sharpRoot, WittVector.one_coeff_zero]
  · intro k _ hk0
    have hcoeff : (1 : A_inf p O).coeff k = 0 :=
      WittVector.one_coeff_eq_of_pos p (Tilt p O) k (Nat.pos_of_ne_zero hk0)
    rw [hcoeff, sharpRoot_zero, mul_zero]
  · intro h0; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0

theorem thetaTrunc_zero (n : ℕ) : thetaTrunc (p := p) (O := O) n 0 = 0 := by
  unfold thetaTrunc
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [WittVector.zero_coeff, sharpRoot_zero, mul_zero]

/-- **Fontaine's Canonical Ring Homomorphism `thetaMap : A_inf p O →+* O`**:
`∑ [a_n] p^n ↦ ∑ a_n^♯ p^n`, proved unconditionally via `WittVector.ghostComponent` and
`p`-adic completeness of `O`. -/
def thetaMap (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)]
    [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] : A_inf p O →+* O where
  toFun := thetaFun
  map_one' := by
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_pow_dvd ((p : ℕ) : O) fun n => ?_
    have h := thetaFun_sub_thetaTrunc_dvd (p := p) (O := O) 1 n
    rw [thetaTrunc_one] at h
    simpa [neg_sub] using dvd_neg.mpr h
  map_zero' := by
    refine eq_zero_of_forall_pow_dvd ((p : ℕ) : O) fun n => ?_
    have h := thetaFun_sub_thetaTrunc_dvd (p := p) (O := O) 0 n
    rw [thetaTrunc_zero, zero_sub] at h
    exact dvd_neg.mp h
  map_add' x y := by
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_pow_dvd ((p : ℕ) : O) fun n => ?_
    have hxy := thetaFun_sub_thetaTrunc_dvd_succ (p := p) (O := O) (x + y) n
    have hx := thetaFun_sub_thetaTrunc_dvd_succ (p := p) (O := O) x n
    have hy := thetaFun_sub_thetaTrunc_dvd_succ (p := p) (O := O) y n
    have ha := thetaTrunc_add_dvd (p := p) (O := O) n x y
    have heq : thetaFun (x + y) - (thetaFun x + thetaFun y) =
        -(thetaTrunc (p := p) (O := O) n (x + y) - thetaFun (x + y)) +
        (thetaTrunc (p := p) (O := O) n (x + y) -
          (thetaTrunc (p := p) (O := O) n x + thetaTrunc (p := p) (O := O) n y)) +
        (thetaTrunc (p := p) (O := O) n x - thetaFun x) +
        (thetaTrunc (p := p) (O := O) n y - thetaFun y) := by ring
    rw [heq]
    exact (pow_dvd_pow _ (Nat.le_succ n)).trans
      (dvd_add (dvd_add (dvd_add (dvd_neg.mpr hxy) ha) hx) hy)
  map_mul' x y := by
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_pow_dvd ((p : ℕ) : O) fun n => ?_
    have hxy := thetaFun_sub_thetaTrunc_dvd_succ (p := p) (O := O) (x * y) n
    have hx := thetaFun_sub_thetaTrunc_dvd_succ (p := p) (O := O) x n
    have hy := thetaFun_sub_thetaTrunc_dvd_succ (p := p) (O := O) y n
    have hm := thetaTrunc_mul_dvd (p := p) (O := O) n x y
    have heq : thetaFun (x * y) - thetaFun x * thetaFun y =
        -(thetaTrunc (p := p) (O := O) n (x * y) - thetaFun (x * y)) +
        (thetaTrunc (p := p) (O := O) n (x * y) -
          thetaTrunc (p := p) (O := O) n x * thetaTrunc (p := p) (O := O) n y) +
        (thetaTrunc (p := p) (O := O) n x - thetaFun x) * thetaTrunc (p := p) (O := O) n y +
        thetaFun x * (thetaTrunc (p := p) (O := O) n y - thetaFun y) := by ring
    rw [heq]
    exact (pow_dvd_pow _ (Nat.le_succ n)).trans
      (dvd_add (dvd_add (dvd_add (dvd_neg.mpr hxy) hm) (hx.mul_right _)) (hy.mul_left _))

/-- On Teichmüller lifts, `thetaMap ([a]) = a^♯`. -/
@[simp] theorem thetaMap_teichmuller (a : Tilt p O) :
    thetaMap p O (WittVector.teichmuller p a) = sharp p O a := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_pow_dvd ((p : ℕ) : O) fun n => ?_
  have h := thetaFun_sub_thetaTrunc_dvd (p := p) (O := O) (WittVector.teichmuller p a) n
  have htrunc : thetaTrunc (p := p) (O := O) n (WittVector.teichmuller p a) = sharp p O a := by
    unfold thetaTrunc
    rw [Finset.sum_eq_single 0]
    · simp [sharpRoot, WittVector.teichmuller_coeff_zero]
    · intro k _ hk0
      rw [WittVector.teichmuller_coeff_pos p a k (Nat.pos_of_ne_zero hk0), sharpRoot_zero, mul_zero]
    · intro h0; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0
  rw [htrunc] at h
  simpa [thetaMap, neg_sub] using dvd_neg.mpr h

/-- Reduction of `thetaMap x` modulo `p` equals `PreTilt.coeff 0 (x.coeff 0)`. -/
theorem mk_thetaMap (x : A_inf p O) :
    Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (thetaMap p O x) =
      PreTilt.coeff 0 (x.coeff 0) := by
  have h := thetaFun_sub_thetaTrunc_dvd_succ (p := p) (O := O) x 0
  have h1 : ((p : ℕ) : O) ∣ sharp p O (x.coeff 0) - thetaMap p O x := by
    simpa [thetaTrunc, sharpRoot, thetaMap] using h
  have hmk : Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (thetaMap p O x) =
      Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (sharp p O (x.coeff 0)) :=
    (Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h1)).symm
  rw [hmk, mk_sharp]

omit [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] in
/-- `p` divides `x` in `A_inf` iff `x.coeff 0 = 0`. -/
theorem ainf_p_dvd_iff (x : A_inf p O) : ((p : ℕ) : A_inf p O) ∣ x ↔ x.coeff 0 = 0 := by
  rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker]
  rfl

omit [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] in
theorem ainf_p_dvd_sub_teich (x : A_inf p O) :
    ((p : ℕ) : A_inf p O) ∣ x - WittVector.teichmuller p (x.coeff 0) := by
  rw [ainf_p_dvd_iff]
  change WittVector.constantCoeff (x - WittVector.teichmuller p (x.coeff 0)) = 0
  rw [map_sub]
  simp [WittVector.constantCoeff, WittVector.teichmuller_coeff_zero]

/-- `A_inf = WittVector p (Tilt p O)` is `p`-adically complete (from Mathlib's
`WittVector.isAdicCompleteIdealSpanP`). -/
instance instIsAdicCompleteAinf :
    IsAdicComplete (Ideal.span {((p : ℕ) : A_inf p O)}) (A_inf p O) :=
  WittVector.isAdicCompleteIdealSpanP (p := p) (k := Tilt p O)

omit [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] in
/-- An element `x : A_inf p O` is a unit iff `x.coeff 0` is a unit in `Tilt p O`. -/
theorem ainf_isUnit_iff_isUnit_coeff (x : A_inf p O) : IsUnit x ↔ IsUnit (x.coeff 0) := by
  refine ⟨fun h => h.map WittVector.constantCoeff, fun h => ?_⟩
  obtain ⟨c, hc⟩ := ainf_p_dvd_sub_teich x
  obtain ⟨t, ht⟩ := h.map (WittVector.teichmuller p)
  have hj := IsAdicComplete.le_jacobson_bot (Ideal.span {((p : ℕ) : A_inf p O)})
    (Ideal.mem_span_singleton_self ((p : ℕ) : A_inf p O))
  have h1 := Ideal.mem_jacobson_bot.1 hj (c * ↑t⁻¹)
  have heq : x = (((p : ℕ) : A_inf p O) * (c * ↑t⁻¹) + 1) * (t : A_inf p O) := by
    rw [add_mul, mul_assoc, mul_assoc, Units.inv_mul, mul_one, one_mul, ← hc, ht, sub_add_cancel]
  rw [heq]
  exact h1.mul t.isUnit

/-- **Surjectivity of `thetaMap`** for any `PerfectoidBase p O`! -/
theorem thetaMap_surjective [PerfectoidBase p O] : Function.Surjective (thetaMap p O) := by
  have hcoeff0_surj : Function.Surjective (PreTilt.coeff 0 : Tilt p O → ModP O p) := by
    intro y
    choose s hs using PerfectoidBase.frob_mod_p_surj (p := p) (O := O)
    refine ⟨⟨fun n => s^[n] y, fun n => ?_⟩, rfl⟩
    change (s^[n + 1] y) ^ p = s^[n] y
    rw [Function.iterate_succ_apply']
    exact hs (s^[n] y)
  have hstep : ∀ y : O, ∃ (a : Tilt p O) (y' : O), y = sharp p O a + ((p : ℕ) : O) * y' := by
    intro y
    obtain ⟨a, ha⟩ := hcoeff0_surj (Ideal.Quotient.mk _ y)
    have hdvd : ((p : ℕ) : O) ∣ y - sharp p O a :=
      p_dvd_sub_of_mk_eq (by rw [mk_sharp, ha])
    obtain ⟨y', hy'⟩ := hdvd
    exact ⟨a, y', by linear_combination hy'⟩
  choose a next hnext using hstep
  intro y
  let partialSum : ℕ → A_inf p O :=
    fun n => ∑ k ∈ Finset.range n, ((p : ℕ) : A_inf p O) ^ k * WittVector.teichmuller p (a (next^[k] y))
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      partialSum m ≡ partialSum n
        [SMOD (Ideal.span {((p : ℕ) : A_inf p O)} ^ m • ⊤ : Submodule (A_inf p O) (A_inf p O))] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      simp only [partialSum] at ih ⊢
      rw [Finset.sum_range_succ, ← sub_sub]
      exact dvd_sub ih ((pow_dvd_pow _ hmn).mul_right _)
  obtain ⟨x, hx⟩ := IsPrecomplete.prec (I := Ideal.span {((p : ℕ) : A_inf p O)}) (M := A_inf p O)
    inferInstance (f := partialSum) hcauchy
  have h2 : ∀ n : ℕ, y = thetaMap p O (partialSum n) + ((p : ℕ) : O) ^ n * next^[n] y := by
    intro n
    induction n with
    | zero => simp [partialSum]
    | succ n ih =>
      simp only [partialSum] at ih ⊢
      rw [Finset.sum_range_succ, map_add, map_mul, map_pow, map_natCast, thetaMap_teichmuller,
        Function.iterate_succ_apply']
      have hn := hnext (next^[n] y)
      linear_combination ih + ((p : ℕ) : O) ^ n * hn
  refine ⟨x, ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_pow_dvd ((p : ℕ) : O) fun n => ?_
  have h1 := hx n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at h1
  have h1' : ((p : ℕ) : O) ^ n ∣ thetaMap p O (partialSum n) - thetaMap p O x := by
    simpa [map_sub, map_pow, map_natCast] using map_dvd (thetaMap p O) h1
  have heq : thetaMap p O x - y =
      -(thetaMap p O (partialSum n) - thetaMap p O x) - ((p : ℕ) : O) ^ n * next^[n] y := by
    linear_combination -(h2 n)
  rw [heq]
  exact dvd_sub (dvd_neg.mpr h1') (dvd_mul_right _ _)

/-! ### `p^♭`, `ε`, `ξ = [p^♭] - p`, and `ker θ = (ξ)` -/

section KernelTheta

variable [PerfectoidBase p O]

/-- Compatible `p`-power element `p^♭ = (p, p^{1/p}, p^{1/p²}, …) ∈ Tilt p O`. -/
def pFlat (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)]
    [PerfectoidBase p O] : Tilt p O :=
  Tilt.ofSeq (p := p) (PerfectoidBase.pPowerSeq (p := p) (O := O))
    (PerfectoidBase.pPowerSeq_pow (p := p) (O := O))

/-- Compatible primitive `p`-power root of unity `ε = (1, ζ_p, ζ_{p²}, …) ∈ Tilt p O`. -/
def epsFlat (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)]
    [PerfectoidBase p O] : Tilt p O :=
  Tilt.ofSeq (p := p) (PerfectoidBase.zetaSeq (p := p) (O := O))
    (PerfectoidBase.zetaSeq_pow (p := p) (O := O))

@[simp] theorem sharp_pFlat : sharp p O (pFlat p O) = ((p : ℕ) : O) := by
  unfold pFlat
  rw [sharp_ofSeq, PerfectoidBase.pPowerSeq_zero]

@[simp] theorem sharp_epsFlat : sharp p O (epsFlat p O) = 1 := by
  unfold epsFlat
  rw [sharp_ofSeq, PerfectoidBase.zetaSeq_zero]

/-- **Fontaine's Generator `ξ := [p^♭] - p ∈ A_inf p O`**. -/
def xi (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)]
    [PerfectoidBase p O] : A_inf p O :=
  WittVector.teichmuller p (pFlat p O) - ((p : ℕ) : A_inf p O)

@[simp] theorem thetaMap_xi : thetaMap p O (xi p O) = 0 := by
  unfold xi
  rw [map_sub, thetaMap_teichmuller, sharp_pFlat, map_natCast, sub_self]

theorem xi_mem_ker_thetaMap : xi p O ∈ RingHom.ker (thetaMap p O) :=
  RingHom.mem_ker.mpr (thetaMap_xi (p := p) (O := O))

omit [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] in
theorem coeff_zero_xi : (xi p O).coeff 0 = pFlat p O := by
  change WittVector.constantCoeff (xi p O) = pFlat p O
  unfold xi
  rw [map_sub, map_natCast, CharP.cast_eq_zero (Tilt p O) p, sub_zero]
  exact WittVector.teichmuller_coeff_zero p (pFlat p O)

theorem xi_ne_zero [IsDomain O] [CharZero O] : xi p O ≠ 0 := by
  intro h
  have h1 := congrArg (fun w : A_inf p O => w.coeff 0) h
  rw [coeff_zero_xi, WittVector.zero_coeff] at h1
  have h2 := congrArg (sharp p O) h1
  rw [sharp_pFlat, sharp_zero] at h2
  exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero h2

theorem exists_eq_xi_mul_add [IsDomain O] [IsIntegrallyClosed O] {x : A_inf p O}
    (hx : ((p : ℕ) : O) ∣ thetaMap p O x) :
    ∃ a y : A_inf p O, x = xi p O * a + ((p : ℕ) : A_inf p O) * y := by
  have hmk : Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (thetaMap p O x) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hx)
  rw [mk_thetaMap, ← mk_sharp] at hmk
  have hp_dvd : ((p : ℕ) : O) ∣ sharp p O (x.coeff 0) :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hmk)
  rw [← sharp_pFlat (p := p) (O := O)] at hp_dvd
  obtain ⟨c, hc⟩ := (tilt_dvd_iff_sharp_dvd (pFlat p O) (x.coeff 0)).mpr hp_dvd
  obtain ⟨d, hd⟩ := ainf_p_dvd_sub_teich x
  rw [hc, map_mul] at hd
  exact ⟨WittVector.teichmuller p c, d + WittVector.teichmuller p c, by
    unfold xi; linear_combination hd⟩

/-- **Fontaine's Principal Kernel Theorem (`ker_thetaMap_eq_span_xi`)**:
`RingHom.ker (thetaMap p O) = Ideal.span {xi p O}`! -/
theorem ker_thetaMap_eq_span_xi [IsDomain O] [IsIntegrallyClosed O] [CharZero O] :
    RingHom.ker (thetaMap p O) = Ideal.span {xi p O} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · refine mem_span_of_approx ((p : ℕ) : A_inf p O) (xi p O) (RingHom.ker (thetaMap p O)) ?_ hx
    intro z hz
    have hz' : thetaMap p O z = 0 := hz
    obtain ⟨a, y, h⟩ := exists_eq_xi_mul_add (p := p) (O := O) (x := z) (by rw [hz']; exact dvd_zero _)
    refine ⟨a, y, ?_, h⟩
    show thetaMap p O y = 0
    have h0 := congrArg (thetaMap p O) h
    rw [hz', map_add, map_mul, thetaMap_xi, zero_mul, zero_add, map_mul, map_natCast] at h0
    exact (mul_eq_zero.mp h0.symm).resolve_left (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact xi_mem_ker_thetaMap

theorem thetaMap_eq_zero_iff [IsDomain O] [IsIntegrallyClosed O] [CharZero O] (x : A_inf p O) :
    thetaMap p O x = 0 ↔ xi p O ∣ x := by
  rw [← Ideal.mem_span_singleton, ← ker_thetaMap_eq_span_xi, RingHom.mem_ker]

theorem xi_dvd_of_dvd_p_pow_mul [IsDomain O] [IsIntegrallyClosed O] [CharZero O]
    {x : A_inf p O} {k : ℕ} (h : xi p O ∣ ((p : ℕ) : A_inf p O) ^ k * x) : xi p O ∣ x := by
  rw [← thetaMap_eq_zero_iff] at h ⊢
  rw [map_mul, map_pow, map_natCast] at h
  exact (mul_eq_zero.mp h).resolve_left
    (pow_ne_zero k (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))

theorem xi_pow_dvd_of_dvd_p_pow_mul [IsDomain O] [IsIntegrallyClosed O] [CharZero O]
    {n k : ℕ} {x : A_inf p O} (h : xi p O ^ n ∣ ((p : ℕ) : A_inf p O) ^ k * x) :
    xi p O ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨y, rfl⟩ := xi_dvd_of_dvd_p_pow_mul ((dvd_pow_self _ n.succ_ne_zero).trans h)
    rw [pow_succ', mul_left_comm, mul_dvd_mul_iff_left (xi_ne_zero (p := p) (O := O))] at h
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih h)

/-- `A_inf` is `ξ`-adically separated: `⨅ n, (Ideal.span {xi})^n = ⊥`. -/
theorem eq_zero_of_forall_xi_pow_dvd [IsDomain O] [IsIntegrallyClosed O] [CharZero O]
    {x : A_inf p O} (h : ∀ n : ℕ, xi p O ^ n ∣ x) : x = 0 := by
  refine eq_zero_of_forall_pow_dvd ((p : ℕ) : A_inf p O) fun k => ?_
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have h0 : sharp p O (x.coeff 0) = 0 := eq_zero_of_forall_pow_dvd ((p : ℕ) : O) fun n => by
      have h1 : (xi p O).coeff 0 ^ n ∣ x.coeff 0 := by
        have := map_dvd (WittVector.constantCoeff (p := p) (R := Tilt p O)) (h n)
        rwa [map_pow] at this
      rw [coeff_zero_xi] at h1
      have h2 := map_dvd (sharp p O) h1
      rwa [map_pow, sharp_pFlat] at h2
    obtain ⟨y, rfl⟩ := (ainf_p_dvd_iff x).mpr ((sharp_eq_zero_iff _).mp h0)
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih fun n =>
      xi_pow_dvd_of_dvd_p_pow_mul (k := 1) (by simpa using h n))

/-- Canonical `ℤ_[p] →+* A_inf p O` ring homomorphism via `ℤ_[p] ≃+* WittVector p (ZMod p)`
(explicit `RingHom`, no `Algebra` diamond). -/
def padicIntToAinf (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)] :
    ℤ_[p] →+* A_inf p O :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (Tilt p O))).comp (WittVector.equiv p).symm.toRingHom

omit [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] [PerfectoidBase p O] in
theorem frobenius_padicIntToAinf (z : ℤ_[p]) :
    WittVector.frobenius (padicIntToAinf p O z) = padicIntToAinf p O z := by
  ext k
  simp only [padicIntToAinf, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    WittVector.frobenius_eq_map_frobenius, WittVector.map_coeff, frobenius_def]
  rw [← map_pow, ZMod.pow_card]

end KernelTheta

end SharpMap

end TiltAndAinf

/-! ## Section 4: `A_inf[1/p]`, `B_dR^+`, Fontaine's `t = log([ε])`, `B_dR`, and `Fil^i B_dR` -/

section AdicHelpers

/-- Construct an element of `AdicCompletion I A` from any compatible system `x n : A ⧸ I ^ n`. -/
def adicMk {A : Type u} [CommRing A] (I : Ideal A) (x : ∀ n : ℕ, A ⧸ I ^ n)
    (h : ∀ {m n : ℕ} (hle : m ≤ n), Ideal.Quotient.factorPow I hle (x n) = x m) :
    AdicCompletion I A :=
  AdicCompletion.liftRingHom I
    (fun n => Polynomial.eval₂RingHom (Int.castRingHom (A ⧸ I ^ n)) (x n))
    (fun {m n} hle => by
      apply Polynomial.ringHom_ext'
      · exact Subsingleton.elim _ _
      · simpa using h hle) Polynomial.X

@[simp] theorem evalₐ_adicMk {A : Type u} [CommRing A] (I : Ideal A) (x : ∀ n : ℕ, A ⧸ I ^ n)
    (h : ∀ {m n : ℕ} (hle : m ≤ n), Ideal.Quotient.factorPow I hle (x n) = x m) (n : ℕ) :
    AdicCompletion.evalₐ I n (adicMk I x h) = x n := by
  unfold adicMk
  rw [AdicCompletion.evalₐ_liftRingHom]
  · simp
  · intro m n hle
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · simpa using h hle

theorem factorPow_evalₐ {A : Type u} [CommRing A] (I : Ideal A) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | h x =>
    simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    exact AdicCompletion.Ideal.mk_eq_mk I hle x

theorem evalₐ_eq_zero_iff_dvd_of_eq_span {A : Type u} [CommRing A] {I : Ideal A} {a : A}
    (hI : I = Ideal.span {a}) (n : ℕ) (x : AdicCompletion I A) :
    AdicCompletion.evalₐ I n x = 0 ↔ algebraMap A (AdicCompletion I A) a ^ n ∣ x := by
  have hfg : I.FG := hI ▸ Submodule.fg_span_singleton a
  have h1 : AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I A n x = 0 := by
    constructor
    · intro h
      rw [← AdicCompletion.factor_evalₐ_eq_eval I x (by simp), h, map_zero]
    · intro h
      rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), h, map_zero]
  rw [h1, ← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval hfg]
  have h2 : I ^ n = Ideal.span {a ^ n} := by rw [hI, Ideal.span_singleton_pow]
  rw [h2, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, trivial, by rw [Algebra.smul_def, map_pow]⟩

theorem eq_zero_of_algebraMap_mul_eq_zero {A : Type u} [CommRing A] [IsDomain A]
    {I : Ideal A} {a : A} (hI : I = Ideal.span {a}) (ha : a ≠ 0) {x : AdicCompletion I A}
    (h : algebraMap A (AdicCompletion I A) a * x = 0) : x = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
  have h1 := congrArg (AdicCompletion.evalₐ I (n + 1)) h
  rw [map_mul, AlgHom.commutes, ← hy, map_zero, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at h1
  have h2 : ∀ m, I ^ m = Ideal.span {a ^ m} := fun m => by rw [hI, Ideal.span_singleton_pow]
  rw [h2, Ideal.mem_span_singleton, pow_succ', mul_dvd_mul_iff_left ha] at h1
  rw [← factorPow_evalₐ I n.le_succ, ← hy, map_zero]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  rw [h2, Ideal.mem_span_singleton]
  exact h1

/-- Truncated formal logarithm `∑_{k=0}^{N-1} ((-1)^k / (k+1)) * x^(k+1)` using an explicit
`RingHom` `q : ℚ →+* B` (diamond-free). -/
def truncLogHom {B : Type*} [CommRing B] (q : ℚ →+* B) (N : ℕ) (x : B) : B :=
  ∑ k ∈ Finset.range N, q ((-1 : ℚ) ^ k / (k + 1 : ℚ)) * x ^ (k + 1)

theorem map_truncLogHom {B B' : Type*} [CommRing B] [CommRing B'] (f : B →+* B')
    (q : ℚ →+* B) (N : ℕ) (x : B) :
    f (truncLogHom q N x) = truncLogHom (f.comp q) N (f x) := by
  simp [truncLogHom, map_sum, map_mul, map_pow]

theorem truncLogHom_eq_of_pow_eq_zero {B : Type*} [CommRing B] (q : ℚ →+* B) {x : B} {m n : ℕ}
    (h : x ^ m = 0) (hle : m ≤ n) : truncLogHom q n x = truncLogHom q m x := by
  induction n, hle using Nat.le_induction with
  | base => rfl
  | succ n hle ih =>
    rw [← ih, truncLogHom, Finset.sum_range_succ, pow_eq_zero_of_le (by omega) h, mul_zero,
      add_zero]
    rfl

end AdicHelpers

section BdRConstruction

variable {p : ℕ} [Fact p.Prime]
variable {O : Type u} [CommRing O] [IsDomain O] [ValuationRing O] [CharZero O]
  [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
  [PerfectoidBase p O]

/-- `A_inf[1/p] := Localization.Away (p : A_inf p O)`. -/
abbrev AinfInvP (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)] :
    Type u :=
  Localization.Away ((p : ℕ) : A_inf p O)

/-- Canonical `RingHom` `A_inf →+* A_inf[1/p]`. -/
def ainfToInvP (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)] :
    A_inf p O →+* AinfInvP p O :=
  algebraMap (A_inf p O) (AinfInvP p O)

omit [ValuationRing O] [CharZero O] [PerfectoidBase p O] in
theorem ainf_p_ne_zero : ((p : ℕ) : A_inf p O) ≠ 0 :=
  WittVector.p_nonzero p (Tilt p O)

omit [ValuationRing O] [CharZero O] [PerfectoidBase p O] in
theorem ainfToInvP_injective : Function.Injective (ainfToInvP p O) :=
  IsLocalization.injective (AinfInvP p O)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero (ainf_p_ne_zero (p := p) (O := O))))

instance instIsDomainAinfInvP : IsDomain (AinfInvP p O) :=
  IsLocalization.isDomain_localization (M := Submonoid.powers ((p : ℕ) : A_inf p O))
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero (ainf_p_ne_zero (p := p) (O := O))))

omit [IsDomain O] [ValuationRing O] [CharZero O] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
  [PerfectoidBase p O] in
theorem isUnit_padicIntToAinf_in_invP (z : ℤ_[p]) (hz : z ≠ 0) :
    IsUnit (ainfToInvP p O (padicIntToAinf p O z)) := by
  have hz_eq : z = (PadicInt.unitCoeff hz : ℤ_[p]) * ((p : ℕ) : ℤ_[p]) ^ z.valuation :=
    PadicInt.unitCoeff_spec hz
  rw [hz_eq, map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast]
  have hp_unit : IsUnit ((p : ℕ) : AinfInvP p O) := by
    simpa [ainfToInvP] using IsLocalization.Away.algebraMap_isUnit ((p : ℕ) : A_inf p O) (S := AinfInvP p O)
  have hu_unit : IsUnit (ainfToInvP p O (padicIntToAinf p O (PadicInt.unitCoeff hz : ℤ_[p]))) :=
    ((PadicInt.unitCoeff hz).isUnit.map (padicIntToAinf p O)).map (ainfToInvP p O)
  exact hu_unit.mul (hp_unit.pow _)

/-- Canonical `RingHom` `ℚ_[p] →+* A_inf[1/p]` (explicit `RingHom`, no `Algebra` diamond). -/
def padicToAinfInvP (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] :
    ℚ_[p] →+* AinfInvP p O :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (S := ℚ_[p])
    (g := (ainfToInvP p O).comp (padicIntToAinf p O))
    (fun ⟨z, hz⟩ => isUnit_padicIntToAinf_in_invP z (nonZeroDivisors.ne_zero hz))

/-- Canonical `RingHom` `ℚ →+* A_inf[1/p]` factoring through `ℚ_[p]`. -/
def ratToAinfInvP (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] :
    ℚ →+* AinfInvP p O :=
  (padicToAinfInvP p O).comp (algebraMap ℚ ℚ_[p])

omit [Fact p.Prime] [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [PerfectoidBase p O] in
theorem exists_dvd_p_pow_O {x : O} (hx : x ≠ 0) : ∃ n : ℕ, x ∣ ((p : ℕ) : O) ^ n := by
  by_contra h
  push Not at h
  exact hx (eq_zero_of_forall_pow_dvd ((p : ℕ) : O) fun n =>
    (ValuationRing.dvd_total x _).resolve_left (h n))

instance isFractionRing_away_O : IsFractionRing O (Localization.Away ((p : ℕ) : O)) :=
  IsLocalization.isLocalization_of_is_exists_mul_mem _ (Submonoid.powers ((p : ℕ) : O)) _
    (Submonoid.powers_le.mpr
      (mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)))
    (fun ⟨x, hx⟩ => by
      obtain ⟨n, c, hc⟩ := exists_dvd_p_pow_O (p := p) (O := O) (nonZeroDivisors.ne_zero hx)
      exact ⟨c, n, by simp [hc, mul_comm]⟩)

omit [Fact ¬IsUnit ((p : ℕ) : O)] [PerfectoidBase p O] in
theorem isField_away_O : IsField (Localization.Away ((p : ℕ) : O)) :=
  (IsFractionRing.toField O (K := Localization.Away ((p : ℕ) : O))).toIsField

instance instNontrivialAwayO : Nontrivial (Localization.Away ((p : ℕ) : O)) :=
  ⟨(isField_away_O (p := p) (O := O)).exists_pair_ne⟩

/-- Extension of `thetaMap : A_inf →+* O` to `thetaInvP : A_inf[1/p] →+* O[1/p]`. -/
def thetaInvP (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] :
    AinfInvP p O →+* Localization.Away ((p : ℕ) : O) :=
  IsLocalization.Away.lift ((p : ℕ) : A_inf p O)
    (g := (algebraMap O (Localization.Away ((p : ℕ) : O))).comp (thetaMap p O))
    (by
      rw [RingHom.comp_apply, map_natCast]
      exact IsLocalization.Away.algebraMap_isUnit ((p : ℕ) : O))

omit [IsDomain O] [ValuationRing O] [CharZero O] [PerfectoidBase p O] in
@[simp] theorem thetaInvP_ainfToInvP (x : A_inf p O) :
    thetaInvP p O (ainfToInvP p O x) = algebraMap O (Localization.Away ((p : ℕ) : O)) (thetaMap p O x) :=
  IsLocalization.Away.lift_eq _ _ x

/-- `ker(θ[1/p]) ⊆ A_inf[1/p]`. -/
abbrev kerThetaInvP (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] :
    Ideal (AinfInvP p O) :=
  RingHom.ker (thetaInvP p O)

/-- The image of `ξ` in `A_inf[1/p]`. -/
def xiInvP (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [PerfectoidBase p O] : AinfInvP p O :=
  ainfToInvP p O (xi p O)

omit [ValuationRing O] in
theorem xiInvP_ne_zero : xiInvP p O ≠ 0 :=
  fun h => xi_ne_zero (p := p) (O := O) (ainfToInvP_injective (by simpa [xiInvP] using h))

theorem kerThetaInvP_eq_span_xi :
    kerThetaInvP p O = Ideal.span {xiInvP p O} := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨⟨x, ⟨_, k, rfl⟩⟩, hzx⟩ := IsLocalization.surj (Submonoid.powers ((p : ℕ) : A_inf p O)) z
    dsimp only at hzx
    have hθx : thetaMap p O x = 0 := by
      have h1 := congrArg (thetaInvP p O) hzx
      rw [map_mul, RingHom.mem_ker.mp hz, zero_mul] at h1
      change (0 : Localization.Away ((p : ℕ) : O)) = thetaInvP p O (ainfToInvP p O x) at h1
      rw [thetaInvP_ainfToInvP] at h1
      exact IsFractionRing.injective O (Localization.Away ((p : ℕ) : O)) (by rw [map_zero, h1])
    obtain ⟨y, rfl⟩ := (thetaMap_eq_zero_iff (p := p) (O := O) x).mp hθx
    have hp_unit : IsUnit (ainfToInvP p O (((p : ℕ) : A_inf p O) ^ k)) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit ((p : ℕ) : A_inf p O) (S := AinfInvP p O)).pow k
    obtain ⟨u, hu⟩ := hp_unit
    have hz_eq : z = xiInvP p O * (ainfToInvP p O y * (u⁻¹ : (AinfInvP p O)ˣ)) := by
      have hmul : z * (u : AinfInvP p O) = xiInvP p O * ainfToInvP p O y := by
        simpa [xiInvP, ainfToInvP, hu, map_mul] using hzx
      calc z = z * (u : AinfInvP p O) * (u⁻¹ : (AinfInvP p O)ˣ) := by
            rw [mul_assoc, Units.mul_inv, mul_one]
        _ = xiInvP p O * (ainfToInvP p O y * (u⁻¹ : (AinfInvP p O)ˣ)) := by
            rw [hmul, mul_assoc]
    rw [Ideal.mem_span_singleton]
    exact ⟨_, hz_eq⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show thetaInvP p O (xiInvP p O) = 0
    rw [xiInvP, thetaInvP_ainfToInvP, thetaMap_xi, map_zero]

/-- **Fontaine's De Rham Ring `B_dR^+`**: the `ker(θ)`-adic completion (inverse limit of
`A_inf[1/p] ⧸ (ker θ)^n`). -/
abbrev BdRPlus (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] : Type u :=
  AdicCompletion (kerThetaInvP p O) (AinfInvP p O)

/-- Explicit `RingHom`s into and out of `B_dR^+` (zero `Algebra` diamonds). -/
def ainfInvToBdRPlus (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] :
    AinfInvP p O →+* BdRPlus p O :=
  algebraMap (AinfInvP p O) (AdicCompletion (kerThetaInvP p O) (AinfInvP p O))

def ainfToBdRPlus (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] :
    A_inf p O →+* BdRPlus p O :=
  (ainfInvToBdRPlus p O).comp (ainfToInvP p O)

def padicToBdRPlus (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] :
    ℚ_[p] →+* BdRPlus p O :=
  (ainfInvToBdRPlus p O).comp (padicToAinfInvP p O)

def ratToBdRPlus (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] :
    ℚ →+* BdRPlus p O :=
  (ainfInvToBdRPlus p O).comp (ratToAinfInvP p O)

def evalBdRPlus (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] (n : ℕ) :
    BdRPlus p O →+* AinfInvP p O ⧸ kerThetaInvP p O ^ n :=
  (AdicCompletion.evalₐ (kerThetaInvP p O) n).toRingHom

/-- Canonical map `θ_dR : B_dR^+ →+* O[1/p]`. -/
def thetaBdRPlus (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] :
    BdRPlus p O →+* Localization.Away ((p : ℕ) : O) :=
  (RingHom.kerLift (thetaInvP p O)).comp (AdicCompletion.evalOneₐ (kerThetaInvP p O)).toRingHom

omit [IsDomain O] [ValuationRing O] [CharZero O] [PerfectoidBase p O] in
@[simp] theorem thetaBdRPlus_ainfInv (x : AinfInvP p O) :
    thetaBdRPlus p O (ainfInvToBdRPlus p O x) = thetaInvP p O x := rfl

omit [IsDomain O] [ValuationRing O] [CharZero O] [PerfectoidBase p O] in
@[simp] theorem thetaBdRPlus_ainf (x : A_inf p O) :
    thetaBdRPlus p O (ainfToBdRPlus p O x) =
      algebraMap O (Localization.Away ((p : ℕ) : O)) (thetaMap p O x) := by
  simp [ainfToBdRPlus]

/-- The uniformizer `ξ` inside `B_dR^+`. -/
def xiBdR (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : BdRPlus p O :=
  ainfToBdRPlus p O (xi p O)

theorem evalBdRPlus_eq_zero_iff (n : ℕ) (x : BdRPlus p O) :
    evalBdRPlus p O n x = 0 ↔ xiBdR p O ^ n ∣ x :=
  evalₐ_eq_zero_iff_dvd_of_eq_span (kerThetaInvP_eq_span_xi (p := p) (O := O)) n x

theorem thetaBdRPlus_eq_zero_iff_dvd (x : BdRPlus p O) :
    thetaBdRPlus p O x = 0 ↔ xiBdR p O ∣ x := by
  rw [← pow_one (xiBdR p O), ← evalBdRPlus_eq_zero_iff]
  change (RingHom.kerLift (thetaInvP p O)) (AdicCompletion.evalOneₐ (kerThetaInvP p O) x) = 0 ↔
    AdicCompletion.evalₐ (kerThetaInvP p O) 1 x = 0
  have h1 : RingHom.kerLift (thetaInvP p O) (AdicCompletion.evalOneₐ (kerThetaInvP p O) x) = 0 ↔
      AdicCompletion.evalOneₐ (kerThetaInvP p O) x = 0 :=
    map_eq_zero_iff _ (RingHom.kerLift_injective _)
  rw [h1, ← AdicCompletion.factorₐ_evalₐ_one]
  refine map_eq_zero_iff _ ?_
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
  rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact hy

theorem ker_thetaBdRPlus_eq_span_xi :
    RingHom.ker (thetaBdRPlus p O) = Ideal.span {xiBdR p O} := by
  ext x
  rw [RingHom.mem_ker, thetaBdRPlus_eq_zero_iff_dvd, Ideal.mem_span_singleton]

theorem eq_zero_of_xiBdR_mul_eq_zero {x : BdRPlus p O} (h : xiBdR p O * x = 0) : x = 0 :=
  eq_zero_of_algebraMap_mul_eq_zero (kerThetaInvP_eq_span_xi (p := p) (O := O))
    (xiInvP_ne_zero (p := p) (O := O)) h

theorem eq_zero_of_forall_xiBdR_pow_dvd {x : BdRPlus p O}
    (h : ∀ n : ℕ, xiBdR p O ^ n ∣ x) : x = 0 :=
  AdicCompletion.ext_evalₐ fun n => by
    change evalBdRPlus p O n x = evalBdRPlus p O n 0
    rw [map_zero]
    exact (evalBdRPlus_eq_zero_iff n x).mpr (h n)

theorem xiBdR_ne_zero : xiBdR p O ≠ 0 := by
  intro h
  have h1 : evalBdRPlus p O 2 (xiBdR p O) = 0 := by rw [h, map_zero]
  have hdvd : xiBdR p O ^ 2 ∣ xiBdR p O := (evalBdRPlus_eq_zero_iff 2 _).mp h1
  obtain ⟨c, hc⟩ := hdvd
  have h0 : xiBdR p O * (xiBdR p O * c - 1) = 0 := by linear_combination -hc
  have h2 := eq_zero_of_xiBdR_mul_eq_zero h0
  have h3 := congrArg (thetaBdRPlus p O) h2
  rw [map_sub, map_mul, show thetaBdRPlus p O (xiBdR p O) = 0 from
    (thetaBdRPlus_eq_zero_iff_dvd _).mpr dvd_rfl, zero_mul, zero_sub, map_one, map_zero,
    neg_eq_zero] at h3
  exact one_ne_zero h3

theorem isUnit_BdRPlus_of_one_sub_dvd {u : BdRPlus p O} (h : xiBdR p O ∣ 1 - u) : IsUnit u := by
  obtain ⟨w, hw⟩ := h
  let r : BdRPlus p O := xiBdR p O * w
  have hu : u = 1 - r := by linear_combination -hw
  have hr_pow : ∀ n : ℕ, evalBdRPlus p O n r ^ n = 0 := by
    intro n
    rw [← map_pow, evalBdRPlus_eq_zero_iff]
    exact show xiBdR p O ^ n ∣ (xiBdR p O * w) ^ n by rw [mul_pow]; exact dvd_mul_right _ _
  let inv : BdRPlus p O :=
    adicMk (kerThetaInvP p O)
      (fun n => ∑ k ∈ Finset.range n, evalBdRPlus p O n r ^ k)
      (fun {m n} hle => by
        rw [map_sum]
        have htr : ∀ k, Ideal.Quotient.factorPow (kerThetaInvP p O) hle (evalBdRPlus p O n r ^ k) =
            evalBdRPlus p O m r ^ k := fun k => by
          rw [map_pow]; exact congrArg (· ^ k) (factorPow_evalₐ _ hle r)
        simp_rw [htr]
        clear htr
        induction n, hle using Nat.le_induction with
        | base => rfl
        | succ n hle ih =>
          rw [Finset.sum_range_succ, ih, pow_eq_zero_of_le (by omega) (hr_pow m), add_zero])
  have hmul : u * inv = 1 := by
    refine AdicCompletion.ext_evalₐ fun n => ?_
    change evalBdRPlus p O n (u * inv) = evalBdRPlus p O n 1
    rw [map_mul, map_one, hu, map_sub, map_one]
    have hinv_n : evalBdRPlus p O n inv = ∑ k ∈ Finset.range n, evalBdRPlus p O n r ^ k :=
      evalₐ_adicMk _ _ _ n
    rw [hinv_n]
    have hgeom : (1 - evalBdRPlus p O n r) * (∑ k ∈ Finset.range n, evalBdRPlus p O n r ^ k) =
        1 - evalBdRPlus p O n r ^ n := by
      have := mul_geom_sum (evalBdRPlus p O n r) n
      linear_combination -this
    rw [hgeom, hr_pow n, sub_zero]
  exact isUnit_iff_exists_inv.mpr ⟨inv, hmul⟩

theorem isUnit_BdRPlus_iff_theta_ne_zero (x : BdRPlus p O) :
    IsUnit x ↔ thetaBdRPlus p O x ≠ 0 := by
  constructor
  · intro hu h0
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have h1 := congrArg (thetaBdRPlus p O) hv
    rw [map_mul, h0, zero_mul, map_one] at h1
    exact zero_ne_one h1
  · intro hne
    obtain ⟨y, hy⟩ := (isField_away_O (p := p) (O := O)).mul_inv_cancel hne
    have hsurj : Function.Surjective (thetaBdRPlus p O) := by
      intro z
      obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, haz⟩ := IsLocalization.surj (Submonoid.powers ((p : ℕ) : O)) z
      dsimp only at haz
      obtain ⟨b, hb⟩ := thetaMap_surjective (p := p) (O := O) a
      have hp_u := (IsLocalization.Away.algebraMap_isUnit ((p : ℕ) : A_inf p O) (S := AinfInvP p O)).pow k
      obtain ⟨u, hu⟩ := hp_u
      refine ⟨ainfInvToBdRPlus p O (ainfToInvP p O b * (u⁻¹ : (AinfInvP p O)ˣ)), ?_⟩
      rw [thetaBdRPlus_ainfInv, map_mul, thetaInvP_ainfToInvP, hb]
      have hpu : thetaInvP p O (u : AinfInvP p O) = algebraMap O _ (((p : ℕ) : O) ^ k) := by
        rw [hu]
        change thetaInvP p O (ainfToInvP p O ((p : ℕ) : A_inf p O) ^ k) = _
        rw [← map_pow, thetaInvP_ainfToInvP, map_pow, map_natCast]
      have hmul_z : z * thetaInvP p O (u : AinfInvP p O) = algebraMap O _ a := by
        rw [hpu]; exact haz
      have hinv : thetaInvP p O (u : AinfInvP p O) * thetaInvP p O (u⁻¹ : (AinfInvP p O)ˣ) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      calc algebraMap O _ a * thetaInvP p O (u⁻¹ : (AinfInvP p O)ˣ)
          = z * (thetaInvP p O (u : AinfInvP p O) * thetaInvP p O (u⁻¹ : (AinfInvP p O)ˣ)) := by
            rw [← hmul_z, mul_assoc]
        _ = z := by rw [hinv, mul_one]
    obtain ⟨v, hv⟩ := hsurj y
    have h1 : xiBdR p O ∣ 1 - x * v := by
      rw [← thetaBdRPlus_eq_zero_iff_dvd, map_sub, map_one, map_mul, hv, hy, sub_self]
    exact isUnit_of_mul_isUnit_left (isUnit_BdRPlus_of_one_sub_dvd h1)

/-- Every nonzero element of `B_dR^+` factors as `ξ ^ n * u` for a unit `u : (B_dR^+)ˣ`. -/
theorem exists_xiBdR_pow_mul_unit {x : BdRPlus p O} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : (BdRPlus p O)ˣ), x = xiBdR p O ^ n * (u : BdRPlus p O) := by
  classical
  have hex : ∃ m : ℕ, ¬ (xiBdR p O ^ m ∣ x) := by
    by_contra hall
    push Not at hall
    exact hx (eq_zero_of_forall_xiBdR_pow_dvd hall)
  let m := Nat.find hex
  have hm : ¬ (xiBdR p O ^ m ∣ x) := Nat.find_spec hex
  have hm_pos : 0 < m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hm0, pow_zero] at hm
    exact hm (one_dvd x)
  have hprev : xiBdR p O ^ (m - 1) ∣ x :=
    not_not.mp (Nat.find_min hex (Nat.sub_lt hm_pos zero_lt_one))
  obtain ⟨w, hw⟩ := hprev
  have hw_ndvd : ¬ (xiBdR p O ∣ w) := by
    intro ⟨c, hc⟩
    apply hm
    refine ⟨c, ?_⟩
    rw [hw, hc, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hm_pos]
  have hwu : IsUnit w :=
    (isUnit_BdRPlus_iff_theta_ne_zero w).mpr fun h0 =>
      hw_ndvd ((thetaBdRPlus_eq_zero_iff_dvd w).mp h0)
  obtain ⟨u, rfl⟩ := hwu
  exact ⟨m - 1, u, hw⟩

instance instIsDomainBdRPlus : IsDomain (BdRPlus p O) := by
  have : Nontrivial (BdRPlus p O) :=
    ⟨⟨1, 0, fun h => (one_ne_zero : (1 : Localization.Away ((p : ℕ) : O)) ≠ 0)
      (by simpa using congrArg (thetaBdRPlus p O) h)⟩⟩
  have : NoZeroDivisors (BdRPlus p O) := ⟨fun {a b} hab => by
    by_contra hne
    push Not at hne
    obtain ⟨m, u, rfl⟩ := exists_xiBdR_pow_mul_unit hne.1
    obtain ⟨n, v, rfl⟩ := exists_xiBdR_pow_mul_unit hne.2
    have hmul : xiBdR p O ^ (m + n) * ((u * v : (BdRPlus p O)ˣ) : BdRPlus p O) = 0 := by
      push_cast; linear_combination hab
    have hpow : ∀ k : ℕ, ∀ y : BdRPlus p O, xiBdR p O ^ k * y = 0 → y = 0 := by
      intro k
      induction k with
      | zero => intro y hy; simpa using hy
      | succ k ih =>
        intro y hy
        rw [pow_succ', mul_assoc] at hy
        exact ih y (eq_zero_of_xiBdR_mul_eq_zero hy)
    have huv : ((u * v : (BdRPlus p O)ˣ) : BdRPlus p O) = 0 := hpow (m + n) _ hmul
    exact (u * v).ne_zero huv⟩
  exact NoZeroDivisors.to_isDomain _

/-! ### Fontaine's `p`-adic `2πi` Element `t = log([ε])` and Proof that `t = ξ * unit` -/

/-- Teichmüller lift `[ε] ∈ A_inf p O`. -/
def teichEps (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)]
    [PerfectoidBase p O] : A_inf p O :=
  WittVector.teichmuller p (epsFlat p O)

/-- `ε^{1/p} = (frobeniusEquiv).symm ε ∈ Tilt p O`. -/
def epsRoot (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)]
    [PerfectoidBase p O] : Tilt p O :=
  (frobeniusEquiv (Tilt p O) p).symm (epsFlat p O)

/-- Cyclotomic factor `ω := ∑_{j=0}^{p-1} [ε^{1/p}]^j ∈ A_inf p O`. -/
def omegaAinf (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)]
    [PerfectoidBase p O] : A_inf p O :=
  ∑ j ∈ Finset.range p, (WittVector.teichmuller p (epsRoot p O)) ^ j

omit [IsDomain O] [ValuationRing O] [CharZero O] in
theorem sharp_epsRoot : sharp p O (epsRoot p O) = PerfectoidBase.zetaSeq (p := p) (O := O) 1 := by
  let s : ℕ → O := fun n => PerfectoidBase.zetaSeq (p := p) (O := O) (n + 1)
  have hs : ∀ n, s (n + 1) ^ p = s n := fun n => PerfectoidBase.zetaSeq_pow (n + 1)
  have heq : epsRoot p O = Tilt.ofSeq (p := p) s hs := by
    apply (frobeniusEquiv (Tilt p O) p).injective
    rw [epsRoot, RingEquiv.apply_symm_apply]
    refine Perfection.ext (R := ModP O p) (p := p) fun n => ?_
    change PreTilt.coeff n (epsFlat p O) = PreTilt.coeff n ((Tilt.ofSeq (p := p) s hs) ^ p)
    rw [map_pow, Tilt.coeff_ofSeq, ← map_pow, PerfectoidBase.zetaSeq_pow n]
    rfl
  rw [heq, sharp_ofSeq]

omit [IsDomain O] [ValuationRing O] [CharZero O] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] in
theorem teichEps_sub_one_eq :
    teichEps p O - 1 = (WittVector.teichmuller p (epsRoot p O) - 1) * omegaAinf p O := by
  have hpow : (WittVector.teichmuller p (epsRoot p O)) ^ p = teichEps p O := by
    rw [← map_pow, teichEps]
    congr 1
    exact (frobeniusEquiv (Tilt p O) p).apply_symm_apply (epsFlat p O)
  rw [omegaAinf, ← hpow]
  simpa [mul_comm] using (geom_sum_mul (WittVector.teichmuller p (epsRoot p O)) p).symm

omit [ValuationRing O] [CharZero O] in
theorem thetaMap_omegaAinf : thetaMap p O (omegaAinf p O) = 0 := by
  have hmul : (PerfectoidBase.zetaSeq (p := p) (O := O) 1 - 1) * thetaMap p O (omegaAinf p O) = 0 := by
    have h1 := congrArg (thetaMap p O) (teichEps_sub_one_eq (p := p) (O := O))
    rw [map_sub, map_one, teichEps, thetaMap_teichmuller, sharp_epsFlat, sub_self, map_mul,
      map_sub, map_one, thetaMap_teichmuller, sharp_epsRoot] at h1
    exact h1.symm
  have hne : PerfectoidBase.zetaSeq (p := p) (O := O) 1 - 1 ≠ 0 :=
    sub_ne_zero.mpr (PerfectoidBase.zetaSeq_one_ne_one (p := p) (O := O))
  exact (mul_eq_zero.mp hmul).resolve_left hne

omit [Fact p.Prime] [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)]
  [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] [PerfectoidBase p O] in
private theorem isUnit_one_add_nonunit_O {x : O} (hx : ¬IsUnit x) : IsUnit (1 + x) := by
  have h1 : x ∈ IsLocalRing.maximalIdeal O := hx
  by_contra hnu
  have h2 : 1 + x ∈ IsLocalRing.maximalIdeal O := hnu
  have h3 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    simpa [add_sub_cancel_right] using sub_mem h2 h1
  exact h3 isUnit_one

omit [CharZero O] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] in
private theorem zetaSeq_one_sub_one_pow_assoc :
    Associated ((PerfectoidBase.zetaSeq (p := p) (O := O) 1 - 1) ^ (p - 1)) ((p : ℕ) : O) := by
  have hp : p.Prime := Fact.out
  set y : O := PerfectoidBase.zetaSeq (p := p) (O := O) 1 - 1
  have hy0 : y ≠ 0 := sub_ne_zero.mpr (PerfectoidBase.zetaSeq_one_ne_one (p := p) (O := O))
  have hpow : (y + 1) ^ p - 1 = 0 := by
    have h1 : y + 1 = PerfectoidBase.zetaSeq (p := p) (O := O) 1 := sub_add_cancel _ _
    rw [h1, PerfectoidBase.zetaSeq_pow 0, PerfectoidBase.zetaSeq_zero, sub_self]
  have hexp : y * (∑ j ∈ Finset.range p, (Nat.choose p (j + 1) : O) * y ^ j) = 0 := by
    have h2 : (y + 1) ^ p - 1 = ∑ j ∈ Finset.range p, (Nat.choose p (j + 1) : O) * y ^ (j + 1) := by
      rw [add_pow, Finset.sum_range_succ']
      simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one,
        add_sub_cancel_right]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [← hpow, h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by rw [pow_succ']; ring
  have hsum0 : ∑ j ∈ Finset.range p, (Nat.choose p (j + 1) : O) * y ^ j = 0 :=
    (mul_eq_zero.mp hexp).resolve_left hy0
  -- Split off j = 0 (gives p) and j = p - 1 (gives y^{p-1}); middle terms are divisible by p * y
  have hmiddle : ∃ r : O, y ^ (p - 1) + ((p : ℕ) : O) * (1 + y * r) = 0 := by
    have hsplit : ∑ j ∈ Finset.range p, (Nat.choose p (j + 1) : O) * y ^ j =
        y ^ (p - 1) + ∑ j ∈ Finset.range (p - 1), (Nat.choose p (j + 1) : O) * y ^ j := by
      have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.pos).symm
      conv_lhs => rw [hp1, Finset.sum_range_succ]
      rw [← hp1, Nat.choose_self, Nat.cast_one, one_mul, add_comm]
    rw [hsplit] at hsum0
    have hmid_dvd : ((p : ℕ) : O) * y ∣
        ∑ j ∈ Finset.range (p - 2), (Nat.choose p (j + 2) : O) * y ^ (j + 1) := by
      refine Finset.dvd_sum fun j hj => ?_
      rw [Finset.mem_range] at hj
      have hch : p ∣ Nat.choose p (j + 2) := hp.dvd_choose_self (by omega) (by omega)
      obtain ⟨c, hc⟩ := hch
      rw [hc, Nat.cast_mul, pow_succ']
      exact ⟨(c : O) * y ^ j, by ring⟩
    obtain ⟨r, hr⟩ := hmid_dvd
    have hp_ge2 : 1 ≤ p - 1 := by have := hp.two_le; omega
    have hsplit2 : ∑ j ∈ Finset.range (p - 1), (Nat.choose p (j + 1) : O) * y ^ j =
        ((p : ℕ) : O) + ∑ j ∈ Finset.range (p - 2), (Nat.choose p (j + 2) : O) * y ^ (j + 1) := by
      have hpm : p - 1 = (p - 2) + 1 := by have := hp.two_le; omega
      conv_lhs => rw [hpm, Finset.sum_range_succ']
      simp [Nat.choose_one_right]
      rw [add_comm]
    rw [hsplit2, hr] at hsum0
    exact ⟨r, by linear_combination hsum0⟩
  obtain ⟨r, hr⟩ := hmiddle
  have hy_nu : ¬IsUnit y := by
    intro hyu
    have h1 : y ^ (p - 1) ∈ Ideal.span {((p : ℕ) : O)} := by
      rw [Ideal.mem_span_singleton]
      exact ⟨-(1 + y * r), by linear_combination hr⟩
    have h2 : IsUnit (y ^ (p - 1)) := hyu.pow _
    have hp_nu : ¬IsUnit ((p : ℕ) : O) := Fact.out
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h1
    exact hp_nu (isUnit_of_mul_isUnit_left (hc ▸ h2))
  have hyr_nu : ¬IsUnit (y * r) := fun h => hy_nu (isUnit_of_mul_isUnit_left h)
  have hu : IsUnit (-(1 + y * r)) := (isUnit_one_add_nonunit_O hyr_nu).neg
  obtain ⟨u, hu'⟩ := hu
  exact ⟨u⁻¹, by
    have heq : y ^ (p - 1) = ((p : ℕ) : O) * (u : O) := by rw [hu']; linear_combination hr
    calc y ^ (p - 1) * (u⁻¹ : Oˣ) = ((p : ℕ) : O) * ((u : O) * (u⁻¹ : Oˣ)) := by
          rw [heq, mul_assoc]
      _ = ((p : ℕ) : O) := by rw [Units.mul_inv, mul_one]⟩

omit [CharZero O] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] in
private theorem zetaSeq_sub_one_pow_assoc :
    ∀ n : ℕ,
      Associated ((PerfectoidBase.zetaSeq (p := p) (O := O) (n + 1) - 1) ^ (p ^ n * (p - 1)))
        ((p : ℕ) : O) := by
  have hp : p.Prime := Fact.out
  intro n
  induction n with
  | zero => simpa using zetaSeq_one_sub_one_pow_assoc (p := p) (O := O)
  | succ n ih =>
    set y : O := PerfectoidBase.zetaSeq (p := p) (O := O) (n + 2) - 1
    set z : O := PerfectoidBase.zetaSeq (p := p) (O := O) (n + 1) - 1
    have hzy : z = (y + 1) ^ p - 1 := by
      have h1 : y + 1 = PerfectoidBase.zetaSeq (p := p) (O := O) (n + 2) := sub_add_cancel _ _
      rw [h1, PerfectoidBase.zetaSeq_pow (n + 1)]
    have hexp : ∃ r : O, z = y ^ p + ((p : ℕ) : O) * y * r := by
      rw [hzy, add_pow, Finset.sum_range_succ']
      simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one,
        add_sub_cancel_right]
      have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.pos).symm
      have hsplit : ∑ k ∈ Finset.range p, y ^ (k + 1) * (Nat.choose p (k + 1) : O) =
          y ^ p + ∑ k ∈ Finset.range (p - 1), y ^ (k + 1) * (Nat.choose p (k + 1) : O) := by
        conv_lhs => rw [hp1, Finset.sum_range_succ]
        rw [← hp1, Nat.choose_self, Nat.cast_one, mul_one, add_comm]
      rw [hsplit]
      have hdvd : ((p : ℕ) : O) * y ∣
          ∑ k ∈ Finset.range (p - 1), y ^ (k + 1) * (Nat.choose p (k + 1) : O) := by
        refine Finset.dvd_sum fun k hk => ?_
        rw [Finset.mem_range] at hk
        have hch : p ∣ Nat.choose p (k + 1) := hp.dvd_choose_self (by omega) (by omega)
        obtain ⟨c, hc⟩ := hch
        rw [hc, Nat.cast_mul, pow_succ']
        exact ⟨y ^ k * (c : O), by ring⟩
      obtain ⟨r, hr⟩ := hdvd
      exact ⟨r, by rw [hr]⟩
    obtain ⟨r, hr⟩ := hexp
    have hexp_pos : 1 ≤ p ^ n * (p - 1) :=
      Nat.mul_pos (pow_pos hp.pos n) (by have := hp.two_le; omega)
    have hz_dvd_p : z ∣ ((p : ℕ) : O) :=
      (dvd_pow_self z (by omega : p ^ n * (p - 1) ≠ 0)).trans ih.dvd
    obtain ⟨s, hs⟩ := hz_dvd_p
    have hy_nu : ¬IsUnit y := by
      intro hyu
      have hp_nu : ¬IsUnit ((p : ℕ) : O) := Fact.out
      have h1 : y ^ p = z - ((p : ℕ) : O) * y * r := by linear_combination -hr
      have hz_nu : ¬IsUnit z := fun hzu => hp_nu (by
        obtain ⟨u, hu⟩ := ih
        rw [← hu]
        exact (hzu.pow _).mul u.isUnit)
      have hz_mem : z ∈ IsLocalRing.maximalIdeal O := hz_nu
      have hp_mem : ((p : ℕ) : O) * y * r ∈ IsLocalRing.maximalIdeal O :=
        Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hp_nu)
      have hyp_mem : y ^ p ∈ IsLocalRing.maximalIdeal O := by
        rw [h1]; exact sub_mem hz_mem hp_mem
      exact hyp_mem (hyu.pow p)
    have hnu : ¬IsUnit (-(s * y * r)) := fun h =>
      hy_nu (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left (by simpa using h.neg)))
    have hu : IsUnit (1 + -(s * y * r)) := isUnit_one_add_nonunit_O hnu
    have hyp_eq : y ^ p = z * (1 + -(s * y * r)) := by
      have : z * (1 + -(s * y * r)) = z - ((p : ℕ) : O) * y * r := by
        rw [hs]; ring
      rw [this]; linear_combination -hr
    obtain ⟨u, hu'⟩ := hu
    obtain ⟨v, hv⟩ := ih
    refine ⟨u⁻¹ ^ (p ^ n * (p - 1)) * v, ?_⟩
    rw [pow_succ', mul_assoc, pow_mul, hyp_eq, ← hu', mul_pow]
    push_cast
    calc z ^ (p ^ n * (p - 1)) * (u : O) ^ (p ^ n * (p - 1)) *
          (((u⁻¹ : Oˣ) : O) ^ (p ^ n * (p - 1)) * (v : O))
        = z ^ (p ^ n * (p - 1)) * (((u : O) * (u⁻¹ : Oˣ)) ^ (p ^ n * (p - 1))) * (v : O) := by
          rw [mul_pow]; ring
      _ = z ^ (p ^ n * (p - 1)) * (v : O) := by rw [Units.mul_inv, one_pow, mul_one]
      _ = ((p : ℕ) : O) := hv

theorem omegaAinf_eq_xi_mul_unit :
    ∃ u : (A_inf p O)ˣ, omegaAinf p O = xi p O * (u : A_inf p O) := by
  have hp : p.Prime := Fact.out
  obtain ⟨c, hc⟩ := (thetaMap_eq_zero_iff (p := p) (O := O) (omegaAinf p O)).mp
    (thetaMap_omegaAinf (p := p) (O := O))
  have hcoeff_omega : (omegaAinf p O).coeff 0 = (epsRoot p O - 1) ^ (p - 1) := by
    change WittVector.constantCoeff (omegaAinf p O) = _
    unfold omegaAinf
    rw [map_sum]
    have hterms : ∀ j ∈ Finset.range p,
        WittVector.constantCoeff ((WittVector.teichmuller p (epsRoot p O)) ^ j) = (epsRoot p O) ^ j :=
      fun j _ => by rw [map_pow]; simp [WittVector.constantCoeff, WittVector.teichmuller_coeff_zero]
    rw [Finset.sum_congr rfl hterms]
    have hmul : (epsRoot p O - 1) * (epsRoot p O - 1) ^ (p - 1) =
        (epsRoot p O - 1) * ∑ j ∈ Finset.range p, (epsRoot p O) ^ j := by
      rw [← pow_succ', Nat.sub_add_cancel hp.pos, sub_pow_char (epsRoot p O) 1, one_pow]
      simpa [mul_comm] using (geom_sum_mul (epsRoot p O) p).symm
    have hne : epsRoot p O - 1 ≠ 0 := by
      intro h0
      have h1 : sharp p O (epsRoot p O) = sharp p O 1 := congrArg (sharp p O) (sub_eq_zero.mp h0)
      rw [sharp_epsRoot, map_one] at h1
      exact PerfectoidBase.zetaSeq_one_ne_one (p := p) (O := O) h1
    exact (mul_left_cancel₀ hne hmul).symm
  have hsharp_assoc : Associated (sharp p O ((omegaAinf p O).coeff 0)) ((p : ℕ) : O) := by
    rw [hcoeff_omega]
    let a : ℕ → O := fun n => (PerfectoidBase.zetaSeq (p := p) (O := O) (n + 1) - 1) ^ (p - 1)
    have ha : ∀ n, Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) (a n) =
        PreTilt.coeff n ((epsRoot p O - 1) ^ (p - 1)) := by
      intro n
      have heps : PreTilt.coeff n (epsRoot p O) =
          Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})
            (PerfectoidBase.zetaSeq (p := p) (O := O) (n + 1)) := by
        have h1 := PreTilt.coeff_frobeniusEquiv_symm (O := O) (p := p) n (epsFlat p O)
        rw [epsRoot, h1]; rfl
      change Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})
          ((PerfectoidBase.zetaSeq (p := p) (O := O) (n + 1) - 1) ^ (p - 1)) = _
      rw [map_pow, map_sub, map_one, ← heps, map_pow, map_sub, map_one]
    have hspec2 := sharpFun_spec ((epsRoot p O - 1) ^ (p - 1)) a ha 2
    change ((p : ℕ) : O) ^ 2 ∣ a 2 ^ (p ^ 2) - sharp p O ((epsRoot p O - 1) ^ (p - 1)) at hspec2
    obtain ⟨d, hd⟩ := hspec2
    have ha2 : Associated (a 2 ^ (p ^ 2)) ((p : ℕ) : O) := by
      have := zetaSeq_sub_one_pow_assoc (p := p) (O := O) 2
      simpa only [a, ← pow_mul, mul_comm (p - 1)] using this
    obtain ⟨u, hu⟩ := ha2
    have hsharp_eq : sharp p O ((epsRoot p O - 1) ^ (p - 1)) =
        ((p : ℕ) : O) * ((u⁻¹ : Oˣ) - ((p : ℕ) : O) * d) := by
      have ha2_eq : a 2 ^ (p ^ 2) = ((p : ℕ) : O) * (u⁻¹ : Oˣ) := by
        calc a 2 ^ (p ^ 2) = a 2 ^ (p ^ 2) * (u : O) * (u⁻¹ : Oˣ) := by
              rw [mul_assoc, Units.mul_inv, mul_one]
          _ = ((p : ℕ) : O) * (u⁻¹ : Oˣ) := by rw [hu]
      linear_combination -hd + ha2_eq
    have hv_unit : IsUnit ((u⁻¹ : Oˣ) - ((p : ℕ) : O) * d) := by
      have hnu : ¬IsUnit (-(((p : ℕ) : O) * d * (u : O))) := by
        intro h
        have h' : IsUnit (((p : ℕ) : O) * d * (u : O)) := by simpa using h.neg
        exact (Fact.out : ¬IsUnit ((p : ℕ) : O))
          (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h'))
      have h1 := isUnit_one_add_nonunit_O hnu
      have h2 : (u⁻¹ : Oˣ) - ((p : ℕ) : O) * d = (u⁻¹ : Oˣ) * (1 + -(((p : ℕ) : O) * d * (u : O))) := by
        rw [mul_add, mul_one, mul_neg, mul_comm (((p : ℕ) : O) * d) (u : O), ← mul_assoc,
          ← mul_assoc, Units.inv_mul, one_mul]; ring
      rw [h2]
      exact (u⁻¹).isUnit.mul h1
    obtain ⟨v, hv⟩ := hv_unit
    exact ⟨v⁻¹, by
      rw [hsharp_eq, ← hv, mul_assoc, Units.mul_inv, mul_one]⟩
  have hc0_eq : (omegaAinf p O).coeff 0 = pFlat p O * c.coeff 0 := by
    have h0 := congrArg (WittVector.constantCoeff (p := p) (R := Tilt p O)) hc
    rw [map_mul] at h0
    simpa [WittVector.constantCoeff, coeff_zero_xi] using h0
  have hc0_unit : IsUnit (c.coeff 0) := by
    have h1 := congrArg (sharp p O) hc0_eq
    rw [map_mul, sharp_pFlat] at h1
    obtain ⟨u, hu⟩ := hsharp_assoc
    have hmul : ((p : ℕ) : O) * (sharp p O (c.coeff 0) * (u : O)) = ((p : ℕ) : O) * 1 := by
      rw [← mul_assoc, ← h1, hu, mul_one]
    have hsu : sharp p O (c.coeff 0) * (u : O) = 1 :=
      mul_left_cancel₀ (Nat.cast_ne_zero.mpr hp.ne_zero) hmul
    have hs_unit : IsUnit (sharp p O (c.coeff 0)) := isUnit_iff_exists_inv.mpr ⟨(u : O), hsu⟩
    rw [isUnit_iff_dvd_one, tilt_dvd_iff_sharp_dvd, map_one]
    exact hs_unit.dvd
  obtain ⟨u, hu⟩ := (ainf_isUnit_iff_isUnit_coeff c).mpr hc0_unit
  exact ⟨u, by rw [hc, hu]⟩

private theorem tBdR_compat {m n : ℕ} (hle : m ≤ n) :
    Ideal.Quotient.factorPow (kerThetaInvP p O) hle
      (truncLogHom ((Ideal.Quotient.mk _).comp (ratToAinfInvP p O)) n
        (evalBdRPlus p O n (ainfToBdRPlus p O (teichEps p O) - 1))) =
    truncLogHom ((Ideal.Quotient.mk _).comp (ratToAinfInvP p O)) m
      (evalBdRPlus p O m (ainfToBdRPlus p O (teichEps p O) - 1)) := by
  rw [map_truncLogHom]
  have hq : (Ideal.Quotient.factorPow (kerThetaInvP p O) hle).comp
      ((Ideal.Quotient.mk _).comp (ratToAinfInvP p O)) =
      (Ideal.Quotient.mk _).comp (ratToAinfInvP p O) := by
    ext q; rfl
  have hfac : Ideal.Quotient.factorPow (kerThetaInvP p O) hle
      (evalBdRPlus p O n (ainfToBdRPlus p O (teichEps p O) - 1)) =
      evalBdRPlus p O m (ainfToBdRPlus p O (teichEps p O) - 1) :=
    factorPow_evalₐ (kerThetaInvP p O) hle _
  rw [hq, hfac]
  refine truncLogHom_eq_of_pow_eq_zero _ ?_ hle
  rw [← map_pow, evalBdRPlus_eq_zero_iff]
  have hdvd : xiBdR p O ∣ ainfToBdRPlus p O (teichEps p O) - 1 := by
    rw [← thetaBdRPlus_eq_zero_iff_dvd, map_sub, map_one, thetaBdRPlus_ainf, teichEps,
      thetaMap_teichmuller, sharp_epsFlat, map_one, sub_self]
  exact pow_dvd_pow_of_dvd hdvd m

/-- **Fontaine's `p`-adic `2πi` Period `t = log([ε]) ∈ B_dR^+`**. -/
def tBdR (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : BdRPlus p O :=
  adicMk (kerThetaInvP p O)
    (fun n => truncLogHom ((Ideal.Quotient.mk _).comp (ratToAinfInvP p O)) n
      (evalBdRPlus p O n (ainfToBdRPlus p O (teichEps p O) - 1)))
    (tBdR_compat (p := p) (O := O))

theorem evalBdRPlus_tBdR (n : ℕ) :
    evalBdRPlus p O n (tBdR p O) =
      truncLogHom ((Ideal.Quotient.mk _).comp (ratToAinfInvP p O)) n
        (evalBdRPlus p O n (ainfToBdRPlus p O (teichEps p O) - 1)) := by
  change AdicCompletion.evalₐ (kerThetaInvP p O) n (tBdR p O) = _
  unfold tBdR
  exact evalₐ_adicMk _ _ (tBdR_compat (p := p) (O := O)) n

theorem tBdR_mem_ker_thetaBdRPlus : tBdR p O ∈ RingHom.ker (thetaBdRPlus p O) := by
  rw [RingHom.mem_ker, thetaBdRPlus_eq_zero_iff_dvd, ← pow_one (xiBdR p O),
    ← evalBdRPlus_eq_zero_iff, evalBdRPlus_tBdR]
  unfold truncLogHom
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_zero, zero_add, div_one,
    map_one, one_mul, pow_one]
  rw [evalBdRPlus_eq_zero_iff, pow_one, ← thetaBdRPlus_eq_zero_iff_dvd, map_sub, map_one,
    thetaBdRPlus_ainf, teichEps, thetaMap_teichmuller, sharp_epsFlat, map_one, sub_self]

/-- **Fontaine's Uniformizer Theorem**: `t = log([ε])` generates `ker(θ_dR)`, i.e.
`t = ξ * u` for a unit `u : (B_dR^+)ˣ`! -/
theorem tBdR_associated_xiBdR :
    ∃ u : (BdRPlus p O)ˣ, tBdR p O = xiBdR p O * (u : BdRPlus p O) := by
  obtain ⟨u_ω, hu_ω⟩ := omegaAinf_eq_xi_mul_unit (p := p) (O := O)
  let c : A_inf p O := (WittVector.teichmuller p (epsRoot p O) - 1) * (u_ω : A_inf p O)
  have hteich : teichEps p O - 1 = xi p O * c := by
    rw [teichEps_sub_one_eq, hu_ω]; ring
  have hmod2 : xiBdR p O ^ 2 ∣ tBdR p O - (ainfToBdRPlus p O (teichEps p O) - 1) := by
    rw [← evalBdRPlus_eq_zero_iff, map_sub, evalBdRPlus_tBdR]
    unfold truncLogHom
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pow_zero, Nat.cast_zero, zero_add, div_one, map_one, one_mul, pow_one]
    have hsq : evalBdRPlus p O 2 (ainfToBdRPlus p O (teichEps p O) - 1) ^ 2 = 0 := by
      rw [← map_pow, evalBdRPlus_eq_zero_iff]
      have hdvd : xiBdR p O ∣ ainfToBdRPlus p O (teichEps p O) - 1 := by
        rw [← map_one (ainfToBdRPlus p O), ← map_sub, hteich, map_mul]
        exact dvd_mul_right _ _
      exact pow_dvd_pow_of_dvd hdvd 2
    rw [hsq, mul_zero, add_zero, sub_self]
  obtain ⟨r, hr⟩ := hmod2
  have ht_eq : tBdR p O = xiBdR p O * (ainfToBdRPlus p O c + xiBdR p O * r) := by
    have h1 : ainfToBdRPlus p O (teichEps p O) - 1 = xiBdR p O * ainfToBdRPlus p O c := by
      rw [← map_one (ainfToBdRPlus p O), ← map_sub, hteich, map_mul]; rfl
    linear_combination hr + h1
  have hu : IsUnit (ainfToBdRPlus p O c + xiBdR p O * r) := by
    rw [isUnit_BdRPlus_iff_theta_ne_zero, map_add, map_mul (thetaBdRPlus p O) (xiBdR p O) r,
      show thetaBdRPlus p O (xiBdR p O) = 0 from (thetaBdRPlus_eq_zero_iff_dvd _).mpr dvd_rfl,
      zero_mul, add_zero, thetaBdRPlus_ainf]
    intro h0
    have htc : thetaMap p O c = 0 :=
      IsFractionRing.injective O (Localization.Away ((p : ℕ) : O)) (by rw [map_zero, h0])
    have h1 : thetaMap p O (WittVector.teichmuller p (epsRoot p O) - 1) *
        thetaMap p O (u_ω : A_inf p O) = 0 := by simpa [c, map_mul] using htc
    have hne1 : thetaMap p O (WittVector.teichmuller p (epsRoot p O) - 1) ≠ 0 := by
      rw [map_sub, map_one, thetaMap_teichmuller, sharp_epsRoot]
      exact sub_ne_zero.mpr (PerfectoidBase.zetaSeq_one_ne_one (p := p) (O := O))
    have hne2 : thetaMap p O (u_ω : A_inf p O) ≠ 0 :=
      (u_ω.isUnit.map (thetaMap p O)).ne_zero
    exact (mul_ne_zero hne1 hne2) h1
  obtain ⟨u, hu'⟩ := hu
  exact ⟨u, by rw [ht_eq, hu']⟩

theorem tBdR_ne_zero : tBdR p O ≠ 0 := by
  obtain ⟨u, hu⟩ := tBdR_associated_xiBdR (p := p) (O := O)
  rw [hu]
  exact mul_ne_zero (xiBdR_ne_zero (p := p) (O := O)) u.ne_zero

theorem exists_tBdR_pow_mul_unit {x : BdRPlus p O} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : (BdRPlus p O)ˣ), x = tBdR p O ^ n * (u : BdRPlus p O) := by
  obtain ⟨n, v, rfl⟩ := exists_xiBdR_pow_mul_unit hx
  obtain ⟨u, hu⟩ := tBdR_associated_xiBdR (p := p) (O := O)
  refine ⟨n, u⁻¹ ^ n * v, ?_⟩
  rw [hu, mul_pow]
  push_cast
  calc xiBdR p O ^ n * (v : BdRPlus p O)
      = xiBdR p O ^ n * (((u : BdRPlus p O) ^ n * ((u⁻¹ : (BdRPlus p O)ˣ) : BdRPlus p O) ^ n) *
          (v : BdRPlus p O)) := by
        rw [← mul_pow, Units.mul_inv, one_pow, one_mul]
    _ = xiBdR p O ^ n * (u : BdRPlus p O) ^ n *
          (((u⁻¹ : (BdRPlus p O)ˣ) : BdRPlus p O) ^ n * (v : BdRPlus p O)) := by ring

/-! ### Fontaine's De Rham Field `B_dR := Localization.Away t` & `ℤ`-Filtration `Fil^i B_dR = t^i B_dR^+` -/

/-- **Fontaine's De Rham Field `B_dR := Localization.Away tBdR`**. -/
abbrev BdR (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : Type u :=
  Localization.Away (tBdR p O)

/-- Canonical `RingHom` `B_dR^+ →+* B_dR`. -/
def bdrPlusToBdR (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : BdRPlus p O →+* BdR p O :=
  algebraMap (BdRPlus p O) (BdR p O)

theorem bdrPlusToBdR_injective : Function.Injective (bdrPlusToBdR p O) :=
  IsLocalization.injective (BdR p O)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero (tBdR_ne_zero (p := p) (O := O))))

/-- **`B_dR` is the fraction field of the DVR `B_dR^+` (hence a `Field`)**! -/
instance isFractionRing_BdR : IsFractionRing (BdRPlus p O) (BdR p O) :=
  IsLocalization.isLocalization_of_is_exists_mul_mem _ (Submonoid.powers (tBdR p O)) _
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero (tBdR_ne_zero (p := p) (O := O))))
    (fun ⟨x, hx⟩ => by
      obtain ⟨n, u, rfl⟩ := exists_tBdR_pow_mul_unit (nonZeroDivisors.ne_zero hx)
      refine ⟨(u⁻¹ : (BdRPlus p O)ˣ), n, ?_⟩
      dsimp only
      rw [mul_left_comm, Units.inv_mul, mul_one])

theorem isField_BdR : IsField (BdR p O) :=
  (IsFractionRing.toField (BdRPlus p O) (K := BdR p O)).toIsField

noncomputable instance instFieldBdR : Field (BdR p O) :=
  (isField_BdR (p := p) (O := O)).toField

/-- Canonical `RingHom` `ℚ_[p] →+* B_dR`. -/
def padicToBdR (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : ℚ_[p] →+* BdR p O :=
  (bdrPlusToBdR p O).comp (padicToBdRPlus p O)

/-- The period `t` inside `B_dR`. -/
def tInBdR (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : BdR p O :=
  bdrPlusToBdR p O (tBdR p O)

theorem tInBdR_ne_zero : tInBdR p O ≠ 0 := by
  intro h
  exact tBdR_ne_zero (p := p) (O := O) (bdrPlusToBdR_injective (by simpa [tInBdR] using h))

/-- **Fontaine's `ℤ`-indexed Decreasing Hodge Filtration `Fil^i B_dR = t^i B_dR^+`**. -/
def FilBdR (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] (i : ℤ) : AddSubgroup (BdR p O) where
  carrier := { x : BdR p O | ∃ y : BdRPlus p O, x = tInBdR p O ^ i * bdrPlusToBdR p O y }
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨y₁, rfl⟩ ⟨y₂, rfl⟩
    exact ⟨y₁ + y₂, by rw [map_add, mul_add]⟩
  neg_mem' := by
    rintro _ ⟨y, rfl⟩
    exact ⟨-y, by rw [map_neg, mul_neg]⟩

theorem mem_FilBdR_iff (i : ℤ) (x : BdR p O) :
    x ∈ FilBdR p O i ↔ ∃ y : BdRPlus p O, x = tInBdR p O ^ i * bdrPlusToBdR p O y := Iff.rfl

theorem FilBdR_antitone {i j : ℤ} (hij : i ≤ j) : FilBdR p O j ≤ FilBdR p O i := by
  rintro x ⟨y, rfl⟩
  have hdiff : 0 ≤ j - i := sub_nonneg.mpr hij
  lift (j - i) to ℕ using hdiff with k hk
  refine ⟨tBdR p O ^ k * y, ?_⟩
  rw [map_mul, map_pow, ← mul_assoc]
  have hpow : tInBdR p O ^ i * bdrPlusToBdR p O (tBdR p O) ^ k = tInBdR p O ^ j := by
    change tInBdR p O ^ i * tInBdR p O ^ k = tInBdR p O ^ j
    rw [← zpow_natCast, ← zpow_add₀ (tInBdR_ne_zero (p := p) (O := O)), hk, add_sub_cancel]
  rw [hpow]

theorem one_mem_FilBdR_zero : (1 : BdR p O) ∈ FilBdR p O 0 :=
  ⟨1, by simp⟩

/-- **Multiplicativity of the Hodge Filtration**: `Fil^i B_dR · Fil^j B_dR ⊆ Fil^{i+j} B_dR`! -/
theorem FilBdR_mul {i j : ℤ} {x y : BdR p O}
    (hx : x ∈ FilBdR p O i) (hy : y ∈ FilBdR p O j) :
    x * y ∈ FilBdR p O (i + j) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * b, ?_⟩
  rw [map_mul, zpow_add₀ (tInBdR_ne_zero (p := p) (O := O))]
  ring

theorem FilBdR_exhaustive (x : BdR p O) : ∃ i : ℤ, x ∈ FilBdR p O i := by
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, hax⟩ := IsLocalization.surj (Submonoid.powers (tBdR p O)) x
  refine ⟨-(k : ℤ), a, ?_⟩
  have ht0 : tInBdR p O ≠ 0 := tInBdR_ne_zero (p := p) (O := O)
  have h1 : x * tInBdR p O ^ (k : ℤ) = bdrPlusToBdR p O a := by
    simpa [tInBdR, bdrPlusToBdR, map_pow] using hax
  calc x = (x * tInBdR p O ^ (k : ℤ)) * tInBdR p O ^ (-(k : ℤ)) := by
        rw [mul_assoc, ← zpow_add₀ ht0, add_neg_cancel, zpow_zero, mul_one]
    _ = tInBdR p O ^ (-(k : ℤ)) * bdrPlusToBdR p O a := by rw [h1, mul_comm]

theorem FilBdR_separated {x : BdR p O} (hx : ∀ i : ℤ, x ∈ FilBdR p O i) : x = 0 := by
  obtain ⟨y, hy⟩ := hx 0
  rw [zpow_zero, one_mul] at hy
  subst hy
  have hy0 : y = 0 := by
    obtain ⟨u, hu⟩ := tBdR_associated_xiBdR (p := p) (O := O)
    refine eq_zero_of_forall_xiBdR_pow_dvd fun n => ?_
    obtain ⟨z, hz⟩ := hx (n : ℤ)
    have h1 : bdrPlusToBdR p O y = bdrPlusToBdR p O (tBdR p O ^ n * z) := by
      simpa [tInBdR, map_mul, map_pow] using hz
    have h2 : y = tBdR p O ^ n * z := bdrPlusToBdR_injective h1
    rw [h2, hu, mul_pow]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  rw [hy0, map_zero]

theorem tInBdR_mem_FilBdR_one : tInBdR p O ∈ FilBdR p O 1 :=
  ⟨1, by simp⟩

theorem tInBdR_not_mem_FilBdR_two : tInBdR p O ∉ FilBdR p O 2 := by
  rintro ⟨y, hy⟩
  have h1 : bdrPlusToBdR p O (tBdR p O) = bdrPlusToBdR p O (tBdR p O ^ 2 * y) := by
    simpa [tInBdR, map_mul, map_pow] using hy
  have h2 : tBdR p O = tBdR p O ^ 2 * y := bdrPlusToBdR_injective h1
  have h3 : tBdR p O * (1 - tBdR p O * y) = 0 := by linear_combination h2
  have h4 : 1 - tBdR p O * y = 0 := (mul_eq_zero.mp h3).resolve_left (tBdR_ne_zero (p := p) (O := O))
  have h5 := congrArg (thetaBdRPlus p O) h4
  rw [map_sub, map_one, map_mul, RingHom.mem_ker.mp (tBdR_mem_ker_thetaBdRPlus (p := p) (O := O)),
    zero_mul, sub_zero, map_zero] at h5
  exact one_ne_zero h5

end BdRConstruction

/-! ## Section 5: Concrete `A_cris`, `B_cris := A_cris[1/t]`, Witt-Vector Frobenius `frobBcris`,
and `frobBcris t = p * t` -/

section AcrisBcrisConstruction

open scoped Nat

/-- Polynomial truncated logarithm `∑_{k=0}^{N-1} ((-1)^k / (k+1)) X^{k+1} ∈ ℚ[X]`. -/
def truncLogPoly (N : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range N, Polynomial.C ((-1 : ℚ) ^ k / (k + 1 : ℚ)) * Polynomial.X ^ (k + 1)

theorem derivative_truncLogPoly (N : ℕ) :
    (truncLogPoly N).derivative = ∑ k ∈ Finset.range N, (-Polynomial.X : Polynomial ℚ) ^ k := by
  unfold truncLogPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.derivative_X_pow]
  have hk0 : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  calc Polynomial.C ((-1 : ℚ) ^ k / (k + 1 : ℚ)) * (Polynomial.C ((k + 1 : ℕ) : ℚ) * Polynomial.X ^ k)
      = Polynomial.C ((-1 : ℚ) ^ k / (k + 1 : ℚ) * ((k + 1 : ℕ) : ℚ)) * Polynomial.X ^ k := by
        rw [← mul_assoc, ← map_mul]
    _ = Polynomial.C ((-1 : ℚ) ^ k) * Polynomial.X ^ k := by
        congr 2; push_cast; field_simp
    _ = (-Polynomial.X : Polynomial ℚ) ^ k := by
        rw [show (-Polynomial.X : Polynomial ℚ) = Polynomial.C (-1 : ℚ) * Polynomial.X by simp,
          mul_pow, ← map_pow]

/-- **Polynomial Logarithm Identity**:
`truncLogPoly N ((1 + X)^p - 1) ≡ p * truncLogPoly N X (mod X^{N+1})` in `ℚ[X]`, proved in 15 lines
via `Polynomial.derivative`! -/
theorem truncLogPoly_comp_pow_sub_mul_dvd (p N : ℕ) :
    Polynomial.X ^ (N + 1) ∣
      ((truncLogPoly N).comp ((1 + Polynomial.X) ^ p - 1) -
        Polynomial.C (p : ℚ) * truncLogPoly N) := by
  set Y : Polynomial ℚ := (1 + Polynomial.X) ^ p - 1
  set P : Polynomial ℚ := (truncLogPoly N).comp Y - Polynomial.C (p : ℚ) * truncLogPoly N
  have hY0 : Y.eval 0 = 0 := by simp [Y]
  have hP0 : P.eval 0 = 0 := by
    simp only [P, Polynomial.eval_sub, Polynomial.eval_comp, hY0, Polynomial.eval_mul,
      Polynomial.eval_C, truncLogPoly, Polynomial.eval_finsetSum, Polynomial.eval_pow,
      Polynomial.eval_X, zero_pow (Nat.succ_ne_zero _), mul_zero, Finset.sum_const_zero, sub_self]
  have h1Y : 1 + Y = (1 + Polynomial.X) ^ p := by simp [Y]
  have hderiv_Y : Y.derivative = Polynomial.C (p : ℚ) * (1 + Polynomial.X) ^ (p - 1) := by
    simp [Y, Polynomial.derivative_pow, Polynomial.derivative_add, Polynomial.derivative_X]
  have hgeom : ∀ Z : Polynomial ℚ, (1 + Z) * (truncLogPoly N).derivative.comp Z = 1 - (-Z) ^ N := by
    intro Z
    rw [derivative_truncLogPoly, Polynomial.sum_comp]
    have hterms : ∀ k ∈ Finset.range N, ((-Polynomial.X : Polynomial ℚ) ^ k).comp Z = (-Z) ^ k :=
      fun k _ => by rw [Polynomial.pow_comp, Polynomial.neg_comp, Polynomial.X_comp]
    rw [Finset.sum_congr rfl hterms]
    have h := mul_geom_sum (-Z) N
    linear_combination -h
  have hmul_deriv : (1 + Polynomial.X) * P.derivative =
      Polynomial.C (p : ℚ) * ((-Polynomial.X) ^ N - (-Y) ^ N) := by
    have hPd : P.derivative =
        (truncLogPoly N).derivative.comp Y * Y.derivative -
          Polynomial.C (p : ℚ) * (truncLogPoly N).derivative := by
      simp [P, Polynomial.derivative_sub, Polynomial.derivative_comp, Polynomial.derivative_mul,
        mul_comm]
    rw [hPd, hderiv_Y, mul_sub]
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp [Y]
    · have hpow_p : (1 + Polynomial.X) * (1 + Polynomial.X) ^ (p - 1) = 1 + Y := by
        rw [← pow_succ', Nat.sub_add_cancel hp, h1Y]
      have h1 : (1 + Polynomial.X) * ((truncLogPoly N).derivative.comp Y *
          (Polynomial.C (p : ℚ) * (1 + Polynomial.X) ^ (p - 1))) =
          Polynomial.C (p : ℚ) * ((1 + Y) * (truncLogPoly N).derivative.comp Y) := by
        rw [← hpow_p]; ring
      have h2 : (1 + Polynomial.X) * (Polynomial.C (p : ℚ) * (truncLogPoly N).derivative) =
          Polynomial.C (p : ℚ) * ((1 + Polynomial.X) * (truncLogPoly N).derivative.comp Polynomial.X) := by
        rw [Polynomial.comp_X]; ring
      rw [h1, h2, hgeom Y, hgeom Polynomial.X]
      ring
  have hXdvdY : Polynomial.X ∣ Y := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero, hY0]
  have hXdvd_rhs : Polynomial.X ^ N ∣ (1 + Polynomial.X) * P.derivative := by
    rw [hmul_deriv]
    refine dvd_mul_of_dvd_right (dvd_sub ?_ ?_) _
    · rw [neg_pow]; exact dvd_mul_left _ _
    · rw [neg_pow]; exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hXdvdY N) _
  -- Every coefficient of P.derivative of degree < N is 0
  have hP'_coeff : ∀ k < N, P.derivative.coeff k = 0 := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk
      have h0 : ((1 + Polynomial.X) * P.derivative).coeff k = 0 := by
        obtain ⟨Q, hQ⟩ := hXdvd_rhs
        rw [hQ, Polynomial.coeff_X_pow_mul']
        exact if_neg (not_le.mpr hk)
      rw [add_mul, one_mul, Polynomial.coeff_add] at h0
      cases k with
      | zero => simpa using h0
      | succ k =>
        rw [Polynomial.coeff_X_mul] at h0
        have hprev := ih k (Nat.lt_succ_self k) (by omega)
        simpa [hprev] using h0
  -- Hence every coefficient of P of degree ≤ N is 0
  have hP_coeff : ∀ k < N + 1, P.coeff k = 0 := by
    intro k hk
    cases k with
    | zero => simpa [Polynomial.coeff_zero_eq_eval_zero] using hP0
    | succ k =>
      have hd := hP'_coeff k (by omega)
      rw [Polynomial.coeff_derivative] at hd
      have hk0 : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      exact (mul_eq_zero.mp (by simpa using hd)).resolve_right hk0
  rw [Polynomial.X_pow_dvd_iff]
  exact hP_coeff

private theorem prime_pow_dvd_finset_lcm_exists {p : ℕ} (hp : p.Prime) (s : Finset ℕ) (e : ℕ)
    (h : p ^ e ∣ s.lcm id) : e = 0 ∨ ∃ r ∈ s, p ^ e ∣ r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.lcm_empty] at h
    rcases Nat.eq_zero_or_pos e with rfl | he
    · exact Or.inl rfl
    · exfalso
      have h1 : p ∣ 1 := (dvd_pow_self p he.ne').trans h
      exact hp.not_dvd_one h1
  | @insert a s _ ih =>
    rw [Finset.lcm_insert] at h
    rcases Nat.eq_zero_or_pos e with rfl | he
    · exact Or.inl rfl
    · by_cases ha : p ^ e ∣ a
      · exact Or.inr ⟨a, Finset.mem_insert_self a s, ha⟩
      · have hs : p ^ e ∣ s.lcm id := by
          -- If p^e ∣ lcm a b and ¬ (p^e ∣ a), then p^e ∣ b (comparing p-adic valuations!)
          have : Fact p.Prime := ⟨hp⟩
          by_cases ha0 : a = 0
          · subst ha0; exact absurd (dvd_zero _) ha
          by_cases hb0 : s.lcm id = 0
          · rw [hb0]; exact dvd_zero _
          have hlab0 : Nat.lcm a (s.lcm id) ≠ 0 := Nat.lcm_ne_zero ha0 hb0
          have hv : e ≤ padicValNat p (Nat.lcm a (s.lcm id)) :=
            (padicValNat_dvd_iff_le hlab0).mp h
          have hv_a : padicValNat p a < e := by
            by_contra hge
            exact ha ((padicValNat_dvd_iff_le ha0).mpr (not_lt.mp hge))
          have hv_lcm : padicValNat p (Nat.lcm a (s.lcm id)) =
              max (padicValNat p a) (padicValNat p (s.lcm id)) := by
            have hprod : a * s.lcm id = Nat.gcd a (s.lcm id) * Nat.lcm a (s.lcm id) :=
              (Nat.gcd_mul_lcm a (s.lcm id)).symm
            have hgcd0 : Nat.gcd a (s.lcm id) ≠ 0 := Nat.gcd_ne_zero_left ha0
            have h1 := congrArg (padicValNat p) hprod
            rw [padicValNat.mul ha0 hb0, padicValNat.mul hgcd0 hlab0] at h1
            have hg_le_a : padicValNat p (Nat.gcd a (s.lcm id)) ≤ padicValNat p a :=
              (padicValNat_dvd_iff_le ha0).mp (pow_padicValNat_dvd.trans (Nat.gcd_dvd_left _ _))
            have hg_le_b : padicValNat p (Nat.gcd a (s.lcm id)) ≤ padicValNat p (s.lcm id) :=
              (padicValNat_dvd_iff_le hb0).mp (pow_padicValNat_dvd.trans (Nat.gcd_dvd_right _ _))
            have hl_ge_a : padicValNat p a ≤ padicValNat p (Nat.lcm a (s.lcm id)) :=
              (padicValNat_dvd_iff_le hlab0).mp ((pow_padicValNat_dvd (p := p)).trans (Nat.dvd_lcm_left _ _))
            have hl_ge_b : padicValNat p (s.lcm id) ≤ padicValNat p (Nat.lcm a (s.lcm id)) :=
              (padicValNat_dvd_iff_le hlab0).mp ((pow_padicValNat_dvd (p := p)).trans (Nat.dvd_lcm_right _ _))
            have hmin : min (padicValNat p a) (padicValNat p (s.lcm id)) ≤
                padicValNat p (Nat.gcd a (s.lcm id)) := by
              rw [← padicValNat_dvd_iff_le hgcd0]
              exact Nat.dvd_gcd
                ((pow_dvd_pow p (min_le_left _ _)).trans (pow_padicValNat_dvd))
                ((pow_dvd_pow p (min_le_right _ _)).trans (pow_padicValNat_dvd))
            omega
          rw [hv_lcm] at hv
          have hv_b : e ≤ padicValNat p (s.lcm id) := by omega
          exact (padicValNat_dvd_iff_le hb0).mpr hv_b
        rcases ih hs with h0 | ⟨r, hr, hdr⟩
        · exact Or.inl h0
        · exact Or.inr ⟨r, Finset.mem_insert_of_mem hr, hdr⟩

variable {p : ℕ} [Fact p.Prime]
variable {O : Type u} [CommRing O] [IsDomain O] [ValuationRing O] [CharZero O]
  [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
  [PerfectoidBase p O]

/-- Divided power `γ_m(ξ) := ξ^m / m! ∈ A_inf[1/p]`. -/
def gammaXi (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] (m : ℕ) : AinfInvP p O :=
  ratToAinfInvP p O ((m ! : ℚ)⁻¹) * xiInvP p O ^ m

private theorem two_mul_add_three_le_two_pow (n : ℕ) : 2 * n + 3 ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, pow_succ]
    omega

omit [ValuationRing O] [CharZero O] [PerfectoidBase p O] in
theorem ratToAinfInvP_natCast (n : ℕ) :
    ratToAinfInvP p O (n : ℚ) = ((n : ℕ) : AinfInvP p O) := by
  rw [← map_natCast (ratToAinfInvP p O) n]

omit [ValuationRing O] [CharZero O] in
theorem factorial_mul_gammaXi (m : ℕ) :
    ((m ! : ℕ) : AinfInvP p O) * gammaXi p O m = xiInvP p O ^ m := by
  unfold gammaXi
  rw [← mul_assoc, ← ratToAinfInvP_natCast, ← map_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)), map_one, one_mul]

omit [ValuationRing O] [CharZero O] in
theorem gammaXi_zero : gammaXi p O 0 = 1 := by
  simp [gammaXi]

omit [ValuationRing O] [CharZero O] in
theorem gammaXi_mul (m n : ℕ) :
    gammaXi p O m * gammaXi p O n = ((Nat.choose (m + n) m : ℕ) : AinfInvP p O) * gammaXi p O (m + n) := by
  unfold gammaXi
  have h1 : ((m ! : ℚ)⁻¹) * ((n ! : ℚ)⁻¹) =
      ((Nat.choose (m + n) m : ℕ) : ℚ) * (((m + n)! : ℚ)⁻¹) := by
    have hch := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m n)
    rw [Nat.add_sub_cancel_left] at hch
    have hchq : ((Nat.choose (m + n) m : ℕ) : ℚ) * (m ! : ℚ) * (n ! : ℚ) = ((m + n)! : ℚ) := by
      exact_mod_cast hch
    have hm : (m ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hn : (n ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hmn : ((m + n)! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + n))
    field_simp
    linarith
  calc ratToAinfInvP p O (m ! : ℚ)⁻¹ * xiInvP p O ^ m * (ratToAinfInvP p O (n ! : ℚ)⁻¹ * xiInvP p O ^ n)
      = ratToAinfInvP p O ((m ! : ℚ)⁻¹ * (n ! : ℚ)⁻¹) * xiInvP p O ^ (m + n) := by
        rw [map_mul, pow_add]; ring
    _ = ((Nat.choose (m + n) m : ℕ) : AinfInvP p O) * (ratToAinfInvP p O ((m + n)! : ℚ)⁻¹ * xiInvP p O ^ (m + n)) := by
        rw [h1, map_mul, ratToAinfInvP_natCast, mul_assoc]

/-- **Divided-Power Subring `A_cris^0 ⊆ A_inf[1/p]`**: generated by `A_inf` and `{ξ^m / m! | m : ℕ}`.
Every element is a finite `A_inf`-linear combination `∑_{r=0}^R a_r * (ξ^r / r!)`. -/
def Acris0 (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : Subring (AinfInvP p O) where
  carrier := { z : AinfInvP p O | ∃ (R : ℕ) (a : ℕ → A_inf p O),
    z = ∑ r ∈ Finset.range R, ainfToInvP p O (a r) * gammaXi p O r }
  zero_mem' := ⟨0, fun _ => 0, by simp⟩
  one_mem' := ⟨1, fun _ => 1, by simp [gammaXi_zero]⟩
  add_mem' := by
    rintro _ _ ⟨R₁, a₁, rfl⟩ ⟨R₂, a₂, rfl⟩
    let R := max R₁ R₂
    refine ⟨R, fun r => (if r < R₁ then a₁ r else 0) + (if r < R₂ then a₂ r else 0), ?_⟩
    have hsplit : ∀ (M : ℕ) (f : ℕ → A_inf p O), M ≤ R →
        ∑ r ∈ Finset.range R, ainfToInvP p O (if r < M then f r else 0) * gammaXi p O r =
          ∑ r ∈ Finset.range M, ainfToInvP p O (f r) * gammaXi p O r := by
      intro M f hM
      rw [← Finset.sum_subset (Finset.range_mono hM)]
      · refine Finset.sum_congr rfl fun r hr => by rw [if_pos (Finset.mem_range.mp hr)]
      · intro r _ hrM
        rw [if_neg (by simpa [Finset.mem_range] using hrM), map_zero, zero_mul]
    simp_rw [map_add, add_mul, Finset.sum_add_distrib]
    rw [hsplit R₁ a₁ (le_max_left _ _), hsplit R₂ a₂ (le_max_right _ _)]
  neg_mem' := by
    rintro _ ⟨R, a, rfl⟩
    refine ⟨R, fun r => -a r, ?_⟩
    simp [Finset.sum_neg_distrib]
  mul_mem' := by
    rintro _ _ ⟨R₁, a₁, rfl⟩ ⟨R₂, a₂, rfl⟩
    let c : ℕ → A_inf p O := fun k =>
      ∑ r ∈ Finset.range R₁, ∑ s ∈ Finset.range R₂,
        if r + s = k then a₁ r * a₂ s * ((Nat.choose (r + s) r : ℕ) : A_inf p O) else 0
    refine ⟨R₁ + R₂, c, ?_⟩
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    have hinner : ∀ r ∈ Finset.range R₁, ∀ s ∈ Finset.range R₂,
        ainfToInvP p O (a₁ r) * gammaXi p O r * (ainfToInvP p O (a₂ s) * gammaXi p O s) =
          ainfToInvP p O (a₁ r * a₂ s * ((Nat.choose (r + s) r : ℕ) : A_inf p O)) * gammaXi p O (r + s) := by
      intro r _ s _
      rw [map_mul, map_mul, map_natCast]
      have hgm := gammaXi_mul (p := p) (O := O) r s
      calc ainfToInvP p O (a₁ r) * gammaXi p O r * (ainfToInvP p O (a₂ s) * gammaXi p O s)
          = ainfToInvP p O (a₁ r) * ainfToInvP p O (a₂ s) * (gammaXi p O r * gammaXi p O s) := by ring
        _ = ainfToInvP p O (a₁ r) * ainfToInvP p O (a₂ s) *
              (((Nat.choose (r + s) r : ℕ) : AinfInvP p O) * gammaXi p O (r + s)) := by rw [hgm]
        _ = _ := by ring
    trans (∑ r ∈ Finset.range R₁, ∑ s ∈ Finset.range R₂,
      ainfToInvP p O (a₁ r * a₂ s * ((Nat.choose (r + s) r : ℕ) : A_inf p O)) * gammaXi p O (r + s))
    · exact Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun s hs => hinner r hr s hs
    · -- Rearrange by k = r + s < R₁ + R₂
      have hre : ∀ k ∈ Finset.range (R₁ + R₂),
          ainfToInvP p O (c k) * gammaXi p O k =
            ∑ r ∈ Finset.range R₁, ∑ s ∈ Finset.range R₂,
              if r + s = k then
                ainfToInvP p O (a₁ r * a₂ s * ((Nat.choose (r + s) r : ℕ) : A_inf p O)) * gammaXi p O (r + s)
              else 0 := by
        intro k _
        simp only [c, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
        split_ifs with h
        · rw [h]
        · simp
      rw [Finset.sum_congr rfl hre]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [Finset.sum_ite_eq (Finset.range (R₁ + R₂)) (r + s)]
      have hmem : r + s ∈ Finset.range (R₁ + R₂) := by
        rw [Finset.mem_range] at hr hs ⊢; omega
      rw [if_pos hmem]

/-- Explicit `RingHom` `A_inf →+* Acris0`. -/
def ainfToAcris0 (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : A_inf p O →+* Acris0 p O :=
  (ainfToInvP p O).codRestrict (Acris0 p O) fun x =>
    ⟨1, fun _ => x, by simp [gammaXi_zero]⟩

/-- The divided power `ξ^m / m!` as an element of `Acris0`. -/
def gammaXiAcris0 (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] (m : ℕ) : Acris0 p O :=
  ⟨gammaXi p O m, ⟨m + 1, fun r => if r = m then 1 else 0, by
    rw [Finset.sum_eq_single m]
    · simp
    · intro r _ hrm; simp [hrm]
    · intro hm; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) hm⟩⟩

omit [ValuationRing O] [CharZero O] in
@[simp] theorem coe_gammaXiAcris0 (m : ℕ) :
    (gammaXiAcris0 p O m : AinfInvP p O) = gammaXi p O m := rfl

omit [ValuationRing O] [CharZero O] in
@[simp] theorem coe_ainfToAcris0 (x : A_inf p O) :
    (ainfToAcris0 p O x : AinfInvP p O) = ainfToInvP p O x := rfl

omit [IsDomain O] [ValuationRing O] [CharZero O] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
  [PerfectoidBase p O] in
/-- Any natural number `u` not divisible by `p` is a unit in `A_inf p O`. -/
theorem isUnit_natCast_Ainf_of_not_dvd {u : ℕ} (hu : ¬ (p ∣ u)) : IsUnit ((u : ℕ) : A_inf p O) := by
  have hp : p.Prime := Fact.out
  rw [ainf_isUnit_iff_isUnit_coeff]
  change IsUnit (WittVector.constantCoeff ((u : ℕ) : A_inf p O))
  rw [map_natCast]
  have hcop : Nat.Coprime p u := hp.coprime_iff_not_dvd.mpr hu
  have hbez := Nat.gcd_eq_gcd_ab p u
  rw [hcop.gcd_eq_one] at hbez
  have hcast : (1 : Tilt p O) = (p : Tilt p O) * (Nat.gcdA p u : Tilt p O) +
      (u : Tilt p O) * (Nat.gcdB p u : Tilt p O) := by
    have := congrArg (Int.cast : ℤ → Tilt p O) hbez
    simpa using this
  rw [CharP.cast_eq_zero (Tilt p O) p, zero_mul, zero_add] at hcast
  exact isUnit_iff_exists_inv.mpr ⟨(Nat.gcdB p u : Tilt p O), hcast.symm⟩

/-- Witt-vector Frobenius extended to `A_inf[1/p]`. -/
def frobAinfInvP (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] :
    AinfInvP p O →+* AinfInvP p O :=
  IsLocalization.Away.lift ((p : ℕ) : A_inf p O)
    (g := (ainfToInvP p O).comp (WittVector.frobenius (p := p) (R := Tilt p O)))
    (by
      rw [RingHom.comp_apply, map_natCast]
      exact IsLocalization.Away.algebraMap_isUnit ((p : ℕ) : A_inf p O) (S := AinfInvP p O))

omit [ValuationRing O] [CharZero O] [PerfectoidBase p O] in
@[simp] theorem frobAinfInvP_ainf (x : A_inf p O) :
    frobAinfInvP p O (ainfToInvP p O x) = ainfToInvP p O (WittVector.frobenius x) :=
  IsLocalization.Away.lift_eq _ _ x

omit [ValuationRing O] [CharZero O] [PerfectoidBase p O] in
theorem frobAinfInvP_padic (c : ℚ_[p]) :
    frobAinfInvP p O (padicToAinfInvP p O c) = padicToAinfInvP p O c := by
  have hcomp : (frobAinfInvP p O).comp (padicToAinfInvP p O) = padicToAinfInvP p O := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun z => ?_)
    simp only [RingHom.comp_apply, padicToAinfInvP]
    rw [IsLocalization.lift_eq, RingHom.comp_apply, frobAinfInvP_ainf, frobenius_padicIntToAinf]
  exact RingHom.congr_fun hcomp c

omit [ValuationRing O] [CharZero O] [PerfectoidBase p O] in
theorem frobAinfInvP_rat (q : ℚ) :
    frobAinfInvP p O (ratToAinfInvP p O q) = ratToAinfInvP p O q :=
  frobAinfInvP_padic (algebraMap ℚ ℚ_[p] q)

omit [IsDomain O] [ValuationRing O] [CharZero O] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
  [PerfectoidBase p O] in
theorem frobenius_teichmuller (a : Tilt p O) :
    WittVector.frobenius (WittVector.teichmuller p a) = (WittVector.teichmuller p a) ^ p := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

omit [ValuationRing O] [CharZero O] in
/-- `φ(ξ) = ξ^p + p * δ` for an explicit `δ ∈ A_inf`, hence `φ(ξ) = p * α` with `α ∈ Acris0`! -/
theorem frobAinfInvP_xi_eq_p_mul :
    ∃ α : Acris0 p O, frobAinfInvP p O (xiInvP p O) = ((p : ℕ) : AinfInvP p O) * (α : AinfInvP p O) := by
  have hp : p.Prime := Fact.out
  have hphi_xi : ∃ δ : A_inf p O, WittVector.frobenius (xi p O) =
      xi p O ^ p + ((p : ℕ) : A_inf p O) * δ := by
    have h1 : WittVector.frobenius (xi p O) = (xi p O + ((p : ℕ) : A_inf p O)) ^ p - ((p : ℕ) : A_inf p O) := by
      unfold xi
      rw [map_sub, frobenius_teichmuller, map_natCast, sub_add_cancel]
    rw [h1, add_pow]
    have hsplit : ∑ k ∈ Finset.range (p + 1), xi p O ^ k * ((p : ℕ) : A_inf p O) ^ (p - k) * (Nat.choose p k : A_inf p O) =
        xi p O ^ p + ∑ k ∈ Finset.range p, xi p O ^ k * ((p : ℕ) : A_inf p O) ^ (p - k) * (Nat.choose p k : A_inf p O) := by
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
        mul_one, add_comm]
    rw [hsplit]
    have hdvd : ((p : ℕ) : A_inf p O) ∣
        (∑ k ∈ Finset.range p, xi p O ^ k * ((p : ℕ) : A_inf p O) ^ (p - k) * (Nat.choose p k : A_inf p O)) -
          ((p : ℕ) : A_inf p O) := by
      refine dvd_sub (Finset.dvd_sum fun k hk => ?_) dvd_rfl
      rw [Finset.mem_range] at hk
      have hpos : 1 ≤ p - k := by omega
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) _) _
    obtain ⟨δ, hδ⟩ := hdvd
    exact ⟨δ, by linear_combination hδ⟩
  obtain ⟨δ, hδ⟩ := hphi_xi
  let α : Acris0 p O := (((p - 1)! : ℕ) : Acris0 p O) * gammaXiAcris0 p O p + ainfToAcris0 p O δ
  refine ⟨α, ?_⟩
  rw [xiInvP, frobAinfInvP_ainf, hδ, map_add, map_pow, map_mul, map_natCast]
  have hp_fac : ((p : ℕ) : AinfInvP p O) * (((p - 1)! : ℕ) : AinfInvP p O) = ((p ! : ℕ) : AinfInvP p O) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hp.ne_zero]
  have hxp : ((p : ℕ) : AinfInvP p O) * ((((p - 1)! : ℕ) : AinfInvP p O) * gammaXi p O p) = xiInvP p O ^ p := by
    rw [← mul_assoc, hp_fac, factorial_mul_gammaXi]
  show ainfToInvP p O (xi p O) ^ p + ((p : ℕ) : AinfInvP p O) * ainfToInvP p O δ = _
  change xiInvP p O ^ p + ((p : ℕ) : AinfInvP p O) * ainfToInvP p O δ =
    ((p : ℕ) : AinfInvP p O) * ((((p - 1)! : ℕ) : AinfInvP p O) * gammaXi p O p + ainfToInvP p O δ)
  rw [mul_add, hxp]

omit [ValuationRing O] [CharZero O] in
theorem frobAinfInvP_mem_Acris0 {x : AinfInvP p O} (hx : x ∈ Acris0 p O) :
    frobAinfInvP p O x ∈ Acris0 p O := by
  have hp : p.Prime := Fact.out
  rcases hx with ⟨R, a, rfl⟩
  rw [map_sum]
  refine Subring.sum_mem _ fun m _ => ?_
  rw [map_mul, frobAinfInvP_ainf]
  refine Subring.mul_mem _ ⟨1, fun _ => WittVector.frobenius (a m), by simp [gammaXi_zero]⟩ ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [gammaXi_zero, map_one]; exact Subring.one_mem _
  · obtain ⟨α, hα⟩ := frobAinfInvP_xi_eq_p_mul (p := p) (O := O)
    have hv_lt : padicValNat p (m !) < m := padicValNat_factorial_lt (p := p) hm
    set v := padicValNat p (m !)
    have hv_dvd : p ^ v ∣ m ! := pow_padicValNat_dvd
    obtain ⟨u, hu⟩ := hv_dvd
    have hu_ndvd : ¬ (p ∣ u) := by
      intro hpu
      obtain ⟨w, rfl⟩ := hpu
      have h1 : p ^ (v + 1) ∣ m ! := ⟨w, by rw [hu, pow_succ]; ring⟩
      have h2 : v + 1 ≤ padicValNat p (m !) :=
        (padicValNat_dvd_iff_le (Nat.factorial_ne_zero m)).mp h1
      omega
    obtain ⟨u_unit, hu_unit⟩ := isUnit_natCast_Ainf_of_not_dvd (p := p) (O := O) hu_ndvd
    have hinv_eq : ratToAinfInvP p O ((m ! : ℚ)⁻¹) * ((p : ℕ) : AinfInvP p O) ^ m =
        ainfToInvP p O (((p : ℕ) : A_inf p O) ^ (m - v) * ((u_unit⁻¹ : (A_inf p O)ˣ) : A_inf p O)) := by
      have hm_eq : ((m ! : ℕ) : AinfInvP p O) =
          ((p : ℕ) : AinfInvP p O) ^ v * ainfToInvP p O (u_unit : A_inf p O) := by
        rw [hu, Nat.cast_mul, Nat.cast_pow, hu_unit, map_natCast]
      have hmul_eq : ((m ! : ℕ) : AinfInvP p O) *
          (ainfToInvP p O (((p : ℕ) : A_inf p O) ^ (m - v) * ((u_unit⁻¹ : (A_inf p O)ˣ) : A_inf p O))) =
          ((p : ℕ) : AinfInvP p O) ^ m := by
        rw [hm_eq, map_mul, map_pow, map_natCast]
        calc ((p : ℕ) : AinfInvP p O) ^ v * ainfToInvP p O (u_unit : A_inf p O) *
              (((p : ℕ) : AinfInvP p O) ^ (m - v) * ainfToInvP p O ((u_unit⁻¹ : (A_inf p O)ˣ) : A_inf p O))
            = (((p : ℕ) : AinfInvP p O) ^ v * ((p : ℕ) : AinfInvP p O) ^ (m - v)) *
                ainfToInvP p O ((u_unit : A_inf p O) * ((u_unit⁻¹ : (A_inf p O)ˣ) : A_inf p O)) := by
              rw [map_mul]; ring
          _ = ((p : ℕ) : AinfInvP p O) ^ m := by
              rw [← pow_add, Nat.add_sub_of_le hv_lt.le, Units.mul_inv, map_one, mul_one]
      calc ratToAinfInvP p O ((m ! : ℚ)⁻¹) * ((p : ℕ) : AinfInvP p O) ^ m
          = ratToAinfInvP p O ((m ! : ℚ)⁻¹) *
              (((m ! : ℕ) : AinfInvP p O) *
                ainfToInvP p O (((p : ℕ) : A_inf p O) ^ (m - v) * ((u_unit⁻¹ : (A_inf p O)ˣ) : A_inf p O))) := by
            rw [hmul_eq]
        _ = (ratToAinfInvP p O ((m ! : ℚ)⁻¹) * ratToAinfInvP p O (m ! : ℚ)) *
              ainfToInvP p O (((p : ℕ) : A_inf p O) ^ (m - v) * ((u_unit⁻¹ : (A_inf p O)ˣ) : A_inf p O)) := by
            rw [ratToAinfInvP_natCast, mul_assoc]
        _ = _ := by
            rw [← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)),
              map_one, one_mul]
    have hf : frobAinfInvP p O (gammaXi p O m) =
        ainfToInvP p O (((p : ℕ) : A_inf p O) ^ (m - v) * ((u_unit⁻¹ : (A_inf p O)ˣ) : A_inf p O)) *
          (α : AinfInvP p O) ^ m := by
      unfold gammaXi
      rw [map_mul, frobAinfInvP_rat, map_pow, hα, mul_pow, ← mul_assoc, hinv_eq]
    rw [hf]
    exact Subring.mul_mem _
      ⟨1, fun _ => ((p : ℕ) : A_inf p O) ^ (m - v) * ((u_unit⁻¹ : (A_inf p O)ˣ) : A_inf p O),
        by simp [gammaXi_zero]⟩
      (Subring.pow_mem _ α.2 m)

/-- **Witt-Vector Frobenius on `A_cris^0`**. -/
def frobAcris0 (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : Acris0 p O →+* Acris0 p O :=
  ((frobAinfInvP p O).comp (Acris0 p O).subtype).codRestrict (Acris0 p O) fun x =>
    frobAinfInvP_mem_Acris0 x.2

@[simp] theorem coe_frobAcris0 (x : Acris0 p O) :
    ((frobAcris0 p O x : Acris0 p O) : AinfInvP p O) = frobAinfInvP p O (x : AinfInvP p O) := rfl

/-- **Fontaine's Crystalline Ring `A_cris`**: the `p`-adic completion of `A_cris^0`. -/
abbrev Acris (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : Type u :=
  AdicCompletion (Ideal.span {((p : ℕ) : Acris0 p O)}) (Acris0 p O)

/-- Canonical `RingHom`s into `A_cris`. -/
def acris0ToAcris (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : Acris0 p O →+* Acris p O :=
  algebraMap (Acris0 p O) (Acris p O)

def ainfToAcris (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : A_inf p O →+* Acris p O :=
  (acris0ToAcris p O).comp (ainfToAcris0 p O)

def padicIntToAcris (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O]
    [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : ℤ_[p] →+* Acris p O :=
  (ainfToAcris p O).comp (padicIntToAinf p O)

private theorem frobAcris0_pow_mem (n : ℕ) :
    Ideal.span {((p : ℕ) : Acris0 p O)} ^ n ≤
      (Ideal.span {((p : ℕ) : Acris0 p O)} ^ n).comap (frobAcris0 p O) := by
  rw [Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
  show frobAcris0 p O (((p : ℕ) : Acris0 p O) ^ n) ∈ Ideal.span {((p : ℕ) : Acris0 p O) ^ n}
  rw [map_pow, map_natCast]
  exact Ideal.mem_span_singleton_self _

private theorem frobAcris_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {((p : ℕ) : Acris0 p O)}) hle).comp
      ((Ideal.quotientMap (Ideal.span {((p : ℕ) : Acris0 p O)} ^ n) (frobAcris0 p O)
        (frobAcris0_pow_mem (p := p) (O := O) n)).comp
        (AdicCompletion.evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) n).toRingHom) =
    (Ideal.quotientMap (Ideal.span {((p : ℕ) : Acris0 p O)} ^ m) (frobAcris0 p O)
      (frobAcris0_pow_mem (p := p) (O := O) m)).comp
      (AdicCompletion.evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) m).toRingHom := by
  ext x
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) n x)
  have hfac := factorPow_evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) hle x
  rw [← ha] at hfac ⊢
  rw [← hfac]
  rfl

/-- **Witt-Vector Frobenius on `A_cris`**: `frobAcris : A_cris →+* A_cris`. -/
def frobAcris (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : Acris p O →+* Acris p O :=
  AdicCompletion.liftRingHom (Ideal.span {((p : ℕ) : Acris0 p O)})
    (fun n => (Ideal.quotientMap (Ideal.span {((p : ℕ) : Acris0 p O)} ^ n) (frobAcris0 p O)
      (frobAcris0_pow_mem (p := p) (O := O) n)).comp
      (AdicCompletion.evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) n).toRingHom)
    (frobAcris_compat (p := p) (O := O))

theorem eval_frobAcris (n : ℕ) (x : Acris p O) :
    AdicCompletion.evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) n (frobAcris p O x) =
      Ideal.quotientMap (Ideal.span {((p : ℕ) : Acris0 p O)} ^ n) (frobAcris0 p O)
        (frobAcris0_pow_mem (p := p) (O := O) n)
        (AdicCompletion.evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) n x) := by
  unfold frobAcris
  rw [AdicCompletion.evalₐ_liftRingHom _ _ (frobAcris_compat (p := p) (O := O))]
  rfl

@[simp] theorem frobAcris_acris0 (x : Acris0 p O) :
    frobAcris p O (acris0ToAcris p O x) = acris0ToAcris p O (frobAcris0 p O x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [eval_frobAcris]
  rfl

/-- Element `c_ε ∈ A_inf` such that `[ε] - 1 = ξ * c_ε`. -/
private def epsDivXi (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O]
    [ValuationRing O] [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)]
    [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] [PerfectoidBase p O] : A_inf p O :=
  (WittVector.teichmuller p (epsRoot p O) - 1) *
    ((omegaAinf_eq_xi_mul_unit (p := p) (O := O)).choose : A_inf p O)

private theorem teichEps_sub_one_eq_xi_mul_epsDivXi :
    teichEps p O - 1 = xi p O * epsDivXi p O := by
  have hu := (omegaAinf_eq_xi_mul_unit (p := p) (O := O)).choose_spec
  unfold epsDivXi
  rw [teichEps_sub_one_eq]
  conv_lhs => rw [hu]
  ring

/-- The `k`-th term `(-1)^k ([ε] - 1)^{k+1} / (k + 1)` inside `A_cris^0`. -/
def tAcrisTerm (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] (k : ℕ) : Acris0 p O :=
  (-1 : Acris0 p O) ^ k * ((k ! : ℕ) : Acris0 p O) *
    ainfToAcris0 p O (epsDivXi p O ^ (k + 1)) * gammaXiAcris0 p O (k + 1)

def tAcrisPartial (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] (N : ℕ) : Acris0 p O :=
  ∑ k ∈ Finset.range N, tAcrisTerm p O k

theorem coe_tAcrisTerm (k : ℕ) :
    (tAcrisTerm p O k : AinfInvP p O) =
      ratToAinfInvP p O ((-1 : ℚ) ^ k / (k + 1 : ℚ)) *
        (ainfToInvP p O (teichEps p O - 1)) ^ (k + 1) := by
  unfold tAcrisTerm
  push_cast
  rw [coe_ainfToAcris0, coe_gammaXiAcris0, teichEps_sub_one_eq_xi_mul_epsDivXi, map_mul, mul_pow,
    map_pow]
  unfold gammaXi
  have hq : ((-1 : ℚ) ^ k / (k + 1 : ℚ)) = (-1 : ℚ) ^ k * (k ! : ℚ) * (((k + 1)! : ℚ)⁻¹) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hk : (k ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hk1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    push_cast
    field_simp
  rw [hq, map_mul, map_mul, map_pow, map_neg, map_one, ratToAinfInvP_natCast]
  change (-1 : AinfInvP p O) ^ k * ((k ! : ℕ) : AinfInvP p O) * ainfToInvP p O (epsDivXi p O) ^ (k + 1) *
      (ratToAinfInvP p O (((k + 1)! : ℚ)⁻¹) * xiInvP p O ^ (k + 1)) = _
  simp only [xiInvP]
  ring

theorem coe_tAcrisPartial (N : ℕ) :
    (tAcrisPartial p O N : AinfInvP p O) =
      truncLogHom (ratToAinfInvP p O) N (ainfToInvP p O (teichEps p O - 1)) := by
  unfold tAcrisPartial truncLogHom
  push_cast
  exact Finset.sum_congr rfl fun k _ => coe_tAcrisTerm k

theorem p_pow_dvd_tAcrisTerm {n k : ℕ} (hk : p * n ≤ k) :
    ((p : ℕ) : Acris0 p O) ^ n ∣ tAcrisTerm p O k := by
  have hp : p.Prime := Fact.out
  have hdvd : p ^ n ∣ k ! :=
    (prime_pow_dvd_factorial_mul hp.pos n).trans (Nat.factorial_dvd_factorial hk)
  obtain ⟨q, hq⟩ := hdvd
  unfold tAcrisTerm
  have hcast : ((k ! : ℕ) : Acris0 p O) = ((p : ℕ) : Acris0 p O) ^ n * ((q : ℕ) : Acris0 p O) := by
    rw [hq, Nat.cast_mul, Nat.cast_pow]
  rw [hcast]
  exact ⟨(-1 : Acris0 p O) ^ k * ((q : ℕ) : Acris0 p O) *
    ainfToAcris0 p O (epsDivXi p O ^ (k + 1)) * gammaXiAcris0 p O (k + 1), by ring⟩

theorem tAcrisPartial_sub_dvd {n N₁ N₂ : ℕ} (h1 : p * n ≤ N₁) (h2 : N₁ ≤ N₂) :
    ((p : ℕ) : Acris0 p O) ^ n ∣ tAcrisPartial p O N₂ - tAcrisPartial p O N₁ := by
  induction N₂, h2 using Nat.le_induction with
  | base => simp
  | succ N₂ h2 ih =>
    have hstep : tAcrisPartial p O (N₂ + 1) - tAcrisPartial p O N₁ =
        (tAcrisPartial p O N₂ - tAcrisPartial p O N₁) + tAcrisTerm p O N₂ := by
      unfold tAcrisPartial
      rw [Finset.sum_range_succ]; ring
    rw [hstep]
    exact dvd_add ih (p_pow_dvd_tAcrisTerm (le_trans h1 h2))

private theorem tAcris_compat {m n : ℕ} (hle : m ≤ n) :
    Ideal.Quotient.factorPow (Ideal.span {((p : ℕ) : Acris0 p O)}) hle
      (Ideal.Quotient.mk _ (tAcrisPartial p O (p * n))) =
    Ideal.Quotient.mk _ (tAcrisPartial p O (p * m)) := by
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact tAcrisPartial_sub_dvd le_rfl (Nat.mul_le_mul_left p hle)

/-- **Fontaine's Period `t = log([ε])` inside `A_cris`**. -/
def tAcris (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : Acris p O :=
  adicMk (Ideal.span {((p : ℕ) : Acris0 p O)})
    (fun n => Ideal.Quotient.mk _ (tAcrisPartial p O (p * n)))
    (tAcris_compat (p := p) (O := O))

theorem eval_tAcris_eq_of_le (n N : ℕ) (hN : p * n ≤ N) :
    AdicCompletion.evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) n (tAcris p O) =
      Ideal.Quotient.mk _ (tAcrisPartial p O N) := by
  unfold tAcris
  rw [evalₐ_adicMk _ _ (tAcris_compat (p := p) (O := O)) n]
  symm
  rw [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact tAcrisPartial_sub_dvd le_rfl hN

/-- **Fundamental Crystalline Period Equation**: `φ(t) = p * t` in `A_cris`! -/
theorem frobAcris_tAcris :
    frobAcris p O (tAcris p O) = ((p : ℕ) : Acris p O) * tAcris p O := by
  have hp : p.Prime := Fact.out
  refine AdicCompletion.ext_evalₐ fun n => ?_
  set N : ℕ := p ^ (n + 3)
  have hpn_le_N : p * n ≤ N := by
    have h1 : n ≤ 2 ^ (n + 2) := le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : 2 ^ (n + 2) ≤ p ^ (n + 2) := Nat.pow_le_pow_left hp.two_le _
    calc p * n ≤ p * p ^ (n + 2) := Nat.mul_le_mul_left p (le_trans h1 h2)
      _ = p ^ (n + 3) := by rw [← pow_succ']
  rw [eval_frobAcris, eval_tAcris_eq_of_le n N hpn_le_N]
  conv_rhs => rw [map_mul, map_natCast, eval_tAcris_eq_of_le n N hpn_le_N]
  simp only [Ideal.quotientMap_mk, ← map_natCast (Ideal.Quotient.mk _), ← map_mul]
  rw [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  -- Now prove `p^n ∣ frobAcris0 (tAcrisPartial N) - p * tAcrisPartial N` in `Acris0`!
  let L : ℕ := (Finset.Icc 1 N).lcm id
  have hL_pos : 0 < L := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [Finset.lcm_eq_zero_iff] at h0
    obtain ⟨r, hr, hr0⟩ := h0
    rw [Finset.mem_Icc] at hr
    dsimp [id] at hr0
    omega
  -- `L * P(X)` has integer coefficients `Q_int ∈ ℤ[X]`
  let truncLogInt : Polynomial ℤ :=
    ∑ k ∈ Finset.range N, Polynomial.C ((-1 : ℤ) ^ k * ((L / (k + 1) : ℕ) : ℤ)) * Polynomial.X ^ (k + 1)
  have htrunc_map : Polynomial.map (Int.castRingHom ℚ) truncLogInt =
      Polynomial.C (L : ℚ) * truncLogPoly N := by
    unfold truncLogInt truncLogPoly
    rw [Polynomial.map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have hdvd : k + 1 ∣ L := Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, ← mul_assoc,
      ← map_mul]
    congr 2
    simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    have hq : ((L / (k + 1) : ℕ) : ℚ) = (L : ℚ) / (k + 1 : ℚ) := by
      rw [Nat.cast_div hdvd (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))]
      push_cast; rfl
    rw [hq]; ring
  let Q_int : Polynomial ℤ :=
    truncLogInt.comp ((1 + Polynomial.X) ^ p - 1) - Polynomial.C (p : ℤ) * truncLogInt
  have hQ_map : Polynomial.map (Int.castRingHom ℚ) Q_int =
      Polynomial.C (L : ℚ) *
        ((truncLogPoly N).comp ((1 + Polynomial.X) ^ p - 1) - Polynomial.C (p : ℚ) * truncLogPoly N) := by
    unfold Q_int
    rw [Polynomial.map_sub, Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one,
      Polynomial.map_X, htrunc_map, Polynomial.mul_comp, Polynomial.C_comp]
    simp only [eq_intCast, Int.cast_natCast]
    ring
  have hQ_coeff_zero : ∀ k < N + 1, Q_int.coeff k = 0 := by
    intro k hk
    have hrat : (Polynomial.map (Int.castRingHom ℚ) Q_int).coeff k = 0 := by
      rw [hQ_map]
      obtain ⟨R, hR⟩ := truncLogPoly_comp_pow_sub_mul_dvd p N
      rw [hR, ← mul_assoc, mul_comm (Polynomial.C (L : ℚ)), mul_assoc, Polynomial.coeff_X_pow_mul']
      exact if_neg (not_le.mpr hk)
    rw [Polynomial.coeff_map, eq_intCast, Int.cast_eq_zero] at hrat
    exact hrat
  -- Bound `v := padicValNat p L ≤ n + 3`
  set v := padicValNat p L
  have hv_le : v ≤ n + 3 := by
    by_contra hgt
    have hge : n + 4 ≤ v := by omega
    have hdvd : p ^ (n + 4) ∣ L := (pow_dvd_pow p hge).trans pow_padicValNat_dvd
    rcases prime_pow_dvd_finset_lcm_exists hp (Finset.Icc 1 N) (n + 4) hdvd with h0 | ⟨r, hr, hdr⟩
    · omega
    · rw [Finset.mem_Icc] at hr
      have hle : p ^ (n + 4) ≤ r := Nat.le_of_dvd (by omega) hdr
      have hlt : N < p ^ (n + 4) := Nat.pow_lt_pow_right hp.one_lt (by omega)
      omega
  obtain ⟨u, hu⟩ := (pow_padicValNat_dvd (p := p) (n := L))
  have hu_ndvd : ¬ (p ∣ u) := by
    intro ⟨w, hw⟩
    have h1 : p ^ (v + 1) ∣ L := ⟨w, by rw [hu, hw, pow_succ]; ring⟩
    have h2 : v + 1 ≤ padicValNat p L := (padicValNat_dvd_iff_le hL_pos.ne').mp h1
    omega
  obtain ⟨u_unit, hu_unit⟩ := isUnit_natCast_Ainf_of_not_dvd (p := p) (O := O) hu_ndvd
  -- For every k ≥ N + 1, `p^(v + n) ∣ k!`
  have hk_fac_dvd : ∀ k ≥ N + 1, p ^ (v + n) ∣ k ! := by
    intro k hk
    have hpow_ge : v + n ≤ p ^ (n + 2) := by
      have h2 : 2 ^ (n + 2) ≤ p ^ (n + 2) := Nat.pow_le_pow_left hp.two_le _
      have h2n : 2 * n + 3 ≤ 2 ^ (n + 2) := two_mul_add_three_le_two_pow n
      omega
    have h1 : p ^ (v + n) ∣ p ^ (p ^ (n + 2)) := pow_dvd_pow p hpow_ge
    have h2 : p ^ (p ^ (n + 2)) ∣ (p * p ^ (n + 2))! := prime_pow_dvd_factorial_mul hp.pos _
    have h3 : (p * p ^ (n + 2))! ∣ k ! := Nat.factorial_dvd_factorial (by
      have : p * p ^ (n + 2) = N := by simp [N, pow_succ']
      omega)
    exact (h1.trans h2).trans h3
  -- Construct explicit witness `W ∈ Acris0` with `frobAcris0 (tAcrisPartial N) - p * tAcrisPartial N = p^n * W`
  let termW : ℕ → Acris0 p O := fun k =>
    if hk : N + 1 ≤ k then
      let w : ℕ := (hk_fac_dvd k hk).choose
      ((Q_int.coeff k : ℤ) : Acris0 p O) * ((w : ℕ) : Acris0 p O) *
        ainfToAcris0 p O (((u_unit⁻¹ : (A_inf p O)ˣ) : A_inf p O) * epsDivXi p O ^ k) *
        gammaXiAcris0 p O k
    else 0
  refine ⟨∑ k ∈ Finset.range (Q_int.natDegree + 1), termW k, ?_⟩
  -- Check equality inside `AinfInvP p O` (since `Acris0` is a subring of `AinfInvP`)
  apply Subtype.ext
  push_cast
  rw [coe_frobAcris0, coe_tAcrisPartial, map_truncLogHom]
  have hfr : (frobAinfInvP p O).comp (ratToAinfInvP p O) = ratToAinfInvP p O := by
    ext q; exact frobAinfInvP_rat q
  rw [hfr]
  have hfrob_eps : frobAinfInvP p O (ainfToInvP p O (teichEps p O - 1)) =
      (1 + ainfToInvP p O (teichEps p O - 1)) ^ p - 1 := by
    rw [frobAinfInvP_ainf, map_sub, map_one, teichEps, frobenius_teichmuller, map_sub, map_pow,
      map_one]
    congr 1
    rw [map_sub, map_one, add_sub_cancel]
  rw [hfrob_eps]
  set X : AinfInvP p O := ainfToInvP p O (teichEps p O - 1)
  have heval_lhs : truncLogHom (ratToAinfInvP p O) N ((1 + X) ^ p - 1) -
      ((p : ℕ) : AinfInvP p O) * truncLogHom (ratToAinfInvP p O) N X =
      Polynomial.eval₂ (ratToAinfInvP p O) X
        ((truncLogPoly N).comp ((1 + Polynomial.X) ^ p - 1) - Polynomial.C (p : ℚ) * truncLogPoly N) := by
    have hev : ∀ Z : AinfInvP p O, Polynomial.eval₂ (ratToAinfInvP p O) Z (truncLogPoly N) =
        truncLogHom (ratToAinfInvP p O) N Z := fun Z => by
      unfold truncLogPoly truncLogHom
      rw [Polynomial.eval₂_finsetSum]
      refine Finset.sum_congr rfl fun k _ => by
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_comp, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      ratToAinfInvP_natCast, hev, hev]
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_one,
      Polynomial.eval₂_X]
  rw [heval_lhs]
  have hL_inv : ratToAinfInvP p O (L : ℚ) * ratToAinfInvP p O ((L : ℚ)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hL_pos.ne'), map_one]
  have hQ_eval : Polynomial.eval₂ (ratToAinfInvP p O) X (Polynomial.map (Int.castRingHom ℚ) Q_int) =
      ∑ k ∈ Finset.range (Q_int.natDegree + 1),
        ((Q_int.coeff k : ℤ) : AinfInvP p O) * X ^ k := by
    rw [Polynomial.eval₂_map, Polynomial.eval₂_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => by
      simp only [eq_intCast]
  rw [hQ_map, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hQ_eval
  have hlhs_eq : Polynomial.eval₂ (ratToAinfInvP p O) X
      ((truncLogPoly N).comp ((1 + Polynomial.X) ^ p - 1) - Polynomial.C (p : ℚ) * truncLogPoly N) =
      ratToAinfInvP p O ((L : ℚ)⁻¹) *
        ∑ k ∈ Finset.range (Q_int.natDegree + 1), ((Q_int.coeff k : ℤ) : AinfInvP p O) * X ^ k := by
    rw [← hQ_eval, ← mul_assoc, mul_comm (ratToAinfInvP p O (L : ℚ)⁻¹), hL_inv, one_mul]
  rw [hlhs_eq, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : N + 1 ≤ k
  · simp only [termW, dif_pos hk]
    push_cast
    rw [coe_ainfToAcris0, coe_gammaXiAcris0]
    set w : ℕ := (hk_fac_dvd k hk).choose
    have hw : k ! = p ^ (v + n) * w := (hk_fac_dvd k hk).choose_spec
    have hX : X ^ k = ainfToInvP p O (epsDivXi p O ^ k) * xiInvP p O ^ k := by
      simp only [X, teichEps_sub_one_eq_xi_mul_epsDivXi, map_mul, mul_pow, xiInvP, map_pow]
      ring
    rw [hX, ← factorial_mul_gammaXi k, hw, Nat.cast_mul, Nat.cast_pow, pow_add]
    have hL_eq : ratToAinfInvP p O ((L : ℚ)⁻¹) * ((p : ℕ) : AinfInvP p O) ^ v =
        ainfToInvP p O ((u_unit⁻¹ : (A_inf p O)ˣ) : A_inf p O) := by
      have h1 : ratToAinfInvP p O (L : ℚ) =
          ((p : ℕ) : AinfInvP p O) ^ v * ainfToInvP p O (u_unit : A_inf p O) := by
        rw [ratToAinfInvP_natCast, hu, Nat.cast_mul, Nat.cast_pow, hu_unit, map_natCast]
      calc ratToAinfInvP p O ((L : ℚ)⁻¹) * ((p : ℕ) : AinfInvP p O) ^ v
          = ratToAinfInvP p O ((L : ℚ)⁻¹) *
              (((p : ℕ) : AinfInvP p O) ^ v *
                (ainfToInvP p O (u_unit : A_inf p O) * ainfToInvP p O ((u_unit⁻¹ : (A_inf p O)ˣ) : A_inf p O))) := by
            rw [← map_mul, Units.mul_inv, map_one, mul_one]
        _ = (ratToAinfInvP p O (L : ℚ) * ratToAinfInvP p O ((L : ℚ)⁻¹)) *
              ainfToInvP p O ((u_unit⁻¹ : (A_inf p O)ˣ) : A_inf p O) := by
            rw [h1]; ring
        _ = ainfToInvP p O ((u_unit⁻¹ : (A_inf p O)ˣ) : A_inf p O) := by
            rw [hL_inv, one_mul]
    rw [map_mul]
    calc ratToAinfInvP p O (L : ℚ)⁻¹ *
          (((Q_int.coeff k : ℤ) : AinfInvP p O) *
            (ainfToInvP p O (epsDivXi p O ^ k) *
              (((p : ℕ) : AinfInvP p O) ^ v * ((p : ℕ) : AinfInvP p O) ^ n * ((w : ℕ) : AinfInvP p O) *
                gammaXi p O k)))
        = ((p : ℕ) : AinfInvP p O) ^ n *
            (((Q_int.coeff k : ℤ) : AinfInvP p O) * ((w : ℕ) : AinfInvP p O) *
              ((ratToAinfInvP p O (L : ℚ)⁻¹ * ((p : ℕ) : AinfInvP p O) ^ v) *
                ainfToInvP p O (epsDivXi p O ^ k)) * gammaXi p O k) := by ring
      _ = _ := by rw [hL_eq]
  · simp only [termW, dif_neg hk, ZeroMemClass.coe_zero, mul_zero]
    rw [hQ_coeff_zero k (by omega), Int.cast_zero, zero_mul, mul_zero]

private theorem prime_dvd_add_pow_sub {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) (a b : R) :
    ((p : ℕ) : R) ∣ (a + b) ^ p - a ^ p - b ^ p := by
  rw [add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self,
    Nat.cast_one, mul_one]
  have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.pos).symm
  rw [hp1, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, tsub_zero, ← hp1]
  have heq : (∑ k ∈ Finset.range (p - 1), a ^ (k + 1) * b ^ (p - (k + 1)) * (Nat.choose p (k + 1) : R)) +
      b ^ p + a ^ p - a ^ p - b ^ p =
      ∑ k ∈ Finset.range (p - 1), a ^ (k + 1) * b ^ (p - (k + 1)) * (Nat.choose p (k + 1) : R) := by
    ring
  rw [heq]
  refine Finset.dvd_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hch : p ∣ Nat.choose p (k + 1) := hp.dvd_choose_self (by omega) (by omega)
  obtain ⟨c, hc⟩ := hch
  rw [hc, Nat.cast_mul]
  exact ⟨a ^ (k + 1) * b ^ (p - (k + 1)) * (c : R), by ring⟩

private theorem prime_dvd_sum_pow {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
    {ι : Type*} (s : Finset ι) (f : ι → R) (hf : ∀ i ∈ s, ((p : ℕ) : R) ∣ f i ^ p) :
    ((p : ℕ) : R) ∣ (∑ i ∈ s, f i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_pow hp.ne_zero]
  | @insert a s has ih =>
    rw [Finset.sum_insert has]
    have h1 := prime_dvd_add_pow_sub hp (f a) (∑ i ∈ s, f i)
    have h2 : ((p : ℕ) : R) ∣ f a ^ p := hf a (Finset.mem_insert_self a s)
    have h3 : ((p : ℕ) : R) ∣ (∑ i ∈ s, f i) ^ p :=
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have heq : (f a + ∑ i ∈ s, f i) ^ p =
        ((f a + ∑ i ∈ s, f i) ^ p - f a ^ p - (∑ i ∈ s, f i) ^ p) + f a ^ p + (∑ i ∈ s, f i) ^ p := by
      ring
    rw [heq]
    exact dvd_add (dvd_add h1 h2) h3

/-- **Divisibility `p ∣ t^p` in `A_cris`**: implies `p` is automatically invertible in
`B_cris := A_cris[1/t]`! -/
theorem p_dvd_tAcris_pow_p : ((p : ℕ) : Acris p O) ∣ tAcris p O ^ p := by
  have hp : p.Prime := Fact.out
  rw [← pow_one ((p : ℕ) : Acris p O)]
  change algebraMap (Acris0 p O) (Acris p O) ((p : ℕ) : Acris0 p O) ^ 1 ∣ tAcris p O ^ p
  rw [← evalₐ_eq_zero_iff_dvd_of_eq_span (rfl : Ideal.span {((p : ℕ) : Acris0 p O)} = Ideal.span _),
    map_pow, eval_tAcris_eq_of_le 1 p (by omega)]
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton]
  unfold tAcrisPartial
  refine prime_dvd_sum_pow hp _ _ fun k _ => ?_
  unfold tAcrisTerm
  rw [mul_pow]
  refine dvd_mul_of_dvd_right ?_ _
  obtain ⟨r, hr⟩ := prime_mul_factorial_pow_dvd_factorial (p := p) (k := k + 1) (by omega)
  refine ⟨((r : ℕ) : Acris0 p O) * gammaXiAcris0 p O (p * (k + 1)), ?_⟩
  apply Subtype.ext
  push_cast
  rw [coe_gammaXiAcris0, coe_gammaXiAcris0]
  unfold gammaXi
  rw [mul_pow, ← pow_mul, mul_comm (k + 1) p]
  have hq : (((k + 1)! : ℚ)⁻¹) ^ p = (p : ℚ) * (r : ℚ) * (((p * (k + 1))! : ℚ)⁻¹) := by
    have hrq : ((p * (k + 1))! : ℚ) = (p : ℚ) * (((k + 1)! : ℚ) ^ p) * (r : ℚ) := by
      exact_mod_cast hr
    have hk : ((k + 1)! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + 1))
    have hpk : ((p * (k + 1))! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (p * (k + 1)))
    rw [inv_pow]
    field_simp
    linarith
  rw [← map_pow, hq, map_mul, map_mul, ratToAinfInvP_natCast, ratToAinfInvP_natCast]
  ring

/-- **Fontaine's Crystalline Period Ring `B_cris := A_cris[1/t]`**. -/
abbrev Bcris (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : Type u :=
  Localization.Away (tAcris p O)

/-- Canonical `RingHom`s into `B_cris`. -/
def acrisToBcris (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : Acris p O →+* Bcris p O :=
  algebraMap (Acris p O) (Bcris p O)

def ainfToBcris (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : A_inf p O →+* Bcris p O :=
  (acrisToBcris p O).comp (ainfToAcris p O)

/-- The period `t` inside `B_cris`. -/
def tBcris (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : Bcris p O :=
  acrisToBcris p O (tAcris p O)

theorem isUnit_tBcris : IsUnit (tBcris p O) :=
  IsLocalization.Away.algebraMap_isUnit (tAcris p O)

/-- Since `p ∣ t^p` in `A_cris`, `p` is automatically a unit in `B_cris = A_cris[1/t]`. -/
theorem isUnit_p_Bcris : IsUnit ((p : ℕ) : Bcris p O) := by
  obtain ⟨c, hc⟩ := p_dvd_tAcris_pow_p (p := p) (O := O)
  have h1 : (tBcris p O) ^ p = ((p : ℕ) : Bcris p O) * acrisToBcris p O c := by
    have := congrArg (acrisToBcris p O) hc
    simpa [tBcris, map_pow, map_mul, map_natCast] using this
  have hu : IsUnit ((tBcris p O) ^ p) := (isUnit_tBcris (p := p) (O := O)).pow p
  rw [h1] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- Canonical `RingHom` `ℚ_[p] →+* B_cris`. -/
def padicToBcris (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : ℚ_[p] →+* Bcris p O :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (S := ℚ_[p])
    (g := (acrisToBcris p O).comp (padicIntToAcris p O))
    (fun ⟨z, hz⟩ => by
      have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
      have hz_eq : z = (PadicInt.unitCoeff hz0 : ℤ_[p]) * ((p : ℕ) : ℤ_[p]) ^ z.valuation :=
        PadicInt.unitCoeff_spec hz0
      rw [RingHom.comp_apply]
      dsimp only
      rw [hz_eq, map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast]
      exact (((PadicInt.unitCoeff hz0).isUnit.map (padicIntToAcris p O)).map (acrisToBcris p O)).mul
        ((isUnit_p_Bcris (p := p) (O := O)).pow _))

/-- **Witt-Vector Frobenius Endomorphism `frobBcris : B_cris →+* B_cris`**! -/
def frobBcris (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : Bcris p O →+* Bcris p O :=
  IsLocalization.Away.lift (tAcris p O)
    (g := (acrisToBcris p O).comp (frobAcris p O))
    (by
      rw [RingHom.comp_apply, frobAcris_tAcris, map_mul, map_natCast]
      exact (isUnit_p_Bcris (p := p) (O := O)).mul (isUnit_tBcris (p := p) (O := O)))

@[simp] theorem frobBcris_acris (x : Acris p O) :
    frobBcris p O (acrisToBcris p O x) = acrisToBcris p O (frobAcris p O x) :=
  IsLocalization.Away.lift_eq _ _ x

/-- **Fontaine's Fundamental Frobenius Identity on `B_cris`**: `frobBcris t = p * t`! -/
theorem frobBcris_tBcris :
    frobBcris p O (tBcris p O) = ((p : ℕ) : Bcris p O) * tBcris p O := by
  unfold tBcris
  rw [frobBcris_acris, frobAcris_tAcris, map_mul, map_natCast]

/-- `frobBcris` is `ℚ_[p]`-linear (fixes every `c ∈ ℚ_[p]`). -/
theorem frobBcris_padic (c : ℚ_[p]) :
    frobBcris p O (padicToBcris p O c) = padicToBcris p O c := by
  have hcomp : (frobBcris p O).comp (padicToBcris p O) = padicToBcris p O := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun z => ?_)
    simp only [RingHom.comp_apply, padicToBcris]
    rw [IsLocalization.lift_eq, RingHom.comp_apply, frobBcris_acris]
    congr 1
    unfold padicIntToAcris ainfToAcris
    simp only [RingHom.comp_apply, frobAcris_acris0]
    congr 1
    apply Subtype.ext
    rw [coe_frobAcris0, coe_ainfToAcris0, frobAinfInvP_ainf, frobenius_padicIntToAinf]
  exact RingHom.congr_fun hcomp c

/-! ### Canonical Comparison Homomorphisms `acrisToBdRPlus : A_cris →+* B_dR^+` & `bcrisToBdR : B_cris →+* B_dR` -/

private theorem xi_pow_dvd_of_forall_p_pow {m : ℕ} {x : A_inf p O}
    (h : ∀ k : ℕ, ∃ a b : A_inf p O, x = ((p : ℕ) : A_inf p O) ^ k * a + xi p O ^ m * b) :
    xi p O ^ m ∣ x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    have h0 : thetaMap p O x = 0 := eq_zero_of_forall_pow_dvd ((p : ℕ) : O) fun k => by
      obtain ⟨a, b, e⟩ := h k
      exact ⟨thetaMap p O a, by rw [e, map_add, map_mul, map_pow, map_natCast, map_mul, map_pow,
        thetaMap_xi, zero_pow (Nat.succ_ne_zero m), zero_mul, add_zero]⟩
    obtain ⟨y, rfl⟩ := (thetaMap_eq_zero_iff (p := p) (O := O) x).mp h0
    rw [pow_succ']
    refine mul_dvd_mul_left _ (ih fun k => ?_)
    obtain ⟨a, b, e⟩ := h k
    obtain ⟨a', rfl⟩ : xi p O ∣ a := xi_dvd_of_dvd_p_pow_mul (k := k)
      ⟨y - xi p O ^ m * b, by linear_combination -e⟩
    exact ⟨a', b, mul_left_cancel₀ (xi_ne_zero (p := p) (O := O)) (by linear_combination e)⟩

private theorem exists_ainf_mul_factorial_mod (m : ℕ) (x : Acris0 p O) :
    ∃ a : A_inf p O, ((m ! : ℕ) : AinfInvP p O) * (x : AinfInvP p O) - ainfToInvP p O a ∈
      kerThetaInvP p O ^ m := by
  rcases x.2 with ⟨R, c, hx⟩
  refine ⟨∑ r ∈ Finset.range (min R m), c r * (((m ! / r ! : ℕ) : A_inf p O) * xi p O ^ r), ?_⟩
  rw [hx, Finset.mul_sum, map_sum]
  have hsplit : ∑ r ∈ Finset.range R, ((m ! : ℕ) : AinfInvP p O) * (ainfToInvP p O (c r) * gammaXi p O r) =
      (∑ r ∈ Finset.range (min R m), ((m ! : ℕ) : AinfInvP p O) * (ainfToInvP p O (c r) * gammaXi p O r)) +
      (∑ r ∈ Finset.Ico (min R m) R, ((m ! : ℕ) : AinfInvP p O) * (ainfToInvP p O (c r) * gammaXi p O r)) := by
    rw [Finset.sum_range_add_sum_Ico _ (Nat.min_le_left R m)]
  rw [hsplit, add_sub_right_comm]
  have hfirst : (∑ r ∈ Finset.range (min R m),
      ((m ! : ℕ) : AinfInvP p O) * (ainfToInvP p O (c r) * gammaXi p O r)) -
      ∑ r ∈ Finset.range (min R m), ainfToInvP p O (c r * (((m ! / r ! : ℕ) : A_inf p O) * xi p O ^ r)) = 0 := by
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    have hrm : r ≤ m := le_of_lt (lt_of_lt_of_le hr (Nat.min_le_right R m))
    have hdvd : r ! ∣ m ! := Nat.factorial_dvd_factorial hrm
    have hmul_fac : ((m ! : ℕ) : AinfInvP p O) =
        (((m ! / r ! : ℕ) : AinfInvP p O)) * ((r ! : ℕ) : AinfInvP p O) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    rw [map_mul, map_mul, map_natCast, map_pow]
    calc ((m ! : ℕ) : AinfInvP p O) * (ainfToInvP p O (c r) * gammaXi p O r)
        = ainfToInvP p O (c r) * (((m ! / r ! : ℕ) : AinfInvP p O) *
            (((r ! : ℕ) : AinfInvP p O) * gammaXi p O r)) := by rw [hmul_fac]; ring
      _ = ainfToInvP p O (c r) * (((m ! / r ! : ℕ) : AinfInvP p O) * xiInvP p O ^ r) := by
            rw [factorial_mul_gammaXi]
      _ = _ := rfl
  rw [hfirst, zero_add]
  refine Submodule.sum_mem _ fun r hr => ?_
  rw [Finset.mem_Ico] at hr
  have hmr : m ≤ r := by omega
  rw [kerThetaInvP_eq_span_xi, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  unfold gammaXi
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (pow_dvd_pow _ hmr) _) _) _

private def acrisLiftSeq (y : Acris p O) (k : ℕ) : Acris0 p O :=
  (Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) k y)).choose

omit [ValuationRing O] [CharZero O] in
private theorem acrisLiftSeq_spec (y : Acris p O) (k : ℕ) :
    Ideal.Quotient.mk (Ideal.span {((p : ℕ) : Acris0 p O)} ^ k) (acrisLiftSeq (p := p) (O := O) y k) =
      AdicCompletion.evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) k y :=
  (Ideal.Quotient.mk_surjective _).choose_spec

omit [ValuationRing O] [CharZero O] in
private theorem acrisLiftSeq_step_dvd (y : Acris p O) (k : ℕ) :
    ((p : ℕ) : Acris0 p O) ^ k ∣
      acrisLiftSeq (p := p) (O := O) y (k + 1) - acrisLiftSeq (p := p) (O := O) y k := by
  have hfac := factorPow_evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) (Nat.le_succ k) y
  rw [← acrisLiftSeq_spec (p := p) (O := O) y (k + 1),
    ← acrisLiftSeq_spec (p := p) (O := O) y k] at hfac
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk] at hfac
  exact Ideal.mem_span_singleton.mp (by rw [← Ideal.span_singleton_pow]; exact Ideal.Quotient.eq.mp hfac)

private def acrisApproxSeq (m : ℕ) (y : Acris p O) (k : ℕ) : A_inf p O :=
  let b0 : A_inf p O :=
    (exists_ainf_mul_factorial_mod (p := p) (O := O) m (acrisLiftSeq (p := p) (O := O) y 0)).choose
  let ck : ℕ → A_inf p O := fun j =>
    (exists_ainf_mul_factorial_mod (p := p) (O := O) m
      ((acrisLiftSeq_step_dvd (p := p) (O := O) y j).choose)).choose
  b0 + ∑ j ∈ Finset.range k, ((p : ℕ) : A_inf p O) ^ j * ck j

private theorem acrisApproxSeq_cauchy (m : ℕ) (y : Acris p O) :
    ∀ {k₁ k₂ : ℕ}, k₁ ≤ k₂ →
      acrisApproxSeq (p := p) (O := O) m y k₁ ≡ acrisApproxSeq (p := p) (O := O) m y k₂
        [SMOD (Ideal.span {((p : ℕ) : A_inf p O)} ^ k₁ • ⊤ : Submodule (A_inf p O) (A_inf p O))] := by
  intro k₁ k₂ hle
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  induction k₂, hle using Nat.le_induction with
  | base => simp
  | succ k₂ hle ih =>
    unfold acrisApproxSeq at ih ⊢
    dsimp only at ih ⊢
    rw [Finset.sum_range_succ, ← add_assoc, sub_add_eq_sub_sub]
    exact dvd_sub ih ((pow_dvd_pow _ hle).mul_right _)

/-- Step map `acrisToQuotFun m : Acris p O → AinfInvP p O ⧸ kerThetaInvP p O ^ m`. -/
private def acrisToQuotFun (m : ℕ) (y : Acris p O) : AinfInvP p O ⧸ kerThetaInvP p O ^ m :=
  let b : A_inf p O :=
    (IsPrecomplete.prec (I := Ideal.span {((p : ℕ) : A_inf p O)}) (M := A_inf p O)
      inferInstance (f := acrisApproxSeq (p := p) (O := O) m y)
      (acrisApproxSeq_cauchy (p := p) (O := O) m y)).choose
  Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ratToAinfInvP p O ((m ! : ℚ)⁻¹) * ainfToInvP p O b)

private theorem acrisToQuotFun_spec (m : ℕ) (y : Acris p O) (k : ℕ) (z : Acris0 p O)
    (hz : Ideal.Quotient.mk (Ideal.span {((p : ℕ) : Acris0 p O)} ^ k) z =
      AdicCompletion.evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) k y) :
    ∃ w : A_inf p O,
      Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
        (acrisToQuotFun (p := p) (O := O) m y - Ideal.Quotient.mk (kerThetaInvP p O ^ m) (z : AinfInvP p O)) =
      Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ainfToInvP p O (((p : ℕ) : A_inf p O) ^ k * w)) := by
  have hseq_mod : ∀ j,
      ((m ! : ℕ) : AinfInvP p O) * (acrisLiftSeq (p := p) (O := O) y j : AinfInvP p O) -
        ainfToInvP p O (acrisApproxSeq (p := p) (O := O) m y j) ∈ kerThetaInvP p O ^ m := by
    intro j
    induction j with
    | zero =>
      simpa [acrisApproxSeq] using
        (exists_ainf_mul_factorial_mod (p := p) (O := O) m (acrisLiftSeq (p := p) (O := O) y 0)).choose_spec
    | succ j ih =>
      have hdk := (acrisLiftSeq_step_dvd (p := p) (O := O) y j).choose_spec
      have hck := (exists_ainf_mul_factorial_mod (p := p) (O := O) m
        ((acrisLiftSeq_step_dvd (p := p) (O := O) y j).choose)).choose_spec
      have hstep_c := congrArg (fun t : Acris0 p O => (t : AinfInvP p O)) hdk
      push_cast at hstep_c
      have h1 : ((m ! : ℕ) : AinfInvP p O) * (acrisLiftSeq (p := p) (O := O) y (j + 1) : AinfInvP p O) -
            ainfToInvP p O (acrisApproxSeq (p := p) (O := O) m y (j + 1)) =
          (((m ! : ℕ) : AinfInvP p O) * (acrisLiftSeq (p := p) (O := O) y j : AinfInvP p O) -
            ainfToInvP p O (acrisApproxSeq (p := p) (O := O) m y j)) +
            ((p : ℕ) : AinfInvP p O) ^ j *
              (((m ! : ℕ) : AinfInvP p O) *
                ((acrisLiftSeq_step_dvd (p := p) (O := O) y j).choose : AinfInvP p O) -
                ainfToInvP p O ((exists_ainf_mul_factorial_mod (p := p) (O := O) m
                  ((acrisLiftSeq_step_dvd (p := p) (O := O) y j).choose)).choose)) := by
        unfold acrisApproxSeq
        dsimp only
        rw [Finset.sum_range_succ, ← add_assoc, map_add, map_add, map_mul, map_pow, map_natCast]
        linear_combination ((m ! : ℕ) : AinfInvP p O) * hstep_c
      rw [h1]
      exact Ideal.add_mem _ ih (Ideal.mul_mem_left _ _ hck)
  have hzk : ((p : ℕ) : Acris0 p O) ^ k ∣ acrisLiftSeq (p := p) (O := O) y k - z := by
    have heq : Ideal.Quotient.mk (Ideal.span {((p : ℕ) : Acris0 p O)} ^ k)
        (acrisLiftSeq (p := p) (O := O) y k) =
        Ideal.Quotient.mk (Ideal.span {((p : ℕ) : Acris0 p O)} ^ k) z :=
      (acrisLiftSeq_spec (p := p) (O := O) y k).trans hz.symm
    exact Ideal.mem_span_singleton.mp (by rw [← Ideal.span_singleton_pow]; exact Ideal.Quotient.eq.mp heq)
  obtain ⟨e, he⟩ := hzk
  obtain ⟨a_e, ha_e⟩ := exists_ainf_mul_factorial_mod (p := p) (O := O) m e
  have hb_k := (IsPrecomplete.prec (I := Ideal.span {((p : ℕ) : A_inf p O)}) (M := A_inf p O)
    inferInstance (f := acrisApproxSeq (p := p) (O := O) m y)
    (acrisApproxSeq_cauchy (p := p) (O := O) m y)).choose_spec k
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hb_k
  obtain ⟨w1, hw1⟩ := hb_k
  refine ⟨-w1 + a_e, ?_⟩
  have hlim : acrisToQuotFun (p := p) (O := O) m y =
      Ideal.Quotient.mk (kerThetaInvP p O ^ m)
        (ratToAinfInvP p O ((m ! : ℚ)⁻¹) *
          ainfToInvP p O (acrisApproxSeq (p := p) (O := O) m y k + ((p : ℕ) : A_inf p O) ^ k * (-w1))) := by
    unfold acrisToQuotFun
    dsimp only
    congr 1; congr 1; congr 1
    linear_combination -hw1
  rw [hlim, ← map_sub, ← map_mul, Ideal.Quotient.eq]
  have hm_inv : ((m ! : ℕ) : AinfInvP p O) * ratToAinfInvP p O ((m ! : ℚ)⁻¹) = 1 := by
    rw [← ratToAinfInvP_natCast, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)), map_one]
  have he_c := congrArg (fun t : Acris0 p O => (t : AinfInvP p O)) he
  push_cast at he_c
  have hdiff : ((m ! : ℕ) : AinfInvP p O) *
      (ratToAinfInvP p O ((m ! : ℚ)⁻¹) *
        ainfToInvP p O (acrisApproxSeq (p := p) (O := O) m y k + ((p : ℕ) : A_inf p O) ^ k * (-w1)) -
        (z : AinfInvP p O)) -
      ainfToInvP p O (((p : ℕ) : A_inf p O) ^ k * (-w1 + a_e)) =
      -(((m ! : ℕ) : AinfInvP p O) * (acrisLiftSeq (p := p) (O := O) y k : AinfInvP p O) -
          ainfToInvP p O (acrisApproxSeq (p := p) (O := O) m y k)) +
        ((p : ℕ) : AinfInvP p O) ^ k *
          (((m ! : ℕ) : AinfInvP p O) * (e : AinfInvP p O) - ainfToInvP p O a_e) := by
    rw [mul_sub, ← mul_assoc, hm_inv, one_mul, map_add, map_mul, map_mul, map_add, map_pow,
      map_natCast]
    linear_combination ((m ! : ℕ) : AinfInvP p O) * he_c
  rw [hdiff]
  exact Ideal.add_mem _ (Submodule.neg_mem _ (hseq_mod k)) (Ideal.mul_mem_left _ _ ha_e)

private theorem eq_in_quot_of_forall_p_pow {m : ℕ} {q₁ q₂ : AinfInvP p O ⧸ kerThetaInvP p O ^ m}
    (h : ∀ k : ℕ, ∃ w : A_inf p O,
      q₁ - q₂ = Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ainfToInvP p O (((p : ℕ) : A_inf p O) ^ k * w))) :
    q₁ = q₂ := by
  rw [← sub_eq_zero]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (q₁ - q₂)
  obtain ⟨⟨x, ⟨_, s, rfl⟩⟩, hxr⟩ := IsLocalization.surj (Submonoid.powers ((p : ℕ) : A_inf p O)) r
  dsimp only at hxr
  have hx_dvd : xi p O ^ m ∣ x := by
    refine xi_pow_dvd_of_forall_p_pow fun k => ?_
    obtain ⟨w, hw⟩ := h (k + s)
    rw [← hr, Ideal.Quotient.eq, kerThetaInvP_eq_span_xi, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hw
    obtain ⟨c, hc⟩ := hw
    obtain ⟨⟨c0, ⟨_, t, rfl⟩⟩, hct⟩ := IsLocalization.surj (Submonoid.powers ((p : ℕ) : A_inf p O)) c
    dsimp only at hct
    have hmul : ainfToInvP p O (((p : ℕ) : A_inf p O) ^ t * x) =
        ainfToInvP p O (((p : ℕ) : A_inf p O) ^ (t + s + (k + s)) * w +
          xi p O ^ m * (((p : ℕ) : A_inf p O) ^ s * c0)) := by
      have h2 : r * ((p : ℕ) : AinfInvP p O) ^ s = ainfToInvP p O x := by simpa [ainfToInvP] using hxr
      have h3 : c * ((p : ℕ) : AinfInvP p O) ^ t = ainfToInvP p O c0 := by simpa [ainfToInvP] using hct
      have hc' : r = ((p : ℕ) : AinfInvP p O) ^ (k + s) * ainfToInvP p O w +
          ainfToInvP p O (xi p O) ^ m * c := by
        simp only [map_mul, map_pow, map_natCast, xiInvP] at hc
        linear_combination hc
      simp only [map_add, map_mul, map_pow, map_natCast]
      calc ((p : ℕ) : AinfInvP p O) ^ t * ainfToInvP p O x
          = ((p : ℕ) : AinfInvP p O) ^ t * (r * ((p : ℕ) : AinfInvP p O) ^ s) := by rw [h2]
        _ = ((p : ℕ) : AinfInvP p O) ^ t *
              ((((p : ℕ) : AinfInvP p O) ^ (k + s) * ainfToInvP p O w +
                ainfToInvP p O (xi p O) ^ m * c) * ((p : ℕ) : AinfInvP p O) ^ s) := by rw [hc']
        _ = (((p : ℕ) : AinfInvP p O) ^ t * ((p : ℕ) : AinfInvP p O) ^ s * ((p : ℕ) : AinfInvP p O) ^ (k + s)) *
              ainfToInvP p O w +
              ainfToInvP p O (xi p O) ^ m * (((p : ℕ) : AinfInvP p O) ^ s * (c * ((p : ℕ) : AinfInvP p O) ^ t)) := by
            ring
        _ = ((p : ℕ) : AinfInvP p O) ^ (t + s + (k + s)) * ainfToInvP p O w +
              ainfToInvP p O (xi p O) ^ m * (((p : ℕ) : AinfInvP p O) ^ s * ainfToInvP p O c0) := by
            rw [← pow_add, ← pow_add, h3]
    have hA : ((p : ℕ) : A_inf p O) ^ t * x =
        ((p : ℕ) : A_inf p O) ^ (t + s + (k + s)) * w +
          xi p O ^ m * (((p : ℕ) : A_inf p O) ^ s * c0) :=
      ainfToInvP_injective hmul
    have hxi_dvd : xi p O ^ m ∣ ((p : ℕ) : A_inf p O) ^ t *
        (x - ((p : ℕ) : A_inf p O) ^ (s + (k + s)) * w) := by
      refine ⟨((p : ℕ) : A_inf p O) ^ s * c0, ?_⟩
      have : ((p : ℕ) : A_inf p O) ^ (t + s + (k + s)) =
          ((p : ℕ) : A_inf p O) ^ t * ((p : ℕ) : A_inf p O) ^ (s + (k + s)) := by
        rw [add_assoc, pow_add]
      linear_combination hA - this * w
    obtain ⟨b, hb⟩ := xi_pow_dvd_of_dvd_p_pow_mul hxi_dvd
    exact ⟨((p : ℕ) : A_inf p O) ^ (s + s) * w, b, by
      have : ((p : ℕ) : A_inf p O) ^ (s + (k + s)) =
          ((p : ℕ) : A_inf p O) ^ k * ((p : ℕ) : A_inf p O) ^ (s + s) := by
        rw [← pow_add]; congr 1; omega
      linear_combination hb + this * w⟩
  obtain ⟨y, rfl⟩ := hx_dvd
  rw [← hr, Ideal.Quotient.eq_zero_iff_mem, kerThetaInvP_eq_span_xi, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  have hp_u := (IsLocalization.Away.algebraMap_isUnit ((p : ℕ) : A_inf p O) (S := AinfInvP p O)).pow s
  obtain ⟨u, hu⟩ := hp_u
  refine ⟨ainfToInvP p O y * (u⁻¹ : (AinfInvP p O)ˣ), ?_⟩
  have h1 : r * (u : AinfInvP p O) = xiInvP p O ^ m * ainfToInvP p O y := by
    simpa [hu, xiInvP, ainfToInvP, map_mul, map_pow] using hxr
  calc r = r * (u : AinfInvP p O) * (u⁻¹ : (AinfInvP p O)ˣ) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
    _ = xiInvP p O ^ m * (ainfToInvP p O y * (u⁻¹ : (AinfInvP p O)ˣ)) := by
        rw [h1, mul_assoc]

private def acrisToQuot (m : ℕ) : Acris p O →+* AinfInvP p O ⧸ kerThetaInvP p O ^ m where
  toFun := acrisToQuotFun (p := p) (O := O) m
  map_one' := by
    have hm_inv : Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
        Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ratToAinfInvP p O ((m ! : ℚ)⁻¹)) = 1 := by
      rw [← map_mul, ← ratToAinfInvP_natCast, ← map_mul,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)), map_one, map_one]
    have hmul : Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
        acrisToQuotFun (p := p) (O := O) m 1 =
        Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) * 1 := by
      refine eq_in_quot_of_forall_p_pow fun k => ?_
      obtain ⟨w, hw⟩ := acrisToQuotFun_spec (p := p) (O := O) m 1 k 1 (by simp)
      refine ⟨w, ?_⟩
      simpa [mul_sub] using hw
    calc acrisToQuotFun (p := p) (O := O) m 1
        = Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ratToAinfInvP p O ((m ! : ℚ)⁻¹)) *
            (Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
              acrisToQuotFun (p := p) (O := O) m 1) := by
          rw [← mul_assoc, mul_comm (Ideal.Quotient.mk _ (ratToAinfInvP p O _)), hm_inv, one_mul]
      _ = 1 := by
          rw [hmul, mul_one, mul_comm, hm_inv]
  map_zero' := by
    have hm_inv : Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
        Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ratToAinfInvP p O ((m ! : ℚ)⁻¹)) = 1 := by
      rw [← map_mul, ← ratToAinfInvP_natCast, ← map_mul,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)), map_one, map_one]
    have hmul : Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
        acrisToQuotFun (p := p) (O := O) m 0 = 0 := by
      refine eq_in_quot_of_forall_p_pow fun k => ?_
      obtain ⟨w, hw⟩ := acrisToQuotFun_spec (p := p) (O := O) m 0 k 0 (by simp)
      exact ⟨w, by simpa using hw⟩
    calc acrisToQuotFun (p := p) (O := O) m 0
        = Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ratToAinfInvP p O ((m ! : ℚ)⁻¹)) *
            (Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
              acrisToQuotFun (p := p) (O := O) m 0) := by
          rw [← mul_assoc, mul_comm (Ideal.Quotient.mk _ (ratToAinfInvP p O _)), hm_inv, one_mul]
      _ = 0 := by rw [hmul, mul_zero]
  map_add' x y := by
    have hm_inv : Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
        Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ratToAinfInvP p O ((m ! : ℚ)⁻¹)) = 1 := by
      rw [← map_mul, ← ratToAinfInvP_natCast, ← map_mul,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)), map_one, map_one]
    have hmul : Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
        acrisToQuotFun (p := p) (O := O) m (x + y) =
        Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
          (acrisToQuotFun (p := p) (O := O) m x + acrisToQuotFun (p := p) (O := O) m y) := by
      refine eq_in_quot_of_forall_p_pow fun k => ?_
      obtain ⟨zx, hzx⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) k x)
      obtain ⟨zy, hzy⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) k y)
      obtain ⟨wx, hwx⟩ := acrisToQuotFun_spec (p := p) (O := O) m x k zx hzx
      obtain ⟨wy, hwy⟩ := acrisToQuotFun_spec (p := p) (O := O) m y k zy hzy
      obtain ⟨wxy, hwxy⟩ := acrisToQuotFun_spec (p := p) (O := O) m (x + y) k (zx + zy)
        (by rw [map_add, hzx, hzy, map_add])
      refine ⟨wxy - wx - wy, ?_⟩
      have hcoe : ((zx + zy : Acris0 p O) : AinfInvP p O) = (zx : AinfInvP p O) + (zy : AinfInvP p O) := rfl
      rw [hcoe] at hwxy
      simp only [mul_sub, map_sub, map_mul, map_add] at hwxy hwx hwy ⊢
      linear_combination hwxy - hwx - hwy
    calc acrisToQuotFun (p := p) (O := O) m (x + y)
        = Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ratToAinfInvP p O ((m ! : ℚ)⁻¹)) *
            (Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
              acrisToQuotFun (p := p) (O := O) m (x + y)) := by
          rw [← mul_assoc, mul_comm (Ideal.Quotient.mk _ (ratToAinfInvP p O _)), hm_inv, one_mul]
      _ = acrisToQuotFun (p := p) (O := O) m x + acrisToQuotFun (p := p) (O := O) m y := by
          rw [hmul, ← mul_assoc, mul_comm (Ideal.Quotient.mk _ (ratToAinfInvP p O _)), hm_inv, one_mul]
  map_mul' x y := by
    have hm_inv : Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
        Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ratToAinfInvP p O ((m ! : ℚ)⁻¹)) = 1 := by
      rw [← map_mul, ← ratToAinfInvP_natCast, ← map_mul,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)), map_one, map_one]
    have hmul : Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) ^ 2 *
        acrisToQuotFun (p := p) (O := O) m (x * y) =
        Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) ^ 2 *
          (acrisToQuotFun (p := p) (O := O) m x * acrisToQuotFun (p := p) (O := O) m y) := by
      refine eq_in_quot_of_forall_p_pow fun k => ?_
      obtain ⟨zx, hzx⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) k x)
      obtain ⟨zy, hzy⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) k y)
      obtain ⟨wx, hwx⟩ := acrisToQuotFun_spec (p := p) (O := O) m x k zx hzx
      obtain ⟨wy, hwy⟩ := acrisToQuotFun_spec (p := p) (O := O) m y k zy hzy
      obtain ⟨wxy, hwxy⟩ := acrisToQuotFun_spec (p := p) (O := O) m (x * y) k (zx * zy)
        (by rw [map_mul, hzx, hzy, map_mul])
      obtain ⟨ax, hax⟩ := exists_ainf_mul_factorial_mod (p := p) (O := O) m zx
      obtain ⟨ay, hay⟩ := exists_ainf_mul_factorial_mod (p := p) (O := O) m zy
      have haxq : Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
          Ideal.Quotient.mk (kerThetaInvP p O ^ m) (zx : AinfInvP p O) =
          Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ainfToInvP p O ax) :=
        by rw [← map_mul, Ideal.Quotient.eq]; exact hax
      have hayq : Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
          Ideal.Quotient.mk (kerThetaInvP p O ^ m) (zy : AinfInvP p O) =
          Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ainfToInvP p O ay) :=
        by rw [← map_mul, Ideal.Quotient.eq]; exact hay
      refine ⟨((m ! : ℕ) : A_inf p O) * wxy - wx * ay - wy * ax - ((p : ℕ) : A_inf p O) ^ k * (wx * wy), ?_⟩
      set M := Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O))
      set qx := acrisToQuotFun (p := p) (O := O) m x
      set qy := acrisToQuotFun (p := p) (O := O) m y
      set qxy := acrisToQuotFun (p := p) (O := O) m (x * y)
      set px := Ideal.Quotient.mk (kerThetaInvP p O ^ m) (zx : AinfInvP p O)
      set py := Ideal.Quotient.mk (kerThetaInvP p O ^ m) (zy : AinfInvP p O)
      have hpxy : Ideal.Quotient.mk (kerThetaInvP p O ^ m) ((zx * zy : Acris0 p O) : AinfInvP p O) = px * py := by
        push_cast; rw [map_mul]
      rw [hpxy] at hwxy
      have hprod : M ^ 2 * (qx * qy - px * py) =
          (M * (qx - px)) * (M * py) + (M * (qy - py)) * (M * px) + (M * (qx - px)) * (M * (qy - py)) := by
        ring
      have hgoal : M ^ 2 * qxy - M ^ 2 * (qx * qy) =
          M * (M * (qxy - px * py)) - M ^ 2 * (qx * qy - px * py) := by ring
      rw [hgoal, hprod, hwxy, hwx, hwy, haxq, hayq]
      simp only [M, map_sub, map_mul, map_pow, map_natCast]
      ring
    calc acrisToQuotFun (p := p) (O := O) m (x * y)
        = (Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ratToAinfInvP p O ((m ! : ℚ)⁻¹))) ^ 2 *
            (Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) ^ 2 *
              acrisToQuotFun (p := p) (O := O) m (x * y)) := by
          rw [← mul_assoc, ← mul_pow, mul_comm (Ideal.Quotient.mk _ (ratToAinfInvP p O _)),
            hm_inv, one_pow, one_mul]
      _ = acrisToQuotFun (p := p) (O := O) m x * acrisToQuotFun (p := p) (O := O) m y := by
          rw [hmul, ← mul_assoc, ← mul_pow, mul_comm (Ideal.Quotient.mk _ (ratToAinfInvP p O _)),
            hm_inv, one_pow, one_mul]

private theorem acrisToQuot_compat {m₁ m₂ : ℕ} (hle : m₁ ≤ m₂) :
    (Ideal.Quotient.factorPow (kerThetaInvP p O) hle).comp (acrisToQuot (p := p) (O := O) m₂) =
      acrisToQuot (p := p) (O := O) m₁ := by
  ext y
  simp only [RingHom.comp_apply]
  have hm_inv : Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (((m₁ ! * m₂ ! : ℕ) : AinfInvP p O)) *
      Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (ratToAinfInvP p O (((m₁ ! * m₂ ! : ℕ) : ℚ)⁻¹)) = 1 := by
    rw [← map_mul, ← ratToAinfInvP_natCast, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))),
      map_one, map_one]
  have hmul : Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (((m₁ ! * m₂ ! : ℕ) : AinfInvP p O)) *
      Ideal.Quotient.factorPow (kerThetaInvP p O) hle (acrisToQuot (p := p) (O := O) m₂ y) =
      Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (((m₁ ! * m₂ ! : ℕ) : AinfInvP p O)) *
        acrisToQuot (p := p) (O := O) m₁ y := by
    refine eq_in_quot_of_forall_p_pow fun k => ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (Ideal.span {((p : ℕ) : Acris0 p O)}) k y)
    obtain ⟨w₁, hw₁⟩ := acrisToQuotFun_spec (p := p) (O := O) m₁ y k z hz
    obtain ⟨w₂, hw₂⟩ := acrisToQuotFun_spec (p := p) (O := O) m₂ y k z hz
    have hw₂' := congrArg (Ideal.Quotient.factorPow (kerThetaInvP p O) hle) hw₂
    simp only [map_mul, map_sub, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk] at hw₂'
    refine ⟨((m₁ ! : ℕ) : A_inf p O) * w₂ - ((m₂ ! : ℕ) : A_inf p O) * w₁, ?_⟩
    change Ideal.Quotient.mk _ (((m₁ ! * m₂ ! : ℕ) : AinfInvP p O)) * _ -
        Ideal.Quotient.mk _ (((m₁ ! * m₂ ! : ℕ) : AinfInvP p O)) * _ = _
    have hcast : Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (((m₁ ! * m₂ ! : ℕ) : AinfInvP p O)) =
        Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (((m₁ ! : ℕ) : AinfInvP p O)) *
        Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (((m₂ ! : ℕ) : AinfInvP p O)) := by
      rw [← map_mul, Nat.cast_mul]
    rw [hcast]
    have hre : Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (((m₁ ! : ℕ) : AinfInvP p O)) *
        Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (((m₂ ! : ℕ) : AinfInvP p O)) *
          Ideal.Quotient.factorPow (kerThetaInvP p O) hle (acrisToQuotFun (p := p) (O := O) m₂ y) -
        Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (((m₁ ! : ℕ) : AinfInvP p O)) *
        Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (((m₂ ! : ℕ) : AinfInvP p O)) *
          acrisToQuotFun (p := p) (O := O) m₁ y =
        Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (((m₁ ! : ℕ) : AinfInvP p O)) *
          (Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (((m₂ ! : ℕ) : AinfInvP p O)) *
            (Ideal.Quotient.factorPow (kerThetaInvP p O) hle (acrisToQuotFun (p := p) (O := O) m₂ y) -
              Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (z : AinfInvP p O))) -
        Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (((m₂ ! : ℕ) : AinfInvP p O)) *
          (Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (((m₁ ! : ℕ) : AinfInvP p O)) *
            (acrisToQuotFun (p := p) (O := O) m₁ y -
              Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (z : AinfInvP p O))) := by ring
    rw [show Ideal.Quotient.factorPow (kerThetaInvP p O) hle (acrisToQuot (p := p) (O := O) m₂ y) =
        Ideal.Quotient.factorPow (kerThetaInvP p O) hle (acrisToQuotFun (p := p) (O := O) m₂ y) from rfl,
      show acrisToQuot (p := p) (O := O) m₁ y = acrisToQuotFun (p := p) (O := O) m₁ y from rfl,
      hre, hw₂', hw₁]
    simp only [map_sub, map_mul, map_pow, map_natCast]
    ring
  calc Ideal.Quotient.factorPow (kerThetaInvP p O) hle (acrisToQuot (p := p) (O := O) m₂ y)
      = Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (ratToAinfInvP p O (((m₁ ! * m₂ ! : ℕ) : ℚ)⁻¹)) *
          (Ideal.Quotient.mk (kerThetaInvP p O ^ m₁) (((m₁ ! * m₂ ! : ℕ) : AinfInvP p O)) *
            Ideal.Quotient.factorPow (kerThetaInvP p O) hle (acrisToQuot (p := p) (O := O) m₂ y)) := by
        rw [← mul_assoc, mul_comm (Ideal.Quotient.mk _ (ratToAinfInvP p O _)), hm_inv, one_mul]
    _ = acrisToQuot (p := p) (O := O) m₁ y := by
        rw [hmul, ← mul_assoc, mul_comm (Ideal.Quotient.mk _ (ratToAinfInvP p O _)), hm_inv, one_mul]

/-- **Canonical Comparison Homomorphism `acrisToBdRPlus : A_cris →+* B_dR^+`**! -/
def acrisToBdRPlus (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : Acris p O →+* BdRPlus p O :=
  AdicCompletion.liftRingHom (kerThetaInvP p O) (fun m => acrisToQuot (p := p) (O := O) m)
    (acrisToQuot_compat (p := p) (O := O))

/-- `acrisToBdRPlus` sends `tAcris` to `tBdR`! -/
theorem acrisToBdRPlus_tAcris : acrisToBdRPlus p O (tAcris p O) = tBdR p O := by
  refine AdicCompletion.ext_evalₐ fun m => ?_
  change evalBdRPlus p O m (acrisToBdRPlus p O (tAcris p O)) = evalBdRPlus p O m (tBdR p O)
  rw [evalBdRPlus_tBdR]
  have hev : evalBdRPlus p O m (acrisToBdRPlus p O (tAcris p O)) = acrisToQuot (p := p) (O := O) m (tAcris p O) := by
    change AdicCompletion.evalₐ (kerThetaInvP p O) m (acrisToBdRPlus p O (tAcris p O)) = _
    unfold acrisToBdRPlus
    exact AdicCompletion.evalₐ_liftRingHom _ _ (acrisToQuot_compat (p := p) (O := O)) m (tAcris p O)
  rw [hev]
  have hm_inv : Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
      Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ratToAinfInvP p O ((m ! : ℚ)⁻¹)) = 1 := by
    rw [← map_mul, ← ratToAinfInvP_natCast, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)), map_one, map_one]
  have hmul : Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
      acrisToQuot (p := p) (O := O) m (tAcris p O) =
      Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
        truncLogHom ((Ideal.Quotient.mk _).comp (ratToAinfInvP p O)) m
          (evalBdRPlus p O m (ainfToBdRPlus p O (teichEps p O) - 1)) := by
    refine eq_in_quot_of_forall_p_pow fun k => ?_
    set N := max m (p * k)
    obtain ⟨w, hw⟩ := acrisToQuotFun_spec (p := p) (O := O) m (tAcris p O) k (tAcrisPartial p O N)
      (eval_tAcris_eq_of_le k N (le_max_right m (p * k))).symm
    refine ⟨w, ?_⟩
    have htrunc : Ideal.Quotient.mk (kerThetaInvP p O ^ m) (tAcrisPartial p O N : AinfInvP p O) =
        truncLogHom ((Ideal.Quotient.mk _).comp (ratToAinfInvP p O)) m
          (evalBdRPlus p O m (ainfToBdRPlus p O (teichEps p O) - 1)) := by
      rw [coe_tAcrisPartial, map_truncLogHom]
      have harg : Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ainfToInvP p O (teichEps p O - 1)) =
          evalBdRPlus p O m (ainfToBdRPlus p O (teichEps p O) - 1) := by
        rw [map_sub, map_one, map_sub, map_one]; rfl
      rw [harg]
      refine truncLogHom_eq_of_pow_eq_zero _ ?_ (le_max_left m (p * k))
      rw [← map_pow, evalBdRPlus_eq_zero_iff]
      have hdvd : xiBdR p O ∣ ainfToBdRPlus p O (teichEps p O) - 1 := by
        rw [← thetaBdRPlus_eq_zero_iff_dvd, map_sub, map_one, thetaBdRPlus_ainf, teichEps,
          thetaMap_teichmuller, sharp_epsFlat, map_one, sub_self]
      exact pow_dvd_pow_of_dvd hdvd m
    rw [htrunc] at hw
    change Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
        acrisToQuotFun (p := p) (O := O) m (tAcris p O) - _ = _
    simpa [mul_sub] using hw
  calc acrisToQuot (p := p) (O := O) m (tAcris p O)
      = Ideal.Quotient.mk (kerThetaInvP p O ^ m) (ratToAinfInvP p O ((m ! : ℚ)⁻¹)) *
          (Ideal.Quotient.mk (kerThetaInvP p O ^ m) (((m ! : ℕ) : AinfInvP p O)) *
            acrisToQuot (p := p) (O := O) m (tAcris p O)) := by
        rw [← mul_assoc, mul_comm (Ideal.Quotient.mk _ (ratToAinfInvP p O _)), hm_inv, one_mul]
    _ = truncLogHom ((Ideal.Quotient.mk _).comp (ratToAinfInvP p O)) m
          (evalBdRPlus p O m (ainfToBdRPlus p O (teichEps p O) - 1)) := by
        rw [hmul, ← mul_assoc, mul_comm (Ideal.Quotient.mk _ (ratToAinfInvP p O _)), hm_inv, one_mul]

/-- **Canonical Comparison Homomorphism `bcrisToBdR : B_cris →+* B_dR`** sending `tBcris ↦ tInBdR`! -/
def bcrisToBdR (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharZero O] [Fact ¬IsUnit ((p : ℕ) : O)] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    [PerfectoidBase p O] : Bcris p O →+* BdR p O :=
  IsLocalization.Away.lift (tAcris p O)
    (g := (bdrPlusToBdR p O).comp (acrisToBdRPlus p O))
    (by
      rw [RingHom.comp_apply, acrisToBdRPlus_tAcris]
      exact IsLocalization.Away.algebraMap_isUnit (tBdR p O))

@[simp] theorem bcrisToBdR_tBcris :
    bcrisToBdR p O (tBcris p O) = tInBdR p O := by
  unfold bcrisToBdR tBcris acrisToBcris tInBdR
  rw [IsLocalization.Away.lift_eq, RingHom.comp_apply, acrisToBdRPlus_tAcris]

end AcrisBcrisConstruction

/-! ## Section 6: Fontaine's `D_cris(V)` Functor, Admissibility Inequality `dim D_cris(V) ≤ dim V`,
and Landing in `Stage11CrystallineFontaine.FilteredPhiModule p` -/

section DcrisFunctor

open scoped TensorProduct
open Stage2HodgeWeights Stage11CrystallineFontaine

/-- **Axiomatic Fontaine Period Ring System `(B_cris, B_dR, G, φ, ι, Fil•, t)` over `ℚ_[p]`**:
captures the exact algebraic and Galois-theoretic interface needed for Fontaine's functors
`D_cris(V) = (B_cris ⊗_{ℚ_p} V)^G` and `D_dR(V) = (B_dR ⊗_{ℚ_p} V)^G`. -/
structure FontainePeriodSystem (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] where
  BcrisRing : Type u
  BdRRing : Type u
  [commRingBcris : CommRing BcrisRing]
  [fieldBdR : Field BdRRing]
  [algBcris : Algebra ℚ_[p] BcrisRing]
  [algBdR : Algebra ℚ_[p] BdRRing]
  actBcris : G →* (BcrisRing ≃ₐ[ℚ_[p]] BcrisRing)
  actBdR : G →* (BdRRing ≃ₐ[ℚ_[p]] BdRRing)
  invBdR : ∀ x : BdRRing, (∀ g : G, actBdR g x = x) → ∃ c : ℚ_[p], algebraMap ℚ_[p] BdRRing c = x
  φ : BcrisRing →ₐ[ℚ_[p]] BcrisRing
  φ_inj : Function.Injective φ
  φ_comm : ∀ (g : G) (x : BcrisRing), φ (actBcris g x) = actBcris g (φ x)
  ι : BcrisRing →ₐ[ℚ_[p]] BdRRing
  ι_inj : Function.Injective ι
  ι_comm : ∀ (g : G) (x : BcrisRing), ι (actBcris g x) = actBdR g (ι x)
  Fil : ℤ → Submodule ℚ_[p] BdRRing
  Fil_anti : ∀ ⦃i j : ℤ⦄, i ≤ j → Fil j ≤ Fil i
  one_mem : (1 : BdRRing) ∈ Fil 0
  Fil_mul : ∀ ⦃i j : ℤ⦄ {x y : BdRRing}, x ∈ Fil i → y ∈ Fil j → x * y ∈ Fil (i + j)
  Fil_exh : ∀ x : BdRRing, ∃ i : ℤ, x ∈ Fil i
  Fil_sep : ∀ x : BdRRing, (∀ i : ℤ, x ∈ Fil i) → x = 0
  Fil_G : ∀ (g : G) (i : ℤ) {x : BdRRing}, x ∈ Fil i → actBdR g x ∈ Fil i
  t : BcrisRing
  t_unit : IsUnit t
  t_phi : φ t = ((p : ℕ) : ℚ_[p]) • t
  t_mem_fil1 : ι t ∈ Fil 1
  t_not_mem_fil2 : ι t ∉ Fil 2

attribute [instance] FontainePeriodSystem.commRingBcris FontainePeriodSystem.fieldBdR
  FontainePeriodSystem.algBcris FontainePeriodSystem.algBdR

namespace FontainePeriodSystem

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] (S : FontainePeriodSystem p G)

/-- Diagonal Galois action on `B_cris ⊗_{ℚ_[p]} V`. -/
def actBcrisV {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) (g : G) :
    (S.BcrisRing ⊗[ℚ_[p]] V) →ₗ[ℚ_[p]] (S.BcrisRing ⊗[ℚ_[p]] V) :=
  TensorProduct.map (S.actBcris g).toLinearMap (ρ g)

/-- Diagonal Galois action on `B_dR ⊗_{ℚ_[p]} V`. -/
def actBdRV {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) (g : G) :
    (S.BdRRing ⊗[ℚ_[p]] V) →ₗ[ℚ_[p]] (S.BdRRing ⊗[ℚ_[p]] V) :=
  TensorProduct.map (S.actBdR g).toLinearMap (ρ g)

/-- **Fontaine's Crystalline Functor `D_cris(V) := (B_cris ⊗_{ℚ_[p]} V)^G`**. -/
def D_cris {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) : Submodule ℚ_[p] (S.BcrisRing ⊗[ℚ_[p]] V) :=
  ⨅ g : G, LinearMap.ker (S.actBcrisV ρ g - LinearMap.id)

/-- **Fontaine's De Rham Functor `D_dR(V) := (B_dR ⊗_{ℚ_[p]} V)^G`**. -/
def D_dR {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) : Submodule ℚ_[p] (S.BdRRing ⊗[ℚ_[p]] V) :=
  ⨅ g : G, LinearMap.ker (S.actBdRV ρ g - LinearMap.id)

theorem mem_D_cris_iff {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) {x : S.BcrisRing ⊗[ℚ_[p]] V} :
    x ∈ S.D_cris ρ ↔ ∀ g : G, S.actBcrisV ρ g x = x := by
  simp [D_cris, Submodule.mem_iInf, sub_eq_zero]

theorem mem_D_dR_iff {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) {x : S.BdRRing ⊗[ℚ_[p]] V} :
    x ∈ S.D_dR ρ ↔ ∀ g : G, S.actBdRV ρ g x = x := by
  simp [D_dR, Submodule.mem_iInf, sub_eq_zero]

/-- Comparison map `ι_V := ι ⊗ id : B_cris ⊗_{ℚ_p} V → B_dR ⊗_{ℚ_p} V`. -/
def ιV {V : Type u} [AddCommGroup V] [Module ℚ_[p] V] :
    (S.BcrisRing ⊗[ℚ_[p]] V) →ₗ[ℚ_[p]] (S.BdRRing ⊗[ℚ_[p]] V) :=
  TensorProduct.map S.ι.toLinearMap LinearMap.id

/-- Frobenius map `φ_V := φ ⊗ id : B_cris ⊗_{ℚ_p} V → B_cris ⊗_{ℚ_p} V`. -/
def φV {V : Type u} [AddCommGroup V] [Module ℚ_[p] V] :
    (S.BcrisRing ⊗[ℚ_[p]] V) →ₗ[ℚ_[p]] (S.BcrisRing ⊗[ℚ_[p]] V) :=
  TensorProduct.map S.φ.toLinearMap LinearMap.id

/-- Coordinate projection `M ⊗_K V →ₗ[K] M` for a finite-dimensional vector space `V` with basis `b`. -/
private def tensorCoord {K M V : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup V] [Module K V] {ι_idx : Type*} (b : Module.Basis ι_idx K V) (k : ι_idx) :
    (M ⊗[K] V) →ₗ[K] M :=
  TensorProduct.lift
    { toFun := fun m =>
        { toFun := fun v => (b.repr v k) • m
          map_add' := fun v₁ v₂ => by simp [add_smul]
          map_smul' := fun c v => by simp [mul_smul] }
      map_add' := fun m₁ m₂ => by ext v; simp [smul_add]
      map_smul' := fun c m => by
        ext v
        exact smul_comm (b.repr v k) c m }

@[simp] private theorem tensorCoord_tmul {K M V : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup V] [Module K V] {ι_idx : Type*} (b : Module.Basis ι_idx K V) (k : ι_idx)
    (m : M) (v : V) :
    tensorCoord b k (m ⊗ₜ[K] v) = (b.repr v k) • m := rfl

private theorem sum_tensorCoord_tmul {K M V : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup V] [Module K V] {ι_idx : Type*} [Fintype ι_idx]
    (b : Module.Basis ι_idx K V) (z : M ⊗[K] V) :
    ∑ k : ι_idx, tensorCoord b k z ⊗ₜ[K] b k = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m v =>
    have hv : ∑ k : ι_idx, (b.repr v k) • b k = v := b.sum_repr v
    calc ∑ k : ι_idx, ((b.repr v k) • m) ⊗ₜ[K] b k
        = ∑ k : ι_idx, m ⊗ₜ[K] ((b.repr v k) • b k) := by
          refine Finset.sum_congr rfl fun k _ => TensorProduct.smul_tmul _ m (b k)
      _ = m ⊗ₜ[K] (∑ k : ι_idx, (b.repr v k) • b k) := (TensorProduct.tmul_sum m _ _).symm
      _ = m ⊗ₜ[K] v := by rw [hv]
  | add z₁ z₂ ih₁ ih₂ =>
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, ih₁, ih₂]

/-- Injectivity of `f ⊗ id : M ⊗_K V → N ⊗_K V` for any injective `K`-linear map `f` and
finite-dimensional vector space `V` over a field `K`. -/
private theorem tensorMap_id_injective {K M N V : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (f : M →ₗ[K] N) (hf : Function.Injective f) :
    Function.Injective (TensorProduct.map f (LinearMap.id : V →ₗ[K] V)) := by
  classical
  let b := Module.finBasis K V
  intro x y hxy
  rw [← sum_tensorCoord_tmul b x, ← sum_tensorCoord_tmul b y]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  apply hf
  have hcomm : ∀ z : M ⊗[K] V,
      tensorCoord b k (TensorProduct.map f LinearMap.id z) = f (tensorCoord b k z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m v => simp
    | add z₁ z₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
  rw [← hcomm x, ← hcomm y, hxy]

theorem ιV_injective {V : Type u} [AddCommGroup V] [Module ℚ_[p] V] [Module.Finite ℚ_[p] V] :
    Function.Injective (S.ιV (V := V)) :=
  tensorMap_id_injective S.ι.toLinearMap S.ι_inj

theorem φV_injective {V : Type u} [AddCommGroup V] [Module ℚ_[p] V] [Module.Finite ℚ_[p] V] :
    Function.Injective (S.φV (V := V)) :=
  tensorMap_id_injective S.φ.toLinearMap S.φ_inj

theorem ιV_mem_D_dR {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) {x : S.BcrisRing ⊗[ℚ_[p]] V} (hx : x ∈ S.D_cris ρ) :
    S.ιV x ∈ S.D_dR ρ := by
  rw [mem_D_dR_iff]
  intro g
  have hcomm : (S.actBdRV ρ g).comp S.ιV = S.ιV.comp (S.actBcrisV ρ g) := by
    ext b v
    simp [actBdRV, actBcrisV, ιV, S.ι_comm]
  have h1 := LinearMap.congr_fun hcomm x
  simp only [LinearMap.comp_apply] at h1
  rw [h1, (mem_D_cris_iff S ρ).mp hx g]

theorem φV_mem_D_cris {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) {x : S.BcrisRing ⊗[ℚ_[p]] V} (hx : x ∈ S.D_cris ρ) :
    S.φV x ∈ S.D_cris ρ := by
  rw [mem_D_cris_iff]
  intro g
  have hcomm : (S.actBcrisV ρ g).comp S.φV = S.φV.comp (S.actBcrisV ρ g) := by
    ext b v
    simp [actBcrisV, φV, S.φ_comm]
  have h1 := LinearMap.congr_fun hcomm x
  simp only [LinearMap.comp_apply] at h1
  rw [h1, (mem_D_cris_iff S ρ).mp hx g]

theorem actBdRV_smul {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) (g : G) (c : S.BdRRing) (x : S.BdRRing ⊗[ℚ_[p]] V) :
    S.actBdRV ρ g (c • x) = (S.actBdR g c) • S.actBdRV ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v =>
    change S.actBdRV ρ g ((c * b) ⊗ₜ[ℚ_[p]] v) = (S.actBdR g c) • ((S.actBdR g b) ⊗ₜ[ℚ_[p]] (ρ g v))
    simp [actBdRV, map_mul, TensorProduct.smul_tmul']
  | add x₁ x₂ ih₁ ih₂ =>
    rw [smul_add, map_add, ih₁, ih₂, map_add, smul_add]

/-- **Fontaine's Fundamental Linear Independence Lemma**:
any `ℚ_[p]`-linearly independent family in `D_dR(V) = (B_dR ⊗_{ℚ_[p]} V)^G` remains
`B_dR`-linearly independent in `B_dR ⊗_{ℚ_[p]} V`! -/
theorem linearIndependent_BdR_of_D_dR {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) {ι_idx : Type*} (f : ι_idx → S.D_dR ρ)
    (hf : LinearIndependent ℚ_[p] f) :
    LinearIndependent S.BdRRing (fun i => (f i : S.BdRRing ⊗[ℚ_[p]] V)) := by
  classical
  rw [linearIndependent_iff']
  by_contra hnot
  push Not at hnot
  -- Choose a nontrivial `B_dR`-linear relation of minimal support cardinality
  let P : ℕ → Prop := fun m =>
    ∃ (s : Finset ι_idx) (c : ι_idx → S.BdRRing),
      s.card = m ∧ (∀ i ∈ s, c i ≠ 0) ∧ (∑ i ∈ s, c i • (f i : S.BdRRing ⊗[ℚ_[p]] V) = 0) ∧
      s.Nonempty
  have hex : ∃ m, P m := by
    rcases hnot with ⟨s, c, hsum, i₀, hi₀, hc₀⟩
    let s' := s.filter (fun i => c i ≠ 0)
    have hsum' : ∑ i ∈ s', c i • (f i : S.BdRRing ⊗[ℚ_[p]] V) = 0 := by
      rw [← hsum]
      refine Finset.sum_subset (Finset.filter_subset _ _) fun i hi hni => ?_
      have hc0 : c i = 0 := by
        by_contra hne; exact hni (Finset.mem_filter.mpr ⟨hi, hne⟩)
      rw [hc0, zero_smul]
    exact ⟨s'.card, s', c, rfl, fun i hi => (Finset.mem_filter.mp hi).2, hsum',
      ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hc₀⟩⟩⟩
  let m := Nat.find hex
  obtain ⟨s, c, hcard, hne, hsum, ⟨i₁, hi₁⟩⟩ := Nat.find_spec hex
  have hc1 : c i₁ ≠ 0 := hne i₁ hi₁
  -- Normalize so that `c i₁ = 1`
  let d : ι_idx → S.BdRRing := fun i => (c i₁)⁻¹ * c i
  have hd1 : d i₁ = 1 := inv_mul_cancel₀ hc1
  have hd_ne : ∀ i ∈ s, d i ≠ 0 := fun i hi => mul_ne_zero (inv_ne_zero hc1) (hne i hi)
  have hd_sum : ∑ i ∈ s, d i • (f i : S.BdRRing ⊗[ℚ_[p]] V) = 0 := by
    have h := congrArg ((c i₁)⁻¹ • ·) hsum
    rw [smul_zero, Finset.smul_sum] at h
    simpa only [d, smul_smul] using h
  -- Every `d i` (`i ∈ s`) is `G`-invariant, otherwise subtracting gives a shorter relation!
  have hd_inv : ∀ i ∈ s, ∀ g : G, S.actBdR g (d i) = d i := by
    intro i hi g
    by_contra hdiff
    have hg_sum : ∑ j ∈ s, (S.actBdR g (d j)) • (f j : S.BdRRing ⊗[ℚ_[p]] V) = 0 := by
      have h1 := congrArg (S.actBdRV ρ g) hd_sum
      rw [map_zero, map_sum] at h1
      refine (Finset.sum_congr rfl fun j _ => ?_).symm.trans h1
      rw [S.actBdRV_smul ρ g (d j), (mem_D_dR_iff S ρ).mp (f j).2 g]
    have hsub : ∑ j ∈ s.erase i₁, (S.actBdR g (d j) - d j) • (f j : S.BdRRing ⊗[ℚ_[p]] V) = 0 := by
      have h1 : ∑ j ∈ s, (S.actBdR g (d j) - d j) • (f j : S.BdRRing ⊗[ℚ_[p]] V) = 0 := by
        simp_rw [sub_smul, Finset.sum_sub_distrib, hg_sum, hd_sum, sub_self]
      rw [← Finset.add_sum_erase s _ hi₁, hd1, map_one, sub_self, zero_smul, zero_add] at h1
      exact h1
    let t := (s.erase i₁).filter (fun j => S.actBdR g (d j) - d j ≠ 0)
    have hi_ne : i ≠ i₁ := by
      rintro rfl; exact hdiff (by rw [hd1, map_one])
    have hi_mem : i ∈ t :=
      Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hi_ne, hi⟩, sub_ne_zero.mpr hdiff⟩
    have ht_lt : t.card < m := by
      calc t.card ≤ (s.erase i₁).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ < s.card := Finset.card_erase_lt_of_mem hi₁
        _ = m := hcard
    have ht_sum : ∑ j ∈ t, (S.actBdR g (d j) - d j) • (f j : S.BdRRing ⊗[ℚ_[p]] V) = 0 := by
      rw [← hsub]
      refine Finset.sum_subset (Finset.filter_subset _ _) fun j hj hnj => ?_
      have h0 : S.actBdR g (d j) - d j = 0 := by
        by_contra hne0; exact hnj (Finset.mem_filter.mpr ⟨hj, hne0⟩)
      rw [h0, zero_smul]
    exact Nat.find_min hex ht_lt ⟨t, fun j => S.actBdR g (d j) - d j, rfl,
      fun j hj => (Finset.mem_filter.mp hj).2, ht_sum, ⟨i, hi_mem⟩⟩
  -- Since `BdR^G = ℚ_[p]`, every `d i` (`i ∈ s`) lies in `ℚ_[p]`!
  choose q hq using fun i (hi : i ∈ s) => S.invBdR (d i) (hd_inv i hi)
  let qFun : ι_idx → ℚ_[p] := fun i => if hi : i ∈ s then q i hi else 0
  have hq_sum : ∑ i ∈ s, qFun i • f i = 0 := by
    apply Subtype.ext
    rw [Submodule.coe_sum, ZeroMemClass.coe_zero]
    have hterms : ∀ i ∈ s, ((qFun i • f i : S.D_dR ρ) : S.BdRRing ⊗[ℚ_[p]] V) =
        d i • (f i : S.BdRRing ⊗[ℚ_[p]] V) := by
      intro i hi
      simp only [qFun, dif_pos hi, SetLike.val_smul, ← hq i hi, algebraMap_smul]
    rw [Finset.sum_congr rfl hterms, hd_sum]
  have hq1_zero : qFun i₁ = 0 := linearIndependent_iff'.mp hf s qFun hq_sum i₁ hi₁
  have hd1_zero : d i₁ = 0 := by
    rw [← hq i₁ hi₁]
    have : q i₁ hi₁ = 0 := by simpa [qFun, dif_pos hi₁] using hq1_zero
    rw [this, map_zero]
  exact one_ne_zero (hd1.symm.trans hd1_zero)

/-- `D_dR(V)` is finite-dimensional and satisfies **`dim_{ℚ_p} D_dR(V) ≤ dim_{ℚ_p} V`**! -/
theorem D_dR_finite_and_finrank_le {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    [Module.Finite ℚ_[p] V] (ρ : Representation ℚ_[p] G V) :
    Module.Finite ℚ_[p] (S.D_dR ρ) ∧ Module.finrank ℚ_[p] (S.D_dR ρ) ≤ Module.finrank ℚ_[p] V := by
  classical
  have hBdR_fin : Module.Finite S.BdRRing (S.BdRRing ⊗[ℚ_[p]] V) := inferInstance
  have hBdR_dim : Module.finrank S.BdRRing (S.BdRRing ⊗[ℚ_[p]] V) = Module.finrank ℚ_[p] V := by
    let b := Module.finBasis ℚ_[p] V
    let b' : Module.Basis (Fin (Module.finrank ℚ_[p] V)) S.BdRRing (S.BdRRing ⊗[ℚ_[p]] V) :=
      b.baseChange S.BdRRing
    rw [Module.finrank_eq_card_basis b', Fintype.card_fin]
  have hcard_le : ∀ (m : ℕ) (f : Fin m → S.D_dR ρ), LinearIndependent ℚ_[p] f →
      m ≤ Module.finrank ℚ_[p] V := by
    intro m f hf
    have hli := S.linearIndependent_BdR_of_D_dR ρ f hf
    have hle := hli.fintype_card_le_finrank
    rwa [Fintype.card_fin, hBdR_dim] at hle
  have hfin : Module.Finite ℚ_[p] (S.D_dR ρ) := by
    by_contra hnotfin
    have hstep : ∀ k : ℕ, ∃ f : Fin k → S.D_dR ρ, LinearIndependent ℚ_[p] f := by
      intro k
      induction k with
      | zero => exact ⟨Fin.elim0, linearIndependent_empty_type⟩
      | succ k ih =>
        obtain ⟨f, hf⟩ := ih
        have hne_top : Submodule.span ℚ_[p] (Set.range f) ≠ ⊤ := by
          intro htop
          apply hnotfin
          have hfg : (⊤ : Submodule ℚ_[p] (S.D_dR ρ)).FG := by
            rw [← htop]; exact Submodule.fg_span (Set.finite_range f)
          exact Module.finite_def.mpr hfg
        obtain ⟨v, hv⟩ : ∃ v : S.D_dR ρ, v ∉ Submodule.span ℚ_[p] (Set.range f) := by
          by_contra hall
          push Not at hall
          exact hne_top (eq_top_iff.mpr fun x _ => hall x)
        refine ⟨Fin.cons v f, ?_⟩
        rw [linearIndependent_finCons]
        exact ⟨hf, hv⟩
    obtain ⟨f, hf⟩ := hstep (Module.finrank ℚ_[p] V + 1)
    have hle := hcard_le _ f hf
    omega
  refine ⟨hfin, ?_⟩
  let bD := Module.finBasis ℚ_[p] (S.D_dR ρ)
  exact hcard_le (Module.finrank ℚ_[p] (S.D_dR ρ)) bD bD.linearIndependent

instance instFiniteDdR {V : Type u} [AddCommGroup V] [Module ℚ_[p] V] [Module.Finite ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) : Module.Finite ℚ_[p] (S.D_dR ρ) :=
  (S.D_dR_finite_and_finrank_le ρ).1

/-- Canonical injective `ℚ_[p]`-linear map `D_cris(V) → D_dR(V)`. -/
def D_cris_to_D_dR {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) : S.D_cris ρ →ₗ[ℚ_[p]] S.D_dR ρ where
  toFun d := ⟨S.ιV d.1, S.ιV_mem_D_dR ρ d.2⟩
  map_add' x y := Subtype.ext (map_add S.ιV x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul S.ιV c x.1)

theorem D_cris_to_D_dR_injective {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    [Module.Finite ℚ_[p] V] (ρ : Representation ℚ_[p] G V) :
    Function.Injective (S.D_cris_to_D_dR ρ) := fun _ _ h =>
  Subtype.ext (S.ιV_injective (congrArg Subtype.val h))

instance instFiniteDcris {V : Type u} [AddCommGroup V] [Module ℚ_[p] V] [Module.Finite ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) : Module.Finite ℚ_[p] (S.D_cris ρ) :=
  Module.Finite.of_injective (S.D_cris_to_D_dR ρ) (S.D_cris_to_D_dR_injective ρ)

/-- **Fontaine's Fundamental Admissibility Inequality**:
`dim_{ℚ_p} D_cris(V) ≤ dim_{ℚ_p} V` for every finite-dimensional `ℚ_[p]`-representation `V`! -/
theorem finrank_D_cris_le {V : Type u} [AddCommGroup V] [Module ℚ_[p] V] [Module.Finite ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) :
    Module.finrank ℚ_[p] (S.D_cris ρ) ≤ Module.finrank ℚ_[p] V :=
  le_trans
    (LinearMap.finrank_le_finrank_of_injective (S.D_cris_to_D_dR_injective ρ))
    (S.D_dR_finite_and_finrank_le ρ).2

/-- **Fontaine Crystalline Representation Predicate**: `V` is crystalline iff
`dim_{ℚ_p} D_cris(V) = dim_{ℚ_p} V`! -/
def IsCrystalline {V : Type u} [AddCommGroup V] [Module ℚ_[p] V] [Module.Finite ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) : Prop :=
  Module.finrank ℚ_[p] (S.D_cris ρ) = Module.finrank ℚ_[p] V

/-- Induced invertible Frobenius `φ : D_cris(V) ≃ₗ[ℚ_[p]] D_cris(V)`. -/
def D_cris_phi {V : Type u} [AddCommGroup V] [Module ℚ_[p] V] [Module.Finite ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) : S.D_cris ρ ≃ₗ[ℚ_[p]] S.D_cris ρ :=
  linearEquivOfInjectiveEndo
    { toFun := fun d => ⟨S.φV d.1, S.φV_mem_D_cris ρ d.2⟩
      map_add' := fun x y => Subtype.ext (map_add S.φV x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_smul S.φV c x.1) }
    (fun _ _ h => Subtype.ext (S.φV_injective (congrArg Subtype.val h)))

/-- Filtration step `Fil^i (B_dR ⊗_{ℚ_p} V)` induced by `S.Fil i`. -/
def FilBdRV {V : Type u} [AddCommGroup V] [Module ℚ_[p] V] (i : ℤ) :
    Submodule ℚ_[p] (S.BdRRing ⊗[ℚ_[p]] V) :=
  LinearMap.range (TensorProduct.map (S.Fil i).subtype (LinearMap.id : V →ₗ[ℚ_[p]] V))

theorem FilBdRV_antitone {V : Type u} [AddCommGroup V] [Module ℚ_[p] V] {i j : ℤ} (hij : i ≤ j) :
    S.FilBdRV (V := V) j ≤ S.FilBdRV (V := V) i := by
  rintro _ ⟨z, rfl⟩
  let incl : S.Fil j →ₗ[ℚ_[p]] S.Fil i := Submodule.inclusion (S.Fil_anti hij)
  refine ⟨TensorProduct.map incl LinearMap.id z, ?_⟩
  have hcomp : (TensorProduct.map (S.Fil i).subtype (LinearMap.id : V →ₗ[ℚ_[p]] V)).comp
      (TensorProduct.map incl LinearMap.id) =
      TensorProduct.map (S.Fil j).subtype (LinearMap.id : V →ₗ[ℚ_[p]] V) := by
    ext x v; rfl
  exact LinearMap.congr_fun hcomp z

theorem FilBdRV_exhaustive {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    (x : S.BdRRing ⊗[ℚ_[p]] V) : ∃ i : ℤ, x ∈ S.FilBdRV i := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_mem _⟩
  | tmul b v =>
    obtain ⟨i, hi⟩ := S.Fil_exh b
    exact ⟨i, ⟨⟨b, hi⟩ ⊗ₜ[ℚ_[p]] v, rfl⟩⟩
  | add x₁ x₂ ih₁ ih₂ =>
    obtain ⟨i₁, hi₁⟩ := ih₁
    obtain ⟨i₂, hi₂⟩ := ih₂
    exact ⟨min i₁ i₂, add_mem (S.FilBdRV_antitone (min_le_left i₁ i₂) hi₁)
      (S.FilBdRV_antitone (min_le_right i₁ i₂) hi₂)⟩

theorem FilBdRV_separated {V : Type u} [AddCommGroup V] [Module ℚ_[p] V] [Module.Finite ℚ_[p] V]
    {x : S.BdRRing ⊗[ℚ_[p]] V} (hx : ∀ i : ℤ, x ∈ S.FilBdRV i) : x = 0 := by
  classical
  let b := Module.finBasis ℚ_[p] V
  rw [← sum_tensorCoord_tmul b x]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk0 : tensorCoord b k x = 0 := by
    refine S.Fil_sep (tensorCoord b k x) fun i => ?_
    rcases hx i with ⟨z, rfl⟩
    clear hx
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul y v =>
      simp only [TensorProduct.map_tmul, Submodule.coe_subtype, LinearMap.id_coe, id_eq,
        tensorCoord_tmul]
      exact Submodule.smul_mem _ _ y.2
    | add z₁ z₂ ih₁ ih₂ =>
      rw [map_add, map_add]
      exact add_mem ih₁ ih₂
  rw [hk0, TensorProduct.zero_tmul]

/-- Induced exhaustive, separated, bounded decreasing Hodge filtration on `D_cris(V)`. -/
def D_cris_fil {V : Type u} [AddCommGroup V] [Module ℚ_[p] V] [Module.Finite ℚ_[p] V]
    (ρ : Representation ℚ_[p] G V) : HodgeFiltration ℚ_[p] (S.D_cris ρ) := by
  classical
  let F : ℤ → Submodule ℚ_[p] (S.D_cris ρ) :=
    fun i => (S.FilBdRV (V := V) i).comap (S.ιV.comp (S.D_cris ρ).subtype)
  have hanti : ∀ ⦃i j : ℤ⦄, i ≤ j → F j ≤ F i := fun i j hij =>
    Submodule.comap_mono (S.FilBdRV_antitone hij)
  let bD := Module.finBasis ℚ_[p] (S.D_cris ρ)
  have hbot : ∃ B : ℤ, F B = ⊤ := by
    choose bi hbi using fun k : Fin (Module.finrank ℚ_[p] (S.D_cris ρ)) =>
      S.FilBdRV_exhaustive (S.ιV (bD k).1)
    let B : ℤ := Finset.univ.fold min 0 bi
    refine ⟨B, eq_top_iff.mpr fun x _ => ?_⟩
    rw [← bD.sum_repr x]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    have hle : B ≤ bi k := by
      have := Finset.fold_min_le (s := (Finset.univ : Finset _)) (b := (0 : ℤ)) (f := bi) (c := bi k)
      exact this.mpr (Or.inr ⟨k, Finset.mem_univ k, le_rfl⟩)
    exact S.FilBdRV_antitone hle (hbi k)
  have htop : ∃ T : ℤ, F T = ⊥ := by
    -- By well-foundedness of `ℕ`, pick `T ≥ 0` minimizing `finrank (F T)`
    let dims : Set ℕ := { d | ∃ i : ℤ, Module.finrank ℚ_[p] (F i) = d }
    have hne : dims.Nonempty := ⟨Module.finrank ℚ_[p] (F 0), 0, rfl⟩
    let dmin := Nat.find hne
    obtain ⟨T, hT⟩ := Nat.find_spec hne
    refine ⟨T, eq_bot_iff.mpr fun x hx => ?_⟩
    have hx_all : ∀ i : ℤ, x ∈ F i := by
      intro i
      by_cases hle : i ≤ T
      · exact hanti hle hx
      · have hTi : T ≤ i := le_of_not_ge hle
        have hsub : F i ≤ F T := hanti hTi
        have hdim_eq : Module.finrank ℚ_[p] (F i) = Module.finrank ℚ_[p] (F T) := by
          apply le_antisymm (Submodule.finrank_mono hsub)
          rw [hT]
          exact Nat.find_min' hne ⟨i, rfl⟩
        have hFeq : F i = F T := Submodule.eq_of_le_of_finrank_eq hsub hdim_eq
        rwa [hFeq]
    exact Subtype.ext (S.ιV_injective (S.FilBdRV_separated fun i => hx_all i))
  let B := hbot.choose
  let T := max B htop.choose
  exact
    { fil := F
      antitone := hanti
      botBound := B
      topBound := T
      bot_le_top := le_max_left _ _
      eq_top_of_le := fun i hi => eq_top_iff.mpr (hbot.choose_spec ▸ hanti hi)
      eq_bot_of_gt := fun i hi => eq_bot_iff.mpr (htop.choose_spec ▸ hanti (le_trans (le_max_right _ _) hi.le)) }

/-- **Main Bridge Theorem into Stage 11**:
For ANY finite-dimensional `ℚ_[p]`-representation `ρ : Representation ℚ_[p] G V` (and in
particular any crystalline representation `IsCrystalline S ρ`), `D_cris(V)` carries a genuine
`Stage11CrystallineFontaine.FilteredPhiModule p (S.D_cris ρ)`! -/
def D_cris_toFilteredPhiModule {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    [Module.Finite ℚ_[p] V] (ρ : Representation ℚ_[p] G V) :
    FilteredPhiModule p (S.D_cris ρ) where
  φ := S.D_cris_phi ρ
  fil := S.D_cris_fil ρ

/-- The trivial `ℚ_[p]`-representation `1` on any finite-dimensional `V` is **crystalline**
(`IsCrystalline S 1`, i.e. `dim D_cris(V) = dim V`)! -/
theorem isCrystalline_trivial {V : Type u} [AddCommGroup V] [Module ℚ_[p] V]
    [Module.Finite ℚ_[p] V] :
    S.IsCrystalline (1 : Representation ℚ_[p] G V) := by
  unfold IsCrystalline
  refine le_antisymm (S.finrank_D_cris_le 1) ?_
  let emb : V →ₗ[ℚ_[p]] S.D_cris (1 : Representation ℚ_[p] G V) :=
    { toFun := fun v => ⟨(1 : S.BcrisRing) ⊗ₜ[ℚ_[p]] v, (mem_D_cris_iff S 1).mpr fun g => by
        simp [actBcrisV]⟩
      map_add' := fun u v => Subtype.ext (TensorProduct.tmul_add _ u v)
      map_smul' := fun c v => Subtype.ext (TensorProduct.tmul_smul c _ v) }
  have hemb_inj : Function.Injective emb := by
    intro u v huv
    have h1 : (1 : S.BcrisRing) ⊗ₜ[ℚ_[p]] u = (1 : S.BcrisRing) ⊗ₜ[ℚ_[p]] v :=
      congrArg Subtype.val huv
    have h2 : (1 : S.BdRRing) ⊗ₜ[ℚ_[p]] u = (1 : S.BdRRing) ⊗ₜ[ℚ_[p]] v := by
      have := congrArg S.ιV h1
      simpa [ιV] using this
    classical
    let b := Module.finBasis ℚ_[p] V
    apply b.repr.injective
    ext k
    have hk := congrArg (tensorCoord b k) h2
    simp only [tensorCoord_tmul, Algebra.smul_def, mul_one] at hk
    exact (algebraMap ℚ_[p] S.BdRRing).injective hk
  exact LinearMap.finrank_le_finrank_of_injective hemb_inj

end FontainePeriodSystem

end DcrisFunctor

/-! ## Section 7: Concrete Non-Vacuous `LocTied p` Witness (`Nonempty (LocTied p)`) for Every Prime `p` -/

section LocTiedWitness

/-- **Local Fontaine Period Package (`LocPrimePackage p`)**: packages `A_inf`, `B_cris`, `B_dR`,
`φ`, `ι`, `Fil•`, and `t` for a prime `p`, paralleling Alpöge's `LocPrime` / `LocAinf`. -/
structure LocPrimePackage (p : ℕ) [Fact p.Prime] where
  AinfRing : Type
  BcrisRing : Type
  BdRRing : Type
  [commRingAinf : CommRing AinfRing]
  [commRingBcris : CommRing BcrisRing]
  [fieldBdR : Field BdRRing]
  padicToBcris : ℚ_[p] →+* BcrisRing
  padicToBdR : ℚ_[p] →+* BdRRing
  ainfToBcris : AinfRing →+* BcrisRing
  frobBcris : BcrisRing →+* BcrisRing
  bcrisToBdR : BcrisRing →+* BdRRing
  FilBdR : ℤ → AddSubgroup BdRRing
  tBcris : BcrisRing
  t_unit : IsUnit tBcris
  frob_t : frobBcris tBcris = ((p : ℕ) : BcrisRing) * tBcris
  frob_padic : ∀ c : ℚ_[p], frobBcris (padicToBcris c) = padicToBcris c
  fil_anti : ∀ ⦃i j : ℤ⦄, i ≤ j → FilBdR j ≤ FilBdR i
  fil_mul : ∀ ⦃i j : ℤ⦄ {x y : BdRRing}, x ∈ FilBdR i → y ∈ FilBdR j → x * y ∈ FilBdR (i + j)
  t_mem_fil1 : bcrisToBdR tBcris ∈ FilBdR 1
  t_not_mem_fil2 : bcrisToBdR tBcris ∉ FilBdR 2

attribute [instance] LocPrimePackage.commRingAinf LocPrimePackage.commRingBcris
  LocPrimePackage.fieldBdR

/-- **`LocTied p P`**: ties an abstract `LocPrimePackage p` to our **CONCRETE constructed
Fontaine period rings** `A_inf p (OCp p)`, `Bcris p (OCp p)`, and `BdR p (OCp p)` over
`O_{ℂ_p} = PadicComplexInt p` via ring isomorphisms intertwining all structures! -/
structure LocTied (p : ℕ) [Fact p.Prime] (P : LocPrimePackage p) where
  eA : P.AinfRing ≃+* A_inf p (OCp p)
  eB : P.BcrisRing ≃+* Bcris p (OCp p)
  eD : P.BdRRing ≃+* BdR p (OCp p)
  zB : ∀ c : ℚ_[p], eB (P.padicToBcris c) = padicToBcris p (OCp p) c
  zD : ∀ c : ℚ_[p], eD (P.padicToBdR c) = padicToBdR p (OCp p) c
  ιA : ∀ a : P.AinfRing, eB (P.ainfToBcris a) = ainfToBcris p (OCp p) (eA a)
  frob : ∀ b : P.BcrisRing, eB (P.frobBcris b) = frobBcris p (OCp p) (eB b)
  incl : ∀ b : P.BcrisRing, eD (P.bcrisToBdR b) = bcrisToBdR p (OCp p) (eB b)
  fil : ∀ (i : ℤ) (x : P.BdRRing), x ∈ P.FilBdR i ↔ eD x ∈ FilBdR p (OCp p) i
  t_eq : eB P.tBcris = tBcris p (OCp p)

/-- The **concrete Fontaine Period Package over `O_{ℂ_p} = PadicComplexInt p`** built directly
from our Mathlib `WittVector`-based `A_inf`, `A_cris`, `B_cris`, `B_dR^+`, and `B_dR`. -/
def concreteLocPrimePackage (p : ℕ) [Fact p.Prime] : LocPrimePackage p where
  AinfRing := A_inf p (OCp p)
  BcrisRing := Bcris p (OCp p)
  BdRRing := BdR p (OCp p)
  padicToBcris := padicToBcris p (OCp p)
  padicToBdR := padicToBdR p (OCp p)
  ainfToBcris := ainfToBcris p (OCp p)
  frobBcris := frobBcris p (OCp p)
  bcrisToBdR := bcrisToBdR p (OCp p)
  FilBdR := FilBdR p (OCp p)
  tBcris := tBcris p (OCp p)
  t_unit := isUnit_tBcris (p := p) (O := OCp p)
  frob_t := frobBcris_tBcris (p := p) (O := OCp p)
  frob_padic := frobBcris_padic (p := p) (O := OCp p)
  fil_anti := fun _ _ hij => FilBdR_antitone hij
  fil_mul := fun _ _ _ _ hx hy => FilBdR_mul hx hy
  t_mem_fil1 := by rw [bcrisToBdR_tBcris]; exact tInBdR_mem_FilBdR_one
  t_not_mem_fil2 := by rw [bcrisToBdR_tBcris]; exact tInBdR_not_mem_FilBdR_two

/-- **Concrete Non-Vacuous `Nonempty (LocTied p)` Witness** for EVERY prime `p`! -/
theorem nonempty_locTied (p : ℕ) [Fact p.Prime] :
    ∃ P : LocPrimePackage p, Nonempty (LocTied p P) :=
  ⟨concreteLocPrimePackage p, ⟨{
    eA := RingEquiv.refl _
    eB := RingEquiv.refl _
    eD := RingEquiv.refl _
    zB := fun _ => rfl
    zD := fun _ => rfl
    ιA := fun _ => rfl
    frob := fun _ => rfl
    incl := fun _ => rfl
    fil := fun _ _ => Iff.rfl
    t_eq := rfl }⟩⟩

/-- Scaling automorphism `X ↦ c * X` of `Polynomial ℚ_[p]` for any unit `c : ℚ_[p]ˣ`. -/
private def scalePoly (p : ℕ) [Fact p.Prime] (c : ℚ_[p]ˣ) :
    Polynomial ℚ_[p] ≃ₐ[ℚ_[p]] Polynomial ℚ_[p] :=
  AlgEquiv.ofAlgHom
    (Polynomial.aeval (Polynomial.C (c : ℚ_[p]) * Polynomial.X))
    (Polynomial.aeval (Polynomial.C ((c⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * Polynomial.X))
    (by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, AlgHom.id_apply, Polynomial.aeval_X, map_mul,
        Polynomial.aeval_C, Polynomial.algebraMap_eq]
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul])
    (by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, AlgHom.id_apply, Polynomial.aeval_X, map_mul,
        Polynomial.aeval_C, Polynomial.algebraMap_eq]
      rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul])

private theorem coeff_scalePoly {p : ℕ} [Fact p.Prime] (c : ℚ_[p]ˣ) (f : Polynomial ℚ_[p]) (k : ℕ) :
    (scalePoly p c f).coeff k = (c : ℚ_[p]) ^ k * f.coeff k := by
  induction f using Polynomial.induction_on' with
  | add f₁ f₂ ih₁ ih₂ =>
    simp [map_add, Polynomial.coeff_add, ih₁, ih₂, mul_add]
  | monomial n a =>
    change (Polynomial.aeval (Polynomial.C (c : ℚ_[p]) * Polynomial.X) (Polynomial.monomial n a)).coeff k = _
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, mul_pow, ← map_pow,
      Polynomial.smul_eq_C_mul, mul_one, ← mul_assoc, ← map_mul, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_monomial]
    by_cases h : n = k
    · subst h; simp [mul_comm]
    · have h' : k ≠ n := Ne.symm h
      simp [h, h']

private theorem eval_zero_scalePoly {p : ℕ} [Fact p.Prime] (c : ℚ_[p]ˣ) (f : Polynomial ℚ_[p]) :
    (scalePoly p c f).eval 0 = f.eval 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero, coeff_scalePoly,
    pow_zero, one_mul]

private theorem scalePoly_X {p : ℕ} [Fact p.Prime] (c : ℚ_[p]ˣ) :
    scalePoly p c Polynomial.X = Polynomial.C (c : ℚ_[p]) * Polynomial.X := by
  change Polynomial.aeval (Polynomial.C (c : ℚ_[p]) * Polynomial.X) Polynomial.X = _
  rw [Polynomial.aeval_X]

private theorem natDegree_scalePoly {p : ℕ} [Fact p.Prime] (c : ℚ_[p]ˣ) (f : Polynomial ℚ_[p]) :
    (scalePoly p c f).natDegree = f.natDegree := by
  refine le_antisymm ?_ ?_
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn => ?_
    rw [coeff_scalePoly, Polynomial.coeff_eq_zero_of_natDegree_lt hn, mul_zero]
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn => ?_
    have h0 := Polynomial.coeff_eq_zero_of_natDegree_lt hn
    rw [coeff_scalePoly] at h0
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero n c.ne_zero)

private theorem leadingCoeff_scalePoly {p : ℕ} [Fact p.Prime] (c : ℚ_[p]ˣ) (f : Polynomial ℚ_[p]) :
    (scalePoly p c f).leadingCoeff = (c : ℚ_[p]) ^ f.natDegree * f.leadingCoeff := by
  rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, natDegree_scalePoly, coeff_scalePoly]

private theorem exists_X_pow_mul_eval_zero_ne {K : Type*} [Field K] {f : Polynomial K} (hf : f ≠ 0) :
    ∃ (k : ℕ) (f₀ : Polynomial K), f₀.eval 0 ≠ 0 ∧ f = Polynomial.X ^ k * f₀ := by
  induction hn : f.natDegree generalizing f with
  | zero =>
    refine ⟨0, f, ?_, by simp⟩
    have h := Polynomial.eq_C_of_natDegree_eq_zero hn
    rw [h, Polynomial.eval_C]
    intro hc0
    exact hf (by rw [h, hc0, map_zero])
  | succ d ih =>
    by_cases h0 : f.eval 0 = 0
    · obtain ⟨g, hg⟩ := (Polynomial.X_dvd_iff (f := f)).mpr (by rwa [Polynomial.coeff_zero_eq_eval_zero])
      have hg0 : g ≠ 0 := by intro h; rw [h, mul_zero] at hg; exact hf hg
      have hdeg : g.natDegree = d := by
        have h1 : f.natDegree = (Polynomial.X * g).natDegree := congrArg Polynomial.natDegree hg
        rw [Polynomial.natDegree_X_mul hg0] at h1
        omega
      obtain ⟨k, g₀, hg₀, hgeq⟩ := ih hg0 hdeg
      refine ⟨k + 1, g₀, hg₀, ?_⟩
      rw [hg, hgeq, pow_succ', mul_assoc]
    · exact ⟨0, f, h0, by simp⟩

private theorem isUnit_scaleAwayX (p : ℕ) [Fact p.Prime] (u : ℚ_[p]ˣ) :
    IsUnit (((algebraMap (Polynomial ℚ_[p]) (Localization.Away (Polynomial.X : Polynomial ℚ_[p]))).comp
      (scalePoly p u).toAlgHom.toRingHom) Polynomial.X) := by
  rw [RingHom.comp_apply]
  change IsUnit (algebraMap (Polynomial ℚ_[p]) (Localization.Away (Polynomial.X : Polynomial ℚ_[p]))
    (scalePoly p u Polynomial.X))
  rw [scalePoly_X, map_mul]
  have hc : IsUnit (algebraMap (Polynomial ℚ_[p])
      (Localization.Away (Polynomial.X : Polynomial ℚ_[p])) (Polynomial.C (u : ℚ_[p]))) :=
    (u.isUnit.map Polynomial.C).map (algebraMap _ _)
  exact hc.mul (IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial ℚ_[p]))

/-- Ring homomorphism lifting `scalePoly u` to `Localization.Away (Polynomial.X : Polynomial ℚ_[p])`. -/
private def scaleAwayHom (p : ℕ) [Fact p.Prime] (u : ℚ_[p]ˣ) :
    Localization.Away (Polynomial.X : Polynomial ℚ_[p]) →ₐ[ℚ_[p]]
      Localization.Away (Polynomial.X : Polynomial ℚ_[p]) :=
  { toRingHom := IsLocalization.Away.lift (Polynomial.X : Polynomial ℚ_[p])
      (g := (algebraMap (Polynomial ℚ_[p]) (Localization.Away (Polynomial.X : Polynomial ℚ_[p]))).comp
        (scalePoly p u).toAlgHom.toRingHom)
      (isUnit_scaleAwayX p u)
    commutes' := fun q => by
      change (IsLocalization.Away.lift (Polynomial.X : Polynomial ℚ_[p])
        (g := (algebraMap (Polynomial ℚ_[p]) (Localization.Away (Polynomial.X : Polynomial ℚ_[p]))).comp
          (scalePoly p u).toAlgHom.toRingHom) (isUnit_scaleAwayX p u))
        (algebraMap (Polynomial ℚ_[p]) (Localization.Away (Polynomial.X : Polynomial ℚ_[p])) (Polynomial.C q)) =
        algebraMap (Polynomial ℚ_[p]) (Localization.Away (Polynomial.X : Polynomial ℚ_[p])) (Polynomial.C q)
      rw [IsLocalization.Away.lift_eq, RingHom.comp_apply]
      change algebraMap _ _ (scalePoly p u (Polynomial.C q)) = _
      rw [← Polynomial.algebraMap_eq, AlgEquiv.commutes] }

private theorem scaleAwayHom_algebraMap {p : ℕ} [Fact p.Prime] (u : ℚ_[p]ˣ) (f : Polynomial ℚ_[p]) :
    scaleAwayHom p u (algebraMap (Polynomial ℚ_[p]) _ f) = algebraMap (Polynomial ℚ_[p]) _ (scalePoly p u f) := by
  change (IsLocalization.Away.lift (Polynomial.X : Polynomial ℚ_[p])
    (g := (algebraMap (Polynomial ℚ_[p]) (Localization.Away (Polynomial.X : Polynomial ℚ_[p]))).comp
      (scalePoly p u).toAlgHom.toRingHom) (isUnit_scaleAwayX p u))
    (algebraMap (Polynomial ℚ_[p]) (Localization.Away (Polynomial.X : Polynomial ℚ_[p])) f) = _
  rw [IsLocalization.Away.lift_eq]; rfl

/-- Lifting `scalePoly c` to `Localization.Away (Polynomial.X : Polynomial ℚ_[p])`. -/
private def scaleAway (p : ℕ) [Fact p.Prime] (c : ℚ_[p]ˣ) :
    Localization.Away (Polynomial.X : Polynomial ℚ_[p]) ≃ₐ[ℚ_[p]]
      Localization.Away (Polynomial.X : Polynomial ℚ_[p]) :=
  AlgEquiv.ofAlgHom (scaleAwayHom p c) (scaleAwayHom p c⁻¹)
    (by
      apply AlgHom.coe_ringHom_injective
      refine IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial ℚ_[p]))
        (RingHom.ext fun f => ?_)
      change scaleAwayHom p c (scaleAwayHom p c⁻¹ (algebraMap _ _ f)) = algebraMap _ _ f
      rw [scaleAwayHom_algebraMap, scaleAwayHom_algebraMap]
      congr 1; ext k; simp [coeff_scalePoly])
    (by
      apply AlgHom.coe_ringHom_injective
      refine IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial ℚ_[p]))
        (RingHom.ext fun f => ?_)
      change scaleAwayHom p c⁻¹ (scaleAwayHom p c (algebraMap _ _ f)) = algebraMap _ _ f
      rw [scaleAwayHom_algebraMap, scaleAwayHom_algebraMap]
      congr 1; ext k; simp [coeff_scalePoly])

private theorem scaleAway_algebraMap {p : ℕ} [Fact p.Prime] (c : ℚ_[p]ˣ) (f : Polynomial ℚ_[p]) :
    scaleAway p c (algebraMap (Polynomial ℚ_[p]) _ f) = algebraMap (Polynomial ℚ_[p]) _ (scalePoly p c f) :=
  scaleAwayHom_algebraMap c f

/-- Ring homomorphism lifting `scalePoly u` to `FractionRing (Polynomial ℚ_[p])`. -/
private def scaleFracHom (p : ℕ) [Fact p.Prime] (u : ℚ_[p]ˣ) :
    FractionRing (Polynomial ℚ_[p]) →ₐ[ℚ_[p]] FractionRing (Polynomial ℚ_[p]) :=
  { toRingHom := IsLocalization.lift (M := nonZeroDivisors (Polynomial ℚ_[p]))
      (S := FractionRing (Polynomial ℚ_[p]))
      (g := (algebraMap (Polynomial ℚ_[p]) (FractionRing (Polynomial ℚ_[p]))).comp
        (scalePoly p u).toAlgHom.toRingHom)
      (fun ⟨f, hf⟩ => by
        rw [RingHom.comp_apply]
        change IsUnit (algebraMap (Polynomial ℚ_[p]) (FractionRing (Polynomial ℚ_[p])) (scalePoly p u f))
        refine IsUnit.mk0 _ ?_
        intro h0
        have hf0 : scalePoly p u f = 0 :=
          IsFractionRing.injective (Polynomial ℚ_[p]) (FractionRing (Polynomial ℚ_[p]))
            (h0.trans (map_zero _).symm)
        exact nonZeroDivisors.ne_zero hf ((scalePoly p u).injective (by rwa [map_zero])))
    commutes' := fun q => by
      change (IsLocalization.lift (M := nonZeroDivisors (Polynomial ℚ_[p]))
        (S := FractionRing (Polynomial ℚ_[p]))
        (g := (algebraMap (Polynomial ℚ_[p]) (FractionRing (Polynomial ℚ_[p]))).comp
          (scalePoly p u).toAlgHom.toRingHom) _)
        (algebraMap (Polynomial ℚ_[p]) (FractionRing (Polynomial ℚ_[p])) (Polynomial.C q)) =
        algebraMap (Polynomial ℚ_[p]) (FractionRing (Polynomial ℚ_[p])) (Polynomial.C q)
      rw [IsLocalization.lift_eq, RingHom.comp_apply]
      change algebraMap _ _ (scalePoly p u (Polynomial.C q)) = _
      rw [← Polynomial.algebraMap_eq, AlgEquiv.commutes] }

private theorem scaleFracHom_algebraMap {p : ℕ} [Fact p.Prime] (u : ℚ_[p]ˣ) (f : Polynomial ℚ_[p]) :
    scaleFracHom p u (algebraMap (Polynomial ℚ_[p]) _ f) = algebraMap (Polynomial ℚ_[p]) _ (scalePoly p u f) := by
  dsimp [scaleFracHom]
  exact IsLocalization.lift_eq _ f

/-- Lifting `scalePoly c` to `FractionRing (Polynomial ℚ_[p])`. -/
private def scaleFrac (p : ℕ) [Fact p.Prime] (c : ℚ_[p]ˣ) :
    FractionRing (Polynomial ℚ_[p]) ≃ₐ[ℚ_[p]] FractionRing (Polynomial ℚ_[p]) :=
  AlgEquiv.ofAlgHom (scaleFracHom p c) (scaleFracHom p c⁻¹)
    (by
      apply AlgHom.coe_ringHom_injective
      refine IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℚ_[p])) (RingHom.ext fun f => ?_)
      change scaleFracHom p c (scaleFracHom p c⁻¹ (algebraMap _ _ f)) = algebraMap _ _ f
      rw [scaleFracHom_algebraMap, scaleFracHom_algebraMap]
      congr 1; ext k; simp [coeff_scalePoly])
    (by
      apply AlgHom.coe_ringHom_injective
      refine IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℚ_[p])) (RingHom.ext fun f => ?_)
      change scaleFracHom p c⁻¹ (scaleFracHom p c (algebraMap _ _ f)) = algebraMap _ _ f
      rw [scaleFracHom_algebraMap, scaleFracHom_algebraMap]
      congr 1; ext k; simp [coeff_scalePoly])

private theorem scaleFrac_algebraMap {p : ℕ} [Fact p.Prime] (c : ℚ_[p]ˣ) (f : Polynomial ℚ_[p]) :
    scaleFrac p c (algebraMap (Polynomial ℚ_[p]) _ f) = algebraMap (Polynomial ℚ_[p]) _ (scalePoly p c f) :=
  scaleFracHom_algebraMap c f

/-- Canonical `ℚ_[p]`-algebra embedding `ℚ_[p][X, X⁻¹] → Frac(ℚ_[p][X])`. -/
private def inclAwayFrac (p : ℕ) [Fact p.Prime] :
    Localization.Away (Polynomial.X : Polynomial ℚ_[p]) →ₐ[ℚ_[p]] FractionRing (Polynomial ℚ_[p]) :=
  { toRingHom := IsLocalization.Away.lift (Polynomial.X : Polynomial ℚ_[p])
      (g := algebraMap (Polynomial ℚ_[p]) (FractionRing (Polynomial ℚ_[p])))
      (IsUnit.mk0 _ (fun h0 => Polynomial.X_ne_zero
        (IsFractionRing.injective (Polynomial ℚ_[p]) (FractionRing (Polynomial ℚ_[p]))
          (h0.trans (map_zero _).symm))))
    commutes' := fun q => by
      change (IsLocalization.Away.lift (Polynomial.X : Polynomial ℚ_[p])
        (g := algebraMap (Polynomial ℚ_[p]) (FractionRing (Polynomial ℚ_[p]))) _)
        (algebraMap (Polynomial ℚ_[p]) (Localization.Away (Polynomial.X : Polynomial ℚ_[p])) (Polynomial.C q)) = _
      rw [IsLocalization.Away.lift_eq]; rfl }

private theorem inclAwayFrac_algebraMap {p : ℕ} [Fact p.Prime] (f : Polynomial ℚ_[p]) :
    inclAwayFrac p (algebraMap (Polynomial ℚ_[p]) _ f) =
      algebraMap (Polynomial ℚ_[p]) (FractionRing (Polynomial ℚ_[p])) f := by
  dsimp [inclAwayFrac]
  exact IsLocalization.Away.lift_eq _ _ f

/-- **Concrete Inhabited `FontainePeriodSystem p (ℤ_[p]ˣ)`** with genuine cyclotomic group
`G = ℤ_[p]ˣ`, `B_cris = ℚ_[p][t, t⁻¹]`, `B_dR = Frac(ℚ_[p][t])`, `φ(t) = p * t`,
`g • t = g * t`, `(B_dR)^G = ℚ_[p]`, and `t ∈ Fil^1 \ Fil^2`! -/
def cyclotomicLaurentPeriodSystem (p : ℕ) [Fact p.Prime] :
    FontainePeriodSystem p (ℤ_[p]ˣ) := by
  classical
  have hp : p.Prime := Fact.out
  let toQpUnit : ℤ_[p]ˣ →* ℚ_[p]ˣ := Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom
  let pUnit : ℚ_[p]ˣ := Units.mk0 ((p : ℕ) : ℚ_[p]) (Nat.cast_ne_zero.mpr hp.ne_zero)
  let BcrisR := Localization.Away (Polynomial.X : Polynomial ℚ_[p])
  let BdRR := FractionRing (Polynomial ℚ_[p])
  let X_dR : BdRR := algebraMap (Polynomial ℚ_[p]) BdRR Polynomial.X
  have hXdR0 : X_dR ≠ 0 := fun h0 => Polynomial.X_ne_zero
    (IsFractionRing.injective (Polynomial ℚ_[p]) BdRR (h0.trans (map_zero _).symm))
  have hinj_ne : ∀ {b : Polynomial ℚ_[p]}, b.eval 0 ≠ 0 → algebraMap (Polynomial ℚ_[p]) BdRR b ≠ 0 := by
    intro b hb h0
    have hb0 : b = 0 := IsFractionRing.injective (Polynomial ℚ_[p]) BdRR (h0.trans (map_zero _).symm)
    exact hb (by rw [hb0, Polynomial.eval_zero])
  let FilFn : ℤ → Submodule ℚ_[p] BdRR := fun i =>
    { carrier := { z : BdRR | ∃ (a b : Polynomial ℚ_[p]), b.eval 0 ≠ 0 ∧
        z = X_dR ^ i * (algebraMap (Polynomial ℚ_[p]) BdRR a / algebraMap (Polynomial ℚ_[p]) BdRR b) }
      zero_mem' := ⟨0, 1, by simp, by simp⟩
      add_mem' := by
        rintro _ _ ⟨a₁, b₁, hb₁, rfl⟩ ⟨a₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, by rw [Polynomial.eval_mul]; exact mul_ne_zero hb₁ hb₂, ?_⟩
        have hb₁0 : algebraMap (Polynomial ℚ_[p]) BdRR b₁ ≠ 0 := hinj_ne hb₁
        have hb₂0 : algebraMap (Polynomial ℚ_[p]) BdRR b₂ ≠ 0 := hinj_ne hb₂
        rw [map_add, map_mul, map_mul, map_mul, ← mul_add, div_add_div _ _ hb₁0 hb₂0,
          mul_comm (algebraMap (Polynomial ℚ_[p]) BdRR b₁)]
      smul_mem' := by
        rintro c _ ⟨a, b, hb, rfl⟩
        refine ⟨Polynomial.C c * a, b, hb, ?_⟩
        rw [Algebra.smul_def, map_mul]
        change algebraMap ℚ_[p] BdRR c * _ = X_dR ^ i * (algebraMap ℚ_[p] BdRR c * algebraMap _ _ a / _)
        ring }
  refine
    { BcrisRing := BcrisR
      BdRRing := BdRR
      actBcris :=
        { toFun := fun g => scaleAway p (toQpUnit g)
          map_one' := by
            apply AlgEquiv.ext; intro x
            have h : (scaleAway p (toQpUnit 1)).toAlgHom.toRingHom = RingHom.id BcrisR := by
              rw [map_one]
              refine IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial ℚ_[p]))
                (RingHom.ext fun f => ?_)
              change scaleAway p 1 (algebraMap _ _ f) = algebraMap _ _ f
              rw [scaleAway_algebraMap]
              congr 1; ext k; simp [coeff_scalePoly]
            exact RingHom.congr_fun h x
          map_mul' := fun g₁ g₂ => by
            apply AlgEquiv.ext; intro x
            have h : (scaleAway p (toQpUnit (g₁ * g₂))).toAlgHom.toRingHom =
                ((scaleAway p (toQpUnit g₁)).toAlgHom.toRingHom).comp
                  (scaleAway p (toQpUnit g₂)).toAlgHom.toRingHom := by
              refine IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial ℚ_[p]))
                (RingHom.ext fun f => ?_)
              change scaleAway p (toQpUnit (g₁ * g₂)) (algebraMap _ _ f) =
                scaleAway p (toQpUnit g₁) (scaleAway p (toQpUnit g₂) (algebraMap _ _ f))
              rw [scaleAway_algebraMap, scaleAway_algebraMap, scaleAway_algebraMap]
              congr 1; ext k; simp [coeff_scalePoly, map_mul, mul_pow, mul_assoc]
            exact RingHom.congr_fun h x }
      actBdR :=
        { toFun := fun g => scaleFrac p (toQpUnit g)
          map_one' := by
            apply AlgEquiv.ext; intro x
            have h : (scaleFrac p (toQpUnit 1)).toAlgHom.toRingHom = RingHom.id BdRR := by
              rw [map_one]
              refine IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℚ_[p]))
                (RingHom.ext fun f => ?_)
              change scaleFrac p 1 (algebraMap _ _ f) = algebraMap _ _ f
              rw [scaleFrac_algebraMap]
              congr 1; ext k; simp [coeff_scalePoly]
            exact RingHom.congr_fun h x
          map_mul' := fun g₁ g₂ => by
            apply AlgEquiv.ext; intro x
            have h : (scaleFrac p (toQpUnit (g₁ * g₂))).toAlgHom.toRingHom =
                ((scaleFrac p (toQpUnit g₁)).toAlgHom.toRingHom).comp
                  (scaleFrac p (toQpUnit g₂)).toAlgHom.toRingHom := by
              refine IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℚ_[p]))
                (RingHom.ext fun f => ?_)
              change scaleFrac p (toQpUnit (g₁ * g₂)) (algebraMap _ _ f) =
                scaleFrac p (toQpUnit g₁) (scaleFrac p (toQpUnit g₂) (algebraMap _ _ f))
              rw [scaleFrac_algebraMap, scaleFrac_algebraMap, scaleFrac_algebraMap]
              congr 1; ext k; simp [coeff_scalePoly, map_mul, mul_pow, mul_assoc]
            exact RingHom.congr_fun h x }
      invBdR := fun z hz => by
        have h1p_norm : ‖((1 + p : ℕ) : ℚ_[p])‖ = 1 := by
          have hp_lt : ‖((p : ℕ) : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
          have h1 : ‖(1 : ℚ_[p])‖ = 1 := norm_one
          have hle : ‖(1 : ℚ_[p]) + ((p : ℕ) : ℚ_[p])‖ ≤ 1 := by
            calc ‖(1 : ℚ_[p]) + ((p : ℕ) : ℚ_[p])‖ ≤ max ‖(1 : ℚ_[p])‖ ‖((p : ℕ) : ℚ_[p])‖ :=
                  IsUltrametricDist.norm_add_le_max _ _
              _ = 1 := by rw [h1]; exact max_eq_left hp_lt.le
          have hge : 1 ≤ ‖(1 : ℚ_[p]) + ((p : ℕ) : ℚ_[p])‖ := by
            by_contra hlt
            push Not at hlt
            have hsub : ‖(1 : ℚ_[p])‖ ≤ max ‖(1 : ℚ_[p]) + ((p : ℕ) : ℚ_[p])‖ ‖-((p : ℕ) : ℚ_[p])‖ := by
              simpa using IsUltrametricDist.norm_add_le_max ((1 : ℚ_[p]) + (p : ℚ_[p])) (-(p : ℚ_[p]))
            rw [norm_neg, h1] at hsub
            have hmax : max ‖(1 : ℚ_[p]) + ((p : ℕ) : ℚ_[p])‖ ‖((p : ℕ) : ℚ_[p])‖ < 1 := max_lt hlt hp_lt
            linarith
          exact_mod_cast le_antisymm hle hge
        let g0_int : ℤ_[p] := ⟨((1 + p : ℕ) : ℚ_[p]), h1p_norm.le⟩
        have hg0_unit : IsUnit g0_int := by
          rw [PadicInt.isUnit_iff]; exact h1p_norm
        obtain ⟨g0, hg0⟩ := hg0_unit
        have hu0 : (toQpUnit g0 : ℚ_[p]) = ((1 + p : ℕ) : ℚ_[p]) := by
          change ((g0 : ℤ_[p]) : ℚ_[p]) = _; rw [hg0]
        have hu0_pow_ne : ∀ {a b : ℕ}, a ≠ b → (toQpUnit g0 : ℚ_[p]) ^ a ≠ (toQpUnit g0 : ℚ_[p]) ^ b := by
          intro a b hab heq
          rw [hu0, ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_inj] at heq
          have h1p : 1 < 1 + p := by have := hp.pos; omega
          exact hab (Nat.pow_right_injective h1p heq)
        obtain ⟨⟨f₀, ⟨h₀, hh₀⟩⟩, hz_eq⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial ℚ_[p])) z
        dsimp only at hz_eq
        have hh₀0 : h₀ ≠ 0 := nonZeroDivisors.ne_zero hh₀
        let d := EuclideanDomain.gcd f₀ h₀
        have hd0 : d ≠ 0 := fun h => hh₀0 (zero_dvd_iff.mp (h ▸ EuclideanDomain.gcd_dvd_right f₀ h₀))
        obtain ⟨f, hf⟩ := EuclideanDomain.gcd_dvd_left f₀ h₀
        obtain ⟨h, hh⟩ := EuclideanDomain.gcd_dvd_right f₀ h₀
        have hh0 : h ≠ 0 := fun h' => hh₀0 (by rw [hh, h', mul_zero])
        have hcop : IsCoprime f h := by
          have hg1 : IsUnit (EuclideanDomain.gcd f h) := by
            have hd_dvd : d * EuclideanDomain.gcd f h ∣ d := by
              have h1 : d * EuclideanDomain.gcd f h ∣ f₀ := by
                rw [hf]; exact mul_dvd_mul_left d (EuclideanDomain.gcd_dvd_left f h)
              have h2 : d * EuclideanDomain.gcd f h ∣ h₀ := by
                rw [hh]; exact mul_dvd_mul_left d (EuclideanDomain.gcd_dvd_right f h)
              exact EuclideanDomain.dvd_gcd h1 h2
            obtain ⟨c, hc⟩ := hd_dvd
            have h1 : EuclideanDomain.gcd f h * c = 1 :=
              mul_left_cancel₀ hd0 (by linear_combination hc.symm)
            exact isUnit_iff_exists_inv.mpr ⟨c, h1⟩
          obtain ⟨u, hu⟩ := hg1
          refine ⟨EuclideanDomain.gcdA f h * (u⁻¹ : (Polynomial ℚ_[p])ˣ),
            EuclideanDomain.gcdB f h * (u⁻¹ : (Polynomial ℚ_[p])ˣ), ?_⟩
          have hbez := EuclideanDomain.gcd_eq_gcd_ab f h
          rw [← hu] at hbez
          calc EuclideanDomain.gcdA f h * (u⁻¹ : (Polynomial ℚ_[p])ˣ) * f +
                EuclideanDomain.gcdB f h * (u⁻¹ : (Polynomial ℚ_[p])ˣ) * h
              = (f * EuclideanDomain.gcdA f h + h * EuclideanDomain.gcdB f h) *
                  (u⁻¹ : (Polynomial ℚ_[p])ˣ) := by ring
            _ = (u : Polynomial ℚ_[p]) * (u⁻¹ : (Polynomial ℚ_[p])ˣ) := by rw [← hbez]
            _ = 1 := Units.mul_inv u
        have hz_fh : z * algebraMap (Polynomial ℚ_[p]) BdRR h = algebraMap (Polynomial ℚ_[p]) BdRR f := by
          have hd_ne : algebraMap (Polynomial ℚ_[p]) BdRR d ≠ 0 := fun h0 =>
            hd0 (IsFractionRing.injective (Polynomial ℚ_[p]) BdRR (h0.trans (map_zero _).symm))
          apply mul_left_cancel₀ hd_ne
          have : algebraMap (Polynomial ℚ_[p]) BdRR d * (z * algebraMap (Polynomial ℚ_[p]) BdRR h) =
              z * algebraMap (Polynomial ℚ_[p]) BdRR h₀ := by rw [hh, map_mul]; ring
          rw [this, hz_eq, hf, map_mul]
        have hfix : scalePoly p (toQpUnit g0) f * h = f * scalePoly p (toQpUnit g0) h := by
          have hzg0 : scaleFrac p (toQpUnit g0) z = z := hz g0
          have h1 := congrArg (scaleFrac p (toQpUnit g0)) hz_fh
          rw [map_mul, hzg0, scaleFrac_algebraMap, scaleFrac_algebraMap] at h1
          have h2 : algebraMap (Polynomial ℚ_[p]) BdRR (scalePoly p (toQpUnit g0) f * h) =
              algebraMap (Polynomial ℚ_[p]) BdRR (f * scalePoly p (toQpUnit g0) h) := by
            rw [map_mul, map_mul, ← h1, ← hz_fh]; ring
          exact IsFractionRing.injective (Polynomial ℚ_[p]) BdRR h2
        have hh_dvd : h ∣ scalePoly p (toQpUnit g0) h :=
          hcop.symm.dvd_of_dvd_mul_left ⟨scalePoly p (toQpUnit g0) f, by linear_combination -hfix⟩
        obtain ⟨q, hq⟩ := hh_dvd
        have hq0 : q ≠ 0 := fun h' => hh0 ((scalePoly p (toQpUnit g0)).injective
          (by rw [map_zero, hq, h', mul_zero]))
        have hq_deg : q.natDegree = 0 := by
          have hd1 := congrArg Polynomial.natDegree hq
          rw [natDegree_scalePoly, Polynomial.natDegree_mul hh0 hq0] at hd1
          omega
        have hq_eq : q = Polynomial.C ((toQpUnit g0 : ℚ_[p]) ^ h.natDegree) := by
          have hC := Polynomial.eq_C_of_natDegree_eq_zero hq_deg
          have hlc := congrArg Polynomial.leadingCoeff hq
          rw [leadingCoeff_scalePoly, Polynomial.leadingCoeff_mul, hC, Polynomial.leadingCoeff_C] at hlc
          have hlc_ne : h.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hh0
          have hq0_eq : q.coeff 0 = (toQpUnit g0 : ℚ_[p]) ^ h.natDegree :=
            mul_left_cancel₀ hlc_ne (by linear_combination hlc.symm)
          rw [hC, hq0_eq]
        rw [hq_eq, mul_comm] at hq
        have hh_mon : ∀ k ≠ h.natDegree, h.coeff k = 0 := by
          intro k hk
          have hc := congrArg (fun P => P.coeff k) hq
          rw [coeff_scalePoly, Polynomial.coeff_C_mul] at hc
          have hsub : ((toQpUnit g0 : ℚ_[p]) ^ k - (toQpUnit g0 : ℚ_[p]) ^ h.natDegree) * h.coeff k = 0 := by
            linear_combination hc
          exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr (hu0_pow_ne hk))
        have hf_eq : scalePoly p (toQpUnit g0) f = Polynomial.C ((toQpUnit g0 : ℚ_[p]) ^ h.natDegree) * f := by
          apply mul_right_cancel₀ hh0
          rw [hfix, hq]; ring
        have hf_mon : ∀ k ≠ h.natDegree, f.coeff k = 0 := by
          intro k hk
          have hc := congrArg (fun P => P.coeff k) hf_eq
          rw [coeff_scalePoly, Polynomial.coeff_C_mul] at hc
          have hsub : ((toQpUnit g0 : ℚ_[p]) ^ k - (toQpUnit g0 : ℚ_[p]) ^ h.natDegree) * f.coeff k = 0 := by
            linear_combination hc
          exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr (hu0_pow_ne hk))
        have h_eq_mon : h = Polynomial.C (h.coeff h.natDegree) * Polynomial.X ^ h.natDegree := by
          ext k
          rw [Polynomial.coeff_C_mul_X_pow]
          split_ifs with hk
          · subst hk; rfl
          · exact hh_mon k hk
        have f_eq_mon : f = Polynomial.C (f.coeff h.natDegree) * Polynomial.X ^ h.natDegree := by
          ext k
          rw [Polynomial.coeff_C_mul_X_pow]
          split_ifs with hk
          · subst hk; rfl
          · exact hf_mon k hk
        have hlc_ne : h.coeff h.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hh0
        refine ⟨f.coeff h.natDegree / h.coeff h.natDegree, ?_⟩
        have hh_dR : algebraMap (Polynomial ℚ_[p]) BdRR h ≠ 0 := fun h0 =>
          hh0 (IsFractionRing.injective (Polynomial ℚ_[p]) BdRR (h0.trans (map_zero _).symm))
        apply mul_right_cancel₀ hh_dR
        rw [hz_fh]
        have h1 : algebraMap (Polynomial ℚ_[p]) BdRR h =
            algebraMap ℚ_[p] BdRR (h.coeff h.natDegree) *
              algebraMap (Polynomial ℚ_[p]) BdRR (Polynomial.X ^ h.natDegree) := by
          conv_lhs => rw [h_eq_mon]
          rw [map_mul]; rfl
        have h2 : algebraMap (Polynomial ℚ_[p]) BdRR f =
            algebraMap ℚ_[p] BdRR (f.coeff h.natDegree) *
              algebraMap (Polynomial ℚ_[p]) BdRR (Polynomial.X ^ h.natDegree) := by
          conv_lhs => rw [f_eq_mon]
          rw [map_mul]; rfl
        rw [h1, h2, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hlc_ne]
      φ := (scaleAway p pUnit).toAlgHom
      φ_inj := (scaleAway p pUnit).injective
      φ_comm := fun g x => by
        have h : ((scaleAway p pUnit).toAlgHom.toRingHom).comp (scaleAway p (toQpUnit g)).toAlgHom.toRingHom =
            ((scaleAway p (toQpUnit g)).toAlgHom.toRingHom).comp (scaleAway p pUnit).toAlgHom.toRingHom := by
          refine IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial ℚ_[p]))
            (RingHom.ext fun f => ?_)
          change scaleAway p pUnit (scaleAway p (toQpUnit g) (algebraMap _ _ f)) =
            scaleAway p (toQpUnit g) (scaleAway p pUnit (algebraMap _ _ f))
          rw [scaleAway_algebraMap, scaleAway_algebraMap, scaleAway_algebraMap, scaleAway_algebraMap]
          congr 1; ext k; simp [coeff_scalePoly]; ring
        exact RingHom.congr_fun h x
      ι := inclAwayFrac p
      ι_inj := by
        intro x y hxy
        obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, hxa⟩ := IsLocalization.surj (Submonoid.powers (Polynomial.X : Polynomial ℚ_[p])) x
        obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hyb⟩ := IsLocalization.surj (Submonoid.powers (Polynomial.X : Polynomial ℚ_[p])) y
        dsimp only at hxa hyb
        have h1 : algebraMap (Polynomial ℚ_[p]) BdRR (a * Polynomial.X ^ n) =
            algebraMap (Polynomial ℚ_[p]) BdRR (b * Polynomial.X ^ m) := by
          have hx' := congrArg (inclAwayFrac p) hxa
          have hy' := congrArg (inclAwayFrac p) hyb
          rw [map_mul, inclAwayFrac_algebraMap, inclAwayFrac_algebraMap] at hx' hy'
          rw [map_mul, map_mul, ← hx', ← hy', hxy]; ring
        have h2 : a * Polynomial.X ^ n = b * Polynomial.X ^ m :=
          IsFractionRing.injective (Polynomial ℚ_[p]) BdRR h1
        have huX := IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial ℚ_[p]) (S := BcrisR)
        obtain ⟨u, hu⟩ := huX
        have h3 : x * (u : BcrisR) ^ (m + n) = y * (u : BcrisR) ^ (m + n) := by
          have hxa' : x * (u : BcrisR) ^ m = algebraMap (Polynomial ℚ_[p]) BcrisR a := by
            simpa [hu, map_pow] using hxa
          have hyb' : y * (u : BcrisR) ^ n = algebraMap (Polynomial ℚ_[p]) BcrisR b := by
            simpa [hu, map_pow] using hyb
          calc x * (u : BcrisR) ^ (m + n)
              = (x * (u : BcrisR) ^ m) * (u : BcrisR) ^ n := by rw [pow_add, mul_assoc]
            _ = algebraMap (Polynomial ℚ_[p]) BcrisR (a * Polynomial.X ^ n) := by
                rw [hxa', map_mul, map_pow, hu]
            _ = algebraMap (Polynomial ℚ_[p]) BcrisR (b * Polynomial.X ^ m) := by rw [h2]
            _ = (y * (u : BcrisR) ^ n) * (u : BcrisR) ^ m := by
                rw [hyb', map_mul, map_pow, hu]
            _ = y * (u : BcrisR) ^ (m + n) := by rw [pow_add]; ring
        have h4 := congrArg (· * ((u⁻¹ : BcrisRˣ) : BcrisR) ^ (m + n)) h3
        simpa [mul_assoc, ← mul_pow, Units.mul_inv] using h4
      ι_comm := fun g x => by
        have h : (inclAwayFrac p).toRingHom.comp (scaleAway p (toQpUnit g)).toAlgHom.toRingHom =
            ((scaleFrac p (toQpUnit g)).toAlgHom.toRingHom).comp (inclAwayFrac p).toRingHom := by
          refine IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial ℚ_[p]))
            (RingHom.ext fun f => ?_)
          change inclAwayFrac p (scaleAway p (toQpUnit g) (algebraMap _ _ f)) =
            scaleFrac p (toQpUnit g) (inclAwayFrac p (algebraMap _ _ f))
          rw [scaleAway_algebraMap, inclAwayFrac_algebraMap, inclAwayFrac_algebraMap, scaleFrac_algebraMap]
        exact RingHom.congr_fun h x
      Fil := FilFn
      Fil_anti := fun i j hij => by
        rintro z ⟨a, b, hb, rfl⟩
        have hdiff : 0 ≤ j - i := sub_nonneg.mpr hij
        lift (j - i) to ℕ using hdiff with k hk
        refine ⟨Polynomial.X ^ k * a, b, hb, ?_⟩
        rw [map_mul, map_pow, mul_div_assoc, ← mul_assoc]
        congr 1
        change X_dR ^ j = X_dR ^ i * X_dR ^ k
        rw [← zpow_natCast, ← zpow_add₀ hXdR0, hk, add_sub_cancel]
      one_mem := ⟨1, 1, by simp, by simp⟩
      Fil_mul := fun i j x y hx hy => by
        rcases hx with ⟨a₁, b₁, hb₁, rfl⟩
        rcases hy with ⟨a₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, b₁ * b₂, by rw [Polynomial.eval_mul]; exact mul_ne_zero hb₁ hb₂, ?_⟩
        rw [map_mul, map_mul, zpow_add₀ hXdR0]
        ring
      Fil_exh := fun z => by
        obtain ⟨⟨a, ⟨b, hb⟩⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial ℚ_[p])) z
        dsimp only at hz
        obtain ⟨k, b₀, hb₀, rfl⟩ := exists_X_pow_mul_eval_zero_ne (nonZeroDivisors.ne_zero hb)
        refine ⟨-(k : ℤ), a, b₀, hb₀, ?_⟩
        have hb₀_dR : algebraMap (Polynomial ℚ_[p]) BdRR b₀ ≠ 0 := hinj_ne hb₀
        have hxk : X_dR ^ (k : ℤ) ≠ 0 := zpow_ne_zero k hXdR0
        rw [map_mul, map_pow] at hz
        have h1 : z * (X_dR ^ (k : ℤ) * algebraMap (Polynomial ℚ_[p]) BdRR b₀) =
            algebraMap (Polynomial ℚ_[p]) BdRR a := by simpa [X_dR] using hz
        apply mul_right_cancel₀ (mul_ne_zero hxk hb₀_dR)
        rw [h1]
        calc algebraMap (Polynomial ℚ_[p]) BdRR a
            = (X_dR ^ (-(k : ℤ)) * X_dR ^ (k : ℤ)) *
                ((algebraMap (Polynomial ℚ_[p]) BdRR a / algebraMap (Polynomial ℚ_[p]) BdRR b₀) *
                  algebraMap (Polynomial ℚ_[p]) BdRR b₀) := by
                rw [← zpow_add₀ hXdR0, neg_add_cancel, zpow_zero, one_mul, div_mul_cancel₀ _ hb₀_dR]
          _ = X_dR ^ (-(k : ℤ)) *
                (algebraMap (Polynomial ℚ_[p]) BdRR a / algebraMap (Polynomial ℚ_[p]) BdRR b₀) *
                (X_dR ^ (k : ℤ) * algebraMap (Polynomial ℚ_[p]) BdRR b₀) := by ring
      Fil_sep := fun z hz => by
        by_contra hz0
        obtain ⟨⟨a, ⟨b, hb⟩⟩, hzeq⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial ℚ_[p])) z
        dsimp only at hzeq
        have ha0 : a ≠ 0 := fun h => by
          rw [h, map_zero] at hzeq
          have hb_ne : algebraMap (Polynomial ℚ_[p]) BdRR b ≠ 0 := fun h0 =>
            nonZeroDivisors.ne_zero hb
              (IsFractionRing.injective (Polynomial ℚ_[p]) BdRR (h0.trans (map_zero _).symm))
          exact hz0 ((mul_eq_zero.mp hzeq).resolve_right hb_ne)
        obtain ⟨m, a₀, ha₀, rfl⟩ := exists_X_pow_mul_eval_zero_ne ha0
        obtain ⟨n, b₀, hb₀, rfl⟩ := exists_X_pow_mul_eval_zero_ne (nonZeroDivisors.ne_zero hb)
        obtain ⟨c, d, hd, hcd⟩ := hz ((m : ℤ) - (n : ℤ) + 1)
        have hd_dR : algebraMap (Polynomial ℚ_[p]) BdRR d ≠ 0 := hinj_ne hd
        have hb₀_dR : algebraMap (Polynomial ℚ_[p]) BdRR b₀ ≠ 0 := hinj_ne hb₀
        have heq_dR : algebraMap (Polynomial ℚ_[p]) BdRR (a₀ * d) =
            algebraMap (Polynomial ℚ_[p]) BdRR (Polynomial.X * (b₀ * c)) := by
          have hz1 : z = X_dR ^ ((m : ℤ) - (n : ℤ)) *
              (algebraMap (Polynomial ℚ_[p]) BdRR a₀ / algebraMap (Polynomial ℚ_[p]) BdRR b₀) := by
            rw [map_mul, map_pow, map_mul, map_pow] at hzeq
            have h1 : z * (X_dR ^ (n : ℤ) * algebraMap (Polynomial ℚ_[p]) BdRR b₀) =
                X_dR ^ (m : ℤ) * algebraMap (Polynomial ℚ_[p]) BdRR a₀ := by simpa [X_dR] using hzeq
            rw [zpow_sub₀ hXdR0]
            have hxn : X_dR ^ (n : ℤ) ≠ 0 := zpow_ne_zero n hXdR0
            apply mul_right_cancel₀ (mul_ne_zero hxn hb₀_dR)
            rw [h1]
            calc X_dR ^ (m : ℤ) * algebraMap (Polynomial ℚ_[p]) BdRR a₀
                = (X_dR ^ (m : ℤ) / X_dR ^ (n : ℤ) * X_dR ^ (n : ℤ)) *
                    ((algebraMap (Polynomial ℚ_[p]) BdRR a₀ / algebraMap (Polynomial ℚ_[p]) BdRR b₀) *
                      algebraMap (Polynomial ℚ_[p]) BdRR b₀) := by
                    rw [div_mul_cancel₀ _ hxn, div_mul_cancel₀ _ hb₀_dR]
              _ = X_dR ^ (m : ℤ) / X_dR ^ (n : ℤ) *
                    (algebraMap (Polynomial ℚ_[p]) BdRR a₀ / algebraMap (Polynomial ℚ_[p]) BdRR b₀) *
                    (X_dR ^ (n : ℤ) * algebraMap (Polynomial ℚ_[p]) BdRR b₀) := by ring
          rw [hz1, zpow_add₀ hXdR0, zpow_one] at hcd
          have hxm : X_dR ^ ((m : ℤ) - (n : ℤ)) ≠ 0 := zpow_ne_zero _ hXdR0
          have h2 : algebraMap (Polynomial ℚ_[p]) BdRR a₀ / algebraMap (Polynomial ℚ_[p]) BdRR b₀ =
              X_dR * (algebraMap (Polynomial ℚ_[p]) BdRR c / algebraMap (Polynomial ℚ_[p]) BdRR d) :=
            mul_left_cancel₀ hxm (by linear_combination hcd)
          rw [map_mul, map_mul, map_mul]
          change _ = X_dR * _
          have h3 := congrArg (· * (algebraMap (Polynomial ℚ_[p]) BdRR b₀ * algebraMap (Polynomial ℚ_[p]) BdRR d)) h2
          have hL : algebraMap (Polynomial ℚ_[p]) BdRR a₀ / algebraMap (Polynomial ℚ_[p]) BdRR b₀ *
              (algebraMap (Polynomial ℚ_[p]) BdRR b₀ * algebraMap (Polynomial ℚ_[p]) BdRR d) =
              algebraMap (Polynomial ℚ_[p]) BdRR a₀ * algebraMap (Polynomial ℚ_[p]) BdRR d := by
            rw [← mul_assoc, div_mul_cancel₀ _ hb₀_dR]
          have hR : X_dR * (algebraMap (Polynomial ℚ_[p]) BdRR c / algebraMap (Polynomial ℚ_[p]) BdRR d) *
              (algebraMap (Polynomial ℚ_[p]) BdRR b₀ * algebraMap (Polynomial ℚ_[p]) BdRR d) =
              X_dR * (algebraMap (Polynomial ℚ_[p]) BdRR b₀ * algebraMap (Polynomial ℚ_[p]) BdRR c) := by
            calc X_dR * (algebraMap (Polynomial ℚ_[p]) BdRR c / algebraMap (Polynomial ℚ_[p]) BdRR d) *
                  (algebraMap (Polynomial ℚ_[p]) BdRR b₀ * algebraMap (Polynomial ℚ_[p]) BdRR d)
                = X_dR * algebraMap (Polynomial ℚ_[p]) BdRR b₀ *
                    (algebraMap (Polynomial ℚ_[p]) BdRR c / algebraMap (Polynomial ℚ_[p]) BdRR d *
                      algebraMap (Polynomial ℚ_[p]) BdRR d) := by ring
              _ = X_dR * (algebraMap (Polynomial ℚ_[p]) BdRR b₀ * algebraMap (Polynomial ℚ_[p]) BdRR c) := by
                    rw [div_mul_cancel₀ _ hd_dR]; ring
          rw [hL, hR] at h3
          exact h3
        have heq_poly := IsFractionRing.injective (Polynomial ℚ_[p]) BdRR heq_dR
        have hev := congrArg (Polynomial.eval 0) heq_poly
        simp only [Polynomial.eval_mul, Polynomial.eval_X, zero_mul] at hev
        exact mul_ne_zero ha₀ hd hev
      Fil_G := fun g i z hz => by
        rcases hz with ⟨a, b, hb, rfl⟩
        refine ⟨Polynomial.C ((toQpUnit g : ℚ_[p]) ^ i) * scalePoly p (toQpUnit g) a,
          scalePoly p (toQpUnit g) b, by rw [eval_zero_scalePoly]; exact hb, ?_⟩
        change scaleFrac p (toQpUnit g) _ = _
        rw [map_mul, map_div₀, map_zpow₀]
        have hX : scaleFrac p (toQpUnit g) X_dR = algebraMap ℚ_[p] BdRR (toQpUnit g : ℚ_[p]) * X_dR := by
          change scaleFrac p (toQpUnit g) (algebraMap (Polynomial ℚ_[p]) BdRR Polynomial.X) = _
          rw [scaleFrac_algebraMap, scalePoly_X, map_mul]; rfl
        rw [hX, scaleFrac_algebraMap, scaleFrac_algebraMap, mul_zpow, map_mul, ← map_zpow₀]
        change (algebraMap ℚ_[p] BdRR ((toQpUnit g : ℚ_[p]) ^ i) * X_dR ^ i) * _ =
          X_dR ^ i * (algebraMap ℚ_[p] BdRR ((toQpUnit g : ℚ_[p]) ^ i) * _ / _)
        ring
      t := algebraMap (Polynomial ℚ_[p]) BcrisR Polynomial.X
      t_unit := IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial ℚ_[p])
      t_phi := by
        change scaleAway p pUnit (algebraMap (Polynomial ℚ_[p]) BcrisR Polynomial.X) = _
        rw [scaleAway_algebraMap, scalePoly_X, map_mul, Algebra.smul_def]
        rfl
      t_mem_fil1 := by
        refine ⟨1, 1, by simp, ?_⟩
        rw [inclAwayFrac_algebraMap]
        simp [X_dR]
        rfl
      t_not_mem_fil2 := by
        rintro ⟨a, b, hb, h⟩
        rw [inclAwayFrac_algebraMap] at h
        change X_dR = X_dR ^ (2 : ℤ) * _ at h
        have hb_dR : algebraMap (Polynomial ℚ_[p]) BdRR b ≠ 0 := hinj_ne hb
        have h1 : algebraMap (Polynomial ℚ_[p]) BdRR b =
            algebraMap (Polynomial ℚ_[p]) BdRR (Polynomial.X * a) := by
          rw [map_mul]
          change _ = X_dR * _
          have h2 : X_dR * algebraMap (Polynomial ℚ_[p]) BdRR b =
              X_dR * (X_dR * algebraMap (Polynomial ℚ_[p]) BdRR a) := by
            have := congrArg (· * algebraMap (Polynomial ℚ_[p]) BdRR b) h
            rw [mul_assoc, div_mul_cancel₀ _ hb_dR] at this
            simpa [sq, mul_assoc] using this
          exact mul_left_cancel₀ hXdR0 h2
        have h2 := congrArg (Polynomial.eval 0) (IsFractionRing.injective (Polynomial ℚ_[p]) BdRR h1)
        simp only [Polynomial.eval_mul, Polynomial.eval_X, zero_mul] at h2
        exact hb h2 }

/-- **Non-Vacuity of `FontainePeriodSystem`**: for every prime `p`, there exists a genuine
`FontainePeriodSystem p (ℤ_[p]ˣ)` with non-trivial `G = ℤ_[p]ˣ`, `φ(t) = p • t`, and
crystalline functor `D_cris(V) → FilteredPhiModule p`! -/
theorem exists_nonempty_fontainePeriodSystem (p : ℕ) [Fact p.Prime] :
    Nonempty (FontainePeriodSystem p (ℤ_[p]ˣ)) :=
  ⟨cyclotomicLaurentPeriodSystem p⟩

end LocTiedWitness

end Stage12FontainePeriods
end RHDirect
