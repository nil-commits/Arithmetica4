/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dwork Rationality campaign, Wave 1: the algebraic rationality criterion

A power series over a field is rational iff its coefficients satisfy a linear recurrence
eventually. This is the algebraic engine underlying the Borel–Dwork rationality criterion
(Dwork's proof of Weil Conjecture I): p-adic meromorphicity produces such a recurrence, and
integrality + archimedean growth then force rationality.

Stated entirely on Mathlib's native `PowerSeries` / `Polynomial`.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

noncomputable section

namespace RHDirect.DworkRat

open PowerSeries Finset

variable {K : Type*} [Field K]

/-- A power series is **rational** if it is a quotient of polynomials: `Q · f = P` with `Q ≠ 0`. -/
def IsRationalPS (f : PowerSeries K) : Prop :=
  ∃ (P Q : Polynomial K), Q ≠ 0 ∧ (Q : PowerSeries K) * f = (P : PowerSeries K)

/-- The coefficients of `f` satisfy a **linear recurrence eventually**. -/
def HasRecurrencePS (f : PowerSeries K) : Prop :=
  ∃ (d : ℕ) (q : ℕ → K) (N : ℕ), d ≤ N ∧ (∃ i ≤ d, q i ≠ 0) ∧
    (∀ i > d, q i = 0) ∧ ∀ n ≥ N, ∑ i ∈ range (d + 1), q i * coeff (n - i) f = 0

/-! ### Antidiagonal / range sum conversion -/

private lemma antidiagonal_sum_eq_range_sum {β : Type*} [AddCommMonoid β] (n : ℕ)
    (f : ℕ → ℕ → β) :
    ∑ p ∈ Finset.antidiagonal n, f p.1 p.2 = ∑ i ∈ range (n + 1), f i (n - i) := by
  classical
  apply Eq.symm
  apply Finset.sum_bij (fun (i : ℕ) (_ : i ∈ range (n + 1)) => (i, n - i))
  · intro i hi
    rw [Finset.mem_antidiagonal]
    have : i ≤ n := by simp only [mem_range] at hi; omega
    omega
  · intro i₁ hi₁ i₂ hi₂ h
    simpa using congrArg Prod.fst h
  · intro p hp
    rw [Finset.mem_antidiagonal] at hp
    refine ⟨p.1, ?_, ?_⟩
    · simp only [mem_range]; omega
    · have h2 : n - p.1 = p.2 := by omega
      simp [h2]
  · intro i hi
    rfl

/-! ### Coefficient of a polynomial-times-power-series product -/

lemma coeff_mul_eq_recurrence_sum {f : PowerSeries K} {Q : Polynomial K} {n : ℕ}
    (hn : Q.natDegree ≤ n) :
    coeff n ((Q : PowerSeries K) * f) =
      ∑ i ∈ range (Q.natDegree + 1), Q.coeff i * coeff (n - i) f := by
  rw [PowerSeries.coeff_mul]
  rw [antidiagonal_sum_eq_range_sum (f := fun i j => coeff i (Q : PowerSeries K) * coeff j f)]
  have hcoeff : ∀ i, coeff i (Q : PowerSeries K) = Q.coeff i := by intro i; simp
  simp_rw [hcoeff]
  have hsub : range (Q.natDegree + 1) ⊆ range (n + 1) := by
    intro x hx; simp only [mem_range] at hx ⊢; omega
  rw [← Finset.sum_subset hsub]
  intro i hi hni
  simp only [mem_range] at hi hni
  have : Q.natDegree < i := by omega
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt this]
  simp

/-- Extending a coefficient sum beyond the natural degree does not change it. -/
lemma sum_coeff_range_extend {Q : Polynomial K} {d : ℕ} (hd : Q.natDegree ≤ d)
    (g : ℕ → K) :
    ∑ i ∈ range (Q.natDegree + 1), Q.coeff i * g i =
      ∑ i ∈ range (d + 1), Q.coeff i * g i := by
  have hsub : range (Q.natDegree + 1) ⊆ range (d + 1) := by
    intro x hx; simp only [mem_range] at hx ⊢; omega
  rw [← Finset.sum_subset hsub]
  intro i hi hni
  simp only [mem_range] at hi hni
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  simp

/-! ### Coefficient of a coerced polynomial -/

lemma coeff_coe_poly (p : Polynomial K) (n : ℕ) : coeff n (p : PowerSeries K) = p.coeff n := by
  change coeff n (PowerSeries.mk (fun i => p.coeff i)) = p.coeff n
  exact PowerSeries.coeff_mk n _

lemma coeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial K) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  simp

/-! ### A power series with vanishing high coefficients is a polynomial -/

theorem isPolynomial_of_coeff_eq_zero {f : PowerSeries K} {N : ℕ}
    (h : ∀ n ≥ N, coeff n f = 0) :
    ∃ P : Polynomial K, (P : PowerSeries K) = f := by
  use ∑ n ∈ range N, Polynomial.monomial n (coeff n f)
  ext n
  rw [coeff_coe_poly]
  rw [coeff_finset_sum]
  simp only [Polynomial.coeff_monomial]
  by_cases hn : n < N
  · rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hn)]
  · rw [Finset.sum_ite_eq', if_neg (by simpa [Finset.mem_range] using hn)]
    exact (h n (by omega)).symm

/-! ### Recurrence ⇒ rational -/

theorem rational_of_recurrence {f : PowerSeries K} (h : HasRecurrencePS f) :
    IsRationalPS f := by
  obtain ⟨d, q, N, hdN, hqne, hqsupp, hrec⟩ := h
  let Q : Polynomial K := ∑ i ∈ range (d + 1), Polynomial.monomial i (q i)
  have hQcoeff : ∀ i, Q.coeff i = if i ≤ d then q i else 0 := by
    intro i
    dsimp only [Q]
    rw [coeff_finset_sum]
    simp only [Polynomial.coeff_monomial]
    by_cases hid : i ≤ d
    · have hi : i ∈ range (d + 1) := by simp only [mem_range]; omega
      rw [Finset.sum_ite_eq', if_pos hi, if_pos hid]
    · rw [if_neg hid]
      apply Finset.sum_eq_zero; intro j hj
      exact if_neg (by simp only [mem_range] at hj; omega)
  have hQne : Q ≠ 0 := by
    obtain ⟨i, hid, hi⟩ := hqne
    intro hQ
    have hc := congrArg (fun P => P.coeff i) hQ
    rw [hQcoeff, if_pos hid] at hc
    simp at hc
    exact hi hc
  have hQdeg : Q.natDegree ≤ d := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [hQcoeff, if_neg (by omega)]
  have hQq : ∀ i ≤ d, Q.coeff i = q i := by
    intro i hi; rw [hQcoeff, if_pos hi]
  have hQf : ∀ n ≥ N, coeff n ((Q : PowerSeries K) * f) = 0 := by
    intro n hn
    have hnd : Q.natDegree ≤ n := le_trans hQdeg (le_trans hdN hn)
    rw [coeff_mul_eq_recurrence_sum hnd]
    -- extend the sum to range(d+1), replacing Q.coeff by q
    have heq : (∑ i ∈ range (Q.natDegree + 1), Q.coeff i * coeff (n - i) f) =
        ∑ i ∈ range (d + 1), q i * coeff (n - i) f := by
      rw [sum_coeff_range_extend hQdeg (fun i => coeff (n - i) f)]
      apply Finset.sum_congr rfl; intro i hi
      simp only [mem_range] at hi
      rw [hQq i (by omega)]
    rw [heq]
    exact hrec n hn
  obtain ⟨P, hP⟩ := isPolynomial_of_coeff_eq_zero hQf
  exact ⟨P, Q, hQne, by rw [hP]⟩

/-! ### Rational ⇒ recurrence -/

theorem recurrence_of_rational {f : PowerSeries K} (h : IsRationalPS f) :
    HasRecurrencePS f := by
  obtain ⟨P, Q, hQne, hQf⟩ := h
  refine ⟨Q.natDegree, Q.coeff, max Q.natDegree (P.natDegree + 1),
    le_max_left _ _, ?_, ?_, ?_⟩
  · refine ⟨Q.natDegree, le_rfl, ?_⟩
    exact Polynomial.leadingCoeff_ne_zero.mpr hQne
  · intro i hi
    exact Polynomial.coeff_eq_zero_of_natDegree_lt hi
  · intro n hn
    have hnd : Q.natDegree ≤ n := le_trans (le_max_left _ _) hn
    have hPn : P.natDegree < n := by
      have : P.natDegree + 1 ≤ n := le_trans (le_max_right _ _) hn
      omega
    have hcoeff : coeff n ((Q : PowerSeries K) * f) = coeff n (P : PowerSeries K) := by
      rw [hQf]
    rw [coeff_mul_eq_recurrence_sum hnd] at hcoeff
    have hPcoeff : coeff n (P : PowerSeries K) = 0 := by
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt hPn]
    rw [hPcoeff] at hcoeff
    exact hcoeff

/-- **Algebraic rationality criterion.** A power series over a field is rational iff its
coefficients satisfy a linear recurrence eventually. -/
theorem rational_iff_recurrence {f : PowerSeries K} :
    IsRationalPS f ↔ HasRecurrencePS f :=
  ⟨recurrence_of_rational, rational_of_recurrence⟩

end RHDirect.DworkRat
