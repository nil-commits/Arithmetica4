import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Finset.Interval
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Arith4Ext.AnalyticNT — Elementary & Explicit Analytic Number Theory Engine

Reusable, 100%-unconditional (`0` assumptions, `0` proxies, `0` `sorry`, `0` custom axioms)
Tier A analytic number theory library on targeted Mathlib imports (`namespace Arith4Ext.AnalyticNT`):

1. **Abel / Partial Summation Identities & Bounds** over `Finset.Icc a b` for `ℝ`, `ℂ`, and general rings,
   plus continuous-integral Abel summation.
2. **Dirichlet Hyperbola Method & Divisor-Moment Upper Bounds**: general convolution hyperbola
   identity, `d(n)` `sqrt` identity, harmonic `log` bounds, explicit `|∑ d(n) - N log N| ≤ N + 2√N`,
   and general `k`-th divisor moment upper bounds `∑ d(n)^k ≤ N (log N + 1)^(2^k - 1)`.
3. **Weyl Differencing & Van der Corput `A`-Process** (Section 3).
4. **Dirichlet & Fejér Kernel Exact Identities & Positivity / `L¹` Bounds** (Section 4).
5. **Explicit Elementary Chebyshev & Prime-Harmonic Bounds** (Section 5).
-/

open Real Complex Finset MeasureTheory intervalIntegral
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace Arith4Ext.AnalyticNT

noncomputable section

/-! ## Section 1: Abel / Partial Summation Identities & Bounds -/

/-- Discrete Abel summation by parts over `Finset.Icc a b` in any commutative ring `R`. -/
theorem abel_summation_Icc {R : Type*} [CommRing R] (f g : ℕ → R) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Icc a b, f n * g n =
      (∑ k ∈ Finset.Icc a b, f k) * g b -
        ∑ n ∈ Finset.Ico a b, (∑ k ∈ Finset.Icc a n, f k) * (g (n + 1) - g n) := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp
  | succ b hab ih =>
    have hIcc : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hnotIcc : b + 1 ∉ Finset.Icc a b := by
      simp only [Finset.mem_Icc]
      omega
    have hIco : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Ico]
      omega
    have hnotIco : b ∉ Finset.Ico a b := by
      simp only [Finset.mem_Ico]
      omega
    rw [hIcc, Finset.sum_insert hnotIcc, ih, Finset.sum_insert hnotIcc,
      hIco, Finset.sum_insert hnotIco]
    ring

/-- Shifted discrete Abel summation by parts over `Finset.Icc a b` (valid for all `a, b : ℕ`). -/
theorem abel_summation_Icc_shifted {R : Type*} [CommRing R] (f g : ℕ → R) (a b : ℕ) :
    ∑ n ∈ Finset.Icc a b, f n * g n =
      (∑ k ∈ Finset.Icc a b, f k) * g (b + 1) -
        ∑ n ∈ Finset.Icc a b, (∑ k ∈ Finset.Icc a n, f k) * (g (n + 1) - g n) := by
  by_cases hab : a ≤ b
  · have hIcc : Finset.Icc a b = insert b (Finset.Ico a b) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Ico]
      omega
    have hnotIco : b ∉ Finset.Ico a b := by
      simp only [Finset.mem_Ico]
      omega
    have hsub :
        ∑ n ∈ Finset.Icc a b, (∑ k ∈ Finset.Icc a n, f k) * (g (n + 1) - g n) =
          (∑ n ∈ Finset.Ico a b, (∑ k ∈ Finset.Icc a n, f k) * (g (n + 1) - g n)) +
            (∑ k ∈ Finset.Icc a b, f k) * (g (b + 1) - g b) := by
      conv_lhs => rw [hIcc, Finset.sum_insert hnotIco]
      ring
    rw [abel_summation_Icc f g hab, hsub]
    ring
  · have hEmpty : Finset.Icc a b = ∅ := Finset.Icc_eq_empty hab
    simp [hEmpty]

/-- General norm bound from Abel summation over `Finset.Icc a b` in any normed commutative ring. -/
theorem norm_sum_mul_le_abel_ring {R : Type*} [NormedCommRing R] (f g : ℕ → R)
    {a b : ℕ} (hab : a ≤ b) {M : ℝ} (_hM : 0 ≤ M)
    (hf : ∀ n ∈ Finset.Icc a b, ‖∑ k ∈ Finset.Icc a n, f k‖ ≤ M) :
    ‖∑ n ∈ Finset.Icc a b, f n * g n‖ ≤
      M * (‖g b‖ + ∑ n ∈ Finset.Ico a b, ‖g (n + 1) - g n‖) := by
  rw [abel_summation_Icc f g hab]
  have h1 : ‖(∑ k ∈ Finset.Icc a b, f k) * g b‖ ≤ M * ‖g b‖ :=
    (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hf b (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩)) (norm_nonneg _))
  have h2 :
      ‖∑ n ∈ Finset.Ico a b, (∑ k ∈ Finset.Icc a n, f k) * (g (n + 1) - g n)‖ ≤
        ∑ n ∈ Finset.Ico a b, M * ‖g (n + 1) - g n‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    have hnIcc : n ∈ Finset.Icc a b := by
      simp only [Finset.mem_Ico] at hn
      exact Finset.mem_Icc.mpr ⟨hn.1, hn.2.le⟩
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hf n hnIcc) (norm_nonneg _))
  calc
    ‖(∑ k ∈ Finset.Icc a b, f k) * g b -
        ∑ n ∈ Finset.Ico a b, (∑ k ∈ Finset.Icc a n, f k) * (g (n + 1) - g n)‖
      ≤ ‖(∑ k ∈ Finset.Icc a b, f k) * g b‖ +
          ‖∑ n ∈ Finset.Ico a b, (∑ k ∈ Finset.Icc a n, f k) * (g (n + 1) - g n)‖ :=
        norm_sub_le _ _
    _ ≤ M * ‖g b‖ + ∑ n ∈ Finset.Ico a b, M * ‖g (n + 1) - g n‖ := add_le_add h1 h2
    _ = M * (‖g b‖ + ∑ n ∈ Finset.Ico a b, ‖g (n + 1) - g n‖) := by
        rw [← Finset.mul_sum, ← mul_add]

/-- Complex specialization of Abel summation norm bound. -/
theorem norm_sum_mul_le_abel (f g : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ n ∈ Finset.Icc a b, ‖∑ k ∈ Finset.Icc a n, f k‖ ≤ M) :
    ‖∑ n ∈ Finset.Icc a b, f n * g n‖ ≤
      M * (‖g b‖ + ∑ n ∈ Finset.Ico a b, ‖g (n + 1) - g n‖) :=
  norm_sum_mul_le_abel_ring f g hab hM hf

/-- Real specialization of Abel summation absolute-value bound. -/
theorem abs_sum_mul_le_abel (f g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ n ∈ Finset.Icc a b, |∑ k ∈ Finset.Icc a n, f k| ≤ M) :
    |∑ n ∈ Finset.Icc a b, f n * g n| ≤
      M * (|g b| + ∑ n ∈ Finset.Ico a b, |g (n + 1) - g n|) := by
  simpa only [Real.norm_eq_abs] using norm_sum_mul_le_abel_ring f g hab hM hf

private lemma sum_Ico_sub_telescope (g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (g n - g (n + 1)) = g a - g b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hIco : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Ico]
      omega
    have hnot : b ∉ Finset.Ico a b := by simp
    rw [hIco, Finset.sum_insert hnot, ih]
    ring

/-- Abel summation bound for complex sequences with nonnegative antitone real weights `g`:
`‖∑_{n=a}^b f(n) g(n)‖ ≤ M · g(a)`. -/
theorem norm_sum_mul_le_abel_antitone (f : ℕ → ℂ) (g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ n ∈ Finset.Icc a b, ‖∑ k ∈ Finset.Icc a n, f k‖ ≤ M)
    (hg_nonneg : 0 ≤ g b)
    (hg_anti : ∀ n ∈ Finset.Ico a b, g (n + 1) ≤ g n) :
    ‖∑ n ∈ Finset.Icc a b, f n * (g n : ℂ)‖ ≤ M * g a := by
  have h := norm_sum_mul_le_abel f (fun n => (g n : ℂ)) hab hM hf
  have hgb : ‖(g b : ℂ)‖ = g b := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg_nonneg]
  have hdiff : ∑ n ∈ Finset.Ico a b, ‖(g (n + 1) : ℂ) - (g n : ℂ)‖ = g a - g b := by
    rw [← sum_Ico_sub_telescope g hab]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (hg_anti n hn))]
  rw [hgb, hdiff, add_sub_cancel] at h
  exact h

/-- Abel summation bound for real sequences with nonnegative antitone weights `g`:
`|∑_{n=a}^b f(n) g(n)| ≤ M · g(a)`. -/
theorem abs_sum_mul_le_abel_antitone (f g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ n ∈ Finset.Icc a b, |∑ k ∈ Finset.Icc a n, f k| ≤ M)
    (hg_nonneg : 0 ≤ g b)
    (hg_anti : ∀ n ∈ Finset.Ico a b, g (n + 1) ≤ g n) :
    |∑ n ∈ Finset.Icc a b, f n * g n| ≤ M * g a := by
  have h := abs_sum_mul_le_abel f g hab hM hf
  have hgb : |g b| = g b := abs_of_nonneg hg_nonneg
  have hdiff : ∑ n ∈ Finset.Ico a b, |g (n + 1) - g n| = g a - g b := by
    rw [← sum_Ico_sub_telescope g hab]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hg_anti n hn))]
  rw [hgb, hdiff, add_sub_cancel] at h
  exact h

/-- Abel summation bound for complex sequences with nonnegative monotone increasing weights `g`:
`‖∑_{n=a}^b f(n) g(n)‖ ≤ M · (2 g(b) - g(a))`. -/
theorem norm_sum_mul_le_abel_monotone (f : ℕ → ℂ) (g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ n ∈ Finset.Icc a b, ‖∑ k ∈ Finset.Icc a n, f k‖ ≤ M)
    (hg_nonneg : 0 ≤ g a)
    (hg_mono : ∀ n ∈ Finset.Ico a b, g n ≤ g (n + 1)) :
    ‖∑ n ∈ Finset.Icc a b, f n * (g n : ℂ)‖ ≤ M * (2 * g b - g a) := by
  have hgb_nonneg : 0 ≤ g b := by
    have htel := sum_Ico_sub_telescope g hab
    have hle : ∑ n ∈ Finset.Ico a b, (g n - g (n + 1)) ≤ 0 :=
      Finset.sum_nonpos fun n hn => sub_nonpos.mpr (hg_mono n hn)
    linarith
  have h := norm_sum_mul_le_abel f (fun n => (g n : ℂ)) hab hM hf
  have hgb : ‖(g b : ℂ)‖ = g b := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgb_nonneg]
  have hdiff : ∑ n ∈ Finset.Ico a b, ‖(g (n + 1) : ℂ) - (g n : ℂ)‖ = g b - g a := by
    have htel := sum_Ico_sub_telescope g hab
    have hneg : ∑ n ∈ Finset.Ico a b, (g (n + 1) - g n) = g b - g a := by
      calc
        ∑ n ∈ Finset.Ico a b, (g (n + 1) - g n)
          = -∑ n ∈ Finset.Ico a b, (g n - g (n + 1)) := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun n _ => by ring
        _ = g b - g a := by rw [htel]; ring
    rw [← hneg]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (hg_mono n hn))]
  rw [hgb, hdiff] at h
  linarith

/-- Continuous-integral Abel summation over `[a, b]` for real sequences:
`∑_{n=a}^b f(n) · φ(n) = (∑_{k=a}^b f(k)) · φ(b) - ∫_a^b (∑_{k=a}^{⌊t⌋₊} f(k)) · φ'(t) dt`. -/
theorem abel_summation_integral_Icc_real (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    {φ φ' : ℝ → ℝ}
    (hd : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.Icc (a : ℝ) (b : ℝ))) :
    (∑ n ∈ Finset.Icc a b, f n * φ n =
        (∑ k ∈ Finset.Icc a b, f k) * φ b -
          ∫ t in (a : ℝ)..(b : ℝ), (∑ k ∈ Finset.Icc a ⌊t⌋₊, f k) * φ' t) ∧
      IntervalIntegrable (fun t : ℝ => (∑ k ∈ Finset.Icc a ⌊t⌋₊, f k) * φ' t)
        volume (a : ℝ) (b : ℝ) := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp [IntervalIntegrable.refl]
  | succ b hab ih =>
    have hab_real : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have hb_real : (b : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hsub_ab : Set.Icc (a : ℝ) (b : ℝ) ⊆ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
      Set.Icc_subset_Icc_right hb_real
    have hsub_b : Set.Icc (b : ℝ) ((b + 1 : ℕ) : ℝ) ⊆ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
      Set.Icc_subset_Icc_left hab_real
    obtain ⟨ih_eq, ih_int⟩ := ih (fun t ht => hd t (hsub_ab ht)) (hc.mono hsub_ab)
    set S : ℕ → ℝ := fun n => ∑ k ∈ Finset.Icc a n, f k
    have hc_b : ContinuousOn φ' (Set.uIcc (b : ℝ) ((b + 1 : ℕ) : ℝ)) := by
      rw [Set.uIcc_of_le hb_real]
      exact hc.mono hsub_b
    have hd_b : ∀ t ∈ Set.uIcc (b : ℝ) ((b + 1 : ℕ) : ℝ), HasDerivAt φ (φ' t) t := by
      intro t ht
      rw [Set.uIcc_of_le hb_real] at ht
      exact hd t (hsub_b ht)
    have hint_const : IntervalIntegrable (fun t => S b * φ' t) volume (b : ℝ) ((b + 1 : ℕ) : ℝ) :=
      hc_b.intervalIntegrable.const_mul _
    have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (b : ℝ) ((b + 1 : ℕ) : ℝ) →
        S ⌊t⌋₊ * φ' t = S b * φ' t := by
      have hne : ∀ᵐ t ∂volume, t ≠ ((b + 1 : ℕ) : ℝ) := by rw [ae_iff]; simp
      filter_upwards [hne] with t htne htmem
      rw [Set.uIoc_of_le hb_real, Set.mem_Ioc] at htmem
      have hfl : ⌊t⌋₊ = b := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg b) htmem.1.le)).mpr
        ⟨htmem.1.le, by exact_mod_cast lt_of_le_of_ne htmem.2 htne⟩
      rw [hfl]
    have hint_b : IntervalIntegrable (fun t => S ⌊t⌋₊ * φ' t) volume (b : ℝ) ((b + 1 : ℕ) : ℝ) := by
      refine hint_const.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr ?_)
      filter_upwards [hae] with t ht htmem
      exact (ht htmem).symm
    have hint_full : IntervalIntegrable (fun t => S ⌊t⌋₊ * φ' t) volume (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
      ih_int.trans hint_b
    have hsplit : ∫ t in (a : ℝ)..((b + 1 : ℕ) : ℝ), S ⌊t⌋₊ * φ' t =
        (∫ t in (a : ℝ)..(b : ℝ), S ⌊t⌋₊ * φ' t) +
          ∫ t in (b : ℝ)..((b + 1 : ℕ) : ℝ), S ⌊t⌋₊ * φ' t :=
      (intervalIntegral.integral_add_adjacent_intervals ih_int hint_b).symm
    have hint_step : ∫ t in (b : ℝ)..((b + 1 : ℕ) : ℝ), S ⌊t⌋₊ * φ' t =
        S b * (φ ((b + 1 : ℕ) : ℝ) - φ (b : ℝ)) := by
      rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_eq_sub_of_hasDerivAt hd_b hc_b.intervalIntegrable]
    have hIcc : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hnot : b + 1 ∉ Finset.Icc a b := by
      simp only [Finset.mem_Icc]
      omega
    refine ⟨?_, hint_full⟩
    rw [hIcc, Finset.sum_insert hnot, ih_eq]
    have hS : ∑ k ∈ insert (b + 1) (Finset.Icc a b), f k = S b + f (b + 1) := by
      rw [Finset.sum_insert hnot]
      dsimp only [S]
      ring
    rw [hS, hsplit, hint_step]
    push_cast
    ring

/-- Complex continuous-integral Abel summation over `[a, b]`:
`∑_{n=a}^b f(n) φ(n) = (∑_{k=a}^b f(k)) φ(b) - ∫_a^b (∑_{k=a}^{⌊t⌋₊} f(k)) φ'(t) dt`. -/
theorem abel_summation_integral_Icc_complex (f : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b)
    {φ φ' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.Icc (a : ℝ) (b : ℝ))) :
    (∑ n ∈ Finset.Icc a b, f n * φ n =
        (∑ k ∈ Finset.Icc a b, f k) * φ b -
          ∫ t in (a : ℝ)..(b : ℝ), (∑ k ∈ Finset.Icc a ⌊t⌋₊, f k) * φ' t) ∧
      IntervalIntegrable (fun t : ℝ => (∑ k ∈ Finset.Icc a ⌊t⌋₊, f k) * φ' t)
        volume (a : ℝ) (b : ℝ) := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp [IntervalIntegrable.refl]
  | succ b hab ih =>
    have hab_real : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have hb_real : (b : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hsub_ab : Set.Icc (a : ℝ) (b : ℝ) ⊆ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
      Set.Icc_subset_Icc_right hb_real
    have hsub_b : Set.Icc (b : ℝ) ((b + 1 : ℕ) : ℝ) ⊆ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
      Set.Icc_subset_Icc_left hab_real
    obtain ⟨ih_eq, ih_int⟩ := ih (fun t ht => hd t (hsub_ab ht)) (hc.mono hsub_ab)
    set S : ℕ → ℂ := fun n => ∑ k ∈ Finset.Icc a n, f k
    have hc_b : ContinuousOn φ' (Set.uIcc (b : ℝ) ((b + 1 : ℕ) : ℝ)) := by
      rw [Set.uIcc_of_le hb_real]
      exact hc.mono hsub_b
    have hd_b : ∀ t ∈ Set.uIcc (b : ℝ) ((b + 1 : ℕ) : ℝ), HasDerivAt φ (φ' t) t := by
      intro t ht
      rw [Set.uIcc_of_le hb_real] at ht
      exact hd t (hsub_b ht)
    have hint_const : IntervalIntegrable (fun t => S b * φ' t) volume (b : ℝ) ((b + 1 : ℕ) : ℝ) :=
      hc_b.intervalIntegrable.const_mul _
    have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (b : ℝ) ((b + 1 : ℕ) : ℝ) →
        S ⌊t⌋₊ * φ' t = S b * φ' t := by
      have hne : ∀ᵐ t ∂volume, t ≠ ((b + 1 : ℕ) : ℝ) := by rw [ae_iff]; simp
      filter_upwards [hne] with t htne htmem
      rw [Set.uIoc_of_le hb_real, Set.mem_Ioc] at htmem
      have hfl : ⌊t⌋₊ = b := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg b) htmem.1.le)).mpr
        ⟨htmem.1.le, by exact_mod_cast lt_of_le_of_ne htmem.2 htne⟩
      rw [hfl]
    have hint_b : IntervalIntegrable (fun t => S ⌊t⌋₊ * φ' t) volume (b : ℝ) ((b + 1 : ℕ) : ℝ) := by
      refine hint_const.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr ?_)
      filter_upwards [hae] with t ht htmem
      exact (ht htmem).symm
    have hint_full : IntervalIntegrable (fun t => S ⌊t⌋₊ * φ' t) volume (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
      ih_int.trans hint_b
    have hsplit : ∫ t in (a : ℝ)..((b + 1 : ℕ) : ℝ), S ⌊t⌋₊ * φ' t =
        (∫ t in (a : ℝ)..(b : ℝ), S ⌊t⌋₊ * φ' t) +
          ∫ t in (b : ℝ)..((b + 1 : ℕ) : ℝ), S ⌊t⌋₊ * φ' t :=
      (intervalIntegral.integral_add_adjacent_intervals ih_int hint_b).symm
    have hint_step : ∫ t in (b : ℝ)..((b + 1 : ℕ) : ℝ), S ⌊t⌋₊ * φ' t =
        S b * (φ ((b + 1 : ℕ) : ℝ) - φ (b : ℝ)) := by
      rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_eq_sub_of_hasDerivAt hd_b hc_b.intervalIntegrable]
    have hIcc : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hnot : b + 1 ∉ Finset.Icc a b := by
      simp only [Finset.mem_Icc]
      omega
    refine ⟨?_, hint_full⟩
    rw [hIcc, Finset.sum_insert hnot, ih_eq]
    have hS : ∑ k ∈ insert (b + 1) (Finset.Icc a b), f k = S b + f (b + 1) := by
      rw [Finset.sum_insert hnot]
      dsimp only [S]
      ring
    rw [hS, hsplit, hint_step]
    push_cast
    ring

/-! ## Section 2: Dirichlet Hyperbola Method & Divisor-Moment Upper Bounds -/

/-- Exact equivalence between divisor sums over `1 ≤ n ≤ N` and lattice points `1 ≤ a, b`,
`a * b ≤ N`. -/
theorem sum_divisors_mul_eq_sum_filter {R : Type*} [AddCommMonoid R]
    (f : ℕ → ℕ → R) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Nat.divisors n, f d (n / d) =
      ∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N), f p.1 p.2 := by
  have hsig : ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Nat.divisors n, f d (n / d) =
      ∑ x ∈ (Finset.Icc 1 N).sigma (fun n => Nat.divisors n), f x.2 (x.1 / x.2) :=
    Finset.sum_sigma' (Finset.Icc 1 N) (fun n => Nat.divisors n)
      (fun n d => f d (n / d))
  rw [hsig]
  refine Finset.sum_bij'
    (fun x _ => (x.2, x.1 / x.2))
    (fun p _ => ⟨p.1 * p.2, p.1⟩)
    (fun x hx => ?_)
    (fun p hp => ?_)
    (fun x hx => ?_)
    (fun p hp => ?_)
    (fun x _ => rfl)
  · simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
    rcases hx with ⟨⟨hx1, hxN⟩, ⟨hdn, _⟩⟩
    have hd_pos : 0 < x.2 := Nat.pos_of_dvd_of_pos hdn hx1
    have hq_pos : 0 < x.1 / x.2 := Nat.div_pos (Nat.le_of_dvd hx1 hdn) hd_pos
    have hmul : x.2 * (x.1 / x.2) = x.1 := Nat.mul_div_cancel' hdn
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨hd_pos, le_trans (Nat.le_of_dvd hx1 hdn) hxN⟩,
      ⟨hq_pos, le_trans (Nat.div_le_self x.1 x.2) hxN⟩⟩, ?_⟩
    rw [hmul]
    exact hxN
  · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    rcases hp with ⟨⟨⟨ha1, _⟩, ⟨hb1, _⟩⟩, habN⟩
    have hab_pos : 0 < p.1 * p.2 := Nat.mul_pos ha1 hb1
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
    exact ⟨⟨hab_pos, habN⟩, ⟨dvd_mul_right p.1 p.2, hab_pos.ne'⟩⟩
  · simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
    ext
    · exact Nat.mul_div_cancel' hx.2.1
    · rfl
  · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    ext
    · rfl
    · exact Nat.mul_div_cancel_left p.2 hp.1.1.1

private lemma sum_biUnion_Icc_div_eq {R : Type*} [CommRing R] (N M : ℕ) (f g : ℕ → R) :
    ∑ p ∈ (Finset.Icc 1 M).biUnion
        (fun a => (Finset.Icc 1 (N / a)).map
          ⟨fun b => (a, b), fun _b₁ _b₂ h => (Prod.mk.inj h).2⟩), f p.1 * g p.2 =
      ∑ a ∈ Finset.Icc 1 M, f a * ∑ b ∈ Finset.Icc 1 (N / a), g b := by
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_map, Finset.mul_sum]
    rfl
  · intro a₁ _ a₂ _ hne
    exact Finset.disjoint_left.mpr fun p hp₁ hp₂ => by
      rcases Finset.mem_map.mp hp₁ with ⟨_b₁, _, hb₁⟩
      rcases Finset.mem_map.mp hp₂ with ⟨_b₂, _, hb₂⟩
      exact hne (congrArg Prod.fst (hb₁.trans hb₂.symm))

private lemma sum_biUnion_Icc_div_swap_eq {R : Type*} [CommRing R] (N M : ℕ) (f g : ℕ → R) :
    ∑ p ∈ (Finset.Icc 1 M).biUnion
        (fun b => (Finset.Icc 1 (N / b)).map
          ⟨fun a => (a, b), fun _a₁ _a₂ h => (Prod.mk.inj h).1⟩), f p.1 * g p.2 =
      ∑ b ∈ Finset.Icc 1 M, g b * ∑ a ∈ Finset.Icc 1 (N / b), f a := by
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => by
      change f a * g b = g b * f a
      ring
  · intro b₁ _ b₂ _ hne
    exact Finset.disjoint_left.mpr fun p hp₁ hp₂ => by
      rcases Finset.mem_map.mp hp₁ with ⟨_a₁, _, ha₁⟩
      rcases Finset.mem_map.mp hp₂ with ⟨_a₂, _, ha₂⟩
      exact hne (congrArg Prod.snd (ha₁.trans ha₂.symm))

/-- **General Dirichlet Hyperbola Identity** (valid for ALL `N : ℕ`, ALL `U ≥ 1`, and ANY
commutative ring `R`):
`∑_{n=1}^N (f * g)(n) = ∑_{a=1}^U f(a) ∑_{b=1}^{⌊N/a⌋} g(b) + ∑_{b=1}^{⌊N/U⌋} g(b) ∑_{a=1}^{⌊N/b⌋} f(a) - (∑_{a=1}^U f(a))(∑_{b=1}^{⌊N/U⌋} g(b))`. -/
theorem dirichlet_hyperbola_identity {R : Type*} [CommRing R] (f g : ℕ → R)
    (N U : ℕ) (hU : 1 ≤ U) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Nat.divisors n, f d * g (n / d) =
      (∑ a ∈ Finset.Icc 1 U, f a * ∑ b ∈ Finset.Icc 1 (N / a), g b) +
      (∑ b ∈ Finset.Icc 1 (N / U), g b * ∑ a ∈ Finset.Icc 1 (N / b), f a) -
      (∑ a ∈ Finset.Icc 1 U, f a) * (∑ b ∈ Finset.Icc 1 (N / U), g b) := by
  rw [sum_divisors_mul_eq_sum_filter (fun a b => f a * g b) N]
  set S : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N)
  set S₁ : Finset (ℕ × ℕ) := S.filter (fun p => p.1 ≤ U)
  set S₂ : Finset (ℕ × ℕ) := S.filter (fun p => p.2 ≤ N / U)
  have hS_union : S = S₁ ∪ S₂ := by
    ext ⟨a, b⟩
    simp only [S₁, S₂, Finset.mem_union, Finset.mem_filter, S, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN⟩
      by_cases haU : a ≤ U
      · exact Or.inl ⟨⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN⟩, haU⟩
      · right
        refine ⟨⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN⟩, ?_⟩
        by_contra hbU
        have ha' : U + 1 ≤ a := Nat.lt_of_not_ge haU
        have hb' : N / U + 1 ≤ b := Nat.lt_of_not_ge hbU
        have hmul : (U + 1) * (N / U + 1) ≤ a * b := Nat.mul_le_mul ha' hb'
        have hmod : U * (N / U) + N % U = N := Nat.div_add_mod N U
        have hlt : N % U < U := Nat.mod_lt N hU
        have hbig : N < (U + 1) * (N / U + 1) := by nlinarith
        omega
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hUnion : ∑ p ∈ S, f p.1 * g p.2 + ∑ p ∈ S₁ ∩ S₂, f p.1 * g p.2 =
      ∑ p ∈ S₁, f p.1 * g p.2 + ∑ p ∈ S₂, f p.1 * g p.2 := by
    rw [hS_union]
    exact Finset.sum_union_inter (s₁ := S₁) (s₂ := S₂) (f := fun p : ℕ × ℕ => f p.1 * g p.2)
  have hS₁ : ∑ p ∈ S₁, f p.1 * g p.2 =
      ∑ a ∈ Finset.Icc 1 U, f a * ∑ b ∈ Finset.Icc 1 (N / a), g b := by
    have hS₁_eq : S₁ = (Finset.Icc 1 U).biUnion
        (fun a => (Finset.Icc 1 (N / a)).map
          ⟨fun b => (a, b), fun b₁ b₂ h => (Prod.mk.inj h).2⟩) := by
      ext ⟨a, b⟩
      simp only [S₁, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_biUnion, Finset.mem_map]
      constructor
      · rintro ⟨⟨⟨⟨ha1, _⟩, ⟨hb1, _⟩⟩, habN⟩, haU⟩
        exact ⟨a, ⟨ha1, haU⟩, b, ⟨hb1, (Nat.le_div_iff_mul_le ha1).mpr
          (by simpa [mul_comm] using habN)⟩, rfl⟩
      · rintro ⟨a', ⟨ha1, haU⟩, b', ⟨hb1, hba⟩, hEq⟩
        cases hEq
        have habN : a * b ≤ N := (Nat.le_div_iff_mul_le ha1).mp hba |> fun h => by
          simpa [mul_comm] using h
        have haN : a ≤ N := le_trans (Nat.le_mul_of_pos_right a hb1) habN
        have hbN : b ≤ N := le_trans (Nat.le_mul_of_pos_left b ha1) habN
        exact ⟨⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN⟩, haU⟩
    rw [hS₁_eq, sum_biUnion_Icc_div_eq]
  have hS₂ : ∑ p ∈ S₂, f p.1 * g p.2 =
      ∑ b ∈ Finset.Icc 1 (N / U), g b * ∑ a ∈ Finset.Icc 1 (N / b), f a := by
    have hS₂_eq : S₂ = (Finset.Icc 1 (N / U)).biUnion
        (fun b => (Finset.Icc 1 (N / b)).map
          ⟨fun a => (a, b), fun a₁ a₂ h => (Prod.mk.inj h).1⟩) := by
      ext ⟨a, b⟩
      simp only [S₂, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_biUnion, Finset.mem_map]
      constructor
      · rintro ⟨⟨⟨⟨ha1, _⟩, ⟨hb1, _⟩⟩, habN⟩, hbU⟩
        exact ⟨b, ⟨hb1, hbU⟩, a, ⟨ha1, (Nat.le_div_iff_mul_le hb1).mpr habN⟩, rfl⟩
      · rintro ⟨b', ⟨hb1, hbU⟩, a', ⟨ha1, hab⟩, hEq⟩
        cases hEq
        have habN : a * b ≤ N := (Nat.le_div_iff_mul_le hb1).mp hab
        have haN : a ≤ N := le_trans (Nat.le_mul_of_pos_right a hb1) habN
        have hbN : b ≤ N := le_trans (Nat.le_mul_of_pos_left b ha1) habN
        exact ⟨⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN⟩, hbU⟩
    rw [hS₂_eq, sum_biUnion_Icc_div_swap_eq]
  have hInter : ∑ p ∈ S₁ ∩ S₂, f p.1 * g p.2 =
      (∑ a ∈ Finset.Icc 1 U, f a) * (∑ b ∈ Finset.Icc 1 (N / U), g b) := by
    have hInter_eq : S₁ ∩ S₂ = Finset.Icc 1 U ×ˢ Finset.Icc 1 (N / U) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_inter, S₁, S₂, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨⟨⟨ha1, _⟩, ⟨hb1, _⟩⟩, _⟩, haU⟩, ⟨_, hbU⟩⟩
        exact ⟨⟨ha1, haU⟩, ⟨hb1, hbU⟩⟩
      · rintro ⟨⟨ha1, haU⟩, ⟨hb1, hbU⟩⟩
        have habN : a * b ≤ N := (Nat.mul_le_mul haU hbU).trans (Nat.mul_div_le N U)
        have haN : a ≤ N := le_trans (Nat.le_mul_of_pos_right a hb1) habN
        have hbN : b ≤ N := le_trans (Nat.le_mul_of_pos_left b ha1) habN
        exact ⟨⟨⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN⟩, haU⟩,
          ⟨⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN⟩, hbU⟩⟩
    rw [hInter_eq, Finset.sum_product' (f := fun a b => f a * g b), Finset.sum_mul_sum]
  rw [hS₁, hS₂, hInter] at hUnion
  exact eq_sub_of_add_eq hUnion

/-- Symmetric `Nat.sqrt N` Dirichlet hyperbola identity (valid for all `N : ℕ` and any commutative
ring `R`). -/
theorem dirichlet_hyperbola_identity_sqrt {R : Type*} [CommRing R] (f g : ℕ → R) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Nat.divisors n, f d * g (n / d) =
      (∑ a ∈ Finset.Icc 1 (Nat.sqrt N), f a * ∑ b ∈ Finset.Icc 1 (N / a), g b) +
      (∑ b ∈ Finset.Icc 1 (Nat.sqrt N), g b * ∑ a ∈ Finset.Icc 1 (N / b), f a) -
      (∑ a ∈ Finset.Icc 1 (Nat.sqrt N), f a) * (∑ b ∈ Finset.Icc 1 (Nat.sqrt N), g b) := by
  rw [sum_divisors_mul_eq_sum_filter (fun a b => f a * g b) N]
  set s : ℕ := Nat.sqrt N
  set S : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N)
  set S₁ : Finset (ℕ × ℕ) := S.filter (fun p => p.1 ≤ s)
  set S₂ : Finset (ℕ × ℕ) := S.filter (fun p => p.2 ≤ s)
  have hS_union : S = S₁ ∪ S₂ := by
    ext ⟨a, b⟩
    simp only [S₁, S₂, Finset.mem_union, Finset.mem_filter, S, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN⟩
      by_cases has : a ≤ s
      · exact Or.inl ⟨⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN⟩, has⟩
      · right
        refine ⟨⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN⟩, ?_⟩
        by_contra hbs
        have ha' : s + 1 ≤ a := Nat.lt_of_not_ge has
        have hb' : s + 1 ≤ b := Nat.lt_of_not_ge hbs
        have hlt : N < (s + 1) * (s + 1) := by simpa [sq] using Nat.lt_succ_sqrt' N
        have hmul : (s + 1) * (s + 1) ≤ a * b := Nat.mul_le_mul ha' hb'
        omega
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hUnion : ∑ p ∈ S, f p.1 * g p.2 + ∑ p ∈ S₁ ∩ S₂, f p.1 * g p.2 =
      ∑ p ∈ S₁, f p.1 * g p.2 + ∑ p ∈ S₂, f p.1 * g p.2 := by
    rw [hS_union]
    exact Finset.sum_union_inter (s₁ := S₁) (s₂ := S₂) (f := fun p : ℕ × ℕ => f p.1 * g p.2)
  have hS₁ : ∑ p ∈ S₁, f p.1 * g p.2 =
      ∑ a ∈ Finset.Icc 1 s, f a * ∑ b ∈ Finset.Icc 1 (N / a), g b := by
    have hS₁_eq : S₁ = (Finset.Icc 1 s).biUnion
        (fun a => (Finset.Icc 1 (N / a)).map
          ⟨fun b => (a, b), fun b₁ b₂ h => (Prod.mk.inj h).2⟩) := by
      ext ⟨a, b⟩
      simp only [S₁, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_biUnion, Finset.mem_map]
      constructor
      · rintro ⟨⟨⟨⟨ha1, _⟩, ⟨hb1, _⟩⟩, habN⟩, has⟩
        exact ⟨a, ⟨ha1, has⟩, b, ⟨hb1, (Nat.le_div_iff_mul_le ha1).mpr
          (by simpa [mul_comm] using habN)⟩, rfl⟩
      · rintro ⟨a', ⟨ha1, has⟩, b', ⟨hb1, hba⟩, hEq⟩
        cases hEq
        have habN : a * b ≤ N := (Nat.le_div_iff_mul_le ha1).mp hba |> fun h => by
          simpa [mul_comm] using h
        have haN : a ≤ N := le_trans (Nat.le_mul_of_pos_right a hb1) habN
        have hbN : b ≤ N := le_trans (Nat.le_mul_of_pos_left b ha1) habN
        exact ⟨⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN⟩, has⟩
    rw [hS₁_eq, sum_biUnion_Icc_div_eq]
  have hS₂ : ∑ p ∈ S₂, f p.1 * g p.2 =
      ∑ b ∈ Finset.Icc 1 s, g b * ∑ a ∈ Finset.Icc 1 (N / b), f a := by
    have hS₂_eq : S₂ = (Finset.Icc 1 s).biUnion
        (fun b => (Finset.Icc 1 (N / b)).map
          ⟨fun a => (a, b), fun a₁ a₂ h => (Prod.mk.inj h).1⟩) := by
      ext ⟨a, b⟩
      simp only [S₂, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_biUnion, Finset.mem_map]
      constructor
      · rintro ⟨⟨⟨⟨ha1, _⟩, ⟨hb1, _⟩⟩, habN⟩, hbs⟩
        exact ⟨b, ⟨hb1, hbs⟩, a, ⟨ha1, (Nat.le_div_iff_mul_le hb1).mpr habN⟩, rfl⟩
      · rintro ⟨b', ⟨hb1, hbs⟩, a', ⟨ha1, hab⟩, hEq⟩
        cases hEq
        have habN : a * b ≤ N := (Nat.le_div_iff_mul_le hb1).mp hab
        have haN : a ≤ N := le_trans (Nat.le_mul_of_pos_right a hb1) habN
        have hbN : b ≤ N := le_trans (Nat.le_mul_of_pos_left b ha1) habN
        exact ⟨⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN⟩, hbs⟩
    rw [hS₂_eq, sum_biUnion_Icc_div_swap_eq]
  have hInter : ∑ p ∈ S₁ ∩ S₂, f p.1 * g p.2 =
      (∑ a ∈ Finset.Icc 1 s, f a) * (∑ b ∈ Finset.Icc 1 s, g b) := by
    have hInter_eq : S₁ ∩ S₂ = Finset.Icc 1 s ×ˢ Finset.Icc 1 s := by
      ext ⟨a, b⟩
      simp only [Finset.mem_inter, S₁, S₂, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨⟨⟨ha1, _⟩, ⟨hb1, _⟩⟩, _⟩, has⟩, ⟨_, hbs⟩⟩
        exact ⟨⟨ha1, has⟩, ⟨hb1, hbs⟩⟩
      · rintro ⟨⟨ha1, has⟩, ⟨hb1, hbs⟩⟩
        have habN : a * b ≤ N := (Nat.mul_le_mul has hbs).trans (Nat.sqrt_le N)
        have haN : a ≤ N := le_trans (Nat.le_mul_of_pos_right a hb1) habN
        have hbN : b ≤ N := le_trans (Nat.le_mul_of_pos_left b ha1) habN
        exact ⟨⟨⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN⟩, has⟩,
          ⟨⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN⟩, hbs⟩⟩
    rw [hInter_eq, Finset.sum_product' (f := fun a b => f a * g b), Finset.sum_mul_sum]
  rw [hS₁, hS₂, hInter] at hUnion
  exact eq_sub_of_add_eq hUnion

/-- Exact Dirichlet hyperbola identity for the divisor-count summatory function `∑_{n=1}^N d(n)`:
`∑_{n=1}^N d(n) + ⌊√N⌋² = 2 ∑_{a=1}^{⌊√N⌋} ⌊N/a⌋`. -/
theorem sum_divisors_card_hyperbola_nat (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (Nat.divisors n).card + (Nat.sqrt N) ^ 2 =
      2 * ∑ a ∈ Finset.Icc 1 (Nat.sqrt N), (N / a) := by
  have h := dirichlet_hyperbola_identity_sqrt (R := ℤ) (fun _ => 1) (fun _ => 1) N
  have hL : (∑ n ∈ Finset.Icc 1 N, ∑ _d ∈ Nat.divisors n, (1 : ℤ) * 1) =
      ((∑ n ∈ Finset.Icc 1 N, (Nat.divisors n).card : ℕ) : ℤ) := by
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    simp
  have hR1 : (∑ a ∈ Finset.Icc 1 (Nat.sqrt N), (1 : ℤ) * ∑ _b ∈ Finset.Icc 1 (N / a), (1 : ℤ)) =
      ((∑ a ∈ Finset.Icc 1 (Nat.sqrt N), (N / a) : ℕ) : ℤ) := by
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  have hR2 : (∑ a ∈ Finset.Icc 1 (Nat.sqrt N), (1 : ℤ)) = (Nat.sqrt N : ℤ) := by
    simp
  rw [hL, hR1, hR2] at h
  have hZ : ((∑ n ∈ Finset.Icc 1 N, (Nat.divisors n).card + (Nat.sqrt N) ^ 2 : ℕ) : ℤ) =
      ((2 * ∑ a ∈ Finset.Icc 1 (Nat.sqrt N), (N / a) : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, sq]
    linarith
  exact Int.ofNat.inj hZ

/-- Real-valued Dirichlet hyperbola identity for `∑_{n=1}^N d(n)`. -/
theorem sum_divisors_card_hyperbola_real (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((Nat.divisors n).card : ℝ) =
      2 * (∑ a ∈ Finset.Icc 1 (Nat.sqrt N), ((N / a : ℕ) : ℝ)) - ((Nat.sqrt N : ℝ) ^ 2) := by
  have h := congrArg (fun m : ℕ => (m : ℝ)) (sum_divisors_card_hyperbola_nat N)
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] at h
  linarith

private lemma sum_log_succ_sub_telescope {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) =
      Real.log ((N + 1 : ℕ) : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
    rw [hIcc, Finset.sum_insert hnot, ih]
    ring

private lemma sum_log_sub_pred_telescope {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 2 N, (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) =
      Real.log (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have hIcc2 : Finset.Icc 2 (N + 1) = insert (N + 1) (Finset.Icc 2 N) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnot2 : N + 1 ∉ Finset.Icc 2 N := by simp
    rw [hIcc2, Finset.sum_insert hnot2, ih]
    simp

/-- Explicit elementary logarithmic bounds for the harmonic sum `H_N = ∑_{k=1}^N 1/k`:
`log(N + 1) ≤ H_N ≤ log N + 1` for all `N ≥ 1`. -/
theorem harmonic_sum_log_bounds {N : ℕ} (hN : 1 ≤ N) :
    Real.log ((N + 1 : ℕ) : ℝ) ≤ ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) ∧
      ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) ≤ Real.log (N : ℝ) + 1 := by
  have hlow : Real.log ((N + 1 : ℕ) : ℝ) ≤ ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) := by
    rw [← sum_log_succ_sub_telescope hN]
    refine Finset.sum_le_sum fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk.1
    have hdiv_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / (k : ℝ) := by positivity
    have hle := Real.log_le_sub_one_of_pos hdiv_pos
    rw [Real.log_div (by positivity) hk_pos.ne'] at hle
    have hsub : ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 = (1 : ℝ) / (k : ℝ) := by
      push_cast; field_simp; ring
    linarith
  have hhigh : ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) ≤ Real.log (N : ℝ) + 1 := by
    have hIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnot : 1 ∉ Finset.Icc 2 N := by simp
    rw [hIcc, Finset.sum_insert hnot]
    have hsum_le : ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / (k : ℝ) ≤ Real.log (N : ℝ) := by
      rw [← sum_log_sub_pred_telescope hN]
      refine Finset.sum_le_sum fun k hk => ?_
      simp only [Finset.mem_Icc] at hk
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      have hkm_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 1)
      have hdiv_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) / (k : ℝ) := by positivity
      have hle := Real.log_le_sub_one_of_pos hdiv_pos
      rw [Real.log_div hkm_pos.ne' hk_pos.ne'] at hle
      have hsub : ((k - 1 : ℕ) : ℝ) / (k : ℝ) - 1 = -((1 : ℝ) / (k : ℝ)) := by
        have hkm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num
        rw [hkm]; field_simp; ring
      linarith
    linarith [show (1 : ℝ) / ((1 : ℕ) : ℝ) = 1 by norm_num]
  exact ⟨hlow, hhigh⟩

/-- **Explicit Dirichlet Divisor Asymptotic** (100% elementary, valid for all `N ≥ 1`):
`|∑_{n=1}^N d(n) - N log N| ≤ N + 2 √N`. -/
theorem sum_divisors_card_sub_mul_log_le {N : ℕ} (hN : 1 ≤ N) :
    |(∑ n ∈ Finset.Icc 1 N, ((Nat.divisors n).card : ℝ)) - (N : ℝ) * Real.log (N : ℝ)| ≤
      (N : ℝ) + 2 * Real.sqrt (N : ℝ) := by
  rw [sum_divisors_card_hyperbola_real N]
  set s : ℕ := Nat.sqrt N
  have hs1 : 1 ≤ s := Nat.sqrt_pos.mpr hN
  have hs_sq_le : (s : ℝ) ^ 2 ≤ (N : ℝ) := by
    have hnat : N.sqrt * N.sqrt ≤ N := Nat.sqrt_le N
    have hreal : (N.sqrt : ℝ) * (N.sqrt : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnat
    change (N.sqrt : ℝ) ^ 2 ≤ (N : ℝ)
    rw [sq]
    exact hreal
  have hs_le : (s : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg s) (Nat.cast_nonneg N)]
    exact hs_sq_le
  have hlt_sq : (N : ℝ) < ((s + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' N
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
  have hharm := harmonic_sum_log_bounds hs1
  have hdiv_le : ∀ a ∈ Finset.Icc 1 s, ((N / a : ℕ) : ℝ) ≤ (N : ℝ) / (a : ℝ) :=
    fun _ _ => Nat.cast_div_le
  have hdiv_ge : ∀ a ∈ Finset.Icc 1 s, (N : ℝ) / (a : ℝ) - 1 ≤ ((N / a : ℕ) : ℝ) := by
    intro a ha
    have ha_pos : 0 < a := (Finset.mem_Icc.mp ha).1
    have ha_rpos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha_pos
    have hmod : (N : ℝ) = (a : ℝ) * ((N / a : ℕ) : ℝ) + ((N % a : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod N a).symm
    have hrem : ((N % a : ℕ) : ℝ) < (a : ℝ) := by exact_mod_cast Nat.mod_lt N ha_pos
    rw [sub_le_iff_le_add, div_le_iff₀ ha_rpos]
    nlinarith
  have hsum_le : ∑ a ∈ Finset.Icc 1 s, ((N / a : ℕ) : ℝ) ≤
      (N : ℝ) * (Real.log (s : ℝ) + 1) := by
    calc
      ∑ a ∈ Finset.Icc 1 s, ((N / a : ℕ) : ℝ)
        ≤ ∑ a ∈ Finset.Icc 1 s, (N : ℝ) / (a : ℝ) := Finset.sum_le_sum hdiv_le
      _ = (N : ℝ) * ∑ a ∈ Finset.Icc 1 s, (1 : ℝ) / (a : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => by ring
      _ ≤ (N : ℝ) * (Real.log (s : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hharm.2 hN_pos.le
  have hsum_ge : (N : ℝ) * Real.log ((s + 1 : ℕ) : ℝ) - (s : ℝ) ≤
      ∑ a ∈ Finset.Icc 1 s, ((N / a : ℕ) : ℝ) := by
    calc
      (N : ℝ) * Real.log ((s + 1 : ℕ) : ℝ) - (s : ℝ)
        ≤ (N : ℝ) * (∑ a ∈ Finset.Icc 1 s, (1 : ℝ) / (a : ℝ)) - (s : ℝ) := by
          gcongr; exact hharm.1
      _ = ∑ a ∈ Finset.Icc 1 s, ((N : ℝ) / (a : ℝ) - 1) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
          have hs_card : ∑ _a ∈ Finset.Icc 1 s, (1 : ℝ) = (s : ℝ) := by simp
          rw [hs_card]
          congr 1
          refine Finset.sum_congr rfl fun a _ => by ring
      _ ≤ ∑ a ∈ Finset.Icc 1 s, ((N / a : ℕ) : ℝ) := Finset.sum_le_sum hdiv_ge
  have hlog_s_le : 2 * Real.log (s : ℝ) ≤ Real.log (N : ℝ) := by
    rw [← Real.log_rpow hs_pos 2]
    apply Real.log_le_log (by positivity)
    have : (s : ℝ) ^ (2 : ℝ) = (s : ℝ) ^ (2 : ℕ) := by norm_cast
    rw [this]
    exact hs_sq_le
  have hlog_succ_ge : Real.log (N : ℝ) ≤ 2 * Real.log ((s + 1 : ℕ) : ℝ) := by
    have hs1_pos : (0 : ℝ) < ((s + 1 : ℕ) : ℝ) := by positivity
    rw [← Real.log_rpow hs1_pos 2]
    apply Real.log_le_log hN_pos
    have : ((s + 1 : ℕ) : ℝ) ^ (2 : ℝ) = ((s + 1 : ℕ) : ℝ) ^ (2 : ℕ) := by norm_cast
    rw [this]
    exact hlt_sq.le
  have hupper : 2 * ∑ a ∈ Finset.Icc 1 s, ((N / a : ℕ) : ℝ) - (s : ℝ) ^ 2 -
      (N : ℝ) * Real.log (N : ℝ) ≤ (N : ℝ) + 2 * Real.sqrt (N : ℝ) := by
    have hs_sq_tight : (N : ℝ) - (s : ℝ) ^ 2 ≤ 2 * Real.sqrt (N : ℝ) := by
      have hNat : N < (s + 1) ^ 2 := Nat.lt_succ_sqrt' N
      have hNat2 : N ≤ s ^ 2 + 2 * s := by nlinarith
      have hReal : (N : ℝ) ≤ (s : ℝ) ^ 2 + 2 * (s : ℝ) := by exact_mod_cast hNat2
      linarith
    nlinarith
  have hlower : -((N : ℝ) + 2 * Real.sqrt (N : ℝ)) ≤
      2 * ∑ a ∈ Finset.Icc 1 s, ((N / a : ℕ) : ℝ) - (s : ℝ) ^ 2 - (N : ℝ) * Real.log (N : ℝ) := by
    nlinarith
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Elementary bound `d(a * b) ≤ d(a) * d(b)` for all `a, b : ℕ`. -/
theorem divisors_card_mul_le (a b : ℕ) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun d => (Nat.gcd d a, d / Nat.gcd d a)) ?_ ?_
  · intro d hd
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Nat.mem_divisors] at hd ⊢
    rcases hd with ⟨hdab, _⟩
    set u := Nat.gcd d a
    have hu_dvd_d : u ∣ d := Nat.gcd_dvd_left d a
    have hu_dvd_a : u ∣ a := Nat.gcd_dvd_right d a
    have hu_pos : 0 < u := Nat.gcd_pos_of_pos_right d ha_pos
    have hcop : Nat.Coprime (d / u) (a / u) := Nat.coprime_div_gcd_div_gcd hu_pos
    have hdvd_prod : (d / u) * u ∣ (a / u) * b * u := by
      rw [Nat.div_mul_cancel hu_dvd_d, mul_right_comm (a / u) b u, Nat.div_mul_cancel hu_dvd_a]
      exact hdab
    have hdvd_mul : d / u ∣ (a / u) * b := (Nat.mul_dvd_mul_iff_right hu_pos).mp hdvd_prod
    have hdv_b : d / u ∣ b := hcop.dvd_of_dvd_mul_left hdvd_mul
    exact ⟨⟨hu_dvd_a, ha⟩, ⟨hdv_b, hb⟩⟩
  · intro d₁ _ d₂ _ hEq
    have h1 : Nat.gcd d₁ a = Nat.gcd d₂ a := congrArg Prod.fst hEq
    have h2 : d₁ / Nat.gcd d₁ a = d₂ / Nat.gcd d₂ a := congrArg Prod.snd hEq
    calc
      d₁ = d₁ / Nat.gcd d₁ a * Nat.gcd d₁ a := (Nat.div_mul_cancel (Nat.gcd_dvd_left d₁ a)).symm
      _ = d₂ / Nat.gcd d₂ a * Nat.gcd d₂ a := by rw [h2, h1]
      _ = d₂ := Nat.div_mul_cancel (Nat.gcd_dvd_left d₂ a)

/-- Elementary pointwise divisor bound `d(n) ≤ 2 √n` for all `n ≥ 1`. -/
theorem divisors_card_le_two_sqrt {n : ℕ} (hn : 1 ≤ n) :
    ((Nat.divisors n).card : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  set s : ℕ := Nat.sqrt n
  have hsub : n.divisors ⊆ Finset.Icc 1 s ∪ (Finset.Icc 1 s).image (fun k => n / k) := by
    intro d hd
    simp only [Nat.mem_divisors] at hd
    rcases hd with ⟨hdn, hn0⟩
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_image]
    by_cases hds : d ≤ s
    · exact Or.inl ⟨hd_pos, hds⟩
    · right
      have hq_pos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd_pos
      have hq_le : n / d ≤ s := by
        by_contra hqs
        have hd1 : s + 1 ≤ d := Nat.lt_of_not_ge hds
        have hq1 : s + 1 ≤ n / d := Nat.lt_of_not_ge hqs
        have hlt : n < (s + 1) * (s + 1) := by simpa [sq] using Nat.lt_succ_sqrt' n
        have hmul : (s + 1) * (s + 1) ≤ (n / d) * d := Nat.mul_le_mul hq1 hd1
        rw [Nat.div_mul_cancel hdn] at hmul
        omega
      refine ⟨n / d, ⟨hq_pos, hq_le⟩, ?_⟩
      exact Nat.div_div_self hdn hn0
  have hcard : n.divisors.card ≤ 2 * s := by
    calc
      n.divisors.card ≤ (Finset.Icc 1 s ∪ (Finset.Icc 1 s).image (fun k => n / k)).card :=
        Finset.card_le_card hsub
      _ ≤ (Finset.Icc 1 s).card + ((Finset.Icc 1 s).image (fun k => n / k)).card :=
        Finset.card_union_le _ _
      _ ≤ s + s := by
        gcongr
        · simp
        · exact (Finset.card_image_le).trans (by simp)
      _ = 2 * s := by ring
  have hs_le : (s : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg s) (Nat.cast_nonneg n)]
    have hnat : n.sqrt * n.sqrt ≤ n := Nat.sqrt_le n
    have hreal : (n.sqrt : ℝ) * (n.sqrt : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnat
    dsimp only [s]
    rw [sq]
    exact hreal
  have hreal : ((Nat.divisors n).card : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast hcard
  linarith

/-- First divisor moment upper bound: `∑_{n=1}^N d(n) ≤ N (log N + 1)` for all `N ≥ 1`. -/
theorem sum_divisors_card_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ((Nat.divisors n).card : ℝ) ≤ (N : ℝ) * (Real.log (N : ℝ) + 1) := by
  have h1 : ∑ n ∈ Finset.Icc 1 N, ((Nat.divisors n).card : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, ((N / d : ℕ) : ℝ) := by
    have hNat : ∑ n ∈ Finset.Icc 1 N, (Nat.divisors n).card = ∑ d ∈ Finset.Icc 1 N, (N / d) := by
      have h := sum_divisors_mul_eq_sum_filter (R := ℕ) (fun _ _ => 1) N
      have hL : ∑ n ∈ Finset.Icc 1 N, ∑ _d ∈ Nat.divisors n, 1 =
          ∑ n ∈ Finset.Icc 1 N, (Nat.divisors n).card := by
        refine Finset.sum_congr rfl fun n _ => by simp
      have hR : ∑ _p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N), 1 =
          ∑ d ∈ Finset.Icc 1 N, (N / d) := by
        have hS : (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N) =
            (Finset.Icc 1 N).biUnion
              (fun d => (Finset.Icc 1 (N / d)).map
                ⟨fun q => (d, q), fun q₁ q₂ h => (Prod.mk.inj h).2⟩) := by
          ext ⟨a, b⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_biUnion,
            Finset.mem_map]
          constructor
          · rintro ⟨⟨⟨ha1, haN⟩, ⟨hb1, _⟩⟩, habN⟩
            exact ⟨a, ⟨ha1, haN⟩, b, ⟨hb1, (Nat.le_div_iff_mul_le ha1).mpr
              (by simpa [mul_comm] using habN)⟩, rfl⟩
          · rintro ⟨a', ⟨ha1, haN⟩, b', ⟨hb1, hba⟩, hEq⟩
            cases hEq
            have habN : a * b ≤ N := (Nat.le_div_iff_mul_le ha1).mp hba |> fun h => by
              simpa [mul_comm] using h
            exact ⟨⟨⟨ha1, haN⟩, ⟨hb1, le_trans (Nat.le_mul_of_pos_left b ha1) habN⟩⟩, habN⟩
        rw [hS, Finset.sum_biUnion]
        · refine Finset.sum_congr rfl fun d _ => by simp
        · intro d₁ _ d₂ _ hne
          exact Finset.disjoint_left.mpr fun p hp₁ hp₂ => by
            rcases Finset.mem_map.mp hp₁ with ⟨b₁, _, hb₁⟩
            rcases Finset.mem_map.mp hp₂ with ⟨b₂, _, hb₂⟩
            exact hne (congrArg Prod.fst (hb₁.trans hb₂.symm))
      rw [hL, hR] at h
      exact h
    exact_mod_cast hNat
  rw [h1]
  have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  calc
    ∑ d ∈ Finset.Icc 1 N, ((N / d : ℕ) : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 N, (N : ℝ) / (d : ℝ) := by
        refine Finset.sum_le_sum fun d _ => Nat.cast_div_le
    _ = (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => by ring
    _ ≤ (N : ℝ) * (Real.log (N : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (harmonic_sum_log_bounds hN).2 hN_nonneg

/-- General `k`-th divisor moment reciprocal bound:
`∑_{n=1}^N d(n)^k / n ≤ (log N + 1)^(2^k)` for all `k : ℕ` and `N ≥ 1`. -/
theorem sum_divisors_card_pow_div_le (k : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ((Nat.divisors n).card : ℝ) ^ k / (n : ℝ) ≤
      (Real.log (N : ℝ) + 1) ^ (2 ^ k) := by
  induction k generalizing N with
  | zero =>
    simpa [pow_zero] using (harmonic_sum_log_bounds hN).2
  | succ k ih =>
    have hlog1 : 0 ≤ Real.log (N : ℝ) + 1 := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith [Real.log_nonneg this]
    have hrewrite : ∀ n ∈ Finset.Icc 1 N,
        ((Nat.divisors n).card : ℝ) ^ (k + 1) / (n : ℝ) =
          ∑ _d ∈ Nat.divisors n, ((Nat.divisors n).card : ℝ) ^ k / (n : ℝ) := by
      intro n _
      rw [Finset.sum_const, nsmul_eq_mul, pow_succ']
      ring
    calc
      ∑ n ∈ Finset.Icc 1 N, ((Nat.divisors n).card : ℝ) ^ (k + 1) / (n : ℝ)
        = ∑ n ∈ Finset.Icc 1 N, ∑ _d ∈ Nat.divisors n,
            ((Nat.divisors n).card : ℝ) ^ k / (n : ℝ) := Finset.sum_congr rfl hrewrite
      _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Nat.divisors n,
            ((Nat.divisors (d * (n / d))).card : ℝ) ^ k / ((d * (n / d) : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun d hd => ?_
          rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
      _ = ∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N),
            ((Nat.divisors (p.1 * p.2)).card : ℝ) ^ k / ((p.1 * p.2 : ℕ) : ℝ) :=
          sum_divisors_mul_eq_sum_filter
            (fun a b => ((Nat.divisors (a * b)).card : ℝ) ^ k / ((a * b : ℕ) : ℝ)) N
      _ ≤ ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
            (((Nat.divisors p.1).card : ℝ) ^ k / (p.1 : ℝ)) *
              (((Nat.divisors p.2).card : ℝ) ^ k / (p.2 : ℝ)) := by
          have hfilter_le :
              ∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N),
                ((Nat.divisors (p.1 * p.2)).card : ℝ) ^ k / ((p.1 * p.2 : ℕ) : ℝ) ≤
              ∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N),
                (((Nat.divisors p.1).card : ℝ) ^ k / (p.1 : ℝ)) *
                  (((Nat.divisors p.2).card : ℝ) ^ k / (p.2 : ℝ)) := by
            refine Finset.sum_le_sum fun p hp => ?_
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
            have hp1 : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hp.1.1.1
            have hp2 : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast hp.1.2.1
            have hmul_le : ((Nat.divisors (p.1 * p.2)).card : ℝ) ≤
                ((Nat.divisors p.1).card : ℝ) * ((Nat.divisors p.2).card : ℝ) := by
              exact_mod_cast divisors_card_mul_le p.1 p.2
            have hpow : ((Nat.divisors (p.1 * p.2)).card : ℝ) ^ k ≤
                (((Nat.divisors p.1).card : ℝ) * ((Nat.divisors p.2).card : ℝ)) ^ k :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) hmul_le k
            rw [mul_pow] at hpow
            have hcast : ((p.1 * p.2 : ℕ) : ℝ) = (p.1 : ℝ) * (p.2 : ℝ) := by push_cast; rfl
            rw [hcast]
            calc
              ((Nat.divisors (p.1 * p.2)).card : ℝ) ^ k / ((p.1 : ℝ) * (p.2 : ℝ))
                ≤ (((Nat.divisors p.1).card : ℝ) ^ k * ((Nat.divisors p.2).card : ℝ) ^ k) /
                    ((p.1 : ℝ) * (p.2 : ℝ)) := by gcongr
              _ = (((Nat.divisors p.1).card : ℝ) ^ k / (p.1 : ℝ)) *
                    (((Nat.divisors p.2).card : ℝ) ^ k / (p.2 : ℝ)) := by ring
          refine hfilter_le.trans ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
            by positivity
      _ = (∑ n ∈ Finset.Icc 1 N, ((Nat.divisors n).card : ℝ) ^ k / (n : ℝ)) *
            (∑ n ∈ Finset.Icc 1 N, ((Nat.divisors n).card : ℝ) ^ k / (n : ℝ)) := by
          rw [Finset.sum_product' (f := fun a b =>
            (((Nat.divisors a).card : ℝ) ^ k / (a : ℝ)) *
              (((Nat.divisors b).card : ℝ) ^ k / (b : ℝ))), Finset.sum_mul_sum]
      _ ≤ (Real.log (N : ℝ) + 1) ^ (2 ^ k) * (Real.log (N : ℝ) + 1) ^ (2 ^ k) :=
          mul_le_mul (ih hN) (ih hN) (Finset.sum_nonneg fun _ _ => by positivity)
            (pow_nonneg hlog1 _)
      _ = (Real.log (N : ℝ) + 1) ^ (2 ^ (k + 1)) := by
          rw [← pow_add, show 2 ^ k + 2 ^ k = 2 ^ (k + 1) by ring]

/-- General `k`-th divisor moment upper bound:
`∑_{n=1}^N d(n)^k ≤ N · (log N + 1)^(2^k - 1)` for all `k : ℕ` and `N ≥ 1`. -/
theorem sum_divisors_card_pow_le (k : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ((Nat.divisors n).card : ℝ) ^ k ≤
      (N : ℝ) * (Real.log (N : ℝ) + 1) ^ (2 ^ k - 1) := by
  induction k generalizing N with
  | zero =>
    simp
  | succ k ih =>
    have hlog1 : 0 ≤ Real.log (N : ℝ) + 1 := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith [Real.log_nonneg this]
    have hN_pos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hrewrite : ∀ n ∈ Finset.Icc 1 N,
        ((Nat.divisors n).card : ℝ) ^ (k + 1) =
          ∑ _d ∈ Nat.divisors n, ((Nat.divisors n).card : ℝ) ^ k := by
      intro n _
      rw [Finset.sum_const, nsmul_eq_mul, pow_succ']
    calc
      ∑ n ∈ Finset.Icc 1 N, ((Nat.divisors n).card : ℝ) ^ (k + 1)
        = ∑ n ∈ Finset.Icc 1 N, ∑ _d ∈ Nat.divisors n,
            ((Nat.divisors n).card : ℝ) ^ k := Finset.sum_congr rfl hrewrite
      _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Nat.divisors n,
            ((Nat.divisors (d * (n / d))).card : ℝ) ^ k := by
          refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun d hd => ?_
          rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
      _ = ∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N),
            ((Nat.divisors (p.1 * p.2)).card : ℝ) ^ k :=
          sum_divisors_mul_eq_sum_filter (fun a b => ((Nat.divisors (a * b)).card : ℝ) ^ k) N
      _ ≤ ∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N),
            ((Nat.divisors p.1).card : ℝ) ^ k * ((Nat.divisors p.2).card : ℝ) ^ k := by
          refine Finset.sum_le_sum fun p _ => ?_
          have hmul : ((Nat.divisors (p.1 * p.2)).card : ℝ) ≤
              ((Nat.divisors p.1).card : ℝ) * ((Nat.divisors p.2).card : ℝ) := by
            exact_mod_cast divisors_card_mul_le p.1 p.2
          rw [← mul_pow]
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) hmul k
      _ = ∑ a ∈ Finset.Icc 1 N, ((Nat.divisors a).card : ℝ) ^ k *
            ∑ b ∈ Finset.Icc 1 (N / a), ((Nat.divisors b).card : ℝ) ^ k := by
          have hS : (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N) =
              (Finset.Icc 1 N).biUnion
                (fun a => (Finset.Icc 1 (N / a)).map
                  ⟨fun b => (a, b), fun b₁ b₂ h => (Prod.mk.inj h).2⟩) := by
            ext ⟨a, b⟩
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_biUnion,
              Finset.mem_map]
            constructor
            · rintro ⟨⟨⟨ha1, haN⟩, ⟨hb1, _⟩⟩, habN⟩
              exact ⟨a, ⟨ha1, haN⟩, b, ⟨hb1, (Nat.le_div_iff_mul_le ha1).mpr
                (by simpa [mul_comm] using habN)⟩, rfl⟩
            · rintro ⟨a', ⟨ha1, haN⟩, b', ⟨hb1, hba⟩, hEq⟩
              cases hEq
              have habN : a * b ≤ N := (Nat.le_div_iff_mul_le ha1).mp hba |> fun h => by
                simpa [mul_comm] using h
              exact ⟨⟨⟨ha1, haN⟩, ⟨hb1, le_trans (Nat.le_mul_of_pos_left b ha1) habN⟩⟩, habN⟩
          rw [hS, Finset.sum_biUnion]
          · refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.sum_map, Finset.mul_sum]
            rfl
          · intro a₁ _ a₂ _ hne
            exact Finset.disjoint_left.mpr fun p hp₁ hp₂ => by
              rcases Finset.mem_map.mp hp₁ with ⟨b₁, _, hb₁⟩
              rcases Finset.mem_map.mp hp₂ with ⟨b₂, _, hb₂⟩
              exact hne (congrArg Prod.fst (hb₁.trans hb₂.symm))
      _ ≤ ∑ a ∈ Finset.Icc 1 N, ((Nat.divisors a).card : ℝ) ^ k *
            (((N / a : ℕ) : ℝ) * (Real.log (N : ℝ) + 1) ^ (2 ^ k - 1)) := by
          refine Finset.sum_le_sum fun a ha => ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          by_cases hNa : 1 ≤ N / a
          · have hsub := ih hNa
            have hlog_le : Real.log ((N / a : ℕ) : ℝ) + 1 ≤ Real.log (N : ℝ) + 1 := by
              have hNa_pos : (0 : ℝ) < ((N / a : ℕ) : ℝ) := by exact_mod_cast hNa
              have hNa_le : ((N / a : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.div_le_self N a
              linarith [Real.log_le_log hNa_pos hNa_le]
            calc
              ∑ b ∈ Finset.Icc 1 (N / a), ((Nat.divisors b).card : ℝ) ^ k
                ≤ ((N / a : ℕ) : ℝ) * (Real.log ((N / a : ℕ) : ℝ) + 1) ^ (2 ^ k - 1) := hsub
              _ ≤ ((N / a : ℕ) : ℝ) * (Real.log (N : ℝ) + 1) ^ (2 ^ k - 1) := by
                gcongr
          · have h0 : N / a = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp hNa)
            simp [h0]
      _ ≤ ∑ a ∈ Finset.Icc 1 N, ((Nat.divisors a).card : ℝ) ^ k *
            (((N : ℝ) / (a : ℝ)) * (Real.log (N : ℝ) + 1) ^ (2 ^ k - 1)) := by
          refine Finset.sum_le_sum fun a _ => ?_
          gcongr
          exact Nat.cast_div_le
      _ = (N : ℝ) * (Real.log (N : ℝ) + 1) ^ (2 ^ k - 1) *
            ∑ a ∈ Finset.Icc 1 N, ((Nat.divisors a).card : ℝ) ^ k / (a : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => by ring
      _ ≤ (N : ℝ) * (Real.log (N : ℝ) + 1) ^ (2 ^ k - 1) * (Real.log (N : ℝ) + 1) ^ (2 ^ k) := by
          gcongr
          exact sum_divisors_card_pow_div_le k hN
      _ = (N : ℝ) * (Real.log (N : ℝ) + 1) ^ (2 ^ (k + 1) - 1) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          have hpow1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
          omega

/-! ## Section 3: Weyl Differencing & Van der Corput `A`-Process -/

/-- Additive unit-circle character `e(x) = exp(2π i x)`. -/
def e (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

@[simp] theorem e_zero : e 0 = 1 := by
  simp [e]

theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp only [e, ← Complex.exp_add]
  push_cast
  ring

theorem e_neg (x : ℝ) : e (-x) = (e x)⁻¹ := by
  simp only [e, ← Complex.exp_neg]
  push_cast
  ring

theorem e_sub (x y : ℝ) : e (x - y) = e x / e y := by
  rw [sub_eq_add_neg, e_add, e_neg, div_eq_mul_inv]

@[simp] theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  simp only [e]
  exact Complex.norm_exp_ofReal_mul_I _

theorem e_ne_zero (x : ℝ) : e x ≠ 0 := by
  have h := norm_e x
  intro hz
  rw [hz, norm_zero] at h
  norm_num at h

@[simp] theorem e_intCast (k : ℤ) : e (k : ℝ) = 1 := by
  simp only [e]
  rw [Complex.exp_eq_one_iff]
  refine ⟨k, ?_⟩
  push_cast
  ring

@[simp] theorem star_e (x : ℝ) : star (e x) = e (-x) := by
  simp only [e, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem e_mul_star_e (x y : ℝ) : e x * star (e y) = e (x - y) := by
  rw [star_e, ← e_add, sub_eq_add_neg]

theorem norm_e_sub_one (α : ℝ) : ‖e α - 1‖ = 2 * |Real.sin (Real.pi * α)| := by
  have hfac : e α - 1 = e (α / 2) * (e (α / 2) - e (-(α / 2))) := by
    rw [mul_sub, ← e_add, ← e_add]
    have h1 : α / 2 + α / 2 = α := by ring
    have h2 : α / 2 + -(α / 2) = 0 := by ring
    rw [h1, h2, e_zero]
  have hsin_eq : e (α / 2) - e (-(α / 2)) =
      ((2 * Real.sin (Real.pi * α) : ℝ) : ℂ) * Complex.I := by
    simp only [e]
    have ha : ((2 * Real.pi * (α / 2) : ℝ) : ℂ) * Complex.I =
        ((Real.pi * α : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hb : ((2 * Real.pi * -(α / 2) : ℝ) : ℂ) * Complex.I =
        ((- (Real.pi * α) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [ha, hb, Complex.exp_mul_I, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hfac, norm_mul, norm_e, one_mul, hsin_eq, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Geometric-series identity for linear exponential sums on `Finset.Ico a b`. -/
theorem e_sub_one_mul_sum_Ico (α : ℝ) {a b : ℕ} (hab : a ≤ b) :
    (e α - 1) * ∑ n ∈ Finset.Ico a b, e (α * (n : ℝ)) =
      e (α * (b : ℝ)) - e (α * (a : ℝ)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hIco : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Ico]; omega
    have hnot : b ∉ Finset.Ico a b := by simp
    rw [hIco, Finset.sum_insert hnot, mul_add, ih]
    have hstep : (e α - 1) * e (α * (b : ℝ)) =
        e (α * ((b + 1 : ℕ) : ℝ)) - e (α * (b : ℝ)) := by
      rw [sub_mul, one_mul, ← e_add]
      congr 1
      push_cast
      ring
    rw [hstep]
    ring

/-- Classical linear exponential sum bound:
`‖∑_{n ∈ Ico a b} e(α n)‖ ≤ min (b - a) (1 / |sin(π α)|)` whenever `sin(π α) ≠ 0`. -/
theorem norm_sum_e_linear_Ico_le (α : ℝ) {a b : ℕ} (hab : a ≤ b)
    (hsin : Real.sin (Real.pi * α) ≠ 0) :
    ‖∑ n ∈ Finset.Ico a b, e (α * (n : ℝ))‖ ≤
      min ((b - a : ℝ)) (1 / |Real.sin (Real.pi * α)|) := by
  refine le_min ?_ ?_
  · calc
      ‖∑ n ∈ Finset.Ico a b, e (α * (n : ℝ))‖
        ≤ ∑ _n ∈ Finset.Ico a b, ‖e (α * (_n : ℝ))‖ := norm_sum_le _ _
      _ = ((Finset.Ico a b).card : ℝ) := by simp
      _ = ((b - a : ℕ) : ℝ) := by rw [Nat.card_Ico]
      _ = (b : ℝ) - (a : ℝ) := by rw [Nat.cast_sub hab]
  · have hne : e α - 1 ≠ 0 := by
      intro hz
      have hnorm : ‖e α - 1‖ = 0 := by rw [hz, norm_zero]
      rw [norm_e_sub_one] at hnorm
      have habs : |Real.sin (Real.pi * α)| = 0 := by linarith
      exact hsin (abs_eq_zero.mp habs)
    have hmul := congrArg norm (e_sub_one_mul_sum_Ico α hab)
    rw [norm_mul, norm_e_sub_one] at hmul
    have hrhs : ‖e (α * (b : ℝ)) - e (α * (a : ℝ))‖ ≤ 2 := by
      calc
        ‖e (α * (b : ℝ)) - e (α * (a : ℝ))‖
          ≤ ‖e (α * (b : ℝ))‖ + ‖e (α * (a : ℝ))‖ := norm_sub_le _ _
        _ = 2 := by simp; norm_num
    have hpos : 0 < |Real.sin (Real.pi * α)| := abs_pos.mpr hsin
    rw [le_div_iff₀ hpos]
    linarith

/-- Jordan's inequality specialization for `0 < |α| ≤ 1/2`:
`‖∑_{n ∈ Ico a b} e(α n)‖ ≤ min (b - a) (1 / (2 * |α|))`. -/
theorem norm_sum_e_linear_Ico_le_abs {α : ℝ} (hα0 : α ≠ 0) (hαhalf : |α| ≤ 1 / 2)
    {a b : ℕ} (hab : a ≤ b) :
    ‖∑ n ∈ Finset.Ico a b, e (α * (n : ℝ))‖ ≤ min ((b - a : ℝ)) (1 / (2 * |α|)) := by
  have harg_nn : 0 ≤ Real.pi * |α| := mul_nonneg Real.pi_pos.le (abs_nonneg α)
  have harg_le : Real.pi * |α| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hjordan : 2 * |α| ≤ Real.sin (Real.pi * |α|) := by
    have h := Real.mul_le_sin harg_nn harg_le
    have hpi : 2 / Real.pi * (Real.pi * |α|) = 2 * |α| := by
      field_simp [Real.pi_ne_zero]
    linarith
  have hsin_abs : |Real.sin (Real.pi * α)| = Real.sin (Real.pi * |α|) := by
    by_cases h0 : 0 ≤ α
    · rw [abs_of_nonneg h0]
      have hnn := Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le h0)
        (by rw [abs_of_nonneg h0] at harg_le; linarith [Real.pi_pos])
      exact abs_of_nonneg hnn
    · push Not at h0
      have hneg : Real.sin (Real.pi * |α|) = -Real.sin (Real.pi * α) := by
        rw [abs_of_neg h0, mul_neg, Real.sin_neg]
      have hnn : 0 ≤ Real.sin (Real.pi * |α|) :=
        Real.sin_nonneg_of_nonneg_of_le_pi harg_nn (by linarith [Real.pi_pos])
      rw [hneg] at hnn ⊢
      exact abs_of_nonpos (by linarith)
  have hsin_pos : 0 < |Real.sin (Real.pi * α)| := by
    have : 0 < |α| := abs_pos.mpr hα0
    linarith
  have hbase := norm_sum_e_linear_Ico_le α hab (abs_pos.mp hsin_pos)
  refine hbase.trans (min_le_min le_rfl ?_)
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

private lemma sum_Ico_prod_split {R : Type*} [CommRing R] (F : ℕ → ℕ → R) {a b : ℕ}
    (hab : a ≤ b) :
    ∑ m ∈ Finset.Ico a b, ∑ n ∈ Finset.Ico a b, F m n =
      (∑ n ∈ Finset.Ico a b, F n n) +
        ∑ h ∈ Finset.Icc 1 (b - a), ∑ n ∈ Finset.Ico a (b - h), (F (n + h) n + F n (n + h)) := by
  rw [← Finset.sum_product']
  set D : Finset (ℕ × ℕ) := (Finset.Ico a b).image (fun n => (n, n))
  set U : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 (b - a)).biUnion (fun h => (Finset.Ico a (b - h)).image (fun n => (n + h, n)))
  set L : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 (b - a)).biUnion (fun h => (Finset.Ico a (b - h)).image (fun n => (n, n + h)))
  have hDU : Disjoint D U := by
    rw [Finset.disjoint_left]
    intro p hpD hpU
    rcases Finset.mem_image.mp hpD with ⟨n, _, rfl⟩
    rcases Finset.mem_biUnion.mp hpU with ⟨h, hh, hmem⟩
    rcases Finset.mem_image.mp hmem with ⟨m, _, hm⟩
    simp only [Finset.mem_Icc] at hh
    have h1 := congrArg Prod.fst hm
    have h2 := congrArg Prod.snd hm
    omega
  have hDL : Disjoint D L := by
    rw [Finset.disjoint_left]
    intro p hpD hpL
    rcases Finset.mem_image.mp hpD with ⟨n, _, rfl⟩
    rcases Finset.mem_biUnion.mp hpL with ⟨h, hh, hmem⟩
    rcases Finset.mem_image.mp hmem with ⟨m, _, hm⟩
    simp only [Finset.mem_Icc] at hh
    have h1 := congrArg Prod.fst hm
    have h2 := congrArg Prod.snd hm
    omega
  have hUL : Disjoint U L := by
    rw [Finset.disjoint_left]
    intro p hpU hpL
    rcases Finset.mem_biUnion.mp hpU with ⟨h₁, hh₁, hmem₁⟩
    rcases Finset.mem_image.mp hmem₁ with ⟨m₁, _, hm₁⟩
    rcases Finset.mem_biUnion.mp hpL with ⟨h₂, hh₂, hmem₂⟩
    rcases Finset.mem_image.mp hmem₂ with ⟨m₂, _, hm₂⟩
    simp only [Finset.mem_Icc] at hh₁ hh₂
    have hf1 := congrArg Prod.fst hm₁
    have hs1 := congrArg Prod.snd hm₁
    have hf2 := congrArg Prod.fst hm₂
    have hs2 := congrArg Prod.snd hm₂
    omega
  have hAll : Finset.Ico a b ×ˢ Finset.Ico a b = D ∪ U ∪ L := by
    ext ⟨m, n⟩
    simp only [Finset.mem_product, Finset.mem_Ico, Finset.mem_union, D, U, L, Finset.mem_image,
      Finset.mem_biUnion, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hm1, hm2⟩, ⟨hn1, hn2⟩⟩
      rcases lt_trichotomy m n with hlt | rfl | hgt
      · right
        refine ⟨n - m, ⟨by omega, by omega⟩, m, ⟨hm1, by omega⟩, ?_⟩
        ext <;> simp
        omega
      · left; left
        exact ⟨m, ⟨hm1, hm2⟩, rfl⟩
      · left; right
        refine ⟨m - n, ⟨by omega, by omega⟩, n, ⟨hn1, by omega⟩, ?_⟩
        ext <;> simp
        omega
    · rintro ((⟨k, ⟨hk1, hk2⟩, hEq⟩ | ⟨h, ⟨hh1, _⟩, k, ⟨hk1, hk2⟩, hEq⟩) |
          ⟨h, ⟨hh1, _⟩, k, ⟨hk1, hk2⟩, hEq⟩) <;>
        cases hEq <;> refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hD_sum : ∑ p ∈ D, F p.1 p.2 = ∑ n ∈ Finset.Ico a b, F n n := by
    dsimp only [D]
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact (Prod.mk.inj hxy).1
  have hU_sum : ∑ p ∈ U, F p.1 p.2 =
      ∑ h ∈ Finset.Icc 1 (b - a), ∑ n ∈ Finset.Ico a (b - h), F (n + h) n := by
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.sum_image]
      intro x _ y _ hxy
      exact (Prod.mk.inj hxy).2
    · intro h₁ _ h₂ _ hne
      exact Finset.disjoint_left.mpr fun p hp₁ hp₂ => by
        rcases Finset.mem_image.mp hp₁ with ⟨n₁, _, hn₁⟩
        rcases Finset.mem_image.mp hp₂ with ⟨n₂, _, hn₂⟩
        have hf := congrArg Prod.fst (hn₁.trans hn₂.symm)
        have hs := congrArg Prod.snd (hn₁.trans hn₂.symm)
        dsimp at hf hs
        exact hne (by omega)
  have hL_sum : ∑ p ∈ L, F p.1 p.2 =
      ∑ h ∈ Finset.Icc 1 (b - a), ∑ n ∈ Finset.Ico a (b - h), F n (n + h) := by
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.sum_image]
      intro x _ y _ hxy
      exact (Prod.mk.inj hxy).1
    · intro h₁ _ h₂ _ hne
      exact Finset.disjoint_left.mpr fun p hp₁ hp₂ => by
        rcases Finset.mem_image.mp hp₁ with ⟨n₁, _, hn₁⟩
        rcases Finset.mem_image.mp hp₂ with ⟨n₂, _, hn₂⟩
        have hf := congrArg Prod.fst (hn₁.trans hn₂.symm)
        have hs := congrArg Prod.snd (hn₁.trans hn₂.symm)
        dsimp at hf hs
        exact hne (by omega)
  rw [hAll, Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hDL, hUL⟩),
    Finset.sum_union hDU, hD_sum, hU_sum, hL_sum, add_assoc, ← Finset.sum_add_distrib]
  refine congrArg (∑ n ∈ Finset.Ico a b, F n n + ·) (Finset.sum_congr rfl fun h _ => ?_)
  rw [← Finset.sum_add_distrib]

/-- Exact complex sum squaring identity (for arbitrary `z : ℕ → ℂ` and `a ≤ b`):
`‖∑_{n ∈ Ico a b} z(n)‖² = ∑_{n ∈ Ico a b} ‖z(n)‖² + 2 ∑_{h=1}^{b-a} ∑_{n ∈ Ico a (b-h)} Re(z(n+h) conj(z(n)))`. -/
theorem normSq_sum_Ico_eq_re_diag_offdiag (z : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ‖∑ n ∈ Finset.Ico a b, z n‖ ^ 2 =
      (∑ n ∈ Finset.Ico a b, ‖z n‖ ^ 2) +
        2 * ∑ h ∈ Finset.Icc 1 (b - a),
          ∑ n ∈ Finset.Ico a (b - h), (z (n + h) * star (z n)).re := by
  set S : ℂ := ∑ n ∈ Finset.Ico a b, z n
  have hsq : ‖S‖ ^ 2 = (S * star S).re := by
    have hm := Complex.mul_conj S
    have hre := congrArg Complex.re hm
    rw [Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hre
    exact hre.symm
  have hprod : S * star S = ∑ m ∈ Finset.Ico a b, ∑ n ∈ Finset.Ico a b, z m * star (z n) := by
    dsimp only [S]
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
  rw [hsq, hprod, Complex.re_sum]
  simp_rw [Complex.re_sum]
  rw [sum_Ico_prod_split (fun m n => (z m * star (z n)).re) hab]
  congr 1
  · refine Finset.sum_congr rfl fun n _ => ?_
    have hm := Complex.mul_conj (z n)
    have hre := congrArg Complex.re hm
    rw [Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hre
    exact hre
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hconj : (z n * star (z (n + h))).re = (z (n + h) * star (z n)).re := by
      rw [← Complex.conj_re (z (n + h) * star (z n))]
      simp [mul_comm]
    rw [hconj]
    ring

/-- **Weyl Differencing Inequality (General `ℂ` Unit-Disk Sequence)**:
For `a ≤ b` and `‖z n‖ ≤ 1` on `Ico a b`,
`‖∑_{n ∈ Ico a b} z(n)‖² ≤ (b - a) + 2 ∑_{h=1}^{b-a} ‖∑_{n ∈ Ico a (b-h)} z(n+h) conj(z(n))‖`. -/
theorem weyl_differencing_Ico (z : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b)
    (hz : ∀ n ∈ Finset.Ico a b, ‖z n‖ ≤ 1) :
    ‖∑ n ∈ Finset.Ico a b, z n‖ ^ 2 ≤
      ((b : ℝ) - (a : ℝ)) +
        2 * ∑ h ∈ Finset.Icc 1 (b - a),
          ‖∑ n ∈ Finset.Ico a (b - h), z (n + h) * star (z n)‖ := by
  rw [normSq_sum_Ico_eq_re_diag_offdiag z hab]
  have hdiag : ∑ n ∈ Finset.Ico a b, ‖z n‖ ^ 2 ≤ (b : ℝ) - (a : ℝ) := by
    calc
      ∑ n ∈ Finset.Ico a b, ‖z n‖ ^ 2
        ≤ ∑ _n ∈ Finset.Ico a b, (1 : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have h1 : ‖z n‖ ≤ 1 := hz n hn
          nlinarith [norm_nonneg (z n)]
      _ = ((Finset.Ico a b).card : ℝ) := by simp
      _ = (b : ℝ) - (a : ℝ) := by rw [Nat.card_Ico, Nat.cast_sub hab]
  have hoff :
      ∑ h ∈ Finset.Icc 1 (b - a), ∑ n ∈ Finset.Ico a (b - h), (z (n + h) * star (z n)).re ≤
        ∑ h ∈ Finset.Icc 1 (b - a), ‖∑ n ∈ Finset.Ico a (b - h), z (n + h) * star (z n)‖ := by
    refine Finset.sum_le_sum fun h _ => ?_
    rw [← Complex.re_sum]
    exact Complex.re_le_norm _
  linarith

/-- **Weyl Differencing Inequality for Exponential Sums** `e(f n)` over `Finset.Ico a b`:
`‖∑_{n ∈ Ico a b} e(f n)‖² ≤ (b - a) + 2 ∑_{h=1}^{b-a} ‖∑_{n ∈ Ico a (b-h)} e(f(n+h) - f(n))‖`. -/
theorem weyl_differencing_exp_Ico (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ‖∑ n ∈ Finset.Ico a b, e (f n)‖ ^ 2 ≤
      ((b : ℝ) - (a : ℝ)) +
        2 * ∑ h ∈ Finset.Icc 1 (b - a),
          ‖∑ n ∈ Finset.Ico a (b - h), e (f (n + h) - f n)‖ := by
  have h := weyl_differencing_Ico (fun n => e (f n)) hab (fun _ _ => (norm_e _).le)
  simpa only [e_mul_star_e] using h

/-- **Weyl Differencing Inequality for Exponential Sums** `e(f n)` over `Finset.Icc a b` (`a ≤ b`). -/
theorem weyl_differencing_exp_Icc (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ‖∑ n ∈ Finset.Icc a b, e (f n)‖ ^ 2 ≤
      ((b : ℝ) - (a : ℝ) + 1) +
        2 * ∑ h ∈ Finset.Icc 1 (b - a),
          ‖∑ n ∈ Finset.Icc a (b - h), e (f (n + h) - f n)‖ := by
  have hIcc : Finset.Icc a b = Finset.Ico a (b + 1) := rfl
  rw [hIcc]
  have h := weyl_differencing_exp_Ico f (Nat.le_succ_of_le hab)
  have hcast : ((b + 1 : ℕ) : ℝ) - (a : ℝ) = (b : ℝ) - (a : ℝ) + 1 := by push_cast; ring
  rw [hcast] at h
  have hsplit_sum :
      ∑ h ∈ Finset.Icc 1 (b + 1 - a), ‖∑ n ∈ Finset.Ico a (b + 1 - h), e (f (n + h) - f n)‖ =
        ∑ h ∈ Finset.Icc 1 (b - a), ‖∑ n ∈ Finset.Icc a (b - h), e (f (n + h) - f n)‖ := by
    have hIcc_ins : Finset.Icc 1 (b + 1 - a) = insert (b + 1 - a) (Finset.Icc 1 (b - a)) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnot : b + 1 - a ∉ Finset.Icc 1 (b - a) := by
      simp only [Finset.mem_Icc]; omega
    rw [hIcc_ins, Finset.sum_insert hnot]
    have hzero : Finset.Ico a (b + 1 - (b + 1 - a)) = ∅ := by
      apply Finset.Ico_eq_empty_of_le; omega
    rw [hzero, Finset.sum_empty, norm_zero, zero_add]
    refine Finset.sum_congr rfl fun h hh => ?_
    have hh_mem := Finset.mem_Icc.mp hh
    refine congrArg norm (Finset.sum_congr ?_ fun _ _ => rfl)
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hsplit_sum] at h
  exact h

private lemma sum_Ico_shift_eq (z : ℕ → ℂ) (a b H h : ℕ) (_hab : a ≤ b) (hh : h ∈ Finset.range H) :
    ∑ m ∈ Finset.Ico a (b + H), (if a + h ≤ m ∧ m < b + h then z (m - h) else 0) =
      ∑ n ∈ Finset.Ico a b, z n := by
  have hh_lt : h < H := Finset.mem_range.mp hh
  calc
    ∑ m ∈ Finset.Ico a (b + H), (if a + h ≤ m ∧ m < b + h then z (m - h) else 0)
      = ∑ m ∈ (Finset.Ico a (b + H)).filter (fun m => a + h ≤ m ∧ m < b + h), z (m - h) := by
          rw [Finset.sum_filter]
    _ = ∑ m ∈ Finset.Ico (a + h) (b + h), z (m - h) := by
          congr 1
          ext m
          simp only [Finset.mem_filter, Finset.mem_Ico]
          omega
    _ = ∑ n ∈ Finset.Ico a b, z n := by
          refine Finset.sum_bij' (fun m _ => m - h) (fun n _ => n + h)
            (fun m hm => ?_) (fun n hn => ?_) (fun m hm => ?_) (fun n hn => ?_)
            (fun _ _ => rfl)
          · simp only [Finset.mem_Ico] at hm ⊢; omega
          · simp only [Finset.mem_Ico] at hn ⊢; omega
          · simp only [Finset.mem_Ico] at hm; omega
          · simp only [Finset.mem_Ico] at hn; omega

private lemma sum_Ico_shift_pair_eq (z : ℕ → ℂ) (a b H h₁ h₂ : ℕ) (_hab : a ≤ b)
    (hh₁ : h₁ ∈ Finset.range H) (hh₂ : h₂ ∈ Finset.range H) :
    ∑ m ∈ Finset.Ico a (b + H),
        (if (a + h₁ ≤ m ∧ m < b + h₁) ∧ (a + h₂ ≤ m ∧ m < b + h₂) then
          (z (m - h₁) * star (z (m - h₂))).re else 0) =
      if h₂ ≤ h₁ then
        ∑ n ∈ Finset.Ico a (b - (h₁ - h₂)), (z n * star (z (n + (h₁ - h₂)))).re
      else
        ∑ n ∈ Finset.Ico a (b - (h₂ - h₁)), (z (n + (h₂ - h₁)) * star (z n)).re := by
  have hh₁_lt : h₁ < H := Finset.mem_range.mp hh₁
  have hh₂_lt : h₂ < H := Finset.mem_range.mp hh₂
  rw [← Finset.sum_filter (p := fun m => (a + h₁ ≤ m ∧ m < b + h₁) ∧ (a + h₂ ≤ m ∧ m < b + h₂))]
  split_ifs with hle
  · have hfilt : (Finset.Ico a (b + H)).filter
        (fun m => (a + h₁ ≤ m ∧ m < b + h₁) ∧ (a + h₂ ≤ m ∧ m < b + h₂)) =
        Finset.Ico (a + h₁) (b + h₂) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    rw [hfilt]
    refine Finset.sum_bij' (fun m _ => m - h₁) (fun n _ => n + h₁)
      (fun m hm => ?_) (fun n hn => ?_) (fun m hm => ?_) (fun n hn => ?_)
      (fun m hm => ?_)
    · simp only [Finset.mem_Ico] at hm ⊢; omega
    · simp only [Finset.mem_Ico] at hn ⊢; omega
    · simp only [Finset.mem_Ico] at hm; omega
    · simp only [Finset.mem_Ico] at hn; omega
    · simp only [Finset.mem_Ico] at hm
      have hsub : m - h₂ = m - h₁ + (h₁ - h₂) := by omega
      rw [hsub]
  · have hfilt : (Finset.Ico a (b + H)).filter
        (fun m => (a + h₁ ≤ m ∧ m < b + h₁) ∧ (a + h₂ ≤ m ∧ m < b + h₂)) =
        Finset.Ico (a + h₂) (b + h₁) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    rw [hfilt]
    refine Finset.sum_bij' (fun m _ => m - h₂) (fun n _ => n + h₂)
      (fun m hm => ?_) (fun n hn => ?_) (fun m hm => ?_) (fun n hn => ?_)
      (fun m hm => ?_)
    · simp only [Finset.mem_Ico] at hm ⊢; omega
    · simp only [Finset.mem_Ico] at hn ⊢; omega
    · simp only [Finset.mem_Ico] at hm; omega
    · simp only [Finset.mem_Ico] at hn; omega
    · simp only [Finset.mem_Ico] at hm
      have hsub : m - h₁ = m - h₂ + (h₂ - h₁) := by omega
      rw [hsub]

/-- **Van der Corput `A`-Process (General `ℂ` Unit-Disk Sequence)**:
For any `a ≤ b`, any shift parameter `H ≥ 1`, and any `z : ℕ → ℂ` with `‖z n‖ ≤ 1` on `Ico a b`,
`‖∑_{n ∈ Ico a b} z(n)‖² ≤ ((N + H) / H) · (N + 2 ∑_{h=1}^{H-1} (1 - h / H) ‖∑_{n ∈ Ico a (b-h)} z(n+h) conj(z(n))‖)`
where `N = b - a`. -/
theorem van_der_corput_A_process_Ico (z : ℕ → ℂ) {a b H : ℕ} (hab : a ≤ b) (hH : 1 ≤ H)
    (hz : ∀ n ∈ Finset.Ico a b, ‖z n‖ ≤ 1) :
    ‖∑ n ∈ Finset.Ico a b, z n‖ ^ 2 ≤
      (((b : ℝ) - (a : ℝ) + (H : ℝ)) / (H : ℝ)) *
        (((b : ℝ) - (a : ℝ)) +
          2 * ∑ h ∈ Finset.Icc 1 (H - 1),
            (1 - (h : ℝ) / (H : ℝ)) *
              ‖∑ n ∈ Finset.Ico a (b - h), z (n + h) * star (z n)‖) := by
  set w : ℕ → ℂ := fun m =>
    ∑ h ∈ Finset.range H, if a + h ≤ m ∧ m < b + h then z (m - h) else 0
  have hw_sum : ∑ m ∈ Finset.Ico a (b + H), w m = (H : ℂ) * ∑ n ∈ Finset.Ico a b, z n := by
    dsimp only [w]
    rw [Finset.sum_comm]
    calc
      ∑ h ∈ Finset.range H, ∑ m ∈ Finset.Ico a (b + H),
          (if a + h ≤ m ∧ m < b + h then z (m - h) else 0)
        = ∑ _h ∈ Finset.range H, ∑ n ∈ Finset.Ico a b, z n := by
          refine Finset.sum_congr rfl fun h hh => sum_Ico_shift_eq z a b H h hab hh
      _ = (H : ℂ) * ∑ n ∈ Finset.Ico a b, z n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hH_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hcard : ((Finset.Ico a (b + H)).card : ℝ) = (b : ℝ) - (a : ℝ) + (H : ℝ) := by
    rw [Nat.card_Ico, Nat.cast_sub (by omega : a ≤ b + H), Nat.cast_add]
    ring
  have hcs : (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a b, z n‖ ^ 2 ≤
      ((b : ℝ) - (a : ℝ) + (H : ℝ)) * ∑ m ∈ Finset.Ico a (b + H), ‖w m‖ ^ 2 := by
    have hnorm : (H : ℝ) * ‖∑ n ∈ Finset.Ico a b, z n‖ = ‖∑ m ∈ Finset.Ico a (b + H), w m‖ := by
      rw [hw_sum, norm_mul, Complex.norm_natCast]
    have h1 : ‖∑ m ∈ Finset.Ico a (b + H), w m‖ ^ 2 ≤
        (∑ m ∈ Finset.Ico a (b + H), ‖w m‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    have h2 : (∑ m ∈ Finset.Ico a (b + H), ‖w m‖) ^ 2 ≤
        ((Finset.Ico a (b + H)).card : ℝ) * ∑ m ∈ Finset.Ico a (b + H), ‖w m‖ ^ 2 := by
      have hnn : 0 ≤ ∑ m ∈ Finset.Ico a (b + H), ∑ m' ∈ Finset.Ico a (b + H),
          (‖w m‖ - ‖w m'‖) ^ 2 :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hexp_sq :
          ∑ m ∈ Finset.Ico a (b + H), ∑ m' ∈ Finset.Ico a (b + H), (‖w m‖ - ‖w m'‖) ^ 2 =
            2 * ((Finset.Ico a (b + H)).card : ℝ) * (∑ m ∈ Finset.Ico a (b + H), ‖w m‖ ^ 2) -
              2 * (∑ m ∈ Finset.Ico a (b + H), ‖w m‖) ^ 2 := by
        have hterm : ∀ m m' : ℕ, (‖w m‖ - ‖w m'‖) ^ 2 =
            ‖w m‖ ^ 2 + ‖w m'‖ ^ 2 - 2 * (‖w m‖ * ‖w m'‖) := fun m m' => by ring
        simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
          nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
        ring
      linarith
    calc
      (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a b, z n‖ ^ 2
        = ((H : ℝ) * ‖∑ n ∈ Finset.Ico a b, z n‖) ^ 2 := by ring
      _ = ‖∑ m ∈ Finset.Ico a (b + H), w m‖ ^ 2 := by rw [hnorm]
      _ ≤ ((Finset.Ico a (b + H)).card : ℝ) * ∑ m ∈ Finset.Ico a (b + H), ‖w m‖ ^ 2 :=
          h1.trans h2
      _ = ((b : ℝ) - (a : ℝ) + (H : ℝ)) * ∑ m ∈ Finset.Ico a (b + H), ‖w m‖ ^ 2 := by rw [hcard]
  have hexp : ∑ m ∈ Finset.Ico a (b + H), ‖w m‖ ^ 2 =
      ∑ h₁ ∈ Finset.range H, ∑ h₂ ∈ Finset.range H,
        ∑ m ∈ Finset.Ico a (b + H),
          if (a + h₁ ≤ m ∧ m < b + h₁) ∧ (a + h₂ ≤ m ∧ m < b + h₂) then
            (z (m - h₁) * star (z (m - h₂))).re else 0 := by
    have hm_eq : ∀ m : ℕ, ‖w m‖ ^ 2 =
        ∑ h₁ ∈ Finset.range H, ∑ h₂ ∈ Finset.range H,
          if (a + h₁ ≤ m ∧ m < b + h₁) ∧ (a + h₂ ≤ m ∧ m < b + h₂) then
            (z (m - h₁) * star (z (m - h₂))).re else 0 := by
      intro m
      have hsq : ‖w m‖ ^ 2 = (w m * star (w m)).re := by
        have hm := Complex.mul_conj (w m)
        have hre := congrArg Complex.re hm
        rw [Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hre
        exact hre.symm
      rw [hsq]
      dsimp only [w]
      rw [star_sum, Finset.sum_mul, Complex.re_sum]
      refine Finset.sum_congr rfl fun h₁ _ => ?_
      rw [Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun h₂ _ => ?_
      split_ifs <;> simp_all
    simp_rw [hm_eq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h₁ _ => Finset.sum_comm
  have hsplit : ∑ m ∈ Finset.Ico a (b + H), ‖w m‖ ^ 2 =
      (∑ h ∈ Finset.range H,
        ∑ m ∈ Finset.Ico a (b + H),
          if (a + h ≤ m ∧ m < b + h) ∧ (a + h ≤ m ∧ m < b + h) then
            (z (m - h) * star (z (m - h))).re else 0) +
      ∑ d ∈ Finset.Icc 1 H, ∑ h ∈ Finset.Ico 0 (H - d),
        ((∑ m ∈ Finset.Ico a (b + H),
            if (a + (h + d) ≤ m ∧ m < b + (h + d)) ∧ (a + h ≤ m ∧ m < b + h) then
              (z (m - (h + d)) * star (z (m - h))).re else 0) +
          ∑ m ∈ Finset.Ico a (b + H),
            if (a + h ≤ m ∧ m < b + h) ∧ (a + (h + d) ≤ m ∧ m < b + (h + d)) then
              (z (m - h) * star (z (m - (h + d)))).re else 0) := by
    rw [hexp, show Finset.range H = Finset.Ico 0 H by ext; simp]
    exact sum_Ico_prod_split (fun h₁ h₂ => ∑ m ∈ Finset.Ico a (b + H),
      if (a + h₁ ≤ m ∧ m < b + h₁) ∧ (a + h₂ ≤ m ∧ m < b + h₂) then
        (z (m - h₁) * star (z (m - h₂))).re else 0) (Nat.zero_le H)
  have hdiag_le : (∑ h ∈ Finset.range H,
      ∑ m ∈ Finset.Ico a (b + H),
        if (a + h ≤ m ∧ m < b + h) ∧ (a + h ≤ m ∧ m < b + h) then
          (z (m - h) * star (z (m - h))).re else 0) ≤ (H : ℝ) * ((b : ℝ) - (a : ℝ)) := by
    have hterm : ∀ h ∈ Finset.range H,
        (∑ m ∈ Finset.Ico a (b + H),
          if (a + h ≤ m ∧ m < b + h) ∧ (a + h ≤ m ∧ m < b + h) then
            (z (m - h) * star (z (m - h))).re else 0) ≤ (b : ℝ) - (a : ℝ) := by
      intro h hh
      rw [sum_Ico_shift_pair_eq z a b H h h hab hh hh]
      simp only [le_refl, ↓reduceIte, tsub_self]
      calc
        ∑ n ∈ Finset.Ico a b, (z n * star (z (n + 0))).re
          = ∑ n ∈ Finset.Ico a b, ‖z n‖ ^ 2 := by
            refine Finset.sum_congr rfl fun n _ => ?_
            simp only [add_zero]
            have hm := Complex.mul_conj (z n)
            have hre := congrArg Complex.re hm
            rw [Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hre
            exact hre
        _ ≤ ∑ _n ∈ Finset.Ico a b, (1 : ℝ) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have h1 := hz n hn
            nlinarith [norm_nonneg (z n)]
        _ = (b : ℝ) - (a : ℝ) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, Nat.cast_sub hab]
    calc
      ∑ h ∈ Finset.range H, _ ≤ ∑ _h ∈ Finset.range H, ((b : ℝ) - (a : ℝ)) :=
        Finset.sum_le_sum hterm
      _ = (H : ℝ) * ((b : ℝ) - (a : ℝ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hoff_le : (∑ d ∈ Finset.Icc 1 H, ∑ h ∈ Finset.Ico 0 (H - d),
      ((∑ m ∈ Finset.Ico a (b + H),
          if (a + (h + d) ≤ m ∧ m < b + (h + d)) ∧ (a + h ≤ m ∧ m < b + h) then
            (z (m - (h + d)) * star (z (m - h))).re else 0) +
        ∑ m ∈ Finset.Ico a (b + H),
          if (a + h ≤ m ∧ m < b + h) ∧ (a + (h + d) ≤ m ∧ m < b + (h + d)) then
            (z (m - h) * star (z (m - (h + d)))).re else 0)) ≤
      2 * ∑ d ∈ Finset.Icc 1 (H - 1),
        ((H : ℝ) - (d : ℝ)) * ‖∑ n ∈ Finset.Ico a (b - d), z (n + d) * star (z n)‖ := by
    have hIcc_split : Finset.Icc 1 H = insert H (Finset.Icc 1 (H - 1)) := by
      ext d; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hH_not : H ∉ Finset.Icc 1 (H - 1) := by
      simp only [Finset.mem_Icc]; omega
    rw [hIcc_split, Finset.sum_insert hH_not]
    simp only [Nat.sub_self, Finset.Ico_self, Finset.sum_empty, zero_add]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    simp only [Finset.mem_Icc] at hd
    have hd_le : d ≤ H := by omega
    have hpair : ∀ h ∈ Finset.Ico 0 (H - d),
        ((∑ m ∈ Finset.Ico a (b + H),
            if (a + (h + d) ≤ m ∧ m < b + (h + d)) ∧ (a + h ≤ m ∧ m < b + h) then
              (z (m - (h + d)) * star (z (m - h))).re else 0) +
          ∑ m ∈ Finset.Ico a (b + H),
            if (a + h ≤ m ∧ m < b + h) ∧ (a + (h + d) ≤ m ∧ m < b + (h + d)) then
              (z (m - h) * star (z (m - (h + d)))).re else 0) ≤
          2 * ‖∑ n ∈ Finset.Ico a (b - d), z (n + d) * star (z n)‖ := by
      intro h hh
      simp only [Finset.mem_Ico] at hh
      have hh_range : h ∈ Finset.range H := Finset.mem_range.mpr (by omega)
      have hhd_range : h + d ∈ Finset.range H := Finset.mem_range.mpr (by omega)
      rw [sum_Ico_shift_pair_eq z a b H (h + d) h hab hhd_range hh_range,
        sum_Ico_shift_pair_eq z a b H h (h + d) hab hh_range hhd_range]
      have hle1 : h ≤ h + d := Nat.le_add_right h d
      have hnot : ¬ (h + d ≤ h) := by omega
      simp only [hle1, ↓reduceIte, hnot, Nat.add_sub_cancel_left]
      have hconj : ∑ n ∈ Finset.Ico a (b - d), (z n * star (z (n + d))).re =
          ∑ n ∈ Finset.Ico a (b - d), (z (n + d) * star (z n)).re := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Complex.conj_re (z (n + d) * star (z n))]
        simp [mul_comm]
      rw [hconj, ← Complex.re_sum]
      have hre := Complex.re_le_norm (∑ n ∈ Finset.Ico a (b - d), z (n + d) * star (z n))
      linarith
    calc
      ∑ h ∈ Finset.Ico 0 (H - d), _
        ≤ ∑ _h ∈ Finset.Ico 0 (H - d),
            (2 * ‖∑ n ∈ Finset.Ico a (b - d), z (n + d) * star (z n)‖) :=
          Finset.sum_le_sum hpair
      _ = ((H - d : ℕ) : ℝ) * (2 * ‖∑ n ∈ Finset.Ico a (b - d), z (n + d) * star (z n)‖) := by
          rw [Finset.sum_const, Nat.card_Ico, tsub_zero, nsmul_eq_mul]
      _ = 2 * (((H : ℝ) - (d : ℝ)) * ‖∑ n ∈ Finset.Ico a (b - d), z (n + d) * star (z n)‖) := by
          rw [Nat.cast_sub hd_le]; ring
  have hsum_wm : ∑ m ∈ Finset.Ico a (b + H), ‖w m‖ ^ 2 ≤
      (H : ℝ) * ((b : ℝ) - (a : ℝ)) +
        2 * ∑ d ∈ Finset.Icc 1 (H - 1),
          ((H : ℝ) - (d : ℝ)) * ‖∑ n ∈ Finset.Ico a (b - d), z (n + d) * star (z n)‖ := by
    rw [hsplit]
    exact add_le_add hdiag_le hoff_le
  have hba_nn : (0 : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    linarith
  have hdiv_sq : (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a b, z n‖ ^ 2 ≤
      ((b : ℝ) - (a : ℝ) + (H : ℝ)) *
        ((H : ℝ) * ((b : ℝ) - (a : ℝ)) +
          2 * ∑ d ∈ Finset.Icc 1 (H - 1),
            ((H : ℝ) - (d : ℝ)) * ‖∑ n ∈ Finset.Ico a (b - d), z (n + d) * star (z n)‖) :=
    hcs.trans (mul_le_mul_of_nonneg_left hsum_wm (by linarith))
  rw [← le_div_iff₀' (pow_pos hH_pos 2)] at hdiv_sq
  refine hdiv_sq.trans_eq ?_
  have hrew : ∑ d ∈ Finset.Icc 1 (H - 1),
      (1 - (d : ℝ) / (H : ℝ)) * ‖∑ n ∈ Finset.Ico a (b - d), z (n + d) * star (z n)‖ =
      (1 / (H : ℝ)) * ∑ d ∈ Finset.Icc 1 (H - 1),
        ((H : ℝ) - (d : ℝ)) * ‖∑ n ∈ Finset.Ico a (b - d), z (n + d) * star (z n)‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    field_simp [hH_pos.ne']
  rw [hrew]
  field_simp [hH_pos.ne']

/-- **Van der Corput `A`-Process for Exponential Sums** `e(f n)` over `Finset.Ico a b`:
`‖∑_{n ∈ Ico a b} e(f n)‖² ≤ ((N + H) / H) · (N + 2 ∑_{h=1}^{H-1} (1 - h / H) ‖∑_{n ∈ Ico a (b-h)} e(f(n+h) - f(n))‖)`. -/
theorem van_der_corput_A_process_exp_Ico (f : ℕ → ℝ) {a b H : ℕ} (hab : a ≤ b) (hH : 1 ≤ H) :
    ‖∑ n ∈ Finset.Ico a b, e (f n)‖ ^ 2 ≤
      (((b : ℝ) - (a : ℝ) + (H : ℝ)) / (H : ℝ)) *
        (((b : ℝ) - (a : ℝ)) +
          2 * ∑ h ∈ Finset.Icc 1 (H - 1),
            (1 - (h : ℝ) / (H : ℝ)) *
              ‖∑ n ∈ Finset.Ico a (b - h), e (f (n + h) - f n)‖) := by
  have h := van_der_corput_A_process_Ico (fun n => e (f n)) hab hH (fun _ _ => (norm_e _).le)
  simpa only [e_mul_star_e] using h

/-- Unweighted Van der Corput `A`-Process corollary for `e(f n)` over `Finset.Ico a b`. -/
theorem van_der_corput_A_process_exp_unweighted (f : ℕ → ℝ) {a b H : ℕ}
    (hab : a ≤ b) (hH : 1 ≤ H) :
    ‖∑ n ∈ Finset.Ico a b, e (f n)‖ ^ 2 ≤
      (((b : ℝ) - (a : ℝ) + (H : ℝ)) / (H : ℝ)) *
        (((b : ℝ) - (a : ℝ)) +
          2 * ∑ h ∈ Finset.Icc 1 (H - 1),
            ‖∑ n ∈ Finset.Ico a (b - h), e (f (n + h) - f n)‖) := by
  have h := van_der_corput_A_process_exp_Ico f hab hH
  have hH_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hfac_nn : 0 ≤ ((b : ℝ) - (a : ℝ) + (H : ℝ)) / (H : ℝ) := by
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    positivity
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hfac_nn)
  have hsum_le :
      ∑ h ∈ Finset.Icc 1 (H - 1),
          (1 - (h : ℝ) / (H : ℝ)) * ‖∑ n ∈ Finset.Ico a (b - h), e (f (n + h) - f n)‖ ≤
        ∑ h ∈ Finset.Icc 1 (H - 1), ‖∑ n ∈ Finset.Ico a (b - h), e (f (n + h) - f n)‖ := by
    refine Finset.sum_le_sum fun d _ => ?_
    have hd_nn : (0 : ℝ) ≤ (d : ℝ) / (H : ℝ) := by positivity
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  linarith

/-- **Quadratic Weyl Differencing Bound**: for `f(n) = α n² + β n + γ` and `h ≥ 1`,
`‖∑_{n ∈ Ico a (b - h)} e(f(n + h) - f(n))‖ ≤ min (b - a) (1 / |sin(2π α h)|)`
whenever `sin(2π α h) ≠ 0`. -/
theorem weyl_quadratic_diff_bound (α β γ : ℝ) {a b h : ℕ} (hab : a ≤ b)
    (hsin : Real.sin (Real.pi * (2 * α * (h : ℝ))) ≠ 0) :
    ‖∑ n ∈ Finset.Ico a (b - h),
        e (α * ((n + h : ℕ) : ℝ) ^ 2 + β * ((n + h : ℕ) : ℝ) + γ -
            (α * (n : ℝ) ^ 2 + β * (n : ℝ) + γ))‖ ≤
      min ((b : ℝ) - (a : ℝ)) (1 / |Real.sin (Real.pi * (2 * α * (h : ℝ)))|) := by
  have hconst :
      ‖∑ n ∈ Finset.Ico a (b - h),
          e (α * ((n + h : ℕ) : ℝ) ^ 2 + β * ((n + h : ℕ) : ℝ) + γ -
              (α * (n : ℝ) ^ 2 + β * (n : ℝ) + γ))‖ =
        ‖∑ n ∈ Finset.Ico a (b - h), e (2 * α * (h : ℝ) * (n : ℝ))‖ := by
    have hsum :
        ∑ n ∈ Finset.Ico a (b - h),
            e (α * ((n + h : ℕ) : ℝ) ^ 2 + β * ((n + h : ℕ) : ℝ) + γ -
                (α * (n : ℝ) ^ 2 + β * (n : ℝ) + γ)) =
          e (α * (h : ℝ) ^ 2 + β * (h : ℝ)) *
            ∑ n ∈ Finset.Ico a (b - h), e (2 * α * (h : ℝ) * (n : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← e_add]
      congr 1
      push_cast
      ring
    rw [hsum, norm_mul, norm_e, one_mul]
  rw [hconst]
  by_cases ha : a ≤ b - h
  · have hlin := norm_sum_e_linear_Ico_le (2 * α * (h : ℝ)) ha hsin
    refine hlin.trans (min_le_min ?_ le_rfl)
    have h1 : ((b - h : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast Nat.sub_le b h
    linarith
  · have hEmpty : Finset.Ico a (b - h) = ∅ := Finset.Ico_eq_empty_of_le (Nat.le_of_not_ge ha)
    rw [hEmpty, Finset.sum_empty, norm_zero]
    refine le_min ?_ (by positivity)
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    linarith

/-! ## Section 4: Dirichlet & Fejér Kernel Exact Identities & Positivity / `L¹` Bounds -/

/-- The Dirichlet kernel `D_N(θ) = 1 + 2 ∑_{k=1}^N cos(k θ)`. -/
def dirichletKernel (N : ℕ) (θ : ℝ) : ℝ :=
  1 + 2 * ∑ k ∈ Finset.Icc 1 N, Real.cos ((k : ℝ) * θ)

@[simp] theorem dirichletKernel_zero_order (θ : ℝ) : dirichletKernel 0 θ = 1 := by
  simp [dirichletKernel]

@[simp] theorem dirichletKernel_at_zero (N : ℕ) : dirichletKernel N 0 = 2 * (N : ℝ) + 1 := by
  simp [dirichletKernel]
  ring

theorem dirichletKernel_neg (N : ℕ) (θ : ℝ) : dirichletKernel N (-θ) = dirichletKernel N θ := by
  simp [dirichletKernel, mul_neg, Real.cos_neg]

theorem dirichletKernel_add_two_pi (N : ℕ) (θ : ℝ) :
    dirichletKernel N (θ + 2 * Real.pi) = dirichletKernel N θ := by
  simp only [dirichletKernel]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (k : ℝ) * (θ + 2 * Real.pi) = (k : ℝ) * θ + (k : ℝ) * (2 * Real.pi) by ring]
  exact Real.cos_add_nat_mul_two_pi ((k : ℝ) * θ) k

/-- Complex exponential representation of the Dirichlet kernel:
`(D_N(θ) : ℂ) = ∑_{k=-N}^N exp(i k θ)`. -/
theorem dirichletKernel_eq_sum_cexp (N : ℕ) (θ : ℝ) :
    (dirichletKernel N θ : ℂ) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Complex.exp (((k : ℝ) * θ : ℝ) * Complex.I) := by
  induction N with
  | zero =>
    simp [dirichletKernel]
  | succ N ih =>
    have hIcc_nat : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnot_nat : N + 1 ∉ Finset.Icc 1 N := by simp
    have hIcc_int : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N + 1 : ℕ) : ℤ))
          (insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
      ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnot1 : -((N + 1 : ℕ) : ℤ) ∉
        insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnot2 : ((N + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    have hcos_pair :
        Complex.exp ((((-((N + 1 : ℕ) : ℤ) : ℤ) : ℝ) * θ : ℝ) * Complex.I) +
          Complex.exp (((((N + 1 : ℕ) : ℤ) : ℝ) * θ : ℝ) * Complex.I) =
          ((2 * Real.cos (((N + 1 : ℕ) : ℝ) * θ) : ℝ) : ℂ) := by
      have h1 : (((-((N + 1 : ℕ) : ℤ) : ℤ) : ℝ) * θ : ℝ) = -(((N + 1 : ℕ) : ℝ) * θ) := by
        push_cast; ring
      have h2 : ((((N + 1 : ℕ) : ℤ) : ℝ) * θ : ℝ) = ((N + 1 : ℕ) : ℝ) * θ := by
        push_cast; ring
      rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    have hD_step : dirichletKernel (N + 1) θ =
        dirichletKernel N θ + 2 * Real.cos (((N + 1 : ℕ) : ℝ) * θ) := by
      simp only [dirichletKernel, hIcc_nat, Finset.sum_insert hnot_nat]
      ring
    rw [hD_step, Complex.ofReal_add, ih, hIcc_int, Finset.sum_insert hnot1,
      Finset.sum_insert hnot2, ← add_assoc, hcos_pair, add_comm]

/-- Classical closed-form identity for the Dirichlet kernel:
`D_N(θ) = sin((N + 1/2) θ) / sin(θ / 2)` whenever `sin(θ / 2) ≠ 0`. -/
theorem dirichletKernel_eq_sin_div_sin (N : ℕ) {θ : ℝ} (hsin : Real.sin (θ / 2) ≠ 0) :
    dirichletKernel N θ = Real.sin (((N : ℝ) + 1 / 2) * θ) / Real.sin (θ / 2) := by
  have hdiff : ∀ M : ℕ,
      (Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((-(θ / 2) : ℝ) : ℂ) * Complex.I)) *
        (dirichletKernel M θ : ℂ) =
      Complex.exp (((((M : ℝ) + 1 / 2) * θ : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-(((M : ℝ) + 1 / 2) * θ) : ℝ) : ℂ) * Complex.I) := by
    intro M
    rw [dirichletKernel_eq_sum_cexp]
    induction M with
    | zero =>
      simp only [Nat.cast_zero, zero_add]
      have h0 : Finset.Icc (-(0 : ℤ)) (0 : ℤ) = {0} := by decide
      rw [h0, Finset.sum_singleton]
      simp only [Int.cast_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one]
      congr 2 <;> push_cast <;> ring
    | succ M ih =>
      have hIcc_int : Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
          insert (-((M + 1 : ℕ) : ℤ))
            (insert ((M + 1 : ℕ) : ℤ) (Finset.Icc (-(M : ℤ)) (M : ℤ))) := by
        ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      have hnot1 : -((M + 1 : ℕ) : ℤ) ∉
          insert ((M + 1 : ℕ) : ℤ) (Finset.Icc (-(M : ℤ)) (M : ℤ)) := by
        simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      have hnot2 : ((M + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
        simp only [Finset.mem_Icc]; omega
      rw [hIcc_int, Finset.sum_insert hnot1, Finset.sum_insert hnot2, mul_add, mul_add, ih]
      have ha :
          (Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) -
              Complex.exp (((-(θ / 2) : ℝ) : ℂ) * Complex.I)) *
            Complex.exp (((((-((M + 1 : ℕ) : ℤ) : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((-(((M : ℝ) + 1 / 2) * θ) : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((-((((M + 1 : ℕ) : ℝ) + 1 / 2) * θ) : ℝ) : ℂ) * Complex.I) := by
        rw [sub_mul, ← Complex.exp_add, ← Complex.exp_add]
        congr 1 <;> congr 1 <;> push_cast <;> ring
      have hb :
          (Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) -
              Complex.exp (((-(θ / 2) : ℝ) : ℂ) * Complex.I)) *
            Complex.exp ((((((M + 1 : ℕ) : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((((((M + 1 : ℕ) : ℝ) + 1 / 2) * θ : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((((M : ℝ) + 1 / 2) * θ : ℝ) : ℂ) * Complex.I) := by
        rw [sub_mul, ← Complex.exp_add, ← Complex.exp_add]
        congr 1 <;> congr 1 <;> push_cast <;> ring
      rw [ha, hb]
      ring
  have hm := hdiff N
  have hLHS :
      Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((-(θ / 2) : ℝ) : ℂ) * Complex.I) =
        ((2 * Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hRHS :
      Complex.exp (((((N : ℝ) + 1 / 2) * θ : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((-(((N : ℝ) + 1 / 2) * θ) : ℝ) : ℂ) * Complex.I) =
        ((2 * Real.sin (((N : ℝ) + 1 / 2) * θ) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hLHS, hRHS] at hm
  have him := congrArg Complex.im hm
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero, zero_add] at him
  rw [eq_div_iff hsin]
  linarith

private lemma integral_cos_nat_mul_two_pi {k : ℕ} (hk : 1 ≤ k) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos ((k : ℝ) * θ) = 0 := by
  have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hd : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt (fun t => Real.sin ((k : ℝ) * t) / (k : ℝ)) (Real.cos ((k : ℝ) * θ)) θ := by
    intro θ _
    have h1 : HasDerivAt (fun t => (k : ℝ) * t) (k : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (k : ℝ)
    have h2 := (Real.hasDerivAt_sin ((k : ℝ) * θ)).comp θ h1
    have h3 := h2.div_const (k : ℝ)
    have h4 : Real.cos ((k : ℝ) * θ) * (k : ℝ) / (k : ℝ) = Real.cos ((k : ℝ) * θ) := by
      field_simp [hk_ne]
    simpa [Function.comp_def, h4] using h3
  have hc : Continuous (fun t : ℝ => Real.cos ((k : ℝ) * t)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 (2 * Real.pi))]
  have h2pi : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
    rw [show (k : ℝ) * (2 * Real.pi) = 0 + k * (2 * Real.pi) by ring]
    simpa using Real.sin_add_nat_mul_two_pi 0 k
  simp [h2pi]

/-- Integral normalization of the Dirichlet kernel:
`(1 / (2π)) ∫_0^{2π} D_N(θ) dθ = 1`. -/
theorem integral_dirichletKernel (N : ℕ) :
    (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), dirichletKernel N θ = 1 := by
  simp only [dirichletKernel]
  have hint_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 (2 * Real.pi) :=
    intervalIntegrable_const
  have hint_sum : IntervalIntegrable
      (fun θ : ℝ => 2 * ∑ k ∈ Finset.Icc 1 N, Real.cos ((k : ℝ) * θ)) volume 0 (2 * Real.pi) := by
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop
  rw [intervalIntegral.integral_add hint_const hint_sum, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (s := Finset.Icc 1 N)
      (f := fun k θ => Real.cos ((k : ℝ) * θ))
      (fun k _ => (by fun_prop : Continuous fun θ : ℝ => Real.cos ((k : ℝ) * θ)).intervalIntegrable
        0 (2 * Real.pi))]
  have hzeros : ∑ k ∈ Finset.Icc 1 N, ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos ((k : ℝ) * θ) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    exact integral_cos_nat_mul_two_pi (Finset.mem_Icc.mp hk).1
  rw [hzeros, mul_zero, add_zero, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  field_simp [Real.pi_ne_zero]

/-- The Fejér kernel `K_N(θ) = (1 / N) ∑_{m=0}^{N-1} D_m(θ)` (for `N ≥ 1`, and `0` for `N = 0`). -/
def fejerKernel (N : ℕ) (θ : ℝ) : ℝ :=
  if N = 0 then 0 else (1 / (N : ℝ)) * ∑ m ∈ Finset.range N, dirichletKernel m θ

@[simp] theorem fejerKernel_at_zero {N : ℕ} (hN : 1 ≤ N) : fejerKernel N 0 = (N : ℝ) := by
  have hN0 : N ≠ 0 := by omega
  simp only [fejerKernel, hN0, ↓reduceIte, dirichletKernel_at_zero]
  have hsum : ∑ m ∈ Finset.range N, (2 * (m : ℝ) + 1) = (N : ℝ) ^ 2 := by
    clear hN hN0
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  rw [hsum]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
  field_simp [hNr]

theorem fejerKernel_neg (N : ℕ) (θ : ℝ) : fejerKernel N (-θ) = fejerKernel N θ := by
  by_cases hN : N = 0
  · simp [fejerKernel, hN]
  · simp only [fejerKernel, hN, ↓reduceIte, dirichletKernel_neg]

theorem fejerKernel_add_two_pi (N : ℕ) (θ : ℝ) :
    fejerKernel N (θ + 2 * Real.pi) = fejerKernel N θ := by
  by_cases hN : N = 0
  · simp [fejerKernel, hN]
  · simp only [fejerKernel, hN, ↓reduceIte, dirichletKernel_add_two_pi]

/-- Exact cosine-polynomial representation of the Fejér kernel (`1 ≤ N`):
`K_N(θ) = 1 + 2 ∑_{k=1}^{N-1} (1 - k / N) cos(k θ)`. -/
theorem fejerKernel_eq_sum_cos {N : ℕ} (hN : 1 ≤ N) (θ : ℝ) :
    fejerKernel N θ =
      1 + 2 * ∑ k ∈ Finset.Icc 1 (N - 1), (1 - (k : ℝ) / (N : ℝ)) * Real.cos ((k : ℝ) * θ) := by
  have hN0 : N ≠ 0 := by omega
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
  have hsum : ∑ m ∈ Finset.range N, dirichletKernel m θ =
      (N : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - (k : ℝ)) * Real.cos ((k : ℝ) * θ) := by
    clear hN0 hNr
    induction N, hN using Nat.le_induction with
    | base =>
      simp [dirichletKernel]
    | succ N hN ih =>
      rw [Finset.sum_range_succ, ih]
      have hD : dirichletKernel N θ = 1 + 2 * ∑ k ∈ Finset.Icc 1 N, Real.cos ((k : ℝ) * θ) := rfl
      rw [hD]
      have hIcc1 : Finset.Icc 1 N = insert N (Finset.Icc 1 (N - 1)) := by
        ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      have hnot : N ∉ Finset.Icc 1 (N - 1) := by
        simp only [Finset.mem_Icc]; omega
      have hsub_add : ∀ k ∈ Finset.Icc 1 (N - 1),
          ((N : ℝ) - (k : ℝ)) * Real.cos ((k : ℝ) * θ) + Real.cos ((k : ℝ) * θ) =
            ((N : ℝ) + 1 - (k : ℝ)) * Real.cos ((k : ℝ) * θ) := by
        intro k _
        ring
      have hN_term : ((N : ℝ) + 1 - (N : ℝ)) * Real.cos ((N : ℝ) * θ) =
          Real.cos ((N : ℝ) * θ) := by ring
      simp only [Nat.add_sub_cancel]
      have hcomb : ∑ k ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - (k : ℝ)) * Real.cos ((k : ℝ) * θ) +
          ∑ k ∈ Finset.Icc 1 N, Real.cos ((k : ℝ) * θ) =
          ∑ k ∈ Finset.Icc 1 N, ((N : ℝ) + 1 - (k : ℝ)) * Real.cos ((k : ℝ) * θ) := by
        rw [hIcc1, Finset.sum_insert hnot, Finset.sum_insert hnot, hN_term]
        have hsum_eq :
            ∑ k ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - (k : ℝ)) * Real.cos ((k : ℝ) * θ) +
              ∑ k ∈ Finset.Icc 1 (N - 1), Real.cos ((k : ℝ) * θ) =
              ∑ k ∈ Finset.Icc 1 (N - 1),
                ((N : ℝ) + 1 - (k : ℝ)) * Real.cos ((k : ℝ) * θ) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl hsub_add
        linarith
      push_cast
      linarith
  simp only [fejerKernel, hN0, ↓reduceIte, hsum]
  have hdiv : (1 / (N : ℝ)) * (2 * ∑ k ∈ Finset.Icc 1 (N - 1),
        ((N : ℝ) - (k : ℝ)) * Real.cos ((k : ℝ) * θ)) =
      2 * ∑ k ∈ Finset.Icc 1 (N - 1), (1 - (k : ℝ) / (N : ℝ)) * Real.cos ((k : ℝ) * θ) := by
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp [hNr]
  rw [mul_add, one_div_mul_cancel hNr, hdiv]

/-- **Fundamental Fejér Kernel Positivity Identity** (`1 ≤ N`):
`K_N(θ) = (1 / N) ‖∑_{m=0}^{N-1} exp(i m θ)‖²`. -/
theorem fejerKernel_eq_normSq_exp_sum {N : ℕ} (hN : 1 ≤ N) (θ : ℝ) :
    fejerKernel N θ =
      (1 / (N : ℝ)) * ‖∑ m ∈ Finset.range N, Complex.exp (((m : ℝ) * θ : ℝ) * Complex.I)‖ ^ 2 := by
  have hN0 : N ≠ 0 := by omega
  simp only [fejerKernel, hN0, ↓reduceIte]
  congr 1
  clear hN0
  induction N, hN using Nat.le_induction with
  | base =>
    simp [dirichletKernel]
  | succ N hN ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    set S : ℂ := ∑ m ∈ Finset.range N, Complex.exp (((m : ℝ) * θ : ℝ) * Complex.I)
    set w : ℂ := Complex.exp (((N : ℝ) * θ : ℝ) * Complex.I)
    have hnorm_w : ‖w‖ ^ 2 = 1 := by
      dsimp only [w]
      rw [Complex.norm_exp_ofReal_mul_I]
      norm_num
    have hexp_sq : ‖S + w‖ ^ 2 = ‖S‖ ^ 2 + 2 * (S * star w).re + ‖w‖ ^ 2 := by
      have hm1 : ‖S + w‖ ^ 2 = ((S + w) * star (S + w)).re := by
        have hm := Complex.mul_conj (S + w)
        have hre := congrArg Complex.re hm
        rw [Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hre
        exact hre.symm
      have hmS : ‖S‖ ^ 2 = (S * star S).re := by
        have hm := Complex.mul_conj S
        have hre := congrArg Complex.re hm
        rw [Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hre
        exact hre.symm
      have hmw : ‖w‖ ^ 2 = (w * star w).re := by
        have hm := Complex.mul_conj w
        have hre := congrArg Complex.re hm
        rw [Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hre
        exact hre.symm
      have hconj : (w * star S).re = (S * star w).re := by
        rw [← Complex.conj_re (S * star w)]
        simp [mul_comm]
      rw [hm1, hmS, hmw]
      simp only [star_add, mul_add, add_mul, Complex.add_re]
      linarith
    have hre_Sw : (S * star w).re = ∑ k ∈ Finset.Icc 1 N, Real.cos ((k : ℝ) * θ) := by
      dsimp only [S, w]
      rw [Finset.sum_mul, Complex.re_sum]
      have hbij : ∑ m ∈ Finset.range N,
          (Complex.exp (((m : ℝ) * θ : ℝ) * Complex.I) *
            star (Complex.exp (((N : ℝ) * θ : ℝ) * Complex.I))).re =
          ∑ k ∈ Finset.Icc 1 N, Real.cos ((k : ℝ) * θ) := by
        refine Finset.sum_bij' (fun m _ => N - m) (fun k _ => N - k)
          (fun m hm => ?_) (fun k hk => ?_) (fun m hm => ?_) (fun k hk => ?_)
          (fun m hm => ?_)
        · simp only [Finset.mem_range] at hm
          simp only [Finset.mem_Icc]
          omega
        · simp only [Finset.mem_Icc] at hk
          simp only [Finset.mem_range]
          omega
        · simp only [Finset.mem_range] at hm; omega
        · simp only [Finset.mem_Icc] at hk; omega
        · simp only [Finset.mem_range] at hm
          have hstar : star (Complex.exp (((N : ℝ) * θ : ℝ) * Complex.I)) =
              Complex.exp (((-(N : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
            rw [Complex.star_def, ← Complex.exp_conj]
            congr 1
            simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
            push_cast; ring
          rw [hstar, ← Complex.exp_add]
          have harg : ((((m : ℝ) * θ : ℝ) : ℂ) * Complex.I +
              ((-(N : ℝ) * θ : ℝ) : ℂ) * Complex.I) =
              (((-(((N - m : ℕ) : ℝ) * θ) : ℝ) : ℂ) * Complex.I) := by
            rw [Nat.cast_sub hm.le]
            push_cast
            ring
          rw [harg]
          have hre_cexp : ∀ r : ℝ, (Complex.exp ((r : ℂ) * Complex.I)).re = Real.cos r := by
            intro r
            rw [Complex.exp_re]
            simp
          rw [hre_cexp, Real.cos_neg]
      exact hbij
    have hD : dirichletKernel N θ = 1 + 2 * ∑ k ∈ Finset.Icc 1 N, Real.cos ((k : ℝ) * θ) := rfl
    rw [hexp_sq, hnorm_w, hre_Sw, hD]
    ring

/-- **Positivity of the Fejér kernel**: `0 ≤ K_N(θ)` for all `N : ℕ` and `θ : ℝ`. -/
theorem fejerKernel_nonneg (N : ℕ) (θ : ℝ) : 0 ≤ fejerKernel N θ := by
  by_cases hN : N = 0
  · simp [fejerKernel, hN]
  · rw [fejerKernel_eq_normSq_exp_sum (Nat.pos_of_ne_zero hN)]
    positivity

/-- Closed-form identity for the Fejér kernel (`1 ≤ N`, `sin(θ/2) ≠ 0`):
`K_N(θ) = (1 / N) * (sin(N θ / 2) / sin(θ / 2))²`. -/
theorem fejerKernel_eq_sin_sq_div {N : ℕ} (hN : 1 ≤ N) {θ : ℝ} (hsin : Real.sin (θ / 2) ≠ 0) :
    fejerKernel N θ = (1 / (N : ℝ)) * (Real.sin ((N : ℝ) * θ / 2) / Real.sin (θ / 2)) ^ 2 := by
  rw [fejerKernel_eq_normSq_exp_sum hN]
  congr 1
  have hsum_eq :
      ∑ m ∈ Finset.range N, Complex.exp (((m : ℝ) * θ : ℝ) * Complex.I) =
        ∑ m ∈ Finset.Ico 0 N, e ((θ / (2 * Real.pi)) * (m : ℝ)) := by
    rw [Finset.range_eq_Ico]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [e]
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  have hmul := congrArg norm (e_sub_one_mul_sum_Ico (θ / (2 * Real.pi)) (Nat.zero_le N))
  rw [norm_mul, norm_e_sub_one] at hmul
  have hpi_th : Real.pi * (θ / (2 * Real.pi)) = θ / 2 := by field_simp [Real.pi_ne_zero]
  have hrhs : ‖e ((θ / (2 * Real.pi)) * (N : ℝ)) - e ((θ / (2 * Real.pi)) * (0 : ℕ))‖ =
      2 * |Real.sin ((N : ℝ) * θ / 2)| := by
    simp only [Nat.cast_zero, mul_zero, e_zero]
    rw [norm_e_sub_one]
    congr 2
    field_simp [Real.pi_ne_zero]
  rw [hpi_th, hrhs] at hmul
  have hnorm_sum : ‖∑ m ∈ Finset.range N, Complex.exp (((m : ℝ) * θ : ℝ) * Complex.I)‖ =
      |Real.sin ((N : ℝ) * θ / 2)| / |Real.sin (θ / 2)| := by
    rw [hsum_eq]
    have hpos : 0 < |Real.sin (θ / 2)| := abs_pos.mpr hsin
    rw [eq_div_iff hpos.ne']
    linarith
  rw [hnorm_sum, div_pow, sq_abs, sq_abs, ← div_pow]

/-- Integral normalization of the Fejér kernel (`1 ≤ N`):
`(1 / (2π)) ∫_0^{2π} K_N(θ) dθ = 1`. -/
theorem integral_fejerKernel {N : ℕ} (hN : 1 ≤ N) :
    (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), fejerKernel N θ = 1 := by
  have hN0 : N ≠ 0 := by omega
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
  have hint_m : ∀ m ∈ Finset.range N,
      IntervalIntegrable (fun θ => dirichletKernel m θ) volume 0 (2 * Real.pi) := by
    intro m _
    refine Continuous.intervalIntegrable ?_ _ _
    dsimp only [dirichletKernel]
    fun_prop
  have hfun : (fun θ : ℝ => fejerKernel N θ) =
      fun θ : ℝ => (1 / (N : ℝ)) * ∑ m ∈ Finset.range N, dirichletKernel m θ := by
    funext θ; simp [fejerKernel, hN0]
  rw [hfun, intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hint_m]
  have hsum_int : ∑ m ∈ Finset.range N, ∫ θ in (0 : ℝ)..(2 * Real.pi), dirichletKernel m θ =
      (N : ℝ) * (2 * Real.pi) := by
    have heach : ∀ m ∈ Finset.range N,
        ∫ θ in (0 : ℝ)..(2 * Real.pi), dirichletKernel m θ = 2 * Real.pi := by
      intro m _
      have hi := integral_dirichletKernel m
      field_simp [Real.pi_ne_zero] at hi
      linarith
    rw [Finset.sum_congr rfl heach, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum_int]
  field_simp [hNr, Real.pi_ne_zero]

/-- `L¹` norm of the Fejér kernel (`1 ≤ N`):
`(1 / (2π)) ∫_0^{2π} |K_N(θ)| dθ = 1`. -/
theorem integral_abs_fejerKernel {N : ℕ} (hN : 1 ≤ N) :
    (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), |fejerKernel N θ| = 1 := by
  have hfun : (fun θ : ℝ => |fejerKernel N θ|) = fun θ : ℝ => fejerKernel N θ := by
    funext θ; exact abs_of_nonneg (fejerKernel_nonneg N θ)
  rw [hfun]
  exact integral_fejerKernel hN

/-- **Discrete Fejér Kernel Normalization at `M`-th Roots of Unity** (`1 ≤ N ≤ M`):
`(1 / M) ∑_{j=0}^{M-1} K_N(2π j / M) = 1`. -/
theorem sum_fejerKernel_roots {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (1 / (M : ℝ)) * ∑ j ∈ Finset.range M,
        fejerKernel N (2 * Real.pi * (j : ℝ) / (M : ℝ)) = 1 := by
  have hM0 : M ≠ 0 := by omega
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM0
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hsum_cos_zero : ∀ k ∈ Finset.Icc 1 (N - 1),
      ∑ j ∈ Finset.range M, Real.cos ((k : ℝ) * (2 * Real.pi * (j : ℝ) / (M : ℝ))) = 0 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk_lt : k < M := by omega
    have hre : (∑ j ∈ Finset.range M,
        e (((k : ℝ) / (M : ℝ)) * (j : ℝ))).re =
        ∑ j ∈ Finset.range M, Real.cos ((k : ℝ) * (2 * Real.pi * (j : ℝ) / (M : ℝ))) := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [e]
      have harg : ((2 * Real.pi * ((k : ℝ) / (M : ℝ) * (j : ℝ)) : ℝ) : ℂ) * Complex.I =
          ((((k : ℝ) * (2 * Real.pi * (j : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I) := by
        push_cast; ring
      rw [harg]
      have hre_cexp : ∀ r : ℝ, (Complex.exp ((r : ℂ) * Complex.I)).re = Real.cos r := by
        intro r
        rw [Complex.exp_re]
        simp
      exact hre_cexp ((k : ℝ) * (2 * Real.pi * (j : ℝ) / (M : ℝ)))
    rw [← hre]
    have hmul := e_sub_one_mul_sum_Ico ((k : ℝ) / (M : ℝ)) (Nat.zero_le M)
    rw [← Finset.range_eq_Ico] at hmul
    have hrhs_zero : e ((k : ℝ) / (M : ℝ) * (M : ℝ)) - e ((k : ℝ) / (M : ℝ) * (0 : ℕ)) = 0 := by
      have hkM : (k : ℝ) / (M : ℝ) * (M : ℝ) = ((k : ℤ) : ℝ) := by
        field_simp [hMr]; norm_cast
      rw [hkM, e_intCast]
      simp
    rw [hrhs_zero] at hmul
    have hne : e ((k : ℝ) / (M : ℝ)) - 1 ≠ 0 := by
      intro hz
      have hnorm : ‖e ((k : ℝ) / (M : ℝ)) - 1‖ = 0 := by rw [hz, norm_zero]
      rw [norm_e_sub_one] at hnorm
      have hpi_arg : 0 < Real.pi * ((k : ℝ) / (M : ℝ)) := by
        have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk.1
        positivity
      have hpi_lt : Real.pi * ((k : ℝ) / (M : ℝ)) < Real.pi := by
        have hk_real : (k : ℝ) < (M : ℝ) := by exact_mod_cast hk_lt
        have hdiv : (k : ℝ) / (M : ℝ) < 1 := (div_lt_one hM_pos).mpr hk_real
        nlinarith [Real.pi_pos]
      have hsin_pos : 0 < Real.sin (Real.pi * ((k : ℝ) / (M : ℝ))) :=
        Real.sin_pos_of_pos_of_lt_pi hpi_arg hpi_lt
      have habs : |Real.sin (Real.pi * ((k : ℝ) / (M : ℝ)))| = 0 := by linarith
      linarith [abs_pos.mpr hsin_pos.ne']
    have hsum_zero : ∑ j ∈ Finset.range M, e ((k : ℝ) / (M : ℝ) * (j : ℝ)) = 0 :=
      (mul_eq_zero.mp hmul).resolve_left hne
    rw [hsum_zero, Complex.zero_re]
  have hsum_fejer : ∑ j ∈ Finset.range M,
      fejerKernel N (2 * Real.pi * (j : ℝ) / (M : ℝ)) = (M : ℝ) := by
    simp_rw [fejerKernel_eq_sum_cos hN]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      ← Finset.mul_sum, Finset.sum_comm]
    have hinner : ∑ k ∈ Finset.Icc 1 (N - 1),
        ∑ j ∈ Finset.range M, (1 - (k : ℝ) / (N : ℝ)) *
          Real.cos ((k : ℝ) * (2 * Real.pi * (j : ℝ) / (M : ℝ))) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [← Finset.mul_sum, hsum_cos_zero k hk, mul_zero]
    rw [hinner, mul_zero, add_zero]
  rw [hsum_fejer]
  field_simp [hMr]

/-- **Fejér Kernel Approximate-Identity Tail Bound**:
For `1 ≤ N`, `0 < δ ≤ π`, and `θ ∈ [δ, 2π - δ]`,
`K_N(θ) ≤ π² / (N · δ²)`. -/
theorem fejerKernel_tail_le {N : ℕ} (hN : 1 ≤ N) {δ θ : ℝ}
    (hδ0 : 0 < δ) (hδpi : δ ≤ Real.pi) (hθ1 : δ ≤ θ) (hθ2 : θ ≤ 2 * Real.pi - δ) :
    fejerKernel N θ ≤ Real.pi ^ 2 / ((N : ℝ) * δ ^ 2) := by
  have hhalf_ge : δ / 2 ≤ θ / 2 := by linarith
  have hhalf_le : θ / 2 ≤ Real.pi - δ / 2 := by linarith
  have hsin_lb : δ / Real.pi ≤ Real.sin (θ / 2) := by
    have hjordan : δ / Real.pi ≤ Real.sin (δ / 2) := by
      have h := Real.mul_le_sin (x := δ / 2) (by linarith) (by linarith)
      have hpi : 2 / Real.pi * (δ / 2) = δ / Real.pi := by field_simp [Real.pi_ne_zero]
      linarith
    by_cases hq : θ / 2 ≤ Real.pi / 2
    · have hmono : Real.sin (δ / 2) ≤ Real.sin (θ / 2) :=
        Real.strictMonoOn_sin.monotoneOn
          (Set.mem_Icc.mpr ⟨by linarith [Real.pi_pos], by linarith⟩)
          (Set.mem_Icc.mpr ⟨by linarith [Real.pi_pos], hq⟩) hhalf_ge
      linarith
    · push Not at hq
      have hsym : Real.sin (θ / 2) = Real.sin (Real.pi - θ / 2) := (Real.sin_pi_sub (θ / 2)).symm
      have hmono : Real.sin (δ / 2) ≤ Real.sin (Real.pi - θ / 2) :=
        Real.strictMonoOn_sin.monotoneOn
          (Set.mem_Icc.mpr ⟨by linarith [Real.pi_pos], by linarith⟩)
          (Set.mem_Icc.mpr ⟨by linarith [Real.pi_pos], by linarith⟩) (by linarith)
      linarith
  have hsin_pos : 0 < Real.sin (θ / 2) := by
    have : 0 < δ / Real.pi := div_pos hδ0 Real.pi_pos
    linarith
  rw [fejerKernel_eq_sin_sq_div hN hsin_pos.ne']
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hnum : (Real.sin ((N : ℝ) * θ / 2)) ^ 2 ≤ 1 := by
    have h1 := Real.sin_le_one ((N : ℝ) * θ / 2)
    have h2 := Real.neg_one_le_sin ((N : ℝ) * θ / 2)
    nlinarith [Real.sin_le_one ((N : ℝ) * θ / 2)]
  have hden : (δ / Real.pi) ^ 2 ≤ (Real.sin (θ / 2)) ^ 2 := by
    have h0 : 0 ≤ δ / Real.pi := (div_pos hδ0 Real.pi_pos).le
    nlinarith
  have hden_pos : 0 < (δ / Real.pi) ^ 2 := pow_pos (div_pos hδ0 Real.pi_pos) 2
  calc
    (1 / (N : ℝ)) * (Real.sin ((N : ℝ) * θ / 2) / Real.sin (θ / 2)) ^ 2
      = (Real.sin ((N : ℝ) * θ / 2)) ^ 2 / ((N : ℝ) * (Real.sin (θ / 2)) ^ 2) := by
        rw [div_pow]; ring
    _ ≤ 1 / ((N : ℝ) * (δ / Real.pi) ^ 2) := by
        gcongr
    _ = Real.pi ^ 2 / ((N : ℝ) * δ ^ 2) := by
        field_simp [Real.pi_ne_zero, hN_pos.ne', hδ0.ne']

/-! ## Section 5: Explicit Elementary Chebyshev & Prime-Harmonic Bounds -/

/-- Chebyshev's first function `θ(x) = ∑_{p ≤ x, p prime} log p`. -/
def chebyshevTheta (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ)

/-- Chebyshev's second function `ψ(x) = ∑_{1 ≤ n ≤ x} Λ(n)`. -/
def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n

/-- Prime counting function `π(x) = #{p ≤ x : p prime}`. -/
def primePi (x : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime).card

/-- Prime log-reciprocal partial sum `∑_{p ≤ x} log p / p`. -/
def primeLogRecipSum (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)

/-- Prime reciprocal partial sum `∑_{p ≤ x} 1 / p`. -/
def primeRecipSum (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)

/-- Euler-product partial product at `s = 1`: `∏_{p ≤ x} (1 - 1 / p)`. -/
def eulerProdPartial (x : ℝ) : ℝ :=
  ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 - (p : ℝ)⁻¹)

theorem chebyshevTheta_mono {x y : ℝ} (hxy : x ≤ y) :
    chebyshevTheta x ≤ chebyshevTheta y := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_mono hxy)⟩, hp.2⟩
  · intro p hp _
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      exact_mod_cast hp.1.1
    exact Real.log_nonneg hp1

theorem primePi_mono {x y : ℝ} (hxy : x ≤ y) : primePi x ≤ primePi y := by
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_mono hxy)⟩, hp.2⟩

private lemma prime_dvd_factorial_iff {p n : ℕ} (hp : Nat.Prime p) :
    p ∣ Nat.factorial n ↔ p ≤ n := by
  induction n with
  | zero =>
    simp only [Nat.factorial_zero, Nat.dvd_one]
    constructor
    · intro h; exact absurd h hp.ne_one
    · intro h; exact absurd (Nat.le_zero.mp h) hp.ne_zero
  | succ n ih =>
    rw [Nat.factorial_succ, hp.dvd_mul, ih]
    constructor
    · rintro (h | h)
      · exact Nat.le_of_dvd (Nat.succ_pos n) h
      · omega
    · intro h
      rcases eq_or_lt_of_le h with rfl | hlt
      · left; exact dvd_rfl
      · right; omega

/-- Product of primes in `(m+1, 2m+1]` divides `choose (2m+1) m`. -/
theorem prod_primes_Ioc_dvd_choose (m : ℕ) :
    ∏ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, p ∣ Nat.choose (2 * m + 1) m := by
  have hprod_dvd : ∀ S : Finset ℕ,
      (∀ p ∈ S, Nat.Prime p ∧ p ∣ Nat.choose (2 * m + 1) m) →
      ∏ p ∈ S, p ∣ Nat.choose (2 * m + 1) m := by
    intro S hS
    induction S using Finset.induction_on with
    | empty => simp
    | @insert p S hpS ih =>
      rw [Finset.prod_insert hpS]
      have hp_mem := hS p (Finset.mem_insert_self p S)
      have hS_dvd : ∏ q ∈ S, q ∣ Nat.choose (2 * m + 1) m :=
        ih fun q hq => hS q (Finset.mem_insert_of_mem hq)
      have hcop : Nat.Coprime p (∏ q ∈ S, q) := by
        refine Nat.Coprime.prod_right fun q hq => ?_
        have hq_prime := (hS q (Finset.mem_insert_of_mem hq)).1
        refine (Nat.coprime_primes hp_mem.1 hq_prime).mpr ?_
        intro hEq
        exact hpS (hEq ▸ hq)
      exact hcop.mul_dvd_of_dvd_of_dvd hp_mem.2 hS_dvd
  refine hprod_dvd _ fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
  rcases hp with ⟨⟨hpm, hp2m⟩, hp_prime⟩
  have hfac := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m + 1)
  rw [show 2 * m + 1 - m = m + 1 by omega] at hfac
  have hdvd_fac : p ∣ Nat.factorial (2 * m + 1) := (prime_dvd_factorial_iff hp_prime).mpr hp2m
  rw [← hfac] at hdvd_fac
  have hnd1 : ¬ p ∣ Nat.factorial m := by
    rw [prime_dvd_factorial_iff hp_prime]; omega
  have hnd2 : ¬ p ∣ Nat.factorial (m + 1) := by
    rw [prime_dvd_factorial_iff hp_prime]; omega
  rcases hp_prime.dvd_mul.mp hdvd_fac with h12 | h3
  · rcases hp_prime.dvd_mul.mp h12 with h1 | h2
    · exact ⟨hp_prime, h1⟩
    · exact False.elim (hnd1 h2)
  · exact False.elim (hnd2 h3)

/-- `choose (2m + 1) m ≤ 4 ^ m` for all `m : ℕ`. -/
theorem choose_two_mul_add_one_le_four_pow (m : ℕ) : Nat.choose (2 * m + 1) m ≤ 4 ^ m := by
  have hsymm : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
    rw [← Nat.choose_symm (by omega : m ≤ 2 * m + 1)]
    congr 1; omega
  have hsub : ({m, m + 1} : Finset ℕ) ⊆ Finset.range (2 * m + 2) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    simp only [Finset.mem_range]
    omega
  have hsum_pair :
      Nat.choose (2 * m + 1) m + Nat.choose (2 * m + 1) (m + 1) ≤
        ∑ k ∈ Finset.range (2 * m + 2), Nat.choose (2 * m + 1) k := by
    have hdisj : m ≠ m + 1 := by omega
    calc
      Nat.choose (2 * m + 1) m + Nat.choose (2 * m + 1) (m + 1)
        = ∑ k ∈ ({m, m + 1} : Finset ℕ), Nat.choose (2 * m + 1) k := by
          rw [Finset.sum_pair hdisj]
      _ ≤ ∑ k ∈ Finset.range (2 * m + 2), Nat.choose (2 * m + 1) k :=
          Finset.sum_le_sum_of_subset hsub
  rw [hsymm, Nat.sum_range_choose (2 * m + 1)] at hsum_pair
  have hpow : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, mul_comm (2 ^ (2 * m)) 2, pow_mul, show 2 ^ 2 = 4 by norm_num]
  omega

/-- **Chebyshev Upper Bound on `θ(x)`** (100% elementary, valid for all `x ≥ 0`):
`θ(x) ≤ (2 log 2) · x`. -/
theorem chebyshevTheta_le_two_log_two_mul {x : ℝ} (hx : 0 ≤ x) :
    chebyshevTheta x ≤ (2 * Real.log 2) * x := by
  have hnat : ∀ n : ℕ,
      ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log (p : ℝ) ≤ (2 * Real.log 2) * (n : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases le_or_gt n 2 with hn2 | hn2
      · interval_cases n
        · simp
        · simp; positivity
        · have hset : (Finset.Icc 1 2).filter Nat.Prime = {2} := by decide
          rw [hset, Finset.sum_singleton]
          have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          push_cast; linarith
      · rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
        · have hm2 : 2 ≤ m := by omega
          have hcomp : ¬ Nat.Prime (m + m) := by
            intro hp
            have hdvd : 2 ∣ m + m := ⟨m, by ring⟩
            rcases (Nat.dvd_prime hp).mp hdvd with h21 | h2m
            · omega
            · omega
          have hfilt : (Finset.Icc 1 (m + m)).filter Nat.Prime =
              (Finset.Icc 1 (m + m - 1)).filter Nat.Prime := by
            ext p
            simp only [Finset.mem_filter, Finset.mem_Icc]
            constructor
            · rintro ⟨⟨hp1, hpm⟩, hp⟩
              refine ⟨⟨hp1, ?_⟩, hp⟩
              rcases eq_or_lt_of_le hpm with rfl | hlt
              · exact False.elim (hcomp hp)
              · omega
            · rintro ⟨⟨hp1, hpm⟩, hp⟩
              exact ⟨⟨hp1, by omega⟩, hp⟩
          rw [hfilt]
          have hsub := ih (m + m - 1) (by omega)
          have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          have hle : ((m + m - 1 : ℕ) : ℝ) ≤ ((m + m : ℕ) : ℝ) := by
            exact_mod_cast (by omega : m + m - 1 ≤ m + m)
          nlinarith
        · have hm1 : 1 ≤ m := by omega
          have hsplit : (Finset.Icc 1 (2 * m + 1)).filter Nat.Prime =
              (Finset.Icc 1 (m + 1)).filter Nat.Prime ∪
                (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime := by
            ext p
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
            constructor
            · rintro ⟨⟨hp1, hp2m⟩, hp⟩
              by_cases hpm : p ≤ m + 1
              · exact Or.inl ⟨⟨hp1, hpm⟩, hp⟩
              · exact Or.inr ⟨⟨by omega, hp2m⟩, hp⟩
            · rintro (⟨⟨hp1, hpm⟩, hp⟩ | ⟨⟨hpm, hp2m⟩, hp⟩)
              · exact ⟨⟨hp1, by omega⟩, hp⟩
              · exact ⟨⟨by omega, hp2m⟩, hp⟩
          have hdisj : Disjoint ((Finset.Icc 1 (m + 1)).filter Nat.Prime)
              ((Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime) := by
            rw [Finset.disjoint_left]
            intro p hp1 hp2
            simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp1 hp2
            omega
          rw [hsplit, Finset.sum_union hdisj]
          have h1 := ih (m + 1) (by omega)
          have h2 : ∑ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, Real.log (p : ℝ) ≤
              (2 * Real.log 2) * (m : ℝ) := by
            have hprod_pos : (0 : ℝ) <
                ((∏ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, p : ℕ) : ℝ) := by
              exact_mod_cast Finset.prod_pos
                (s := (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime)
                fun p hp => (Finset.mem_filter.mp hp).2.pos
            have hlog_prod :
                ∑ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, Real.log (p : ℝ) =
                  Real.log ((∏ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, p : ℕ) : ℝ) := by
              rw [Nat.cast_prod, Real.log_prod]
              intro p hp
              exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
            have hdvd := prod_primes_Ioc_dvd_choose m
            have hle_choose :
                ∏ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, p ≤
                  Nat.choose (2 * m + 1) m :=
              Nat.le_of_dvd (Nat.choose_pos (by omega)) hdvd
            have hle_pow :
                ((∏ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, p : ℕ) : ℝ) ≤
                  ((4 ^ m : ℕ) : ℝ) := by
              exact_mod_cast hle_choose.trans (choose_two_mul_add_one_le_four_pow m)
            rw [hlog_prod]
            calc
              Real.log ((∏ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, p : ℕ) : ℝ)
                ≤ Real.log ((4 ^ m : ℕ) : ℝ) := Real.log_le_log hprod_pos hle_pow
              _ = (m : ℝ) * Real.log ((2 : ℝ) ^ 2) := by
                  rw [Nat.cast_pow, Real.log_pow]
                  norm_num
              _ = (2 * Real.log 2) * (m : ℝ) := by
                  rw [Real.log_pow]; ring
          push_cast at h1 ⊢
          linarith
  have hfl := hnat ⌊x⌋₊
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfl_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  calc
    chebyshevTheta x = ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ) := rfl
    _ ≤ (2 * Real.log 2) * (⌊x⌋₊ : ℝ) := hfl
    _ ≤ (2 * Real.log 2) * x := mul_le_mul_of_nonneg_left hfl_le (by positivity)

/-- **Explicit Elementary Upper Bound on `π(x)`** (valid for all `x ≥ 2`):
`π(x) ≤ (4 log 2 + 2) · x / log x`. -/
theorem primePi_le_explicit {x : ℝ} (hx : 2 ≤ x) :
    (primePi x : ℝ) ≤ (4 * Real.log 2 + 2) * x / Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hlog_x_pos : 0 < Real.log x := Real.log_pos (by linarith)
  set s : ℕ := ⌊Real.sqrt x⌋₊
  have hs_le : (s : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hpart : (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime ⊆
      Finset.Icc 1 s ∪ (Finset.Ioc s ⌊x⌋₊).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc] at hp ⊢
    by_cases hps : p ≤ s
    · exact Or.inl ⟨hp.1.1, hps⟩
    · exact Or.inr ⟨⟨Nat.lt_of_not_ge hps, hp.1.2⟩, hp.2⟩
  have hcard : primePi x ≤ s + ((Finset.Ioc s ⌊x⌋₊).filter Nat.Prime).card := by
    calc
      primePi x ≤ (Finset.Icc 1 s ∪ (Finset.Ioc s ⌊x⌋₊).filter Nat.Prime).card :=
        Finset.card_le_card hpart
      _ ≤ (Finset.Icc 1 s).card + ((Finset.Ioc s ⌊x⌋₊).filter Nat.Prime).card :=
        Finset.card_union_le _ _
      _ = s + ((Finset.Ioc s ⌊x⌋₊).filter Nat.Prime).card := by simp
  have hgt_sqrt : ∀ p ∈ (Finset.Ioc s ⌊x⌋₊).filter Nat.Prime,
      Real.log x / 2 ≤ Real.log (p : ℝ) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hlt_p : Real.sqrt x < (p : ℝ) := by
      have h1 : s + 1 ≤ p := hp.1.1
      have h2 : Real.sqrt x < (s : ℝ) + 1 := Nat.lt_floor_add_one (Real.sqrt x)
      have h3 : (s : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast h1
      linarith
    have hlog_eq : Real.log x / 2 = Real.log (Real.sqrt x) := by
      rw [Real.sqrt_eq_rpow, Real.log_rpow (by linarith : (0 : ℝ) < x)]
      ring
    rw [hlog_eq]
    exact Real.log_le_log hsqrt_pos hlt_p.le
  have htail : (((Finset.Ioc s ⌊x⌋₊).filter Nat.Prime).card : ℝ) * (Real.log x / 2) ≤
      chebyshevTheta x := by
    calc
      (((Finset.Ioc s ⌊x⌋₊).filter Nat.Prime).card : ℝ) * (Real.log x / 2)
        = ∑ _p ∈ (Finset.Ioc s ⌊x⌋₊).filter Nat.Prime, (Real.log x / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ (Finset.Ioc s ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ) :=
          Finset.sum_le_sum hgt_sqrt
      _ ≤ ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro p hp
            simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
            exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
          · intro p hp _
            have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
              simp only [Finset.mem_filter, Finset.mem_Icc] at hp
              exact_mod_cast hp.1.1
            exact Real.log_nonneg hp1
  have htail_le : (((Finset.Ioc s ⌊x⌋₊).filter Nat.Prime).card : ℝ) ≤
      (4 * Real.log 2) * x / Real.log x := by
    have h1 := htail.trans (chebyshevTheta_le_two_log_two_mul hx0)
    rw [le_div_iff₀ hlog_x_pos]
    linarith
  have hsqrt_le : Real.sqrt x ≤ 2 * x / Real.log x := by
    have hlog_sqrt : Real.log (Real.sqrt x) ≤ Real.sqrt x := by
      have h := Real.log_le_sub_one_of_pos hsqrt_pos
      linarith
    have hlog_x_le : Real.log x ≤ 2 * Real.sqrt x := by
      have hlog_eq : Real.log x = 2 * Real.log (Real.sqrt x) := by
        rw [Real.sqrt_eq_rpow, Real.log_rpow (by linarith : (0 : ℝ) < x)]
        ring
      linarith
    rw [le_div_iff₀ hlog_x_pos]
    calc
      Real.sqrt x * Real.log x ≤ Real.sqrt x * (2 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hlog_x_le hsqrt_pos.le
      _ = 2 * (Real.sqrt x * Real.sqrt x) := by ring
      _ = 2 * x := by rw [Real.mul_self_sqrt hx0]
  have hcard_r : (primePi x : ℝ) ≤ (s : ℝ) + (((Finset.Ioc s ⌊x⌋₊).filter Nat.Prime).card : ℝ) := by
    exact_mod_cast hcard
  calc
    (primePi x : ℝ) ≤ (s : ℝ) + (((Finset.Ioc s ⌊x⌋₊).filter Nat.Prime).card : ℝ) := hcard_r
    _ ≤ Real.sqrt x + (4 * Real.log 2) * x / Real.log x := add_le_add hs_le htail_le
    _ ≤ 2 * x / Real.log x + (4 * Real.log 2) * x / Real.log x := add_le_add hsqrt_le le_rfl
    _ = (4 * Real.log 2 + 2) * x / Real.log x := by ring

private lemma choose_le_centralBinom_aux (m k : ℕ) (hk : k ≤ 2 * m) :
    Nat.choose (2 * m) k ≤ Nat.choose (2 * m) m := by
  have hmono : ∀ a b : ℕ, a ≤ b → b ≤ m → Nat.choose (2 * m) a ≤ Nat.choose (2 * m) b := by
    intro a b hab hbm
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih =>
      have ih' := ih (by omega)
      have hstep : Nat.choose (2 * m) b ≤ Nat.choose (2 * m) (b + 1) := by
        have h1 := Nat.choose_mul_factorial_mul_factorial (by omega : b ≤ 2 * m)
        have h2 := Nat.choose_mul_factorial_mul_factorial (by omega : b + 1 ≤ 2 * m)
        have hsub : 2 * m - b = (2 * m - (b + 1)) + 1 := by omega
        have hpos_fac : 0 < Nat.factorial b * Nat.factorial (2 * m - (b + 1)) :=
          Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
        have hrec : Nat.choose (2 * m) (b + 1) * (b + 1) =
            Nat.choose (2 * m) b * (2 * m - b) := by
          apply Nat.mul_right_cancel hpos_fac
          calc
            Nat.choose (2 * m) (b + 1) * (b + 1) * (Nat.factorial b * Nat.factorial (2 * m - (b + 1)))
              = Nat.choose (2 * m) (b + 1) * ((b + 1) * Nat.factorial b) *
                  Nat.factorial (2 * m - (b + 1)) := by ring
            _ = Nat.choose (2 * m) (b + 1) * Nat.factorial (b + 1) *
                  Nat.factorial (2 * m - (b + 1)) := by rw [← Nat.factorial_succ b]
            _ = Nat.factorial (2 * m) := h2
            _ = Nat.choose (2 * m) b * Nat.factorial b * Nat.factorial (2 * m - b) := h1.symm
            _ = Nat.choose (2 * m) b * Nat.factorial b *
                  ((2 * m - b) * Nat.factorial (2 * m - (b + 1))) := by
                rw [hsub, Nat.factorial_succ]
            _ = Nat.choose (2 * m) b * (2 * m - b) *
                  (Nat.factorial b * Nat.factorial (2 * m - (b + 1))) := by ring
        have hpos : 0 < b + 1 := Nat.succ_pos b
        have hle_rhs : Nat.choose (2 * m) b * (b + 1) ≤ Nat.choose (2 * m) b * (2 * m - b) :=
          Nat.mul_le_mul_left _ (by omega)
        have hle2 : Nat.choose (2 * m) b * (b + 1) ≤ Nat.choose (2 * m) (b + 1) * (b + 1) := by
          linarith [hrec]
        exact Nat.le_of_mul_le_mul_right hle2 hpos
      exact ih'.trans hstep
  rcases le_or_gt k m with hkm | hkm
  · exact hmono k m hkm le_rfl
  · rw [← Nat.choose_symm hk]
    exact hmono (2 * m - k) m (by omega) le_rfl

/-- `4 ^ m ≤ (2m + 1) · choose (2m) m` for all `m : ℕ`. -/
theorem four_pow_le_mul_centralBinom (m : ℕ) :
    4 ^ m ≤ (2 * m + 1) * Nat.choose (2 * m) m := by
  have hsum : 4 ^ m = ∑ k ∈ Finset.range (2 * m + 1), Nat.choose (2 * m) k := by
    rw [Nat.sum_range_choose (2 * m)]
    calc
      4 ^ m = (2 ^ 2) ^ m := by norm_num
      _ = 2 ^ (2 * m) := by rw [← pow_mul]
  rw [hsum]
  calc
    ∑ k ∈ Finset.range (2 * m + 1), Nat.choose (2 * m) k
      ≤ ∑ _k ∈ Finset.range (2 * m + 1), Nat.choose (2 * m) m := by
        refine Finset.sum_le_sum fun k hk => ?_
        exact choose_le_centralBinom_aux m k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    _ = (2 * m + 1) * Nat.choose (2 * m) m := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- Exact prime-power exponent bound in the central binomial coefficient:
`v_p(choose (2m) m) ≤ ⌊log_p(2m)⌋` for every prime `p` and `m ≥ 1`. -/
theorem padicValNat_centralBinom_le_log {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) :
    padicValNat p (Nat.choose (2 * m) m) ≤ Nat.log p (2 * m) := by
  have : Fact p.Prime := ⟨hp⟩
  set B : ℕ := Nat.log p (2 * m) + 1
  have hfac_eq := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m)
  rw [show 2 * m - m = m by omega] at hfac_eq
  have hne1 : Nat.choose (2 * m) m ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hne2 : Nat.factorial m ≠ 0 := Nat.factorial_ne_zero m
  have hv_mul : padicValNat p (Nat.choose (2 * m) m) +
      padicValNat p (Nat.factorial m) + padicValNat p (Nat.factorial m) =
      padicValNat p (Nat.factorial (2 * m)) := by
    have h1 := padicValNat.mul (p := p) (a := Nat.choose (2 * m) m * Nat.factorial m)
      (b := Nat.factorial m) (Nat.mul_ne_zero hne1 hne2) hne2
    have h2 := padicValNat.mul (p := p) (a := Nat.choose (2 * m) m)
      (b := Nat.factorial m) hne1 hne2
    rw [hfac_eq] at h1
    omega
  have hv2m := padicValNat_factorial (p := p) (n := 2 * m) (b := B) (Nat.lt_succ_self _)
  have hvm := padicValNat_factorial (p := p) (n := m) (b := B)
    ((Nat.log_mono_right (by omega : m ≤ 2 * m)).trans_lt (Nat.lt_succ_self _))
  rw [hv2m, hvm] at hv_mul
  have hterm : ∀ j ∈ Finset.Ico 1 B, (2 * m) / p ^ j ≤ 2 * (m / p ^ j) + 1 := by
    intro j _
    set d : ℕ := p ^ j
    have hd_pos : 0 < d := pow_pos hp.pos j
    have hmod : m = d * (m / d) + m % d := (Nat.div_add_mod m d).symm
    have hrem : m % d < d := Nat.mod_lt m hd_pos
    have hlt : 2 * m < d * (2 * (m / d) + 2) := by nlinarith
    have hdiv : (2 * m) / d < 2 * (m / d) + 2 := Nat.div_lt_of_lt_mul hlt
    omega
  have hsum_le : ∑ j ∈ Finset.Ico 1 B, (2 * m) / p ^ j ≤
      2 * (∑ j ∈ Finset.Ico 1 B, m / p ^ j) + Nat.log p (2 * m) := by
    calc
      ∑ j ∈ Finset.Ico 1 B, (2 * m) / p ^ j
        ≤ ∑ j ∈ Finset.Ico 1 B, (2 * (m / p ^ j) + 1) := Finset.sum_le_sum hterm
      _ = 2 * (∑ j ∈ Finset.Ico 1 B, m / p ^ j) + (Finset.Ico 1 B).card := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_one]
      _ = 2 * (∑ j ∈ Finset.Ico 1 B, m / p ^ j) + Nat.log p (2 * m) := by
          congr 1; simp [B]
  omega

/-- Representation of Chebyshev's `ψ(n)` as a sum over primes `p ≤ n` of `⌊log_p n⌋ · log p`. -/
theorem chebyshevPsi_nat_eq_sum_primes (n : ℕ) :
    chebyshevPsi (n : ℝ) =
      ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, (Nat.log p n : ℝ) * Real.log (p : ℝ) := by
  have hfl : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
  simp only [chebyshevPsi, hfl]
  set S : Finset ℕ := ((Finset.Icc 1 n).filter Nat.Prime).biUnion
    (fun p => (Finset.Icc 1 (Nat.log p n)).image (fun j => p ^ j))
  have hsub : S ⊆ Finset.Icc 1 n := by
    intro k hk
    rcases Finset.mem_biUnion.mp hk with ⟨p, hp, hmem⟩
    rcases Finset.mem_image.mp hmem with ⟨j, hj, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp hj
    simp only [Finset.mem_Icc]
    refine ⟨Nat.one_le_pow j p hp.2.pos, ?_⟩
    exact (Nat.pow_le_pow_right hp.2.pos hj.2).trans (Nat.pow_log_le_self p (by omega))
  have hzero : ∀ k ∈ Finset.Icc 1 n, k ∉ S → ArithmeticFunction.vonMangoldt k = 0 := by
    intro k hk hkS
    by_contra hne
    have hk_pp : IsPrimePow k := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne
    rcases hk_pp with ⟨p, j, hp_prime, hj0, rfl⟩
    have hp_nat : p.Prime := Nat.prime_iff.mpr hp_prime
    have hkn : p ^ j ≤ n := (Finset.mem_Icc.mp hk).2
    have hp_le : p ≤ n := (Nat.le_self_pow hj0.ne' p).trans hkn
    have hn_ne : n ≠ 0 := by
      have hk1 : 1 ≤ p ^ j := Nat.one_le_pow j p hp_nat.pos
      omega
    have hj_le : j ≤ Nat.log p n :=
      (Nat.le_log_iff_pow_le hp_nat.one_lt hn_ne).mpr hkn
    apply hkS
    refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hp_nat.pos, hp_le⟩, hp_nat⟩, Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr
      ⟨Nat.pos_of_ne_zero hj0.ne', hj_le⟩, rfl⟩⟩
  rw [← Finset.sum_subset hsub hzero]
  have hdisj : Set.PairwiseDisjoint
      (((Finset.Icc 1 n).filter Nat.Prime) : Set ℕ)
      (fun p => (Finset.Icc 1 (Nat.log p n)).image (fun j => p ^ j)) := by
    intro p₁ hp₁ p₂ hp₂ hpne
    exact Finset.disjoint_left.mpr fun k hk₁ hk₂ => by
      rcases Finset.mem_image.mp hk₁ with ⟨j₁, hj₁, rfl⟩
      rcases Finset.mem_image.mp hk₂ with ⟨j₂, hj₂, hEq⟩
      have hp1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₁)).2
      have hp2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₂)).2
      have hj1_pos : 0 < j₁ := (Finset.mem_Icc.mp hj₁).1
      have hj2_pos : 0 < j₂ := (Finset.mem_Icc.mp hj₂).1
      have hdvd : p₁ ∣ p₂ ^ j₂ := by
        rw [hEq]
        exact dvd_pow_self p₁ hj1_pos.ne'
      have hp_eq := (Nat.prime_dvd_prime_iff_eq hp1 hp2).mp (hp1.dvd_of_dvd_pow hdvd)
      exact hpne hp_eq
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp_prime := (Finset.mem_filter.mp hp).2
  rw [Finset.sum_image]
  · have hterm : ∀ j ∈ Finset.Icc 1 (Nat.log p n),
        ArithmeticFunction.vonMangoldt (p ^ j) = Real.log (p : ℝ) := by
      intro j hj
      have hj_pos : 0 < j := (Finset.mem_Icc.mp hj).1
      rw [ArithmeticFunction.vonMangoldt_apply_pow hj_pos.ne',
        ArithmeticFunction.vonMangoldt_apply_prime hp_prime]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    simp
  · intro j₁ _ j₂ _ hEq
    exact Nat.pow_right_injective hp_prime.two_le hEq

/-- Lower bound from the central binomial coefficient:
`m log 4 - log(2m + 1) ≤ ψ(2m)` and `m log 4 - log(2m + 1) ≤ π(2m) · log(2m)` for `m ≥ 1`. -/
theorem centralBinom_chebyshev_lower {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) * Real.log 4 - Real.log ((2 * m + 1 : ℕ) : ℝ) ≤ chebyshevPsi ((2 * m : ℕ) : ℝ) ∧
      (m : ℝ) * Real.log 4 - Real.log ((2 * m + 1 : ℕ) : ℝ) ≤
        (primePi ((2 * m : ℕ) : ℝ) : ℝ) * Real.log ((2 * m : ℕ) : ℝ) := by
  set C := Nat.choose (2 * m) m
  have hC_pos : 0 < C := Nat.choose_pos (by omega)
  have hC_le_fac : C ≤ Nat.factorial (2 * m) := by
    have h := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m)
    have hpos : 0 < Nat.factorial m * Nat.factorial (2 * m - m) :=
      Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    calc
      C ≤ C * (Nat.factorial m * Nat.factorial (2 * m - m)) := Nat.le_mul_of_pos_right C hpos
      _ = C * Nat.factorial m * Nat.factorial (2 * m - m) := by ring
      _ = Nat.factorial (2 * m) := h
  have hprod_eq : C = ∏ p ∈ C.primeFactors, p ^ (padicValNat p C) := by
    have h := Nat.prod_factorization_pow_eq_self hC_pos.ne'
    conv_lhs => rw [← h, Finsupp.prod, Nat.support_factorization]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    rw [Nat.factorization_def C hp_prime]
  have hp_sub : C.primeFactors ⊆ (Finset.Icc 1 (2 * m)).filter Nat.Prime := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ C := Nat.dvd_of_mem_primeFactors hp
    have hp_dvd_fac : p ∣ Nat.factorial (2 * m) := hp_dvd.trans (Nat.dvd_of_mod_eq_zero (by
      have := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m)
      have hdiv : C ∣ Nat.factorial (2 * m) :=
        ⟨Nat.factorial m * Nat.factorial (2 * m - m), by linarith⟩
      exact Nat.mod_eq_zero_of_dvd hdiv))
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hp_prime.pos, (prime_dvd_factorial_iff hp_prime).mp hp_dvd_fac⟩, hp_prime⟩
  have hlogC_le_psi : Real.log (C : ℝ) ≤ chebyshevPsi ((2 * m : ℕ) : ℝ) := by
    rw [chebyshevPsi_nat_eq_sum_primes (2 * m)]
    have hlog_prod : Real.log (C : ℝ) =
        ∑ p ∈ C.primeFactors, (padicValNat p C : ℝ) * Real.log (p : ℝ) := by
      conv_lhs => rw [hprod_eq, Nat.cast_prod]
      rw [Real.log_prod]
      · refine Finset.sum_congr rfl fun p _ => ?_
        rw [Nat.cast_pow, Real.log_pow]
      · intro p hp
        exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)
    rw [hlog_prod]
    calc
      ∑ p ∈ C.primeFactors, (padicValNat p C : ℝ) * Real.log (p : ℝ)
        ≤ ∑ p ∈ C.primeFactors, (Nat.log p (2 * m) : ℝ) * Real.log (p : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp_prime := Nat.prime_of_mem_primeFactors hp
          have hv := padicValNat_centralBinom_le_log hp_prime hm
          have hlog_nn : 0 ≤ Real.log (p : ℝ) :=
            Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hv) hlog_nn
      _ ≤ ∑ p ∈ (Finset.Icc 1 (2 * m)).filter Nat.Prime,
            (Nat.log p (2 * m) : ℝ) * Real.log (p : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hp_sub ?_
          intro p hp _
          have hp_prime := (Finset.mem_filter.mp hp).2
          have hlog_nn : 0 ≤ Real.log (p : ℝ) :=
            Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
          positivity
  have hpsi_le_pi : chebyshevPsi ((2 * m : ℕ) : ℝ) ≤
      (primePi ((2 * m : ℕ) : ℝ) : ℝ) * Real.log ((2 * m : ℕ) : ℝ) := by
    rw [chebyshevPsi_nat_eq_sum_primes (2 * m)]
    have hfl : ⌊((2 * m : ℕ) : ℝ)⌋₊ = 2 * m := Nat.floor_natCast (2 * m)
    simp only [primePi, hfl]
    calc
      ∑ p ∈ (Finset.Icc 1 (2 * m)).filter Nat.Prime, (Nat.log p (2 * m) : ℝ) * Real.log (p : ℝ)
        ≤ ∑ _p ∈ (Finset.Icc 1 (2 * m)).filter Nat.Prime, Real.log ((2 * m : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp_prime := (Finset.mem_filter.mp hp).2
          have hp_pow : p ^ Nat.log p (2 * m) ≤ 2 * m := Nat.pow_log_le_self p (by omega)
          have hpow_pos : (0 : ℝ) < ((p ^ Nat.log p (2 * m) : ℕ) : ℝ) := by
            exact_mod_cast pow_pos hp_prime.pos _
          have hp_pow_r : ((p ^ Nat.log p (2 * m) : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
            exact_mod_cast hp_pow
          have hlog_le := Real.log_le_log hpow_pos hp_pow_r
          rw [Nat.cast_pow, Real.log_pow] at hlog_le
          exact hlog_le
      _ = (((Finset.Icc 1 (2 * m)).filter Nat.Prime).card : ℝ) * Real.log ((2 * m : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hlow : (m : ℝ) * Real.log 4 - Real.log ((2 * m + 1 : ℕ) : ℝ) ≤ Real.log (C : ℝ) := by
    have h4m := four_pow_le_mul_centralBinom m
    have hpow_pos : (0 : ℝ) < ((4 ^ m : ℕ) : ℝ) := by positivity
    have h4m_r : ((4 ^ m : ℕ) : ℝ) ≤ (((2 * m + 1) * Nat.choose (2 * m) m : ℕ) : ℝ) := by
      exact_mod_cast h4m
    have hlog := Real.log_le_log hpow_pos h4m_r
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul, Real.log_mul
      (by positivity) (by exact_mod_cast hC_pos.ne')] at hlog
    push_cast at hlog ⊢
    dsimp only [C]
    linarith
  exact ⟨hlow.trans hlogC_le_psi, (hlow.trans hlogC_le_psi).trans hpsi_le_pi⟩

/-- **Explicit Elementary Lower Bound on `π(x)`** (valid for all `x ≥ 2`):
`(log 2 / 4) · x / log x ≤ π(x)`. -/
theorem primePi_ge_explicit {x : ℝ} (hx : 2 ≤ x) :
    (Real.log 2 / 4) * x / Real.log x ≤ (primePi x : ℝ) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt_one : Real.log 2 < 1 := by
    have h2 : (2 : ℝ) < Real.exp 1 := by
      have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
      linarith
    calc
      Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) h2
      _ = 1 := Real.log_exp 1
  have hlog2_gt : 2 / 3 < Real.log 2 := by
    have hexp_lt : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
    have hpow : (Real.exp 1) ^ 2 < (2 : ℝ) ^ 3 := by
      have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      nlinarith
    have hlog := Real.log_lt_log (pow_pos (Real.exp_pos 1) 2) hpow
    rw [Real.log_pow, Real.log_exp, Real.log_pow] at hlog
    push_cast at hlog
    linarith
  have hlog_x_pos : 0 < Real.log x := Real.log_pos (by linarith)
  by_cases hx4 : x < 4
  · have hpi1 : 1 ≤ primePi x := by
      have h2_mem : 2 ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime := by
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by norm_num, Nat.le_floor (by exact_mod_cast hx)⟩, Nat.prime_two⟩
      exact Finset.card_pos.mpr ⟨2, h2_mem⟩
    have h1 : (1 : ℝ) ≤ (primePi x : ℝ) := by exact_mod_cast hpi1
    have hlog_ge : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    rw [div_le_iff₀ hlog_x_pos]
    nlinarith
  · push Not at hx4
    by_cases hx8 : x < 8
    · have hpi2 : 2 ≤ primePi x := by
        have hsub : ({2, 3} : Finset ℕ) ⊆ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime := by
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          simp only [Finset.mem_filter, Finset.mem_Icc]
          rcases hp with rfl | rfl
          · exact ⟨⟨by norm_num, Nat.le_floor (by norm_num; linarith)⟩, Nat.prime_two⟩
          · exact ⟨⟨by norm_num, Nat.le_floor (by norm_num; linarith)⟩, Nat.prime_three⟩
        exact (show ({2, 3} : Finset ℕ).card = 2 by decide) ▸ Finset.card_le_card hsub
      have h2 : (2 : ℝ) ≤ (primePi x : ℝ) := by exact_mod_cast hpi2
      have hlog4 : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx4
      have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
      rw [div_le_iff₀ hlog_x_pos]
      nlinarith
    · push Not at hx8
      set m : ℕ := ⌊x / 2⌋₊
      have hm4 : 4 ≤ m := Nat.le_floor (by linarith)
      have h2m_le : ((2 * m : ℕ) : ℝ) ≤ x := by
        have hfl := Nat.floor_le (by linarith : 0 ≤ x / 2)
        push_cast; linarith
      have hx_lt : x < ((2 * m + 2 : ℕ) : ℝ) := by
        have hlt := Nat.lt_floor_add_one (x / 2)
        push_cast; linarith
      have hcb := (centralBinom_chebyshev_lower (by omega : 1 ≤ m)).2
      have hpi_mono : (primePi ((2 * m : ℕ) : ℝ) : ℝ) ≤ (primePi x : ℝ) := by
        exact_mod_cast primePi_mono h2m_le
      have h2m_pos : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * m)
      have hlog_2m_le : Real.log ((2 * m : ℕ) : ℝ) ≤ Real.log x :=
        Real.log_le_log h2m_pos h2m_le
      have hlog_2m_pos : 0 < Real.log ((2 * m : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * m))
      have hlog_ub : Real.log ((2 * m + 1 : ℕ) : ℝ) ≤
          3 * Real.log 2 + (m : ℝ) / 4 - 7 / 8 := by
        have hdiv_pos : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) / 8 := by positivity
        have hle := Real.log_le_sub_one_of_pos hdiv_pos
        rw [Real.log_div (by positivity) (by norm_num)] at hle
        have hlog8 : Real.log 8 = 3 * Real.log 2 := by
          rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; ring
        push_cast at hle ⊢
        linarith
      have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
      have hm_r : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
      have hmain : (Real.log 2 / 4) * x ≤
          (m : ℝ) * Real.log 4 - Real.log ((2 * m + 1 : ℕ) : ℝ) := by
        have h1 : (Real.log 2 / 4) * x ≤ (Real.log 2 / 4) * (2 * (m : ℝ) + 2) := by
          have : x < 2 * (m : ℝ) + 2 := by push_cast at hx_lt; exact hx_lt
          nlinarith
        have h2 : (m : ℝ) * (3 / 2 * Real.log 2 - 1 / 4) ≥ 4 * (3 / 2 * Real.log 2 - 1 / 4) := by
          have hcoef : 0 ≤ 3 / 2 * Real.log 2 - 1 / 4 := by linarith
          nlinarith
        rw [hlog4_eq]
        linarith
      have hpi_prod : (Real.log 2 / 4) * x ≤ (primePi x : ℝ) * Real.log x := by
        calc
          (Real.log 2 / 4) * x
            ≤ (m : ℝ) * Real.log 4 - Real.log ((2 * m + 1 : ℕ) : ℝ) := hmain
          _ ≤ (primePi ((2 * m : ℕ) : ℝ) : ℝ) * Real.log ((2 * m : ℕ) : ℝ) := hcb
          _ ≤ (primePi x : ℝ) * Real.log x :=
              mul_le_mul hpi_mono hlog_2m_le hlog_2m_pos.le (Nat.cast_nonneg _)
      exact (div_le_iff₀ hlog_x_pos).mpr hpi_prod

/-- **Explicit Elementary Lower Bound on `ψ(x)`** (`x ≥ 2`):
`(log 2) · x - 2 log 2 - log(x + 1) ≤ ψ(x)`. -/
theorem chebyshevPsi_ge_explicit {x : ℝ} (hx : 2 ≤ x) :
    Real.log 2 * x - 2 * Real.log 2 - Real.log (x + 1) ≤ chebyshevPsi x := by
  set m : ℕ := ⌊x / 2⌋₊
  have hm1 : 1 ≤ m := Nat.le_floor (by linarith)
  have h2m_le : ((2 * m : ℕ) : ℝ) ≤ x := by
    have hfl := Nat.floor_le (by linarith : 0 ≤ x / 2)
    push_cast; linarith
  have hx_lt : x < ((2 * m + 2 : ℕ) : ℝ) := by
    have hlt := Nat.lt_floor_add_one (x / 2)
    push_cast; linarith
  have hcb := (centralBinom_chebyshev_lower hm1).1
  have hpsi_mono : chebyshevPsi ((2 * m : ℕ) : ℝ) ≤ chebyshevPsi x := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      exact ⟨hk.1, hk.2.trans (Nat.floor_le_floor h2m_le)⟩
    · intro k _ _
      exact ArithmeticFunction.vonMangoldt_nonneg
  have hlog_le : Real.log ((2 * m + 1 : ℕ) : ℝ) ≤ Real.log (x + 1) := by
    apply Real.log_le_log (by positivity)
    push_cast at h2m_le ⊢
    linarith
  have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hm_ge : x / 2 - 1 ≤ (m : ℝ) := by
    push_cast at hx_lt; linarith
  calc
    Real.log 2 * x - 2 * Real.log 2 - Real.log (x + 1)
      ≤ (m : ℝ) * Real.log 4 - Real.log ((2 * m + 1 : ℕ) : ℝ) := by
        rw [hlog4_eq]; nlinarith
    _ ≤ chebyshevPsi ((2 * m : ℕ) : ℝ) := hcb
    _ ≤ chebyshevPsi x := hpsi_mono

/-- **Explicit Elementary Lower Bound on `θ(x)`** (`x ≥ 2`):
`(log 2) · x - (8 log 2 + 4) √x - 2 log 2 - log(x + 1) ≤ θ(x)`. -/
theorem chebyshevTheta_ge_explicit {x : ℝ} (hx : 2 ≤ x) :
    Real.log 2 * x - (8 * Real.log 2 + 4) * Real.sqrt x - 2 * Real.log 2 - Real.log (x + 1) ≤
      chebyshevTheta x := by
  have hx0 : 0 ≤ x := by linarith
  have hpsi := chebyshevPsi_ge_explicit hx
  have hdiff : chebyshevPsi x - chebyshevTheta x ≤ (8 * Real.log 2 + 4) * Real.sqrt x := by
    have hfl_eq : chebyshevPsi x =
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
          (Nat.log p ⌊x⌋₊ : ℝ) * Real.log (p : ℝ) := by
      have h := chebyshevPsi_nat_eq_sum_primes ⌊x⌋₊
      simpa only [chebyshevPsi, Nat.floor_natCast] using h
    have htheta_eq : chebyshevTheta x =
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ) := rfl
    rw [hfl_eq, htheta_eq, ← Finset.sum_sub_distrib]
    by_cases hx4 : x < 4
    · have hfl3 : ⌊x⌋₊ ≤ 3 := Nat.lt_succ_iff.mp ((Nat.floor_lt hx0).mpr (by norm_num; linarith))
      have hzero : ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
          ((Nat.log p ⌊x⌋₊ : ℝ) * Real.log (p : ℝ) - Real.log (p : ℝ)) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        simp only [Finset.mem_filter, Finset.mem_Icc] at hp
        have hlogp : Nat.log p ⌊x⌋₊ = 1 := by
          have hp2 : 2 ≤ p := hp.2.two_le
          have h1 : 1 ≤ Nat.log p ⌊x⌋₊ :=
            (Nat.le_log_iff_pow_le hp.2.one_lt (by omega : ⌊x⌋₊ ≠ 0)).mpr (by simpa using hp.1.2)
          have h2 : ⌊x⌋₊ < p ^ 2 := by
            have : 4 ≤ p ^ 2 := by nlinarith
            omega
          have h3 : Nat.log p ⌊x⌋₊ < 2 :=
            (Nat.log_lt_iff_lt_pow hp.2.one_lt (by omega : ⌊x⌋₊ ≠ 0)).mpr h2
          omega
        simp [hlogp]
      rw [hzero]
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      positivity
    · push Not at hx4
      have hsqrt2 : 2 ≤ Real.sqrt x := by
        rw [Real.le_sqrt (by norm_num) hx0]
        linarith
      set S₂ := ((Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime).filter (fun p => 2 ≤ Nat.log p ⌊x⌋₊)
      have hsub_S2 : S₂ ⊆ (Finset.Icc 1 ⌊Real.sqrt x⌋₊).filter Nat.Prime := by
        intro p hp
        simp only [S₂, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
        refine ⟨⟨hp.1.1.1, ?_⟩, hp.1.2⟩
        apply Nat.le_floor
        rw [Real.le_sqrt (Nat.cast_nonneg p) hx0]
        have hp_sq : p ^ 2 ≤ ⌊x⌋₊ :=
          (Nat.le_log_iff_pow_le hp.1.2.one_lt (by omega : ⌊x⌋₊ ≠ 0)).mp hp.2
        have hreal_sq : (p : ℝ) ^ 2 ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hp_sq
        nlinarith [Nat.floor_le hx0]
      have hsum_le :
          ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
              ((Nat.log p ⌊x⌋₊ : ℝ) * Real.log (p : ℝ) - Real.log (p : ℝ)) ≤
            ∑ p ∈ S₂, Real.log x := by
        have hterm : ∀ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ((Nat.log p ⌊x⌋₊ : ℝ) * Real.log (p : ℝ) - Real.log (p : ℝ)) ≤
              if p ∈ S₂ then Real.log x else 0 := by
          intro p hp
          have hp_prime := (Finset.mem_filter.mp hp).2
          have hp_le_fl : p ≤ ⌊x⌋₊ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
          have hfl_pos : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
          have hlogp_pos : 1 ≤ Nat.log p ⌊x⌋₊ :=
            (Nat.le_log_iff_pow_le hp_prime.one_lt hfl_pos.ne').mpr (by simpa using hp_le_fl)
          by_cases h2 : 2 ≤ Nat.log p ⌊x⌋₊
          · have hm : p ∈ S₂ := Finset.mem_filter.mpr ⟨hp, h2⟩
            rw [if_pos hm]
            have hpow : p ^ Nat.log p ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.pow_log_le_self p hfl_pos.ne'
            have hlog_pow : (Nat.log p ⌊x⌋₊ : ℝ) * Real.log (p : ℝ) ≤ Real.log x := by
              have hpow_pos : (0 : ℝ) < ((p ^ Nat.log p ⌊x⌋₊ : ℕ) : ℝ) := by
                exact_mod_cast pow_pos hp_prime.pos _
              have hle := Real.log_le_log hpow_pos
                ((by exact_mod_cast hpow : ((p ^ Nat.log p ⌊x⌋₊ : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
                  (Nat.floor_le hx0))
              rw [Nat.cast_pow, Real.log_pow] at hle
              exact hle
            have hlog_nn : 0 ≤ Real.log (p : ℝ) :=
              Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
            linarith
          · have h1 : Nat.log p ⌊x⌋₊ = 1 := by omega
            have hnm : p ∉ S₂ := by simp [S₂, h2]
            rw [if_neg hnm, h1]
            simp
        calc
          ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, _
            ≤ ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, if p ∈ S₂ then Real.log x else 0 :=
              Finset.sum_le_sum hterm
          _ = ∑ p ∈ S₂, Real.log x := by
              rw [← Finset.sum_filter]
              congr 1
              ext p
              simp only [S₂, Finset.mem_filter]
              tauto
      have hcard_le : (S₂.card : ℝ) ≤ (primePi (Real.sqrt x) : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub_S2
      have hpi_sqrt := primePi_le_explicit hsqrt2
      have hlog_sqrt_eq : Real.log (Real.sqrt x) = Real.log x / 2 := by
        rw [Real.sqrt_eq_rpow, Real.log_rpow (by linarith : (0 : ℝ) < x)]
        ring
      rw [hlog_sqrt_eq] at hpi_sqrt
      have hlog_x_pos : 0 < Real.log x := Real.log_pos (by linarith)
      calc
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ((Nat.log p ⌊x⌋₊ : ℝ) * Real.log (p : ℝ) - Real.log (p : ℝ))
          ≤ ∑ _p ∈ S₂, Real.log x := hsum_le
        _ = (S₂.card : ℝ) * Real.log x := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (primePi (Real.sqrt x) : ℝ) * Real.log x :=
            mul_le_mul_of_nonneg_right hcard_le hlog_x_pos.le
        _ ≤ ((4 * Real.log 2 + 2) * Real.sqrt x / (Real.log x / 2)) * Real.log x :=
            mul_le_mul_of_nonneg_right hpi_sqrt hlog_x_pos.le
        _ = (8 * Real.log 2 + 4) * Real.sqrt x := by
            field_simp [hlog_x_pos.ne']
            ring
  linarith

private lemma sum_inv_mul_sqrt_le (N : ℕ) :
    ∑ m ∈ Finset.Icc 2 N, (1 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤ 2 := by
  have hterm : ∀ m ∈ Finset.Icc 2 N,
      (1 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤
        2 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := by
    intro m hm
    have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m - 1)
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hs1_pos : 0 < Real.sqrt ((m - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hm1_pos
    have hs_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos
    have hm1_cast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m)]; norm_num
    have hsq_diff : Real.sqrt (m : ℝ) ^ 2 - Real.sqrt ((m - 1 : ℕ) : ℝ) ^ 2 = 1 := by
      rw [Real.sq_sqrt hm_pos.le, Real.sq_sqrt hm1_pos.le, hm1_cast]; ring
    have hconj : (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) *
        (Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ)) = 1 := by
      linarith [hsq_diff]
    have hsum_le : Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
      have hs_le : Real.sqrt ((m - 1 : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le m 1)
      linarith
    have hdiff_ge : 1 / (2 * Real.sqrt (m : ℝ)) ≤
        Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      calc
        1 = (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) *
              (Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ)) := hconj.symm
        _ ≤ (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) * (2 * Real.sqrt (m : ℝ)) := by
            gcongr
            exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le m 1))
    calc
      (1 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ))
        ≤ (1 : ℝ) / ((m : ℝ) * Real.sqrt ((m - 1 : ℕ) : ℝ)) := by
          gcongr
          exact Nat.sub_le m 1
      _ = (Real.sqrt (m : ℝ) ^ 2 * Real.sqrt ((m - 1 : ℕ) : ℝ))⁻¹ := by
          rw [Real.sq_sqrt hm_pos.le, one_div]
      _ ≤ 2 * (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) /
            (Real.sqrt (m : ℝ) * Real.sqrt ((m - 1 : ℕ) : ℝ)) := by
          rw [inv_eq_one_div, le_div_iff₀ (mul_pos hs_pos hs1_pos)]
          calc
            1 / (Real.sqrt (m : ℝ) ^ 2 * Real.sqrt ((m - 1 : ℕ) : ℝ)) *
                (Real.sqrt (m : ℝ) * Real.sqrt ((m - 1 : ℕ) : ℝ))
              = 1 / Real.sqrt (m : ℝ) := by
                field_simp [hs_pos.ne', hs1_pos.ne']
            _ = 2 * (1 / (2 * Real.sqrt (m : ℝ))) := by
                field_simp [hs_pos.ne']
            _ ≤ 2 * (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_left hdiff_ge (by norm_num)
      _ = 2 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := by
          field_simp [hs_pos.ne', hs1_pos.ne']
  have htel : ∀ M : ℕ, 1 ≤ M →
      ∑ m ∈ Finset.Icc 2 M,
          (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) =
        1 - 1 / Real.sqrt (M : ℝ) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      have hIcc : Finset.Icc 2 (M + 1) = insert (M + 1) (Finset.Icc 2 M) := by
        ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      have hnot : M + 1 ∉ Finset.Icc 2 M := by simp
      rw [hIcc, Finset.sum_insert hnot, ih]
      simp only [Nat.add_sub_cancel]
      ring
  by_cases hN1 : 1 ≤ N
  · calc
      ∑ m ∈ Finset.Icc 2 N, (1 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ))
        ≤ ∑ m ∈ Finset.Icc 2 N,
            2 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = 2 * (1 - 1 / Real.sqrt (N : ℝ)) := by rw [← Finset.mul_sum, htel N hN1]
      _ ≤ 2 := by
          have : 0 ≤ 1 / Real.sqrt (N : ℝ) := by positivity
          linarith
  · have hN0 : N = 0 := by omega
    simp [hN0]

/-- **Mertens' First Theorem (Explicit Elementary Bounds)** for all `x ≥ 1`:
`log x - 11 ≤ ∑_{p ≤ x} log p / p ≤ log x + 2 log 2`. -/
theorem primeLogRecipSum_bounds {x : ℝ} (hx : 1 ≤ x) :
    Real.log x - 11 ≤ primeLogRecipSum x ∧
      primeLogRecipSum x ≤ Real.log x + 2 * Real.log 2 := by
  set N : ℕ := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hN_le : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hx_lt : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hlog_fac_eq :
      Real.log ((Nat.factorial N : ℕ) : ℝ) =
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          (padicValNat p (Nat.factorial N) : ℝ) * Real.log (p : ℝ) := by
    have hfac_pos : 0 < Nat.factorial N := Nat.factorial_pos N
    have hprod : Nat.factorial N =
        ∏ p ∈ (Nat.factorial N).primeFactors, p ^ padicValNat p (Nat.factorial N) := by
      have h := Nat.prod_factorization_pow_eq_self hfac_pos.ne'
      rw [Finsupp.prod, Nat.support_factorization] at h
      conv_lhs => rw [← h]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.factorization_def (Nat.factorial N) (Nat.prime_of_mem_primeFactors hp)]
    have hsub : (Nat.factorial N).primeFactors ⊆ (Finset.Icc 1 N).filter Nat.Prime := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨hp_prime.pos, (prime_dvd_factorial_iff hp_prime).mp (Nat.dvd_of_mem_primeFactors hp)⟩,
        hp_prime⟩
    have hzero : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        p ∉ (Nat.factorial N).primeFactors →
        (padicValNat p (Nat.factorial N) : ℝ) * Real.log (p : ℝ) = 0 := by
      intro p hp hnp
      have hp_prime := (Finset.mem_filter.mp hp).2
      have hdvd : p ∣ Nat.factorial N :=
        (prime_dvd_factorial_iff hp_prime).mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      exact False.elim (hnp (Nat.mem_primeFactors.mpr ⟨hp_prime, hdvd, hfac_pos.ne'⟩))
    rw [← Finset.sum_subset hsub hzero]
    conv_lhs => rw [hprod, Nat.cast_prod]
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hfac_ub : Real.log ((Nat.factorial N : ℕ) : ℝ) ≤ (N : ℝ) * Real.log (N : ℝ) := by
    have hprod : (Nat.factorial N : ℕ) = ∏ k ∈ Finset.Icc 1 N, k := by
      clear hN1 hN_pos hN_le hx_lt hlog_fac_eq
      induction N with
      | zero => simp
      | succ N ih =>
        have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
          ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
        have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
        rw [Nat.factorial_succ, ih, hIcc, Finset.prod_insert hnot]
    rw [hprod, Nat.cast_prod, Real.log_prod]
    · calc
        ∑ k ∈ Finset.Icc 1 N, Real.log (k : ℝ)
          ≤ ∑ _k ∈ Finset.Icc 1 N, Real.log (N : ℝ) := by
            refine Finset.sum_le_sum fun k hk => ?_
            exact Real.log_le_log (by exact_mod_cast (Finset.mem_Icc.mp hk).1)
              (by exact_mod_cast (Finset.mem_Icc.mp hk).2)
        _ = (N : ℝ) * Real.log (N : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; simp
    · intro k hk
      exact Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hk).1; omega)
  have hfac_lb :
      (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) ≤ Real.log ((Nat.factorial N : ℕ) : ℝ) := by
    have hpow := Real.pow_div_factorial_le_exp (N : ℝ) hN_pos.le N
    have hpos : (0 : ℝ) < (N : ℝ) ^ N / ((Nat.factorial N : ℕ) : ℝ) := by positivity
    have hlog := Real.log_le_log hpos hpow
    rw [Real.log_div (pow_ne_zero N hN_pos.ne') (by exact_mod_cast (Nat.factorial_pos N).ne'),
      Real.log_pow, Real.log_exp] at hlog
    linarith
  have hv_ge : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (N / p : ℕ) ≤ padicValNat p (Nat.factorial N) := by
    intro p hp
    have hp_prime := (Finset.mem_filter.mp hp).2
    have : Fact p.Prime := ⟨hp_prime⟩
    rw [padicValNat_factorial (p := p) (n := N) (b := Nat.log p N + 1) (Nat.lt_succ_self _)]
    by_cases hp_le : p ≤ N
    · have hlog1 : 1 ≤ Nat.log p N :=
        (Nat.le_log_iff_pow_le hp_prime.one_lt (by omega : N ≠ 0)).mpr (by simpa using hp_le)
      have hmem : 1 ∈ Finset.Ico 1 (Nat.log p N + 1) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
      calc
        N / p = N / p ^ 1 := by rw [pow_one]
        _ ≤ ∑ j ∈ Finset.Ico 1 (Nat.log p N + 1), N / p ^ j :=
            Finset.single_le_sum (f := fun j => N / p ^ j) (fun _ _ => Nat.zero_le _) hmem
    · have hdiv0 : N / p = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_ge hp_le)
      omega
  have hv_le : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (padicValNat p (Nat.factorial N) : ℝ) ≤
        (N : ℝ) / (p : ℝ) + (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have hp_prime := (Finset.mem_filter.mp hp).2
    have : Fact p.Prime := ⟨hp_prime⟩
    rw [padicValNat_factorial (p := p) (n := N) (b := Nat.log p N + 1) (Nat.lt_succ_self _)]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
    have hsplit : ∑ j ∈ Finset.Ico 1 (Nat.log p N + 1), N / p ^ j ≤
        N / p + ∑ j ∈ Finset.Ico 2 (Nat.log p N + 1), N / p ^ j := by
      by_cases h1 : 1 ≤ Nat.log p N
      · have hIco : Finset.Ico 1 (Nat.log p N + 1) =
            insert 1 (Finset.Ico 2 (Nat.log p N + 1)) := by
          ext k; simp only [Finset.mem_insert, Finset.mem_Ico]; omega
        have hnot : 1 ∉ Finset.Ico 2 (Nat.log p N + 1) := by simp
        rw [hIco, Finset.sum_insert hnot, pow_one]
      · have h0 : Nat.log p N = 0 := by omega
        simp [h0]
    have hcast_le : ((∑ j ∈ Finset.Ico 1 (Nat.log p N + 1), N / p ^ j : ℕ) : ℝ) ≤
        ((N / p : ℕ) : ℝ) + ∑ j ∈ Finset.Ico 2 (Nat.log p N + 1), (N : ℝ) / ((p : ℝ) ^ j) := by
      have h1 : ((∑ j ∈ Finset.Ico 1 (Nat.log p N + 1), N / p ^ j : ℕ) : ℝ) ≤
          ((N / p : ℕ) : ℝ) + ((∑ j ∈ Finset.Ico 2 (Nat.log p N + 1), N / p ^ j : ℕ) : ℝ) := by
        exact_mod_cast hsplit
      refine h1.trans (by
        gcongr
        rw [Nat.cast_sum]
        refine Finset.sum_le_sum fun j _ => ?_
        have := (Nat.cast_div_le (m := N) (n := p ^ j) (α := ℝ))
        simpa using this)
    have hgeom : ∑ j ∈ Finset.Ico 2 (Nat.log p N + 1), (N : ℝ) / ((p : ℝ) ^ j) ≤
        (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have htel_geom : ∀ M : ℕ, 2 ≤ M →
          ∑ j ∈ Finset.Ico 2 M, (1 : ℝ) / (p : ℝ) ^ j ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        intro M hM
        have hp_inv : (1 : ℝ) / (p : ℝ) ^ 2 * (1 / (1 - 1 / (p : ℝ))) =
            1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
          field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 1 ≠ 0 by linarith]
        have hsum_eq : ∑ j ∈ Finset.Ico 2 M, (1 : ℝ) / (p : ℝ) ^ j =
            (1 / (p : ℝ) ^ 2) * ∑ k ∈ Finset.range (M - 2), ((p : ℝ)⁻¹) ^ k := by
          rw [Finset.mul_sum]
          refine Finset.sum_bij' (fun j _ => j - 2) (fun k _ => k + 2)
            (fun j hj => ?_) (fun k hk => ?_) (fun j hj => ?_) (fun k hk => ?_)
            (fun j hj => ?_)
          · simp only [Finset.mem_Ico] at hj; simp only [Finset.mem_range]; omega
          · simp only [Finset.mem_range] at hk; simp only [Finset.mem_Ico]; omega
          · simp only [Finset.mem_Ico] at hj; omega
          · simp only [Finset.mem_range] at hk; omega
          · simp only [Finset.mem_Ico] at hj
            calc
              (1 : ℝ) / (p : ℝ) ^ j = ((p : ℝ) ^ j)⁻¹ := one_div _
              _ = ((p : ℝ)⁻¹) ^ j := (inv_pow _ _).symm
              _ = ((p : ℝ)⁻¹) ^ (2 + (j - 2)) := by rw [show 2 + (j - 2) = j by omega]
              _ = (1 / (p : ℝ) ^ 2) * ((p : ℝ)⁻¹) ^ (j - 2) := by
                  rw [pow_add, inv_pow, one_div]
        rw [hsum_eq, ← hp_inv]
        gcongr
        have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
        have hgeom_id : (1 - (p : ℝ)⁻¹) * ∑ k ∈ Finset.range (M - 2), ((p : ℝ)⁻¹) ^ k =
            1 - ((p : ℝ)⁻¹) ^ (M - 2) := by
          clear hM
          induction M - 2 with
          | zero => simp
          | succ m ih =>
            rw [Finset.sum_range_succ, mul_add, ih]
            ring
        have h1sub_pos : 0 < 1 - (p : ℝ)⁻¹ := by
          have hp_inv_lt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
          linarith
        have hpow_nn : 0 ≤ ((p : ℝ)⁻¹) ^ (M - 2) := pow_nonneg hr0 _
        have hmul_le : (1 - (p : ℝ)⁻¹) * ∑ k ∈ Finset.range (M - 2), ((p : ℝ)⁻¹) ^ k ≤ 1 := by
          linarith
        have hle_inv : ∑ k ∈ Finset.range (M - 2), ((p : ℝ)⁻¹) ^ k ≤ 1 / (1 - (p : ℝ)⁻¹) :=
          (le_div_iff₀ h1sub_pos).mpr (by rw [mul_comm]; exact hmul_le)
        refine hle_inv.trans_eq ?_
        rw [← one_div ((p : ℝ))]
      calc
        ∑ j ∈ Finset.Ico 2 (Nat.log p N + 1), (N : ℝ) / ((p : ℝ) ^ j)
          = (N : ℝ) * ∑ j ∈ Finset.Ico 2 (Nat.log p N + 1), (1 : ℝ) / (p : ℝ) ^ j := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
        _ ≤ (N : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
            by_cases hM : 2 ≤ Nat.log p N + 1
            · exact mul_le_mul_of_nonneg_left (htel_geom _ hM) hN_pos.le
            · have hIco : Finset.Ico 2 (Nat.log p N + 1) = ∅ :=
                Finset.Ico_eq_empty_of_le (by omega)
              have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
              rw [hIco, Finset.sum_empty, mul_zero]
              positivity
        _ = (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by ring
    have hdiv_le : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) := Nat.cast_div_le
    linarith
  have hupper : primeLogRecipSum x ≤ Real.log x + 2 * Real.log 2 := by
    have hsum_lb :
        (N : ℝ) * primeLogRecipSum x - chebyshevTheta x ≤
          Real.log ((Nat.factorial N : ℕ) : ℝ) := by
      have h1 : ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            ((N : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) ≤
            Real.log ((Nat.factorial N : ℕ) : ℝ) := by
        rw [hlog_fac_eq]
        refine Finset.sum_le_sum fun p hp => ?_
        have hp_pos : 0 < p := (Finset.mem_filter.mp hp).2.pos
        have hp_rpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
        have hmod : (N : ℝ) = (p : ℝ) * ((N / p : ℕ) : ℝ) + ((N % p : ℕ) : ℝ) := by
          exact_mod_cast (Nat.div_add_mod N p).symm
        have hrem : ((N % p : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast Nat.mod_lt N hp_pos
        have hdiv_ge : (N : ℝ) / (p : ℝ) - 1 ≤ ((N / p : ℕ) : ℝ) := by
          rw [sub_le_iff_le_add, div_le_iff₀ hp_rpos]; nlinarith
        have hlog_nn : 0 ≤ Real.log (p : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
        exact mul_le_mul_of_nonneg_right (hdiv_ge.trans (by exact_mod_cast hv_ge p hp)) hlog_nn
      have hLHS : ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            ((N : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) =
          (N : ℝ) * primeLogRecipSum x - chebyshevTheta x := by
        simp only [primeLogRecipSum, chebyshevTheta, N]
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun p _ => by ring
      linarith
    have htheta_ub : chebyshevTheta x ≤ (2 * Real.log 2) * (N : ℝ) := by
      simpa only [chebyshevTheta, Nat.floor_natCast] using
        chebyshevTheta_le_two_log_two_mul (x := (N : ℝ)) hN_pos.le
    have hlog_le : Real.log (N : ℝ) ≤ Real.log x := Real.log_le_log hN_pos hN_le
    have hN_mul : (N : ℝ) * primeLogRecipSum x ≤ (N : ℝ) * (Real.log x + 2 * Real.log 2) := by
      nlinarith
    exact le_of_mul_le_mul_left hN_mul hN_pos
  have hlower : Real.log x - 11 ≤ primeLogRecipSum x := by
    have htail_err :
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 8 := by
      calc
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
          ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
              (4 : ℝ) / ((p : ℝ) * Real.sqrt (p : ℝ)) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp_prime := (Finset.mem_filter.mp hp).2
            have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
            have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
            have hs_pos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp_pos
            have hlog_ub : Real.log (p : ℝ) ≤ 2 * Real.sqrt (p : ℝ) := by
              have h1 := Real.log_le_sub_one_of_pos hs_pos
              have h2 : Real.log (p : ℝ) = 2 * Real.log (Real.sqrt (p : ℝ)) := by
                rw [Real.sqrt_eq_rpow, Real.log_rpow hp_pos]; ring
              linarith
            have hp1_ge : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
            calc
              Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
                ≤ (2 * Real.sqrt (p : ℝ)) / ((p : ℝ) * ((p : ℝ) / 2)) := by
                  gcongr
              _ = 4 / ((p : ℝ) * Real.sqrt (p : ℝ)) := by
                  have hsq : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) :=
                    Real.mul_self_sqrt hp_pos.le
                  calc
                    (2 * Real.sqrt (p : ℝ)) / ((p : ℝ) * ((p : ℝ) / 2))
                      = 4 * Real.sqrt (p : ℝ) / ((p : ℝ) * (p : ℝ)) := by ring
                    _ = 4 * Real.sqrt (p : ℝ) /
                          ((p : ℝ) * (Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ))) := by
                        have hden : (p : ℝ) * (Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ)) =
                            (p : ℝ) * (p : ℝ) := by rw [hsq]
                        rw [← hden]
                    _ = 4 / ((p : ℝ) * Real.sqrt (p : ℝ)) := by
                        field_simp [hp_pos.ne', hs_pos.ne']
        _ ≤ ∑ m ∈ Finset.Icc 2 N, (4 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro p hp
              simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
              exact ⟨hp.2.two_le, hp.1.2⟩
            · intro m _ _; positivity
        _ = 4 * ∑ m ∈ Finset.Icc 2 N, (1 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ)) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by ring
        _ ≤ 4 * 2 := mul_le_mul_of_nonneg_left (sum_inv_mul_sqrt_le N) (by norm_num)
        _ = 8 := by norm_num
    have hfac_sum : Real.log ((Nat.factorial N : ℕ) : ℝ) ≤
        (N : ℝ) * primeLogRecipSum x + 8 * (N : ℝ) := by
      rw [hlog_fac_eq]
      calc
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            (padicValNat p (Nat.factorial N) : ℝ) * Real.log (p : ℝ)
          ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
              ((N : ℝ) / (p : ℝ) + (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) * Real.log (p : ℝ) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hlog_nn : 0 ≤ Real.log (p : ℝ) :=
              Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
            exact mul_le_mul_of_nonneg_right (hv_le p hp) hlog_nn
        _ = (N : ℝ) * primeLogRecipSum x +
              (N : ℝ) * ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
                Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
            simp only [primeLogRecipSum, N]
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p _ => by ring
        _ ≤ (N : ℝ) * primeLogRecipSum x + (N : ℝ) * 8 := by
            gcongr
        _ = (N : ℝ) * primeLogRecipSum x + 8 * (N : ℝ) := by ring
    have hlog_x_sub_N : Real.log x - Real.log (N : ℝ) ≤ 1 := by
      have hdiv_le : x / (N : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hN_pos]
        have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
        linarith
      have hlog_div : Real.log (x / (N : ℝ)) ≤ 1 := (Real.log_le_sub_one_of_pos (div_pos
        (by linarith) hN_pos)).trans (by linarith)
      rw [Real.log_div (by linarith) hN_pos.ne'] at hlog_div
      exact hlog_div
    have hN_mul : (N : ℝ) * (Real.log (N : ℝ) - 9) ≤ (N : ℝ) * primeLogRecipSum x := by
      linarith
    have hN_sub : Real.log (N : ℝ) - 9 ≤ primeLogRecipSum x := le_of_mul_le_mul_left hN_mul hN_pos
    linarith
  exact ⟨hlower, hupper⟩

/-- **Finite Euler-Product Partial Sum Upper Bound** (valid for ALL `s > 0` and ALL `N : ℕ`):
`∑_{n=1}^N n^{-s} ≤ ∏_{p ≤ N, p prime} (1 - p^{-s})⁻¹`. -/
theorem sum_rpow_neg_le_euler_prod {s : ℝ} (hs : 0 < s) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-s) ≤
      ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 - (p : ℝ) ^ (-s))⁻¹ := by
  set P := (Finset.Icc 1 N).filter Nat.Prime
  set K := Nat.log 2 N
  have hprod_le :
      ∏ p ∈ P, ∑ k ∈ Finset.range (K + 1), ((p : ℝ) ^ (-s)) ^ k ≤
        ∏ p ∈ P, (1 - (p : ℝ) ^ (-s))⁻¹ := by
    refine Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) ?_
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have hr0 : 0 ≤ (p : ℝ) ^ (-s) := by positivity
    have hr1 : (p : ℝ) ^ (-s) < 1 := by
      rw [Real.rpow_neg (by linarith), inv_lt_one_iff₀]
      right
      exact Real.one_lt_rpow (by linarith) hs
    have hgeom_id : (1 - (p : ℝ) ^ (-s)) * ∑ k ∈ Finset.range (K + 1), ((p : ℝ) ^ (-s)) ^ k =
        1 - ((p : ℝ) ^ (-s)) ^ (K + 1) := by
      induction K + 1 with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        ring
    have h1sub_pos : 0 < 1 - (p : ℝ) ^ (-s) := by linarith
    have hpow_nn : 0 ≤ ((p : ℝ) ^ (-s)) ^ (K + 1) := pow_nonneg hr0 _
    rw [← one_div]
    exact (le_div_iff₀ h1sub_pos).mpr (by rw [mul_comm]; linarith)
  refine le_trans ?_ hprod_le
  rw [Finset.prod_sum]
  let F : ℕ → (∀ p ∈ P, ℕ) := fun n p _ => padicValNat p n
  have hF_mem : ∀ n ∈ Finset.Icc 1 N, F n ∈ P.pi fun _ => Finset.range (K + 1) := by
    intro n hn
    simp only [Finset.mem_pi, Finset.mem_range, F]
    intro p hp
    have hp_prime := (Finset.mem_filter.mp hp).2
    have hn_pos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hpow_le : p ^ padicValNat p n ≤ n := by
      have := Nat.ordProj_dvd n p
      rw [Nat.factorization_def n hp_prime] at this
      exact Nat.le_of_dvd hn_pos this
    have h2_le : 2 ^ padicValNat p n ≤ N := by
      calc
        2 ^ padicValNat p n ≤ p ^ padicValNat p n :=
          Nat.pow_le_pow_left hp_prime.two_le _
        _ ≤ n := hpow_le
        _ ≤ N := (Finset.mem_Icc.mp hn).2
    have hlog : padicValNat p n ≤ K := by
      by_cases hN0 : N = 0
      · exfalso; have := (Finset.mem_Icc.mp hn).2; omega
      · exact (Nat.le_log_iff_pow_le (by norm_num) hN0).mpr h2_le
    omega
  have hprod_eq : ∀ n ∈ Finset.Icc 1 N, n = ∏ p ∈ P, p ^ padicValNat p n := by
    intro n hn
    have hn_pos : 0 < n := (Finset.mem_Icc.mp hn).1
    have h := Nat.prod_factorization_pow_eq_self hn_pos.ne'
    rw [Finsupp.prod, Nat.support_factorization] at h
    have hsub : n.primeFactors ⊆ P := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hdvd := Nat.dvd_of_mem_primeFactors hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_prime.pos,
        (Nat.le_of_dvd hn_pos hdvd).trans (Finset.mem_Icc.mp hn).2⟩, hp_prime⟩
    have hzero : ∀ p ∈ P, p ∉ n.primeFactors → p ^ padicValNat p n = 1 := by
      intro p hp hnp
      have hp_prime := (Finset.mem_filter.mp hp).2
      have hnd : ¬ p ∣ n := fun hd => hnp (Nat.mem_primeFactors.mpr ⟨hp_prime, hd, hn_pos.ne'⟩)
      simp [padicValNat.eq_zero_of_not_dvd hnd]
    have h' : ∏ a ∈ n.primeFactors, a ^ padicValNat a n = n := by
      calc
        ∏ a ∈ n.primeFactors, a ^ padicValNat a n
          = ∏ a ∈ n.primeFactors, a ^ n.factorization a := by
            refine Finset.prod_congr rfl fun p hp => ?_
            rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]
        _ = n := h
    rw [Finset.prod_subset hsub hzero] at h'
    exact h'.symm
  have hF_inj : Set.InjOn F (Finset.Icc 1 N : Set ℕ) := by
    intro n₁ hn₁ n₂ hn₂ hEq
    rw [hprod_eq n₁ hn₁, hprod_eq n₂ hn₂]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_eq := congrFun (congrFun hEq p) hp
    simp only [F] at hp_eq
    rw [hp_eq]
  have hval : ∀ n ∈ Finset.Icc 1 N,
      (n : ℝ) ^ (-s) = ∏ p ∈ P.attach, ((p.1 : ℝ) ^ (-s)) ^ (F n p.1 p.2) := by
    intro n hn
    conv_lhs => rw [hprod_eq n hn, Nat.cast_prod]
    simp_rw [Nat.cast_pow]
    rw [← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    rw [← Finset.prod_attach P (fun p => ((p : ℝ) ^ padicValNat p n) ^ (-s))]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp only [F]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p.1),
      ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p.1), mul_comm]
  calc
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-s)
      = ∑ n ∈ Finset.Icc 1 N, ∏ p ∈ P.attach, ((p.1 : ℝ) ^ (-s)) ^ (F n p.1 p.2) :=
        Finset.sum_congr rfl hval
    _ ≤ ∑ f ∈ P.pi fun _ => Finset.range (K + 1),
          ∏ p ∈ P.attach, ((p.1 : ℝ) ^ (-s)) ^ (f p.1 p.2) := by
        classical
        have himg : (Finset.Icc 1 N).image F ⊆ P.pi fun _ => Finset.range (K + 1) := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨n, hn, rfl⟩
          exact hF_mem n hn
        have hsum_img :
            ∑ n ∈ Finset.Icc 1 N, ∏ p ∈ P.attach, ((p.1 : ℝ) ^ (-s)) ^ (F n p.1 p.2) =
              ∑ f ∈ (Finset.Icc 1 N).image F,
                ∏ p ∈ P.attach, ((p.1 : ℝ) ^ (-s)) ^ (f p.1 p.2) := by
          symm
          exact Finset.sum_image fun a ha b hb h => hF_inj ha hb h
        rw [hsum_img]
        exact Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ =>
          Finset.prod_nonneg fun _ _ => by positivity

/-- **Explicit Euler-Product / Prime-Reciprocal Exponential Bridge** (`x ≥ 2`):
`exp(-(∑_{p ≤ x} 1/p + 2)) ≤ ∏_{p ≤ x} (1 - 1/p) ≤ exp(-(∑_{p ≤ x} 1/p))`. -/
theorem eulerProdPartial_exp_sandwich {x : ℝ} (_hx : 2 ≤ x) :
    Real.exp (-(primeRecipSum x + 2)) ≤ eulerProdPartial x ∧
      eulerProdPartial x ≤ Real.exp (-(primeRecipSum x)) := by
  have hlog_term : ∀ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      (1 : ℝ) / (p : ℝ) ≤ -Real.log (1 - (p : ℝ)⁻¹) ∧
        -Real.log (1 - (p : ℝ)⁻¹) ≤ (1 : ℝ) / (p : ℝ) + 2 / ((p : ℝ) ^ 2) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    have h1sub_pos : 0 < 1 - (p : ℝ)⁻¹ := by
      have : (p : ℝ)⁻¹ ≤ 1 / 2 := (inv_anti₀ (by norm_num) hp2).trans (by norm_num)
      linarith
    have hlow : (1 : ℝ) / (p : ℝ) ≤ -Real.log (1 - (p : ℝ)⁻¹) := by
      have h := Real.log_le_sub_one_of_pos h1sub_pos
      rw [one_div]
      linarith
    have hhigh : -Real.log (1 - (p : ℝ)⁻¹) ≤ (1 : ℝ) / (p : ℝ) + 2 / ((p : ℝ) ^ 2) := by
      have hinv_pos : 0 < (1 - (p : ℝ)⁻¹)⁻¹ := inv_pos.mpr h1sub_pos
      have h := Real.log_le_sub_one_of_pos hinv_pos
      rw [Real.log_inv] at h
      have hp1_ne : (p : ℝ) - 1 ≠ 0 := by linarith
      have hid : (1 - (p : ℝ)⁻¹)⁻¹ - 1 = (p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹) := by
        field_simp [hp_pos.ne', h1sub_pos.ne', hp1_ne]
        ring
      have hid2 : (p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹) - (1 : ℝ) / (p : ℝ) =
          ((p : ℝ)⁻¹) ^ 2 / (1 - (p : ℝ)⁻¹) := by
        field_simp [hp_pos.ne', h1sub_pos.ne', hp1_ne]
        ring
      have hhalf : 1 / 2 ≤ 1 - (p : ℝ)⁻¹ := by
        have : (p : ℝ)⁻¹ ≤ 1 / 2 := (inv_anti₀ (by norm_num) hp2).trans (by norm_num)
        linarith
      have hbound : ((p : ℝ)⁻¹) ^ 2 / (1 - (p : ℝ)⁻¹) ≤ 2 / (p : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ h1sub_pos (pow_pos hp_pos 2), inv_pow]
        field_simp [hp_pos.ne']
        linarith
      linarith
    exact ⟨hlow, hhigh⟩
  have hprod_pos : 0 < eulerProdPartial x := by
    refine Finset.prod_pos fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have : (p : ℝ)⁻¹ ≤ 1 / 2 := (inv_anti₀ (by norm_num) hp2).trans (by norm_num)
    linarith
  have hlog_prod : -Real.log (eulerProdPartial x) =
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, -Real.log (1 - (p : ℝ)⁻¹) := by
    dsimp only [eulerProdPartial]
    rw [Real.log_prod]
    · rw [Finset.sum_neg_distrib]
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
      have : (p : ℝ)⁻¹ ≤ 1 / 2 := (inv_anti₀ (by norm_num) hp2).trans (by norm_num)
      linarith
  have hsum_low : primeRecipSum x ≤ -Real.log (eulerProdPartial x) := by
    rw [hlog_prod]
    exact Finset.sum_le_sum fun p hp => (hlog_term p hp).1
  have hsq_bound : ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2 ≤ 2 := by
    have hterm : ∀ m ∈ Finset.Icc 2 ⌊x⌋₊,
        (2 : ℝ) / (m : ℝ) ^ 2 ≤ 2 * (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) := by
      intro m hm
      have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
      have hm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m - 1)
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hm1_cast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ m)]; norm_num
      rw [div_le_iff₀ (pow_pos hm_pos 2)]
      field_simp [hm1_pos.ne', hm_pos.ne']
      rw [hm1_cast]
      nlinarith
    have htel : ∀ M : ℕ, 1 ≤ M →
        ∑ m ∈ Finset.Icc 2 M, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) = 1 - 1 / (M : ℝ) := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base => simp
      | succ M hM ih =>
        have hIcc : Finset.Icc 2 (M + 1) = insert (M + 1) (Finset.Icc 2 M) := by
          ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
        have hnot : M + 1 ∉ Finset.Icc 2 M := by simp
        rw [hIcc, Finset.sum_insert hnot, ih]
        simp only [Nat.add_sub_cancel]
        ring
    by_cases hfl1 : 1 ≤ ⌊x⌋₊
    · calc
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2
          ≤ ∑ m ∈ Finset.Icc 2 ⌊x⌋₊, (2 : ℝ) / (m : ℝ) ^ 2 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro p hp
              simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
              exact ⟨hp.2.two_le, hp.1.2⟩
            · intro m _ _; positivity
        _ ≤ ∑ m ∈ Finset.Icc 2 ⌊x⌋₊, 2 * (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) :=
            Finset.sum_le_sum hterm
        _ = 2 * (1 - 1 / (⌊x⌋₊ : ℝ)) := by rw [← Finset.mul_sum, htel ⌊x⌋₊ hfl1]
        _ ≤ 2 := by
            have : 0 ≤ 1 / (⌊x⌋₊ : ℝ) := by positivity
            linarith
    · have hfl0 : ⌊x⌋₊ = 0 := by omega
      simp [hfl0]
  have hsum_high : -Real.log (eulerProdPartial x) ≤ primeRecipSum x + 2 := by
    rw [hlog_prod]
    calc
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, -Real.log (1 - (p : ℝ)⁻¹)
        ≤ ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ((1 : ℝ) / (p : ℝ) + 2 / (p : ℝ) ^ 2) :=
          Finset.sum_le_sum fun p hp => (hlog_term p hp).2
      _ = primeRecipSum x +
            ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2 :=
          Finset.sum_add_distrib
      _ ≤ primeRecipSum x + 2 := by linarith
  have hlow_exp : Real.exp (-(primeRecipSum x + 2)) ≤ eulerProdPartial x := by
    rw [← Real.exp_log hprod_pos]
    exact Real.exp_le_exp.mpr (by linarith)
  have hhigh_exp : eulerProdPartial x ≤ Real.exp (-(primeRecipSum x)) := by
    rw [← Real.exp_log hprod_pos]
    exact Real.exp_le_exp.mpr (by linarith)
  exact ⟨hlow_exp, hhigh_exp⟩

/-- **Mertens' Second Theorem (Explicit Elementary Bounds)** via Section 1 Abel summation,
valid for all `x ≥ 3`:
`|∑_{p ≤ x} 1/p - log(log x)| ≤ 20`. -/
theorem primeRecipSum_bounds {x : ℝ} (hx : 3 ≤ x) :
    |primeRecipSum x - Real.log (Real.log x)| ≤ 20 := by
  set N : ℕ := ⌊x⌋₊
  have hN3 : 3 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN_le : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hx_lt : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  set a : ℕ → ℝ := fun n => if Nat.Prime n then Real.log (n : ℝ) / (n : ℝ) else 0
  set S : ℕ → ℝ := fun k => ∑ n ∈ Finset.Icc 2 k, a n
  have hS_eq : ∀ k : ℕ, 2 ≤ k → S k = primeLogRecipSum (k : ℝ) := by
    intro k _
    simp only [S, primeLogRecipSum, Nat.floor_natCast, a]
    rw [← Finset.sum_filter]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp2, hpk⟩, hp⟩; exact ⟨⟨by omega, hpk⟩, hp⟩
    · rintro ⟨⟨_, hpk⟩, hp⟩; exact ⟨⟨hp.two_le, hpk⟩, hp⟩
  have hrec_eq : primeRecipSum x = ∑ n ∈ Finset.Icc 2 N, a n * (1 / Real.log (n : ℝ)) := by
    simp only [primeRecipSum, a, N, ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    have hfilt_eq : (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime =
        (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime := by
      ext p; simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨_, hpx⟩, hp⟩; exact ⟨⟨hp.two_le, hpx⟩, hp⟩
      · rintro ⟨⟨hp2, hpx⟩, hp⟩; exact ⟨⟨by omega, hpx⟩, hp⟩
    rw [hfilt_eq]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp_prime := (Finset.mem_filter.mp hp).2
    have hlog_ne : Real.log (p : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hp_prime.one_lt)).ne'
    field_simp [hlog_ne]
  have hab := abel_summation_integral_Icc_real a (by omega : 2 ≤ N)
    (φ := fun t => 1 / Real.log t) (φ' := fun t => -1 / (t * (Real.log t) ^ 2))
    (fun t ht => by
      have ht2 : (2 : ℝ) ≤ t := by
        have h := (Set.mem_Icc.mp ht).1
        push_cast at h
        exact h
      have ht_pos : 0 < t := by linarith
      have hlog_ne : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
      have hd_log : HasDerivAt Real.log (t⁻¹) t := Real.hasDerivAt_log ht_pos.ne'
      have hd_div := (hasDerivAt_const t (1 : ℝ)).div hd_log hlog_ne
      refine hd_div.congr_deriv ?_
      field_simp [ht_pos.ne', hlog_ne]
      ring)
    (by
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · exact continuousOn_id.mul ((Real.continuousOn_log.mono (fun t ht => by
          have h := (Set.mem_Icc.mp ht).1
          push_cast at h
          exact (by linarith : (0 : ℝ) < t).ne')).pow 2)
      · intro t ht
        have ht2 : (2 : ℝ) ≤ t := by
          have h := (Set.mem_Icc.mp ht).1
          push_cast at h
          exact h
        have ht_pos : 0 < t := by linarith
        have hlog_ne : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
        exact mul_ne_zero ht_pos.ne' (pow_ne_zero 2 hlog_ne))
  have hsum_eq := hab.1
  have hint_eq := hab.2
  push_cast at hsum_eq hint_eq
  rw [hrec_eq, hsum_eq]
  have hS_bounds : ∀ t ∈ Set.Icc (2 : ℝ) (N : ℝ),
      |∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t| ≤ 11 := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    have hb_fl := primeLogRecipSum_bounds (x := t) (by linarith)
    have hfl_eq : ∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k = primeLogRecipSum t := by
      simp only [primeLogRecipSum, a]
      rw [← Finset.sum_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨_, hpt⟩, hp⟩; exact ⟨⟨hp.pos, hpt⟩, hp⟩
      · rintro ⟨⟨_, hpt⟩, hp⟩; exact ⟨⟨hp.two_le, hpt⟩, hp⟩
    rw [hfl_eq]
    have h2log2 : 2 * Real.log 2 ≤ 2 := by
      have h2 : (2 : ℝ) < Real.exp 1 := by
        have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0); linarith
      have hlog2_lt : Real.log 2 < 1 := by
        calc Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) h2
        _ = 1 := Real.log_exp 1
      linarith
    exact abs_le.mpr ⟨by linarith [hb_fl.1], by linarith [hb_fl.2, h2log2]⟩
  have hmain_int :
      ∫ t in (2 : ℝ)..(N : ℝ), Real.log t * (-1 / (t * (Real.log t) ^ 2)) =
        -(Real.log (Real.log (N : ℝ)) - Real.log (Real.log 2)) := by
    have hd : ∀ t ∈ Set.uIcc (2 : ℝ) (N : ℝ),
        HasDerivAt (fun u => -Real.log (Real.log u))
          (Real.log t * (-1 / (t * (Real.log t) ^ 2))) t := by
      intro t ht
      rw [Set.uIcc_of_le (by exact_mod_cast (by omega : 2 ≤ N) : (2 : ℝ) ≤ N)] at ht
      have ht2 : (2 : ℝ) ≤ t := ht.1
      have ht_pos : 0 < t := by linarith
      have hlog_pos : 0 < Real.log t := Real.log_pos (by linarith)
      have hd1 := Real.hasDerivAt_log ht_pos.ne'
      have hd2 := (Real.hasDerivAt_log hlog_pos.ne').comp t hd1
      have hd3 := hd2.neg
      refine hd3.congr_deriv ?_
      field_simp [ht_pos.ne', hlog_pos.ne']
    have hc : ContinuousOn (fun t => Real.log t * (-1 / (t * (Real.log t) ^ 2)))
        (Set.uIcc (2 : ℝ) (N : ℝ)) := by
      rw [Set.uIcc_of_le (by exact_mod_cast (by omega : 2 ≤ N) : (2 : ℝ) ≤ N)]
      refine ContinuousOn.mul (Real.continuousOn_log.mono fun t ht => by
        have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
        exact (by linarith : (0 : ℝ) < t).ne') ?_
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · exact continuousOn_id.mul ((Real.continuousOn_log.mono fun t ht => by
          have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
          exact (by linarith : (0 : ℝ) < t).ne').pow 2)
      · intro t ht
        have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
        exact mul_ne_zero (by linarith : (0 : ℝ) < t).ne'
          (pow_ne_zero 2 (Real.log_pos (by linarith)).ne')
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
    ring
  have herr_int_bound :
      ∫ t in (2 : ℝ)..(N : ℝ), 11 / (t * (Real.log t) ^ 2) =
        11 * (1 / Real.log 2 - 1 / Real.log (N : ℝ)) := by
    have hd : ∀ t ∈ Set.uIcc (2 : ℝ) (N : ℝ),
        HasDerivAt (fun u => -11 / Real.log u) (11 / (t * (Real.log t) ^ 2)) t := by
      intro t ht
      rw [Set.uIcc_of_le (by exact_mod_cast (by omega : 2 ≤ N) : (2 : ℝ) ≤ N)] at ht
      have ht2 : (2 : ℝ) ≤ t := ht.1
      have ht_pos : 0 < t := by linarith
      have hlog_pos : 0 < Real.log t := Real.log_pos (by linarith)
      have hd1 := (hasDerivAt_const t (-11 : ℝ)).div (Real.hasDerivAt_log ht_pos.ne') hlog_pos.ne'
      refine hd1.congr_deriv ?_
      field_simp [ht_pos.ne', hlog_pos.ne']
      ring
    have hc : ContinuousOn (fun t => (11 : ℝ) / (t * (Real.log t) ^ 2))
        (Set.uIcc (2 : ℝ) (N : ℝ)) := by
      rw [Set.uIcc_of_le (by exact_mod_cast (by omega : 2 ≤ N) : (2 : ℝ) ≤ N)]
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · exact continuousOn_id.mul ((Real.continuousOn_log.mono fun t ht => by
          have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
          exact (by linarith : (0 : ℝ) < t).ne').pow 2)
      · intro t ht
        have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
        exact mul_ne_zero (by linarith : (0 : ℝ) < t).ne'
          (pow_ne_zero 2 (Real.log_pos (by linarith)).ne')
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
    ring
  have hint_main : IntervalIntegrable
      (fun t => Real.log t * (-1 / (t * (Real.log t) ^ 2))) volume 2 (N : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by exact_mod_cast (by omega : 2 ≤ N) : (2 : ℝ) ≤ N)]
    refine ContinuousOn.mul (Real.continuousOn_log.mono fun t ht => by
      have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      exact (by linarith : (0 : ℝ) < t).ne') ?_
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact continuousOn_id.mul ((Real.continuousOn_log.mono fun t ht => by
        have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
        exact (by linarith : (0 : ℝ) < t).ne').pow 2)
    · intro t ht
      have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      exact mul_ne_zero (by linarith : (0 : ℝ) < t).ne'
        (pow_ne_zero 2 (Real.log_pos (by linarith)).ne')
  have hint_err_abs : IntervalIntegrable
      (fun t => (11 : ℝ) / (t * (Real.log t) ^ 2)) volume 2 (N : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by exact_mod_cast (by omega : 2 ≤ N) : (2 : ℝ) ≤ N)]
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact continuousOn_id.mul ((Real.continuousOn_log.mono fun t ht => by
        have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
        exact (by linarith : (0 : ℝ) < t).ne').pow 2)
    · intro t ht
      have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      exact mul_ne_zero (by linarith : (0 : ℝ) < t).ne'
        (pow_ne_zero 2 (Real.log_pos (by linarith)).ne')
  have hint_diff :
      |∫ t in (2 : ℝ)..(N : ℝ),
          (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t) * (-1 / (t * (Real.log t) ^ 2))| ≤
        11 * (1 / Real.log 2 - 1 / Real.log (N : ℝ)) := by
    rw [← herr_int_bound]
    have hint_diff_int : IntervalIntegrable
        (fun t => (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t) * (-1 / (t * (Real.log t) ^ 2)))
        volume 2 (N : ℝ) := by
      have hsub_fun :
          (fun t => (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t) * (-1 / (t * (Real.log t) ^ 2))) =
            fun t => (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k) * (-1 / (t * (Real.log t) ^ 2)) -
              Real.log t * (-1 / (t * (Real.log t) ^ 2)) := by
        funext t; ring
      rw [hsub_fun]
      exact hint_eq.sub hint_main
    have hle_abs := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
      (by exact_mod_cast (by omega : 2 ≤ N) : (2 : ℝ) ≤ N)
      (f := fun t => (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t) * (-1 / (t * (Real.log t) ^ 2)))
    refine hle_abs.trans ?_
    refine intervalIntegral.integral_mono_on (by exact_mod_cast (by omega : 2 ≤ N) : (2 : ℝ) ≤ N)
      hint_diff_int.abs hint_err_abs fun t ht => ?_
    have ht2 : 2 ≤ t := ht.1
    have ht_pos : 0 < t := by linarith
    have hlog_pos : 0 < Real.log t := Real.log_pos (by linarith)
    have hden_pos : 0 < t * (Real.log t) ^ 2 := mul_pos ht_pos (pow_pos hlog_pos 2)
    rw [abs_mul, show |-1 / (t * (Real.log t) ^ 2)| = 1 / (t * (Real.log t) ^ 2) by
      rw [abs_div, abs_neg, abs_one, abs_of_pos hden_pos]]
    have hS := hS_bounds t ht
    calc
      |∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t| * (1 / (t * (Real.log t) ^ 2))
        ≤ 11 * (1 / (t * (Real.log t) ^ 2)) :=
          mul_le_mul_of_nonneg_right hS (by positivity)
      _ = 11 / (t * (Real.log t) ^ 2) := by ring
  have hsplit_int :
      ∫ t in (2 : ℝ)..(N : ℝ), (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k) * (-1 / (t * (Real.log t) ^ 2)) =
        (∫ t in (2 : ℝ)..(N : ℝ), Real.log t * (-1 / (t * (Real.log t) ^ 2))) +
          ∫ t in (2 : ℝ)..(N : ℝ),
            (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t) * (-1 / (t * (Real.log t) ^ 2)) := by
    have hfun : (fun t => (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k) * (-1 / (t * (Real.log t) ^ 2))) =
        fun t => Real.log t * (-1 / (t * (Real.log t) ^ 2)) +
          (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t) * (-1 / (t * (Real.log t) ^ 2)) := by
      funext t; ring
    have hsub_int : IntervalIntegrable
        (fun t => (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t) * (-1 / (t * (Real.log t) ^ 2)))
        volume 2 (N : ℝ) := by
      have hsub_fun :
          (fun t => (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t) * (-1 / (t * (Real.log t) ^ 2))) =
            fun t => (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k) * (-1 / (t * (Real.log t) ^ 2)) -
              Real.log t * (-1 / (t * (Real.log t) ^ 2)) := by
        funext t; ring
      rw [hsub_fun]
      exact hint_eq.sub hint_main
    rw [hfun, intervalIntegral.integral_add hint_main hsub_int]
  have hboundary : |(∑ k ∈ Finset.Icc 2 N, a k) * (1 / Real.log (N : ℝ)) - 1| ≤
      11 / Real.log (N : ℝ) := by
    have hSN : |∑ k ∈ Finset.Icc 2 N, a k - Real.log (N : ℝ)| ≤ 11 := by
      simpa only [Nat.floor_natCast] using
        hS_bounds (N : ℝ) ⟨by exact_mod_cast (by omega : 2 ≤ N), le_rfl⟩
    have hlogN_pos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have heq : (∑ k ∈ Finset.Icc 2 N, a k) * (1 / Real.log (N : ℝ)) - 1 =
        (∑ k ∈ Finset.Icc 2 N, a k - Real.log (N : ℝ)) / Real.log (N : ℝ) := by
      field_simp [hlogN_pos.ne']
    rw [heq, abs_div, abs_of_pos hlogN_pos]
    exact div_le_div_of_nonneg_right hSN hlogN_pos.le
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_gt : 2 / 3 < Real.log 2 := by
    have hexp_lt : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
    have hpow : (Real.exp 1) ^ 2 < (2 : ℝ) ^ 3 := by
      have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      nlinarith
    have hlog := Real.log_lt_log (pow_pos (Real.exp_pos 1) 2) hpow
    rw [Real.log_pow, Real.log_exp, Real.log_pow] at hlog
    push_cast at hlog
    linarith
  have hlog_N_ge : Real.log 3 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN3)
  have hlog3_gt1 : 1 < Real.log 3 := by
    have hexp_lt : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    calc 1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) hexp_lt
  have hlog_log_diff : |Real.log (Real.log x) - Real.log (Real.log (N : ℝ))| ≤ 1 := by
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hle_log : Real.log (N : ℝ) ≤ Real.log x :=
      Real.log_le_log hN_pos hN_le
    have hlog_x_sub_N : Real.log x ≤ Real.log (N : ℝ) + 1 := by
      have hdiv_le : x / (N : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hN_pos]
        have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
        linarith
      have h1 := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < x) hN_pos)
      have h : Real.log (x / (N : ℝ)) ≤ 1 := by linarith [h1, hdiv_le]
      rw [Real.log_div (by linarith) hN_pos.ne'] at h
      linarith
    have hratio : Real.log x / Real.log (N : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hlogN_pos]
      linarith
    have hdiff_le : Real.log (Real.log x) - Real.log (Real.log (N : ℝ)) ≤ 1 := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos hlogx_pos hlogN_pos)
      have h : Real.log (Real.log x / Real.log (N : ℝ)) ≤ 1 := by linarith [h1, hratio]
      rw [Real.log_div hlogx_pos.ne' hlogN_pos.ne'] at h
      exact h
    have hdiff_nn : 0 ≤ Real.log (Real.log x) - Real.log (Real.log (N : ℝ)) :=
      sub_nonneg.mpr (Real.log_le_log hlogN_pos hle_log)
    rw [abs_of_nonneg hdiff_nn]
    exact hdiff_le
  have hlog_log2_bound : |Real.log (Real.log 2)| ≤ 1 / 2 := by
    have hlog2_lt1 : Real.log 2 < 1 := by
      have h2 : (2 : ℝ) < Real.exp 1 := by
        have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0); linarith
      calc Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) h2
      _ = 1 := Real.log_exp 1
    have hinv_le : (Real.log 2)⁻¹ ≤ 3 / 2 := by
      have h := inv_anti₀ (by norm_num : (0 : ℝ) < 2 / 3) hlog2_gt.le
      linarith
    have hlog_inv : -Real.log (Real.log 2) ≤ 1 / 2 := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hlog2_pos)
      rw [Real.log_inv] at h
      linarith
    have hneg : Real.log (Real.log 2) ≤ 0 := Real.log_nonpos hlog2_pos.le hlog2_lt1.le
    rw [abs_of_nonpos hneg]
    exact hlog_inv
  have h11_cancel :
      |(∑ k ∈ Finset.Icc 2 N, a k) * (1 / Real.log (N : ℝ)) - 1| +
        |∫ t in (2 : ℝ)..(N : ℝ),
          (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t) * (-1 / (t * (Real.log t) ^ 2))| ≤
      11 / Real.log 2 := by
    have h := add_le_add hboundary hint_diff
    refine h.trans_eq ?_
    ring
  have h11_val : 11 / Real.log 2 ≤ 33 / 2 := by
    have hinv : 1 / Real.log 2 ≤ 3 / 2 := by
      rw [one_div]; have := inv_anti₀ (by norm_num : (0 : ℝ) < 2 / 3) hlog2_gt.le; linarith
    have : 11 / Real.log 2 = 11 * (1 / Real.log 2) := by ring
    linarith
  rw [hsplit_int, hmain_int]
  have hdecomp :
      (∑ k ∈ Finset.Icc 2 N, a k) * (1 / Real.log (N : ℝ)) -
          (-(Real.log (Real.log (N : ℝ)) - Real.log (Real.log 2)) +
            ∫ t in (2 : ℝ)..(N : ℝ),
              (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t) * (-1 / (t * (Real.log t) ^ 2))) -
          Real.log (Real.log x) =
        ((∑ k ∈ Finset.Icc 2 N, a k) * (1 / Real.log (N : ℝ)) - 1) +
          (-∫ t in (2 : ℝ)..(N : ℝ),
              (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t) * (-1 / (t * (Real.log t) ^ 2))) +
          (1 - Real.log (Real.log 2) + (Real.log (Real.log (N : ℝ)) - Real.log (Real.log x))) := by
    ring
  rw [hdecomp]
  have htri1 :
      |((∑ k ∈ Finset.Icc 2 N, a k) * (1 / Real.log (N : ℝ)) - 1) +
          (-∫ t in (2 : ℝ)..(N : ℝ),
              (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t) * (-1 / (t * (Real.log t) ^ 2))) +
          (1 - Real.log (Real.log 2) + (Real.log (Real.log (N : ℝ)) - Real.log (Real.log x)))| ≤
        |(∑ k ∈ Finset.Icc 2 N, a k) * (1 / Real.log (N : ℝ)) - 1| +
          |∫ t in (2 : ℝ)..(N : ℝ),
              (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t) * (-1 / (t * (Real.log t) ^ 2))| +
          |(1 : ℝ) - Real.log (Real.log 2) +
              (Real.log (Real.log (N : ℝ)) - Real.log (Real.log x))| := by
    have h1 := abs_add_le
      (((∑ k ∈ Finset.Icc 2 N, a k) * (1 / Real.log (N : ℝ)) - 1) +
        (-∫ t in (2 : ℝ)..(N : ℝ),
            (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t) * (-1 / (t * (Real.log t) ^ 2))))
      (1 - Real.log (Real.log 2) + (Real.log (Real.log (N : ℝ)) - Real.log (Real.log x)))
    have h2 := abs_add_le
      ((∑ k ∈ Finset.Icc 2 N, a k) * (1 / Real.log (N : ℝ)) - 1)
      (-∫ t in (2 : ℝ)..(N : ℝ),
          (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, a k - Real.log t) * (-1 / (t * (Real.log t) ^ 2)))
    rw [abs_neg] at h2
    linarith
  have h12 : |(1 : ℝ) - Real.log (Real.log 2)| ≤ 1 + |Real.log (Real.log 2)| := by
    rw [sub_eq_add_neg]
    exact (abs_add_le (1 : ℝ) (-Real.log (Real.log 2))).trans (by simp)
  have hLN : |Real.log (Real.log (N : ℝ)) - Real.log (Real.log x)| =
      |Real.log (Real.log x) - Real.log (Real.log (N : ℝ))| := abs_sub_comm _ _
  have htri2 : |(1 : ℝ) - Real.log (Real.log 2) +
        (Real.log (Real.log (N : ℝ)) - Real.log (Real.log x))| ≤
      1 + |Real.log (Real.log 2)| + |Real.log (Real.log x) - Real.log (Real.log (N : ℝ))| := by
    have h := abs_add_le ((1 : ℝ) - Real.log (Real.log 2))
      (Real.log (Real.log (N : ℝ)) - Real.log (Real.log x))
    linarith
  linarith

/-- **Mertens' Third Theorem (Explicit Elementary Two-Sided Bounds)** for all `x ≥ 3`:
`exp(-22) / log x ≤ ∏_{p ≤ x} (1 - 1/p) ≤ exp(20) / log x`. -/
theorem eulerProdPartial_bounds {x : ℝ} (hx : 3 ≤ x) :
    Real.exp (-22) / Real.log x ≤ eulerProdPartial x ∧
      eulerProdPartial x ≤ Real.exp 20 / Real.log x := by
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hsand := eulerProdPartial_exp_sandwich (by linarith : 2 ≤ x)
  have hm2 := primeRecipSum_bounds hx
  have hm2_le : Real.log (Real.log x) - 20 ≤ primeRecipSum x ∧
      primeRecipSum x ≤ Real.log (Real.log x) + 20 := abs_le.mp hm2 |> fun ⟨h1, h2⟩ =>
    ⟨by linarith, by linarith⟩
  have hlow : Real.exp (-22) / Real.log x ≤ eulerProdPartial x := by
    have hexp_eq : Real.exp (-22) / Real.log x = Real.exp (-(Real.log (Real.log x) + 22)) := by
      rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hlog_pos,
        div_eq_mul_inv, mul_comm]
    rw [hexp_eq]
    refine le_trans ?_ hsand.1
    exact Real.exp_le_exp.mpr (by linarith [hm2_le.2])
  have hhigh : eulerProdPartial x ≤ Real.exp 20 / Real.log x := by
    have hexp_eq : Real.exp 20 / Real.log x = Real.exp (-(Real.log (Real.log x) - 20)) := by
      rw [neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_neg, Real.exp_log hlog_pos,
        div_eq_mul_inv, mul_comm]
    rw [hexp_eq]
    refine le_trans hsand.2 ?_
    exact Real.exp_le_exp.mpr (by linarith [hm2_le.1])
  exact ⟨hlow, hhigh⟩

end

end Arith4Ext.AnalyticNT


