import RHDirect.Stage6EffectivePNT
import RHDirect.Stage7PNTInAP
import RHDirect.Stage3RealAnalyticLandau
import RHDirect.Stage2DirichletAP
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# RHDirect.Stage8MertensTheorems

**UNCONDITIONAL PROOF OF ALL THREE OF MERTENS'S CLASSIC THEOREMS (WITH THE EXACT `e^{-γ}` CONSTANT)
AND MERTENS'S THEOREM IN ARITHMETIC PROGRESSIONS** (0 assumptions, 0 `sorry`, 0 custom `axiom`s)
in pure Mathlib `v4.33.1`.

## Main Results
1. **Mertens' First Theorem (Sharp Quantitative + Classical + Exact Constant)**:
   - `mertens_first_theorem_sharp`:
     `∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |∑_{p ≤ x} log p / p - (log x + mertensFirstConst)| ≤ C exp(-c √(log x))`.
   - `mertens_first_theorem`:
     `∃ C > 0, ∀ x ≥ 2, |∑_{p ≤ x} log p / p - log x| ≤ C`.
   - `integral_psi_sub_id_div_sq_eq_unconditional`:
     `∫_1^∞ (ψ(t) - t) / t² dt = -(1 + γ)` (completely unconditional via `effective_pnt_psi` + DCT).
   - `mertensFirstConst_eq`:
     `mertensFirstConst = -γ - ∑'_p log p / (p (p - 1))`.
2. **Mertens' Second Theorem & Exact Euler–Mascheroni Constant Identity**:
   - `meisselMertensConst`: exact Meissel–Mertens constant `M`.
   - `mertens_second_theorem`:
     `∃ C > 0, ∀ x ≥ 3, |∑_{p ≤ x} 1 / p - (log (log x) + meisselMertensConst)| ≤ C / log x`.
   - `meisselMertensConst_eq_eulerMascheroni_add_tsum`:
     `meisselMertensConst = γ + ∑' p : Nat.Primes, (log (1 - 1/p) + 1/p)`
     proved unconditionally by comparing two limits of `∑_p p^{-σ} - log (1 / (σ - 1))` as `σ → 1⁺`:
     Mertens II + `∫_0^∞ log u · e^{-u} du = Γ'(1) = -γ` gives `M - γ`, while the Euler product
     `riemannZeta_eulerProduct_exp_log` + `riemannZeta_residue_one` gives `∑_p (log (1 - 1/p) + 1/p)`.
3. **Mertens' Third Theorem (Asymptotic + Quantitative `O(1 / log x)`)**:
   - `mertens_third_theorem_quant`:
     `∃ C > 0, ∀ x ≥ 3, |log x * ∏_{p ≤ x} (1 - 1/p) - e^{-γ}| ≤ C / log x`.
   - `mertens_third_theorem`:
     `Tendsto (fun x : ℝ => Real.log x * ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)))`.
4. **Mertens' Theorems in Arithmetic Progressions (First & Second)**:
   For EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `a` with `Nat.Coprime a q`:
   - `mertens_first_theorem_AP`:
     `∃ C > 0, ∀ x ≥ 2, |∑_{p ≤ x, p ≡ a [MOD q]} log p / p - (1 / φ(q)) * log x| ≤ C`.
   - `mertens_second_theorem_AP`:
     `∃ M_qa : ℝ, ∃ C > 0, ∀ x ≥ 3, |∑_{p ≤ x, p ≡ a [MOD q]} 1 / p - ((1 / φ(q)) * log (log x) + M_qa)| ≤ C / log x`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage8MertensTheorems

/-! ## Section 1: Real Abelian / Partial Summation & Exponential-Decay Tail Integrals -/

/-- Real step summatory function `A(x) = ∑_{1 ≤ n ≤ ⌊x⌋₊} a_n`. -/
def realStepSum (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n

theorem realStepSum_const_on_Ico (a : ℕ → ℝ) (k : ℕ) {t : ℝ} (ht1 : (k : ℝ) ≤ t)
    (ht2 : t < ((k + 1 : ℕ) : ℝ)) :
    realStepSum a t = realStepSum a (k : ℝ) := by
  unfold realStepSum
  have hfl : ⌊t⌋₊ = k := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg k) ht1)).mpr
    ⟨ht1, by exact_mod_cast ht2⟩
  rw [hfl, Nat.floor_natCast]

theorem measurable_realStepSum (a : ℕ → ℝ) : Measurable (realStepSum a) := by
  have h : realStepSum a = (fun k : ℕ => ∑ n ∈ Finset.Icc 1 k, a n) ∘ Nat.floor := rfl
  rw [h]
  exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor

/-- **Real General Abelian / Partial Summation on `[1, x]`** (extracted from
`Stage3RealAnalyticLandau.abel_summation_general`):
`∑_{1 ≤ n ≤ ⌊x⌋₊} a_n φ(n) = A(x) φ(x) - ∫_1^x A(t) φ'(t) dt`. -/
theorem abel_summation_real (a : ℕ → ℝ) {x : ℝ} (hx : 1 ≤ x) {φ φ' : ℝ → ℝ}
    (hd : ∀ t ∈ Set.Icc (1 : ℝ) x, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.Icc (1 : ℝ) x)) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * φ (n : ℝ) =
      realStepSum a x * φ x - ∫ t in (1 : ℝ)..x, realStepSum a t * φ' t := by
  have hab := Stage3RealAnalyticLandau.abel_summation_general
    (a := fun n => (a n : ℂ)) hx
    (φ := fun t => (φ t : ℂ)) (φ' := fun t => (φ' t : ℂ))
    (fun t ht => (hd t ht).ofReal_comp)
    (Complex.continuous_ofReal.comp_continuousOn hc)
  have hre := congrArg Complex.re hab
  have hstep : ∀ t : ℝ, Stage3RealAnalyticLandau.stepSum (fun n => (a n : ℂ)) t =
      (realStepSum a t : ℂ) := fun t => by
    unfold Stage3RealAnalyticLandau.stepSum realStepSum
    rw [Complex.ofReal_sum]
  have hLHS : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (a n : ℂ) * (φ (n : ℝ) : ℂ)).re =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * φ (n : ℝ) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hRHS : (Stage3RealAnalyticLandau.stepSum (fun n => (a n : ℂ)) x * (φ x : ℂ) -
        ∫ t in (1 : ℝ)..x, Stage3RealAnalyticLandau.stepSum (fun n => (a n : ℂ)) t * (φ' t : ℂ)).re =
      realStepSum a x * φ x - ∫ t in (1 : ℝ)..x, realStepSum a t * φ' t := by
    have hfun : (fun t : ℝ => Stage3RealAnalyticLandau.stepSum (fun n => (a n : ℂ)) t * (φ' t : ℂ)) =
        fun t : ℝ => ((realStepSum a t * φ' t : ℝ) : ℂ) := by
      funext t; rw [hstep t, ← Complex.ofReal_mul]
    rw [hstep x, ← Complex.ofReal_mul, hfun, intervalIntegral.integral_ofReal,
      Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re]
  rw [hLHS, hRHS] at hre
  exact hre

private lemma intervalIntegral_realStepSum_unit (a : ℕ → ℝ) (k : ℕ) {φ φ' : ℝ → ℝ}
    (hd : ∀ t ∈ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ), HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ))) :
    ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), realStepSum a t * φ' t =
      realStepSum a (k : ℝ) * (φ ((k + 1 : ℕ) : ℝ) - φ (k : ℝ)) := by
  have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (k : ℝ) ((k + 1 : ℕ) : ℝ) →
      realStepSum a t * φ' t = realStepSum a (k : ℝ) * φ' t := by
    have hne : ∀ᵐ t ∂volume, t ≠ ((k + 1 : ℕ) : ℝ) := by rw [ae_iff]; simp
    filter_upwards [hne] with t hne ht
    rw [Set.uIoc_of_le hle, Set.mem_Ioc] at ht
    rw [realStepSum_const_on_Ico a k ht.1.le (lt_of_le_of_ne ht.2 hne)]
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]

private lemma intervalIntegrable_realStepSum_mul_unit (a : ℕ → ℝ) (k : ℕ) {φ' : ℝ → ℝ}
    (hc : ContinuousOn φ' (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ))) :
    IntervalIntegrable (fun t => realStepSum a t * φ' t) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
  have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hconst : IntervalIntegrable (fun t => realStepSum a (k : ℝ) * φ' t) volume (k : ℝ)
      ((k + 1 : ℕ) : ℝ) := hc.intervalIntegrable.const_mul _
  refine hconst.congr_ae ?_
  have hne : ∀ᵐ t ∂volume, t ≠ ((k + 1 : ℕ) : ℝ) := by rw [ae_iff]; simp
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards [hne] with t hne ht
  rw [Set.uIoc_of_le hle, Set.mem_Ioc] at ht
  exact (congrArg (· * φ' t) (realStepSum_const_on_Ico a k ht.1.le (lt_of_le_of_ne ht.2 hne))).symm

/-- **Real General Abelian / Partial Summation Starting at `2`**:
for any `a : ℕ → ℝ` with `a 1 = 0`, any `x ≥ 2`, and any `C¹` weight `φ` on `[2, x]`:
`∑_{2 ≤ n ≤ ⌊x⌋₊} a_n φ(n) = A(x) φ(x) - ∫_2^x A(t) φ'(t) dt`. -/
theorem abel_summation_from_two (a : ℕ → ℝ) (ha1 : a 1 = 0) {x : ℝ} (hx : 2 ≤ x) {φ φ' : ℝ → ℝ}
    (hd : ∀ t ∈ Set.Icc (2 : ℝ) x, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.Icc (2 : ℝ) x)) :
    ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, a n * φ (n : ℝ) =
      realStepSum a x * φ x - ∫ t in (2 : ℝ)..x, realStepSum a t * φ' t := by
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfl_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hint_nat : ∀ N : ℕ, 2 ≤ N → (N : ℝ) ≤ x →
      IntervalIntegrable (fun t => realStepSum a t * φ' t) volume (2 : ℝ) (N : ℝ) ∧
      ∑ n ∈ Finset.Icc 2 N, a n * φ (n : ℝ) =
        realStepSum a (N : ℝ) * φ (N : ℝ) - ∫ t in (2 : ℝ)..(N : ℝ), realStepSum a t * φ' t := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      intro _
      have hIcc12 : Finset.Icc 1 2 = {1, 2} := by decide
      simp [realStepSum, hIcc12, ha1]
    | succ m hm ih =>
      intro hm1
      have hm_le : (m : ℝ) ≤ x := le_trans (by push_cast; linarith) hm1
      obtain ⟨hint_m, heq_m⟩ := ih hm_le
      have hsub_u : Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ) ⊆ Set.Icc (2 : ℝ) x := by
        rw [Set.uIcc_of_le (by push_cast; linarith)]
        intro t ht
        have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        exact ⟨le_trans hm2R ht.1, le_trans ht.2 hm1⟩
      have hint_step := intervalIntegrable_realStepSum_mul_unit a m (hc.mono hsub_u)
      have hval_step := intervalIntegral_realStepSum_unit a m (fun t ht => hd t (hsub_u ht))
        (hc.mono hsub_u)
      refine ⟨hint_m.trans hint_step, ?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals hint_m hint_step, hval_step]
      have hIcc2 : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hIcc1 : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot2 : m + 1 ∉ Finset.Icc 2 m := by simp
      have hnot1 : m + 1 ∉ Finset.Icc 1 m := by simp
      have hstep_succ : realStepSum a ((m + 1 : ℕ) : ℝ) = realStepSum a (m : ℝ) + a (m + 1) := by
        unfold realStepSum
        rw [Nat.floor_natCast, Nat.floor_natCast, hIcc1, Finset.sum_insert hnot1]
        ring
      rw [hIcc2, Finset.sum_insert hnot2, heq_m, hstep_succ]
      ring
  obtain ⟨hint_N, heq_N⟩ := hint_nat ⌊x⌋₊ hN2 hfl_le
  have hsub_tail : Set.uIcc (⌊x⌋₊ : ℝ) x ⊆ Set.Icc (2 : ℝ) x := by
    rw [Set.uIcc_of_le hfl_le]
    intro t ht
    have hfl2 : (2 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hN2
    exact ⟨le_trans hfl2 ht.1, ht.2⟩
  have htail_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (⌊x⌋₊ : ℝ) x →
      realStepSum a t * φ' t = realStepSum a (⌊x⌋₊ : ℝ) * φ' t := by
    have hne : ∀ᵐ t ∂volume, t ≠ x := by rw [ae_iff]; simp
    filter_upwards [hne] with t hne ht
    rw [Set.uIoc_of_le hfl_le, Set.mem_Ioc] at ht
    have hlt : t < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := lt_trans (lt_of_le_of_ne ht.2 hne) (by
      push_cast; exact Nat.lt_floor_add_one x)
    rw [realStepSum_const_on_Ico a ⌊x⌋₊ ht.1.le hlt]
  have hint_tail : IntervalIntegrable (fun t => realStepSum a t * φ' t) volume (⌊x⌋₊ : ℝ) x := by
    refine ((hc.mono hsub_tail).intervalIntegrable.const_mul (realStepSum a (⌊x⌋₊ : ℝ))).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [htail_ae] with t ht hmem using (ht hmem).symm
  have hval_tail : ∫ t in (⌊x⌋₊ : ℝ)..x, realStepSum a t * φ' t =
      realStepSum a (⌊x⌋₊ : ℝ) * (φ x - φ (⌊x⌋₊ : ℝ)) := by
    rw [intervalIntegral.integral_congr_ae htail_ae, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsub_tail ht))
        (hc.mono hsub_tail).intervalIntegrable]
  have hstep_x : realStepSum a x = realStepSum a (⌊x⌋₊ : ℝ) := by
    unfold realStepSum; rw [Nat.floor_natCast]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_N hint_tail, hval_tail, heq_N,
    hstep_x]
  ring

/-- Elementary sub-exponential decay bound: for any `c > 0` and `α > 0`, there exists `K > 0`
such that `exp(-c * (log t)^α) ≤ K / (log t)^2` for all `t ≥ 2`. -/
lemma exp_neg_rpow_log_le_div_log_sq {c α : ℝ} (hc : 0 < c) (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 2 ≤ t →
      Real.exp (-c * (Real.log t) ^ α) ≤ K / (Real.log t) ^ 2 := by
  set k : ℕ := ⌈2 / α⌉₊ with hk_def
  have hk_ge : 2 / α ≤ (k : ℝ) := Nat.le_ceil _
  have hka : (2 : ℝ) ≤ (k : ℝ) * α := by
    have := mul_le_mul_of_nonneg_right hk_ge hα.le
    rwa [div_mul_cancel₀ _ hα.ne'] at this
  set K : ℝ := max ((k.factorial : ℝ) / c ^ k) 1 with hK_def
  have hK_pos : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨K, hK_pos, fun t ht => ?_⟩
  have hLt_pos : 0 < Real.log t := Real.log_pos (by linarith)
  by_cases hL1 : 1 ≤ Real.log t
  · set u : ℝ := c * (Real.log t) ^ α with hu_def
    have hu_pos : 0 < u := mul_pos hc (Real.rpow_pos_of_pos hLt_pos α)
    have hpow_le_exp : u ^ k / (k.factorial : ℝ) ≤ Real.exp u :=
      Real.pow_div_factorial_le_exp u hu_pos.le k
    have hexp_neg : Real.exp (-u) ≤ (k.factorial : ℝ) / u ^ k := by
      rw [Real.exp_neg, le_div_iff₀ (pow_pos hu_pos k)]
      have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
      have h1 := mul_le_mul_of_nonneg_left hpow_le_exp (Real.exp_pos (-u)).le
      have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      rw [Real.exp_neg] at h1 h2
      have h3 : (Real.exp u)⁻¹ * (u ^ k / (k.factorial : ℝ)) ≤ 1 := by linarith
      have h4 := mul_le_mul_of_nonneg_right h3 hfac_pos.le
      rw [mul_div_assoc', div_mul_cancel₀ _ hfac_pos.ne', one_mul] at h4
      exact h4
    have hlog_pow : (Real.log t) ^ 2 ≤ ((Real.log t) ^ α) ^ k := by
      rw [← Real.rpow_natCast ((Real.log t) ^ α) k, ← Real.rpow_mul hLt_pos.le,
        show (Real.log t) ^ 2 = (Real.log t) ^ (2 : ℝ) by norm_cast]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hu_pow : u ^ k = c ^ k * ((Real.log t) ^ α) ^ k := mul_pow c ((Real.log t) ^ α) k
    have hneg_eq : -c * (Real.log t) ^ α = -u := by dsimp only [u]; ring
    rw [hneg_eq]
    calc Real.exp (-u)
        ≤ (k.factorial : ℝ) / u ^ k := hexp_neg
      _ = ((k.factorial : ℝ) / c ^ k) / ((Real.log t) ^ α) ^ k := by
          rw [hu_pow, div_div]
      _ ≤ ((k.factorial : ℝ) / c ^ k) / (Real.log t) ^ 2 := by
          refine div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hLt_pos) hlog_pow
      _ ≤ K / (Real.log t) ^ 2 :=
          div_le_div_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  · push Not at hL1
    have hsq_le1 : (Real.log t) ^ 2 ≤ 1 := by nlinarith
    have hexp_le1 : Real.exp (-c * (Real.log t) ^ α) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have := Real.rpow_nonneg hLt_pos.le α
      nlinarith
    have h1_le : (1 : ℝ) ≤ K / (Real.log t) ^ 2 := by
      rw [one_le_div (sq_pos_of_pos hLt_pos)]
      exact hsq_le1.trans (le_max_right _ _)
    linarith

/-- Exact improper integral `∫_a^∞ (t * (log t)^2)⁻¹ dt = (log a)⁻¹` for every `a > 1`,
together with integrability on `Ioi a`. -/
lemma integrableOn_and_integral_Ioi_inv_mul_log_sq {a : ℝ} (ha : 1 < a) :
    IntegrableOn (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹) (Ioi a) ∧
    ∫ t in Ioi a, (t * (Real.log t) ^ 2)⁻¹ = (Real.log a)⁻¹ := by
  have hd : ∀ t ∈ Ici a,
      HasDerivAt (fun u : ℝ => -(Real.log u)⁻¹) ((t * (Real.log t) ^ 2)⁻¹) t := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans ht1).ne'
    have hlt0 : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have h1 : HasDerivAt (fun u : ℝ => (Real.log u)⁻¹) (-(t⁻¹) / (Real.log t) ^ 2) t :=
      (Real.hasDerivAt_log ht0).inv hlt0
    refine h1.neg.congr_deriv ?_
    field_simp [ht0, hlt0]
  have hlim : Tendsto (fun t : ℝ => -(Real.log t)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    simpa using h1.neg
  have hnn : ∀ t ∈ Ioi a, 0 ≤ (t * (Real.log t) ^ 2)⁻¹ := fun t ht => by
    have ht0 : 0 < t := zero_lt_one.trans (ha.trans ht)
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg' hd hnn hlim
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim
  rw [zero_sub, neg_neg] at hval
  exact ⟨hint, hval⟩

/-- Integrability of `exp(-c * (log t)^α) / t` on `Ioi 2` for any `c > 0`, `α > 0`. -/
lemma integrableOn_exp_neg_rpow_log_div_id {c α : ℝ} (hc : 0 < c) (hα : 0 < α) :
    IntegrableOn (fun t : ℝ => Real.exp (-c * (Real.log t) ^ α) / t) (Ioi (2 : ℝ)) := by
  obtain ⟨K, hK_pos, hK⟩ := exp_neg_rpow_log_le_div_log_sq hc hα
  have hdom : IntegrableOn (fun t : ℝ => K * (t * (Real.log t) ^ 2)⁻¹) (Ioi (2 : ℝ)) :=
    (integrableOn_and_integral_Ioi_inv_mul_log_sq (by norm_num : (1 : ℝ) < 2)).1.const_mul K
  refine Integrable.mono' hdom ?_ ?_
  · have hm : Measurable (fun t : ℝ => Real.exp (-c * (Real.log t) ^ α) / t) :=
      (Real.measurable_exp.comp (measurable_const.mul (Real.measurable_log.pow_const α))).div
        measurable_id
    exact hm.aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := by linarith [Set.mem_Ioi.mp ht]
    rw [Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le ht0.le)]
    calc Real.exp (-c * (Real.log t) ^ α) / t
        ≤ (K / (Real.log t) ^ 2) / t :=
          div_le_div_of_nonneg_right (hK t (Set.mem_Ioi.mp ht).le) ht0.le
      _ = K * (t * (Real.log t) ^ 2)⁻¹ := by
          field_simp [ht0.ne', (Real.log_pos (by linarith [Set.mem_Ioi.mp ht] : (1 : ℝ) < t)).ne']

/-! ## Section 2: Mertens' First Theorem (Sharp Quantitative, Classical & Exact Constant) -/

/-- Mertens' first prime sum `∑_{p ≤ x} log p / p`. -/
def mertensSum1 (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)

/-- Exact constant `c₁ = 1 + ∫_1^∞ (θ(t) - t) / t² dt` in Mertens' first theorem. -/
def mertensFirstConst : ℝ :=
  1 + ∫ t in Ioi (1 : ℝ), (Chebyshev.theta t - t) / t ^ 2

private lemma realStepSum_primeLog_eq_theta (t : ℝ) :
    realStepSum (fun n : ℕ => if n.Prime then Real.log (n : ℝ) else 0) t = Chebyshev.theta t := by
  unfold realStepSum Chebyshev.theta
  rw [← Finset.sum_filter]
  congr 1

/-- Exact Abelian-summation identity for `mertensSum1 x - log x` for all `x ≥ 1`. -/
theorem mertensSum1_sub_log_eq {x : ℝ} (hx : 1 ≤ x) :
    mertensSum1 x - Real.log x =
      (Chebyshev.theta x - x) / x + 1 + ∫ t in (1 : ℝ)..x, (Chebyshev.theta t - t) / t ^ 2 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hd : ∀ t ∈ Set.Icc (1 : ℝ) x, HasDerivAt (fun u : ℝ => u⁻¹) (-(t ^ 2)⁻¹) t := fun t ht =>
    hasDerivAt_inv (zero_lt_one.trans_le ht.1).ne'
  have hc : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc (1 : ℝ) x) :=
    (ContinuousOn.inv₀ (continuousOn_pow 2) fun t ht =>
      pow_ne_zero 2 (zero_lt_one.trans_le ht.1).ne').neg
  have hab := abel_summation_real (fun n : ℕ => if n.Prime then Real.log (n : ℝ) else 0) hx hd hc
  have hLHS : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (if n.Prime then Real.log (n : ℝ) else 0) * (n : ℝ)⁻¹ = mertensSum1 x := by
    unfold mertensSum1
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> simp [div_eq_mul_inv]
  rw [hLHS] at hab
  have hstep_x : realStepSum (fun n : ℕ => if n.Prime then Real.log (n : ℝ) else 0) x =
      Chebyshev.theta x := realStepSum_primeLog_eq_theta x
  have hint_rew : ∫ t in (1 : ℝ)..x,
        realStepSum (fun n : ℕ => if n.Prime then Real.log (n : ℝ) else 0) t * -(t ^ 2)⁻¹ =
      -(∫ t in (1 : ℝ)..x, Chebyshev.theta t / t ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [realStepSum_primeLog_eq_theta t]
    ring
  rw [hstep_x, hint_rew, sub_neg_eq_add] at hab
  have hint_log : ∫ t in (1 : ℝ)..x, (1 : ℝ) / t = Real.log x := by
    simpa [one_div, Real.log_one] using integral_inv_of_pos zero_lt_one hx0
  have hth_int : IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / t ^ 2) volume (1 : ℝ) x := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr ?_
    refine Integrable.mono'
      (integrableOn_const (C := Chebyshev.theta x) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
    · have hm : Measurable Chebyshev.theta := by
        have h : Chebyshev.theta =
            (fun k : ℕ => ∑ p ∈ (Finset.Ioc 0 k).filter Nat.Prime, Real.log (p : ℝ)) ∘ Nat.floor := rfl
        rw [h]; exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
      exact (hm.div (continuous_pow 2).measurable).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
      have htsq : 1 ≤ t ^ 2 := by nlinarith [ht.1]
      rw [Real.norm_of_nonneg (div_nonneg (Chebyshev.theta_nonneg t) (sq_nonneg t))]
      exact (div_le_self (Chebyshev.theta_nonneg t) htsq).trans (Chebyshev.theta_mono ht.2)
  have hinv_int : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / t) volume (1 : ℝ) x := by
    have hc1 : ContinuousOn (fun t : ℝ => (1 : ℝ) / t) (Set.uIcc 1 x) := by
      rw [Set.uIcc_of_le hx]
      exact continuousOn_const.div continuousOn_id fun t ht => (zero_lt_one.trans_le ht.1).ne'
    exact hc1.intervalIntegrable
  have hpt : Set.EqOn (fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2)
      (fun t : ℝ => Chebyshev.theta t / t ^ 2 - 1 / t) (Set.uIcc 1 x) := by
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht.1).ne'
    dsimp only; field_simp
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub hth_int hinv_int,
    hint_log, hab]
  field_simp [hx0.ne']
  ring

/-- Unconditional integrability of `(Chebyshev.theta t - t) / t²` on `(1, ∞)`. -/
theorem integrableOn_theta_sub_id_div_sq :
    IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2) (Ioi (1 : ℝ)) := by
  obtain ⟨c, hc, C, hC, hth⟩ := Stage6EffectivePNT.effective_pnt_theta
  have hmeas_th : Measurable Chebyshev.theta := by
    have h : Chebyshev.theta =
        (fun k : ℕ => ∑ p ∈ (Finset.Ioc 0 k).filter Nat.Prime, Real.log (p : ℝ)) ∘ Nat.floor := rfl
    rw [h]; exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
  have hmeas : Measurable (fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2) :=
    (hmeas_th.sub measurable_id).div (continuous_pow 2).measurable
  have h12 : IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2) (Ioc (1 : ℝ) 2) := by
    refine Integrable.mono'
      (integrableOn_const (C := Chebyshev.theta 2 + 2) (hs := measure_Ioc_lt_top.ne))
      hmeas.aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    have htsq : 1 ≤ t ^ 2 := by nlinarith [ht.1]
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
    refine (div_le_self (abs_nonneg _) htsq).trans ?_
    have hle : |Chebyshev.theta t - t| ≤ Chebyshev.theta t + t := by
      have := Chebyshev.theta_nonneg t
      rcases abs_cases (Chebyshev.theta t - t) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith [ht.1]
    linarith [Chebyshev.theta_mono ht.2, ht.2]
  have h2inf : IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2) (Ioi (2 : ℝ)) := by
    have hdom : IntegrableOn (fun t : ℝ => C * (Real.exp (-c * (Real.log t) ^ (1 / 2 : ℝ)) / t))
        (Ioi (2 : ℝ)) :=
      (integrableOn_exp_neg_rpow_log_div_id hc (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht2 : 2 ≤ t := (Set.mem_Ioi.mp ht).le
    have ht0 : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
    have hbd := hth t ht2
    rw [Real.sqrt_eq_rpow] at hbd
    calc |Chebyshev.theta t - t| / t ^ 2
        ≤ (C * t * Real.exp (-c * (Real.log t) ^ (1 / 2 : ℝ))) / t ^ 2 :=
          div_le_div_of_nonneg_right hbd (sq_nonneg t)
      _ = C * (Real.exp (-c * (Real.log t) ^ (1 / 2 : ℝ)) / t) := by
          field_simp [ht0.ne']
  have hunion : Ioi (1 : ℝ) = Ioc (1 : ℝ) 2 ∪ Ioi (2 : ℝ) :=
    (Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 2)).symm
  rw [hunion]
  exact h12.union h2inf

/-- **SHARP QUANTITATIVE MERTENS' FIRST THEOREM (0 ASSUMPTIONS!)**:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |∑_{p ≤ x} log p / p - (log x + mertensFirstConst)| ≤ C exp(-c √(log x))`. -/
theorem mertens_first_theorem_sharp :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) -
            (Real.log x + mertensFirstConst)| ≤
          C * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, C, hC, hth⟩ := Stage6EffectivePNT.effective_pnt_theta
  set c' : ℝ := c / 2 with hc'_def
  have hc'_pos : 0 < c' := by positivity
  have hint_tail : IntegrableOn (fun t : ℝ => Real.exp (-c' * (Real.log t) ^ (1 / 2 : ℝ)) / t)
      (Ioi (2 : ℝ)) :=
    integrableOn_exp_neg_rpow_log_div_id hc'_pos (by norm_num : (0 : ℝ) < 1 / 2)
  set I₀ : ℝ := ∫ t in Ioi (2 : ℝ), Real.exp (-c' * (Real.log t) ^ (1 / 2 : ℝ)) / t with hI₀_def
  have hI₀_nn : 0 ≤ I₀ :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      div_nonneg (Real.exp_pos _).le (by linarith [Set.mem_Ioi.mp ht])
  set C_fin : ℝ := C * (1 + I₀) with hC_fin_def
  have hC_fin_pos : 0 < C_fin := by positivity
  refine ⟨c', hc'_pos, C_fin, hC_fin_pos, fun x hx2 => ?_⟩
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hsplit : (∫ t in (1 : ℝ)..x, (Chebyshev.theta t - t) / t ^ 2) +
      (∫ t in Ioi x, (Chebyshev.theta t - t) / t ^ 2) =
      ∫ t in Ioi (1 : ℝ), (Chebyshev.theta t - t) / t ^ 2 := by
    rw [intervalIntegral.integral_of_le hx1]
    have hdisj : Disjoint (Ioc (1 : ℝ) x) (Ioi x) := Ioc_disjoint_Ioi_same
    have hunion : Ioc (1 : ℝ) x ∪ Ioi x = Ioi (1 : ℝ) := Ioc_union_Ioi_eq_Ioi hx1
    rw [← setIntegral_union hdisj measurableSet_Ioi
      (integrableOn_theta_sub_id_div_sq.mono_set Ioc_subset_Ioi_self)
      (integrableOn_theta_sub_id_div_sq.mono_set (Ioi_subset_Ioi hx1)), hunion]
  have hdiff_eq : mertensSum1 x - (Real.log x + mertensFirstConst) =
      (Chebyshev.theta x - x) / x - ∫ t in Ioi x, (Chebyshev.theta t - t) / t ^ 2 := by
    have h1 := mertensSum1_sub_log_eq hx1
    unfold mertensFirstConst
    linarith
  -- Bound the first term `|(θ(x) - x) / x| ≤ C * exp(-c' * √(log x))`
  have hterm1 : |(Chebyshev.theta x - x) / x| ≤ C * Real.exp (-c' * Real.sqrt (Real.log x)) := by
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    have hexp_le : Real.exp (-c * Real.sqrt (Real.log x)) ≤
        Real.exp (-c' * Real.sqrt (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      have := Real.sqrt_nonneg (Real.log x)
      nlinarith
    have h1 := hth x hx2
    nlinarith [mul_le_mul_of_nonneg_left hexp_le (show 0 ≤ C * x by positivity)]
  -- Bound the tail integral `|∫_{Ioi x} (θ(t) - t) / t²| ≤ C * I₀ * exp(-c' * √(log x))`
  have hterm2 : |∫ t in Ioi x, (Chebyshev.theta t - t) / t ^ 2| ≤
      C * I₀ * Real.exp (-c' * Real.sqrt (Real.log x)) := by
    have hmono1 : |∫ t in Ioi x, (Chebyshev.theta t - t) / t ^ 2| ≤
        ∫ t in Ioi x, |(Chebyshev.theta t - t) / t ^ 2| :=
      abs_integral_le_integral_abs
    have hint_x : IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2) (Ioi x) :=
      integrableOn_theta_sub_id_div_sq.mono_set (Ioi_subset_Ioi hx1)
    have hint_rhs : IntegrableOn
        (fun t : ℝ => (C * Real.exp (-c' * Real.sqrt (Real.log x))) *
          (Real.exp (-c' * (Real.log t) ^ (1 / 2 : ℝ)) / t)) (Ioi x) :=
      (hint_tail.mono_set (Ioi_subset_Ioi hx2)).const_mul _
    have hmono2 : ∫ t in Ioi x, |(Chebyshev.theta t - t) / t ^ 2| ≤
        ∫ t in Ioi x, (C * Real.exp (-c' * Real.sqrt (Real.log x))) *
          (Real.exp (-c' * (Real.log t) ^ (1 / 2 : ℝ)) / t) := by
      refine setIntegral_mono_on hint_x.abs hint_rhs measurableSet_Ioi fun t ht => ?_
      have hxt : x ≤ t := (Set.mem_Ioi.mp ht).le
      have ht2 : 2 ≤ t := hx2.trans hxt
      have ht0 : 0 < t := by linarith
      rw [abs_div, abs_of_nonneg (sq_nonneg t)]
      have hsqrt_le : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log t) :=
        Real.sqrt_le_sqrt (Real.log_le_log hx0 hxt)
      have hexp_split : Real.exp (-c * Real.sqrt (Real.log t)) ≤
          Real.exp (-c' * Real.sqrt (Real.log x)) *
            Real.exp (-c' * (Real.log t) ^ (1 / 2 : ℝ)) := by
        rw [← Real.exp_add, ← Real.sqrt_eq_rpow]
        apply Real.exp_le_exp.mpr
        dsimp only [c']
        nlinarith
      calc |Chebyshev.theta t - t| / t ^ 2
          ≤ (C * t * Real.exp (-c * Real.sqrt (Real.log t))) / t ^ 2 :=
            div_le_div_of_nonneg_right (hth t ht2) (sq_nonneg t)
        _ ≤ (C * t * (Real.exp (-c' * Real.sqrt (Real.log x)) *
              Real.exp (-c' * (Real.log t) ^ (1 / 2 : ℝ)))) / t ^ 2 := by
            gcongr
        _ = (C * Real.exp (-c' * Real.sqrt (Real.log x))) *
              (Real.exp (-c' * (Real.log t) ^ (1 / 2 : ℝ)) / t) := by
            field_simp [ht0.ne']
    rw [integral_const_mul] at hmono2
    have hsub_int : ∫ t in Ioi x, Real.exp (-c' * (Real.log t) ^ (1 / 2 : ℝ)) / t ≤ I₀ := by
      refine setIntegral_mono_set hint_tail ?_ (Eventually.of_forall (Ioi_subset_Ioi hx2))
      exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
        div_nonneg (Real.exp_pos _).le (by linarith [Set.mem_Ioi.mp ht])
    calc |∫ t in Ioi x, (Chebyshev.theta t - t) / t ^ 2|
        ≤ (C * Real.exp (-c' * Real.sqrt (Real.log x))) *
            ∫ t in Ioi x, Real.exp (-c' * (Real.log t) ^ (1 / 2 : ℝ)) / t := hmono1.trans hmono2
      _ ≤ (C * Real.exp (-c' * Real.sqrt (Real.log x))) * I₀ :=
          mul_le_mul_of_nonneg_left hsub_int (by positivity)
      _ = C * I₀ * Real.exp (-c' * Real.sqrt (Real.log x)) := by ring
  change |mertensSum1 x - (Real.log x + mertensFirstConst)| ≤ _
  rw [hdiff_eq]
  have htri := abs_sub ((Chebyshev.theta x - x) / x) (∫ t in Ioi x, (Chebyshev.theta t - t) / t ^ 2)
  dsimp only [C_fin]
  linarith

/-- **MERTENS' FIRST THEOREM (UNCONDITIONAL, 0 ASSUMPTIONS!)**:
`∃ C > 0, ∀ x ≥ 2, |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log p / p - Real.log x| ≤ C`. -/
theorem mertens_first_theorem :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) - Real.log x| ≤ C := by
  obtain ⟨c, hc, C, hC, hsharp⟩ := mertens_first_theorem_sharp
  refine ⟨C + |mertensFirstConst|, by positivity, fun x hx => ?_⟩
  have hexp_le1 : Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have := Real.sqrt_nonneg (Real.log x)
    nlinarith
  have h1 := (hsharp x hx).trans (by nlinarith : C * Real.exp (-c * Real.sqrt (Real.log x)) ≤ C)
  have htri : |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) - Real.log x| ≤
      |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) -
        (Real.log x + mertensFirstConst)| + |mertensFirstConst| := by
    have hrew : (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) - Real.log x) =
        (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) -
          (Real.log x + mertensFirstConst)) + mertensFirstConst := by ring
    rw [hrew]
    exact abs_add_le _ _
  linarith

/-- **Unconditional Improper Integral Evaluation `∫_1^∞ (ψ(t) - t) / t² dt = -(1 + γ)`**
(discharging the `ψ(t) - t = O(t^θ)` hypothesis of `Stage3RealAnalyticLandau.integral_psi_sub_id_div_sq_eq`
via `Stage6EffectivePNT.effective_pnt_psi` + DCT). -/
theorem integral_psi_sub_id_div_sq_eq_unconditional :
    ∫ t in Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2 = -(1 + Real.eulerMascheroniConstant) := by
  obtain ⟨c, hc, C, hC, hpsi⟩ := Stage6EffectivePNT.effective_pnt_psi
  -- Auxiliary entire function g(s) = (s - 1) ζ(s) with g(1) = 1, g'(1) = γ
  set g : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1
  have hg_ne : ∀ w : ℂ, w ≠ 1 → g w = (w - 1) * riemannZeta w := fun w hw => by simp [g, hw]
  have hg1 : g 1 = 1 := by simp [g]
  have hg_diff : Differentiable ℂ g := by
    rw [← differentiableOn_univ,
      ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
    refine ⟨fun z hz => ?_, by simpa only [g, continuousAt_update_same] using riemannZeta_residue_one⟩
    have hz1 : z ≠ 1 := by simpa using hz
    have hev : g =ᶠ[𝓝 z] fun s => (s - 1) * riemannZeta s := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz1] with w hw using hg_ne w hw
    exact ((DifferentiableAt.mul (by fun_prop) (differentiableAt_riemannZeta hz1)).congr_of_eventuallyEq
      hev).differentiableWithinAt
  have hderiv1 : deriv g 1 = (Real.eulerMascheroniConstant : ℂ) := by
    have hd := hasDerivAt_iff_tendsto_slope.mp (hg_diff 1).hasDerivAt
    refine tendsto_nhds_unique hd (tendsto_riemannZeta_sub_one_div.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    rw [slope_def_field, hg_ne s hs, hg1]; field_simp
  have hderiv_ne : ∀ s : ℂ, s ≠ 1 → deriv g s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
    intro s hs1
    have hev : g =ᶠ[𝓝 s] fun t => (t - 1) * riemannZeta t := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with w hw using hg_ne w hw
    have h3 : HasDerivAt (fun t : ℂ => (t - 1) * riemannZeta t)
        (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
      ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs1).hasDerivAt
    rw [hev.deriv_eq, h3.deriv]; ring
  have hLim1 : Tendsto (fun σ : ℝ =>
      -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) - 1 / ((σ : ℂ) - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
    have hcont_g' : ContinuousAt (deriv g) 1 := (hg_diff.analyticAt 1).deriv.continuousAt
    have hcont_div : ContinuousAt (fun z : ℂ => -(deriv g z / g z)) 1 :=
      (hcont_g'.div (hg_diff.continuous.continuousAt) (by rw [hg1]; exact one_ne_zero)).neg
    have h1 : Tendsto (fun σ : ℝ => -(deriv g (σ : ℂ) / g (σ : ℂ))) (𝓝[>] (1 : ℝ))
        (𝓝 (-(deriv g 1 / g 1))) :=
      (hcont_div.tendsto.comp Complex.continuous_ofReal.continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds
    rw [hderiv1, hg1, div_one] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    have hσ1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ.ne'
    have hσ1' : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hσ1
    have hz : riemannZeta (σ : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simpa using hσ.le)
    rw [hderiv_ne (σ : ℂ) hσ1, hg_ne (σ : ℂ) hσ1]
    field_simp; ring
  have hmeas_psi : Measurable RHDirect.chebyshevPsi := by
    have h : RHDirect.chebyshevPsi = (fun k : ℕ => ∑ n ∈ Finset.range (k + 1), Λ n) ∘ Nat.floor := rfl
    rw [h]; exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
  -- Dominating function on `(1, ∞)`: constant `Chebyshev.psi 2 + 2` on `(1, 2]`, `C * exp(-c √(log t)) / t` on `(2, ∞)`
  set B : ℝ → ℝ := fun t =>
    if t ≤ 2 then Chebyshev.psi 2 + 2 else C * (Real.exp (-c * (Real.log t) ^ (1 / 2 : ℝ)) / t)
  have hB_int : IntegrableOn B (Ioi (1 : ℝ)) := by
    have hunion : Ioi (1 : ℝ) = Ioc (1 : ℝ) 2 ∪ Ioi (2 : ℝ) :=
      (Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 2)).symm
    rw [hunion]
    refine IntegrableOn.union ?_ ?_
    · refine (integrableOn_const (C := Chebyshev.psi 2 + 2) (hs := measure_Ioc_lt_top.ne)).congr_fun
        (fun t ht => ?_) measurableSet_Ioc
      simp [B, ht.2]
    · have h2dom : IntegrableOn (fun t : ℝ => C * (Real.exp (-c * (Real.log t) ^ (1 / 2 : ℝ)) / t))
          (Ioi (2 : ℝ)) :=
        (integrableOn_exp_neg_rpow_log_div_id hc (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C
      refine h2dom.congr_fun (fun t ht => ?_) measurableSet_Ioi
      have hgt : ¬ t ≤ 2 := not_le.mpr (Set.mem_Ioi.mp ht)
      simp [B, hgt]
  have hDCT : Tendsto (fun σ : ℝ =>
      ∫ t in Ioi (1 : ℝ), ((RHDirect.chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))
      (𝓝[>] (1 : ℝ))
      (𝓝 (∫ t in Ioi (1 : ℝ), ((RHDirect.chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(2 : ℂ)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (bound := B) ?_ ?_ hB_int ?_
    · exact Eventually.of_forall fun σ =>
        ((Complex.measurable_ofReal.comp (hmeas_psi.sub measurable_id)).mul
          (Complex.measurable_ofReal.pow_const (-(σ : ℂ) - 1))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have hre : (-(σ : ℂ) - 1).re = -σ - 1 := by simp
      rw [hre, Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi]
      have hpow_le : t ^ (-σ - 1) ≤ t ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)
      have ht2_eq : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
      dsimp only [B]
      split_ifs with hle2
      · have htsq : 1 ≤ t ^ 2 := by nlinarith [(Set.mem_Ioi.mp ht).le]
        have hinv_le1 : t ^ (-2 : ℝ) ≤ 1 := by
          rw [ht2_eq]; exact inv_le_one_of_one_le₀ htsq
        have habs : |Chebyshev.psi t - t| ≤ Chebyshev.psi 2 + 2 := by
          have h0 := Chebyshev.psi_nonneg t
          have hm := Chebyshev.psi_mono hle2
          rcases abs_cases (Chebyshev.psi t - t) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
        calc |Chebyshev.psi t - t| * t ^ (-σ - 1)
            ≤ |Chebyshev.psi t - t| * 1 :=
              mul_le_mul_of_nonneg_left (hpow_le.trans hinv_le1) (abs_nonneg _)
          _ = |Chebyshev.psi t - t| := mul_one _
          _ ≤ Chebyshev.psi 2 + 2 := habs
      · have hgt2 : 2 ≤ t := (lt_of_not_ge hle2).le
        have hbd := hpsi t hgt2
        rw [Real.sqrt_eq_rpow] at hbd
        calc |Chebyshev.psi t - t| * t ^ (-σ - 1)
            ≤ (C * t * Real.exp (-c * (Real.log t) ^ (1 / 2 : ℝ))) * (t ^ 2)⁻¹ := by
              rw [← ht2_eq]
              exact mul_le_mul hbd hpow_le (Real.rpow_nonneg ht0.le _) (by positivity)
          _ = C * (Real.exp (-c * (Real.log t) ^ (1 / 2 : ℝ)) / t) := by
              field_simp [ht0.ne']
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      have hfun : (fun σ : ℝ => (t : ℂ) ^ (-(σ : ℂ) - 1)) =
          fun σ : ℝ => cexp ((Real.log t : ℂ) * (-(σ : ℂ) - 1)) := by
        funext σ
        rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht0.le]
      have hlim_pow : Tendsto (fun σ : ℝ => (t : ℂ) ^ (-(σ : ℂ) - 1)) (𝓝[>] (1 : ℝ))
          (𝓝 ((t : ℂ) ^ (-(2 : ℂ)))) := by
        rw [hfun]
        have hcont : Continuous (fun σ : ℝ => cexp ((Real.log t : ℂ) * (-(σ : ℂ) - 1))) := by
          fun_prop
        have h2 : Tendsto (fun σ : ℝ => cexp ((Real.log t : ℂ) * (-(σ : ℂ) - 1))) (𝓝[>] (1 : ℝ))
            (𝓝 (cexp ((Real.log t : ℂ) * (-((1 : ℝ) : ℂ) - 1)))) :=
          (hcont.continuousAt.tendsto (x := (1 : ℝ))).mono_left nhdsWithin_le_nhds
        have hval : cexp ((Real.log t : ℂ) * (-((1 : ℝ) : ℂ) - 1)) = (t : ℂ) ^ (-(2 : ℂ)) := by
          rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht0.le]
          congr 2; push_cast; ring
        rwa [hval] at h2
      exact hlim_pow.const_mul _
  have hLim2 : Tendsto (fun σ : ℝ =>
      1 + (σ : ℂ) * ∫ t in Ioi (1 : ℝ), ((RHDirect.chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))
      (𝓝[>] (1 : ℝ))
      (𝓝 (1 + (1 : ℂ) * ∫ t in Ioi (1 : ℝ), ((RHDirect.chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(2 : ℂ)))) :=
    (((Complex.continuous_ofReal.continuousAt.tendsto (x := (1 : ℝ))).mono_left
      nhdsWithin_le_nhds).mul hDCT).const_add 1
  have hEv : (fun σ : ℝ => -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) - 1 / ((σ : ℂ) - 1)) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun σ : ℝ => 1 + (σ : ℂ) * ∫ t in Ioi (1 : ℝ), ((RHDirect.chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    exact Stage3RealAnalyticLandau.neg_deriv_zeta_div_sub_pole_eq_mellin_psi (by simpa using hσ)
  have heqC := tendsto_nhds_unique (hLim1.congr' hEv) hLim2
  have hcast_int : ∫ t in Ioi (1 : ℝ), ((RHDirect.chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(2 : ℂ)) =
      ((∫ t in Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have hpow : (t : ℂ) ^ (-(2 : ℂ)) = (((t ^ 2)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      push_cast; rfl
    rw [hpow, Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi, ← Complex.ofReal_mul, div_eq_mul_inv]
  rw [one_mul, hcast_int] at heqC
  have hre := congrArg Complex.re heqC
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.add_re, Complex.one_re] at hre
  linarith

/-- **Exact Closed-Form Evaluation of Mertens' First Constant (`0` Assumptions!)**:
`mertensFirstConst = -Real.eulerMascheroniConstant - ∑' p : Nat.Primes, Real.log p / (p * (p - 1))`. -/
theorem mertensFirstConst_eq :
    mertensFirstConst =
      -Real.eulerMascheroniConstant -
        ∑' p : Nat.Primes, Real.log (p.1 : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 1)) := by
  -- 1. `∑_{1 ≤ n ≤ N} Λ(n)/n - log N → -γ` as `N → ∞`
  have hpsi_int_Ioi : IntegrableOn (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2) (Ioi (1 : ℝ)) := by
    obtain ⟨c, hc, C, hC, hpsi⟩ := Stage6EffectivePNT.effective_pnt_psi
    have hmeas_psi : Measurable Chebyshev.psi := by
      have h : Chebyshev.psi = (fun k : ℕ => ∑ n ∈ Finset.Ioc 0 k, Λ n) ∘ Nat.floor := rfl
      rw [h]; exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
    have hmeas : Measurable (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2) :=
      (hmeas_psi.sub measurable_id).div (continuous_pow 2).measurable
    have h12 : IntegrableOn (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2) (Ioc (1 : ℝ) 2) := by
      refine Integrable.mono'
        (integrableOn_const (C := Chebyshev.psi 2 + 2) (hs := measure_Ioc_lt_top.ne))
        hmeas.aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
      have htsq : 1 ≤ t ^ 2 := by nlinarith [ht.1]
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
      refine (div_le_self (abs_nonneg _) htsq).trans ?_
      have h0 := Chebyshev.psi_nonneg t
      have hm := Chebyshev.psi_mono ht.2
      rcases abs_cases (Chebyshev.psi t - t) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith [ht.1, ht.2]
    have h2inf : IntegrableOn (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2) (Ioi (2 : ℝ)) := by
      have hdom := (integrableOn_exp_neg_rpow_log_div_id hc (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C
      refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht2 : 2 ≤ t := (Set.mem_Ioi.mp ht).le
      have ht0 : 0 < t := by linarith
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
      have hbd := hpsi t ht2
      rw [Real.sqrt_eq_rpow] at hbd
      calc |Chebyshev.psi t - t| / t ^ 2
          ≤ (C * t * Real.exp (-c * (Real.log t) ^ (1 / 2 : ℝ))) / t ^ 2 :=
            div_le_div_of_nonneg_right hbd (sq_nonneg t)
        _ = C * (Real.exp (-c * (Real.log t) ^ (1 / 2 : ℝ)) / t) := by field_simp [ht0.ne']
    rw [(Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 2)).symm]
    exact h12.union h2inf
  have hLambda_abel : ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, Λ n / (n : ℝ)) - Real.log (N : ℝ) =
        (Chebyshev.psi (N : ℝ) - (N : ℝ)) / (N : ℝ) + 1 +
          ∫ t in (1 : ℝ)..(N : ℝ), (Chebyshev.psi t - t) / t ^ 2 := by
    intro N hN
    have hNR : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    have hN0 : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans_le hNR
    have hd : ∀ t ∈ Set.Icc (1 : ℝ) (N : ℝ), HasDerivAt (fun u : ℝ => u⁻¹) (-(t ^ 2)⁻¹) t :=
      fun t ht => hasDerivAt_inv (zero_lt_one.trans_le ht.1).ne'
    have hc : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc (1 : ℝ) (N : ℝ)) :=
      (ContinuousOn.inv₀ (continuousOn_pow 2) fun t ht =>
        pow_ne_zero 2 (zero_lt_one.trans_le ht.1).ne').neg
    have hab := abel_summation_real (fun n => Λ n) hNR hd hc
    rw [Nat.floor_natCast] at hab
    have hstep_psi : ∀ t : ℝ, realStepSum (fun n => Λ n) t = Chebyshev.psi t := fun t => by
      unfold realStepSum Chebyshev.psi; rfl
    have hLHS : ∑ n ∈ Finset.Icc 1 N, Λ n * (n : ℝ)⁻¹ = ∑ n ∈ Finset.Icc 1 N, Λ n / (n : ℝ) :=
      Finset.sum_congr rfl fun _ _ => (div_eq_mul_inv _ _).symm
    have hint_rew : ∫ t in (1 : ℝ)..(N : ℝ), realStepSum (fun n => Λ n) t * -(t ^ 2)⁻¹ =
        -(∫ t in (1 : ℝ)..(N : ℝ), Chebyshev.psi t / t ^ 2) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ => by rw [hstep_psi t]; ring
    rw [hLHS, hstep_psi (N : ℝ), hint_rew, sub_neg_eq_add] at hab
    have hint_log : ∫ t in (1 : ℝ)..(N : ℝ), (1 : ℝ) / t = Real.log (N : ℝ) := by
      simpa [one_div, Real.log_one] using integral_inv_of_pos zero_lt_one hN0
    have hpsi_int : IntervalIntegrable (fun t : ℝ => Chebyshev.psi t / t ^ 2) volume (1 : ℝ) (N : ℝ) := by
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hNR).mpr ?_
      refine Integrable.mono'
        (integrableOn_const (C := Chebyshev.psi (N : ℝ)) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
      · have hm : Measurable Chebyshev.psi := by
          have h : Chebyshev.psi = (fun k : ℕ => ∑ n ∈ Finset.Ioc 0 k, Λ n) ∘ Nat.floor := rfl
          rw [h]; exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
        exact (hm.div (continuous_pow 2).measurable).aestronglyMeasurable
      · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
        have htsq : 1 ≤ t ^ 2 := by nlinarith [ht.1]
        rw [Real.norm_of_nonneg (div_nonneg (Chebyshev.psi_nonneg t) (sq_nonneg t))]
        exact (div_le_self (Chebyshev.psi_nonneg t) htsq).trans (Chebyshev.psi_mono ht.2)
    have hinv_int : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / t) volume (1 : ℝ) (N : ℝ) := by
      have hc1 : ContinuousOn (fun t : ℝ => (1 : ℝ) / t) (Set.uIcc 1 (N : ℝ)) := by
        rw [Set.uIcc_of_le hNR]
        exact continuousOn_const.div continuousOn_id fun t ht => (zero_lt_one.trans_le ht.1).ne'
      exact hc1.intervalIntegrable
    have hpt : Set.EqOn (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2)
        (fun t : ℝ => Chebyshev.psi t / t ^ 2 - 1 / t) (Set.uIcc 1 (N : ℝ)) := by
      rw [Set.uIcc_of_le hNR]
      intro t ht
      have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht.1).ne'
      dsimp only; field_simp
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub hpsi_int hinv_int,
      hint_log, hab]
    field_simp [hN0.ne']
    ring
  have hLambda_lim : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, Λ n / (n : ℝ)) - Real.log (N : ℝ))
      atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
    have h1 : Tendsto (fun N : ℕ => (Chebyshev.psi (N : ℝ) - (N : ℝ)) / (N : ℝ)) atTop (𝓝 0) := by
      have h := (Stage6EffectivePNT.pnt_psi_asymp.comp tendsto_natCast_atTop_atTop).sub_const 1
      rw [sub_self] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      dsimp only [Function.comp_apply]
      field_simp [hN0]
    have h2 : Tendsto (fun N : ℕ => ∫ t in (1 : ℝ)..(N : ℝ), (Chebyshev.psi t - t) / t ^ 2)
        atTop (𝓝 (-(1 + Real.eulerMascheroniConstant))) := by
      rw [← integral_psi_sub_id_div_sq_eq_unconditional]
      exact intervalIntegral_tendsto_integral_Ioi (1 : ℝ) hpsi_int_Ioi tendsto_natCast_atTop_atTop
    have hsum := (h1.add_const 1).add h2
    have hval : 0 + 1 + -(1 + Real.eulerMascheroniConstant) = -Real.eulerMascheroniConstant := by ring
    rw [hval] at hsum
    exact hsum.congr' (by filter_upwards [eventually_ge_atTop 1] with N hN using (hLambda_abel N hN).symm)
  -- 2. `mertensSum1 N - log N → mertensFirstConst` as `N → ∞`
  have hM1_lim : Tendsto (fun N : ℕ => mertensSum1 (N : ℝ) - Real.log (N : ℝ))
      atTop (𝓝 mertensFirstConst) := by
    obtain ⟨c, hc, C, hC, hsharp⟩ := mertens_first_theorem_sharp
    rw [← tendsto_sub_nhds_zero_iff]
    have hdec : Tendsto (fun N : ℕ => C * Real.exp (-c * Real.sqrt (Real.log (N : ℝ)))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => c * Real.sqrt (Real.log x)) atTop atTop :=
        Tendsto.const_mul_atTop hc ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
          Real.tendsto_log_atTop |>.congr fun x => (Real.sqrt_eq_rpow (Real.log x)).symm)
      have h2 : Tendsto (fun x : ℝ => Real.exp (-c * Real.sqrt (Real.log x))) atTop (𝓝 0) :=
        (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)).congr fun x => by
          dsimp only [Function.comp_apply]; congr 1; ring
      simpa using (h2.comp tendsto_natCast_atTop_atTop).const_mul C
    refine squeeze_zero_norm' (a := fun N : ℕ => C * Real.exp (-c * Real.sqrt (Real.log (N : ℝ)))) ?_ hdec
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [Real.norm_eq_abs, show mertensSum1 (N : ℝ) - Real.log (N : ℝ) - mertensFirstConst =
      mertensSum1 (N : ℝ) - (Real.log (N : ℝ) + mertensFirstConst) by ring]
    exact hsharp (N : ℝ) (by exact_mod_cast hN)
  -- 3. Difference `(∑_{n ≤ N} Λ(n)/n) - mertensSum1 N = ∑_{n ≤ N, IsPrimePow n ∧ ¬ n.Prime} Λ(n)/n`
  set ppTerm : ℕ → ℝ := fun n => if IsPrimePow n ∧ ¬ n.Prime then Λ n / (n : ℝ) else 0
  have hdiff_lim1 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), ppTerm n)
      atTop (𝓝 (-Real.eulerMascheroniConstant - mertensFirstConst)) := by
    refine (hLambda_lim.sub hM1_lim).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N _
    have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 N)]
    have hpp0 : ppTerm 0 = 0 := by simp [ppTerm]
    rw [hpp0, zero_add]
    unfold mertensSum1
    rw [Nat.floor_natCast, Finset.sum_filter,
      show ((∑ n ∈ Finset.Icc 1 N, Λ n / (n : ℝ)) - Real.log (N : ℝ)) -
        ((∑ n ∈ Finset.Icc 1 N, if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0) - Real.log (N : ℝ)) =
      ∑ n ∈ Finset.Icc 1 N, (Λ n / (n : ℝ) - if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0) by
        rw [Finset.sum_sub_distrib]; ring]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only [ppTerm]
    by_cases hp : n.Prime
    · rw [if_pos hp, if_neg (fun h => h.2 hp), ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self]
    · rw [if_neg hp, sub_zero]
      by_cases hpp : IsPrimePow n
      · rw [if_pos ⟨hpp, hp⟩]
      · rw [if_neg (fun h => hpp h.1), ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, zero_div]
  -- 4. Compute `∑' n, ppTerm n = ∑'_p log p / (p * (p - 1))` via prime-power bijection!
  have hbij : ∃ e : (Nat.Primes × ℕ) ≃ {n : ℕ // IsPrimePow n ∧ ¬ n.Prime},
      ∀ pk : Nat.Primes × ℕ, (e pk).1 = pk.1.1 ^ (pk.2 + 2) := by
    let toFun : Nat.Primes × ℕ → {n : ℕ // IsPrimePow n ∧ ¬ n.Prime} := fun pk =>
      ⟨pk.1.1 ^ (pk.2 + 2),
        pk.1.2.isPrimePow.pow (by omega),
        by
          rw [pow_succ']
          exact Nat.not_prime_mul pk.1.2.ne_one
            (ne_of_gt (Nat.one_lt_pow (by omega : pk.2 + 1 ≠ 0) pk.1.2.one_lt))⟩
    have hinj : Function.Injective toFun := by
      rintro ⟨p₁, k₁⟩ ⟨p₂, k₂⟩ heq
      have hval : p₁.1 ^ (k₁ + 2) = p₂.1 ^ (k₂ + 2) := congrArg Subtype.val heq
      have hdvd : p₁.1 ∣ p₂.1 :=
        p₁.2.dvd_of_dvd_pow (hval ▸ dvd_pow_self p₁.1 (by omega : k₁ + 2 ≠ 0))
      have hp_eq : p₁.1 = p₂.1 := (Nat.prime_dvd_prime_iff_eq p₁.2 p₂.2).mp hdvd
      have hp_sub : p₁ = p₂ := Subtype.ext hp_eq
      subst hp_sub
      have hk_eq : k₁ + 2 = k₂ + 2 := Nat.pow_right_injective p₁.2.two_le hval
      exact Prod.ext rfl (by omega)
    have hsurj : Function.Surjective toFun := by
      rintro ⟨n, hpp, hnp⟩
      obtain ⟨p, k, hp, hkpos, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
      have hk2 : 2 ≤ k := by
        by_contra hlt
        have hk1 : k = 1 := by omega
        subst hk1; rw [pow_one] at hnp; exact hnp hp
      refine ⟨(⟨p, hp⟩, k - 2), Subtype.ext ?_⟩
      change p ^ (k - 2 + 2) = p ^ k
      rw [Nat.sub_add_cancel hk2]
    exact ⟨Equiv.ofBijective toFun ⟨hinj, hsurj⟩, fun _ => rfl⟩
  obtain ⟨e, he⟩ := hbij
  have hgeom : ∀ p : Nat.Primes,
      HasSum (fun k : ℕ => Real.log (p.1 : ℝ) / ((p.1 : ℝ) ^ (k + 2)))
        (Real.log (p.1 : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 1))) := by
    intro p
    have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
    have hp0 : (0 : ℝ) < (p.1 : ℝ) := by linarith
    have hp1 : (0 : ℝ) < (p.1 : ℝ) - 1 := by linarith
    have hinv_lt1 : (p.1 : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    have hg := (hasSum_geometric_of_lt_one (by positivity) hinv_lt1).mul_left
      (Real.log (p.1 : ℝ) / (p.1 : ℝ) ^ 2)
    have hval : (Real.log (p.1 : ℝ) / (p.1 : ℝ) ^ 2) * (1 - (p.1 : ℝ)⁻¹)⁻¹ =
        Real.log (p.1 : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 1)) := by
      field_simp [hp0.ne', hp1.ne']
    rw [hval] at hg
    refine hg.congr_fun fun k => ?_
    rw [pow_add, inv_pow]
    field_simp [hp0.ne']
  have hsumm_p : Summable (fun p : Nat.Primes => Real.log (p.1 : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 1))) := by
    have hdom : Summable (fun p : Nat.Primes => 4 * ((p.1 : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
      have hnat : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
        (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 4
      exact hnat.subtype ({p : ℕ | p.Prime})
    refine Summable.of_nonneg_of_le (fun p => by
      have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
      exact div_nonneg (Real.log_nonneg (by linarith)) (by nlinarith)) (fun p => ?_) hdom
    have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
    have hp0 : (0 : ℝ) < (p.1 : ℝ) := by linarith
    have hlog : Real.log (p.1 : ℝ) ≤ 2 * (p.1 : ℝ) ^ (1 / 2 : ℝ) := by
      have h := Real.log_le_rpow_div hp0.le (by norm_num : (0 : ℝ) < 1 / 2)
      linarith [show (p.1 : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) = 2 * (p.1 : ℝ) ^ (1 / 2 : ℝ) by ring]
    have hden : (p.1 : ℝ) ^ 2 / 2 ≤ (p.1 : ℝ) * ((p.1 : ℝ) - 1) := by nlinarith
    have hpow : (p.1 : ℝ) ^ (1 / 2 : ℝ) * (p.1 : ℝ) ^ (3 / 2 : ℝ) = (p.1 : ℝ) ^ 2 := by
      rw [← Real.rpow_add hp0]; norm_num
    calc Real.log (p.1 : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 1))
        ≤ (2 * (p.1 : ℝ) ^ (1 / 2 : ℝ)) / ((p.1 : ℝ) ^ 2 / 2) :=
          div_le_div₀ (by positivity) hlog (by positivity) hden
      _ = 4 * ((p.1 : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
          have h1 : (p.1 : ℝ) ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hp0 _).ne'
          field_simp [hp0.ne', h1]
          linarith [hpow]
  have hsumm_prod : Summable (fun pk : Nat.Primes × ℕ => Real.log (pk.1.1 : ℝ) / ((pk.1.1 : ℝ) ^ (pk.2 + 2))) := by
    rw [summable_prod_of_nonneg fun pk => by
      have hp2 : (2 : ℝ) ≤ (pk.1.1 : ℝ) := by exact_mod_cast pk.1.2.two_le
      exact div_nonneg (Real.log_nonneg (by linarith)) (by positivity)]
    refine ⟨fun p => (hgeom p).summable, ?_⟩
    exact hsumm_p.congr fun p => (hgeom p).tsum_eq.symm
  have htsum_prod : ∑' pk : Nat.Primes × ℕ, Real.log (pk.1.1 : ℝ) / ((pk.1.1 : ℝ) ^ (pk.2 + 2)) =
      ∑' p : Nat.Primes, Real.log (p.1 : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 1)) := by
    rw [hsumm_prod.tsum_prod]
    exact tsum_congr fun p => (hgeom p).tsum_eq
  have hsumm_sub : Summable (fun n : {n : ℕ // IsPrimePow n ∧ ¬ n.Prime} => Λ n.1 / (n.1 : ℝ)) := by
    rw [← e.summable_iff]
    refine hsumm_prod.congr fun pk => ?_
    dsimp only [Function.comp_apply]
    rw [he pk, ArithmeticFunction.vonMangoldt_apply_pow (by omega : pk.2 + 2 ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime pk.1.2, Nat.cast_pow]
  have htsum_sub : ∑' n : {n : ℕ // IsPrimePow n ∧ ¬ n.Prime}, Λ n.1 / (n.1 : ℝ) =
      ∑' p : Nat.Primes, Real.log (p.1 : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 1)) := by
    rw [← htsum_prod, ← e.tsum_eq]
    refine tsum_congr fun pk => ?_
    rw [he pk, ArithmeticFunction.vonMangoldt_apply_pow (by omega : pk.2 + 2 ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime pk.1.2, Nat.cast_pow]
  have hsumm_pp : Summable ppTerm := by
    have h := (summable_subtype_iff_indicator (s := {n : ℕ | IsPrimePow n ∧ ¬ n.Prime})
      (f := fun n : ℕ => Λ n / (n : ℝ))).mp hsumm_sub
    refine h.congr fun n => ?_
    by_cases hn : IsPrimePow n ∧ ¬ n.Prime <;> simp [ppTerm, hn, Set.indicator]
  have htsum_pp : ∑' n : ℕ, ppTerm n =
      ∑' p : Nat.Primes, Real.log (p.1 : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 1)) := by
    rw [← htsum_sub]
    have hsub : (∑' n : {n : ℕ // IsPrimePow n ∧ ¬ n.Prime}, Λ n.1 / (n.1 : ℝ)) =
        ∑' n : ↥{n : ℕ | IsPrimePow n ∧ ¬ n.Prime}, Λ n.1 / (n.1 : ℝ) := rfl
    rw [hsub, tsum_subtype ({n : ℕ | IsPrimePow n ∧ ¬ n.Prime}) (fun n : ℕ => Λ n / (n : ℝ))]
    refine tsum_congr fun n => ?_
    by_cases hn : IsPrimePow n ∧ ¬ n.Prime <;> simp [ppTerm, hn, Set.indicator]
  have hdiff_lim2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), ppTerm n)
      atTop (𝓝 (∑' p : Nat.Primes, Real.log (p.1 : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 1)))) := by
    rw [← htsum_pp]
    exact hsumm_pp.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have heq := tendsto_nhds_unique hdiff_lim1 hdiff_lim2
  linarith

/-! ## Section 3: Abstract Partial Summation & Mertens' Second Theorem -/

/-- **Reusable Partial-Summation Engine for Reciprocal Prime Sums**:
if `a : ℕ → ℝ` satisfies `a 0 = 0`, `a 1 = 0`, and `|A(t) - δ * log t| ≤ C₀` for all `t ≥ 2`
(where `A(t) = ∑_{1 ≤ n ≤ t} a_n`), then for
`M := δ * (1 - log (log 2)) + ∫_2^∞ (A(t) - δ * log t) / (t * (log t)^2) dt`
and EVERY `x ≥ 2`:
`|∑_{2 ≤ n ≤ ⌊x⌋₊} a_n / log n - (δ * log (log x) + M)| ≤ 2 * C₀ / log x`! -/
theorem reciprocal_sum_asymp_of_log_weighted_bound (a : ℕ → ℝ) (ha1 : a 1 = 0)
    {δ C₀ : ℝ} (_hC₀ : 0 < C₀)
    (hbd : ∀ t : ℝ, 2 ≤ t → |realStepSum a t - δ * Real.log t| ≤ C₀) :
    let M : ℝ := δ * (1 - Real.log (Real.log 2)) +
      ∫ t in Ioi (2 : ℝ), (realStepSum a t - δ * Real.log t) / (t * (Real.log t) ^ 2)
    IntegrableOn (fun t : ℝ => (realStepSum a t - δ * Real.log t) / (t * (Real.log t) ^ 2)) (Ioi (2 : ℝ)) ∧
    ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ Finset.Icc 2 ⌊x⌋₊, a n / Real.log (n : ℝ) - (δ * Real.log (Real.log x) + M)| ≤
        2 * C₀ / Real.log x := by
  intro M
  set R : ℝ → ℝ := fun t => realStepSum a t - δ * Real.log t with hR_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hint_inv2 := (integrableOn_and_integral_Ioi_inv_mul_log_sq (by norm_num : (1 : ℝ) < 2)).1
  have hint_R : IntegrableOn (fun t : ℝ => R t / (t * (Real.log t) ^ 2)) (Ioi (2 : ℝ)) := by
    refine Integrable.mono' (hint_inv2.const_mul C₀) ?_ ?_
    · have hm : Measurable (fun t : ℝ => R t / (t * (Real.log t) ^ 2)) :=
        ((measurable_realStepSum a).sub (measurable_const.mul Real.measurable_log)).div
          (measurable_id.mul (Real.measurable_log.pow_const 2))
      exact hm.aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht2 : 2 ≤ t := (Set.mem_Ioi.mp ht).le
      have ht0 : 0 < t := by linarith
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (mul_nonneg ht0.le (sq_nonneg _)), div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hbd t ht2) (inv_nonneg.mpr (mul_nonneg ht0.le (sq_nonneg _)))
  refine ⟨hint_R, fun x hx2 => ?_⟩
  have hx0 : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  -- Apply `abel_summation_from_two` with `φ(t) = (log t)⁻¹`, `φ'(t) = -(t * (log t)^2)⁻¹`
  have hd : ∀ t ∈ Set.Icc (2 : ℝ) x,
      HasDerivAt (fun u : ℝ => (Real.log u)⁻¹) (-(t * (Real.log t) ^ 2)⁻¹) t := by
    intro t ht
    have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
    have hlt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    refine ((Real.hasDerivAt_log ht0).inv hlt0).congr_deriv ?_
    field_simp [ht0, hlt0]
  have hc : ContinuousOn (fun t : ℝ => -(t * (Real.log t) ^ 2)⁻¹) (Set.Icc (2 : ℝ) x) := by
    refine (ContinuousOn.inv₀ (continuousOn_id.mul
      ((Real.continuousOn_log.mono fun t ht => (by linarith [ht.1] : (0 : ℝ) < t).ne').pow 2))
      fun t ht => ?_).neg
    exact mul_ne_zero (by linarith [ht.1] : (0 : ℝ) < t).ne'
      (pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne')
  have hab := abel_summation_from_two a ha1 hx2 hd hc
  have hLHS : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, a n * (Real.log (n : ℝ))⁻¹ =
      ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, a n / Real.log (n : ℝ) :=
    Finset.sum_congr rfl fun _ _ => (div_eq_mul_inv _ _).symm
  rw [hLHS] at hab
  -- Compute `∫_2^x (δ * log t) / (t * (log t)^2) dt = δ * (log (log x) - log (log 2))`
  have hint_loglog : ∫ t in (2 : ℝ)..x, δ / (t * Real.log t) =
      δ * (Real.log (Real.log x) - Real.log (Real.log 2)) := by
    have hd_ll : ∀ t ∈ Set.uIcc (2 : ℝ) x,
        HasDerivAt (fun u : ℝ => δ * Real.log (Real.log u)) (δ / (t * Real.log t)) t := by
      intro t ht
      rw [Set.uIcc_of_le hx2] at ht
      have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
      have hlt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      have h1 : HasDerivAt (fun u : ℝ => Real.log (Real.log u)) (t⁻¹ / Real.log t) t :=
        (Real.hasDerivAt_log ht0).log hlt0
      refine (h1.const_mul δ).congr_deriv ?_
      field_simp [ht0, hlt0]
    have hc_ll : ContinuousOn (fun t : ℝ => δ / (t * Real.log t)) (Set.uIcc (2 : ℝ) x) := by
      rw [Set.uIcc_of_le hx2]
      exact continuousOn_const.div
        (continuousOn_id.mul (Real.continuousOn_log.mono fun t ht => (by linarith [ht.1] : (0 : ℝ) < t).ne'))
        fun t ht => mul_ne_zero (by linarith [ht.1] : (0 : ℝ) < t).ne'
          (Real.log_pos (by linarith [ht.1])).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd_ll hc_ll.intervalIntegrable]
    ring
  have hint_ll_int : IntervalIntegrable (fun t : ℝ => δ / (t * Real.log t)) volume (2 : ℝ) x := by
    have hc_ll : ContinuousOn (fun t : ℝ => δ / (t * Real.log t)) (Set.uIcc (2 : ℝ) x) := by
      rw [Set.uIcc_of_le hx2]
      exact continuousOn_const.div
        (continuousOn_id.mul (Real.continuousOn_log.mono fun t ht => (by linarith [ht.1] : (0 : ℝ) < t).ne'))
        fun t ht => mul_ne_zero (by linarith [ht.1] : (0 : ℝ) < t).ne'
          (Real.log_pos (by linarith [ht.1])).ne'
    exact hc_ll.intervalIntegrable
  have hint_R_2x : IntervalIntegrable (fun t : ℝ => R t / (t * (Real.log t) ^ 2)) volume (2 : ℝ) x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx2).mpr
      (hint_R.mono_set Ioc_subset_Ioi_self)
  have hint_step_rew : -(∫ t in (2 : ℝ)..x, realStepSum a t * -(t * (Real.log t) ^ 2)⁻¹) =
      δ * (Real.log (Real.log x) - Real.log (Real.log 2)) +
      ∫ t in (2 : ℝ)..x, R t / (t * (Real.log t) ^ 2) := by
    rw [← intervalIntegral.integral_neg, ← hint_loglog, ← intervalIntegral.integral_add hint_ll_int hint_R_2x]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx2] at ht
    have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
    have hlt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    dsimp only [R]
    field_simp [ht0, hlt0]
    ring
  have hsplit : (∫ t in (2 : ℝ)..x, R t / (t * (Real.log t) ^ 2)) +
      (∫ t in Ioi x, R t / (t * (Real.log t) ^ 2)) =
      ∫ t in Ioi (2 : ℝ), R t / (t * (Real.log t) ^ 2) := by
    rw [intervalIntegral.integral_of_le hx2]
    have hdisj : Disjoint (Ioc (2 : ℝ) x) (Ioi x) := Ioc_disjoint_Ioi_same
    have hunion : Ioc (2 : ℝ) x ∪ Ioi x = Ioi (2 : ℝ) := Ioc_union_Ioi_eq_Ioi hx2
    rw [← setIntegral_union hdisj measurableSet_Ioi
      (hint_R.mono_set Ioc_subset_Ioi_self)
      (hint_R.mono_set (Ioi_subset_Ioi hx2)), hunion]
  have hstep_x_rew : realStepSum a x * (Real.log x)⁻¹ = δ + R x / Real.log x := by
    dsimp only [R]
    field_simp [hLx_pos.ne']
    ring
  have hdiff : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, a n / Real.log (n : ℝ) - (δ * Real.log (Real.log x) + M) =
      R x / Real.log x - ∫ t in Ioi x, R t / (t * (Real.log t) ^ 2) := by
    rw [hab, show realStepSum a x * (Real.log x)⁻¹ -
        ∫ t in (2 : ℝ)..x, realStepSum a t * -(t * (Real.log t) ^ 2)⁻¹ =
      realStepSum a x * (Real.log x)⁻¹ +
        -(∫ t in (2 : ℝ)..x, realStepSum a t * -(t * (Real.log t) ^ 2)⁻¹) by ring,
      hstep_x_rew, hint_step_rew]
    dsimp only [M]
    linarith
  have hterm1 : |R x / Real.log x| ≤ C₀ / Real.log x := by
    rw [abs_div, abs_of_pos hLx_pos]
    exact div_le_div_of_nonneg_right (hbd x hx2) hLx_pos.le
  have hterm2 : |∫ t in Ioi x, R t / (t * (Real.log t) ^ 2)| ≤ C₀ / Real.log x := by
    have hint_invx := integrableOn_and_integral_Ioi_inv_mul_log_sq (by linarith : (1 : ℝ) < x)
    calc |∫ t in Ioi x, R t / (t * (Real.log t) ^ 2)|
        ≤ ∫ t in Ioi x, |R t / (t * (Real.log t) ^ 2)| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioi x, C₀ * (t * (Real.log t) ^ 2)⁻¹ := by
          refine setIntegral_mono_on (hint_R.mono_set (Ioi_subset_Ioi hx2)).abs
            (hint_invx.1.const_mul C₀) measurableSet_Ioi fun t ht => ?_
          have ht2 : 2 ≤ t := hx2.trans (Set.mem_Ioi.mp ht).le
          have ht0 : 0 < t := by linarith
          rw [abs_div, abs_of_nonneg (mul_nonneg ht0.le (sq_nonneg _)), div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (hbd t ht2)
            (inv_nonneg.mpr (mul_nonneg ht0.le (sq_nonneg _)))
      _ = C₀ * (Real.log x)⁻¹ := by rw [integral_const_mul, hint_invx.2]
      _ = C₀ / Real.log x := (div_eq_mul_inv _ _).symm
  rw [hdiff]
  have htri := abs_sub (R x / Real.log x) (∫ t in Ioi x, R t / (t * (Real.log t) ^ 2))
  linarith [show 2 * C₀ / Real.log x = C₀ / Real.log x + C₀ / Real.log x by ring]

/-- Mertens' second prime sum `∑_{p ≤ x} 1 / p`. -/
def mertensSum2 (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (p : ℝ)⁻¹

/-- The exact **Meissel–Mertens constant `M`**:
`M = (1 - log (log 2)) + ∫_2^∞ (mertensSum1 t - log t) / (t * (log t)^2) dt`. -/
def meisselMertensConst : ℝ :=
  (1 - Real.log (Real.log 2)) +
    ∫ t in Ioi (2 : ℝ), (mertensSum1 t - Real.log t) / (t * (Real.log t) ^ 2)

private lemma realStepSum_primeLogDiv_eq_mertensSum1 (t : ℝ) :
    realStepSum (fun n : ℕ => if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0) t =
      mertensSum1 t := by
  unfold realStepSum mertensSum1
  rw [← Finset.sum_filter]

/-- **MERTENS' SECOND THEOREM FOR ALL `x ≥ 2` (UNCONDITIONAL, 0 ASSUMPTIONS!)**:
`∃ C > 0, ∀ x ≥ 2, |mertensSum2 x - (Real.log (Real.log x) + meisselMertensConst)| ≤ C / Real.log x`. -/
theorem mertens_second_theorem_ge_two :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |mertensSum2 x - (Real.log (Real.log x) + meisselMertensConst)| ≤ C / Real.log x := by
  obtain ⟨C₀, hC₀, hM1⟩ := mertens_first_theorem
  set a : ℕ → ℝ := fun n => if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0
  have ha1 : a 1 = 0 := by simp [a]
  have hbd : ∀ t : ℝ, 2 ≤ t → |realStepSum a t - 1 * Real.log t| ≤ C₀ := by
    intro t ht
    rw [one_mul, realStepSum_primeLogDiv_eq_mertensSum1 t]
    exact hM1 t ht
  have hab := (reciprocal_sum_asymp_of_log_weighted_bound a ha1 hC₀ hbd).2
  refine ⟨2 * C₀, by positivity, fun x hx => ?_⟩
  have hsum_eq : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, a n / Real.log (n : ℝ) = mertensSum2 x := by
    unfold mertensSum2
    rw [Finset.sum_filter]
    have hIcc : Finset.Icc 1 ⌊x⌋₊ = insert 1 (Finset.Icc 2 ⌊x⌋₊) := by
      have hfl2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp : (1 : ℕ) ∉ Finset.Icc 2 ⌊x⌋₊),
      if_neg Nat.not_prime_one, zero_add]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only [a]
    split_ifs with hp
    · have hlog_ne : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      field_simp [hlog_ne]
    · simp
  have hM_eq : 1 * (1 - Real.log (Real.log 2)) +
      ∫ t in Ioi (2 : ℝ), (realStepSum a t - 1 * Real.log t) / (t * (Real.log t) ^ 2) =
      meisselMertensConst := by
    unfold meisselMertensConst
    simp only [one_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [realStepSum_primeLogDiv_eq_mertensSum1 t]
  have hres := hab x hx
  rw [hsum_eq, one_mul, hM_eq] at hres
  exact hres

/-- **MERTENS' SECOND THEOREM (UNCONDITIONAL, 0 ASSUMPTIONS!)**:
`∃ C > 0, ∀ x ≥ 3, |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ - (Real.log (Real.log x) + meisselMertensConst)| ≤ C / Real.log x`. -/
theorem mertens_second_theorem :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ -
          (Real.log (Real.log x) + meisselMertensConst)| ≤ C / Real.log x := by
  obtain ⟨C, hC, h2⟩ := mertens_second_theorem_ge_two
  exact ⟨C, hC, fun x hx => h2 x (by linarith)⟩

/-! ## Section 4: Exact Euler–Mascheroni Relation `meisselMertensConst = γ + ∑_p (log(1 - 1/p) + 1/p)` -/

/-- Exact Gamma-derivative integral identity:
`∫_0^∞ (log u) * exp(-u) du = -Real.eulerMascheroniConstant`. -/
theorem integral_log_mul_exp_neg_eq_neg_eulerMascheroni :
    ∫ u in Ioi (0 : ℝ), Real.log u * Real.exp (-u) = -Real.eulerMascheroniConstant := by
  have hd1 : HasDerivAt Complex.Gamma (-(Real.eulerMascheroniConstant : ℂ)) 1 :=
    Complex.hasDerivAt_Gamma_one
  have hd2 : HasDerivAt Complex.Gamma
      (∫ t : ℝ in Ioi (0 : ℝ), (t : ℂ) ^ ((1 : ℂ) - 1) * (Real.log t * Real.exp (-t))) 1 := by
    have hev : Complex.Gamma =ᶠ[𝓝 (1 : ℂ)] Complex.GammaIntegral := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by norm_num : (0 : ℝ) < (1 : ℂ).re)] with s hs
      exact Complex.Gamma_eq_integral hs
    exact (Complex.hasDerivAt_GammaIntegral (by norm_num : (0 : ℝ) < (1 : ℂ).re)).congr_of_eventuallyEq hev
  have heqC : ∫ t : ℝ in Ioi (0 : ℝ), (t : ℂ) ^ ((1 : ℂ) - 1) * (Real.log t * Real.exp (-t)) =
      -(Real.eulerMascheroniConstant : ℂ) := hd2.unique hd1
  have hcast : ∫ t : ℝ in Ioi (0 : ℝ), (t : ℂ) ^ ((1 : ℂ) - 1) * (Real.log t * Real.exp (-t)) =
      ((∫ t : ℝ in Ioi (0 : ℝ), Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp [Complex.cpow_zero]
  rw [hcast] at heqC
  have hre := congrArg Complex.re heqC
  simpa using hre

/-- Integrability of `u ↦ Real.log u * Real.exp (-u)` on `Ioi 0`. -/
lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Ioi (0 : ℝ)) := by
  have hdom1 : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ ((1 / 2 : ℝ) - 1)) (Ioi (0 : ℝ)) :=
    Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)
  have hdom2 : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ ((2 : ℝ) - 1)) (Ioi (0 : ℝ)) :=
    Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 2)
  have hdom : IntegrableOn (fun u : ℝ =>
      2 * (Real.exp (-u) * u ^ ((1 / 2 : ℝ) - 1)) + (Real.exp (-u) * u ^ ((2 : ℝ) - 1))) (Ioi (0 : ℝ)) :=
    (hdom1.const_mul 2).add hdom2
  refine Integrable.mono' hdom
    (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg)).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
  have hu0 : 0 < u := Set.mem_Ioi.mp hu
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (-u))]
  by_cases hu1 : 1 ≤ u
  · have hlog_le : |Real.log u| ≤ u := by
      rw [abs_of_nonneg (Real.log_nonneg hu1)]
      exact (Real.log_le_sub_one_of_pos hu0).trans (by linarith)
    have hnn : 0 ≤ 2 * (Real.exp (-u) * u ^ ((1 / 2 : ℝ) - 1)) := by positivity
    have hpow : u ^ ((2 : ℝ) - 1) = u := by norm_num
    rw [hpow]
    nlinarith [Real.exp_pos (-u)]
  · push Not at hu1
    have hinv_gt1 : 1 < u⁻¹ := one_lt_inv₀ hu0 |>.mpr hu1
    have hlog_neg : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1.le
    have habs : |Real.log u| = Real.log (u⁻¹) := by
      rw [abs_of_nonpos hlog_neg, Real.log_inv]
    have hbound : Real.log (u⁻¹) ≤ 2 * (u⁻¹) ^ (1 / 2 : ℝ) := by
      have h := Real.log_le_rpow_div (inv_nonneg.mpr hu0.le) (by norm_num : (0 : ℝ) < 1 / 2)
      linarith [show (u⁻¹) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) = 2 * (u⁻¹) ^ (1 / 2 : ℝ) by ring]
    have hpow_eq : (u⁻¹) ^ (1 / 2 : ℝ) = u ^ ((1 / 2 : ℝ) - 1) := by
      rw [Real.inv_rpow hu0.le, ← Real.rpow_neg hu0.le]
      congr 1; norm_num
    have hnn : 0 ≤ Real.exp (-u) * u ^ ((2 : ℝ) - 1) := by positivity
    rw [hpow_eq] at hbound
    rw [habs]
    have hmul : Real.log u⁻¹ * Real.exp (-u) ≤ 2 * (Real.exp (-u) * u ^ ((1 / 2 : ℝ) - 1)) := by
      have h1 := mul_le_mul_of_nonneg_right hbound (Real.exp_pos (-u)).le
      linarith [show 2 * u ^ ((1 / 2 : ℝ) - 1) * Real.exp (-u) =
        2 * (Real.exp (-u) * u ^ ((1 / 2 : ℝ) - 1)) by ring]
    exact hmul.trans (le_add_of_nonneg_right hnn)

/-- Exact integral evaluation `∫_0^∞ exp(-u) du = 1`. -/
lemma integral_exp_neg_Ioi_zero :
    ∫ u in Ioi (0 : ℝ), Real.exp (-u) = 1 := by
  have hd : ∀ u ∈ Ici (0 : ℝ), HasDerivAt (fun x : ℝ => -Real.exp (-x)) (Real.exp (-u)) u := by
    intro u _
    have h := (hasDerivAt_id u).neg.exp.fun_neg
    simpa using h
  have hlim : Tendsto (fun x : ℝ => -Real.exp (-x)) atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    simpa using h.neg
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi (0 : ℝ)) := by
    simpa using exp_neg_integrableOn_Ioi (0 : ℝ) one_pos
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim
  simpa using hval

/-- Exact change-of-variables evaluation for `ε > 0`:
`ε * ∫_1^∞ log(log t) * t^{-ε - 1} dt = -γ + log (1 / ε)`, together with integrability. -/
lemma integral_log_log_mul_rpow_Ioi_one {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => Real.log (Real.log t) * t ^ (-ε - 1)) (Ioi (1 : ℝ)) ∧
    ε * ∫ t in Ioi (1 : ℝ), Real.log (Real.log t) * t ^ (-ε - 1) =
      -Real.eulerMascheroniConstant + Real.log (1 / ε) := by
  -- First compute `∫_0^∞ log v * exp(-ε v) dv` by scaling `u = ε v`
  have hint_exp_ε : IntegrableOn (fun v : ℝ => Real.exp (-ε * v)) (Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi 0 hε
  have hint_v : IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-ε * v)) (Ioi (0 : ℝ)) := by
    -- Under `v ↦ ε * v`, `(log (ε v) - log ε) * exp(-(ε v))` is integrable
    have h1 : IntegrableOn (fun v : ℝ => Real.log (ε * v) * Real.exp (-(ε * v))) (Ioi (0 : ℝ)) := by
      have hind : Integrable ((Ioi (0 : ℝ)).indicator (fun u : ℝ => Real.log u * Real.exp (-u))) :=
        (integrable_indicator_iff measurableSet_Ioi).mpr integrableOn_log_mul_exp_neg
      have hc := hind.comp_mul_left' hε.ne'
      rw [← integrable_indicator_iff measurableSet_Ioi]
      refine hc.congr (Eventually.of_forall fun v => ?_)
      by_cases hv : 0 < v
      · have hεv : 0 < ε * v := mul_pos hε hv
        simp [Set.indicator_of_mem (Set.mem_Ioi.mpr hv), Set.indicator_of_mem (Set.mem_Ioi.mpr hεv)]
      · have hεv : ¬ 0 < ε * v := fun h => hv ((mul_pos_iff_of_pos_left hε).mp h)
        simp [Set.indicator_of_notMem (show v ∉ Ioi (0 : ℝ) from hv),
          Set.indicator_of_notMem (show ε * v ∉ Ioi (0 : ℝ) from hεv)]
    have h2 : IntegrableOn (fun v : ℝ => Real.log ε * Real.exp (-ε * v)) (Ioi (0 : ℝ)) :=
      hint_exp_ε.const_mul (Real.log ε)
    have hsub : IntegrableOn
        (fun v : ℝ => Real.log (ε * v) * Real.exp (-(ε * v)) - Real.log ε * Real.exp (-ε * v))
        (Ioi (0 : ℝ)) := h1.sub h2
    refine hsub.congr_fun (fun v hv => ?_) measurableSet_Ioi
    have hv0 : 0 < v := Set.mem_Ioi.mp hv
    dsimp only
    rw [Real.log_mul hε.ne' hv0.ne', show -(ε * v) = -ε * v by ring]
    ring
  have hval_v : ε * ∫ v in Ioi (0 : ℝ), Real.log v * Real.exp (-ε * v) =
      -Real.eulerMascheroniConstant + Real.log (1 / ε) := by
    have hscale := integral_comp_mul_left_Ioi (fun u : ℝ => Real.log u * Real.exp (-u)) 0 hε
    rw [mul_zero, smul_eq_mul] at hscale
    have hscale_exp := integral_comp_mul_left_Ioi (fun u : ℝ => Real.exp (-u)) 0 hε
    rw [mul_zero, smul_eq_mul, integral_exp_neg_Ioi_zero, mul_one] at hscale_exp
    have hsplit : ∫ v in Ioi (0 : ℝ), Real.log (ε * v) * Real.exp (-(ε * v)) =
        Real.log ε * (∫ v in Ioi (0 : ℝ), Real.exp (-ε * v)) +
        ∫ v in Ioi (0 : ℝ), Real.log v * Real.exp (-ε * v) := by
      rw [← integral_const_mul, ← integral_add (hint_exp_ε.const_mul (Real.log ε)) hint_v]
      refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
      have hv0 : 0 < v := Set.mem_Ioi.mp hv
      rw [Real.log_mul hε.ne' hv0.ne', show -(ε * v) = -ε * v by ring]
      ring
    have hexp_eq : ∫ v in Ioi (0 : ℝ), Real.exp (-ε * v) = ε⁻¹ := by
      have hcongr : ∫ v in Ioi (0 : ℝ), Real.exp (-(ε * v)) = ∫ v in Ioi (0 : ℝ), Real.exp (-ε * v) :=
        setIntegral_congr_fun measurableSet_Ioi fun v _ => by congr 1; ring
      rw [← hcongr, hscale_exp]
    rw [hsplit, hexp_eq, integral_log_mul_exp_neg_eq_neg_eulerMascheroni] at hscale
    have hmul := congrArg (ε * ·) hscale
    rw [mul_add, ← mul_assoc, mul_comm ε (Real.log ε), mul_assoc, mul_inv_cancel₀ hε.ne', mul_one,
      ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul] at hmul
    rw [one_div, Real.log_inv]
    linarith
  -- Now change variable `t = exp v` (`Ioi 0 → Ioi 1`)!
  have himg : Real.exp '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
    ext t
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact Real.one_lt_exp_iff.mpr hv
    · intro ht
      exact ⟨Real.log t, Real.log_pos ht, Real.exp_log (zero_lt_one.trans ht)⟩
  have hinj : InjOn Real.exp (Ioi (0 : ℝ)) := Real.exp_injective.injOn
  have hderiv : ∀ v ∈ Ioi (0 : ℝ), HasDerivWithinAt Real.exp (Real.exp v) (Ioi (0 : ℝ)) v :=
    fun v _ => (Real.hasDerivAt_exp v).hasDerivWithinAt
  have hcomp_eq : ∀ v ∈ Ioi (0 : ℝ),
      |Real.exp v| • (Real.log (Real.log (Real.exp v)) * (Real.exp v) ^ (-ε - 1)) =
        Real.log v * Real.exp (-ε * v) := by
    intro v _
    rw [abs_of_pos (Real.exp_pos v), smul_eq_mul, Real.log_exp,
      Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp]
    calc Real.exp v * (Real.log v * Real.exp (v * (-ε - 1)))
        = Real.log v * (Real.exp v * Real.exp (v * (-ε - 1))) := by ring
      _ = Real.log v * Real.exp (v + v * (-ε - 1)) := by rw [← Real.exp_add]
      _ = Real.log v * Real.exp (-ε * v) := by congr 2; ring
  have hint_t : IntegrableOn (fun t : ℝ => Real.log (Real.log t) * t ^ (-ε - 1)) (Ioi (1 : ℝ)) := by
    rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj]
    exact hint_v.congr_fun (fun v hv => (hcomp_eq v hv).symm) measurableSet_Ioi
  have hval_t : ∫ t in Ioi (1 : ℝ), Real.log (Real.log t) * t ^ (-ε - 1) =
      ∫ v in Ioi (0 : ℝ), Real.log v * Real.exp (-ε * v) := by
    rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
    exact setIntegral_congr_fun measurableSet_Ioi hcomp_eq
  exact ⟨hint_t, by rw [hval_t, hval_v]⟩

/-- Prime Dirichlet series `P(σ) = ∑'_p p^{-σ}` for `σ > 1`. -/
def primeZetaSum (σ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, (p.1 : ℝ) ^ (-σ)

/-- Exact Abel-summation integral representation of `primeZetaSum σ` for `σ > 1`:
`∑'_p p^{-σ} = (σ - 1) * ∫_1^∞ mertensSum2 t * t^{-σ} dt`. -/
lemma primeZetaSum_eq_integral_mertensSum2 {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun t : ℝ => mertensSum2 t * t ^ (-σ)) (Ioi (1 : ℝ)) ∧
    primeZetaSum σ = (σ - 1) * ∫ t in Ioi (1 : ℝ), mertensSum2 t * t ^ (-σ) := by
  set ε : ℝ := σ - 1 with hε_def
  have hε : 0 < ε := sub_pos.mpr hσ
  have hσ_eq : -σ = -ε - 1 := by dsimp only [ε]; ring
  obtain ⟨C, hC, hM2⟩ := mertens_second_theorem_ge_two
  -- Bound `|mertensSum2 t| ≤ K₁ * t ^ (ε / 2)` for `t ≥ 1`
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmertens_bound : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t →
      0 ≤ mertensSum2 t ∧ mertensSum2 t ≤ K * t ^ (ε / 2) := by
    set K : ℝ := 2 / ε + |meisselMertensConst| + C / Real.log 2 + 1
    refine ⟨K, by positivity, fun t ht1 => ⟨Finset.sum_nonneg fun p _ => by positivity, ?_⟩⟩
    by_cases ht2 : 2 ≤ t
    · have ht0 : 0 < t := by linarith
      have hLt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
      have hLt_pos : 0 < Real.log t := hlog2_pos.trans_le hLt_ge
      have hloglog : Real.log (Real.log t) ≤ Real.log t :=
        (Real.log_le_sub_one_of_pos hLt_pos).trans (by linarith)
      have hlog_rpow : Real.log t ≤ (2 / ε) * t ^ (ε / 2) := by
        have h := Real.log_le_rpow_div ht0.le (by positivity : 0 < ε / 2)
        linarith [show t ^ (ε / 2) / (ε / 2) = (2 / ε) * t ^ (ε / 2) by field_simp [hε.ne']]
      have h1_le_pow : (1 : ℝ) ≤ t ^ (ε / 2) := Real.one_le_rpow ht1 (by positivity)
      have hC_div : C / Real.log t ≤ C / Real.log 2 :=
        div_le_div_of_nonneg_left hC.le hlog2_pos hLt_ge
      have hbd := (abs_le.mp (hM2 t ht2)).2
      have hm_le : mertensSum2 t ≤ Real.log (Real.log t) + |meisselMertensConst| + C / Real.log 2 := by
        linarith [le_abs_self meisselMertensConst]
      dsimp only [K]
      nlinarith [abs_nonneg meisselMertensConst, div_nonneg hC.le hlog2_pos.le]
    · push Not at ht2
      have hfl : ⌊t⌋₊ ≤ 1 := Nat.lt_succ_iff.mp (Nat.floor_lt (by linarith) |>.mpr ht2)
      have hempty : (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro p hp
        simp only [Finset.mem_Icc] at hp
        have hp1 : p = 1 := by omega
        subst hp1; exact Nat.not_prime_one
      unfold mertensSum2
      rw [hempty, Finset.sum_empty]
      positivity
  obtain ⟨K, hK_pos, hKbd⟩ := hmertens_bound
  have hmeas_m2 : Measurable mertensSum2 := by
    have h : mertensSum2 =
        (fun k : ℕ => ∑ p ∈ (Finset.Icc 1 k).filter Nat.Prime, (p : ℝ)⁻¹) ∘ Nat.floor := rfl
    rw [h]; exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
  have hint : IntegrableOn (fun t : ℝ => mertensSum2 t * t ^ (-σ)) (Ioi (1 : ℝ)) := by
    have hexp : ε / 2 - σ < -1 := by dsimp only [ε]; linarith
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt hexp zero_lt_one).const_mul K)
      (hmeas_m2.mul (measurable_id.pow_const (-σ))).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht1 : 1 ≤ t := (Set.mem_Ioi.mp ht).le
    have ht0 : 0 < t := zero_lt_one.trans_le ht1
    rw [Real.norm_of_nonneg (mul_nonneg (hKbd t ht1).1 (Real.rpow_nonneg ht0.le _))]
    calc mertensSum2 t * t ^ (-σ)
        ≤ (K * t ^ (ε / 2)) * t ^ (-σ) :=
          mul_le_mul_of_nonneg_right (hKbd t ht1).2 (Real.rpow_nonneg ht0.le _)
      _ = K * (t ^ (ε / 2) * t ^ (-σ)) := by ring
      _ = K * t ^ (ε / 2 - σ) := by rw [← Real.rpow_add ht0, sub_eq_add_neg]
  refine ⟨hint, ?_⟩
  -- For every `N ≥ 1`, apply `abel_summation_real` to `b n = if n.Prime then (n : ℝ)⁻¹ else 0` and `φ(t) = t ^ (-ε)`
  have habel_N : ∀ N : ℕ, 1 ≤ N →
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ) ^ (-σ) =
        mertensSum2 (N : ℝ) * (N : ℝ) ^ (-ε) +
        ε * ∫ t in (1 : ℝ)..(N : ℝ), mertensSum2 t * t ^ (-σ) := by
    intro N hN
    have hNR : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    have hd : ∀ t ∈ Set.Icc (1 : ℝ) (N : ℝ),
        HasDerivAt (fun u : ℝ => u ^ (-ε)) ((-ε) * t ^ (-σ)) t := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans_le ht.1
      have h1 := Real.hasDerivAt_rpow_const (p := -ε) (Or.inl ht0.ne')
      refine h1.congr_deriv ?_
      rw [hσ_eq]
    have hc : ContinuousOn (fun t : ℝ => (-ε) * t ^ (-σ)) (Set.Icc (1 : ℝ) (N : ℝ)) :=
      continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id fun t ht =>
        Or.inl (zero_lt_one.trans_le ht.1).ne')
    have hab := abel_summation_real (fun n : ℕ => if n.Prime then (n : ℝ)⁻¹ else 0) hNR hd hc
    rw [Nat.floor_natCast] at hab
    have hstep_eq : ∀ t : ℝ, realStepSum (fun n : ℕ => if n.Prime then (n : ℝ)⁻¹ else 0) t =
        mertensSum2 t := fun t => by
      unfold realStepSum mertensSum2; rw [← Finset.sum_filter]
    have hLHS : ∑ n ∈ Finset.Icc 1 N, (if n.Prime then (n : ℝ)⁻¹ else 0) * (n : ℝ) ^ (-ε) =
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ) ^ (-σ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n hn => ?_
      split_ifs with hp
      · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
        rw [← Real.rpow_neg_one (n : ℝ), ← Real.rpow_add hn0]
        congr 1; dsimp only [ε]; ring
      · simp
    rw [hLHS, hstep_eq (N : ℝ)] at hab
    have hint_eq : ∫ t in (1 : ℝ)..(N : ℝ),
        realStepSum (fun n : ℕ => if n.Prime then (n : ℝ)⁻¹ else 0) t * ((-ε) * t ^ (-σ)) =
        (-ε) * ∫ t in (1 : ℝ)..(N : ℝ), mertensSum2 t * t ^ (-σ) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hstep_eq t]; ring
    rw [hint_eq] at hab
    linarith
  -- Pass `N → ∞`: LHS → `primeZetaSum σ`, boundary term → `0`, integral → `∫_{Ioi 1}`
  have hLHS_lim : Tendsto (fun N : ℕ => ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ) ^ (-σ))
      atTop (𝓝 (primeZetaSum σ)) := by
    have hsumm_nat : Summable (fun n : ℕ => if n.Prime then (n : ℝ) ^ (-σ) else 0) := by
      have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
        have h := Real.summable_nat_rpow_inv.mpr hσ
        exact h.congr fun n => (Real.rpow_neg (Nat.cast_nonneg n) σ).symm
      refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
        (fun n => by split_ifs <;> [exact le_rfl; positivity]) hnat
    have htsum_eq : ∑' n : ℕ, (if n.Prime then (n : ℝ) ^ (-σ) else 0) = primeZetaSum σ := by
      unfold primeZetaSum
      have hsub : (∑' p : Nat.Primes, (p.1 : ℝ) ^ (-σ)) =
          ∑' p : ↥{p : ℕ | p.Prime}, (p.1 : ℝ) ^ (-σ) := rfl
      rw [hsub, tsum_subtype ({p : ℕ | p.Prime}) (fun n : ℕ => (n : ℝ) ^ (-σ))]
      refine tsum_congr fun n => ?_
      by_cases hp : n.Prime <;> simp [hp, Set.indicator]
    rw [← htsum_eq]
    have htend := hsumm_nat.hasSum.tendsto_sum_nat
    have hshift := htend.comp (tendsto_add_atTop_nat 1)
    refine hshift.congr fun N => ?_
    dsimp only [Function.comp_apply]
    rw [Finset.sum_filter]
    have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 N),
      if_neg Nat.not_prime_zero, zero_add]
  have hbd_lim : Tendsto (fun N : ℕ => mertensSum2 (N : ℝ) * (N : ℝ) ^ (-ε)) atTop (𝓝 0) := by
    have hpow0 : Tendsto (fun N : ℕ => K * (N : ℝ) ^ (-(ε / 2))) atTop (𝓝 0) := by
      have h1 := (tendsto_rpow_neg_atTop (by positivity : 0 < ε / 2)).comp tendsto_natCast_atTop_atTop
      simpa using h1.const_mul K
    refine squeeze_zero_norm' (a := fun N : ℕ => K * (N : ℝ) ^ (-(ε / 2))) ?_ hpow0
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    have hN0 : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans_le hNR
    rw [Real.norm_of_nonneg (mul_nonneg (hKbd (N : ℝ) hNR).1 (Real.rpow_nonneg hN0.le _))]
    calc mertensSum2 (N : ℝ) * (N : ℝ) ^ (-ε)
        ≤ (K * (N : ℝ) ^ (ε / 2)) * (N : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (hKbd (N : ℝ) hNR).2 (Real.rpow_nonneg hN0.le _)
      _ = K * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-ε)) := by ring
      _ = K * (N : ℝ) ^ (-(ε / 2)) := by
          rw [← Real.rpow_add hN0]; congr 2; ring
  have hint_lim : Tendsto (fun N : ℕ => ε * ∫ t in (1 : ℝ)..(N : ℝ), mertensSum2 t * t ^ (-σ))
      atTop (𝓝 (ε * ∫ t in Ioi (1 : ℝ), mertensSum2 t * t ^ (-σ))) :=
    (intervalIntegral_tendsto_integral_Ioi (1 : ℝ) hint tendsto_natCast_atTop_atTop).const_mul ε
  have hRHS_lim : Tendsto (fun N : ℕ =>
      mertensSum2 (N : ℝ) * (N : ℝ) ^ (-ε) +
        ε * ∫ t in (1 : ℝ)..(N : ℝ), mertensSum2 t * t ^ (-σ))
      atTop (𝓝 (ε * ∫ t in Ioi (1 : ℝ), mertensSum2 t * t ^ (-σ))) := by
    simpa using hbd_lim.add hint_lim
  exact tendsto_nhds_unique hLHS_lim
    (hRHS_lim.congr' (by filter_upwards [eventually_ge_atTop 1] with N hN using (habel_N N hN).symm))

/-- **Side 1 Limit (`σ → 1⁺`)**:
from Mertens' Second Theorem + `∫_0^∞ log u · exp(-u) du = -γ`,
`Tendsto (fun σ => primeZetaSum σ - log (1 / (σ - 1))) (𝓝[>] 1) (𝓝 (meisselMertensConst - γ))`. -/
theorem tendsto_primeZetaSum_sub_log_eq_meisselMertens_sub_gamma :
    Tendsto (fun σ : ℝ => primeZetaSum σ - Real.log (1 / (σ - 1)))
      (𝓝[>] (1 : ℝ)) (𝓝 (meisselMertensConst - Real.eulerMascheroniConstant)) := by
  obtain ⟨C, hC, hM2⟩ := mertens_second_theorem_ge_two
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Integrability of `|log (log t) + M| / t` on `(1, 2]` (for the `(1, 2]` remainder)
  have hint_12_ll : IntegrableOn (fun t : ℝ => Real.log (Real.log t) * t ^ (-(1 : ℝ) - 1)) (Ioc (1 : ℝ) 2) :=
    (integral_log_log_mul_rpow_Ioi_one one_pos).1.mono_set Ioc_subset_Ioi_self
  have hint_12_abs : IntegrableOn
      (fun t : ℝ => (|Real.log (Real.log t)| + |meisselMertensConst| + 1) / t) (Ioc (1 : ℝ) 2) := by
    have h1 : IntegrableOn (fun t : ℝ => |Real.log (Real.log t)| / t) (Ioc (1 : ℝ) 2) := by
      refine Integrable.mono' (hint_12_ll.abs.const_mul 2)
        ((continuous_abs.measurable.comp (Real.measurable_log.comp Real.measurable_log)).div
          measurable_id).aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
      have ht0 : 0 < t := zero_lt_one.trans ht.1
      have hpow : t ^ (-(1 : ℝ) - 1) = (t ^ 2)⁻¹ := by
        rw [show (-(1 : ℝ) - 1) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
      rw [Real.norm_of_nonneg (div_nonneg (abs_nonneg _) ht0.le), abs_mul, hpow,
        abs_of_pos (inv_pos.mpr (sq_pos_of_pos ht0))]
      have hle : t⁻¹ ≤ 2 * (t ^ 2)⁻¹ := by
        have h1 : t ≤ 2 := ht.2
        have h2 : t * (t ^ 2)⁻¹ = t⁻¹ := by field_simp [ht0.ne']
        nlinarith [inv_pos.mpr (sq_pos_of_pos ht0)]
      rw [div_eq_mul_inv]
      nlinarith [abs_nonneg (Real.log (Real.log t))]
    have h2 : IntegrableOn (fun t : ℝ => (|meisselMertensConst| + 1) / t) (Ioc (1 : ℝ) 2) := by
      refine Integrable.mono'
        (integrableOn_const (C := |meisselMertensConst| + 1) (hs := measure_Ioc_lt_top.ne))
        (measurable_const.div measurable_id).aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
      rw [Real.norm_of_nonneg (div_nonneg (by positivity) (zero_lt_one.trans ht.1).le)]
      exact div_le_self (by positivity) ht.1.le
    have h12sum : IntegrableOn (fun t : ℝ => |Real.log (Real.log t)| / t + (|meisselMertensConst| + 1) / t)
        (Ioc (1 : ℝ) 2) := h1.add h2
    refine h12sum.congr_fun (fun t _ => by dsimp only; ring) measurableSet_Ioc
  set K₁ : ℝ := ∫ t in Ioc (1 : ℝ) 2, (|Real.log (Real.log t)| + |meisselMertensConst| + 1) / t
  have hK₁_nn : 0 ≤ K₁ :=
    setIntegral_nonneg measurableSet_Ioc fun t ht =>
      div_nonneg (by positivity) (zero_lt_one.trans ht.1).le
  set K₂ : ℝ := C * (1 / Real.log 2 + 1)
  have hK₂_pos : 0 < K₂ := by positivity
  -- Prove `|primeZetaSum σ - log(1/(σ-1)) - (M - γ)| ≤ K₁ * (σ - 1) + K₂ * √(σ - 1)` for `σ ∈ (1, 2)`
  rw [← tendsto_sub_nhds_zero_iff]
  have hbound_lim : Tendsto (fun σ : ℝ => K₁ * (σ - 1) + K₂ * Real.sqrt (σ - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have hsub0 : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      have hc : ContinuousAt (fun σ : ℝ => σ - 1) 1 := (continuous_id.sub continuous_const).continuousAt
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have h1 : Tendsto (fun σ : ℝ => K₁ * (σ - 1)) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      simpa using hsub0.const_mul K₁
    have h2 : Tendsto (fun σ : ℝ => K₂ * Real.sqrt (σ - 1)) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      have hs : Tendsto (fun σ : ℝ => Real.sqrt (σ - 1)) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
        simpa [Function.comp_def] using (Real.continuous_sqrt.continuousAt.tendsto.comp hsub0)
      simpa using hs.const_mul K₂
    simpa using h1.add h2
  refine squeeze_zero_norm' (a := fun σ : ℝ => K₁ * (σ - 1) + K₂ * Real.sqrt (σ - 1)) ?_ hbound_lim
  have hlt2 : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), σ < 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [self_mem_nhdsWithin, hlt2] with σ (hσ1 : 1 < σ) hσ2
  set ε : ℝ := σ - 1 with hε_def
  have hε : 0 < ε := sub_pos.mpr hσ1
  have hε_lt1 : ε < 1 := by dsimp only [ε]; linarith
  have hσ_eq : -σ = -ε - 1 := by dsimp only [ε]; ring
  have hP := primeZetaSum_eq_integral_mertensSum2 hσ1
  have hLL := integral_log_log_mul_rpow_Ioi_one hε
  have hint_const : IntegrableOn (fun t : ℝ => meisselMertensConst * t ^ (-ε - 1)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -ε - 1 < -1) zero_lt_one).const_mul _
  have hval_const : ε * ∫ t in Ioi (1 : ℝ), meisselMertensConst * t ^ (-ε - 1) =
      meisselMertensConst := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -ε - 1 < -1) zero_lt_one]
    have hne : -ε - 1 + 1 ≠ 0 := by linarith
    rw [Real.one_rpow]
    field_simp [hε.ne', hne]
    ring
  set E : ℝ → ℝ := fun t => mertensSum2 t - (Real.log (Real.log t) + meisselMertensConst)
  have hint_E : IntegrableOn (fun t : ℝ => E t * t ^ (-ε - 1)) (Ioi (1 : ℝ)) := by
    have hP_int : IntegrableOn (fun t : ℝ => mertensSum2 t * t ^ (-ε - 1)) (Ioi (1 : ℝ)) := by
      simpa [hσ_eq] using hP.1
    have hsum_int : IntegrableOn
        (fun t : ℝ => Real.log (Real.log t) * t ^ (-ε - 1) + meisselMertensConst * t ^ (-ε - 1))
        (Ioi (1 : ℝ)) := hLL.1.add hint_const
    have hsub_int : IntegrableOn
        (fun t : ℝ => mertensSum2 t * t ^ (-ε - 1) -
          (Real.log (Real.log t) * t ^ (-ε - 1) + meisselMertensConst * t ^ (-ε - 1)))
        (Ioi (1 : ℝ)) := hP_int.sub hsum_int
    refine hsub_int.congr_fun (fun t _ => by dsimp only [E]; ring) measurableSet_Ioi
  have hdiff_eq : primeZetaSum σ - Real.log (1 / ε) - (meisselMertensConst - Real.eulerMascheroniConstant) =
      ε * ∫ t in Ioi (1 : ℝ), E t * t ^ (-ε - 1) := by
    have hP_int : IntegrableOn (fun t : ℝ => mertensSum2 t * t ^ (-ε - 1)) (Ioi (1 : ℝ)) := by
      simpa [hσ_eq] using hP.1
    have hsum_int : IntegrableOn
        (fun t : ℝ => Real.log (Real.log t) * t ^ (-ε - 1) + meisselMertensConst * t ^ (-ε - 1))
        (Ioi (1 : ℝ)) := hLL.1.add hint_const
    have hsub : ∫ t in Ioi (1 : ℝ), E t * t ^ (-ε - 1) =
        (∫ t in Ioi (1 : ℝ), mertensSum2 t * t ^ (-ε - 1)) -
        ((∫ t in Ioi (1 : ℝ), Real.log (Real.log t) * t ^ (-ε - 1)) +
         (∫ t in Ioi (1 : ℝ), meisselMertensConst * t ^ (-ε - 1))) := by
      rw [← integral_add hLL.1 hint_const, ← integral_sub hP_int hsum_int]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by dsimp only [E]; ring
    rw [hsub, mul_sub, mul_add, hLL.2, hval_const]
    have hP2 : ε * ∫ t in Ioi (1 : ℝ), mertensSum2 t * t ^ (-ε - 1) = primeZetaSum σ := by
      rw [← hσ_eq, hP.2]
    rw [hP2]
    ring
  -- Split `Ioi 1 = Ioc 1 2 ∪ Ioi 2`
  have hsplit_E : ∫ t in Ioi (1 : ℝ), E t * t ^ (-ε - 1) =
      (∫ t in Ioc (1 : ℝ) 2, E t * t ^ (-ε - 1)) +
      (∫ t in Ioi (2 : ℝ), E t * t ^ (-ε - 1)) := by
    have hunion : Ioc (1 : ℝ) 2 ∪ Ioi (2 : ℝ) = Ioi (1 : ℝ) := Ioc_union_Ioi_eq_Ioi (by norm_num)
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint_E.mono_set Ioc_subset_Ioi_self)
      (hint_E.mono_set (Ioi_subset_Ioi (by norm_num))), hunion]
  -- Bound part 1 on `(1, 2]` by `K₁ * ε`
  have hpart1 : ε * |∫ t in Ioc (1 : ℝ) 2, E t * t ^ (-ε - 1)| ≤ K₁ * ε := by
    have h1 : |∫ t in Ioc (1 : ℝ) 2, E t * t ^ (-ε - 1)| ≤ K₁ := by
      calc |∫ t in Ioc (1 : ℝ) 2, E t * t ^ (-ε - 1)|
          ≤ ∫ t in Ioc (1 : ℝ) 2, |E t * t ^ (-ε - 1)| := abs_integral_le_integral_abs
        _ ≤ K₁ := by
            refine setIntegral_mono_on (hint_E.mono_set Ioc_subset_Ioi_self).abs
              hint_12_abs measurableSet_Ioc fun t ht => ?_
            have ht0 : 0 < t := zero_lt_one.trans ht.1
            have hpow_le : t ^ (-ε - 1) ≤ t⁻¹ := by
              have h := Real.rpow_le_rpow_of_exponent_le ht.1.le (by linarith : -ε - 1 ≤ (-1 : ℝ))
              simpa [Real.rpow_neg_one] using h
            have hm2_le1 : |mertensSum2 t| ≤ 1 := by
              have hnn : 0 ≤ mertensSum2 t := Finset.sum_nonneg fun p _ => by positivity
              rw [abs_of_nonneg hnn]
              have hfl : ⌊t⌋₊ ≤ 2 := Nat.floor_le_of_le (by exact_mod_cast ht.2)
              unfold mertensSum2
              calc ∑ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, (p : ℝ)⁻¹
                  ≤ ∑ p ∈ (Finset.Icc 1 2).filter Nat.Prime, (p : ℝ)⁻¹ :=
                    Finset.sum_le_sum_of_subset_of_nonneg
                      (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hfl))
                      fun p _ _ => by positivity
                _ = (2 : ℝ)⁻¹ := by
                    have hfilt : (Finset.Icc 1 2).filter Nat.Prime = {2} := by decide
                    rw [hfilt, Finset.sum_singleton]; norm_num
                _ ≤ 1 := by norm_num
            have hE_le : |E t| ≤ |Real.log (Real.log t)| + |meisselMertensConst| + 1 := by
              dsimp only [E]
              have h1 := abs_sub (mertensSum2 t) (Real.log (Real.log t) + meisselMertensConst)
              have h2 := abs_add_le (Real.log (Real.log t)) meisselMertensConst
              linarith
            rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _), div_eq_mul_inv]
            exact mul_le_mul hE_le hpow_le (Real.rpow_pos_of_pos ht0 _).le (by positivity)
    nlinarith
  -- Bound part 2 on `(2, ∞)` by splitting at `X := Real.exp (1 / Real.sqrt ε) > 2`!
  set R : ℝ := 1 / Real.sqrt ε with hR_def
  have hR_gt1 : 1 < R := by
    dsimp only [R]
    rw [one_lt_div (Real.sqrt_pos.mpr hε)]
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt hε.le hε_lt1
  have hlog2_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  set X : ℝ := Real.exp R with hX_def
  have h2_lt_X : 2 < X := by
    have h1 : Real.log 2 < R := hlog2_lt1.trans hR_gt1
    simpa [X, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_lt_exp.mpr h1
  have hlogX : Real.log X = R := Real.log_exp R
  have hpart2 : ε * |∫ t in Ioi (2 : ℝ), E t * t ^ (-ε - 1)| ≤ K₂ * Real.sqrt ε := by
    have hsplit2 : ∫ t in Ioi (2 : ℝ), E t * t ^ (-ε - 1) =
        (∫ t in Ioc (2 : ℝ) X, E t * t ^ (-ε - 1)) +
        (∫ t in Ioi X, E t * t ^ (-ε - 1)) := by
      have hunion : Ioc (2 : ℝ) X ∪ Ioi X = Ioi (2 : ℝ) := Ioc_union_Ioi_eq_Ioi h2_lt_X.le
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hint_E.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num))))
        (hint_E.mono_set (Ioi_subset_Ioi (by linarith))), hunion]
    -- On `(2, X]`: `|E t| * t ^ (-ε - 1) ≤ (C / log 2) * (1 / t)`, integral `≤ (C / log 2) * R`
    have h2X : |∫ t in Ioc (2 : ℝ) X, E t * t ^ (-ε - 1)| ≤ (C / Real.log 2) * R := by
      have hint_inv : IntegrableOn (fun t : ℝ => (C / Real.log 2) * t⁻¹) (Ioc (2 : ℝ) X) := by
        refine (ContinuousOn.inv₀ continuousOn_id fun t ht => by
          have : (2 : ℝ) ≤ t := ht.1; simp only [id_eq]; linarith).const_mul (C / Real.log 2)
          |>.integrableOn_Icc.mono_set Ioc_subset_Icc_self
      calc |∫ t in Ioc (2 : ℝ) X, E t * t ^ (-ε - 1)|
          ≤ ∫ t in Ioc (2 : ℝ) X, |E t * t ^ (-ε - 1)| := abs_integral_le_integral_abs
        _ ≤ ∫ t in Ioc (2 : ℝ) X, (C / Real.log 2) * t⁻¹ := by
            refine setIntegral_mono_on
              (hint_E.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))).abs
              hint_inv measurableSet_Ioc fun t ht => ?_
            have ht2 : 2 ≤ t := ht.1.le
            have ht0 : 0 < t := by linarith
            have hpow_le : t ^ (-ε - 1) ≤ t⁻¹ := by
              have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ t)
                (by linarith : -ε - 1 ≤ (-1 : ℝ))
              simpa [Real.rpow_neg_one] using h
            have hE_le : |E t| ≤ C / Real.log 2 :=
              (hM2 t ht2).trans (div_le_div_of_nonneg_left hC.le hlog2_pos (Real.log_le_log (by norm_num) ht2))
            rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
            exact mul_le_mul hE_le hpow_le (Real.rpow_pos_of_pos ht0 _).le (by positivity)
        _ = (C / Real.log 2) * (Real.log X - Real.log 2) := by
            rw [integral_const_mul, ← intervalIntegral.integral_of_le h2_lt_X.le,
              integral_inv_of_pos (by norm_num : (0 : ℝ) < 2) (by linarith),
              Real.log_div (by linarith) (by norm_num)]
        _ ≤ (C / Real.log 2) * R := by
            rw [hlogX]
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    -- On `(X, ∞)`: `|E t| * t ^ (-ε - 1) ≤ (C / R) * t ^ (-ε - 1)`, integral `≤ (C / R) * (1 / ε)`
    have hXinf : |∫ t in Ioi X, E t * t ^ (-ε - 1)| ≤ (C / R) / ε := by
      have hX0 : 0 < X := by linarith
      have hint_rpow : IntegrableOn (fun t : ℝ => (C / R) * t ^ (-ε - 1)) (Ioi X) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith : -ε - 1 < -1) hX0).const_mul (C / R)
      calc |∫ t in Ioi X, E t * t ^ (-ε - 1)|
          ≤ ∫ t in Ioi X, |E t * t ^ (-ε - 1)| := abs_integral_le_integral_abs
        _ ≤ ∫ t in Ioi X, (C / R) * t ^ (-ε - 1) := by
            refine setIntegral_mono_on (hint_E.mono_set (Ioi_subset_Ioi (by linarith))).abs
              hint_rpow measurableSet_Ioi fun t ht => ?_
            have hXt : X ≤ t := (Set.mem_Ioi.mp ht).le
            have ht2 : 2 ≤ t := by linarith
            have ht0 : 0 < t := by linarith
            have hlog_ge : R ≤ Real.log t := by
              rw [← hlogX]; exact Real.log_le_log hX0 hXt
            have hE_le : |E t| ≤ C / R :=
              (hM2 t ht2).trans (div_le_div_of_nonneg_left hC.le (by linarith) hlog_ge)
            rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
            exact mul_le_mul_of_nonneg_right hE_le (Real.rpow_pos_of_pos ht0 _).le
        _ = (C / R) * (X ^ (-ε) / ε) := by
            rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -ε - 1 < -1) hX0]
            have h1 : -ε - 1 + 1 = -ε := by ring
            rw [h1]
            field_simp [hε.ne', (by linarith : R ≠ 0)]
        _ ≤ (C / R) * (1 / ε) := by
            have hX_pow : X ^ (-ε) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
            have hdiv : X ^ (-ε) / ε ≤ 1 / ε := div_le_div_of_nonneg_right hX_pow hε.le
            exact mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = (C / R) / ε := by ring
    have htri := abs_add_le (∫ t in Ioc (2 : ℝ) X, E t * t ^ (-ε - 1))
      (∫ t in Ioi X, E t * t ^ (-ε - 1))
    rw [hsplit2]
    have hεR : ε * R = Real.sqrt ε := by
      dsimp only [R]
      have hs0 : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.mpr hε).ne'
      field_simp [hs0]
      exact (Real.sq_sqrt hε.le).symm
    have hinvR : 1 / R = Real.sqrt ε := by
      dsimp only [R]; rw [one_div_one_div]
    have halg : ε * ((C / Real.log 2) * R + (C / R) / ε) = K₂ * Real.sqrt ε := by
      have h1 : ε * ((C / Real.log 2) * R) = (C / Real.log 2) * Real.sqrt ε := by
        calc ε * ((C / Real.log 2) * R) = (C / Real.log 2) * (ε * R) := by ring
          _ = (C / Real.log 2) * Real.sqrt ε := by rw [hεR]
      have h2 : ε * ((C / R) / ε) = C * Real.sqrt ε := by
        rw [mul_div_cancel₀ _ hε.ne', div_eq_mul_inv, show R⁻¹ = 1 / R by ring, hinvR]
      rw [mul_add, h1, h2]
      dsimp only [K₂]; ring
    calc ε * |(∫ t in Ioc (2 : ℝ) X, E t * t ^ (-ε - 1)) + (∫ t in Ioi X, E t * t ^ (-ε - 1))|
        ≤ ε * ((C / Real.log 2) * R + (C / R) / ε) :=
          mul_le_mul_of_nonneg_left (htri.trans (add_le_add h2X hXinf)) hε.le
      _ = K₂ * Real.sqrt ε := halg
  rw [Real.norm_eq_abs, hdiff_eq, abs_mul, abs_of_pos hε, hsplit_E]
  have htri := abs_add_le (∫ t in Ioc (1 : ℝ) 2, E t * t ^ (-ε - 1))
    (∫ t in Ioi (2 : ℝ), E t * t ^ (-ε - 1))
  have hcomb := mul_le_mul_of_nonneg_left htri hε.le
  rw [mul_add] at hcomb
  linarith

/-- Elementary logarithm-tail inequality on `[0, 1/2]`:
`0 ≤ -(Real.log (1 - x) + x) ≤ x ^ 2`. -/
lemma neg_log_one_sub_sub_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    0 ≤ -(Real.log (1 - x) + x) ∧ -(Real.log (1 - x) + x) ≤ x ^ 2 := by
  constructor
  · have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - x)
    linarith
  · -- Prove `g(x) = log(1 - x) + x + x^2 ≥ 0` on `[0, 1/2]` via monotonicity (`g' ≥ 0`, `g(0) = 0`)
    set g : ℝ → ℝ := fun u => Real.log (1 - u) + u + u ^ 2
    have hmono : MonotoneOn g (Set.Icc 0 (1 / 2 : ℝ)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2 : ℝ)) ?_ ?_ ?_
      · exact ((Real.continuousOn_log.comp (continuousOn_const.sub continuousOn_id)
          fun u hu => by show (1 : ℝ) - u ≠ 0; linarith [hu.2]).add continuousOn_id).add (continuousOn_pow 2)
      · intro u hu
        rw [interior_Icc] at hu
        have hd1 : HasDerivAt (fun v : ℝ => 1 - v) (-1) u := by
          simpa using (hasDerivAt_const u (1 : ℝ)).fun_sub (hasDerivAt_id u)
        have hd : HasDerivAt g ((-1) / (1 - u) + 1 + 2 * u ^ (2 - 1)) u :=
          ((hd1.log (by linarith [hu.2])).fun_add (hasDerivAt_id u)).fun_add (hasDerivAt_pow 2 u)
        exact hd.differentiableAt.differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        have h1u : 0 < 1 - u := by linarith [hu.2]
        have hd1 : HasDerivAt (fun v : ℝ => 1 - v) (-1) u := by
          simpa using (hasDerivAt_const u (1 : ℝ)).fun_sub (hasDerivAt_id u)
        have hd : HasDerivAt g ((-1) / (1 - u) + 1 + 2 * u ^ (2 - 1)) u :=
          ((hd1.log h1u.ne').fun_add (hasDerivAt_id u)).fun_add (hasDerivAt_pow 2 u)
        rw [hd.deriv]
        have halg : (-1) / (1 - u) + 1 + 2 * u ^ (2 - 1) = u * (1 - 2 * u) / (1 - u) := by
          field_simp [h1u.ne']; ring
        rw [halg]
        exact div_nonneg (mul_nonneg hu.1.le (by linarith [hu.2])) h1u.le
    have h0 : g 0 = 0 := by simp [g]
    have hge : g 0 ≤ g x := hmono ⟨le_rfl, by norm_num⟩ ⟨hx0, hx1⟩ hx0
    rw [h0] at hge
    dsimp only [g] at hge
    linarith

/-- Summability of the prime tail series `p ↦ log (1 - 1/p) + 1/p` over `Nat.Primes`. -/
theorem summable_log_one_sub_inv_add_inv :
    Summable (fun p : Nat.Primes => Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹) := by
  have hsq : Summable (fun p : Nat.Primes => ((p.1 : ℝ)⁻¹) ^ 2) := by
    have hnat : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
      refine (Real.summable_nat_rpow_inv.mpr one_lt_two).congr fun n => ?_
      rw [show (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ (2 : ℕ) by norm_cast, inv_pow]
    exact hnat.subtype ({p : ℕ | p.Prime})
  refine Summable.of_norm_bounded hsq fun p => ?_
  have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
  have hinv_nn : 0 ≤ (p.1 : ℝ)⁻¹ := by positivity
  have hinv_le : (p.1 : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) hp2
  have hbd := neg_log_one_sub_sub_bounds hinv_nn hinv_le
  rw [Real.norm_eq_abs, ← abs_neg, abs_of_nonneg hbd.1]
  exact hbd.2

/-- Exact real-log Euler product for `riemannZeta σ` (`σ > 1`):
`0 < (riemannZeta σ).re` and `Real.log (riemannZeta σ).re = ∑'_p (-Real.log (1 - p^{-σ}))`. -/
lemma real_log_riemannZeta_eq_tsum {σ : ℝ} (hσ : 1 < σ) :
    0 < (riemannZeta (σ : ℂ)).re ∧
    Real.log (riemannZeta (σ : ℂ)).re =
      ∑' p : Nat.Primes, -Real.log (1 - (p.1 : ℝ) ^ (-σ)) := by
  have heuler := riemannZeta_eulerProduct_exp_log (s := (σ : ℂ)) (by simpa using hσ)
  have hterm : ∀ p : Nat.Primes,
      -Complex.log (1 - (p.1 : ℂ) ^ (-(σ : ℂ))) =
        ((-Real.log (1 - (p.1 : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
    intro p
    have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
    have hp0 : (0 : ℝ) < (p.1 : ℝ) := by linarith
    have hpow_pos : 0 < (p.1 : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hp0 (-σ)
    have hpow_le : (p.1 : ℝ) ^ (-σ) ≤ 1 / 2 := by
      have h1 : (p.1 : ℝ) ^ (-σ) ≤ (p.1 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      rw [Real.rpow_neg_one] at h1
      have h2 : (p.1 : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
      linarith [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    have h1sub_pos : 0 < 1 - (p.1 : ℝ) ^ (-σ) := by linarith
    have hcpow : (p.1 : ℂ) ^ (-(σ : ℂ)) = (((p.1 : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.ofReal_cpow hp0.le]
    rw [hcpow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_log h1sub_pos.le, Complex.ofReal_neg]
  have htsumC : (∑' p : Nat.Primes, -Complex.log (1 - (p.1 : ℂ) ^ (-(σ : ℂ)))) =
      ((∑' p : Nat.Primes, -Real.log (1 - (p.1 : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr hterm
  rw [htsumC, ← Complex.ofReal_exp] at heuler
  have hre := congrArg Complex.re heuler
  rw [Complex.ofReal_re] at hre
  exact ⟨hre ▸ Real.exp_pos _, by rw [← hre, Real.log_exp]⟩

/-- **Side 2 Limit (`σ → 1⁺`)**:
from the Euler product `riemannZeta_eulerProduct_exp_log` and `riemannZeta_residue_one`,
`Tendsto (fun σ => primeZetaSum σ - log (1 / (σ - 1))) (𝓝[>] 1) (𝓝 (∑'_p (log (1 - 1/p) + 1/p)))`. -/
theorem tendsto_primeZetaSum_sub_log_eq_euler_tail :
    Tendsto (fun σ : ℝ => primeZetaSum σ - Real.log (1 / (σ - 1)))
      (𝓝[>] (1 : ℝ)) (𝓝 (∑' p : Nat.Primes, (Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹))) := by
  -- 1. `log (riemannZeta σ).re - log (1 / (σ - 1)) → 0` as `σ → 1⁺`
  have hzeta_lim : Tendsto (fun σ : ℝ => Real.log (riemannZeta (σ : ℂ)).re - Real.log (1 / (σ - 1)))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have hres_C : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * riemannZeta (σ : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 1) := by
      have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨(Complex.continuous_ofReal.continuousAt.tendsto (x := (1 : ℝ))).mono_left
          nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact_mod_cast hσ.ne'
      exact riemannZeta_residue_one.comp hmap
    have hres_R : Tendsto (fun σ : ℝ => (σ - 1) * (riemannZeta (σ : ℂ)).re)
        (𝓝[>] (1 : ℝ)) (𝓝 1) := by
      have h1 := (Complex.continuous_re.continuousAt.tendsto (x := (1 : ℂ))).comp hres_C
      rw [Complex.one_re] at h1
      refine h1.congr fun σ => ?_
      dsimp only [Function.comp_apply]
      have hsub : ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) := by push_cast; rfl
      rw [hsub, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hres_R
    rw [Real.log_one] at hlog
    refine hlog.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    have hε : 0 < σ - 1 := sub_pos.mpr hσ
    have hzpos : 0 < (riemannZeta (σ : ℂ)).re := (real_log_riemannZeta_eq_tsum hσ).1
    dsimp only [Function.comp_apply]
    rw [Real.log_mul hε.ne' hzpos.ne', one_div, Real.log_inv]
    ring
  -- 2. `∑'_p (log (1 - p^{-σ}) + p^{-σ}) → ∑'_p (log (1 - 1/p) + 1/p)` by `tendsto_tsum_of_dominated_convergence`
  have hsq : Summable (fun p : Nat.Primes => ((p.1 : ℝ)⁻¹) ^ 2) := by
    have hnat : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
      refine (Real.summable_nat_rpow_inv.mpr one_lt_two).congr fun n => ?_
      rw [show (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ (2 : ℕ) by norm_cast, inv_pow]
    exact hnat.subtype ({p : ℕ | p.Prime})
  have htail_lim : Tendsto
      (fun σ : ℝ => ∑' p : Nat.Primes, (Real.log (1 - (p.1 : ℝ) ^ (-σ)) + (p.1 : ℝ) ^ (-σ)))
      (𝓝[>] (1 : ℝ))
      (𝓝 (∑' p : Nat.Primes, (Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹))) := by
    refine tendsto_tsum_of_dominated_convergence hsq ?_ ?_
    · intro p
      have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
      have hp0 : (0 : ℝ) < (p.1 : ℝ) := by linarith
      have hpow_lim : Tendsto (fun σ : ℝ => (p.1 : ℝ) ^ (-σ)) (𝓝[>] (1 : ℝ)) (𝓝 ((p.1 : ℝ)⁻¹)) := by
        have hc : ContinuousAt (fun σ : ℝ => (p.1 : ℝ) ^ (-σ)) 1 :=
          (Real.continuousAt_const_rpow hp0.ne').comp continuousAt_neg
        have h1 : Tendsto (fun σ : ℝ => (p.1 : ℝ) ^ (-σ)) (𝓝[>] (1 : ℝ)) (𝓝 ((p.1 : ℝ) ^ (-(1 : ℝ)))) :=
          hc.tendsto.mono_left nhdsWithin_le_nhds
        simpa [Real.rpow_neg_one] using h1
      have h1sub_ne : 1 - (p.1 : ℝ)⁻¹ ≠ 0 := by
        have : (p.1 : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
        linarith
      exact ((Real.continuousAt_log h1sub_ne).tendsto.comp (tendsto_const_nhds.sub hpow_lim)).add hpow_lim
    · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ) p
      have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
      have hp0 : (0 : ℝ) < (p.1 : ℝ) := by linarith
      have hpow_nn : 0 ≤ (p.1 : ℝ) ^ (-σ) := Real.rpow_nonneg hp0.le _
      have hpow_le_inv : (p.1 : ℝ) ^ (-σ) ≤ (p.1 : ℝ)⁻¹ := by
        have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ (p.1 : ℝ))
          (by linarith : -σ ≤ (-1 : ℝ))
        simpa [Real.rpow_neg_one] using h
      have hinv_le_half : (p.1 : ℝ)⁻¹ ≤ 1 / 2 := by
        rw [one_div]; exact inv_anti₀ (by norm_num) hp2
      have hbd := neg_log_one_sub_sub_bounds hpow_nn (hpow_le_inv.trans hinv_le_half)
      rw [Real.norm_eq_abs, ← abs_neg, abs_of_nonneg hbd.1]
      exact hbd.2.trans (pow_le_pow_left₀ hpow_nn hpow_le_inv 2)
  -- 3. Combine: for `σ > 1`, `primeZetaSum σ - log(1/(σ-1)) = (log ζ(σ) - log(1/(σ-1))) + ∑_p (log(1 - p^{-σ}) + p^{-σ})`
  have hsum_lim := hzeta_lim.add htail_lim
  rw [zero_add] at hsum_lim
  refine hsum_lim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  rw [(real_log_riemannZeta_eq_tsum hσ).2]
  have hsumm_P : Summable (fun p : Nat.Primes => (p.1 : ℝ) ^ (-σ)) := by
    have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
      (Real.summable_nat_rpow_inv.mpr hσ).congr fun n => (Real.rpow_neg (Nat.cast_nonneg n) σ).symm
    exact hnat.subtype ({p : ℕ | p.Prime})
  have hsumm_tail : Summable (fun p : Nat.Primes => Real.log (1 - (p.1 : ℝ) ^ (-σ)) + (p.1 : ℝ) ^ (-σ)) := by
    refine Summable.of_norm_bounded hsq fun p => ?_
    have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
    have hp0 : (0 : ℝ) < (p.1 : ℝ) := by linarith
    have hpow_nn : 0 ≤ (p.1 : ℝ) ^ (-σ) := Real.rpow_nonneg hp0.le _
    have hpow_le_inv : (p.1 : ℝ) ^ (-σ) ≤ (p.1 : ℝ)⁻¹ := by
      have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ (p.1 : ℝ))
        (by linarith : -σ ≤ (-1 : ℝ))
      simpa [Real.rpow_neg_one] using h
    have hinv_le_half : (p.1 : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) hp2
    have hbd := neg_log_one_sub_sub_bounds hpow_nn (hpow_le_inv.trans hinv_le_half)
    rw [Real.norm_eq_abs, ← abs_neg, abs_of_nonneg hbd.1]
    exact hbd.2.trans (pow_le_pow_left₀ hpow_nn hpow_le_inv 2)
  have hsumm_log : Summable (fun p : Nat.Primes => -Real.log (1 - (p.1 : ℝ) ^ (-σ))) := by
    refine (hsumm_P.sub hsumm_tail).congr fun p => by ring
  have hadd_eq : (∑' p : Nat.Primes, -Real.log (1 - (p.1 : ℝ) ^ (-σ))) +
      (∑' p : Nat.Primes, (Real.log (1 - (p.1 : ℝ) ^ (-σ)) + (p.1 : ℝ) ^ (-σ))) =
      primeZetaSum σ := by
    rw [← hsumm_log.tsum_add hsumm_tail]
    unfold primeZetaSum
    refine tsum_congr fun p => by ring
  linarith

/-- **EXACT EULER–MASCHERONI RELATION FOR THE MEISSEL–MERTENS CONSTANT (0 ASSUMPTIONS!)**:
`meisselMertensConst = Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹)`. -/
theorem meisselMertensConst_eq_eulerMascheroni_add_tsum :
    meisselMertensConst =
      Real.eulerMascheroniConstant +
        ∑' p : Nat.Primes, (Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹) := by
  have : (𝓝[>] (1 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have heq := tendsto_nhds_unique
    tendsto_primeZetaSum_sub_log_eq_meisselMertens_sub_gamma
    tendsto_primeZetaSum_sub_log_eq_euler_tail
  linarith

/-! ## Section 5: Mertens' Third Theorem (Quantitative `O(1 / log x)` & Asymptotic `e^{-γ}`) -/

/-- Mertens' third prime product `∏_{p ≤ x} (1 - 1/p)`. -/
def mertensProd (x : ℝ) : ℝ :=
  ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 - (p : ℝ)⁻¹)

lemma mertensProd_pos (x : ℝ) : 0 < mertensProd x := by
  unfold mertensProd
  refine Finset.prod_pos fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
  have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
  linarith

/-- Elementary tail bound: `∑_{n > N} 1/n^2 ≤ 1 / N` for every `N ≥ 1`. -/
private lemma tsum_inv_sq_tail_le {N : ℕ} (hN : 1 ≤ N) :
    ∑' n : ℕ, (if N < n then ((n : ℝ)⁻¹) ^ 2 else 0) ≤ (N : ℝ)⁻¹ := by
  refine Real.tsum_le_of_sum_range_le (fun n => by split_ifs <;> positivity) fun M => ?_
  by_cases hMN : M ≤ N + 1
  · have hzero : ∑ n ∈ Finset.range M, (if N < n then ((n : ℝ)⁻¹) ^ 2 else 0) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [Finset.mem_range] at hn
      rw [if_neg (by omega)]
    rw [hzero]; positivity
  · push Not at hMN
    have hsplit : ∑ n ∈ Finset.range M, (if N < n then ((n : ℝ)⁻¹) ^ 2 else 0) =
        ∑ n ∈ Finset.Icc (N + 1) (M - 1), ((n : ℝ)⁻¹) ^ 2 := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
    rw [hsplit]
    have htel : ∀ K : ℕ, N + 1 ≤ K →
        ∑ n ∈ Finset.Icc (N + 1) K, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)) =
          1 / (N : ℝ) - 1 / (K : ℝ) := by
      intro K hK
      induction K, hK using Nat.le_induction with
      | base =>
        have hsing : Finset.Icc (N + 1) (N + 1) = {N + 1} := by simp
        rw [hsing, Finset.sum_singleton]
        push_cast; ring
      | succ m hm ih =>
        have hIcc : Finset.Icc (N + 1) (m + 1) = insert (m + 1) (Finset.Icc (N + 1) m) := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnot : m + 1 ∉ Finset.Icc (N + 1) m := by simp
        rw [hIcc, Finset.sum_insert hnot, ih]
        push_cast; ring
    calc ∑ n ∈ Finset.Icc (N + 1) (M - 1), ((n : ℝ)⁻¹) ^ 2
        ≤ ∑ n ∈ Finset.Icc (N + 1) (M - 1), ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn2 : (2 : ℝ) ≤ (n : ℝ) := by
            have := (Finset.mem_Icc.mp hn).1
            exact_mod_cast (by omega : 2 ≤ n)
          have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
          have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
          have halg : (1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ) = 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
            field_simp [hn0.ne', hn1.ne']; ring
          rw [halg, inv_pow, ← one_div]
          exact one_div_le_one_div_of_le (mul_pos hn0 hn1) (by nlinarith)
      _ = 1 / (N : ℝ) - 1 / ((M - 1 : ℕ) : ℝ) := htel (M - 1) (by omega)
      _ ≤ (N : ℝ)⁻¹ := by
          rw [one_div]
          have : (0 : ℝ) ≤ 1 / ((M - 1 : ℕ) : ℝ) := by positivity
          linarith

/-- Quantitative tail bound for `∑_{p ≤ x} (log(1 - 1/p) + 1/p)`:
for all `x ≥ 2`, its difference from `∑'_p (log(1 - 1/p) + 1/p)` has absolute value `≤ 2 / x`. -/
lemma abs_prime_log_tail_sub_le {x : ℝ} (hx : 2 ≤ x) :
    |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) -
      ∑' p : Nat.Primes, (Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹)| ≤ 2 / x := by
  set f : ℕ → ℝ := fun n => if n.Prime then Real.log (1 - (n : ℝ)⁻¹) + (n : ℝ)⁻¹ else 0
  have htsum_eq : ∑' p : Nat.Primes, (Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹) = ∑' n : ℕ, f n := by
    have hsub : (∑' p : Nat.Primes, (Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹)) =
        ∑' p : ↥{p : ℕ | p.Prime}, (Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹) := rfl
    rw [hsub, tsum_subtype ({p : ℕ | p.Prime}) (fun n : ℕ => Real.log (1 - (n : ℝ)⁻¹) + (n : ℝ)⁻¹)]
    refine tsum_congr fun n => ?_
    by_cases hp : n.Prime <;> simp [f, hp, Set.indicator]
  have hsumm_f : Summable f := by
    have h := (summable_subtype_iff_indicator (s := {p : ℕ | p.Prime})
      (f := fun n : ℕ => Real.log (1 - (n : ℝ)⁻¹) + (n : ℝ)⁻¹)).mp summable_log_one_sub_inv_add_inv
    refine h.congr fun n => ?_
    by_cases hp : n.Prime <;> simp [f, hp, Set.indicator]
  have hfin_eq : ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1), f n := by
    rw [Finset.sum_filter]
    have hset : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 ⌊x⌋₊)]
    simp [f]
  rw [htsum_eq, hfin_eq]
  have htail_eq : ∑' n : ℕ, f n - ∑ n ∈ Finset.range (⌊x⌋₊ + 1), f n =
      ∑' n : ℕ, (if ⌊x⌋₊ < n then f n else 0) := by
    have hsplit := hsumm_f.sum_add_tsum_compl (s := Finset.range (⌊x⌋₊ + 1))
    have hcompl : ∑' n : ↥(Finset.range (⌊x⌋₊ + 1) : Set ℕ)ᶜ, f n =
        ∑' n : ℕ, (if ⌊x⌋₊ < n then f n else 0) := by
      rw [tsum_subtype ((Finset.range (⌊x⌋₊ + 1) : Set ℕ)ᶜ) f]
      refine tsum_congr fun n => ?_
      have hiff : n ∈ ((Finset.range (⌊x⌋₊ + 1) : Set ℕ)ᶜ) ↔ ⌊x⌋₊ < n := by
        simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_range]; omega
      by_cases h : ⌊x⌋₊ < n
      · rw [Set.indicator_of_mem (hiff.mpr h), if_pos h]
      · rw [Set.indicator_of_notMem (fun hm => h (hiff.mp hm)), if_neg h]
    linarith
  rw [abs_sub_comm, htail_eq]
  have hf_le : ∀ n : ℕ, 0 ≤ -f n ∧ -f n ≤ if n.Prime then ((n : ℝ)⁻¹) ^ 2 else 0 := by
    intro n
    dsimp only [f]
    split_ifs with hp
    · have hp2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
      exact neg_log_one_sub_sub_bounds (by positivity) (by rw [one_div]; exact inv_anti₀ (by norm_num) hp2)
    · simp
  have hneg_tsum : |∑' n : ℕ, (if ⌊x⌋₊ < n then f n else 0)| =
      ∑' n : ℕ, (if ⌊x⌋₊ < n then -f n else 0) := by
    have hneg : -(∑' n : ℕ, (if ⌊x⌋₊ < n then f n else 0)) =
        ∑' n : ℕ, (if ⌊x⌋₊ < n then -f n else 0) := by
      rw [← tsum_neg]
      refine tsum_congr fun n => by split_ifs <;> ring
    rw [← abs_neg, hneg, abs_of_nonneg (tsum_nonneg fun n => by
      split_ifs
      · exact (hf_le n).1
      · exact le_rfl)]
  rw [hneg_tsum]
  have hsumm_sq : Summable (fun n : ℕ => if ⌊x⌋₊ < n then ((n : ℝ)⁻¹) ^ 2 else 0) := by
    have hnat : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
      refine (Real.summable_nat_rpow_inv.mpr one_lt_two).congr fun n => ?_
      rw [show (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ (2 : ℕ) by norm_cast, inv_pow]
    refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> [exact le_rfl; positivity]) hnat
  have hsumm_neg : Summable (fun n : ℕ => if ⌊x⌋₊ < n then -f n else 0) := by
    refine Summable.of_nonneg_of_le (fun n => by split_ifs; exact (hf_le n).1; exact le_rfl)
      (fun n => by
        split_ifs
        · exact (hf_le n).2.trans (by split_ifs <;> [exact le_rfl; positivity])
        · exact le_rfl) hsumm_sq
  have hfl_ge1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hfl_ge_half : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
    have hlt := Nat.lt_floor_add_one x
    have h2 : (2 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor (by exact_mod_cast hx : (2 : ℕ) ≤ x)
    linarith
  calc ∑' n : ℕ, (if ⌊x⌋₊ < n then -f n else 0)
      ≤ ∑' n : ℕ, (if ⌊x⌋₊ < n then ((n : ℝ)⁻¹) ^ 2 else 0) := by
        refine hsumm_neg.tsum_le_tsum (fun n => ?_) hsumm_sq
        split_ifs
        · exact (hf_le n).2.trans (by split_ifs <;> [exact le_rfl; positivity])
        · exact le_rfl
    _ ≤ (⌊x⌋₊ : ℝ)⁻¹ := tsum_inv_sq_tail_le hfl_ge1
    _ ≤ (x / 2)⁻¹ := inv_anti₀ (by linarith) hfl_ge_half
    _ = 2 / x := by field_simp

/-- Elementary exponential-Lipschitz bound: `|exp u - 1| ≤ |u| * exp |u|` for all `u : ℝ`. -/
private lemma abs_exp_sub_one_le_mul_exp_abs (u : ℝ) :
    |Real.exp u - 1| ≤ |u| * Real.exp |u| := by
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hu))]
    -- `exp u - 1 ≤ u * exp u` since `1 - u ≤ exp (-u)`
    have h := Real.add_one_le_exp (-u)
    rw [Real.exp_neg] at h
    have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos u).le
    rw [inv_mul_cancel₀ (Real.exp_pos u).ne'] at hmul
    linarith
  · push Not at hu
    rw [abs_of_neg hu, abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hu.le))]
    have h := Real.add_one_le_exp u
    have h1 : 1 - Real.exp u ≤ -u := by linarith
    have h2 : (1 : ℝ) ≤ Real.exp (-u) := Real.one_le_exp (by linarith)
    nlinarith

/-- **QUANTITATIVE MERTENS' THIRD THEOREM WITH EXACT `e^{-γ}` CONSTANT (0 ASSUMPTIONS!)**:
`∃ C > 0, ∀ x ≥ 3, |Real.log x * ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 - (p : ℝ)⁻¹) - Real.exp (-Real.eulerMascheroniConstant)| ≤ C / Real.log x`. -/
theorem mertens_third_theorem_quant :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      |Real.log x * ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 - (p : ℝ)⁻¹) -
          Real.exp (-Real.eulerMascheroniConstant)| ≤ C / Real.log x := by
  obtain ⟨C₂, hC₂, hM2⟩ := mertens_second_theorem
  set K : ℝ := C₂ + 2 with hK_def
  have hK_pos : 0 < K := by positivity
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set C₃ : ℝ := Real.exp (-Real.eulerMascheroniConstant) * Real.exp (K / Real.log 3) * K
  have hC₃_pos : 0 < C₃ := by positivity
  refine ⟨C₃, hC₃_pos, fun x hx3 => ?_⟩
  have hx0 : 0 < x := by linarith
  have hLx_ge : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3
  have hLx_pos : 0 < Real.log x := hlog3_pos.trans_le hLx_ge
  have hprod_pos : 0 < mertensProd x := mertensProd_pos x
  -- Logarithm identity: `log (log x * mertensProd x) + γ = -(mertensSum2 x - (log (log x) + M)) + (S_tail x - B_tail)`
  have hlog_prod : Real.log (mertensProd x) =
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (1 - (p : ℝ)⁻¹) := by
    unfold mertensProd
    rw [Real.log_prod]
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
    linarith
  set u : ℝ := Real.log (Real.log x * mertensProd x) + Real.eulerMascheroniConstant with hu_def
  have hu_eq : u =
      -(mertensSum2 x - (Real.log (Real.log x) + meisselMertensConst)) +
      (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) -
        ∑' p : Nat.Primes, (Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹)) := by
    dsimp only [u]
    rw [Real.log_mul hLx_pos.ne' hprod_pos.ne', hlog_prod,
      meisselMertensConst_eq_eulerMascheroni_add_tsum]
    have hsplit : ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) =
        (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (1 - (p : ℝ)⁻¹)) + mertensSum2 x := by
      unfold mertensSum2; rw [Finset.sum_add_distrib]
    linarith
  have hu_bd : |u| ≤ K / Real.log x := by
    rw [hu_eq]
    have h1 : |-(mertensSum2 x - (Real.log (Real.log x) + meisselMertensConst))| ≤ C₂ / Real.log x := by
      rw [abs_neg]; exact hM2 x hx3
    have h2 : |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) -
        ∑' p : Nat.Primes, (Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹)| ≤ 2 / Real.log x := by
      have hlog_le_x : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
      exact (abs_prime_log_tail_sub_le (by linarith)).trans
        (div_le_div_of_nonneg_left (by norm_num) hLx_pos hlog_le_x)
    have htri := abs_add_le
      (-(mertensSum2 x - (Real.log (Real.log x) + meisselMertensConst)))
      (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) -
        ∑' p : Nat.Primes, (Real.log (1 - (p.1 : ℝ)⁻¹) + (p.1 : ℝ)⁻¹))
    dsimp only [K]
    linarith [show (C₂ + 2) / Real.log x = C₂ / Real.log x + 2 / Real.log x by ring]
  have hu_le_3 : |u| ≤ K / Real.log 3 :=
    hu_bd.trans (div_le_div_of_nonneg_left hK_pos.le hlog3_pos hLx_ge)
  have hprod_eq : Real.log x * mertensProd x = Real.exp (-Real.eulerMascheroniConstant) * Real.exp u := by
    rw [← Real.exp_add, hu_def, show -Real.eulerMascheroniConstant +
      (Real.log (Real.log x * mertensProd x) + Real.eulerMascheroniConstant) =
      Real.log (Real.log x * mertensProd x) by ring,
      Real.exp_log (mul_pos hLx_pos hprod_pos)]
  change |Real.log x * mertensProd x - Real.exp (-Real.eulerMascheroniConstant)| ≤ _
  rw [hprod_eq, show Real.exp (-Real.eulerMascheroniConstant) * Real.exp u -
      Real.exp (-Real.eulerMascheroniConstant) =
      Real.exp (-Real.eulerMascheroniConstant) * (Real.exp u - 1) by ring,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-Real.eulerMascheroniConstant) * |Real.exp u - 1|
      ≤ Real.exp (-Real.eulerMascheroniConstant) * (|u| * Real.exp |u|) :=
        mul_le_mul_of_nonneg_left (abs_exp_sub_one_le_mul_exp_abs u) (Real.exp_pos _).le
    _ ≤ Real.exp (-Real.eulerMascheroniConstant) * ((K / Real.log x) * Real.exp (K / Real.log 3)) := by
        gcongr
    _ = C₃ / Real.log x := by dsimp only [C₃]; ring

/-- **MERTENS' THIRD THEOREM WITH THE EXACT `e^{-γ}` CONSTANT (UNCONDITIONAL, 0 ASSUMPTIONS!)**:
`Tendsto (fun x : ℝ => Real.log x * ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)))`. -/
theorem mertens_third_theorem :
    Tendsto (fun x : ℝ => Real.log x * ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 - (p : ℝ)⁻¹))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  obtain ⟨C, hC, hquant⟩ := mertens_third_theorem_quant
  rw [← tendsto_sub_nhds_zero_iff]
  have hbound : Tendsto (fun x : ℝ => C / Real.log x) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul C
    rw [mul_zero] at h
    exact h.congr fun x => by dsimp only [Function.comp_apply]; ring
  refine squeeze_zero_norm' (a := fun x : ℝ => C / Real.log x) ?_ hbound
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx3
  rw [Real.norm_eq_abs]
  exact hquant x hx3

/-! ## Section 6: Mertens' Theorems in Arithmetic Progressions (First & Second) -/

private lemma realStepSum_primeLogAP_eq_thetaAP (q a : ℕ) (t : ℝ) :
    realStepSum (fun n : ℕ => if n.Prime ∧ n ≡ a [MOD q] then Real.log (n : ℝ) else 0) t =
      Stage2DirichletAP.chebyshevThetaAP q a t := by
  unfold realStepSum Stage2DirichletAP.chebyshevThetaAP
  have hset : Finset.range (⌊t⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊t⌋₊) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hset, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 ⌊t⌋₊)]
  simp

/-- **MERTENS' FIRST THEOREM IN ARITHMETIC PROGRESSIONS (UNCONDITIONAL, 0 ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `a : ℕ` with `Nat.Coprime a q`:
`∃ C > 0, ∀ x ≥ 2, |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]), Real.log p / p - (1 / φ(q)) * Real.log x| ≤ C`. -/
theorem mertens_first_theorem_AP {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]),
          Real.log (p : ℝ) / (p : ℝ) -
        (1 / (q.totient : ℝ)) * Real.log x| ≤ C := by
  obtain ⟨c, hc, C_θ, hC_θ, hthAP⟩ := Stage7PNTInAP.effective_pnt_thetaAP hcop
  set δ : ℝ := 1 / (q.totient : ℝ) with hδ_def
  have hδ_pos : 0 < δ := by
    have : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
    positivity
  -- Show `(chebyshevThetaAP q a t - δ * t) / t^2` is integrable on `Ioi 1`
  have hmeas_th : Measurable (Stage2DirichletAP.chebyshevThetaAP q a) := by
    have h : Stage2DirichletAP.chebyshevThetaAP q a =
        (fun k : ℕ => ∑ n ∈ Finset.range (k + 1),
          if n.Prime ∧ n ≡ a [MOD q] then Real.log (n : ℝ) else 0) ∘ Nat.floor := rfl
    rw [h]; exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
  have hthAP_mono : ∀ {u v : ℝ}, u ≤ v →
      Stage2DirichletAP.chebyshevThetaAP q a u ≤ Stage2DirichletAP.chebyshevThetaAP q a v := by
    intro u v huv
    unfold Stage2DirichletAP.chebyshevThetaAP
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.add_le_add_right (Nat.floor_mono huv) 1))
      fun n _ _ => by split_ifs <;> [exact Real.log_natCast_nonneg n; exact le_rfl]
  have hint_err : IntegrableOn
      (fun t : ℝ => (Stage2DirichletAP.chebyshevThetaAP q a t - δ * t) / t ^ 2) (Ioi (1 : ℝ)) := by
    have hmeas : Measurable (fun t : ℝ => (Stage2DirichletAP.chebyshevThetaAP q a t - δ * t) / t ^ 2) :=
      (hmeas_th.sub (measurable_const.mul measurable_id)).div (continuous_pow 2).measurable
    have h12 : IntegrableOn
        (fun t : ℝ => (Stage2DirichletAP.chebyshevThetaAP q a t - δ * t) / t ^ 2) (Ioc (1 : ℝ) 2) := by
      refine Integrable.mono'
        (integrableOn_const (C := Stage2DirichletAP.chebyshevThetaAP q a 2 + 2 * δ)
          (hs := measure_Ioc_lt_top.ne))
        hmeas.aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
      have htsq : 1 ≤ t ^ 2 := by nlinarith [ht.1]
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
      refine (div_le_self (abs_nonneg _) htsq).trans ?_
      have h0 := Stage2DirichletAP.chebyshevThetaAP_nonneg q a t
      have hm := hthAP_mono ht.2
      have hδt_nn : 0 ≤ δ * t := mul_nonneg hδ_pos.le (by linarith [ht.1])
      have hδt : δ * t ≤ 2 * δ := by nlinarith [ht.2]
      rcases abs_cases (Stage2DirichletAP.chebyshevThetaAP q a t - δ * t) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    have h2inf : IntegrableOn
        (fun t : ℝ => (Stage2DirichletAP.chebyshevThetaAP q a t - δ * t) / t ^ 2) (Ioi (2 : ℝ)) := by
      have hdom := (integrableOn_exp_neg_rpow_log_div_id hc (by norm_num : (0 : ℝ) < 1 / 20)).const_mul C_θ
      refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht2 : 2 ≤ t := (Set.mem_Ioi.mp ht).le
      have ht0 : 0 < t := by linarith
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
      have hbd := hthAP t ht2
      have hδt_eq : t / (q.totient : ℝ) = δ * t := by dsimp only [δ]; ring
      rw [hδt_eq] at hbd
      calc |Stage2DirichletAP.chebyshevThetaAP q a t - δ * t| / t ^ 2
          ≤ (C_θ * t * Real.exp (-c * (Real.log t) ^ (1 / 20 : ℝ))) / t ^ 2 :=
            div_le_div_of_nonneg_right hbd (sq_nonneg t)
        _ = C_θ * (Real.exp (-c * (Real.log t) ^ (1 / 20 : ℝ)) / t) := by
            field_simp [ht0.ne']
    have hunion : Ioi (1 : ℝ) = Ioc (1 : ℝ) 2 ∪ Ioi (2 : ℝ) :=
      (Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 2)).symm
    rw [hunion]
    exact h12.union h2inf
  set I_abs : ℝ := ∫ t in Ioi (1 : ℝ), |(Stage2DirichletAP.chebyshevThetaAP q a t - δ * t) / t ^ 2|
  have hI_nn : 0 ≤ I_abs := setIntegral_nonneg measurableSet_Ioi fun _ _ => abs_nonneg _
  refine ⟨C_θ + δ + I_abs, by positivity, fun x hx2 => ?_⟩
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  -- Apply `abel_summation_real` with `φ(t) = t⁻¹`
  have hd : ∀ t ∈ Set.Icc (1 : ℝ) x, HasDerivAt (fun u : ℝ => u⁻¹) (-(t ^ 2)⁻¹) t := fun t ht =>
    hasDerivAt_inv (zero_lt_one.trans_le ht.1).ne'
  have hc_φ' : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc (1 : ℝ) x) :=
    (ContinuousOn.inv₀ (continuousOn_pow 2) fun t ht =>
      pow_ne_zero 2 (zero_lt_one.trans_le ht.1).ne').neg
  have hab := abel_summation_real
    (fun n : ℕ => if n.Prime ∧ n ≡ a [MOD q] then Real.log (n : ℝ) else 0) hx1 hd hc_φ'
  have hLHS : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (if n.Prime ∧ n ≡ a [MOD q] then Real.log (n : ℝ) else 0) * (n : ℝ)⁻¹ =
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]),
        Real.log (p : ℝ) / (p : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => by split_ifs <;> simp [div_eq_mul_inv]
  rw [hLHS, realStepSum_primeLogAP_eq_thetaAP] at hab
  have hint_rew : ∫ t in (1 : ℝ)..x,
        realStepSum (fun n : ℕ => if n.Prime ∧ n ≡ a [MOD q] then Real.log (n : ℝ) else 0) t * -(t ^ 2)⁻¹ =
      -(∫ t in (1 : ℝ)..x, Stage2DirichletAP.chebyshevThetaAP q a t / t ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [realStepSum_primeLogAP_eq_thetaAP]; ring
  rw [hint_rew, sub_neg_eq_add] at hab
  have hint_log : ∫ t in (1 : ℝ)..x, δ / t = δ * Real.log x := by
    rw [show (fun t : ℝ => δ / t) = fun t => δ * t⁻¹ by funext t; ring,
      intervalIntegral.integral_const_mul]
    simpa [Real.log_one] using congrArg (δ * ·) (integral_inv_of_pos zero_lt_one hx0)
  have hth_int : IntervalIntegrable (fun t : ℝ => Stage2DirichletAP.chebyshevThetaAP q a t / t ^ 2)
      volume (1 : ℝ) x := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hx1).mpr ?_
    refine Integrable.mono'
      (integrableOn_const (C := Stage2DirichletAP.chebyshevThetaAP q a x) (hs := measure_Ioc_lt_top.ne))
      (hmeas_th.div (continuous_pow 2).measurable).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    have htsq : 1 ≤ t ^ 2 := by nlinarith [ht.1]
    rw [Real.norm_of_nonneg (div_nonneg (Stage2DirichletAP.chebyshevThetaAP_nonneg q a t) (sq_nonneg t))]
    exact (div_le_self (Stage2DirichletAP.chebyshevThetaAP_nonneg q a t) htsq).trans (hthAP_mono ht.2)
  have hinv_int : IntervalIntegrable (fun t : ℝ => δ / t) volume (1 : ℝ) x := by
    have hc1 : ContinuousOn (fun t : ℝ => δ / t) (Set.uIcc 1 x) := by
      rw [Set.uIcc_of_le hx1]
      exact continuousOn_const.div continuousOn_id fun t ht => (zero_lt_one.trans_le ht.1).ne'
    exact hc1.intervalIntegrable
  have hpt : Set.EqOn (fun t : ℝ => (Stage2DirichletAP.chebyshevThetaAP q a t - δ * t) / t ^ 2)
      (fun t : ℝ => Stage2DirichletAP.chebyshevThetaAP q a t / t ^ 2 - δ / t) (Set.uIcc 1 x) := by
    rw [Set.uIcc_of_le hx1]
    intro t ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht.1).ne'
    dsimp only; field_simp
  have hdiff : ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]),
        Real.log (p : ℝ) / (p : ℝ) - δ * Real.log x =
      (Stage2DirichletAP.chebyshevThetaAP q a x - δ * x) / x + δ +
      ∫ t in (1 : ℝ)..x, (Stage2DirichletAP.chebyshevThetaAP q a t - δ * t) / t ^ 2 := by
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub hth_int hinv_int,
      hint_log, hab]
    field_simp [hx0.ne']
    ring
  rw [hdiff]
  have hterm1 : |(Stage2DirichletAP.chebyshevThetaAP q a x - δ * x) / x| ≤ C_θ := by
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    have hbd := hthAP x hx2
    have hδx : x / (q.totient : ℝ) = δ * x := by dsimp only [δ]; ring
    rw [hδx] at hbd
    have hexp_le1 : Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have := Real.rpow_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ x)) (1 / 20 : ℝ)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hexp_le1 (show 0 ≤ C_θ * x by positivity)]
  have hterm2 : |∫ t in (1 : ℝ)..x, (Stage2DirichletAP.chebyshevThetaAP q a t - δ * t) / t ^ 2| ≤ I_abs := by
    rw [intervalIntegral.integral_of_le hx1]
    calc |∫ t in Ioc (1 : ℝ) x, (Stage2DirichletAP.chebyshevThetaAP q a t - δ * t) / t ^ 2|
        ≤ ∫ t in Ioc (1 : ℝ) x, |(Stage2DirichletAP.chebyshevThetaAP q a t - δ * t) / t ^ 2| :=
          abs_integral_le_integral_abs
      _ ≤ I_abs := by
          refine setIntegral_mono_set hint_err.abs ?_ (Eventually.of_forall Ioc_subset_Ioi_self)
          exact ae_restrict_of_forall_mem measurableSet_Ioi fun _ _ => abs_nonneg _
  have htri1 := abs_add_le ((Stage2DirichletAP.chebyshevThetaAP q a x - δ * x) / x + δ)
    (∫ t in (1 : ℝ)..x, (Stage2DirichletAP.chebyshevThetaAP q a t - δ * t) / t ^ 2)
  have htri2 := abs_add_le ((Stage2DirichletAP.chebyshevThetaAP q a x - δ * x) / x) δ
  rw [abs_of_pos hδ_pos] at htri2
  linarith

/-- **MERTENS' SECOND THEOREM IN ARITHMETIC PROGRESSIONS (UNCONDITIONAL, 0 ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `a : ℕ` with `Nat.Coprime a q`:
`∃ M_qa : ℝ, ∃ C > 0, ∀ x ≥ 3, |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]), (p : ℝ)⁻¹ - ((1 / (q.totient : ℝ)) * Real.log (Real.log x) + M_qa)| ≤ C / Real.log x`. -/
theorem mertens_second_theorem_AP {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    ∃ M_qa : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]), (p : ℝ)⁻¹ -
        ((1 / (q.totient : ℝ)) * Real.log (Real.log x) + M_qa)| ≤ C / Real.log x := by
  obtain ⟨C₀, hC₀, hM1AP⟩ := mertens_first_theorem_AP hcop
  set f : ℕ → ℝ := fun n => if n.Prime ∧ n ≡ a [MOD q] then Real.log (n : ℝ) / (n : ℝ) else 0
  have hf1 : f 1 = 0 := by simp [f]
  have hstep_eq : ∀ t : ℝ, realStepSum f t =
      ∑ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]),
        Real.log (p : ℝ) / (p : ℝ) := fun t => by
    unfold realStepSum; rw [← Finset.sum_filter]
  have hbd : ∀ t : ℝ, 2 ≤ t → |realStepSum f t - (1 / (q.totient : ℝ)) * Real.log t| ≤ C₀ := by
    intro t ht; rw [hstep_eq t]; exact hM1AP t ht
  set M_qa : ℝ := (1 / (q.totient : ℝ)) * (1 - Real.log (Real.log 2)) +
    ∫ t in Ioi (2 : ℝ), (realStepSum f t - (1 / (q.totient : ℝ)) * Real.log t) / (t * (Real.log t) ^ 2)
  have hab := (reciprocal_sum_asymp_of_log_weighted_bound f hf1 hC₀ hbd).2
  refine ⟨M_qa, 2 * C₀, by positivity, fun x hx3 => ?_⟩
  have hx2 : 2 ≤ x := by linarith
  have hsum_eq : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, f n / Real.log (n : ℝ) =
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]), (p : ℝ)⁻¹ := by
    rw [Finset.sum_filter]
    have hIcc : Finset.Icc 1 ⌊x⌋₊ = insert 1 (Finset.Icc 2 ⌊x⌋₊) := by
      have hfl2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx2)
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp : (1 : ℕ) ∉ Finset.Icc 2 ⌊x⌋₊),
      if_neg (fun h => Nat.not_prime_one h.1), zero_add]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only [f]
    split_ifs with h
    · have hlog_ne : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast h.1.one_lt)).ne'
      field_simp [hlog_ne]
    · simp
  have hres := hab x hx2
  rw [hsum_eq] at hres
  exact hres

end RHDirect.Stage8MertensTheorems

