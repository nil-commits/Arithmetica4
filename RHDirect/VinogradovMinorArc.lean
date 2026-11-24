import RHDirect.VinogradovParseval
import RHDirect.VinogradovSingularSeriesBound

/-!
# Vinogradov — Wave 3: minor-arc L³ estimate (sup × L²) and real Parseval

The minor-arc contribution is controlled by
`‖∫_𝔪 S(α)³ e(-nα)‖ ≤ (sup_𝔪 ‖S‖) · ∫₀¹ ‖S‖²`,
and Parseval gives `∫₀¹ ‖S‖² = ∑_{p≤N} (log p)²`. Combined with the Vinogradov
minor-arc `L^∞` bound `sup_𝔪‖S‖ ≪ N/(log N)^A` (the remaining deep analytic input),
this makes the minor-arc integral `o(n²)`. No `sorry`, no custom axioms.
-/

open Real Complex Finset MeasureTheory intervalIntegral

namespace RHDirect.Vinogradov

noncomputable section

/-- Real-valued Parseval: `∫₀¹ ‖S_N(α)‖² = ∑_{p≤N} (log p)²`. -/
theorem parseval_S_real (N : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖S N α‖ ^ 2 = ∑ p ∈ primesUpTo N, (Real.log (p : ℝ)) ^ 2 := by
  have hc : (∫ α in (0 : ℝ)..1, (‖S N α‖ ^ 2 : ℝ) : ℂ) =
      ∫ α in (0 : ℝ)..1, S N α * star (S N α) := by
    refine intervalIntegral.integral_congr (fun α _ => ?_)
    have h : S N α * star (S N α) = (↑(‖S N α‖ ^ 2) : ℂ) := by
      rw [mul_comm, Complex.star_def, Complex.conj_mul']
      push_cast
      rfl
    exact h.symm
  have hcast : (↑(∫ α in (0 : ℝ)..1, ‖S N α‖ ^ 2) : ℂ) =
      (↑(∑ p ∈ primesUpTo N, (Real.log (p : ℝ)) ^ 2) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal, hc, parseval_S]
    push_cast
    rfl
  exact_mod_cast hcast

/-- The integrand norm on the minor arc: `‖S³ e(-nα)‖ = ‖S‖³`. -/
theorem norm_integrand (N n : ℕ) (α : ℝ) :
    ‖(S N α) ^ 3 * e (-(n : ℝ) * α)‖ = ‖S N α‖ ^ 3 := by
  simp only [norm_mul, norm_pow, norm_e, mul_one]

/-- Pointwise minor-arc bound: `‖S‖³ ≤ M · ‖S‖²` when `‖S‖ ≤ M`. -/
theorem cube_le_sup_mul_sq {s M : ℝ} (hs : 0 ≤ s) (hM : s ≤ M) :
    s ^ 3 ≤ M * s ^ 2 := by
  have hsq : 0 ≤ s ^ 2 := pow_nonneg hs 2
  calc s ^ 3 = s * s ^ 2 := by ring
    _ ≤ M * s ^ 2 := mul_le_mul_of_nonneg_right hM hsq

/-- The minor-arc `L³` estimate: `‖∫_𝔪 S³ e(-nα)‖ ≤ (sup_𝔪‖S‖) · ∑_{p≤N}(log p)²`.
This is the `L³ ≤ sup × L²` step combined with Parseval; the remaining deep input is
the Vinogradov minor-arc `L^∞` bound on `sup_𝔪‖S‖`. -/
theorem minor_arc_L3_bound (N n : ℕ) (m : Set ℝ) (M : ℝ)
    (hmeas : MeasurableSet m) (hm : m ⊆ Set.Icc (0 : ℝ) 1) (hM0 : 0 ≤ M)
    (hM : ∀ α ∈ m, ‖S N α‖ ≤ M) :
    ‖∫ α in m, (S N α) ^ 3 * e (-(n : ℝ) * α)‖ ≤
      M * ∑ p ∈ primesUpTo N, (Real.log (p : ℝ)) ^ 2 := by
  have hScont : Continuous (S N) := by fun_prop [S]
  have hIcc2 : IntegrableOn (fun α => ‖S N α‖ ^ 2) (Set.Icc (0 : ℝ) 1) := by
    apply Continuous.integrableOn_Icc
    fun_prop
  have hm2 : IntegrableOn (fun α => ‖S N α‖ ^ 2) m := hIcc2.mono hm le_rfl
  have hmM2 : IntegrableOn (fun α => M * ‖S N α‖ ^ 2) m := hm2.const_mul M
  have hmf : IntegrableOn (fun α => (S N α) ^ 3 * e (-(n : ℝ) * α)) m := by
    have : Continuous (fun α => (S N α) ^ 3 * e (-(n : ℝ) * α)) := by fun_prop
    exact (this.integrableOn_Icc (a := 0) (b := 1)).mono hm le_rfl
  have hm3 : IntegrableOn (fun α => ‖S N α‖ ^ 3) m := by
    have : Continuous (fun α => ‖S N α‖ ^ 3) := by fun_prop
    exact (this.integrableOn_Icc (a := 0) (b := 1)).mono hm le_rfl
  calc ‖∫ α in m, (S N α) ^ 3 * e (-(n : ℝ) * α)‖
      ≤ ∫ α in m, ‖(S N α) ^ 3 * e (-(n : ℝ) * α)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ α in m, ‖S N α‖ ^ 3 := by
        apply setIntegral_congr_fun hmeas
        intro α ha
        exact norm_integrand N n α
    _ ≤ ∫ α in m, M * ‖S N α‖ ^ 2 :=
        MeasureTheory.integral_mono_ae hm3 hmM2
          ((ae_restrict_mem (μ := volume) hmeas).mono
            (fun α ha => cube_le_sup_mul_sq (norm_nonneg _) (hM α ha)))
    _ = M * ∫ α in m, ‖S N α‖ ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ M * ∫ α in Set.Icc (0 : ℝ) 1, ‖S N α‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hM0
        exact setIntegral_mono_set hIcc2
          (Filter.Eventually.of_forall fun α => sq_nonneg (‖S N α‖))
          (Filter.Eventually.of_forall hm)
    _ = M * ∫ α in (0 : ℝ)..1, ‖S N α‖ ^ 2 := by
        congr 1
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    _ = M * ∑ p ∈ primesUpTo N, (Real.log (p : ℝ)) ^ 2 := by
        rw [parseval_S_real]

end

#print axioms RHDirect.Vinogradov.parseval_S_real
#print axioms RHDirect.Vinogradov.minor_arc_L3_bound

end RHDirect.Vinogradov
