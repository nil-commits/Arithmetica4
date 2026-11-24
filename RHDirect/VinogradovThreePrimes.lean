import RHDirect.VinogradovMajorArcEval
import RHDirect.VinogradovMinorArcBound
import RHDirect.VinogradovAssembly

/-!
# Vinogradov's Three-Primes Theorem (1937) — 100% Unconditional on Native Mathlib `Nat.Prime`

Every sufficiently large odd natural number is a sum of three primes:
```lean
theorem vinogradov_three_primes_unconditional :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Odd n →
      ∃ p₁ p₂ p₃ : ℕ, Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ Nat.Prime p₃ ∧ p₁ + p₂ + p₃ = n
```

## Proof Assembly
1. **Minor-Arc `L^∞` Bound (`VinogradovMinorArcBound.vinogradov_minor_arc_sup_bound`):**
   With `A = 3`, obtains `B ≥ 1` and `C > 0` such that on `minorArcs n ((log n)^B)`,
   `‖S n α‖ ≤ C * n / (log n)^3`.
2. **Minor-Arc `L³` Integral Bound (`VinogradovMinorArc.minor_arc_L3_bound`):**
   Combines the `L^∞` bound with Parseval (`∑_{p ≤ n} (log p)² ≤ n * (log n)²`) to yield
   `‖∫_{minorArcs n Q} (S n α)³ e(-n α)‖ ≤ C * n² / log n = o(n²)`.
3. **Major-Arc Asymptotic Lower Bound (`VinogradovMajorArcEval.major_arc_integral_lower_bound`):**
   At the same cutoff `Q = (log n)^B`, proves unconditionally via Siegel–Walfisz (`0` exceptions),
   exact singular integral evaluation, and truncated singular-series Euler product bounds that
   `(1 / 4) * (2 * (2 - π² / 6)) * n² ≤ (∫_{majorArcs n Q} (S n α)³ e(-n α)).re`
   for all sufficiently large odd `n`.
4. **Circle-Method Assembly (`VinogradovAssembly.vinogradov_assembly`):**
   Splits `∫₀¹ = ∫_{majorArcs} + ∫_{minorArcs}` and extracts `p₁ + p₂ + p₃ = n` with all `pᵢ` prime.

Native Mathlib objects throughout; zero `sorry`, zero custom axioms.
-/

open Real Complex Finset MeasureTheory intervalIntegral Filter Topology

namespace RHDirect.Vinogradov

noncomputable section

/-- Exact definitional compatibility between `minorArcs` and `majorArcs`. -/
theorem minorArcs_eq_diff (N : ℕ) (Q : ℝ) :
    minorArcs N Q = Set.Icc (0 : ℝ) 1 \ majorArcs N Q := rfl

/-- Measurability of `minorArcs N Q`. -/
theorem measurableSet_minorArcs (N : ℕ) (Q : ℝ) :
    MeasurableSet (minorArcs N Q) :=
  measurableSet_Icc.diff (measurableSet_majorArcs N Q)

/-- Elementary `L²` prime-log upper bound: `∑_{p ≤ n} (log p)² ≤ n * (log n)²`. -/
theorem sum_log_sq_primesUpTo_le (n : ℕ) :
    ∑ p ∈ primesUpTo n, (Real.log (p : ℝ)) ^ 2 ≤ (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  have hsub : primesUpTo n ⊆ Finset.Icc 1 n := by
    intro p hp
    have hlt : p < n + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    have hprime : p.Prime := (Finset.mem_filter.mp hp).2
    exact Finset.mem_Icc.mpr ⟨hprime.pos, Nat.lt_succ_iff.mp hlt⟩
  have hcard : ((primesUpTo n).card : ℝ) ≤ (n : ℝ) := by
    have h := Finset.card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at h
    exact_mod_cast h
  calc ∑ p ∈ primesUpTo n, (Real.log (p : ℝ)) ^ 2
      ≤ ∑ _p ∈ primesUpTo n, (Real.log (n : ℝ)) ^ 2 := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hprime : p.Prime := (Finset.mem_filter.mp hp).2
        have hp_le : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
        have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
        have hlog_le : Real.log (p : ℝ) ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hp_le)
        exact pow_le_pow_left₀ hlog_nn hlog_le 2
    _ = ((primesUpTo n).card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) * (Real.log (n : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard (sq_nonneg _)

/-- Exact decomposition of the circle integral into major arcs plus minor arcs. -/
theorem integral_circle_eq_major_add_minor (N n : ℕ) (Q : ℝ) :
    (∫ α in (0 : ℝ)..1, (S N α) ^ 3 * e (-(n : ℝ) * α)) =
      (∫ α in majorArcs N Q, (S N α) ^ 3 * e (-(n : ℝ) * α)) +
      (∫ α in minorArcs N Q, (S N α) ^ 3 * e (-(n : ℝ) * α)) := by
  have hcont : Continuous (fun α : ℝ => (S N α) ^ 3 * e (-(n : ℝ) * α)) := by
    have : Continuous (S N) := by unfold S; fun_prop
    fun_prop
  have hIcc : IntegrableOn (fun α : ℝ => (S N α) ^ 3 * e (-(n : ℝ) * α)) (Set.Icc (0 : ℝ) 1) :=
    hcont.integrableOn_Icc
  have hsub_maj : majorArcs N Q ⊆ Set.Icc (0 : ℝ) 1 := Set.inter_subset_left
  have hsub_min : minorArcs N Q ⊆ Set.Icc (0 : ℝ) 1 := Set.sdiff_subset
  have hunion : majorArcs N Q ∪ minorArcs N Q = Set.Icc (0 : ℝ) 1 :=
    Set.union_sdiff_cancel hsub_maj
  have hdisj : Disjoint (majorArcs N Q) (minorArcs N Q) := disjoint_sdiff_self_right
  calc (∫ α in (0 : ℝ)..1, (S N α) ^ 3 * e (-(n : ℝ) * α))
      = ∫ α in Set.Icc (0 : ℝ) 1, (S N α) ^ 3 * e (-(n : ℝ) * α) := by
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ = ∫ α in majorArcs N Q ∪ minorArcs N Q, (S N α) ^ 3 * e (-(n : ℝ) * α) := by
        rw [hunion]
    _ = (∫ α in majorArcs N Q, (S N α) ^ 3 * e (-(n : ℝ) * α)) +
        (∫ α in minorArcs N Q, (S N α) ^ 3 * e (-(n : ℝ) * α)) :=
        MeasureTheory.setIntegral_union hdisj (measurableSet_minorArcs N Q)
          (hIcc.mono_set hsub_maj) (hIcc.mono_set hsub_min)

/-- **VINOGRADOV'S THREE-PRIMES THEOREM (1937) — 100% UNCONDITIONAL**:
every sufficiently large odd natural number is the sum of three primes. -/
theorem vinogradov_three_primes_unconditional :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Odd n →
      ∃ p₁ p₂ p₃ : ℕ, Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ Nat.Prime p₃ ∧ p₁ + p₂ + p₃ = n := by
  -- Step 1: Minor-arc `L^∞` bound at `A = 3` yields cutoff exponent `B ≥ 1` and constant `C > 0`
  obtain ⟨B, C_min, hB1, hCmin_pos, hminor_sup⟩ :=
    vinogradov_minor_arc_sup_bound 3 (by norm_num : (0 : ℝ) ≤ 3)
  -- Step 2: Major-arc asymptotic lower bound at the exact same cutoff `Q = (log n)^B`
  obtain ⟨N_maj, hNmaj16, hmaj_lb⟩ := major_arc_integral_lower_bound B hB1
  set c_S : ℝ := 2 * (2 - Real.pi ^ 2 / 6)
  have hcS_pos : 0 < c_S := singular_series_constant_pos
  -- Step 3: Threshold `N₁` so that `C_min / log n < (1 / 4) * c_S` and `log n > 1`
  have hlog_large : ∀ᶠ x : ℝ in atTop, max 2 (4 * C_min / c_S + 1) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 2 (4 * C_min / c_S + 1)))
  rw [Filter.eventually_atTop] at hlog_large
  obtain ⟨X₁, hX₁⟩ := hlog_large
  refine ⟨max N_maj ⌈X₁⌉₊, fun n hn hodd => ?_⟩
  have hn_maj : N_maj ≤ n := (le_max_left _ _).trans hn
  have hn16 : 16 ≤ n := hNmaj16.trans hn_maj
  have hnX : X₁ ≤ (n : ℝ) := (Nat.le_ceil X₁).trans (by exact_mod_cast (le_max_right _ _).trans hn)
  have hlog_ge : max 2 (4 * C_min / c_S + 1) ≤ Real.log (n : ℝ) := hX₁ (n : ℝ) hnX
  have hlog2 : (2 : ℝ) ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hlog_ge
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  set Q : ℝ := (Real.log (n : ℝ)) ^ B
  -- Step 4: Major-arc lower bound
  set main : ℝ := (∫ α in majorArcs n Q, (S n α) ^ 3 * e (-(n : ℝ) * α)).re
  set error : ℝ := (∫ α in minorArcs n Q, (S n α) ^ 3 * e (-(n : ℝ) * α)).re
  have hmain_lb : (1 / 4 : ℝ) * c_S * (n : ℝ) ^ 2 ≤ main := hmaj_lb n hn_maj hodd
  have hmain_pos : 0 < main := lt_of_lt_of_le (by positivity) hmain_lb
  -- Step 5: Minor-arc `L³` upper bound `< (1 / 4) * c_S * n² ≤ main`
  set M_sup : ℝ := C_min * (n : ℝ) / (Real.log (n : ℝ)) ^ (3 : ℝ)
  have hM0 : 0 ≤ M_sup := by positivity
  have hmin_L3 : ‖∫ α in minorArcs n Q, (S n α) ^ 3 * e (-(n : ℝ) * α)‖ ≤
      M_sup * ∑ p ∈ primesUpTo n, (Real.log (p : ℝ)) ^ 2 :=
    minor_arc_L3_bound n n (minorArcs n Q) M_sup
      (measurableSet_minorArcs n Q) Set.sdiff_subset hM0 (hminor_sup n (by omega))
  have hparseval_le : ∑ p ∈ primesUpTo n, (Real.log (p : ℝ)) ^ 2 ≤ (n : ℝ) * (Real.log (n : ℝ)) ^ 2 :=
    sum_log_sq_primesUpTo_le n
  have hmin_bound : |error| < (1 / 4 : ℝ) * c_S * (n : ℝ) ^ 2 := by
    have hpow3 : (Real.log (n : ℝ)) ^ (3 : ℝ) = (Real.log (n : ℝ)) ^ (3 : ℕ) := by norm_cast
    have hprod : M_sup * ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) =
        (C_min / Real.log (n : ℝ)) * (n : ℝ) ^ 2 := by
      dsimp only [M_sup]
      rw [hpow3]
      field_simp [hlog_pos.ne']
    have hcoeff_lt : C_min / Real.log (n : ℝ) < (1 / 4 : ℝ) * c_S := by
      have hgt : 4 * C_min / c_S < Real.log (n : ℝ) :=
        lt_of_lt_of_le (by linarith) ((le_max_right _ _).trans hlog_ge)
      rw [div_lt_iff₀ hlog_pos]
      have hmul := mul_lt_mul_of_pos_left hgt hcS_pos
      rw [mul_div_cancel₀ _ hcS_pos.ne'] at hmul
      linarith
    calc |error|
        ≤ ‖∫ α in minorArcs n Q, (S n α) ^ 3 * e (-(n : ℝ) * α)‖ := Complex.abs_re_le_norm _
      _ ≤ M_sup * ∑ p ∈ primesUpTo n, (Real.log (p : ℝ)) ^ 2 := hmin_L3
      _ ≤ M_sup * ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hparseval_le hM0
      _ = (C_min / Real.log (n : ℝ)) * (n : ℝ) ^ 2 := hprod
      _ < (1 / 4 : ℝ) * c_S * (n : ℝ) ^ 2 :=
          mul_lt_mul_of_pos_right hcoeff_lt (pow_pos hn_pos 2)
  have herr_lt : |error| < main := lt_of_lt_of_le hmin_bound hmain_lb
  -- Step 6: Split `∫₀¹ = main + error` and invoke `vinogradov_assembly`
  have hintegral : (∫ α in (0 : ℝ)..1, (S n α) ^ 3 * e (-(n : ℝ) * α)).re = main + error := by
    rw [integral_circle_eq_major_add_minor n n Q, Complex.add_re]
  exact vinogradov_assembly main error hmain_pos herr_lt hintegral

end

#print axioms RHDirect.Vinogradov.minorArcs_eq_diff
#print axioms RHDirect.Vinogradov.integral_circle_eq_major_add_minor
#print axioms RHDirect.Vinogradov.vinogradov_three_primes_unconditional

end RHDirect.Vinogradov
