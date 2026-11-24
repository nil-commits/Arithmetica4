import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

/-!
# RHDirect.Stage9DiophantineWeyl

Unconditional formalization (0 `sorry`, 0 custom `axiom`s, 0 assumptions) of:

1. **Weyl's 1916 Equidistribution Criterion (`weyl_criterion_iff`)**:
   - Exact equivalence between equidistribution mod 1 (`IsEquidistributed`) and vanishing of all
     nonzero Weyl exponential sum averages `(1 / N) ∑_{n < N} exp(2π i k u(n)) → 0`, via
     trigonometric polynomial density on `AddCircle 1` (`span_fourier_closure_eq_top`) and
     continuous piecewise-linear trapezoid sandwiching.
2. **Weyl's Linear Rotation Theorem & Kronecker's Density Theorem**:
   - `weyl_equidistributed_linear_of_irrational` and `kronecker_density_irrational` /
     `kronecker_closure_eq_Icc` for every irrational `α`.
3. **van der Corput's Fundamental Difference Theorem & Weyl's Polynomial Equidistribution**:
   - `van_der_corput_inequality` and `van_der_corput_difference_theorem`, yielding
     `weyl_equidistributed_polynomial` and `weyl_equidistributed_quadratic` for every real
     polynomial of degree `d ≥ 1` with irrational leading coefficient.
4. **Dirichlet Simultaneous Approximation, Continued-Fraction Convergent Bounds, Hurwitz's
   Sharp `1 / √5` Theorem, Golden Ratio Optimality, & Liouville Transcendence**:
   - `dirichlet_approximation_simultaneous` via pigeonhole on `[0, 1)^d`.
   - Regular continued-fraction convergents `cfNum / cfDen` with determinant identity
     `P_{n+1} Q_n - P_n Q_{n+1} = (-1)^n`, coprimality, alternating error formula, and
     `|α - P_n / Q_n| < 1 / (Q_n Q_{n+1})`.
   - `hurwitz_three_consecutive_convergents` and `hurwitz_approximation_theorem`: infinitely
     many coprime `p / q` with `|α - p / q| < 1 / (√5 · q²)`.
   - `hurwitz_constant_optimal_goldenRatio`: for every `C > √5`, only finitely many `p / q`
     satisfy `|(1 + √5)/2 - p / q| < 1 / (C · q²)`.
   - `liouville_algebraic_approximation_bound` and `liouville_constant_transcendental`.
5. **Benford's First-Digit Law for Powers of 2 (`benford_law_pow_two`)**:
   - `irrational_log2_div_log10` and asymptotic density `log(1 + 1/d) / log 10` for every
     leading decimal digit `d ∈ {1, …, 9}` of `2^n`.
-/

namespace RHDirect.Stage9DiophantineWeyl

open scoped BigOperators Topology
open Filter MeasureTheory

/-!
## Section 1: Weyl's 1916 Equidistribution Criterion
-/

/-- A real sequence `u : ℕ → ℝ` is equidistributed modulo `1` if for every subinterval
`[a, b) ⊆ [0, 1]`, the asymptotic proportion of indices `n < N` with `Int.fract (u n) ∈ [a, b)`
converges to `b - a`. -/
def IsEquidistributed (u : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n => a ≤ Int.fract (u n) ∧ Int.fract (u n) < b)).card : ℝ) /
          (N : ℝ))
      atTop (nhds (b - a))

/-- The `k`-th additive character `e(k x) = exp(2π i k x)` on `ℝ`. -/
noncomputable def weylExp (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))

lemma weylExp_eq (k : ℤ) (x : ℝ) :
    weylExp k x = Complex.exp (2 * Real.pi * Complex.I * k * x) := rfl

lemma norm_weylExp (k : ℤ) (x : ℝ) : ‖weylExp k x‖ = 1 := by
  unfold weylExp
  have h : (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)) =
      ((2 * Real.pi * (k : ℝ) * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma weylExp_add (k : ℤ) (x y : ℝ) :
    weylExp k (x + y) = weylExp k x * weylExp k y := by
  unfold weylExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma weylExp_sub (k : ℤ) (x y : ℝ) :
    weylExp k (x - y) = weylExp k x * star (weylExp k y) := by
  unfold weylExp
  have hstar : star (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (y : ℂ))) =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (y : ℂ))) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal, map_ofNat]
  rw [hstar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma weylExp_int (k m : ℤ) : weylExp k (m : ℝ) = 1 := by
  unfold weylExp
  have h : 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((m : ℝ) : ℂ) =
      ((k * m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

lemma weylExp_fract (k : ℤ) (x : ℝ) : weylExp k (Int.fract x) = weylExp k x := by
  have hx : x = (⌊x⌋ : ℝ) + Int.fract x := by
    rw [Int.fract]; ring
  conv_rhs => rw [hx, weylExp_add, weylExp_int, one_mul]

lemma weylExp_zero_freq (x : ℝ) : weylExp 0 x = 1 := by
  simp [weylExp]

lemma fourier_one_coe_apply (k : ℤ) (x : ℝ) :
    (fourier (T := (1 : ℝ)) k) (x : AddCircle (1 : ℝ)) = weylExp k x := by
  rw [fourier_coe_apply]
  simp [weylExp]

lemma coe_addCircle_fract (x : ℝ) :
    ((Int.fract x : ℝ) : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) := by
  rw [QuotientAddGroup.eq]
  change -(Int.fract x) + x ∈ AddSubgroup.zmultiples (1 : ℝ)
  have h : -(Int.fract x) + x = (⌊x⌋ : ℤ) • (1 : ℝ) := by
    rw [Int.fract, zsmul_eq_mul, mul_one]; ring
  rw [h]
  exact AddSubgroup.zsmul_mem_zmultiples (1 : ℝ) ⌊x⌋

lemma integral_weylExp_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ t in (0 : ℝ)..1, weylExp k t = 0 := by
  have : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
  have hfc := fourierCoeff_eq_intervalIntegral (T := (1 : ℝ)) (f := ⇑(fourier (T := (1 : ℝ)) k)) 0 0
  have hfc0 : fourierCoeff (T := (1 : ℝ)) (⇑(fourier (T := (1 : ℝ)) k)) 0 = 0 := by
    rw [fourierCoeff_fourier, Pi.single_eq_of_ne (Ne.symm hk)]
  rw [hfc0] at hfc
  simp only [one_div, inv_one, one_smul, zero_add, neg_zero, fourier_zero, smul_eq_mul,
    one_mul] at hfc
  have heq : (fun x : ℝ => (fourier (T := (1 : ℝ)) k) (x : AddCircle (1 : ℝ))) =
      fun x : ℝ => weylExp k x := by
    funext x; exact fourier_one_coe_apply k x
  rw [heq] at hfc
  exact hfc.symm

/-- For any function continuous on `[0, 1]`, an equidistributed sequence satisfies the
Cesàro average limit `(1/N) ∑_{n < N} f (Int.fract (u n)) → ∫_0^1 f`. -/
theorem IsEquidistributed.tendsto_average_of_continuousOn {u : ℕ → ℝ} (hu : IsEquidistributed u)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, f (Int.fract (u n)))
      atTop (nhds (∫ t in (0 : ℝ)..1, f t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huc : UniformContinuousOn f (Set.Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδpos, hδ⟩ := huc (ε / 3) (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
  have hMpos : 0 < M := by
    by_contra hM0
    push Not at hM0
    have hM0' : M = 0 := Nat.le_zero.mp hM0
    subst hM0'
    have : (0 : ℝ) < 1 / δ := by positivity
    linarith
  have hMreal : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hMpos
  have h1Mltδ : 1 / (M : ℝ) < δ := by
    rw [div_lt_iff₀ hMreal]
    have h1 := (div_lt_iff₀ hδpos).mp hM
    linarith
  -- Partition `[0, 1)` into `M` subintervals `[j/M, (j+1)/M)`
  let step : ℝ → ℂ := fun x =>
    ∑ j ∈ Finset.range M,
      if ((j : ℝ) / M ≤ x ∧ x < ((j : ℝ) + 1) / M) then f ((j : ℝ) / M) else 0
  have hstep_approx : ∀ x ∈ Set.Ico (0 : ℝ) 1, ‖f x - step x‖ < ε / 3 := by
    intro x ⟨hx0, hx1⟩
    set j0 : ℕ := ⌊x * (M : ℝ)⌋₊
    have hj0_lt : j0 < M := by
      rw [Nat.floor_lt (by positivity)]
      nlinarith
    have hj0_le : (j0 : ℝ) / M ≤ x := by
      rw [div_le_iff₀ hMreal]
      exact Nat.floor_le (by positivity)
    have hj0_gt : x < ((j0 : ℝ) + 1) / M := by
      rw [lt_div_iff₀ hMreal]
      exact Nat.lt_floor_add_one (x * M)
    have hstep_eq : step x = f ((j0 : ℝ) / M) := by
      unfold step
      rw [Finset.sum_eq_single j0]
      · simp [hj0_le, hj0_gt]
      · intro j hj hne
        rw [if_neg]
        rintro ⟨h1, h2⟩
        have hlt : (j : ℝ) < (j0 : ℝ) + 1 := by
          have : (j : ℝ) / M < ((j0 : ℝ) + 1) / M := lt_of_le_of_lt h1 hj0_gt
          exact (div_lt_div_iff_of_pos_right hMreal).mp this
        have hgt : (j0 : ℝ) < (j : ℝ) + 1 := by
          have : (j0 : ℝ) / M < ((j : ℝ) + 1) / M := lt_of_le_of_lt hj0_le h2
          exact (div_lt_div_iff_of_pos_right hMreal).mp this
        have h1' : j < j0 + 1 := by exact_mod_cast hlt
        have h2' : j0 < j + 1 := by exact_mod_cast hgt
        omega
      · intro hmem; exact absurd (Finset.mem_range.mpr hj0_lt) hmem
    rw [hstep_eq]
    have hx_mem : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx0, le_of_lt hx1⟩
    have hj0_mem : (j0 : ℝ) / M ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · rw [div_le_one hMreal]; exact_mod_cast le_of_lt hj0_lt
    have hdist : dist x ((j0 : ℝ) / M) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hj0_le)]
      have : x - (j0 : ℝ) / M < 1 / M := by
        have h' : ((j0 : ℝ) + 1) / M = (j0 : ℝ) / M + 1 / M := by ring
        linarith
      linarith
    simpa [dist_eq_norm] using hδ x hx_mem ((j0 : ℝ) / M) hj0_mem hdist
  -- Riemann sum approximation to the integral
  have hint_approx :
      ‖(∫ t in (0 : ℝ)..1, f t) - ∑ j ∈ Finset.range M, (1 / (M : ℂ)) * f ((j : ℝ) / M)‖ ≤
        ε / 3 := by
    have hsplit : ∀ k : ℕ, k ≤ M →
        ∫ t in (0 : ℝ)..((k : ℝ) / M), f t =
          ∑ j ∈ Finset.range k, ∫ t in ((j : ℝ) / M)..(((j : ℝ) + 1) / M), f t := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        rw [Finset.sum_range_succ, ← ih (Nat.le_of_succ_le hk)]
        have h1 : IntervalIntegrable f volume 0 ((k : ℝ) / M) := by
          apply ContinuousOn.intervalIntegrable
          apply hf.mono
          rw [Set.uIcc_of_le (by positivity)]
          intro t ⟨ht0, ht1⟩
          refine ⟨ht0, le_trans ht1 ?_⟩
          rw [div_le_one hMreal]
          exact_mod_cast Nat.le_of_succ_le hk
        have h2 : IntervalIntegrable f volume ((k : ℝ) / M) (((k : ℝ) + 1) / M) := by
          apply ContinuousOn.intervalIntegrable
          apply hf.mono
          have hle : (k : ℝ) / M ≤ ((k : ℝ) + 1) / M := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hMreal); linarith
          rw [Set.uIcc_of_le hle]
          intro t ⟨ht0, ht1⟩
          refine ⟨le_trans (by positivity) ht0, le_trans ht1 ?_⟩
          rw [div_le_one hMreal]
          have : (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
          rw [this]; exact_mod_cast hk
        have hcast : (((k + 1 : ℕ) : ℝ) / M) = ((k : ℝ) + 1) / M := by push_cast; ring
        rw [hcast, intervalIntegral.integral_add_adjacent_intervals h1 h2]
    have hfull : ∫ t in (0 : ℝ)..1, f t =
        ∑ j ∈ Finset.range M, ∫ t in ((j : ℝ) / M)..(((j : ℝ) + 1) / M), f t := by
      have h := hsplit M le_rfl
      rw [div_self (ne_of_gt hMreal)] at h
      exact h
    rw [hfull, ← Finset.sum_sub_distrib]
    calc ‖∑ j ∈ Finset.range M,
            ((∫ t in ((j : ℝ) / M)..(((j : ℝ) + 1) / M), f t) -
              (1 / (M : ℂ)) * f ((j : ℝ) / M))‖
        ≤ ∑ j ∈ Finset.range M,
            ‖(∫ t in ((j : ℝ) / M)..(((j : ℝ) + 1) / M), f t) -
              (1 / (M : ℂ)) * f ((j : ℝ) / M)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range M, (ε / 3) * (1 / (M : ℝ)) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjlt : j < M := Finset.mem_range.mp hj
          have hle : (j : ℝ) / M ≤ ((j : ℝ) + 1) / M := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hMreal); linarith
          have hconst : (1 / (M : ℂ)) * f ((j : ℝ) / M) =
              ∫ _t in ((j : ℝ) / M)..(((j : ℝ) + 1) / M), f ((j : ℝ) / M) := by
            rw [intervalIntegral.integral_const]
            have hdiff : ((j : ℝ) + 1) / M - (j : ℝ) / M = 1 / (M : ℝ) := by ring
            rw [hdiff, Complex.real_smul]
            push_cast; rfl
          rw [hconst, ← intervalIntegral.integral_sub]
          · have hbound : ∀ t ∈ Set.Ioc ((j : ℝ) / M) (((j : ℝ) + 1) / M),
                ‖f t - f ((j : ℝ) / M)‖ ≤ ε / 3 := by
              intro t ⟨ht1, ht2⟩
              have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := by
                refine ⟨le_trans (by positivity) (le_of_lt ht1), le_trans ht2 ?_⟩
                rw [div_le_one hMreal]
                have : (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
                rw [this]; exact_mod_cast hjlt
              have hj_mem : (j : ℝ) / M ∈ Set.Icc (0 : ℝ) 1 := by
                refine ⟨by positivity, ?_⟩
                rw [div_le_one hMreal]; exact_mod_cast le_of_lt hjlt
              have hdist : dist t ((j : ℝ) / M) < δ := by
                rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_lt ht1))]
                have : t - (j : ℝ) / M ≤ 1 / M := by
                  have h' : ((j : ℝ) + 1) / M = (j : ℝ) / M + 1 / M := by ring
                  linarith
                linarith
              exact le_of_lt (by simpa [dist_eq_norm] using hδ t ht_mem ((j : ℝ) / M) hj_mem hdist)
            have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 3)
              (f := fun t => f t - f ((j : ℝ) / M)) (a := (j : ℝ) / M) (b := ((j : ℝ) + 1) / M)
              (fun t ht => hbound t (by rwa [Set.uIoc_of_le hle] at ht))
            have hdiff : |((j : ℝ) + 1) / M - (j : ℝ) / M| = 1 / (M : ℝ) := by
              have : ((j : ℝ) + 1) / M - (j : ℝ) / M = 1 / (M : ℝ) := by ring
              rw [this, abs_of_pos (by positivity)]
            rwa [hdiff] at hnorm
          · apply ContinuousOn.intervalIntegrable
            apply hf.mono
            rw [Set.uIcc_of_le hle]
            intro t ⟨ht0, ht1⟩
            refine ⟨le_trans (by positivity) ht0, le_trans ht1 ?_⟩
            rw [div_le_one hMreal]
            have : (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
            rw [this]; exact_mod_cast hjlt
          · exact intervalIntegrable_const
      _ = ε / 3 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp [ne_of_gt hMreal]
  -- Step function Cesàro average converges to the Riemann sum
  have hstep_tendsto :
      Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, step (Int.fract (u n)))
        atTop (nhds (∑ j ∈ Finset.range M, (1 / (M : ℂ)) * f ((j : ℝ) / M))) := by
    have hrewrite : ∀ N : ℕ,
        (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, step (Int.fract (u n)) =
          ∑ j ∈ Finset.range M,
            ((((((Finset.range N).filter
              (fun n => (j : ℝ) / M ≤ Int.fract (u n) ∧
                Int.fract (u n) < ((j : ℝ) + 1) / M)).card : ℝ) / (N : ℝ) : ℝ) : ℂ)) *
              f ((j : ℝ) / M) := by
      intro N
      simp only [step]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring
    simp_rw [hrewrite]
    apply tendsto_finsetSum
    intro j hj
    have hjlt : j < M := Finset.mem_range.mp hj
    have ha0 : 0 ≤ (j : ℝ) / M := by positivity
    have hab : (j : ℝ) / M ≤ ((j : ℝ) + 1) / M := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hMreal); linarith
    have hb1 : ((j : ℝ) + 1) / M ≤ 1 := by
      rw [div_le_one hMreal]
      have : (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [this]; exact_mod_cast hjlt
    have hcard := hu ((j : ℝ) / M) (((j : ℝ) + 1) / M) ha0 hab hb1
    have hdiff : ((j : ℝ) + 1) / M - (j : ℝ) / M = 1 / (M : ℝ) := by ring
    rw [hdiff] at hcard
    have hcardC : Tendsto
        (fun N : ℕ => (((((Finset.range N).filter
          (fun n => (j : ℝ) / M ≤ Int.fract (u n) ∧
            Int.fract (u n) < ((j : ℝ) + 1) / M)).card : ℝ) / (N : ℝ) : ℝ) : ℂ))
        atTop (nhds ((1 / (M : ℝ) : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hcard
    have hmul := hcardC.mul_const (f ((j : ℝ) / M))
    simpa using hmul
  rw [Metric.tendsto_atTop] at hstep_tendsto
  obtain ⟨N0, hN0⟩ := hstep_tendsto (ε / 3) (by positivity)
  refine ⟨max N0 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hN0' : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hterm1 :
      ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, f (Int.fract (u n)) -
        (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, step (Int.fract (u n))‖ ≤ ε / 3 := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_div, norm_one,
      Complex.norm_natCast]
    calc (1 / (N : ℝ)) * ‖∑ n ∈ Finset.range N, (f (Int.fract (u n)) - step (Int.fract (u n)))‖
        ≤ (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, ‖f (Int.fract (u n)) - step (Int.fract (u n))‖ := by
          gcongr; exact norm_sum_le _ _
      _ ≤ (1 / (N : ℝ)) * ∑ _n ∈ Finset.range N, (ε / 3) := by
          gcongr with n _
          exact le_of_lt (hstep_approx (Int.fract (u n))
            ⟨Int.fract_nonneg (u n), Int.fract_lt_one (u n)⟩)
      _ = ε / 3 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp [ne_of_gt hNpos]
  have hterm2 := hN0 N hN0'
  rw [dist_eq_norm] at hterm2 ⊢
  calc ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, f (Int.fract (u n)) - ∫ t in (0 : ℝ)..1, f t‖
      = ‖((1 / (N : ℂ)) * ∑ n ∈ Finset.range N, f (Int.fract (u n)) -
            (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, step (Int.fract (u n))) +
          ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N, step (Int.fract (u n)) -
            ∑ j ∈ Finset.range M, (1 / (M : ℂ)) * f ((j : ℝ) / M)) -
          ((∫ t in (0 : ℝ)..1, f t) -
            ∑ j ∈ Finset.range M, (1 / (M : ℂ)) * f ((j : ℝ) / M))‖ := by
        congr 1; abel
    _ ≤ ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, f (Int.fract (u n)) -
            (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, step (Int.fract (u n))‖ +
        ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, step (Int.fract (u n)) -
            ∑ j ∈ Finset.range M, (1 / (M : ℂ)) * f ((j : ℝ) / M)‖ +
        ‖(∫ t in (0 : ℝ)..1, f t) -
            ∑ j ∈ Finset.range M, (1 / (M : ℂ)) * f ((j : ℝ) / M)‖ := by
        calc _ ≤ _ + _ := norm_sub_le _ _
          _ ≤ _ + _ + _ := by gcongr; exact norm_add_le _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

/-- Forward direction of Weyl's Criterion: equidistribution implies vanishing of all nonzero
Weyl exponential sums. -/
theorem IsEquidistributed.weyl_sum_tendsto_zero {u : ℕ → ℝ} (hu : IsEquidistributed u)
    {k : ℤ} (hk : k ≠ 0) :
    Tendsto
      (fun N : ℕ =>
        (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * u n))
      atTop (nhds 0) := by
  have hcont : ContinuousOn (fun t : ℝ => weylExp k t) (Set.Icc 0 1) := by
    unfold weylExp
    exact (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).continuousOn
  have hlim := hu.tendsto_average_of_continuousOn hcont
  rw [integral_weylExp_eq_zero hk] at hlim
  have heq : (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, weylExp k (Int.fract (u n))) =
      fun N : ℕ =>
        (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * u n) := by
    funext N
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [weylExp_fract, weylExp_eq]
  rwa [heq] at hlim

/-- If all nonzero Weyl exponential sums vanish, then Cesàro averages of every continuous function
on the circle `AddCircle 1` converge to its integral over `[0, 1]`. -/
theorem tendsto_average_continuous_addCircle_of_weyl {u : ℕ → ℝ}
    (hw : ∀ k : ℤ, k ≠ 0 →
      Tendsto
        (fun N : ℕ =>
          (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * u n))
        atTop (nhds 0))
    (g : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, g (u n : AddCircle (1 : ℝ)))
      atTop (nhds (∫ t in (0 : ℝ)..1, g (t : AddCircle (1 : ℝ)))) := by
  have : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
  -- Step 1: every element of `Submodule.span ℂ (Set.range fourier)` satisfies the limit
  have hspan : ∀ P ∈ Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))),
      Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, P (u n : AddCircle (1 : ℝ)))
        atTop (nhds (∫ t in (0 : ℝ)..1, P (t : AddCircle (1 : ℝ)))) := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨k, rfl⟩
      by_cases hk : k = 0
      · subst hk
        have h1 : ∀ N : ℕ, 1 ≤ N →
            (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
              (fourier (T := (1 : ℝ)) 0) (u n : AddCircle (1 : ℝ)) = 1 := by
          intro N hN
          simp only [fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          field_simp [hN0]
        have hint : ∫ t in (0 : ℝ)..1, (fourier (T := (1 : ℝ)) 0) (t : AddCircle (1 : ℝ)) = 1 := by
          simp
        rw [hint]
        exact tendsto_atTop_of_eventually_const (i₀ := 1) h1
      · have hint : ∫ t in (0 : ℝ)..1, (fourier (T := (1 : ℝ)) k) (t : AddCircle (1 : ℝ)) = 0 := by
          have heq : (fun t : ℝ => (fourier (T := (1 : ℝ)) k) (t : AddCircle (1 : ℝ))) =
              fun t : ℝ => weylExp k t := by funext t; exact fourier_one_coe_apply k t
          rw [heq, integral_weylExp_eq_zero hk]
        rw [hint]
        have heq : (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
              (fourier (T := (1 : ℝ)) k) (u n : AddCircle (1 : ℝ))) =
            fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
              Complex.exp (2 * Real.pi * Complex.I * k * u n) := by
          funext N
          congr 1
          apply Finset.sum_congr rfl
          intro n _
          rw [fourier_one_coe_apply, weylExp_eq]
        rw [heq]
        exact hw k hk
    | zero =>
      simp
    | add x y _ _ ihx ihy =>
      have havg : (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
            (x + y) (u n : AddCircle (1 : ℝ))) =
          fun N : ℕ =>
            (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, x (u n : AddCircle (1 : ℝ)) +
            (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, y (u n : AddCircle (1 : ℝ)) := by
        funext N
        simp only [ContinuousMap.add_apply, Finset.sum_add_distrib, mul_add]
      have hint : ∫ t in (0 : ℝ)..1, (x + y) (t : AddCircle (1 : ℝ)) =
          (∫ t in (0 : ℝ)..1, x (t : AddCircle (1 : ℝ))) +
          (∫ t in (0 : ℝ)..1, y (t : AddCircle (1 : ℝ))) := by
        simp only [ContinuousMap.add_apply]
        apply intervalIntegral.integral_add
        · exact (x.continuous.comp (AddCircle.continuous_mk' _)).intervalIntegrable _ _
        · exact (y.continuous.comp (AddCircle.continuous_mk' _)).intervalIntegrable _ _
      rw [havg, hint]
      exact ihx.add ihy
    | smul c x _ ihx =>
      have havg : (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
            (c • x) (u n : AddCircle (1 : ℝ))) =
          fun N : ℕ => c * ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N, x (u n : AddCircle (1 : ℝ))) := by
        funext N
        simp only [ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        ring
      have hint : ∫ t in (0 : ℝ)..1, (c • x) (t : AddCircle (1 : ℝ)) =
          c * ∫ t in (0 : ℝ)..1, x (t : AddCircle (1 : ℝ)) := by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul]
      rw [havg, hint]
      exact ihx.const_mul c
  -- Step 2: approximate `g` uniformly by `P ∈ span fourier` using `span_fourier_closure_eq_top`
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hmem : g ∈ (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  have hclos : g ∈ closure (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) :
      Set C(AddCircle (1 : ℝ), ℂ)) := hmem
  rw [Metric.mem_closure_iff] at hclos
  obtain ⟨P, hPmem, hPg⟩ := hclos (ε / 3) (by positivity)
  have hnorm_le : ∀ z : AddCircle (1 : ℝ), ‖g z - P z‖ ≤ ε / 3 := by
    intro z
    have h1 : ‖(g - P) z‖ ≤ ‖g - P‖ := ContinuousMap.norm_coe_le_norm (g - P) z
    have h2 : ‖g - P‖ < ε / 3 := by simpa [dist_eq_norm] using hPg
    exact le_of_lt (lt_of_le_of_lt h1 h2)
  have hPlim := hspan P hPmem
  rw [Metric.tendsto_atTop] at hPlim
  obtain ⟨N0, hN0⟩ := hPlim (ε / 3) (by positivity)
  refine ⟨max N0 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hN0' : N0 ≤ N := le_trans (le_max_left _ _) hN
  have h1 : ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, g (u n : AddCircle (1 : ℝ)) -
      (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, P (u n : AddCircle (1 : ℝ))‖ ≤ ε / 3 := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_div, norm_one, Complex.norm_natCast]
    calc (1 / (N : ℝ)) * ‖∑ n ∈ Finset.range N,
            (g (u n : AddCircle (1 : ℝ)) - P (u n : AddCircle (1 : ℝ)))‖
        ≤ (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
            ‖g (u n : AddCircle (1 : ℝ)) - P (u n : AddCircle (1 : ℝ))‖ := by
          gcongr; exact norm_sum_le _ _
      _ ≤ (1 / (N : ℝ)) * ∑ _n ∈ Finset.range N, (ε / 3) := by
          gcongr with n _
          exact hnorm_le _
      _ = ε / 3 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp [ne_of_gt hNpos]
  have h2 : ‖(∫ t in (0 : ℝ)..1, g (t : AddCircle (1 : ℝ))) -
      ∫ t in (0 : ℝ)..1, P (t : AddCircle (1 : ℝ))‖ ≤ ε / 3 := by
    rw [← intervalIntegral.integral_sub]
    · have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 3)
        (f := fun t : ℝ => g (t : AddCircle (1 : ℝ)) - P (t : AddCircle (1 : ℝ))) (a := 0) (b := 1)
        (fun t _ => hnorm_le (t : AddCircle (1 : ℝ)))
      simpa using hbd
    · exact (g.continuous.comp (AddCircle.continuous_mk' _)).intervalIntegrable _ _
    · exact (P.continuous.comp (AddCircle.continuous_mk' _)).intervalIntegrable _ _
  have h3 := hN0 N hN0'
  rw [dist_eq_norm] at h3 ⊢
  calc ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, g (u n : AddCircle (1 : ℝ)) -
          ∫ t in (0 : ℝ)..1, g (t : AddCircle (1 : ℝ))‖
      = ‖((1 / (N : ℂ)) * ∑ n ∈ Finset.range N, g (u n : AddCircle (1 : ℝ)) -
            (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, P (u n : AddCircle (1 : ℝ))) +
          ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N, P (u n : AddCircle (1 : ℝ)) -
            ∫ t in (0 : ℝ)..1, P (t : AddCircle (1 : ℝ))) -
          ((∫ t in (0 : ℝ)..1, g (t : AddCircle (1 : ℝ))) -
            ∫ t in (0 : ℝ)..1, P (t : AddCircle (1 : ℝ)))‖ := by ring_nf
    _ ≤ _ := by
        calc _ ≤ _ + _ := norm_sub_le _ _
          _ ≤ _ + _ + _ := by gcongr; exact norm_add_le _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

/-- Continuous piecewise-linear trapezoid equal to `0` on `(-∞, a₁] ∪ [b₂, ∞)` and `1` on
`[a₂, b₁]`, rising linearly on `[a₁, a₂]` and falling linearly on `[b₁, b₂]`. -/
noncomputable def trapezoid (a₁ a₂ b₁ b₂ t : ℝ) : ℝ :=
  min 1 (max 0 (min ((t - a₁) / (a₂ - a₁)) ((b₂ - t) / (b₂ - b₁))))

lemma continuous_trapezoid (a₁ a₂ b₁ b₂ : ℝ) : Continuous (trapezoid a₁ a₂ b₁ b₂) := by
  unfold trapezoid
  fun_prop

lemma trapezoid_nonneg (a₁ a₂ b₁ b₂ t : ℝ) : 0 ≤ trapezoid a₁ a₂ b₁ b₂ t := by
  unfold trapezoid
  exact le_min (by norm_num) (le_max_left _ _)

lemma trapezoid_le_one (a₁ a₂ b₁ b₂ t : ℝ) : trapezoid a₁ a₂ b₁ b₂ t ≤ 1 :=
  min_le_left _ _

lemma trapezoid_eq_zero_of_le {a₁ a₂ b₁ b₂ t : ℝ} (ha : a₁ < a₂) (ht : t ≤ a₁) :
    trapezoid a₁ a₂ b₁ b₂ t = 0 := by
  unfold trapezoid
  have h1 : (t - a₁) / (a₂ - a₁) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have h2 : min ((t - a₁) / (a₂ - a₁)) ((b₂ - t) / (b₂ - b₁)) ≤ 0 := le_trans (min_le_left _ _) h1
  rw [max_eq_left h2, min_eq_right (by norm_num)]

lemma trapezoid_eq_zero_of_ge {a₁ a₂ b₁ b₂ t : ℝ} (hb : b₁ < b₂) (ht : b₂ ≤ t) :
    trapezoid a₁ a₂ b₁ b₂ t = 0 := by
  unfold trapezoid
  have h1 : (b₂ - t) / (b₂ - b₁) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have h2 : min ((t - a₁) / (a₂ - a₁)) ((b₂ - t) / (b₂ - b₁)) ≤ 0 := le_trans (min_le_right _ _) h1
  rw [max_eq_left h2, min_eq_right (by norm_num)]

lemma trapezoid_eq_one_of_mem {a₁ a₂ b₁ b₂ t : ℝ} (ha : a₁ < a₂) (hb : b₁ < b₂)
    (ht1 : a₂ ≤ t) (ht2 : t ≤ b₁) :
    trapezoid a₁ a₂ b₁ b₂ t = 1 := by
  unfold trapezoid
  have h1 : 1 ≤ (t - a₁) / (a₂ - a₁) := by rw [le_div_iff₀ (by linarith)]; linarith
  have h2 : 1 ≤ (b₂ - t) / (b₂ - b₁) := by rw [le_div_iff₀ (by linarith)]; linarith
  have h3 : 1 ≤ min ((t - a₁) / (a₂ - a₁)) ((b₂ - t) / (b₂ - b₁)) := le_min h1 h2
  have h4 : 1 ≤ max 0 (min ((t - a₁) / (a₂ - a₁)) ((b₂ - t) / (b₂ - b₁))) :=
    le_trans h3 (le_max_right _ _)
  exact min_eq_left h4

lemma trapezoid_eq_left_ramp {a₁ a₂ b₁ b₂ t : ℝ} (ha : a₁ < a₂) (hab : a₂ ≤ b₁) (hb : b₁ < b₂)
    (ht1 : a₁ ≤ t) (ht2 : t ≤ a₂) :
    trapezoid a₁ a₂ b₁ b₂ t = (t - a₁) / (a₂ - a₁) := by
  unfold trapezoid
  have h0 : 0 ≤ (t - a₁) / (a₂ - a₁) := div_nonneg (by linarith) (by linarith)
  have h1 : (t - a₁) / (a₂ - a₁) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h2 : 1 ≤ (b₂ - t) / (b₂ - b₁) := by rw [le_div_iff₀ (by linarith)]; linarith
  rw [min_eq_left (le_trans h1 h2), max_eq_right h0, min_eq_right h1]

lemma trapezoid_eq_right_ramp {a₁ a₂ b₁ b₂ t : ℝ} (ha : a₁ < a₂) (hab : a₂ ≤ b₁) (hb : b₁ < b₂)
    (ht1 : b₁ ≤ t) (ht2 : t ≤ b₂) :
    trapezoid a₁ a₂ b₁ b₂ t = (b₂ - t) / (b₂ - b₁) := by
  unfold trapezoid
  have h0 : 0 ≤ (b₂ - t) / (b₂ - b₁) := div_nonneg (by linarith) (by linarith)
  have h1 : (b₂ - t) / (b₂ - b₁) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h2 : 1 ≤ (t - a₁) / (a₂ - a₁) := by rw [le_div_iff₀ (by linarith)]; linarith
  rw [min_eq_right (le_trans h1 h2), max_eq_right h0, min_eq_right h1]

lemma integral_trapezoid {a₁ a₂ b₁ b₂ : ℝ} (h0 : 0 ≤ a₁) (ha : a₁ < a₂) (hab : a₂ ≤ b₁)
    (hb : b₁ < b₂) (h1 : b₂ ≤ 1) :
    ∫ t in (0 : ℝ)..1, trapezoid a₁ a₂ b₁ b₂ t = (b₁ + b₂ - a₁ - a₂) / 2 := by
  have hint : ∀ x y : ℝ, IntervalIntegrable (trapezoid a₁ a₂ b₁ b₂) volume x y :=
    fun x y => (continuous_trapezoid a₁ a₂ b₁ b₂).intervalIntegrable x y
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 a₁) (hint a₁ 1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint a₁ a₂) (hint a₂ 1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint a₂ b₁) (hint b₁ 1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint b₁ b₂) (hint b₂ 1)]
  have i1 : ∫ t in (0 : ℝ)..a₁, trapezoid a₁ a₂ b₁ b₂ t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht; rw [Set.uIcc_of_le h0] at ht; exact trapezoid_eq_zero_of_le ha ht.2
  have hid_eq : ∀ x y : ℝ, ∫ t in x..y, t = (y ^ 2 - x ^ 2) / 2 := by
    intro x y
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x) (b := y)
      (f := fun t : ℝ => t ^ 2 / 2) (f' := fun t : ℝ => t)
      (fun t _ => by
        have hd := (hasDerivAt_pow 2 t).div_const (2 : ℝ)
        simpa using hd)
      (continuous_id.intervalIntegrable _ _)
    linarith
  have i2 : ∫ t in a₁..a₂, trapezoid a₁ a₂ b₁ b₂ t = (a₂ - a₁) / 2 := by
    rw [intervalIntegral.integral_congr (g := fun t => (t - a₁) / (a₂ - a₁))]
    · simp only [div_eq_mul_inv]
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ => a₁)
          (continuous_id.intervalIntegrable _ _) intervalIntegrable_const]
      have hid := hid_eq a₁ a₂
      have hc : ∫ _t in a₁..a₂, a₁ = (a₂ - a₁) * a₁ := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      rw [hid, hc]
      have hne : a₂ - a₁ ≠ 0 := by linarith
      field_simp [hne]
      ring
    · intro t ht; rw [Set.uIcc_of_le (le_of_lt ha)] at ht
      exact trapezoid_eq_left_ramp ha hab hb ht.1 ht.2
  have i3 : ∫ t in a₂..b₁, trapezoid a₁ a₂ b₁ b₂ t = b₁ - a₂ := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
    · simp
    · intro t ht; rw [Set.uIcc_of_le hab] at ht
      exact trapezoid_eq_one_of_mem ha hb ht.1 ht.2
  have i4 : ∫ t in b₁..b₂, trapezoid a₁ a₂ b₁ b₂ t = (b₂ - b₁) / 2 := by
    rw [intervalIntegral.integral_congr (g := fun t => (b₂ - t) / (b₂ - b₁))]
    · simp only [div_eq_mul_inv]
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_sub (f := fun _ => b₂) (g := fun t : ℝ => t)
          intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
      have hid := hid_eq b₁ b₂
      have hc : ∫ _t in b₁..b₂, b₂ = (b₂ - b₁) * b₂ := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      rw [hid, hc]
      have hne : b₂ - b₁ ≠ 0 := by linarith
      field_simp [hne]
      ring
    · intro t ht; rw [Set.uIcc_of_le (le_of_lt hb)] at ht
      exact trapezoid_eq_right_ramp ha hab hb ht.1 ht.2
  have i5 : ∫ t in b₂..1, trapezoid a₁ a₂ b₁ b₂ t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht; rw [Set.uIcc_of_le h1] at ht; exact trapezoid_eq_zero_of_ge hb ht.1
  rw [i1, i2, i3, i4, i5]
  ring

/-- Real-valued version of `tendsto_average_continuous_addCircle_of_weyl` for lifted functions
vanishing at `0` and `1`. -/
lemma tendsto_average_trapezoid_of_weyl {u : ℕ → ℝ}
    (hw : ∀ k : ℤ, k ≠ 0 →
      Tendsto
        (fun N : ℕ =>
          (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * u n))
        atTop (nhds 0))
    {a₁ a₂ b₁ b₂ : ℝ} (h0 : 0 ≤ a₁) (ha : a₁ < a₂) (hab : a₂ ≤ b₁)
    (hb : b₁ < b₂) (h1 : b₂ ≤ 1) :
    Tendsto
      (fun N : ℕ =>
        (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, trapezoid a₁ a₂ b₁ b₂ (Int.fract (u n)))
      atTop (nhds ((b₁ + b₂ - a₁ - a₂) / 2)) := by
  have : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
  let fC : ℝ → ℂ := fun t => (trapezoid a₁ a₂ b₁ b₂ t : ℂ)
  have hfC01 : fC 0 = fC (0 + 1) := by
    simp only [fC, zero_add]
    rw [trapezoid_eq_zero_of_le ha h0, trapezoid_eq_zero_of_ge hb h1]
  have hfCcont : ContinuousOn fC (Set.Icc 0 (0 + 1)) :=
    (Complex.continuous_ofReal.comp (continuous_trapezoid a₁ a₂ b₁ b₂)).continuousOn
  let g : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨AddCircle.liftIco (1 : ℝ) 0 fC, AddCircle.liftIco_continuous hfC01 hfCcont⟩
  have hlim := tendsto_average_continuous_addCircle_of_weyl hw g
  have hlim_re := (Complex.continuous_re.tendsto _).comp hlim
  -- Evaluate `g (u n)` using `coe_addCircle_fract` and `AddCircle.liftIco_coe_apply`
  have hval : ∀ x : ℝ, g (x : AddCircle (1 : ℝ)) = (trapezoid a₁ a₂ b₁ b₂ (Int.fract x) : ℂ) := by
    intro x
    rw [← coe_addCircle_fract x]
    change AddCircle.liftIco (1 : ℝ) 0 fC ((Int.fract x : ℝ) : AddCircle (1 : ℝ)) = _
    rw [AddCircle.liftIco_coe_apply]
    have hx : Int.fract x ∈ Set.Ico (0 : ℝ) (0 + 1) := by
      rw [zero_add]; exact ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
    exact hx
  have hre_avg : ∀ N : ℕ,
      (((1 / (N : ℂ)) * ∑ n ∈ Finset.range N, g (u n : AddCircle (1 : ℝ))).re) =
        (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, trapezoid a₁ a₂ b₁ b₂ (Int.fract (u n)) := by
    intro N
    simp only [hval, ← Complex.ofReal_sum, one_div]
    rw [show ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) by simp]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hre_int :
      (∫ t in (0 : ℝ)..1, g (t : AddCircle (1 : ℝ))).re = (b₁ + b₂ - a₁ - a₂) / 2 := by
    have hcongr : ∫ t in (0 : ℝ)..1, g (t : AddCircle (1 : ℝ)) =
        ∫ t in (0 : ℝ)..1, (trapezoid a₁ a₂ b₁ b₂ t : ℂ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      by_cases ht1 : t = 1
      · subst ht1
        rw [hval, Int.fract_one, trapezoid_eq_zero_of_le ha h0, trapezoid_eq_zero_of_ge hb h1]
      · have htIco : t ∈ Set.Ico (0 : ℝ) 1 := ⟨le_of_lt ht.1, lt_of_le_of_ne ht.2 ht1⟩
        rw [hval, Int.fract_eq_self.mpr htIco]
    rw [hcongr, intervalIntegral.integral_ofReal, Complex.ofReal_re,
      integral_trapezoid h0 ha hab hb h1]
  have heq_fn :
      (fun N : ℕ => ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N, g (u n : AddCircle (1 : ℝ))).re) =
        fun N : ℕ =>
          (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, trapezoid a₁ a₂ b₁ b₂ (Int.fract (u n)) := by
    funext N; exact hre_avg N
  rwa [Function.comp_def, heq_fn, hre_int] at hlim_re

/-- Interior interval equidistribution from Weyl's exponential sum hypothesis:
if `0 < a < b < 1`, sandwich `1_{[a, b)}` between two continuous trapezoids. -/
lemma tendsto_Ico_of_weyl_interior {u : ℕ → ℝ}
    (hw : ∀ k : ℤ, k ≠ 0 →
      Tendsto
        (fun N : ℕ =>
          (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * u n))
        atTop (nhds 0))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n => a ≤ Int.fract (u n) ∧ Int.fract (u n) < b)).card : ℝ) /
          (N : ℝ))
      atTop (nhds (b - a)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := min (min (ε / 2) ((b - a) / 4)) (min (a / 2) ((1 - b) / 2))
  have hδpos : 0 < δ := by
    dsimp only [δ]
    positivity
  have hδ_eps : δ ≤ ε / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ_ab : δ ≤ (b - a) / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ_a : δ ≤ a / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_b : δ ≤ (1 - b) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  -- Lower trapezoid `gMinus` on `[a, a+δ, b-δ, b]`
  have hlo := tendsto_average_trapezoid_of_weyl hw (a₁ := a) (a₂ := a + δ) (b₁ := b - δ) (b₂ := b)
    (le_of_lt ha) (by linarith) (by linarith) (by linarith) (le_of_lt hb)
  -- Upper trapezoid `gPlus` on `[a-δ, a, b, b+δ]`
  have hhi := tendsto_average_trapezoid_of_weyl hw (a₁ := a - δ) (a₂ := a) (b₁ := b) (b₂ := b + δ)
    (by linarith) (by linarith) (le_of_lt hab) (by linarith) (by linarith)
  have hlo_val : (b - δ + b - a - (a + δ)) / 2 = (b - a) - δ := by ring
  have hhi_val : (b + (b + δ) - (a - δ) - a) / 2 = (b - a) + δ := by ring
  rw [hlo_val] at hlo
  rw [hhi_val] at hhi
  rw [Metric.tendsto_atTop] at hlo hhi
  obtain ⟨N1, hN1⟩ := hlo (ε / 2) (by positivity)
  obtain ⟨N2, hN2⟩ := hhi (ε / 2) (by positivity)
  refine ⟨max (max N1 N2) 1, fun N hN => ?_⟩
  have hN1' : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2' : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 1 ≤ N := le_trans (le_max_right _ _) hN
    exact_mod_cast this
  -- Pointwise sandwich: `gMinus (fract (u n)) ≤ 1_{[a,b)} (fract (u n)) ≤ gPlus (fract (u n))`
  have hcard_eq :
      ((((Finset.range N).filter (fun n => a ≤ Int.fract (u n) ∧ Int.fract (u n) < b)).card : ℝ) /
        (N : ℝ)) =
      (1 / (N : ℝ)) *
        ∑ n ∈ Finset.range N, (if a ≤ Int.fract (u n) ∧ Int.fract (u n) < b then (1 : ℝ) else 0) := by
    rw [Finset.sum_boole]
    ring
  have hs_lo : (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
      trapezoid a (a + δ) (b - δ) b (Int.fract (u n)) ≤
      (((Finset.range N).filter (fun n => a ≤ Int.fract (u n) ∧ Int.fract (u n) < b)).card : ℝ) /
        (N : ℝ) := by
    rw [hcard_eq]
    gcongr with n _
    split_ifs with hmem
    · exact trapezoid_le_one _ _ _ _ _
    · push Not at hmem
      by_cases hlt : Int.fract (u n) < a
      · rw [trapezoid_eq_zero_of_le (by linarith) (le_of_lt hlt)]
      · push Not at hlt
        rw [trapezoid_eq_zero_of_ge (by linarith) (hmem hlt)]
  have hs_hi :
      (((Finset.range N).filter (fun n => a ≤ Int.fract (u n) ∧ Int.fract (u n) < b)).card : ℝ) /
        (N : ℝ) ≤
      (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
        trapezoid (a - δ) a b (b + δ) (Int.fract (u n)) := by
    rw [hcard_eq]
    gcongr with n _
    split_ifs with hmem
    · rw [trapezoid_eq_one_of_mem (by linarith) (by linarith) hmem.1 (le_of_lt hmem.2)]
    · exact trapezoid_nonneg _ _ _ _ _
  have h1 := hN1 N hN1'
  have h2 := hN2 N hN2'
  rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
  constructor <;> linarith

/-- Backward direction of Weyl's Criterion: vanishing of all nonzero Weyl exponential sums
implies equidistribution modulo `1`. -/
theorem isEquidistributed_of_weyl_sum {u : ℕ → ℝ}
    (hw : ∀ k : ℤ, k ≠ 0 →
      Tendsto
        (fun N : ℕ =>
          (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * u n))
        atTop (nhds 0)) :
    IsEquidistributed u := by
  -- Shift-invariance of the Weyl hypothesis
  have hw_shift : ∀ c : ℝ, ∀ k : ℤ, k ≠ 0 →
      Tendsto
        (fun N : ℕ =>
          (1 / (N : ℂ)) *
            ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * ((u n + c : ℝ) : ℂ)))
        atTop (nhds 0) := by
    intro c k hk
    have heq : (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
          Complex.exp (2 * Real.pi * Complex.I * k * ((u n + c : ℝ) : ℂ))) =
        fun N : ℕ => weylExp k c * ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
          Complex.exp (2 * Real.pi * Complex.I * k * u n)) := by
      funext N
      have hterm : ∀ n : ℕ, Complex.exp (2 * Real.pi * Complex.I * k * ((u n + c : ℝ) : ℂ)) =
          weylExp k c * Complex.exp (2 * Real.pi * Complex.I * k * u n) := by
        intro n
        change weylExp k (u n + c) = weylExp k c * weylExp k (u n)
        rw [weylExp_add, mul_comm]
      simp_rw [hterm, ← Finset.mul_sum]
      ring
    rw [heq]
    simpa using (hw k hk).const_mul (weylExp k c)
  -- Helper for `[0, b)` with `0 < b < 1`: shift by `c = (1 - b) / 2` into the interior
  have hzero_left : ∀ b : ℝ, 0 < b → b < 1 →
      Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter (fun n => 0 ≤ Int.fract (u n) ∧ Int.fract (u n) < b)).card : ℝ) /
            (N : ℝ))
        atTop (nhds (b - 0)) := by
    intro b hb0 hb1
    set c : ℝ := (1 - b) / 2
    have hc0 : 0 < c := by dsimp [c]; linarith
    have hcb : c < b + c := by linarith
    have hcb1 : b + c < 1 := by dsimp [c]; linarith
    have hiff : ∀ x : ℝ, (0 ≤ Int.fract x ∧ Int.fract x < b) ↔
        (c ≤ Int.fract (x + c) ∧ Int.fract (x + c) < b + c) := by
      intro x
      have hf0 := Int.fract_nonneg x
      have hf1 := Int.fract_lt_one x
      have hxc : Int.fract (x + c) = Int.fract (Int.fract x + c) := by
        have h1 : x + c = (Int.fract x + c) + (⌊x⌋ : ℤ) := by rw [Int.fract]; ring
        rw [h1, Int.fract_add_intCast]
      rw [hxc]
      by_cases hlt1 : Int.fract x + c < 1
      · have heq : Int.fract (Int.fract x + c) = Int.fract x + c :=
          Int.fract_eq_self.mpr ⟨by linarith, hlt1⟩
        rw [heq]
        constructor <;> intro h <;> constructor <;> linarith
      · push Not at hlt1
        have hlt2 : Int.fract x + c - 1 < 1 := by linarith
        have hge0 : 0 ≤ Int.fract x + c - 1 := by linarith
        have heq : Int.fract (Int.fract x + c) = Int.fract x + c - 1 := by
          have h1 : Int.fract x + c = (Int.fract x + c - 1) + (1 : ℤ) := by push_cast; ring
          conv_lhs => rw [h1]
          rw [Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨hge0, hlt2⟩]
        rw [heq]
        constructor
        · rintro ⟨_, hxb⟩; exfalso; linarith
        · rintro ⟨hc_le, _⟩; exfalso; linarith
    have hint := tendsto_Ico_of_weyl_interior (u := fun n => u n + c) (hw_shift c) hc0 hcb hcb1
    have hsub : b + c - c = b - 0 := by ring
    rw [hsub] at hint
    have hfn : (fun N : ℕ =>
          (((Finset.range N).filter (fun n => 0 ≤ Int.fract (u n) ∧ Int.fract (u n) < b)).card : ℝ) /
            (N : ℝ)) =
        fun N : ℕ =>
          (((Finset.range N).filter
            (fun n => c ≤ Int.fract (u n + c) ∧ Int.fract (u n + c) < b + c)).card : ℝ) /
            (N : ℝ) := by
      funext N
      congr 3
      apply Finset.filter_congr
      intro n _
      exact hiff (u n)
    rwa [hfn]
  -- Now handle all `0 ≤ a ≤ b ≤ 1`
  intro a b ha0 hab hb1
  by_cases heq : a = b
  · subst heq
    have h0 : ∀ N : ℕ,
        (((Finset.range N).filter (fun n => a ≤ Int.fract (u n) ∧ Int.fract (u n) < a)).card : ℝ) /
          (N : ℝ) = 0 := by
      intro N
      have : (Finset.range N).filter (fun n => a ≤ Int.fract (u n) ∧ Int.fract (u n) < a) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro n _ ⟨h1, h2⟩; linarith
      rw [this]; simp
    simp_rw [h0, sub_self]
    exact tendsto_const_nhds
  have hab' : a < b := lt_of_le_of_ne hab heq
  rcases eq_or_lt_of_le ha0 with rfl | ha_pos
  · rcases eq_or_lt_of_le hb1 with rfl | hb_lt
    · -- `[0, 1)`
      have h1 : ∀ N : ℕ, 1 ≤ N →
          (((Finset.range N).filter (fun n => 0 ≤ Int.fract (u n) ∧ Int.fract (u n) < 1)).card : ℝ) /
            (N : ℝ) = 1 - 0 := by
        intro N hN
        have hfilt : (Finset.range N).filter (fun n => 0 ≤ Int.fract (u n) ∧ Int.fract (u n) < 1) =
            Finset.range N := by
          rw [Finset.filter_true_of_mem]
          intro n _; exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
        rw [hfilt, Finset.card_range, sub_zero, div_self]
        exact Nat.cast_ne_zero.mpr (by omega)
      exact tendsto_atTop_of_eventually_const (i₀ := 1) h1
    · exact hzero_left b hab' hb_lt
  · rcases eq_or_lt_of_le hb1 with rfl | hb_lt
    · -- `[a, 1)` with `0 < a < 1`: complement of `[0, a)`
      have hcomp := (tendsto_const_nhds (x := (1 : ℝ))).sub (hzero_left a ha_pos hab')
      rw [sub_zero] at hcomp
      have hev : ∀ᶠ N : ℕ in atTop,
          (((Finset.range N).filter (fun n => a ≤ Int.fract (u n) ∧ Int.fract (u n) < 1)).card : ℝ) /
            (N : ℝ) =
          1 - (((Finset.range N).filter (fun n => 0 ≤ Int.fract (u n) ∧ Int.fract (u n) < a)).card : ℝ) /
            (N : ℝ) := by
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hdisj : Disjoint
            ((Finset.range N).filter (fun n => 0 ≤ Int.fract (u n) ∧ Int.fract (u n) < a))
            ((Finset.range N).filter (fun n => a ≤ Int.fract (u n) ∧ Int.fract (u n) < 1)) := by
          rw [Finset.disjoint_filter]
          intro n _ h1 h2; linarith
        have hunion :
            ((Finset.range N).filter (fun n => 0 ≤ Int.fract (u n) ∧ Int.fract (u n) < a)) ∪
            ((Finset.range N).filter (fun n => a ≤ Int.fract (u n) ∧ Int.fract (u n) < 1)) =
            Finset.range N := by
          ext n
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
          · intro h
            by_cases hlt : Int.fract (u n) < a
            · left; exact ⟨h, Int.fract_nonneg _, hlt⟩
            · right; push Not at hlt; exact ⟨h, hlt, Int.fract_lt_one _⟩
        have hcard :
            ((Finset.range N).filter (fun n => 0 ≤ Int.fract (u n) ∧ Int.fract (u n) < a)).card +
            ((Finset.range N).filter (fun n => a ≤ Int.fract (u n) ∧ Int.fract (u n) < 1)).card = N := by
          rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_range]
        have hcardR :
            (((Finset.range N).filter (fun n => 0 ≤ Int.fract (u n) ∧ Int.fract (u n) < a)).card : ℝ) +
            (((Finset.range N).filter (fun n => a ≤ Int.fract (u n) ∧ Int.fract (u n) < 1)).card : ℝ) =
            (N : ℝ) := by exact_mod_cast hcard
        field_simp [hN0]
        linarith
      exact hcomp.congr' (hev.mono fun _ h => h.symm)
    · exact tendsto_Ico_of_weyl_interior hw ha_pos hab' hb_lt

/-- **Weyl's 1916 Equidistribution Criterion (Master `↔` Form)**:
A real sequence `u` is equidistributed modulo `1` if and only if for every nonzero integer `k`,
the Weyl exponential sums `(1 / N) ∑_{n < N} exp(2π i k u(n))` tend to `0`. -/
theorem weyl_criterion_iff (u : ℕ → ℝ) :
    IsEquidistributed u ↔
      ∀ k : ℤ, k ≠ 0 →
        Tendsto
          (fun N : ℕ =>
            (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * u n))
          atTop (nhds 0) :=
  ⟨fun hu _ hk => hu.weyl_sum_tendsto_zero hk, isEquidistributed_of_weyl_sum⟩

/-- Alias for `weyl_criterion_iff`. -/
theorem weyl_equidistribution_criterion (u : ℕ → ℝ) :
    IsEquidistributed u ↔
      ∀ k : ℤ, k ≠ 0 →
        Tendsto
          (fun N : ℕ =>
            (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * u n))
          atTop (nhds 0) :=
  weyl_criterion_iff u

/-- Translating an equidistributed sequence by a constant preserves equidistribution. -/
theorem IsEquidistributed.add_const {u : ℕ → ℝ} (hu : IsEquidistributed u) (c : ℝ) :
    IsEquidistributed (fun n => u n + c) := by
  rw [weyl_criterion_iff] at hu ⊢
  intro k hk
  have heq : (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * k * ((u n + c : ℝ) : ℂ))) =
      fun N : ℕ => weylExp k c * ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * k * u n)) := by
    funext N
    have hterm : ∀ n : ℕ, Complex.exp (2 * Real.pi * Complex.I * k * ((u n + c : ℝ) : ℂ)) =
        weylExp k c * Complex.exp (2 * Real.pi * Complex.I * k * u n) := by
      intro n
      change weylExp k (u n + c) = weylExp k c * weylExp k (u n)
      rw [weylExp_add, mul_comm]
    simp_rw [hterm, ← Finset.mul_sum]
    ring
  rw [heq]
  simpa using (hu k hk).const_mul (weylExp k c)

/-!
## Section 2: Weyl's Linear Rotation Theorem & Kronecker's Density Theorem
-/

lemma weylExp_ne_one_of_irrational {α : ℝ} (hα : Irrational α) {k : ℤ} (hk : k ≠ 0) :
    weylExp k α ≠ 1 := by
  intro heq
  unfold weylExp at heq
  rw [Complex.exp_eq_one_iff] at heq
  rcases heq with ⟨m, hm⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hmul : (k : ℂ) * (α : ℂ) = (m : ℂ) := by
    apply mul_left_cancel₀ hpi
    linear_combination hm
  have hreal : (k : ℝ) * α = (m : ℝ) := by
    have := congrArg Complex.re hmul
    simpa using this
  have hrat : α = ((m : ℚ) / (k : ℚ) : ℝ) := by
    have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    push_cast
    exact eq_div_of_mul_eq hkR (by linarith)
  exact hα ⟨(m : ℚ) / (k : ℚ), by simpa using hrat.symm⟩

/-- Geometric series bound for linear Weyl sums: `‖∑_{n < N} e(k n α)‖ ≤ 2 / ‖e(k α) - 1‖`. -/
theorem weyl_exp_sum_linear_bound {α : ℝ} (hα : Irrational α) {k : ℤ} (hk : k ≠ 0) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * (((n : ℝ) * α : ℝ) : ℂ))‖ ≤
      2 / ‖weylExp k α - 1‖ := by
  set z : ℂ := weylExp k α
  have hz_ne : z ≠ 1 := weylExp_ne_one_of_irrational hα hk
  have hz_sub_ne : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne
  have hpow : ∀ n : ℕ, Complex.exp (2 * Real.pi * Complex.I * k * (((n : ℝ) * α : ℝ) : ℂ)) = z ^ n := by
    intro n
    change weylExp k ((n : ℝ) * α) = (weylExp k α) ^ n
    unfold weylExp
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  simp_rw [hpow]
  rw [geom_sum_eq hz_ne N, norm_div]
  have hnum : ‖z ^ N - 1‖ ≤ 2 := by
    calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖z‖ ^ N + 1 := by rw [norm_pow, norm_one]
      _ = 1 ^ N + 1 := by rw [norm_weylExp]
      _ = 2 := by norm_num
  gcongr

/-- **Weyl's Equidistribution of Linear Rotations**:
For every irrational `α`, the sequence `n ↦ n · α` is equidistributed modulo `1`. -/
theorem weyl_equidistributed_linear_of_irrational {α : ℝ} (hα : Irrational α) :
    IsEquidistributed (fun n : ℕ => (n : ℝ) * α) := by
  rw [weyl_criterion_iff]
  intro k hk
  rw [tendsto_zero_iff_norm_tendsto_zero]
  set C : ℝ := 2 / ‖weylExp k α - 1‖
  have hzero : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hzero
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  by_cases hN : N = 0
  · subst hN; simp
  · have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    calc (1 / (N : ℝ)) *
            ‖∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * (((n : ℝ) * α : ℝ) : ℂ))‖
        ≤ (1 / (N : ℝ)) * C := by
          gcongr; exact weyl_exp_sum_linear_bound hα hk N
      _ = C / (N : ℝ) := by ring

/-- Affine rotation `n ↦ n · α + β` is equidistributed modulo `1` for every irrational `α`. -/
theorem weyl_equidistributed_affine_of_irrational {α : ℝ} (hα : Irrational α) (β : ℝ) :
    IsEquidistributed (fun n : ℕ => (n : ℝ) * α + β) :=
  (weyl_equidistributed_linear_of_irrational hα).add_const β

/-- Every nonempty subinterval `[a, b) ⊆ [0, 1]` contains `Int.fract (n * α)` for some `n : ℕ`. -/
theorem kronecker_exists_in_Ico {α : ℝ} (hα : Irrational α) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ n : ℕ, a ≤ Int.fract ((n : ℝ) * α) ∧ Int.fract ((n : ℝ) * α) < b := by
  have hlim := weyl_equidistributed_linear_of_irrational hα a b ha (le_of_lt hab) hb
  have hev : ∀ᶠ N : ℕ in atTop,
      0 < (((Finset.range N).filter
        (fun n : ℕ => a ≤ Int.fract ((n : ℝ) * α) ∧ Int.fract ((n : ℝ) * α) < b)).card : ℝ) /
        (N : ℝ) :=
    hlim.eventually (Ioi_mem_nhds (sub_pos.mpr hab))
  obtain ⟨N, hNpos⟩ := hev.exists
  have hcard_pos : 0 < ((Finset.range N).filter
      (fun n : ℕ => a ≤ Int.fract ((n : ℝ) * α) ∧ Int.fract ((n : ℝ) * α) < b)).card := by
    by_contra h0
    push Not at h0
    have h0' : ((Finset.range N).filter
        (fun n : ℕ => a ≤ Int.fract ((n : ℝ) * α) ∧ Int.fract ((n : ℝ) * α) < b)).card = 0 :=
      Nat.le_zero.mp h0
    rw [h0'] at hNpos
    simp at hNpos
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hcard_pos
  exact ⟨n, (Finset.mem_filter.mp hn).2⟩

/-- **Kronecker's Density Theorem (Metric Form)**:
For every irrational `α`, the fractional parts `{ Int.fract (n * α) | n : ℕ }` are dense in
`[0, 1]`. -/
theorem kronecker_density_irrational {α : ℝ} (hα : Irrational α) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ ε > 0, ∃ n : ℕ, |Int.fract ((n : ℝ) * α) - x| < ε := by
  intro x ⟨hx0, hx1⟩ ε hε
  by_cases hx1' : x = 1
  · subst hx1'
    set a : ℝ := max 0 (1 - ε / 2)
    have ha0 : 0 ≤ a := le_max_left _ _
    have ha1 : a < 1 := max_lt (by norm_num) (by linarith)
    obtain ⟨n, hn1, hn2⟩ := kronecker_exists_in_Ico hα ha0 ha1 le_rfl
    refine ⟨n, ?_⟩
    rw [abs_lt]
    have h1 : 1 - ε / 2 ≤ a := le_max_right _ _
    constructor <;> linarith
  · set b : ℝ := min 1 (x + ε)
    have hxb : x < b := lt_min (lt_of_le_of_ne hx1 hx1') (by linarith)
    have hb1 : b ≤ 1 := min_le_left _ _
    obtain ⟨n, hn1, hn2⟩ := kronecker_exists_in_Ico hα hx0 hxb hb1
    refine ⟨n, ?_⟩
    rw [abs_lt]
    have h1 : b ≤ x + ε := min_le_right _ _
    constructor <;> linarith

/-- **Kronecker's Density Theorem (Topological Closure Form)**:
For every irrational `α`, `closure (Set.range (fun n : ℕ => Int.fract (n * α))) = [0, 1]`. -/
theorem kronecker_closure_eq_Icc {α : ℝ} (hα : Irrational α) :
    closure (Set.range (fun n : ℕ => Int.fract ((n : ℝ) * α))) = Set.Icc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · exact closure_minimal (by rintro _ ⟨n, rfl⟩; exact ⟨Int.fract_nonneg _, le_of_lt (Int.fract_lt_one _)⟩)
      isClosed_Icc
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := kronecker_density_irrational hα x hx ε hε
    exact ⟨Int.fract ((n : ℝ) * α), ⟨n, rfl⟩, by simpa [Real.dist_eq, abs_sub_comm] using hn⟩

/-!
## Section 3: van der Corput's Difference Theorem & Weyl's Polynomial Equidistribution
-/

/-- **van der Corput's Fundamental Inequality**:
For any sequence `z : ℕ → ℂ` with `‖z n‖ = 1` and integers `N, H ≥ 1`,
`H² · ‖∑_{n < N} z n‖² ≤ (N + H) · (H · N + 2 · ∑_{r=1}^{H-1} (H - r) · ‖∑_{n < N - r} z(n+r) · conj(z n)‖)`. -/
theorem van_der_corput_inequality (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ = 1) (N H : ℕ) (hH : 1 ≤ H) :
    ((H : ℝ) ^ 2) * ‖∑ n ∈ Finset.range N, z n‖ ^ 2 ≤
      ((N + H : ℕ) : ℝ) *
        ((H : ℝ) * (N : ℝ) +
          2 * ∑ r ∈ Finset.Ico 1 H,
            ((H - r : ℕ) : ℝ) * ‖∑ n ∈ Finset.range (N - r), z (n + r) * star (z n)‖) := by
  -- Padded sequence `g t = z (t - H)` for `H ≤ t < N + H`, else `0`
  let g : ℕ → ℂ := fun t => if H ≤ t ∧ t < N + H then z (t - H) else 0
  have hg_shift' : ∀ h < H, ∑ m ∈ Finset.range (N + H), g (m + h) = ∑ n ∈ Finset.range N, z n := by
    intro h hh
    have hfilt : (Finset.range (N + H)).filter (fun m => H ≤ m + h ∧ m + h < N + H) =
        Finset.Ico (H - h) (N + H - h) := by
      ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    simp only [g, Finset.sum_ite, Finset.sum_const_zero, add_zero, hfilt]
    refine Finset.sum_bij (fun m _ => m + h - H) ?_ ?_ ?_ ?_
    · intro m hm; simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢; omega
    · intro m1 hm1 m2 hm2 heq; simp only [Finset.mem_Ico] at hm1 hm2; omega
    · intro n hn
      simp only [Finset.mem_range] at hn
      refine ⟨n + (H - h), ?_, ?_⟩
      · simp only [Finset.mem_Ico]; omega
      · omega
    · intro m _; rfl
  -- Step 1: `H * ∑_{n < N} z n = ∑_{m < N + H} ∑_{h < H} g (m + h)`
  have hsum_eq : (H : ℂ) * ∑ n ∈ Finset.range N, z n =
      ∑ m ∈ Finset.range (N + H), ∑ h ∈ Finset.range H, g (m + h) := by
    rw [Finset.sum_comm]
    have h1 : ∑ h ∈ Finset.range H, ∑ m ∈ Finset.range (N + H), g (m + h) =
        ∑ _h ∈ Finset.range H, ∑ n ∈ Finset.range N, z n :=
      Finset.sum_congr rfl fun h hh => hg_shift' h (Finset.mem_range.mp hh)
    rw [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Step 2: Cauchy–Schwarz on `m ∈ range (N + H)`
  have hcs : ((H : ℝ) ^ 2) * ‖∑ n ∈ Finset.range N, z n‖ ^ 2 ≤
      ((N + H : ℕ) : ℝ) * ∑ m ∈ Finset.range (N + H), ‖∑ h ∈ Finset.range H, g (m + h)‖ ^ 2 := by
    have hnorm : ((H : ℝ) ^ 2) * ‖∑ n ∈ Finset.range N, z n‖ ^ 2 =
        ‖∑ m ∈ Finset.range (N + H), ∑ h ∈ Finset.range H, g (m + h)‖ ^ 2 := by
      rw [← hsum_eq, norm_mul, Complex.norm_natCast, mul_pow]
    rw [hnorm]
    have h1 : ‖∑ m ∈ Finset.range (N + H), ∑ h ∈ Finset.range H, g (m + h)‖ ≤
        ∑ m ∈ Finset.range (N + H), ‖∑ h ∈ Finset.range H, g (m + h)‖ := norm_sum_le _ _
    have h2 : (∑ m ∈ Finset.range (N + H), ‖∑ h ∈ Finset.range H, g (m + h)‖) ^ 2 ≤
        ((N + H : ℕ) : ℝ) * ∑ m ∈ Finset.range (N + H), ‖∑ h ∈ Finset.range H, g (m + h)‖ ^ 2 := by
      let a : ℕ → ℝ := fun m => ‖∑ h ∈ Finset.range H, g (m + h)‖
      have hsq_nn : 0 ≤ ∑ i ∈ Finset.range (N + H), ∑ j ∈ Finset.range (N + H), (a i - a j) ^ 2 :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hexp : ∑ i ∈ Finset.range (N + H), ∑ j ∈ Finset.range (N + H), (a i - a j) ^ 2 =
          2 * (((N + H : ℕ) : ℝ) * (∑ i ∈ Finset.range (N + H), a i ^ 2) -
            (∑ i ∈ Finset.range (N + H), a i) ^ 2) := by
        simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
        ring
      dsimp only [a] at hexp hsq_nn
      linarith
    exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2
  -- Step 3: Expand `∑_m ‖∑_h g (m + h)‖²` as a complex double sum and extract its real part
  have hexpand :
      ∑ m ∈ Finset.range (N + H), ‖∑ h ∈ Finset.range H, g (m + h)‖ ^ 2 =
      (∑ h₁ ∈ Finset.range H, ∑ h₂ ∈ Finset.range H,
        ∑ m ∈ Finset.range (N + H), g (m + h₁) * star (g (m + h₂))).re := by
    have hpt : ∀ m : ℕ, ‖∑ h ∈ Finset.range H, g (m + h)‖ ^ 2 =
        (∑ h₁ ∈ Finset.range H, ∑ h₂ ∈ Finset.range H, g (m + h₁) * star (g (m + h₂))).re := by
      intro m
      set S : ℂ := ∑ h ∈ Finset.range H, g (m + h)
      have hS : (S * star S).re = ‖S‖ ^ 2 := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      rw [← hS]
      congr 1
      dsimp only [S]
      rw [star_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h₁ _
      rw [Finset.mul_sum]
    simp_rw [hpt, ← Complex.re_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h₁ _
    rw [Finset.sum_comm]
  -- Step 4: Evaluate each inner sum `∑_{m < N + H} g (m + h₁) * star (g (m + h₂))`
  have hcorr : ∀ h₁ h₂ : ℕ, h₁ < H → h₂ < H → h₂ ≤ h₁ →
      ∑ m ∈ Finset.range (N + H), g (m + h₁) * star (g (m + h₂)) =
        ∑ n ∈ Finset.range (N - (h₁ - h₂)), z (n + (h₁ - h₂)) * star (z n) := by
    intro h₁ h₂ hh₁ hh₂ hle
    have hterm : ∀ m : ℕ, g (m + h₁) * star (g (m + h₂)) =
        if (H ≤ m + h₂ ∧ m + h₁ < N + H) then
          z (m + h₂ - H + (h₁ - h₂)) * star (z (m + h₂ - H))
        else 0 := by
      intro m
      dsimp only [g]
      by_cases hcond : H ≤ m + h₂ ∧ m + h₁ < N + H
      · rw [if_pos hcond, if_pos (by omega), if_pos (by omega)]
        congr 2; omega
      · rw [if_neg hcond]
        by_cases h1 : H ≤ m + h₁ ∧ m + h₁ < N + H
        · rw [if_pos h1, if_neg (by omega), star_zero, mul_zero]
        · rw [if_neg h1, zero_mul]
    simp_rw [hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hfilt : (Finset.range (N + H)).filter (fun m => H ≤ m + h₂ ∧ m + h₁ < N + H) =
        Finset.Ico (H - h₂) (N + H - h₁) := by
      ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [hfilt]
    refine Finset.sum_bij (fun m _ => m + h₂ - H) ?_ ?_ ?_ ?_
    · intro m hm; simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢; omega
    · intro m1 hm1 m2 hm2 heq; simp only [Finset.mem_Ico] at hm1 hm2; omega
    · intro n hn
      simp only [Finset.mem_range] at hn
      refine ⟨n + (H - h₂), ?_, ?_⟩
      · simp only [Finset.mem_Ico]; omega
      · omega
    · intro m _; rfl
  -- Step 5: Split `(h₁, h₂)` into `h₁ = h₂`, `h₁ > h₂`, `h₁ < h₂`
  have hdiag : ∀ h < H,
      (∑ m ∈ Finset.range (N + H), g (m + h) * star (g (m + h))).re = (N : ℝ) := by
    intro h hh
    rw [hcorr h h hh hh le_rfl, Nat.sub_self, Nat.sub_zero]
    simp only [add_zero]
    have h1 : ∀ n : ℕ, z n * star (z n) = 1 := by
      intro n
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz n]
      norm_num
    simp_rw [h1]
    simp
  have hsymm : ∀ h₁ h₂ : ℕ,
      (∑ m ∈ Finset.range (N + H), g (m + h₁) * star (g (m + h₂))).re =
      (∑ m ∈ Finset.range (N + H), g (m + h₂) * star (g (m + h₁))).re := by
    intro h₁ h₂
    have h1 : ∑ m ∈ Finset.range (N + H), g (m + h₁) * star (g (m + h₂)) =
        star (∑ m ∈ Finset.range (N + H), g (m + h₂) * star (g (m + h₁))) := by
      rw [star_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [star_mul, star_star, mul_comm]
    rw [h1, Complex.star_def, Complex.conj_re]
  -- Bound the real double sum cleanly
  have hbound_inner :
      (∑ h₁ ∈ Finset.range H, ∑ h₂ ∈ Finset.range H,
        ∑ m ∈ Finset.range (N + H), g (m + h₁) * star (g (m + h₂))).re ≤
      (H : ℝ) * (N : ℝ) +
        2 * ∑ r ∈ Finset.Ico 1 H,
          ((H - r : ℕ) : ℝ) * ‖∑ n ∈ Finset.range (N - r), z (n + r) * star (z n)‖ := by
    let F : ℕ → ℕ → ℝ := fun h₁ h₂ =>
      (∑ m ∈ Finset.range (N + H), g (m + h₁) * star (g (m + h₂))).re
    have hre : (∑ h₁ ∈ Finset.range H, ∑ h₂ ∈ Finset.range H,
        ∑ m ∈ Finset.range (N + H), g (m + h₁) * star (g (m + h₂))).re =
        ∑ p ∈ Finset.range H ×ˢ Finset.range H, F p.1 p.2 := by
      rw [Finset.sum_product]
      simp only [Complex.re_sum, F]
    rw [hre]
    -- Partition `range H ×ˢ range H` into `p.1 = p.2`, `p.2 < p.1`, `p.1 < p.2`
    let S := Finset.range H ×ˢ Finset.range H
    let S_eq := S.filter (fun p => p.1 = p.2)
    let S_gt := S.filter (fun p => p.2 < p.1)
    let S_lt := S.filter (fun p => p.1 < p.2)
    have hpart : ∑ p ∈ S, F p.1 p.2 =
        (∑ p ∈ S_eq, F p.1 p.2) + (∑ p ∈ S_gt, F p.1 p.2) + (∑ p ∈ S_lt, F p.1 p.2) := by
      have hd1 : Disjoint S_eq S_gt := by
        rw [Finset.disjoint_filter]; intro p _ h1 h2; omega
      have hd2 : Disjoint (S_eq ∪ S_gt) S_lt := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [Finset.mem_union, S_eq, S_gt, S_lt, Finset.mem_filter] at hp1 hp2
        omega
      have hu : (S_eq ∪ S_gt) ∪ S_lt = S := by
        ext p
        simp only [Finset.mem_union, S_eq, S_gt, S_lt, Finset.mem_filter]
        constructor
        · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
        · intro h
          rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
          · right; exact ⟨h, hlt⟩
          · left; left; exact ⟨h, heq⟩
          · left; right; exact ⟨h, hgt⟩
      rw [← hu, Finset.sum_union hd2, Finset.sum_union hd1]
    have hSeq : ∑ p ∈ S_eq, F p.1 p.2 = (H : ℝ) * (N : ℝ) := by
      have hbij : ∑ p ∈ S_eq, F p.1 p.2 = ∑ h ∈ Finset.range H, F h h := by
        refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
        · intro p hp; simp only [S_eq, S, Finset.mem_filter, Finset.mem_product] at hp; exact hp.1.1
        · intro p1 hp1 p2 hp2 heq
          simp only [S_eq, Finset.mem_filter] at hp1 hp2
          ext <;> omega
        · intro h hh
          refine ⟨(h, h), ?_, rfl⟩
          simp only [S_eq, S, Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨hh, hh⟩, trivial⟩
        · intro p hp
          simp only [S_eq, Finset.mem_filter] at hp
          rw [hp.2]
      rw [hbij]
      have : ∑ h ∈ Finset.range H, F h h = ∑ _h ∈ Finset.range H, (N : ℝ) :=
        Finset.sum_congr rfl fun h hh => hdiag h (Finset.mem_range.mp hh)
      rw [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hSlt_eq : ∑ p ∈ S_lt, F p.1 p.2 = ∑ p ∈ S_gt, F p.1 p.2 := by
      refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [S_lt, S_gt, S, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p1 _ p2 _ heq; ext <;> simp_all
      · intro p hp
        simp only [S_lt, S_gt, S, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨(p.2, p.1), ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩, rfl⟩
      · intro p _; exact hsymm p.1 p.2
    have hSgt_le : ∑ p ∈ S_gt, F p.1 p.2 ≤
        ∑ r ∈ Finset.Ico 1 H,
          ((H - r : ℕ) : ℝ) * ‖∑ n ∈ Finset.range (N - r), z (n + r) * star (z n)‖ := by
      -- Group `S_gt` by `r = p.1 - p.2 ∈ Ico 1 H`
      have hbi : ∑ p ∈ S_gt, F p.1 p.2 =
          ∑ r ∈ Finset.Ico 1 H, ∑ h₂ ∈ Finset.range (H - r), F (h₂ + r) h₂ := by
        rw [Finset.sum_sigma']
        refine Finset.sum_bij (fun p _ => ⟨p.1 - p.2, p.2⟩) ?_ ?_ ?_ ?_
        · intro p hp
          simp only [S_gt, S, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
            Finset.mem_sigma, Finset.mem_Ico] at hp ⊢
          omega
        · intro p1 hp1 p2 hp2 heq
          simp only [S_gt, Finset.mem_filter] at hp1 hp2
          have h1 : p1.1 - p1.2 = p2.1 - p2.2 := congrArg Sigma.fst heq
          have h2 : p1.2 = p2.2 := by
            have := congrArg Sigma.snd heq
            simpa using this
          ext <;> omega
        · intro q hq
          simp only [Finset.mem_sigma, Finset.mem_Ico, Finset.mem_range] at hq
          refine ⟨(q.2 + q.1, q.2), ?_, ?_⟩
          · simp only [S_gt, S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            omega
          · ext <;> simp
        · intro p hp
          simp only [S_gt, Finset.mem_filter] at hp
          have : p.2 + (p.1 - p.2) = p.1 := by omega
          rw [this]
      rw [hbi]
      apply Finset.sum_le_sum
      intro r hr
      simp only [Finset.mem_Ico] at hr
      calc ∑ h₂ ∈ Finset.range (H - r), F (h₂ + r) h₂
          ≤ ∑ _h₂ ∈ Finset.range (H - r),
              ‖∑ n ∈ Finset.range (N - r), z (n + r) * star (z n)‖ := by
            apply Finset.sum_le_sum
            intro h₂ hh₂
            simp only [Finset.mem_range] at hh₂
            dsimp only [F]
            rw [hcorr (h₂ + r) h₂ (by omega) (by omega) (by omega)]
            have hsub : h₂ + r - h₂ = r := by omega
            rw [hsub]
            exact Complex.re_le_norm _
        _ = ((H - r : ℕ) : ℝ) * ‖∑ n ∈ Finset.range (N - r), z (n + r) * star (z n)‖ := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hpart, hSeq, hSlt_eq]
    linarith
  calc ((H : ℝ) ^ 2) * ‖∑ n ∈ Finset.range N, z n‖ ^ 2
      ≤ ((N + H : ℕ) : ℝ) * ∑ m ∈ Finset.range (N + H), ‖∑ h ∈ Finset.range H, g (m + h)‖ ^ 2 := hcs
    _ = ((N + H : ℕ) : ℝ) *
          (∑ h₁ ∈ Finset.range H, ∑ h₂ ∈ Finset.range H,
            ∑ m ∈ Finset.range (N + H), g (m + h₁) * star (g (m + h₂))).re := by rw [hexpand]
    _ ≤ ((N + H : ℕ) : ℝ) *
          ((H : ℝ) * (N : ℝ) +
            2 * ∑ r ∈ Finset.Ico 1 H,
              ((H - r : ℕ) : ℝ) * ‖∑ n ∈ Finset.range (N - r), z (n + r) * star (z n)‖) := by
        gcongr

/-- **van der Corput's Fundamental Difference Theorem**:
If `u (n + h) - u n` is equidistributed modulo `1` for every `h ≥ 1`, then `u` is
equidistributed modulo `1`. -/
theorem van_der_corput_difference_theorem {u : ℕ → ℝ}
    (hdiff : ∀ h : ℕ, 1 ≤ h → IsEquidistributed (fun n => u (n + h) - u n)) :
    IsEquidistributed u := by
  rw [weyl_criterion_iff]
  intro k hk
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨H, hH_gt⟩ := exists_nat_gt (4 / ε ^ 2)
  have hH1 : 1 ≤ H := by
    by_contra h0; push Not at h0
    have hH0 : H = 0 := Nat.lt_one_iff.mp h0
    subst hH0
    have : (0 : ℝ) < 4 / ε ^ 2 := by positivity
    linarith
  have hHpos : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr hH1
  -- For each `r ∈ Ico 1 H`, `(1 / N) * ‖∑_{n < N - r} e(k (u(n+r) - u n))‖ → 0`
  have hcorr_zero : ∀ r : ℕ, 1 ≤ r →
      Tendsto
        (fun N : ℕ =>
          ‖∑ n ∈ Finset.range (N - r),
            weylExp k (u (n + r)) * star (weylExp k (u n))‖ / (N : ℝ))
        atTop (nhds 0) := by
    intro r hr
    have hr_weyl := (hdiff r hr).weyl_sum_tendsto_zero hk
    have hr_norm : Tendsto
        (fun N : ℕ =>
          ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
            weylExp k (u (n + r) - u n)‖)
        atTop (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mp hr_weyl
    have htail : Tendsto (fun N : ℕ => (r : ℝ) / (N : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hsum_lim : Tendsto
        (fun N : ℕ =>
          ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
            weylExp k (u (n + r) - u n)‖ + (r : ℝ) / (N : ℝ))
        atTop (nhds 0) := by simpa using hr_norm.add htail
    refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hsum_lim
    filter_upwards [eventually_ge_atTop (r + 1)] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hrew : ∀ n : ℕ, weylExp k (u (n + r)) * star (weylExp k (u n)) =
        weylExp k (u (n + r) - u n) := fun n => (weylExp_sub k (u (n + r)) (u n)).symm
    simp_rw [hrew]
    have hsplit : ∑ n ∈ Finset.range N, weylExp k (u (n + r) - u n) =
        (∑ n ∈ Finset.range (N - r), weylExp k (u (n + r) - u n)) +
        (∑ n ∈ Finset.Ico (N - r) N, weylExp k (u (n + r) - u n)) := by
      have h1 := Finset.sum_range_add_sum_Ico
        (f := fun n => weylExp k (u (n + r) - u n))
        (show N - r ≤ N by omega)
      exact h1.symm
    have hsub : ‖∑ n ∈ Finset.range (N - r), weylExp k (u (n + r) - u n)‖ ≤
        ‖∑ n ∈ Finset.range N, weylExp k (u (n + r) - u n)‖ + (r : ℝ) := by
      have h1 : ∑ n ∈ Finset.range (N - r), weylExp k (u (n + r) - u n) =
          (∑ n ∈ Finset.range N, weylExp k (u (n + r) - u n)) -
          (∑ n ∈ Finset.Ico (N - r) N, weylExp k (u (n + r) - u n)) := by
        rw [hsplit]; ring
      rw [h1]
      calc ‖_ - _‖ ≤ ‖∑ n ∈ Finset.range N, _‖ + ‖∑ n ∈ Finset.Ico (N - r) N, _‖ := norm_sub_le _ _
        _ ≤ ‖∑ n ∈ Finset.range N, _‖ + ∑ n ∈ Finset.Ico (N - r) N,
              ‖weylExp k (u (n + r) - u n)‖ := by
            gcongr; exact norm_sum_le _ _
        _ = ‖∑ n ∈ Finset.range N, _‖ + (r : ℝ) := by
            have hunit : ∀ n, ‖weylExp k (u (n + r) - u n)‖ = 1 :=
              fun n => norm_weylExp k (u (n + r) - u n)
            simp only [hunit, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
            congr 1; exact_mod_cast (show N - (N - r) = r by omega)
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
    have hdiv : ‖∑ n ∈ Finset.range (N - r), weylExp k (u (n + r) - u n)‖ / (N : ℝ) ≤
        (‖∑ n ∈ Finset.range N, weylExp k (u (n + r) - u n)‖ + (r : ℝ)) / (N : ℝ) := by
      gcongr
    calc _ ≤ _ := hdiv
      _ = 1 / (N : ℝ) * ‖∑ n ∈ Finset.range N, _‖ + (r : ℝ) / (N : ℝ) := by ring
  -- Combine into the RHS limit `1 / H`
  let rhs : ℕ → ℝ := fun N =>
    (((N + H : ℕ) : ℝ) / (N : ℝ)) *
      (1 / (H : ℝ) +
        (2 / (H : ℝ) ^ 2) * ∑ r ∈ Finset.Ico 1 H,
          ((H - r : ℕ) : ℝ) *
            (‖∑ n ∈ Finset.range (N - r),
              weylExp k (u (n + r)) * star (weylExp k (u n))‖ / (N : ℝ)))
  have hrhs_tendsto : Tendsto rhs atTop (nhds (1 / (H : ℝ))) := by
    have hratio : Tendsto (fun N : ℕ => ((N + H : ℕ) : ℝ) / (N : ℝ)) atTop (nhds 1) := by
      have h1 : Tendsto (fun N : ℕ => 1 + (H : ℝ) / (N : ℝ)) atTop (nhds (1 + 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
      rw [add_zero] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast; field_simp [hN0]
    have hsum0 : Tendsto (fun N : ℕ =>
        ∑ r ∈ Finset.Ico 1 H,
          ((H - r : ℕ) : ℝ) *
            (‖∑ n ∈ Finset.range (N - r),
              weylExp k (u (n + r)) * star (weylExp k (u n))‖ / (N : ℝ)))
        atTop (nhds 0) := by
      have := tendsto_finsetSum (Finset.Ico 1 H) fun r hr =>
        (hcorr_zero r (Finset.mem_Ico.mp hr).1).const_mul ((H - r : ℕ) : ℝ)
      simpa using this
    have hinner : Tendsto (fun N : ℕ =>
        1 / (H : ℝ) + (2 / (H : ℝ) ^ 2) * ∑ r ∈ Finset.Ico 1 H,
          ((H - r : ℕ) : ℝ) *
            (‖∑ n ∈ Finset.range (N - r),
              weylExp k (u (n + r)) * star (weylExp k (u n))‖ / (N : ℝ)))
        atTop (nhds (1 / (H : ℝ))) := by
      simpa using (tendsto_const_nhds (x := 1 / (H : ℝ))).add
        (hsum0.const_mul (2 / (H : ℝ) ^ 2))
    simpa [rhs] using hratio.mul hinner
  have h1H_lt : 1 / (H : ℝ) < ε ^ 2 := by
    rw [div_lt_iff₀ hHpos]
    have h1 := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)).mp hH_gt
    linarith
  have hev := hrhs_tendsto.eventually (Iio_mem_nhds h1H_lt)
  rw [eventually_atTop] at hev
  obtain ⟨N0, hN0⟩ := hev
  refine ⟨max N0 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hvdc := van_der_corput_inequality (fun n => weylExp k (u n)) (fun n => norm_weylExp k (u n))
    N H hH1
  have hsq_le : ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I * k * u n)‖ ^ 2 ≤ rhs N := by
    have hrew : ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * u n) =
        ∑ n ∈ Finset.range N, weylExp k (u n) := rfl
    rw [hrew, norm_mul, norm_div, norm_one, Complex.norm_natCast, mul_pow]
    have hden_pos : (0 : ℝ) < (H : ℝ) ^ 2 * (N : ℝ) ^ 2 := by positivity
    rw [show (1 / (N : ℝ)) ^ 2 * ‖∑ n ∈ Finset.range N, weylExp k (u n)‖ ^ 2 =
        ((H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, weylExp k (u n)‖ ^ 2) / ((H : ℝ) ^ 2 * (N : ℝ) ^ 2) by
      field_simp [ne_of_gt hHpos, ne_of_gt hNpos]]
    calc ((H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, weylExp k (u n)‖ ^ 2) / ((H : ℝ) ^ 2 * (N : ℝ) ^ 2)
        ≤ (((N + H : ℕ) : ℝ) *
            ((H : ℝ) * (N : ℝ) +
              2 * ∑ r ∈ Finset.Ico 1 H,
                ((H - r : ℕ) : ℝ) *
                  ‖∑ n ∈ Finset.range (N - r), weylExp k (u (n + r)) * star (weylExp k (u n))‖)) /
            ((H : ℝ) ^ 2 * (N : ℝ) ^ 2) := by gcongr
      _ = rhs N := by
          dsimp only [rhs]
          rw [Finset.mul_sum, Finset.mul_sum]
          have hH0 : (H : ℝ) ≠ 0 := ne_of_gt hHpos
          have hN0' : (N : ℝ) ≠ 0 := ne_of_gt hNpos
          rw [mul_add, ← Finset.mul_sum, ← Finset.mul_sum]
          have hsimp : ∑ r ∈ Finset.Ico 1 H,
              ((H - r : ℕ) : ℝ) *
                (‖∑ n ∈ Finset.range (N - r), weylExp k (u (n + r)) * star (weylExp k (u n))‖ /
                  (N : ℝ)) =
              (∑ r ∈ Finset.Ico 1 H,
                ((H - r : ℕ) : ℝ) *
                  ‖∑ n ∈ Finset.range (N - r), weylExp k (u (n + r)) * star (weylExp k (u n))‖) /
                (N : ℝ) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro r _; ring
          rw [hsimp]
          field_simp [hH0, hN0']
  have hsq_lt : ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I * k * u n)‖ ^ 2 < ε ^ 2 :=
    lt_of_le_of_lt hsq_le (hN0 N (le_trans (le_max_left _ _) hN))
  rw [dist_zero_right]
  nlinarith [norm_nonneg ((1 / (N : ℂ)) * ∑ n ∈ Finset.range N,
    Complex.exp (2 * Real.pi * Complex.I * k * u n))]

/-- Finite-difference degree and leading-coefficient formula for polynomials over `ℝ`:
if `P.natDegree = d + 1` and `h ≠ 0`, then `Q(X) = P(X + h) - P(X)` has `Q.natDegree = d` and
`Q.leadingCoeff = ((d + 1) * h) * P.leadingCoeff`. -/
lemma poly_finite_diff_natDegree_leadingCoeff (P : Polynomial ℝ) (d : ℕ) (hd : P.natDegree = d + 1)
    {h : ℝ} (hh : h ≠ 0) :
    let Q : Polynomial ℝ := P.comp (Polynomial.X + Polynomial.C h) - P
    Q.natDegree = d ∧ Q.leadingCoeff = ((d + 1 : ℕ) : ℝ) * h * P.leadingCoeff := by
  intro Q
  have hPne : P ≠ 0 := by
    intro h0; subst h0; simp at hd
  have hcoeff_top : P.coeff (d + 1) ≠ 0 := by
    rw [← hd]; exact Polynomial.leadingCoeff_ne_zero.mpr hPne
  -- Compute `Q.coeff k` for `k ≥ d` using `P = ∑ i ∈ range (d + 2), C (P.coeff i) * X ^ i`
  have hPsum : P = ∑ i ∈ Finset.range (d + 2), Polynomial.C (P.coeff i) * Polynomial.X ^ i := by
    conv_lhs => rw [Polynomial.as_sum_range' P (d + 2) (by omega)]
    apply Finset.sum_congr rfl
    intro i _; exact (Polynomial.C_mul_X_pow_eq_monomial).symm
  have hQsum : Q = ∑ i ∈ Finset.range (d + 2),
      Polynomial.C (P.coeff i) * ((Polynomial.X + Polynomial.C h) ^ i - Polynomial.X ^ i) := by
    dsimp only [Q]
    conv_lhs => rw [hPsum]
    rw [Polynomial.sum_comp, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp, mul_sub]
  have hbin : ∀ i k : ℕ,
      ((Polynomial.X + Polynomial.C h) ^ i - Polynomial.X ^ i).coeff k =
        if k < i then h ^ (i - k) * (Nat.choose i k : ℝ) else 0 := by
    intro i k
    rw [Polynomial.coeff_sub, add_pow]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
    have hterm : ∀ j : ℕ,
        (Polynomial.X ^ j * Polynomial.C h ^ (i - j) * (i.choose j : Polynomial ℝ)).coeff k =
          if k = j then h ^ (i - j) * (i.choose j : ℝ) else 0 := by
      intro j
      have heq : Polynomial.X ^ j * Polynomial.C h ^ (i - j) * (i.choose j : Polynomial ℝ) =
          Polynomial.C (h ^ (i - j) * (i.choose j : ℝ)) * Polynomial.X ^ j := by
        rw [Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_eq_natCast]
        ring
      rw [heq, Polynomial.coeff_C_mul_X_pow]
    simp_rw [hterm]
    by_cases hki : k < i
    · rw [if_pos hki, if_neg (ne_of_lt hki), sub_zero]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk; rw [if_neg (Ne.symm hjk)]
      · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem
    · by_cases hkeq : k = i
      · subst hkeq
        rw [if_neg (lt_irrefl _), if_pos rfl]
        rw [Finset.sum_eq_single k]
        · simp
        · intro j _ hjk; rw [if_neg (Ne.symm hjk)]
        · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem
      · have hgt : i < k := by omega
        rw [if_neg hki, if_neg (ne_of_gt hgt), sub_zero]
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.mem_range] at hj
        rw [if_neg (by omega)]
  have hQcoeff_gt : ∀ k : ℕ, d < k → Q.coeff k = 0 := by
    intro k hk
    rw [hQsum, Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Polynomial.coeff_C_mul, hbin i k, if_neg (by omega), mul_zero]
  have hQcoeff_d : Q.coeff d = ((d + 1 : ℕ) : ℝ) * h * P.leadingCoeff := by
    rw [hQsum, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single (d + 1)]
    · rw [Polynomial.coeff_C_mul, hbin (d + 1) d, if_pos (by omega)]
      simp only [Nat.add_sub_cancel_left, pow_one, Nat.choose_succ_self_right]
      rw [← hd, Polynomial.coeff_natDegree]
      ring
    · intro i hi hine
      rw [Finset.mem_range] at hi
      rw [Polynomial.coeff_C_mul, hbin i d, if_neg (by omega), mul_zero]
    · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem
  have hQd_ne : Q.coeff d ≠ 0 := by
    rw [hQcoeff_d]
    have h1 : (((d + 1 : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
    have h2 : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hPne
    exact mul_ne_zero (mul_ne_zero h1 hh) h2
  have hdeg_le : Q.natDegree ≤ d := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    exact hQcoeff_gt
  have hdeg_ge : d ≤ Q.natDegree := Polynomial.le_natDegree_of_ne_zero hQd_ne
  have hdeg : Q.natDegree = d := le_antisymm hdeg_le hdeg_ge
  refine ⟨hdeg, ?_⟩
  rw [Polynomial.leadingCoeff, hdeg, hQcoeff_d]

/-- **Weyl's Polynomial Equidistribution Theorem**:
For every polynomial `P ∈ ℝ[X]` of degree `d ≥ 1` with irrational leading coefficient,
`n ↦ P(n)` is equidistributed modulo `1`. -/
theorem weyl_equidistributed_polynomial (P : Polynomial ℝ) (hd : 1 ≤ P.natDegree)
    (hlead : Irrational P.leadingCoeff) :
    IsEquidistributed (fun n : ℕ => P.eval (n : ℝ)) := by
  -- Induction on `d = P.natDegree - 1`
  obtain ⟨d, hd_eq⟩ : ∃ d : ℕ, P.natDegree = d + 1 := ⟨P.natDegree - 1, by omega⟩
  induction d generalizing P with
  | zero =>
    -- Degree 1: `P(x) = a * x + b` with `Irrational a`
    have hP1 : P.natDegree = 1 := hd_eq
    have heval : ∀ n : ℕ, P.eval (n : ℝ) = (n : ℝ) * P.leadingCoeff + P.coeff 0 := by
      intro n
      have hPsum : P = Polynomial.C (P.coeff 0) + Polynomial.C (P.coeff 1) * Polynomial.X := by
        rw [Polynomial.as_sum_range_C_mul_X_pow P, hP1]
        simp [Finset.sum_range_succ]
      conv_lhs => rw [hPsum]
      simp [Polynomial.leadingCoeff, hP1]
      ring
    simp_rw [heval]
    exact weyl_equidistributed_affine_of_irrational hlead (P.coeff 0)
  | succ d ih =>
    apply van_der_corput_difference_theorem
    intro h hh
    let Q : Polynomial ℝ := P.comp (Polynomial.X + Polynomial.C (h : ℝ)) - P
    have hQ := poly_finite_diff_natDegree_leadingCoeff P (d + 1) hd_eq
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hh))
    have hQ_lead_irr : Irrational Q.leadingCoeff := by
      rw [hQ.2]
      have hmul_eq : ((d + 1 + 1 : ℕ) : ℝ) * (h : ℝ) * P.leadingCoeff =
          (((d + 2) * h : ℕ) : ℝ) * P.leadingCoeff := by
        push_cast; ring
      rw [hmul_eq]
      exact hlead.natCast_mul (Nat.mul_ne_zero (Nat.succ_ne_zero _) (Nat.ne_of_gt hh))
    have hQ_eq : (fun n : ℕ => P.eval ((n + h : ℕ) : ℝ) - P.eval (n : ℝ)) =
        fun n : ℕ => Q.eval (n : ℝ) := by
      funext n
      dsimp only [Q]
      simp [Polynomial.eval_comp]
    rw [hQ_eq]
    exact ih Q (by rw [hQ.1]; omega) hQ_lead_irr hQ.1

/-- **Weyl's Quadratic Equidistribution Theorem**:
For every irrational `α` and real `β, γ`, `n ↦ α n² + β n + γ` is equidistributed modulo `1`. -/
theorem weyl_equidistributed_quadratic {α : ℝ} (hα : Irrational α) (β γ : ℝ) :
    IsEquidistributed (fun n : ℕ => α * (n : ℝ) ^ 2 + β * (n : ℝ) + γ) := by
  let P : Polynomial ℝ :=
    Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C γ
  have hα_ne : α ≠ 0 := hα.ne_zero
  have hdeg : P.natDegree = 2 := by
    have h1 : (Polynomial.C α * Polynomial.X ^ 2).natDegree = 2 := by
      rw [Polynomial.natDegree_C_mul_X_pow 2 α hα_ne]
    have h2 : (Polynomial.C β * Polynomial.X + Polynomial.C γ).natDegree ≤ 1 := by
      calc (Polynomial.C β * Polynomial.X + Polynomial.C γ).natDegree
          ≤ max (Polynomial.C β * Polynomial.X).natDegree (Polynomial.C γ).natDegree :=
            Polynomial.natDegree_add_le _ _
        _ ≤ max 1 0 := by
            gcongr
            · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)
            · simp
        _ = 1 := by norm_num
    have hP : P = Polynomial.C α * Polynomial.X ^ 2 +
        (Polynomial.C β * Polynomial.X + Polynomial.C γ) := by dsimp [P]; ring
    rw [hP, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by omega), h1]
  have hlead : P.leadingCoeff = α := by
    rw [Polynomial.leadingCoeff, hdeg]
    dsimp [P]
    simp [Polynomial.coeff_X_pow]
  have heval : (fun n : ℕ => α * (n : ℝ) ^ 2 + β * (n : ℝ) + γ) =
      fun n : ℕ => P.eval (n : ℝ) := by
    funext n; dsimp [P]; simp
  rw [heval]
  exact weyl_equidistributed_polynomial P (by omega) (hlead ▸ hα)

/-!
## Section 4: Dirichlet Simultaneous Approximation, Continued-Fraction Convergents,
Hurwitz's Optimal `1 / √5` Theorem, Golden Ratio Sharpness, & Liouville Transcendence
-/

/-- **Dirichlet's Simultaneous Diophantine Approximation Theorem**:
For any `d : ℕ`, `α : Fin d → ℝ`, and `Q ≥ 1`, there exist `1 ≤ q ≤ Q ^ d` and `p : Fin d → ℤ`
such that `|q · α i - p i| < 1 / Q` for every `i : Fin d`. -/
theorem dirichlet_approximation_simultaneous (d : ℕ) (α : Fin d → ℝ) (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ (q : ℕ) (p : Fin d → ℤ),
      1 ≤ q ∧ q ≤ Q ^ d ∧ ∀ i : Fin d, |(q : ℝ) * α i - (p i : ℝ)| < 1 / (Q : ℝ) := by
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  let box : Fin (Q ^ d + 1) → (Fin d → Fin Q) := fun k i =>
    ⟨⌊(Q : ℝ) * Int.fract ((k.val : ℝ) * α i)⌋₊, by
      rw [Nat.floor_lt (by positivity)]
      have h1 := Int.fract_lt_one ((k.val : ℝ) * α i)
      nlinarith⟩
  have hcard : Fintype.card (Fin d → Fin Q) < Fintype.card (Fin (Q ^ d + 1)) := by
    simp
  obtain ⟨k₁, k₂, hne, hbox⟩ := Fintype.exists_ne_map_eq_of_card_lt box hcard
  -- Order `k₁, k₂` as `a < b`
  obtain ⟨a, b, hab, hbox_ab⟩ :
      ∃ a b : Fin (Q ^ d + 1), a.val < b.val ∧ box a = box b := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact ⟨k₁, k₂, hlt, hbox⟩
    · exact ⟨k₂, k₁, hgt, hbox.symm⟩
  refine ⟨b.val - a.val, fun i => ⌊(b.val : ℝ) * α i⌋ - ⌊(a.val : ℝ) * α i⌋,
    by omega, by omega, fun i => ?_⟩
  have hbi : (box a i).val = (box b i).val := congrArg (fun f => (f i).val) hbox_ab
  dsimp only [box] at hbi
  set fa : ℝ := Int.fract ((a.val : ℝ) * α i)
  set fb : ℝ := Int.fract ((b.val : ℝ) * α i)
  set m : ℕ := ⌊(Q : ℝ) * fa⌋₊
  have hm_a1 : (m : ℝ) ≤ (Q : ℝ) * fa := Nat.floor_le (by positivity)
  have hm_a2 : (Q : ℝ) * fa < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hm_b1 : (m : ℝ) ≤ (Q : ℝ) * fb := by rw [hbi]; exact Nat.floor_le (by positivity)
  have hm_b2 : (Q : ℝ) * fb < (m : ℝ) + 1 := by rw [hbi]; exact Nat.lt_floor_add_one _
  have hdiff : ((b.val - a.val : ℕ) : ℝ) * α i -
      ((⌊(b.val : ℝ) * α i⌋ - ⌊(a.val : ℝ) * α i⌋ : ℤ) : ℝ) = fb - fa := by
    rw [Nat.cast_sub (le_of_lt hab)]
    push_cast
    dsimp only [fa, fb, Int.fract]
    ring
  rw [hdiff, abs_lt]
  have h1 : -1 < (Q : ℝ) * (fb - fa) := by nlinarith
  have h2 : (Q : ℝ) * (fb - fa) < 1 := by nlinarith
  constructor
  · rw [← neg_div, div_lt_iff₀' hQpos]; linarith
  · rw [lt_div_iff₀' hQpos]; linarith

/-!
### Regular Continued-Fraction Convergents for Irrational Numbers
-/

/-- The Gauss remainder sequence `x_0 = α`, `x_{n+1} = 1 / Int.fract (x_n)` for an irrational `α`. -/
noncomputable def cfRem (α : ℝ) : ℕ → ℝ
  | 0 => α
  | n + 1 => (Int.fract (cfRem α n))⁻¹

/-- The `n`-th partial quotient `a_n = ⌊x_n⌋` of `α`. -/
noncomputable def cfCoeff (α : ℝ) (n : ℕ) : ℤ := ⌊cfRem α n⌋

/-- Positive natural partial quotient `a_n` for `n ≥ 1` (`cfCoeffNat α n = ⌊x_n⌋₊`). -/
noncomputable def cfCoeffNat (α : ℝ) (n : ℕ) : ℕ := ⌊cfRem α n⌋₊

lemma irrational_sub_int_cast {x : ℝ} (hx : Irrational x) (m : ℤ) : Irrational (x - (m : ℝ)) := by
  rintro ⟨q, hq⟩
  exact hx ⟨q + m, by push_cast; linarith⟩

lemma irrational_inv_of_irrational {x : ℝ} (hx : Irrational x) : Irrational x⁻¹ := by
  rintro ⟨q, hq⟩
  exact hx ⟨q⁻¹, by rw [Rat.cast_inv, hq, inv_inv]⟩

lemma cfRem_irrational {α : ℝ} (hα : Irrational α) : ∀ n : ℕ, Irrational (cfRem α n)
  | 0 => hα
  | n + 1 => by
    have ih := cfRem_irrational hα n
    change Irrational (Int.fract (cfRem α n))⁻¹
    rw [Int.fract]
    exact irrational_inv_of_irrational (irrational_sub_int_cast ih ⌊cfRem α n⌋)

lemma cfRem_fract_pos {α : ℝ} (hα : Irrational α) (n : ℕ) : 0 < Int.fract (cfRem α n) := by
  have hnn := Int.fract_nonneg (cfRem α n)
  rcases eq_or_lt_of_le hnn with heq | hpos
  · exfalso
    have h1 : cfRem α n = (⌊cfRem α n⌋ : ℝ) := by
      have : Int.fract (cfRem α n) = cfRem α n - ⌊cfRem α n⌋ := rfl
      linarith
    exact (cfRem_irrational hα n).ne_int ⌊cfRem α n⌋ h1
  · exact hpos

lemma one_lt_cfRem_succ {α : ℝ} (hα : Irrational α) (n : ℕ) : 1 < cfRem α (n + 1) := by
  change 1 < (Int.fract (cfRem α n))⁻¹
  exact one_lt_inv₀ (cfRem_fract_pos hα n) |>.mpr (Int.fract_lt_one _)

lemma cfRem_eq_coeff_add_inv (α : ℝ) (n : ℕ) :
    cfRem α n = (cfCoeff α n : ℝ) + (cfRem α (n + 1))⁻¹ := by
  change cfRem α n = (⌊cfRem α n⌋ : ℝ) + ((Int.fract (cfRem α n))⁻¹)⁻¹
  rw [inv_inv, Int.fract]
  ring

lemma one_le_cfCoeffNat_succ {α : ℝ} (hα : Irrational α) (n : ℕ) :
    1 ≤ cfCoeffNat α (n + 1) := by
  unfold cfCoeffNat
  exact Nat.le_floor (by exact_mod_cast le_of_lt (one_lt_cfRem_succ hα n))

lemma cfCoeff_succ_eq_nat {α : ℝ} (hα : Irrational α) (n : ℕ) :
    cfCoeff α (n + 1) = (cfCoeffNat α (n + 1) : ℤ) := by
  unfold cfCoeff cfCoeffNat
  exact (Int.natCast_floor_eq_floor (by linarith [one_lt_cfRem_succ hα n])).symm

lemma cfCoeff_lt_cfRem {α : ℝ} (hα : Irrational α) (n : ℕ) :
    (cfCoeff α n : ℝ) < cfRem α n := by
  have h := cfRem_fract_pos hα n
  unfold cfCoeff
  rw [Int.fract] at h
  linarith

/-- Shifted convergent numerator sequence `P_{-1} = 1, P_0 = a_0, P_{n+1} = a_{n+1} P_n + P_{n-1}`
indexed by `k = n + 1` (`cfNumAux α 0 = 1`, `cfNumAux α 1 = a_0`, `cfNumAux α (n+2) = a_{n+1} * ...`). -/
noncomputable def cfNumAux (α : ℝ) : ℕ → ℤ
  | 0 => 1
  | 1 => cfCoeff α 0
  | n + 2 => cfCoeff α (n + 1) * cfNumAux α (n + 1) + cfNumAux α n

/-- Shifted convergent denominator sequence `Q_{-1} = 0, Q_0 = 1, Q_{n+1} = a_{n+1} Q_n + Q_{n-1}`
indexed by `k = n + 1`. -/
noncomputable def cfDenAux (α : ℝ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => cfCoeffNat α (n + 1) * cfDenAux α (n + 1) + cfDenAux α n

/-- The `n`-th regular continued-fraction convergent numerator `p_n ∈ ℤ`. -/
noncomputable def cfNum (α : ℝ) (n : ℕ) : ℤ := cfNumAux α (n + 1)

/-- The `n`-th regular continued-fraction convergent denominator `q_n ∈ ℕ`. -/
noncomputable def cfDen (α : ℝ) (n : ℕ) : ℕ := cfDenAux α (n + 1)

lemma cfDen_zero (α : ℝ) : cfDen α 0 = 1 := rfl
lemma cfDen_one (α : ℝ) : cfDen α 1 = cfCoeffNat α 1 := by
  simp [cfDen, cfDenAux]

lemma cfNum_recurrence (α : ℝ) (n : ℕ) :
    cfNum α (n + 2) = cfCoeff α (n + 2) * cfNum α (n + 1) + cfNum α n := rfl

lemma cfDen_recurrence (α : ℝ) (n : ℕ) :
    cfDen α (n + 2) = cfCoeffNat α (n + 2) * cfDen α (n + 1) + cfDen α n := rfl

lemma cfDen_pos {α : ℝ} (hα : Irrational α) : ∀ n : ℕ, 1 ≤ cfDen α n
  | 0 => le_rfl
  | 1 => by rw [cfDen_one]; exact one_le_cfCoeffNat_succ hα 0
  | n + 2 => by
    rw [cfDen_recurrence]
    have h1 := one_le_cfCoeffNat_succ hα (n + 1)
    have h2 := cfDen_pos hα (n + 1)
    have h3 := cfDen_pos hα n
    nlinarith

lemma cfDen_le_succ {α : ℝ} (hα : Irrational α) : ∀ n : ℕ, cfDen α n ≤ cfDen α (n + 1)
  | 0 => by rw [cfDen_zero, cfDen_one]; exact one_le_cfCoeffNat_succ hα 0
  | n + 1 => by
    rw [cfDen_recurrence]
    have h1 := one_le_cfCoeffNat_succ hα (n + 1)
    have h2 := cfDen_pos hα (n + 1)
    nlinarith

lemma cfDen_ge_fib {α : ℝ} (hα : Irrational α) : ∀ n : ℕ, Nat.fib (n + 1) ≤ cfDen α n
  | 0 => by simp [cfDen_zero]
  | 1 => by rw [cfDen_one]; simpa using one_le_cfCoeffNat_succ hα 0
  | n + 2 => by
    rw [cfDen_recurrence, Nat.fib_add_two]
    have h1 := one_le_cfCoeffNat_succ hα (n + 1)
    have ih1 := cfDen_ge_fib hα (n + 1)
    have ih0 := cfDen_ge_fib hα n
    nlinarith

lemma cfDen_ge_self {α : ℝ} (hα : Irrational α) : ∀ n : ℕ, n ≤ cfDen α n
  | 0 => by simp [cfDen_zero]
  | 1 => by rw [cfDen_one]; exact one_le_cfCoeffNat_succ hα 0
  | n + 2 => by
    rw [cfDen_recurrence]
    have h1 := one_le_cfCoeffNat_succ hα (n + 1)
    have ih1 := cfDen_ge_self hα (n + 1)
    have h0 := cfDen_pos hα n
    nlinarith

/-- **Continued-Fraction Determinant Identity**:
`p_{n+1} q_n - p_n q_{n+1} = (-1)^n` (equivalently `P_n Q_{n-1} - P_{n-1} Q_n = (-1)^{n-1}`). -/
theorem cf_determinant_aux {α : ℝ} (hα : Irrational α) :
    ∀ k : ℕ, cfNumAux α (k + 1) * (cfDenAux α k : ℤ) - cfNumAux α k * (cfDenAux α (k + 1) : ℤ) =
      (-1 : ℤ) ^ (k + 1)
  | 0 => by simp [cfNumAux, cfDenAux]
  | k + 1 => by
    have ih := cf_determinant_aux hα k
    change (cfCoeff α (k + 1) * cfNumAux α (k + 1) + cfNumAux α k) * (cfDenAux α (k + 1) : ℤ) -
      cfNumAux α (k + 1) * ((cfCoeffNat α (k + 1) * cfDenAux α (k + 1) + cfDenAux α k : ℕ) : ℤ) =
      (-1 : ℤ) ^ (k + 2)
    push_cast
    rw [← cfCoeff_succ_eq_nat hα k]
    calc _ = -(cfNumAux α (k + 1) * (cfDenAux α k : ℤ) -
              cfNumAux α k * (cfDenAux α (k + 1) : ℤ)) := by ring
      _ = -((-1 : ℤ) ^ (k + 1)) := by rw [ih]
      _ = (-1 : ℤ) ^ (k + 2) := by rw [pow_succ]; ring

theorem cf_determinant {α : ℝ} (hα : Irrational α) (n : ℕ) :
    cfNum α (n + 1) * (cfDen α n : ℤ) - cfNum α n * (cfDen α (n + 1) : ℤ) = (-1 : ℤ) ^ n := by
  have h := cf_determinant_aux hα (n + 1)
  change cfNum α (n + 1) * (cfDen α n : ℤ) - cfNum α n * (cfDen α (n + 1) : ℤ) =
    (-1 : ℤ) ^ (n + 2) at h
  rw [h, pow_add]
  norm_num

/-- Every continued-fraction convergent `p_n / q_n` is automatically in lowest terms. -/
theorem cf_coprime {α : ℝ} (hα : Irrational α) (n : ℕ) :
    Nat.Coprime (cfNum α n).natAbs (cfDen α n) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  set d := Nat.gcd (cfNum α n).natAbs (cfDen α n)
  have hd1 : (d : ℤ) ∣ cfNum α n := Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_left _ _)
  have hd2 : (d : ℤ) ∣ (cfDen α n : ℤ) := Int.ofNat_dvd.mpr (Nat.gcd_dvd_right _ _)
  have hdet := cf_determinant hα n
  have hd_pow : (d : ℤ) ∣ (-1 : ℤ) ^ n := by
    rw [← hdet]
    exact dvd_sub (dvd_mul_of_dvd_right hd2 _) (dvd_mul_of_dvd_left hd1 _)
  have hd_one : d ∣ 1 := by
    have := Int.natAbs_dvd_natAbs.mpr hd_pow
    simpa using this
  exact Nat.dvd_one.mp hd_one

/-- Exact continued-fraction value identity:
`α = (x_{n+1} · p_n + p_{n-1}) / (x_{n+1} · q_n + q_{n-1})`. -/
theorem cf_exact_value {α : ℝ} (hα : Irrational α) :
    ∀ n : ℕ,
      α = (cfRem α (n + 1) * (cfNumAux α (n + 1) : ℝ) + (cfNumAux α n : ℝ)) /
          (cfRem α (n + 1) * (cfDenAux α (n + 1) : ℝ) + (cfDenAux α n : ℝ))
  | 0 => by
    have hrem : α = (cfCoeff α 0 : ℝ) + (cfRem α 1)⁻¹ := cfRem_eq_coeff_add_inv α 0
    have hpos : 0 < cfRem α 1 := by linarith [one_lt_cfRem_succ hα 0]
    simp only [cfNumAux, cfDenAux, Int.cast_one, Nat.cast_one, Nat.cast_zero, mul_one, add_zero]
    conv_lhs => rw [hrem]
    field_simp [ne_of_gt hpos]
  | n + 1 => by
    have ih := cf_exact_value hα n
    have hrem := cfRem_eq_coeff_add_inv α (n + 1)
    have hr_pos : 0 < cfRem α (n + 2) := by linarith [one_lt_cfRem_succ hα (n + 1)]
    have hr_ne : cfRem α (n + 2) ≠ 0 := ne_of_gt hr_pos
    have hcn : (cfCoeffNat α (n + 1) : ℝ) = (cfCoeff α (n + 1) : ℝ) := by
      have := cfCoeff_succ_eq_nat hα n
      exact_mod_cast this.symm
    calc α = (cfRem α (n + 1) * (cfNumAux α (n + 1) : ℝ) + (cfNumAux α n : ℝ)) /
              (cfRem α (n + 1) * (cfDenAux α (n + 1) : ℝ) + (cfDenAux α n : ℝ)) := ih
      _ = (((cfCoeff α (n + 1) : ℝ) + (cfRem α (n + 2))⁻¹) * (cfNumAux α (n + 1) : ℝ) +
              (cfNumAux α n : ℝ)) /
          (((cfCoeff α (n + 1) : ℝ) + (cfRem α (n + 2))⁻¹) * (cfDenAux α (n + 1) : ℝ) +
              (cfDenAux α n : ℝ)) := by rw [hrem]
      _ = (cfRem α (n + 2) * (((cfCoeff α (n + 1) : ℝ) + (cfRem α (n + 2))⁻¹) *
              (cfNumAux α (n + 1) : ℝ) + (cfNumAux α n : ℝ))) /
          (cfRem α (n + 2) * (((cfCoeff α (n + 1) : ℝ) + (cfRem α (n + 2))⁻¹) *
              (cfDenAux α (n + 1) : ℝ) + (cfDenAux α n : ℝ))) :=
          (mul_div_mul_left _ _ hr_ne).symm
      _ = (cfRem α (n + 2) * ((cfCoeff α (n + 1) : ℝ) * (cfNumAux α (n + 1) : ℝ) +
              (cfNumAux α n : ℝ)) + (cfNumAux α (n + 1) : ℝ)) /
          (cfRem α (n + 2) * ((cfCoeff α (n + 1) : ℝ) * (cfDenAux α (n + 1) : ℝ) +
              (cfDenAux α n : ℝ)) + (cfDenAux α (n + 1) : ℝ)) := by
          congr 1
          · linear_combination (cfNumAux α (n + 1) : ℝ) * mul_inv_cancel₀ hr_ne
          · linear_combination (cfDenAux α (n + 1) : ℝ) * mul_inv_cancel₀ hr_ne
      _ = (cfRem α (n + 2) * (cfNumAux α (n + 2) : ℝ) + (cfNumAux α (n + 1) : ℝ)) /
          (cfRem α (n + 2) * (cfDenAux α (n + 2) : ℝ) + (cfDenAux α (n + 1) : ℝ)) := by
          change _ = (cfRem α (n + 2) *
              ((cfCoeff α (n + 1) * cfNumAux α (n + 1) + cfNumAux α n : ℤ) : ℝ) +
              (cfNumAux α (n + 1) : ℝ)) /
            (cfRem α (n + 2) *
              ((cfCoeffNat α (n + 1) * cfDenAux α (n + 1) + cfDenAux α n : ℕ) : ℝ) +
              (cfDenAux α (n + 1) : ℝ))
          push_cast; rw [hcn]

/-- **Exact Alternating Error Formula for Continued-Fraction Convergents**:
`α - p_n / q_n = (-1)^n / (q_n · (x_{n+1} · q_n + q_{n-1}))`. -/
theorem cf_error_formula {α : ℝ} (hα : Irrational α) (n : ℕ) :
    α - (cfNum α n : ℝ) / (cfDen α n : ℝ) =
      (-1 : ℝ) ^ n /
        ((cfDen α n : ℝ) * (cfRem α (n + 1) * (cfDen α n : ℝ) + (cfDenAux α n : ℝ))) := by
  conv_lhs => arg 1; rw [cf_exact_value hα n]
  change (cfRem α (n + 1) * (cfNum α n : ℝ) + (cfNumAux α n : ℝ)) /
      (cfRem α (n + 1) * (cfDen α n : ℝ) + (cfDenAux α n : ℝ)) -
      (cfNum α n : ℝ) / (cfDen α n : ℝ) = _
  have hqpos : 0 < (cfDen α n : ℝ) := by exact_mod_cast cfDen_pos hα n
  have hrpos : 0 < cfRem α (n + 1) := by linarith [one_lt_cfRem_succ hα n]
  have hden_pos : 0 < cfRem α (n + 1) * (cfDen α n : ℝ) + (cfDenAux α n : ℝ) := by
    have : (0 : ℝ) ≤ (cfDenAux α n : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hdet : (cfNumAux α n : ℝ) * (cfDen α n : ℝ) - (cfNum α n : ℝ) * (cfDenAux α n : ℝ) =
      (-1 : ℝ) ^ n := by
    have h := cf_determinant_aux hα n
    have hR : (cfNumAux α (n + 1) : ℝ) * (cfDenAux α n : ℝ) -
        (cfNumAux α n : ℝ) * (cfDenAux α (n + 1) : ℝ) = (-1 : ℝ) ^ (n + 1) := by
      exact_mod_cast h
    change (cfNum α n : ℝ) * (cfDenAux α n : ℝ) -
        (cfNumAux α n : ℝ) * (cfDen α n : ℝ) = (-1 : ℝ) ^ (n + 1) at hR
    rw [pow_succ] at hR
    linarith
  field_simp [ne_of_gt hqpos, ne_of_gt hden_pos]
  linear_combination hdet

/-- **Classical Continued-Fraction Convergent Bound**:
`|α - p_n / q_n| < 1 / (q_n · q_{n+1})` for every `n : ℕ`. -/
theorem cf_convergent_bound {α : ℝ} (hα : Irrational α) (n : ℕ) :
    |α - (cfNum α n : ℝ) / (cfDen α n : ℝ)| <
      1 / ((cfDen α n : ℝ) * (cfDen α (n + 1) : ℝ)) := by
  rw [cf_error_formula hα n, abs_div, abs_pow, abs_neg, abs_one, one_pow]
  have hqpos : 0 < (cfDen α n : ℝ) := by exact_mod_cast cfDen_pos hα n
  have hq1pos : 0 < (cfDen α (n + 1) : ℝ) := by exact_mod_cast cfDen_pos hα (n + 1)
  have hrpos : 0 < cfRem α (n + 1) := by linarith [one_lt_cfRem_succ hα n]
  have hden_pos : 0 < cfRem α (n + 1) * (cfDen α n : ℝ) + (cfDenAux α n : ℝ) := by
    have : (0 : ℝ) ≤ (cfDenAux α n : ℝ) := Nat.cast_nonneg _
    nlinarith
  rw [abs_of_pos (mul_pos hqpos hden_pos)]
  have hlt : (cfDen α (n + 1) : ℝ) < cfRem α (n + 1) * (cfDen α n : ℝ) + (cfDenAux α n : ℝ) := by
    have hrec : (cfDen α (n + 1) : ℝ) =
        (cfCoeff α (n + 1) : ℝ) * (cfDen α n : ℝ) + (cfDenAux α n : ℝ) := by
      have hcn : (cfCoeffNat α (n + 1) : ℝ) = (cfCoeff α (n + 1) : ℝ) := by
        have := cfCoeff_succ_eq_nat hα n
        exact_mod_cast this.symm
      change ((cfCoeffNat α (n + 1) * cfDenAux α (n + 1) + cfDenAux α n : ℕ) : ℝ) = _
      push_cast; rw [hcn]; rfl
    rw [hrec]
    have hclt := cfCoeff_lt_cfRem hα (n + 1)
    nlinarith
  exact one_div_lt_one_div_of_lt (mul_pos hqpos hq1pos) (by nlinarith)

/-- Adjacent convergent errors sum to exactly `1 / (q_n · q_{n+1})` because `α` lies strictly
between `p_n / q_n` and `p_{n+1} / q_{n+1}`. -/
lemma cf_adjacent_error_sum {α : ℝ} (hα : Irrational α) (n : ℕ) :
    |α - (cfNum α n : ℝ) / (cfDen α n : ℝ)| +
      |α - (cfNum α (n + 1) : ℝ) / (cfDen α (n + 1) : ℝ)| =
      1 / ((cfDen α n : ℝ) * (cfDen α (n + 1) : ℝ)) := by
  have hqn : 0 < (cfDen α n : ℝ) := by exact_mod_cast cfDen_pos hα n
  have hqn1 : 0 < (cfDen α (n + 1) : ℝ) := by exact_mod_cast cfDen_pos hα (n + 1)
  have he0 := cf_error_formula hα n
  have he1 := cf_error_formula hα (n + 1)
  have hden0 : 0 < (cfDen α n : ℝ) * (cfRem α (n + 1) * (cfDen α n : ℝ) + (cfDenAux α n : ℝ)) := by
    have hr : 0 < cfRem α (n + 1) := by linarith [one_lt_cfRem_succ hα n]
    have hnn : (0 : ℝ) ≤ (cfDenAux α n : ℝ) := Nat.cast_nonneg _
    exact mul_pos hqn (by nlinarith)
  have hden1 : 0 < (cfDen α (n + 1) : ℝ) *
      (cfRem α (n + 2) * (cfDen α (n + 1) : ℝ) + (cfDenAux α (n + 1) : ℝ)) := by
    have hr : 0 < cfRem α (n + 2) := by linarith [one_lt_cfRem_succ hα (n + 1)]
    have hnn : (0 : ℝ) ≤ (cfDenAux α (n + 1) : ℝ) := Nat.cast_nonneg _
    exact mul_pos hqn1 (by nlinarith)
  have hdet : (cfNum α (n + 1) : ℝ) / (cfDen α (n + 1) : ℝ) -
      (cfNum α n : ℝ) / (cfDen α n : ℝ) =
      (-1 : ℝ) ^ n / ((cfDen α n : ℝ) * (cfDen α (n + 1) : ℝ)) := by
    have hd : (cfNum α (n + 1) : ℝ) * (cfDen α n : ℝ) -
        (cfNum α n : ℝ) * (cfDen α (n + 1) : ℝ) = (-1 : ℝ) ^ n := by
      exact_mod_cast cf_determinant hα n
    field_simp [ne_of_gt hqn, ne_of_gt hqn1]
    linarith [hd]
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have hpow0 : (-1 : ℝ) ^ (m + m) = 1 := by rw [← two_mul, pow_mul]; norm_num
    have hpow1 : (-1 : ℝ) ^ (m + m + 1) = -1 := by rw [pow_succ, hpow0]; norm_num
    have hpos0 : 0 < α - (cfNum α (m + m) : ℝ) / (cfDen α (m + m) : ℝ) := by
      rw [he0, hpow0]; positivity
    have hneg1 : α - (cfNum α (m + m + 1) : ℝ) / (cfDen α (m + m + 1) : ℝ) < 0 := by
      rw [he1, hpow1]; exact div_neg_of_neg_of_pos (by norm_num) hden1
    rw [abs_of_pos hpos0, abs_of_neg hneg1]
    rw [hpow0] at hdet
    linarith
  · subst hm
    have hpow0 : (-1 : ℝ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have hpow1 : (-1 : ℝ) ^ (2 * m + 1 + 1) = 1 := by rw [pow_succ, hpow0]; norm_num
    have hneg0 : α - (cfNum α (2 * m + 1) : ℝ) / (cfDen α (2 * m + 1) : ℝ) < 0 := by
      rw [he0, hpow0]; exact div_neg_of_neg_of_pos (by norm_num) hden0
    have hpos1 : 0 < α - (cfNum α (2 * m + 1 + 1) : ℝ) / (cfDen α (2 * m + 1 + 1) : ℝ) := by
      rw [he1, hpow1]; positivity
    rw [abs_of_neg hneg0, abs_of_pos hpos1]
    rw [hpow0, neg_div] at hdet
    linarith

/-- Key algebraic lemma for Hurwitz's theorem: if `r = q₁ / q₀ ≥ 1` is rational and
`r + r⁻¹ ≤ √5`, then strictly `r < (1 + √5) / 2`. -/
lemma hurwitz_ratio_lt_goldenRatio {q₀ q₁ : ℕ} (hq0 : 1 ≤ q₀) (hle : q₀ ≤ q₁)
    (hsum : (q₁ : ℝ) / (q₀ : ℝ) + (q₀ : ℝ) / (q₁ : ℝ) ≤ Real.sqrt 5) :
    (q₁ : ℝ) / (q₀ : ℝ) < (1 + Real.sqrt 5) / 2 := by
  set x : ℝ := (q₁ : ℝ) / (q₀ : ℝ)
  have hq0pos : (0 : ℝ) < (q₀ : ℝ) := Nat.cast_pos.mpr hq0
  have hq1pos : (0 : ℝ) < (q₁ : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hq0 hle)
  have hx1 : 1 ≤ x := by dsimp [x]; rw [one_le_div hq0pos]; exact_mod_cast hle
  have hsq5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrt5_lt3 : Real.sqrt 5 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hquad : (x - (1 + Real.sqrt 5) / 2) * (x - (Real.sqrt 5 - 1) / 2) ≤ 0 := by
    have hmul : x * x + 1 ≤ Real.sqrt 5 * x := by
      have h1 : x + x⁻¹ ≤ Real.sqrt 5 := by
        simpa [x, inv_div] using hsum
      have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ x)
      rw [add_mul, inv_mul_cancel₀ (by positivity)] at h2
      exact h2
    nlinarith [hsq5]
  have hpos_factor : 0 < x - (Real.sqrt 5 - 1) / 2 := by linarith
  have hle_phi : x ≤ (1 + Real.sqrt 5) / 2 := by
    nlinarith
  have hne_phi : x ≠ (1 + Real.sqrt 5) / 2 := by
    intro heq
    refine Real.goldenRatio_irrational ⟨(q₁ : ℚ) / (q₀ : ℚ), ?_⟩
    rw [Real.goldenRatio, ← heq]
    dsimp [x]; push_cast; rfl
  exact lt_of_le_of_ne hle_phi hne_phi

/-- **Hurwitz's 3-Consecutive-Convergents Theorem (1891)**:
For every irrational `α` and every `n : ℕ`, at least one of the three consecutive convergents
`p_k / q_k` (`k ∈ {n, n + 1, n + 2}`) satisfies `|α - p_k / q_k| < 1 / (√5 · q_k²)`. -/
theorem hurwitz_three_consecutive_convergents {α : ℝ} (hα : Irrational α) (n : ℕ) :
    ∃ k : ℕ, (k = n ∨ k = n + 1 ∨ k = n + 2) ∧
      |α - (cfNum α k : ℝ) / (cfDen α k : ℝ)| < 1 / (Real.sqrt 5 * (cfDen α k : ℝ) ^ 2) := by
  by_contra h
  push Not at h
  have h0 := h n (Or.inl rfl)
  have h1 := h (n + 1) (Or.inr (Or.inl rfl))
  have h2 := h (n + 2) (Or.inr (Or.inr rfl))
  have hs5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hq0 : (0 : ℝ) < (cfDen α n : ℝ) := by exact_mod_cast cfDen_pos hα n
  have hq1 : (0 : ℝ) < (cfDen α (n + 1) : ℝ) := by exact_mod_cast cfDen_pos hα (n + 1)
  have hq2 : (0 : ℝ) < (cfDen α (n + 2) : ℝ) := by exact_mod_cast cfDen_pos hα (n + 2)
  -- From `(n, n + 1)`: `q_{n+1} / q_n + q_n / q_{n+1} ≤ √5`
  have hsum01 : (cfDen α (n + 1) : ℝ) / (cfDen α n : ℝ) +
      (cfDen α n : ℝ) / (cfDen α (n + 1) : ℝ) ≤ Real.sqrt 5 := by
    have hadj := cf_adjacent_error_sum hα n
    have hineq : 1 / (Real.sqrt 5 * (cfDen α n : ℝ) ^ 2) +
        1 / (Real.sqrt 5 * (cfDen α (n + 1) : ℝ) ^ 2) ≤
        1 / ((cfDen α n : ℝ) * (cfDen α (n + 1) : ℝ)) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hineq
      (by positivity : 0 ≤ Real.sqrt 5 * (cfDen α n : ℝ) * (cfDen α (n + 1) : ℝ))
    have hL : Real.sqrt 5 * (cfDen α n : ℝ) * (cfDen α (n + 1) : ℝ) *
        (1 / (Real.sqrt 5 * (cfDen α n : ℝ) ^ 2) +
         1 / (Real.sqrt 5 * (cfDen α (n + 1) : ℝ) ^ 2)) =
        (cfDen α (n + 1) : ℝ) / (cfDen α n : ℝ) + (cfDen α n : ℝ) / (cfDen α (n + 1) : ℝ) := by
      field_simp [ne_of_gt hs5, ne_of_gt hq0, ne_of_gt hq1]
    have hR : Real.sqrt 5 * (cfDen α n : ℝ) * (cfDen α (n + 1) : ℝ) *
        (1 / ((cfDen α n : ℝ) * (cfDen α (n + 1) : ℝ))) = Real.sqrt 5 := by
      field_simp [ne_of_gt hq0, ne_of_gt hq1]
    linarith
  -- From `(n + 1, n + 2)`: `q_{n+2} / q_{n+1} + q_{n+1} / q_{n+2} ≤ √5`
  have hsum12 : (cfDen α (n + 2) : ℝ) / (cfDen α (n + 1) : ℝ) +
      (cfDen α (n + 1) : ℝ) / (cfDen α (n + 2) : ℝ) ≤ Real.sqrt 5 := by
    have hadj := cf_adjacent_error_sum hα (n + 1)
    have hineq : 1 / (Real.sqrt 5 * (cfDen α (n + 1) : ℝ) ^ 2) +
        1 / (Real.sqrt 5 * (cfDen α (n + 2) : ℝ) ^ 2) ≤
        1 / ((cfDen α (n + 1) : ℝ) * (cfDen α (n + 2) : ℝ)) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hineq
      (by positivity : 0 ≤ Real.sqrt 5 * (cfDen α (n + 1) : ℝ) * (cfDen α (n + 2) : ℝ))
    have hL : Real.sqrt 5 * (cfDen α (n + 1) : ℝ) * (cfDen α (n + 2) : ℝ) *
        (1 / (Real.sqrt 5 * (cfDen α (n + 1) : ℝ) ^ 2) +
         1 / (Real.sqrt 5 * (cfDen α (n + 2) : ℝ) ^ 2)) =
        (cfDen α (n + 2) : ℝ) / (cfDen α (n + 1) : ℝ) +
        (cfDen α (n + 1) : ℝ) / (cfDen α (n + 2) : ℝ) := by
      field_simp [ne_of_gt hs5, ne_of_gt hq1, ne_of_gt hq2]
    have hR : Real.sqrt 5 * (cfDen α (n + 1) : ℝ) * (cfDen α (n + 2) : ℝ) *
        (1 / ((cfDen α (n + 1) : ℝ) * (cfDen α (n + 2) : ℝ))) = Real.sqrt 5 := by
      field_simp [ne_of_gt hq1, ne_of_gt hq2]
    linarith
  have hx : (cfDen α (n + 1) : ℝ) / (cfDen α n : ℝ) < (1 + Real.sqrt 5) / 2 :=
    hurwitz_ratio_lt_goldenRatio (cfDen_pos hα n) (cfDen_le_succ hα n) hsum01
  have hy : (cfDen α (n + 2) : ℝ) / (cfDen α (n + 1) : ℝ) < (1 + Real.sqrt 5) / 2 :=
    hurwitz_ratio_lt_goldenRatio (cfDen_pos hα (n + 1)) (cfDen_le_succ hα (n + 1)) hsum12
  -- Recurrence `q_{n+2} ≥ q_{n+1} + q_n` implies `y ≥ 1 + 1 / x > 1 + (√5 - 1) / 2 = (1 + √5) / 2`
  have hrec : (cfDen α (n + 1) : ℝ) + (cfDen α n : ℝ) ≤ (cfDen α (n + 2) : ℝ) := by
    have hna : 1 ≤ cfCoeffNat α (n + 2) := one_le_cfCoeffNat_succ hα (n + 1)
    have hnat : cfDen α (n + 1) + cfDen α n ≤ cfDen α (n + 2) := by
      rw [cfDen_recurrence]
      have := cfDen_pos hα (n + 1)
      nlinarith
    exact_mod_cast hnat
  have hy_ge : 1 + (cfDen α n : ℝ) / (cfDen α (n + 1) : ℝ) ≤
      (cfDen α (n + 2) : ℝ) / (cfDen α (n + 1) : ℝ) := by
    rw [show 1 + (cfDen α n : ℝ) / (cfDen α (n + 1) : ℝ) =
        ((cfDen α (n + 1) : ℝ) + (cfDen α n : ℝ)) / (cfDen α (n + 1) : ℝ) by
      field_simp [ne_of_gt hq1]]
    exact div_le_div_of_nonneg_right hrec (le_of_lt hq1)
  have hinv : (Real.sqrt 5 - 1) / 2 < (cfDen α n : ℝ) / (cfDen α (n + 1) : ℝ) := by
    have hsq5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hprod : ((1 + Real.sqrt 5) / 2) * ((Real.sqrt 5 - 1) / 2) = 1 := by nlinarith [hsq5]
    have h1 : (Real.sqrt 5 - 1) / 2 = ((1 + Real.sqrt 5) / 2)⁻¹ := by
      exact eq_inv_of_mul_eq_one_right hprod
    rw [h1]
    have h2 : ((cfDen α (n + 1) : ℝ) / (cfDen α n : ℝ))⁻¹ =
        (cfDen α n : ℝ) / (cfDen α (n + 1) : ℝ) := inv_div _ _
    rw [← h2]
    exact inv_strictAnti₀ (by positivity) hx
  linarith

/-- **Hurwitz's 1891 Sharp Diophantine Approximation Theorem**:
For every irrational `α`, there are infinitely many coprime pairs `(p, q) : ℤ × ℕ` with `q ≥ 1`
satisfying `|α - p / q| < 1 / (√5 · q²)`. -/
theorem hurwitz_approximation_theorem {α : ℝ} (hα : Irrational α) :
    { pq : ℤ × ℕ |
      1 ≤ pq.2 ∧ Nat.Coprime pq.1.natAbs pq.2 ∧
      |α - (pq.1 : ℝ) / (pq.2 : ℝ)| < 1 / (Real.sqrt 5 * (pq.2 : ℝ) ^ 2) }.Infinite := by
  intro hfin
  -- If finite, the denominators are bounded by some `M`
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ pq ∈ { pq : ℤ × ℕ |
      1 ≤ pq.2 ∧ Nat.Coprime pq.1.natAbs pq.2 ∧
      |α - (pq.1 : ℝ) / (pq.2 : ℝ)| < 1 / (Real.sqrt 5 * (pq.2 : ℝ) ^ 2) }, pq.2 ≤ M := by
    refine ⟨hfin.toFinset.sup Prod.snd, fun pq hpq => ?_⟩
    exact Finset.le_sup (f := Prod.snd) (hfin.mem_toFinset.mpr hpq)
  obtain ⟨k, hk_cases, hk_bound⟩ := hurwitz_three_consecutive_convergents hα (M + 1)
  have hk_ge : M + 1 ≤ k := by rcases hk_cases with rfl | rfl | rfl <;> omega
  have hden_ge : M + 1 ≤ cfDen α k := le_trans hk_ge (cfDen_ge_self hα k)
  have hmem : (cfNum α k, cfDen α k) ∈ { pq : ℤ × ℕ |
      1 ≤ pq.2 ∧ Nat.Coprime pq.1.natAbs pq.2 ∧
      |α - (pq.1 : ℝ) / (pq.2 : ℝ)| < 1 / (Real.sqrt 5 * (pq.2 : ℝ) ^ 2) } :=
    ⟨cfDen_pos hα k, cf_coprime hα k, hk_bound⟩
  have hle := hM _ hmem
  omega

/-- Rational-number formulation of Hurwitz's theorem:
infinitely many `r : ℚ` satisfy `|α - r| < 1 / (√5 · r.den²)`. -/
theorem hurwitz_approximation_rat {α : ℝ} (hα : Irrational α) :
    { r : ℚ | |α - (r : ℝ)| < 1 / (Real.sqrt 5 * (r.den : ℝ) ^ 2) }.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ r ∈ { r : ℚ | |α - (r : ℝ)| < 1 / (Real.sqrt 5 * (r.den : ℝ) ^ 2) },
      r.den ≤ M :=
    ⟨hfin.toFinset.sup Rat.den, fun r hr => Finset.le_sup (f := Rat.den) (hfin.mem_toFinset.mpr hr)⟩
  obtain ⟨k, hk_cases, hk_bound⟩ := hurwitz_three_consecutive_convergents hα (M + 1)
  have hk_ge : M + 1 ≤ k := by rcases hk_cases with rfl | rfl | rfl <;> omega
  have hden_ge : M + 1 ≤ cfDen α k := le_trans hk_ge (cfDen_ge_self hα k)
  let r : ℚ := ⟨cfNum α k, cfDen α k, Nat.ne_of_gt (cfDen_pos hα k), cf_coprime hα k⟩
  have hr_cast : (r : ℝ) = (cfNum α k : ℝ) / (cfDen α k : ℝ) := Rat.cast_def r
  have hr_mem : r ∈ { r : ℚ | |α - (r : ℝ)| < 1 / (Real.sqrt 5 * (r.den : ℝ) ^ 2) } := by
    show |α - (r : ℝ)| < 1 / (Real.sqrt 5 * (r.den : ℝ) ^ 2)
    rw [hr_cast]
    exact hk_bound
  have hle : cfDen α k ≤ M := hM r hr_mem
  omega

/-- **Optimality of Hurwitz's Constant `√5` via the Golden Ratio `φ = (1 + √5) / 2`**:
For every `C > √5`, there are only finitely many `(p, q) : ℤ × ℕ` with `q ≥ 1` satisfying
`|(1 + √5) / 2 - p / q| < 1 / (C · q²)`. -/
theorem hurwitz_constant_optimal_goldenRatio {C : ℝ} (hC : Real.sqrt 5 < C) :
    { pq : ℤ × ℕ |
      1 ≤ pq.2 ∧
      |((1 + Real.sqrt 5) / 2) - (pq.1 : ℝ) / (pq.2 : ℝ)| < 1 / (C * (pq.2 : ℝ) ^ 2) }.Finite := by
  have hs5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hCpos : 0 < C := lt_trans hs5 hC
  have hCdiff : 0 < C - Real.sqrt 5 := sub_pos.mpr hC
  set φ : ℝ := (1 + Real.sqrt 5) / 2
  set ψ : ℝ := (1 - Real.sqrt 5) / 2
  have hsq5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  -- Bound on `q`: `q² < 1 / (C * (C - √5))`
  obtain ⟨Qmax, hQmax⟩ := exists_nat_gt (1 / (C * (C - Real.sqrt 5)))
  have hq_bound : ∀ pq : ℤ × ℕ, 1 ≤ pq.2 →
      |φ - (pq.1 : ℝ) / (pq.2 : ℝ)| < 1 / (C * (pq.2 : ℝ) ^ 2) → pq.2 ≤ Qmax := by
    intro ⟨p, q⟩ hq hlt
    have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
    -- Norm `(p - φ q)(p - ψ q) = p² - p q - q² ∈ ℤ \ {0}`
    have hnorm_eq : ((p : ℝ) - φ * (q : ℝ)) * ((p : ℝ) - ψ * (q : ℝ)) =
        ((p ^ 2 - p * (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ℝ) := by
      push_cast; dsimp [φ, ψ]; nlinarith [hsq5]
    have hint_ne : (p ^ 2 - p * (q : ℤ) - (q : ℤ) ^ 2 : ℤ) ≠ 0 := by
      intro h0
      have h0R : ((p : ℝ) - φ * (q : ℝ)) * ((p : ℝ) - ψ * (q : ℝ)) = 0 := by
        rw [hnorm_eq, h0]; simp
      rcases mul_eq_zero.mp h0R with h1 | h2
      · refine Real.goldenRatio_irrational ⟨(p : ℚ) / (q : ℚ), ?_⟩
        rw [Real.goldenRatio]; push_cast; dsimp [φ] at h1
        exact (eq_div_of_mul_eq (ne_of_gt hqpos) (by linarith)).symm
      · refine Real.goldenConj_irrational ⟨(p : ℚ) / (q : ℚ), ?_⟩
        rw [Real.goldenConj]; push_cast; dsimp [ψ] at h2
        exact (eq_div_of_mul_eq (ne_of_gt hqpos) (by linarith)).symm
    have hge1 : (1 : ℝ) ≤ |((p : ℝ) - φ * (q : ℝ)) * ((p : ℝ) - ψ * (q : ℝ))| := by
      rw [hnorm_eq]
      have h1 : (1 : ℤ) ≤ |p ^ 2 - p * (q : ℤ) - (q : ℤ) ^ 2| := Int.one_le_abs hint_ne
      exact_mod_cast h1
    have hprod_eq : |((p : ℝ) - φ * (q : ℝ)) * ((p : ℝ) - ψ * (q : ℝ))| =
        (q : ℝ) ^ 2 * |φ - (p : ℝ) / (q : ℝ)| * |(p : ℝ) / (q : ℝ) - ψ| := by
      have h1 : (p : ℝ) - φ * (q : ℝ) = -(q : ℝ) * (φ - (p : ℝ) / (q : ℝ)) := by
        field_simp [ne_of_gt hqpos]; ring
      have h2 : (p : ℝ) - ψ * (q : ℝ) = (q : ℝ) * ((p : ℝ) / (q : ℝ) - ψ) := by
        field_simp [ne_of_gt hqpos]
      rw [h1, h2, abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos hqpos]
      ring
    have hpsi : |(p : ℝ) / (q : ℝ) - ψ| < Real.sqrt 5 + 1 / (C * (q : ℝ) ^ 2) := by
      have htri : |(p : ℝ) / (q : ℝ) - ψ| ≤ |(p : ℝ) / (q : ℝ) - φ| + |φ - ψ| := by
        have : (p : ℝ) / (q : ℝ) - ψ = ((p : ℝ) / (q : ℝ) - φ) + (φ - ψ) := by ring
        rw [this]; exact abs_add_le _ _
      have hphi_psi : |φ - ψ| = Real.sqrt 5 := by
        have : φ - ψ = Real.sqrt 5 := by dsimp [φ, ψ]; ring
        rw [this, abs_of_pos hs5]
      rw [abs_sub_comm] at hlt
      linarith
    have h1lt : (1 : ℝ) < (Real.sqrt 5 + 1 / (C * (q : ℝ) ^ 2)) / C := by
      rw [hprod_eq] at hge1
      have hstep : (q : ℝ) ^ 2 * |φ - (p : ℝ) / (q : ℝ)| * |(p : ℝ) / (q : ℝ) - ψ| <
          (q : ℝ) ^ 2 * (1 / (C * (q : ℝ) ^ 2)) * (Real.sqrt 5 + 1 / (C * (q : ℝ) ^ 2)) := by
        have ha : (q : ℝ) ^ 2 * |φ - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ 2 * (1 / (C * (q : ℝ) ^ 2)) :=
          mul_lt_mul_of_pos_left hlt (by positivity)
        have hb : 0 ≤ |(p : ℝ) / (q : ℝ) - ψ| := abs_nonneg _
        have hc : 0 < (q : ℝ) ^ 2 * (1 / (C * (q : ℝ) ^ 2)) := by positivity
        nlinarith
      have hsimp : (q : ℝ) ^ 2 * (1 / (C * (q : ℝ) ^ 2)) * (Real.sqrt 5 + 1 / (C * (q : ℝ) ^ 2)) =
          (Real.sqrt 5 + 1 / (C * (q : ℝ) ^ 2)) / C := by
        field_simp [ne_of_gt hCpos, ne_of_gt hqpos]
      linarith
    have hqsq : (q : ℝ) ^ 2 < 1 / (C * (C - Real.sqrt 5)) := by
      have h1 : C < Real.sqrt 5 + 1 / (C * (q : ℝ) ^ 2) := (one_lt_div hCpos).mp h1lt
      have h2 : C - Real.sqrt 5 < 1 / (C * (q : ℝ) ^ 2) := by linarith
      rw [lt_div_iff₀ (by positivity)] at h2 ⊢
      linarith
    have hqle : (q : ℝ) ≤ (q : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      nlinarith
    have hqlt : (q : ℝ) < (Qmax : ℝ) := lt_of_le_of_lt hqle (lt_trans hqsq hQmax)
    exact le_of_lt (Nat.cast_lt.mp hqlt)
  -- Embed into a finite box `[-Pmax, Pmax] × [0, Qmax]`
  set Pmax : ℤ := ⌈(|φ| + 1) * (Qmax : ℝ) + 1 / C⌉ + 1
  let box : Finset (ℤ × ℕ) := (Finset.Icc (-Pmax) Pmax) ×ˢ (Finset.range (Qmax + 1))
  have hsub : { pq : ℤ × ℕ |
      1 ≤ pq.2 ∧
      |((1 + Real.sqrt 5) / 2) - (pq.1 : ℝ) / (pq.2 : ℝ)| < 1 / (C * (pq.2 : ℝ) ^ 2) } ⊆
      (box : Set (ℤ × ℕ)) := by
    rintro ⟨p, q⟩ ⟨hq, hlt⟩
    have hqle : q ≤ Qmax := hq_bound (p, q) hq hlt
    have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
    have hp_abs : |(p : ℝ)| ≤ (|φ| + 1) * (Qmax : ℝ) + 1 / C := by
      have h1 : |(p : ℝ) - φ * (q : ℝ)| < 1 / (C * (q : ℝ)) := by
        have heq : |(p : ℝ) - φ * (q : ℝ)| = (q : ℝ) * |φ - (p : ℝ) / (q : ℝ)| := by
          have : (p : ℝ) - φ * (q : ℝ) = -(q : ℝ) * (φ - (p : ℝ) / (q : ℝ)) := by
            field_simp [ne_of_gt hqpos]; ring
          rw [this, abs_mul, abs_neg, abs_of_pos hqpos]
        rw [heq]
        calc (q : ℝ) * |φ - (p : ℝ) / (q : ℝ)|
            < (q : ℝ) * (1 / (C * (q : ℝ) ^ 2)) := mul_lt_mul_of_pos_left hlt hqpos
          _ = 1 / (C * (q : ℝ)) := by field_simp [ne_of_gt hCpos, ne_of_gt hqpos]
      have h2 : 1 / (C * (q : ℝ)) ≤ 1 / C := by
        apply div_le_div_of_nonneg_left (by norm_num) hCpos
        have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
        nlinarith
      have h3 : |(p : ℝ)| ≤ |φ * (q : ℝ)| + |(p : ℝ) - φ * (q : ℝ)| := by
        have : (p : ℝ) = φ * (q : ℝ) + ((p : ℝ) - φ * (q : ℝ)) := by ring
        conv_lhs => rw [this]
        exact abs_add_le _ _
      rw [abs_mul, abs_of_pos hqpos] at h3
      have hqR : (q : ℝ) ≤ (Qmax : ℝ) := by exact_mod_cast hqle
      nlinarith [abs_nonneg φ]
    have hp_le : (p : ℝ) ≤ (Pmax : ℝ) := by
      have hceil := Int.le_ceil ((|φ| + 1) * (Qmax : ℝ) + 1 / C)
      have h1 := le_trans (le_abs_self (p : ℝ)) hp_abs
      dsimp only [Pmax]; push_cast; linarith
    have hp_ge : -(Pmax : ℝ) ≤ (p : ℝ) := by
      have hceil := Int.le_ceil ((|φ| + 1) * (Qmax : ℝ) + 1 / C)
      have h1 := le_trans (neg_le_abs (p : ℝ)) hp_abs
      dsimp only [Pmax]; push_cast; linarith
    simp only [box, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
    exact ⟨⟨by exact_mod_cast hp_ge, by exact_mod_cast hp_le⟩, Nat.lt_succ_of_le hqle⟩
  exact (Finset.finite_toSet box).subset hsub

/-- Rational-number formulation of Hurwitz optimality at the golden ratio. -/
theorem hurwitz_constant_optimal_goldenRatio_rat {C : ℝ} (hC : Real.sqrt 5 < C) :
    { r : ℚ | |Real.goldenRatio - (r : ℝ)| < 1 / (C * (r.den : ℝ) ^ 2) }.Finite := by
  have hfin := hurwitz_constant_optimal_goldenRatio hC
  let g : ℚ → ℤ × ℕ := fun r => (r.num, r.den)
  have hinj : Function.Injective g := by
    intro r1 r2 heq
    have h1 : r1.num = r2.num := congrArg Prod.fst heq
    have h2 : r1.den = r2.den := congrArg Prod.snd heq
    exact Rat.ext h1 h2
  refine Set.Finite.of_finite_image (f := g) ?_ (hinj.injOn)
  refine hfin.subset ?_
  rintro pq ⟨r, hr, rfl⟩
  refine ⟨r.pos, ?_⟩
  change |Real.goldenRatio - (r.num : ℝ) / (r.den : ℝ)| < 1 / (C * (r.den : ℝ) ^ 2)
  have hrc : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := Rat.cast_def r
  rwa [← hrc]

/-- **Liouville's Algebraic Irrationality Approximation Bound**:
If `α` is an irrational root of a nonzero integer polynomial `f ∈ ℤ[X]` of degree `d`, then
there exists `c > 0` such that `|α - p / q| ≥ c / q^d` for every rational `p / q` (`q ≥ 1`). -/
theorem liouville_algebraic_approximation_bound {α : ℝ} (hα : Irrational α)
    (f : Polynomial ℤ) (hf : f ≠ 0) (hroot : Polynomial.aeval α f = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℤ) (q : ℕ), 1 ≤ q →
      c / (q : ℝ) ^ f.natDegree ≤ |α - (p : ℝ) / (q : ℝ)| := by
  let fR : Polynomial ℝ := f.map (Int.castRingHom ℝ)
  have hfR_ne : fR ≠ 0 := by
    intro h0
    apply hf
    ext n
    have h1 := congrArg (fun P => P.coeff n) h0
    simp only [fR, Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at h1
    exact Int.cast_eq_zero.mp h1
  have hfR_eval : ∀ x : ℝ, fR.eval x = Polynomial.aeval x f := by
    intro x; simp [fR, Polynomial.aeval_def, Polynomial.eval_map]
  -- Choose `r ∈ (0, 1]` such that `α` is the only root of `fR` in `[α - r, α + r]`
  let otherRoots : Finset ℝ := fR.roots.toFinset.filter (fun x => x ≠ α)
  set r : ℝ := if h : otherRoots.Nonempty then
      min 1 ((otherRoots.image (fun x => |x - α|)).min' (h.image _) / 2)
    else 1
  have hr_pos : 0 < r := by
    dsimp only [r]
    split_ifs with h
    · apply lt_min (by norm_num)
      have hmin := Finset.min'_mem (otherRoots.image (fun x => |x - α|)) (h.image _)
      obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hmin
      have hxne : x ≠ α := (Finset.mem_filter.mp hx).2
      have hpos : 0 < |x - α| := abs_pos.mpr (sub_ne_zero.mpr hxne)
      linarith
    · norm_num
  have hr_le1 : r ≤ 1 := by
    dsimp only [r]; split_ifs <;> [exact min_le_left _ _; exact le_rfl]
  have hno_other_root : ∀ x : ℝ, x ≠ α → |x - α| < r → fR.eval x ≠ 0 := by
    intro x hxne hxlt hfx
    have hxroot : x ∈ otherRoots := by
      simp only [otherRoots, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hfR_ne,
        Polynomial.IsRoot.def]
      exact ⟨hfx, hxne⟩
    have hne : otherRoots.Nonempty := ⟨x, hxroot⟩
    have hr_le : r ≤ |x - α| / 2 := by
      dsimp only [r]
      rw [dif_pos hne]
      refine le_trans (min_le_right _ _) ?_
      have := Finset.min'_le (otherRoots.image (fun y => |y - α|)) |x - α|
        (Finset.mem_image_of_mem _ hxroot)
      linarith
    have hpos : 0 < |x - α| := abs_pos.mpr (sub_ne_zero.mpr hxne)
    linarith
  -- Bound `|fR'.eval t|` on the compact interval `[α - 1, α + 1]`
  have hbdd : ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Set.Icc (α - 1) (α + 1), |(Polynomial.derivative fR).eval t| ≤ M := by
    obtain ⟨t0, _, ht0⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr (by linarith : α - 1 ≤ α + 1))
      ((Polynomial.derivative fR).continuous.abs.continuousOn)
    refine ⟨|(Polynomial.derivative fR).eval t0| + 1, by positivity, fun t ht => ?_⟩
    have hle : |(Polynomial.derivative fR).eval t| ≤ |(Polynomial.derivative fR).eval t0| := ht0 ht
    linarith
  obtain ⟨M, hMpos, hM⟩ := hbdd
  refine ⟨min r (1 / M), lt_min hr_pos (by positivity), fun p q hq => ?_⟩
  have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hqge1 : (1 : ℝ) ≤ (q : ℝ) ^ f.natDegree := one_le_pow₀ (by exact_mod_cast hq)
  set x : ℝ := (p : ℝ) / (q : ℝ)
  by_cases hfar : r ≤ |α - x|
  · calc min r (1 / M) / (q : ℝ) ^ f.natDegree
        ≤ r / 1 := by
          apply div_le_div₀ (le_of_lt hr_pos) (min_le_left _ _) (by norm_num) hqge1
      _ = r := div_one r
      _ ≤ |α - x| := hfar
  · push Not at hfar
    have hx_ne : x ≠ α := by
      intro heq
      exact hα ⟨(p : ℚ) / (q : ℚ), by dsimp [x] at heq; push_cast; exact heq⟩
    have hfx_ne : fR.eval x ≠ 0 := hno_other_root x hx_ne (by rwa [abs_sub_comm])
    -- Denominator clearing: `q ^ f.natDegree * fR.eval (p / q)` is a nonzero integer
    have hint_val : ∃ m : ℤ, (q : ℝ) ^ f.natDegree * fR.eval x = (m : ℝ) := by
      refine ⟨∑ i ∈ Finset.range (f.natDegree + 1),
          f.coeff i * p ^ i * (q : ℤ) ^ (f.natDegree - i), ?_⟩
      rw [hfR_eval, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
      rw [Finset.mul_sum]
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have hile : i ≤ f.natDegree := Nat.lt_succ_iff.mp hi
      dsimp only [x]
      rw [div_pow]
      have hpow : (q : ℝ) ^ f.natDegree = (q : ℝ) ^ i * (q : ℝ) ^ (f.natDegree - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hile]
      rw [hpow]
      have hqi : (q : ℝ) ^ i ≠ 0 := pow_ne_zero i (ne_of_gt hqpos)
      field_simp [hqi]
      simp only [eq_intCast]
      ring
    obtain ⟨m, hm⟩ := hint_val
    have hm_ne : m ≠ 0 := by
      intro hm0; subst hm0
      simp only [Int.cast_zero] at hm
      rcases mul_eq_zero.mp hm with h1 | h2
      · exact (pow_ne_zero f.natDegree (ne_of_gt hqpos)) h1
      · exact hfx_ne h2
    have hfx_ge : 1 / (q : ℝ) ^ f.natDegree ≤ |fR.eval x| := by
      have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm_ne
      rw [← hm, abs_mul, abs_of_pos (pow_pos hqpos _)] at hm1
      rw [div_le_iff₀ (pow_pos hqpos _)]
      linarith
    -- Mean Value Theorem between `x` and `α`
    have hmvt : |fR.eval x| ≤ M * |α - x| := by
      have hfa : fR.eval α = 0 := by rw [hfR_eval, hroot]
      rcases lt_or_gt_of_ne hx_ne with hlt | hgt
      · obtain ⟨t, ⟨ht1, ht2⟩, hslope⟩ := exists_deriv_eq_slope (fun y => fR.eval y) hlt
          fR.continuous.continuousOn (fun y _ => fR.differentiableAt.differentiableWithinAt)
        have hderiv : deriv (fun y => fR.eval y) t = (Polynomial.derivative fR).eval t :=
          fR.hasDerivAt t |>.deriv
        rw [hderiv, hfa, zero_sub] at hslope
        have hfeq : |fR.eval x| = |(Polynomial.derivative fR).eval t| * |α - x| := by
          have h1 : -fR.eval x = (Polynomial.derivative fR).eval t * (α - x) := by
            rw [hslope]; field_simp [sub_ne_zero.mpr (ne_of_gt hlt)]
          have := congrArg abs h1
          rwa [abs_neg, abs_mul] at this
        have ht_mem : t ∈ Set.Icc (α - 1) (α + 1) := by
          rw [abs_lt] at hfar
          constructor <;> linarith
        rw [hfeq]
        exact mul_le_mul_of_nonneg_right (hM t ht_mem) (abs_nonneg _)
      · obtain ⟨t, ⟨ht1, ht2⟩, hslope⟩ := exists_deriv_eq_slope (fun y => fR.eval y) hgt
          fR.continuous.continuousOn (fun y _ => fR.differentiableAt.differentiableWithinAt)
        have hderiv : deriv (fun y => fR.eval y) t = (Polynomial.derivative fR).eval t :=
          fR.hasDerivAt t |>.deriv
        rw [hderiv, hfa, sub_zero] at hslope
        have hfeq : |fR.eval x| = |(Polynomial.derivative fR).eval t| * |α - x| := by
          have h1 : fR.eval x = (Polynomial.derivative fR).eval t * (x - α) := by
            rw [hslope]; field_simp [sub_ne_zero.mpr (ne_of_gt hgt)]
          have := congrArg abs h1
          rwa [abs_mul, abs_sub_comm x α] at this
        have ht_mem : t ∈ Set.Icc (α - 1) (α + 1) := by
          rw [abs_lt] at hfar
          constructor <;> linarith
        rw [hfeq]
        exact mul_le_mul_of_nonneg_right (hM t ht_mem) (abs_nonneg _)
    calc min r (1 / M) / (q : ℝ) ^ f.natDegree
        ≤ (1 / M) / (q : ℝ) ^ f.natDegree := by
          gcongr; exact min_le_right _ _
      _ = (1 / (q : ℝ) ^ f.natDegree) / M := by ring
      _ ≤ |fR.eval x| / M := by gcongr
      _ ≤ (M * |α - x|) / M := by gcongr
      _ = |α - x| := by field_simp [ne_of_gt hMpos]

/-- **Transcendence of Liouville's Constant `∑_{n ≥ 0} 10^{-n!}`** (and general base `m ≥ 2`). -/
theorem liouville_constant_transcendental : Transcendental ℤ (liouvilleNumber (10 : ℝ)) :=
  transcendental_liouvilleNumber (m := 10) (by norm_num)

theorem liouville_base_transcendental {m : ℕ} (hm : 2 ≤ m) :
    Transcendental ℤ (liouvilleNumber (m : ℝ)) :=
  transcendental_liouvilleNumber hm

theorem liouville_constant_irrational : Irrational (liouvilleNumber (10 : ℝ)) :=
  (liouville_liouvilleNumber (m := 10) (by norm_num)).irrational

/-!
## Section 5: Unconditional Benford's First-Digit Law for Powers of 2
-/

/-- `log 2 / log 10` is irrational (since `2^b = 10^a = 2^a · 5^a` has no positive solutions). -/
theorem irrational_log2_div_log10 : Irrational (Real.log 2 / Real.log 10) := by
  intro ⟨q, hq⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hqpos : 0 < (q : ℝ) := by rw [hq]; positivity
  have hqposQ : 0 < q := by exact_mod_cast hqpos
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hqposQ
  set a : ℕ := q.num.natAbs
  set b : ℕ := q.den
  have ha_pos : 0 < a := Int.natAbs_pos.mpr (ne_of_gt hnum_pos)
  have hb_pos : 0 < b := q.pos
  have hq_eq : (q : ℝ) = (a : ℝ) / (b : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    have : (a : ℤ) = q.num := Int.natAbs_of_nonneg (le_of_lt hnum_pos)
    exact_mod_cast this.symm
  have hmul : (b : ℝ) * Real.log 2 = (a : ℝ) * Real.log 10 := by
    rw [hq_eq] at hq
    have hbR : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hb_pos)
    field_simp [hbR, ne_of_gt hlog10] at hq
    linarith
  have hexp : (2 : ℝ) ^ b = (10 : ℝ) ^ a := by
    have h1 : Real.log ((2 : ℝ) ^ b) = Real.log ((10 : ℝ) ^ a) := by
      rw [Real.log_pow, Real.log_pow, hmul]
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) h1
  have hnat : 2 ^ b = 10 ^ a := by exact_mod_cast hexp
  have h5dvd : 5 ∣ 2 ^ b := by
    rw [hnat, show (10 : ℕ) = 5 * 2 by norm_num, mul_pow]
    exact dvd_mul_of_dvd_left (dvd_pow_self 5 (ne_of_gt ha_pos)) _
  have h5dvd2 : 5 ∣ 2 := (Nat.prime_five).dvd_of_dvd_pow h5dvd
  omega

/-- The leading (most significant) base-10 digit of a positive natural number `m`. -/
def leadingDigit10 (m : ℕ) : ℕ := m / 10 ^ Nat.log 10 m

lemma leadingDigit10_eq_iff {m d : ℕ} (hm : 1 ≤ m) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    leadingDigit10 m = d ↔ ∃ k : ℕ, d * 10 ^ k ≤ m ∧ m < (d + 1) * 10 ^ k := by
  constructor
  · intro heq
    refine ⟨Nat.log 10 m, ?_, ?_⟩
    · have h1 := Nat.div_mul_le_self m (10 ^ Nat.log 10 m)
      change m / 10 ^ Nat.log 10 m = d at heq
      rw [heq] at h1; exact h1
    · have h1 : m < (m / 10 ^ Nat.log 10 m + 1) * 10 ^ Nat.log 10 m := by
        have hpos : 0 < 10 ^ Nat.log 10 m := by positivity
        have hdm := Nat.div_add_mod m (10 ^ Nat.log 10 m)
        have hmod := Nat.mod_lt m hpos
        nlinarith
      change m / 10 ^ Nat.log 10 m = d at heq
      rw [heq] at h1; exact h1
  · rintro ⟨k, h1, h2⟩
    have hlog : Nat.log 10 m = k := by
      apply le_antisymm
      · apply Nat.le_of_lt_succ
        rw [Nat.log_lt_iff_lt_pow (by norm_num) (by omega)]
        calc m < (d + 1) * 10 ^ k := h2
          _ ≤ 10 * 10 ^ k := by gcongr; omega
          _ = 10 ^ (k + 1) := by rw [pow_succ]; ring
      · rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
        calc 10 ^ k = 1 * 10 ^ k := (one_mul _).symm
          _ ≤ d * 10 ^ k := by gcongr
          _ ≤ m := h1
    unfold leadingDigit10
    rw [hlog]
    have hpos : 0 < 10 ^ k := by positivity
    exact Nat.div_eq_of_lt_le h1 h2

lemma leadingDigit10_pow_two_iff_fract (n d : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    leadingDigit10 (2 ^ n) = d ↔
      Real.log (d : ℝ) / Real.log 10 ≤ Int.fract ((n : ℝ) * (Real.log 2 / Real.log 10)) ∧
      Int.fract ((n : ℝ) * (Real.log 2 / Real.log 10)) <
        Real.log ((d : ℝ) + 1) / Real.log 10 := by
  have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hm1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  rw [leadingDigit10_eq_iff hm1 hd1 hd9]
  set x : ℝ := (n : ℝ) * (Real.log 2 / Real.log 10)
  have hx0 : 0 ≤ x := by positivity
  constructor
  · rintro ⟨k, h1, h2⟩
    have h1R : (d : ℝ) * (10 : ℝ) ^ k ≤ (2 : ℝ) ^ n := by exact_mod_cast h1
    have h2R : (2 : ℝ) ^ n < ((d : ℝ) + 1) * (10 : ℝ) ^ k := by
      have : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
      rw [← this]; exact_mod_cast h2
    have hlog_le : Real.log ((d : ℝ) * (10 : ℝ) ^ k) ≤ Real.log ((2 : ℝ) ^ n) :=
      Real.log_le_log (by positivity) h1R
    have hlog_lt : Real.log ((2 : ℝ) ^ n) < Real.log (((d : ℝ) + 1) * (10 : ℝ) ^ k) :=
      Real.log_lt_log (by positivity) h2R
    rw [Real.log_mul (ne_of_gt hd_pos) (by positivity), Real.log_pow, Real.log_pow] at hlog_le
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog_lt
    have hx_lo : Real.log (d : ℝ) / Real.log 10 + (k : ℝ) ≤ x := by
      dsimp [x]
      have : (Real.log (d : ℝ) + (k : ℝ) * Real.log 10) / Real.log 10 =
          Real.log (d : ℝ) / Real.log 10 + (k : ℝ) := by field_simp [ne_of_gt hlog10]
      have h2' : ((n : ℝ) * Real.log 2) / Real.log 10 = (n : ℝ) * (Real.log 2 / Real.log 10) := by
        ring
      have hdiv := div_le_div_of_nonneg_right hlog_le (le_of_lt hlog10)
      linarith
    have hx_hi : x < Real.log ((d : ℝ) + 1) / Real.log 10 + (k : ℝ) := by
      dsimp [x]
      have : (Real.log ((d : ℝ) + 1) + (k : ℝ) * Real.log 10) / Real.log 10 =
          Real.log ((d : ℝ) + 1) / Real.log 10 + (k : ℝ) := by field_simp [ne_of_gt hlog10]
      have h2' : ((n : ℝ) * Real.log 2) / Real.log 10 = (n : ℝ) * (Real.log 2 / Real.log 10) := by
        ring
      have hdiv := div_lt_div_of_pos_right hlog_lt hlog10
      linarith
    have hld0 : 0 ≤ Real.log (d : ℝ) / Real.log 10 :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast hd1)) (le_of_lt hlog10)
    have hld1 : Real.log ((d : ℝ) + 1) / Real.log 10 ≤ 1 := by
      rw [div_le_one hlog10]
      apply Real.log_le_log (by positivity)
      have : (d : ℝ) + 1 ≤ 10 := by exact_mod_cast (show d + 1 ≤ 10 by omega)
      exact this
    have hfloor : ⌊x⌋ = (k : ℤ) := by
      rw [Int.floor_eq_iff]
      push_cast
      exact ⟨by linarith, by linarith⟩
    rw [Int.fract, hfloor]
    push_cast
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    set k : ℕ := ⌊x⌋₊
    have hfk : (⌊x⌋ : ℝ) = (k : ℝ) := by
      dsimp [k]; rw [← Int.natCast_floor_eq_floor hx0]; push_cast; rfl
    rw [Int.fract, hfk] at h1 h2
    have hlog_le : Real.log ((d : ℝ) * (10 : ℝ) ^ k) ≤ Real.log ((2 : ℝ) ^ n) := by
      rw [Real.log_mul (ne_of_gt hd_pos) (by positivity), Real.log_pow, Real.log_pow]
      have h1' := mul_le_mul_of_nonneg_right h1 (le_of_lt hlog10)
      dsimp [x] at h1'
      have hne : Real.log 10 ≠ 0 := ne_of_gt hlog10
      have hL : Real.log (d : ℝ) / Real.log 10 * Real.log 10 = Real.log (d : ℝ) :=
        div_mul_cancel₀ _ hne
      have hR : ((n : ℝ) * (Real.log 2 / Real.log 10) - (k : ℝ)) * Real.log 10 =
          (n : ℝ) * Real.log 2 - (k : ℝ) * Real.log 10 := by field_simp [hne]
      linarith
    have hlog_lt : Real.log ((2 : ℝ) ^ n) < Real.log (((d : ℝ) + 1) * (10 : ℝ) ^ k) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      have h2' := mul_lt_mul_of_pos_right h2 hlog10
      dsimp [x] at h2'
      have hne : Real.log 10 ≠ 0 := ne_of_gt hlog10
      have hR : Real.log ((d : ℝ) + 1) / Real.log 10 * Real.log 10 = Real.log ((d : ℝ) + 1) :=
        div_mul_cancel₀ _ hne
      have hL : ((n : ℝ) * (Real.log 2 / Real.log 10) - (k : ℝ)) * Real.log 10 =
          (n : ℝ) * Real.log 2 - (k : ℝ) * Real.log 10 := by field_simp [hne]
      linarith
    have h1R : (d : ℝ) * (10 : ℝ) ^ k ≤ (2 : ℝ) ^ n :=
      (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog_le
    have h2R : (2 : ℝ) ^ n < ((d : ℝ) + 1) * (10 : ℝ) ^ k :=
      (Real.log_lt_log_iff (by positivity) (by positivity)).mp hlog_lt
    refine ⟨k, by exact_mod_cast h1R, ?_⟩
    have : ((d : ℝ) + 1) * (10 : ℝ) ^ k = (((d + 1) * 10 ^ k : ℕ) : ℝ) := by push_cast; ring
    rw [this] at h2R
    exact_mod_cast h2R

/-- **Benford's First-Digit Law for Powers of 2**:
For every decimal digit `d ∈ {1, …, 9}`, the asymptotic density of `n : ℕ` whose base-10
leading digit of `2^n` is `d` equals `log(1 + 1 / d) / log 10`. -/
theorem benford_law_pow_two (d : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n => leadingDigit10 (2 ^ n) = d)).card : ℝ) / (N : ℝ))
      atTop (nhds (Real.log (1 + 1 / (d : ℝ)) / Real.log 10)) := by
  have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have ha0 : 0 ≤ Real.log (d : ℝ) / Real.log 10 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hd1)) (le_of_lt hlog10)
  have hab : Real.log (d : ℝ) / Real.log 10 ≤ Real.log ((d : ℝ) + 1) / Real.log 10 :=
    div_le_div_of_nonneg_right (Real.log_le_log hd_pos (by linarith)) (le_of_lt hlog10)
  have hb1 : Real.log ((d : ℝ) + 1) / Real.log 10 ≤ 1 := by
    rw [div_le_one hlog10]
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show d + 1 ≤ 10 by omega)
  have hweyl := weyl_equidistributed_linear_of_irrational irrational_log2_div_log10
    (Real.log (d : ℝ) / Real.log 10) (Real.log ((d : ℝ) + 1) / Real.log 10) ha0 hab hb1
  have hlim_eq : Real.log ((d : ℝ) + 1) / Real.log 10 - Real.log (d : ℝ) / Real.log 10 =
      Real.log (1 + 1 / (d : ℝ)) / Real.log 10 := by
    rw [← sub_div, ← Real.log_div (by positivity) (ne_of_gt hd_pos)]
    congr 2
    field_simp [ne_of_gt hd_pos]
  rw [hlim_eq] at hweyl
  have hfn :
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n => leadingDigit10 (2 ^ n) = d)).card : ℝ) / (N : ℝ)) =
      fun N : ℕ =>
        (((Finset.range N).filter (fun n : ℕ =>
          Real.log (d : ℝ) / Real.log 10 ≤ Int.fract ((n : ℝ) * (Real.log 2 / Real.log 10)) ∧
          Int.fract ((n : ℝ) * (Real.log 2 / Real.log 10)) <
            Real.log ((d : ℝ) + 1) / Real.log 10)).card : ℝ) / (N : ℝ) := by
    funext N
    congr 3
    apply Finset.filter_congr
    intro n _
    exact leadingDigit10_pow_two_iff_fract n d hd1 hd9
  rwa [hfn]

end RHDirect.Stage9DiophantineWeyl
