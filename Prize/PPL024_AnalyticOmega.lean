import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Basic
import RHDirect.Stage8MertensTheorems
import RHDirect.Stage10SiegelWalfiszFull
import RHDirect.ChenBVPrimes
import Prize.PPL024_AnalyticMertens

/-!
# PPL 024 Analytic Foundations — Part 3: Normal Order of `ω(p ± 1)` (Bloom's Lemma 2)

Unconditional formalization of Bloom's Lemma 2 (`lem-nt2` of arXiv:2305.02689) and Halberstam's
shifted-prime variance bound:
For both signs `plus : Bool` (`p - 1` and `p + 1`) and every `δ > 0`, there exist `C > 0` and
`N₀` such that for all `N ≥ N₀`:
`#{p ≤ N : p prime ∧ |ω(shiftVal plus p) - log (log (shiftVal plus p))| ≥ δ * log (log (shiftVal plus p))} ≤ C * N / (log N * log (log N))`.

Proof ingredients (100% unconditional Tier-A `Arithmetica4`):
- `RHDirect.ChenBVPrimes.bombieri_vinogradov_primes` (with `A = 3`)
- `RHDirect.Stage8MertensTheorems.mertens_second_theorem`
- `RHDirect.Stage10SiegelWalfiszFull.siegel_walfisz_pi_real` (for `π(N) ≤ 5 N / log N`)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset Filter Topology

namespace PPL024

/-! ## Section 1: Truncated `ω_Y` and Basic Prime-Factor Bounds -/

/-- Number of distinct prime divisors `r ≤ Y` dividing `n`. -/
def omegaTrunc (Y n : ℕ) : ℕ :=
  ((Finset.Icc 1 Y).filter (fun r => r.Prime ∧ r ∣ n)).card

lemma omegaTrunc_le_card_primeFactors (Y n : ℕ) (hn : n ≠ 0) :
    omegaTrunc Y n ≤ n.primeFactors.card := by
  unfold omegaTrunc
  refine Finset.card_le_card fun r hr => ?_
  have hr' := Finset.mem_filter.mp hr
  exact Nat.mem_primeFactors.mpr ⟨hr'.2.1, hr'.2.2, hn⟩

/-- At most `8` distinct primes `> Y` can divide `n` when `(Y + 1)^9 > n`. -/
lemma card_primeFactors_sub_omegaTrunc_le_eight {Y n : ℕ} (hn : n ≠ 0)
    (hpow : n < (Y + 1) ^ 9) :
    n.primeFactors.card - omegaTrunc Y n ≤ 8 := by
  set S_lo := (Finset.Icc 1 Y).filter (fun r => r.Prime ∧ r ∣ n)
  set S_hi := n.primeFactors.filter (fun r => Y < r)
  have hsub : S_lo ⊆ n.primeFactors := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    exact Nat.mem_primeFactors.mpr ⟨hr'.2.1, hr'.2.2, hn⟩
  have hdisj : Disjoint S_lo S_hi := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr1).1).2
    have h2 := (Finset.mem_filter.mp hr2).2
    omega
  have hunion : S_lo ∪ S_hi = n.primeFactors := by
    ext r
    simp only [S_lo, S_hi, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Nat.mem_primeFactors]
    constructor
    · rintro (⟨⟨_, _⟩, hpr, hd⟩ | ⟨⟨hpr, hd, _⟩, _⟩) <;> exact ⟨hpr, hd, hn⟩
    · rintro ⟨hpr, hd, _⟩
      by_cases hle : r ≤ Y
      · left; exact ⟨⟨hpr.pos, hle⟩, hpr, hd⟩
      · right; exact ⟨⟨hpr, hd, hn⟩, by omega⟩
  have hcard_eq : n.primeFactors.card = S_lo.card + S_hi.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hprod_dvd : (∏ r ∈ S_hi, r) ∣ n := by
    have h1 : (∏ r ∈ S_hi, r) ∣ (∏ r ∈ n.primeFactors, r) :=
      Finset.prod_dvd_prod_of_subset S_hi n.primeFactors id (Finset.filter_subset _ _)
    exact dvd_trans h1 (Nat.prod_primeFactors_dvd n)
  have hprod_le : ∏ r ∈ S_hi, r ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hprod_dvd
  have hprod_ge : (Y + 1) ^ S_hi.card ≤ ∏ r ∈ S_hi, r := by
    calc (Y + 1) ^ S_hi.card = ∏ _r ∈ S_hi, (Y + 1) := by rw [Finset.prod_const]
      _ ≤ ∏ r ∈ S_hi, r := Finset.prod_le_prod' fun r hr => by
          have := (Finset.mem_filter.mp hr).2; omega
  have hlt_pow : (Y + 1) ^ S_hi.card < (Y + 1) ^ 9 := lt_of_le_of_lt (hprod_ge.trans hprod_le) hpow
  have hhi_le : S_hi.card ≤ 8 := by
    by_contra hgt
    have h9 : 9 ≤ S_hi.card := by omega
    have hge : (Y + 1) ^ 9 ≤ (Y + 1) ^ S_hi.card :=
      Nat.pow_le_pow_right (by omega : 1 ≤ Y + 1) h9
    omega
  change n.primeFactors.card - S_lo.card ≤ 8
  omega

/-- Injectivity of multiplication on ordered pairs of distinct primes `r₁ < r₂`. -/
lemma prime_mul_injOn :
    ∀ {r₁ r₂ s₁ s₂ : ℕ}, r₁.Prime → r₂.Prime → s₁.Prime → s₂.Prime →
      r₁ < r₂ → s₁ < s₂ → r₁ * r₂ = s₁ * s₂ → r₁ = s₁ ∧ r₂ = s₂ := by
  intro r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ hlt_r hlt_s heq
  have hdvd : r₁ ∣ s₁ * s₂ := ⟨r₂, heq.symm⟩
  rcases hr₁.dvd_mul.mp hdvd with h1 | h2
  · have hreq : r₁ = s₁ := (Nat.prime_dvd_prime_iff_eq hr₁ hs₁).mp h1
    subst hreq
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hr₁.pos heq⟩
  · have hreq : r₁ = s₂ := (Nat.prime_dvd_prime_iff_eq hr₁ hs₂).mp h2
    have hlt : s₁ * s₂ < r₁ * r₂ := by nlinarith
    omega

/-- Bound on `∑_{r ≤ x, r prime} 1/(r - 1)` vs `Real.log (Real.log x)`. -/
lemma sum_prime_inv_sub_one_asymp :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      |∑ r ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / ((r : ℝ) - 1) -
          Real.log (Real.log x)| ≤ C := by
  obtain ⟨C₂, hC₂, hM2⟩ := RHDirect.Stage8MertensTheorems.mertens_second_theorem
  refine ⟨C₂ / Real.log 3 + |RHDirect.Stage8MertensTheorems.meisselMertensConst| + 2, by positivity,
    fun x hx3 => ?_⟩
  set P := (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime
  -- Difference `∑_{r ∈ P} (1/(r-1) - 1/r) = ∑_{r ∈ P} 1/(r*(r-1)) ≤ ∑_{k=2}^⌊x⌋₊ (1/(k-1) - 1/k) ≤ 1`
  have hdiff_nn : 0 ≤ ∑ r ∈ P, ((1 : ℝ) / ((r : ℝ) - 1) - (r : ℝ)⁻¹) := by
    refine Finset.sum_nonneg fun r hr => ?_
    have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hr).2.two_le
    rw [one_div]
    have : (r : ℝ)⁻¹ ≤ ((r : ℝ) - 1)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    linarith
  have hdiff_le : ∑ r ∈ P, ((1 : ℝ) / ((r : ℝ) - 1) - (r : ℝ)⁻¹) ≤ 2 := by
    have hsub : P ⊆ Finset.Icc 2 (max 2 ⌊x⌋₊) := by
      intro r hr
      have hr1 := Finset.mem_filter.mp hr
      exact Finset.mem_Icc.mpr ⟨hr1.2.two_le, le_trans (Finset.mem_Icc.mp hr1.1).2 (le_max_right _ _)⟩
    have hterm_le : ∀ n ∈ Finset.Icc 2 (max 2 ⌊x⌋₊),
        (0 : ℝ) ≤ (1 : ℝ) / ((n : ℝ) - 1) - (n : ℝ)⁻¹ := by
      intro n hn
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [one_div]; have : (n : ℝ)⁻¹ ≤ ((n : ℝ) - 1)⁻¹ := inv_anti₀ (by linarith) (by linarith); linarith
    have htele : ∀ M : ℕ, 2 ≤ M →
        ∑ n ∈ Finset.Icc 2 M, ((1 : ℝ) / ((n : ℝ) - 1) - (n : ℝ)⁻¹) = 1 - (M : ℝ)⁻¹ := by
      intro M hM
      induction M with
      | zero => omega
      | succ k ih =>
        rcases eq_or_lt_of_le hM with h2 | hk2
        · have hk1 : k = 1 := by omega
          subst hk1
          norm_num
        · have hIcc : Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) := by
            ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.sum_insert (by simp), ih (by omega)]
          push_cast
          have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
          field_simp [hk0]
          ring
    calc ∑ r ∈ P, ((1 : ℝ) / ((r : ℝ) - 1) - (r : ℝ)⁻¹)
        ≤ ∑ n ∈ Finset.Icc 2 (max 2 ⌊x⌋₊), ((1 : ℝ) / ((n : ℝ) - 1) - (n : ℝ)⁻¹) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => hterm_le n hn
      _ = 1 - ((max 2 ⌊x⌋₊ : ℕ) : ℝ)⁻¹ := htele _ (le_max_left _ _)
      _ ≤ 2 := by
          have hinv_nn : (0 : ℝ) ≤ ((max 2 ⌊x⌋₊ : ℕ) : ℝ)⁻¹ := by positivity
          linarith
  have hM := hM2 x hx3
  have hCdiv : C₂ / Real.log x ≤ C₂ / Real.log 3 :=
    div_le_div_of_nonneg_left hC₂.le (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hx3)
  have hsum_eq : ∑ r ∈ P, (1 : ℝ) / ((r : ℝ) - 1) - Real.log (Real.log x) =
      (∑ r ∈ P, ((1 : ℝ) / ((r : ℝ) - 1) - (r : ℝ)⁻¹)) +
      (∑ r ∈ P, (r : ℝ)⁻¹ - (Real.log (Real.log x) + RHDirect.Stage8MertensTheorems.meisselMertensConst)) +
      RHDirect.Stage8MertensTheorems.meisselMertensConst := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hsum_eq]
  have hab1 : |∑ r ∈ P, ((1 : ℝ) / ((r : ℝ) - 1) - (r : ℝ)⁻¹)| ≤ 2 := by
    rw [abs_of_nonneg hdiff_nn]; exact hdiff_le
  calc |(∑ r ∈ P, ((1 : ℝ) / ((r : ℝ) - 1) - (r : ℝ)⁻¹)) +
        (∑ r ∈ P, (r : ℝ)⁻¹ - (Real.log (Real.log x) + RHDirect.Stage8MertensTheorems.meisselMertensConst)) +
        RHDirect.Stage8MertensTheorems.meisselMertensConst|
      ≤ |∑ r ∈ P, ((1 : ℝ) / ((r : ℝ) - 1) - (r : ℝ)⁻¹)| +
        |∑ r ∈ P, (r : ℝ)⁻¹ - (Real.log (Real.log x) + RHDirect.Stage8MertensTheorems.meisselMertensConst)| +
        |RHDirect.Stage8MertensTheorems.meisselMertensConst| := by
          have := abs_add_le ((∑ r ∈ P, ((1 : ℝ) / ((r : ℝ) - 1) - (r : ℝ)⁻¹)) +
            (∑ r ∈ P, (r : ℝ)⁻¹ - (Real.log (Real.log x) + RHDirect.Stage8MertensTheorems.meisselMertensConst)))
            RHDirect.Stage8MertensTheorems.meisselMertensConst
          have := abs_add_le (∑ r ∈ P, ((1 : ℝ) / ((r : ℝ) - 1) - (r : ℝ)⁻¹))
            (∑ r ∈ P, (r : ℝ)⁻¹ - (Real.log (Real.log x) + RHDirect.Stage8MertensTheorems.meisselMertensConst))
          linarith
    _ ≤ 2 + C₂ / Real.log 3 + |RHDirect.Stage8MertensTheorems.meisselMertensConst| := by linarith
    _ = C₂ / Real.log 3 + |RHDirect.Stage8MertensTheorems.meisselMertensConst| + 2 := by ring

/-- Upper bound `π(N) ≤ 5 * N / log N` for sufficiently large `N` (from `siegel_walfisz_pi_real`). -/
lemma primeCount_le_five_div_log :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (((Finset.Icc 1 N).filter Nat.Prime).card : ℝ) ≤ 5 * (N : ℝ) / Real.log (N : ℝ) := by
  obtain ⟨c_sw, hc_sw, hsw_all⟩ := RHDirect.Stage10SiegelWalfiszFull.siegel_walfisz_pi_real
  obtain ⟨C_sw, hC_sw, hsw⟩ := hsw_all 1 zero_lt_one
  have htend : Tendsto (fun N : ℕ => C_sw * Real.log (N : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (N : ℝ))))
      atTop (𝓝 0) := by
    have ht1 : Tendsto (fun t : ℝ => t ^ 2 * Real.exp (-c_sw * t)) atTop (𝓝 0) := by
      have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
        (tendsto_id.const_mul_atTop hc_sw)
      have hsc := h.const_mul (c_sw ^ 2)⁻¹
      rw [mul_zero] at hsc
      refine hsc.congr fun t => ?_
      dsimp only [Function.comp_apply, id_eq]
      have hne : c_sw ^ 2 ≠ 0 := pow_ne_zero 2 hc_sw.ne'
      have hexp : Real.exp (-(c_sw * t)) = Real.exp (-c_sw * t) := by ring_nf
      rw [hexp]
      field_simp [hne]
    have ht2 : Tendsto (fun N : ℕ => Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have ht3 := (ht1.comp ht2).const_mul C_sw
    rw [mul_zero] at ht3
    refine ht3.congr' ?_
    filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN
    have hlog_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    dsimp only [Function.comp_apply]
    rw [Real.sq_sqrt hlog_nn]
    ring
  obtain ⟨N₁, hN₁⟩ := ((tendsto_order.mp htend).2 (1 : ℝ) zero_lt_one).exists_forall_of_atTop
  refine ⟨max N₁ 4, le_max_right _ _, fun N hN => ?_⟩
  have hN4 : 4 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN4R : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hlogN_ge1 : (1 : ℝ) ≤ Real.log (N : ℝ) := by
    have h4 : Real.exp 1 ≤ (N : ℝ) := by linarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (N : ℝ) := Real.log_le_log (Real.exp_pos 1) h4
  have hsw1 := hsw (N : ℝ) hN4R 1 (by rw [Real.rpow_one]; simpa using hlogN_ge1) 1 (Nat.coprime_one_left 1)
  have hcard_eq : RHDirect.Stage2DirichletAP.primeCountAP 1 1 (N : ℝ) =
      ((Finset.Icc 1 N).filter Nat.Prime).card := by
    rw [primeCountAP_eq_Icc_card]
    congr 1; ext p; simp [Nat.ModEq, Nat.mod_one]
  rw [hcard_eq] at hsw1
  simp only [Nat.totient_one, Nat.cast_one, div_one] at hsw1
  have h1 := (abs_le.mp hsw1).2
  have hli := li_le_four_mul_div_log hN4R
  have herr : C_sw * (N : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (N : ℝ))) ≤ (N : ℝ) / Real.log (N : ℝ) := by
    rw [le_div_iff₀ (by linarith)]
    have hle := (hN₁ N hNN₁).le
    calc C_sw * (N : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (N : ℝ))) * Real.log (N : ℝ)
        = (C_sw * Real.log (N : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (N : ℝ)))) * (N : ℝ) := by ring
      _ ≤ 1 * (N : ℝ) := mul_le_mul_of_nonneg_right hle (by positivity)
      _ = (N : ℝ) := one_mul _
  linarith [show 4 * (N : ℝ) / Real.log (N : ℝ) + (N : ℝ) / Real.log (N : ℝ) =
      5 * (N : ℝ) / Real.log (N : ℝ) by ring]

/-! ## Section 2: Halberstam Variance Bound via Bombieri–Vinogradov -/

/-- **Unconditional Shifted-Prime Variance Bound** (Halberstam 1956, via Bombieri–Vinogradov):
For `Y = ⌊N^(1/8)⌋₊` and `M_Y = ∑_{r ≤ Y, r prime} 1/(r - 1)`,
`∑_{p ≤ N, p prime} (ω_Y(shiftVal plus p) - M_Y)² ≤ 10 * (N / log N) * log (log N)` for all large `N`. -/
theorem shifted_prime_omegaTrunc_variance (plus : Bool) :
    ∃ N₀ : ℕ, 16 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      let Y := ⌊(N : ℝ) ^ (1 / 8 : ℝ)⌋₊
      let M_Y := ∑ r ∈ (Finset.Icc 1 Y).filter Nat.Prime, (1 : ℝ) / ((r : ℝ) - 1)
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ((omegaTrunc Y (shiftVal plus p) : ℝ) - M_Y) ^ 2 ≤
        10 * ((N : ℝ) / Real.log (N : ℝ)) * Real.log (Real.log (N : ℝ)) := by
  obtain ⟨B, C_bv, hB_pos, hCbv_pos, hBV⟩ := RHDirect.Chen.bombieri_vinogradov_primes 3
  obtain ⟨C_m, hCm_pos, hMert⟩ := sum_prime_inv_sub_one_asymp
  obtain ⟨N_pi, _, hpi_le⟩ := primeCount_le_five_div_log
  -- Choose `N₀` large enough that:
  -- (1) `N^(1/4) ≤ √N / (log N)^B` (i.e. `(log N)^B ≤ N^(1/4)`),
  -- (2) `Y = ⌊N^(1/8)⌋₊ ≥ 3`,
  -- (3) `(2 * M_Y + 3) * C_bv / (log N)^2 ≤ log (log N)`,
  -- (4) `M_Y ≤ (3/2) * log (log N)` and `1 ≤ log (log N)`.
  have htend_B : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ B / (N : ℝ) ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    set kB : ℕ := ⌈B⌉₊
    have hBk : B ≤ (kB : ℝ) := Nat.le_ceil B
    have h0 : Tendsto (fun x : ℝ => (Real.log x) ^ kB / x ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
      have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero kB).comp
        (Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 4))
      have hsc := h.const_mul (((1 / 4 : ℝ) ^ kB)⁻¹)
      rw [mul_zero] at hsc
      refine hsc.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      dsimp only [Function.comp_apply]
      rw [Real.rpow_def_of_pos (by linarith : 0 < x), Real.exp_neg, mul_pow]
      have hrew : (1 / 4 : ℝ) * Real.log x = Real.log x * (1 / 4) := by ring
      rw [hrew]
      have hne : ((1 / 4 : ℝ) ^ kB) ≠ 0 := pow_ne_zero kB (by norm_num)
      field_simp [hne]
    refine squeeze_zero' ?_ ?_ (h0.comp tendsto_natCast_atTop_atTop)
    · filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN
      have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
      positivity
    · filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN
      dsimp only [Function.comp_apply]
      have hlog1 : 1 ≤ Real.log (N : ℝ) := by
        have h4 : Real.exp 1 ≤ (N : ℝ) := by
          have : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          linarith [Real.exp_one_lt_d9]
        calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
          _ ≤ Real.log (N : ℝ) := Real.log_le_log (Real.exp_pos 1) h4
      have hpow : (Real.log (N : ℝ)) ^ B ≤ (Real.log (N : ℝ)) ^ kB := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hlog1 hBk
      exact div_le_div_of_nonneg_right hpow (by positivity)
  obtain ⟨N₁, hN₁⟩ := ((tendsto_order.mp htend_B).2 (1 : ℝ) zero_lt_one).exists_forall_of_atTop
  have htend_ll : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₂, hN₂⟩ := (tendsto_atTop.mp htend_ll (2 * C_m + 6 * C_bv + 10)).exists_forall_of_atTop
  set N₀ : ℕ := max (max (max N₁ N₂) N_pi) (4 ^ 8)
  refine ⟨N₀, by norm_num at *; omega, fun N hN => ?_⟩
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hNNpi : N_pi ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN48 : 4 ^ 8 ≤ N := le_trans (le_max_right _ _) hN
  have hN4R : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 4 ≤ N)
  have hNR_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hll_big : 2 * C_m + 6 * C_bv + 10 ≤ Real.log (Real.log (N : ℝ)) := hN₂ N hNN₂
  have hlogN_ge_ll : Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) :=
    (Real.log_le_sub_one_of_pos hlogN_pos).trans (by linarith)
  set Y : ℕ := ⌊(N : ℝ) ^ (1 / 8 : ℝ)⌋₊
  have hY_ge4 : 4 ≤ Y := by
    apply Nat.le_floor
    have h1 : ((4 : ℝ) ^ (8 : ℕ)) ^ (1 / 8 : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hN48) (by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h1
    norm_num at h1
    exact h1
  set Q_pr : Finset ℕ := (Finset.Icc 1 Y).filter Nat.Prime
  set PrN : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  set M_Y : ℝ := ∑ r ∈ Q_pr, (1 : ℝ) / ((r : ℝ) - 1)
  set πN : ℝ := (PrN.card : ℝ)
  have hMY_nn : 0 ≤ M_Y := Finset.sum_nonneg fun r hr => by
    have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hr).2.two_le
    have : (0 : ℝ) < (r : ℝ) - 1 := by linarith
    positivity
  -- Bound `M_Y ≤ (3/2) * log (log N)`
  have hMY_le : M_Y ≤ (3 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) := by
    have hM := hMert (Y : ℝ) (by exact_mod_cast (by omega : 3 ≤ Y))
    rw [Nat.floor_natCast] at hM
    have h1 := (abs_le.mp hM).2
    have hY_le_N : (Y : ℝ) ≤ (N : ℝ) := by
      calc (Y : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ) := Nat.floor_le (by positivity)
        _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = (N : ℝ) := Real.rpow_one _
    have hllY_le : Real.log (Real.log (Y : ℝ)) ≤ Real.log (Real.log (N : ℝ)) :=
      Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < Y)))
        (Real.log_le_log (by positivity) hY_le_N)
    linarith
  -- Bombieri–Vinogradov bound at `x = N`
  set Q_bv : ℕ := ⌊Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B⌋₊
  have hY2_le_Qbv : Y * Y ≤ Q_bv := by
    apply Nat.le_floor
    have hY_le : (Y : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ) := Nat.floor_le (by positivity)
    have hY2 : ((Y * Y : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
      push_cast
      calc (Y : ℝ) * (Y : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ) * (N : ℝ) ^ (1 / 8 : ℝ) :=
            mul_le_mul hY_le hY_le (Nat.cast_nonneg _) (by positivity)
        _ = (N : ℝ) ^ (1 / 4 : ℝ) := by rw [← Real.rpow_add hNR_pos]; norm_num
    have hlogB_le : (Real.log (N : ℝ)) ^ B ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
      have hlt := (hN₁ N hNN₁).le
      exact (div_le_one (by positivity)).mp hlt
    have hdiv_ge : (N : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B := by
      rw [le_div_iff₀ (by positivity)]
      calc (N : ℝ) ^ (1 / 4 : ℝ) * (Real.log (N : ℝ)) ^ B
          ≤ (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_left hlogB_le (by positivity)
        _ = Real.sqrt (N : ℝ) := by rw [← Real.rpow_add hNR_pos, Real.sqrt_eq_rpow]; norm_num
    exact hY2.trans hdiv_ge
  -- Define the AP error `err d` for `d ≥ 1`
  let err (d : ℕ) : ℝ :=
    |(RHDirect.Stage2DirichletAP.primeCountAP d (shiftRes plus d) (N : ℝ) : ℝ) - πN / (d.totient : ℝ)|
  -- Show `err d ≤ BV_term d` for `d ∈ Icc 1 Q_bv`
  let bvTerm (d : ℕ) : ℝ :=
    if h : ((Finset.range d).filter (fun a => Nat.Coprime a d)).Nonempty then
      ((Finset.range d).filter (fun a => Nat.Coprime a d)).sup' h
        (fun a => |(RHDirect.Stage2DirichletAP.primeCountAP d a (N : ℝ) : ℝ) -
          (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)|)
    else 0
  have hPrN_eq_range : (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) = πN := by
    dsimp only [πN, PrN]
    congr 2
    rw [Nat.floor_natCast]
    ext p; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨hlt, hpr⟩; exact ⟨⟨hpr.pos, by omega⟩, hpr⟩
    · rintro ⟨⟨_, hle⟩, hpr⟩; exact ⟨by omega, hpr⟩
  have herr_le_bv : ∀ d : ℕ, 1 ≤ d → err d ≤ bvTerm d := by
    intro d hd1
    have hres_lt : shiftRes plus d % d < d := Nat.mod_lt _ (by omega)
    have hcop_mod : Nat.Coprime (shiftRes plus d % d) d := by
      have hcop := shiftRes_coprime plus hd1
      rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]
      exact hcop.gcd_eq_one
    have hmem : shiftRes plus d % d ∈ (Finset.range d).filter (fun a => Nat.Coprime a d) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hres_lt, hcop_mod⟩
    have hne : ((Finset.range d).filter (fun a => Nat.Coprime a d)).Nonempty := ⟨_, hmem⟩
    dsimp only [bvTerm]
    rw [dif_pos hne]
    have hap_eq : RHDirect.Stage2DirichletAP.primeCountAP d (shiftRes plus d) (N : ℝ) =
        RHDirect.Stage2DirichletAP.primeCountAP d (shiftRes plus d % d) (N : ℝ) := by
      unfold RHDirect.Stage2DirichletAP.primeCountAP
      congr 1; ext p; simp [Nat.ModEq]
    dsimp only [err]
    rw [hap_eq, ← hPrN_eq_range]
    exact Finset.le_sup' (fun a => |(RHDirect.Stage2DirichletAP.primeCountAP d a (N : ℝ) : ℝ) -
      (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)|) hmem
  have hBV_sum : ∑ d ∈ Finset.Icc 1 Q_bv, bvTerm d ≤ C_bv * (N : ℝ) / (Real.log (N : ℝ)) ^ (3 : ℝ) := by
    simpa [bvTerm, Q_bv] using hBV (N : ℝ) hN4R
  have hBV_sum' : ∑ d ∈ Finset.Icc 1 Q_bv, bvTerm d ≤ C_bv * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
    simpa [Real.rpow_natCast] using hBV_sum
  have hbvTerm_nn : ∀ d : ℕ, 0 ≤ bvTerm d := by
    intro d
    dsimp only [bvTerm]
    split_ifs with h
    · obtain ⟨a, ha⟩ := h
      exact le_trans (abs_nonneg _)
        (Finset.le_sup' (fun a => |(RHDirect.Stage2DirichletAP.primeCountAP d a (N : ℝ) : ℝ) -
          (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)|) ha)
    · exact le_rfl
  -- Step 1: First moment of `ω_Y`
  have hmom1_eq : ∑ p ∈ PrN, (omegaTrunc Y (shiftVal plus p) : ℝ) =
      ∑ r ∈ Q_pr, (RHDirect.Stage2DirichletAP.primeCountAP r (shiftRes plus r) (N : ℝ) : ℝ) := by
    have h1 : ∀ p ∈ PrN, (omegaTrunc Y (shiftVal plus p) : ℝ) =
        ∑ r ∈ Q_pr, if r ∣ shiftVal plus p then (1 : ℝ) else 0 := by
      intro p _
      unfold omegaTrunc
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      have hfilt : (Finset.Icc 1 Y).filter (fun r => r.Prime ∧ r ∣ shiftVal plus p) =
          Q_pr.filter (fun r => r ∣ shiftVal plus p) := by
        ext r; simp [Q_pr, Finset.mem_filter]; tauto
      rw [hfilt, Finset.sum_filter]
      simp
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr_pr : r.Prime := (Finset.mem_filter.mp hr).2
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, primeCountAP_eq_Icc_card]
    congr 2
    ext p
    simp only [PrN, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpI, hpr⟩, hd⟩
      exact ⟨hpI, hpr, (dvd_shiftVal_iff_modEq plus hr_pr.pos hpr.pos).mp hd⟩
    · rintro ⟨hpI, hpr, hmod⟩
      exact ⟨⟨hpI, hpr⟩, (dvd_shiftVal_iff_modEq plus hr_pr.pos hpr.pos).mpr hmod⟩
  have hmom1_err : |∑ p ∈ PrN, (omegaTrunc Y (shiftVal plus p) : ℝ) - πN * M_Y| ≤
      ∑ r ∈ Q_pr, err r := by
    rw [hmom1_eq]
    have hmain : πN * M_Y = ∑ r ∈ Q_pr, πN / (r.totient : ℝ) := by
      dsimp only [M_Y]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr_pr : r.Prime := (Finset.mem_filter.mp hr).2
      rw [Nat.totient_prime hr_pr, Nat.cast_sub hr_pr.one_lt.le, Nat.cast_one, mul_one_div]
    rw [hmain, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  -- Step 2: Second moment of `ω_Y`
  set PairsLt : Finset (ℕ × ℕ) := (Q_pr ×ˢ Q_pr).filter (fun rr => rr.1 < rr.2)
  have hmom2_eq : ∑ p ∈ PrN, (omegaTrunc Y (shiftVal plus p) : ℝ) ^ 2 =
      ∑ r ∈ Q_pr, (RHDirect.Stage2DirichletAP.primeCountAP r (shiftRes plus r) (N : ℝ) : ℝ) +
      2 * ∑ rr ∈ PairsLt,
        (RHDirect.Stage2DirichletAP.primeCountAP (rr.1 * rr.2) (shiftRes plus (rr.1 * rr.2)) (N : ℝ) : ℝ) := by
    have hsq : ∀ p ∈ PrN, (omegaTrunc Y (shiftVal plus p) : ℝ) ^ 2 =
        (∑ r ∈ Q_pr, if r ∣ shiftVal plus p then (1 : ℝ) else 0) +
        2 * ∑ rr ∈ PairsLt, if rr.1 * rr.2 ∣ shiftVal plus p then (1 : ℝ) else 0 := by
      intro p _
      set S := Q_pr.filter (fun r => r ∣ shiftVal plus p)
      have hcard : (omegaTrunc Y (shiftVal plus p) : ℝ) = (S.card : ℝ) := by
        unfold omegaTrunc
        congr 2; ext r; simp [S, Q_pr, Finset.mem_filter]; tauto
      have hdiag : ∑ r ∈ Q_pr, (if r ∣ shiftVal plus p then (1 : ℝ) else 0) = (S.card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hoff : ∑ rr ∈ PairsLt, (if rr.1 * rr.2 ∣ shiftVal plus p then (1 : ℝ) else 0) =
          (((S ×ˢ S).filter (fun rr => rr.1 < rr.2)).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 2
        ext ⟨r₁, r₂⟩
        simp only [PairsLt, S, Finset.mem_filter, Finset.mem_product]
        constructor
        · rintro ⟨⟨⟨hr₁, hr₂⟩, hlt⟩, hdvd⟩
          have h1 : r₁ ∣ shiftVal plus p := dvd_trans (dvd_mul_right r₁ r₂) hdvd
          have h2 : r₂ ∣ shiftVal plus p := dvd_trans (dvd_mul_left r₂ r₁) hdvd
          exact ⟨⟨⟨hr₁, h1⟩, ⟨hr₂, h2⟩⟩, hlt⟩
        · rintro ⟨⟨⟨hr₁, h1⟩, ⟨hr₂, h2⟩⟩, hlt⟩
          have hpr1 : r₁.Prime := (Finset.mem_filter.mp hr₁).2
          have hpr2 : r₂.Prime := (Finset.mem_filter.mp hr₂).2
          have hcop : Nat.Coprime r₁ r₂ := (Nat.coprime_primes hpr1 hpr2).mpr (by omega)
          exact ⟨⟨⟨hr₁, hr₂⟩, hlt⟩, hcop.mul_dvd_of_dvd_of_dvd h1 h2⟩
      -- Partition `S ×ˢ S` into `r₁ = r₂`, `r₁ < r₂`, and `r₂ < r₁`
      have hcard_sq : S.card * S.card =
          S.card + 2 * ((S ×ˢ S).filter (fun rr => rr.1 < rr.2)).card := by
        set Tlt := (S ×ˢ S).filter (fun rr => rr.1 < rr.2)
        set Tgt := (S ×ˢ S).filter (fun rr => rr.2 < rr.1)
        set Teq := (S ×ˢ S).filter (fun rr => rr.1 = rr.2)
        have hswap : Tgt.card = Tlt.card := by
          refine Finset.card_bij (fun rr _ => (rr.2, rr.1)) ?_ ?_ ?_
          · intro rr hrr
            have h1 := Finset.mem_filter.mp hrr
            have h2 := Finset.mem_product.mp h1.1
            exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2.2, h2.1⟩, h1.2⟩
          · intro a _ b _ h; cases a; cases b; simp_all
          · intro rr hrr
            have h1 := Finset.mem_filter.mp hrr
            have h2 := Finset.mem_product.mp h1.1
            exact ⟨(rr.2, rr.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2.2, h2.1⟩, h1.2⟩, rfl⟩
        have hdiag_card : Teq.card = S.card := by
          refine Finset.card_bij (fun rr _ => rr.1) ?_ ?_ ?_
          · intro rr hrr; exact (Finset.mem_product.mp (Finset.mem_filter.mp hrr).1).1
          · intro a ha b hb h
            have ha' := (Finset.mem_filter.mp ha).2
            have hb' := (Finset.mem_filter.mp hb).2
            exact Prod.ext h (by rw [← ha', ← hb', h])
          · intro r hr
            exact ⟨(r, r), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr, hr⟩, rfl⟩, rfl⟩
        have hpart : S ×ˢ S = Teq ∪ (Tlt ∪ Tgt) := by
          ext ⟨a, b⟩
          simp only [Teq, Tlt, Tgt, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
          constructor
          · intro h; rcases lt_trichotomy a b with hlt | heq | hgt
            · right; left; exact ⟨h, hlt⟩
            · left; exact ⟨h, heq⟩
            · right; right; exact ⟨h, hgt⟩
          · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        have hd1 : Disjoint Teq (Tlt ∪ Tgt) := by
          rw [Finset.disjoint_left]; intro ⟨a, b⟩ h1 h2
          have heq := (Finset.mem_filter.mp h1).2
          rcases Finset.mem_union.mp h2 with h | h <;> have := (Finset.mem_filter.mp h).2 <;> omega
        have hd2 : Disjoint Tlt Tgt := by
          rw [Finset.disjoint_left]; intro ⟨a, b⟩ h1 h2
          have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
        have htot := congrArg Finset.card hpart
        rw [Finset.card_product, Finset.card_union_of_disjoint hd1,
          Finset.card_union_of_disjoint hd2, hdiag_card, hswap] at htot
        omega
      rw [hcard, hdiag, hoff, sq]
      exact_mod_cast hcard_sq
    rw [Finset.sum_congr rfl hsq, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr_pr : r.Prime := (Finset.mem_filter.mp hr).2
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, primeCountAP_eq_Icc_card]
      congr 2; ext p; simp only [PrN, Finset.mem_filter]
      exact ⟨fun ⟨⟨hI, hp⟩, hd⟩ => ⟨hI, hp, (dvd_shiftVal_iff_modEq plus hr_pr.pos hp.pos).mp hd⟩,
             fun ⟨hI, hp, hm⟩ => ⟨⟨hI, hp⟩, (dvd_shiftVal_iff_modEq plus hr_pr.pos hp.pos).mpr hm⟩⟩
    · congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun rr hrr => ?_
      have hrr1 := Finset.mem_filter.mp hrr
      have hrrp := Finset.mem_product.mp hrr1.1
      have hpr1 : rr.1.Prime := (Finset.mem_filter.mp hrrp.1).2
      have hpr2 : rr.2.Prime := (Finset.mem_filter.mp hrrp.2).2
      have hpos : 1 ≤ rr.1 * rr.2 := Nat.mul_pos hpr1.pos hpr2.pos
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, primeCountAP_eq_Icc_card]
      congr 2; ext p; simp only [PrN, Finset.mem_filter]
      exact ⟨fun ⟨⟨hI, hp⟩, hd⟩ => ⟨hI, hp, (dvd_shiftVal_iff_modEq plus hpos hp.pos).mp hd⟩,
             fun ⟨hI, hp, hm⟩ => ⟨⟨hI, hp⟩, (dvd_shiftVal_iff_modEq plus hpos hp.pos).mpr hm⟩⟩
  -- Bound the off-diagonal main term: `2 * ∑_{rr ∈ PairsLt} πN / φ(rr.1 * rr.2) ≤ πN * M_Y²`
  have hoff_main_le :
      2 * ∑ rr ∈ PairsLt, πN / ((rr.1 * rr.2).totient : ℝ) ≤ πN * M_Y ^ 2 := by
    let g : ℕ × ℕ → ℝ := fun rr => ((1 : ℝ) / ((rr.1 : ℝ) - 1)) * ((1 : ℝ) / ((rr.2 : ℝ) - 1))
    have hg_nn : ∀ rr ∈ Q_pr ×ˢ Q_pr, 0 ≤ g rr := by
      intro rr hrr
      have h1 : (2 : ℝ) ≤ (rr.1 : ℝ) := by exact_mod_cast (Finset.mem_filter.mp (Finset.mem_product.mp hrr).1).2.two_le
      have h2 : (2 : ℝ) ≤ (rr.2 : ℝ) := by exact_mod_cast (Finset.mem_filter.mp (Finset.mem_product.mp hrr).2).2.two_le
      have h1p : (0 : ℝ) < (rr.1 : ℝ) - 1 := by linarith
      have h2p : (0 : ℝ) < (rr.2 : ℝ) - 1 := by linarith
      dsimp only [g]; positivity
    have hsum_sq : M_Y ^ 2 = ∑ rr ∈ Q_pr ×ˢ Q_pr, g rr := by
      rw [sq]
      dsimp only [M_Y, g]
      rw [Finset.sum_mul_sum, Finset.sum_product]
    set PairsGt : Finset (ℕ × ℕ) := (Q_pr ×ˢ Q_pr).filter (fun rr => rr.2 < rr.1)
    have hdisj_lg : Disjoint PairsLt PairsGt := by
      rw [Finset.disjoint_left]; intro rr h1 h2
      have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
    have hswap_sum : ∑ rr ∈ PairsGt, g rr = ∑ rr ∈ PairsLt, g rr := by
      refine Finset.sum_bij (fun rr _ => (rr.2, rr.1)) ?_ ?_ ?_ ?_
      · intro rr hrr
        have h1 := Finset.mem_filter.mp hrr
        have h2 := Finset.mem_product.mp h1.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2.2, h2.1⟩, h1.2⟩
      · intro a _ b _ h; cases a; cases b; simp_all
      · intro rr hrr
        have h1 := Finset.mem_filter.mp hrr
        have h2 := Finset.mem_product.mp h1.1
        exact ⟨(rr.2, rr.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2.2, h2.1⟩, h1.2⟩, rfl⟩
      · intro rr _; dsimp only [g]; ring
    have h2_le_sq : 2 * ∑ rr ∈ PairsLt, g rr ≤ M_Y ^ 2 := by
      rw [hsum_sq]
      calc 2 * ∑ rr ∈ PairsLt, g rr
          = ∑ rr ∈ PairsLt, g rr + ∑ rr ∈ PairsGt, g rr := by rw [two_mul, hswap_sum]
        _ = ∑ rr ∈ PairsLt ∪ PairsGt, g rr := (Finset.sum_union hdisj_lg).symm
        _ ≤ ∑ rr ∈ Q_pr ×ˢ Q_pr, g rr :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
              (fun rr hrr _ => hg_nn rr hrr)
    have hrew : ∑ rr ∈ PairsLt, πN / ((rr.1 * rr.2).totient : ℝ) = πN * ∑ rr ∈ PairsLt, g rr := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun rr hrr => ?_
      have h1 := Finset.mem_filter.mp hrr
      have h2 := Finset.mem_product.mp h1.1
      have hp1 : rr.1.Prime := (Finset.mem_filter.mp h2.1).2
      have hp2 : rr.2.Prime := (Finset.mem_filter.mp h2.2).2
      have hcop : Nat.Coprime rr.1 rr.2 := (Nat.coprime_primes hp1 hp2).mpr (by omega)
      rw [Nat.totient_mul hcop, Nat.totient_prime hp1, Nat.totient_prime hp2]
      have hcast : (((rr.1 - 1) * (rr.2 - 1) : ℕ) : ℝ) = ((rr.1 : ℝ) - 1) * ((rr.2 : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub hp1.one_lt.le, Nat.cast_sub hp2.one_lt.le, Nat.cast_one]
      rw [hcast]
      have h1ne : (rr.1 : ℝ) - 1 ≠ 0 := by
        have h2 : (2 : ℝ) ≤ (rr.1 : ℝ) := by exact_mod_cast hp1.two_le
        linarith
      have h2ne : (rr.2 : ℝ) - 1 ≠ 0 := by
        have h2 : (2 : ℝ) ≤ (rr.2 : ℝ) := by exact_mod_cast hp2.two_le
        linarith
      dsimp only [g]
      field_simp [h1ne, h2ne]
    rw [hrew]
    have hπ_nn : 0 ≤ πN := Nat.cast_nonneg _
    nlinarith
  -- Bound the BV error sums
  have herr1_le : ∑ r ∈ Q_pr, err r ≤ C_bv * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
    calc ∑ r ∈ Q_pr, err r
        ≤ ∑ r ∈ Q_pr, bvTerm r := Finset.sum_le_sum fun r hr =>
          herr_le_bv r (Finset.mem_filter.mp hr).2.pos
      _ ≤ ∑ d ∈ Finset.Icc 1 Q_bv, bvTerm d := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => hbvTerm_nn d)
          intro r hr
          have hr1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
          have hr_le : r ≤ Y * Y := by nlinarith
          exact Finset.mem_Icc.mpr ⟨hr1.1, hr_le.trans hY2_le_Qbv⟩
      _ ≤ C_bv * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := hBV_sum'
  have herr2_le : ∑ rr ∈ PairsLt, err (rr.1 * rr.2) ≤ C_bv * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
    let prodFn : ℕ × ℕ → ℕ := fun rr => rr.1 * rr.2
    have hinj : Set.InjOn prodFn (PairsLt : Set (ℕ × ℕ)) := by
      intro a ha b hb heq
      have ha1 := Finset.mem_filter.mp ha
      have hb1 := Finset.mem_filter.mp hb
      have hap := Finset.mem_product.mp ha1.1
      have hbp := Finset.mem_product.mp hb1.1
      have h := prime_mul_injOn (Finset.mem_filter.mp hap.1).2 (Finset.mem_filter.mp hap.2).2
        (Finset.mem_filter.mp hbp.1).2 (Finset.mem_filter.mp hbp.2).2 ha1.2 hb1.2 heq
      exact Prod.ext h.1 h.2
    have hmaps : PairsLt.image prodFn ⊆ Finset.Icc 1 Q_bv := by
      intro d hd
      obtain ⟨rr, hrr, rfl⟩ := Finset.mem_image.mp hd
      have hrrp := Finset.mem_product.mp (Finset.mem_filter.mp hrr).1
      have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hrrp.1).1
      have h2 := Finset.mem_Icc.mp (Finset.mem_filter.mp hrrp.2).1
      exact Finset.mem_Icc.mpr ⟨Nat.mul_pos h1.1 h2.1, (Nat.mul_le_mul h1.2 h2.2).trans hY2_le_Qbv⟩
    calc ∑ rr ∈ PairsLt, err (rr.1 * rr.2)
        ≤ ∑ rr ∈ PairsLt, bvTerm (prodFn rr) := Finset.sum_le_sum fun rr hrr => by
          have hrrp := Finset.mem_product.mp (Finset.mem_filter.mp hrr).1
          exact herr_le_bv _ (Nat.mul_pos (Finset.mem_filter.mp hrrp.1).2.pos
            (Finset.mem_filter.mp hrrp.2).2.pos)
      _ = ∑ d ∈ PairsLt.image prodFn, bvTerm d := (Finset.sum_image hinj).symm
      _ ≤ ∑ d ∈ Finset.Icc 1 Q_bv, bvTerm d :=
          Finset.sum_le_sum_of_subset_of_nonneg hmaps fun d _ _ => hbvTerm_nn d
      _ ≤ C_bv * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := hBV_sum'
  -- Assemble the variance bound!
  have hvar_exp : ∑ p ∈ PrN, ((omegaTrunc Y (shiftVal plus p) : ℝ) - M_Y) ^ 2 =
      ∑ p ∈ PrN, (omegaTrunc Y (shiftVal plus p) : ℝ) ^ 2 -
      2 * M_Y * ∑ p ∈ PrN, (omegaTrunc Y (shiftVal plus p) : ℝ) + πN * M_Y ^ 2 := by
    have h1 : ∀ p ∈ PrN, ((omegaTrunc Y (shiftVal plus p) : ℝ) - M_Y) ^ 2 =
        (omegaTrunc Y (shiftVal plus p) : ℝ) ^ 2 - 2 * M_Y * (omegaTrunc Y (shiftVal plus p) : ℝ) + M_Y ^ 2 :=
      fun _ _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hmom2_le : ∑ p ∈ PrN, (omegaTrunc Y (shiftVal plus p) : ℝ) ^ 2 ≤
      πN * M_Y + ∑ r ∈ Q_pr, err r + (πN * M_Y ^ 2 + 2 * ∑ rr ∈ PairsLt, err (rr.1 * rr.2)) := by
    rw [hmom2_eq]
    have h1 : ∑ r ∈ Q_pr, (RHDirect.Stage2DirichletAP.primeCountAP r (shiftRes plus r) (N : ℝ) : ℝ) ≤
        πN * M_Y + ∑ r ∈ Q_pr, err r := by
      have := (abs_le.mp hmom1_err).2
      rw [hmom1_eq] at this
      linarith
    have h2 : 2 * ∑ rr ∈ PairsLt,
        (RHDirect.Stage2DirichletAP.primeCountAP (rr.1 * rr.2) (shiftRes plus (rr.1 * rr.2)) (N : ℝ) : ℝ) ≤
        πN * M_Y ^ 2 + 2 * ∑ rr ∈ PairsLt, err (rr.1 * rr.2) := by
      have hdiff : ∑ rr ∈ PairsLt,
          (RHDirect.Stage2DirichletAP.primeCountAP (rr.1 * rr.2) (shiftRes plus (rr.1 * rr.2)) (N : ℝ) : ℝ) ≤
          ∑ rr ∈ PairsLt, πN / ((rr.1 * rr.2).totient : ℝ) + ∑ rr ∈ PairsLt, err (rr.1 * rr.2) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun rr _ => ?_
        have := le_abs_self ((RHDirect.Stage2DirichletAP.primeCountAP (rr.1 * rr.2)
          (shiftRes plus (rr.1 * rr.2)) (N : ℝ) : ℝ) - πN / ((rr.1 * rr.2).totient : ℝ))
        dsimp only [err]
        linarith
      linarith
    linarith
  have hmom1_ge : πN * M_Y - ∑ r ∈ Q_pr, err r ≤ ∑ p ∈ PrN, (omegaTrunc Y (shiftVal plus p) : ℝ) := by
    have := (abs_le.mp hmom1_err).1; linarith
  have hvar_le : ∑ p ∈ PrN, ((omegaTrunc Y (shiftVal plus p) : ℝ) - M_Y) ^ 2 ≤
      πN * M_Y + (2 * M_Y + 1) * (∑ r ∈ Q_pr, err r) + 2 * ∑ rr ∈ PairsLt, err (rr.1 * rr.2) := by
    rw [hvar_exp]
    have hmul := mul_le_mul_of_nonneg_left hmom1_ge (by positivity : (0 : ℝ) ≤ 2 * M_Y)
    linarith
  have hpi_bd : πN ≤ 5 * (N : ℝ) / Real.log (N : ℝ) := hpi_le N hNNpi
  have hmain_bd : πN * M_Y ≤ (15 / 2 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) * Real.log (Real.log (N : ℝ)) := by
    calc πN * M_Y ≤ (5 * (N : ℝ) / Real.log (N : ℝ)) * ((3 / 2 : ℝ) * Real.log (Real.log (N : ℝ))) :=
          mul_le_mul hpi_bd hMY_le hMY_nn (by positivity)
      _ = (15 / 2 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) * Real.log (Real.log (N : ℝ)) := by ring
  have herr_tot_le : (2 * M_Y + 1) * (∑ r ∈ Q_pr, err r) + 2 * ∑ rr ∈ PairsLt, err (rr.1 * rr.2) ≤
      (5 / 2 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) * Real.log (Real.log (N : ℝ)) := by
    have hcoeff : (2 * M_Y + 3) ≤ 4 * Real.log (Real.log (N : ℝ)) := by linarith
    have hcomb : (2 * M_Y + 1) * (∑ r ∈ Q_pr, err r) + 2 * ∑ rr ∈ PairsLt, err (rr.1 * rr.2) ≤
        (2 * M_Y + 3) * (C_bv * (N : ℝ) / (Real.log (N : ℝ)) ^ 3) := by
      have h1 := mul_le_mul_of_nonneg_left herr1_le (by positivity : 0 ≤ 2 * M_Y + 1)
      linarith
    have hll_div : 4 * C_bv * Real.log (Real.log (N : ℝ)) / (Real.log (N : ℝ)) ^ 2 ≤ 1 := by
      rw [div_le_one (sq_pos_of_pos hlogN_pos)]
      have h1 : 4 * C_bv ≤ Real.log (N : ℝ) := by linarith
      nlinarith
    calc (2 * M_Y + 1) * (∑ r ∈ Q_pr, err r) + 2 * ∑ rr ∈ PairsLt, err (rr.1 * rr.2)
        ≤ (4 * Real.log (Real.log (N : ℝ))) * (C_bv * (N : ℝ) / (Real.log (N : ℝ)) ^ 3) :=
          hcomb.trans (mul_le_mul_of_nonneg_right hcoeff (by positivity))
      _ = (4 * C_bv * Real.log (Real.log (N : ℝ)) / (Real.log (N : ℝ)) ^ 2) * ((N : ℝ) / Real.log (N : ℝ)) := by
          field_simp [hlogN_pos.ne']
      _ ≤ 1 * ((N : ℝ) / Real.log (N : ℝ)) := mul_le_mul_of_nonneg_right hll_div (by positivity)
      _ ≤ (5 / 2 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) * Real.log (Real.log (N : ℝ)) := by
          have : (1 : ℝ) ≤ (5 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) := by linarith
          calc 1 * ((N : ℝ) / Real.log (N : ℝ))
              ≤ ((5 / 2 : ℝ) * Real.log (Real.log (N : ℝ))) * ((N : ℝ) / Real.log (N : ℝ)) :=
                mul_le_mul_of_nonneg_right this (by positivity)
            _ = (5 / 2 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) * Real.log (Real.log (N : ℝ)) := by ring
  linarith

/-! ## Section 3: Bloom's Lemma 2 (`lem-nt2`) via Chebyshev's Inequality -/

/-- **Bloom's Lemma 2 (`lem-nt2`)**: For both signs `plus : Bool` (`p - 1` and `p + 1`) and any
`δ > 0`, there exist `C > 0` and `N₀` such that for all `N ≥ N₀`:
`#{p ≤ N : p prime ∧ δ * log(log(shiftVal plus p)) ≤ |ω(shiftVal plus p) - log(log(shiftVal plus p))|} ≤ C * N / (log N * log(log N))`. -/
theorem shifted_prime_omega_normal_order (plus : Bool) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 16 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (((Finset.Icc 1 N).filter (fun p =>
          p.Prime ∧ δ * Real.log (Real.log (shiftVal plus p : ℝ)) ≤
            |((shiftVal plus p).primeFactors.card : ℝ) -
              Real.log (Real.log (shiftVal plus p : ℝ))|)).card : ℝ) ≤
        C * (N : ℝ) / (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) := by
  obtain ⟨N_var, _, hVar⟩ := shifted_prime_omegaTrunc_variance plus
  obtain ⟨C_m, hCm_pos, hMert⟩ := sum_prime_inv_sub_one_asymp
  -- Choose `C = 160 / δ^2 + 2`
  refine ⟨160 / δ ^ 2 + 2, by positivity, ?_⟩
  -- Pick `N₀` large enough that:
  -- (1) `N ≥ max N_var (4^8)` and `(N : ℝ)^(1/8) ≥ 4`,
  -- (2) `(δ / 4) * log(log N) ≥ C_m + 20 + 4 * δ`,
  -- (3) `√N ≤ N / (log N * log(log N))`,
  -- (4) `√N - 1 ≥ N^(1/3)` (e.g. `N ≥ 2^12`).
  have htend_ll : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₁, hN₁⟩ := (tendsto_atTop.mp htend_ll ((4 / δ) * (C_m + 20 + 4 * δ) + 10)).exists_forall_of_atTop
  -- `log N * log(log N) ≤ √N` for large `N`: since `(log N)^2 ≤ √N` for large `N`
  have htend_sq : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ 2 / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
        (Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
      have hsc := h.const_mul (4 : ℝ)
      rw [mul_zero] at hsc
      refine hsc.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      dsimp only [Function.comp_apply]
      rw [Real.rpow_def_of_pos (by linarith : 0 < x), Real.exp_neg]
      have hrew : (1 / 2 : ℝ) * Real.log x = Real.log x * (1 / 2) := by ring
      rw [mul_pow, hrew]
      ring
    refine (h0.comp tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N _
    dsimp only [Function.comp_apply]
    rw [Real.sqrt_eq_rpow]
  obtain ⟨N₂, hN₂⟩ := ((tendsto_order.mp htend_sq).2 (1 : ℝ) zero_lt_one).exists_forall_of_atTop
  set N₀ : ℕ := max (max (max N_var N₁) N₂) (4 ^ 8)
  refine ⟨N₀, by norm_num at *; omega, fun N hN => ?_⟩
  have hNNv : N_var ≤ N := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN48 : 4 ^ 8 ≤ N := le_trans (le_max_right _ _) hN
  have hNR_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hll_big : (4 / δ) * (C_m + 20 + 4 * δ) + 10 ≤ Real.log (Real.log (N : ℝ)) := hN₁ N hNN₁
  have hll_pos : 0 < Real.log (Real.log (N : ℝ)) := by
    have hnn : 0 ≤ (4 / δ) * (C_m + 20 + 4 * δ) := by positivity
    linarith
  set Y : ℕ := ⌊(N : ℝ) ^ (1 / 8 : ℝ)⌋₊
  set M_Y : ℝ := ∑ r ∈ (Finset.Icc 1 Y).filter Nat.Prime, (1 : ℝ) / ((r : ℝ) - 1)
  -- Check `Y ≥ 4` and `(Y + 1)^9 > N + 1`
  have hY_ge4 : 4 ≤ Y := by
    apply Nat.le_floor
    have h1 : ((4 : ℝ) ^ (8 : ℕ)) ^ (1 / 8 : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hN48) (by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h1
    norm_num at h1; exact h1
  have hY1_pow9 : N + 1 < (Y + 1) ^ 9 := by
    have hlt : (N : ℝ) ^ (1 / 8 : ℝ) < (Y : ℝ) + 1 := Nat.lt_floor_add_one _
    have h9 : ((N : ℝ) ^ (1 / 8 : ℝ)) ^ (9 : ℕ) < ((Y : ℝ) + 1) ^ (9 : ℕ) :=
      pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
    have hlhs : ((N : ℝ) ^ (1 / 8 : ℝ)) ^ (9 : ℕ) = (N : ℝ) * (N : ℝ) ^ (1 / 8 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNR_pos.le]
      have : (1 / 8 : ℝ) * (9 : ℕ) = 1 + 1 / 8 := by norm_num
      rw [this, Real.rpow_add hNR_pos, Real.rpow_one]
    have h4_le : (4 : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by
      have : (4 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY_ge4
      exact this.trans (Nat.floor_le (by positivity))
    have hN1_lt : ((N + 1 : ℕ) : ℝ) < ((Y + 1 : ℕ) : ℝ) ^ (9 : ℕ) := by
      push_cast
      have : (N : ℝ) + 1 ≤ (N : ℝ) * (N : ℝ) ^ (1 / 8 : ℝ) := by
        have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
        nlinarith
      linarith
    exact_mod_cast hN1_lt
  -- Bound `|M_Y - log(log N)| ≤ C_m + 3`
  have hMY_diff : |M_Y - Real.log (Real.log (N : ℝ))| ≤ C_m + 3 := by
    have hM := hMert (Y : ℝ) (by exact_mod_cast (by omega : 3 ≤ Y))
    rw [Nat.floor_natCast] at hM
    -- `log Y ∈ [log N / 8 - log 2, log N / 8]`, so `|log(log Y) - log(log N)| ≤ 3`
    have hY_le : (Y : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ) := Nat.floor_le (by positivity)
    have hY_ge : (N : ℝ) ^ (1 / 8 : ℝ) / 2 ≤ (Y : ℝ) := by
      have h1 := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 8 : ℝ))
      have h4 : (4 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY_ge4
      linarith
    have hlogY_le : Real.log (Y : ℝ) ≤ Real.log (N : ℝ) := by
      have h1 : (Y : ℝ) ≤ (N : ℝ) := by
        calc (Y : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ) := hY_le
          _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) (by norm_num)
          _ = (N : ℝ) := Real.rpow_one _
      exact Real.log_le_log (by exact_mod_cast (by omega : 0 < Y)) h1
    have hlogY_ge : Real.log (N : ℝ) / 16 ≤ Real.log (Y : ℝ) := by
      have h1 : Real.log ((N : ℝ) ^ (1 / 8 : ℝ) / 2) ≤ Real.log (Y : ℝ) :=
        Real.log_le_log (by positivity) hY_ge
      rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hNR_pos] at h1
      have hlogN_ge16 : 16 ≤ Real.log (N : ℝ) := by
        have h1 : Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) :=
          (Real.log_le_sub_one_of_pos hlogN_pos).trans (by linarith)
        have h2 : (10 : ℝ) ≤ Real.log (Real.log (N : ℝ)) := by
          have : 0 ≤ (4 / δ) * (C_m + 20 + 4 * δ) := by positivity
          linarith
        -- Actually `exp(10) > 16`, so `log N ≥ exp(10) > 16`!
        have he10 : (16 : ℝ) ≤ Real.exp 10 := by
          have h1 := Real.add_one_le_exp (10 : ℝ)
          -- `11 ≤ exp 10`, and `exp 10 = exp 5 * exp 5 ≥ 6 * 6 = 36 ≥ 16`
          have h5 : (6 : ℝ) ≤ Real.exp 5 := by linarith [Real.add_one_le_exp (5 : ℝ)]
          have h10 : Real.exp 10 = Real.exp 5 * Real.exp 5 := by rw [← Real.exp_add]; norm_num
          nlinarith
        have hle : Real.exp 10 ≤ Real.log (N : ℝ) := by
          calc Real.exp 10 ≤ Real.exp (Real.log (Real.log (N : ℝ))) := Real.exp_le_exp.mpr h2
            _ = Real.log (N : ℝ) := Real.exp_log hlogN_pos
        linarith
      have hlog2 : Real.log 2 ≤ 1 := by
        calc Real.log 2 ≤ Real.log (Real.exp 1) :=
              Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
          _ = 1 := Real.log_exp 1
      linarith
    have hllY_diff : |Real.log (Real.log (Y : ℝ)) - Real.log (Real.log (N : ℝ))| ≤ 3 := by
      have hlogY_pos : 0 < Real.log (Y : ℝ) := by linarith
      have h1 : Real.log (Real.log (Y : ℝ)) ≤ Real.log (Real.log (N : ℝ)) :=
        Real.log_le_log hlogY_pos hlogY_le
      have h2 : Real.log (Real.log (N : ℝ)) - 3 ≤ Real.log (Real.log (Y : ℝ)) := by
        have ha : Real.log (Real.log (N : ℝ) / 16) ≤ Real.log (Real.log (Y : ℝ)) :=
          Real.log_le_log (by positivity) hlogY_ge
        rw [Real.log_div hlogN_pos.ne' (by norm_num)] at ha
        have hlog16 : Real.log 16 ≤ 3 := by
          have h16e3 : (16 : ℝ) ≤ Real.exp 3 := by
            have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by
              -- `1 + 1 + 1/2 + 1/6 = 8/3 ≥ 2.66`, wait: `exp 3 = (exp 1)^3`, `exp 1 ≥ 2.71` via `Real.exp_one_gt_d9`!
              linarith [Real.exp_one_gt_d9]
            have h3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
              rw [← Real.exp_add, ← Real.exp_add]; norm_num
            nlinarith
          calc Real.log 16 ≤ Real.log (Real.exp 3) := Real.log_le_log (by norm_num) h16e3
            _ = 3 := Real.log_exp 3
        linarith
      rw [abs_le]; constructor <;> linarith
    have htri := abs_add_le (M_Y - Real.log (Real.log (Y : ℝ)))
      (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log (N : ℝ)))
    have heq : (M_Y - Real.log (Real.log (Y : ℝ))) +
        (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log (N : ℝ))) =
        M_Y - Real.log (Real.log (N : ℝ)) := by ring
    rw [heq] at htri
    linarith
  -- Split bad set `S_bad` into `p ≤ Nat.sqrt N` and `Nat.sqrt N < p`
  set S_bad := (Finset.Icc 1 N).filter (fun p =>
      p.Prime ∧ δ * Real.log (Real.log (shiftVal plus p : ℝ)) ≤
        |((shiftVal plus p).primeFactors.card : ℝ) -
          Real.log (Real.log (shiftVal plus p : ℝ))|)
  set S_lo := S_bad.filter (fun p => p ≤ Nat.sqrt N)
  set S_hi := S_bad.filter (fun p => ¬ p ≤ Nat.sqrt N)
  have hsplit : S_bad.card = S_lo.card + S_hi.card := by
    have hdisj : Disjoint S_lo S_hi := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
    have hu : S_lo ∪ S_hi = S_bad := by
      ext p; simp only [S_lo, S_hi, Finset.mem_union, Finset.mem_filter]; tauto
    rw [← hu, Finset.card_union_of_disjoint hdisj]
  -- Bound `S_lo.card ≤ √N ≤ N / (log N * log(log N))`
  have hSlo_le : (S_lo.card : ℝ) ≤ (N : ℝ) / (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) := by
    have h1 : S_lo.card ≤ Nat.sqrt N := by
      have hsub : S_lo ⊆ Finset.Icc 1 (Nat.sqrt N) := by
        intro p hp
        have h1 := Finset.mem_filter.mp hp
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp h1.1).1).1, h1.2⟩
      exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
    have h2 : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
      rw [Real.le_sqrt (Nat.cast_nonneg _) hNR_pos.le]
      have : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
      rw [sq]; exact_mod_cast this
    have h3 : Real.sqrt (N : ℝ) ≤ (N : ℝ) / (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) := by
      rw [le_div_iff₀ (mul_pos hlogN_pos hll_pos)]
      have hlog_sq : (Real.log (N : ℝ)) ^ 2 ≤ Real.sqrt (N : ℝ) :=
        (div_le_one (Real.sqrt_pos.mpr hNR_pos)).mp (hN₂ N hNN₂).le
      have hll_le_log : Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) :=
        (Real.log_le_sub_one_of_pos hlogN_pos).trans (by linarith)
      calc Real.sqrt (N : ℝ) * (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))
          ≤ Real.sqrt (N : ℝ) * (Real.log (N : ℝ) * Real.log (N : ℝ)) := by gcongr
        _ = Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2 := by ring
        _ ≤ Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := mul_le_mul_of_nonneg_left hlog_sq (Real.sqrt_nonneg _)
        _ = (N : ℝ) := Real.mul_self_sqrt hNR_pos.le
    exact ((by exact_mod_cast h1 : (S_lo.card : ℝ) ≤ (Nat.sqrt N : ℝ)).trans h2).trans h3
  -- Bound `S_hi.card` via Chebyshev on `shifted_prime_omegaTrunc_variance`
  have hShi_each : ∀ p ∈ S_hi,
      ((δ / 4 : ℝ) * Real.log (Real.log (N : ℝ))) ^ 2 ≤
        ((omegaTrunc Y (shiftVal plus p) : ℝ) - M_Y) ^ 2 := by
    intro p hp
    have hp1 := Finset.mem_filter.mp hp
    have hbad := Finset.mem_filter.mp hp1.1
    have hp_icc := Finset.mem_Icc.mp hbad.1
    have hpr : p.Prime := hbad.2.1
    have hineq := hbad.2.2
    have hp_gt_sq : Nat.sqrt N < p := by omega
    have hsh_pos : 0 < shiftVal plus p := shiftVal_pos_of_prime plus hpr
    have hsh_le : shiftVal plus p ≤ N + 1 := by
      have := hp_icc.2; cases plus <;> simp [shiftVal] <;> omega
    -- `|ω(shiftVal plus p) - ω_Y(shiftVal plus p)| ≤ 8`
    have htrunc_le := omegaTrunc_le_card_primeFactors Y (shiftVal plus p) hsh_pos.ne'
    have htrunc_diff := card_primeFactors_sub_omegaTrunc_le_eight hsh_pos.ne'
      (lt_of_le_of_lt hsh_le hY1_pow9)
    have hω_diff : |((shiftVal plus p).primeFactors.card : ℝ) - (omegaTrunc Y (shiftVal plus p) : ℝ)| ≤ 8 := by
      have h1 : (omegaTrunc Y (shiftVal plus p) : ℝ) ≤ ((shiftVal plus p).primeFactors.card : ℝ) := by
        exact_mod_cast htrunc_le
      have h2 : ((shiftVal plus p).primeFactors.card : ℝ) - (omegaTrunc Y (shiftVal plus p) : ℝ) ≤ 8 := by
        have hnat : (shiftVal plus p).primeFactors.card ≤ omegaTrunc Y (shiftVal plus p) + 8 := by omega
        have hR : ((shiftVal plus p).primeFactors.card : ℝ) ≤ (omegaTrunc Y (shiftVal plus p) : ℝ) + 8 := by
          exact_mod_cast hnat
        linarith
      rw [abs_of_nonneg (by linarith)]
      exact h2
    -- `|log(log(shiftVal plus p)) - log(log N)| ≤ 2` since `N^(1/4) ≤ shiftVal plus p ≤ N^2`
    have hsh_ge_sq : (N : ℝ) ^ (1 / 4 : ℝ) ≤ (shiftVal plus p : ℝ) := by
      have hsq_lt : Real.sqrt (N : ℝ) < (p : ℝ) := by
        have h1 : Nat.sqrt N + 1 ≤ p := hp_gt_sq
        have h2 : Real.sqrt (N : ℝ) < (Nat.sqrt N : ℝ) + 1 := by
          have hlt := Nat.lt_succ_sqrt N
          have hR : (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
            have : N < (Nat.sqrt N + 1) ^ 2 := by rw [sq]; exact hlt
            exact_mod_cast this
          rw [Real.sqrt_lt' (by positivity)]
          exact hR
        have h3 : (Nat.sqrt N : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast h1
        linarith
      have hsh_ge_pm1 : (p : ℝ) - 1 ≤ (shiftVal plus p : ℝ) := by
        cases plus
        · simp only [shiftVal, Bool.false_eq_true, ↓reduceIte]
          rw [Nat.cast_sub hpr.pos, Nat.cast_one]
        · simp only [shiftVal, ↓reduceIte]; push_cast; linarith
      have h4_le_N14 : (4 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
        have : ((4 : ℝ) ^ (4 : ℕ)) ≤ (N : ℝ) := by norm_num; exact_mod_cast (by omega : 256 ≤ N)
        calc (4 : ℝ) = ((4 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
          _ ≤ (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) this (by norm_num)
      have hN12 : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) = Real.sqrt (N : ℝ) := by
        rw [← Real.rpow_add hNR_pos, Real.sqrt_eq_rpow]; norm_num
      nlinarith
    have hsh_le_sq : (shiftVal plus p : ℝ) ≤ (N : ℝ) ^ 2 := by
      have h1 : (shiftVal plus p : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hsh_le
      have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
      nlinarith
    have hll_sh_diff : |Real.log (Real.log (shiftVal plus p : ℝ)) - Real.log (Real.log (N : ℝ))| ≤ 2 := by
      have hlog_ge : Real.log (N : ℝ) / 4 ≤ Real.log (shiftVal plus p : ℝ) := by
        have h := Real.log_le_log (by positivity) hsh_ge_sq
        rw [Real.log_rpow hNR_pos] at h
        linarith
      have hlog_le : Real.log (shiftVal plus p : ℝ) ≤ 2 * Real.log (N : ℝ) := by
        have h := Real.log_le_log (by exact_mod_cast hsh_pos) hsh_le_sq
        rw [Real.log_pow] at h
        simpa using h
      have hlog2 : Real.log 2 ≤ 1 := by
        calc Real.log 2 ≤ Real.log (Real.exp 1) :=
              Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
          _ = 1 := Real.log_exp 1
      have hlog4 : Real.log 4 ≤ 2 := by
        have : Real.log 4 = 2 * Real.log 2 := by
          have : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
          rw [this, Real.log_pow]; norm_num
        linarith
      have h1 : Real.log (Real.log (shiftVal plus p : ℝ)) ≤ Real.log (Real.log (N : ℝ)) + 2 := by
        have h := Real.log_le_log (by linarith) hlog_le
        rw [Real.log_mul (by norm_num) hlogN_pos.ne'] at h
        linarith
      have h2 : Real.log (Real.log (N : ℝ)) - 2 ≤ Real.log (Real.log (shiftVal plus p : ℝ)) := by
        have h := Real.log_le_log (by positivity) hlog_ge
        rw [Real.log_div hlogN_pos.ne' (by norm_num)] at h
        linarith
      rw [abs_le]; constructor <;> linarith
    -- Triangle inequality: `|ω_Y - M_Y| ≥ δ * log(log N) - 2*δ - (8 + 2 + C_m + 3) ≥ (δ/4) * log(log N)`
    have hll_sh_ge : Real.log (Real.log (N : ℝ)) - 2 ≤ Real.log (Real.log (shiftVal plus p : ℝ)) := by
      linarith [(abs_le.mp hll_sh_diff).1]
    have hδ_big : (δ / 4) * Real.log (Real.log (N : ℝ)) ≥ C_m + 20 + 4 * δ := by
      have h1 := mul_le_mul_of_nonneg_left hll_big (by positivity : 0 ≤ δ / 4)
      have hrew : (δ / 4) * ((4 / δ) * (C_m + 20 + 4 * δ) + 10) = (C_m + 20 + 4 * δ) + (5 / 2) * δ := by
        field_simp [hδ.ne']; ring
      linarith
    have habs_ge : (δ / 4 : ℝ) * Real.log (Real.log (N : ℝ)) ≤
        |(omegaTrunc Y (shiftVal plus p) : ℝ) - M_Y| := by
      have htri : |((shiftVal plus p).primeFactors.card : ℝ) - Real.log (Real.log (shiftVal plus p : ℝ))| ≤
          |((shiftVal plus p).primeFactors.card : ℝ) - (omegaTrunc Y (shiftVal plus p) : ℝ)| +
          |(omegaTrunc Y (shiftVal plus p) : ℝ) - M_Y| +
          |M_Y - Real.log (Real.log (N : ℝ))| +
          |Real.log (Real.log (N : ℝ)) - Real.log (Real.log (shiftVal plus p : ℝ))| := by
        have h1 := abs_add_le
          (((shiftVal plus p).primeFactors.card : ℝ) - (omegaTrunc Y (shiftVal plus p) : ℝ))
          ((omegaTrunc Y (shiftVal plus p) : ℝ) - Real.log (Real.log (shiftVal plus p : ℝ)))
        have h2 := abs_add_le
          ((omegaTrunc Y (shiftVal plus p) : ℝ) - M_Y)
          (M_Y - Real.log (Real.log (shiftVal plus p : ℝ)))
        have h3 := abs_add_le
          (M_Y - Real.log (Real.log (N : ℝ)))
          (Real.log (Real.log (N : ℝ)) - Real.log (Real.log (shiftVal plus p : ℝ)))
        have hs1 : (((shiftVal plus p).primeFactors.card : ℝ) - (omegaTrunc Y (shiftVal plus p) : ℝ)) +
            ((omegaTrunc Y (shiftVal plus p) : ℝ) - Real.log (Real.log (shiftVal plus p : ℝ))) =
            ((shiftVal plus p).primeFactors.card : ℝ) - Real.log (Real.log (shiftVal plus p : ℝ)) := by ring
        have hs2 : ((omegaTrunc Y (shiftVal plus p) : ℝ) - M_Y) +
            (M_Y - Real.log (Real.log (shiftVal plus p : ℝ))) =
            (omegaTrunc Y (shiftVal plus p) : ℝ) - Real.log (Real.log (shiftVal plus p : ℝ)) := by ring
        have hs3 : (M_Y - Real.log (Real.log (N : ℝ))) +
            (Real.log (Real.log (N : ℝ)) - Real.log (Real.log (shiftVal plus p : ℝ))) =
            M_Y - Real.log (Real.log (shiftVal plus p : ℝ)) := by ring
        rw [hs1] at h1; rw [hs2] at h2; rw [hs3] at h3
        linarith
      rw [abs_sub_comm (Real.log (Real.log (N : ℝ)))] at htri
      have hmul_sh := mul_le_mul_of_nonneg_left hll_sh_ge hδ.le
      linarith
    have hsq := pow_le_pow_left₀ (by positivity) habs_ge 2
    rwa [sq_abs] at hsq
  -- Apply Chebyshev's inequality
  have hShi_sub : S_hi ⊆ (Finset.Icc 1 N).filter Nat.Prime := by
    intro p hp
    have h1 := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_filter.mpr ⟨h1.1, h1.2.1⟩
  have hCheb : (S_hi.card : ℝ) * ((δ / 4 : ℝ) * Real.log (Real.log (N : ℝ))) ^ 2 ≤
      10 * ((N : ℝ) / Real.log (N : ℝ)) * Real.log (Real.log (N : ℝ)) := by
    calc (S_hi.card : ℝ) * ((δ / 4 : ℝ) * Real.log (Real.log (N : ℝ))) ^ 2
        = ∑ _p ∈ S_hi, ((δ / 4 : ℝ) * Real.log (Real.log (N : ℝ))) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ S_hi, ((omegaTrunc Y (shiftVal plus p) : ℝ) - M_Y) ^ 2 :=
          Finset.sum_le_sum hShi_each
      _ ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ((omegaTrunc Y (shiftVal plus p) : ℝ) - M_Y) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hShi_sub (fun _ _ _ => sq_nonneg _)
      _ ≤ 10 * ((N : ℝ) / Real.log (N : ℝ)) * Real.log (Real.log (N : ℝ)) := hVar N hNNv
  have hShi_le : (S_hi.card : ℝ) ≤
      (160 / δ ^ 2) * (N : ℝ) / (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) := by
    have hden_pos : 0 < ((δ / 4 : ℝ) * Real.log (Real.log (N : ℝ))) ^ 2 := by positivity
    have h1 := (le_div_iff₀ hden_pos).mpr hCheb
    have hrew : (10 * ((N : ℝ) / Real.log (N : ℝ)) * Real.log (Real.log (N : ℝ))) /
        ((δ / 4 : ℝ) * Real.log (Real.log (N : ℝ))) ^ 2 =
        (160 / δ ^ 2) * (N : ℝ) / (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) := by
      field_simp [hδ.ne', hlogN_pos.ne', hll_pos.ne']; ring
    rwa [hrew] at h1
  have hcast : (S_bad.card : ℝ) = (S_lo.card : ℝ) + (S_hi.card : ℝ) := by exact_mod_cast hsplit
  rw [hcast]
  have h1_le_2 : (N : ℝ) / (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) ≤
      2 * (N : ℝ) / (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) := by
    have hnn : 0 ≤ (N : ℝ) / (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) := by positivity
    linarith [show 2 * (N : ℝ) / (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) =
      2 * ((N : ℝ) / (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) by ring]
  linarith [show (160 / δ ^ 2) * (N : ℝ) / (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) +
      2 * (N : ℝ) / (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) =
      (160 / δ ^ 2 + 2) * (N : ℝ) / (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) by ring]

end PPL024
