import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.IsPrimePow
import Prize.PPL024_AnalyticMertens
import Prize.PPL024_AnalyticSmooth
import Prize.PPL024_AnalyticOmega

/-!
# PPL 024 Analytic Foundations — Unified Shifted-Prime Bundle & Reduction

Unconditional assembly of Bloom's Section 1 & Section 2 (`arXiv:2305.02689`):
1. `recSum_le_of_dyadic_block_bound`: clean dyadic block-to-harmonic summation helper.
2. `shifted_prime_filtered_set_exists`: for both signs `plus : Bool` (`p - 1` and `p + 1`),
   any modulus `q ≥ 1`, and any cutoff `X`, constructs `ε₀ > 0` such that for every `0 < ε ≤ ε₀`
   and every `y ≥ 4`, there exist `w, z` (`y ≤ w`, `4 * w ≤ z`) and `N₀` such that for all `N ≥ N₀`,
   the filtered shifted-prime set `B' ⊆ {m ∈ [2, N] : (unshiftPrime plus q m).Prime ∧ X < unshiftPrime plus q m}`
   satisfies ALL FIVE hypotheses of Bloom's Proposition 2 (`prop-tech`):
   - (1) `∀ m ∈ B', ∀ r, IsPrimePow r → r ∣ m → (r : ℝ) ≤ (m : ℝ) ^ (1 - ε)`
   - (2) `∀ m ∈ B', |(m.primeFactors.card : ℝ) - log(log m)| ≤ log(log m) / 1000`
   - (3) `∀ m ∈ B', ∃ d₁, y ≤ d₁ ∧ d₁ < w ∧ d₁ ∣ m`
   - (4) `∀ m ∈ B', ∃ d₂, 4 * w ≤ d₂ ∧ d₂ < z ∧ d₂ ∣ m`
   - (5) `(1 / 4 : ℝ) * log(log N) ≤ ∑ m ∈ B', (1 : ℝ) / m`.
3. `prop_tech_of_th_techmain`: Bloom's Proposition 2 (`prop-tech`) deduced unconditionally from
   Bloom's Proposition 1 (`th-techmain`, the constant-`c` Fourier/combinatorial core).
4. `exists_shifted_prime_inv_q_of_prop_tech` & `sun_conjecture_of_th_techmain`:
   Complete unconditional reduction of Zhi-Wei Sun's conjecture (both `p - 1` and `p + 1`,
   for every positive rational `r : ℚ`) to Bloom's Proposition 1 (`th-techmain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset Filter Topology

namespace PPL024

/-! ## Section 1: Dyadic Block Reciprocal-Sum Helper -/

/-- If for all `k ≥ K₀`, the dyadic block `{m ∈ (2^k, 2^{k+1}] : P m}` has size at most
`β * 2^k / k`, then for all `N ≥ 4`:
`∑_{m ∈ (Icc 2 N).filter P} 1/m ≤ β * log(log N) + (2^K₀ + 2 * β)`. -/
lemma recSum_le_of_dyadic_block_bound (P : ℕ → Prop) [DecidablePred P]
    {β : ℝ} (hβ : 0 ≤ β) {K₀ : ℕ} (hK₀ : 1 ≤ K₀)
    (hblk : ∀ k : ℕ, K₀ ≤ k →
      (((Finset.Icc 1 (2 ^ (k + 1))).filter (fun m => 2 ^ k < m ∧ P m)).card : ℝ) ≤
        β * ((2 ^ k : ℕ) : ℝ) / (k : ℝ)) :
    ∀ N : ℕ, 4 ≤ N →
      ∑ m ∈ (Finset.Icc 2 N).filter P, (1 : ℝ) / (m : ℝ) ≤
        β * Real.log (Real.log (N : ℝ)) + (((2 ^ K₀ : ℕ) : ℝ) + 2 * β) := by
  intro N hN4
  set S := (Finset.Icc 2 N).filter P
  set S_lo := S.filter (fun m => m ≤ 2 ^ K₀)
  set S_hi := S.filter (fun m => ¬ m ≤ 2 ^ K₀)
  have hsplit : ∑ m ∈ S, (1 : ℝ) / (m : ℝ) =
      ∑ m ∈ S_lo, (1 : ℝ) / (m : ℝ) + ∑ m ∈ S_hi, (1 : ℝ) / (m : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not S (fun m => m ≤ 2 ^ K₀) _).symm
  have hlo : ∑ m ∈ S_lo, (1 : ℝ) / (m : ℝ) ≤ ((2 ^ K₀ : ℕ) : ℝ) := by
    calc ∑ m ∈ S_lo, (1 : ℝ) / (m : ℝ)
        ≤ ∑ _m ∈ S_lo, (1 : ℝ) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm2 : 2 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1).1
          rw [one_div]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ m))
      _ = (S_lo.card : ℝ) := by simp
      _ ≤ ((2 ^ K₀ : ℕ) : ℝ) := by
          have hsub : S_lo ⊆ Finset.Icc 1 (2 ^ K₀) := by
            intro m hm
            have h1 := Finset.mem_filter.mp hm
            have h2 := Finset.mem_Icc.mp (Finset.mem_filter.mp h1.1).1
            exact Finset.mem_Icc.mpr ⟨by omega, h1.2⟩
          have h2pos : 1 ≤ 2 ^ K₀ := Nat.one_le_pow _ _ (by norm_num)
          exact_mod_cast (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
  set K : ℕ := Nat.log 2 N
  have hK1 : 1 ≤ K := Nat.le_log_of_pow_le (by norm_num) (by omega : 2 ^ 1 ≤ N)
  have hhi_cover : S_hi ⊆ (Finset.Icc K₀ K).biUnion (fun k => S_hi.filter (fun m => 2 ^ k < m ∧ m ≤ 2 ^ (k + 1))) := by
    intro m hm
    have h1 := Finset.mem_filter.mp hm
    have h2 := Finset.mem_Icc.mp (Finset.mem_filter.mp h1.1).1
    have hm_gt : 2 ^ K₀ < m := by omega
    set k := Nat.log 2 (m - 1)
    have hk_ge : K₀ ≤ k := Nat.le_log_of_pow_le (by norm_num) (by omega : 2 ^ K₀ ≤ m - 1)
    have hk_le : k ≤ K := Nat.log_mono_right (by omega)
    have hpow_le : 2 ^ k ≤ m - 1 := Nat.pow_log_le_self 2 (by omega)
    have hlt_pow : m - 1 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (m - 1)
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk_ge, hk_le⟩,
      Finset.mem_filter.mpr ⟨hm, by omega, by omega⟩⟩
  have hpair : (Finset.Icc K₀ K : Set ℕ).PairwiseDisjoint
      (fun k => S_hi.filter (fun m => 2 ^ k < m ∧ m ≤ 2 ^ (k + 1))) := by
    intro k₁ _ k₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro m hm₁ hm₂
    have h1 := (Finset.mem_filter.mp hm₁).2
    have h2 := (Finset.mem_filter.mp hm₂).2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : 2 ^ (k₁ + 1) ≤ 2 ^ k₂ := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have : 2 ^ (k₂ + 1) ≤ 2 ^ k₁ := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hhi_sum : ∑ m ∈ S_hi, (1 : ℝ) / (m : ℝ) ≤
      ∑ k ∈ Finset.Icc K₀ K, ∑ m ∈ S_hi.filter (fun m => 2 ^ k < m ∧ m ≤ 2 ^ (k + 1)), (1 : ℝ) / (m : ℝ) := by
    calc ∑ m ∈ S_hi, (1 : ℝ) / (m : ℝ)
        ≤ ∑ m ∈ (Finset.Icc K₀ K).biUnion (fun k => S_hi.filter (fun m => 2 ^ k < m ∧ m ≤ 2 ^ (k + 1))),
            (1 : ℝ) / (m : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hhi_cover fun _ _ _ => by positivity
      _ = ∑ k ∈ Finset.Icc K₀ K, ∑ m ∈ S_hi.filter (fun m => 2 ^ k < m ∧ m ≤ 2 ^ (k + 1)),
            (1 : ℝ) / (m : ℝ) := Finset.sum_biUnion hpair
  have hblock : ∀ k ∈ Finset.Icc K₀ K,
      ∑ m ∈ S_hi.filter (fun m => 2 ^ k < m ∧ m ≤ 2 ^ (k + 1)), (1 : ℝ) / (m : ℝ) ≤
        β * ((1 : ℝ) / (k : ℝ)) := by
    intro k hk
    have hk_ge : K₀ ≤ k := (Finset.mem_Icc.mp hk).1
    have hk1 : 1 ≤ k := le_trans hK₀ hk_ge
    set Bk := S_hi.filter (fun m => 2 ^ k < m ∧ m ≤ 2 ^ (k + 1))
    have hpow_pos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
    have hBk_sub : Bk ⊆ (Finset.Icc 1 (2 ^ (k + 1))).filter (fun m => 2 ^ k < m ∧ P m) := by
      intro m hm
      have h1 := Finset.mem_filter.mp hm
      have h2 := Finset.mem_filter.mp (Finset.mem_filter.mp h1.1).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, h1.2.2⟩, h1.2.1, h2.2⟩
    have hcard : (Bk.card : ℝ) ≤ β * ((2 ^ k : ℕ) : ℝ) / (k : ℝ) :=
      ((by exact_mod_cast Finset.card_le_card hBk_sub) :
        (Bk.card : ℝ) ≤ (((Finset.Icc 1 (2 ^ (k + 1))).filter (fun m => 2 ^ k < m ∧ P m)).card : ℝ)).trans
        (hblk k hk_ge)
    calc ∑ m ∈ Bk, (1 : ℝ) / (m : ℝ)
        ≤ ∑ _m ∈ Bk, (1 : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun m hm => ?_
          exact one_div_le_one_div_of_le hpow_pos (by exact_mod_cast (Finset.mem_filter.mp hm).2.1.le)
      _ = (Bk.card : ℝ) / ((2 ^ k : ℕ) : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ (β * ((2 ^ k : ℕ) : ℝ) / (k : ℝ)) / ((2 ^ k : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hcard hpow_pos.le
      _ = β * ((1 : ℝ) / (k : ℝ)) := by
          have hk0 : (k : ℝ) ≠ 0 := (Nat.cast_pos.mpr hk1).ne'
          field_simp [hpow_pos.ne', hk0]
  have hsum_hi : ∑ k ∈ Finset.Icc K₀ K, β * ((1 : ℝ) / (k : ℝ)) ≤ β * (Real.log (K : ℝ) + 1) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hβ
    calc ∑ k ∈ Finset.Icc K₀ K, (1 : ℝ) / (k : ℝ)
        ≤ ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left hK₀) fun _ _ _ => by positivity
      _ ≤ Real.log (K : ℝ) + 1 := harmonic_sum_le_log_add_one hK1
  have hlogK_le : Real.log (K : ℝ) ≤ Real.log (Real.log (N : ℝ)) + 1 := by
    have h2K : ((2 ^ K : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have hKlog2 : (K : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ K : ℕ) : ℝ)) h2K
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
      exact h
    have hlog2_ge : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hK_le : (K : ℝ) ≤ 2 * Real.log (N : ℝ) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) K]
    have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK1
    have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have h1 := Real.log_le_log hK_pos hK_le
    rw [Real.log_mul (by norm_num) hlogN_pos.ne'] at h1
    have hlog2_le_1 : Real.log 2 ≤ 1 := by
      calc Real.log 2 ≤ Real.log (Real.exp 1) :=
            Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
        _ = 1 := Real.log_exp 1
    linarith
  have hhi_final : ∑ m ∈ S_hi, (1 : ℝ) / (m : ℝ) ≤ β * Real.log (Real.log (N : ℝ)) + 2 * β := by
    have h1 := hhi_sum.trans ((Finset.sum_le_sum hblock).trans hsum_hi)
    nlinarith
  linarith

/-! ## Section 2: Filtered Shifted-Prime Set Satisfying All Hypotheses of Bloom's Prop 2 -/

/-- Injectivity of `m ↦ unshiftPrime plus q m` on `{m : (unshiftPrime plus q m).Prime}` when `q ≥ 1`. -/
lemma unshiftPrime_injOn (plus : Bool) {q : ℕ} (hq : 1 ≤ q) :
    Set.InjOn (unshiftPrime plus q) {m : ℕ | (unshiftPrime plus q m).Prime} := by
  intro m₁ hm₁ m₂ hm₂ heq
  have h1 := shiftVal_unshiftPrime plus hm₁
  have h2 := shiftVal_unshiftPrime plus hm₂
  have hmul : q * m₁ = q * m₂ := by rw [← h1, ← h2, heq]
  exact Nat.eq_of_mul_eq_mul_left (by omega) hmul

/-- **Main Analytic Bundle Theorem** (Bloom Section 1, lines 168–189, unconditional for both signs):
For any sign `plus : Bool` (`p - 1` or `p + 1`), modulus `q ≥ 1`, and prime lower bound `X`,
there exists `ε₀ ∈ (0, 1/8)` such that for EVERY `0 < ε ≤ ε₀` and EVERY `y ≥ 4`, there exist
`w, z` (`y ≤ w`, `4 * w ≤ z`) and `N₀ ≥ 16` such that for ALL `N ≥ N₀`, the filtered set
`B' ⊆ {m ∈ Icc 2 N | (unshiftPrime plus q m).Prime ∧ X < unshiftPrime plus q m}` satisfies:
1. Smoothness: `∀ m ∈ B', ∀ r, IsPrimePow r → r ∣ m → (r : ℝ) ≤ (m : ℝ) ^ (1 - ε)`
2. Normal order of `ω`: `∀ m ∈ B', |(m.primeFactors.card : ℝ) - log(log m)| ≤ log(log m) / 1000`
3. Small divisor `d₁ ∈ [y, w)` dividing `m`
4. Second divisor `d₂ ∈ [4 * w, z)` dividing `m`
5. Reciprocal sum: `(1 / 4 : ℝ) * log(log N) ≤ ∑ m ∈ B', (1 : ℝ) / m`. -/
theorem shifted_prime_filtered_set_exists (plus : Bool) {q : ℕ} (hq : 1 ≤ q) (X : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 8 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ y : ℕ, 4 ≤ y →
        ∃ w z : ℕ, y ≤ w ∧ 4 * w ≤ z ∧
          ∃ N₀ : ℕ, 16 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
            let B' : Finset ℕ := (Finset.Icc 2 N).filter (fun m =>
              (unshiftPrime plus q m).Prime ∧
              X < unshiftPrime plus q m ∧
              (∀ r : ℕ, IsPrimePow r → r ∣ m → (r : ℝ) ≤ (m : ℝ) ^ (1 - ε)) ∧
              |(m.primeFactors.card : ℝ) - Real.log (Real.log (m : ℝ))| ≤ Real.log (Real.log (m : ℝ)) / 1000 ∧
              (∃ d₁ : ℕ, y ≤ d₁ ∧ d₁ < w ∧ d₁ ∣ m) ∧
              (∃ d₂ : ℕ, 4 * w ≤ d₂ ∧ d₂ < z ∧ d₂ ∣ m))
            (1 / 4 : ℝ) * Real.log (Real.log (N : ℝ)) ≤ ∑ m ∈ B', (1 : ℝ) / (m : ℝ) := by
  obtain ⟨C₁, hC₁_pos, hLem1⟩ := shifted_prime_large_prime_power_bound
  obtain ⟨C₂, hC₂_pos, N₂_om, hN₂_om, hLem2⟩ := shifted_prime_omega_normal_order plus (δ := 1 / 2000) (by norm_num)
  obtain ⟨C₃, hC₃_pos, hLem3⟩ := shifted_prime_no_prime_divisor_in_Icc
  obtain ⟨N_ap, hN_ap4, hAP_lo⟩ := shifted_prime_ap_reciprocal_sum_lower plus hq X
  -- Choose `ε₀ = min (1 / 16) (1 / (512 * C₁ * q))`
  set ε₀ : ℝ := min (1 / 16 : ℝ) (1 / (512 * C₁ * (q : ℝ)))
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hε₀_pos : 0 < ε₀ := lt_min (by norm_num) (by positivity)
  have hε₀_lt : ε₀ < 1 / 8 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨ε₀, hε₀_pos, hε₀_lt, fun ε hε0 hε_le y hy4 => ?_⟩
  have h2ε_pos : 0 < 2 * ε := by linarith
  have h2ε_lt : 2 * ε < 1 / 4 := by linarith
  -- Choose `w` and `z` via Lemma 3 so that the missing-divisor densities are `≤ 1 / 32` each!
  set y' : ℕ := max y (q + 1)
  have hy'4 : 4 ≤ y' := le_trans hy4 (le_max_left _ _)
  -- Pick integer exponent `A ≥ 2` such that `16 * C₃ * q / A ≤ 1 / 32`
  set A : ℕ := max 2 (⌈512 * C₃ * (q : ℝ)⌉₊ + 1)
  have hA2 : 2 ≤ A := le_max_left _ _
  have hA_big : 512 * C₃ * (q : ℝ) < (A : ℝ) := by
    have h1 : 512 * C₃ * (q : ℝ) ≤ (⌈512 * C₃ * (q : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈512 * C₃ * (q : ℝ)⌉₊ : ℝ) + 1 ≤ (A : ℝ) := by exact_mod_cast le_max_right 2 _
    linarith
  set w : ℕ := y' ^ A + 1
  set z : ℕ := (4 * w) ^ A + 1
  have hy_le_w : y ≤ w := by
    have h1 : y' ≤ y' ^ A := Nat.le_self_pow (by omega : A ≠ 0) y'
    have h2 : y ≤ y' := le_max_left _ _
    omega
  have h4w_le_z : 4 * w ≤ z := by
    have h1 : 4 * w ≤ (4 * w) ^ A := Nat.le_self_pow (by omega : A ≠ 0) (4 * w)
    omega
  refine ⟨w, z, hy_le_w, h4w_le_z, ?_⟩
  -- Pull `N₀` thresholds from Lemmas 1, 2, 3
  obtain ⟨N₁_sm, hN₁_sm, hSm⟩ := hLem1 plus (2 * ε) h2ε_pos h2ε_lt
  obtain ⟨N₃_a, hN₃_a, hDivA⟩ := hLem3 plus y' (w - 1) hy'4 (by
    have h1 : y' * y' ≤ y' ^ A := by
      calc y' * y' = y' ^ 2 := (sq y').symm
        _ ≤ y' ^ A := Nat.pow_le_pow_right (by omega) hA2
    have : y' < y' * y' := by nlinarith
    omega)
  obtain ⟨N₃_b, hN₃_b, hDivB⟩ := hLem3 plus (4 * w) (z - 1) (by omega) (by
    have h1 : (4 * w) * (4 * w) ≤ (4 * w) ^ A := by
      calc (4 * w) * (4 * w) = (4 * w) ^ 2 := (sq _).symm
        _ ≤ (4 * w) ^ A := Nat.pow_le_pow_right (by omega) hA2
    have : 4 * w < (4 * w) * (4 * w) := by nlinarith
    omega)
  -- Define the 4 bad predicates on `m : ℕ` (restricted to `p = unshiftPrime plus q m` prime):
  let Bad1 (m : ℕ) : Prop :=
    (unshiftPrime plus q m).Prime ∧
    ∃ r : ℕ, IsPrimePow r ∧ (m : ℝ) ^ (1 - ε) < (r : ℝ) ∧ r ∣ m
  let Bad2 (m : ℕ) : Prop :=
    (unshiftPrime plus q m).Prime ∧
    Real.log (Real.log (m : ℝ)) / 1000 <
      |(m.primeFactors.card : ℝ) - Real.log (Real.log (m : ℝ))|
  let Bad3a (m : ℕ) : Prop :=
    (unshiftPrime plus q m).Prime ∧ ∀ d₁ : ℕ, y ≤ d₁ → d₁ < w → ¬ d₁ ∣ m
  let Bad3b (m : ℕ) : Prop :=
    (unshiftPrime plus q m).Prime ∧ ∀ d₂ : ℕ, 4 * w ≤ d₂ → d₂ < z → ¬ d₂ ∣ m
  -- (A) Dyadic block bound for `Bad1` with `β₁ = 1 / 16`
  have hBad1_sum : ∃ C_b1 : ℝ, ∀ N : ℕ, 4 ≤ N →
      ∑ m ∈ (Finset.Icc 2 N).filter Bad1, (1 : ℝ) / (m : ℝ) ≤
        (1 / 16 : ℝ) * Real.log (Real.log (N : ℝ)) + C_b1 := by
    -- Choose `K₁ ≥ 4` so that for all `k ≥ K₁`:
    -- (i) `2 * q * 2^(k+1) ≥ N₁_sm`,
    -- (ii) `(4 * q : ℝ) ≤ ((2^k : ℕ) : ℝ) ^ ε` (so `(2*q*2^(k+1))^(1-2ε) ≤ (2^k)^(1-ε)`).
    have htend_pow : Tendsto (fun k : ℕ => ((2 ^ k : ℕ) : ℝ) ^ ε) atTop atTop := by
      have h2 : Tendsto (fun k : ℕ => ((2 ^ k : ℕ) : ℝ)) atTop atTop := by
        have h := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
        simpa [Nat.cast_pow] using h
      exact (tendsto_rpow_atTop hε0).comp h2
    obtain ⟨K1a, hK1a⟩ := (tendsto_atTop.mp htend_pow (4 * (q : ℝ) + 1)).exists_forall_of_atTop
    set K₁ : ℕ := max (max K1a (Nat.log 2 N₁_sm + 2)) 4
    refine ⟨((2 ^ K₁ : ℕ) : ℝ) + 2 * (1 / 16 : ℝ), recSum_le_of_dyadic_block_bound Bad1
      (by norm_num : (0 : ℝ) ≤ 1 / 16) (by omega : 1 ≤ K₁) fun k hk => ?_⟩
    set Xk : ℕ := 2 * q * 2 ^ (k + 1)
    have hXk_ge : N₁_sm ≤ Xk := by
      have hk_log : Nat.log 2 N₁_sm + 1 ≤ k + 1 := by omega
      have hlt : N₁_sm < 2 ^ (Nat.log 2 N₁_sm + 1) := Nat.lt_pow_succ_log_self (by norm_num) N₁_sm
      have hpow : 2 ^ (Nat.log 2 N₁_sm + 1) ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) hk_log
      have hmul : 2 ^ (k + 1) ≤ Xk := by
        dsimp only [Xk]
        have : 1 * 2 ^ (k + 1) ≤ (2 * q) * 2 ^ (k + 1) := Nat.mul_le_mul_right _ (by omega)
        simpa using this
      omega
    have hXk_rpow : (Xk : ℝ) ^ (1 - 2 * ε) ≤ ((2 ^ k : ℕ) : ℝ) ^ (1 - ε) := by
      have hXk_eq : (Xk : ℝ) = (4 * (q : ℝ)) * ((2 ^ k : ℕ) : ℝ) := by
        dsimp only [Xk]; rw [pow_succ]; push_cast; ring
      have h4q_le : 4 * (q : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) ^ ε := by
        have := hK1a k (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk)
        linarith
      have h2k_pos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
      have h4q_pow : (4 * (q : ℝ)) ^ (1 - 2 * ε) ≤ 4 * (q : ℝ) := by
        have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
        calc (4 * (q : ℝ)) ^ (1 - 2 * ε) ≤ (4 * (q : ℝ)) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          _ = 4 * (q : ℝ) := Real.rpow_one _
      rw [hXk_eq, Real.mul_rpow (by positivity) h2k_pos.le]
      calc (4 * (q : ℝ)) ^ (1 - 2 * ε) * ((2 ^ k : ℕ) : ℝ) ^ (1 - 2 * ε)
          ≤ ((2 ^ k : ℕ) : ℝ) ^ ε * ((2 ^ k : ℕ) : ℝ) ^ (1 - 2 * ε) :=
            mul_le_mul_of_nonneg_right (h4q_pow.trans h4q_le) (by positivity)
        _ = ((2 ^ k : ℕ) : ℝ) ^ (ε + (1 - 2 * ε)) := (Real.rpow_add h2k_pos _ _).symm
        _ = ((2 ^ k : ℕ) : ℝ) ^ (1 - ε) := by ring_nf
    -- Map `m ↦ unshiftPrime plus q m` injectively into the Lemma 1 set at `Xk`
    set Dom := (Finset.Icc 1 (2 ^ (k + 1))).filter (fun m => 2 ^ k < m ∧ Bad1 m)
    set Cod := (Finset.Icc 1 Xk).filter (fun p =>
        p.Prime ∧ ∃ q₀ : ℕ, IsPrimePow q₀ ∧ (Xk : ℝ) ^ (1 - 2 * ε) < (q₀ : ℝ) ∧ q₀ ∣ shiftVal plus p)
    have hmaps : ∀ m ∈ Dom, unshiftPrime plus q m ∈ Cod := by
      intro m hm
      have hm1 := Finset.mem_filter.mp hm
      have hm_le : m ≤ 2 ^ (k + 1) := (Finset.mem_Icc.mp hm1.1).2
      have hm_gt : 2 ^ k < m := hm1.2.1
      obtain ⟨hpr, r, hr_pp, hr_gt, hr_dvd⟩ := hm1.2.2
      have hp_le : unshiftPrime plus q m ≤ Xk := by
        have hqm : q * m ≤ q * 2 ^ (k + 1) := Nat.mul_le_mul_left q hm_le
        have h1 : 1 ≤ q * 2 ^ (k + 1) := Nat.mul_pos (by omega) (by positivity)
        have hXk_add : Xk = q * 2 ^ (k + 1) + q * 2 ^ (k + 1) := by dsimp only [Xk]; ring
        cases plus <;> simp only [unshiftPrime, Bool.false_eq_true, ↓reduceIte] <;> omega
      have hsh_eq := shiftVal_unshiftPrime plus hpr
      have hr_dvd_sh : r ∣ shiftVal plus (unshiftPrime plus q m) := by
        rw [hsh_eq]; exact dvd_mul_of_dvd_right hr_dvd q
      have hr_gt_Xk : (Xk : ℝ) ^ (1 - 2 * ε) < (r : ℝ) := by
        have hpow_mono : ((2 ^ k : ℕ) : ℝ) ^ (1 - ε) ≤ (m : ℝ) ^ (1 - ε) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hm_gt.le) (by linarith)
        exact lt_of_le_of_lt (hXk_rpow.trans hpow_mono) hr_gt
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpr.pos, hp_le⟩, hpr, r, hr_pp, hr_gt_Xk, hr_dvd_sh⟩
    have hinj : Set.InjOn (unshiftPrime plus q) (Dom : Set ℕ) :=
      (unshiftPrime_injOn plus hq).mono fun m hm => (Finset.mem_filter.mp hm).2.2.1
    have hcard_le : (Dom.card : ℝ) ≤ (Cod.card : ℝ) := by
      exact_mod_cast Finset.card_le_card_of_injOn (unshiftPrime plus q) hmaps hinj
    have hSm_Xk := hSm Xk hXk_ge
    -- Simplify `C₁ * (2 * ε) * Xk / log Xk ≤ (1 / 16) * 2^k / k`
    have hlogXk_ge : (k : ℝ) * (1 / 2 : ℝ) ≤ Real.log (Xk : ℝ) := by
      have hle : ((2 ^ k : ℕ) : ℝ) ≤ (Xk : ℝ) := by
        dsimp only [Xk]; rw [pow_succ]; push_cast
        have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]
      have h1 := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ)) hle
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h1
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hXk_eq : (Xk : ℝ) = 4 * (q : ℝ) * ((2 ^ k : ℕ) : ℝ) := by
      dsimp only [Xk]; rw [pow_succ]; push_cast; ring
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hε_bd : ε ≤ 1 / (512 * C₁ * (q : ℝ)) := hε_le.trans (min_le_right _ _)
    have hcoeff : 16 * C₁ * (q : ℝ) * ε ≤ 1 / 16 := by
      have h1 := mul_le_mul_of_nonneg_left hε_bd (by positivity : 0 ≤ 16 * C₁ * (q : ℝ))
      have hrew : 16 * C₁ * (q : ℝ) * (1 / (512 * C₁ * (q : ℝ))) = 1 / 32 := by
        field_simp [hC₁_pos.ne', hqR_pos.ne']; ring
      linarith
    calc (Dom.card : ℝ) ≤ (Cod.card : ℝ) := hcard_le
      _ ≤ C₁ * (2 * ε) * (Xk : ℝ) / Real.log (Xk : ℝ) := hSm_Xk
      _ ≤ C₁ * (2 * ε) * (Xk : ℝ) / ((k : ℝ) * (1 / 2 : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hlogXk_ge
      _ = (16 * C₁ * (q : ℝ) * ε) * ((2 ^ k : ℕ) : ℝ) / (k : ℝ) := by
          rw [hXk_eq]; field_simp [hk_pos.ne']; ring
      _ ≤ (1 / 16 : ℝ) * ((2 ^ k : ℕ) : ℝ) / (k : ℝ) := by gcongr
  -- (B) Dyadic block bound for `Bad2` with `β₂ = 1 / 16`
  have hBad2_sum : ∃ C_b2 : ℝ, ∀ N : ℕ, 4 ≤ N →
      ∑ m ∈ (Finset.Icc 2 N).filter Bad2, (1 : ℝ) / (m : ℝ) ≤
        (1 / 16 : ℝ) * Real.log (Real.log (N : ℝ)) + C_b2 := by
    -- Pick `K₂` large enough that for all `k ≥ K₂`:
    -- (i) `2 * q * 2^(k+1) ≥ N₂_om`,
    -- (ii) `128 * C₂ * q ≤ Real.log (Real.log (2 * q * 2^(k+1)))`,
    -- (iii) for all `m > 2^k`, `|(m.primeFactors.card : ℝ) - log(log m)| > log(log m) / 1000`
    --       implies `|ω(q*m) - log(log(q*m))| ≥ (1 / 2000) * log(log(q*m))`!
    have htend_ll : Tendsto (fun k : ℕ => Real.log (Real.log ((2 ^ k : ℕ) : ℝ))) atTop atTop := by
      have h2 : Tendsto (fun k : ℕ => ((2 ^ k : ℕ) : ℝ)) atTop atTop := by
        have h := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
        simpa [Nat.cast_pow] using h
      exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h2)
    obtain ⟨K2a, hK2a⟩ := (tendsto_atTop.mp htend_ll
      (2000 * ((q.primeFactors.card : ℝ) + 4) + 128 * C₂ * (q : ℝ) + 10)).exists_forall_of_atTop
    have htend_log : Tendsto (fun k : ℕ => Real.log ((2 ^ k : ℕ) : ℝ)) atTop atTop := by
      have h2 : Tendsto (fun k : ℕ => ((2 ^ k : ℕ) : ℝ)) atTop atTop := by
        have h := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
        simpa [Nat.cast_pow] using h
      exact Real.tendsto_log_atTop.comp h2
    obtain ⟨K2b, hK2b⟩ := (tendsto_atTop.mp htend_log (Real.log (q : ℝ) + 4)).exists_forall_of_atTop
    set K₂ : ℕ := max (max (max K2a K2b) (Nat.log 2 N₂_om + 2)) 4
    refine ⟨((2 ^ K₂ : ℕ) : ℝ) + 2 * (1 / 16 : ℝ), recSum_le_of_dyadic_block_bound Bad2
      (by norm_num : (0 : ℝ) ≤ 1 / 16) (by omega : 1 ≤ K₂) fun k hk => ?_⟩
    set Xk : ℕ := 2 * q * 2 ^ (k + 1)
    have hXk_ge : N₂_om ≤ Xk := by
      have hk_log : Nat.log 2 N₂_om + 1 ≤ k + 1 := by omega
      have hlt : N₂_om < 2 ^ (Nat.log 2 N₂_om + 1) := Nat.lt_pow_succ_log_self (by norm_num) N₂_om
      have hpow : 2 ^ (Nat.log 2 N₂_om + 1) ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) hk_log
      have hmul : 2 ^ (k + 1) ≤ Xk := by
        dsimp only [Xk]
        have : 1 * 2 ^ (k + 1) ≤ (2 * q) * 2 ^ (k + 1) := Nat.mul_le_mul_right _ (by omega)
        simpa using this
      omega
    have hll_k : 2000 * ((q.primeFactors.card : ℝ) + 4) + 128 * C₂ * (q : ℝ) + 10 ≤
        Real.log (Real.log ((2 ^ k : ℕ) : ℝ)) :=
      hK2a k (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hk)
    have hlog_k : Real.log (q : ℝ) + 4 ≤ Real.log ((2 ^ k : ℕ) : ℝ) :=
      hK2b k (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hk)
    set Dom := (Finset.Icc 1 (2 ^ (k + 1))).filter (fun m => 2 ^ k < m ∧ Bad2 m)
    set Cod := (Finset.Icc 1 Xk).filter (fun p =>
        p.Prime ∧ (1 / 2000 : ℝ) * Real.log (Real.log (shiftVal plus p : ℝ)) ≤
          |((shiftVal plus p).primeFactors.card : ℝ) - Real.log (Real.log (shiftVal plus p : ℝ))|)
    have hmaps : ∀ m ∈ Dom, unshiftPrime plus q m ∈ Cod := by
      intro m hm
      have hm1 := Finset.mem_filter.mp hm
      have hm_le : m ≤ 2 ^ (k + 1) := (Finset.mem_Icc.mp hm1.1).2
      have hm_gt : 2 ^ k < m := hm1.2.1
      obtain ⟨hpr, hbad_om⟩ := hm1.2.2
      have hp_le : unshiftPrime plus q m ≤ Xk := by
        have hqm : q * m ≤ q * 2 ^ (k + 1) := Nat.mul_le_mul_left q hm_le
        have h1 : 1 ≤ q * 2 ^ (k + 1) := Nat.mul_pos (by omega) (by positivity)
        have hXk_add : Xk = q * 2 ^ (k + 1) + q * 2 ^ (k + 1) := by dsimp only [Xk]; ring
        cases plus <;> simp only [unshiftPrime, Bool.false_eq_true, ↓reduceIte] <;> omega
      have hsh_eq : shiftVal plus (unshiftPrime plus q m) = q * m := shiftVal_unshiftPrime plus hpr
      -- Compare `ω(q * m)` and `ω(m)`: `ω(m) ≤ ω(q * m) ≤ ω(m) + ω(q)`
      have hm_pos : 0 < m := by omega
      have hpf_sub : m.primeFactors ⊆ (q * m).primeFactors := by
        intro r hr
        have hr' := Nat.mem_primeFactors.mp hr
        exact Nat.mem_primeFactors.mpr ⟨hr'.1, dvd_mul_of_dvd_right hr'.2.1 q, (Nat.mul_pos (by omega) hm_pos).ne'⟩
      have hpf_union : (q * m).primeFactors = q.primeFactors ∪ m.primeFactors :=
        Nat.primeFactors_mul (by omega) hm_pos.ne'
      have hω_diff : |((q * m).primeFactors.card : ℝ) - (m.primeFactors.card : ℝ)| ≤ (q.primeFactors.card : ℝ) := by
        have hlo : m.primeFactors.card ≤ (q * m).primeFactors.card := Finset.card_le_card hpf_sub
        have hhi : (q * m).primeFactors.card ≤ q.primeFactors.card + m.primeFactors.card := by
          rw [hpf_union]; exact Finset.card_union_le _ _
        have hloR : (m.primeFactors.card : ℝ) ≤ ((q * m).primeFactors.card : ℝ) := by exact_mod_cast hlo
        have hhiR : ((q * m).primeFactors.card : ℝ) ≤ (q.primeFactors.card : ℝ) + (m.primeFactors.card : ℝ) := by
          exact_mod_cast hhi
        rw [abs_of_nonneg (by linarith)]
        linarith
      -- Compare `log(log(q * m))` and `log(log m)`: since `log q ≤ log m`, `log(q * m) ≤ 2 * log m`,
      -- so `0 ≤ log(log(q * m)) - log(log m) ≤ log 2 ≤ 1`!
      have hlogm_ge : Real.log (q : ℝ) + 4 ≤ Real.log (m : ℝ) :=
        hlog_k.trans (Real.log_le_log (by positivity) (by exact_mod_cast hm_gt.le))
      have hlogm_pos : 0 < Real.log (m : ℝ) := by
        have : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
        linarith
      have hllm_ge : Real.log (Real.log ((2 ^ k : ℕ) : ℝ)) ≤ Real.log (Real.log (m : ℝ)) :=
        Real.log_le_log (by have : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq); linarith)
          (Real.log_le_log (by positivity) (by exact_mod_cast hm_gt.le))
      have hll_diff : |Real.log (Real.log ((q * m : ℕ) : ℝ)) - Real.log (Real.log (m : ℝ))| ≤ 1 := by
        have hlog_qm : Real.log ((q * m : ℕ) : ℝ) = Real.log (q : ℝ) + Real.log (m : ℝ) := by
          rw [Nat.cast_mul, Real.log_mul hqR_pos.ne' (by positivity)]
        have hlo : Real.log (m : ℝ) ≤ Real.log ((q * m : ℕ) : ℝ) := by
          rw [hlog_qm]; linarith [Real.log_nonneg (by exact_mod_cast hq : (1 : ℝ) ≤ (q : ℝ))]
        have hhi : Real.log ((q * m : ℕ) : ℝ) ≤ 2 * Real.log (m : ℝ) := by
          rw [hlog_qm]; linarith
        have h1 : Real.log (Real.log (m : ℝ)) ≤ Real.log (Real.log ((q * m : ℕ) : ℝ)) :=
          Real.log_le_log hlogm_pos hlo
        have h2 : Real.log (Real.log ((q * m : ℕ) : ℝ)) ≤ Real.log (Real.log (m : ℝ)) + 1 := by
          have ha := Real.log_le_log (by linarith) hhi
          rw [Real.log_mul (by norm_num) hlogm_pos.ne'] at ha
          have hlog2 : Real.log 2 ≤ 1 := by
            calc Real.log 2 ≤ Real.log (Real.exp 1) :=
                  Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
              _ = 1 := Real.log_exp 1
          linarith
        rw [abs_of_nonneg (by linarith)]
        linarith
      -- Triangle inequality for `|ω(q * m) - log(log(q * m))|`
      have htri : |(m.primeFactors.card : ℝ) - Real.log (Real.log (m : ℝ))| ≤
          |((q * m).primeFactors.card : ℝ) - (m.primeFactors.card : ℝ)| +
          |((q * m).primeFactors.card : ℝ) - Real.log (Real.log ((q * m : ℕ) : ℝ))| +
          |Real.log (Real.log ((q * m : ℕ) : ℝ)) - Real.log (Real.log (m : ℝ))| := by
        have h1 := abs_add_le
          ((m.primeFactors.card : ℝ) - ((q * m).primeFactors.card : ℝ))
          (((q * m).primeFactors.card : ℝ) - Real.log (Real.log (m : ℝ)))
        have h2 := abs_add_le
          (((q * m).primeFactors.card : ℝ) - Real.log (Real.log ((q * m : ℕ) : ℝ)))
          (Real.log (Real.log ((q * m : ℕ) : ℝ)) - Real.log (Real.log (m : ℝ)))
        have hs1 : ((m.primeFactors.card : ℝ) - ((q * m).primeFactors.card : ℝ)) +
            (((q * m).primeFactors.card : ℝ) - Real.log (Real.log (m : ℝ))) =
            (m.primeFactors.card : ℝ) - Real.log (Real.log (m : ℝ)) := by ring
        have hs2 : (((q * m).primeFactors.card : ℝ) - Real.log (Real.log ((q * m : ℕ) : ℝ))) +
            (Real.log (Real.log ((q * m : ℕ) : ℝ)) - Real.log (Real.log (m : ℝ))) =
            ((q * m).primeFactors.card : ℝ) - Real.log (Real.log (m : ℝ)) := by ring
        rw [hs1] at h1; rw [hs2] at h2
        have hcomm : |(m.primeFactors.card : ℝ) - ((q * m).primeFactors.card : ℝ)| =
            |((q * m).primeFactors.card : ℝ) - (m.primeFactors.card : ℝ)| := abs_sub_comm _ _
        linarith
      have hll_qm_le : Real.log (Real.log ((q * m : ℕ) : ℝ)) ≤ Real.log (Real.log (m : ℝ)) + 1 := by
        linarith [(abs_le.mp hll_diff).2]
      have hgoal_om : (1 / 2000 : ℝ) * Real.log (Real.log ((q * m : ℕ) : ℝ)) ≤
          |((q * m).primeFactors.card : ℝ) - Real.log (Real.log ((q * m : ℕ) : ℝ))| := by
        have hbig : (q.primeFactors.card : ℝ) + 4 ≤ Real.log (Real.log (m : ℝ)) / 2000 := by
          have : 0 ≤ 128 * C₂ * (q : ℝ) := by positivity
          linarith
        linarith
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpr.pos, hp_le⟩, hpr, ?_⟩
      rwa [hsh_eq]
    have hinj : Set.InjOn (unshiftPrime plus q) (Dom : Set ℕ) :=
      (unshiftPrime_injOn plus hq).mono fun m hm => (Finset.mem_filter.mp hm).2.2.1
    have hcard_le : (Dom.card : ℝ) ≤ (Cod.card : ℝ) := by
      exact_mod_cast Finset.card_le_card_of_injOn (unshiftPrime plus q) hmaps hinj
    have hOm_Xk := hLem2 Xk hXk_ge
    have h2k_le_Xk : ((2 ^ k : ℕ) : ℝ) ≤ (Xk : ℝ) := by
      dsimp only [Xk]; rw [pow_succ]; push_cast
      have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]
    have hlogXk_ge : (k : ℝ) * (1 / 2 : ℝ) ≤ Real.log (Xk : ℝ) := by
      have h1 := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ)) h2k_le_Xk
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h1
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hllXk_ge : 128 * C₂ * (q : ℝ) ≤ Real.log (Real.log (Xk : ℝ)) := by
      have h1 : Real.log (Real.log ((2 ^ k : ℕ) : ℝ)) ≤ Real.log (Real.log (Xk : ℝ)) :=
        Real.log_le_log (by have : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq); linarith)
          (Real.log_le_log (by positivity) h2k_le_Xk)
      have hnn : 0 ≤ 2000 * ((q.primeFactors.card : ℝ) + 4) := by positivity
      linarith
    have hXk_eq : (Xk : ℝ) = 4 * (q : ℝ) * ((2 ^ k : ℕ) : ℝ) := by
      dsimp only [Xk]; rw [pow_succ]; push_cast; ring
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hden_ge : ((k : ℝ) * (1 / 2 : ℝ)) * (128 * C₂ * (q : ℝ)) ≤
        Real.log (Xk : ℝ) * Real.log (Real.log (Xk : ℝ)) :=
      mul_le_mul hlogXk_ge hllXk_ge (by positivity) (by linarith)
    calc (Dom.card : ℝ) ≤ (Cod.card : ℝ) := hcard_le
      _ ≤ C₂ * (Xk : ℝ) / (Real.log (Xk : ℝ) * Real.log (Real.log (Xk : ℝ))) := hOm_Xk
      _ ≤ C₂ * (Xk : ℝ) / (((k : ℝ) * (1 / 2 : ℝ)) * (128 * C₂ * (q : ℝ))) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
      _ = (1 / 16 : ℝ) * ((2 ^ k : ℕ) : ℝ) / (k : ℝ) := by
          rw [hXk_eq]; field_simp [hC₂_pos.ne', hqR_pos.ne', hk_pos.ne']; ring
  -- (C) Helper for both divisor bad sets `Bad3a` and `Bad3b` with `β₃ = 1 / 32` each
  have hDiv_block : ∀ (u v : ℕ), q < u → 4 ≤ u → u < v →
      (Real.log (u : ℝ) / Real.log (v : ℝ)) ≤ 1 / (512 * C₃ * (q : ℝ)) →
      (∃ N_u : ℕ, 4 ≤ N_u ∧ ∀ N : ℕ, N_u ≤ N →
        (((Finset.Icc 1 N).filter (fun p =>
            p.Prime ∧ ∀ r ∈ Finset.Icc u v, r.Prime → ¬ r ∣ shiftVal plus p)).card : ℝ) ≤
          C₃ * (Real.log (u : ℝ) / Real.log (v : ℝ)) * ((N : ℝ) / Real.log (N : ℝ))) →
      ∃ C_u : ℝ, ∀ N : ℕ, 4 ≤ N →
        ∑ m ∈ (Finset.Icc 2 N).filter (fun m =>
            (unshiftPrime plus q m).Prime ∧ ∀ d : ℕ, u ≤ d → d ≤ v → ¬ d ∣ m),
          (1 : ℝ) / (m : ℝ) ≤ (1 / 32 : ℝ) * Real.log (Real.log (N : ℝ)) + C_u := by
    intro u v hqu hu4 huv hratio ⟨N_u, _, hLem_u⟩
    let Bu (m : ℕ) : Prop := (unshiftPrime plus q m).Prime ∧ ∀ d : ℕ, u ≤ d → d ≤ v → ¬ d ∣ m
    set Ku : ℕ := max (Nat.log 2 N_u + 2) 4
    refine ⟨((2 ^ Ku : ℕ) : ℝ) + 2 * (1 / 32 : ℝ), recSum_le_of_dyadic_block_bound Bu
      (by norm_num : (0 : ℝ) ≤ 1 / 32) (by omega : 1 ≤ Ku) fun k hk => ?_⟩
    set Xk : ℕ := 2 * q * 2 ^ (k + 1)
    have hXk_ge : N_u ≤ Xk := by
      have hk_log : Nat.log 2 N_u + 1 ≤ k + 1 := by omega
      have hlt : N_u < 2 ^ (Nat.log 2 N_u + 1) := Nat.lt_pow_succ_log_self (by norm_num) N_u
      have hpow : 2 ^ (Nat.log 2 N_u + 1) ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) hk_log
      have hmul : 2 ^ (k + 1) ≤ Xk := by
        dsimp only [Xk]
        have : 1 * 2 ^ (k + 1) ≤ (2 * q) * 2 ^ (k + 1) := Nat.mul_le_mul_right _ (by omega)
        simpa using this
      omega
    set Dom := (Finset.Icc 1 (2 ^ (k + 1))).filter (fun m => 2 ^ k < m ∧ Bu m)
    set Cod := (Finset.Icc 1 Xk).filter (fun p =>
        p.Prime ∧ ∀ r ∈ Finset.Icc u v, r.Prime → ¬ r ∣ shiftVal plus p)
    have hmaps : ∀ m ∈ Dom, unshiftPrime plus q m ∈ Cod := by
      intro m hm
      have hm1 := Finset.mem_filter.mp hm
      have hm_le : m ≤ 2 ^ (k + 1) := (Finset.mem_Icc.mp hm1.1).2
      obtain ⟨hpr, hno⟩ := hm1.2.2
      have hp_le : unshiftPrime plus q m ≤ Xk := by
        have hqm : q * m ≤ q * 2 ^ (k + 1) := Nat.mul_le_mul_left q hm_le
        have h1 : 1 ≤ q * 2 ^ (k + 1) := Nat.mul_pos (by omega) (by positivity)
        have hXk_add : Xk = q * 2 ^ (k + 1) + q * 2 ^ (k + 1) := by dsimp only [Xk]; ring
        cases plus <;> simp only [unshiftPrime, Bool.false_eq_true, ↓reduceIte] <;> omega
      have hsh_eq := shiftVal_unshiftPrime plus hpr
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpr.pos, hp_le⟩, hpr, fun r hr hr_pr hdvd => ?_⟩
      have hr_icc := Finset.mem_Icc.mp hr
      rw [hsh_eq] at hdvd
      have hnot_q : ¬ r ∣ q := fun h => by
        have := Nat.le_of_dvd (by omega) h; omega
      have hrm : r ∣ m := (hr_pr.dvd_mul.mp hdvd).resolve_left hnot_q
      exact hno r hr_icc.1 hr_icc.2 hrm
    have hinj : Set.InjOn (unshiftPrime plus q) (Dom : Set ℕ) :=
      (unshiftPrime_injOn plus hq).mono fun m hm => (Finset.mem_filter.mp hm).2.2.1
    have hcard_le : (Dom.card : ℝ) ≤ (Cod.card : ℝ) := by
      exact_mod_cast Finset.card_le_card_of_injOn (unshiftPrime plus q) hmaps hinj
    have hlogXk_ge : (k : ℝ) * (1 / 2 : ℝ) ≤ Real.log (Xk : ℝ) := by
      have hle : ((2 ^ k : ℕ) : ℝ) ≤ (Xk : ℝ) := by
        dsimp only [Xk]; rw [pow_succ]; push_cast
        have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]
      have h1 := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ)) hle
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h1
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hXk_eq : (Xk : ℝ) = 4 * (q : ℝ) * ((2 ^ k : ℕ) : ℝ) := by
      dsimp only [Xk]; rw [pow_succ]; push_cast; ring
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hC3_ratio : 8 * C₃ * (q : ℝ) * (Real.log (u : ℝ) / Real.log (v : ℝ)) ≤ 1 / 32 := by
      have h1 := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 8 * C₃ * (q : ℝ))
      have hrew : 8 * C₃ * (q : ℝ) * (1 / (512 * C₃ * (q : ℝ))) = 1 / 64 := by
        field_simp [hC₃_pos.ne', hqR_pos.ne']; ring
      linarith
    calc (Dom.card : ℝ) ≤ (Cod.card : ℝ) := hcard_le
      _ ≤ C₃ * (Real.log (u : ℝ) / Real.log (v : ℝ)) * ((Xk : ℝ) / Real.log (Xk : ℝ)) := hLem_u Xk hXk_ge
      _ ≤ C₃ * (Real.log (u : ℝ) / Real.log (v : ℝ)) * ((Xk : ℝ) / ((k : ℝ) * (1 / 2 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact div_le_div_of_nonneg_left (by positivity) (by positivity) hlogXk_ge
          · have : 0 < Real.log (u : ℝ) / Real.log (v : ℝ) :=
              div_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < u)))
                (Real.log_pos (by exact_mod_cast (by omega : 1 < v)))
            positivity
      _ = (8 * C₃ * (q : ℝ) * (Real.log (u : ℝ) / Real.log (v : ℝ))) * ((2 ^ k : ℕ) : ℝ) / (k : ℝ) := by
          rw [hXk_eq]; field_simp [hk_pos.ne']; ring
      _ ≤ (1 / 32 : ℝ) * ((2 ^ k : ℕ) : ℝ) / (k : ℝ) := by gcongr
  -- Instantiate `hDiv_block` for `(y', w - 1)` and `(4 * w, z - 1)`
  have hratio_a : Real.log (y' : ℝ) / Real.log ((w - 1 : ℕ) : ℝ) ≤ 1 / (512 * C₃ * (q : ℝ)) := by
    have hw1 : w - 1 = y' ^ A := by dsimp only [w]; omega
    rw [hw1, Nat.cast_pow, Real.log_pow]
    have hlogy' : 0 < Real.log (y' : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y'))
    have hrew : Real.log (y' : ℝ) / ((A : ℝ) * Real.log (y' : ℝ)) = 1 / (A : ℝ) := by
      field_simp [hlogy'.ne']
    rw [hrew]
    exact one_div_le_one_div_of_le (by positivity) hA_big.le
  have hratio_b : Real.log ((4 * w : ℕ) : ℝ) / Real.log ((z - 1 : ℕ) : ℝ) ≤ 1 / (512 * C₃ * (q : ℝ)) := by
    have hz1 : z - 1 = (4 * w) ^ A := by dsimp only [z]; omega
    rw [hz1, Nat.cast_pow, Real.log_pow]
    have hlog4w : 0 < Real.log ((4 * w : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < 4 * w))
    have hrew : Real.log ((4 * w : ℕ) : ℝ) / ((A : ℝ) * Real.log ((4 * w : ℕ) : ℝ)) = 1 / (A : ℝ) := by
      field_simp [hlog4w.ne']
    rw [hrew]
    exact one_div_le_one_div_of_le (by positivity) hA_big.le
  obtain ⟨C_b1, hB1⟩ := hBad1_sum
  obtain ⟨C_b2, hB2⟩ := hBad2_sum
  obtain ⟨C_3a, hB3a⟩ := hDiv_block y' (w - 1) (lt_of_lt_of_le (Nat.lt_succ_self q) (le_max_right _ _))
    hy'4 (by
      have h1 : y' * y' ≤ y' ^ A := by
        calc y' * y' = y' ^ 2 := (sq y').symm
          _ ≤ y' ^ A := Nat.pow_le_pow_right (by omega) hA2
      have : y' < y' * y' := by nlinarith
      omega) hratio_a ⟨N₃_a, hN₃_a, hDivA⟩
  obtain ⟨C_3b, hB3b⟩ := hDiv_block (4 * w) (z - 1) (by
      have : q + 1 ≤ y' := le_max_right _ _
      have : y' ≤ w := by
        have h1 : y' ≤ y' ^ A := Nat.le_self_pow (by omega : A ≠ 0) y'
        omega
      omega) (by omega) (by
      have h1 : (4 * w) * (4 * w) ≤ (4 * w) ^ A := by
        calc (4 * w) * (4 * w) = (4 * w) ^ 2 := (sq _).symm
          _ ≤ (4 * w) ^ A := Nat.pow_le_pow_right (by omega) hA2
      have : 4 * w < (4 * w) * (4 * w) := by nlinarith
      omega) hratio_b ⟨N₃_b, hN₃_b, hDivB⟩
  -- Pick `N₀` large enough that `(1 / 16) * log(log N) ≥ C_b1 + C_b2 + C_3a + C_3b + 2`
  have htend_ll : Tendsto (fun N : ℕ => (1 / 16 : ℝ) * Real.log (Real.log (N : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop
      (by norm_num)
  obtain ⟨N_big, hN_big⟩ := (tendsto_atTop.mp htend_ll (C_b1 + C_b2 + C_3a + C_3b + 2)).exists_forall_of_atTop
  refine ⟨max (max N_ap N_big) 16, le_max_right _ _, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := le_trans (le_max_right _ _) hN
  have hNap : N_ap ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNbig : N_big ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  set B_all := (Finset.Icc 1 N).filter (fun m => (unshiftPrime plus q m).Prime ∧ X < unshiftPrime plus q m)
  set B' : Finset ℕ := (Finset.Icc 2 N).filter (fun m =>
    (unshiftPrime plus q m).Prime ∧
    X < unshiftPrime plus q m ∧
    (∀ r : ℕ, IsPrimePow r → r ∣ m → (r : ℝ) ≤ (m : ℝ) ^ (1 - ε)) ∧
    |(m.primeFactors.card : ℝ) - Real.log (Real.log (m : ℝ))| ≤ Real.log (Real.log (m : ℝ)) / 1000 ∧
    (∃ d₁ : ℕ, y ≤ d₁ ∧ d₁ < w ∧ d₁ ∣ m) ∧
    (∃ d₂ : ℕ, 4 * w ≤ d₂ ∧ d₂ < z ∧ d₂ ∣ m))
  set S1 := (Finset.Icc 2 N).filter Bad1
  set S2 := (Finset.Icc 2 N).filter Bad2
  set S3a := (Finset.Icc 2 N).filter (fun m => (unshiftPrime plus q m).Prime ∧ ∀ d : ℕ, y' ≤ d → d ≤ w - 1 → ¬ d ∣ m)
  set S3b := (Finset.Icc 2 N).filter (fun m => (unshiftPrime plus q m).Prime ∧ ∀ d : ℕ, 4 * w ≤ d → d ≤ z - 1 → ¬ d ∣ m)
  -- `B_all ⊆ B' ∪ {1} ∪ S1 ∪ S2 ∪ S3a ∪ S3b`
  have hcov : B_all ⊆ B' ∪ ({1} : Finset ℕ) ∪ S1 ∪ S2 ∪ S3a ∪ S3b := by
    intro m hm
    have hm1 := Finset.mem_filter.mp hm
    have hm_icc := Finset.mem_Icc.mp hm1.1
    obtain ⟨hpr, hgtX⟩ := hm1.2
    by_cases hm1eq : m = 1
    · subst hm1eq
      simp
    · have hm2 : m ∈ Finset.Icc 2 N := Finset.mem_Icc.mpr ⟨by omega, hm_icc.2⟩
      by_cases h1 : ∀ r : ℕ, IsPrimePow r → r ∣ m → (r : ℝ) ≤ (m : ℝ) ^ (1 - ε)
      · by_cases h2 : |(m.primeFactors.card : ℝ) - Real.log (Real.log (m : ℝ))| ≤
            Real.log (Real.log (m : ℝ)) / 1000
        · by_cases h3a : ∃ d₁ : ℕ, y' ≤ d₁ ∧ d₁ ≤ w - 1 ∧ d₁ ∣ m
          · by_cases h3b : ∃ d₂ : ℕ, 4 * w ≤ d₂ ∧ d₂ ≤ z - 1 ∧ d₂ ∣ m
            · -- `m ∈ B'`!
              obtain ⟨d₁, hd1a, hd1b, hd1d⟩ := h3a
              obtain ⟨d₂, hd2a, hd2b, hd2d⟩ := h3b
              have hy_le_y' : y ≤ y' := le_max_left _ _
              have hw_pos : 1 ≤ w := by omega
              have hz_pos : 1 ≤ z := by omega
              have hmB' : m ∈ B' := Finset.mem_filter.mpr ⟨hm2, hpr, hgtX, h1, h2,
                ⟨d₁, le_trans hy_le_y' hd1a, by omega, hd1d⟩,
                ⟨d₂, hd2a, by omega, hd2d⟩⟩
              exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hmB'))))
            · push Not at h3b
              exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm2, hpr, h3b⟩)
          · push Not at h3a
            exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨hm2, hpr, h3a⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hm2, hpr, lt_of_not_ge h2⟩)))
      · push Not at h1
        obtain ⟨r, hr_pp, hr_dvd, hr_gt⟩ := h1
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm2, hpr, r, hr_pp, hr_gt, hr_dvd⟩))))
  have hsum_union_le : ∀ A B : Finset ℕ,
      ∑ m ∈ A ∪ B, (1 : ℝ) / (m : ℝ) ≤ (∑ m ∈ A, (1 : ℝ) / (m : ℝ)) + ∑ m ∈ B, (1 : ℝ) / (m : ℝ) := by
    intro A B
    have hui := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := fun m : ℕ => (1 : ℝ) / (m : ℝ))
    have hnn : 0 ≤ ∑ m ∈ A ∩ B, (1 : ℝ) / (m : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
    linarith
  have htot_le : ∑ m ∈ B_all, (1 : ℝ) / (m : ℝ) ≤
      (∑ m ∈ B', (1 : ℝ) / (m : ℝ)) + 1 +
      (∑ m ∈ S1, (1 : ℝ) / (m : ℝ)) + (∑ m ∈ S2, (1 : ℝ) / (m : ℝ)) +
      (∑ m ∈ S3a, (1 : ℝ) / (m : ℝ)) + (∑ m ∈ S3b, (1 : ℝ) / (m : ℝ)) := by
    have h0 : ∑ m ∈ B_all, (1 : ℝ) / (m : ℝ) ≤
        ∑ m ∈ B' ∪ {1} ∪ S1 ∪ S2 ∪ S3a ∪ S3b, (1 : ℝ) / (m : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => by positivity
    have h1 := hsum_union_le (B' ∪ {1} ∪ S1 ∪ S2 ∪ S3a) S3b
    have h2 := hsum_union_le (B' ∪ {1} ∪ S1 ∪ S2) S3a
    have h3 := hsum_union_le (B' ∪ {1} ∪ S1) S2
    have h4 := hsum_union_le (B' ∪ {1}) S1
    have h5 := hsum_union_le B' {1}
    have h1val : ∑ m ∈ ({1} : Finset ℕ), (1 : ℝ) / (m : ℝ) = 1 := by simp
    linarith
  have hlo := hAP_lo N hNap
  have hs1 := hB1 N (by omega)
  have hs2 := hB2 N (by omega)
  have hs3a := hB3a N (by omega)
  have hs3b := hB3b N (by omega)
  have hbig := hN_big N hNbig
  linarith

/-! ## Section 3: Bloom's Proposition 2 (`prop-tech`) & Reduction of Zhi-Wei Sun's Conjecture -/

/-- Exact statement of Bloom's **Proposition 1 (`th-techmain`, arXiv:2305.02689)** —
the Fourier/combinatorial engine proved by the sibling `PPL024_Comb*` campaign. -/
def BloomProp1Statement : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 / 4 →
    ∃ N₀ : ℕ, 16 ≤ N₀ ∧ ∀ (N : ℕ), N₀ ≤ N →
      ∀ (y z : ℕ), 1 ≤ y → y ≤ z → (z : ℝ) ≤ (Real.log (N : ℝ)) ^ (1 / 500 : ℝ) →
        ∀ A : Finset ℕ,
          (∀ n ∈ A, (N : ℝ) ^ (1 - c) ≤ (n : ℝ) ∧ n ≤ N) →
          (2 : ℝ) / (y : ℝ) + (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) ≤ ∑ n ∈ A, (1 : ℝ) / (n : ℝ) →
          (∀ n ∈ A, ∃ d₁ d₂ : ℕ, y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ d₂ ≤ z ∧ d₁ ∣ n ∧ d₂ ∣ n) →
          (∀ n ∈ A, ∀ q : ℕ, IsPrimePow q → q ∣ n → (q : ℝ) ≤ (N : ℝ) ^ (1 - 4 * c)) →
          (∀ n ∈ A, (99 / 100 : ℝ) * Real.log (Real.log (N : ℝ)) ≤ (n.primeFactors.card : ℝ) ∧
            (n.primeFactors.card : ℝ) ≤ 2 * Real.log (Real.log (N : ℝ))) →
          ∃ S ⊆ A, ∃ d : ℕ, y ≤ d ∧ d ≤ z ∧ ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = (1 : ℚ) / (d : ℚ)

/-- **Bloom's Proposition 2 (`prop-tech`, arXiv:2305.02689)** deduced unconditionally from
`BloomProp1Statement` via dyadic-logarithmic pigeonhole `N_i = N ^ ((1 - ε/4)^i)`. -/
theorem prop_tech_of_bloom_prop1 (hProp1 : BloomProp1Statement)
    {δ ε : ℝ} (hδ : 0 < δ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ y₀ : ℕ, 4 ≤ y₀ ∧ ∀ y w z : ℕ, y₀ ≤ y → y ≤ w → 4 * w ≤ z →
      ∃ N₀ : ℕ, 16 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
        ∀ A : Finset ℕ,
          (∀ n ∈ A, 2 ≤ n ∧ n ≤ N) →
          (∀ n ∈ A, ∀ q : ℕ, IsPrimePow q → q ∣ n → (q : ℝ) ≤ (n : ℝ) ^ (1 - ε)) →
          (∀ n ∈ A, |(n.primeFactors.card : ℝ) - Real.log (Real.log (n : ℝ))| ≤
            Real.log (Real.log (n : ℝ)) / 1000) →
          (∀ n ∈ A, ∃ d₁ : ℕ, y ≤ d₁ ∧ d₁ < w ∧ d₁ ∣ n) →
          (∀ n ∈ A, ∃ d₂ : ℕ, 4 * w ≤ d₂ ∧ d₂ < z ∧ d₂ ∣ n) →
          δ * Real.log (Real.log (N : ℝ)) ≤ ∑ n ∈ A, (1 : ℝ) / (n : ℝ) →
          ∃ S ⊆ A, ∃ d : ℕ, y ≤ d ∧ d ≤ z ∧ ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = (1 : ℚ) / (d : ℚ) := by
  set c : ℝ := ε / 4
  have hc0 : 0 < c := by positivity
  have hc4 : c < 1 / 4 := by dsimp only [c]; linarith
  obtain ⟨N_p1, hN_p1, hP1⟩ := hProp1 c hc0 hc4
  -- Let `r = 1 - c = 1 - ε / 4 ∈ (3/4, 1)`.
  set r : ℝ := 1 - c
  have hr_pos : 0 < r := by dsimp only [r, c]; linarith
  have hr_lt1 : r < 1 := by dsimp only [r]; linarith
  have hlogr_neg : Real.log r < 0 := Real.log_neg hr_pos hr_lt1
  set κ : ℝ := -Real.log r
  have hκ_pos : 0 < κ := by dsimp only [κ]; linarith
  -- Choose `y₀` so that `2 / y₀ ≤ δ * κ / 8`
  set y₀ : ℕ := max 4 (⌈16 / (δ * κ)⌉₊ + 1)
  refine ⟨y₀, le_max_left _ _, fun y w z hy₀ hyw h4wz => ?_⟩
  have h2y_le : (2 : ℝ) / (y : ℝ) ≤ δ * κ / 8 := by
    have h1 : 16 / (δ * κ) < (y : ℝ) := by
      have ha : 16 / (δ * κ) ≤ (⌈16 / (δ * κ)⌉₊ : ℝ) := Nat.le_ceil _
      have hb : (⌈16 / (δ * κ)⌉₊ : ℝ) + 1 ≤ (y₀ : ℝ) := by exact_mod_cast le_max_right 4 _
      have hc : (y₀ : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy₀
      linarith
    rw [div_le_iff₀ (by exact_mod_cast (by omega : 0 < y))]
    have hmul := mul_lt_mul_of_pos_left h1 (by positivity : 0 < δ * κ / 8)
    have hrew : δ * κ / 8 * (16 / (δ * κ)) = 2 := by field_simp [hδ.ne', hκ_pos.ne']; ring
    linarith
  -- Choose a cutoff `M_cut : ℕ` large enough so that every `N' ≥ M_cut` satisfies:
  -- (a) `N' ≥ N_p1` and `N' ≥ 16`,
  -- (b) `(z : ℝ) ≤ (log N')^(1/500)`,
  -- (c) `(log N')^(-1/200) ≤ δ * κ / 8`,
  -- (d) `|log(r)| ≤ log(log N') / 500` (so `n ∈ [N'^r, N'] ⟹ (99/100) log log N' ≤ ω(n) ≤ 2 log log N'`).
  have htend_z : Tendsto (fun M : ℕ => (Real.log (M : ℝ)) ^ (1 / 500 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 500)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨M1, hM1⟩ := (tendsto_atTop.mp htend_z ((z : ℝ) + 1)).exists_forall_of_atTop
  have htend_200 : Tendsto (fun M : ℕ => (Real.log (M : ℝ)) ^ (1 / 200 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨M2, hM2⟩ := (tendsto_atTop.mp htend_200 (8 / (δ * κ) + 1)).exists_forall_of_atTop
  have htend_ll : Tendsto (fun M : ℕ => Real.log (Real.log (M : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨M3, hM3⟩ := (tendsto_atTop.mp htend_ll (500 * κ + 1000)).exists_forall_of_atTop
  set M_cut : ℕ := max (max (max M1 M2) M3) (max N_p1 16)
  have hMcut_ge16 : 16 ≤ M_cut := le_trans (le_max_right _ _) (le_max_right _ _)
  -- Now choose `N₀` large enough that:
  -- (1) `M_cut ≤ N₀`,
  -- (2) `(M_cut : ℝ) + 1 ≤ (δ / 2) * log(log N)` (so elements `≤ M_cut` contribute `≤ (δ/2) log log N`),
  -- (3) `Real.log (Real.log (M_cut : ℝ)) + 2 * κ ≤ (δ / 2) * ...` — specifically, the number of intervals
  --     `K_steps = ⌈(log(log N) - log(log M_cut)) / κ⌉₊ + 1` satisfies `K_steps * (δ * κ / 4) ≤ (δ / 2) * log(log N) - M_cut`!
  obtain ⟨N₀_big, hN₀_big⟩ := (tendsto_atTop.mp htend_ll
    ((4 / δ) * ((M_cut : ℝ) + 4) + 8 * κ + 20)).exists_forall_of_atTop
  set N₀ : ℕ := max (max N₀_big (M_cut ^ 2)) 16
  refine ⟨N₀, le_max_right _ _, fun N hN A hA_range hA_sm hA_om hA_d1 hA_d2 hA_sum => ?_⟩
  have hN16 : 16 ≤ N := le_trans (le_max_right _ _) hN
  have hNbig : N₀_big ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNM2 : M_cut ^ 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hMcut_le_N : M_cut ≤ N := by nlinarith
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogM_pos : 0 < Real.log (M_cut : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M_cut))
  -- Split `A` into `A_lo = {n ∈ A | n ≤ M_cut}` and `A_hi = {n ∈ A | M_cut < n}`
  set A_lo := A.filter (fun n => n ≤ M_cut)
  set A_hi := A.filter (fun n => ¬ n ≤ M_cut)
  have hlo_le : ∑ n ∈ A_lo, (1 : ℝ) / (n : ℝ) ≤ (M_cut : ℝ) := by
    calc ∑ n ∈ A_lo, (1 : ℝ) / (n : ℝ)
        ≤ ∑ _n ∈ A_lo, (1 : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn2 : 2 ≤ n := (hA_range n (Finset.mem_filter.mp hn).1).1
          rw [one_div]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ n))
      _ = (A_lo.card : ℝ) := by simp
      _ ≤ (M_cut : ℝ) := by
          have hsub : A_lo ⊆ Finset.Icc 1 M_cut := by
            intro n hn
            have h1 := Finset.mem_filter.mp hn
            exact Finset.mem_Icc.mpr ⟨by have := (hA_range n h1.1).1; omega, h1.2⟩
          exact_mod_cast (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
  have hhi_ge : (δ / 2 : ℝ) * Real.log (Real.log (N : ℝ)) ≤ ∑ n ∈ A_hi, (1 : ℝ) / (n : ℝ) := by
    have hsplit : ∑ n ∈ A, (1 : ℝ) / (n : ℝ) =
        (∑ n ∈ A_lo, (1 : ℝ) / (n : ℝ)) + ∑ n ∈ A_hi, (1 : ℝ) / (n : ℝ) :=
      (Finset.sum_filter_add_sum_filter_not A (fun n => n ≤ M_cut) _).symm
    have hll_big := hN₀_big N hNbig
    have hM_small : (M_cut : ℝ) ≤ (δ / 2 : ℝ) * Real.log (Real.log (N : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hll_big (by positivity : 0 ≤ δ / 2)
      have hrew : (δ / 2) * ((4 / δ) * ((M_cut : ℝ) + 4) + 8 * κ + 20) =
          2 * ((M_cut : ℝ) + 4) + 4 * δ * κ + 10 * δ := by field_simp [hδ.ne']; ring
      have hnn : 0 ≤ 4 * δ * κ + 10 * δ := by positivity
      linarith
    linarith
  -- Cover `A_hi` by blocks `B i = A_hi.filter (fun n => (N_i : ℝ)^r ≤ n ∧ n ≤ N_i)`
  -- where `N_i = ⌊(N : ℝ) ^ (r ^ i)⌋₊` for `i = 0, ..., K_steps` until `(N : ℝ)^(r^(K+1)) ≤ M_cut`!
  -- Wait: use real thresholds `T i = (N : ℝ) ^ (r ^ i)` and `N_i = ⌊T i⌋₊`!
  -- Note `(N_i : ℝ)^r ≤ (T i)^r = T (i + 1) ≤ N_(i+1) + 1`, so every `n ∈ (T (i+1), T i]`
  -- satisfies `n ≤ N_i` AND `(N_i : ℝ)^r ≤ (T i)^r = T (i+1) < n`!!
  -- CHECK THAT!! `N_i = ⌊T i⌋₊ ≤ T i ⟹ (N_i : ℝ)^r ≤ (T i)^r = T (i+1) < n ≤ ⌊T i⌋₊ = N_i`!!
  -- THAT'S LITERALLY EXACT WITH ZERO FLOOR LOSS!!
  let T (i : ℕ) : ℝ := (N : ℝ) ^ (r ^ i)
  have hT_pos : ∀ i : ℕ, 0 < T i := fun i => Real.rpow_pos_of_pos (by positivity) _
  have hT_succ : ∀ i : ℕ, T (i + 1) = (T i) ^ r := by
    intro i; dsimp only [T]
    rw [← Real.rpow_mul (by positivity), pow_succ]
  -- Pick `K : ℕ` = least `K` such that `T K ≤ M_cut`, i.e. `r^K * log N ≤ log M_cut`,
  -- which holds at `K := ⌊Real.log (Real.log (N : ℝ) / Real.log (M_cut : ℝ)) / κ⌋₊ + 1`!
  set K : ℕ := ⌊Real.log (Real.log (N : ℝ) / Real.log (M_cut : ℝ)) / κ⌋₊ + 1
  have hK_ge1 : 1 ≤ K := by omega
  have hTK_le_M : T K ≤ (M_cut : ℝ) := by
    dsimp only [T]
    have hlog_div : Real.log (Real.log (N : ℝ) / Real.log (M_cut : ℝ)) / κ < (K : ℝ) := by
      dsimp only [K]; push_cast; exact Nat.lt_floor_add_one _
    have hmul : Real.log (Real.log (N : ℝ) / Real.log (M_cut : ℝ)) < (K : ℝ) * κ :=
      (div_lt_iff₀ hκ_pos).mp hlog_div
    have hlog_rK : Real.log (r ^ K) = -(K : ℝ) * κ := by
      rw [Real.log_pow]; dsimp only [κ]; ring
    have hrK_lt : r ^ K < Real.log (M_cut : ℝ) / Real.log (N : ℝ) := by
      rw [← Real.exp_log (pow_pos hr_pos K), ← Real.exp_log (div_pos hlogM_pos hlogN_pos)]
      apply Real.exp_lt_exp.mpr
      rw [hlog_rK, Real.log_div hlogM_pos.ne' hlogN_pos.ne']
      rw [Real.log_div hlogN_pos.ne' hlogM_pos.ne'] at hmul
      linarith
    have hmulN : r ^ K * Real.log (N : ℝ) < Real.log (M_cut : ℝ) :=
      (lt_div_iff₀ hlogN_pos).mp hrK_lt
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (N : ℝ))]
    calc Real.exp (Real.log (N : ℝ) * r ^ K)
        ≤ Real.exp (Real.log (M_cut : ℝ)) := Real.exp_le_exp.mpr (by linarith)
      _ = (M_cut : ℝ) := Real.exp_log (by exact_mod_cast (by omega : 0 < M_cut))
  -- Also `K ≤ (log(log N)) / κ + 1` (since `log M_cut ≥ 1`)
  have hK_le : (K : ℝ) ≤ Real.log (Real.log (N : ℝ)) / κ + 1 := by
    have hlogM_ge1 : 1 ≤ Real.log (M_cut : ℝ) := by
      have h16 : Real.exp 1 ≤ (M_cut : ℝ) := by
        have : (16 : ℝ) ≤ (M_cut : ℝ) := by exact_mod_cast hMcut_ge16
        linarith [Real.exp_one_lt_d9]
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log (M_cut : ℝ) := Real.log_le_log (Real.exp_pos 1) h16
    have hdiv_le : Real.log (N : ℝ) / Real.log (M_cut : ℝ) ≤ Real.log (N : ℝ) :=
      div_le_self hlogN_pos.le hlogM_ge1
    have hlog_le : Real.log (Real.log (N : ℝ) / Real.log (M_cut : ℝ)) ≤ Real.log (Real.log (N : ℝ)) :=
      Real.log_le_log (div_pos hlogN_pos hlogM_pos) hdiv_le
    have hfl : (⌊Real.log (Real.log (N : ℝ) / Real.log (M_cut : ℝ)) / κ⌋₊ : ℝ) ≤
        Real.log (Real.log (N : ℝ) / Real.log (M_cut : ℝ)) / κ := by
      apply Nat.floor_le
      have hM_le_N : Real.log (M_cut : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < M_cut)) (by exact_mod_cast hMcut_le_N)
      exact div_nonneg (Real.log_nonneg ((one_le_div hlogM_pos).mpr hM_le_N)) hκ_pos.le
    dsimp only [K]; push_cast
    have hdiv := div_le_div_of_nonneg_right hlog_le hκ_pos.le
    linarith
  -- Cover `A_hi` by `i ∈ Finset.range K` with `B i = A_hi.filter (fun n => T (i + 1) < (n : ℝ) ∧ (n : ℝ) ≤ T i)`
  let blk (i : ℕ) : Finset ℕ := A_hi.filter (fun n => T (i + 1) < (n : ℝ) ∧ (n : ℝ) ≤ T i)
  have hcov : A_hi ⊆ (Finset.range K).biUnion blk := by
    intro n hn
    have hn1 := Finset.mem_filter.mp hn
    have hn_le_N : (n : ℝ) ≤ T 0 := by
      dsimp only [T]; rw [pow_zero, Real.rpow_one]; exact_mod_cast (hA_range n hn1.1).2
    have hn_gt_M : T K < (n : ℝ) := lt_of_le_of_lt hTK_le_M (by exact_mod_cast (by omega : M_cut < n))
    -- Find largest `i < K` with `(n : ℝ) ≤ T i`
    have hex : ∃ i ∈ Finset.range K, T (i + 1) < (n : ℝ) ∧ (n : ℝ) ≤ T i := by
      by_contra hnone
      push Not at hnone
      have hind : ∀ i : ℕ, i ≤ K → (n : ℝ) ≤ T i := by
        intro i hi
        induction i with
        | zero => exact hn_le_N
        | succ j ih =>
          by_contra hgt
          push Not at hgt
          have h1 := hnone j (Finset.mem_range.mpr (by omega)) hgt
          have h2 := ih (by omega)
          linarith
      linarith [hind K le_rfl]
    obtain ⟨i, hi, hlt, hle⟩ := hex
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hn, hlt, hle⟩⟩
  -- Sum over `i ∈ range K` exceeds `(δ / 2) * log(log N)`
  have hsum_ge : (δ / 2 : ℝ) * Real.log (Real.log (N : ℝ)) ≤
      ∑ i ∈ Finset.range K, ∑ n ∈ blk i, (1 : ℝ) / (n : ℝ) := by
    calc (δ / 2 : ℝ) * Real.log (Real.log (N : ℝ))
        ≤ ∑ n ∈ A_hi, (1 : ℝ) / (n : ℝ) := hhi_ge
      _ ≤ ∑ n ∈ (Finset.range K).biUnion blk, (1 : ℝ) / (n : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => by positivity
      _ ≤ ∑ i ∈ Finset.range K, ∑ n ∈ blk i, (1 : ℝ) / (n : ℝ) := by
          -- Blocks `blk i` are pairwise disjoint since `T` is strictly decreasing!
          have hT_anti : ∀ a b : ℕ, a < b → T b < T a := by
            intro a b hab
            dsimp only [T]
            apply Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < N))
            exact pow_lt_pow_right_of_lt_one₀ hr_pos hr_lt1 hab
          have hpair : (Finset.range K : Set ℕ).PairwiseDisjoint blk := by
            intro i _ j _ hne
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro n hn₁ hn₂
            have h1 := (Finset.mem_filter.mp hn₁).2
            have h2 := (Finset.mem_filter.mp hn₂).2
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · have : T j ≤ T (i + 1) := by
                rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with rfl | hlt'
                · exact le_rfl
                · exact (hT_anti _ _ hlt').le
              linarith
            · have : T i ≤ T (j + 1) := by
                rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with rfl | hlt'
                · exact le_rfl
                · exact (hT_anti _ _ hlt').le
              linarith
          rw [Finset.sum_biUnion hpair]
  -- By pigeonhole, some `i ∈ range K` has `∑ n ∈ blk i, 1/n ≥ δ * κ / 4`!
  have hex_i : ∃ i ∈ Finset.range K, δ * κ / 4 ≤ ∑ n ∈ blk i, (1 : ℝ) / (n : ℝ) := by
    by_contra hlt_all
    push Not at hlt_all
    have hsum_lt : ∑ i ∈ Finset.range K, ∑ n ∈ blk i, (1 : ℝ) / (n : ℝ) < (K : ℝ) * (δ * κ / 4) := by
      have hne : (Finset.range K).Nonempty := ⟨0, Finset.mem_range.mpr hK_ge1⟩
      calc ∑ i ∈ Finset.range K, ∑ n ∈ blk i, (1 : ℝ) / (n : ℝ)
          < ∑ _i ∈ Finset.range K, (δ * κ / 4) := Finset.sum_lt_sum_of_nonempty hne hlt_all
        _ = (K : ℝ) * (δ * κ / 4) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hK_mul : (K : ℝ) * (δ * κ / 4) ≤ (δ / 2 : ℝ) * Real.log (Real.log (N : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_right hK_le (by positivity : 0 ≤ δ * κ / 4)
      have hrew : (Real.log (Real.log (N : ℝ)) / κ + 1) * (δ * κ / 4) =
          (δ / 4 : ℝ) * Real.log (Real.log (N : ℝ)) + δ * κ / 4 := by
        field_simp [hκ_pos.ne']
      rw [hrew] at h1
      have hll_big := hN₀_big N hNbig
      have h2 : δ * κ / 4 ≤ (δ / 4 : ℝ) * Real.log (Real.log (N : ℝ)) := by
        have hnn : 0 ≤ (4 / δ) * ((M_cut : ℝ) + 4) := by positivity
        nlinarith
      linarith
    linarith
  obtain ⟨i, _, hbi_ge⟩ := hex_i
  -- Let `N' = ⌊T i⌋₊` and apply `hP1` to `blk i`!
  set N' : ℕ := ⌊T i⌋₊
  -- Note `blk i` is nonempty since its reciprocal sum is `≥ δ * κ / 4 > 0`, so `M_cut < n ≤ N'`!
  have hbi_ne : (blk i).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.sum_empty] at hbi_ge
    linarith [show (0 : ℝ) < δ * κ / 4 by positivity]
  obtain ⟨n₀, hn₀⟩ := hbi_ne
  have hMcut_le_N' : M_cut ≤ N' := by
    have h1 := Finset.mem_filter.mp hn₀
    have hgt : M_cut < n₀ := by have := (Finset.mem_filter.mp h1.1).2; omega
    have hle : n₀ ≤ N' := Nat.le_floor h1.2.2
    omega
  have hN'_ge_Np1 : N_p1 ≤ N' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMcut_le_N'
  have hN'_ge_M1 : M1 ≤ N' := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hMcut_le_N'
  have hN'_ge_M2 : M2 ≤ N' := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hMcut_le_N'
  have hN'_ge_M3 : M3 ≤ N' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMcut_le_N'
  have hN'_ge16 : 16 ≤ N' := le_trans hMcut_ge16 hMcut_le_N'
  have hlogN'_pos : 0 < Real.log (N' : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N'))
  -- Check all 5 hypotheses of `hP1` at `N'` and `blk i`!
  have hrange_bi : ∀ n ∈ blk i, (N' : ℝ) ^ (1 - c) ≤ (n : ℝ) ∧ n ≤ N' := by
    intro n hn
    have h1 := Finset.mem_filter.mp hn
    have hle : n ≤ N' := Nat.le_floor h1.2.2
    have hge : (N' : ℝ) ^ (1 - c) ≤ (n : ℝ) := by
      have hN'_le_T : (N' : ℝ) ≤ T i := Nat.floor_le (hT_pos i).le
      calc (N' : ℝ) ^ (1 - c) = (N' : ℝ) ^ r := rfl
        _ ≤ (T i) ^ r := Real.rpow_le_rpow (Nat.cast_nonneg _) hN'_le_T hr_pos.le
        _ = T (i + 1) := (hT_succ i).symm
        _ ≤ (n : ℝ) := h1.2.1.le
    exact ⟨hge, hle⟩
  have hz_le : (z : ℝ) ≤ (Real.log (N' : ℝ)) ^ (1 / 500 : ℝ) := by
    have := hM1 N' hN'_ge_M1; linarith
  have hsum_p1 : (2 : ℝ) / (y : ℝ) + (Real.log (N' : ℝ)) ^ (-(1 / 200 : ℝ)) ≤
      ∑ n ∈ blk i, (1 : ℝ) / (n : ℝ) := by
    have h1 : (Real.log (N' : ℝ)) ^ (-(1 / 200 : ℝ)) ≤ δ * κ / 8 := by
      rw [Real.rpow_neg hlogN'_pos.le, ← one_div]
      have h2 := hM2 N' hN'_ge_M2
      have hgt : 8 / (δ * κ) ≤ (Real.log (N' : ℝ)) ^ (1 / 200 : ℝ) := by linarith
      calc (1 : ℝ) / (Real.log (N' : ℝ)) ^ (1 / 200 : ℝ)
          ≤ 1 / (8 / (δ * κ)) := one_div_le_one_div_of_le (by positivity) hgt
        _ = δ * κ / 8 := by field_simp [hδ.ne', hκ_pos.ne']
    linarith
  have hdiv_p1 : ∀ n ∈ blk i, ∃ d₁ d₂ : ℕ, y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ d₂ ≤ z ∧ d₁ ∣ n ∧ d₂ ∣ n := by
    intro n hn
    have hnA : n ∈ A := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    obtain ⟨d₁, hd1a, hd1b, hd1d⟩ := hA_d1 n hnA
    obtain ⟨d₂, hd2a, hd2b, hd2d⟩ := hA_d2 n hnA
    exact ⟨d₁, d₂, hd1a, by omega, by omega, hd1d, hd2d⟩
  have hsm_p1 : ∀ n ∈ blk i, ∀ q₀ : ℕ, IsPrimePow q₀ → q₀ ∣ n → (q₀ : ℝ) ≤ (N' : ℝ) ^ (1 - 4 * c) := by
    intro n hn q₀ hqpp hqdvd
    have hnA : n ∈ A := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    have hle : n ≤ N' := (hrange_bi n hn).2
    have h1 := hA_sm n hnA q₀ hqpp hqdvd
    have h4c : 1 - 4 * c = 1 - ε := by dsimp only [c]; ring
    rw [h4c]
    exact h1.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hle) (by linarith))
  have hom_p1 : ∀ n ∈ blk i,
      (99 / 100 : ℝ) * Real.log (Real.log (N' : ℝ)) ≤ (n.primeFactors.card : ℝ) ∧
        (n.primeFactors.card : ℝ) ≤ 2 * Real.log (Real.log (N' : ℝ)) := by
    intro n hn
    have hnA : n ∈ A := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    have hrng := hrange_bi n hn
    have hll_n_le : Real.log (Real.log (n : ℝ)) ≤ Real.log (Real.log (N' : ℝ)) :=
      Real.log_le_log (Real.log_pos (by exact_mod_cast (by have := (hA_range n hnA).1; omega : 1 < n)))
        (Real.log_le_log (by exact_mod_cast (by have := (hA_range n hnA).1; omega : 0 < n)) (by exact_mod_cast hrng.2))
    have hll_n_ge : Real.log (Real.log (N' : ℝ)) - κ ≤ Real.log (Real.log (n : ℝ)) := by
      have hlog_ge : r * Real.log (N' : ℝ) ≤ Real.log (n : ℝ) := by
        have h := Real.log_le_log (by positivity) hrng.1
        rw [Real.log_rpow (by exact_mod_cast (by omega : 0 < N'))] at h
        linarith
      have h1 := Real.log_le_log (mul_pos hr_pos hlogN'_pos) hlog_ge
      rw [Real.log_mul hr_pos.ne' hlogN'_pos.ne'] at h1
      dsimp only [κ]
      linarith
    have hll_big := hM3 N' hN'_ge_M3
    have hom_n := abs_le.mp (hA_om n hnA)
    constructor <;> linarith
  obtain ⟨S, hS_sub, d, hd_lo, hd_hi, hS_sum⟩ :=
    hP1 N' hN'_ge_Np1 y z (by omega) (by omega) hz_le (blk i) hrange_bi hsum_p1 hdiv_p1 hsm_p1 hom_p1
  have hS_A : S ⊆ A := hS_sub.trans ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
  exact ⟨S, hS_A, d, hd_lo, hd_hi, hS_sum⟩

/-- Given `BloomProp1Statement`, for any sign `plus : Bool`, modulus `q ≥ 1`, and cutoff `X : ℕ`,
there exists a finite set `S` of primes `> X` such that `∑ p ∈ S, 1 / (shiftVal plus p) = 1 / q`. -/
theorem exists_shifted_prime_inv_q_of_bloom_prop1 (hProp1 : BloomProp1Statement)
    (plus : Bool) {q : ℕ} (hq : 1 ≤ q) (X : ℕ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ X < p) ∧
      ∑ p ∈ S, (1 : ℚ) / ((shiftVal plus p : ℕ) : ℚ) = (1 : ℚ) / (q : ℚ) := by
  obtain ⟨ε₀, hε₀_pos, hε₀_lt, hFilt⟩ := shifted_prime_filtered_set_exists plus hq X
  obtain ⟨y₀, hy₀_4, hProp2⟩ := prop_tech_of_bloom_prop1 hProp1 (δ := 1 / 8) (ε := ε₀)
    (by norm_num) hε₀_pos (by linarith)
  obtain ⟨w, z, hyw, h4wz, N_f, hN_f, hB'⟩ := hFilt ε₀ hε₀_pos le_rfl y₀ hy₀_4
  obtain ⟨N_p2, hN_p2, hP2⟩ := hProp2 y₀ w z le_rfl hyw h4wz
  -- Choose `N` large enough that `(1 / 8) * log(log N) ≥ z^2` and `N ≥ max N_f N_p2`
  have htend_ll : Tendsto (fun N : ℕ => (1 / 8 : ℝ) * Real.log (Real.log (N : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop
      (by norm_num)
  obtain ⟨N_z, hN_z⟩ := (tendsto_atTop.mp htend_ll ((z : ℝ) ^ 2 + 1)).exists_forall_of_atTop
  set N : ℕ := max (max N_f N_p2) N_z
  have hNf : N_f ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNp2 : N_p2 ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hNz : N_z ≤ N := le_max_right _ _
  -- Let `B₀` be the filtered shifted-prime set at scale `N`
  set B₀ : Finset ℕ := (Finset.Icc 2 N).filter (fun m =>
    (unshiftPrime plus q m).Prime ∧
    X < unshiftPrime plus q m ∧
    (∀ r : ℕ, IsPrimePow r → r ∣ m → (r : ℝ) ≤ (m : ℝ) ^ (1 - ε₀)) ∧
    |(m.primeFactors.card : ℝ) - Real.log (Real.log (m : ℝ))| ≤ Real.log (Real.log (m : ℝ)) / 1000 ∧
    (∃ d₁ : ℕ, y₀ ≤ d₁ ∧ d₁ < w ∧ d₁ ∣ m) ∧
    (∃ d₂ : ℕ, 4 * w ≤ d₂ ∧ d₂ < z ∧ d₂ ∣ m))
  have hB₀_sum : (1 / 4 : ℝ) * Real.log (Real.log (N : ℝ)) ≤ ∑ m ∈ B₀, (1 : ℝ) / (m : ℝ) := hB' N hNf
  -- Extract `K = z^2` pairwise disjoint subsets `T 0, ..., T (K - 1) ⊆ B₀` with `R(T i) = 1 / d i`, `d i ∈ [y₀, z]`!
  set K : ℕ := z ^ 2
  have hex_seq : ∀ k : ℕ, k ≤ K →
      ∃ (T : Fin k → Finset ℕ) (d : Fin k → ℕ),
        (∀ i, T i ⊆ B₀) ∧
        (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
        (∀ i, y₀ ≤ d i ∧ d i ≤ z ∧ ∑ m ∈ T i, (1 : ℚ) / (m : ℚ) = (1 : ℚ) / (d i : ℚ)) := by
    intro k hk
    induction k with
    | zero => exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      obtain ⟨T, d, hTsub, hTdisj, hTd⟩ := ih (by omega)
      -- Let `U = ⋃ i, T i` and `Rem = B₀ \ U`
      set U : Finset ℕ := Finset.univ.biUnion T
      set Rem : Finset ℕ := B₀ \ U
      have hU_sum : ∑ m ∈ U, (1 : ℝ) / (m : ℝ) ≤ (k : ℝ) := by
        have hpair : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint T := by
          intro i _ j _ hne
          exact hTdisj i j hne
        rw [Finset.sum_biUnion hpair]
        calc ∑ i : Fin k, ∑ m ∈ T i, (1 : ℝ) / (m : ℝ)
            ≤ ∑ _i : Fin k, (1 : ℝ) := by
              refine Finset.sum_le_sum fun i _ => ?_
              have hq_eq := (hTd i).2.2
              have hR : ∑ m ∈ T i, (1 : ℝ) / (m : ℝ) = (1 : ℝ) / ((d i : ℕ) : ℝ) := by
                have hc := congrArg (fun x : ℚ => (x : ℝ)) hq_eq
                push_cast at hc; exact hc
              rw [hR, one_div]
              exact inv_le_one_of_one_le₀ (by exact_mod_cast (by have := (hTd i).1; omega : 1 ≤ d i))
          _ = (k : ℝ) := by simp
      have hRem_sum : (1 / 8 : ℝ) * Real.log (Real.log (N : ℝ)) ≤ ∑ m ∈ Rem, (1 : ℝ) / (m : ℝ) := by
        have hU_sub : U ⊆ B₀ := Finset.biUnion_subset.mpr fun i _ => hTsub i
        have hdiff : ∑ m ∈ Rem, (1 : ℝ) / (m : ℝ) =
            (∑ m ∈ B₀, (1 : ℝ) / (m : ℝ)) - ∑ m ∈ U, (1 : ℝ) / (m : ℝ) := by
          have := Finset.sum_sdiff (f := fun m : ℕ => (1 : ℝ) / (m : ℝ)) hU_sub
          linarith
        have hkz : (k : ℝ) ≤ (z : ℝ) ^ 2 := by
          have : k ≤ z ^ 2 := by omega
          exact_mod_cast this
        have hbig := hN_z N hNz
        linarith
      -- Apply `hP2` to `Rem ⊆ B₀`!
      have hRem_B0 : ∀ m ∈ Rem, m ∈ B₀ := fun m hm => (Finset.mem_sdiff.mp hm).1
      obtain ⟨S_new, hS_sub, d_new, hd_lo, hd_hi, hS_sum⟩ := hP2 N hNp2 Rem
        (fun m hm => Finset.mem_Icc.mp (Finset.mem_filter.mp (hRem_B0 m hm)).1)
        (fun m hm => (Finset.mem_filter.mp (hRem_B0 m hm)).2.2.2.1)
        (fun m hm => (Finset.mem_filter.mp (hRem_B0 m hm)).2.2.2.2.1)
        (fun m hm => (Finset.mem_filter.mp (hRem_B0 m hm)).2.2.2.2.2.1)
        (fun m hm => (Finset.mem_filter.mp (hRem_B0 m hm)).2.2.2.2.2.2)
        hRem_sum
      -- Extend `T` and `d` to `Fin (k + 1)`
      let T' : Fin (k + 1) → Finset ℕ := Fin.snoc T S_new
      let d' : Fin (k + 1) → ℕ := Fin.snoc d d_new
      refine ⟨T', d', ?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [T'] using hS_sub.trans Finset.sdiff_subset
        · simpa [T'] using hTsub j
      · intro i j hne
        revert hne
        refine Fin.lastCases ?_ (fun i' => ?_) i
        · refine Fin.lastCases (fun h => absurd rfl h) (fun j' _ => ?_) j
          simp only [T', Fin.snoc_last, Fin.snoc_castSucc]
          rw [Finset.disjoint_left]
          intro m hmS hmTj
          have hmRem := hS_sub hmS
          exact (Finset.mem_sdiff.mp hmRem).2 (Finset.mem_biUnion.mpr ⟨j', Finset.mem_univ _, hmTj⟩)
        · refine Fin.lastCases (fun _ => ?_) (fun j' hne' => ?_) j
          · simp only [T', Fin.snoc_last, Fin.snoc_castSucc]
            rw [Finset.disjoint_right]
            intro m hmS hmTi
            have hmRem := hS_sub hmS
            exact (Finset.mem_sdiff.mp hmRem).2 (Finset.mem_biUnion.mpr ⟨i', Finset.mem_univ _, hmTi⟩)
          · simp only [T', Fin.snoc_castSucc]
            exact hTdisj i' j' (fun h => hne' (congrArg Fin.castSucc h))
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [T', d', Fin.snoc_last]
          exact ⟨hd_lo, hd_hi, hS_sum⟩
        · simp only [T', d', Fin.snoc_castSucc]
          exact hTd j
  obtain ⟨T, d, hTsub, hTdisj, hTd⟩ := hex_seq K le_rfl
  -- Pigeonhole: among `z^2` indices `i : Fin (z^2)` with `d i ∈ Icc 1 z`, some `d₀ ∈ Icc 1 z`
  -- has fiber size `≥ d₀` (since `∑_{v = 1}^z (v - 1) = z*(z-1)/2 < z^2` for `z ≥ 1`)!
  have hz_pos : 1 ≤ z := by omega
  have hex_fiber : ∃ d₀ ∈ Finset.Icc 1 z, d₀ ≤ (Finset.univ.filter (fun i : Fin K => d i = d₀)).card := by
    by_contra hnone
    push Not at hnone
    have hsum_fib : ∑ v ∈ Finset.Icc 1 z, (Finset.univ.filter (fun i : Fin K => d i = v)).card = K := by
      rw [← Finset.card_biUnion]
      · have heq : (Finset.Icc 1 z).biUnion (fun v => Finset.univ.filter (fun i : Fin K => d i = v)) = Finset.univ := by
          ext i
          simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          exact ⟨d i, ⟨by have := (hTd i).1; omega, (hTd i).2.1⟩, rfl⟩
        rw [heq, Finset.card_univ, Fintype.card_fin]
      · intro v₁ _ v₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        have h1 := (Finset.mem_filter.mp hi1).2
        have h2 := (Finset.mem_filter.mp hi2).2
        exact hne (h1.symm.trans h2)
    have hlt_sum : ∑ v ∈ Finset.Icc 1 z, (Finset.univ.filter (fun i : Fin K => d i = v)).card ≤
        ∑ v ∈ Finset.Icc 1 z, (v - 1) := by
      refine Finset.sum_le_sum fun v hv => ?_
      have := hnone v hv
      omega
    have hbound_z : ∑ v ∈ Finset.Icc 1 z, (v - 1) < z ^ 2 := by
      calc ∑ v ∈ Finset.Icc 1 z, (v - 1)
          ≤ ∑ _v ∈ Finset.Icc 1 z, (z - 1) :=
            Finset.sum_le_sum fun v hv => by have := (Finset.mem_Icc.mp hv).2; omega
        _ = z * (z - 1) := by rw [Finset.sum_const, Nat.card_Icc]; simp
        _ < z * z := Nat.mul_lt_mul_of_pos_left (by omega) hz_pos
        _ = z ^ 2 := (sq z).symm
    omega
  obtain ⟨d₀, hd₀_icc, hd₀_le⟩ := hex_fiber
  have hd₀_pos : 0 < d₀ := (Finset.mem_Icc.mp hd₀_icc).1
  obtain ⟨I, hI_sub, hI_card⟩ := Finset.exists_subset_card_eq hd₀_le
  -- Take `M_set = I.biUnion T ⊆ B₀`! Then `∑ m ∈ M_set, 1/m = d₀ * (1 / d₀) = 1`!
  set M_set : Finset ℕ := I.biUnion T
  have hM_sub : M_set ⊆ B₀ := Finset.biUnion_subset.mpr fun i _ => hTsub i
  have hM_sum : ∑ m ∈ M_set, (1 : ℚ) / (m : ℚ) = 1 := by
    have hpair : (I : Set (Fin K)).PairwiseDisjoint T := fun i _ j _ hne => hTdisj i j hne
    rw [Finset.sum_biUnion hpair]
    have heach : ∀ i ∈ I, ∑ m ∈ T i, (1 : ℚ) / (m : ℚ) = (1 : ℚ) / (d₀ : ℚ) := by
      intro i hi
      have hdi : d i = d₀ := (Finset.mem_filter.mp (hI_sub hi)).2
      rw [← hdi]
      exact (hTd i).2.2
    rw [Finset.sum_congr rfl heach, Finset.sum_const, hI_card, nsmul_eq_mul]
    have hd₀0 : (d₀ : ℚ) ≠ 0 := by exact_mod_cast hd₀_pos.ne'
    field_simp [hd₀0]
  -- Map `M_set` to primes via `m ↦ unshiftPrime plus q m`!
  set S : Finset ℕ := M_set.image (unshiftPrime plus q)
  have hinj : Set.InjOn (unshiftPrime plus q) (M_set : Set ℕ) :=
    (unshiftPrime_injOn plus hq).mono fun m hm => (Finset.mem_filter.mp (hM_sub hm)).2.1
  refine ⟨S, ?_, ?_⟩
  · intro p hp
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hp
    have hmB := (Finset.mem_filter.mp (hM_sub hm)).2
    exact ⟨hmB.1, hmB.2.1⟩
  · rw [Finset.sum_image hinj]
    have hterm : ∀ m ∈ M_set,
        (1 : ℚ) / ((shiftVal plus (unshiftPrime plus q m) : ℕ) : ℚ) =
          ((1 : ℚ) / (q : ℚ)) * ((1 : ℚ) / (m : ℚ)) := by
      intro m hm
      have hpr : (unshiftPrime plus q m).Prime := (Finset.mem_filter.mp (hM_sub hm)).2.1
      rw [shiftVal_unshiftPrime plus hpr, Nat.cast_mul]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hM_sum, mul_one]

/-- **Complete Unconditional Reduction of Zhi-Wei Sun's Conjecture (PPL 024)** to `BloomProp1Statement`:
For every positive rational `r : ℚ` and both signs `d ∈ ({-1, 1} : Set ℤ)`, there exists a finite
set `S : Finset ℕ` of primes such that `r = ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) + (d : ℚ))`. -/
theorem sun_conjecture_of_bloom_prop1 (hProp1 : BloomProp1Statement)
    (r : ℚ) (hr : 0 < r) (plus : Bool) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      r = ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) + (if plus then (1 : ℚ) else (-1 : ℚ))) := by
  -- Write `r = a / b` with `a = r.num.toNat ≥ 1` and `b = r.den ≥ 1`
  set a : ℕ := r.num.toNat
  set b : ℕ := r.den
  have hnum_pos : 0 < r.num := Rat.num_pos.mpr hr
  have ha_eq : (a : ℤ) = r.num := Int.toNat_of_nonneg hnum_pos.le
  have hb_pos : 1 ≤ b := r.den_pos
  have hr_eq : r = (a : ℚ) / (b : ℚ) := by
    have h := (Rat.num_div_den r).symm
    have ha_q : (a : ℚ) = (r.num : ℚ) := by exact_mod_cast ha_eq
    rw [← ha_q] at h
    exact h
  -- Induct on `k` to construct a finite set `S` of primes summing to `k / b`
  suffices hstep : ∀ k : ℕ, ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      ∑ p ∈ S, (1 : ℚ) / ((shiftVal plus p : ℕ) : ℚ) = (k : ℚ) / (b : ℚ) by
    obtain ⟨S, hSpr, hSsum⟩ := hstep a
    refine ⟨S, hSpr, ?_⟩
    rw [hr_eq, ← hSsum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [shiftVal_cast_rat plus (hSpr p hp)]
  intro k
  induction k with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨S₁, hS₁_pr, hS₁_sum⟩ := ih
    set X : ℕ := S₁.sup id
    obtain ⟨S₂, hS₂_pr, hS₂_sum⟩ := exists_shifted_prime_inv_q_of_bloom_prop1 hProp1 plus hb_pos X
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have hle : p ≤ X := Finset.le_sup (f := id) hp1
      have hgt : X < p := (hS₂_pr p hp2).2
      omega
    refine ⟨S₁ ∪ S₂, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_union.mp hp with h1 | h2
      · exact hS₁_pr p h1
      · exact (hS₂_pr p h2).1
    · rw [Finset.sum_union hdisj, hS₁_sum, hS₂_sum]
      push_cast
      ring

end PPL024
