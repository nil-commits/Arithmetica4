import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import RHDirect.Stage8MertensTheorems
import RHDirect.Stage10SiegelWalfiszFull

/-!
# PPL 024 Analytic Foundations — Part 1: Mertens in AP, Partial Summation, and Small Divisors

Unconditional formalization of:
1. Unified shifted-prime arithmetic (`p - 1` and `p + 1`) via `shiftVal` / `unshiftPrime`.
2. Lower bound on the reciprocal sum `∑_{m ≤ N, q*m ∓ 1 prime, > X} 1 / m ≥ (1/2) log log N`
   via `RHDirect.Stage8MertensTheorems.mertens_second_theorem_AP`.
3. Elementary dyadic partial summation (`reciprocal_sum_le_of_count_bound`).
4. Bloom's Lemma 3 (`shifted_prime_no_prime_divisor_in_Icc`): the relative density of primes
   `p ≤ N` such that `p ± 1` has no prime divisor in `[y, z]` is `O(log y / log z)`,
   proved via the Sieve of Eratosthenes–Legendre, `Stage10SiegelWalfiszFull.siegel_walfisz_pi_real`,
   and `Stage8MertensTheorems.mertens_third_theorem_quant`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset Filter Topology

namespace PPL024

/-! ## Section 1: Unified Shifted-Prime Definitions -/

/-- Shifted value of a natural number `p`: `p + 1` when `plus = true`, `p - 1` when `plus = false`. -/
def shiftVal (plus : Bool) (p : ℕ) : ℕ :=
  if plus then p + 1 else p - 1

/-- Residue class modulo `d` corresponding to `d ∣ shiftVal plus p`:
`d - 1` when `plus = true`, `1` when `plus = false`. -/
def shiftRes (plus : Bool) (d : ℕ) : ℕ :=
  if plus then d - 1 else 1

/-- Inverse map recovering `p` from `m = shiftVal plus p / q`:
`q * m - 1` when `plus = true`, `q * m + 1` when `plus = false`. -/
def unshiftPrime (plus : Bool) (q m : ℕ) : ℕ :=
  if plus then q * m - 1 else q * m + 1

lemma shiftVal_pos_of_prime (plus : Bool) {p : ℕ} (hp : p.Prime) : 0 < shiftVal plus p := by
  have hp2 : 2 ≤ p := hp.two_le
  cases plus <;> simp only [shiftVal, Bool.false_eq_true, ↓reduceIte] <;> omega

lemma shiftVal_cast_rat (plus : Bool) {p : ℕ} (hp : p.Prime) :
    ((shiftVal plus p : ℕ) : ℚ) = (p : ℚ) + (if plus then (1 : ℚ) else (-1 : ℚ)) := by
  have hp2 : 2 ≤ p := hp.two_le
  cases plus
  · simp only [shiftVal, Bool.false_eq_true, ↓reduceIte]
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    push_cast
    ring
  · simp only [shiftVal, ↓reduceIte]
    push_cast
    ring

lemma shiftRes_coprime (plus : Bool) {d : ℕ} (hd : 1 ≤ d) :
    Nat.Coprime (shiftRes plus d) d := by
  cases plus
  · simp [shiftRes]
  · simp only [shiftRes, ↓reduceIte]
    have h : Nat.Coprime (d - 1) ((d - 1) + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    rwa [Nat.sub_add_cancel hd] at h

lemma dvd_shiftVal_iff_modEq (plus : Bool) {d p : ℕ} (hd : 1 ≤ d) (hp : 1 ≤ p) :
    d ∣ shiftVal plus p ↔ p ≡ shiftRes plus d [MOD d] := by
  cases plus
  · simp only [shiftVal, shiftRes, Bool.false_eq_true, ↓reduceIte]
    rw [Nat.ModEq]
    constructor
    · rintro ⟨k, hk⟩
      have hp_eq : p = d * k + 1 := by omega
      rw [hp_eq, Nat.mul_add_mod]
    · intro hmod
      have h1 : (p - 1) % d = 0 := by
        rcases eq_or_lt_of_le hd with rfl | hd2
        · simp [Nat.mod_one]
        · have : 1 % d = 1 := Nat.mod_eq_of_lt hd2
          rw [this] at hmod
          have hdiv := Nat.div_add_mod p d
          rw [hmod] at hdiv
          have : p - 1 = d * (p / d) := by omega
          rw [this, Nat.mul_mod_right]
      exact Nat.dvd_of_mod_eq_zero h1
  · simp only [shiftVal, shiftRes, ↓reduceIte]
    rw [Nat.ModEq]
    rcases eq_or_lt_of_le hd with rfl | hd2
    · simp [Nat.mod_one]
    · constructor
      · rintro ⟨k, hk⟩
        have hk1 : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with rfl | hkpos
          · omega
          · exact hkpos
        have hp_eq : p = d * (k - 1) + (d - 1) := by
          have : d * k = d * (k - 1) + d := by
            conv_lhs => rw [← Nat.sub_add_cancel hk1, mul_add, mul_one]
          omega
        rw [hp_eq, Nat.mul_add_mod]
      · intro hmod
        have hlt : d - 1 < d := by omega
        rw [Nat.mod_eq_of_lt hlt] at hmod
        have hdiv := Nat.div_add_mod p d
        rw [hmod] at hdiv
        have hp1 : p + 1 = d * (p / d + 1) := by
          rw [mul_add, mul_one]
          omega
        exact ⟨p / d + 1, hp1⟩

lemma shiftVal_unshiftPrime (plus : Bool) {q m : ℕ} (hp : (unshiftPrime plus q m).Prime) :
    shiftVal plus (unshiftPrime plus q m) = q * m := by
  have hp2 : 2 ≤ unshiftPrime plus q m := hp.two_le
  cases plus <;> simp only [shiftVal, unshiftPrime, Bool.false_eq_true, ↓reduceIte] at hp2 ⊢ <;> omega

lemma unshiftPrime_div_eq (plus : Bool) {q p : ℕ} (hp : p.Prime) (hd : q ∣ shiftVal plus p) :
    unshiftPrime plus q (shiftVal plus p / q) = p := by
  have hmul : q * (shiftVal plus p / q) = shiftVal plus p := Nat.mul_div_cancel' hd
  have hp2 : 2 ≤ p := hp.two_le
  cases plus <;> simp only [unshiftPrime, shiftVal, Bool.false_eq_true, ↓reduceIte] at hmul ⊢ <;> omega

lemma primeCountAP_eq_Icc_card (q a N : ℕ) :
    RHDirect.Stage2DirichletAP.primeCountAP q a (N : ℝ) =
      ((Finset.Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card := by
  unfold RHDirect.Stage2DirichletAP.primeCountAP
  rw [Nat.floor_natCast]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hlt, hpr, hmod⟩
    exact ⟨⟨hpr.pos, by omega⟩, hpr, hmod⟩
  · rintro ⟨⟨_, hle⟩, hpr, hmod⟩
    exact ⟨by omega, hpr, hmod⟩

/-! ## Section 2: Lower Bound on Reciprocal Sum of Shifted Primes in AP -/

/-- For any modulus `q ≥ 1`, sign `plus`, and cutoff `X`, the reciprocal sum of `m ≤ N` with
`unshiftPrime plus q m` prime and `> X` is at least `(1/2) * log (log N)` for all large `N`. -/
theorem shifted_prime_ap_reciprocal_sum_lower (plus : Bool) {q : ℕ} (hq : 1 ≤ q) (X : ℕ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) ≤
        ∑ m ∈ (Finset.Icc 1 N).filter (fun m => (unshiftPrime plus q m).Prime ∧ X < unshiftPrime plus q m),
          (1 : ℝ) / (m : ℝ) := by
  have : NeZero q := ⟨by omega⟩
  have hcop : Nat.Coprime (shiftRes plus q) q := shiftRes_coprime plus hq
  obtain ⟨M_qa, C, hCpos, hMert⟩ := RHDirect.Stage8MertensTheorems.mertens_second_theorem_AP hcop
  -- Choose `K_cut ≥ max X 3` so that `p > K_cut` implies `1 / (p + 1) ≥ (3 / 4) / p`
  set Kcut : ℕ := max X 3
  -- Bound the tail up to `Kcut`: `∑_{p ≤ Kcut} 1/p ≤ Kcut`
  set tailBd : ℝ := (Kcut : ℝ) + |M_qa| + C + 2
  -- We need `N₀` large enough that:
  -- `(3/4) * log (log (q * N - 1)) ≥ (1/2) * log (log N) + (q.totient : ℝ) * (tailBd + 1)`
  -- and `q * N - 1 ≥ max 3 (N / 2)`
  have htot_pos : (0 : ℝ) < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
  have hq_ge_tot : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hq_div_tot : (1 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) := (one_le_div htot_pos).mpr hq_ge_tot
  -- Pick `N₀` such that `(1/4) * log (log N) ≥ (q : ℝ) * tailBd + 4` and `N₀ ≥ 16`
  have htend : Tendsto (fun N : ℕ => (1 / 4 : ℝ) * Real.log (Real.log (N : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop
      (by norm_num)
  obtain ⟨N₁, hN₁⟩ := (tendsto_atTop.mp htend ((q : ℝ) * tailBd + 10)).exists_forall_of_atTop
  set N₀ : ℕ := max (max N₁ (Kcut + 4)) 16
  refine ⟨N₀, by omega, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := le_trans (le_max_right _ _) hN
  have hNK : Kcut + 4 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  -- Let `Y = q * N - 1` so every prime `p ∈ (Kcut, Y]` with `p ≡ shiftRes plus q [MOD q]`
  -- yields `m = shiftVal plus p / q ∈ [1, N]`.
  set Y : ℕ := q * N - 1
  have hY_ge_N : N - 1 ≤ Y := by
    have : 1 * N ≤ q * N := Nat.mul_le_mul_right N hq
    omega
  have hY3 : (3 : ℝ) ≤ (Y : ℝ) := by
    have : 3 ≤ Y := by omega
    exact_mod_cast this
  have hY_ge_halfN : (N : ℝ) / 2 ≤ (Y : ℝ) := by
    have : N ≤ 2 * Y := by omega
    have hR : (N : ℝ) ≤ 2 * (Y : ℝ) := by exact_mod_cast this
    linarith
  have hlogY_ge_1 : (1 : ℝ) ≤ Real.log (Y : ℝ) := by
    have h3 : Real.exp 1 ≤ (Y : ℝ) := by
      have he : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        linarith
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (Y : ℝ) := Real.log_le_log (Real.exp_pos 1) h3
  -- Define the AP prime set `P_hi = {p ∈ Icc (Kcut + 1) Y | p.Prime ∧ p ≡ shiftRes plus q [MOD q]}`
  set P_all : Finset ℕ := (Finset.Icc 1 Y).filter (fun p => p.Prime ∧ p ≡ shiftRes plus q [MOD q])
  set P_hi : Finset ℕ := P_all.filter (fun p => Kcut < p)
  set S_m : Finset ℕ := (Finset.Icc 1 N).filter (fun m => (unshiftPrime plus q m).Prime ∧ X < unshiftPrime plus q m)
  -- Injection `f : P_hi → S_m` given by `p ↦ shiftVal plus p / q`
  let f : ℕ → ℕ := fun p => shiftVal plus p / q
  have hf_maps : ∀ p ∈ P_hi, f p ∈ S_m := by
    intro p hp
    have hp1 := Finset.mem_filter.mp hp
    have hp_all := Finset.mem_filter.mp hp1.1
    have hp_icc := Finset.mem_Icc.mp hp_all.1
    have hpr : p.Prime := hp_all.2.1
    have hmod : p ≡ shiftRes plus q [MOD q] := hp_all.2.2
    have hgtK : Kcut < p := hp1.2
    have hdvd : q ∣ shiftVal plus p := (dvd_shiftVal_iff_modEq plus hq hpr.pos).mpr hmod
    have hsh_pos : 0 < shiftVal plus p := shiftVal_pos_of_prime plus hpr
    have hsh_le : shiftVal plus p ≤ q * N := by
      cases plus <;> simp only [shiftVal, Bool.false_eq_true, ↓reduceIte] <;> omega
    have hfm_pos : 1 ≤ f p := by
      dsimp only [f]
      exact Nat.div_pos (Nat.le_of_dvd hsh_pos hdvd) (by omega)
    have hfm_le : f p ≤ N := by
      dsimp only [f]
      exact Nat.div_le_of_le_mul hsh_le
    have hun : unshiftPrime plus q (f p) = p := unshiftPrime_div_eq plus hpr hdvd
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hfm_pos, hfm_le⟩,
      by rw [hun]; exact hpr, by rw [hun]; exact lt_of_le_of_lt (le_max_left X 3) hgtK⟩
  have hf_inj : Set.InjOn f (P_hi : Set ℕ) := by
    intro p₁ hp₁ p₂ hp₂ heq
    have h1 := Finset.mem_filter.mp (Finset.mem_filter.mp hp₁).1
    have h2 := Finset.mem_filter.mp (Finset.mem_filter.mp hp₂).1
    have hd1 : q ∣ shiftVal plus p₁ := (dvd_shiftVal_iff_modEq plus hq h1.2.1.pos).mpr h1.2.2
    have hd2 : q ∣ shiftVal plus p₂ := (dvd_shiftVal_iff_modEq plus hq h2.2.1.pos).mpr h2.2.2
    have hu1 := unshiftPrime_div_eq plus h1.2.1 hd1
    have hu2 := unshiftPrime_div_eq plus h2.2.1 hd2
    dsimp only [f] at heq
    rw [← hu1, ← hu2, heq]
  -- Compare sums: `∑_{m ∈ S_m} 1/m ≥ ∑_{p ∈ P_hi} 1 / f p ≥ (3/4) * q * ∑_{p ∈ P_hi} 1/p`
  have hsum_ge_img : ∑ p ∈ P_hi, (1 : ℝ) / (f p : ℝ) ≤ ∑ m ∈ S_m, (1 : ℝ) / (m : ℝ) := by
    rw [← Finset.sum_image (f := fun m : ℕ => (1 : ℝ) / (m : ℝ)) hf_inj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hf_maps)
      fun _ _ _ => by positivity
  have hterm_ge : ∀ p ∈ P_hi, ((3 / 4 : ℝ) * (q : ℝ)) * (p : ℝ)⁻¹ ≤ (1 : ℝ) / (f p : ℝ) := by
    intro p hp
    have hp1 := Finset.mem_filter.mp hp
    have hp_all := Finset.mem_filter.mp hp1.1
    have hpr : p.Prime := hp_all.2.1
    have hdvd : q ∣ shiftVal plus p := (dvd_shiftVal_iff_modEq plus hq hpr.pos).mpr hp_all.2.2
    have hgt3 : 3 < p := lt_of_le_of_lt (le_max_right X 3) hp1.2
    have hfm_mul : (q : ℝ) * (f p : ℝ) = (shiftVal plus p : ℝ) := by
      exact_mod_cast Nat.mul_div_cancel' hdvd
    have hsh_le : (shiftVal plus p : ℝ) ≤ (4 / 3 : ℝ) * (p : ℝ) := by
      have hp4 : (4 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 4 ≤ p)
      cases plus
      · simp only [shiftVal, Bool.false_eq_true, ↓reduceIte]
        have : (p - 1 : ℕ) ≤ p := Nat.sub_le p 1
        have hR : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast this
        linarith
      · simp only [shiftVal, ↓reduceIte]
        push_cast
        linarith
    have hfp_pos : (0 : ℝ) < (f p : ℝ) := by
      have hsh_pos : 0 < shiftVal plus p := shiftVal_pos_of_prime plus hpr
      have hmul := Nat.mul_div_cancel' hdvd
      have : 0 < f p := by
        by_contra h0
        have h0' : f p = 0 := by omega
        dsimp only [f] at h0'
        rw [h0', mul_zero] at hmul
        omega
      exact_mod_cast this
    have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpr.pos
    rw [one_div, mul_assoc, ← div_eq_mul_inv]
    rw [show (3 / 4 : ℝ) * ((q : ℝ) / (p : ℝ)) = (3 * (q : ℝ)) / (4 * (p : ℝ)) by ring]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (p : ℝ))]
    have hgoal : (3 : ℝ) * ((q : ℝ) * (f p : ℝ)) ≤ 4 * (p : ℝ) := by
      rw [hfm_mul]; linarith
    have hdiv : (3 : ℝ) * (q : ℝ) ≤ (f p : ℝ)⁻¹ * (4 * (p : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hgoal (inv_nonneg.mpr hfp_pos.le)
      have hl : (f p : ℝ)⁻¹ * (3 * ((q : ℝ) * (f p : ℝ))) = 3 * (q : ℝ) := by
        field_simp [hfp_pos.ne']
      linarith
    exact hdiv
  -- Relate `∑_{p ∈ P_hi} p⁻¹` to `∑_{p ∈ P_all} p⁻¹` via Mertens in AP
  have hP_lo_bound : ∑ p ∈ P_all.filter (fun p => ¬ Kcut < p), (p : ℝ)⁻¹ ≤ (Kcut : ℝ) := by
    calc ∑ p ∈ P_all.filter (fun p => ¬ Kcut < p), (p : ℝ)⁻¹
        ≤ ∑ p ∈ P_all.filter (fun p => ¬ Kcut < p), (1 : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp1 : 1 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
          exact inv_le_one_of_one_le₀ (by exact_mod_cast hp1)
      _ = ((P_all.filter (fun p => ¬ Kcut < p)).card : ℝ) := by simp
      _ ≤ (Kcut : ℝ) := by
          have hsub : P_all.filter (fun p => ¬ Kcut < p) ⊆ Finset.Icc 1 Kcut := by
            intro p hp
            have h1 := Finset.mem_filter.mp hp
            have h2 := Finset.mem_Icc.mp (Finset.mem_filter.mp h1.1).1
            exact Finset.mem_Icc.mpr ⟨h2.1, by omega⟩
          exact_mod_cast (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
  have hP_split : ∑ p ∈ P_all, (p : ℝ)⁻¹ =
      ∑ p ∈ P_hi, (p : ℝ)⁻¹ + ∑ p ∈ P_all.filter (fun p => ¬ Kcut < p), (p : ℝ)⁻¹ :=
    (Finset.sum_filter_add_sum_filter_not P_all (fun p => Kcut < p) (fun p => (p : ℝ)⁻¹)).symm
  have hMert_Y := hMert (Y : ℝ) hY3
  rw [Nat.floor_natCast] at hMert_Y
  have hP_all_ge : (1 / (q.totient : ℝ)) * Real.log (Real.log (Y : ℝ)) + M_qa - C / Real.log (Y : ℝ) ≤
      ∑ p ∈ P_all, (p : ℝ)⁻¹ := by
    have h1 := (abs_le.mp hMert_Y).1
    linarith
  have hC_div : C / Real.log (Y : ℝ) ≤ C := div_le_self hCpos.le hlogY_ge_1
  have hP_hi_ge : (1 / (q.totient : ℝ)) * Real.log (Real.log (Y : ℝ)) - tailBd ≤
      ∑ p ∈ P_hi, (p : ℝ)⁻¹ := by
    have hMabs : -|M_qa| ≤ M_qa := neg_abs_le M_qa
    dsimp only [tailBd]
    linarith
  -- Compare `log (log Y)` with `log (log N)`: since `Y ≥ N / 2`, `log Y ≥ log N - log 2 ≥ (1/2) log N`,
  -- so `log (log Y) ≥ log (log N) - log 2 ≥ log (log N) - 1`.
  have hlogN_ge_2 : (2 : ℝ) ≤ Real.log (N : ℝ) := by
    have h16 : Real.exp 2 ≤ (N : ℝ) := by
      have he2 : Real.exp 2 < 16 := by
        have h1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos 1]
      have hN16R : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
      linarith
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log (N : ℝ) := Real.log_le_log (Real.exp_pos 2) h16
  have hlog2_le_1 : Real.log 2 ≤ 1 := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2e
      _ = 1 := Real.log_exp 1
  have hloglogY_ge : Real.log (Real.log (N : ℝ)) - 1 ≤ Real.log (Real.log (Y : ℝ)) := by
    have hlogY_half : Real.log (N : ℝ) / 2 ≤ Real.log (Y : ℝ) := by
      have h1 : Real.log ((N : ℝ) / 2) ≤ Real.log (Y : ℝ) :=
        Real.log_le_log (by positivity) hY_ge_halfN
      rw [Real.log_div (by positivity) (by norm_num)] at h1
      linarith
    have h2 : Real.log (Real.log (N : ℝ) / 2) ≤ Real.log (Real.log (Y : ℝ)) :=
      Real.log_le_log (by positivity) hlogY_half
    rw [Real.log_div (by positivity) (by norm_num)] at h2
    linarith
  -- Assemble the lower bound!
  have hbig : (q : ℝ) * tailBd + 10 ≤ (1 / 4 : ℝ) * Real.log (Real.log (N : ℝ)) := hN₁ N hNN₁
  have hloglogN_nn : 0 ≤ Real.log (Real.log (N : ℝ)) :=
    Real.log_nonneg (by linarith)
  have hstep1 : ((3 / 4 : ℝ) * (q : ℝ)) * ∑ p ∈ P_hi, (p : ℝ)⁻¹ ≤ ∑ m ∈ S_m, (1 : ℝ) / (m : ℝ) := by
    calc ((3 / 4 : ℝ) * (q : ℝ)) * ∑ p ∈ P_hi, (p : ℝ)⁻¹
        = ∑ p ∈ P_hi, ((3 / 4 : ℝ) * (q : ℝ)) * (p : ℝ)⁻¹ := Finset.mul_sum _ _ _
      _ ≤ ∑ p ∈ P_hi, (1 : ℝ) / (f p : ℝ) := Finset.sum_le_sum hterm_ge
      _ ≤ ∑ m ∈ S_m, (1 : ℝ) / (m : ℝ) := hsum_ge_img
  have hstep2 : (3 / 4 : ℝ) * Real.log (Real.log (Y : ℝ)) - (3 / 4 : ℝ) * (q : ℝ) * tailBd ≤
      ((3 / 4 : ℝ) * (q : ℝ)) * ∑ p ∈ P_hi, (p : ℝ)⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_left hP_hi_ge (by positivity : (0 : ℝ) ≤ (3 / 4 : ℝ) * (q : ℝ))
    have hrew : (3 / 4 : ℝ) * (q : ℝ) * ((1 / (q.totient : ℝ)) * Real.log (Real.log (Y : ℝ)) - tailBd) =
        (3 / 4 : ℝ) * ((q : ℝ) / (q.totient : ℝ)) * Real.log (Real.log (Y : ℝ)) -
          (3 / 4 : ℝ) * (q : ℝ) * tailBd := by ring
    rw [hrew] at hmul
    have hloglogY_nn : 0 ≤ Real.log (Real.log (Y : ℝ)) := Real.log_nonneg hlogY_ge_1
    have hge1 : (3 / 4 : ℝ) * Real.log (Real.log (Y : ℝ)) ≤
        (3 / 4 : ℝ) * ((q : ℝ) / (q.totient : ℝ)) * Real.log (Real.log (Y : ℝ)) := by
      have := mul_le_mul_of_nonneg_right hq_div_tot hloglogY_nn
      nlinarith
    linarith
  have htail_nn : 0 ≤ tailBd := by
    dsimp only [tailBd]
    have : 0 ≤ |M_qa| := abs_nonneg M_qa
    positivity
  have hq_nn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  linarith

/-! ## Section 3: Elementary Dyadic Partial Summation -/

/-- Harmonic sum upper bound: `∑_{k = 1}^{K} 1 / k ≤ Real.log K + 1` for `K ≥ 1`. -/
lemma harmonic_sum_le_log_add_one {K : ℕ} (hK : 1 ≤ K) :
    ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) ≤ Real.log (K : ℝ) + 1 := by
  induction K with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp)]
      have ihm := ih hm
      have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
        have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
        have hm1R : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
        rw [← Real.log_div hm1R.ne' hmR.ne']
        -- Use `1 - 1/x ≤ log x` at `x = (m+1)/m`, i.e. `1 - m/(m+1) = 1/(m+1) ≤ log((m+1)/m)`
        have h := Real.one_sub_inv_le_log_of_pos (div_pos hm1R hmR)
        have hsimp : 1 - (((m + 1 : ℕ) : ℝ) / (m : ℝ))⁻¹ = (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
          push_cast; field_simp [hmR.ne', (by positivity : (m : ℝ) + 1 ≠ 0)]; ring
        linarith
      linarith

/-- Dyadic partial summation: if `#{n ≤ x : P n} ≤ α * x / log x` for all `x ≥ X₀`,
then `∑_{2 ≤ n ≤ N, P n} 1/n ≤ 4 * α * log (log N) + (X₀ + 6 * α)` for all `N ≥ 4`. -/
theorem reciprocal_sum_le_of_count_bound (P : ℕ → Prop) [DecidablePred P]
    {α : ℝ} (hα : 0 ≤ α) {X₀ : ℕ} (hX₀ : 4 ≤ X₀)
    (hcnt : ∀ x : ℝ, (X₀ : ℝ) ≤ x →
      (((Finset.Icc 1 ⌊x⌋₊).filter P).card : ℝ) ≤ α * x / Real.log x) :
    ∀ N : ℕ, 4 ≤ N →
      ∑ n ∈ (Finset.Icc 2 N).filter P, (1 : ℝ) / (n : ℝ) ≤
        4 * α * Real.log (Real.log (N : ℝ)) + ((X₀ : ℝ) + 6 * α) := by
  intro N hN4
  set S : Finset ℕ := (Finset.Icc 2 N).filter P
  set S_lo : Finset ℕ := S.filter (fun n => n ≤ X₀)
  set S_hi : Finset ℕ := S.filter (fun n => ¬ n ≤ X₀)
  have hsplit : ∑ n ∈ S, (1 : ℝ) / (n : ℝ) =
      ∑ n ∈ S_lo, (1 : ℝ) / (n : ℝ) + ∑ n ∈ S_hi, (1 : ℝ) / (n : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not S (fun n => n ≤ X₀) _).symm
  -- Bound `S_lo` by `X₀`
  have hlo : ∑ n ∈ S_lo, (1 : ℝ) / (n : ℝ) ≤ (X₀ : ℝ) := by
    calc ∑ n ∈ S_lo, (1 : ℝ) / (n : ℝ)
        ≤ ∑ _n ∈ S_lo, (1 : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn2 : 2 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).1
          rw [one_div]
          exact inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ n))
      _ = (S_lo.card : ℝ) := by simp
      _ ≤ (X₀ : ℝ) := by
          have hsub : S_lo ⊆ Finset.Icc 1 X₀ := by
            intro n hn
            have h1 := Finset.mem_filter.mp hn
            have h2 := Finset.mem_Icc.mp (Finset.mem_filter.mp h1.1).1
            exact Finset.mem_Icc.mpr ⟨by omega, h1.2⟩
          exact_mod_cast (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
  -- Cover `S_hi` by dyadic blocks `B k = S_hi.filter (fun n => 2^k < n ∧ n ≤ 2^(k+1))`
  -- for `k ∈ Icc 1 K` where `K = Nat.log 2 N`
  set K : ℕ := Nat.log 2 N
  have hK1 : 1 ≤ K := by
    have : 2 ^ 1 ≤ N := by omega
    exact Nat.le_log_of_pow_le (by norm_num) this
  have hN_lt_pow : N < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hhi_cover : S_hi ⊆ (Finset.Icc 1 K).biUnion (fun k => S_hi.filter (fun n => 2 ^ k < n ∧ n ≤ 2 ^ (k + 1))) := by
    intro n hn
    have h1 := Finset.mem_filter.mp hn
    have h2 := Finset.mem_Icc.mp (Finset.mem_filter.mp h1.1).1
    have hn_gt_X : X₀ < n := by omega
    have hn_ge_4 : 4 ≤ n := by omega
    -- Choose `k = Nat.log 2 (n - 1)`
    set k := Nat.log 2 (n - 1)
    have hk1 : 1 ≤ k := Nat.le_log_of_pow_le (by norm_num) (by omega : 2 ^ 1 ≤ n - 1)
    have hkK : k ≤ K := Nat.log_mono_right (by omega)
    have hpow_le : 2 ^ k ≤ n - 1 := Nat.pow_log_le_self 2 (by omega)
    have hlt_pow : n - 1 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (n - 1)
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk1, hkK⟩,
      Finset.mem_filter.mpr ⟨hn, by omega, by omega⟩⟩
  have hhi_sum : ∑ n ∈ S_hi, (1 : ℝ) / (n : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 K, ∑ n ∈ S_hi.filter (fun n => 2 ^ k < n ∧ n ≤ 2 ^ (k + 1)), (1 : ℝ) / (n : ℝ) := by
    calc ∑ n ∈ S_hi, (1 : ℝ) / (n : ℝ)
        ≤ ∑ n ∈ (Finset.Icc 1 K).biUnion (fun k => S_hi.filter (fun n => 2 ^ k < n ∧ n ≤ 2 ^ (k + 1))),
            (1 : ℝ) / (n : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hhi_cover fun _ _ _ => by positivity
      _ ≤ ∑ k ∈ Finset.Icc 1 K, ∑ n ∈ S_hi.filter (fun n => 2 ^ k < n ∧ n ≤ 2 ^ (k + 1)),
            (1 : ℝ) / (n : ℝ) := by
          have hpair : (Finset.Icc 1 K : Set ℕ).PairwiseDisjoint
              (fun k => S_hi.filter (fun n => 2 ^ k < n ∧ n ≤ 2 ^ (k + 1))) := by
            intro k₁ _ k₂ _ hne
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro n hn₁ hn₂
            have h1 := (Finset.mem_filter.mp hn₁).2
            have h2 := (Finset.mem_filter.mp hn₂).2
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · have : 2 ^ (k₁ + 1) ≤ 2 ^ k₂ := Nat.pow_le_pow_right (by norm_num) (by omega)
              omega
            · have : 2 ^ (k₂ + 1) ≤ 2 ^ k₁ := Nat.pow_le_pow_right (by norm_num) (by omega)
              omega
          rw [Finset.sum_biUnion hpair]
  -- Bound each dyadic block `k` by `(2 / log 2) * α / (k + 1) ≤ 3 * α / k`
  have hlog2_ge : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hblock : ∀ k ∈ Finset.Icc 1 K,
      ∑ n ∈ S_hi.filter (fun n => 2 ^ k < n ∧ n ≤ 2 ^ (k + 1)), (1 : ℝ) / (n : ℝ) ≤
        3 * α * ((1 : ℝ) / (k : ℝ)) := by
    intro k hk
    set Bk := S_hi.filter (fun n => 2 ^ k < n ∧ n ≤ 2 ^ (k + 1))
    by_cases hne : Bk.Nonempty
    · obtain ⟨n₀, hn₀⟩ := hne
      have hn₀_hi := Finset.mem_filter.mp hn₀
      have hn₀_gtX : X₀ < n₀ := by
        have := (Finset.mem_filter.mp hn₀_hi.1).2; omega
      have hX_le_pow : (X₀ : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by
        exact_mod_cast (by omega : X₀ ≤ 2 ^ (k + 1))
      have hBk_sub : Bk ⊆ (Finset.Icc 1 (2 ^ (k + 1))).filter P := by
        intro n hn
        have h1 := Finset.mem_filter.mp hn
        have h2 := Finset.mem_filter.mp (Finset.mem_filter.mp h1.1).1
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, h1.2.2⟩, h2.2⟩
      have hcard_le : (Bk.card : ℝ) ≤ α * ((2 ^ (k + 1) : ℕ) : ℝ) / Real.log ((2 ^ (k + 1) : ℕ) : ℝ) := by
        have h1 : (Bk.card : ℝ) ≤ (((Finset.Icc 1 (2 ^ (k + 1))).filter P).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hBk_sub
        have h2 := hcnt ((2 ^ (k + 1) : ℕ) : ℝ) hX_le_pow
        rw [Nat.floor_natCast] at h2
        exact h1.trans h2
      have hpow_pos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
      have hsum_Bk : ∑ n ∈ Bk, (1 : ℝ) / (n : ℝ) ≤ (Bk.card : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
        calc ∑ n ∈ Bk, (1 : ℝ) / (n : ℝ)
            ≤ ∑ _n ∈ Bk, (1 : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
              refine Finset.sum_le_sum fun n hn => ?_
              have hgt : 2 ^ k < n := (Finset.mem_filter.mp hn).2.1
              exact one_div_le_one_div_of_le hpow_pos (by exact_mod_cast hgt.le)
          _ = (Bk.card : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      have hlog_pow : Real.log ((2 ^ (k + 1) : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      have h2pow : ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * ((2 ^ k : ℕ) : ℝ) := by
        rw [pow_succ]; push_cast; ring
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hk).1
      have hlog_pos : 0 < ((k + 1 : ℕ) : ℝ) * Real.log 2 := by positivity
      calc ∑ n ∈ Bk, (1 : ℝ) / (n : ℝ)
          ≤ (Bk.card : ℝ) / ((2 ^ k : ℕ) : ℝ) := hsum_Bk
        _ ≤ (α * ((2 ^ (k + 1) : ℕ) : ℝ) / Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) / ((2 ^ k : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right hcard_le hpow_pos.le
        _ = (2 * α) / (((k + 1 : ℕ) : ℝ) * Real.log 2) := by
            rw [hlog_pow, h2pow]; field_simp [hpow_pos.ne', hlog_pos.ne']
        _ ≤ (2 * α) / ((k : ℝ) * (2 / 3 : ℝ)) := by
            refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
            have hk1 : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
            exact mul_le_mul hk1 hlog2_ge (by positivity) (by positivity)
        _ = 3 * α * ((1 : ℝ) / (k : ℝ)) := by field_simp [hk_pos.ne']
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      positivity
  -- Sum over `k = 1..K` and relate `log K` to `log (log N)`
  have hsum_K : ∑ k ∈ Finset.Icc 1 K, 3 * α * ((1 : ℝ) / (k : ℝ)) ≤ 3 * α * (Real.log (K : ℝ) + 1) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (harmonic_sum_le_log_add_one hK1) (by positivity)
  -- Since `2^K ≤ N`, `K * log 2 ≤ log N`, so `K ≤ (3/2) * log N`, so `log K ≤ log (log N) + 1`.
  have hlogK_le : Real.log (K : ℝ) ≤ Real.log (Real.log (N : ℝ)) + 1 := by
    have h2K : ((2 ^ K : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have hKlog2 : (K : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ K : ℕ) : ℝ)) h2K
      rw [Nat.cast_pow, Real.log_pow] at h
      simpa using h
    have hK_le : (K : ℝ) ≤ 2 * Real.log (N : ℝ) := by
      have : (2 / 3 : ℝ) * (K : ℝ) ≤ (K : ℝ) * Real.log 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) K]
      linarith
    have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK1
    have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have h1 := Real.log_le_log hK_pos hK_le
    rw [Real.log_mul (by norm_num) hlogN_pos.ne'] at h1
    have hlog2_le_1 : Real.log 2 ≤ 1 := by
      have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2e
        _ = 1 := Real.log_exp 1
    linarith
  have hloglogN_nn : 0 ≤ Real.log (Real.log (N : ℝ)) := by
    apply Real.log_nonneg
    have h4 : Real.exp 1 ≤ (N : ℝ) := by
      have h1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have h4R : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (N : ℝ) := Real.log_le_log (Real.exp_pos 1) h4
  have hhi_final : ∑ n ∈ S_hi, (1 : ℝ) / (n : ℝ) ≤ 4 * α * Real.log (Real.log (N : ℝ)) + 6 * α := by
    have h1 : ∑ n ∈ S_hi, (1 : ℝ) / (n : ℝ) ≤ 3 * α * (Real.log (K : ℝ) + 1) :=
      hhi_sum.trans ((Finset.sum_le_sum hblock).trans hsum_K)
    nlinarith
  linarith

/-! ## Section 4: Sieve of Eratosthenes–Legendre & Bloom's Lemma 3 (`lem-nt3`) -/

/-- Exact Möbius indicator of `Nat.Coprime n P`:
`∑ d ∈ P.divisors, (if d ∣ n then (μ d : ℝ) else 0) = if Nat.Coprime n P then 1 else 0`. -/
lemma moebius_coprime_indicator (n P : ℕ) (hP : 0 < P) :
    ∑ d ∈ P.divisors, (if d ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) =
      if Nat.Coprime n P then 1 else 0 := by
  have hfilt : P.divisors.filter (fun d => d ∣ n) = (Nat.gcd n P).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdP, _⟩, hdn⟩
      exact ⟨Nat.dvd_gcd hdn hdP, (Nat.gcd_pos_of_pos_right n hP).ne'⟩
    · rintro ⟨hdg, _⟩
      exact ⟨⟨dvd_trans hdg (Nat.gcd_dvd_right n P), hP.ne'⟩,
        dvd_trans hdg (Nat.gcd_dvd_left n P)⟩
  rw [← Finset.sum_filter, hfilt]
  have hint : ∑ d ∈ (Nat.gcd n P).divisors, ArithmeticFunction.moebius d =
      if Nat.gcd n P = 1 then 1 else 0 := by
    have h := ArithmeticFunction.moebius_mul_coe_zeta
    have hval := congrFun (congrArg DFunLike.coe h) (Nat.gcd n P)
    simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, ArithmeticFunction.one_apply] at hval
    have hsum : ∑ x ∈ (Nat.gcd n P).divisorsAntidiagonal,
        ArithmeticFunction.moebius x.1 * (if x.2 = 0 then (0 : ℤ) else 1) =
        ∑ d ∈ (Nat.gcd n P).divisors, ArithmeticFunction.moebius d := by
      rw [Nat.sum_divisorsAntidiagonal (f := fun a b => ArithmeticFunction.moebius a * (if b = 0 then (0 : ℤ) else 1))]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd_dvd : d ∣ Nat.gcd n P := Nat.dvd_of_mem_divisors hd
      have hg_pos : 0 < Nat.gcd n P := Nat.gcd_pos_of_pos_right n hP
      have hd_le : d ≤ Nat.gcd n P := Nat.le_of_dvd hg_pos hd_dvd
      have hq_ne : Nat.gcd n P / d ≠ 0 := (Nat.div_pos hd_le (Nat.pos_of_mem_divisors hd)).ne'
      simp [hq_ne]
    rw [← hsum]
    simpa [Nat.cast_ite] using hval
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) hint
  push_cast at hcast
  simpa [Nat.Coprime] using hcast

/-- Multiplicative Euler product for `∑_{d ∣ P} μ(d) / φ(d)` when `P` is a product of a finset of primes `S`. -/
lemma sum_moebius_div_totient_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ d ∈ (∏ p ∈ S, p).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d.totient : ℝ) =
      ∏ p ∈ S, (1 - (1 : ℝ) / ((p : ℝ) - 1)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hpS ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    set Q := ∏ q ∈ S, q
    have hcop : Nat.Coprime p Q := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hqpr := hS' q hq
      exact (Nat.coprime_primes hp hqpr).mpr (fun heq => hpS (heq ▸ hq))
    rw [Finset.prod_insert hpS, Finset.prod_insert hpS]
    -- Divisors of `p * Q` split via `Nat.Coprime.divisors_mul` (or `mul_divisors_eq`)
    have hQpos : 0 < Q := Finset.prod_pos fun q hq => (hS' q hq).pos
    have hdiv_eq : (p * Q).divisors = Q.divisors ∪ Q.divisors.image (p * ·) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨hd, hne⟩
        by_cases hpd : p ∣ d
        · right
          obtain ⟨e, rfl⟩ := hpd
          refine ⟨e, ⟨?_, hQpos.ne'⟩, rfl⟩
          exact (mul_dvd_mul_iff_left hp.ne_zero).mp hd
        · left
          exact ⟨((hp.coprime_iff_not_dvd.mpr hpd).symm).dvd_of_dvd_mul_left hd, hQpos.ne'⟩
      · rintro (⟨hd, _⟩ | ⟨e, ⟨he, _⟩, rfl⟩)
        · exact ⟨dvd_mul_of_dvd_right hd p, (Nat.mul_pos hp.pos hQpos).ne'⟩
        · exact ⟨mul_dvd_mul_left p he, (Nat.mul_pos hp.pos hQpos).ne'⟩
    have hdisj : Disjoint Q.divisors (Q.divisors.image (p * ·)) := by
      rw [Finset.disjoint_left]
      intro d hd1 hd2
      obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hd2
      have hpd : p ∣ Q := dvd_trans (dvd_mul_right p e) (Nat.dvd_of_mem_divisors hd1)
      exact hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hpd)
    have hinj : Function.Injective (p * ·) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hp.pos h
    rw [hdiv_eq, Finset.sum_union hdisj, Finset.sum_image (fun _ _ _ _ h => hinj h)]
    have hshift : ∑ d ∈ Q.divisors, ((ArithmeticFunction.moebius (p * d) : ℤ) : ℝ) / ((p * d).totient : ℝ) =
        (-((1 : ℝ) / ((p : ℝ) - 1))) *
          ∑ d ∈ Q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d.totient : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdQ : d ∣ Q := Nat.dvd_of_mem_divisors hd
      have hcop_pd : Nat.Coprime p d := hcop.coprime_dvd_right hdQ
      have hmu : ArithmeticFunction.moebius (p * d) = -ArithmeticFunction.moebius d := by
        rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_pd,
          ArithmeticFunction.moebius_apply_prime hp]
        ring
      have htot : (p * d).totient = (p - 1) * d.totient := by
        rw [Nat.totient_mul hcop_pd, Nat.totient_prime hp]
      rw [hmu, htot]
      have hp1 : 1 ≤ p := hp.one_lt.le
      have htot_cast : (((p - 1) * d.totient : ℕ) : ℝ) = ((p : ℝ) - 1) * (d.totient : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_one]
      rw [htot_cast, Int.cast_neg]
      have hp_ne : (p : ℝ) - 1 ≠ 0 := by
        have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
        linarith
      have hdt_ne : (d.totient : ℝ) ≠ 0 :=
        (Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_mem_divisors hd))).ne'
      field_simp [hp_ne, hdt_ne]
    rw [hshift, ih hS']
    ring

/-- Upper bound `∫_2^x (1 / log t) dt ≤ 4 * x / log x` for `x ≥ 4`. -/
lemma li_le_four_mul_div_log {x : ℝ} (hx : 4 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / Real.log t ≤ 4 * x / Real.log x := by
  have hx0 : 0 < x := by linarith
  have hsq_ge : (2 : ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) hx0.le]; norm_num; linarith
  have hsq_le : Real.sqrt x ≤ x := by
    rw [Real.sqrt_le_left hx0.le]; nlinarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.uIcc 2 x) := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ x)] at ht
    have ht1 : 1 < t := by linarith [ht.1]
    exact ContinuousAt.continuousWithinAt
      (continuousAt_const.div (Real.continuousAt_log (by linarith)) (Real.log_pos ht1).ne')
  have hint1 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume 2 (Real.sqrt x) :=
    (hcont.mono (by rw [Set.uIcc_of_le hsq_ge, Set.uIcc_of_le (by linarith)]; intro t ht; exact ⟨ht.1, ht.2.trans hsq_le⟩)).intervalIntegrable
  have hint2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume (Real.sqrt x) x :=
    (hcont.mono (by rw [Set.uIcc_of_le hsq_le, Set.uIcc_of_le (by linarith)]; intro t ht; exact ⟨hsq_ge.trans ht.1, ht.2⟩)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  -- Part 1: `∫_2^{√x} 1 / log t ≤ (√x - 2) / log 2 ≤ 2 * √x`
  have hp1 : ∫ t in (2 : ℝ)..Real.sqrt x, 1 / Real.log t ≤ 2 * Real.sqrt x := by
    have hbd : ∀ t ∈ Set.Icc (2 : ℝ) (Real.sqrt x), 1 / Real.log t ≤ 2 := by
      intro t ht
      have h2 : (1 / 2 : ℝ) ≤ Real.log t := by
        have hlt := Real.log_le_log (by norm_num) ht.1
        have := Real.log_two_gt_d9
        linarith
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hle := intervalIntegral.integral_mono_on hsq_ge hint1 intervalIntegrable_const hbd
    rw [intervalIntegral.integral_const, smul_eq_mul] at hle
    linarith
  -- Part 2: `∫_{√x}^x 1 / log t ≤ x / (log x / 2) = 2 * x / log x`
  have hp2 : ∫ t in Real.sqrt x..x, 1 / Real.log t ≤ 2 * x / Real.log x := by
    have hlog_sq : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
    have hbd : ∀ t ∈ Set.Icc (Real.sqrt x) x, 1 / Real.log t ≤ 2 / Real.log x := by
      intro t ht
      have hge : Real.log x / 2 ≤ Real.log t := by
        rw [← hlog_sq]
        exact Real.log_le_log (by linarith) ht.1
      rw [div_le_div_iff₀ (by linarith) hlogx_pos]
      linarith
    have hle := intervalIntegral.integral_mono_on hsq_le hint2 intervalIntegrable_const hbd
    rw [intervalIntegral.integral_const, smul_eq_mul] at hle
    have hsub : (x - Real.sqrt x) * (2 / Real.log x) ≤ 2 * x / Real.log x := by
      have hnn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
      have : x - Real.sqrt x ≤ x := by linarith
      calc (x - Real.sqrt x) * (2 / Real.log x) ≤ x * (2 / Real.log x) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = 2 * x / Real.log x := by ring
    exact hle.trans hsub
  -- Combine: `2 * √x ≤ 2 * x / log x` since `log x ≤ √x` (from `log x ≤ 2 * x^(1/2)`? Wait: `log x ≤ x^(1/2)` for `x ≥ 4`!)
  have hsqrt_le : 2 * Real.sqrt x ≤ 2 * x / Real.log x := by
    -- `log x ≤ √x` since `log(√x) ≤ √x / 2`? Actually `log u ≤ u - 1` at `u = √x / 2` gives `log x = 2 log(√x) ≤ 2 * (√x / 2)`? No: `log t ≤ t / e < t / 2` so `2 log(√x) < √x`!
    have hlog_le_sq : Real.log x ≤ Real.sqrt x := by
      have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x / 2 := by
        have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < Real.sqrt x / 2)
        -- Actually `log(√x / 2) ≤ √x / 2 - 1 ⟹ log(√x) ≤ √x / 2 - (1 - log 2) ≤ √x / 2`!
        rw [Real.log_div (by positivity) (by norm_num)] at h
        have hlog2 : Real.log 2 ≤ 1 := by
          calc Real.log 2 ≤ Real.log (Real.exp 1) :=
                Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
            _ = 1 := Real.log_exp 1
        linarith
      rw [Real.log_sqrt hx0.le] at h1
      linarith
    rw [le_div_iff₀ hlogx_pos]
    calc 2 * Real.sqrt x * Real.log x ≤ 2 * Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_left hlog_le_sq (by positivity)
      _ = 2 * (Real.sqrt x * Real.sqrt x) := by ring
      _ = 2 * x := by rw [Real.mul_self_sqrt hx0.le]
  linarith [show 2 * x / Real.log x + 2 * x / Real.log x = 4 * x / Real.log x by ring]

/-- **Bloom's Lemma 3 (`lem-nt3`)**: There is an absolute constant `C > 0` such that for both signs
`plus : Bool` and every `4 ≤ y < z`, for all sufficiently large `N`:
`#{p ≤ N : p prime ∧ ∀ r ∈ [y, z], r prime → ¬ r ∣ shiftVal plus p} ≤ C * (log y / log z) * (N / log N)`. -/
theorem shifted_prime_no_prime_divisor_in_Icc :
    ∃ C : ℝ, 0 < C ∧ ∀ (plus : Bool) (y z : ℕ), 4 ≤ y → y < z →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
        (((Finset.Icc 1 N).filter (fun p =>
            p.Prime ∧ ∀ r ∈ Finset.Icc y z, r.Prime → ¬ r ∣ shiftVal plus p)).card : ℝ) ≤
          C * (Real.log (y : ℝ) / Real.log (z : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) := by
  -- Pull Mertens' third theorem quantitative constants first (uniform in `y, z`)
  obtain ⟨C₃, hC₃_pos, hM3⟩ := RHDirect.Stage8MertensTheorems.mertens_third_theorem_quant
  -- Pull Siegel–Walfisz constants
  obtain ⟨c_sw, hc_sw, hsw_all⟩ := RHDirect.Stage10SiegelWalfiszFull.siegel_walfisz_pi_real
  obtain ⟨C_sw, hC_sw, hsw⟩ := hsw_all 1 zero_lt_one
  -- From `mertens_third_theorem_quant`, we get a uniform `K₃ > 0` such that
  -- `∏_{r ∈ (Icc y z).filter Prime} (1 - 1/r) ≤ K₃ * (log y / log z)` for ALL `4 ≤ y < z`!
  -- Wait: for small `y` where `C₃ / log (y - 1) ≥ exp(-γ)/2`, the lower bound on `∏_{r ≤ y-1} (1-1/r)`
  -- is still positive (`≥ ∏_{r ≤ W₀} (1 - 1/r) > 0`), so there is a global `c_lo > 0` and `C_hi > 0` with
  -- `c_lo / log w ≤ ∏_{r ≤ w} (1 - 1/r) ≤ C_hi / log w` for ALL `w ≥ 3`!
  set eγ : ℝ := Real.exp (-Real.eulerMascheroniConstant)
  have heγ_pos : 0 < eγ := Real.exp_pos _
  -- Threshold `W₀ ≥ 4` such that `C₃ / log W₀ ≤ eγ / 2`
  set W₀ : ℕ := max 4 (⌈Real.exp (2 * C₃ / eγ)⌉₊ + 1)
  have hW₀_ge4 : 4 ≤ W₀ := le_max_left _ _
  -- Lower bound `c_lo_small` for `3 ≤ w ≤ W₀`: the minimum of `log w * ∏_{r ≤ w} (1 - 1/r)` is positive
  have hprod_pos : ∀ w : ℕ, 0 < ∏ r ∈ (Finset.Icc 1 w).filter Nat.Prime, (1 - (r : ℝ)⁻¹) := by
    intro w
    refine Finset.prod_pos fun r hr => ?_
    have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hr).2.two_le
    have : (r : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  set c_small : ℝ := Real.log 3 * ∏ r ∈ (Finset.Icc 1 W₀).filter Nat.Prime, (1 - (r : ℝ)⁻¹)
  have hc_small_pos : 0 < c_small := mul_pos (Real.log_pos (by norm_num)) (hprod_pos W₀)
  set c_lo : ℝ := min (eγ / 2) c_small
  have hc_lo_pos : 0 < c_lo := lt_min (by positivity) hc_small_pos
  set C_hi : ℝ := eγ + C₃ / Real.log 3
  have hC_hi_pos : 0 < C_hi := by positivity
  -- Prove uniform Mertens III upper and lower bounds for all `w : ℕ`, `3 ≤ w`
  have hM3_hi : ∀ w : ℕ, 3 ≤ w →
      ∏ r ∈ (Finset.Icc 1 w).filter Nat.Prime, (1 - (r : ℝ)⁻¹) ≤ C_hi / Real.log (w : ℝ) := by
    intro w hw
    have hwR : (3 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
    have hlogw : 0 < Real.log (w : ℝ) := Real.log_pos (by linarith)
    have hq := hM3 (w : ℝ) hwR
    rw [Nat.floor_natCast] at hq
    have h1 := (abs_le.mp hq).2
    have h2 : C₃ / Real.log (w : ℝ) ≤ C₃ / Real.log 3 :=
      div_le_div_of_nonneg_left hC₃_pos.le (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hwR)
    rw [le_div_iff₀ hlogw, mul_comm]
    dsimp only [C_hi, eγ]
    linarith
  have hM3_lo : ∀ w : ℕ, 3 ≤ w →
      c_lo / Real.log (w : ℝ) ≤ ∏ r ∈ (Finset.Icc 1 w).filter Nat.Prime, (1 - (r : ℝ)⁻¹) := by
    intro w hw
    have hwR : (3 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
    have hlogw : 0 < Real.log (w : ℝ) := Real.log_pos (by linarith)
    by_cases hbig : W₀ ≤ w
    · have hq := hM3 (w : ℝ) hwR
      rw [Nat.floor_natCast] at hq
      have h1 := (abs_le.mp hq).1
      have hlogW : 2 * C₃ / eγ < Real.log (w : ℝ) := by
        have hlt : Real.exp (2 * C₃ / eγ) < (W₀ : ℝ) := by
          have h1 : Real.exp (2 * C₃ / eγ) ≤ (⌈Real.exp (2 * C₃ / eγ)⌉₊ : ℝ) := Nat.le_ceil _
          have h2 : ⌈Real.exp (2 * C₃ / eγ)⌉₊ + 1 ≤ W₀ := le_max_right _ _
          have h3 : (⌈Real.exp (2 * C₃ / eγ)⌉₊ : ℝ) + 1 ≤ (W₀ : ℝ) := by exact_mod_cast h2
          linarith
        have hle : (W₀ : ℝ) ≤ (w : ℝ) := by exact_mod_cast hbig
        calc 2 * C₃ / eγ = Real.log (Real.exp (2 * C₃ / eγ)) := (Real.log_exp _).symm
          _ < Real.log (w : ℝ) := Real.log_lt_log (Real.exp_pos _) (lt_of_lt_of_le hlt hle)
      have hC3_le : C₃ / Real.log (w : ℝ) ≤ eγ / 2 := by
        rw [div_le_iff₀ hlogw]
        have hmul := mul_lt_mul_of_pos_left hlogW (by positivity : 0 < eγ / 2)
        have : eγ / 2 * (2 * C₃ / eγ) = C₃ := by field_simp [heγ_pos.ne']
        linarith
      rw [div_le_iff₀ hlogw, mul_comm]
      have hclo : c_lo ≤ eγ / 2 := min_le_left _ _
      dsimp only [eγ] at h1 hC3_le hclo ⊢
      linarith
    · have hw_le : w ≤ W₀ := by omega
      have hsub : (Finset.Icc 1 w).filter Nat.Prime ⊆ (Finset.Icc 1 W₀).filter Nat.Prime :=
        Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hw_le)
      have hprod_ge : ∏ r ∈ (Finset.Icc 1 W₀).filter Nat.Prime, (1 - (r : ℝ)⁻¹) ≤
          ∏ r ∈ (Finset.Icc 1 w).filter Nat.Prime, (1 - (r : ℝ)⁻¹) := by
        rw [← Finset.prod_sdiff hsub]
        have hsdiff_le1 : ∏ r ∈ ((Finset.Icc 1 W₀).filter Nat.Prime \ (Finset.Icc 1 w).filter Nat.Prime),
            (1 - (r : ℝ)⁻¹) ≤ 1 := by
          refine Finset.prod_le_one (fun r hr => ?_) (fun r hr => ?_)
          · have hr2 : (2 : ℝ) ≤ (r : ℝ) := by
              exact_mod_cast (Finset.mem_filter.mp (Finset.mem_sdiff.mp hr).1).2.two_le
            have : (r : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
              rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
            linarith
          · have : (0 : ℝ) ≤ (r : ℝ)⁻¹ := by positivity
            linarith
        calc (∏ r ∈ ((Finset.Icc 1 W₀).filter Nat.Prime \ (Finset.Icc 1 w).filter Nat.Prime),
                (1 - (r : ℝ)⁻¹)) *
              (∏ r ∈ (Finset.Icc 1 w).filter Nat.Prime, (1 - (r : ℝ)⁻¹))
            ≤ 1 * (∏ r ∈ (Finset.Icc 1 w).filter Nat.Prime, (1 - (r : ℝ)⁻¹)) :=
              mul_le_mul_of_nonneg_right hsdiff_le1 (hprod_pos w).le
          _ = ∏ r ∈ (Finset.Icc 1 w).filter Nat.Prime, (1 - (r : ℝ)⁻¹) := one_mul _
      have hlog_ge : Real.log 3 ≤ Real.log (w : ℝ) := Real.log_le_log (by norm_num) hwR
      rw [div_le_iff₀ hlogw, mul_comm]
      calc c_lo ≤ c_small := min_le_right _ _
        _ = Real.log 3 * ∏ r ∈ (Finset.Icc 1 W₀).filter Nat.Prime, (1 - (r : ℝ)⁻¹) := rfl
        _ ≤ Real.log (w : ℝ) * ∏ r ∈ (Finset.Icc 1 w).filter Nat.Prime, (1 - (r : ℝ)⁻¹) :=
            mul_le_mul hlog_ge hprod_ge (hprod_pos W₀).le hlogw.le
  -- Set our absolute constant `C := 4 * (C_hi / c_lo) + 1`
  refine ⟨4 * (C_hi / c_lo) + 1, by positivity, fun plus y z hy4 hyz => ?_⟩
  set S : Finset ℕ := (Finset.Icc y z).filter Nat.Prime
  set P : ℕ := ∏ r ∈ S, r
  have hS_pr : ∀ r ∈ S, r.Prime := fun r hr => (Finset.mem_filter.mp hr).2
  have hP_pos : 0 < P := Finset.prod_pos fun r hr => (hS_pr r hr).pos
  have hlog_yz_pos : 0 < Real.log (y : ℝ) / Real.log (z : ℝ) :=
    div_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < y)))
      (Real.log_pos (by exact_mod_cast (by omega : 1 < z)))
  -- Pick `N₀` large enough that:
  -- (1) `(P : ℝ) ≤ Real.log N₀`,
  -- (2) `(P.divisors.card : ℝ) * C_sw * exp (-c_sw * √(log N)) ≤ (log y / log z) / log N`
  have htend_err : Tendsto (fun N : ℕ =>
      (P.divisors.card : ℝ) * C_sw * Real.log (N : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (N : ℝ))))
      atTop (𝓝 0) := by
    -- `t^2 * exp(-c_sw * t) → 0` as `t = √(log N) → ∞`
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
    have ht3 := (ht1.comp ht2).const_mul ((P.divisors.card : ℝ) * C_sw)
    rw [mul_zero] at ht3
    refine ht3.congr' ?_
    filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN
    have hlog_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    dsimp only [Function.comp_apply]
    rw [Real.sq_sqrt hlog_nn]
    ring
  have hev_err := (tendsto_order.mp htend_err).2 (Real.log (y : ℝ) / Real.log (z : ℝ)) hlog_yz_pos
  obtain ⟨N₁, hN₁⟩ := hev_err.exists_forall_of_atTop
  have htend_log : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₂, hN₂⟩ := (tendsto_atTop.mp htend_log (P : ℝ)).exists_forall_of_atTop
  set N₀ : ℕ := max (max N₁ N₂) 4
  refine ⟨N₀, le_max_right _ _, fun N hN => ?_⟩
  have hN4 : 4 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN4R : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  -- Step 1: Express the sifted count using Möbius inversion over `d ∣ P`
  have hcop_iff : ∀ p : ℕ, (∀ r ∈ Finset.Icc y z, r.Prime → ¬ r ∣ shiftVal plus p) ↔
      Nat.Coprime (shiftVal plus p) P := by
    intro p
    constructor
    · intro hno
      refine Nat.Coprime.prod_right fun r hr => ?_
      have hrm := Finset.mem_filter.mp hr
      exact (hrm.2.coprime_iff_not_dvd.mpr (hno r hrm.1 hrm.2)).symm
    · intro hcop r hr hpr hdvd
      have hrm : r ∈ S := Finset.mem_filter.mpr ⟨hr, hpr⟩
      have hrP : r ∣ P := Finset.dvd_prod_of_mem _ hrm
      exact hpr.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hdvd hrP)
  set A := (Finset.Icc 1 N).filter Nat.Prime
  have hsift_eq :
      (((Finset.Icc 1 N).filter (fun p =>
          p.Prime ∧ ∀ r ∈ Finset.Icc y z, r.Prime → ¬ r ∣ shiftVal plus p)).card : ℝ) =
        ∑ d ∈ P.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          (RHDirect.Stage2DirichletAP.primeCountAP d (shiftRes plus d) (N : ℝ) : ℝ) := by
    have hfilt : (Finset.Icc 1 N).filter (fun p =>
        p.Prime ∧ ∀ r ∈ Finset.Icc y z, r.Prime → ¬ r ∣ shiftVal plus p) =
        A.filter (fun p => Nat.Coprime (shiftVal plus p) P) := by
      ext p; simp only [A, Finset.mem_filter, hcop_iff]; tauto
    rw [hfilt, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    have hlhs : ∑ p ∈ A, (if Nat.Coprime (shiftVal plus p) P then (1 : ℝ) else 0) =
        ∑ p ∈ A, ∑ d ∈ P.divisors, (if d ∣ shiftVal plus p then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun p _ => (moebius_coprime_indicator (shiftVal plus p) P hP_pos).symm
    rw [show (∑ p ∈ A, if Nat.Coprime (shiftVal plus p) P then ((1 : ℕ) : ℝ) else 0) =
        ∑ p ∈ A, (if Nat.Coprime (shiftVal plus p) P then (1 : ℝ) else 0) by
      refine Finset.sum_congr rfl fun p _ => by split_ifs <;> simp]
    rw [hlhs, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    rw [primeCountAP_eq_Icc_card]
    congr 1
    ext p
    simp only [A, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpI, hpr⟩, hdvd⟩
      exact ⟨hpI, hpr, (dvd_shiftVal_iff_modEq plus hd1 hpr.pos).mp hdvd⟩
    · rintro ⟨hpI, hpr, hmod⟩
      exact ⟨⟨hpI, hpr⟩, (dvd_shiftVal_iff_modEq plus hd1 hpr.pos).mpr hmod⟩
  -- Step 2: Apply Siegel–Walfisz to every `d ∣ P`
  set liN : ℝ := ∫ t in (2 : ℝ)..(N : ℝ), 1 / Real.log t
  have hli_nn : 0 ≤ liN := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    have : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    positivity
  have hsw_each : ∀ d ∈ P.divisors,
      |(RHDirect.Stage2DirichletAP.primeCountAP d (shiftRes plus d) (N : ℝ) : ℝ) - liN / (d.totient : ℝ)| ≤
        C_sw * (N : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (N : ℝ))) := by
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have : NeZero d := ⟨hdpos.ne'⟩
    have hdP : (d : ℝ) ≤ (Real.log (N : ℝ)) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
      exact le_trans (by exact_mod_cast Nat.le_of_dvd hP_pos (Nat.dvd_of_mem_divisors hd)) (hN₂ N hNN₂)
    exact hsw (N : ℝ) hN4R d hdP (shiftRes plus d) (shiftRes_coprime plus hdpos)
  -- Bound `∑ μ(d) * π(N; d, a)` by `liN * ∑ μ(d)/φ(d) + ∑ |R_d|`
  have hdecomp :
      ∑ d ∈ P.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (RHDirect.Stage2DirichletAP.primeCountAP d (shiftRes plus d) (N : ℝ) : ℝ) ≤
      liN * (∑ d ∈ P.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d.totient : ℝ)) +
        (P.divisors.card : ℝ) * (C_sw * (N : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (N : ℝ)))) := by
    have hsplit_sum :
        ∑ d ∈ P.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          (RHDirect.Stage2DirichletAP.primeCountAP d (shiftRes plus d) (N : ℝ) : ℝ) =
        liN * (∑ d ∈ P.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d.totient : ℝ)) +
        ∑ d ∈ P.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          ((RHDirect.Stage2DirichletAP.primeCountAP d (shiftRes plus d) (N : ℝ) : ℝ) - liN / (d.totient : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ => by ring
    rw [hsplit_sum]
    gcongr
    calc ∑ d ∈ P.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            ((RHDirect.Stage2DirichletAP.primeCountAP d (shiftRes plus d) (N : ℝ) : ℝ) - liN / (d.totient : ℝ))
        ≤ ∑ d ∈ P.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            ((RHDirect.Stage2DirichletAP.primeCountAP d (shiftRes plus d) (N : ℝ) : ℝ) - liN / (d.totient : ℝ))| :=
          Finset.sum_le_sum fun d _ => le_abs_self _
      _ ≤ ∑ _d ∈ P.divisors, (C_sw * (N : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (N : ℝ)))) := by
          refine Finset.sum_le_sum fun d hd => ?_
          rw [abs_mul]
          have hmu1 : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
            by_cases hsq : Squarefree d
            · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
              simp [abs_pow]
            · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
              simp
          calc |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
                |(RHDirect.Stage2DirichletAP.primeCountAP d (shiftRes plus d) (N : ℝ) : ℝ) - liN / (d.totient : ℝ)|
              ≤ 1 * (C_sw * (N : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (N : ℝ)))) :=
                mul_le_mul hmu1 (hsw_each d hd) (abs_nonneg _) zero_le_one
            _ = C_sw * (N : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (N : ℝ))) := one_mul _
      _ = (P.divisors.card : ℝ) * (C_sw * (N : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (N : ℝ)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Step 3: Bound the Euler product `∏_{r ∈ S} (1 - 1/(r-1)) ≤ (C_hi / c_lo) * (log y / log z)`
  have hprod_le : ∏ r ∈ S, (1 - (1 : ℝ) / ((r : ℝ) - 1)) ≤
      (C_hi / c_lo) * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
    have h1 : ∏ r ∈ S, (1 - (1 : ℝ) / ((r : ℝ) - 1)) ≤ ∏ r ∈ S, (1 - (r : ℝ)⁻¹) := by
      refine Finset.prod_le_prod (fun r hr => ?_) (fun r hr => ?_)
      · have hr4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast le_trans hy4 (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
        have : (1 : ℝ) / ((r : ℝ) - 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
        linarith
      · have hr4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast le_trans hy4 (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
        have : (r : ℝ)⁻¹ ≤ (1 : ℝ) / ((r : ℝ) - 1) := by
          rw [one_div]; exact inv_anti₀ (by linarith) (by linarith)
        linarith
    -- Relate `S = (Icc 1 z).filter Prime \ (Icc 1 (y-1)).filter Prime`
    have hS_sub : (Finset.Icc 1 (y - 1)).filter Nat.Prime ⊆ (Finset.Icc 1 z).filter Nat.Prime :=
      Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right (by omega))
    have hS_eq : S = (Finset.Icc 1 z).filter Nat.Prime \ (Finset.Icc 1 (y - 1)).filter Nat.Prime := by
      ext r
      simp only [S, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, hpr⟩; exact ⟨⟨⟨by omega, h2⟩, hpr⟩, fun ⟨⟨_, h3⟩, _⟩ => by omega⟩
      · rintro ⟨⟨⟨_, h2⟩, hpr⟩, hnot⟩
        refine ⟨⟨?_, h2⟩, hpr⟩
        by_contra hlt
        exact hnot ⟨⟨hpr.pos, by omega⟩, hpr⟩
    have hprod_eq : ∏ r ∈ S, (1 - (r : ℝ)⁻¹) =
        (∏ r ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 - (r : ℝ)⁻¹)) /
        (∏ r ∈ (Finset.Icc 1 (y - 1)).filter Nat.Prime, (1 - (r : ℝ)⁻¹)) := by
      rw [hS_eq, eq_div_iff (hprod_pos (y - 1)).ne', Finset.prod_sdiff hS_sub]
    rw [hprod_eq] at h1
    have hhi_z := hM3_hi z (by omega)
    have hlo_y := hM3_lo (y - 1) (by omega)
    have hlogy1_le : Real.log ((y - 1 : ℕ) : ℝ) ≤ Real.log (y : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < y - 1)) (by exact_mod_cast (by omega : y - 1 ≤ y))
    have hlo_y' : c_lo / Real.log (y : ℝ) ≤ ∏ r ∈ (Finset.Icc 1 (y - 1)).filter Nat.Prime, (1 - (r : ℝ)⁻¹) := by
      refine le_trans ?_ hlo_y
      exact div_le_div_of_nonneg_left hc_lo_pos.le
        (Real.log_pos (by exact_mod_cast (by omega : 1 < y - 1))) hlogy1_le
    have hdiv_le : (∏ r ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 - (r : ℝ)⁻¹)) /
        (∏ r ∈ (Finset.Icc 1 (y - 1)).filter Nat.Prime, (1 - (r : ℝ)⁻¹)) ≤
        (C_hi / Real.log (z : ℝ)) / (c_lo / Real.log (y : ℝ)) :=
      div_le_div₀ (by positivity) hhi_z (div_pos hc_lo_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < y)))) hlo_y'
    have hrew : (C_hi / Real.log (z : ℝ)) / (c_lo / Real.log (y : ℝ)) =
        (C_hi / c_lo) * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
      have hz0 : Real.log (z : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < z))).ne'
      have hy0 : Real.log (y : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < y))).ne'
      field_simp [hz0, hy0, hc_lo_pos.ne']
    exact h1.trans (hrew ▸ hdiv_le)
  -- Step 4: Combine everything!
  have hmain_le : liN * (∑ d ∈ P.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d.totient : ℝ)) ≤
      4 * (C_hi / c_lo) * (Real.log (y : ℝ) / Real.log (z : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) := by
    rw [sum_moebius_div_totient_prod_primes S hS_pr]
    have hli_bd := li_le_four_mul_div_log hN4R
    have hprod_nn : 0 ≤ ∏ r ∈ S, (1 - (1 : ℝ) / ((r : ℝ) - 1)) := by
      refine Finset.prod_nonneg fun r hr => ?_
      have hr4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast le_trans hy4 (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
      have : (1 : ℝ) / ((r : ℝ) - 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
      linarith
    calc liN * ∏ r ∈ S, (1 - (1 : ℝ) / ((r : ℝ) - 1))
        ≤ (4 * (N : ℝ) / Real.log (N : ℝ)) * ((C_hi / c_lo) * (Real.log (y : ℝ) / Real.log (z : ℝ))) :=
          mul_le_mul hli_bd hprod_le hprod_nn (by positivity)
      _ = 4 * (C_hi / c_lo) * (Real.log (y : ℝ) / Real.log (z : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) := by ring
  have herr_le : (P.divisors.card : ℝ) * (C_sw * (N : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (N : ℝ)))) ≤
      (Real.log (y : ℝ) / Real.log (z : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) := by
    have h1 := (hN₁ N hNN₁).le
    rw [mul_div_assoc', le_div_iff₀ hlogN_pos]
    calc (P.divisors.card : ℝ) * (C_sw * (N : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (N : ℝ)))) *
            Real.log (N : ℝ)
        = ((P.divisors.card : ℝ) * C_sw * Real.log (N : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (N : ℝ)))) *
            (N : ℝ) := by ring
      _ ≤ (Real.log (y : ℝ) / Real.log (z : ℝ)) * (N : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg N)
  rw [hsift_eq]
  calc ∑ d ∈ P.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          (RHDirect.Stage2DirichletAP.primeCountAP d (shiftRes plus d) (N : ℝ) : ℝ)
      ≤ liN * (∑ d ∈ P.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d.totient : ℝ)) +
          (P.divisors.card : ℝ) * (C_sw * (N : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (N : ℝ)))) := hdecomp
    _ ≤ 4 * (C_hi / c_lo) * (Real.log (y : ℝ) / Real.log (z : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) +
          (Real.log (y : ℝ) / Real.log (z : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) := add_le_add hmain_le herr_le
    _ = (4 * (C_hi / c_lo) + 1) * (Real.log (y : ℝ) / Real.log (z : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) := by ring

end PPL024
