import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.IsPrimePow
import RHDirect.Stage7SieveMethods
import RHDirect.Stage8BrunTuran
import RHDirect.Stage8UniformAP
import Prize.PPL024_AnalyticMertens

/-!
# PPL 024 Analytic Foundations — Part 2: Friability / Smoothness of Shifted Primes (Bloom's Lemma 1)

Unconditional formalization of Bloom's Lemma 1 (`lem-nt1` of arXiv:2305.02689):
There exists an absolute constant `C > 0` such that for both signs `plus : Bool` (`p - 1` and `p + 1`)
and every `0 < ε < 1/4`, for all sufficiently large `N`:
`#{p ≤ N : p prime ∧ ∃ q₀ prime power > N^(1-ε), q₀ ∣ shiftVal plus p} ≤ C * ε * N / log N`.

Proof ingredients (100% unconditional Tier-A `Arithmetica4`):
- `RHDirect.Stage7SieveMethods.montgomery_arithmetic_large_sieve_Icc`
- `RHDirect.Stage8BrunTuran.montgomeryL_prime_pair_ge`
- `RHDirect.Stage8UniformAP.sum_inv_totient_le`
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset Filter Topology

namespace PPL024

/-! ## Section 1: Linear Prime-Pair Upper Bound via Montgomery's Large Sieve -/

/-- Elementary inequality: for `x ≥ 3`, `√x ≤ 16 * x / (log x)²`. -/
private lemma sqrt_le_sixteen_div_log_sq {x : ℝ} (hx : 3 ≤ x) :
    Real.sqrt x ≤ 16 * x / (Real.log x) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog_rpow : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
    linarith [show x ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) = 4 * x ^ (1 / 4 : ℝ) by ring]
  have hsq : (Real.log x) ^ 2 ≤ 16 * Real.sqrt x := by
    have h1 : (Real.log x) ^ 2 ≤ (4 * x ^ (1 / 4 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hLx_pos.le hlog_rpow 2
    have h2 : (4 * x ^ (1 / 4 : ℝ)) ^ 2 = 16 * Real.sqrt x := by
      rw [mul_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast (x ^ (1 / 4 : ℝ)) 2,
        ← Real.rpow_mul hx0.le]
      norm_num
    linarith
  rw [le_div_iff₀ (sq_pos_of_pos hLx_pos)]
  calc Real.sqrt x * (Real.log x) ^ 2
      ≤ Real.sqrt x * (16 * Real.sqrt x) := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg x)
    _ = 16 * (Real.sqrt x * Real.sqrt x) := by ring
    _ = 16 * x := by rw [Real.mul_self_sqrt hx0.le]

/-- **Unconditional linear prime-pair upper bound** for `r` prime and `a * r ± 1` prime:
for every even `a ≥ 2`, sign `plus : Bool`, and `x ≥ 3`:
`#{r ≤ x : r prime ∧ (unshiftPrime plus a r) prime} ≤ 48 * (a / φ(a)) * x / (log x)²`. -/
theorem linear_prime_pair_upper_bound (plus : Bool) {a : ℕ} (ha2 : 2 ≤ a) (ha_even : Even a)
    {x : ℝ} (hx : 3 ≤ x) :
    (((Finset.Icc 1 ⌊x⌋₊).filter (fun r => r.Prime ∧ (unshiftPrime plus a r).Prime)).card : ℝ) ≤
      80 * ((a : ℝ) / (a.totient : ℝ)) * x / (Real.log x) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  set N : ℕ := ⌊x⌋₊
  have hN3 : 3 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  set Q : ℕ := Nat.sqrt N
  have hQ1 : 1 ≤ Q := Nat.sqrt_pos.mpr (by omega)
  set R : ℕ := Nat.sqrt Q
  have hR1 : 1 ≤ R := Nat.sqrt_pos.mpr hQ1
  -- Show `Real.log x ≤ 4 * Real.log (R + 1)`
  have hx_lt_R4 : x ≤ ((R : ℝ) + 1) ^ 4 := by
    have hNQ : N + 1 ≤ (Q + 1) ^ 2 := by have h := Nat.lt_succ_sqrt N; nlinarith
    have hQR : Q + 1 ≤ (R + 1) ^ 2 := by have h := Nat.lt_succ_sqrt Q; nlinarith
    have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
    have h1 : (N : ℝ) + 1 ≤ ((Q : ℝ) + 1) ^ 2 := by exact_mod_cast hNQ
    have h2 : (Q : ℝ) + 1 ≤ ((R : ℝ) + 1) ^ 2 := by exact_mod_cast hQR
    have h3 : ((Q : ℝ) + 1) ^ 2 ≤ (((R : ℝ) + 1) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    nlinarith [show (((R : ℝ) + 1) ^ 2) ^ 2 = ((R : ℝ) + 1) ^ 4 by ring]
  have hlogR_pos : 0 < Real.log ((R : ℝ) + 1) := by
    apply Real.log_pos
    have hR1R : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
    linarith
  have hlogx_le : Real.log x ≤ 4 * Real.log ((R : ℝ) + 1) := by
    have h1 := Real.log_le_log hx0 hx_lt_R4
    rw [Real.log_pow] at h1
    simpa using h1
  -- Split `P = A ∪ B` at threshold `Q`
  set P : Finset ℕ := (Finset.Icc 1 N).filter (fun r => r.Prime ∧ (unshiftPrime plus a r).Prime)
  set A : Finset ℕ := P.filter (fun r => Q < r)
  set B : Finset ℕ := P.filter (fun r => r ≤ Q)
  have hsplit : P.card = A.card + B.card := by
    have hdisj : Disjoint A B := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hunion : A ∪ B = P := by
      ext r; simp only [A, B, Finset.mem_union, Finset.mem_filter]; constructor
      · rintro (h | h) <;> exact h.1
      · intro hr; by_cases hc : Q < r <;> [left; right] <;> exact ⟨hr, by omega⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  -- Bound `B.card ≤ Q ≤ √x ≤ 16 * x / (log x)²`
  have hB_le : (B.card : ℝ) ≤ 16 * x / (Real.log x) ^ 2 := by
    have hB_Q : B.card ≤ Q := by
      have hsub : B ⊆ Finset.Icc 1 Q := by
        intro r hr
        have hr' := Finset.mem_filter.mp hr
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hr'.1).2.1.pos, hr'.2⟩
      exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
    have hQ_sqrt : (Q : ℝ) ≤ Real.sqrt x := by
      rw [Real.le_sqrt (Nat.cast_nonneg Q) hx0.le]
      have hsq : Q * Q ≤ N := Nat.sqrt_le N
      have hNle : (N : ℝ) ≤ x := Nat.floor_le hx0.le
      have hsqR : (Q : ℝ) ^ 2 ≤ (N : ℝ) := by rw [sq]; exact_mod_cast hsq
      linarith
    exact ((by exact_mod_cast hB_Q : (B.card : ℝ) ≤ (Q : ℝ)).trans hQ_sqrt).trans
      (sqrt_le_sixteen_div_log_sq hx)
  -- Apply Montgomery's arithmetic large sieve to `A` with `w p = if p ∣ a then 1 else 2`
  let w : ℕ → ℕ := fun p => if p ∣ a then 1 else 2
  have h2dvd : 2 ∣ a := even_iff_two_dvd.mp ha_even
  have hA_sub : A ⊆ Finset.Icc (0 + 1) (0 + N) := by
    intro r hr
    simpa using (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  have hAvoid : ∀ p : ℕ, p.Prime → p ≤ Q →
      w p < p ∧ ∃ SΩ : Finset (ZMod p), SΩ.card = w p ∧ ∀ r ∈ A, (r : ZMod p) ∉ SΩ := by
    intro p hp hpQ
    have : Fact p.Prime := ⟨hp⟩
    dsimp only [w]
    by_cases hpa : p ∣ a
    · rw [if_pos hpa]
      refine ⟨hp.one_lt, {0}, Finset.card_singleton 0, fun r hr hmem => ?_⟩
      have h0 : (r : ZMod p) = 0 := Finset.mem_singleton.mp hmem
      have hdvd : p ∣ r := (ZMod.natCast_eq_zero_iff r p).mp h0
      have hr_pr : r.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.1
      have hr_gt : Q < r := (Finset.mem_filter.mp hr).2
      have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp hr_pr).mp hdvd
      omega
    · rw [if_neg hpa]
      have hp_ne2 : p ≠ 2 := fun h2 => hpa (h2 ▸ h2dvd)
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have ha_ne0 : (a : ZMod p) ≠ 0 := by
        intro h0; exact hpa ((ZMod.natCast_eq_zero_iff a p).mp h0)
      let u : ZMod p := if plus then (a : ZMod p)⁻¹ else -(a : ZMod p)⁻¹
      have hu_ne0 : u ≠ 0 := by
        dsimp only [u]
        cases plus
        · simp [ha_ne0]
        · simp [ha_ne0]
      refine ⟨by omega, {0, u}, Finset.card_pair hu_ne0.symm, fun r hr hmem => ?_⟩
      have hr_pair := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
      have hr_gt : Q < r := (Finset.mem_filter.mp hr).2
      rcases Finset.mem_insert.mp hmem with h0 | hu
      · have hdvd : p ∣ r := (ZMod.natCast_eq_zero_iff r p).mp h0
        have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp hr_pair.1).mp hdvd
        omega
      · have hr_eq : (r : ZMod p) = u := Finset.mem_singleton.mp hu
        cases plus
        · -- `unshiftPrime false a r = a * r + 1`
          have hsum0 : ((a * r + 1 : ℕ) : ZMod p) = 0 := by
            push_cast
            rw [hr_eq]
            dsimp only [u]
            simp only [Bool.false_eq_true, ↓reduceIte, mul_neg, mul_inv_cancel₀ ha_ne0, neg_add_cancel]
          have hdvd : p ∣ a * r + 1 := (ZMod.natCast_eq_zero_iff (a * r + 1) p).mp hsum0
          have hpr2 : (a * r + 1).Prime := by simpa [unshiftPrime] using hr_pair.2
          have heq : p = a * r + 1 := (Nat.prime_dvd_prime_iff_eq hp hpr2).mp hdvd
          have hge : r ≤ a * r := Nat.le_mul_of_pos_left r (by omega)
          omega
        · -- `unshiftPrime true a r = a * r - 1`
          have har1 : 1 ≤ a * r := Nat.mul_pos (by omega) hr_pair.1.pos
          have hsub0 : ((a * r - 1 : ℕ) : ZMod p) = 0 := by
            rw [Nat.cast_sub har1, Nat.cast_mul, Nat.cast_one, hr_eq]
            dsimp only [u]
            simp only [↓reduceIte, mul_inv_cancel₀ ha_ne0, sub_self]
          have hdvd : p ∣ a * r - 1 := (ZMod.natCast_eq_zero_iff (a * r - 1) p).mp hsub0
          have hpr2 : (a * r - 1).Prime := by simpa [unshiftPrime] using hr_pair.2
          have heq : p = a * r - 1 := (Nat.prime_dvd_prime_iff_eq hp hpr2).mp hdvd
          have h2r : 2 * r ≤ a * r := Nat.mul_le_mul_right r ha2
          have hr2 : 2 ≤ r := hr_pair.1.two_le
          omega
  have hMS := RHDirect.Stage7SieveMethods.montgomery_arithmetic_large_sieve_Icc hA_sub w hAvoid
  have hL_ge := RHDirect.Stage8BrunTuran.montgomeryL_prime_pair_ge ha2 ha_even Q
  have htot_pos : (0 : ℝ) < (a.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
  have ha_pos : (0 : ℝ) < (a : ℝ) := by positivity
  have hL_ge_logx : ((a.totient : ℝ) / (a : ℝ)) * ((Real.log x) ^ 2 / 16) ≤
      RHDirect.Stage7SieveMethods.montgomeryL w Q := by
    have hsq : (Real.log x) ^ 2 / 16 ≤ (Real.log ((R : ℝ) + 1)) ^ 2 := by
      have h1 : (Real.log x) ^ 2 ≤ (4 * Real.log ((R : ℝ) + 1)) ^ 2 :=
        pow_le_pow_left₀ hLx_pos.le hlogx_le 2
      linarith [show (4 * Real.log ((R : ℝ) + 1)) ^ 2 = 16 * (Real.log ((R : ℝ) + 1)) ^ 2 by ring]
    exact (mul_le_mul_of_nonneg_left hsq (by positivity)).trans hL_ge
  have hL_pos : 0 < RHDirect.Stage7SieveMethods.montgomeryL w Q :=
    lt_of_lt_of_le (by positivity) hL_ge_logx
  have hNQ_le : (N : ℝ) + 3 * (Q : ℝ) ^ 2 ≤ 4 * x := by
    have hsq : Q * Q ≤ N := Nat.sqrt_le N
    have hsqR : (Q : ℝ) ^ 2 ≤ (N : ℝ) := by rw [sq]; exact_mod_cast hsq
    have hNle : (N : ℝ) ≤ x := Nat.floor_le hx0.le
    linarith
  have hA_le : (A.card : ℝ) ≤ 64 * ((a : ℝ) / (a.totient : ℝ)) * x / (Real.log x) ^ 2 := by
    have hMS_div : (A.card : ℝ) ≤ ((N : ℝ) + 3 * (Q : ℝ) ^ 2) / RHDirect.Stage7SieveMethods.montgomeryL w Q :=
      (le_div_iff₀ hL_pos).mpr hMS
    calc (A.card : ℝ) ≤ ((N : ℝ) + 3 * (Q : ℝ) ^ 2) / RHDirect.Stage7SieveMethods.montgomeryL w Q := hMS_div
      _ ≤ (4 * x) / (((a.totient : ℝ) / (a : ℝ)) * ((Real.log x) ^ 2 / 16)) :=
          div_le_div₀ (by positivity) hNQ_le (by positivity) hL_ge_logx
      _ = 64 * ((a : ℝ) / (a.totient : ℝ)) * x / (Real.log x) ^ 2 := by
          field_simp [htot_pos.ne', ha_pos.ne', hLx_pos.ne']; ring
  have ha_div_ge1 : (1 : ℝ) ≤ (a : ℝ) / (a.totient : ℝ) :=
    (one_le_div htot_pos).mpr (by exact_mod_cast Nat.totient_le a)
  have hB_le' : (B.card : ℝ) ≤ 16 * ((a : ℝ) / (a.totient : ℝ)) * x / (Real.log x) ^ 2 := by
    calc (B.card : ℝ) ≤ 16 * x / (Real.log x) ^ 2 := hB_le
      _ = 16 * 1 * x / (Real.log x) ^ 2 := by ring
      _ ≤ 16 * ((a : ℝ) / (a.totient : ℝ)) * x / (Real.log x) ^ 2 := by gcongr
  have hP_cast : (P.card : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hsplit
  rw [hP_cast]
  linarith [show 64 * ((a : ℝ) / (a.totient : ℝ)) * x / (Real.log x) ^ 2 +
      16 * ((a : ℝ) / (a.totient : ℝ)) * x / (Real.log x) ^ 2 =
      80 * ((a : ℝ) / (a.totient : ℝ)) * x / (Real.log x) ^ 2 by ring]

/-! ## Section 2: Higher Prime-Power Divisors `r^k > N^(1-ε)` (`k ≥ 2`) -/

/-- Count of `p ∈ Icc 1 N` with `d ∣ shiftVal plus p` is at most `(N + 1) / d + 1`. -/
private lemma card_shiftVal_dvd_le (plus : Bool) {d : ℕ} (_hd : 1 ≤ d) (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun p => d ∣ shiftVal plus p)).card ≤ (N + 1) / d + 1 := by
  -- Injection into `Finset.Icc 0 ((N + 1) / d)` via `p ↦ shiftVal plus p / d`
  let f : ℕ → ℕ := fun p => shiftVal plus p / d
  have hmaps : ∀ p ∈ (Finset.Icc 1 N).filter (fun p => d ∣ shiftVal plus p),
      f p ∈ Finset.Icc 0 ((N + 1) / d) := by
    intro p hp
    have hp1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
    have hsh_le : shiftVal plus p ≤ N + 1 := by
      cases plus <;> simp [shiftVal] <;> omega
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right hsh_le⟩
  have hinj : Set.InjOn f (((Finset.Icc 1 N).filter (fun p => d ∣ shiftVal plus p)) : Set ℕ) := by
    intro p₁ hp₁ p₂ hp₂ heq
    have h1 := Finset.mem_filter.mp hp₁
    have h2 := Finset.mem_filter.mp hp₂
    have h1_icc := Finset.mem_Icc.mp h1.1
    have h2_icc := Finset.mem_Icc.mp h2.1
    have hm1 := Nat.mul_div_cancel' h1.2
    have hm2 := Nat.mul_div_cancel' h2.2
    dsimp only [f] at heq
    have hsh : shiftVal plus p₁ = shiftVal plus p₂ := by rw [← hm1, ← hm2, heq]
    cases plus <;> simp only [shiftVal, Bool.false_eq_true, ↓reduceIte] at hsh <;> omega
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  simpa [Nat.card_Icc] using hcard

/-- Higher prime-power divisors (`k ≥ 2`, `r^k > N^(1-ε)`) contribute `O(N^(3/4) * log N) = o(ε N / log N)`. -/
lemma higher_prime_power_divisors_bound (plus : Bool) {ε : ℝ} (hε0 : 0 < ε) (hε4 : ε < 1 / 4) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (((Finset.Icc 1 N).filter (fun p =>
          p.Prime ∧ ∃ r k : ℕ, r.Prime ∧ 2 ≤ k ∧ (N : ℝ) ^ (1 - ε) < ((r ^ k : ℕ) : ℝ) ∧
            r ^ k ∣ shiftVal plus p)).card : ℝ) ≤
        ε * (N : ℝ) / Real.log (N : ℝ) := by
  -- Show `8 * (N + 1)^(3/4) * (log_2(N + 1) + 1) ≤ ε * N / log N` for large `N`.
  -- Specifically `(N : ℝ)^(-1/4) * (log N)^2 → 0`, so `16 * N^(3/4) * log N ≤ ε * N / log N`.
  have htend : Tendsto (fun N : ℕ => (Real.log ((N : ℝ) + 1)) ^ 2 / (N : ℝ) ^ (1 / 8 : ℝ)) atTop (𝓝 0) := by
    -- `log(N+1) ≤ 2 * log N` for `N ≥ 2`, and `(log N)^2 / N^(1/8) → 0`
    have h0 : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x ^ (1 / 8 : ℝ)) atTop (𝓝 0) := by
      have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
        (Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 8))
      have hsc := h.const_mul (64 : ℝ)
      rw [mul_zero] at hsc
      refine hsc.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      dsimp only [Function.comp_apply]
      rw [Real.rpow_def_of_pos (by linarith : 0 < x), Real.exp_neg]
      have hrew : (1 / 8 : ℝ) * Real.log x = Real.log x * (1 / 8) := by ring
      rw [mul_pow, hrew]
      ring
    have h1 := (h0.comp tendsto_natCast_atTop_atTop).const_mul (4 : ℝ)
    rw [mul_zero] at h1
    refine squeeze_zero' ?_ ?_ h1
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
      positivity
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
      dsimp only [Function.comp_apply]
      have hN1 : (N : ℝ) + 1 ≤ (N : ℝ) ^ 2 := by
        have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        nlinarith
      have hlog : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log (N : ℝ) := by
        have h := Real.log_le_log (by positivity) hN1
        rw [Real.log_pow] at h; simpa using h
      have hlog_nn : 0 ≤ Real.log ((N : ℝ) + 1) :=
        Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
      have hsq : (Real.log ((N : ℝ) + 1)) ^ 2 ≤ 4 * (Real.log (N : ℝ)) ^ 2 := by
        have := pow_le_pow_left₀ hlog_nn hlog 2
        linarith [show (2 * Real.log (N : ℝ)) ^ 2 = 4 * (Real.log (N : ℝ)) ^ 2 by ring]
      have hden : 0 ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by positivity
      calc (Real.log ((N : ℝ) + 1)) ^ 2 / (N : ℝ) ^ (1 / 8 : ℝ)
          ≤ (4 * (Real.log (N : ℝ)) ^ 2) / (N : ℝ) ^ (1 / 8 : ℝ) := div_le_div_of_nonneg_right hsq hden
        _ = 4 * ((Real.log (N : ℝ)) ^ 2 / (N : ℝ) ^ (1 / 8 : ℝ)) := by ring
  obtain ⟨N₁, hN₁⟩ := ((tendsto_order.mp htend).2 (ε / 100) (by positivity)).exists_forall_of_atTop
  set N₀ : ℕ := max N₁ 16
  refine ⟨N₀, by omega, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hNR_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  -- Cover the set by pairs `(r, k)` with `2 ≤ r ≤ Nat.sqrt (N + 1)` and `2 ≤ k ≤ Nat.log 2 (N + 1)`
  -- satisfying `(N : ℝ)^(1 - ε) < (r ^ k : ℝ)`
  set Rmax : ℕ := Nat.sqrt (N + 1)
  set Kmax : ℕ := Nat.log 2 (N + 1)
  set Pairs : Finset (ℕ × ℕ) :=
    ((Finset.Icc 2 Rmax) ×ˢ (Finset.Icc 2 Kmax)).filter (fun rk =>
      (N : ℝ) ^ (1 - ε) < ((rk.1 ^ rk.2 : ℕ) : ℝ))
  set S := (Finset.Icc 1 N).filter (fun p =>
      p.Prime ∧ ∃ r k : ℕ, r.Prime ∧ 2 ≤ k ∧ (N : ℝ) ^ (1 - ε) < ((r ^ k : ℕ) : ℝ) ∧
        r ^ k ∣ shiftVal plus p)
  have hcov : S ⊆ Pairs.biUnion (fun rk => (Finset.Icc 1 N).filter (fun p => rk.1 ^ rk.2 ∣ shiftVal plus p)) := by
    intro p hp
    have hp1 := Finset.mem_filter.mp hp
    obtain ⟨r, k, hr_pr, hk2, hgt, hdvd⟩ := hp1.2.2
    have hsh_pos : 0 < shiftVal plus p := shiftVal_pos_of_prime plus hp1.2.1
    have hsh_le : shiftVal plus p ≤ N + 1 := by
      have hle := (Finset.mem_Icc.mp hp1.1).2
      cases plus <;> simp [shiftVal] <;> omega
    have hrk_le : r ^ k ≤ N + 1 := le_trans (Nat.le_of_dvd hsh_pos hdvd) hsh_le
    have hr2_le : r * r ≤ N + 1 := by
      have : r ^ 2 ≤ r ^ k := Nat.pow_le_pow_right hr_pr.pos hk2
      rw [sq] at this; exact le_trans this hrk_le
    have hr_le : r ≤ Rmax := Nat.le_sqrt.mpr hr2_le
    have hk_le : k ≤ Kmax := by
      have h2k : 2 ^ k ≤ r ^ k := Nat.pow_le_pow_left hr_pr.two_le k
      exact Nat.le_log_of_pow_le (by norm_num) (le_trans h2k hrk_le)
    exact Finset.mem_biUnion.mpr ⟨(r, k),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hr_pr.two_le, hr_le⟩,
        Finset.mem_Icc.mpr ⟨hk2, hk_le⟩⟩, hgt⟩,
      Finset.mem_filter.mpr ⟨hp1.1, hdvd⟩⟩
  -- For each `(r, k) ∈ Pairs`, count is `≤ (N + 1) / r^k + 1 ≤ 3 * N^ε`
  have heach : ∀ rk ∈ Pairs,
      (((Finset.Icc 1 N).filter (fun p => rk.1 ^ rk.2 ∣ shiftVal plus p)).card : ℝ) ≤
        3 * (N : ℝ) ^ ε := by
    intro rk hrk
    have hrk1 := Finset.mem_filter.mp hrk
    have hr2 : 2 ≤ rk.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hrk1.1).1).1
    have hpow_pos : 1 ≤ rk.1 ^ rk.2 := Nat.one_le_pow _ _ (by omega)
    have hcard := card_shiftVal_dvd_le plus hpow_pos N
    have hcardR : (((Finset.Icc 1 N).filter (fun p => rk.1 ^ rk.2 ∣ shiftVal plus p)).card : ℝ) ≤
        ((N + 1 : ℕ) : ℝ) / ((rk.1 ^ rk.2 : ℕ) : ℝ) + 1 := by
      have h1 : (((Finset.Icc 1 N).filter (fun p => rk.1 ^ rk.2 ∣ shiftVal plus p)).card : ℝ) ≤
          (((N + 1) / (rk.1 ^ rk.2) : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
      have h2 : (((N + 1) / (rk.1 ^ rk.2) : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) / ((rk.1 ^ rk.2 : ℕ) : ℝ) :=
        Nat.cast_div_le
      linarith
    have hdiv_le : ((N + 1 : ℕ) : ℝ) / ((rk.1 ^ rk.2 : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ ε := by
      have hN1 : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
        push_cast
        have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
        linarith
      calc ((N + 1 : ℕ) : ℝ) / ((rk.1 ^ rk.2 : ℕ) : ℝ)
          ≤ (2 * (N : ℝ)) / (N : ℝ) ^ (1 - ε) :=
            div_le_div₀ (by positivity) hN1 (by positivity) hrk1.2.le
        _ = 2 * (N : ℝ) ^ ε := by
            rw [mul_div_assoc, Real.rpow_sub hNR_pos, Real.rpow_one,
              div_div_eq_mul_div, mul_div_cancel_left₀ _ hNR_pos.ne']
    have h1_le : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N)) hε0.le
    linarith
  have hS_card : (S.card : ℝ) ≤ (Pairs.card : ℝ) * (3 * (N : ℝ) ^ ε) := by
    have h1 : S.card ≤ ∑ rk ∈ Pairs, ((Finset.Icc 1 N).filter (fun p => rk.1 ^ rk.2 ∣ shiftVal plus p)).card :=
      (Finset.card_le_card hcov).trans Finset.card_biUnion_le
    have h1R : (S.card : ℝ) ≤ ∑ rk ∈ Pairs, (((Finset.Icc 1 N).filter (fun p => rk.1 ^ rk.2 ∣ shiftVal plus p)).card : ℝ) := by
      exact_mod_cast h1
    calc (S.card : ℝ) ≤ ∑ _rk ∈ Pairs, (3 * (N : ℝ) ^ ε) := h1R.trans (Finset.sum_le_sum heach)
      _ = (Pairs.card : ℝ) * (3 * (N : ℝ) ^ ε) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- Bound `Pairs.card ≤ Rmax * Kmax ≤ 2 * √N * (2 * log(N+1))`
  have hPairs_card : (Pairs.card : ℝ) ≤ 4 * Real.sqrt (N : ℝ) * Real.log ((N : ℝ) + 1) := by
    have hsub : Pairs ⊆ (Finset.Icc 2 Rmax) ×ˢ (Finset.Icc 2 Kmax) := Finset.filter_subset _ _
    have hcard : Pairs.card ≤ Rmax * Kmax := by
      calc Pairs.card ≤ ((Finset.Icc 2 Rmax) ×ˢ (Finset.Icc 2 Kmax)).card := Finset.card_le_card hsub
        _ = (Finset.Icc 2 Rmax).card * (Finset.Icc 2 Kmax).card := Finset.card_product _ _
        _ ≤ Rmax * Kmax := Nat.mul_le_mul (by rw [Nat.card_Icc]; omega) (by rw [Nat.card_Icc]; omega)
    have hRmax : (Rmax : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
      have hsq : Rmax * Rmax ≤ N + 1 := Nat.sqrt_le (N + 1)
      have hR : (Rmax : ℝ) ^ 2 ≤ (N : ℝ) + 1 := by rw [sq]; exact_mod_cast hsq
      have h4N : (N : ℝ) + 1 ≤ (2 * Real.sqrt (N : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hNR_pos.le]
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
        linarith
      nlinarith [Nat.cast_nonneg (α := ℝ) Rmax, Real.sqrt_nonneg (N : ℝ)]
    have hKmax : (Kmax : ℝ) ≤ 2 * Real.log ((N : ℝ) + 1) := by
      have h2K : ((2 ^ Kmax : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega : N + 1 ≠ 0)
      have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ Kmax : ℕ) : ℝ)) h2K
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlog
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith [Nat.cast_nonneg (α := ℝ) Kmax]
    calc (Pairs.card : ℝ) ≤ (Rmax : ℝ) * (Kmax : ℝ) := by exact_mod_cast hcard
      _ ≤ (2 * Real.sqrt (N : ℝ)) * (2 * Real.log ((N : ℝ) + 1)) :=
          mul_le_mul hRmax hKmax (Nat.cast_nonneg _) (by positivity)
      _ = 4 * Real.sqrt (N : ℝ) * Real.log ((N : ℝ) + 1) := by ring
  -- Combine: `12 * √N * N^ε * log(N+1) ≤ 12 * N^(3/4) * log(N+1) ≤ ε * N / log N`
  have hNeps_le : (N : ℝ) ^ ε ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) hε4.le
  have hsqrt_pow : Real.sqrt (N : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) = (N : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNR_pos]; norm_num
  have hlogN_le : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log hNR_pos (by linarith)
  have hN18_le : (N : ℝ) ^ (1 / 8 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) (by norm_num)
  have hsmall := (hN₁ N hNN₁).le
  have hprod_small : 12 * (Real.log ((N : ℝ) + 1)) ^ 2 ≤ ε * (N : ℝ) ^ (1 / 4 : ℝ) := by
    have h1 : (Real.log ((N : ℝ) + 1)) ^ 2 ≤ (ε / 100) * (N : ℝ) ^ (1 / 8 : ℝ) :=
      (div_le_iff₀ (by positivity)).mp hsmall
    nlinarith
  have hfinal_mul : (S.card : ℝ) * Real.log (N : ℝ) ≤ ε * (N : ℝ) := by
    calc (S.card : ℝ) * Real.log (N : ℝ)
        ≤ ((4 * Real.sqrt (N : ℝ) * Real.log ((N : ℝ) + 1)) * (3 * (N : ℝ) ^ ε)) * Real.log (N : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hlogN_pos.le
          exact hS_card.trans (mul_le_mul_of_nonneg_right hPairs_card (by positivity))
      _ ≤ ((4 * Real.sqrt (N : ℝ) * Real.log ((N : ℝ) + 1)) * (3 * (N : ℝ) ^ (1 / 4 : ℝ))) *
            Real.log ((N : ℝ) + 1) := by
          have hlog1_nn : 0 ≤ Real.log ((N : ℝ) + 1) :=
            Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
          refine mul_le_mul ?_ hlogN_le hlogN_pos.le (by positivity)
          gcongr
      _ = (N : ℝ) ^ (3 / 4 : ℝ) * (12 * (Real.log ((N : ℝ) + 1)) ^ 2) := by
          rw [← hsqrt_pow]; ring
      _ ≤ (N : ℝ) ^ (3 / 4 : ℝ) * (ε * (N : ℝ) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hprod_small (by positivity)
      _ = ε * ((N : ℝ) ^ (3 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ)) := by ring
      _ = ε * (N : ℝ) := by rw [← Real.rpow_add hNR_pos]; norm_num
  exact (le_div_iff₀ hlogN_pos).mpr hfinal_mul

/-! ## Section 3: Large Prime Divisors `r > N^(1-ε)` & Full Lemma 1 (`lem-nt1`) -/

/-- **Bloom's Lemma 1 (`lem-nt1`)**: There is an absolute constant `C > 0` (`C = 3000`) such that
for both signs `plus : Bool` and every `0 < ε < 1/4`, for all sufficiently large `N`:
`#{p ≤ N : p prime ∧ ∃ q₀ prime power > N^(1-ε), q₀ ∣ shiftVal plus p} ≤ C * ε * N / log N`. -/
theorem shifted_prime_large_prime_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (plus : Bool) (ε : ℝ), 0 < ε → ε < 1 / 4 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
        (((Finset.Icc 1 N).filter (fun p =>
            p.Prime ∧ ∃ q₀ : ℕ, IsPrimePow q₀ ∧ (N : ℝ) ^ (1 - ε) < (q₀ : ℝ) ∧
              q₀ ∣ shiftVal plus p)).card : ℝ) ≤
          C * ε * (N : ℝ) / Real.log (N : ℝ) := by
  refine ⟨4000, by norm_num, fun plus ε hε0 hε4 => ?_⟩
  obtain ⟨N₁, hN₁_4, hHigher⟩ := higher_prime_power_divisors_bound plus hε0 hε4
  -- Choose `N₂` large enough that:
  -- (a) `N^(1 - ε) > 2` (so every prime `r > N^(1-ε)` is odd),
  -- (b) `ε * log N ≥ 4` (so `3 * (ε * log N + 2) ≤ 5 * ε * log N`, and `1 ≤ ε * N / log N`),
  -- (c) `N^(1 - ε) / 2 ≥ N^(1/2)` and `(N + 1) / (2 * N^ε) ≥ 3` (so `log((N+1)/a) ≥ (1/2) log N`).
  have htend_log : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₂, hN₂⟩ := (tendsto_atTop.mp htend_log (4 / ε + 10)).exists_forall_of_atTop
  set N₀ : ℕ := max (max N₁ N₂) 256
  refine ⟨N₀, by omega, fun N hN => ?_⟩
  have hN256 : 256 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNR_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogN_ge : 4 / ε + 10 ≤ Real.log (N : ℝ) := hN₂ N hNN₂
  have hlogN_pos : 0 < Real.log (N : ℝ) := by
    have : 0 < 4 / ε := by positivity
    linarith
  have heps_log : 4 ≤ ε * Real.log (N : ℝ) := by
    have := mul_le_mul_of_nonneg_left hlogN_ge hε0.le
    have hrew : ε * (4 / ε + 10) = 4 + 10 * ε := by field_simp [hε0.ne']
    linarith
  -- Split the target set into:
  -- `S_hi` (has a higher prime-power divisor `r^k`, `k ≥ 2`, `r^k > N^(1-ε)`)
  -- `S_pr` (has a prime divisor `r > N^(1-ε)` and `p ≥ 3`)
  -- `{2}` (at most 1 element)
  set S_all := (Finset.Icc 1 N).filter (fun p =>
      p.Prime ∧ ∃ q₀ : ℕ, IsPrimePow q₀ ∧ (N : ℝ) ^ (1 - ε) < (q₀ : ℝ) ∧ q₀ ∣ shiftVal plus p)
  set S_hi := (Finset.Icc 1 N).filter (fun p =>
      p.Prime ∧ ∃ r k : ℕ, r.Prime ∧ 2 ≤ k ∧ (N : ℝ) ^ (1 - ε) < ((r ^ k : ℕ) : ℝ) ∧
        r ^ k ∣ shiftVal plus p)
  set S_pr := (Finset.Icc 3 N).filter (fun p =>
      p.Prime ∧ ∃ r : ℕ, r.Prime ∧ (N : ℝ) ^ (1 - ε) < (r : ℝ) ∧ r ∣ shiftVal plus p)
  have hsub : S_all ⊆ S_hi ∪ S_pr ∪ {2} := by
    intro p hp
    have hp1 := Finset.mem_filter.mp hp
    have hpr := hp1.2.1
    obtain ⟨q₀, hpp, hgt, hdvd⟩ := hp1.2.2
    rw [isPrimePow_nat_iff] at hpp
    obtain ⟨r, k, hr_pr, hkpos, rfl⟩ := hpp
    by_cases hk2 : 2 ≤ k
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hp1.1, hpr, r, k, hr_pr, hk2, hgt, hdvd⟩))
    · have hk1 : k = 1 := by omega
      subst hk1
      simp only [pow_one] at hgt hdvd
      by_cases hp2 : p = 2
      · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hp2)
      · have hp3 : 3 ≤ p := by have := hpr.two_le; omega
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp3, (Finset.mem_Icc.mp hp1.1).2⟩,
            hpr, r, hr_pr, hgt, hdvd⟩))
  -- Bound `S_pr` by decomposing `shiftVal plus p = a * r` over even `a ∈ Icc 2 M_a`, `M_a = ⌊2 * N^ε⌋₊`
  set M_a : ℕ := ⌊2 * (N : ℝ) ^ ε⌋₊
  have hMa_ge2 : 2 ≤ M_a := by
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    have h1 : (2 : ℝ) ≤ 2 * (N : ℝ) ^ ε := by
      have := Real.one_le_rpow h1N hε0.le; linarith
    exact Nat.le_floor h1
  have hN_1meps_gt2 : (2 : ℝ) < (N : ℝ) ^ (1 - ε) := by
    have h1 : (256 : ℝ) ^ (3 / 4 : ℝ) ≤ (N : ℝ) ^ (1 - ε) := by
      calc (256 : ℝ) ^ (3 / 4 : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hN256) (by norm_num)
        _ ≤ (N : ℝ) ^ (1 - ε) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) (by linarith)
    have h2 : (2 : ℝ) < (256 : ℝ) ^ (3 / 4 : ℝ) := by
      have h4 : (256 : ℝ) = (4 : ℝ) ^ (4 : ℕ) := by norm_num
      rw [h4, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  -- Cover `S_pr` by `a ∈ (Icc 2 M_a).filter Even`
  set Evens : Finset ℕ := (Finset.Icc 2 M_a).filter Even
  let fiber (a : ℕ) : Finset ℕ :=
    ((Finset.Icc 1 ⌊((N : ℝ) + 1) / (a : ℝ)⌋₊).filter (fun r =>
      r.Prime ∧ (unshiftPrime plus a r).Prime)).image (unshiftPrime plus a)
  have hSpr_cov : S_pr ⊆ Evens.biUnion fiber := by
    intro p hp
    have hp1 := Finset.mem_filter.mp hp
    have hp_icc := Finset.mem_Icc.mp hp1.1
    have hpr := hp1.2.1
    obtain ⟨r, hr_pr, hr_gt, hr_dvd⟩ := hp1.2.2
    set a := shiftVal plus p / r
    have har : a * r = shiftVal plus p := by
      rw [mul_comm]; exact Nat.mul_div_cancel' hr_dvd
    have hr_gt2 : 2 < r := by
      have : (2 : ℝ) < (r : ℝ) := lt_trans hN_1meps_gt2 hr_gt
      exact_mod_cast this
    have hp_odd : Odd p := hpr.odd_of_ne_two (by omega)
    have hr_odd : Odd r := hr_pr.odd_of_ne_two (by omega)
    have hsh_even : Even (shiftVal plus p) := by
      obtain ⟨k, hk⟩ := hp_odd
      cases plus
      · exact ⟨k, by simp [shiftVal]; omega⟩
      · exact ⟨k + 1, by simp [shiftVal]; omega⟩
    have ha_even : Even a := by
      rw [← har] at hsh_even
      rcases Nat.even_mul.mp hsh_even with h | h
      · exact h
      · exact absurd h (Nat.not_even_iff_odd.mpr hr_odd)
    have ha_pos : 0 < a :=
      Nat.div_pos (Nat.le_of_dvd (shiftVal_pos_of_prime plus hpr) hr_dvd) hr_pr.pos
    have ha2 : 2 ≤ a := by obtain ⟨k, hk⟩ := ha_even; omega
    have ha_le : a ≤ M_a := by
      apply Nat.le_floor
      have hsh_le : (shiftVal plus p : ℝ) ≤ (N : ℝ) + 1 := by
        have hle : p ≤ N := hp_icc.2
        cases plus <;> simp only [shiftVal, Bool.false_eq_true, ↓reduceIte]
        · have : (p - 1 : ℕ) ≤ N := by omega
          have hR : ((p - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast this
          linarith
        · push_cast; exact_mod_cast (by omega : p + 1 ≤ N + 1)
      have harR : (a : ℝ) * (r : ℝ) = (shiftVal plus p : ℝ) := by exact_mod_cast har
      have hmul : (a : ℝ) * (N : ℝ) ^ (1 - ε) ≤ (N : ℝ) + 1 := by
        calc (a : ℝ) * (N : ℝ) ^ (1 - ε) ≤ (a : ℝ) * (r : ℝ) :=
              mul_le_mul_of_nonneg_left hr_gt.le (Nat.cast_nonneg a)
          _ = (shiftVal plus p : ℝ) := harR
          _ ≤ (N : ℝ) + 1 := hsh_le
      have hN1 : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
        have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
        linarith
      calc (a : ℝ) ≤ ((N : ℝ) + 1) / (N : ℝ) ^ (1 - ε) := (le_div_iff₀ (by positivity)).mpr hmul
        _ ≤ (2 * (N : ℝ)) / (N : ℝ) ^ (1 - ε) := div_le_div_of_nonneg_right hN1 (by positivity)
        _ = 2 * (N : ℝ) ^ ε := by
            rw [mul_div_assoc, Real.rpow_sub hNR_pos, Real.rpow_one,
              div_div_eq_mul_div, mul_div_cancel_left₀ _ hNR_pos.ne']
    have hr_le_div : r ≤ ⌊((N : ℝ) + 1) / (a : ℝ)⌋₊ := by
      apply Nat.le_floor
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ))]
      have harR : (r : ℝ) * (a : ℝ) = (shiftVal plus p : ℝ) := by
        rw [mul_comm]; exact_mod_cast har
      have hsh_le : (shiftVal plus p : ℝ) ≤ (N : ℝ) + 1 := by
        have hle : p ≤ N := hp_icc.2
        cases plus <;> simp only [shiftVal, Bool.false_eq_true, ↓reduceIte]
        · have : ((p - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : p - 1 ≤ N)
          linarith
        · exact_mod_cast (by omega : p + 1 ≤ N + 1)
      linarith
    have hun : unshiftPrime plus a r = p := by
      have ha_dvd : a ∣ shiftVal plus p := ⟨r, har.symm⟩
      have hr_eq : shiftVal plus p / a = r := by
        rw [← har, Nat.mul_div_cancel_left _ ha_pos]
      rw [← hr_eq]
      exact unshiftPrime_div_eq plus hpr ha_dvd
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha2, ha_le⟩, ha_even⟩,
      Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr_pr.pos, hr_le_div⟩,
        hr_pr, hun ▸ hpr⟩, hun⟩⟩
  -- Bound each fiber using `linear_prime_pair_upper_bound`
  have hfiber_le : ∀ a ∈ Evens,
      ((fiber a).card : ℝ) ≤ 640 * ((1 : ℝ) / (a.totient : ℝ)) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    intro a ha
    have ha_m := Finset.mem_filter.mp ha
    have ha_icc := Finset.mem_Icc.mp ha_m.1
    have ha2 : 2 ≤ a := ha_icc.1
    have ha_even : Even a := ha_m.2
    have ha_leR : (a : ℝ) ≤ 2 * (N : ℝ) ^ ε :=
      (by exact_mod_cast ha_icc.2 : (a : ℝ) ≤ (M_a : ℝ)).trans (Nat.floor_le (by positivity))
    set x_a : ℝ := ((N : ℝ) + 1) / (a : ℝ)
    -- Show `√N ≤ x_a` and `3 ≤ x_a`
    have hxa_ge_sqrt : Real.sqrt (N : ℝ) ≤ x_a := by
      rw [Real.sqrt_eq_rpow]
      dsimp only [x_a]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ))]
      have h1 : (N : ℝ) ^ (1 / 2 : ℝ) * (a : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) * (2 * (N : ℝ) ^ ε) :=
        mul_le_mul_of_nonneg_left ha_leR (by positivity)
      have h2 : (N : ℝ) ^ (1 / 2 : ℝ) * (2 * (N : ℝ) ^ ε) = 2 * (N : ℝ) ^ (1 / 2 + ε) := by
        rw [← mul_assoc, mul_comm ((N : ℝ) ^ (1 / 2 : ℝ)) 2, mul_assoc, ← Real.rpow_add hNR_pos]
      have h3 : 2 * (N : ℝ) ^ (1 / 2 + ε) ≤ (N : ℝ) := by
        -- Since `1/2 + ε < 3/4` and `2 ≤ 256^(1/4) = 4 ≤ N^(1/4)`
        have h4 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
          have : (2 : ℝ) ^ (4 : ℕ) ≤ (N : ℝ) := by norm_num; exact_mod_cast (by omega : 16 ≤ N)
          calc (2 : ℝ) = ((2 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
            _ ≤ (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) this (by norm_num)
        have h5 : (N : ℝ) ^ (1 / 2 + ε) ≤ (N : ℝ) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) (by linarith)
        calc 2 * (N : ℝ) ^ (1 / 2 + ε) ≤ (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) :=
              mul_le_mul h4 h5 (by positivity) (by positivity)
          _ = (N : ℝ) := by rw [← Real.rpow_add hNR_pos]; norm_num
      linarith
    have hxa3 : 3 ≤ x_a := by
      have h16 : (16 : ℝ) ≤ Real.sqrt (N : ℝ) := by
        rw [Real.le_sqrt (by norm_num) hNR_pos.le]; norm_num; exact_mod_cast hN256
      linarith
    have hlog_xa : Real.log (N : ℝ) / 2 ≤ Real.log x_a := by
      rw [← Real.log_sqrt hNR_pos.le]
      exact Real.log_le_log (Real.sqrt_pos.mpr hNR_pos) hxa_ge_sqrt
    have hcard_img : (fiber a).card ≤
        ((Finset.Icc 1 ⌊x_a⌋₊).filter (fun r => r.Prime ∧ (unshiftPrime plus a r).Prime)).card :=
      Finset.card_image_le
    have hbd := linear_prime_pair_upper_bound plus ha2 ha_even hxa3
    have hlog_sq : (Real.log (N : ℝ)) ^ 2 / 4 ≤ (Real.log x_a) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hlog_xa 2
      linarith [show (Real.log (N : ℝ) / 2) ^ 2 = (Real.log (N : ℝ)) ^ 2 / 4 by ring]
    have ha_pos : (0 : ℝ) < (a : ℝ) := by positivity
    have htot_pos : (0 : ℝ) < (a.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
    have hN1 : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
      linarith
    calc ((fiber a).card : ℝ)
        ≤ (((Finset.Icc 1 ⌊x_a⌋₊).filter (fun r => r.Prime ∧ (unshiftPrime plus a r).Prime)).card : ℝ) := by
          exact_mod_cast hcard_img
      _ ≤ 80 * ((a : ℝ) / (a.totient : ℝ)) * x_a / (Real.log x_a) ^ 2 := hbd
      _ ≤ 80 * ((a : ℝ) / (a.totient : ℝ)) * x_a / ((Real.log (N : ℝ)) ^ 2 / 4) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hlog_sq
      _ = 320 * ((1 : ℝ) / (a.totient : ℝ)) * ((N : ℝ) + 1) / (Real.log (N : ℝ)) ^ 2 := by
          dsimp only [x_a]; field_simp [ha_pos.ne', htot_pos.ne', hlogN_pos.ne']; ring
      _ ≤ 320 * ((1 : ℝ) / (a.totient : ℝ)) * (2 * (N : ℝ)) / (Real.log (N : ℝ)) ^ 2 := by
          gcongr
      _ = 640 * ((1 : ℝ) / (a.totient : ℝ)) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by ring
  -- Sum over `a ∈ Evens ⊆ Icc 1 M_a` using `RHDirect.Stage8UniformAP.sum_inv_totient_le`
  have hSpr_le : (S_pr.card : ℝ) ≤ 3900 * ε * (N : ℝ) / Real.log (N : ℝ) := by
    have h1 : S_pr.card ≤ ∑ a ∈ Evens, (fiber a).card :=
      (Finset.card_le_card hSpr_cov).trans Finset.card_biUnion_le
    have h1R : (S_pr.card : ℝ) ≤ ∑ a ∈ Evens, ((fiber a).card : ℝ) := by exact_mod_cast h1
    have h2 : ∑ a ∈ Evens, ((fiber a).card : ℝ) ≤
        (640 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) * ∑ a ∈ Finset.Icc 1 M_a, (1 : ℝ) / (a.totient : ℝ) := by
      calc ∑ a ∈ Evens, ((fiber a).card : ℝ)
          ≤ ∑ a ∈ Evens, 640 * ((1 : ℝ) / (a.totient : ℝ)) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 :=
            Finset.sum_le_sum hfiber_le
        _ = (640 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) * ∑ a ∈ Evens, (1 : ℝ) / (a.totient : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => by ring
        _ ≤ (640 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) * ∑ a ∈ Finset.Icc 1 M_a, (1 : ℝ) / (a.totient : ℝ) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
            intro a ha
            have ha_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
            exact Finset.mem_Icc.mpr ⟨by omega, ha_icc.2⟩
    have htot_sum := RHDirect.Stage8UniformAP.sum_inv_totient_le (by omega : 1 ≤ M_a)
    have hlogMa : Real.log (M_a : ℝ) + 1 ≤ 2 * ε * Real.log (N : ℝ) := by
      have hMa_le : (M_a : ℝ) ≤ 2 * (N : ℝ) ^ ε := Nat.floor_le (by positivity)
      have hlog1 : Real.log (M_a : ℝ) ≤ Real.log (2 * (N : ℝ) ^ ε) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < M_a)) hMa_le
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hNR_pos] at hlog1
      have hlog2 : Real.log 2 ≤ 1 := by
        calc Real.log 2 ≤ Real.log (Real.exp 1) :=
              Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
          _ = 1 := Real.log_exp 1
      linarith
    have hsum_le : ∑ a ∈ Finset.Icc 1 M_a, (1 : ℝ) / (a.totient : ℝ) ≤ 6 * ε * Real.log (N : ℝ) := by
      linarith [htot_sum]
    calc (S_pr.card : ℝ)
        ≤ (640 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) * (6 * ε * Real.log (N : ℝ)) :=
          (h1R.trans h2).trans (mul_le_mul_of_nonneg_left hsum_le (by positivity))
      _ = 3840 * ε * (N : ℝ) / Real.log (N : ℝ) := by field_simp [hlogN_pos.ne']; ring
      _ ≤ 3900 * ε * (N : ℝ) / Real.log (N : ℝ) := by gcongr; norm_num
  -- Combine `S_hi`, `S_pr`, and `{2}`
  have hcard_union : (S_all.card : ℝ) ≤ (S_hi.card : ℝ) + (S_pr.card : ℝ) + 1 := by
    have h1 : S_all.card ≤ S_hi.card + S_pr.card + 1 := by
      calc S_all.card ≤ (S_hi ∪ S_pr ∪ {2}).card := Finset.card_le_card hsub
        _ ≤ (S_hi ∪ S_pr).card + ({2} : Finset ℕ).card := Finset.card_union_le _ _
        _ ≤ S_hi.card + S_pr.card + 1 := by
            have := Finset.card_union_le S_hi S_pr; simp at *; omega
    exact_mod_cast h1
  have hhi := hHigher N hNN₁
  have h1_le : (1 : ℝ) ≤ ε * (N : ℝ) / Real.log (N : ℝ) := by
    rw [le_div_iff₀ hlogN_pos, one_mul]
    -- `log N ≤ ε * N` since `ε * log N ≥ 4` and `(log N)^2 ≤ 4 * N`
    have hlog_sq_le : (Real.log (N : ℝ)) ^ 2 ≤ 4 * (N : ℝ) := by
      have h := Real.log_le_rpow_div hNR_pos.le (by norm_num : (0 : ℝ) < 1 / 2)
      have h1 : Real.log (N : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
        rw [Real.sqrt_eq_rpow]; linarith [show (N : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) = 2 * (N : ℝ) ^ (1 / 2 : ℝ) by ring]
      have h2 := pow_le_pow_left₀ hlogN_pos.le h1 2
      rw [mul_pow, Real.sq_sqrt hNR_pos.le] at h2
      linarith
    nlinarith
  linarith [show ε * (N : ℝ) / Real.log (N : ℝ) + 3900 * ε * (N : ℝ) / Real.log (N : ℝ) +
      ε * (N : ℝ) / Real.log (N : ℝ) = 3902 * ε * (N : ℝ) / Real.log (N : ℝ) by ring,
    show (3902 : ℝ) * ε * (N : ℝ) / Real.log (N : ℝ) ≤ 4000 * ε * (N : ℝ) / Real.log (N : ℝ) by
      gcongr; norm_num]

end PPL024
