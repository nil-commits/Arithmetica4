import RHDirect.ChenDefs
import RHDirect.ChenCombinatorics
import RHDirect.ChenSieveFunctions
import RHDirect.ChenLinearSieve
import RHDirect.ChenBVPrimes
import RHDirect.ChenBilinearBV
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# RHDirect.ChenTheorem

**CHEN'S THEOREM (1973)** — Unconditional, Native-Mathlib Formalization in Lean 4 (`v4.33.1`):

```lean
theorem chen_theorem :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧
        (Nat.Prime q ∨ ∃ r s : ℕ, Nat.Prime r ∧ Nat.Prime s ∧ q = r * s) ∧
        p + q = n
```

Assembles all six independently `leanchecker`-verified pillars:
- `RHDirect.ChenDefs`
- `RHDirect.ChenCombinatorics` (weighted sieve inequality + switching bound + `O(N^{7/8})` exception bound)
- `RHDirect.ChenSieveFunctions` (`LinearSievePair chenF chenf` + certified positive margin `chen_margin_pos`)
- `RHDirect.ChenLinearSieve` (Rosser–Iwaniec linear sieve upper/lower bounds + uniform Chen density)
- `RHDirect.ChenBVPrimes` (prime-counting Bombieri–Vinogradov, `A`/`A_q` remainders, `T₂` integral, `|M|` bound)
- `RHDirect.ChenBilinearBV` (switched bilinear Bombieri–Vinogradov for `chenMProd N`)

Zero `sorry`, zero custom `axiom`s, zero `opaque`, zero `native_decide`.
-/

noncomputable section

open Finset Filter Topology Classical

namespace RHDirect.Chen

/-! ## Section 1: Elementary Asymptotic, Uniform Sieve & Switched-Set Helpers -/

/-- Uniform-in-`ω` Rosser–Iwaniec linear sieve upper & lower bounds with a SINGLE `z₀`
depending ONLY on `(K, F, f, ε)`. -/
private lemma linear_sieve_uniform_bounds {K : ℝ} (hK : 1 ≤ K)
    {F f : ℝ → ℝ} (hFf : LinearSievePair F f) {ε : ℝ} (hε : 0 < ε) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      (∀ (ω : ℕ → ℝ), LinearSieveDensity ω K →
        ∀ (A : Finset ℕ) (X D z : ℝ), 0 ≤ X → z₀ ≤ z → z ≤ D →
          (siftedCard A z : ℝ) ≤
            X * siftProd ω z * (F (Real.log D / Real.log z) + ε) +
              ∑ d ∈ (Finset.range (⌊D⌋₊ + 1)).filter
                  (fun d : ℕ => Squarefree d ∧ (d : ℝ) < D ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < z),
                |((A.filter (fun a => d ∣ a)).card : ℝ) - X * multDensity ω d|) ∧
      (∀ (ω : ℕ → ℝ), LinearSieveDensity ω K →
        ∀ (A : Finset ℕ) (X D z : ℝ), 0 ≤ X → z₀ ≤ z → z ^ 2 ≤ D →
          X * siftProd ω z * (f (Real.log D / Real.log z) - ε) -
              ∑ d ∈ (Finset.range (⌊D⌋₊ + 1)).filter
                  (fun d : ℕ => Squarefree d ∧ (d : ℝ) < D ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < z),
                |((A.filter (fun a => d ∣ a)).card : ℝ) - X * multDensity ω d| ≤
            (siftedCard A z : ℝ)) := by
  obtain ⟨z₀, hz₀2, hV⟩ := linear_sieve_V_bounds hK hFf ε hε
  refine ⟨z₀, hz₀2, ?_, ?_⟩
  · intro ω hω A X D z hX hzz₀ hzD
    have hD1 : 1 < D := by linarith
    have hcomb := (siftedCard_rosser_bounds ω A (X := X) hD1 hzD).1
    have hVup := (hV hω z D hzz₀).1 hzD
    have hXmul := mul_le_mul_of_nonneg_left hVup hX
    unfold sieveDivisors at hcomb
    linarith
  · intro ω hω A X D z hX hzz₀ hz2D
    have hz2 : 2 ≤ z := le_trans hz₀2 hzz₀
    have hzD : z ≤ D := by nlinarith
    have hD1 : 1 < D := by linarith
    have hcomb := (siftedCard_rosser_bounds ω A (X := X) hD1 hzD).2
    have hVlo := (hV hω z D hzz₀).2 hz2D
    have hXmul := mul_le_mul_of_nonneg_left hVlo hX
    unfold sieveDivisors at hcomb
    linarith

/-- Lower bound `siftProd (chenPrimeDensity N) z ≥ c / log z` for `z ≥ 2`, uniform in `N`,
directly from `LinearSieveDensity.mertens_ratio` at `w = 2`. -/
private lemma siftProd_chenPrimeDensity_ge {K : ℝ} {N : ℕ}
    (hω : LinearSieveDensity (chenPrimeDensity N) K) {z : ℝ} (hz : 2 ≤ z) :
    Real.log 2 / ((1 + K / Real.log 2) * Real.log z) ≤ siftProd (chenPrimeDensity N) z := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogz_pos : 0 < Real.log z := Real.log_pos (by linarith)
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hω.K_ge_one
  have hdenom_pos : 0 < 1 + K / Real.log 2 := by positivity
  have hm := hω.mertens_ratio 2 z le_rfl hz
  have hfilt :
      (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (2 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < z) =
        (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < z) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hr, hp, _, hlt⟩; exact ⟨hr, hp, hlt⟩
    · rintro ⟨hr, hp, hlt⟩
      exact ⟨hr, hp, by exact_mod_cast hp.two_le, hlt⟩
  rw [hfilt, Finset.prod_inv_distrib] at hm
  have hV_pos : 0 < siftProd (chenPrimeDensity N) z := siftProd_chenPrimeDensity_pos N z
  change (siftProd (chenPrimeDensity N) z)⁻¹ ≤ (Real.log z / Real.log 2) * (1 + K / Real.log 2) at hm
  have hinv := inv_anti₀ (inv_pos.mpr hV_pos) hm
  rw [inv_inv] at hinv
  have heq : ((Real.log z / Real.log 2) * (1 + K / Real.log 2))⁻¹ =
      Real.log 2 / ((1 + K / Real.log 2) * Real.log z) := by
    field_simp [hlog2_pos.ne', hlogz_pos.ne', hdenom_pos.ne']
  linarith

/-- Every `m ∈ chenMProd N` satisfies `m < N` and `Nat.Coprime m N`. -/
private lemma mem_chenMProd_props {N m : ℕ} (hm : m ∈ chenMProd N) :
    m < N ∧ Nat.Coprime m N := by
  unfold chenMProd at hm
  rcases Finset.mem_image.mp hm with ⟨t, ht, rfl⟩
  unfold chenM at ht
  rw [Finset.mem_filter] at ht
  rcases ht.2 with ⟨hq1, hq2, hq3, h1N, h2N, h3N, _, _, _, _, hltN⟩
  refine ⟨hltN, ?_⟩
  have hc1 : Nat.Coprime t.1 N := (hq1.coprime_iff_not_dvd).mpr h1N
  have hc2 : Nat.Coprime t.2.1 N := (hq2.coprime_iff_not_dvd).mpr h2N
  have hc3 : Nat.Coprime t.2.2 N := (hq3.coprime_iff_not_dvd).mpr h3N
  exact (hc1.mul_left hc2).mul_left hc3

/-- For any `d`, `((chenSwitchedSet N).filter (d ∣ ·)).card = ((chenMProd N).filter (d ∣ N - ·)).card`. -/
private lemma card_chenSwitchedSet_filter_dvd (N d : ℕ) :
    ((chenSwitchedSet N).filter (fun b => d ∣ b)).card =
      ((chenMProd N).filter (fun m => d ∣ (N - m))).card := by
  unfold chenSwitchedSet
  rw [Finset.filter_image]
  refine Finset.card_image_of_injOn ?_
  intro m₁ hm₁ m₂ hm₂ heq
  have h1 : m₁ < N := (mem_chenMProd_props (Finset.mem_filter.mp (Finset.mem_coe.mp hm₁)).1).1
  have h2 : m₂ < N := (mem_chenMProd_props (Finset.mem_filter.mp (Finset.mem_coe.mp hm₂)).1).1
  dsimp only at heq
  omega

/-- If `¬ Nat.Coprime d N`, no element `m ∈ chenMProd N` satisfies `d ∣ (N - m)`. -/
private lemma chenMProd_filter_dvd_eq_zero_of_not_coprime {N d : ℕ} (hnc : ¬ Nat.Coprime d N) :
    ((chenMProd N).filter (fun m => d ∣ (N - m))).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m hm hdvd
  obtain ⟨hmN, hmcop⟩ := mem_chenMProd_props hm
  have hg : Nat.gcd d N ≠ 1 := hnc
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
  have hpd : p ∣ d := hpg.trans (Nat.gcd_dvd_left d N)
  have hpN : p ∣ N := hpg.trans (Nat.gcd_dvd_right d N)
  have hpsub : p ∣ (N - m) := hpd.trans hdvd
  have hpm : p ∣ m := by
    have hsum : (N - m) + m = N := Nat.sub_add_cancel hmN.le
    exact (Nat.dvd_add_right hpsub).mp (hsum.symm ▸ hpN)
  have hp1 : p ∣ Nat.gcd m N := Nat.dvd_gcd hpm hpN
  rw [hmcop.gcd_eq_one] at hp1
  exact hp.not_dvd_one hp1

/-- The linear-sieve remainder sum for `chenSwitchedSet N` reduces directly to the sum bounded
by `chen_bilinear_bombieri_vinogradov_prod`: non-coprime `d` contribute `0`. -/
private lemma chenSwitchedSet_remainder_le {N : ℕ} (hEven : Even N) {D z : ℝ} :
    ∑ d ∈ (Finset.range (⌊D⌋₊ + 1)).filter
        (fun d : ℕ => Squarefree d ∧ (d : ℝ) < D ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < z),
        |(((chenSwitchedSet N).filter (fun b => d ∣ b)).card : ℝ) -
          ((chenMProd N).card : ℝ) * multDensity (chenPrimeDensity N) d| ≤
      ∑ d ∈ (Finset.Icc 1 ⌊D⌋₊).filter
        (fun d : ℕ => Squarefree d ∧ Nat.Coprime d N ∧ ∀ p ∈ d.primeFactors, p ≠ 2),
        |(((chenMProd N).filter (fun m => d ∣ (N - m))).card : ℝ) -
          ((chenMProd N).card : ℝ) / (d.totient : ℝ)| := by
  set S_lhs := (Finset.range (⌊D⌋₊ + 1)).filter
    (fun d : ℕ => Squarefree d ∧ (d : ℝ) < D ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < z)
  set S_rhs := (Finset.Icc 1 ⌊D⌋₊).filter
    (fun d : ℕ => Squarefree d ∧ Nat.Coprime d N ∧ ∀ p ∈ d.primeFactors, p ≠ 2)
  have hterm : ∀ d ∈ S_lhs,
      |(((chenSwitchedSet N).filter (fun b => d ∣ b)).card : ℝ) -
        ((chenMProd N).card : ℝ) * multDensity (chenPrimeDensity N) d| =
      if d ∈ S_rhs then
        |(((chenMProd N).filter (fun m => d ∣ (N - m))).card : ℝ) -
          ((chenMProd N).card : ℝ) / (d.totient : ℝ)|
      else 0 := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_range] at hd
    rcases hd with ⟨hd_le, hd_sqf, _, _⟩
    have hd_pos : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with rfl | hp
      · exact absurd hd_sqf not_squarefree_zero
      · exact hp
    rw [card_chenSwitchedSet_filter_dvd]
    by_cases hcop : Nat.Coprime d N
    · have hno2 : ∀ p ∈ d.primeFactors, p ≠ 2 := by
        intro p hp hpeq
        subst hpeq
        have h2d : 2 ∣ d := Nat.dvd_of_mem_primeFactors hp
        have h2N : 2 ∣ N := even_iff_two_dvd.mp hEven
        have h21 : 2 ∣ Nat.gcd d N := Nat.dvd_gcd h2d h2N
        rw [hcop.gcd_eq_one] at h21
        omega
      have hd_rhs : d ∈ S_rhs := by
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hd_pos, by omega⟩, hd_sqf, hcop, hno2⟩
      rw [if_pos hd_rhs]
      have hmd := (multDensity_chenPrimeDensity_eq hEven hd_sqf).1 hcop
      rw [hmd, mul_one_div]
    · have hd_nrhs : d ∉ S_rhs := by
        intro hmem
        exact hcop (Finset.mem_filter.mp hmem).2.2.1
      rw [if_neg hd_nrhs]
      have hmd := (multDensity_chenPrimeDensity_eq hEven hd_sqf).2 hcop
      rw [hmd.1, mul_zero, chenMProd_filter_dvd_eq_zero_of_not_coprime hcop]
      simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => (Finset.mem_filter.mp hd).2) ?_
  intro d _ _
  exact abs_nonneg _

/-- For any `B : ℝ` and `α > 0`, `(log N) ^ B ≤ N ^ α` for all sufficiently large `N : ℕ`. -/
private lemma eventually_log_rpow_le_rpow (B α : ℝ) (hα : 0 < α) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (Real.log (N : ℝ)) ^ B ≤ (N : ℝ) ^ α := by
  have h1 : Tendsto (fun x : ℝ => (Real.log x) ^ B / x ^ α) atTop (nhds 0) :=
    isLittleO_log_rpow_rpow_atTop B hα |>.tendsto_div_nhds_zero
  have h2 := h1.comp tendsto_natCast_atTop_atTop
  have hev := h2.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₁, hN₁⟩ := hev
  refine ⟨max N₁ 3, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hpow_pos : (0 : ℝ) < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNpos α
  have hlt : (Real.log (N : ℝ)) ^ B / (N : ℝ) ^ α < 1 := hN₁ N hN1
  exact ((div_lt_one hpow_pos).mp hlt).le

/-- `log (log N) / log N → 0` as `N → ∞`. -/
private lemma eventually_log_log_div_log_lt (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)| < δ := by
  have h1 : Tendsto (fun y : ℝ => Real.log y / y) atTop (nhds 0) := by
    simpa [Real.rpow_one] using isLittleO_log_rpow_rpow_atTop (1 : ℝ) one_pos |>.tendsto_div_nhds_zero
  have h2 : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) atTop (nhds 0) :=
    h1.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hev := Metric.tendsto_atTop.mp h2 δ hδ
  obtain ⟨N₁, hN₁⟩ := hev
  refine ⟨N₁, fun N hN => ?_⟩
  rw [abs_div]
  simpa [Real.dist_eq] using hN₁ N hN

/-- For any `C : ℝ` and `δ > 0`, `C / log N < δ` for all sufficiently large `N : ℕ`. -/
private lemma eventually_const_div_log_lt (C δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C / Real.log (N : ℝ) < δ := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev := hlog.eventually (Filter.eventually_gt_atTop (max 1 (|C| / δ + 1)))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₁, hN₁⟩ := hev
  refine ⟨max N₁ 3, fun N hN => ?_⟩
  have hgt : max 1 (|C| / δ + 1) < Real.log (N : ℝ) := hN₁ N (le_trans (le_max_left _ _) hN)
  have hLpos : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le zero_lt_one (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hgt))
  have hLgt : |C| / δ < Real.log (N : ℝ) := by
    have : |C| / δ + 1 < Real.log (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hgt
    linarith
  rw [div_lt_iff₀ hLpos]
  calc C ≤ |C| := le_abs_self C
    _ = (|C| / δ) * δ := by field_simp [hδ.ne']
    _ < Real.log (N : ℝ) * δ := mul_lt_mul_of_pos_right hLgt hδ
    _ = δ * Real.log (N : ℝ) := mul_comm _ _

/-- For any `C ≥ 0` and `α > 0`, `C * N ^ (1 - α) ≤ N / (log N)^3` for all sufficiently large `N`. -/
private lemma eventually_subpower_le_div_log_cube (C α : ℝ) (_hC : 0 ≤ C) (hα : 0 < α) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C * (N : ℝ) ^ (1 - α) ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
  obtain ⟨N₁, hN₁⟩ := eventually_log_rpow_le_rpow 3 (α / 2) (by linarith)
  have hpow_atTop : Tendsto (fun N : ℕ => (N : ℝ) ^ (α / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < α / 2)).comp tendsto_natCast_atTop_atTop
  have hev := hpow_atTop.eventually (Filter.eventually_ge_atTop (max 1 C))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₂, hN₂⟩ := hev
  refine ⟨max (max N₁ N₂) 3, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hLpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlog3 : (Real.log (N : ℝ)) ^ (3 : ℕ) ≤ (N : ℝ) ^ (α / 2) := by
    have := hN₁ N hN1
    rwa [show (Real.log (N : ℝ)) ^ (3 : ℝ) = (Real.log (N : ℝ)) ^ (3 : ℕ) by
      exact_mod_cast Real.rpow_natCast (Real.log (N : ℝ)) 3] at this
  have hC_le : C ≤ (N : ℝ) ^ (α / 2) := le_trans (le_max_right _ _) (hN₂ N hN2)
  rw [le_div_iff₀ (pow_pos hLpos 3)]
  have hprod : C * (Real.log (N : ℝ)) ^ 3 ≤ (N : ℝ) ^ α := by
    calc C * (Real.log (N : ℝ)) ^ 3
        ≤ (N : ℝ) ^ (α / 2) * (N : ℝ) ^ (α / 2) :=
          mul_le_mul hC_le hlog3 (pow_nonneg hLpos.le 3) (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ (α / 2 + α / 2) := (Real.rpow_add hNpos _ _).symm
      _ = (N : ℝ) ^ α := by ring_nf
  calc C * (N : ℝ) ^ (1 - α) * (Real.log (N : ℝ)) ^ 3
      = (N : ℝ) ^ (1 - α) * (C * (Real.log (N : ℝ)) ^ 3) := by ring
    _ ≤ (N : ℝ) ^ (1 - α) * (N : ℝ) ^ α :=
        mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hNpos.le _)
    _ = (N : ℝ) ^ ((1 - α) + α) := (Real.rpow_add hNpos _ _).symm
    _ = (N : ℝ) := by simp

/-! ## Section 2: Main Proof of Chen's Theorem (1973) -/

/-- **Quantitative Chen Lower Bound**:
there exists `N₀ : ℕ` such that for every even integer `N ≥ N₀`, `0 < (chenP2Count N : ℝ)`. -/
theorem chenP2Count_pos_eventually :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → (0 : ℝ) < (chenP2Count N : ℝ) := by
  -- 1. Uniform Chen density constant `K ≥ 1` and lower bound `V(N^{1/8}) ≥ c_V / log N`
  obtain ⟨K, hω_all⟩ := chenPrimeDensity_linearSieve
  have hK1 : 1 ≤ K := (hω_all 0).K_ge_one
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c_V : ℝ := 8 * Real.log 2 / (1 + K / Real.log 2) with hcV_def
  have hcV_pos : 0 < c_V := by positivity

  -- 2. Certified positive Chen margin `M > 0` from `chen_margin_pos`
  set M : ℝ := (1 / 50 : ℝ) / (8 * chenL₀) with hM_def
  have hL₀_pos : 0 < chenL₀ := chenL₀_pos
  have hM_pos : 0 < M := by positivity
  set I_T2 : ℝ := ∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), chenF (4 - 8 * u) / u with hIT2_def
  have hmargin : M ≤ chenf 4 - (1 / 2 : ℝ) * I_T2 - (1 / 4 : ℝ) * chenIB * chenF 2 := chen_margin_pos
  have hF2_pos : 0 < chenF 2 := lt_of_lt_of_le zero_lt_one (chenSievePair.one_le_F 2 (by norm_num))
  have hf4_le : chenf 4 ≤ 1 := chenSievePair.f_le_one 4 (by norm_num)
  have hf4_nn : 0 ≤ chenf 4 := chenSievePair.f_nonneg 4 (by norm_num)
  have hIB_lt : chenIB < 37 / 100 := chenIB_lt
  have hIB_nn : 0 ≤ chenIB := by
    unfold chenIB
    refine intervalIntegral.integral_nonneg (by norm_num) fun u hu => ?_
    have h1 : 1 ≤ 2 - 3 * u := by linarith [hu.2]
    have hlog_nn : 0 ≤ Real.log (2 - 3 * u) := Real.log_nonneg h1
    have hu_pos : 0 < u := by linarith [hu.1]
    have h1u_pos : 0 < 1 - u := by linarith [hu.2]
    positivity
  have hIT2_eq : (1 / 2 : ℝ) * I_T2 = Real.log 6 / (8 * chenL₀) := chen_T2_integral_eq
  have hIT2_nn : 0 ≤ I_T2 := by
    have h6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    have : 0 ≤ (1 / 2 : ℝ) * I_T2 := by rw [hIT2_eq]; positivity
    linarith

  -- 3. Choose a single tiny tolerance `η > 0` so all error terms sum to `< M / 2`
  set W : ℝ := 10 + I_T2 + chenF 2 + 2 * chenIB with hW_def
  have hW_pos : 0 < W := by positivity
  set η : ℝ := min (1 / 20) (M / (40 * W)) with hη_def
  have hη_pos : 0 < η := by positivity
  have hη_le : η ≤ 1 / 20 := min_le_left _ _
  have hηW : η * W ≤ M / 40 := by
    have hle : η ≤ M / (40 * W) := min_le_right _ _
    calc η * W ≤ (M / (40 * W)) * W := mul_le_mul_of_nonneg_right hle hW_pos.le
      _ = M / 40 := by field_simp [hW_pos.ne']

  -- 4. Gather all analytic & sieve inputs with uniform thresholds independent of `N`
  obtain ⟨B₁, C₁, hB₁_pos, hC₁_pos, hRemA⟩ := chen_A_remainder_bound_ge 3
  obtain ⟨B₂, C₂, hB₂_pos, hC₂_pos, hRemAq⟩ := chen_Aq_remainder_bound_ge 3
  obtain ⟨B₃, C₃, hB₃_pos, hC₃_pos, hRemB⟩ := chen_bilinear_bombieri_vinogradov_prod 3
  set B₁₂ : ℝ := max B₁ B₂ with hB12_def
  have hB₁₂_pos : 0 < B₁₂ := lt_of_lt_of_le hB₁_pos (le_max_left _ _)

  obtain ⟨z₀, hz₀2, hSieveUp, hSieveLo⟩ := linear_sieve_uniform_bounds hK1 chenSievePair hη_pos
  obtain ⟨N_gold, hN_gold4, hGoldAsymp⟩ := chenGoldbachSet_card_asymp η hη_pos
  obtain ⟨N_M, hM_upper⟩ := chenM_card_upper η hη_pos
  obtain ⟨N_rat, hV_rat⟩ := siftProd_chenPrimeDensity_ratio_of_ge_rpow η hη_pos

  -- `T₂` integral bound for `chenF` AND for constant `1` (giving `∑ 1/(q-1) ≤ 3`!)
  obtain ⟨N_T2, hT2_int⟩ := chen_T2_sum_le_integral chenSievePair.F_cont chenSievePair.F_antitone
    (fun s hs => le_trans zero_le_one (chenSievePair.one_le_F s hs)) hB₁₂_pos η hη_pos
  obtain ⟨N_T2_one, hT2_one⟩ := chen_T2_sum_le_integral continuousOn_const
    (fun _ _ _ _ _ => le_rfl) (fun _ _ => zero_le_one) hB₁₂_pos (1 : ℝ) one_pos

  -- Continuity of `chenf` at `4` and `chenF` at `2`
  have hf4_cont : ContinuousAt chenf 4 :=
    chenSievePair.f_cont.continuousAt (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 4))
  have hF2_cont : ContinuousAt chenF 2 :=
    chenSievePair.F_cont.continuousAt (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 2))
  obtain ⟨δf, hδf_pos, hδf_ball⟩ := Metric.continuousAt_iff.mp hf4_cont η hη_pos
  obtain ⟨δF, hδF_pos, hδF_ball⟩ := Metric.continuousAt_iff.mp hF2_cont η hη_pos
  set δ_arg : ℝ := min (min δf δF) (1 / 2) with hδarg_def
  have hδarg_pos : 0 < δ_arg := by positivity
  set B_max : ℝ := max B₁₂ B₃ with hBmax_def
  have hBmax_pos : 0 < B_max := lt_of_lt_of_le hB₁₂_pos (le_max_left _ _)
  obtain ⟨N_ll, hll⟩ := eventually_log_log_div_log_lt (δ_arg / (8 * B_max)) (by positivity)

  -- Thresholds for `z₀ ≤ N^{1/8}`, `N^{1/4} ≤ D₁₂`, `N^{1/8} ≤ D₁₂ / N^{1/3}`, `N^{1/4} ≤ D₃`
  have hz8_tend : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 8)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N_z0, hN_z0⟩ := Filter.eventually_atTop.mp
    (hz8_tend.eventually (Filter.eventually_ge_atTop (max z₀ 2)))
  obtain ⟨N_log12, hN_log12⟩ := eventually_log_rpow_le_rpow B₁₂ (1 / 24) (by norm_num)
  obtain ⟨N_log3, hN_log3⟩ := eventually_log_rpow_le_rpow B₃ (1 / 4) (by norm_num)

  -- Thresholds for remainders & `O(N^{7/8})` errors `≤ (M / 20) * (c_V * N / (log N)^2)`
  obtain ⟨N_sub78, hN_sub78⟩ := eventually_subpower_le_div_log_cube (5 : ℝ) (1 / 8) (by norm_num) (by norm_num)
  set C_tot : ℝ := C₁ + (1 / 2 : ℝ) * C₂ + (1 / 2 : ℝ) * C₃ + 5 with hCtot_def
  have hCtot_pos : 0 < C_tot := by positivity
  obtain ⟨N_rem, hN_rem⟩ := eventually_const_div_log_lt (C_tot / c_V) (M / 20) (by positivity)

  -- Combine all `N`-thresholds into one explicit `N₀`
  let N₀ : ℕ :=
    max (max (max (max 256 N_gold) (max N_M N_rat))
             (max (max N_T2 N_T2_one) (max N_ll N_z0)))
        (max (max N_log12 N_log3) (max N_sub78 N_rem))
  refine ⟨N₀, fun N hN hEven => ?_⟩

  -- Unpack all individual threshold inequalities for `N ≥ N₀`
  have hN256 : 256 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)))
  have hN_gold_le : N_gold ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)))
  have hN_M_le : N_M ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)))
  have hN_rat_le : N_rat ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)))
  have hN_T2_le : N_T2 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)))
  have hN_T2_one_le : N_T2_one ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)))
  have hN_ll_le : N_ll ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)))
  have hN_z0_le : N_z0 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)))
  have hN_log12_le : N_log12 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN))
  have hN_log3_le : N_log3 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN))
  have hN_sub78_le : N_sub78 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN))
  have hN_rem_le : N_rem ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN))

  have hN4 : 4 ≤ N := by omega
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN_gt1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hL_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN_gt1

  -- Define scales `z₈ = N^{1/8}`, `z₄ = N^{1/4}`, `D₁₂`, `D₃`, `V₈`, and reference scale `S₀`
  set ω := chenPrimeDensity N
  have hω : LinearSieveDensity ω K := hω_all N
  set z₈ : ℝ := (N : ℝ) ^ ((1 : ℝ) / 8) with hz8_def
  set z₄ : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4) with hz4_def
  set D₁₂ : ℝ := Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B₁₂ with hD12_def
  set D₃ : ℝ := Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B₃ with hD3_def
  set V₈ : ℝ := siftProd ω z₈ with hV8_def
  set V₄ : ℝ := siftProd ω z₄ with hV4_def
  set X_A : ℝ := ((chenGoldbachSet N).card : ℝ) with hXA_def
  set S₀ : ℝ := ((N : ℝ) / Real.log (N : ℝ)) * V₈ with hS0_def

  have hz8_ge_z0 : z₀ ≤ z₈ := le_trans (le_max_left _ _) (hN_z0 N hN_z0_le)
  have hz8_ge2 : 2 ≤ z₈ := le_trans (le_max_right _ _) (hN_z0 N hN_z0_le)
  have hz8_pos : 0 < z₈ := by linarith
  have hz8_le_z4 : z₈ ≤ z₄ := Real.rpow_le_rpow_of_exponent_le hN_gt1.le (by norm_num)
  have hz4_ge_z0 : z₀ ≤ z₄ := le_trans hz8_ge_z0 hz8_le_z4
  have hz8_sq_eq : z₈ ^ 2 = z₄ := by
    rw [hz8_def, hz4_def, ← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]; norm_num
  have hV8_pos : 0 < V₈ := siftProd_chenPrimeDensity_pos N z₈
  have hS0_pos : 0 < S₀ := by positivity

  -- Lower bound `V₈ ≥ c_V / log N` and hence `c_V * N / (log N)^2 ≤ S₀`
  have hlog_z8 : Real.log z₈ = (1 / 8 : ℝ) * Real.log (N : ℝ) := by
    rw [hz8_def, Real.log_rpow hN_pos]
  have hlog_z4 : Real.log z₄ = (1 / 4 : ℝ) * Real.log (N : ℝ) := by
    rw [hz4_def, Real.log_rpow hN_pos]
  have hV8_ge : c_V / Real.log (N : ℝ) ≤ V₈ := by
    have h1 := siftProd_chenPrimeDensity_ge hω hz8_ge2
    rw [hlog_z8] at h1
    have hrew : Real.log 2 / ((1 + K / Real.log 2) * ((1 / 8 : ℝ) * Real.log (N : ℝ))) =
        c_V / Real.log (N : ℝ) := by
      rw [hcV_def]
      have hd : 1 + K / Real.log 2 ≠ 0 := by positivity
      field_simp [hlog2_pos.ne', hL_pos.ne', hd]
    linarith
  have hS0_ge : c_V * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 ≤ S₀ := by
    have h1 := mul_le_mul_of_nonneg_left hV8_ge (show 0 ≤ (N : ℝ) / Real.log (N : ℝ) by positivity)
    have hrew : (N : ℝ) / Real.log (N : ℝ) * (c_V / Real.log (N : ℝ)) =
        c_V * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by ring
    linarith

  -- Verify `z₄ ≤ D₁₂`, `z₈ ≤ D₁₂ / N^{1/3}`, and `z₄ ≤ D₃`
  have hsqrt_eq : Real.sqrt (N : ℝ) = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (N : ℝ)
  have hlogB12_pos : 0 < (Real.log (N : ℝ)) ^ B₁₂ := Real.rpow_pos_of_pos hL_pos B₁₂
  have hlogB3_pos : 0 < (Real.log (N : ℝ)) ^ B₃ := Real.rpow_pos_of_pos hL_pos B₃
  have hlogB12_le : (Real.log (N : ℝ)) ^ B₁₂ ≤ (N : ℝ) ^ ((1 : ℝ) / 24) := hN_log12 N hN_log12_le
  have hlogB3_le : (Real.log (N : ℝ)) ^ B₃ ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := hN_log3 N hN_log3_le
  have hz4_le_D12 : z₄ ≤ D₁₂ := by
    rw [hD12_def, le_div_iff₀ hlogB12_pos, hz4_def, hsqrt_eq]
    calc (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log (N : ℝ)) ^ B₁₂
        ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((1 : ℝ) / 24) :=
          mul_le_mul_of_nonneg_left hlogB12_le (Real.rpow_nonneg hN_pos.le _)
      _ = (N : ℝ) ^ ((1 : ℝ) / 4 + 1 / 24) := (Real.rpow_add hN_pos _ _).symm
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hN_gt1.le (by norm_num)
  have hz8_sq_le_D12 : z₈ ^ 2 ≤ D₁₂ := by rw [hz8_sq_eq]; exact hz4_le_D12
  have hz4_le_D3 : z₄ ≤ D₃ := by
    rw [hD3_def, le_div_iff₀ hlogB3_pos, hz4_def, hsqrt_eq]
    calc (N : ℝ) ^ ((1 : ℝ) / 4) * (Real.log (N : ℝ)) ^ B₃
        ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left hlogB3_le (Real.rpow_nonneg hN_pos.le _)
      _ = (N : ℝ) ^ ((1 : ℝ) / 4 + 1 / 4) := (Real.rpow_add hN_pos _ _).symm
      _ = (N : ℝ) ^ ((1 : ℝ) / 2) := by norm_num

  -- Continuity bounds: `chenf (log D₁₂ / log z₈) ≥ chenf 4 - η` and `chenF (log D₃ / log z₄) ≤ chenF 2 + η`
  have hll_bd : |Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)| < δ_arg / (8 * B_max) := hll N hN_ll_le
  have hs1_eq : Real.log D₁₂ / Real.log z₈ =
      4 - 8 * B₁₂ * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) := by
    rw [hD12_def, Real.log_div (Real.sqrt_pos.mpr hN_pos).ne' hlogB12_pos.ne',
      Real.log_sqrt hN_pos.le, Real.log_rpow hL_pos, hlog_z8]
    field_simp [hL_pos.ne']
    ring
  have hs3_eq : Real.log D₃ / Real.log z₄ =
      2 - 4 * B₃ * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) := by
    rw [hD3_def, Real.log_div (Real.sqrt_pos.mpr hN_pos).ne' hlogB3_pos.ne',
      Real.log_sqrt hN_pos.le, Real.log_rpow hL_pos, hlog_z4]
    field_simp [hL_pos.ne']
    ring
  have hf_s1_ge : chenf 4 - η ≤ chenf (Real.log D₁₂ / Real.log z₈) := by
    have hdist : dist (Real.log D₁₂ / Real.log z₈) 4 < δf := by
      rw [Real.dist_eq, hs1_eq, show (4 - 8 * B₁₂ * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))) - 4 =
        -(8 * B₁₂ * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))) by ring, abs_neg,
        abs_mul, abs_of_pos (by positivity : 0 < 8 * B₁₂)]
      have hB12_le : B₁₂ ≤ B_max := le_max_left _ _
      calc 8 * B₁₂ * |Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)|
          ≤ 8 * B_max * |Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ < 8 * B_max * (δ_arg / (8 * B_max)) :=
            mul_lt_mul_of_pos_left hll_bd (by positivity)
        _ = δ_arg := by field_simp [hBmax_pos.ne']
        _ ≤ δf := le_trans (min_le_left _ _) (min_le_left _ _)
    have h := hδf_ball hdist
    rw [Real.dist_eq, abs_lt] at h
    linarith
  have hF_s3_le : chenF (Real.log D₃ / Real.log z₄) ≤ chenF 2 + η := by
    have hdist : dist (Real.log D₃ / Real.log z₄) 2 < δF := by
      rw [Real.dist_eq, hs3_eq, show (2 - 4 * B₃ * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))) - 2 =
        -(4 * B₃ * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))) by ring, abs_neg,
        abs_mul, abs_of_pos (by positivity : 0 < 4 * B₃)]
      have hB3_le : B₃ ≤ B_max := le_max_right _ _
      calc 4 * B₃ * |Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)|
          ≤ 8 * B_max * |Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ < 8 * B_max * (δ_arg / (8 * B_max)) :=
            mul_lt_mul_of_pos_left hll_bd (by positivity)
        _ = δ_arg := by field_simp [hBmax_pos.ne']
        _ ≤ δF := le_trans (min_le_left _ _) (min_le_right _ _)
    have h := hδF_ball hdist
    rw [Real.dist_eq, abs_lt] at h
    linarith

  -- Asymptotic scale bounds for `X_A = (chenGoldbachSet N).card`
  have hXA_asymp := hGoldAsymp N hN_gold_le hEven
  have hXA_lo : (1 - η) * ((N : ℝ) / Real.log (N : ℝ)) ≤ X_A := by
    rw [abs_le] at hXA_asymp
    have hNL_pos : 0 < (N : ℝ) / Real.log (N : ℝ) := by positivity
    have h1 := (le_div_iff₀ hNL_pos).mp (by linarith [hXA_asymp.1] : 1 - η ≤ X_A / ((N : ℝ) / Real.log (N : ℝ)))
    linarith
  have hXA_hi : X_A ≤ (1 + η) * ((N : ℝ) / Real.log (N : ℝ)) := by
    rw [abs_le] at hXA_asymp
    have hNL_pos : 0 < (N : ℝ) / Real.log (N : ℝ) := by positivity
    have h1 := (div_le_iff₀ hNL_pos).mp (by linarith [hXA_asymp.2] : X_A / ((N : ℝ) / Real.log (N : ℝ)) ≤ 1 + η)
    linarith
  have hXA_nn : 0 ≤ X_A := by positivity

  -- =========================================================================
  -- TERM 1: Lower bound on `S(A, P(N^{1/8}))` via `linear_sieve_lower`
  -- =========================================================================
  have hT1_raw := hSieveLo ω hω (chenGoldbachSet N) X_A D₁₂ z₈ hXA_nn hz8_ge_z0 hz8_sq_le_D12
  have hR1_le :
      ∑ d ∈ (Finset.range (⌊D₁₂⌋₊ + 1)).filter
          (fun d : ℕ => Squarefree d ∧ (d : ℝ) < D₁₂ ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < z₈),
        |(((chenGoldbachSet N).filter (fun a => d ∣ a)).card : ℝ) - X_A * multDensity ω d| ≤
      C₁ * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
    have hsub : (Finset.range (⌊D₁₂⌋₊ + 1)).filter
          (fun d : ℕ => Squarefree d ∧ (d : ℝ) < D₁₂ ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < z₈) ⊆
        (Finset.Icc 1 ⌊D₁₂⌋₊).filter Squarefree := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_range] at hd
      have hd_pos : 1 ≤ d := by
        rcases Nat.eq_zero_or_pos d with rfl | hp
        · exact absurd hd.2.1 not_squarefree_zero
        · exact hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd_pos, by omega⟩, hd.2.1⟩
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun d => |(((chenGoldbachSet N).filter (fun a => d ∣ a)).card : ℝ) - X_A * multDensity ω d|)
      hsub (fun d _ _ => abs_nonneg _)
    have ha := hRemA B₁₂ (le_max_left _ _) N hN4 hEven
    rw [show (Real.log (N : ℝ)) ^ (3 : ℝ) = (Real.log (N : ℝ)) ^ (3 : ℕ) by
      exact_mod_cast Real.rpow_natCast (Real.log (N : ℝ)) 3] at ha
    exact hle.trans ha
  have hT1_main : (chenf 4 - 3 * η) * S₀ ≤ X_A * V₈ * (chenf (Real.log D₁₂ / Real.log z₈) - η) := by
    have hcoef_le : chenf 4 - 2 * η ≤ chenf (Real.log D₁₂ / Real.log z₈) - η := by linarith only [hf_s1_ge]
    have hXV_ge : (1 - η) * S₀ ≤ X_A * V₈ := by
      have h1 := mul_le_mul_of_nonneg_right hXA_lo hV8_pos.le
      rw [hS0_def]; linarith only [h1]
    by_cases hpos : 0 ≤ chenf 4 - 2 * η
    · calc (chenf 4 - 3 * η) * S₀
          ≤ (1 - η) * (chenf 4 - 2 * η) * S₀ := by
            have : (chenf 4 - 3 * η) ≤ (1 - η) * (chenf 4 - 2 * η) := by nlinarith only [hf4_le, hη_pos]
            exact mul_le_mul_of_nonneg_right this hS0_pos.le
        _ = (1 - η) * S₀ * (chenf 4 - 2 * η) := by ring
        _ ≤ X_A * V₈ * (chenf 4 - 2 * η) := mul_le_mul_of_nonneg_right hXV_ge hpos
        _ ≤ X_A * V₈ * (chenf (Real.log D₁₂ / Real.log z₈) - η) :=
            mul_le_mul_of_nonneg_left hcoef_le (mul_nonneg hXA_nn hV8_pos.le)
    · push Not at hpos
      have hXV_le : X_A * V₈ ≤ (1 + η) * S₀ := by
        have h1 := mul_le_mul_of_nonneg_right hXA_hi hV8_pos.le
        rw [hS0_def]; linarith only [h1]
      have h1 : (1 + η) * S₀ * (chenf 4 - 2 * η) ≤ X_A * V₈ * (chenf 4 - 2 * η) :=
        mul_le_mul_of_nonpos_right hXV_le hpos.le
      have h2 : (chenf 4 - 3 * η) * S₀ ≤ (1 + η) * S₀ * (chenf 4 - 2 * η) := by
        have : chenf 4 - 3 * η ≤ (1 + η) * (chenf 4 - 2 * η) := by nlinarith only [hf4_nn, hη_pos, hη_le]
        have hmul := mul_le_mul_of_nonneg_right this hS0_pos.le
        linarith only [hmul]
      exact (h2.trans h1).trans (mul_le_mul_of_nonneg_left hcoef_le (mul_nonneg hXA_nn hV8_pos.le))
  have hT1_bound :
      (chenf 4 - 3 * η) * S₀ - C₁ * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 ≤
        (siftedCard (chenGoldbachSet N) z₈ : ℝ) := by
    linarith only [hT1_raw, hR1_le, hT1_main]

  -- =========================================================================
  -- TERM 2: Upper bound on `∑_{q ∈ chenMidPrimes N} S(A_q, P(N^{1/8}))`
  -- =========================================================================
  have hT2_each : ∀ q ∈ chenMidPrimes N,
      (siftedCard (chenGoldbachSetDiv N q) z₈ : ℝ) ≤
        (X_A / ((q : ℝ) - 1)) * V₈ * (chenF (Real.log (D₁₂ / (q : ℝ)) / Real.log z₈) + η) +
          ∑ d ∈ (Finset.range (⌊D₁₂ / (q : ℝ)⌋₊ + 1)).filter
              (fun d : ℕ => Squarefree d ∧ (d : ℝ) < D₁₂ / (q : ℝ) ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < z₈),
            |(((chenGoldbachSetDiv N q).filter (fun a => d ∣ a)).card : ℝ) -
              (X_A / ((q : ℝ) - 1)) * multDensity ω d| := by
    intro q hq
    rw [chenMidPrimes, Finset.mem_filter] at hq
    rcases hq with ⟨_, hq_prime, _, _, hq_lt_y⟩
    have hq_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_prime.two_le
    have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
    have hXq_nn : 0 ≤ X_A / ((q : ℝ) - 1) := div_nonneg hXA_nn (by linarith)
    have hz8_le_Dq : z₈ ≤ D₁₂ / (q : ℝ) := by
      rw [hD12_def, le_div_iff₀ hq_pos, le_div_iff₀ hlogB12_pos, hz8_def, hsqrt_eq]
      calc (N : ℝ) ^ ((1 : ℝ) / 8) * (q : ℝ) * (Real.log (N : ℝ)) ^ B₁₂
          ≤ (N : ℝ) ^ ((1 : ℝ) / 8) * (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 24) := by
            have h1 : (N : ℝ) ^ ((1 : ℝ) / 8) * (q : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) * (N : ℝ) ^ ((1 : ℝ) / 3) :=
              mul_le_mul_of_nonneg_left hq_lt_y.le (Real.rpow_nonneg hN_pos.le _)
            exact mul_le_mul h1 hlogB12_le hlogB12_pos.le (by positivity)
        _ = (N : ℝ) ^ ((1 : ℝ) / 8 + 1 / 3 + 1 / 24) := by
            rw [← Real.rpow_add hN_pos, ← Real.rpow_add hN_pos]
        _ = (N : ℝ) ^ ((1 : ℝ) / 2) := by norm_num
    exact hSieveUp ω hω (chenGoldbachSetDiv N q) (X_A / ((q : ℝ) - 1)) (D₁₂ / (q : ℝ)) z₈
      hXq_nn hz8_ge_z0 hz8_le_Dq
  have hT2_sum_raw := Finset.sum_le_sum hT2_each
  rw [Finset.sum_add_distrib] at hT2_sum_raw
  have hR2_le :
      ∑ q ∈ chenMidPrimes N,
        ∑ d ∈ (Finset.range (⌊D₁₂ / (q : ℝ)⌋₊ + 1)).filter
            (fun d : ℕ => Squarefree d ∧ (d : ℝ) < D₁₂ / (q : ℝ) ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < z₈),
          |(((chenGoldbachSetDiv N q).filter (fun a => d ∣ a)).card : ℝ) -
            (X_A / ((q : ℝ) - 1)) * multDensity ω d| ≤
      C₂ * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
    have h1 : ∀ q ∈ chenMidPrimes N,
        ∑ d ∈ (Finset.range (⌊D₁₂ / (q : ℝ)⌋₊ + 1)).filter
            (fun d : ℕ => Squarefree d ∧ (d : ℝ) < D₁₂ / (q : ℝ) ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < z₈),
          |(((chenGoldbachSetDiv N q).filter (fun a => d ∣ a)).card : ℝ) -
            (X_A / ((q : ℝ) - 1)) * multDensity ω d| ≤
        ∑ d ∈ (Finset.range (⌊D₁₂ / (q : ℝ)⌋₊ + 1)).filter
            (fun d : ℕ => Squarefree d ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < z₈),
          |((((chenGoldbachSet N).filter (q ∣ ·)).filter (d ∣ ·)).card : ℝ) -
            (X_A / ((q : ℝ) - 1)) * multDensity ω d| := by
      intro q _
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) (fun d _ _ => abs_nonneg _)
      rw [Finset.mem_filter] at hd ⊢
      exact ⟨hd.1, hd.2.1, hd.2.2.2⟩
    have haq := hRemAq B₁₂ (le_max_right _ _) N hN4 hEven
    rw [show (Real.log (N : ℝ)) ^ (3 : ℝ) = (Real.log (N : ℝ)) ^ (3 : ℕ) by
      exact_mod_cast Real.rpow_natCast (Real.log (N : ℝ)) 3] at haq
    exact (Finset.sum_le_sum h1).trans haq
  -- Bound the main sum `∑ (X_A / (q - 1)) * V₈ * (chenF (...) + η)`
  have hT2_F_sum :
      ∑ q ∈ chenMidPrimes N, chenF (Real.log (D₁₂ / (q : ℝ)) / Real.log z₈) / ((q : ℝ) - 1) ≤
        I_T2 + η := hT2_int N hN_T2_le
  have hT2_one_sum :
      ∑ q ∈ chenMidPrimes N, (1 : ℝ) / ((q : ℝ) - 1) ≤ 3 := by
    have h1 := hT2_one N hN_T2_one_le
    -- `∫_{1/8}^{1/3} (1 / u) du = log (1/3) - log (1/8) = log (8/3) < 2`, so `≤ 3`!
    have hint : ∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), (1 : ℝ) / u ≤ 2 := by
      calc ∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), (1 : ℝ) / u
          ≤ ∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), (8 : ℝ) := by
            refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const fun u hu => ?_
            · exact ContinuousOn.intervalIntegrable (continuousOn_const.div continuousOn_id fun x hx => by
                rw [Set.uIcc_of_le (by norm_num)] at hx; linarith [hx.1])
            · rw [div_le_iff₀ (by linarith [hu.1])]; linarith [hu.1]
        _ = 8 * (1 / 3 - 1 / 8) := by simp; ring
        _ ≤ 2 := by norm_num
    change ∑ q ∈ chenMidPrimes N, (1 : ℝ) / ((q : ℝ) - 1) ≤ (∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), (1 : ℝ) / u) + 1 at h1
    linarith only [h1, hint]
  have hT2_main_eq :
      ∑ q ∈ chenMidPrimes N,
        (X_A / ((q : ℝ) - 1)) * V₈ * (chenF (Real.log (D₁₂ / (q : ℝ)) / Real.log z₈) + η) =
      X_A * V₈ * (∑ q ∈ chenMidPrimes N, chenF (Real.log (D₁₂ / (q : ℝ)) / Real.log z₈) / ((q : ℝ) - 1)
        + η * ∑ q ∈ chenMidPrimes N, (1 : ℝ) / ((q : ℝ) - 1)) := by
    rw [mul_add, Finset.mul_sum, ← mul_assoc (X_A * V₈) η, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => by ring
  have hT2_main_le :
      ∑ q ∈ chenMidPrimes N,
        (X_A / ((q : ℝ) - 1)) * V₈ * (chenF (Real.log (D₁₂ / (q : ℝ)) / Real.log z₈) + η) ≤
      (1 + η) * (I_T2 + 4 * η) * S₀ := by
    rw [hT2_main_eq]
    have hinner : ∑ q ∈ chenMidPrimes N, chenF (Real.log (D₁₂ / (q : ℝ)) / Real.log z₈) / ((q : ℝ) - 1)
        + η * ∑ q ∈ chenMidPrimes N, (1 : ℝ) / ((q : ℝ) - 1) ≤ I_T2 + 4 * η := by
      linarith [mul_le_mul_of_nonneg_left hT2_one_sum hη_pos.le]
    have hXV_le : X_A * V₈ ≤ (1 + η) * S₀ := by
      rw [hS0_def]; nlinarith [mul_le_mul_of_nonneg_right hXA_hi hV8_pos.le]
    have hsum_nn : 0 ≤ I_T2 + 4 * η := by positivity
    calc X_A * V₈ * _ ≤ X_A * V₈ * (I_T2 + 4 * η) :=
          mul_le_mul_of_nonneg_left hinner (mul_nonneg hXA_nn hV8_pos.le)
      _ ≤ (1 + η) * S₀ * (I_T2 + 4 * η) := mul_le_mul_of_nonneg_right hXV_le hsum_nn
      _ = (1 + η) * (I_T2 + 4 * η) * S₀ := by ring
  have hT2_bound :
      ∑ q ∈ chenMidPrimes N, (siftedCard (chenGoldbachSetDiv N q) z₈ : ℝ) ≤
        (1 + η) * (I_T2 + 4 * η) * S₀ + C₂ * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
    linarith

  -- =========================================================================
  -- TERM 3: Upper bound on `S(chenSwitchedSet N, P(N^{1/4}))`
  -- =========================================================================
  set X_M : ℝ := ((chenMProd N).card : ℝ) with hXM_def
  have hXM_nn : 0 ≤ X_M := by positivity
  have hT3_raw := hSieveUp ω hω (chenSwitchedSet N) X_M D₃ z₄ hXM_nn hz4_ge_z0 hz4_le_D3
  have hR3_le :
      ∑ d ∈ (Finset.range (⌊D₃⌋₊ + 1)).filter
          (fun d : ℕ => Squarefree d ∧ (d : ℝ) < D₃ ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < z₄),
        |(((chenSwitchedSet N).filter (fun b => d ∣ b)).card : ℝ) - X_M * multDensity ω d| ≤
      C₃ * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
    have hb := hRemB N hN4
    rw [show (Real.log (N : ℝ)) ^ (3 : ℝ) = (Real.log (N : ℝ)) ^ (3 : ℕ) by
      exact_mod_cast Real.rpow_natCast (Real.log (N : ℝ)) 3] at hb
    exact (chenSwitchedSet_remainder_le hEven).trans hb
  -- Bound `X_M ≤ (chenIB + η) * (N / log N)` and `V₄ ≤ (1 / 2 + η) * V₈`
  have hXM_le : X_M ≤ (chenIB + η) * ((N : ℝ) / Real.log (N : ℝ)) := by
    rw [hXM_def, card_chenMProd_eq]
    exact hM_upper N hN_M_le
  have hV4_le : V₄ ≤ (1 / 2 + η) * V₈ := by
    have hr := hV_rat N hN_rat_le z₈ z₄ le_rfl hz8_le_z4
    rw [hlog_z8, hlog_z4] at hr
    have hratio : ((1 / 8 : ℝ) * Real.log (N : ℝ)) / ((1 / 4 : ℝ) * Real.log (N : ℝ)) = 1 / 2 := by
      field_simp [hL_pos.ne']; ring
    rw [hratio] at hr
    have h1 : V₄ / V₈ ≤ 1 / 2 + η * (1 / 2) := by linarith [(abs_le.mp hr).2]
    have h2 : V₄ / V₈ ≤ 1 / 2 + η := by linarith
    exact (div_le_iff₀ hV8_pos).mp h2
  have hT3_main_le :
      X_M * V₄ * (chenF (Real.log D₃ / Real.log z₄) + η) ≤
        (chenIB + η) * (1 / 2 + η) * (chenF 2 + 2 * η) * S₀ := by
    have hF_bd : chenF (Real.log D₃ / Real.log z₄) + η ≤ chenF 2 + 2 * η := by linarith
    have hV4_nn : 0 ≤ V₄ := (siftProd_chenPrimeDensity_pos N z₄).le
    have hXM_V4 : X_M * V₄ ≤ (chenIB + η) * (1 / 2 + η) * S₀ := by
      calc X_M * V₄
          ≤ ((chenIB + η) * ((N : ℝ) / Real.log (N : ℝ))) * ((1 / 2 + η) * V₈) :=
            mul_le_mul hXM_le hV4_le hV4_nn (by positivity)
        _ = (chenIB + η) * (1 / 2 + η) * S₀ := by rw [hS0_def]; ring
    calc X_M * V₄ * (chenF (Real.log D₃ / Real.log z₄) + η)
        ≤ X_M * V₄ * (chenF 2 + 2 * η) := mul_le_mul_of_nonneg_left hF_bd (mul_nonneg hXM_nn hV4_nn)
      _ ≤ (chenIB + η) * (1 / 2 + η) * S₀ * (chenF 2 + 2 * η) :=
          mul_le_mul_of_nonneg_right hXM_V4 (by positivity)
      _ = (chenIB + η) * (1 / 2 + η) * (chenF 2 + 2 * η) * S₀ := by ring
  have hT3_bound :
      (siftedCard (chenSwitchedSet N) z₄ : ℝ) ≤
        (chenIB + η) * (1 / 2 + η) * (chenF 2 + 2 * η) * S₀ + C₃ * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
    linarith

  -- =========================================================================
  -- COMBINE ALL THREE TERMS + REMAINDERS + `O(N^{7/8})` ERRORS!
  -- =========================================================================
  -- 1. Show all `O(N^{7/8})` combinatorial errors are `≤ 5 * N / (log N)^3`
  have hsub_err : 2 * (N : ℝ) ^ ((7 : ℝ) / 8) + (1 / 2 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 4) + 2 ≤
      5 * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
    have h14_le : (N : ℝ) ^ ((1 : ℝ) / 4) ≤ (N : ℝ) ^ ((7 : ℝ) / 8) :=
      Real.rpow_le_rpow_of_exponent_le hN_gt1.le (by norm_num)
    have h1_le : (1 : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 8) :=
      Real.one_le_rpow hN_gt1.le (by norm_num)
    have h78 : (7 : ℝ) / 8 = 1 - 1 / 8 := by norm_num
    have hsub := hN_sub78 N hN_sub78_le
    rw [← h78] at hsub
    have : 2 * (N : ℝ) ^ ((7 : ℝ) / 8) + (1 / 2 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 4) + 2 ≤
        5 * (N : ℝ) ^ ((7 : ℝ) / 8) := by linarith
    have hrew : 5 * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 = 5 * ((N : ℝ) / (Real.log (N : ℝ)) ^ 3) := by ring
    linarith
  -- 2. Show total remainder `C_tot * N / (log N)^3 ≤ (M / 20) * S₀`
  have hrem_tot : C_tot * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 ≤ (M / 20) * S₀ := by
    have hdiv := hN_rem N hN_rem_le
    have hmul : C_tot / c_V / Real.log (N : ℝ) * (c_V * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) =
        C_tot * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
      field_simp [hcV_pos.ne', hL_pos.ne']
    calc C_tot * (N : ℝ) / (Real.log (N : ℝ)) ^ 3
        = (C_tot / c_V / Real.log (N : ℝ)) * (c_V * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) := hmul.symm
      _ ≤ (M / 20) * (c_V * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_right hdiv.le (by positivity)
      _ ≤ (M / 20) * S₀ := mul_le_mul_of_nonneg_left hS0_ge (by positivity)
  -- 3. Algebraic coefficient margin check:
  --    `(chenf 4 - 3*η) - (1/2)*(1+η)*(I_T2 + 4*η) - (1/2)*(chenIB + η)*(1/2 + η)*(chenF 2 + 2*η) - M/20 ≥ M/2`
  have hcoef_pos :
      M / 2 ≤ (chenf 4 - 3 * η)
        - (1 / 2 : ℝ) * ((1 + η) * (I_T2 + 4 * η))
        - (1 / 2 : ℝ) * ((chenIB + η) * (1 / 2 + η) * (chenF 2 + 2 * η))
        - M / 20 := by
    have hT2_err : (1 / 2 : ℝ) * ((1 + η) * (I_T2 + 4 * η)) - (1 / 2 : ℝ) * I_T2 ≤
        η * (I_T2 / 2 + 3) := by
      have h1 : (1 / 2 : ℝ) * ((1 + η) * (I_T2 + 4 * η)) - (1 / 2 : ℝ) * I_T2 =
          η * (I_T2 / 2 + 2 + 2 * η) := by ring
      rw [h1]
      nlinarith only [hη_pos, hη_le]
    have hT3_err : (1 / 2 : ℝ) * ((chenIB + η) * (1 / 2 + η) * (chenF 2 + 2 * η))
        - (1 / 4 : ℝ) * chenIB * chenF 2 ≤ η * (chenF 2 + 2 * chenIB + 2) := by
      have hexp : (1 / 2 : ℝ) * ((chenIB + η) * (1 / 2 + η) * (chenF 2 + 2 * η))
          - (1 / 4 : ℝ) * chenIB * chenF 2 =
          η * (chenIB * chenF 2 / 2 + chenIB / 2 + chenF 2 / 4 +
               η * (chenIB + chenF 2 / 2 + 1 / 2) + η ^ 2) := by ring
      rw [hexp]
      refine mul_le_mul_of_nonneg_left ?_ hη_pos.le
      nlinarith only [hIB_nn, hIB_lt, hF2_pos, hη_pos, hη_le]
    have hsum_err :
        3 * η + η * (I_T2 / 2 + 3) + η * (chenF 2 + 2 * chenIB + 2) ≤ η * W := by
      rw [hW_def]
      nlinarith only [hη_pos, hIT2_nn, hF2_pos, hIB_nn]
    linarith only [hmargin, hηW, hT2_err, hT3_err, hsum_err, hM_pos]

  have hcomb := chen_weighted_sieve_inequality hN256
  have hfinal : (M / 2) * S₀ ≤ (chenP2Count N : ℝ) := by
    have hC_split :
        C_tot * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 =
          C₁ * (N : ℝ) / (Real.log (N : ℝ)) ^ 3
            + (1 / 2 : ℝ) * (C₂ * (N : ℝ) / (Real.log (N : ℝ)) ^ 3)
            + (1 / 2 : ℝ) * (C₃ * (N : ℝ) / (Real.log (N : ℝ)) ^ 3)
            + 5 * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
      rw [hCtot_def]; ring
    have h1 :
        ((chenf 4 - 3 * η) - (1 / 2 : ℝ) * ((1 + η) * (I_T2 + 4 * η))
          - (1 / 2 : ℝ) * ((chenIB + η) * (1 / 2 + η) * (chenF 2 + 2 * η))) * S₀
          - C_tot * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 ≤
        (chenP2Count N : ℝ) := by
      linarith only [hcomb, hT1_bound, hT2_bound, hT3_bound, hsub_err, hC_split]
    have h2 : (M / 2) * S₀ ≤
        ((chenf 4 - 3 * η) - (1 / 2 : ℝ) * ((1 + η) * (I_T2 + 4 * η))
          - (1 / 2 : ℝ) * ((chenIB + η) * (1 / 2 + η) * (chenF 2 + 2 * η)) - M / 20) * S₀ :=
      mul_le_mul_of_nonneg_right hcoef_pos hS0_pos.le
    linarith only [h1, h2, hrem_tot]
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < (M / 2) * S₀) hfinal

/-- **CHEN'S THEOREM (1973)** — 100% Unconditional, Native-Mathlib Statement:
There exists `N₀ : ℕ` such that every even integer `n ≥ N₀` can be written as `n = p + q`
where `p` is prime and `q` is either prime or the product of two primes (`P₂`). -/
theorem chen_theorem :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧
        (Nat.Prime q ∨ ∃ r s : ℕ, Nat.Prime r ∧ Nat.Prime s ∧ q = r * s) ∧
        p + q = n := by
  obtain ⟨N₀, hN₀⟩ := chenP2Count_pos_eventually
  exact ⟨N₀, fun n hn hEven => exists_prime_add_isP2_of_pos (hN₀ n hn hEven)⟩

#print axioms chen_theorem

end RHDirect.Chen
