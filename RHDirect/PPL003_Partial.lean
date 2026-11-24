import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# PPL 003 (Erdős Problem #50 — Schoenberg `φ(n)/n` Density Derivative) — Partial Real-Analysis, Number-Theoretic & Toy-Dichotomy Milestone

**Honest Scope Notice (PPL 003 / Erdős #50 REMAINS OPEN):**
- **PPL 003 (Erdős #50, $250):** Schoenberg proved the natural density `f(c) = dens {n : φ(n) < c * n}` exists on `[0, 1]`, and Erdős (1939) proved `f` is purely singular (`f'(x) = 0` a.e.). Whether there exists any `x ∈ (0, 1)` where `f'(x)` exists and is strictly positive remains **OPEN**.
- This file formalizes the unconditionally proved number-theoretic, Diophantine-exclusion, real-analysis linearity-equivalence, and infinite-convolution toy-dichotomy theorems from `scripts/ppl003_findings.md` using **pure Mathlib signatures only** (`0` custom or `private` definitions in any public theorem signature).

## Verified Theorems
1. `ppl003_smooth_totient_prob_identity`: Exact `S`-smooth squarefree probability normalization `(∏ p ∈ S, (1 - 1 / p)) * ∑_{m sqfree, S-smooth} 1 / φ(m) = 1` over both `S.powerset` and the explicit filtered integer set `(Finset.Icc 1 (∏ p ∈ S, p)).filter ...`.
2. `ppl003_change_of_variables_equiv`: Smooth diffeomorphism equivalence `HasDerivAt f α x ↔ HasDerivAt (fun t => 1 - f (Real.exp (-t))) (x * α) (-Real.log x)` for `x ∈ (0, 1)`.
3. `ppl003_diophantine_spike_exclusion`: Sharp Diophantine exclusion lemma — any `H` differentiable at `t` experiencing uniform logarithmic spikes `c₀ / (m_k * log(2 / ε))` at `t_k → t` (`t_k ≠ t`) forces `1 / (m_k * |t - t_k| * log(2 / |t - t_k|)) → 0`.
4. `ppl003_linearity_equivalence`: Exact nested-interval local-linearity equivalence for `HasDerivAt H β t` (`β > 0`) via bounded-margin intervals `I_k = [a_k, b_k]` with `L_β(I_k) → 0` and `L_β(I_k) / (|I_{k+1}| / |I_k|) → 0`.
5. `ppl003_dyadic_lattice_impossibility`: Unconditional no-go theorem for lattice-style monotone CDFs satisfying `F(b) - F((a+b)/2) ≤ (C / n) * (F((a+b)/2) - F(a))` on every dyadic interval `[k/2^n, (k+1)/2^n]` (`n ≥ 1`): no `x ∈ (0, 1)` can have `HasDerivAt F β x` with `β > 0`.
6. `ppl003_kakutani_vanishing_step_positive_deriv`: Explicit construction of the Kakutani vanishing-step dyadic product CDF `F` with weights `q_j = 1/2 + 1 / (4 * √(j + 1))` (`∑ (q_j - 1/2)^2 = ∞`), proving `Monotone F`, `F 0 = 0`, `F 1 = 1`, exact dyadic cylinder weights on every `[m/2^n, (m+1)/2^n]`, and `∀ β > 0, ∃ x ∈ (0, 1), HasDerivAt F β x`.
-/

private lemma hasDerivAt_eps_bound {H : ℝ → ℝ} {β t δ : ℝ}
    (hderiv : HasDerivAt H β t) (hδ : 0 < δ) :
    ∃ ρ > 0, ∀ y : ℝ, |y - t| < ρ → |H y - H t - β * (y - t)| ≤ δ * |y - t| := by
  obtain ⟨ρ, hρ_pos, hρ⟩ := Metric.tendsto_nhdsWithin_nhds.mp hderiv.tendsto_slope_zero δ hδ
  refine ⟨ρ, hρ_pos, fun y hy => ?_⟩
  by_cases heq : y = t
  · rw [heq]; simp
  · have hne : y - t ≠ 0 := sub_ne_zero.mpr heq
    have hmem : y - t ∈ ({0}ᶜ : Set ℝ) := hne
    have hdist : dist (y - t) 0 < ρ := by simpa [Real.dist_eq] using hy
    have hs := hρ hmem hdist
    rw [Real.dist_eq, smul_eq_mul, add_sub_cancel] at hs
    have hmul := mul_le_mul_of_nonneg_right hs.le (abs_nonneg (y - t))
    rw [← abs_mul, sub_mul, inv_mul_eq_div, div_mul_cancel₀ _ hne] at hmul
    exact hmul

private lemma hasDerivAt_of_eps_bound {H : ℝ → ℝ} {β t : ℝ}
    (hbound : ∀ δ > 0, ∃ ρ > 0, ∀ y : ℝ, |y - t| < ρ →
      |H y - H t - β * (y - t)| ≤ δ * |y - t|) :
    HasDerivAt H β t := by
  rw [hasDerivAt_iff_tendsto_slope_zero, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨ρ, hρ_pos, hρ⟩ := hbound (ε / 2) (by positivity)
  refine ⟨ρ, hρ_pos, fun {z} hz hdist => ?_⟩
  have hzne : z ≠ 0 := hz
  have hz_abs : |t + z - t| < ρ := by
    rw [add_sub_cancel_left]
    simpa [Real.dist_eq] using hdist
  have hle := hρ (t + z) hz_abs
  rw [add_sub_cancel_left] at hle
  have hz_pos : 0 < |z| := abs_pos.mpr hzne
  rw [Real.dist_eq, smul_eq_mul]
  have hdiv : |z⁻¹ * (H (t + z) - H t) - β| ≤ ε / 2 := by
    rw [← div_le_iff₀ hz_pos, ← abs_div] at hle
    have hid : z⁻¹ * (H (t + z) - H t) - β = (H (t + z) - H t - β * z) / z := by
      field_simp
    rwa [hid]
  linarith

private lemma coprime_prime_prod_of_not_mem
    (q : ℕ) (hq : Nat.Prime q) (d : Finset ℕ) (hd : ∀ p ∈ d, Nat.Prime p) (hqd : q ∉ d) :
    Nat.Coprime q (∏ p ∈ d, p) := by
  rw [hq.coprime_iff_not_dvd]
  intro hdvd
  rw [hq.prime.dvd_finsetProd_iff] at hdvd
  rcases hdvd with ⟨p, hpd, hqp⟩
  have hp := hd p hpd
  exact hqd (((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp) ▸ hpd)

private lemma squarefree_and_totient_prod
    (d : Finset ℕ) (hd : ∀ p ∈ d, Nat.Prime p) :
    Squarefree (∏ p ∈ d, p) ∧ Nat.totient (∏ p ∈ d, p) = ∏ p ∈ d, (p - 1) := by
  classical
  induction d using Finset.induction_on with
  | empty => simp
  | @insert q d' hqd' ih =>
    have hq : Nat.Prime q := hd q (Finset.mem_insert_self q d')
    have hd' : ∀ p ∈ d', Nat.Prime p := fun p hp => hd p (Finset.mem_insert_of_mem hp)
    obtain ⟨hsq, htot⟩ := ih hd'
    have hcop := coprime_prime_prod_of_not_mem q hq d' hd' hqd'
    rw [Finset.prod_insert hqd', Finset.prod_insert hqd']
    refine ⟨?_, ?_⟩
    · exact Nat.squarefree_mul_iff.mpr ⟨hcop, hq.squarefree, hsq⟩
    · rw [Nat.totient_mul hcop, Nat.totient_prime hq, htot]

private lemma prod_filter_dvd_eq_self
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    ∀ m : ℕ, 1 ≤ m → Squarefree m → (∀ p : ℕ, Nat.Prime p → p ∣ m → p ∈ S) →
      ∏ p ∈ S.filter (fun p => p ∣ m), p = m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm1 hsq hmem
    rcases eq_or_lt_of_le hm1 with rfl | hmgt
    · have hfilt : S.filter (fun p => p ∣ 1) = ∅ := by
        ext p
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
        rintro ⟨hpS, hp1⟩
        exact (hS p hpS).ne_one (Nat.eq_one_of_dvd_one hp1)
      rw [hfilt, Finset.prod_empty]
    · have hne1 : m ≠ 1 := Nat.ne_of_gt hmgt
      let q := Nat.minFac m
      have hq : Nat.Prime q := Nat.minFac_prime hne1
      have hqm : q ∣ m := Nat.minFac_dvd m
      have hqS : q ∈ S := hmem q hq hqm
      let m' := m / q
      have hm_eq : q * m' = m := Nat.mul_div_cancel' hqm
      have hm'1 : 1 ≤ m' := Nat.div_pos (Nat.le_of_dvd (by omega) hqm) hq.pos
      have hm'lt : m' < m := Nat.div_lt_self (by omega) hq.one_lt
      have hq_not_dvd : ¬ q ∣ m' := by
        intro hq'
        have hqq : q * q ∣ m := by
          rw [← hm_eq]
          exact mul_dvd_mul_left q hq'
        have hq1 := hsq q hqq
        exact hq.ne_one (Nat.isUnit_iff.mp hq1)
      have hsq' : Squarefree m' := hsq.squarefree_of_dvd ⟨q, by rw [← hm_eq, mul_comm]⟩
      have hmem' : ∀ p : ℕ, Nat.Prime p → p ∣ m' → p ∈ S := by
        intro p hp hpm'
        exact hmem p hp (dvd_trans hpm' ⟨q, by rw [← hm_eq, mul_comm]⟩)
      have ih' := ih m' hm'lt hm'1 hsq' hmem'
      have hfilt_eq : S.filter (fun p => p ∣ m) = insert q (S.filter (fun p => p ∣ m')) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hpS, hpm⟩
          have hp : Nat.Prime p := hS p hpS
          rw [← hm_eq, hp.dvd_mul] at hpm
          rcases hpm with hpq | hpm'
          · left; exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
          · right; exact ⟨hpS, hpm'⟩
        · rintro (rfl | ⟨hpS, hpm'⟩)
          · exact ⟨hqS, hqm⟩
          · exact ⟨hpS, dvd_trans hpm' ⟨q, by rw [← hm_eq, mul_comm]⟩⟩
      have hq_not_mem : q ∉ S.filter (fun p => p ∣ m') := by
        simp only [Finset.mem_filter]
        exact fun ⟨_, h⟩ => hq_not_dvd h
      rw [hfilt_eq, Finset.prod_insert hq_not_mem, ih', hm_eq]

open Classical in
theorem ppl003_smooth_totient_prob_identity
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    (∏ p ∈ S, (1 - 1 / (p : ℝ))) *
        (∑ d ∈ S.powerset, (1 / (Nat.totient (∏ p ∈ d, p) : ℝ))) = 1 ∧
    (∏ p ∈ S, (1 - 1 / (p : ℝ))) *
        (∑ m ∈ (Finset.Icc 1 (∏ p ∈ S, p)).filter
            (fun m => (∀ a ∈ Finset.Icc 2 m, ¬ (a * a ∣ m)) ∧
              ∀ p ∈ Finset.Icc 2 m, Nat.Prime p → p ∣ m → p ∈ S),
          (1 / (Nat.totient m : ℝ))) = 1 := by
  have hpow :
      (∑ d ∈ S.powerset, (1 / (Nat.totient (∏ p ∈ d, p) : ℝ))) =
        ∏ p ∈ S, (1 + 1 / ((p - 1 : ℕ) : ℝ)) := by
    have hterm :
        (∑ d ∈ S.powerset, (1 / (Nat.totient (∏ p ∈ d, p) : ℝ))) =
          ∑ d ∈ S.powerset, ∏ p ∈ d, (1 / ((p - 1 : ℕ) : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hd' : ∀ p ∈ d, Nat.Prime p := fun p hp => hS p (Finset.mem_powerset.mp hd hp)
      rw [(squarefree_and_totient_prod d hd').2, Nat.cast_prod]
      simp only [one_div, Finset.prod_inv_distrib]
    rw [hterm, ← Finset.prod_one_add]
  have hid1 :
      (∏ p ∈ S, (1 - 1 / (p : ℝ))) *
          (∑ d ∈ S.powerset, (1 / (Nat.totient (∏ p ∈ d, p) : ℝ))) = 1 := by
    rw [hpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one ?_
    intro p hp
    have hp_prime := hS p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
    have hpm1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp_prime.one_lt.le, Nat.cast_one]
    have hp_ne : (p : ℝ) ≠ 0 := by linarith
    have hp1_ne : (p : ℝ) - 1 ≠ 0 := by linarith
    rw [hpm1]
    field_simp [hp_ne, hp1_ne]
    ring
  refine ⟨hid1, ?_⟩
  classical
  have hsum_eq :
      (∑ d ∈ S.powerset, (1 / (Nat.totient (∏ p ∈ d, p) : ℝ))) =
        ∑ m ∈ (Finset.Icc 1 (∏ p ∈ S, p)).filter
            (fun m => (∀ a ∈ Finset.Icc 2 m, ¬ (a * a ∣ m)) ∧
              ∀ p ∈ Finset.Icc 2 m, Nat.Prime p → p ∣ m → p ∈ S),
          (1 / (Nat.totient m : ℝ)) := by
    refine Finset.sum_bij (fun d _ => ∏ p ∈ d, p) ?_ ?_ ?_ ?_
    · intro d hd
      have hdS : d ⊆ S := Finset.mem_powerset.mp hd
      have hd' : ∀ p ∈ d, Nat.Prime p := fun p hp => hS p (hdS hp)
      have hsq := (squarefree_and_totient_prod d hd').1
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Finset.one_le_prod' fun p hp => (hd' p hp).pos,
          Finset.prod_le_prod_of_subset_of_one_le' hdS fun p hp _ => (hS p hp).pos⟩, ?_, ?_⟩
      · intro a ha haa
        have hu := hsq a haa
        have ha1 := Nat.isUnit_iff.mp hu
        omega
      · intro p _ hp hpdvd
        rw [hp.prime.dvd_finsetProd_iff] at hpdvd
        rcases hpdvd with ⟨q, hqd, hpq⟩
        have hqp : p = q := (Nat.prime_dvd_prime_iff_eq hp (hd' q hqd)).mp hpq
        exact hdS (hqp ▸ hqd)
    · intro d1 hd1 d2 hd2 heq
      have hd1S := Finset.mem_powerset.mp hd1
      have hd2S := Finset.mem_powerset.mp hd2
      ext p
      constructor
      · intro hp1
        have hp := hS p (hd1S hp1)
        have hdvd : p ∣ ∏ q ∈ d2, q := heq ▸ Finset.dvd_prod_of_mem _ hp1
        rw [hp.prime.dvd_finsetProd_iff] at hdvd
        rcases hdvd with ⟨q, hqd2, hpq⟩
        exact ((Nat.prime_dvd_prime_iff_eq hp (hS q (hd2S hqd2))).mp hpq) ▸ hqd2
      · intro hp2
        have hp := hS p (hd2S hp2)
        have hdvd : p ∣ ∏ q ∈ d1, q := heq.symm ▸ Finset.dvd_prod_of_mem _ hp2
        rw [hp.prime.dvd_finsetProd_iff] at hdvd
        rcases hdvd with ⟨q, hqd1, hpq⟩
        exact ((Nat.prime_dvd_prime_iff_eq hp (hS q (hd1S hqd1))).mp hpq) ▸ hqd1
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_Icc] at hm
      have hsq_m : Squarefree m := by
        intro a haa
        have hm_pos : 0 < m := by omega
        have ha_le : a ≤ m := Nat.le_of_dvd hm_pos (dvd_trans ⟨a, rfl⟩ haa)
        have ha_pos : 0 < a := by
          by_contra ha0
          have ha0' : a = 0 := by omega
          rw [ha0', mul_zero] at haa
          omega
        by_cases ha1 : a = 1
        · subst ha1; exact isUnit_one
        · exfalso
          exact hm.2.1 a ⟨by omega, ha_le⟩ haa
      have hmem_m : ∀ p : ℕ, Nat.Prime p → p ∣ m → p ∈ S := by
        intro p hp hpm
        have hm_pos : 0 < m := by omega
        exact hm.2.2 p ⟨hp.two_le, Nat.le_of_dvd hm_pos hpm⟩ hp hpm
      refine ⟨S.filter (fun p => p ∣ m), Finset.mem_powerset.mpr (Finset.filter_subset _ S), ?_⟩
      exact prod_filter_dvd_eq_self S hS m hm.1.1 hsq_m hmem_m
    · intro _ _; rfl
  rw [← hsum_eq]
  exact hid1

theorem ppl003_change_of_variables_equiv
    (f : ℝ → ℝ) (x α : ℝ) (hx0 : 0 < x) (_hx1 : x < 1) :
    HasDerivAt f α x ↔
      HasDerivAt (fun t => 1 - f (Real.exp (-t))) (x * α) (-Real.log x) := by
  have hexp_log : Real.exp (-(-Real.log x)) = x := by
    rw [neg_neg, Real.exp_log hx0]
  constructor
  · intro hf
    have hneg : HasDerivAt (fun t : ℝ => -t) (-1) (-Real.log x) :=
      (hasDerivAt_id (-Real.log x)).neg
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (x * (-1)) (-Real.log x) := by
      have h := (Real.hasDerivAt_exp (-(-Real.log x))).comp (-Real.log x) hneg
      rw [neg_neg, Real.exp_log hx0] at h
      simpa [Function.comp_def] using h
    have hcomp : HasDerivAt (fun t : ℝ => f (Real.exp (-t))) (α * (x * (-1))) (-Real.log x) := by
      have hf' : HasDerivAt f α (Real.exp (-(-Real.log x))) := by rwa [hexp_log]
      simpa [Function.comp_def] using hf'.comp (-Real.log x) hexp
    have hsub : HasDerivAt (fun t : ℝ => 1 - f (Real.exp (-t))) (-(α * (x * (-1)))) (-Real.log x) :=
      hcomp.const_sub 1
    convert hsub using 1
    ring
  · intro hH
    let G : ℝ → ℝ := fun t => 1 - f (Real.exp (-t))
    have hG : HasDerivAt G (x * α) (-Real.log x) := hH
    have hlog : HasDerivAt (fun u : ℝ => -Real.log u) (-(x⁻¹)) x :=
      (Real.hasDerivAt_log hx0.ne').neg
    have hcomp : HasDerivAt (fun u : ℝ => G (-Real.log u)) ((x * α) * (-(x⁻¹))) x := by
      simpa [Function.comp_def] using hG.comp x hlog
    have hsub : HasDerivAt (fun u : ℝ => 1 - G (-Real.log u)) (-((x * α) * (-(x⁻¹)))) x :=
      hcomp.const_sub 1
    have hval : -((x * α) * (-(x⁻¹))) = α := by
      have hxne : x ≠ 0 := hx0.ne'
      field_simp
    rw [hval] at hsub
    refine hsub.congr_of_eventuallyEq ?_
    have hmem : Set.Ioi (0 : ℝ) ∈ nhds x := Ioi_mem_nhds hx0
    filter_upwards [hmem] with u hu
    dsimp [G]
    simp [Real.exp_log hu]

theorem ppl003_diophantine_spike_exclusion
    (H : ℝ → ℝ) (t β c₀ δ₀ : ℝ)
    (hc₀ : 0 < c₀) (hδ₀ : 0 < δ₀) (hmono : Monotone H) (hderiv : HasDerivAt H β t)
    (tseq : ℕ → ℝ) (mseq : ℕ → ℕ)
    (hm : ∀ k : ℕ, 1 ≤ mseq k)
    (ht_ne : ∀ k : ℕ, tseq k ≠ t)
    (ht_lim : Filter.Tendsto tseq Filter.atTop (nhds t))
    (hspike : ∀ k : ℕ, ∀ ε : ℝ, 0 < ε → ε < δ₀ →
      c₀ / ((mseq k : ℝ) * Real.log (2 / ε)) ≤ H (tseq k + ε) - H (tseq k)) :
    Filter.Tendsto
      (fun k => 1 / ((mseq k : ℝ) * |t - tseq k| * Real.log (2 / |t - tseq k|)))
      Filter.atTop (nhds 0) := by
  have hβ_nonneg : 0 ≤ β := by
    by_contra hβ
    push Not at hβ
    obtain ⟨ρ, hρ_pos, hρ⟩ := hasDerivAt_eps_bound hderiv (by linarith : 0 < -β / 2)
    have hpos_r : 0 < ρ / 2 := by positivity
    have hlt_r : |t + ρ / 2 - t| < ρ := by
      rw [add_sub_cancel_left, abs_of_pos hpos_r]
      linarith
    have hle := hρ (t + ρ / 2) hlt_r
    rw [add_sub_cancel_left, abs_of_pos hpos_r] at hle
    have hmono_y : 0 ≤ H (t + ρ / 2) - H t := sub_nonneg.mpr (hmono (by linarith))
    have h2 := (abs_le.mp hle).2
    have hmul_neg : β * (ρ / 2) < 0 := mul_neg_of_neg_of_pos hβ hpos_r
    have h_eq : β * (ρ / 2) + (-β / 2 * (ρ / 2)) = β * (ρ / 2) / 2 := by ring
    linarith
  rw [Metric.tendsto_atTop]
  intro η hη
  let r : ℝ := min (1 / 2) (c₀ * η / (4 * (β + 1)))
  have hr_pos : 0 < r := by positivity
  have hr_half : r ≤ 1 / 2 := min_le_left _ _
  have hr_bound : (2 / c₀) * (β * r) ≤ η / 2 := by
    have h1 : r ≤ c₀ * η / (4 * (β + 1)) := min_le_right _ _
    have h2 : β * r ≤ β * (c₀ * η / (4 * (β + 1))) := mul_le_mul_of_nonneg_left h1 hβ_nonneg
    have h3 : (2 / c₀) * (β * r) ≤ (2 / c₀) * (β * (c₀ * η / (4 * (β + 1)))) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : (2 / c₀) * (β * (c₀ * η / (4 * (β + 1)))) = (η / 2) * (β / (β + 1)) := by
      field_simp; ring
    have h5 : β / (β + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc
      (2 / c₀) * (β * r) ≤ (η / 2) * (β / (β + 1)) := by rw [← h4]; exact h3
      _ ≤ (η / 2) * 1 := mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = η / 2 := mul_one _
  let δ1 : ℝ := (c₀ * η) / 16
  have hδ1_pos : 0 < δ1 := by positivity
  have hδ1_bound : (2 / c₀) * ((2 + r) * δ1) < η / 2 := by
    have h2r : 2 + r ≤ 5 / 2 := by linarith
    have h1 : (2 / c₀) * ((2 + r) * δ1) ≤ (2 / c₀) * ((5 / 2) * δ1) := by gcongr
    have h2 : (2 / c₀) * ((5 / 2) * δ1) = 5 * η / 16 := by
      dsimp [δ1]; field_simp
    linarith
  obtain ⟨ρ, hρ_pos, hρ⟩ := hasDerivAt_eps_bound hderiv hδ1_pos
  let B := min (1 / 2) (min (δ₀ / (2 * r)) (min (ρ / (1 + r)) (2 * r)))
  have hB_pos : 0 < B := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht_lim B hB_pos
  refine ⟨N, fun k hk => ?_⟩
  have hdist_k : |tseq k - t| < B := by
    simpa [Real.dist_eq] using hN k hk
  set h : ℝ := |t - tseq k|
  have hh_pos : 0 < h := abs_pos.mpr (sub_ne_zero.mpr (ht_ne k).symm)
  have hh_lt_B : h < B := by simpa [h, abs_sub_comm] using hdist_k
  have hh_half : h < 1 / 2 := lt_of_lt_of_le hh_lt_B (min_le_left _ _)
  have hh_rδ : r * h < δ₀ := by
    have h1 : h < δ₀ / (2 * r) :=
      lt_of_lt_of_le hh_lt_B (le_trans (min_le_right _ _) (min_le_left _ _))
    have h2 : 2 * r * h < δ₀ := (lt_div_iff₀' (by positivity)).mp h1
    linarith
  have hh_ρ : (1 + r) * h < ρ := by
    have h1 : h < ρ / (1 + r) :=
      lt_of_lt_of_le hh_lt_B
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    exact (lt_div_iff₀' (by positivity)).mp h1
  have hh_2r : h < 2 * r :=
    lt_of_lt_of_le hh_lt_B
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hlog_h_pos : 0 < Real.log (2 / h) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hh_pos]
    linarith
  have hlog_rh_le : Real.log (2 / (r * h)) ≤ 2 * Real.log (2 / h) := by
    have hsplit : 2 / (r * h) = (2 / h) * (1 / r) := by field_simp
    rw [hsplit, Real.log_mul (by positivity) (by positivity)]
    have hcmp : Real.log (1 / r) ≤ Real.log (2 / h) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ hr_pos hh_pos]
      nlinarith
    linarith
  have hlog_rh_pos : 0 < Real.log (2 / (r * h)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hspike_k := hspike k (r * h) (by positivity) hh_rδ
  have hm_pos : (0 : ℝ) < (mseq k : ℝ) := by exact_mod_cast hm k
  have hlow : c₀ / (2 * (mseq k : ℝ) * Real.log (2 / h)) ≤ H (tseq k + r * h) - H (tseq k) := by
    have h1 : c₀ / (2 * (mseq k : ℝ) * Real.log (2 / h)) ≤
        c₀ / ((mseq k : ℝ) * Real.log (2 / (r * h))) := by
      apply div_le_div_of_nonneg_left hc₀.le (by positivity)
      calc
        (mseq k : ℝ) * Real.log (2 / (r * h)) ≤ (mseq k : ℝ) * (2 * Real.log (2 / h)) :=
          mul_le_mul_of_nonneg_left hlog_rh_le hm_pos.le
        _ = 2 * (mseq k : ℝ) * Real.log (2 / h) := by ring
    exact le_trans h1 hspike_k
  have hy1_est : |H (tseq k) - H t - β * (tseq k - t)| ≤ δ1 * h := by
    have hlt : |tseq k - t| < ρ := by
      have : |tseq k - t| = h := by simp [h, abs_sub_comm]
      rw [this]
      nlinarith
    have h1 := hρ (tseq k) hlt
    simpa [h, abs_sub_comm] using h1
  have hy2_est : |H (tseq k + r * h) - H t - β * (tseq k + r * h - t)| ≤ δ1 * ((1 + r) * h) := by
    have hle_sum : |tseq k + r * h - t| ≤ (1 + r) * h := by
      have htk : |tseq k - t| = h := by rw [abs_sub_comm]
      have hrh_pos : 0 < r * h := by positivity
      calc
        |tseq k + r * h - t| = |(tseq k - t) + r * h| := by ring_nf
        _ ≤ |tseq k - t| + |r * h| := abs_add_le _ _
        _ = h + r * h := by rw [htk, abs_of_pos hrh_pos]
        _ = (1 + r) * h := by ring
    have hlt : |tseq k + r * h - t| < ρ := lt_of_le_of_lt hle_sum hh_ρ
    exact le_trans (hρ (tseq k + r * h) hlt) (mul_le_mul_of_nonneg_left hle_sum hδ1_pos.le)
  have hup : H (tseq k + r * h) - H (tseq k) ≤ ((2 + r) * δ1 + β * r) * h := by
    have hid :
        H (tseq k + r * h) - H (tseq k) =
          (H (tseq k + r * h) - H t - β * (tseq k + r * h - t)) -
            (H (tseq k) - H t - β * (tseq k - t)) + β * (r * h) := by ring
    rw [hid]
    have h1 := (abs_le.mp hy2_est).2
    have h2 := (abs_le.mp hy1_est).1
    linarith
  have hcomb : c₀ / (2 * (mseq k : ℝ) * Real.log (2 / h)) ≤ ((2 + r) * δ1 + β * r) * h :=
    le_trans hlow hup
  have hval_pos : 0 < 1 / ((mseq k : ℝ) * h * Real.log (2 / h)) := by positivity
  have hval_bound : 1 / ((mseq k : ℝ) * h * Real.log (2 / h)) ≤
      (2 / c₀) * ((2 + r) * δ1 + β * r) := by
    have h1 : c₀ / 2 * (1 / ((mseq k : ℝ) * h * Real.log (2 / h))) ≤ (2 + r) * δ1 + β * r := by
      have hdiv := (div_le_iff₀ hh_pos).mpr hcomb
      calc
        c₀ / 2 * (1 / ((mseq k : ℝ) * h * Real.log (2 / h)))
            = (c₀ / (2 * (mseq k : ℝ) * Real.log (2 / h))) / h := by field_simp
        _ ≤ (2 + r) * δ1 + β * r := hdiv
    calc
      1 / ((mseq k : ℝ) * h * Real.log (2 / h))
          = (2 / c₀) * (c₀ / 2 * (1 / ((mseq k : ℝ) * h * Real.log (2 / h)))) := by field_simp
      _ ≤ (2 / c₀) * ((2 + r) * δ1 + β * r) := mul_le_mul_of_nonneg_left h1 (by positivity)
  rw [Real.dist_eq, sub_zero, abs_of_pos hval_pos]
  calc
    1 / ((mseq k : ℝ) * h * Real.log (2 / h))
        ≤ (2 / c₀) * ((2 + r) * δ1 + β * r) := hval_bound
    _ = (2 / c₀) * ((2 + r) * δ1) + (2 / c₀) * (β * r) := by ring
    _ < η / 2 + η / 2 := add_lt_add_of_lt_of_le hδ1_bound hr_bound
    _ = η := add_halves η

theorem ppl003_linearity_equivalence
    (H : ℝ → ℝ) (t β : ℝ) (hβ : 0 < β) :
    HasDerivAt H β t ↔
      ∃ (a b : ℕ → ℝ) (c : ℝ),
        0 < c ∧
        (∀ k : ℕ, a k < b k) ∧
        (∀ k : ℕ, a k ≤ a (k + 1) ∧ b (k + 1) ≤ b k) ∧
        (∀ k : ℕ, a k + c * (b k - a k) ≤ t ∧ t ≤ b k - c * (b k - a k)) ∧
        (∀ k : ℕ, BddAbove ((fun x => |H x - H (a k) - β * (x - a k)| / (β * (b k - a k))) ''
          Set.Icc (a k) (b k))) ∧
        Filter.Tendsto
          (fun k => sSup ((fun x => |H x - H (a k) - β * (x - a k)| / (β * (b k - a k))) ''
            Set.Icc (a k) (b k)))
          Filter.atTop (nhds 0) ∧
        Filter.Tendsto
          (fun k => sSup ((fun x => |H x - H (a k) - β * (x - a k)| / (β * (b k - a k))) ''
            Set.Icc (a k) (b k)) / ((b (k + 1) - a (k + 1)) / (b k - a k)))
          Filter.atTop (nhds 0) := by
  constructor
  · intro hderiv
    obtain ⟨r0, hr0_pos, hr0⟩ := hasDerivAt_eps_bound hderiv zero_lt_one
    let r : ℝ := r0 / 2
    have hr_pos : 0 < r := by positivity
    let a : ℕ → ℝ := fun k => t - r * (1 / 2 : ℝ) ^ k
    let b : ℕ → ℝ := fun k => t + r * (1 / 2 : ℝ) ^ k
    have hbdd_all : ∀ k : ℕ,
        BddAbove ((fun x => |H x - H (a k) - β * (x - a k)| / (β * (b k - a k))) ''
          Set.Icc (a k) (b k)) := by
      intro k
      refine ⟨1 / β, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      have hlen_pos : 0 < β * (b k - a k) := by
        dsimp [a, b]
        have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
        nlinarith [mul_pos hr_pos hpow]
      rw [div_le_iff₀ hlen_pos]
      have hxt : |x - t| ≤ r * (1 / 2 : ℝ) ^ k := by
        rw [abs_le]
        dsimp [a, b] at hx
        constructor <;> linarith [hx.1, hx.2]
      have hat : |a k - t| = r * (1 / 2 : ℝ) ^ k := by
        dsimp [a]
        rw [sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity)]
      have hpow_le : r * (1 / 2 : ℝ) ^ k ≤ r := by
        have h1 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith
      have hx_lt_r0 : |x - t| < r0 := by
        have : r < r0 := by dsimp [r]; linarith
        linarith
      have ha_lt_r0 : |a k - t| < r0 := by
        have : r < r0 := by dsimp [r]; linarith
        linarith
      have hx_err : |H x - H t - β * (x - t)| ≤ |x - t| := by
        simpa using hr0 x hx_lt_r0
      have ha_err : |H (a k) - H t - β * (a k - t)| ≤ |a k - t| := by
        simpa using hr0 (a k) ha_lt_r0
      have htri : |H x - H (a k) - β * (x - a k)| ≤
          |H x - H t - β * (x - t)| + |H (a k) - H t - β * (a k - t)| := by
        have hid : H x - H (a k) - β * (x - a k) =
            (H x - H t - β * (x - t)) - (H (a k) - H t - β * (a k - t)) := by ring
        rw [hid]
        exact abs_sub _ _
      have hlen_val : b k - a k = 2 * (r * (1 / 2 : ℝ) ^ k) := by dsimp [a, b]; ring
      calc
        |H x - H (a k) - β * (x - a k)| ≤ |x - t| + |a k - t| := le_trans htri (add_le_add hx_err ha_err)
        _ ≤ r * (1 / 2 : ℝ) ^ k + r * (1 / 2 : ℝ) ^ k := add_le_add hxt hat.le
        _ = (1 / β) * (β * (b k - a k)) := by rw [hlen_val]; field_simp; ring
    refine ⟨a, b, 1 / 3, by norm_num, ?_, ?_, ?_, hbdd_all, ?_, ?_⟩
    · intro k
      dsimp [a, b]
      have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
      linarith [mul_pos hr_pos hpow]
    · intro k
      dsimp [a, b]
      have hpow : (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2 : ℝ) ^ k := by
        rw [pow_succ]
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
      constructor <;> nlinarith
    · intro k
      dsimp [a, b]
      have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
      constructor <;> nlinarith
    · rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨δ, hδ_pos, hδ⟩ := hasDerivAt_eps_bound hderiv (by positivity : 0 < β * ε / 2)
      obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < δ / (2 * r + 1)) (by norm_num : (1 / 2 : ℝ) < 1)
      refine ⟨K, fun k hk => ?_⟩
      have hpow_le : (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ K :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      have hrk_lt : r * (1 / 2 : ℝ) ^ k < δ := by
        have h1 : (1 / 2 : ℝ) ^ K * (2 * r + 1) < δ := (lt_div_iff₀ (by positivity)).mp hK
        have h2 : 2 * r * (1 / 2 : ℝ) ^ K ≤ (1 / 2 : ℝ) ^ K * (2 * r + 1) := by
          have hpow_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ K := by positivity
          nlinarith
        nlinarith
      have hS_ne :
          ((fun x => |H x - H (a k) - β * (x - a k)| / (β * (b k - a k))) ''
            Set.Icc (a k) (b k)).Nonempty := by
        refine ⟨_, ⟨t, ⟨?_, ?_⟩, rfl⟩⟩
        · dsimp [a]
          have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
          linarith [mul_pos hr_pos hpow]
        · dsimp [b]
          have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
          linarith [mul_pos hr_pos hpow]
      have hS_nonneg :
          0 ≤ sSup ((fun x => |H x - H (a k) - β * (x - a k)| / (β * (b k - a k))) ''
            Set.Icc (a k) (b k)) := by
        rcases hS_ne with ⟨y, hy⟩
        have hy_nn : 0 ≤ y := by
          rcases hy with ⟨x, _, rfl⟩
          have hlen_pos : 0 < β * (b k - a k) := by
            dsimp [a, b]
            have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
            nlinarith [mul_pos hr_pos hpow]
          exact div_nonneg (abs_nonneg _) hlen_pos.le
        exact le_trans hy_nn (le_csSup (hbdd_all k) hy)
      have hS_le :
          sSup ((fun x => |H x - H (a k) - β * (x - a k)| / (β * (b k - a k))) ''
            Set.Icc (a k) (b k)) ≤ ε / 2 := by
        apply csSup_le hS_ne
        rintro _ ⟨x, hx, rfl⟩
        have hlen_pos : 0 < β * (b k - a k) := by
          dsimp [a, b]
          have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
          nlinarith [mul_pos hr_pos hpow]
        rw [div_le_iff₀ hlen_pos]
        have hxt : |x - t| ≤ r * (1 / 2 : ℝ) ^ k := by
          rw [abs_le]; dsimp [a, b] at hx; constructor <;> linarith [hx.1, hx.2]
        have hat : |a k - t| = r * (1 / 2 : ℝ) ^ k := by
          dsimp [a]; rw [sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity)]
        have hx_err : |H x - H t - β * (x - t)| ≤ (β * ε / 2) * |x - t| :=
          hδ x (lt_of_le_of_lt hxt hrk_lt)
        have ha_err : |H (a k) - H t - β * (a k - t)| ≤ (β * ε / 2) * |a k - t| :=
          hδ (a k) (by rw [hat]; exact hrk_lt)
        have htri : |H x - H (a k) - β * (x - a k)| ≤
            |H x - H t - β * (x - t)| + |H (a k) - H t - β * (a k - t)| := by
          have hid : H x - H (a k) - β * (x - a k) =
              (H x - H t - β * (x - t)) - (H (a k) - H t - β * (a k - t)) := by ring
          rw [hid]; exact abs_sub _ _
        have hlen_val : b k - a k = 2 * (r * (1 / 2 : ℝ) ^ k) := by dsimp [a, b]; ring
        calc
          |H x - H (a k) - β * (x - a k)|
              ≤ (β * ε / 2) * |x - t| + (β * ε / 2) * |a k - t| := le_trans htri (add_le_add hx_err ha_err)
          _ ≤ (β * ε / 2) * (r * (1 / 2 : ℝ) ^ k) + (β * ε / 2) * (r * (1 / 2 : ℝ) ^ k) := by
            gcongr; linarith [hat]
          _ = (ε / 2) * (β * (b k - a k)) := by rw [hlen_val]; ring
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hS_nonneg]
      linarith
    · have hS_lim :
          Filter.Tendsto
            (fun k => sSup ((fun x => |H x - H (a k) - β * (x - a k)| / (β * (b k - a k))) ''
              Set.Icc (a k) (b k)))
            Filter.atTop (nhds 0) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨δ, hδ_pos, hδ⟩ := hasDerivAt_eps_bound hderiv (by positivity : 0 < β * ε / 2)
        obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < δ / (2 * r + 1)) (by norm_num : (1 / 2 : ℝ) < 1)
        refine ⟨K, fun k hk => ?_⟩
        have hpow_le : (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ K :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
        have hrk_lt : r * (1 / 2 : ℝ) ^ k < δ := by
          have h1 : (1 / 2 : ℝ) ^ K * (2 * r + 1) < δ := (lt_div_iff₀ (by positivity)).mp hK
          have h2 : 2 * r * (1 / 2 : ℝ) ^ K ≤ (1 / 2 : ℝ) ^ K * (2 * r + 1) := by
            have hpow_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ K := by positivity
            nlinarith
          nlinarith
        have hS_ne :
            ((fun x => |H x - H (a k) - β * (x - a k)| / (β * (b k - a k))) ''
              Set.Icc (a k) (b k)).Nonempty := by
          refine ⟨_, ⟨t, ⟨?_, ?_⟩, rfl⟩⟩
          · dsimp [a]
            have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
            linarith [mul_pos hr_pos hpow]
          · dsimp [b]
            have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
            linarith [mul_pos hr_pos hpow]
        have hS_nonneg :
            0 ≤ sSup ((fun x => |H x - H (a k) - β * (x - a k)| / (β * (b k - a k))) ''
              Set.Icc (a k) (b k)) := by
          rcases hS_ne with ⟨y, hy⟩
          have hy_nn : 0 ≤ y := by
            rcases hy with ⟨x, _, rfl⟩
            have hlen_pos : 0 < β * (b k - a k) := by
              dsimp [a, b]
              have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
              nlinarith [mul_pos hr_pos hpow]
            exact div_nonneg (abs_nonneg _) hlen_pos.le
          exact le_trans hy_nn (le_csSup (hbdd_all k) hy)
        have hS_le :
            sSup ((fun x => |H x - H (a k) - β * (x - a k)| / (β * (b k - a k))) ''
              Set.Icc (a k) (b k)) ≤ ε / 2 := by
          apply csSup_le hS_ne
          rintro _ ⟨x, hx, rfl⟩
          have hlen_pos : 0 < β * (b k - a k) := by
            dsimp [a, b]
            have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
            nlinarith [mul_pos hr_pos hpow]
          rw [div_le_iff₀ hlen_pos]
          have hxt : |x - t| ≤ r * (1 / 2 : ℝ) ^ k := by
            rw [abs_le]; dsimp [a, b] at hx; constructor <;> linarith [hx.1, hx.2]
          have hat : |a k - t| = r * (1 / 2 : ℝ) ^ k := by
            dsimp [a]; rw [sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity)]
          have hx_err : |H x - H t - β * (x - t)| ≤ (β * ε / 2) * |x - t| :=
            hδ x (lt_of_le_of_lt hxt hrk_lt)
          have ha_err : |H (a k) - H t - β * (a k - t)| ≤ (β * ε / 2) * |a k - t| :=
            hδ (a k) (by rw [hat]; exact hrk_lt)
          have htri : |H x - H (a k) - β * (x - a k)| ≤
              |H x - H t - β * (x - t)| + |H (a k) - H t - β * (a k - t)| := by
            have hid : H x - H (a k) - β * (x - a k) =
                (H x - H t - β * (x - t)) - (H (a k) - H t - β * (a k - t)) := by ring
            rw [hid]; exact abs_sub _ _
          have hlen_val : b k - a k = 2 * (r * (1 / 2 : ℝ) ^ k) := by dsimp [a, b]; ring
          calc
            |H x - H (a k) - β * (x - a k)|
                ≤ (β * ε / 2) * |x - t| + (β * ε / 2) * |a k - t| := le_trans htri (add_le_add hx_err ha_err)
            _ ≤ (β * ε / 2) * (r * (1 / 2 : ℝ) ^ k) + (β * ε / 2) * (r * (1 / 2 : ℝ) ^ k) := by
              gcongr; linarith [hat]
            _ = (ε / 2) * (β * (b k - a k)) := by rw [hlen_val]; ring
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hS_nonneg]
        linarith
      have hratio :
          ∀ k : ℕ, (b (k + 1) - a (k + 1)) / (b k - a k) = 1 / 2 := by
        intro k
        dsimp [a, b]
        have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
        rw [pow_succ]
        field_simp
        ring
      have hfun :
          (fun k => sSup ((fun x => |H x - H (a k) - β * (x - a k)| / (β * (b k - a k))) ''
              Set.Icc (a k) (b k)) / ((b (k + 1) - a (k + 1)) / (b k - a k))) =
            fun k => 2 * sSup ((fun x => |H x - H (a k) - β * (x - a k)| / (β * (b k - a k))) ''
              Set.Icc (a k) (b k)) := by
        ext k
        rw [hratio k]
        ring
      rw [hfun]
      simpa using hS_lim.const_mul 2
  · rintro ⟨a, b, c, hc_pos, hlt, hnest, hmargin, hbdd, hL, hLratio⟩
    let L : ℕ → ℝ := fun k =>
      sSup ((fun x => |H x - H (a k) - β * (x - a k)| / (β * (b k - a k))) ''
        Set.Icc (a k) (b k))
    have hL_bound : ∀ k : ℕ, ∀ x ∈ Set.Icc (a k) (b k),
        |H x - H (a k) - β * (x - a k)| ≤ L k * β * (b k - a k) := by
      intro k x hx
      have hlen_pos : 0 < β * (b k - a k) := mul_pos hβ (sub_pos.mpr (hlt k))
      have hsup := le_csSup (hbdd k) ⟨x, hx, rfl⟩
      have hdiv := (div_le_iff₀ hlen_pos).mp hsup
      linarith
    have ht_mem : ∀ k : ℕ, t ∈ Set.Icc (a k) (b k) := by
      intro k
      have hlen_pos : 0 < b k - a k := sub_pos.mpr (hlt k)
      have hcm : 0 ≤ c * (b k - a k) := mul_nonneg hc_pos.le hlen_pos.le
      exact ⟨by linarith [(hmargin k).1], by linarith [(hmargin k).2]⟩
    have hlen_anti : Antitone (fun k => b k - a k) := by
      apply antitone_nat_of_succ_le
      intro k
      linarith [(hnest k).1, (hnest k).2]
    by_cases hlen_zero : Filter.Tendsto (fun k => b k - a k) Filter.atTop (nhds 0)
    · apply hasDerivAt_of_eps_bound
      intro ε hε
      have hlim_pos :
          Filter.Tendsto (fun k => (2 * β / c) * (L k / ((b (k + 1) - a (k + 1)) / (b k - a k))))
            Filter.atTop (nhds 0) := by
        simpa using hLratio.const_mul (2 * β / c)
      obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hlim_pos ε hε
      let δ := c * (b K - a K)
      have hδ_pos : 0 < δ := mul_pos hc_pos (sub_pos.mpr (hlt K))
      refine ⟨δ, hδ_pos, fun y hy => ?_⟩
      by_cases hy_eq : y = t
      · rw [hy_eq]; simp
      · have hy_K : y ∈ Set.Icc (a K) (b K) := by
          have hy_abs := abs_lt.mp hy
          constructor <;> linarith [(hmargin K).1, (hmargin K).2, hy_abs.1, hy_abs.2]
        have hnot_all : ∃ k ≥ K, y ∉ Set.Icc (a k) (b k) := by
          have hyt_pos : 0 < |y - t| := abs_pos.mpr (sub_ne_zero.mpr hy_eq)
          obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hlen_zero |y - t| hyt_pos
          refine ⟨max K M, le_max_left _ _, fun hymem => ?_⟩
          have hle_len : |y - t| ≤ b (max K M) - a (max K M) := by
            rw [abs_le]
            constructor <;> linarith [hymem.1, hymem.2, (ht_mem (max K M)).1, (ht_mem (max K M)).2]
          have hlt_len : b (max K M) - a (max K M) < |y - t| := by
            have := hM (max K M) (le_max_right _ _)
            rw [Real.dist_eq, sub_zero, abs_of_pos (sub_pos.mpr (hlt _))] at this
            exact this
          linarith
        let k := Nat.find hnot_all - 1
        have hfind := Nat.find_spec hnot_all
        have hfind_pos : Nat.find hnot_all > K := by
          by_contra hle
          have hEq : Nat.find hnot_all = K := le_antisymm (not_lt.mp hle) hfind.1
          exact absurd hy_K (hEq ▸ hfind.2)
        have hk_ge : K ≤ k := by omega
        have hk1_eq : k + 1 = Nat.find hnot_all := by omega
        have hy_k : y ∈ Set.Icc (a k) (b k) := by
          by_contra hnot
          have hk_lt : k < Nat.find hnot_all := by omega
          exact Nat.find_min hnot_all hk_lt ⟨hk_ge, hnot⟩
        have hy_k1 : y ∉ Set.Icc (a (k + 1)) (b (k + 1)) := hk1_eq ▸ hfind.2
        have hy_dist : c * (b (k + 1) - a (k + 1)) ≤ |y - t| := by
          simp only [Set.mem_Icc, not_and, not_le] at hy_k1
          by_cases hya : y < a (k + 1)
          · have h1 : c * (b (k + 1) - a (k + 1)) ≤ t - y := by
              linarith [(hmargin (k + 1)).1]
            exact le_trans h1 (le_trans (le_abs_self _) (by rw [abs_sub_comm]))
          · have hyb : b (k + 1) < y := hy_k1 (not_lt.mp hya)
            have h1 : c * (b (k + 1) - a (k + 1)) ≤ y - t := by
              linarith [(hmargin (k + 1)).2]
            exact le_trans h1 (le_abs_self _)
        have hdiff_k : |H y - H t - β * (y - t)| ≤ 2 * L k * β * (b k - a k) := by
          have hid : H y - H t - β * (y - t) =
              (H y - H (a k) - β * (y - a k)) - (H t - H (a k) - β * (t - a k)) := by ring
          rw [hid]
          calc
            |(H y - H (a k) - β * (y - a k)) - (H t - H (a k) - β * (t - a k))|
                ≤ |H y - H (a k) - β * (y - a k)| + |H t - H (a k) - β * (t - a k)| := abs_sub _ _
            _ ≤ L k * β * (b k - a k) + L k * β * (b k - a k) :=
              add_le_add (hL_bound k y hy_k) (hL_bound k t (ht_mem k))
            _ = 2 * L k * β * (b k - a k) := by ring
        have hK_k := hK k hk_ge
        rw [Real.dist_eq, sub_zero] at hK_k
        have hratio_pos : 0 < (b (k + 1) - a (k + 1)) / (b k - a k) :=
          div_pos (sub_pos.mpr (hlt (k + 1))) (sub_pos.mpr (hlt k))
        have hL_nonneg : 0 ≤ L k := by
          have hlen_pos : 0 < β * (b k - a k) := mul_pos hβ (sub_pos.mpr (hlt k))
          have h0 : 0 ≤ |H t - H (a k) - β * (t - a k)| / (β * (b k - a k)) :=
            div_nonneg (abs_nonneg _) hlen_pos.le
          exact le_trans h0 (le_csSup (hbdd k) ⟨t, ht_mem k, rfl⟩)
        have hterm_nn :
            0 ≤ (2 * β / c) * (L k / ((b (k + 1) - a (k + 1)) / (b k - a k))) := by positivity
        rw [abs_of_nonneg hterm_nn] at hK_k
        have hyt_pos : 0 < |y - t| := abs_pos.mpr (sub_ne_zero.mpr hy_eq)
        have hdiv_bound : |H y - H t - β * (y - t)| / |y - t| ≤
            (2 * β / c) * (L k / ((b (k + 1) - a (k + 1)) / (b k - a k))) := by
          calc
            |H y - H t - β * (y - t)| / |y - t|
                ≤ (2 * L k * β * (b k - a k)) / |y - t| :=
              div_le_div_of_nonneg_right hdiff_k hyt_pos.le
            _ ≤ (2 * L k * β * (b k - a k)) / (c * (b (k + 1) - a (k + 1))) := by
              apply div_le_div_of_nonneg_left _ (mul_pos hc_pos (sub_pos.mpr (hlt (k + 1)))) hy_dist
              exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL_nonneg) hβ.le)
                (sub_pos.mpr (hlt k)).le
            _ = (2 * β / c) * (L k / ((b (k + 1) - a (k + 1)) / (b k - a k))) := by
              have hlen1 : b (k + 1) - a (k + 1) ≠ 0 := (sub_pos.mpr (hlt (k + 1))).ne'
              have hlen0 : b k - a k ≠ 0 := (sub_pos.mpr (hlt k)).ne'
              field_simp
        exact (div_le_iff₀ hyt_pos).mp (le_trans hdiv_bound hK_k.le)
    · have hex_pos : ∃ δ0 > 0, ∀ k : ℕ, δ0 ≤ b k - a k := by
        by_contra hno
        push Not at hno
        apply hlen_zero
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨K, hK⟩ := hno ε hε
        refine ⟨K, fun k hk => ?_⟩
        rw [Real.dist_eq, sub_zero, abs_of_pos (sub_pos.mpr (hlt k))]
        exact lt_of_le_of_lt (hlen_anti hk) hK
      rcases hex_pos with ⟨δ0, hδ0_pos, hδ0⟩
      have ha_mono : Monotone a := monotone_nat_of_le_succ (fun k => (hnest k).1)
      have hb_anti : Antitone b := antitone_nat_of_succ_le (fun k => (hnest k).2)
      let aInf := ⨆ k : ℕ, a k
      let bInf := ⨅ k : ℕ, b k
      have ha_bdd : BddAbove (Set.range a) := by
        refine ⟨b 0, ?_⟩
        rintro _ ⟨k, rfl⟩
        exact le_trans (hlt k).le (hb_anti (Nat.zero_le k))
      have hb_bdd : BddBelow (Set.range b) := by
        refine ⟨a 0, ?_⟩
        rintro _ ⟨k, rfl⟩
        exact le_trans (ha_mono (Nat.zero_le k)) (hlt k).le
      have ha_le_all : ∀ k : ℕ, a k ≤ aInf := fun k => le_ciSup ha_bdd k
      have hb_all_le : ∀ k : ℕ, bInf ≤ b k := fun k => ciInf_le hb_bdd k
      have ht_in_inf : aInf + c * δ0 ≤ t ∧ t ≤ bInf - c * δ0 := by
        constructor
        · have : aInf ≤ t - c * δ0 := by
            apply ciSup_le
            intro k
            have hk := (hmargin k).1
            have hd := hδ0 k
            nlinarith [hc_pos]
          linarith
        · have : t + c * δ0 ≤ bInf := by
            apply le_ciInf
            intro k
            have hk := (hmargin k).2
            have hd := hδ0 k
            nlinarith [hc_pos]
          linarith
      have haff : ∀ y ∈ Set.Icc aInf bInf, H y - H t - β * (y - t) = 0 := by
        intro y hy
        by_contra hne
        have hpos : 0 < |H y - H t - β * (y - t)| := abs_pos.mpr hne
        have hlim : Filter.Tendsto (fun k => 2 * L k * β * (b 0 - a 0)) Filter.atTop (nhds 0) := by
          have : (fun k => 2 * L k * β * (b 0 - a 0)) = fun k => (2 * β * (b 0 - a 0)) * L k := by
            ext k; ring
          rw [this]
          simpa using hL.const_mul (2 * β * (b 0 - a 0))
        obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hlim |H y - H t - β * (y - t)| hpos
        have hK0 := hK K le_rfl
        rw [Real.dist_eq, sub_zero] at hK0
        have hy_K : y ∈ Set.Icc (a K) (b K) :=
          ⟨le_trans (ha_le_all K) hy.1, le_trans hy.2 (hb_all_le K)⟩
        have hdiff : |H y - H t - β * (y - t)| ≤ 2 * L K * β * (b K - a K) := by
          have hid : H y - H t - β * (y - t) =
              (H y - H (a K) - β * (y - a K)) - (H t - H (a K) - β * (t - a K)) := by ring
          rw [hid]
          calc
            |(H y - H (a K) - β * (y - a K)) - (H t - H (a K) - β * (t - a K))|
                ≤ |H y - H (a K) - β * (y - a K)| + |H t - H (a K) - β * (t - a K)| := abs_sub _ _
            _ ≤ L K * β * (b K - a K) + L K * β * (b K - a K) :=
              add_le_add (hL_bound K y hy_K) (hL_bound K t (ht_mem K))
            _ = 2 * L K * β * (b K - a K) := by ring
        have hlen_le : b K - a K ≤ b 0 - a 0 := hlen_anti (Nat.zero_le K)
        have hL_nn : 0 ≤ L K := by
          have hlen_pos : 0 < β * (b K - a K) := mul_pos hβ (sub_pos.mpr (hlt K))
          have h0 : 0 ≤ |H t - H (a K) - β * (t - a K)| / (β * (b K - a K)) :=
            div_nonneg (abs_nonneg _) hlen_pos.le
          exact le_trans h0 (le_csSup (hbdd K) ⟨t, ht_mem K, rfl⟩)
        have h1 : 2 * L K * β * (b K - a K) ≤ 2 * L K * β * (b 0 - a 0) :=
          mul_le_mul_of_nonneg_left hlen_le (by positivity)
        have h2 : 2 * L K * β * (b 0 - a 0) ≤ |2 * L K * β * (b 0 - a 0)| := le_abs_self _
        linarith
      have hloc : HasDerivAt (fun y : ℝ => H t + β * (y - t)) β t := by
        have hid : HasDerivAt (fun y : ℝ => y - t) 1 t := (hasDerivAt_id t).sub_const t
        simpa using (hid.const_mul β).const_add (H t)
      refine hloc.congr_of_eventuallyEq ?_
      rw [Filter.EventuallyEq, Metric.eventually_nhds_iff]
      refine ⟨c * δ0, mul_pos hc_pos hδ0_pos, fun y hy => ?_⟩
      rw [Real.dist_eq] at hy
      have hy_in : y ∈ Set.Icc aInf bInf := by
        have habs := abs_lt.mp hy
        constructor <;> linarith [ht_in_inf.1, ht_in_inf.2, habs.1, habs.2]
      have hz := haff y hy_in
      linarith

theorem ppl003_dyadic_lattice_impossibility
    (F : ℝ → ℝ) (C : ℝ) (hmono : Monotone F)
    (hlattice : ∀ n k : ℕ, 1 ≤ n → k < 2 ^ n →
      let a : ℝ := (k : ℝ) / 2 ^ n
      let b : ℝ := ((k + 1 : ℕ) : ℝ) / 2 ^ n
      let m : ℝ := (a + b) / 2
      F b - F m ≤ (C / (n : ℝ)) * (F m - F a)) :
    ¬ ∃ x ∈ Set.Ioo (0 : ℝ) 1, ∃ β > 0, HasDerivAt F β x := by
  rintro ⟨x, hx, β, hβ_pos, hderiv⟩
  obtain ⟨ρ, hρ_pos, hρ⟩ := hasDerivAt_eps_bound hderiv (by positivity : 0 < β / 8)
  obtain ⟨n1, hn1⟩ := exists_pow_lt_of_lt_one hρ_pos (by norm_num : (1 / 2 : ℝ) < 1)
  let N0 : ℕ := max 1 (max n1 (Nat.ceil (4 * max 1 C)))
  have hN0_ge1 : 1 ≤ N0 := le_max_left _ _
  have hN0_pow : (1 / 2 : ℝ) ^ N0 < ρ := by
    have h1 : (1 / 2 : ℝ) ^ N0 ≤ (1 / 2 : ℝ) ^ n1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_trans (le_max_left _ _) (le_max_right _ _))
    exact lt_of_le_of_lt h1 hn1
  have hC_bound : C / (N0 : ℝ) ≤ 1 / 4 := by
    have hN_ge_ceil : (Nat.ceil (4 * max 1 C) : ℝ) ≤ (N0 : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) (le_max_right _ _)
    have hceil := Nat.le_ceil (4 * max 1 C)
    have h4C : 4 * C ≤ (N0 : ℝ) := by linarith [le_max_right (1 : ℝ) C]
    have hN_pos : (0 : ℝ) < (N0 : ℝ) := by exact_mod_cast hN0_ge1
    rw [div_le_iff₀ hN_pos]
    linarith
  let h : ℝ := (1 / 2 : ℝ) ^ N0
  have hh_pos : 0 < h := by positivity
  have hh_inv : (1 : ℝ) / 2 ^ N0 = h := by
    dsimp [h]
    rw [one_div, ← inv_pow, ← one_div]
  let k : ℕ := Nat.floor (x * 2 ^ N0)
  have hk_lt : k < 2 ^ N0 := by
    rw [Nat.floor_lt (by nlinarith [hx.1, pow_pos (by norm_num : (0 : ℝ) < 2) N0])]
    have : x * (2 : ℝ) ^ N0 < (2 : ℝ) ^ N0 := by nlinarith [hx.2, pow_pos (by norm_num : (0 : ℝ) < 2) N0]
    exact_mod_cast this
  let a : ℝ := (k : ℝ) / 2 ^ N0
  let b : ℝ := ((k + 1 : ℕ) : ℝ) / 2 ^ N0
  let m : ℝ := (a + b) / 2
  have ha_le_x : a ≤ x := by
    dsimp [a]
    rw [div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) N0)]
    exact Nat.floor_le (by nlinarith [hx.1, pow_pos (by norm_num : (0 : ℝ) < 2) N0])
  have hx_lt_b : x < b := by
    dsimp [b]
    rw [lt_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) N0)]
    push_cast
    exact Nat.lt_floor_add_one (x * (2 : ℝ) ^ N0)
  have hba : b - a = h := by
    dsimp [a, b]
    push_cast
    rw [← hh_inv]
    field_simp
    ring
  have hbm : b - m = h / 2 := by dsimp [m]; linarith
  have hma : m - a = h / 2 := by dsimp [m]; linarith
  have hm_in : a ≤ m ∧ m ≤ b := by dsimp [m]; constructor <;> linarith
  have herr : ∀ y : ℝ, a ≤ y → y ≤ b → |F y - F x - β * (y - x)| ≤ (β / 8) * h := by
    intro y hya hyb
    have hyx : |y - x| ≤ h := by
      rw [abs_le]
      constructor <;> linarith
    have hlt : |y - x| < ρ := lt_of_le_of_lt hyx hN0_pow
    exact le_trans (hρ y hlt) (mul_le_mul_of_nonneg_left hyx (by positivity))
  have hb_err := (abs_le.mp (herr b (by linarith) le_rfl))
  have hm_err := (abs_le.mp (herr m hm_in.1 hm_in.2))
  have ha_err := (abs_le.mp (herr a le_rfl (by linarith)))
  have hlow : (β / 4) * h ≤ F b - F m := by
    have : β * (b - m) - (β / 8) * h - (β / 8) * h ≤ F b - F m := by linarith [hb_err.1, hm_err.2]
    rw [hbm] at this
    linarith
  have hup : F m - F a ≤ (3 * β / 4) * h := by
    have : F m - F a ≤ β * (m - a) + (β / 8) * h + (β / 8) * h := by linarith [hm_err.2, ha_err.1]
    rw [hma] at this
    linarith
  have hm_a_nonneg : 0 ≤ F m - F a := sub_nonneg.mpr (hmono hm_in.1)
  have hlat := hlattice N0 k hN0_ge1 hk_lt
  dsimp only at hlat
  have hlat' : F b - F m ≤ (1 / 4) * (F m - F a) :=
    le_trans hlat (mul_le_mul_of_nonneg_right hC_bound hm_a_nonneg)
  have hcontra : (β / 4) * h ≤ (1 / 4) * ((3 * β / 4) * h) :=
    le_trans hlow (le_trans hlat' (mul_le_mul_of_nonneg_left hup (by norm_num)))
  nlinarith [mul_pos hβ_pos hh_pos]

private noncomputable def kakEps (j : ℕ) : ℝ :=
  1 / (2 * Real.sqrt ((j + 1 : ℕ) : ℝ))

private noncomputable def kakQ (j : ℕ) : ℝ :=
  1 / 2 + 1 / (4 * Real.sqrt ((j + 1 : ℕ) : ℝ))

private noncomputable def kakW (j : ℕ) (b : Bool) : ℝ :=
  if b then kakQ j else 1 - kakQ j

private noncomputable def kakP (n m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, kakW j (Nat.testBit m (n - 1 - j))

private noncomputable def kakC (n k : ℕ) : ℝ :=
  ∑ m ∈ Finset.range k, kakP n m

private noncomputable def kakApprox (n : ℕ) (x : ℝ) : ℝ :=
  if x ≤ 0 then 0
  else if 1 ≤ x then 1
  else
    let k := Nat.floor (x * (2 : ℝ) ^ n)
    kakC n k + (x * (2 : ℝ) ^ n - (k : ℝ)) * kakP n k

private noncomputable def kakF (x : ℝ) : ℝ :=
  kakApprox 0 x + ∑' n : ℕ, (kakApprox (n + 1) x - kakApprox n x)

private lemma kakEps_pos (j : ℕ) : 0 < kakEps j := by
  dsimp [kakEps]
  positivity

private lemma kakEps_le_half (j : ℕ) : kakEps j ≤ 1 / 2 := by
  dsimp [kakEps]
  have h1 : (1 : ℝ) ≤ Real.sqrt ((j + 1 : ℕ) : ℝ) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.succ_pos j
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

private lemma kakQ_eq (j : ℕ) : kakQ j = (1 + kakEps j) / 2 := by
  dsimp [kakQ, kakEps]
  ring

private lemma one_sub_kakQ_eq (j : ℕ) : 1 - kakQ j = (1 - kakEps j) / 2 := by
  dsimp [kakQ, kakEps]
  ring

private lemma kakW_bounds (j : ℕ) (b : Bool) :
    1 / 4 ≤ kakW j b ∧ kakW j b ≤ 3 / 4 := by
  have he_pos := kakEps_pos j
  have he_half := kakEps_le_half j
  cases b
  · simp [kakW, one_sub_kakQ_eq]; constructor <;> linarith
  · simp [kakW, kakQ_eq]; constructor <;> linarith

private lemma kakW_sum (j : ℕ) : kakW j false + kakW j true = 1 := by
  simp [kakW]

private lemma testBit_zero_even (m : ℕ) : Nat.testBit (2 * m) 0 = false := by
  simp [Nat.testBit_zero]

private lemma testBit_zero_odd (m : ℕ) : Nat.testBit (2 * m + 1) 0 = true := by
  simp [Nat.testBit_zero]

private lemma testBit_succ_div (x k : ℕ) : Nat.testBit x (k + 1) = Nat.testBit (x / 2) k := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    Nat.div_div_eq_div_mul, ← pow_succ']

private lemma testBit_succ_even (m k : ℕ) : Nat.testBit (2 * m) (k + 1) = Nat.testBit m k := by
  rw [testBit_succ_div]
  simp

private lemma testBit_succ_odd (m k : ℕ) : Nat.testBit (2 * m + 1) (k + 1) = Nat.testBit m k := by
  rw [testBit_succ_div]
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [hdiv]

private lemma kakP_nonneg (n m : ℕ) : 0 ≤ kakP n m := by
  apply Finset.prod_nonneg
  intro j _
  exact le_trans (by norm_num) (kakW_bounds j _).1

private lemma kakP_le_pow (n m : ℕ) : kakP n m ≤ (3 / 4 : ℝ) ^ n := by
  calc
    kakP n m ≤ ∏ _j ∈ Finset.range n, (3 / 4 : ℝ) := by
      apply Finset.prod_le_prod
      · intro j _; exact le_trans (by norm_num) (kakW_bounds j _).1
      · intro j _; exact (kakW_bounds j _).2
    _ = (3 / 4 : ℝ) ^ n := by rw [Finset.prod_const, Finset.card_range]

private lemma kakP_even (n m : ℕ) : kakP (n + 1) (2 * m) = kakP n m * kakW n false := by
  dsimp [kakP]
  rw [Finset.prod_range_succ]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    have hjlt : j < n := Finset.mem_range.mp hj
    have hidx : n - j = (n - 1 - j) + 1 := by omega
    rw [hidx, testBit_succ_even]
  · simp

private lemma kakP_odd (n m : ℕ) : kakP (n + 1) (2 * m + 1) = kakP n m * kakW n true := by
  dsimp [kakP]
  rw [Finset.prod_range_succ]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    have hjlt : j < n := Finset.mem_range.mp hj
    have hidx : n - j = (n - 1 - j) + 1 := by omega
    rw [hidx, testBit_succ_odd]
  · simp

private lemma sum_range_two_mul (f : ℕ → ℝ) (k : ℕ) :
    ∑ m ∈ Finset.range (2 * k), f m = ∑ m ∈ Finset.range k, (f (2 * m) + f (2 * m + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

private lemma kakC_even (n k : ℕ) : kakC (n + 1) (2 * k) = kakC n k := by
  dsimp [kakC]
  rw [sum_range_two_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [kakP_even, kakP_odd, ← mul_add, kakW_sum, mul_one]

private lemma kakC_total (n : ℕ) : kakC n (2 ^ n) = 1 := by
  induction n with
  | zero => simp [kakC, kakP]
  | succ n ih =>
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [hpow, kakC_even, ih]

private lemma kakC_mono (n : ℕ) : Monotone (kakC n) := by
  apply monotone_nat_of_le_succ
  intro k
  dsimp [kakC]
  rw [Finset.sum_range_succ]
  linarith [kakP_nonneg n k]

private lemma kakApprox_eq_kakC (n k : ℕ) (hk : k ≤ 2 ^ n) :
    kakApprox n ((k : ℝ) / (2 : ℝ) ^ n) = kakC n k := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk_pos
  · simp [kakApprox, kakC]
  · rcases eq_or_lt_of_le hk with rfl | hk_lt
    · have hge : (1 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) / (2 : ℝ) ^ n := by
        push_cast; rw [div_self hpow.ne']
      have hgt0 : ¬ (((2 ^ n : ℕ) : ℝ) / (2 : ℝ) ^ n ≤ 0) := by
        push_cast; rw [div_self hpow.ne']; norm_num
      simp only [kakApprox, hgt0, ↓reduceIte, hge]
      exact (kakC_total n).symm
    · have hgt0 : ¬ ((k : ℝ) / (2 : ℝ) ^ n ≤ 0) := by
        apply not_le_of_gt
        apply div_pos (by exact_mod_cast hk_pos) hpow
      have hlt1 : ¬ (1 ≤ (k : ℝ) / (2 : ℝ) ^ n) := by
        apply not_le_of_gt
        rw [div_lt_one hpow]
        exact_mod_cast hk_lt
      simp only [kakApprox, hgt0, hlt1, ↓reduceIte]
      have hmul : ((k : ℝ) / (2 : ℝ) ^ n) * (2 : ℝ) ^ n = (k : ℝ) := by field_simp
      rw [hmul, Nat.floor_natCast, sub_self, zero_mul, add_zero]

private lemma kakApprox_mono (n : ℕ) : Monotone (kakApprox n) := by
  intro x y hxy
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hle01 : ∀ z : ℝ, 0 ≤ kakApprox n z ∧ kakApprox n z ≤ 1 := by
    intro z
    by_cases hz0 : z ≤ 0
    · simp [kakApprox, hz0]
    · by_cases hz1 : 1 ≤ z
      · simp [kakApprox, hz0, hz1]
      · simp only [kakApprox, hz0, hz1, ↓reduceIte]
        have hz_pos : 0 < z := lt_of_not_ge hz0
        have hz_lt : z < 1 := lt_of_not_ge hz1
        let k := Nat.floor (z * (2 : ℝ) ^ n)
        have hk_nn : 0 ≤ z * (2 : ℝ) ^ n := mul_nonneg hz_pos.le hpow.le
        have hfl : (k : ℝ) ≤ z * (2 : ℝ) ^ n := Nat.floor_le hk_nn
        have hfl1 : z * (2 : ℝ) ^ n < (k : ℝ) + 1 := Nat.lt_floor_add_one _
        have hk_lt : k < 2 ^ n := by
          rw [Nat.floor_lt hk_nn]
          exact_mod_cast (by nlinarith : z * (2 : ℝ) ^ n < (2 : ℝ) ^ n)
        have hP := kakP_nonneg n k
        constructor
        · have hC0 : 0 ≤ kakC n k := Finset.sum_nonneg fun _ _ => kakP_nonneg n _
          have hdiff_nn : 0 ≤ z * (2 : ℝ) ^ n - (k : ℝ) := sub_nonneg.mpr hfl
          exact add_nonneg hC0 (mul_nonneg hdiff_nn hP)
        · have hC1 : kakC n (k + 1) ≤ 1 := by
            rw [← kakC_total n]
            exact kakC_mono n hk_lt
          have hCk1 : kakC n (k + 1) = kakC n k + kakP n k := by
            dsimp [kakC]; rw [Finset.sum_range_succ]
          have hdiff_le1 : z * (2 : ℝ) ^ n - (k : ℝ) ≤ 1 := by linarith
          calc
            kakC n k + (z * (2 : ℝ) ^ n - (k : ℝ)) * kakP n k
                ≤ kakC n k + 1 * kakP n k := by gcongr
            _ = kakC n (k + 1) := by rw [one_mul, hCk1]
            _ ≤ 1 := hC1
  by_cases hx0 : x ≤ 0
  · dsimp only [kakApprox]
    rw [if_pos hx0]
    exact (hle01 y).1
  · by_cases hy1 : 1 ≤ y
    · have : kakApprox n y = 1 := by
        have hy0 : ¬ y ≤ 0 := by linarith
        simp [kakApprox, hy0, hy1]
      rw [this]
      exact (hle01 x).2
    · have hy0 : ¬ y ≤ 0 := fun h => hx0 (le_trans hxy h)
      have hx1 : ¬ 1 ≤ x := fun h => hy1 (le_trans h hxy)
      simp only [kakApprox, hx0, hx1, hy0, hy1, ↓reduceIte]
      let kx := Nat.floor (x * (2 : ℝ) ^ n)
      let ky := Nat.floor (y * (2 : ℝ) ^ n)
      have hkx_le_ky : kx ≤ ky := Nat.floor_mono (mul_le_mul_of_nonneg_right hxy hpow.le)
      rcases eq_or_lt_of_le hkx_le_ky with hkeq | hklt
      · change kakC n kx + (x * (2 : ℝ) ^ n - (kx : ℝ)) * kakP n kx ≤
            kakC n ky + (y * (2 : ℝ) ^ n - (ky : ℝ)) * kakP n ky
        rw [hkeq]
        have hdiff : x * (2 : ℝ) ^ n - (ky : ℝ) ≤ y * (2 : ℝ) ^ n - (ky : ℝ) := by gcongr
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hdiff (kakP_nonneg n ky))
      · have hkx1 : x * (2 : ℝ) ^ n < (kx : ℝ) + 1 := Nat.lt_floor_add_one _
        have hky0 : (ky : ℝ) ≤ y * (2 : ℝ) ^ n :=
          Nat.floor_le (mul_nonneg (lt_of_not_ge hy0).le hpow.le)
        have hC_step : kakC n (kx + 1) = kakC n kx + kakP n kx := by
          dsimp [kakC]; rw [Finset.sum_range_succ]
        have hC_mono : kakC n (kx + 1) ≤ kakC n ky := kakC_mono n hklt
        change kakC n kx + (x * (2 : ℝ) ^ n - (kx : ℝ)) * kakP n kx ≤
            kakC n ky + (y * (2 : ℝ) ^ n - (ky : ℝ)) * kakP n ky
        have hleft : kakC n kx + (x * (2 : ℝ) ^ n - (kx : ℝ)) * kakP n kx ≤ kakC n (kx + 1) := by
          rw [hC_step]
          have h1 : x * (2 : ℝ) ^ n - (kx : ℝ) ≤ 1 := by linarith
          calc
            kakC n kx + (x * (2 : ℝ) ^ n - (kx : ℝ)) * kakP n kx
                ≤ kakC n kx + 1 * kakP n kx := by gcongr; exact kakP_nonneg n kx
            _ = kakC n kx + kakP n kx := by rw [one_mul]
        have hright : kakC n ky ≤ kakC n ky + (y * (2 : ℝ) ^ n - (ky : ℝ)) * kakP n ky := by
          have h1 : 0 ≤ y * (2 : ℝ) ^ n - (ky : ℝ) := sub_nonneg.mpr hky0
          linarith [mul_nonneg h1 (kakP_nonneg n ky)]
        linarith

private lemma kakApprox_diff_le (n : ℕ) (x : ℝ) :
    |kakApprox (n + 1) x - kakApprox n x| ≤ (3 / 4 : ℝ) ^ n := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  by_cases hx0 : x ≤ 0
  · dsimp only [kakApprox]; rw [if_pos hx0, if_pos hx0]; simp; positivity
  · by_cases hx1 : 1 ≤ x
    · dsimp only [kakApprox]; rw [if_neg hx0, if_pos hx1, if_neg hx0, if_pos hx1]; simp; positivity
    · have hx_pos : 0 < x := lt_of_not_ge hx0
      have hx_lt : x < 1 := lt_of_not_ge hx1
      let k := Nat.floor (x * (2 : ℝ) ^ n)
      have hk_nn : 0 ≤ x * (2 : ℝ) ^ n := mul_nonneg hx_pos.le hpow.le
      have hk_lt : k < 2 ^ n := by
        rw [Nat.floor_lt hk_nn]
        exact_mod_cast (by nlinarith : x * (2 : ℝ) ^ n < (2 : ℝ) ^ n)
      have hax : (k : ℝ) / (2 : ℝ) ^ n ≤ x := by
        rw [div_le_iff₀ hpow]; exact Nat.floor_le hk_nn
      have hxb : x ≤ ((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
        rw [le_div_iff₀ hpow]; push_cast; exact (Nat.lt_floor_add_one _).le
      have h1_a : kakApprox (n + 1) ((k : ℝ) / (2 : ℝ) ^ n) = kakC n k := by
        have hdiv : (k : ℝ) / (2 : ℝ) ^ n = ((2 * k : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) := by
          push_cast; rw [pow_succ]; field_simp
        rw [hdiv, kakApprox_eq_kakC (n + 1) (2 * k) (by omega), kakC_even]
      have h1_b : kakApprox (n + 1) (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) = kakC n (k + 1) := by
        have hdiv : ((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n = ((2 * (k + 1) : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) := by
          push_cast; rw [pow_succ]; field_simp
        rw [hdiv, kakApprox_eq_kakC (n + 1) (2 * (k + 1)) (by omega), kakC_even]
      have h0_a := kakApprox_eq_kakC n k hk_lt.le
      have h0_b := kakApprox_eq_kakC n (k + 1) hk_lt
      have hm1_a : kakC n k ≤ kakApprox (n + 1) x := h1_a ▸ kakApprox_mono (n + 1) hax
      have hm1_b : kakApprox (n + 1) x ≤ kakC n (k + 1) := h1_b ▸ kakApprox_mono (n + 1) hxb
      have hm0_a : kakC n k ≤ kakApprox n x := h0_a ▸ kakApprox_mono n hax
      have hm0_b : kakApprox n x ≤ kakC n (k + 1) := h0_b ▸ kakApprox_mono n hxb
      have hC_step : kakC n (k + 1) - kakC n k = kakP n k := by
        dsimp [kakC]; rw [Finset.sum_range_succ, add_sub_cancel_left]
      have hdiff : |kakApprox (n + 1) x - kakApprox n x| ≤ kakC n (k + 1) - kakC n k := by
        rw [abs_le]; constructor <;> linarith
      rw [hC_step] at hdiff
      exact le_trans hdiff (kakP_le_pow n k)

private lemma kakApprox_tendsto (x : ℝ) :
    Filter.Tendsto (fun n => kakApprox n x) Filter.atTop (nhds (kakF x)) := by
  have hsum : Summable (fun n => kakApprox (n + 1) x - kakApprox n x) := by
    refine Summable.of_norm_bounded
      (summable_geometric_of_lt_one (r := (3 / 4 : ℝ)) (by norm_num) (by norm_num)) ?_
    intro n
    simpa [Real.norm_eq_abs] using kakApprox_diff_le n x
  have htend := hsum.hasSum.tendsto_sum_nat.const_add (kakApprox 0 x)
  have htele : ∀ N : ℕ,
      kakApprox 0 x + ∑ n ∈ Finset.range N, (kakApprox (n + 1) x - kakApprox n x) = kakApprox N x := by
    intro N
    rw [Finset.sum_range_sub (fun n => kakApprox n x) N]
    ring
  dsimp only [kakF]
  exact htend.congr htele

private lemma bernoulli_sub_le (u : ℝ) (_hu0 : 0 ≤ u) (hu1 : u ≤ 1) (M : ℕ) :
    1 - (M : ℝ) * u ≤ (1 - u) ^ M := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    have h1u : 0 ≤ 1 - u := by linarith
    have hprod := mul_le_mul_of_nonneg_right ih h1u
    have hsq : 0 ≤ (m : ℝ) * u ^ 2 := by positivity
    push_cast
    linarith

private lemma bernoulli_upper_inv (u : ℝ) (M : ℕ) (hu0 : 0 ≤ u) (hMu : (M : ℝ) * u ≤ 1 / 2) :
    (1 + u) ^ M ≤ 1 + 2 * (M : ℝ) * u := by
  cases M with
  | zero => simp
  | succ m =>
    have hm_pos : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    have hu_le : u ≤ 1 / 2 := by nlinarith
    have h1u : 1 - u ≥ 0 := by linarith
    have hmul : (1 + u) * (1 - u) ≤ 1 := by nlinarith [sq_nonneg u]
    have hpow_mul : (1 + u) ^ (m + 1) * (1 - u) ^ (m + 1) ≤ 1 := by
      rw [← mul_pow]
      exact pow_le_one₀ (mul_nonneg (by linarith) h1u) hmul
    have hbern : 1 - ((m + 1 : ℕ) : ℝ) * u ≤ (1 - u) ^ (m + 1) :=
      bernoulli_sub_le u hu0 (by linarith) (m + 1)
    have hpos_m : 0 < 1 - ((m + 1 : ℕ) : ℝ) * u := by linarith
    have h1 : (1 + u) ^ (m + 1) ≤ 1 / (1 - ((m + 1 : ℕ) : ℝ) * u) := by
      rw [le_div_iff₀ hpos_m]
      exact le_trans (mul_le_mul_of_nonneg_left hbern (by positivity)) hpow_mul
    have h2 : 1 / (1 - ((m + 1 : ℕ) : ℝ) * u) ≤ 1 + 2 * ((m + 1 : ℕ) : ℝ) * u := by
      rw [div_le_iff₀ hpos_m]
      set x := ((m + 1 : ℕ) : ℝ) * u
      have hx_nn : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) hu0
      have h12x : 0 ≤ 1 - 2 * x := by linarith
      nlinarith [mul_nonneg hx_nn h12x]
    exact le_trans h1 h2

private lemma kak_step_ineq1 (k : ℕ) (hk : 2 ≤ k) :
    (1 - kakEps k) < (1 - kakEps (k - 1)) * (1 + kakEps k) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have he_lt : kakEps (k - 1) < (5 / 4 : ℝ) * kakEps k := by
    dsimp [kakEps]
    have hkm : ((k - 1 + 1 : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast (by omega : k - 1 + 1 = k)
    rw [hkm]
    have hsqrt : Real.sqrt ((k + 1 : ℕ) : ℝ) < (5 / 4 : ℝ) * Real.sqrt (k : ℝ) := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 4), ← Real.sqrt_mul (by norm_num)]
      apply Real.sqrt_lt_sqrt (by positivity)
      have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      push_cast
      nlinarith
    have hmul : (5 / 4 : ℝ) * (1 / (2 * Real.sqrt ((k + 1 : ℕ) : ℝ))) =
        5 / (8 * Real.sqrt ((k + 1 : ℕ) : ℝ)) := by ring
    rw [hmul, div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  have he_third : kakEps k < 1 / 3 := by
    dsimp [kakEps]
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have h12 : (3 : ℝ) < 2 * Real.sqrt ((k + 1 : ℕ) : ℝ) := by
      have hsq : (9 : ℝ) < 4 * ((k + 1 : ℕ) : ℝ) := by
        have : (3 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ k + 1)
        linarith
      nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)),
        Real.sqrt_nonneg ((k + 1 : ℕ) : ℝ)]
    linarith
  have he_pos := kakEps_pos k
  nlinarith

private lemma kak_step_ineq2 (k : ℕ) (hk : 1 ≤ k) :
    (1 + kakEps (k - 1)) * (1 - kakEps k) < 1 := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkm : ((k - 1 + 1 : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast (by omega : k - 1 + 1 = k)
  let sk := Real.sqrt (k : ℝ)
  let sk1 := Real.sqrt ((k + 1 : ℕ) : ℝ)
  have hsk_pos : 0 < sk := Real.sqrt_pos.mpr hk_pos
  have hsk1_pos : 0 < sk1 := Real.sqrt_pos.mpr (by positivity)
  have hsk_ge1 : 1 ≤ sk := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
  have hsk1_gt1 : 1 < sk1 := by
    rw [← Real.sqrt_one]; apply Real.sqrt_lt_sqrt (by norm_num); exact_mod_cast (by omega : 1 < k + 1)
  have hsq : sk1 ^ 2 - sk ^ 2 = 1 := by
    dsimp [sk, sk1]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt hk_pos.le]
    push_cast; ring
  have hdiff : sk1 - sk = 1 / (sk1 + sk) := by
    field_simp
    linarith [hsq]
  have h_sub : kakEps (k - 1) - kakEps k = 2 * (kakEps (k - 1) * kakEps k) / (sk1 + sk) := by
    dsimp [kakEps]
    rw [hkm]
    change 1 / (2 * sk) - 1 / (2 * sk1) = 2 * ((1 / (2 * sk)) * (1 / (2 * sk1))) / (sk1 + sk)
    have hid : 1 / (2 * sk) - 1 / (2 * sk1) = (sk1 - sk) / (2 * sk * sk1) := by
      field_simp
    rw [hid, hdiff]
    field_simp
  have h_lt : kakEps (k - 1) - kakEps k < kakEps (k - 1) * kakEps k := by
    rw [h_sub, div_lt_iff₀ (by positivity)]
    have he2_pos : 0 < kakEps (k - 1) * kakEps k := mul_pos (kakEps_pos _) (kakEps_pos _)
    nlinarith
  linarith

private lemma kak_step_ineq3 (k : ℕ) (hk : 2 ≤ k) :
    1 < (1 - kakEps (k - 1)) * (1 + kakEps k) * (1 + kakEps (k + 1)) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkm : ((k - 1 + 1 : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast (by omega : k - 1 + 1 = k)
  have he_dec : ∀ m : ℕ, kakEps (m + 1) < kakEps m := by
    intro m
    dsimp [kakEps]
    apply div_lt_div_of_pos_left zero_lt_one (by positivity)
    apply mul_lt_mul_of_pos_left _ zero_lt_two
    apply Real.sqrt_lt_sqrt (by positivity)
    push_cast; linarith
  have h_e3 : kakEps 3 = 1 / 4 := by
    dsimp [kakEps]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  by_cases hk2 : k = 2
  · subst hk2
    have h_e1 : kakEps 1 < 0.3575 := by
      dsimp [kakEps]
      have hsq : (1.4 : ℝ) ^ 2 < ((1 + 1 : ℕ) : ℝ) := by norm_num
      have hsqrt : 1.4 < Real.sqrt ((1 + 1 : ℕ) : ℝ) := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.4)]
        exact Real.sqrt_lt_sqrt (by positivity) hsq
      rw [div_lt_iff₀ (by positivity)]
      linarith
    have h_e2 : 0.285 < kakEps 2 := by
      dsimp [kakEps]
      have hsq : ((2 + 1 : ℕ) : ℝ) < (1.75 : ℝ) ^ 2 := by norm_num
      have hsqrt : Real.sqrt ((2 + 1 : ℕ) : ℝ) < 1.75 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.75)]
        exact Real.sqrt_lt_sqrt (by positivity) hsq
      rw [lt_div_iff₀ (by positivity)]
      linarith
    have h12 : 2 - 1 = 1 := rfl
    rw [h12, h_e3]
    nlinarith
  · have hk3 : 3 ≤ k := by omega
    have hy_pos : 0 < kakEps (k + 1) := kakEps_pos (k + 1)
    have hy_le : kakEps (k + 1) ≤ 1 / 4 := by
      have hmono_k : ∀ n : ℕ, 3 ≤ n → kakEps n ≤ kakEps 3 := by
        intro n hn3
        induction n with
        | zero => omega
        | succ m ih =>
          rcases eq_or_lt_of_le hn3 with h3 | h3
          · rw [← h3]
          · exact le_trans (he_dec m).le (ih (by omega))
      exact le_trans (hmono_k (k + 1) (by omega)) h_e3.le
    have h_ek_gt : kakEps (k + 1) < kakEps k := he_dec k
    have h_ekm_lt : kakEps (k - 1) < (4 / 3 : ℝ) * kakEps (k + 1) := by
      dsimp [kakEps]
      rw [hkm]
      have hsqrt : Real.sqrt ((k + 1 + 1 : ℕ) : ℝ) < (4 / 3 : ℝ) * Real.sqrt (k : ℝ) := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4 / 3), ← Real.sqrt_mul (by norm_num)]
        apply Real.sqrt_lt_sqrt (by positivity)
        have hk3r : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
        push_cast; nlinarith
      have hmul : (4 / 3 : ℝ) * (1 / (2 * Real.sqrt ((k + 1 + 1 : ℕ) : ℝ))) =
          4 / (6 * Real.sqrt ((k + 1 + 1 : ℕ) : ℝ)) := by ring
      rw [hmul, div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    have h1 : (1 - (4 / 3 : ℝ) * kakEps (k + 1)) * (1 + kakEps (k + 1)) ^ 2 ≤
        (1 - kakEps (k - 1)) * (1 + kakEps k) * (1 + kakEps (k + 1)) := by
      have hprod1 : 1 - (4 / 3 : ℝ) * kakEps (k + 1) ≤ 1 - kakEps (k - 1) := by linarith
      have hprod2 : 1 + kakEps (k + 1) ≤ 1 + kakEps k := by linarith
      have hnn1 : 0 ≤ 1 - (4 / 3 : ℝ) * kakEps (k + 1) := by linarith
      have hnn2 : 0 ≤ 1 + kakEps (k + 1) := by linarith
      have hstep : (1 - (4 / 3 : ℝ) * kakEps (k + 1)) * (1 + kakEps (k + 1)) ≤
          (1 - kakEps (k - 1)) * (1 + kakEps k) :=
        mul_le_mul hprod1 hprod2 hnn2 (by linarith)
      calc
        (1 - (4 / 3 : ℝ) * kakEps (k + 1)) * (1 + kakEps (k + 1)) ^ 2
            = (1 - (4 / 3 : ℝ) * kakEps (k + 1)) * (1 + kakEps (k + 1)) * (1 + kakEps (k + 1)) := by
          ring
        _ ≤ (1 - kakEps (k - 1)) * (1 + kakEps k) * (1 + kakEps (k + 1)) :=
          mul_le_mul_of_nonneg_right hstep hnn2
    have h2 : 1 < (1 - (4 / 3 : ℝ) * kakEps (k + 1)) * (1 + kakEps (k + 1)) ^ 2 := by
      have hid : (1 - (4 / 3 : ℝ) * kakEps (k + 1)) * (1 + kakEps (k + 1)) ^ 2 - 1 =
          (kakEps (k + 1) / 3) * (2 - 5 * kakEps (k + 1) - 4 * (kakEps (k + 1)) ^ 2) := by ring
      have hpos_poly : 0 < 2 - 5 * kakEps (k + 1) - 4 * (kakEps (k + 1)) ^ 2 := by
        nlinarith [sq_nonneg (kakEps (k + 1))]
      have hmul_pos : 0 < (kakEps (k + 1) / 3) * (2 - 5 * kakEps (k + 1) - 4 * (kakEps (k + 1)) ^ 2) :=
        mul_pos (by positivity) hpos_poly
      linarith
    exact lt_of_lt_of_le h2 h1

private noncomputable def kakGreedy (β : ℝ) : ℕ → ℝ × Bool
  | 0 => (1, decide (1 ≤ β))
  | n + 1 =>
    let prev := kakGreedy β n
    let Snext := prev.1 * (if prev.2 then 1 + kakEps n else 1 - kakEps n)
    (Snext, decide (Snext ≤ β))

private lemma kakGreedy_S_pos (β : ℝ) (n : ℕ) : 0 < (kakGreedy β n).1 := by
  induction n with
  | zero => simp [kakGreedy]
  | succ n ih =>
    dsimp [kakGreedy]
    cases (kakGreedy β n).2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact mul_pos ih (by linarith [kakEps_le_half n])
    · simp only [↓reduceIte]
      exact mul_pos ih (by linarith [kakEps_pos n])

private lemma kakGreedy_S_step (β : ℝ) (n : ℕ) :
    (kakGreedy β (n + 1)).1 =
      (kakGreedy β n).1 * (if (kakGreedy β n).2 then 1 + kakEps n else 1 - kakEps n) := rfl

private lemma kakGreedy_b_eq (β : ℝ) (n : ℕ) :
    (kakGreedy β n).2 = decide ((kakGreedy β n).1 ≤ β) := by
  cases n <;> rfl

private lemma kakEps_sum_diverges (M : ℝ) (k0 : ℕ) :
    ∃ N ≥ k0, M < ∑ j ∈ Finset.Ico k0 N, kakEps j := by
  have hnot : ¬ Summable (fun j : ℕ => kakEps j) := by
    intro hs
    have hcomp : Summable (fun j : ℕ => 1 / (2 * ((j + 1 : ℕ) : ℝ))) := by
      refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hs
      dsimp [kakEps]
      apply div_le_div_of_nonneg_left zero_le_one (by positivity)
      apply mul_le_mul_of_nonneg_left _ zero_lt_two.le
      have h1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
      calc
        Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ Real.sqrt (((j + 1 : ℕ) : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
        _ = ((j + 1 : ℕ) : ℝ) := Real.sqrt_sq (by positivity)
    have hinv : Summable (fun j : ℕ => ((j : ℝ))⁻¹) := by
      have h2 : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ)⁻¹) := by
        have hmul := hcomp.mul_left 2
        refine Summable.congr hmul (fun j => by field_simp)
      exact (summable_nat_add_iff 1).mp h2
    exact Real.not_summable_natCast_inv hinv
  have hge : ∃ N : ℕ, M + (∑ j ∈ Finset.range k0, kakEps j) < ∑ j ∈ Finset.range N, kakEps j := by
    by_contra hle
    push Not at hle
    apply hnot
    exact summable_of_sum_range_le (fun j => (kakEps_pos j).le) hle
  rcases hge with ⟨N, hN⟩
  refine ⟨max k0 N, le_max_left _ _, ?_⟩
  have hsub := Finset.sum_range_add_sum_Ico (fun j => kakEps j) (le_max_left k0 N)
  have hrange : ∑ j ∈ Finset.range N, kakEps j ≤ ∑ j ∈ Finset.range (max k0 N), kakEps j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_right _ _))
      (fun j _ _ => (kakEps_pos j).le)
  linarith

private lemma kak_prod_upper (k0 : ℕ) (M : ℝ) :
    ∃ N ≥ k0, M < ∏ j ∈ Finset.Ico k0 N, (1 + kakEps j) := by
  obtain ⟨N, hNk, hsum⟩ := kakEps_sum_diverges M k0
  refine ⟨N, hNk, ?_⟩
  have h_le : ∀ N0 : ℕ, k0 ≤ N0 →
      1 + ∑ j ∈ Finset.Ico k0 N0, kakEps j ≤ ∏ j ∈ Finset.Ico k0 N0, (1 + kakEps j) := by
    intro N0 hN0
    induction N0 with
    | zero =>
      have hk0 : k0 = 0 := by omega
      subst hk0; simp
    | succ N0 ih =>
      rcases eq_or_lt_of_le hN0 with hEq | hlt
      · rw [← hEq]; simp
      · have hle' : k0 ≤ N0 := by omega
        rw [Finset.sum_Ico_succ_top hle', Finset.prod_Ico_succ_top hle']
        have hih := ih hle'
        have he_nn : 0 ≤ kakEps N0 := (kakEps_pos N0).le
        have hsum_nn : 0 ≤ ∑ j ∈ Finset.Ico k0 N0, kakEps j :=
          Finset.sum_nonneg fun j _ => (kakEps_pos j).le
        calc
          1 + (∑ j ∈ Finset.Ico k0 N0, kakEps j + kakEps N0)
              ≤ (1 + ∑ j ∈ Finset.Ico k0 N0, kakEps j) + kakEps N0 * 1 := by linarith
          _ ≤ (1 + ∑ j ∈ Finset.Ico k0 N0, kakEps j) * (1 + kakEps N0) := by nlinarith
          _ ≤ (∏ j ∈ Finset.Ico k0 N0, (1 + kakEps j)) * (1 + kakEps N0) :=
            mul_le_mul_of_nonneg_right hih (by linarith)
  linarith [h_le N hNk]

private lemma kak_prod_lower (k0 : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N ≥ k0, ∏ j ∈ Finset.Ico k0 N, (1 - kakEps j) < ε := by
  obtain ⟨N, hNk, hprod⟩ := kak_prod_upper k0 (1 / ε)
  refine ⟨N, hNk, ?_⟩
  have hmul :
      (∏ j ∈ Finset.Ico k0 N, (1 + kakEps j)) * (∏ j ∈ Finset.Ico k0 N, (1 - kakEps j)) ≤ 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_one (fun j _ => ?_) (fun j _ => ?_)
    · exact mul_nonneg (by linarith [kakEps_pos j]) (by linarith [kakEps_le_half j])
    · nlinarith [sq_nonneg (kakEps j)]
  have hpos1 : 0 < ∏ j ∈ Finset.Ico k0 N, (1 + kakEps j) :=
    Finset.prod_pos fun j _ => by linarith [kakEps_pos j]
  have h1 : ∏ j ∈ Finset.Ico k0 N, (1 - kakEps j) ≤
      1 / (∏ j ∈ Finset.Ico k0 N, (1 + kakEps j)) := by
    rw [le_div_iff₀ hpos1]
    linarith
  have h2 : 1 / (∏ j ∈ Finset.Ico k0 N, (1 + kakEps j)) < 1 / (1 / ε) :=
    one_div_lt_one_div_of_lt (by positivity) hprod
  simpa using lt_of_le_of_lt h1 h2

private lemma kakGreedy_invariant (β : ℝ) (hβ : 0 < β) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ n : ℕ, N0 ≤ n →
        β * (1 - kakEps (n - 1)) < (kakGreedy β n).1 ∧
        (kakGreedy β n).1 ≤ β * (1 + kakEps (n - 1)) := by
  have h_cross : ∃ N0 ≥ 2,
      β * (1 - kakEps (N0 - 1)) < (kakGreedy β N0).1 ∧
      (kakGreedy β N0).1 ≤ β * (1 + kakEps (N0 - 1)) := by
    by_cases hS2 : (kakGreedy β 2).1 ≤ β
    · have hnot_all : ∃ n ≥ 2, β < (kakGreedy β n).1 := by
        by_contra hno
        push Not at hno
        have h_all_t : ∀ m ≥ 2, (kakGreedy β m).2 = true := by
          intro m hm
          rw [kakGreedy_b_eq, decide_eq_true_iff]
          exact hno m hm
        have h_prod : ∀ N ≥ 2,
            (kakGreedy β N).1 = (kakGreedy β 2).1 * ∏ j ∈ Finset.Ico 2 N, (1 + kakEps j) := by
          intro N hN
          induction N with
          | zero => omega
          | succ N ih =>
            rcases eq_or_lt_of_le hN with hEq | hlt
            · rw [← hEq]; simp
            · have hle2 : 2 ≤ N := by omega
              rw [kakGreedy_S_step, h_all_t N hle2, if_pos rfl, Finset.prod_Ico_succ_top hle2,
                ih hle2]
              ring
        obtain ⟨N, hN2, hbig⟩ := kak_prod_upper 2 (β / (kakGreedy β 2).1)
        have hS2_pos := kakGreedy_S_pos β 2
        have hgt : β < (kakGreedy β N).1 := by
          rw [h_prod N hN2]
          exact (div_lt_iff₀' hS2_pos).mp hbig
        linarith [hno N hN2]
      let N0 := Nat.find hnot_all
      have hfind := Nat.find_spec hnot_all
      have hN0_gt2 : 2 < N0 := by
        by_contra hle
        have hEq : N0 = 2 := by omega
        exact absurd (hEq ▸ hfind.2) (not_lt.mpr hS2)
      have hprev_le : (kakGreedy β (N0 - 1)).1 ≤ β := by
        by_contra hgt
        have hlt : N0 - 1 < N0 := by omega
        exact Nat.find_min hnot_all hlt ⟨by omega, not_le.mp hgt⟩
      have hprev_b : (kakGreedy β (N0 - 1)).2 = true := by
        rw [kakGreedy_b_eq, decide_eq_true_iff]; exact hprev_le
      have hstep : (kakGreedy β N0).1 = (kakGreedy β (N0 - 1)).1 * (1 + kakEps (N0 - 1)) := by
        have hEq : N0 = (N0 - 1) + 1 := by omega
        conv_lhs => rw [hEq, kakGreedy_S_step, hprev_b]
        simp
      refine ⟨N0, by omega, ?_, ?_⟩
      · have h1 : β < (kakGreedy β N0).1 := hfind.2
        have h2 : β * (1 - kakEps (N0 - 1)) < β := by
          nlinarith [kakEps_pos (N0 - 1)]
        linarith
      · rw [hstep]
        exact mul_le_mul_of_nonneg_right hprev_le (by linarith [kakEps_pos (N0 - 1)])
    · have hnot_all : ∃ n ≥ 2, (kakGreedy β n).1 ≤ β := by
        by_contra hno
        push Not at hno
        have h_all_f : ∀ m ≥ 2, (kakGreedy β m).2 = false := by
          intro m hm
          rw [kakGreedy_b_eq, decide_eq_false_iff_not]
          exact not_le.mpr (hno m hm)
        have h_prod : ∀ N ≥ 2,
            (kakGreedy β N).1 = (kakGreedy β 2).1 * ∏ j ∈ Finset.Ico 2 N, (1 - kakEps j) := by
          intro N hN
          induction N with
          | zero => omega
          | succ N ih =>
            rcases eq_or_lt_of_le hN with hEq | hlt
            · rw [← hEq]; simp
            · have hle2 : 2 ≤ N := by omega
              rw [kakGreedy_S_step, h_all_f N hle2, if_neg Bool.false_ne_true,
                Finset.prod_Ico_succ_top hle2, ih hle2]
              ring
        obtain ⟨N, hN2, hsm⟩ := kak_prod_lower 2 (β / (kakGreedy β 2).1)
          (div_pos hβ (kakGreedy_S_pos β 2))
        have hS2_pos := kakGreedy_S_pos β 2
        have hle : (kakGreedy β N).1 ≤ β := by
          rw [h_prod N hN2]
          exact ((lt_div_iff₀' hS2_pos).mp hsm).le
        linarith [hno N hN2]
      let N0 := Nat.find hnot_all
      have hfind := Nat.find_spec hnot_all
      have hN0_gt2 : 2 < N0 := by
        by_contra hle
        have hEq : N0 = 2 := by omega
        exact hS2 (hEq ▸ hfind.2)
      have hprev_gt : β < (kakGreedy β (N0 - 1)).1 := by
        by_contra hle
        have hlt : N0 - 1 < N0 := by omega
        exact Nat.find_min hnot_all hlt ⟨by omega, not_lt.mp hle⟩
      have hprev_b : (kakGreedy β (N0 - 1)).2 = false := by
        rw [kakGreedy_b_eq, decide_eq_false_iff_not]; exact not_le.mpr hprev_gt
      have hstep : (kakGreedy β N0).1 = (kakGreedy β (N0 - 1)).1 * (1 - kakEps (N0 - 1)) := by
        have hEq : N0 = (N0 - 1) + 1 := by omega
        conv_lhs => rw [hEq, kakGreedy_S_step, hprev_b]
        simp
      refine ⟨N0, by omega, ?_, ?_⟩
      · rw [hstep]
        exact mul_lt_mul_of_pos_right hprev_gt (by linarith [kakEps_le_half (N0 - 1)])
      · have h1 : (kakGreedy β N0).1 ≤ β := hfind.2
        have h2 : β ≤ β * (1 + kakEps (N0 - 1)) := by nlinarith [kakEps_pos (N0 - 1)]
        linarith
  rcases h_cross with ⟨N0, hN0_ge2, hlow0, hup0⟩
  refine ⟨N0, hN0_ge2, fun n hn => ?_⟩
  induction n with
  | zero => omega
  | succ m ih =>
    rcases eq_or_lt_of_le hn with hEq | hlt
    · rw [← hEq]; exact ⟨hlow0, hup0⟩
    · have hm_ge : N0 ≤ m := by omega
      have hm2 : 2 ≤ m := le_trans hN0_ge2 hm_ge
      obtain ⟨hlow_m, hup_m⟩ := ih hm_ge
      rw [Nat.succ_sub_one, kakGreedy_S_step]
      by_cases hbm : (kakGreedy β m).1 ≤ β
      · have hb_t : (kakGreedy β m).2 = true := by
          rw [kakGreedy_b_eq, decide_eq_true_iff]; exact hbm
        rw [hb_t, if_pos rfl]
        constructor
        · have hineq := kak_step_ineq1 m hm2
          calc
            β * (1 - kakEps m) < β * ((1 - kakEps (m - 1)) * (1 + kakEps m)) :=
              mul_lt_mul_of_pos_left hineq hβ
            _ = (β * (1 - kakEps (m - 1))) * (1 + kakEps m) := by ring
            _ < (kakGreedy β m).1 * (1 + kakEps m) :=
              mul_lt_mul_of_pos_right hlow_m (by linarith [kakEps_pos m])
        · exact mul_le_mul_of_nonneg_right hbm (by linarith [kakEps_pos m])
      · have hb_f : (kakGreedy β m).2 = false := by
          rw [kakGreedy_b_eq, decide_eq_false_iff_not]; exact hbm
        rw [hb_f, if_neg Bool.false_ne_true]
        constructor
        · exact mul_lt_mul_of_pos_right (lt_of_not_ge hbm) (by linarith [kakEps_le_half m])
        · have hineq := kak_step_ineq2 m (by omega)
          calc
            (kakGreedy β m).1 * (1 - kakEps m)
                ≤ (β * (1 + kakEps (m - 1))) * (1 - kakEps m) :=
              mul_le_mul_of_nonneg_right hup_m (by linarith [kakEps_le_half m])
            _ = β * ((1 + kakEps (m - 1)) * (1 - kakEps m)) := by ring
            _ ≤ β * 1 := mul_le_mul_of_nonneg_left hineq.le hβ.le
            _ ≤ β * (1 + kakEps m) := by nlinarith [kakEps_pos m]

theorem ppl003_kakutani_vanishing_step_positive_deriv :
    ∃ F : ℝ → ℝ,
      Monotone F ∧
      F 0 = 0 ∧
      F 1 = 1 ∧
      (¬ Summable (fun j : ℕ =>
        ((1 / 2 + 1 / (4 * Real.sqrt ((j + 1 : ℕ) : ℝ))) - 1 / 2) ^ 2)) ∧
      (∀ n m : ℕ, m < 2 ^ n →
        F (((m + 1 : ℕ) : ℝ) / 2 ^ n) - F ((m : ℝ) / 2 ^ n) =
          ∏ j ∈ Finset.range n,
            if Nat.testBit m (n - 1 - j)
            then (1 / 2 + 1 / (4 * Real.sqrt ((j + 1 : ℕ) : ℝ)))
            else (1 / 2 - 1 / (4 * Real.sqrt ((j + 1 : ℕ) : ℝ)))) ∧
      (∀ β : ℝ, 0 < β → ∃ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F β x) := by
  have hF_dyad : ∀ n k : ℕ, k ≤ 2 ^ n → kakF ((k : ℝ) / (2 : ℝ) ^ n) = kakC n k := by
    intro n k hk
    refine tendsto_nhds_unique (kakApprox_tendsto _) ?_
    rw [Filter.tendsto_atTop']
    intro s hs
    refine ⟨n, fun N hN => ?_⟩
    have hkN : (k : ℝ) / (2 : ℝ) ^ n = ((k * 2 ^ (N - n) : ℕ) : ℝ) / (2 : ℝ) ^ N := by
      push_cast
      have hpow : (2 : ℝ) ^ N = (2 : ℝ) ^ n * (2 : ℝ) ^ (N - n) := by
        rw [← pow_add, Nat.add_sub_cancel' hN]
      rw [hpow]
      field_simp
    have hleN : k * 2 ^ (N - n) ≤ 2 ^ N := by
      have hpow : 2 ^ N = 2 ^ n * 2 ^ (N - n) := by
        rw [← pow_add, Nat.add_sub_cancel' hN]
      rw [hpow]
      exact Nat.mul_le_mul_right _ hk
    rw [hkN, kakApprox_eq_kakC N _ hleN]
    have hC_shift : ∀ d : ℕ, kakC (n + d) (k * 2 ^ d) = kakC n k := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        have h1 : k * 2 ^ (d + 1) = 2 * (k * 2 ^ d) := by ring
        rw [← add_assoc, h1, kakC_even, ih]
    have hEq := hC_shift (N - n)
    rw [Nat.add_sub_cancel' hN] at hEq
    rw [hEq]
    exact mem_of_mem_nhds hs
  refine ⟨kakF, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact le_of_tendsto_of_tendsto (kakApprox_tendsto x) (kakApprox_tendsto y)
      (Filter.Eventually.of_forall fun n => kakApprox_mono n hxy)
  · have hconst : ∀ n : ℕ, kakApprox n 0 = 0 := fun n => by simp [kakApprox]
    exact tendsto_nhds_unique (kakApprox_tendsto 0) (by simp [hconst])
  · have hconst : ∀ n : ℕ, kakApprox n 1 = 1 := fun n => by simp [kakApprox]
    exact tendsto_nhds_unique (kakApprox_tendsto 1) (by simp [hconst])
  · intro hs
    have heq : (fun j : ℕ => ((1 / 2 + 1 / (4 * Real.sqrt ((j + 1 : ℕ) : ℝ))) - 1 / 2) ^ 2) =
        fun j : ℕ => (1 / 16 : ℝ) * ((j + 1 : ℕ) : ℝ)⁻¹ := by
      ext j
      have hsq : (Real.sqrt ((j + 1 : ℕ) : ℝ)) ^ 2 = ((j + 1 : ℕ) : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hne : Real.sqrt ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      calc
        ((1 / 2 + 1 / (4 * Real.sqrt ((j + 1 : ℕ) : ℝ))) - 1 / 2) ^ 2
            = 1 / (16 * (Real.sqrt ((j + 1 : ℕ) : ℝ)) ^ 2) := by field_simp [hne]; ring
        _ = (1 / 16 : ℝ) * ((j + 1 : ℕ) : ℝ)⁻¹ := by rw [hsq]; ring
    rw [heq] at hs
    have hinv1 : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ)⁻¹) := by
      simpa using hs.mul_left 16
    exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp hinv1)
  · intro n m hm
    have ha := hF_dyad n m hm.le
    have hb := hF_dyad n (m + 1) hm
    push_cast at ha hb ⊢
    rw [hb, ha]
    dsimp [kakC]
    rw [Finset.sum_range_succ, add_sub_cancel_left]
    dsimp [kakP, kakW, kakQ]
    refine Finset.prod_congr rfl fun j _ => ?_
    cases Nat.testBit m (n - 1 - j) <;> (simp; try ring)
  · intro β hβ
    obtain ⟨N0, hN0_ge2, hinv⟩ := kakGreedy_invariant β hβ
    let b : ℕ → Bool := fun n => (kakGreedy β n).2
    let mseq : ℕ → ℕ := fun n => ∑ j ∈ Finset.range n, if b j then 2 ^ (n - 1 - j) else 0
    let a : ℕ → ℝ := fun n => (mseq n : ℝ) / (2 : ℝ) ^ n
    let c : ℕ → ℝ := fun n => ((mseq n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n
    have hmseq_succ : ∀ n : ℕ, mseq (n + 1) = 2 * mseq n + (if b n then 1 else 0) := by
      intro n
      dsimp [mseq]
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjlt : j < n := Finset.mem_range.mp hj
      cases b j
      · simp
      · simp only [↓reduceIte]
        have hidx : n - j = (n - 1 - j) + 1 := by omega
        rw [hidx, pow_succ]
        ring
    have hmseq_lt : ∀ n : ℕ, mseq n < 2 ^ n := by
      intro n
      induction n with
      | zero => simp [mseq]
      | succ n ih =>
        rw [hmseq_succ]
        cases b n <;> simp <;> rw [pow_succ] <;> omega
    have ha_mono : Monotone a := by
      apply monotone_nat_of_le_succ
      intro n
      dsimp [a]
      rw [hmseq_succ, pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
      cases b n
      · simp; linarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
      · simp; linarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
    have hc_anti : Antitone c := by
      apply antitone_nat_of_succ_le
      intro n
      dsimp [c]
      rw [hmseq_succ, pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
      cases b n
      · simp; linarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
      · simp; linarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
    have ha_lt_c : ∀ n : ℕ, a n < c n := by
      intro n
      dsimp [a, c]
      apply div_lt_div_of_pos_right _ (by positivity)
      push_cast; linarith
    have ha_bdd : BddAbove (Set.range a) := by
      refine ⟨c 0, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact le_trans (ha_lt_c n).le (hc_anti (Nat.zero_le n))
    let x : ℝ := ⨆ n : ℕ, a n
    have ha_le_x : ∀ n : ℕ, a n ≤ x := fun n => le_ciSup ha_bdd n
    have hx_le_c : ∀ n : ℕ, x ≤ c n := by
      intro n
      apply ciSup_le
      intro k
      have hk := (ha_lt_c (max k n)).le
      exact le_trans (ha_mono (le_max_left k n)) (le_trans hk (hc_anti (le_max_right k n)))
    have hno00 : ∀ n : ℕ, N0 ≤ n → b n = false → b (n + 1) = true := by
      intro n hn hbf
      have hup_n := (hinv n hn).2
      have hSn1 : (kakGreedy β (n + 1)).1 ≤ β := by
        rw [kakGreedy_S_step]
        have hbf' : (kakGreedy β n).2 = false := hbf
        rw [hbf', if_neg Bool.false_ne_true]
        have hineq := kak_step_ineq2 n (by omega)
        calc
          (kakGreedy β n).1 * (1 - kakEps n) ≤ (β * (1 + kakEps (n - 1))) * (1 - kakEps n) :=
            mul_le_mul_of_nonneg_right hup_n (by linarith [kakEps_le_half n])
          _ = β * ((1 + kakEps (n - 1)) * (1 - kakEps n)) := by ring
          _ ≤ β * 1 := mul_le_mul_of_nonneg_left hineq.le hβ.le
          _ = β := mul_one β
      dsimp [b]
      rw [kakGreedy_b_eq, decide_eq_true_iff]
      exact hSn1
    have hno111 : ∀ n : ℕ, N0 ≤ n → ¬ (b n = true ∧ b (n + 1) = true ∧ b (n + 2) = true) := by
      intro n hn ⟨h0, h1, h2⟩
      have hlow_n := (hinv n hn).1
      have hSn2_le : (kakGreedy β (n + 2)).1 ≤ β := by
        dsimp [b] at h2
        rw [kakGreedy_b_eq, decide_eq_true_iff] at h2
        exact h2
      have hSn2_eq : (kakGreedy β (n + 2)).1 =
          (kakGreedy β n).1 * (1 + kakEps n) * (1 + kakEps (n + 1)) := by
        have h0' : (kakGreedy β n).2 = true := h0
        have h1' : (kakGreedy β (n + 1)).2 = true := h1
        rw [kakGreedy_S_step (n := n + 1), h1', if_pos rfl, kakGreedy_S_step (n := n), h0', if_pos rfl]
      have hineq := kak_step_ineq3 n (by omega)
      have hgt : β < (kakGreedy β (n + 2)).1 := by
        rw [hSn2_eq]
        calc
          β < β * ((1 - kakEps (n - 1)) * (1 + kakEps n) * (1 + kakEps (n + 1))) := by
            nlinarith [hineq]
          _ = (β * (1 - kakEps (n - 1))) * (1 + kakEps n) * (1 + kakEps (n + 1)) := by ring
          _ < (kakGreedy β n).1 * (1 + kakEps n) * (1 + kakEps (n + 1)) := by
            apply mul_lt_mul_of_pos_right _ (by linarith [kakEps_pos (n + 1)])
            exact mul_lt_mul_of_pos_right hlow_n (by linarith [kakEps_pos n])
      linarith
    have hx_margin : ∀ n : ℕ, N0 ≤ n →
        a n + (1 / 8 : ℝ) * (c n - a n) ≤ x ∧ x ≤ c n - (1 / 8 : ℝ) * (c n - a n) := by
      intro n hn
      have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
      have hlen : c n - a n = 1 / (2 : ℝ) ^ n := by
        dsimp [a, c]; push_cast; field_simp; ring
      constructor
      · have h2 : a n + (1 / 4 : ℝ) * (c n - a n) ≤ a (n + 2) := by
          dsimp [a]
          rw [hlen, hmseq_succ (n + 1), hmseq_succ n, pow_succ, pow_succ]
          have hdisj : b n = true ∨ b (n + 1) = true := by
            cases hn0 : b n
            · right; exact hno00 n hn hn0
            · left; rfl
          have hid : (mseq n : ℝ) / (2 : ℝ) ^ n + 1 / 4 * (1 / (2 : ℝ) ^ n) =
              ((4 * mseq n + 1 : ℕ) : ℝ) / ((2 : ℝ) ^ n * 2 * 2) := by
            push_cast; field_simp; ring
          rw [hid]
          apply div_le_div_of_nonneg_right _ (by positivity)
          norm_cast
          rcases hdisj with hbt | hbt
          · cases b (n + 1) <;> simp [hbt] <;> omega
          · cases b n <;> simp [hbt] <;> omega
        have h1 : (1 / 8 : ℝ) * (c n - a n) ≤ (1 / 4 : ℝ) * (c n - a n) := by
          rw [hlen]
          have : (0 : ℝ) < 1 / (2 : ℝ) ^ n := by positivity
          linarith
        linarith [ha_le_x (n + 2)]
      · have h3 : c (n + 3) ≤ c n - (1 / 8 : ℝ) * (c n - a n) := by
          dsimp [c]
          rw [hlen, hmseq_succ (n + 2), hmseq_succ (n + 1), hmseq_succ n,
            pow_succ, pow_succ, pow_succ]
          have hdisj : b n = false ∨ b (n + 1) = false ∨ b (n + 2) = false := by
            by_contra hno
            push Not at hno
            have ht0 : b n = true := Bool.eq_true_of_not_eq_false hno.1
            have ht1 : b (n + 1) = true := Bool.eq_true_of_not_eq_false hno.2.1
            have ht2 : b (n + 2) = true := Bool.eq_true_of_not_eq_false hno.2.2
            exact hno111 n hn ⟨ht0, ht1, ht2⟩
          have hid : ((mseq n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n - 1 / 8 * (1 / (2 : ℝ) ^ n) =
              ((8 * mseq n + 7 : ℕ) : ℝ) / ((2 : ℝ) ^ n * 2 * 2 * 2) := by
            push_cast; field_simp; ring
          rw [hid]
          apply div_le_div_of_nonneg_right _ (by positivity)
          norm_cast
          rcases hdisj with hbf | hbf | hbf
          · cases b (n + 1) <;> cases b (n + 2) <;> simp [hbf] <;> omega
          · cases b n <;> cases b (n + 2) <;> simp [hbf] <;> omega
          · cases b n <;> cases b (n + 1) <;> simp [hbf] <;> omega
        linarith [hx_le_c (n + 3)]
    have hx_in : x ∈ Set.Ioo (0 : ℝ) 1 := by
      have hm0 := hx_margin N0 le_rfl
      have hlen0 : 0 < c N0 - a N0 := sub_pos.mpr (ha_lt_c N0)
      have ha_nn : 0 ≤ a N0 := by dsimp [a]; positivity
      have hc_le1 : c N0 ≤ 1 := by
        dsimp [c]
        rw [div_le_one (by positivity)]
        exact_mod_cast hmseq_lt N0
      exact ⟨by linarith, by linarith⟩
    refine ⟨x, hx_in, ?_⟩
    have hP_mseq : ∀ n : ℕ, (2 : ℝ) ^ n * kakP n (mseq n) = (kakGreedy β n).1 := by
      intro n
      induction n with
      | zero => simp [kakP, kakGreedy]
      | succ n ih =>
        have hm1 : mseq (n + 1) = 2 * mseq n + (if b n then 1 else 0) := hmseq_succ n
        change (2 : ℝ) ^ (n + 1) * kakP (n + 1) (mseq (n + 1)) =
          (kakGreedy β n).1 * (if (kakGreedy β n).2 then 1 + kakEps n else 1 - kakEps n)
        rw [hm1, pow_succ]
        cases hbn : (kakGreedy β n).2
        · have hb' : b n = false := hbn
          simp only [hb', Bool.false_eq_true, ↓reduceIte, add_zero]
          rw [kakP_even]
          have hW : 2 * kakW n false = 1 - kakEps n := by simp [kakW, one_sub_kakQ_eq]; ring
          calc
            (2 : ℝ) ^ n * 2 * (kakP n (mseq n) * kakW n false)
                = ((2 : ℝ) ^ n * kakP n (mseq n)) * (2 * kakW n false) := by ring
            _ = (kakGreedy β n).1 * (1 - kakEps n) := by rw [ih, hW]
        · have hb' : b n = true := hbn
          simp only [hb', ↓reduceIte]
          rw [kakP_odd]
          have hW : 2 * kakW n true = 1 + kakEps n := by simp [kakW, kakQ_eq]; ring
          calc
            (2 : ℝ) ^ n * 2 * (kakP n (mseq n) * kakW n true)
                = ((2 : ℝ) ^ n * kakP n (mseq n)) * (2 * kakW n true) := by ring
            _ = (kakGreedy β n).1 * (1 + kakEps n) := by rw [ih, hW]
    have hS_tend : Filter.Tendsto (fun n => (kakGreedy β n).1) Filter.atTop (nhds β) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, ∀ n ≥ N1, β * kakEps (n - 1) < ε := by
        let M := Nat.ceil ((β + 1) / ε) ^ 2 + 2
        refine ⟨M, fun n hn => ?_⟩
        dsimp [kakEps]
        have hkm : ((n - 1 + 1 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast (by omega : n - 1 + 1 = n)
        rw [hkm]
        have hn_ge : ((Nat.ceil ((β + 1) / ε) : ℝ) ^ 2) < (n : ℝ) := by
          have : Nat.ceil ((β + 1) / ε) ^ 2 < n := by omega
          exact_mod_cast this
        have hsqrt : (Nat.ceil ((β + 1) / ε) : ℝ) < Real.sqrt (n : ℝ) := by
          rw [← Real.sqrt_sq (Nat.cast_nonneg _)]
          exact Real.sqrt_lt_sqrt (by positivity) hn_ge
        have hceil : (β + 1) / ε ≤ Real.sqrt (n : ℝ) :=
          le_trans (Nat.le_ceil _) hsqrt.le
        have h1 : β < ε * Real.sqrt (n : ℝ) := by
          have := mul_le_mul_of_nonneg_left hceil hε.le
          rw [mul_div_cancel₀ _ hε.ne'] at this
          linarith
        have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
        rw [← mul_div_assoc, mul_one, div_lt_iff₀ (by positivity)]
        nlinarith
      refine ⟨max N0 N1, fun n hn => ?_⟩
      obtain ⟨hlow, hup⟩ := hinv n (le_trans (le_max_left _ _) hn)
      have heps := hN1 n (le_trans (le_max_right _ _) hn)
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hF_mono : Monotone kakF := by
      intro u v huv
      exact le_of_tendsto_of_tendsto (kakApprox_tendsto u) (kakApprox_tendsto v)
        (Filter.Eventually.of_forall fun n => kakApprox_mono n huv)
    have hP_sub : ∀ n d s : ℕ, s < 2 ^ d →
        kakP n (mseq n) * ((1 - kakEps n) / 2) ^ d ≤ kakP (n + d) (mseq n * 2 ^ d + s) ∧
        kakP (n + d) (mseq n * 2 ^ d + s) ≤ kakP n (mseq n) * ((1 + kakEps n) / 2) ^ d := by
      intro n d
      induction d with
      | zero =>
        intro s hs
        have hs0 : s = 0 := by omega
        subst hs0
        simp
      | succ d ih =>
        intro s hs
        have hsd : s / 2 < 2 ^ d := by rw [pow_succ'] at hs; omega
        obtain ⟨ihL, ihR⟩ := ih (s / 2) hsd
        have heps_dec : kakEps (n + d) ≤ kakEps n := by
          dsimp [kakEps]
          apply div_le_div_of_nonneg_left zero_le_one (by positivity)
          apply mul_le_mul_of_nonneg_left _ zero_lt_two.le
          apply Real.sqrt_le_sqrt
          exact_mod_cast (by omega : n + 1 ≤ n + d + 1)
        have hw_bounds : ∀ b0 : Bool,
            (1 - kakEps n) / 2 ≤ kakW (n + d) b0 ∧ kakW (n + d) b0 ≤ (1 + kakEps n) / 2 := by
          intro b0
          have hpos_nd := kakEps_pos (n + d)
          have hpos_n := kakEps_pos n
          cases b0
          · simp [kakW, one_sub_kakQ_eq]
            constructor <;> linarith [heps_dec, hpos_nd, hpos_n]
          · simp [kakW, kakQ_eq]
            constructor <;> linarith [heps_dec, hpos_nd, hpos_n]
        have hpos_L : 0 ≤ (1 - kakEps n) / 2 := by linarith [kakEps_le_half n]
        have hpos_R : 0 ≤ (1 + kakEps n) / 2 := by linarith [kakEps_pos n]
        have hPm_nn : 0 ≤ kakP n (mseq n) := kakP_nonneg _ _
        have hid_idx : mseq n * 2 ^ (d + 1) + s = 2 * (mseq n * 2 ^ d + s / 2) + s % 2 := by
          rw [pow_succ']
          have hmul : mseq n * (2 * 2 ^ d) = 2 * (mseq n * 2 ^ d) := by ring
          rw [hmul]
          omega
        have heq_nd : n + (d + 1) = (n + d) + 1 := by omega
        rw [hid_idx, heq_nd]
        rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
        · rw [hmod, add_zero, kakP_even, pow_succ, pow_succ, ← mul_assoc, ← mul_assoc]
          have ⟨wL, wR⟩ := hw_bounds false
          have hw_nn : 0 ≤ kakW (n + d) false := le_trans (by norm_num) (kakW_bounds _ _).1
          constructor
          · exact mul_le_mul ihL wL hpos_L (kakP_nonneg _ _)
          · exact mul_le_mul ihR wR hw_nn (mul_nonneg hPm_nn (pow_nonneg hpos_R d))
        · rw [hmod, kakP_odd, pow_succ, pow_succ, ← mul_assoc, ← mul_assoc]
          have ⟨wL, wR⟩ := hw_bounds true
          have hw_nn : 0 ≤ kakW (n + d) true := le_trans (by norm_num) (kakW_bounds _ _).1
          constructor
          · exact mul_le_mul ihL wL hpos_L (kakP_nonneg _ _)
          · exact mul_le_mul ihR wR hw_nn (mul_nonneg hPm_nn (pow_nonneg hpos_R d))
    have ha_shift : ∃ (a' c' : ℕ → ℝ) (margin : ℝ),
        0 < margin ∧
        (∀ k : ℕ, a' k < c' k) ∧
        (∀ k : ℕ, a' k ≤ a' (k + 1) ∧ c' (k + 1) ≤ c' k) ∧
        (∀ k : ℕ, a' k + margin * (c' k - a' k) ≤ x ∧ x ≤ c' k - margin * (c' k - a' k)) ∧
        (∀ k : ℕ, BddAbove ((fun z => |kakF z - kakF (a' k) - β * (z - a' k)| / (β * (c' k - a' k))) ''
          Set.Icc (a' k) (c' k))) ∧
        Filter.Tendsto
          (fun k => sSup ((fun z => |kakF z - kakF (a' k) - β * (z - a' k)| / (β * (c' k - a' k))) ''
            Set.Icc (a' k) (c' k)))
          Filter.atTop (nhds 0) ∧
        Filter.Tendsto
          (fun k => sSup ((fun z => |kakF z - kakF (a' k) - β * (z - a' k)| / (β * (c' k - a' k))) ''
            Set.Icc (a' k) (c' k)) / ((c' (k + 1) - a' (k + 1)) / (c' k - a' k)))
          Filter.atTop (nhds 0) := by
      let a' : ℕ → ℝ := fun k => a (N0 + k)
      let c' : ℕ → ℝ := fun k => c (N0 + k)
      let E : ℕ → ℝ := fun k =>
        let n := N0 + k
        let M := Nat.sqrt (Nat.sqrt n)
        (3 * (kakGreedy β n).1 * (1 / (2 : ℝ) ^ M) +
          2 * (M : ℝ) * kakEps n * (kakGreedy β n).1 + |(kakGreedy β n).1 - β|) / β
      have hL_pt : ∀ k : ℕ, ∀ z ∈ Set.Icc (a' k) (c' k),
          |kakF z - kakF (a' k) - β * (z - a' k)| / (β * (c' k - a' k)) ≤ E k := by
        intro k z hz
        dsimp [E]
        set n := N0 + k
        set M := Nat.sqrt (Nat.sqrt n)
        have hn1 : 1 ≤ n := by omega
        have hM1 : 1 ≤ M := by
          dsimp [M]
          exact Nat.le_sqrt.mpr (by simpa using Nat.le_sqrt.mpr (by simpa using hn1))
        have hM_bound : (M : ℝ) * kakEps n ≤ 1 / (2 * (M : ℝ)) := by
          have hsq1 : M ^ 2 ≤ Nat.sqrt n := Nat.sqrt_le' (Nat.sqrt n)
          have hsq2 : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n
          have hM4 : M ^ 4 ≤ n := by
            calc
              M ^ 4 = (M ^ 2) ^ 2 := by ring
              _ ≤ (Nat.sqrt n) ^ 2 := Nat.pow_le_pow_left hsq1 2
              _ ≤ n := hsq2
          have hM2_le : ((M : ℝ) ^ 2) ^ 2 < ((n + 1 : ℕ) : ℝ) := by
            have : (M ^ 2) ^ 2 < n + 1 := by
              calc
                (M ^ 2) ^ 2 = M ^ 4 := by ring
                _ < n + 1 := by omega
            exact_mod_cast this
          have hM2_sqrt : (M : ℝ) ^ 2 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by
            rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ 2)]
            exact Real.sqrt_lt_sqrt (by positivity) hM2_le
          dsimp [kakEps]
          have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
          rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have hMe_half : (M : ℝ) * kakEps n ≤ 1 / 2 := by
          have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
          have h1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
          have h2 : 1 / (2 * (M : ℝ)) ≤ 1 / 2 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
          exact le_trans hM_bound h2
        have hbern_low : 1 - (M : ℝ) * kakEps n ≤ (1 - kakEps n) ^ M :=
          bernoulli_sub_le (kakEps n) (kakEps_pos n).le (by linarith [kakEps_le_half n]) M
        have hbern_up : (1 + kakEps n) ^ M ≤ 1 + 2 * (M : ℝ) * kakEps n :=
          bernoulli_upper_inv (kakEps n) M (kakEps_pos n).le hMe_half
        have hlen_n : c n - a n = 1 / (2 : ℝ) ^ n := by
          dsimp [a, c]; push_cast; field_simp; ring
        have hpow_n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
        have hpow_M_pos : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
        have hpow_nM_pos : (0 : ℝ) < (2 : ℝ) ^ (n + M) := by positivity
        have hz_nn : 0 ≤ (z - a n) * (2 : ℝ) ^ (n + M) := by
          have : 0 ≤ z - a n := sub_nonneg.mpr hz.1
          positivity
        let q := Nat.floor ((z - a n) * (2 : ℝ) ^ (n + M))
        have hq_le : q ≤ 2 ^ M := by
          have hz_le_len : z - a n ≤ 1 / (2 : ℝ) ^ n := by
            rw [← hlen_n]; exact sub_le_sub_right hz.2 (a n)
          have hmul : (z - a n) * (2 : ℝ) ^ (n + M) ≤ (2 : ℝ) ^ M := by
            rw [pow_add]
            calc
              (z - a n) * ((2 : ℝ) ^ n * (2 : ℝ) ^ M)
                  ≤ (1 / (2 : ℝ) ^ n) * ((2 : ℝ) ^ n * (2 : ℝ) ^ M) := by gcongr
              _ = (2 : ℝ) ^ M := by field_simp
          exact Nat.floor_le_of_le (by exact_mod_cast hmul)
        let zq : ℝ := ((mseq n * 2 ^ M + q : ℕ) : ℝ) / (2 : ℝ) ^ (n + M)
        have hzq_eq : zq - a n = (q : ℝ) / (2 : ℝ) ^ (n + M) := by
          dsimp [zq, a]
          push_cast
          rw [pow_add]
          field_simp
          ring
        have hzq_le_z : zq ≤ z := by
          have h1 : (q : ℝ) ≤ (z - a n) * (2 : ℝ) ^ (n + M) := Nat.floor_le hz_nn
          have h2 : (q : ℝ) / (2 : ℝ) ^ (n + M) ≤ z - a n := (div_le_iff₀ hpow_nM_pos).mpr h1
          linarith [hzq_eq]
        have hm_pow_le : mseq n * 2 ^ M + q ≤ 2 ^ (n + M) := by
          have hm1 : mseq n + 1 ≤ 2 ^ n := hmseq_lt n
          rw [pow_add]
          nlinarith
        have hC_diff : kakF zq - kakF (a n) =
            ∑ r ∈ Finset.range q, kakP (n + M) (mseq n * 2 ^ M + r) := by
          have ha_eq : a n = ((mseq n * 2 ^ M : ℕ) : ℝ) / (2 : ℝ) ^ (n + M) := by
            dsimp [a]; push_cast; rw [pow_add]; field_simp; ring
          have hm0_le : mseq n * 2 ^ M ≤ 2 ^ (n + M) := by rw [pow_add]; nlinarith [hmseq_lt n]
          rw [ha_eq, hF_dyad (n + M) _ hm_pow_le, hF_dyad (n + M) _ hm0_le]
          have hgen : ∀ q₀ : ℕ, kakC (n + M) (mseq n * 2 ^ M + q₀) - kakC (n + M) (mseq n * 2 ^ M) =
              ∑ r ∈ Finset.range q₀, kakP (n + M) (mseq n * 2 ^ M + r) := by
            intro q₀
            induction q₀ with
            | zero => simp
            | succ q' ih =>
              dsimp [kakC]
              have hadd : mseq n * 2 ^ M + (q' + 1) = (mseq n * 2 ^ M + q') + 1 := by omega
              rw [hadd, Finset.sum_range_succ, Finset.sum_range_succ]
              dsimp [kakC] at ih
              linarith
          exact hgen q
        have hSn_pos : 0 < (kakGreedy β n).1 := kakGreedy_S_pos β n
        have hsum_bounds :
            (q : ℝ) * ((kakGreedy β n).1 / (2 : ℝ) ^ (n + M)) * (1 - (M : ℝ) * kakEps n) ≤
              kakF zq - kakF (a n) ∧
            kakF zq - kakF (a n) ≤
              (q : ℝ) * ((kakGreedy β n).1 / (2 : ℝ) ^ (n + M)) * (1 + 2 * (M : ℝ) * kakEps n) := by
          rw [hC_diff]
          have hterm : ∀ r ∈ Finset.range q,
              ((kakGreedy β n).1 / (2 : ℝ) ^ (n + M)) * (1 - (M : ℝ) * kakEps n) ≤
                kakP (n + M) (mseq n * 2 ^ M + r) ∧
              kakP (n + M) (mseq n * 2 ^ M + r) ≤
                ((kakGreedy β n).1 / (2 : ℝ) ^ (n + M)) * (1 + 2 * (M : ℝ) * kakEps n) := by
            intro r hr
            have hr_lt : r < 2 ^ M := lt_of_lt_of_le (Finset.mem_range.mp hr) hq_le
            obtain ⟨hPL, hPR⟩ := hP_sub n M r hr_lt
            have hPn := hP_mseq n
            have hPn_eq : kakP n (mseq n) = (kakGreedy β n).1 / (2 : ℝ) ^ n := by
              rw [← hPn]; field_simp
            constructor
            · calc
                ((kakGreedy β n).1 / (2 : ℝ) ^ (n + M)) * (1 - (M : ℝ) * kakEps n)
                    = kakP n (mseq n) * ((1 - (M : ℝ) * kakEps n) / (2 : ℝ) ^ M) := by
                  rw [hPn_eq, pow_add]; field_simp
                _ ≤ kakP n (mseq n) * ((1 - kakEps n) ^ M / (2 : ℝ) ^ M) := by
                  gcongr; exact kakP_nonneg _ _
                _ = kakP n (mseq n) * ((1 - kakEps n) / 2) ^ M := by rw [div_pow]
                _ ≤ kakP (n + M) (mseq n * 2 ^ M + r) := hPL
            · calc
                kakP (n + M) (mseq n * 2 ^ M + r)
                    ≤ kakP n (mseq n) * ((1 + kakEps n) / 2) ^ M := hPR
                _ = kakP n (mseq n) * ((1 + kakEps n) ^ M / (2 : ℝ) ^ M) := by rw [div_pow]
                _ ≤ kakP n (mseq n) * ((1 + 2 * (M : ℝ) * kakEps n) / (2 : ℝ) ^ M) := by
                  gcongr; exact kakP_nonneg _ _
                _ = ((kakGreedy β n).1 / (2 : ℝ) ^ (n + M)) * (1 + 2 * (M : ℝ) * kakEps n) := by
                  rw [hPn_eq, pow_add]; field_simp; ring
          constructor
          · calc
              (q : ℝ) * ((kakGreedy β n).1 / (2 : ℝ) ^ (n + M)) * (1 - (M : ℝ) * kakEps n)
                  = ∑ _r ∈ Finset.range q,
                      ((kakGreedy β n).1 / (2 : ℝ) ^ (n + M)) * (1 - (M : ℝ) * kakEps n) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
              _ ≤ ∑ r ∈ Finset.range q, kakP (n + M) (mseq n * 2 ^ M + r) :=
                Finset.sum_le_sum fun r hr => (hterm r hr).1
          · calc
              ∑ r ∈ Finset.range q, kakP (n + M) (mseq n * 2 ^ M + r)
                  ≤ ∑ _r ∈ Finset.range q,
                      ((kakGreedy β n).1 / (2 : ℝ) ^ (n + M)) * (1 + 2 * (M : ℝ) * kakEps n) :=
                Finset.sum_le_sum fun r hr => (hterm r hr).2
              _ = (q : ℝ) * ((kakGreedy β n).1 / (2 : ℝ) ^ (n + M)) * (1 + 2 * (M : ℝ) * kakEps n) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
        have hzq_err : |kakF zq - kakF (a n) - (kakGreedy β n).1 * (zq - a n)| ≤
            2 * (M : ℝ) * kakEps n * (kakGreedy β n).1 * (1 / (2 : ℝ) ^ n) := by
          have hq_nn : (0 : ℝ) ≤ (q : ℝ) / (2 : ℝ) ^ M := by positivity
          have hq_le1 : (q : ℝ) / (2 : ℝ) ^ M ≤ 1 := by
            rw [div_le_one hpow_M_pos]; exact_mod_cast hq_le
          have hid : (q : ℝ) * ((kakGreedy β n).1 / (2 : ℝ) ^ (n + M)) = (kakGreedy β n).1 * (zq - a n) := by
            rw [hzq_eq]; ring
          rw [hid] at hsum_bounds
          have hval_nn : 0 ≤ (kakGreedy β n).1 * (zq - a n) :=
            mul_nonneg hSn_pos.le (by rw [hzq_eq]; positivity)
          have hval_le : (kakGreedy β n).1 * (zq - a n) ≤ (kakGreedy β n).1 * (1 / (2 : ℝ) ^ n) := by
            apply mul_le_mul_of_nonneg_left _ hSn_pos.le
            rw [hzq_eq, pow_add]
            calc
              (q : ℝ) / ((2 : ℝ) ^ n * (2 : ℝ) ^ M) = ((q : ℝ) / (2 : ℝ) ^ M) * (1 / (2 : ℝ) ^ n) := by
                ring
              _ ≤ 1 * (1 / (2 : ℝ) ^ n) := mul_le_mul_of_nonneg_right hq_le1 (by positivity)
              _ = 1 / (2 : ℝ) ^ n := one_mul _
          have heps_nn : 0 ≤ (M : ℝ) * kakEps n := mul_nonneg (Nat.cast_nonneg _) (kakEps_pos n).le
          rw [abs_le]
          constructor
          · calc
              -(2 * (M : ℝ) * kakEps n * (kakGreedy β n).1 * (1 / (2 : ℝ) ^ n))
                  ≤ -(2 * ((M : ℝ) * kakEps n) * ((kakGreedy β n).1 * (zq - a n))) := by
                have h1 : ((M : ℝ) * kakEps n) * ((kakGreedy β n).1 * (zq - a n)) ≤
                    ((M : ℝ) * kakEps n) * ((kakGreedy β n).1 * (1 / (2 : ℝ) ^ n)) :=
                  mul_le_mul_of_nonneg_left hval_le heps_nn
                linarith
              _ ≤ -((M : ℝ) * kakEps n * ((kakGreedy β n).1 * (zq - a n))) := by
                have : 0 ≤ (M : ℝ) * kakEps n * ((kakGreedy β n).1 * (zq - a n)) :=
                  mul_nonneg heps_nn hval_nn
                linarith
              _ ≤ kakF zq - kakF (a n) - (kakGreedy β n).1 * (zq - a n) := by
                linarith [hsum_bounds.1]
          · calc
              kakF zq - kakF (a n) - (kakGreedy β n).1 * (zq - a n)
                  ≤ 2 * ((M : ℝ) * kakEps n) * ((kakGreedy β n).1 * (zq - a n)) := by
                linarith [hsum_bounds.2]
              _ ≤ 2 * ((M : ℝ) * kakEps n) * ((kakGreedy β n).1 * (1 / (2 : ℝ) ^ n)) :=
                mul_le_mul_of_nonneg_left hval_le (by linarith)
              _ = 2 * (M : ℝ) * kakEps n * (kakGreedy β n).1 * (1 / (2 : ℝ) ^ n) := by ring
        have hz_step : |kakF z - kakF zq| ≤ 2 * (kakGreedy β n).1 * (1 / (2 : ℝ) ^ M) * (1 / (2 : ℝ) ^ n) ∧
            |z - zq| ≤ (1 / (2 : ℝ) ^ M) * (1 / (2 : ℝ) ^ n) := by
          rcases eq_or_lt_of_le hq_le with hq_top | hq_lt
          · have hz_eq : z = zq := by
              have hle1 : z ≤ zq := by
                have hq_div : (q : ℝ) / (2 : ℝ) ^ (n + M) = 1 / (2 : ℝ) ^ n := by
                  rw [hq_top, pow_add]; push_cast; field_simp
                linarith [hz.2, hlen_n, hzq_eq, hq_div]
              linarith [hzq_le_z]
            rw [hz_eq]
            simp only [sub_self, abs_zero]
            constructor <;> positivity
          · let zq1 : ℝ := ((mseq n * 2 ^ M + (q + 1) : ℕ) : ℝ) / (2 : ℝ) ^ (n + M)
            have hz_lt_zq1 : z < zq1 := by
              have h1 : (z - a n) * (2 : ℝ) ^ (n + M) < (q : ℝ) + 1 := Nat.lt_floor_add_one _
              have h2 : z - a n < ((q + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + M) := by
                rw [lt_div_iff₀ hpow_nM_pos]; push_cast; exact h1
              have hzq1_eq : zq1 - a n = ((q + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + M) := by
                dsimp [zq1, a]; push_cast; rw [pow_add]; field_simp; ring
              linarith
            have hzq1_le : mseq n * 2 ^ M + (q + 1) ≤ 2 ^ (n + M) := by
              have hm1 : mseq n + 1 ≤ 2 ^ n := hmseq_lt n
              rw [pow_add]; nlinarith
            have hF_step : kakF zq1 - kakF zq = kakP (n + M) (mseq n * 2 ^ M + q) := by
              rw [hF_dyad (n + M) _ hzq1_le, hF_dyad (n + M) _ hm_pow_le]
              dsimp [kakC]
              have hadd : mseq n * 2 ^ M + (q + 1) = (mseq n * 2 ^ M + q) + 1 := by omega
              rw [hadd, Finset.sum_range_succ, add_sub_cancel_left]
            have hP_top : kakP (n + M) (mseq n * 2 ^ M + q) ≤
                2 * (kakGreedy β n).1 * (1 / (2 : ℝ) ^ M) * (1 / (2 : ℝ) ^ n) := by
              have hPR := (hP_sub n M q hq_lt).2
              have hPn := hP_mseq n
              have hPn_eq : kakP n (mseq n) = (kakGreedy β n).1 / (2 : ℝ) ^ n := by
                rw [← hPn]; field_simp
              have h1M_le2 : 1 + 2 * (M : ℝ) * kakEps n ≤ 2 := by linarith
              calc
                kakP (n + M) (mseq n * 2 ^ M + q)
                    ≤ kakP n (mseq n) * ((1 + kakEps n) / 2) ^ M := hPR
                _ = kakP n (mseq n) * ((1 + kakEps n) ^ M / (2 : ℝ) ^ M) := by rw [div_pow]
                _ ≤ kakP n (mseq n) * ((1 + 2 * (M : ℝ) * kakEps n) / (2 : ℝ) ^ M) := by
                  gcongr; exact kakP_nonneg _ _
                _ ≤ kakP n (mseq n) * (2 / (2 : ℝ) ^ M) :=
                  mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1M_le2 (by positivity))
                    (kakP_nonneg _ _)
                _ = 2 * (kakGreedy β n).1 * (1 / (2 : ℝ) ^ M) * (1 / (2 : ℝ) ^ n) := by
                  rw [hPn_eq]; ring
            have hF_diff_nonneg : 0 ≤ kakF z - kakF zq := sub_nonneg.mpr (hF_mono hzq_le_z)
            have hF_diff_le : kakF z - kakF zq ≤ kakF zq1 - kakF zq :=
              sub_le_sub_right (hF_mono hz_lt_zq1.le) (kakF zq)
            have hz_diff_eq : zq1 - zq = (1 / (2 : ℝ) ^ M) * (1 / (2 : ℝ) ^ n) := by
              dsimp [zq1, zq]; push_cast; rw [pow_add]; field_simp; ring
            constructor
            · rw [abs_of_nonneg hF_diff_nonneg]
              exact le_trans hF_diff_le (hF_step ▸ hP_top)
            · rw [abs_of_nonneg (sub_nonneg.mpr hzq_le_z), ← hz_diff_eq]
              linarith
        have hS_z_err : |(kakGreedy β n).1 * (z - zq)| ≤
            (kakGreedy β n).1 * (1 / (2 : ℝ) ^ M) * (1 / (2 : ℝ) ^ n) := by
          rw [abs_mul, abs_of_pos hSn_pos]
          calc
            (kakGreedy β n).1 * |z - zq|
                ≤ (kakGreedy β n).1 * ((1 / (2 : ℝ) ^ M) * (1 / (2 : ℝ) ^ n)) :=
              mul_le_mul_of_nonneg_left hz_step.2 hSn_pos.le
            _ = (kakGreedy β n).1 * (1 / (2 : ℝ) ^ M) * (1 / (2 : ℝ) ^ n) := by ring
        have hβ_z_err : |((kakGreedy β n).1 - β) * (z - a n)| ≤
            |(kakGreedy β n).1 - β| * (1 / (2 : ℝ) ^ n) := by
          rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_of_nonneg (sub_nonneg.mpr hz.1), ← hlen_n]
          exact sub_le_sub_right hz.2 (a n)
        have htot : |kakF z - kakF (a n) - β * (z - a n)| ≤
            (3 * (kakGreedy β n).1 * (1 / (2 : ℝ) ^ M) +
              2 * (M : ℝ) * kakEps n * (kakGreedy β n).1 + |(kakGreedy β n).1 - β|) *
              (1 / (2 : ℝ) ^ n) := by
          have hid : kakF z - kakF (a n) - β * (z - a n) =
              (kakF z - kakF zq) +
              (kakF zq - kakF (a n) - (kakGreedy β n).1 * (zq - a n)) -
              (kakGreedy β n).1 * (z - zq) +
              ((kakGreedy β n).1 - β) * (z - a n) := by ring
          rw [hid]
          have t1 : |((kakF z - kakF zq) + (kakF zq - kakF (a n) - (kakGreedy β n).1 * (zq - a n)) -
              (kakGreedy β n).1 * (z - zq)) + ((kakGreedy β n).1 - β) * (z - a n)| ≤
              |(kakF z - kakF zq) + (kakF zq - kakF (a n) - (kakGreedy β n).1 * (zq - a n))| +
                |(kakGreedy β n).1 * (z - zq)| + |((kakGreedy β n).1 - β) * (z - a n)| := by
            have a1 := abs_add_le
              ((kakF z - kakF zq) + (kakF zq - kakF (a n) - (kakGreedy β n).1 * (zq - a n)) -
                (kakGreedy β n).1 * (z - zq))
              (((kakGreedy β n).1 - β) * (z - a n))
            have a2 := abs_sub
              ((kakF z - kakF zq) + (kakF zq - kakF (a n) - (kakGreedy β n).1 * (zq - a n)))
              ((kakGreedy β n).1 * (z - zq))
            linarith
          have t2 : |(kakF z - kakF zq) + (kakF zq - kakF (a n) - (kakGreedy β n).1 * (zq - a n))| ≤
              |kakF z - kakF zq| + |kakF zq - kakF (a n) - (kakGreedy β n).1 * (zq - a n)| :=
            abs_add_le _ _
          linarith [hz_step.1, hzq_err, hS_z_err, hβ_z_err]
        have hden_pos : 0 < β * (c n - a n) := mul_pos hβ (by rw [hlen_n]; positivity)
        change |kakF z - kakF (a n) - β * (z - a n)| / (β * (c n - a n)) ≤ _
        rw [div_le_div_iff₀ hden_pos hβ, hlen_n]
        have hmul_b : |kakF z - kakF (a n) - β * (z - a n)| * β ≤
            ((3 * (kakGreedy β n).1 * (1 / (2 : ℝ) ^ M) +
              2 * (M : ℝ) * kakEps n * (kakGreedy β n).1 + |(kakGreedy β n).1 - β|) *
              (1 / (2 : ℝ) ^ n)) * β := mul_le_mul_of_nonneg_right htot hβ.le
        linarith
      have hE_tend : Filter.Tendsto E Filter.atTop (nhds 0) := by
        have hM_inf : Filter.Tendsto (fun k : ℕ => Nat.sqrt (Nat.sqrt (N0 + k)))
            Filter.atTop Filter.atTop := by
          rw [Filter.tendsto_atTop_atTop]
          intro K
          refine ⟨K ^ 4, fun k hk => ?_⟩
          have h1 : (K ^ 2) ^ 2 ≤ N0 + k := by
            calc
              (K ^ 2) ^ 2 = K ^ 4 := by ring
              _ ≤ k := hk
              _ ≤ N0 + k := by omega
          have h2 : K ^ 2 ≤ Nat.sqrt (N0 + k) := Nat.le_sqrt.mpr (by simpa [sq] using h1)
          exact Nat.le_sqrt.mpr (by simpa [sq] using h2)
        have hpow_lim : Filter.Tendsto (fun k : ℕ => (1 / (2 : ℝ)) ^ Nat.sqrt (Nat.sqrt (N0 + k)))
            Filter.atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hM_inf
        have hMe_lim : Filter.Tendsto (fun k : ℕ =>
            (Nat.sqrt (Nat.sqrt (N0 + k)) : ℝ) * kakEps (N0 + k)) Filter.atTop (nhds 0) := by
          rw [Metric.tendsto_atTop]
          intro ε hε
          obtain ⟨K1, hK1⟩ := (Filter.tendsto_atTop_atTop.mp hM_inf) (Nat.ceil (1 / ε) + 1)
          refine ⟨max 1 K1, fun k hk => ?_⟩
          set n := N0 + k
          set M := Nat.sqrt (Nat.sqrt n)
          have hM_ge : Nat.ceil (1 / ε) + 1 ≤ M := hK1 k (le_trans (le_max_right _ _) hk)
          have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
          have hM_le_sqrt : (M : ℝ) ^ 2 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by
            have hsq1 : M ^ 2 ≤ Nat.sqrt n := Nat.sqrt_le' (Nat.sqrt n)
            have hsq2 : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n
            have hM4 : M ^ 4 < n + 1 := by
              calc
                M ^ 4 = (M ^ 2) ^ 2 := by ring
                _ ≤ (Nat.sqrt n) ^ 2 := Nat.pow_le_pow_left hsq1 2
                _ ≤ n := hsq2
                _ < n + 1 := Nat.lt_succ_self n
            have hM2_le : ((M : ℝ) ^ 2) ^ 2 < ((n + 1 : ℕ) : ℝ) := by
              exact_mod_cast (show (M ^ 2) ^ 2 < n + 1 by
                calc
                  (M ^ 2) ^ 2 = M ^ 4 := by ring
                  _ < n + 1 := hM4)
            rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ 2)]
            exact Real.sqrt_lt_sqrt (by positivity) hM2_le
          have hMe_bound : (M : ℝ) * kakEps n ≤ 1 / (2 * (M : ℝ)) := by
            dsimp [kakEps]
            rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
          have hM_big : 1 / ε < (M : ℝ) := by
            have h1 : (Nat.ceil (1 / ε) : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : Nat.ceil (1 / ε) < M)
            linarith [Nat.le_ceil (1 / ε)]
          have h12M : 1 / (2 * (M : ℝ)) < ε := by
            rw [div_lt_iff₀ (by positivity)]
            rw [div_lt_iff₀ hε] at hM_big
            linarith
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (kakEps_pos n).le)]
          exact lt_of_le_of_lt hMe_bound h12M
        have hadd_tend : Filter.Tendsto (fun k : ℕ => N0 + k) Filter.atTop Filter.atTop := by
          simpa [add_comm] using Filter.tendsto_add_atTop_nat N0
        have hS_shift : Filter.Tendsto (fun k : ℕ => (kakGreedy β (N0 + k)).1) Filter.atTop (nhds β) :=
          hS_tend.comp hadd_tend
        have hS_diff : Filter.Tendsto (fun k : ℕ => |(kakGreedy β (N0 + k)).1 - β|)
            Filter.atTop (nhds 0) := by
          simpa using (hS_shift.sub_const β).abs
        have hE_eq : E = fun k =>
            (3 * (kakGreedy β (N0 + k)).1 * ((1 / (2 : ℝ)) ^ Nat.sqrt (Nat.sqrt (N0 + k))) +
              2 * ((Nat.sqrt (Nat.sqrt (N0 + k)) : ℝ) * kakEps (N0 + k)) * (kakGreedy β (N0 + k)).1 +
              |(kakGreedy β (N0 + k)).1 - β|) / β := by
          ext k; dsimp [E]; simp only [one_div, inv_pow]; ring
        rw [hE_eq]
        have ht1 : Filter.Tendsto
            (fun k => 3 * (kakGreedy β (N0 + k)).1 * ((1 / (2 : ℝ)) ^ Nat.sqrt (Nat.sqrt (N0 + k))))
            Filter.atTop (nhds (3 * β * 0)) :=
          ((tendsto_const_nhds.mul hS_shift).mul hpow_lim)
        have ht2 : Filter.Tendsto
            (fun k => 2 * ((Nat.sqrt (Nat.sqrt (N0 + k)) : ℝ) * kakEps (N0 + k)) *
              (kakGreedy β (N0 + k)).1)
            Filter.atTop (nhds (2 * 0 * β)) :=
          ((tendsto_const_nhds.mul hMe_lim).mul hS_shift)
        have hsum : Filter.Tendsto
            (fun k => (3 * (kakGreedy β (N0 + k)).1 * ((1 / (2 : ℝ)) ^ Nat.sqrt (Nat.sqrt (N0 + k))) +
              2 * ((Nat.sqrt (Nat.sqrt (N0 + k)) : ℝ) * kakEps (N0 + k)) * (kakGreedy β (N0 + k)).1 +
              |(kakGreedy β (N0 + k)).1 - β|) / β)
            Filter.atTop (nhds ((3 * β * 0 + 2 * 0 * β + 0) / β)) :=
          ((ht1.add ht2).add hS_diff).div_const β
        simpa using hsum
      refine ⟨a', c', 1 / 8, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k; exact ha_lt_c (N0 + k)
      · intro k; exact ⟨ha_mono (by omega), hc_anti (by omega)⟩
      · intro k; exact hx_margin (N0 + k) (by omega)
      · intro k; exact ⟨E k, by rintro _ ⟨z, hz, rfl⟩; exact hL_pt k z hz⟩
      · have hS_nonneg : ∀ k : ℕ, 0 ≤ sSup ((fun z => |kakF z - kakF (a' k) - β * (z - a' k)| /
            (β * (c' k - a' k))) '' Set.Icc (a' k) (c' k)) := by
          intro k
          have hmem : a' k ∈ Set.Icc (a' k) (c' k) := ⟨le_rfl, (ha_lt_c (N0 + k)).le⟩
          have h0 : 0 ≤ |kakF (a' k) - kakF (a' k) - β * (a' k - a' k)| / (β * (c' k - a' k)) := by
            simp
          exact le_trans h0 (le_csSup ⟨E k, by rintro _ ⟨z, hz, rfl⟩; exact hL_pt k z hz⟩ ⟨a' k, hmem, rfl⟩)
        have hS_le_E : ∀ k : ℕ, sSup ((fun z => |kakF z - kakF (a' k) - β * (z - a' k)| /
            (β * (c' k - a' k))) '' Set.Icc (a' k) (c' k)) ≤ E k := by
          intro k
          have hne : ((fun z => |kakF z - kakF (a' k) - β * (z - a' k)| / (β * (c' k - a' k))) ''
              Set.Icc (a' k) (c' k)).Nonempty :=
            ⟨_, ⟨a' k, ⟨le_rfl, (ha_lt_c (N0 + k)).le⟩, rfl⟩⟩
          exact csSup_le hne (by rintro _ ⟨z, hz, rfl⟩; exact hL_pt k z hz)
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE_tend hS_nonneg hS_le_E
      · have hratio : ∀ k : ℕ, (c' (k + 1) - a' (k + 1)) / (c' k - a' k) = 1 / 2 := by
          intro k
          dsimp [a', c', a, c]
          push_cast
          have hp : (2 : ℝ) ^ (N0 + (k + 1)) = (2 : ℝ) ^ (N0 + k) * 2 := by
            have : N0 + (k + 1) = (N0 + k) + 1 := by omega
            rw [this, pow_succ]
          rw [hp]
          field_simp
          ring
        have hfun :
            (fun k => sSup ((fun z => |kakF z - kakF (a' k) - β * (z - a' k)| /
              (β * (c' k - a' k))) '' Set.Icc (a' k) (c' k)) /
              ((c' (k + 1) - a' (k + 1)) / (c' k - a' k))) =
            fun k => 2 * sSup ((fun z => |kakF z - kakF (a' k) - β * (z - a' k)| /
              (β * (c' k - a' k))) '' Set.Icc (a' k) (c' k)) := by
          ext k; rw [hratio k]; ring
        rw [hfun]
        have hS_nonneg : ∀ k : ℕ, 0 ≤ sSup ((fun z => |kakF z - kakF (a' k) - β * (z - a' k)| /
            (β * (c' k - a' k))) '' Set.Icc (a' k) (c' k)) := by
          intro k
          have hmem : a' k ∈ Set.Icc (a' k) (c' k) := ⟨le_rfl, (ha_lt_c (N0 + k)).le⟩
          have h0 : 0 ≤ |kakF (a' k) - kakF (a' k) - β * (a' k - a' k)| / (β * (c' k - a' k)) := by
            simp
          exact le_trans h0 (le_csSup ⟨E k, by rintro _ ⟨z, hz, rfl⟩; exact hL_pt k z hz⟩ ⟨a' k, hmem, rfl⟩)
        have hS_le_E : ∀ k : ℕ, sSup ((fun z => |kakF z - kakF (a' k) - β * (z - a' k)| /
            (β * (c' k - a' k))) '' Set.Icc (a' k) (c' k)) ≤ E k := by
          intro k
          have hne : ((fun z => |kakF z - kakF (a' k) - β * (z - a' k)| / (β * (c' k - a' k))) ''
              Set.Icc (a' k) (c' k)).Nonempty :=
            ⟨_, ⟨a' k, ⟨le_rfl, (ha_lt_c (N0 + k)).le⟩, rfl⟩⟩
          exact csSup_le hne (by rintro _ ⟨z, hz, rfl⟩; exact hL_pt k z hz)
        have hS_tend : Filter.Tendsto
            (fun k => sSup ((fun z => |kakF z - kakF (a' k) - β * (z - a' k)| /
              (β * (c' k - a' k))) '' Set.Icc (a' k) (c' k)))
            Filter.atTop (nhds 0) :=
          tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE_tend hS_nonneg hS_le_E
        simpa using hS_tend.const_mul 2
    exact (ppl003_linearity_equivalence kakF x β hβ).mpr ha_shift
