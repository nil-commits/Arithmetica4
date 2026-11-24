import Prize.PPL024_Analytic
import Prize.PPL024_Comb_Defs
import Prize.PPL024_Comb_Fourier
import Prize.PPL024_AnalyticTechLemmas

/-!
# Prize.PPL024_Main

**100% Unconditional Lean 4 Formalization of PPL 024 — Zhi-Wei Sun's Prime-Shifted Unit
Fractions Conjecture** (proved by Thomas F. Bloom, *"Unit fractions with shifted prime
denominators"*, `arXiv:2305.02689`, *Proc. Roy. Soc. Edinburgh Sect. A* 2025, combining with
*"On a density conjecture about unit fractions"*, `arXiv:2112.03726`).

## Main Unconditional Theorems (Native Mathlib Types)
1. `ppl024_sun_minus_one`: For every `r : ℚ` with `0 < r`, there exists a finite set `S : Finset ℕ`
   of primes (`∀ p ∈ S, Nat.Prime p`) such that `r = ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) - 1)`.
2. `ppl024_sun_plus_one`: For every `r : ℚ` with `0 < r`, there exists a finite set `S : Finset ℕ`
   of primes (`∀ p ∈ S, Nat.Prime p`) such that `r = ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) + 1)`.
3. `ppl024_sun_both`: Unified statement for all `r : ℚ` (`0 < r`) and both signs
   `d ∈ ({-1, 1} : Set ℤ)`.

Zero `sorry`, zero `admit`, zero custom `axiom`s.
-/

noncomputable section

open Finset Filter Topology Prize.PPL024
open scoped BigOperators Classical

namespace PPL024

/-! ## Section 1: Auxiliary Elementary Helpers -/

/-- A prime power `q` has `omega q = 1`. -/
private lemma omega_eq_one_of_isPrimePow {q : ℕ} (hq : IsPrimePow q) : omega q = 1 := by
  rw [isPrimePow_nat_iff] at hq
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  unfold omega
  rw [Nat.primeFactors_pow p hk.ne', hp.primeFactors, Finset.card_singleton]

/-- Three-set Bonferroni lower bound on non-negative sums. -/
private lemma sum_union3_ge {α : Type*} [DecidableEq α] (s₁ s₂ s₃ : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ s₁, f x) + (∑ x ∈ s₂, f x) + (∑ x ∈ s₃, f x) -
      (∑ x ∈ s₁ ∩ s₂, f x) - (∑ x ∈ s₁ ∩ s₃, f x) - (∑ x ∈ s₂ ∩ s₃, f x) ≤
      ∑ x ∈ s₁ ∪ s₂ ∪ s₃, f x := by
  have h12 := Finset.sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := f)
  have h123 := Finset.sum_union_inter (s₁ := s₁ ∪ s₂) (s₂ := s₃) (f := f)
  have hinter : (s₁ ∪ s₂) ∩ s₃ = (s₁ ∩ s₃) ∪ (s₂ ∩ s₃) := Finset.union_inter_distrib_right s₁ s₂ s₃
  have hsub := Finset.sum_union_inter (s₁ := s₁ ∩ s₃) (s₂ := s₂ ∩ s₃) (f := f)
  have hnn : 0 ≤ ∑ x ∈ (s₁ ∩ s₃) ∩ (s₂ ∩ s₃), f x := Finset.sum_nonneg fun x _ => hf x
  rw [hinter] at h123
  linarith

/-- If `n = a * m` with `Nat.Coprime a m` and `r ∥ m`, then `r ∥ n`. -/
private lemma ppowDiv_mul_left_of_coprime {a m r : ℕ} (hcop : Nat.Coprime a m) (hr : ppowDiv r m) :
    ppowDiv r (a * m) := by
  refine ⟨hr.1, dvd_mul_of_dvd_right hr.2.1 a, ?_⟩
  rw [Nat.mul_div_assoc a hr.2.1]
  have hcop_ra : Nat.Coprime r a := (Nat.Coprime.coprime_dvd_right hr.2.1 hcop).symm
  exact hcop_ra.mul_right hr.2.2

/-- If `n ≥ 1` and every `q ∈ exactPrimePowers n` divides either `w₁` or `w₂`, and `(n : ℤ) ∣ x`
with `x ≠ w₁` and `x ≠ w₂`, then `n ∣ (x - w₁).natAbs * (x - w₂).natAbs`. -/
private lemma dvd_natAbs_mul_of_exactPrimePowers_split {n : ℕ} (hn : n ≠ 0) {x w₁ w₂ : ℤ}
    (hxn : (n : ℤ) ∣ x) (hsplit : ∀ q ∈ exactPrimePowers n, (q : ℤ) ∣ w₁ ∨ (q : ℤ) ∣ w₂) :
    n ∣ (x - w₁).natAbs * (x - w₂).natAbs := by
  set E := exactPrimePowers n
  set E₁ := E.filter (fun q : ℕ => (q : ℤ) ∣ w₁)
  set E₂ := E.filter (fun q : ℕ => ¬ (q : ℤ) ∣ w₁)
  set n₁ : ℕ := ∏ q ∈ E₁, q
  set n₂ : ℕ := ∏ q ∈ E₂, q
  have hmul : n = n₁ * n₂ := by
    rw [← prod_exactPrimePowers hn]
    exact (Finset.prod_filter_mul_prod_filter_not E (fun q : ℕ => (q : ℤ) ∣ w₁) id).symm
  have hcop_E : Set.Pairwise (E : Set ℕ) Nat.Coprime := by
    intro r₁ hr₁ r₂ hr₂ hne
    obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hr₁
    obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.mp hr₂
    have h1 := Nat.prime_of_mem_primeFactors hp₁
    have h2 := Nat.prime_of_mem_primeFactors hp₂
    have hpne : p₁ ≠ p₂ := fun h => hne (by subst h; rfl)
    exact ((Nat.coprime_primes h1 h2).mpr hpne).pow _ _
  have hprod_dvd : ∀ (S : Finset ℕ) (m : ℕ), S ⊆ E → (∀ q ∈ S, q ∣ m) → (∏ q ∈ S, q) ∣ m := by
    intro S m hSE hdvd
    induction S using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hcop_a : Nat.Coprime a (∏ q ∈ s, q) :=
        Nat.Coprime.prod_right fun q hq =>
          hcop_E (hSE (Finset.mem_insert_self a s)) (hSE (Finset.mem_insert_of_mem hq))
            (fun h => ha (h ▸ hq))
      exact hcop_a.mul_dvd_of_dvd_of_dvd (hdvd a (Finset.mem_insert_self a s))
        (ih ((Finset.subset_insert a s).trans hSE) fun q hq => hdvd q (Finset.mem_insert_of_mem hq))
  have h1 : n₁ ∣ (x - w₁).natAbs := by
    apply hprod_dvd E₁ _ (Finset.filter_subset _ _)
    intro q hq
    have hqE := (Finset.mem_filter.mp hq).1
    have hqw₁ := (Finset.mem_filter.mp hq).2
    have hqn : q ∣ n := ((ppowDiv_iff_mem_exactPrimePowers hn).mpr hqE).2.1
    have hqx : (q : ℤ) ∣ x := dvd_trans (Int.natCast_dvd_natCast.mpr hqn) hxn
    exact Int.natCast_dvd.mp (dvd_sub hqx hqw₁)
  have h2 : n₂ ∣ (x - w₂).natAbs := by
    apply hprod_dvd E₂ _ (Finset.filter_subset _ _)
    intro q hq
    have hqE := (Finset.mem_filter.mp hq).1
    have hnotw₁ := (Finset.mem_filter.mp hq).2
    have hqw₂ : (q : ℤ) ∣ w₂ := (hsplit q hqE).resolve_left hnotw₁
    have hqn : q ∣ n := ((ppowDiv_iff_mem_exactPrimePowers hn).mpr hqE).2.1
    have hqx : (q : ℤ) ∣ x := dvd_trans (Int.natCast_dvd_natCast.mpr hqn) hxn
    exact Int.natCast_dvd.mp (dvd_sub hqx hqw₂)
  rw [hmul]
  exact mul_dvd_mul h1 h2

/-! ## Section 2: Bloom's Iterative Dichotomy (`prop-tech`, Section 5 of `arXiv:2112.03726`) -/

/-- **Bloom's Proposition 3 (`prop-tech`, Section 5 of `arXiv:2112.03726`)**:
For all sufficiently large `N`, `M ∈ [N^{1/2}, N]`, and `A ⊆ [M, N]` with
`ω(n) ∈ [0.99 log log N, 2 log log N]`, `R(A) ≥ (log N)^{-1/101}`, and
`R(A; q) ≥ (log N)^{-1/100}` for all `q ∈ 𝒬_A`:
either `∑_{q ∈ 𝒬_A} 1/q > (2/3) log log N` and there exists `B ⊆ A` with `R(B) ≥ R(A)/3` and
`∑_{q ∈ 𝒬_B} 1/q ≤ (2/3) log log N`, OR the Fourier interval-divisibility criterion holds
for `K = M N^{-2 / log log N}` and `η = 1 / (2 (log N)^{1/100})`. -/
theorem bloom_prop_tech_iter :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℝ) (A : Finset ℕ),
      (N : ℝ) ^ (1 / 2 : ℝ) ≤ M → M ≤ (N : ℝ) →
      (∀ n ∈ A, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ (N : ℝ)) →
      (∀ n ∈ A, (99 / 100 : ℝ) * Real.log (Real.log (N : ℝ)) ≤ (omega n : ℝ) ∧
        (omega n : ℝ) ≤ 2 * Real.log (Real.log (N : ℝ))) →
      (Real.log (N : ℝ)) ^ (-(1 / 101 : ℝ)) ≤ recSumReal A →
      (∀ q ∈ ppowersInSet A, 1 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ recSumQ A q) →
      ((¬ (∑ q ∈ ppowersInSet A, (1 : ℝ) / (q : ℝ) ≤ (2 / 3 : ℝ) * Real.log (Real.log (N : ℝ)))) ∧
       ∃ B : Finset ℕ, B ⊆ A ∧ (1 / 3 : ℝ) * recSumReal A ≤ recSumReal B ∧
         ∑ q ∈ ppowersInSet B, (1 : ℝ) / (q : ℝ) ≤ (2 / 3 : ℝ) * Real.log (Real.log (N : ℝ))) ∨
      (∀ z : ℤ,
        let K := M * (N : ℝ) ^ (-(2 : ℝ) / Real.log (Real.log (N : ℝ)))
        let η := 1 / (2 * (Real.log (N : ℝ)) ^ (1 / 100 : ℝ))
        M / Real.log (N : ℝ) ≤ ((A.filter (fun n => ¬ dividesInInterval z K n)).card : ℝ) ∨
        ∃ x : ℤ, |(x : ℝ) - (z : ℝ)| ≤ K / 2 ∧ ∀ q ∈ goodPrimePowers A M η K z, (q : ℤ) ∣ x) := by
  obtain ⟨C_pp, hCpp_pos, hCpp⟩ := Prize.PPL024.sum_inv_ppow_le
  have hLL : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- Asymptotic helper: `(log N)^a * (log log N)^b → 0` whenever `a < 0`
  have hpoly_log : ∀ (a : ℝ) (b : ℕ), 0 < a →
      Tendsto (fun N : ℕ => (Real.log (Real.log (N : ℝ))) ^ b / (Real.log (N : ℝ)) ^ a) atTop (𝓝 0) := by
    intro a b ha
    have h1 : Tendsto (fun u : ℝ => (Real.log u) ^ b / u ^ a) atTop (𝓝 0) := by
      have hexp : Tendsto (fun v : ℝ => (v / a) ^ b / Real.exp v) atTop (𝓝 0) := by
        have h0 : Tendsto (fun v : ℝ => Real.exp v / v ^ b) atTop atTop := by
          simpa using Real.tendsto_exp_div_pow_atTop b
        have hinv := (tendsto_inv_atTop_zero.comp h0).const_mul (a⁻¹ ^ b)
        rw [mul_zero] at hinv
        refine hinv.congr fun v => ?_
        simp only [Function.comp_apply, div_pow, inv_div, inv_pow]; ring
      refine (hexp.comp (Filter.Tendsto.const_mul_atTop ha Real.tendsto_log_atTop)).congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
      simp only [Function.comp_apply]
      rw [Real.rpow_def_of_pos (by linarith), mul_comm (Real.log u) a,
        mul_div_cancel_left₀ _ ha.ne']
    exact h1.comp hlogN
  -- `N^(1/2 / LL) / (log N)^2 → ∞`
  have hN_exp_LL : Tendsto (fun N : ℕ =>
      (N : ℝ) ^ ((1 / 2 : ℝ) / Real.log (Real.log (N : ℝ))) / (Real.log (N : ℝ)) ^ 2) atTop atTop := by
    -- `log(N^(1/(2 LL)) / (log N)^2) = log N / (2 LL) - 2 LL → ∞`
    have hlog_tend : Tendsto (fun N : ℕ =>
        Real.log (N : ℝ) / (2 * Real.log (Real.log (N : ℝ))) - 2 * Real.log (Real.log (N : ℝ)))
        atTop atTop := by
      have h1 : Tendsto (fun u : ℝ => Real.exp u / (2 * u) - 2 * u) atTop atTop := by
        have h2 : Tendsto (fun u : ℝ => Real.exp u / u ^ 2) atTop atTop := by
          simpa using Real.tendsto_exp_div_pow_atTop 2
        refine Filter.tendsto_atTop.mpr fun B => ?_
        filter_upwards [h2.eventually_ge_atTop 6, eventually_ge_atTop (max B 1)] with u hu2 huB
        have hu1 : 1 ≤ u := le_trans (le_max_right _ _) huB
        have hu_pos : 0 < u := by linarith
        have h3 : 6 * u ^ 2 ≤ Real.exp u := (le_div_iff₀ (by positivity)).mp hu2
        have h4 : 3 * u ≤ Real.exp u / (2 * u) := by
          rw [le_div_iff₀ (by positivity)]; nlinarith
        linarith [le_trans (le_max_left B 1) huB]
      refine (h1.comp hLL).congr' ?_
      filter_upwards [eventually_ge_atTop 3] with N hN
      have hlp : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      simp only [Function.comp_apply, Real.exp_log hlp]
    refine (Real.tendsto_exp_atTop.comp hlog_tend).congr' ?_
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hNp : (0 : ℝ) < (N : ℝ) := by positivity
    have hlp : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    simp only [Function.comp_apply]
    rw [Real.exp_sub, Real.rpow_def_of_pos hNp,
      show (2 : ℝ) * Real.log (Real.log (N : ℝ)) = ((2 : ℕ) : ℝ) * Real.log (Real.log (N : ℝ)) by norm_num,
      Real.exp_nat_mul, Real.exp_log hlp]
    congr 1; congr 1; ring
  -- `N^(1/4) ≥ 2` and `K ≥ 2`
  have hN14 : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [
    eventually_ge_atTop 16,
    ppl024_lem_basic,
    ppl024_lem_rtop (2 / 99 : ℝ) (by norm_num) (by norm_num),
    ppl024_lem_usingq,
    Prize.PPL024.divisor_bound_sq (1 / 20 : ℝ) (by norm_num),
    hLL.eventually_ge_atTop (max 2000 (1000 * C_pp)),
    hlogN.eventually_ge_atTop 16,
    (hpoly_log (1 / 9900 : ℝ) 3 (by norm_num)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    (hpoly_log (1 / 10100 : ℝ) 1 (by norm_num)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 24)),
    (hpoly_log (1 / 10100 : ℝ) 0 (by norm_num)).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (24 * C_pp + 1))),
    (hpoly_log (100 / 101 : ℝ) 0 (by norm_num)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 12)),
    hN_exp_LL.eventually_ge_atTop 24,
    hN14.eventually_ge_atTop 4
  ] with N hN16 hBasic hRtop hUsingq hDivSq hLL_big hlogN16 hSm1 hSm2 hSm3 hSm4 hNexp hN14_big
  intro M A hMN_lo hMN_hi hA hω hRA hRq
  set LL : ℝ := Real.log (Real.log (N : ℝ))
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hLL_ge2000 : 2000 ≤ LL := le_trans (le_max_left _ _) hLL_big
  have hLL_pos : 0 < LL := by linarith
  have hM_pos : 0 < M := lt_of_lt_of_le (Real.rpow_pos_of_pos hN_pos _) hMN_lo
  have h0A : 0 ∉ A := fun h => by
    have := (hA 0 h).1; norm_num at this; linarith
  have hA_icc : ∀ n ∈ A, 1 ≤ n ∧ n ≤ N := fun n hn =>
    ⟨by have h1 : (1 : ℝ) ≤ (n : ℝ) := by
          have h2 : (4 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := hN14_big
          have h3 : (N : ℝ) ^ (1 / 4 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) (by norm_num)
          linarith [(hA n hn).1]
        exact_mod_cast h1,
     by exact_mod_cast (hA n hn).2⟩
  -- Upper bound `∑ q ∈ ppowersInSet A, 1/q ≤ 1.001 * LL`
  have hQ_tot_le : ∑ q ∈ ppowersInSet A, (1 : ℝ) / (q : ℝ) ≤ (1001 / 1000 : ℝ) * LL := by
    have hsub : ppowersInSet A ⊆ (Finset.Icc 1 N).filter IsPrimePow := fun q hq =>
      Finset.mem_filter.mpr ⟨ppowersInSet_subset_Icc hA_icc hq, mem_ppowersInSet_isPrimePow h0A hq⟩
    have h1 := (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
      (hCpp N (by omega))
    have hCpp_le : C_pp ≤ (1 / 1000 : ℝ) * LL := by
      have := le_trans (le_max_right 2000 (1000 * C_pp)) hLL_big
      linarith
    linarith
  -- Either Case 2 holds, or there exists a bad `z : ℤ`
  set K : ℝ := M * (N : ℝ) ^ (-(2 : ℝ) / LL)
  set η : ℝ := 1 / (2 * (Real.log (N : ℝ)) ^ (1 / 100 : ℝ))
  by_cases hCase2 : ∀ z : ℤ,
      M / Real.log (N : ℝ) ≤ ((A.filter (fun n => ¬ dividesInInterval z K n)).card : ℝ) ∨
      ∃ x : ℤ, |(x : ℝ) - (z : ℝ)| ≤ K / 2 ∧ ∀ q ∈ goodPrimePowers A M η K z, (q : ℤ) ∣ x
  · exact Or.inr hCase2
  push Not at hCase2
  obtain ⟨z, hmiss_lt, hno_x⟩ := hCase2
  have hK_pos : 0 < K := by positivity
  have hK_le_M : K ≤ M := by
    have h1 : (N : ℝ) ^ (-(2 : ℝ) / LL) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ N))
        (div_nonpos_of_nonpos_of_nonneg (by norm_num) hLL_pos.le)
    calc K = M * (N : ℝ) ^ (-(2 : ℝ) / LL) := rfl
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left h1 hM_pos.le
      _ = M := mul_one M
  have hK_ge2 : 2 ≤ K := by
    have h1 : (N : ℝ) ^ (1 / 4 : ℝ) ≤ K := by
      calc (N : ℝ) ^ (1 / 4 : ℝ) = (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
            rw [← Real.rpow_add hN_pos]; norm_num
        _ ≤ M * (N : ℝ) ^ (-(2 : ℝ) / LL) := by
            refine mul_le_mul hMN_lo (Real.rpow_le_rpow_of_exponent_le
              (by exact_mod_cast (by omega : 1 ≤ N)) ?_) (by positivity) hM_pos.le
            rw [le_div_iff₀ hLL_pos]; linarith
    linarith
  set A_I : Finset ℕ := A.filter (fun n => dividesInInterval z K n)
  set E_I : Finset ℕ := (ppowersInSet A).filter (fun q => η < recSumQ A_I q)
  -- Step 1: `goodPrimePowers A M η K z ⊆ E_I`
  have hD_sub_E : goodPrimePowers A M η K z ⊆ E_I := by
    intro q hq
    obtain ⟨hqA, hq_card⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨hqA, ?_⟩
    have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (mem_ppowersInSet_pos h0A hqA)
    have hdiff : recSumQ A q - recSumQ A_I q ≤
        (((exactSlice A q).filter (fun n => ¬ dividesInInterval z K n)).card : ℝ) * ((q : ℝ) / M) := by
      have hsub : exactSlice A q \ exactSlice A_I q =
          (exactSlice A q).filter (fun n => ¬ dividesInInterval z K n) := by
        ext n; simp only [exactSlice, A_I, Finset.mem_sdiff, Finset.mem_filter]; tauto
      have hle_sl : exactSlice A_I q ⊆ exactSlice A q := Finset.filter_subset_filter _ (Finset.filter_subset _ _)
      have hsd : recSumQ A q - recSumQ A_I q =
          ∑ n ∈ exactSlice A q \ exactSlice A_I q, (q : ℝ) / (n : ℝ) := by
        unfold recSumQ
        have := Finset.sum_sdiff (f := fun n : ℕ => (q : ℝ) / (n : ℝ)) hle_sl
        linarith
      rw [hsd, hsub]
      calc ∑ n ∈ (exactSlice A q).filter (fun n => ¬ dividesInInterval z K n), (q : ℝ) / (n : ℝ)
          ≤ ∑ _n ∈ (exactSlice A q).filter (fun n => ¬ dividesInInterval z K n), (q : ℝ) / M := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hnA := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
            exact div_le_div_of_nonneg_left hq_pos.le hM_pos (hA n hnA).1
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hlt_η : (((exactSlice A q).filter (fun n => ¬ dividesInInterval z K n)).card : ℝ) * ((q : ℝ) / M) < η := by
      calc (((exactSlice A q).filter (fun n => ¬ dividesInInterval z K n)).card : ℝ) * ((q : ℝ) / M)
          < (η * M / (q : ℝ)) * ((q : ℝ) / M) := mul_lt_mul_of_pos_right hq_card (by positivity)
        _ = η := by field_simp [hq_pos.ne', hM_pos.ne']
    have h2η : 2 * η = 1 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) := by
      dsimp only [η]
      have hp : (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hlogN_pos _).ne'
      field_simp [hp]
    have hRqA := hRq q hqA
    linarith
  -- Step 2: For every `q ∈ E_I`, find `x_q : ℤ` with `|x_q - z| ≤ K / 2`, `(q : ℤ) ∣ x_q`, and
  -- `∑_{r ∈ ppowersInSet A, (r : ℤ) ∣ x_q} 1/r ≥ (352 / 1000) * LL`!
  have hex_xq : ∀ q ∈ E_I, ∃ x : ℤ, |(x : ℝ) - (z : ℝ)| ≤ K / 2 ∧ (q : ℤ) ∣ x ∧
      (352 / 1000 : ℝ) * LL ≤
        ∑ r ∈ (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ x), (1 : ℝ) / (r : ℝ) := by
    intro q hqE
    have hqA : q ∈ ppowersInSet A := (Finset.mem_filter.mp hqE).1
    have hRq_gt : η < recSumQ A_I q := (Finset.mem_filter.mp hqE).2
    have hq_pp : IsPrimePow q := mem_ppowersInSet_isPrimePow h0A hqA
    have hq1 : 1 ≤ q := hq_pp.pos
    -- Show `(log N)^{-1/2} ≤ η < recSumQ A_I q`
    have hRq_lo : (Real.log (N : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ recSumQ A_I q := by
      have h1 : (Real.log (N : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ η := by
        dsimp only [η]
        rw [Real.rpow_neg hlogN_pos.le, ← one_div,
          div_le_div_iff₀ (Real.rpow_pos_of_pos hlogN_pos _) (by positivity)]
        have h2 : (2 : ℝ) ≤ (Real.log (N : ℝ)) ^ (49 / 100 : ℝ) := by
          have h16 : (16 : ℝ) ≤ Real.log (N : ℝ) := hlogN16
          have hpow := Real.rpow_le_rpow (by norm_num) h16 (by norm_num : (0 : ℝ) ≤ 49 / 100)
          have h2_le : (2 : ℝ) ≤ (16 : ℝ) ^ (49 / 100 : ℝ) := by
            rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
            calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
              _ ≤ (2 : ℝ) ^ (4 * (49 / 100 : ℝ)) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          linarith
        have hmul := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hlogN_pos.le (1 / 100 : ℝ))
        rw [← Real.rpow_add hlogN_pos] at hmul
        norm_num at hmul; linarith
      linarith
    obtain ⟨d, hd1, hcop_qd, hqd_gt, hωd_lt, hslice_ge⟩ :=
      hUsingq M A_I q hMN_lo hMN_hi
        (fun n hn => let hnA := (Finset.mem_filter.mp hn).1; ⟨(hA n hnA).1, (hA n hnA).2, (hω n hnA).2⟩)
        hq1 hRq_lo
    set Sq := (exactSlice A_I q).filter (fun n => q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))
    set Aq := Sq.image (fun n => n / (q * d))
    have hqd_pos : 0 < q * d := Nat.mul_pos hq1 hd1
    have hinj_q : Set.InjOn (fun n => n / (q * d)) (Sq : Set ℕ) := by
      intro n₁ hn₁ n₂ hn₂ heq
      dsimp only at heq
      rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2.1,
          ← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2.1, heq]
    have hRAq_eq : recSumReal Aq = ∑ n ∈ Sq, ((q * d : ℕ) : ℝ) / (n : ℝ) := by
      unfold recSumReal
      rw [Finset.sum_image (f := fun m : ℕ => (1 : ℝ) / (m : ℝ)) hinj_q]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hdvd := (Finset.mem_filter.mp hn).2.1
      have hmul_eq : n = (q * d) * (n / (q * d)) := (Nat.mul_div_cancel' hdvd).symm
      have hqdR : (q : ℝ) * (d : ℝ) ≠ 0 := by exact_mod_cast hqd_pos.ne'
      conv_rhs => rw [hmul_eq]
      push_cast; field_simp [hqdR]
    -- Show `(log N)^{-1/99} ≤ recSumReal Aq`
    have hRAq_ge : (Real.log (N : ℝ)) ^ (-(2 / 99 : ℝ) / 2) ≤ recSumReal Aq := by
      have h1 : (Real.log (N : ℝ)) ^ (-(1 / 99 : ℝ)) ≤ η / LL ^ 3 := by
        dsimp only [η]
        rw [Real.rpow_neg hlogN_pos.le, ← one_div, div_div,
          div_le_div_iff₀ (Real.rpow_pos_of_pos hlogN_pos _) (by positivity)]
        have hsm := (div_lt_iff₀ (Real.rpow_pos_of_pos hlogN_pos (1 / 9900 : ℝ))).mp hSm1
        have h2 : 2 * LL ^ 3 ≤ (Real.log (N : ℝ)) ^ (1 / 9900 : ℝ) := by linarith
        have hmul := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hlogN_pos.le (1 / 100 : ℝ))
        have hadd : (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) * (Real.log (N : ℝ)) ^ (1 / 9900 : ℝ) =
            (Real.log (N : ℝ)) ^ (1 / 99 : ℝ) := by
          rw [← Real.rpow_add hlogN_pos]; congr 1; norm_num
        linarith
      have h2 : η / LL ^ 3 ≤ recSumQ A_I q / LL ^ 3 := div_le_div_of_nonneg_right hRq_gt.le (by positivity)
      rw [show -(2 / 99 : ℝ) / 2 = -(1 / 99 : ℝ) by norm_num]
      linarith
    have hSq_ne : Sq.Nonempty := by
      by_contra hemp
      have hAq_emp : Aq = ∅ := by simp [Aq, Finset.not_nonempty_iff_eq_empty.mp hemp]
      rw [hAq_emp, recSumReal_empty] at hRAq_ge
      linarith [Real.rpow_pos_of_pos hlogN_pos (-(2 / 99 : ℝ) / 2)]
    obtain ⟨n₀, hn₀⟩ := hSq_ne
    have hn₀_AI : n₀ ∈ A_I := (Finset.mem_filter.mp (Finset.mem_filter.mp hn₀).1).1
    obtain ⟨xq, hxq_int, hxq_dvd0⟩ := (Finset.mem_filter.mp hn₀_AI).2
    have hqd_dvd_xq : ((q * d : ℕ) : ℤ) ∣ xq :=
      dvd_trans (Int.natCast_dvd_natCast.mpr (Finset.mem_filter.mp hn₀).2.1) hxq_dvd0
    -- Uniqueness: EVERY `n ∈ Sq` divides `xq`!
    have hall_dvd_xq : ∀ n ∈ Sq, (n : ℤ) ∣ xq := by
      intro n hn
      have hn_AI : n ∈ A_I := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
      obtain ⟨x', hx'_int, hx'_dvd⟩ := (Finset.mem_filter.mp hn_AI).2
      have hqd_dvd_x' : ((q * d : ℕ) : ℤ) ∣ x' :=
        dvd_trans (Int.natCast_dvd_natCast.mpr (Finset.mem_filter.mp hn).2.1) hx'_dvd
      have hEq : x' = xq := by
        by_contra hne
        have hdvd_sub : q * d ∣ (x' - xq).natAbs := Int.natCast_dvd.mp (dvd_sub hqd_dvd_x' hqd_dvd_xq)
        have hpos_sub : 0 < (x' - xq).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
        have hle_sub : q * d ≤ (x' - xq).natAbs := Nat.le_of_dvd hpos_sub hdvd_sub
        have habs_eq : ((x' - xq).natAbs : ℝ) = |(x' : ℝ) - (xq : ℝ)| := by
          rw [← Int.cast_natCast (x' - xq).natAbs, Int.natCast_natAbs, Int.cast_abs]; push_cast; rfl
        have htri : |(x' : ℝ) - (xq : ℝ)| ≤ K := by
          have h1 := abs_sub_le (x' : ℝ) (z : ℝ) (xq : ℝ)
          rw [abs_sub_comm (z : ℝ) (xq : ℝ)] at h1
          linarith
        have hleR : ((q * d : ℕ) : ℝ) ≤ K := by
          have : ((q * d : ℕ) : ℝ) ≤ ((x' - xq).natAbs : ℝ) := by exact_mod_cast hle_sub
          linarith
        linarith
      rwa [← hEq]
    -- Apply `hRtop` to `Aq`!
    have h0Aq : 0 ∉ Aq := by
      intro h0m
      obtain ⟨n, hn, hdiv0⟩ := Finset.mem_image.mp h0m
      have hnA := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).1
      have hn_pos : 0 < n := (hA_icc n hnA).1
      have hdvd := (Finset.mem_filter.mp hn).2.1
      have : 0 < n / (q * d) := Nat.div_pos (Nat.le_of_dvd hn_pos hdvd) hqd_pos
      omega
    have hωAq : ∀ m ∈ Aq, (1 - 2 / 99 : ℝ) * LL ≤ (omega m : ℝ) ∧ (omega m : ℝ) ≤ 2 * LL := by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
      have hnA := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).1
      have hdvd := (Finset.mem_filter.mp hn).2.1
      have hn_pos : 0 < n := (hA_icc n hnA).1
      have hmul_eq : n = q * d * (n / (q * d)) := (Nat.mul_div_cancel' hdvd).symm
      have hdiv_pos : 0 < n / (q * d) := Nat.div_pos (Nat.le_of_dvd hn_pos hdvd) hqd_pos
      have hsub_pf : (n / (q * d)).primeFactors ⊆ n.primeFactors := by
        intro p hp
        have hp' := Nat.mem_primeFactors.mp hp
        have hdiv_dvd : n / (q * d) ∣ n := ⟨q * d, by rw [mul_comm]; exact hmul_eq⟩
        exact Nat.mem_primeFactors.mpr ⟨hp'.1, dvd_trans hp'.2.1 hdiv_dvd, hn_pos.ne'⟩
      have hhi : (omega (n / (q * d)) : ℝ) ≤ 2 * LL :=
        ((by exact_mod_cast Finset.card_le_card hsub_pf) : (omega (n / (q * d)) : ℝ) ≤ (omega n : ℝ)).trans (hω n hnA).2
      have hunion_pf : n.primeFactors ⊆ q.primeFactors ∪ d.primeFactors ∪ (n / (q * d)).primeFactors := by
        intro p hp
        have hp' := Nat.mem_primeFactors.mp hp
        rw [hmul_eq] at hp'
        rcases hp'.1.dvd_mul.mp hp'.2.1 with hqd_p | hm_p
        · rcases hp'.1.dvd_mul.mp hqd_p with hq_p | hd_p
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hp'.1, hq_p, by omega⟩))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp'.1, hd_p, by omega⟩))
        · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp'.1, hm_p, hdiv_pos.ne'⟩)
      have hcard_le : omega n ≤ omega q + omega d + omega (n / (q * d)) := by
        unfold omega
        exact (Finset.card_le_card hunion_pf).trans
          ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
      have hωq1 : omega q = 1 := omega_eq_one_of_isPrimePow hq_pp
      have hcard_R : (omega n : ℝ) ≤ 1 + (omega d : ℝ) + (omega (n / (q * d)) : ℝ) := by
        rw [hωq1] at hcard_le; exact_mod_cast hcard_le
      have hlo : (1 - 2 / 99 : ℝ) * LL ≤ (omega (n / (q * d)) : ℝ) := by
        have h1 := (hω n hnA).1
        linarith
      exact ⟨hlo, hhi⟩
    have hrtop_bd := hRtop Aq h0Aq hRAq_ge hωAq
    -- Show `ppowersInSet Aq ⊆ (ppowersInSet A).filter (fun r => (r : ℤ) ∣ xq)`
    have hQAq_sub : ppowersInSet Aq ⊆ (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ xq) := by
      intro r hr
      obtain ⟨m, hm⟩ := (mem_ppowersInSet_iff h0Aq).mp hr
      obtain ⟨hmAq, hrm⟩ := Finset.mem_filter.mp hm
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hmAq
      have hnA := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).1
      have hdvd := (Finset.mem_filter.mp hn).2.1
      have hcop := (Finset.mem_filter.mp hn).2.2
      have hmul_eq : n = q * d * (n / (q * d)) := (Nat.mul_div_cancel' hdvd).symm
      have hrn : ppowDiv r n := by
        rw [hmul_eq]; exact ppowDiv_mul_left_of_coprime hcop hrm
      have hrA : r ∈ ppowersInSet A := (mem_ppowersInSet_iff h0A).mpr ⟨n, Finset.mem_filter.mpr ⟨hnA, hrn⟩⟩
      have hrx : (r : ℤ) ∣ xq := dvd_trans (Int.natCast_dvd_natCast.mpr hrn.2.1) (hall_dvd_xq n hn)
      exact Finset.mem_filter.mpr ⟨hrA, hrx⟩
    -- Check `(1 - 2 * (2 / 99)) * exp (-1) ≥ 352 / 1000`
    have hconst : (352 / 1000 : ℝ) ≤ (1 - 2 * (2 / 99 : ℝ)) * Real.exp (-1) := by
      have hexp1 : Real.exp 1 < (2718281829 / 1000000000 : ℝ) := by linarith [Real.exp_one_lt_d9]
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos 1)]
      nlinarith
    have hsum_ge : (352 / 1000 : ℝ) * LL ≤
        ∑ r ∈ (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ xq), (1 : ℝ) / (r : ℝ) :=
      (mul_le_mul_of_nonneg_right hconst hLL_pos.le).trans
        (hrtop_bd.trans (Finset.sum_le_sum_of_subset_of_nonneg hQAq_sub fun _ _ _ => by positivity))
    exact ⟨xq, hxq_int, dvd_trans (Int.natCast_dvd_natCast.mpr (dvd_mul_right q d)) hqd_dvd_xq, hsum_ge⟩
  -- Pick `xFn q` for each `q ∈ E_I` via Classical.choose
  let xFn : ℕ → ℤ := fun q => if h : q ∈ E_I then (hex_xq q h).choose else 0
  have hxFn_prop : ∀ q ∈ E_I, |(xFn q : ℝ) - (z : ℝ)| ≤ K / 2 ∧ (q : ℤ) ∣ xFn q ∧
      (352 / 1000 : ℝ) * LL ≤
        ∑ r ∈ (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ xFn q), (1 : ℝ) / (r : ℝ) := by
    intro q hq
    simp only [xFn, dif_pos hq]
    exact (hex_xq q hq).choose_spec
  set X_set : Finset ℤ := E_I.image xFn
  -- Helper: any two distinct `w₁, w₂ ∈ X_set` have small common divisor sum `≤ 0.01 * LL`
  have hX_prop : ∀ w ∈ X_set, |(w : ℝ) - (z : ℝ)| ≤ K / 2 ∧
      (352 / 1000 : ℝ) * LL ≤
        ∑ r ∈ (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ w), (1 : ℝ) / (r : ℝ) := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨(hxFn_prop q hq).1, (hxFn_prop q hq).2.2⟩
  have hcommon_le : ∀ w₁ ∈ X_set, ∀ w₂ ∈ X_set, w₁ ≠ w₂ →
      ∑ r ∈ (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ w₁) ∩
            (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ w₂), (1 : ℝ) / (r : ℝ) ≤
        (1 / 100 : ℝ) * LL := by
    intro w₁ hw₁ w₂ hw₂ hne
    have hdiff : |(w₁ - w₂ : ℝ)| ≤ (N : ℝ) := by
      have h1 := abs_sub_le (w₁ : ℝ) (z : ℝ) (w₂ : ℝ)
      rw [abs_sub_comm (z : ℝ) (w₂ : ℝ)] at h1
      have h2 : |(w₁ : ℝ) - (w₂ : ℝ)| ≤ K := by linarith [(hX_prop w₁ hw₁).1, (hX_prop w₂ hw₂).1]
      linarith
    have hsub : (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ w₁) ∩
          (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ w₂) ⊆
        (Finset.Icc 1 N).filter (fun q : ℕ => IsPrimePow q ∧ (q : ℤ) ∣ w₁ ∧ (q : ℤ) ∣ w₂) := by
      intro r hr
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hr
      have hrA := (Finset.mem_filter.mp h1).1
      exact Finset.mem_filter.mpr ⟨ppowersInSet_subset_Icc hA_icc hrA,
        mem_ppowersInSet_isPrimePow h0A hrA, (Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans (hBasic w₁ w₂ hne hdiff)
  -- Step 3: Show `X_set.card = 2`!
  have hX_ge2 : 2 ≤ X_set.card := by
    by_contra hlt2
    have hle1 : X_set.card ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
    · have hE_emp : E_I = ∅ := by
        rw [Finset.card_eq_zero, Finset.image_eq_empty] at h0; exact h0
      obtain ⟨q, hqD, _⟩ := hno_x z (by simp; linarith)
      have hqE := hD_sub_E hqD
      rw [hE_emp] at hqE; exact Finset.notMem_empty _ hqE
    · obtain ⟨w, hw_eq⟩ := Finset.card_eq_one.mp h1
      have hw_mem : w ∈ X_set := by rw [hw_eq]; exact Finset.mem_singleton_self w
      obtain ⟨q, hqD, hq_ndvd⟩ := hno_x w (hX_prop w hw_mem).1
      have hqE := hD_sub_E hqD
      have hxq_mem : xFn q ∈ X_set := Finset.mem_image_of_mem xFn hqE
      rw [hw_eq, Finset.mem_singleton] at hxq_mem
      have hqdvd := (hxFn_prop q hqE).2.1
      rw [hxq_mem] at hqdvd
      exact hq_ndvd hqdvd
  have hX_le2 : X_set.card ≤ 2 := by
    by_contra hgt2
    have hge3 : 3 ≤ X_set.card := by omega
    obtain ⟨w₁, hw₁⟩ := Finset.card_pos.mp (by omega : 0 < X_set.card)
    have hcard1 : 2 ≤ (X_set.erase w₁).card := by rw [Finset.card_erase_of_mem hw₁]; omega
    obtain ⟨w₂, hw₂'⟩ := Finset.card_pos.mp (by omega : 0 < (X_set.erase w₁).card)
    have hcard2 : 1 ≤ ((X_set.erase w₁).erase w₂).card := by rw [Finset.card_erase_of_mem hw₂']; omega
    obtain ⟨w₃, hw₃'⟩ := Finset.card_pos.mp (by omega : 0 < ((X_set.erase w₁).erase w₂).card)
    have hw₂ : w₂ ∈ X_set := Finset.mem_of_mem_erase hw₂'
    have hne12 : w₁ ≠ w₂ := (Finset.ne_of_mem_erase hw₂').symm
    have hw₃'' : w₃ ∈ X_set.erase w₁ := Finset.mem_of_mem_erase hw₃'
    have hw₃ : w₃ ∈ X_set := Finset.mem_of_mem_erase hw₃''
    have hne13 : w₁ ≠ w₃ := (Finset.ne_of_mem_erase hw₃'').symm
    have hne23 : w₂ ≠ w₃ := (Finset.ne_of_mem_erase hw₃').symm
    set Q₁ := (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ w₁)
    set Q₂ := (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ w₂)
    set Q₃ := (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ w₃)
    have hbonf := sum_union3_ge Q₁ Q₂ Q₃ (fun r : ℕ => (1 : ℝ) / (r : ℝ)) (fun _ => by positivity)
    have hsub3 : Q₁ ∪ Q₂ ∪ Q₃ ⊆ ppowersInSet A :=
      Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
        (Finset.filter_subset _ _)
    have hle_tot : ∑ r ∈ Q₁ ∪ Q₂ ∪ Q₃, (1 : ℝ) / (r : ℝ) ≤ ∑ r ∈ ppowersInSet A, (1 : ℝ) / (r : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub3 fun _ _ _ => by positivity
    have h1 := (hX_prop w₁ hw₁).2
    have h2 := (hX_prop w₂ hw₂).2
    have h3 := (hX_prop w₃ hw₃).2
    have h12 := hcommon_le w₁ hw₁ w₂ hw₂ hne12
    have h13 := hcommon_le w₁ hw₁ w₃ hw₃ hne13
    have h23 := hcommon_le w₂ hw₂ w₃ hw₃ hne23
    linarith
  have hX_eq2 : X_set.card = 2 := le_antisymm hX_le2 hX_ge2
  obtain ⟨w₁, w₂, hne12, hX_pair⟩ := Finset.card_eq_two.mp hX_eq2
  have hw₁ : w₁ ∈ X_set := by rw [hX_pair]; simp
  have hw₂ : w₂ ∈ X_set := by rw [hX_pair]; simp
  set Q₁ := (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ w₁)
  set Q₂ := (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ w₂)
  -- Show `∑ q ∈ ppowersInSet A, 1/q > (2/3) * LL`
  have hQ_gt_23 : ¬ (∑ q ∈ ppowersInSet A, (1 : ℝ) / (q : ℝ) ≤ (2 / 3 : ℝ) * LL) := by
    have hui := Finset.sum_union_inter (s₁ := Q₁) (s₂ := Q₂) (f := fun r : ℕ => (1 : ℝ) / (r : ℝ))
    have hsub12 : Q₁ ∪ Q₂ ⊆ ppowersInSet A :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hle_tot : ∑ r ∈ Q₁ ∪ Q₂, (1 : ℝ) / (r : ℝ) ≤ ∑ r ∈ ppowersInSet A, (1 : ℝ) / (r : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub12 fun _ _ _ => by positivity
    have h1 := (hX_prop w₁ hw₁).2
    have h2 := (hX_prop w₂ hw₂).2
    have h12 := hcommon_le w₁ hw₁ w₂ hw₂ hne12
    linarith
  -- Step 4: Split `A` into `A₁`, `A₂`, `A₀`!
  set A₁ := A.filter (fun n : ℕ => (n : ℤ) ∣ w₁)
  set A₂ := A.filter (fun n : ℕ => (n : ℤ) ∣ w₂)
  set A₀ := A \ (A₁ ∪ A₂)
  have hQA_le_23 : ∀ (Ai : Finset ℕ) (wi wj : ℤ),
      Ai ⊆ A → (∀ n ∈ Ai, (n : ℤ) ∣ wi) → wi ∈ X_set → wj ∈ X_set → wi ≠ wj →
      ∑ r ∈ ppowersInSet Ai, (1 : ℝ) / (r : ℝ) ≤ (2 / 3 : ℝ) * LL := by
    intro Ai wi wj hAiA hAid hwi hwj hneij
    set Qi := (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ wi)
    set Qj := (ppowersInSet A).filter (fun r : ℕ => (r : ℤ) ∣ wj)
    have hsub_i : ppowersInSet Ai ⊆ Qi := by
      intro r hr
      have h0Ai : 0 ∉ Ai := fun h => h0A (hAiA h)
      obtain ⟨n, hn⟩ := (mem_ppowersInSet_iff h0Ai).mp hr
      obtain ⟨hnAi, hrn⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨ppowersInSet_mono hAiA hr,
        dvd_trans (Int.natCast_dvd_natCast.mpr hrn.2.1) (hAid n hnAi)⟩
    have hle_Qi : ∑ r ∈ ppowersInSet Ai, (1 : ℝ) / (r : ℝ) ≤ ∑ r ∈ Qi, (1 : ℝ) / (r : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub_i fun _ _ _ => by positivity
    have hui := Finset.sum_union_inter (s₁ := Qi) (s₂ := Qj) (f := fun r : ℕ => (1 : ℝ) / (r : ℝ))
    have hsub_ij : Qi ∪ Qj ⊆ ppowersInSet A :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hle_tot : ∑ r ∈ Qi ∪ Qj, (1 : ℝ) / (r : ℝ) ≤ ∑ r ∈ ppowersInSet A, (1 : ℝ) / (r : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub_ij fun _ _ _ => by positivity
    have hj := (hX_prop wj hwj).2
    have hij := hcommon_le wi hwi wj hwj hneij
    linarith
  by_cases hA1_big : (1 / 3 : ℝ) * recSumReal A ≤ recSumReal A₁
  · exact Or.inl ⟨hQ_gt_23, A₁, Finset.filter_subset _ _, hA1_big,
      hQA_le_23 A₁ w₁ w₂ (Finset.filter_subset _ _) (fun n hn => (Finset.mem_filter.mp hn).2) hw₁ hw₂ hne12⟩
  by_cases hA2_big : (1 / 3 : ℝ) * recSumReal A ≤ recSumReal A₂
  · exact Or.inl ⟨hQ_gt_23, A₂, Finset.filter_subset _ _, hA2_big,
      hQA_le_23 A₂ w₂ w₁ (Finset.filter_subset _ _) (fun n hn => (Finset.mem_filter.mp hn).2) hw₂ hw₁ hne12.symm⟩
  -- Step 5: Otherwise `R(A₀) ≥ R(A) / 3` — derive contradiction via `divisor_bound_sq`!
  exfalso
  push Not at hA1_big hA2_big
  have hA0_big : (1 / 3 : ℝ) * recSumReal A ≤ recSumReal A₀ := by
    have hcov : A ⊆ A₀ ∪ (A₁ ∪ A₂) := by
      intro n hn
      by_cases h12 : n ∈ A₁ ∪ A₂
      · exact Finset.mem_union_right _ h12
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hn, h12⟩)
    have h1 := recSumReal_mono hcov
    have h2 := recSumReal_union_le A₀ (A₁ ∪ A₂)
    have h3 := recSumReal_union_le A₁ A₂
    linarith
  -- Prune `A₀` to `A' = {n ∈ A_I ∩ A₀ : ∀ q ∈ exactPrimePowers n, q ∈ E_I}`
  set A' : Finset ℕ := (A_I ∩ A₀).filter (fun n => ∀ q ∈ exactPrimePowers n, q ∈ E_I)
  have hloss_A' : recSumReal (A₀ \ A') ≤ (1 / 6 : ℝ) * (Real.log (N : ℝ)) ^ (-(1 / 101 : ℝ)) := by
    have hcov : A₀ \ A' ⊆ (A.filter (fun n => ¬ dividesInInterval z K n)) ∪
        ((ppowersInSet A \ E_I).biUnion (fun q => exactSlice A_I q)) := by
      intro n hn
      obtain ⟨hnA0, hnNotA'⟩ := Finset.mem_sdiff.mp hn
      have hnA : n ∈ A := (Finset.mem_sdiff.mp hnA0).1
      by_cases hnAI : n ∈ A_I
      · have hex_bad : ∃ q ∈ exactPrimePowers n, q ∉ E_I := by
          by_contra hall; push Not at hall
          exact hnNotA' (Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hnAI, hnA0⟩, hall⟩)
        obtain ⟨q, hqep, hqnotE⟩ := hex_bad
        have hn0 : n ≠ 0 := by have := (hA_icc n hnA).1; omega
        have hqA : q ∈ ppowersInSet A := Finset.mem_biUnion.mpr ⟨n, hnA, hqep⟩
        have hqn : ppowDiv q n := (ppowDiv_iff_mem_exactPrimePowers hn0).mpr hqep
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨q, Finset.mem_sdiff.mpr ⟨hqA, hqnotE⟩, Finset.mem_filter.mpr ⟨hnAI, hqn⟩⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnA, fun h => hnAI (Finset.mem_filter.mpr ⟨hnA, h⟩)⟩)
    have hpart1 : recSumReal (A.filter (fun n => ¬ dividesInInterval z K n)) ≤ 1 / Real.log (N : ℝ) := by
      have h1 := recSumReal_le_card_div (A := A.filter (fun n => ¬ dividesInInterval z K n))
        hM_pos fun n hn => (hA n (Finset.mem_filter.mp hn).1).1
      have h2 := div_le_div_of_nonneg_right hmiss_lt.le hM_pos.le
      have h3 : (M / Real.log (N : ℝ)) / M = 1 / Real.log (N : ℝ) := by field_simp [hM_pos.ne']
      linarith
    have hpart2 : recSumReal ((ppowersInSet A \ E_I).biUnion (fun q => exactSlice A_I q)) ≤
        η * (LL + C_pp) := by
      calc recSumReal ((ppowersInSet A \ E_I).biUnion (fun q => exactSlice A_I q))
          ≤ ∑ q ∈ ppowersInSet A \ E_I, recSumReal (exactSlice A_I q) := recSumReal_biUnion_le _ _
        _ ≤ ∑ q ∈ ppowersInSet A \ E_I, η * ((1 : ℝ) / (q : ℝ)) := by
            refine Finset.sum_le_sum fun q hq => ?_
            have hqA := (Finset.mem_sdiff.mp hq).1
            have hqnotE := (Finset.mem_sdiff.mp hq).2
            have hq_ne0 : q ≠ 0 := (mem_ppowersInSet_pos h0A hqA).ne'
            have hq_le_η : recSumQ A_I q ≤ η := by
              by_contra hgt; push Not at hgt
              exact hqnotE (Finset.mem_filter.mpr ⟨hqA, hgt⟩)
            rw [← inv_mul_recSumQ_eq A_I hq_ne0]
            have h1 := mul_le_mul_of_nonneg_left hq_le_η (by positivity : (0 : ℝ) ≤ 1 / (q : ℝ))
            linarith
        _ = η * ∑ q ∈ ppowersInSet A \ E_I, (1 : ℝ) / (q : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ η * (LL + C_pp) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hsub : ppowersInSet A \ E_I ⊆ (Finset.Icc 1 N).filter IsPrimePow := fun q hq =>
              Finset.mem_filter.mpr ⟨ppowersInSet_subset_Icc hA_icc (Finset.mem_sdiff.mp hq).1,
                mem_ppowersInSet_isPrimePow h0A (Finset.mem_sdiff.mp hq).1⟩
            exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans (hCpp N (by omega))
    -- Show `1 / log N ≤ (1/12) * (log N)^{-1/101}` and `η * (LL + C_pp) ≤ (1/12) * (log N)^{-1/101}`
    have hsm_a : 1 / Real.log (N : ℝ) ≤ (1 / 12 : ℝ) * (Real.log (N : ℝ)) ^ (-(1 / 101 : ℝ)) := by
      have h1 : (1 : ℝ) / (Real.log (N : ℝ)) ^ (100 / 101 : ℝ) < 1 / 12 := by simpa using hSm4
      have h2 := mul_le_mul_of_nonneg_left h1.le (Real.rpow_nonneg hlogN_pos.le (-(1 / 101 : ℝ)))
      have hrew : (Real.log (N : ℝ)) ^ (-(1 / 101 : ℝ)) * (1 / (Real.log (N : ℝ)) ^ (100 / 101 : ℝ)) =
          1 / Real.log (N : ℝ) := by
        rw [mul_one_div, Real.rpow_neg hlogN_pos.le, ← one_div, div_div, ← Real.rpow_add hlogN_pos]
        norm_num
      linarith
    have hsm_b : η * (LL + C_pp) ≤ (1 / 12 : ℝ) * (Real.log (N : ℝ)) ^ (-(1 / 101 : ℝ)) := by
      have hpow_split : (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) =
          (Real.log (N : ℝ)) ^ (1 / 101 : ℝ) * (Real.log (N : ℝ)) ^ (1 / 10100 : ℝ) := by
        rw [← Real.rpow_add hlogN_pos]; congr 1; norm_num
      have hLL_bd : LL / (Real.log (N : ℝ)) ^ (1 / 10100 : ℝ) < 1 / 24 := by simpa using hSm2
      have hCpp_bd : C_pp / (Real.log (N : ℝ)) ^ (1 / 10100 : ℝ) ≤ 1 / 24 := by
        have h1 : 1 / (Real.log (N : ℝ)) ^ (1 / 10100 : ℝ) < 1 / (24 * C_pp + 1) := by simpa using hSm3
        have h2 := mul_le_mul_of_nonneg_left h1.le hCpp_pos.le
        have h3 : C_pp * (1 / (24 * C_pp + 1)) ≤ 1 / 24 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        have h4 : C_pp * (1 / (Real.log (N : ℝ)) ^ (1 / 10100 : ℝ)) =
            C_pp / (Real.log (N : ℝ)) ^ (1 / 10100 : ℝ) := by ring
        linarith
      have hsum_bd : (LL + C_pp) / (Real.log (N : ℝ)) ^ (1 / 10100 : ℝ) ≤ 1 / 12 := by
        rw [add_div]; linarith
      dsimp only [η]
      rw [hpow_split, Real.rpow_neg hlogN_pos.le, ← one_div]
      have hrew : 1 / (2 * ((Real.log (N : ℝ)) ^ (1 / 101 : ℝ) * (Real.log (N : ℝ)) ^ (1 / 10100 : ℝ))) *
            (LL + C_pp) =
          (1 / 2 : ℝ) * (1 / (Real.log (N : ℝ)) ^ (1 / 101 : ℝ)) *
            ((LL + C_pp) / (Real.log (N : ℝ)) ^ (1 / 10100 : ℝ)) := by ring
      rw [hrew]
      have hnn : 0 ≤ (1 / 2 : ℝ) * (1 / (Real.log (N : ℝ)) ^ (1 / 101 : ℝ)) := by positivity
      have := mul_le_mul_of_nonneg_left hsum_bd hnn
      linarith
    exact (recSumReal_mono hcov).trans ((recSumReal_union_le _ _).trans (by linarith))
  have hRA'_ge : (1 / 6 : ℝ) * (Real.log (N : ℝ)) ^ (-(1 / 101 : ℝ)) ≤ recSumReal A' := by
    have h1 := recSumReal_sdiff_ge A₀ (A₀ \ A')
    have hsub : A₀ \ (A₀ \ A') ⊆ A' := by
      intro n hn
      simp only [Finset.mem_sdiff, not_and, not_not] at hn
      exact hn.2 hn.1
    have h2 := recSumReal_mono hsub
    linarith
  have hA'_card : (M / 6 : ℝ) * (Real.log (N : ℝ)) ^ (-(1 / 101 : ℝ)) ≤ (A'.card : ℝ) := by
    have h1 := recSumReal_le_card_div (A := A') hM_pos fun n hn =>
      (hA n (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_filter.mp hn).1).2).1).1
    have h2 := (le_div_iff₀ hM_pos).mp (hRA'_ge.trans h1)
    linarith
  -- Pigeonhole over integer interval `I_int = Icc ⌈z - K/2⌉ ⌊z + K/2⌋`
  set I_int : Finset ℤ := Finset.Icc ⌈(z : ℝ) - K / 2⌉ ⌊(z : ℝ) + K / 2⌋
  have hI_card : (I_int.card : ℝ) ≤ 2 * K := by
    dsimp only [I_int]
    rw [Int.card_Icc]
    have hlo : (z : ℝ) - K / 2 ≤ (⌈(z : ℝ) - K / 2⌉ : ℝ) := Int.le_ceil _
    have hhi : (⌊(z : ℝ) + K / 2⌋ : ℝ) ≤ (z : ℝ) + K / 2 := Int.floor_le _
    have hdiff_le : ((⌊(z : ℝ) + K / 2⌋ + 1 - ⌈(z : ℝ) - K / 2⌉ : ℤ) : ℝ) ≤ K + 1 := by
      push_cast; linarith
    by_cases hnn : 0 ≤ ⌊(z : ℝ) + K / 2⌋ + 1 - ⌈(z : ℝ) - K / 2⌉
    · have heq : (((⌊(z : ℝ) + K / 2⌋ + 1 - ⌈(z : ℝ) - K / 2⌉).toNat : ℕ) : ℝ) =
          ((⌊(z : ℝ) + K / 2⌋ + 1 - ⌈(z : ℝ) - K / 2⌉ : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hnn
      linarith
    · have h0 : (⌊(z : ℝ) + K / 2⌋ + 1 - ⌈(z : ℝ) - K / 2⌉).toNat = 0 := Int.toNat_eq_zero.mpr (le_of_not_ge hnn)
      rw [h0]; norm_num; linarith
  have hcover_A' : (A'.card : ℝ) ≤ ∑ x ∈ I_int, ((A'.filter (fun n : ℕ => (n : ℤ) ∣ x)).card : ℝ) := by
    have hsub : A' ⊆ I_int.biUnion (fun x => A'.filter (fun n : ℕ => (n : ℤ) ∣ x)) := by
      intro n hn
      have hnAI := (Finset.mem_inter.mp (Finset.mem_filter.mp hn).1).1
      obtain ⟨x, hx_int, hxn⟩ := (Finset.mem_filter.mp hnAI).2
      have habs := abs_le.mp hx_int
      have hx_mem : x ∈ I_int := Finset.mem_Icc.mpr
        ⟨Int.ceil_le.mpr (by linarith), Int.le_floor.mpr (by linarith)⟩
      exact Finset.mem_biUnion.mpr ⟨x, hx_mem, Finset.mem_filter.mpr ⟨hn, hxn⟩⟩
    have h1 : A'.card ≤ ∑ x ∈ I_int, (A'.filter (fun n : ℕ => (n : ℤ) ∣ x)).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    exact_mod_cast h1
  have hex_x : ∃ x ∈ I_int, (N : ℝ) ^ ((3 / 2 : ℝ) / LL) ≤ ((A'.filter (fun n : ℕ => (n : ℤ) ∣ x)).card : ℝ) := by
    by_contra hlt_all
    push Not at hlt_all
    have hsum_lt : ∑ x ∈ I_int, ((A'.filter (fun n : ℕ => (n : ℤ) ∣ x)).card : ℝ) ≤
        (I_int.card : ℝ) * (N : ℝ) ^ ((3 / 2 : ℝ) / LL) := by
      calc ∑ x ∈ I_int, ((A'.filter (fun n : ℕ => (n : ℤ) ∣ x)).card : ℝ)
          ≤ ∑ _x ∈ I_int, (N : ℝ) ^ ((3 / 2 : ℝ) / LL) :=
            Finset.sum_le_sum fun x hx => (hlt_all x hx).le
        _ = (I_int.card : ℝ) * (N : ℝ) ^ ((3 / 2 : ℝ) / LL) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hupper : (I_int.card : ℝ) * (N : ℝ) ^ ((3 / 2 : ℝ) / LL) <
        (M / 6 : ℝ) * (Real.log (N : ℝ)) ^ (-(1 / 101 : ℝ)) := by
      have h1 : (I_int.card : ℝ) * (N : ℝ) ^ ((3 / 2 : ℝ) / LL) ≤
          2 * M * (N : ℝ) ^ (-(1 / 2 : ℝ) / LL) := by
        calc (I_int.card : ℝ) * (N : ℝ) ^ ((3 / 2 : ℝ) / LL)
            ≤ (2 * K) * (N : ℝ) ^ ((3 / 2 : ℝ) / LL) :=
              mul_le_mul_of_nonneg_right hI_card (by positivity)
          _ = 2 * M * ((N : ℝ) ^ (-(2 : ℝ) / LL) * (N : ℝ) ^ ((3 / 2 : ℝ) / LL)) := by
              dsimp only [K]; ring
          _ = 2 * M * (N : ℝ) ^ (-(1 / 2 : ℝ) / LL) := by
              rw [← Real.rpow_add hN_pos]; congr 2; ring
      have h2 : 24 * (Real.log (N : ℝ)) ^ 2 ≤ (N : ℝ) ^ ((1 / 2 : ℝ) / LL) :=
        (le_div_iff₀ (by positivity : (0 : ℝ) < (Real.log (N : ℝ)) ^ 2)).mp hNexp
      have hlog_pow : (Real.log (N : ℝ)) ^ (1 / 101 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := by
        rw [← Real.rpow_natCast (Real.log (N : ℝ)) 2]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have h3 : 12 * (Real.log (N : ℝ)) ^ (1 / 101 : ℝ) < (N : ℝ) ^ ((1 / 2 : ℝ) / LL) := by
        have : (0 : ℝ) < (Real.log (N : ℝ)) ^ 2 := by positivity
        linarith
      have h4 : 2 * M * (N : ℝ) ^ (-(1 / 2 : ℝ) / LL) < (M / 6 : ℝ) * (Real.log (N : ℝ)) ^ (-(1 / 101 : ℝ)) := by
        rw [neg_div, Real.rpow_neg hN_pos.le, Real.rpow_neg hlogN_pos.le,
          ← div_eq_mul_inv, ← div_eq_mul_inv,
          div_lt_div_iff₀ (Real.rpow_pos_of_pos hN_pos _) (Real.rpow_pos_of_pos hlogN_pos _)]
        nlinarith
      linarith
    linarith
  obtain ⟨x, hxI, hx_card⟩ := hex_x
  set A'' : Finset ℕ := A'.filter (fun n : ℕ => (n : ℤ) ∣ x)
  have hA''_ne : A''.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.card_empty] at hx_card
    norm_num at hx_card
    linarith [Real.rpow_pos_of_pos hN_pos ((3 / 2 : ℝ) / LL)]
  obtain ⟨n_wit, hn_wit⟩ := hA''_ne
  have hn_wit_A0 : n_wit ∈ A₀ := (Finset.mem_inter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn_wit).1).1).2
  have hn_wit_x : (n_wit : ℤ) ∣ x := (Finset.mem_filter.mp hn_wit).2
  have hx_ne_w1 : x ≠ w₁ := by
    intro h; subst h
    exact (Finset.mem_sdiff.mp hn_wit_A0).2 (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn_wit_A0).1, hn_wit_x⟩))
  have hx_ne_w2 : x ≠ w₂ := by
    intro h; subst h
    exact (Finset.mem_sdiff.mp hn_wit_A0).2 (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn_wit_A0).1, hn_wit_x⟩))
  -- Every `n ∈ A''` divides `m := (x - w₁).natAbs * (x - w₂).natAbs` with `1 ≤ m ≤ N^2`!
  set m : ℕ := (x - w₁).natAbs * (x - w₂).natAbs
  have hm_pos : 1 ≤ m := Nat.mul_pos (Int.natAbs_pos.mpr (sub_ne_zero.mpr hx_ne_w1))
    (Int.natAbs_pos.mpr (sub_ne_zero.mpr hx_ne_w2))
  have hx_int_bd : |(x : ℝ) - (z : ℝ)| ≤ K / 2 := by
    have h1 := (Finset.mem_Icc.mp hxI).1
    have h2 := (Finset.mem_Icc.mp hxI).2
    have h1' : (z : ℝ) - K / 2 ≤ (x : ℝ) := (Int.le_ceil _).trans (by exact_mod_cast h1)
    have h2' : (x : ℝ) ≤ (z : ℝ) + K / 2 := (by exact_mod_cast h2 : (x : ℝ) ≤ (⌊(z : ℝ) + K / 2⌋ : ℝ)).trans (Int.floor_le _)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hm_le_N2 : m ≤ N ^ 2 := by
    have h1 : (x - w₁).natAbs ≤ N := by
      have habs : ((x - w₁).natAbs : ℝ) = |(x : ℝ) - (w₁ : ℝ)| := by
        rw [← Int.cast_natCast (x - w₁).natAbs, Int.natCast_natAbs, Int.cast_abs]; push_cast; rfl
      have htri := abs_sub_le (x : ℝ) (z : ℝ) (w₁ : ℝ)
      rw [abs_sub_comm (z : ℝ) (w₁ : ℝ)] at htri
      have hle : ((x - w₁).natAbs : ℝ) ≤ (N : ℝ) := by linarith [(hX_prop w₁ hw₁).1]
      exact_mod_cast hle
    have h2 : (x - w₂).natAbs ≤ N := by
      have habs : ((x - w₂).natAbs : ℝ) = |(x : ℝ) - (w₂ : ℝ)| := by
        rw [← Int.cast_natCast (x - w₂).natAbs, Int.natCast_natAbs, Int.cast_abs]; push_cast; rfl
      have htri := abs_sub_le (x : ℝ) (z : ℝ) (w₂ : ℝ)
      rw [abs_sub_comm (z : ℝ) (w₂ : ℝ)] at htri
      have hle : ((x - w₂).natAbs : ℝ) ≤ (N : ℝ) := by linarith [(hX_prop w₂ hw₂).1]
      exact_mod_cast hle
    calc m = (x - w₁).natAbs * (x - w₂).natAbs := rfl
      _ ≤ N * N := Nat.mul_le_mul h1 h2
      _ = N ^ 2 := (sq N).symm
  have hA''_sub_div : A'' ⊆ m.divisors := by
    intro n hn
    have hnA' := (Finset.mem_filter.mp hn).1
    have hnx := (Finset.mem_filter.mp hn).2
    have hnA := (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_filter.mp hnA').1).2).1
    have hn0 : n ≠ 0 := by have := (hA_icc n hnA).1; omega
    have hsplit : ∀ q ∈ exactPrimePowers n, (q : ℤ) ∣ w₁ ∨ (q : ℤ) ∣ w₂ := by
      intro q hqep
      have hqE : q ∈ E_I := (Finset.mem_filter.mp hnA').2 q hqep
      have hxq_mem : xFn q ∈ X_set := Finset.mem_image_of_mem xFn hqE
      rw [hX_pair] at hxq_mem
      have hqdvd := (hxFn_prop q hqE).2.1
      rcases Finset.mem_insert.mp hxq_mem with h1 | h2
      · rw [h1] at hqdvd; exact Or.inl hqdvd
      · rw [Finset.mem_singleton.mp h2] at hqdvd; exact Or.inr hqdvd
    exact Nat.mem_divisors.mpr ⟨dvd_natAbs_mul_of_exactPrimePowers_split hn0 hnx hsplit, by omega⟩
  have hcard_div : (A''.card : ℝ) ≤ (N : ℝ) ^ ((2 * Real.log 2 + 1 / 20 : ℝ) / LL) :=
    ((by exact_mod_cast Finset.card_le_card hA''_sub_div) :
      (A''.card : ℝ) ≤ (m.divisors.card : ℝ)).trans (hDivSq m hm_pos hm_le_N2)
  have hexp_lt : (2 * Real.log 2 + 1 / 20 : ℝ) / LL < (3 / 2 : ℝ) / LL := by
    apply div_lt_div_of_pos_right _ hLL_pos
    linarith [Real.log_two_lt_d9]
  have hrpow_lt : (N : ℝ) ^ ((2 * Real.log 2 + 1 / 20 : ℝ) / LL) < (N : ℝ) ^ ((3 / 2 : ℝ) / LL) :=
    Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < N)) hexp_lt
  linarith

/-! ## Section 3: Unconditional Proof of Bloom's Proposition 1 (`th-techmain`) -/

/-- Repeated `ppl024_lem_pisq` pruning sequence: given `A ⊆ [M, N]` with
`R(A) ≥ 2 / y₀ + (log N)^{-1/200}` and `y₀ ≤ y₁` satisfying the step gap conditions,
produces a decreasing chain `seq : ℕ → Finset ℕ` (`0 ≤ i ≤ y₁ - y₀`) with
`R(seq i) ∈ [2 / (y₀ + i) - 1 / M, 2 / (y₀ + i))` and `R(seq i; q) ≥ 1 / (log N)^{1/100}`. -/
private lemma exists_pruning_chain
    {N y₀ y₁ : ℕ} {M : ℝ} {A : Finset ℕ}
    (_hN_pos : 0 < Real.log (N : ℝ))
    (hMN_lo : (N : ℝ) ^ (1 / 2 : ℝ) ≤ M) (hMN_hi : M ≤ (N : ℝ))
    (_hy0 : 1 ≤ y₀) (hy01 : y₀ ≤ y₁)
    (hA : ∀ n ∈ A, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ (N : ℝ))
    (hRA : (2 : ℝ) / (y₀ : ℝ) + (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) ≤ recSumReal A)
    (hq_le : ∀ q ∈ ppowersInSet A, (q : ℝ) ≤ M / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ))
    (hpisq : ∀ (M' α : ℝ) (A' : Finset ℕ),
      (N : ℝ) ^ (1 / 2 : ℝ) ≤ M' → M' ≤ (N : ℝ) →
      2 * (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) < α →
      (∀ n ∈ A', M' ≤ (n : ℝ) ∧ (n : ℝ) ≤ (N : ℝ)) →
      α + (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) ≤ recSumReal A' →
      (∀ q ∈ ppowersInSet A', (q : ℝ) ≤ M' / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ)) →
      ∃ B : Finset ℕ, B ⊆ A' ∧ α - 1 / M' ≤ recSumReal B ∧ recSumReal B < α ∧
        ∀ q ∈ ppowersInSet B, 1 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ recSumQ B q)
    (hα_big : ∀ d : ℕ, y₀ ≤ d → d ≤ y₁ → 2 * (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) < 2 / (d : ℝ))
    (hstep_gap : ∀ d : ℕ, y₀ ≤ d → d < y₁ →
      2 / ((d + 1 : ℕ) : ℝ) + (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) ≤ 2 / (d : ℝ) - 1 / M) :
    ∃ seq : ℕ → Finset ℕ,
      (∀ i, i ≤ y₁ - y₀ → seq i ⊆ A) ∧
      (∀ i j, i ≤ j → j ≤ y₁ - y₀ → seq j ⊆ seq i) ∧
      (∀ i, i ≤ y₁ - y₀ →
        2 / ((y₀ + i : ℕ) : ℝ) - 1 / M ≤ recSumReal (seq i) ∧
        recSumReal (seq i) < 2 / ((y₀ + i : ℕ) : ℝ) ∧
        ∀ q ∈ ppowersInSet (seq i), 1 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ recSumQ (seq i) q) := by
  -- Construct `seq` by induction on `k ≤ y₁ - y₀`
  have hbuild : ∀ k : ℕ, k ≤ y₁ - y₀ →
      ∃ seq : ℕ → Finset ℕ,
        (∀ i, i ≤ k → seq i ⊆ A) ∧
        (∀ i j, i ≤ j → j ≤ k → seq j ⊆ seq i) ∧
        (∀ i, i ≤ k →
          2 / ((y₀ + i : ℕ) : ℝ) - 1 / M ≤ recSumReal (seq i) ∧
          recSumReal (seq i) < 2 / ((y₀ + i : ℕ) : ℝ) ∧
          ∀ q ∈ ppowersInSet (seq i), 1 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ recSumQ (seq i) q) := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨B₀, hB₀A, hB₀_lo, hB₀_hi, hB₀_q⟩ :=
        hpisq M (2 / (y₀ : ℝ)) A hMN_lo hMN_hi (hα_big y₀ le_rfl hy01) hA hRA hq_le
      refine ⟨fun _ => B₀, fun _ _ => hB₀A, fun _ _ _ _ => Finset.Subset.rfl, fun i hi => ?_⟩
      have hi0 : i = 0 := by omega
      subst hi0
      simp only [add_zero]
      exact ⟨hB₀_lo, hB₀_hi, hB₀_q⟩
    | succ k ih =>
      intro hk
      obtain ⟨seq, hsub, hanti, hprop⟩ := ih (by omega)
      have hk_prop := hprop k le_rfl
      have hsub_k := hsub k le_rfl
      have hgap := hstep_gap (y₀ + k) (by omega) (by omega)
      have hRA_next : 2 / ((y₀ + (k + 1) : ℕ) : ℝ) + (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) ≤
          recSumReal (seq k) := by
        have heq : y₀ + (k + 1) = (y₀ + k) + 1 := by omega
        rw [heq]; linarith [hk_prop.1]
      obtain ⟨Bk1, hBk1_sub, hBk1_lo, hBk1_hi, hBk1_q⟩ :=
        hpisq M (2 / ((y₀ + (k + 1) : ℕ) : ℝ)) (seq k) hMN_lo hMN_hi
          (hα_big (y₀ + (k + 1)) (by omega) (by omega))
          (fun n hn => hA n (hsub_k hn)) hRA_next
          (fun q hq => hq_le q (ppowersInSet_mono hsub_k hq))
      let seq' : ℕ → Finset ℕ := fun i => if i ≤ k then seq i else Bk1
      refine ⟨seq', ?_, ?_, ?_⟩
      · intro i hi
        dsimp only [seq']; split_ifs with hik
        · exact hsub i hik
        · exact hBk1_sub.trans hsub_k
      · intro i j hij hjk
        dsimp only [seq']; split_ifs with hjk' hik₁ hik₂
        · exact hanti i j hij hjk'
        · omega
        · exact hBk1_sub.trans (hanti i k hik₂ le_rfl)
        · exact Finset.Subset.rfl
      · intro i hi
        dsimp only [seq']; split_ifs with hik
        · exact hprop i hik
        · have hik1 : i = k + 1 := by omega
          subst hik1
          exact ⟨hBk1_lo, hBk1_hi, hBk1_q⟩
  exact hbuild (y₁ - y₀) le_rfl

/-- **Unconditional Proof of Bloom's Proposition 1 (`th-techmain`, constant-`c` version)**:
Matches `PPL024.BloomProp1Statement` in `Prize/PPL024_Analytic.lean` with 0 hypotheses! -/
theorem bloom_prop1_unconditional : PPL024.BloomProp1Statement := by
  intro c hc0 hc14
  obtain ⟨c_F, hcF_pos, N_F, hFourier⟩ := Prize.PPL024.bloom_fourier_prop
  have hLL : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- Helper: `N^a / (log N)^b → ∞` for `a > 0`
  have hN_pow_beats_log : ∀ (a : ℝ) (b : ℕ), 0 < a →
      Tendsto (fun N : ℕ => (N : ℝ) ^ a / (Real.log (N : ℝ)) ^ b) atTop atTop := by
    intro a b ha
    have h1 : Tendsto (fun u : ℝ => Real.exp (a * u) / u ^ b) atTop atTop := by
      have hexp : Tendsto (fun v : ℝ => Real.exp v / v ^ b) atTop atTop := by
        simpa using Real.tendsto_exp_div_pow_atTop b
      have h2 := (Filter.Tendsto.const_mul_atTop (pow_pos ha b) hexp).comp
        (Filter.Tendsto.const_mul_atTop ha tendsto_id)
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      simp only [Function.comp_apply, id_eq, mul_pow]
      field_simp [(pow_pos ha b).ne']
    refine (h1.comp hlogN).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hNp : (0 : ℝ) < (N : ℝ) := by positivity
    simp only [Function.comp_apply]
    rw [Real.rpow_def_of_pos hNp, mul_comm (Real.log (N : ℝ)) a]
  -- Helper: `(log N)^a → ∞` for `a > 0`
  have hlog_rpow : ∀ a : ℝ, 0 < a → Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ a) atTop atTop :=
    fun a ha => (tendsto_rpow_atTop ha).comp hlogN
  have hN_c_div2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (c / 2) / (Real.log (N : ℝ)) ^ 3) atTop atTop :=
    hN_pow_beats_log (c / 2) 3 (by linarith)
  have hN_3c : Tendsto (fun N : ℕ => (N : ℝ) ^ (3 * c) / Real.log (N : ℝ)) atTop atTop := by
    simpa [pow_one] using hN_pow_beats_log (3 * c) 1 (by linarith)
  have hN_34 : Tendsto (fun N : ℕ => (N : ℝ) ^ (3 / 4 : ℝ) / Real.log (N : ℝ)) atTop atTop := by
    simpa [pow_one] using hN_pow_beats_log (3 / 4 : ℝ) 1 (by norm_num)
  have hev : ∀ᶠ N : ℕ in atTop,
      16 ≤ N ∧ N_F ≤ N ∧
      (∀ (M : ℝ) (A : Finset ℕ),
        (N : ℝ) ^ (1 / 2 : ℝ) ≤ M → M ≤ (N : ℝ) →
        (∀ n ∈ A, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ (N : ℝ)) →
        (∀ n ∈ A, (99 / 100 : ℝ) * Real.log (Real.log (N : ℝ)) ≤ (omega n : ℝ) ∧
          (omega n : ℝ) ≤ 2 * Real.log (Real.log (N : ℝ))) →
        (Real.log (N : ℝ)) ^ (-(1 / 101 : ℝ)) ≤ recSumReal A →
        (∀ q ∈ ppowersInSet A, 1 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ recSumQ A q) →
        ((¬ (∑ q ∈ ppowersInSet A, (1 : ℝ) / (q : ℝ) ≤ (2 / 3 : ℝ) * Real.log (Real.log (N : ℝ)))) ∧
         ∃ B : Finset ℕ, B ⊆ A ∧ (1 / 3 : ℝ) * recSumReal A ≤ recSumReal B ∧
           ∑ q ∈ ppowersInSet B, (1 : ℝ) / (q : ℝ) ≤ (2 / 3 : ℝ) * Real.log (Real.log (N : ℝ))) ∨
        (∀ z : ℤ,
          let K := M * (N : ℝ) ^ (-(2 : ℝ) / Real.log (Real.log (N : ℝ)))
          let η := 1 / (2 * (Real.log (N : ℝ)) ^ (1 / 100 : ℝ))
          M / Real.log (N : ℝ) ≤ ((A.filter (fun n => ¬ dividesInInterval z K n)).card : ℝ) ∨
          ∃ x : ℤ, |(x : ℝ) - (z : ℝ)| ≤ K / 2 ∧ ∀ q ∈ goodPrimePowers A M η K z, (q : ℤ) ∣ x)) ∧
      (∀ (M α : ℝ) (A : Finset ℕ),
        (N : ℝ) ^ (1 / 2 : ℝ) ≤ M → M ≤ (N : ℝ) →
        2 * (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) < α →
        (∀ n ∈ A, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ (N : ℝ)) →
        α + (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) ≤ recSumReal A →
        (∀ q ∈ ppowersInSet A, (q : ℝ) ≤ M / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ)) →
        ∃ B : Finset ℕ, B ⊆ A ∧ α - 1 / M ≤ recSumReal B ∧ recSumReal B < α ∧
          ∀ q ∈ ppowersInSet B, 1 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ recSumQ B q) ∧
      max (4 / (1 / 4 - c)) (8 / c) ≤ Real.log (Real.log (N : ℝ)) ∧
      4 ≤ Real.log (N : ℝ) ∧
      2 / c_F + 2 ≤ (N : ℝ) ^ (c / 2) / (Real.log (N : ℝ)) ^ 3 ∧
      1 / c_F + 2 ≤ (N : ℝ) ^ (3 * c) / Real.log (N : ℝ) ∧
      1 / c_F + 4 ≤ (N : ℝ) ^ (3 / 4 : ℝ) / Real.log (N : ℝ) ∧
      24 ≤ (Real.log (N : ℝ)) ^ (1 / 1000 : ℝ) ∧
      4 ≤ (N : ℝ) ^ ((1 / 2 : ℝ) / Real.log (Real.log (N : ℝ))) := by
    have hN_half_LL : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 / 2 : ℝ) / Real.log (Real.log (N : ℝ)))) atTop atTop := by
      have h1 : Tendsto (fun u : ℝ => Real.exp u / (2 * u)) atTop atTop := by
        have h0 : Tendsto (fun u : ℝ => Real.exp u / u) atTop atTop := by
          simpa using Real.tendsto_exp_div_pow_atTop 1
        exact (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) h0).congr fun u => by ring
      refine (Real.tendsto_exp_atTop.comp (h1.comp hLL)).congr' ?_
      filter_upwards [eventually_ge_atTop 3] with N hN
      have hNp : (0 : ℝ) < (N : ℝ) := by positivity
      have hlp : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      simp only [Function.comp_apply]
      rw [Real.rpow_def_of_pos hNp, Real.exp_log hlp]
      congr 1; ring
    filter_upwards [
      eventually_ge_atTop 16,
      eventually_ge_atTop N_F,
      bloom_prop_tech_iter,
      ppl024_lem_pisq,
      hLL.eventually_ge_atTop (max (4 / (1 / 4 - c)) (8 / c)),
      hlogN.eventually_ge_atTop 4,
      hN_c_div2.eventually_ge_atTop (2 / c_F + 2),
      hN_3c.eventually_ge_atTop (1 / c_F + 2),
      hN_34.eventually_ge_atTop (1 / c_F + 4),
      (hlog_rpow (1 / 1000 : ℝ) (by norm_num)).eventually_ge_atTop 24,
      hN_half_LL.eventually_ge_atTop 4
    ] with N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  refine ⟨max N₀ 16, le_max_right _ _, fun N hN y z hy1 hyz hz_le A hA_rng hRA hA_div hA_sm hA_ω => ?_⟩
  obtain ⟨hN16, hN_NF, hPropTech, hPisq, hLL_ge, hlogN4, hNc2, hN3c, hN34, hlog1000, hN_hLL⟩ :=
    hN₀ N (le_trans (le_max_left _ _) hN)
  set LL : ℝ := Real.log (Real.log (N : ℝ))
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hLL_pos : 0 < LL := by
    have : 0 < 8 / c := by positivity
    linarith [le_trans (le_max_right (4 / (1 / 4 - c)) (8 / c)) hLL_ge]
  set M : ℝ := (N : ℝ) ^ (1 - c)
  set K : ℝ := M * (N : ℝ) ^ (-(2 : ℝ) / LL)
  set η : ℝ := 1 / (2 * (Real.log (N : ℝ)) ^ (1 / 100 : ℝ))
  have hM_ge34 : (N : ℝ) ^ (3 / 4 : ℝ) ≤ M :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hM_ge12 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ M :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hM_le_N : M ≤ (N : ℝ) := by
    calc M = (N : ℝ) ^ (1 - c) := rfl
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = (N : ℝ) := Real.rpow_one _
  have hM_pos : 0 < M := Real.rpow_pos_of_pos hN_pos _
  have hK_ge34 : (N : ℝ) ^ (3 / 4 : ℝ) ≤ K := by
    have h2LL : 2 / LL ≤ 1 / 4 - c := by
      have h1 : 4 / (1 / 4 - c) ≤ LL := le_trans (le_max_left _ _) hLL_ge
      have h2 : 0 < 1 / 4 - c := by linarith
      rw [div_le_iff₀ hLL_pos]
      have h3 := (div_le_iff₀ h2).mp h1
      linarith
    have hK_eq : K = (N : ℝ) ^ (1 - c - 2 / LL) := by
      dsimp only [K, M]; rw [← Real.rpow_add hN_pos]; congr 1; ring
    rw [hK_eq]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hK_le_M2 : K ≤ M / 2 := by
    have h1 : (2 : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / LL) := by
      have h2 : (N : ℝ) ^ ((1 / 2 : ℝ) / LL) ≤ (N : ℝ) ^ ((2 : ℝ) / LL) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (div_le_div_of_nonneg_right (by norm_num) hLL_pos.le)
      linarith
    have h2 : (N : ℝ) ^ (-(2 : ℝ) / LL) ≤ 1 / 2 := by
      rw [neg_div, Real.rpow_neg hN_pos.le, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) h1
    calc K = M * (N : ℝ) ^ (-(2 : ℝ) / LL) := rfl
      _ ≤ M * (1 / 2) := mul_le_mul_of_nonneg_left h2 hM_pos.le
      _ = M / 2 := by ring
  have hη0 : 0 < η := by positivity
  have hη1 : η < 1 := by
    dsimp only [η]
    rw [div_lt_one (by positivity)]
    have h1 : (1 : ℝ) ≤ (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    linarith
  have hA_MN : ∀ n ∈ A, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ (N : ℝ) := fun n hn =>
    ⟨(hA_rng n hn).1, by exact_mod_cast (hA_rng n hn).2⟩
  have h0A : 0 ∉ A := fun h => by
    have := (hA_MN 0 h).1; norm_num at this; linarith
  -- Bound on every `q ∈ ppowersInSet A`
  have hq_N14c : ∀ q ∈ ppowersInSet A, (q : ℝ) ≤ (N : ℝ) ^ (1 - 4 * c) := by
    intro q hq
    obtain ⟨n, hn⟩ := (mem_ppowersInSet_iff h0A).mp hq
    obtain ⟨hnA, hqn⟩ := Finset.mem_filter.mp hn
    exact hA_sm n hnA q hqn.1 hqn.2.1
  have hq_pisq : ∀ q ∈ ppowersInSet A, (q : ℝ) ≤ M / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) := by
    intro q hq
    have hq1 := hq_N14c q hq
    have h1 : (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ Real.log (N : ℝ) := by
      calc (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ (Real.log (N : ℝ)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = Real.log (N : ℝ) := Real.rpow_one _
    have h2 : Real.log (N : ℝ) ≤ (N : ℝ) ^ (3 * c) := by
      have := (le_div_iff₀ hlogN_pos).mp hN3c
      have : 0 < 1 / c_F := by positivity
      nlinarith
    have h3 : (N : ℝ) ^ (1 - 4 * c) ≤ M / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hlogN_pos _)]
      calc (N : ℝ) ^ (1 - 4 * c) * (Real.log (N : ℝ)) ^ (1 / 100 : ℝ)
          ≤ (N : ℝ) ^ (1 - 4 * c) * (N : ℝ) ^ (3 * c) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
        _ = M := by dsimp only [M]; rw [← Real.rpow_add hN_pos]; congr 1; ring
    exact hq1.trans h3
  -- Bound on `q ∈ ppowersInSet A` for `bloom_fourier_prop` for any `1 ≤ k ≤ z`
  have hq_fourier : ∀ k : ℕ, 1 ≤ k → k ≤ z → ∀ q ∈ ppowersInSet A,
      (q : ℝ) ≤ c_F * min (M / (k : ℝ)) (η * M * K ^ 2 / ((N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2)) := by
    intro k hk1 hkz q hq
    have hq1 := hq_N14c q hq
    rw [mul_min_of_nonneg _ _ hcF_pos.le, le_min_iff]
    constructor
    · -- `(N)^(1 - 4c) ≤ c_F * M / k`
      have hk_le_log : (k : ℝ) ≤ Real.log (N : ℝ) := by
        calc (k : ℝ) ≤ (z : ℝ) := by exact_mod_cast hkz
          _ ≤ (Real.log (N : ℝ)) ^ (1 / 500 : ℝ) := hz_le
          _ ≤ (Real.log (N : ℝ)) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          _ = Real.log (N : ℝ) := Real.rpow_one _
      have h1 : (1 / c_F) * Real.log (N : ℝ) ≤ (N : ℝ) ^ (3 * c) := by
        have := (le_div_iff₀ hlogN_pos).mp hN3c
        nlinarith
      have h2 : (N : ℝ) ^ (1 - 4 * c) * (k : ℝ) ≤ c_F * M := by
        have h3 : (k : ℝ) ≤ c_F * (N : ℝ) ^ (3 * c) := by
          have := mul_le_mul_of_nonneg_left h1 hcF_pos.le
          have hrew : c_F * (1 / c_F * Real.log (N : ℝ)) = Real.log (N : ℝ) := by field_simp [hcF_pos.ne']
          linarith
        calc (N : ℝ) ^ (1 - 4 * c) * (k : ℝ)
            ≤ (N : ℝ) ^ (1 - 4 * c) * (c_F * (N : ℝ) ^ (3 * c)) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = c_F * ((N : ℝ) ^ (1 - 4 * c) * (N : ℝ) ^ (3 * c)) := by ring
          _ = c_F * M := by dsimp only [M]; rw [← Real.rpow_add hN_pos]; congr 2; ring
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
      rw [mul_div_assoc', le_div_iff₀ hk_pos]
      exact (mul_le_mul_of_nonneg_right hq1 hk_pos.le).trans h2
    · -- `(N)^(1 - 4c) ≤ c_F * η * M * K^2 / (N^2 * (log N)^2)`
      have h4LL : 4 / LL ≤ c / 2 := by
        have h1 : 8 / c ≤ LL := le_trans (le_max_right _ _) hLL_ge
        rw [div_le_iff₀ hLL_pos]
        have h2 := (div_le_iff₀ hc0).mp h1
        linarith
      have hMK2 : (N : ℝ) ^ (1 - 4 * c) * (N : ℝ) ^ (c / 2) ≤ M * K ^ 2 / (N : ℝ) ^ 2 := by
        have hK2 : K ^ 2 = (N : ℝ) ^ (2 - 2 * c - 4 / LL) := by
          dsimp only [K, M]
          rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (1 - c)) 2,
            ← Real.rpow_natCast ((N : ℝ) ^ (-(2 : ℝ) / LL)) 2,
            ← Real.rpow_mul hN_pos.le, ← Real.rpow_mul hN_pos.le, ← Real.rpow_add hN_pos]
          congr 1; ring
        have hRHS : M * K ^ 2 / (N : ℝ) ^ 2 = (N : ℝ) ^ (1 - 3 * c - 4 / LL) := by
          rw [hK2, show (N : ℝ) ^ 2 = (N : ℝ) ^ (2 : ℝ) by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
          dsimp only [M]
          rw [← Real.rpow_add hN_pos, ← Real.rpow_sub hN_pos]
          congr 1; ring
        rw [hRHS, ← Real.rpow_add hN_pos]
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      have hlog_bd : (2 / c_F) * (Real.log (N : ℝ)) ^ 3 ≤ (N : ℝ) ^ (c / 2) := by
        have := (le_div_iff₀ (by positivity : (0 : ℝ) < (Real.log (N : ℝ)) ^ 3)).mp hNc2
        nlinarith [pow_nonneg hlogN_pos.le 3]
      have hlog100_le : (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ Real.log (N : ℝ) := by
        calc (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ (Real.log (N : ℝ)) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          _ = Real.log (N : ℝ) := Real.rpow_one _
      have hden_le : 2 * (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) * (Real.log (N : ℝ)) ^ 2 ≤
          c_F * (N : ℝ) ^ (c / 2) := by
        have h1 : 2 * (Real.log (N : ℝ)) ^ 3 ≤ c_F * (N : ℝ) ^ (c / 2) := by
          have := mul_le_mul_of_nonneg_left hlog_bd hcF_pos.le
          have hrew : c_F * (2 / c_F * (Real.log (N : ℝ)) ^ 3) = 2 * (Real.log (N : ℝ)) ^ 3 := by
            field_simp [hcF_pos.ne']
          linarith
        have h2 : 2 * (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) * (Real.log (N : ℝ)) ^ 2 ≤
            2 * (Real.log (N : ℝ)) ^ 3 := by
          have : (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) * (Real.log (N : ℝ)) ^ 2 ≤
              Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hlog100_le (by positivity)
          linarith
        linarith
      have hfinal : (N : ℝ) ^ (1 - 4 * c) ≤
          c_F * (η * M * K ^ 2 / ((N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2)) := by
        have hrew : c_F * (η * M * K ^ 2 / ((N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2)) =
            (c_F * (M * K ^ 2 / (N : ℝ) ^ 2)) /
              (2 * (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) * (Real.log (N : ℝ)) ^ 2) := by
          dsimp only [η]; ring
        rw [hrew, le_div_iff₀ (by positivity)]
        calc (N : ℝ) ^ (1 - 4 * c) * (2 * (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) * (Real.log (N : ℝ)) ^ 2)
            ≤ (N : ℝ) ^ (1 - 4 * c) * (c_F * (N : ℝ) ^ (c / 2)) :=
              mul_le_mul_of_nonneg_left hden_le (by positivity)
          _ = c_F * ((N : ℝ) ^ (1 - 4 * c) * (N : ℝ) ^ (c / 2)) := by ring
          _ ≤ c_F * (M * K ^ 2 / (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hMK2 hcF_pos.le
      exact hq1.trans hfinal
  -- Bound `k ≤ c_F * M` for all `k ≤ z`
  have hk_le_cFM : ∀ k : ℕ, k ≤ z → (k : ℝ) ≤ c_F * M := by
    intro k hkz
    have hk_log : (k : ℝ) ≤ Real.log (N : ℝ) := by
      calc (k : ℝ) ≤ (z : ℝ) := by exact_mod_cast hkz
        _ ≤ (Real.log (N : ℝ)) ^ (1 / 500 : ℝ) := hz_le
        _ ≤ (Real.log (N : ℝ)) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = Real.log (N : ℝ) := Real.rpow_one _
    have h1 : (1 / c_F) * Real.log (N : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by
      have := (le_div_iff₀ hlogN_pos).mp hN34
      nlinarith
    have h2 : Real.log (N : ℝ) ≤ c_F * (N : ℝ) ^ (3 / 4 : ℝ) := by
      have := mul_le_mul_of_nonneg_left h1 hcF_pos.le
      have hrew : c_F * (1 / c_F * Real.log (N : ℝ)) = Real.log (N : ℝ) := by field_simp [hcF_pos.ne']
      linarith
    exact hk_log.trans (h2.trans (mul_le_mul_of_nonneg_left hM_ge34 hcF_pos.le))
  -- Step-gap helpers for `exists_pruning_chain`
  have h1M_le : 1 / M ≤ (1 / 2 : ℝ) * (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) := by
    have h1 : 2 * Real.log (N : ℝ) ≤ M := by
      have h2 := (le_div_iff₀ hlogN_pos).mp hN34
      have : 0 < 1 / c_F := by positivity
      nlinarith
    have h2 : (Real.log (N : ℝ)) ^ (1 / 200 : ℝ) ≤ Real.log (N : ℝ) := by
      calc (Real.log (N : ℝ)) ^ (1 / 200 : ℝ) ≤ (Real.log (N : ℝ)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = Real.log (N : ℝ) := Real.rpow_one _
    rw [Real.rpow_neg hlogN_pos.le, ← one_div, mul_one_div,
      div_le_div_iff₀ hM_pos (by positivity)]
    linarith
  have hα_big_all : ∀ d : ℕ, 1 ≤ d → d ≤ z → 2 * (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) < 2 / (d : ℝ) := by
    intro d hd1 hdz
    have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd1
    have hd_le : (d : ℝ) ≤ (Real.log (N : ℝ)) ^ (1 / 500 : ℝ) :=
      (by exact_mod_cast hdz : (d : ℝ) ≤ (z : ℝ)).trans hz_le
    have hlt : (Real.log (N : ℝ)) ^ (1 / 500 : ℝ) < (Real.log (N : ℝ)) ^ (1 / 200 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
    rw [Real.rpow_neg hlogN_pos.le, ← one_div, mul_one_div,
      div_lt_div_iff₀ (Real.rpow_pos_of_pos hlogN_pos _) hd_pos]
    linarith
  have hgap_all : ∀ d : ℕ, 1 ≤ d → d < z →
      2 / ((d + 1 : ℕ) : ℝ) + (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) ≤ 2 / (d : ℝ) - 1 / M := by
    intro d hd1 hdz
    have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd1
    have hd1_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
    have hdiff_eq : 2 / (d : ℝ) - 2 / ((d + 1 : ℕ) : ℝ) = 2 / ((d : ℝ) * ((d + 1 : ℕ) : ℝ)) := by
      push_cast; field_simp [hd_pos.ne', (by linarith : (d : ℝ) + 1 ≠ 0)]; ring
    have hprod_le : (d : ℝ) * ((d + 1 : ℕ) : ℝ) ≤ (Real.log (N : ℝ)) ^ (2 / 500 : ℝ) := by
      have hd_le : (d : ℝ) ≤ (Real.log (N : ℝ)) ^ (1 / 500 : ℝ) :=
        (by exact_mod_cast hdz.le : (d : ℝ) ≤ (z : ℝ)).trans hz_le
      have hd1_le : ((d + 1 : ℕ) : ℝ) ≤ (Real.log (N : ℝ)) ^ (1 / 500 : ℝ) :=
        (by exact_mod_cast (by omega : d + 1 ≤ z) : ((d + 1 : ℕ) : ℝ) ≤ (z : ℝ)).trans hz_le
      calc (d : ℝ) * ((d + 1 : ℕ) : ℝ)
          ≤ (Real.log (N : ℝ)) ^ (1 / 500 : ℝ) * (Real.log (N : ℝ)) ^ (1 / 500 : ℝ) :=
            mul_le_mul hd_le hd1_le hd1_pos.le (by positivity)
        _ = (Real.log (N : ℝ)) ^ (2 / 500 : ℝ) := by rw [← Real.rpow_add hlogN_pos]; congr 1; norm_num
    have h2_ge : (3 / 2 : ℝ) * (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) ≤
        2 / ((d : ℝ) * ((d + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg hlogN_pos.le, ← one_div, mul_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have hpow : (Real.log (N : ℝ)) ^ (2 / 500 : ℝ) * (Real.log (N : ℝ)) ^ (1 / 1000 : ℝ) =
          (Real.log (N : ℝ)) ^ (1 / 200 : ℝ) := by
        rw [← Real.rpow_add hlogN_pos]; congr 1; norm_num
      have h24 : (3 / 2 : ℝ) * (Real.log (N : ℝ)) ^ (2 / 500 : ℝ) ≤ 2 * (Real.log (N : ℝ)) ^ (1 / 200 : ℝ) := by
        rw [← hpow]
        have := mul_le_mul_of_nonneg_left hlog1000 (Real.rpow_nonneg hlogN_pos.le (2 / 500 : ℝ))
        nlinarith [Real.rpow_nonneg hlogN_pos.le (2 / 500 : ℝ)]
      nlinarith
    linarith
  have hRA_lb : ∀ d : ℕ, 1 ≤ d → d ≤ z →
      (Real.log (N : ℝ)) ^ (-(1 / 101 : ℝ)) ≤ 2 / (d : ℝ) - 1 / M := by
    intro d hd1 hdz
    have h1 := hα_big_all d hd1 hdz
    have h2 : (Real.log (N : ℝ)) ^ (-(1 / 101 : ℝ)) ≤ (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hnn := Real.rpow_nonneg hlogN_pos.le (-(1 / 200 : ℝ))
    linarith
  -- Note `A` is nonempty (since `R(A) > 0`), so `y ≤ z / 4`!
  have hA_ne : A.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.sum_empty] at hRA
    have : 0 < (2 : ℝ) / (y : ℝ) + (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) := by positivity
    linarith
  have hy_le_z4 : y ≤ z / 4 := by
    obtain ⟨n, hn⟩ := hA_ne
    obtain ⟨d₁, d₂, hd1, hd12, hd2z, _, _⟩ := hA_div n hn
    omega
  -- Step 1: Build the first pruning chain `seq` for `d_i = y + i` (`0 ≤ i ≤ z / 4 - y`)
  obtain ⟨seq, hseq_sub, hseq_anti, hseq_prop⟩ :=
    exists_pruning_chain hlogN_pos hM_ge12 hM_le_N hy1 hy_le_z4 hA_MN hRA hq_pisq hPisq
      (fun d hd1 hd2 => hα_big_all d (by omega) (by omega))
      (fun d hd1 hd2 => hgap_all d (by omega) (by omega))
  -- Some `i ≤ z / 4 - y` has a multiple of `y + i` in `seq i`!
  have hex_i : ∃ i : ℕ, i ≤ z / 4 - y ∧ ∃ n ∈ seq i, (y + i) ∣ n := by
    have hne_end : (seq (z / 4 - y)).Nonempty := by
      by_contra hemp
      have hlo := (hseq_prop (z / 4 - y) le_rfl).1
      rw [Finset.not_nonempty_iff_eq_empty.mp hemp, recSumReal_empty] at hlo
      have hpos := hRA_lb (y + (z / 4 - y)) (by omega) (by omega)
      linarith [Real.rpow_pos_of_pos hlogN_pos (-(1 / 101 : ℝ))]
    obtain ⟨n, hn⟩ := hne_end
    obtain ⟨d₁, d₂, hd1_y, hd12, hd2z, hd1_dvd, _⟩ := hA_div n (hseq_sub (z / 4 - y) le_rfl hn)
    refine ⟨d₁ - y, by omega, n, hseq_anti (d₁ - y) (z / 4 - y) (by omega) le_rfl hn, ?_⟩
    rwa [show y + (d₁ - y) = d₁ by omega]
  let j : ℕ := Nat.find hex_i
  have hj_spec := Nat.find_spec hex_i
  have hj_le : j ≤ z / 4 - y := hj_spec.1
  obtain ⟨n_wit, hn_wit, hdj_dvd⟩ := hj_spec.2
  set dj : ℕ := y + j
  set Aj : Finset ℕ := seq j
  have hAjA : Aj ⊆ A := hseq_sub j hj_le
  have hAj_prop := hseq_prop j hj_le
  have hdj_dvd_lcm : dj ∣ lcmSet (ppowersInSet Aj) := by
    have h0Aj : 0 ∉ Aj := fun h => h0A (hAjA h)
    rw [lcmSet_ppowersInSet_eq h0Aj]
    exact dvd_trans hdj_dvd (Finset.dvd_lcm hn_wit)
  -- Helper: apply `hFourier` to any subset `D ⊆ A` satisfying Case 2 of `bloom_prop_tech_iter`
  have hsolve_of_case2 : ∀ (D : Finset ℕ) (k : ℕ), D ⊆ A → y ≤ k → k ≤ z →
      2 / (k : ℝ) - 1 / M ≤ recSumReal D → recSumReal D < 2 / (k : ℝ) →
      k ∣ lcmSet (ppowersInSet D) →
      (∀ z₀ : ℤ,
        M / Real.log (N : ℝ) ≤ ((D.filter (fun n => ¬ dividesInInterval z₀ K n)).card : ℝ) ∨
        ∃ x : ℤ, |(x : ℝ) - (z₀ : ℝ)| ≤ K / 2 ∧ ∀ q ∈ goodPrimePowers D M η K z₀, (q : ℤ) ∣ x) →
      ∃ S ⊆ A, ∃ d : ℕ, y ≤ d ∧ d ≤ z ∧ ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = (1 : ℚ) / (d : ℚ) := by
    intro D k hDA hyk hkz hRD_lo hRD_hi hk_lcm hCase2
    obtain ⟨S, hSD, hSsum⟩ := hFourier N hN_NF M K η k D hM_ge34 hM_le_N
      (by omega) (hk_le_cFM k hkz) hη0 hη1 hK_ge34 hK_le_M2
      (fun n hn => hA_MN n (hDA hn)) hRD_lo hRD_hi hk_lcm
      (fun q hq => hq_fourier k (by omega) hkz q (ppowersInSet_mono hDA hq)) hCase2
    exact ⟨S, hSD.trans hDA, k, hyk, hkz, hSsum⟩
  -- Step 2: Apply `hPropTech` to `Aj`!
  have hTech_Aj := hPropTech M Aj hM_ge12 hM_le_N (fun n hn => hA_MN n (hAjA hn))
    (fun n hn => hA_ω n (hAjA hn)) ((hRA_lb dj (by omega) (by omega)).trans hAj_prop.1) hAj_prop.2.2
  rcases hTech_Aj with ⟨_, B, hBAj, hRB_ge, hQB_le⟩ | hCase2_Aj
  · -- Case 1: `B ⊆ Aj` has `R(B) ≥ R(Aj)/3 ≥ 2/(4 dj) + (log N)^{-1/200}` and `∑_{𝒬_B} 1/q ≤ (2/3) LL`!
    have h4dj_le_z : 4 * dj ≤ z := by omega
    have hRB_init : 2 / ((4 * dj : ℕ) : ℝ) + (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) ≤ recSumReal B := by
      have hdj_pos : (0 : ℝ) < (dj : ℝ) := Nat.cast_pos.mpr (by omega)
      have hdiff_eq : (1 / 3 : ℝ) * (2 / (dj : ℝ)) - 2 / ((4 * dj : ℕ) : ℝ) = 1 / (6 * (dj : ℝ)) := by
        push_cast; field_simp [hdj_pos.ne']; ring
      have h6dj_le : 6 * (dj : ℝ) ≤ 6 * (Real.log (N : ℝ)) ^ (1 / 500 : ℝ) := by
        have : (dj : ℝ) ≤ (Real.log (N : ℝ)) ^ (1 / 500 : ℝ) :=
          (by exact_mod_cast (by omega : dj ≤ z) : (dj : ℝ) ≤ (z : ℝ)).trans hz_le
        linarith
      have h16_ge : (3 / 2 : ℝ) * (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) ≤ 1 / (6 * (dj : ℝ)) := by
        rw [Real.rpow_neg hlogN_pos.le, ← one_div, mul_one_div,
          div_le_div_iff₀ (by positivity) (by positivity)]
        have hpow : (Real.log (N : ℝ)) ^ (1 / 500 : ℝ) * (Real.log (N : ℝ)) ^ (3 / 1000 : ℝ) =
            (Real.log (N : ℝ)) ^ (1 / 200 : ℝ) := by
          rw [← Real.rpow_add hlogN_pos]; congr 1; norm_num
        have hpow3 : 24 ≤ (Real.log (N : ℝ)) ^ (3 / 1000 : ℝ) := by
          have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ Real.log (N : ℝ))
            (by norm_num : (1 / 1000 : ℝ) ≤ 3 / 1000)
          linarith
        have h9 : 9 * (Real.log (N : ℝ)) ^ (1 / 500 : ℝ) ≤ (Real.log (N : ℝ)) ^ (1 / 200 : ℝ) := by
          rw [← hpow]
          have := mul_le_mul_of_nonneg_left hpow3 (Real.rpow_nonneg hlogN_pos.le (1 / 500 : ℝ))
          nlinarith [Real.rpow_nonneg hlogN_pos.le (1 / 500 : ℝ)]
        nlinarith
      have h1 : (1 / 3 : ℝ) * (2 / (dj : ℝ) - 1 / M) ≤ recSumReal B :=
        (mul_le_mul_of_nonneg_left hAj_prop.1 (by norm_num)).trans hRB_ge
      linarith
    have hBA : B ⊆ A := hBAj.trans hAjA
    -- Build the second pruning chain `seqB` for `e_i = 4 * dj + i` (`0 ≤ i ≤ z - 4 * dj`)
    obtain ⟨seqB, hseqB_sub, hseqB_anti, hseqB_prop⟩ :=
      exists_pruning_chain hlogN_pos hM_ge12 hM_le_N (by omega : 1 ≤ 4 * dj) h4dj_le_z
        (fun n hn => hA_MN n (hBA hn)) hRB_init
        (fun q hq => hq_pisq q (ppowersInSet_mono hBA hq)) hPisq
        (fun d hd1 hd2 => hα_big_all d (by omega) hd2)
        (fun d hd1 hd2 => hgap_all d (by omega) hd2)
    -- `seqB (z - 4 * dj)` is nonempty; pick `n₁` in it!
    have hne_Bend : (seqB (z - 4 * dj)).Nonempty := by
      by_contra hemp
      have hlo := (hseqB_prop (z - 4 * dj) le_rfl).1
      rw [Finset.not_nonempty_iff_eq_empty.mp hemp, recSumReal_empty] at hlo
      have hpos := hRA_lb (4 * dj + (z - 4 * dj)) (by omega) (by omega)
      linarith [Real.rpow_pos_of_pos hlogN_pos (-(1 / 101 : ℝ))]
    obtain ⟨n₁, hn₁⟩ := hne_Bend
    have hn₁_Aj : n₁ ∈ Aj := hBAj (hseqB_sub (z - 4 * dj) le_rfl hn₁)
    obtain ⟨d₁, d₂, hd1_y, hd12, hd2z, hd1_dvd, hd2_dvd⟩ := hA_div n₁ (hAjA hn₁_Aj)
    -- By minimality of `j`, `dj ≤ d₁`, hence `4 * dj ≤ d₂ ≤ z`!
    have hdj_le_d1 : dj ≤ d₁ := by
      by_contra hlt
      have hi_lt : d₁ - y < j := by omega
      have hnot := Nat.find_min hex_i hi_lt
      apply hnot
      refine ⟨by omega, n₁, hseq_anti (d₁ - y) j (by omega) hj_le hn₁_Aj, ?_⟩
      rwa [show y + (d₁ - y) = d₁ by omega]
    set s : ℕ := d₂ - 4 * dj
    have hs_le : s ≤ z - 4 * dj := by omega
    have hes_eq : 4 * dj + s = d₂ := by omega
    set Bs : Finset ℕ := seqB s
    have hBsB : Bs ⊆ B := hseqB_sub s hs_le
    have hBsA : Bs ⊆ A := hBsB.trans hBA
    have hBs_prop := hseqB_prop s hs_le
    rw [hes_eq] at hBs_prop
    have hd2_dvd_lcm : d₂ ∣ lcmSet (ppowersInSet Bs) := by
      have h0Bs : 0 ∉ Bs := fun h => h0A (hBsA h)
      rw [lcmSet_ppowersInSet_eq h0Bs]
      exact dvd_trans hd2_dvd (Finset.dvd_lcm (hseqB_anti s (z - 4 * dj) hs_le le_rfl hn₁))
    -- Apply `hPropTech` to `Bs`: Case 1 is impossible since `∑_{𝒬_{Bs}} 1/q ≤ ∑_{𝒬_B} 1/q ≤ (2/3) LL`!
    have hQBs_le : ∑ q ∈ ppowersInSet Bs, (1 : ℝ) / (q : ℝ) ≤ (2 / 3 : ℝ) * LL :=
      (Finset.sum_le_sum_of_subset_of_nonneg (ppowersInSet_mono hBsB) fun _ _ _ => by positivity).trans hQB_le
    have hTech_Bs := hPropTech M Bs hM_ge12 hM_le_N (fun n hn => hA_MN n (hBsA hn))
      (fun n hn => hA_ω n (hBsA hn)) ((hRA_lb d₂ (by omega) hd2z).trans hBs_prop.1) hBs_prop.2.2
    rcases hTech_Bs with ⟨hgt, _⟩ | hCase2_Bs
    · exact absurd hQBs_le hgt
    · exact hsolve_of_case2 Bs d₂ hBsA (by omega) hd2z hBs_prop.1 hBs_prop.2.1 hd2_dvd_lcm hCase2_Bs
  · -- Case 2 holds directly for `Aj`!
    exact hsolve_of_case2 Aj dj hAjA (by omega) (by omega) hAj_prop.1 hAj_prop.2.1 hdj_dvd_lcm hCase2_Aj

/-! ## Section 4: Headline Unconditional Theorems (PPL 024 — Zhi-Wei Sun's Conjecture) -/

/-- **PPL 024 (Sign `d = -1`)**: Every positive rational `r : ℚ` is a finite sum of distinct
unit fractions `1 / (p - 1)` with `p` prime. Completely unconditional. -/
theorem ppl024_sun_minus_one (r : ℚ) (hr : 0 < r) :
    ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧
      r = ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) - 1) := by
  obtain ⟨S, hSpr, hsum⟩ := sun_conjecture_of_bloom_prop1 bloom_prop1_unconditional r hr false
  refine ⟨S, hSpr, ?_⟩
  simpa [sub_eq_add_neg] using hsum

/-- **PPL 024 (Sign `d = +1`)**: Every positive rational `r : ℚ` is a finite sum of distinct
unit fractions `1 / (p + 1)` with `p` prime. Completely unconditional. -/
theorem ppl024_sun_plus_one (r : ℚ) (hr : 0 < r) :
    ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧
      r = ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) + 1) := by
  obtain ⟨S, hSpr, hsum⟩ := sun_conjecture_of_bloom_prop1 bloom_prop1_unconditional r hr true
  refine ⟨S, hSpr, ?_⟩
  simpa using hsum

/-- **PPL 024 (Unified Statement — Both Signs `d ∈ {-1, 1}`)**:
For every positive rational `r : ℚ` and both signs `d ∈ ({-1, 1} : Set ℤ)`, there exists a
finite set `S : Finset ℕ` of primes (`∀ p ∈ S, Nat.Prime p`) such that
`r = ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) + (d : ℚ))`. Completely unconditional. -/
theorem ppl024_sun_both (r : ℚ) (hr : 0 < r) (d : ℤ) (hd : d ∈ ({-1, 1} : Set ℤ)) :
    ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧
      r = ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) + (d : ℚ)) := by
  rcases hd with rfl | rfl
  · obtain ⟨S, hSpr, hsum⟩ := ppl024_sun_minus_one r hr
    refine ⟨S, hSpr, ?_⟩
    simpa [sub_eq_add_neg] using hsum
  · obtain ⟨S, hSpr, hsum⟩ := ppl024_sun_plus_one r hr
    refine ⟨S, hSpr, ?_⟩
    simpa using hsum

end PPL024

#print axioms PPL024.ppl024_sun_minus_one
#print axioms PPL024.ppl024_sun_plus_one
#print axioms PPL024.ppl024_sun_both
