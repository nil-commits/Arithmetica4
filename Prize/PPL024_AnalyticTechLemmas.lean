import Prize.PPL024_Comb_Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Prize.PPL024_AnalyticTechLemmas

Self-contained unconditional formalization of Bloom's 5 technical combinatorial lemmas from
Sections 4–5 of `arXiv:2112.03726` built directly on top of `Prize.PPL024_Comb_Defs`:

1. `ppl024_lem_basic` (Lemma 1): common prime-power divisor reciprocal sum `≤ 0.01 log log N`.
2. `ppl024_lem_rtop` (Lemma 2): lower bound `∑_{q ∈ 𝒬_A} 1/q ≥ (1 - 2ε) e⁻¹ log log N`.
3. `ppl024_lem_usingq` (Lemma 3): extraction of rough coprime divisor `d` with
   `q d > M N^{-2 / log log N}` and `ω(d) < (1/500) log log N`.
4. `ppl024_lem_pisqa` (Lemma 6): greedy prime-power pruning for `R(B; q) ≥ 2 / (log N)^{1/100}`.
5. `ppl024_lem_pisq` (Lemma 7): controlled mass pruning to `R(B) ∈ [α - 1/M, α)`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Finset Filter Topology Prize.PPL024
open scoped BigOperators Classical

namespace PPL024

/-! ## Section 1: `ppl024_lem_basic` (Bloom's Lemma 1) -/

/-- **Bloom's Lemma 1 (`lem-basic`)**:
For all sufficiently large `N : ℕ`, if `n₁ n₂ : ℤ` satisfy `n₁ ≠ n₂` and `|(n₁ - n₂ : ℝ)| ≤ N`,
then `∑_{q ≤ N, IsPrimePow q, q ∣ n₁, q ∣ n₂} 1/q ≤ (1 / 100) * log (log N)`. -/
theorem ppl024_lem_basic :
    ∀ᶠ N : ℕ in atTop, ∀ (n₁ n₂ : ℤ), n₁ ≠ n₂ → |(n₁ - n₂ : ℝ)| ≤ (N : ℝ) →
      ∑ q ∈ (Finset.Icc 1 N).filter (fun q : ℕ => IsPrimePow q ∧ (q : ℤ) ∣ n₁ ∧ (q : ℤ) ∣ n₂),
        (1 : ℝ) / (q : ℝ) ≤ (1 / 100 : ℝ) * Real.log (Real.log (N : ℝ)) := by
  obtain ⟨C_pp, hCpp_pos, hCpp⟩ := Prize.PPL024.sum_inv_ppow_le
  have hLL : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- `log (log (2 * (log N)^2)) / log (log N) → 0`
  have hratio : Tendsto (fun N : ℕ =>
      (Real.log (Real.log (2 * (Real.log (N : ℝ)) ^ 2)) + C_pp + 4) /
        Real.log (Real.log (N : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => (Real.log (Real.log (2 * u ^ 2)) + C_pp + 4) / Real.log u)
        atTop (𝓝 0) := by
      have hsub : Tendsto (fun v : ℝ => (Real.log (2 * v + Real.log 2) + C_pp + 4) / v)
          atTop (𝓝 0) := by
        have ha : Tendsto (fun v : ℝ => Real.log (2 * v + Real.log 2) / v) atTop (𝓝 0) := by
          have h0 := Real.tendsto_pow_log_div_mul_add_atTop 2 (Real.log 2) 1 (by norm_num)
          have h0' : Tendsto (fun v : ℝ => Real.log (2 * v + Real.log 2) / (2 * v + Real.log 2))
              atTop (𝓝 0) := by
            have hlin : Tendsto (fun v : ℝ => 2 * v + Real.log 2) atTop atTop :=
              Tendsto.atTop_add (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id)
                tendsto_const_nhds
            have hlu : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
              simpa [Real.rpow_one] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
            exact hlu.comp hlin
          have hmul : Tendsto (fun v : ℝ => (2 * v + Real.log 2) / v) atTop (𝓝 2) := by
            have hc : Tendsto (fun v : ℝ => 2 + Real.log 2 / v) atTop (𝓝 (2 + 0)) := by
              have h0 := tendsto_inv_atTop_zero.const_mul (Real.log 2)
              rw [mul_zero] at h0
              exact tendsto_const_nhds.add (h0.congr fun v => (div_eq_mul_inv _ _).symm)
            rw [add_zero] at hc
            refine hc.congr' ?_
            filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
            field_simp [hv.ne']
          have hprod := h0'.mul hmul
          rw [zero_mul] at hprod
          refine hprod.congr' ?_
          filter_upwards [eventually_gt_atTop (1 : ℝ)] with v hv
          have h2v : 0 < 2 * v + Real.log 2 := by
            have : 0 < Real.log 2 := Real.log_pos (by norm_num)
            linarith
          field_simp [h2v.ne', hv.ne']
        have hb : Tendsto (fun v : ℝ => (C_pp + 4) / v) atTop (𝓝 0) := by
          simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.const_mul (C_pp + 4))
        have hs := ha.add hb; rw [add_zero] at hs
        exact hs.congr fun v => by ring
      refine (hsub.comp Real.tendsto_log_atTop).congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
      simp only [Function.comp_apply]
      have hlog : Real.log (2 * u ^ 2) = 2 * Real.log u + Real.log 2 := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; ring
      rw [hlog]
    exact h1.comp hlogN
  filter_upwards [
    eventually_ge_atTop 16,
    hlogN.eventually_ge_atTop 4,
    hLL.eventually_ge_atTop 1,
    hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100))
  ] with N hN16 hlogN4 hLL1 hrat
  intro n₁ n₂ hne hdiff
  set m : ℕ := (n₁ - n₂).natAbs
  have hm_pos : 0 < m := Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  have hm_le_N : m ≤ N := by
    have h1 : (m : ℝ) = |(n₁ - n₂ : ℝ)| := by
      dsimp only [m]
      rw [← Int.cast_natCast (n₁ - n₂).natAbs, Int.natCast_natAbs, Int.cast_abs]
      push_cast; rfl
    exact_mod_cast (h1.le.trans hdiff)
  set Q := (Finset.Icc 1 N).filter (fun q : ℕ => IsPrimePow q ∧ (q : ℤ) ∣ n₁ ∧ (q : ℤ) ∣ n₂)
  set L : ℕ := ⌈(Real.log (N : ℝ)) ^ 2⌉₊
  have hL_ge3 : 3 ≤ L := by
    have h1 : (3 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := by nlinarith
    exact_mod_cast (h1.trans (Nat.le_ceil _))
  have hL_le : (L : ℝ) ≤ 2 * (Real.log (N : ℝ)) ^ 2 := by
    have h1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ (Real.log (N : ℝ)) ^ 2)
    nlinarith
  -- Split `Q` into: non-prime prime powers, primes `≤ L`, and primes `> L` dividing `m`
  set Q_np := (Finset.Icc 1 N).filter (fun q => IsPrimePow q ∧ ¬ q.Prime)
  set Q_lo := (Finset.Icc 1 L).filter IsPrimePow
  set Q_hi := m.primeFactors.filter (fun p => L < p)
  have hQ_sub : Q ⊆ Q_np ∪ Q_lo ∪ Q_hi := by
    intro q hq
    obtain ⟨hq_icc, hq_pp, hq1, hq2⟩ := Finset.mem_filter.mp hq
    by_cases hpr : q.Prime
    · by_cases hle : q ≤ L
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq_icc).1, hle⟩, hq_pp⟩))
      · have hdvd_sub : (q : ℤ) ∣ (n₁ - n₂) := dvd_sub hq1 hq2
        have hdvd_m : q ∣ m := Int.natCast_dvd.mp hdvd_sub
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpr, hdvd_m, hm_pos.ne'⟩, by omega⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hq_icc, hq_pp, hpr⟩))
  have hsum_union : ∀ A B : Finset ℕ,
      ∑ q ∈ A ∪ B, (1 : ℝ) / (q : ℝ) ≤
        (∑ q ∈ A, (1 : ℝ) / (q : ℝ)) + ∑ q ∈ B, (1 : ℝ) / (q : ℝ) := by
    intro A B
    have hui := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := fun q : ℕ => (1 : ℝ) / (q : ℝ))
    have hnn : 0 ≤ ∑ q ∈ A ∩ B, (1 : ℝ) / (q : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
    linarith
  -- Bound each of the 3 pieces
  have h1_np : ∑ q ∈ Q_np, (1 : ℝ) / (q : ℝ) ≤ 2 := Prize.PPL024.sum_inv_nonprime_ppow_le N
  have h2_lo : ∑ q ∈ Q_lo, (1 : ℝ) / (q : ℝ) ≤
      Real.log (Real.log (2 * (Real.log (N : ℝ)) ^ 2)) + C_pp := by
    have hA := hCpp L hL_ge3
    have hlogL_pos : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
    have hlog_mono : Real.log (Real.log (L : ℝ)) ≤
        Real.log (Real.log (2 * (Real.log (N : ℝ)) ^ 2)) :=
      Real.log_le_log hlogL_pos (Real.log_le_log (by positivity) hL_le)
    linarith
  have h3_hi : ∑ q ∈ Q_hi, (1 : ℝ) / (q : ℝ) ≤ 2 := by
    have hcard_pf : (m.primeFactors.card : ℝ) ≤ 2 * Real.log (N : ℝ) := by
      have h2pow : 2 ^ m.primeFactors.card ≤ m := by
        calc 2 ^ m.primeFactors.card
            = ∏ _p ∈ m.primeFactors, 2 := by rw [Finset.prod_const]
          _ ≤ ∏ p ∈ m.primeFactors, p :=
              Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
          _ ≤ m := Nat.le_of_dvd hm_pos (Nat.prod_primeFactors_dvd m)
      have h2R : ((2 : ℝ) ^ m.primeFactors.card) ≤ (N : ℝ) := by
        exact_mod_cast h2pow.trans hm_le_N
      have hlog := Real.log_le_log (by positivity) h2R
      rw [Real.log_pow] at hlog
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith [Nat.cast_nonneg (α := ℝ) m.primeFactors.card]
    have hQhi_card : (Q_hi.card : ℝ) ≤ 2 * Real.log (N : ℝ) :=
      ((by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _) :
        (Q_hi.card : ℝ) ≤ (m.primeFactors.card : ℝ))).trans hcard_pf
    have hL_pos : (0 : ℝ) < (Real.log (N : ℝ)) ^ 2 := by positivity
    calc ∑ q ∈ Q_hi, (1 : ℝ) / (q : ℝ)
        ≤ ∑ _q ∈ Q_hi, (1 : ℝ) / ((Real.log (N : ℝ)) ^ 2) := by
          refine Finset.sum_le_sum fun q hq => ?_
          have hq_gt : L < q := (Finset.mem_filter.mp hq).2
          have hle : (Real.log (N : ℝ)) ^ 2 ≤ (q : ℝ) :=
            (Nat.le_ceil _).trans (by exact_mod_cast hq_gt.le)
          exact one_div_le_one_div_of_le hL_pos hle
      _ = (Q_hi.card : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ (2 * Real.log (N : ℝ)) / (Real.log (N : ℝ)) ^ 2 :=
          div_le_div_of_nonneg_right hQhi_card hL_pos.le
      _ = 2 / Real.log (N : ℝ) := by
          have hne0 : Real.log (N : ℝ) ≠ 0 := by linarith
          field_simp [hne0]
      _ ≤ 2 := by
          rw [div_le_iff₀ (by linarith)]; linarith
  have htot : ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) ≤
      Real.log (Real.log (2 * (Real.log (N : ℝ)) ^ 2)) + C_pp + 4 := by
    have h0 : ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) ≤
        ∑ q ∈ Q_np ∪ Q_lo ∪ Q_hi, (1 : ℝ) / (q : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hQ_sub fun q _ _ => by positivity
    have hu1 := hsum_union (Q_np ∪ Q_lo) Q_hi
    have hu2 := hsum_union Q_np Q_lo
    linarith
  have hrat' := (div_lt_iff₀ (by linarith : (0 : ℝ) < Real.log (Real.log (N : ℝ)))).mp hrat
  linarith

/-! ## Section 2: `ppl024_lem_rtop` (Bloom's Lemma 2) -/

/-- Elementary Stirling lower bound `t^t / exp(t) ≤ t!`, i.e. `(t / exp 1)^t ≤ t!`. -/
private lemma div_exp_pow_le_factorial (t : ℕ) :
    ((t : ℝ) / Real.exp 1) ^ t ≤ (t.factorial : ℝ) := by
  have hexp_pos : 0 < Real.exp (t : ℝ) := Real.exp_pos _
  have hterm : (t : ℝ) ^ t / (t.factorial : ℝ) ≤ Real.exp (t : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg (α := ℝ) t) (t + 1)
    have hle : (t : ℝ) ^ t / (t.factorial : ℝ) ≤
        ∑ i ∈ Finset.range (t + 1), (t : ℝ) ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i : ℕ => (t : ℝ) ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self t))
    exact hle.trans hsum
  have hfac_pos : (0 : ℝ) < (t.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos t)
  rw [div_pow, ← Real.exp_nat_mul, mul_one, div_le_iff₀ hexp_pos]
  rw [div_le_iff₀ hfac_pos] at hterm
  linarith

/-- For fixed `t : ℕ` and `A : Finset ℕ` (`0 ∉ A`), letting `A_t = {n ∈ A : ω(n) = t}`,
we have `t! * R(A_t) ≤ (∑_{q ∈ 𝒬_A} 1/q)^t`. -/
private lemma factorial_mul_recSumReal_omega_eq_le (A : Finset ℕ) (h0 : 0 ∉ A) (t : ℕ) :
    (t.factorial : ℝ) * recSumReal (A.filter (fun n => omega n = t)) ≤
      (∑ q ∈ ppowersInSet A, (1 : ℝ) / (q : ℝ)) ^ t := by
  set Q := ppowersInSet A
  set At := A.filter (fun n => omega n = t)
  -- `((∑ q ∈ Q, 1/q) ^ t) = ∑ f ∈ Fintype.piFinset (fun _ : Fin t => Q), ∏ i, 1 / f i`
  set Ω : Finset (Fin t → ℕ) := Fintype.piFinset (fun _ : Fin t => Q)
  have hpow_eq : (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) ^ t =
      ∑ f ∈ Ω, ∏ i : Fin t, (1 : ℝ) / (f i : ℝ) := by
    simpa [Ω] using Finset.sum_pow' Q (fun q => (1 : ℝ) / (q : ℝ)) t
  rw [hpow_eq]
  -- For each `n ∈ At`, let `Perms n = {f ∈ Ω : (∀ i, f i ∈ exactPrimePowers n) ∧ Function.Injective f}`
  set Perms : ℕ → Finset (Fin t → ℕ) := fun n =>
    Ω.filter (fun f => (∀ i, f i ∈ exactPrimePowers n) ∧ Function.Injective f)
  -- Each `f ∈ Perms n` has `∏ i, f i = n`, hence `∏ i, 1/(f i) = 1/n` and `Perms n₁`, `Perms n₂` are disjoint!
  have hprod_eq : ∀ n ∈ At, ∀ f ∈ Perms n, ∏ i : Fin t, f i = n := by
    intro n hn f hf
    have hnA : n ∈ A := (Finset.mem_filter.mp hn).1
    have hnt : omega n = t := (Finset.mem_filter.mp hn).2
    have hn0 : n ≠ 0 := fun h => h0 (h ▸ hnA)
    obtain ⟨_, hmem, hinj⟩ := Finset.mem_filter.mp hf
    have himg : Finset.univ.image f = exactPrimePowers n := by
      apply Finset.eq_of_subset_of_card_le
      · intro q hq
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
        exact hmem i
      · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
          card_exactPrimePowers, hnt]
    rw [← prod_exactPrimePowers hn0, ← himg, Finset.prod_image (fun a _ b _ h => hinj h)]
  have hcard_perms : ∀ n ∈ At, (Perms n).card = t.factorial := by
    intro n hn
    have hnA : n ∈ A := (Finset.mem_filter.mp hn).1
    have hnt : omega n = t := (Finset.mem_filter.mp hn).2
    have hcard_ep : (exactPrimePowers n).card = t := by rw [card_exactPrimePowers, hnt]
    have hsub_ep : exactPrimePowers n ⊆ Q := fun q hq => Finset.mem_biUnion.mpr ⟨n, hnA, hq⟩
    -- Bijection between `Equiv.Perm (Fin t)` and `Perms n` via a fixed equiv `Fin t ≃ exactPrimePowers n`
    have hcard_eq : Fintype.card (Fin t) = Fintype.card (exactPrimePowers n) := by
      rw [Fintype.card_fin, Fintype.card_coe, hcard_ep]
    let e0 : Fin t ≃ exactPrimePowers n := Fintype.equivOfCardEq hcard_eq
    have hbij : (Finset.univ : Finset (Equiv.Perm (Fin t))).image (fun σ i => (e0 (σ i) : ℕ)) = Perms n := by
      ext f
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Perms, Ω, Finset.mem_filter,
        Fintype.mem_piFinset]
      constructor
      · rintro ⟨σ, rfl⟩
        refine ⟨fun i => hsub_ep (e0 (σ i)).2, fun i => (e0 (σ i)).2, fun i j h => ?_⟩
        exact σ.injective (e0.injective (Subtype.ext h))
      · rintro ⟨_, hmem, hinj⟩
        let g : Fin t → exactPrimePowers n := fun i => ⟨f i, hmem i⟩
        have hg_inj : Function.Injective g := fun i j h => hinj (congrArg Subtype.val h)
        let σfun : Fin t → Fin t := fun i => e0.symm (g i)
        have hσ_inj : Function.Injective σfun := e0.symm.injective.comp hg_inj
        let σ : Equiv.Perm (Fin t) := Equiv.ofBijective σfun (Finite.injective_iff_bijective.mp hσ_inj)
        refine ⟨σ, ?_⟩
        funext i
        change (e0 (e0.symm (g i)) : ℕ) = f i
        simp [g]
    rw [← hbij, Finset.card_image_of_injective]
    · rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    · intro σ₁ σ₂ h
      ext i
      have hi := congrFun h i
      exact congrArg Fin.val (e0.injective (Subtype.ext hi))
  have hpair : (At : Set ℕ).PairwiseDisjoint Perms := by
    intro n₁ hn₁ n₂ hn₂ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro f hf₁ hf₂
    exact hne ((hprod_eq n₁ hn₁ f hf₁).symm.trans (hprod_eq n₂ hn₂ f hf₂))
  have hbi_sub : At.biUnion Perms ⊆ Ω :=
    Finset.biUnion_subset.mpr fun _ _ => Finset.filter_subset _ _
  calc (t.factorial : ℝ) * recSumReal At
      = ∑ n ∈ At, (t.factorial : ℝ) * ((1 : ℝ) / (n : ℝ)) := by
        unfold recSumReal; rw [Finset.mul_sum]
    _ = ∑ n ∈ At, ∑ f ∈ Perms n, ∏ i : Fin t, (1 : ℝ) / (f i : ℝ) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have heach : ∀ f ∈ Perms n, ∏ i : Fin t, (1 : ℝ) / (f i : ℝ) = (1 : ℝ) / (n : ℝ) := by
          intro f hf
          rw [Finset.prod_div_distrib, Finset.prod_const_one, ← Nat.cast_prod, hprod_eq n hn f hf]
        rw [Finset.sum_congr rfl heach, Finset.sum_const, hcard_perms n hn, nsmul_eq_mul]
    _ = ∑ f ∈ At.biUnion Perms, ∏ i : Fin t, (1 : ℝ) / (f i : ℝ) := (Finset.sum_biUnion hpair).symm
    _ ≤ ∑ f ∈ Ω, ∏ i : Fin t, (1 : ℝ) / (f i : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hbi_sub fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity

/-- Elementary monotonicity: for `0 < X ≤ t₀ ≤ t`, `(exp 1 * X / t)^t ≤ (exp 1 * X / t₀)^t₀`. -/
private lemma exp_mul_div_rpow_antitone {X t₀ t : ℝ} (hX : 0 < X) (hXt₀ : X ≤ t₀) (ht : t₀ ≤ t) :
    (Real.exp 1 * X / t) ^ t ≤ (Real.exp 1 * X / t₀) ^ t₀ := by
  have ht₀_pos : 0 < t₀ := lt_of_lt_of_le hX hXt₀
  have ht_pos : 0 < t := lt_of_lt_of_le ht₀_pos ht
  have hb1 : 0 < Real.exp 1 * X / t := by positivity
  have hb0 : 0 < Real.exp 1 * X / t₀ := by positivity
  rw [Real.rpow_def_of_pos hb1, Real.rpow_def_of_pos hb0, Real.exp_le_exp]
  have hlog1 : Real.log (Real.exp 1 * X / t) = 1 + Real.log (X / t₀) - Real.log (t / t₀) := by
    rw [Real.log_div (by positivity) ht_pos.ne', Real.log_mul (Real.exp_pos 1).ne' hX.ne',
      Real.log_exp, Real.log_div hX.ne' ht₀_pos.ne', Real.log_div ht_pos.ne' ht₀_pos.ne']
    ring
  have hlog0 : Real.log (Real.exp 1 * X / t₀) = 1 + Real.log (X / t₀) := by
    rw [Real.log_div (by positivity) ht₀_pos.ne', Real.log_mul (Real.exp_pos 1).ne' hX.ne',
      Real.log_exp, Real.log_div hX.ne' ht₀_pos.ne']
    ring
  rw [hlog1, hlog0]
  have hlog_neg : Real.log (X / t₀) ≤ 0 := Real.log_nonpos (by positivity) ((div_le_one ht₀_pos).mpr hXt₀)
  have hlog_t : t - t₀ ≤ t * Real.log (t / t₀) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos ht₀_pos ht_pos)
    have h2 : Real.log (t₀ / t) = -Real.log (t / t₀) := by
      rw [Real.log_div ht₀_pos.ne' ht_pos.ne', Real.log_div ht_pos.ne' ht₀_pos.ne']; ring
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 ht_pos.le
    have h4 : t * (t₀ / t - 1) = t₀ - t := by field_simp [ht_pos.ne']
    linarith
  nlinarith

/-- **Bloom's Lemma 2 (`lem-rtop`)**:
For `0 < ε < 1/2` and sufficiently large `N`, if `A : Finset ℕ` (`0 ∉ A`) has
`R(A) ≥ (log N)^{-ε/2}` and `(1 - ε) log log N ≤ ω(n) ≤ 2 log log N` for all `n ∈ A`, then
`∑_{q ∈ 𝒬_A} 1/q ≥ (1 - 2ε) e⁻¹ log log N`. -/
theorem ppl024_lem_rtop (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, 0 ∉ A →
      (Real.log (N : ℝ)) ^ (-ε / 2) ≤ recSumReal A →
      (∀ n ∈ A, (1 - ε) * Real.log (Real.log (N : ℝ)) ≤ (omega n : ℝ) ∧
                (omega n : ℝ) ≤ 2 * Real.log (Real.log (N : ℝ))) →
      (1 - 2 * ε) * Real.exp (-1) * Real.log (Real.log (N : ℝ)) ≤
        ∑ q ∈ ppowersInSet A, (1 : ℝ) / (q : ℝ) := by
  have hLL : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  -- `log (2 * LL + 1) / ((1 - ε) * LL) → 0`
  have hsmall_tend : Tendsto (fun N : ℕ =>
      Real.log (2 * Real.log (Real.log (N : ℝ)) + 1) /
        ((1 - ε) * Real.log (Real.log (N : ℝ)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => Real.log (2 * u + 1) / ((1 - ε) * u)) atTop (𝓝 0) := by
      have ha : Tendsto (fun u : ℝ => Real.log (2 * u + 1) / (2 * u + 1)) atTop (𝓝 0) := by
        have hlin : Tendsto (fun u : ℝ => 2 * u + 1) atTop atTop :=
          Tendsto.atTop_add (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id) tendsto_const_nhds
        have hlu : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
          simpa [Real.rpow_one] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
        exact hlu.comp hlin
      have hb : Tendsto (fun u : ℝ => (2 * u + 1) / ((1 - ε) * u)) atTop (𝓝 (2 / (1 - ε))) := by
        have hc : Tendsto (fun u : ℝ => 2 / (1 - ε) + (1 / (1 - ε)) / u) atTop (𝓝 (2 / (1 - ε) + 0)) := by
          have h0 := tendsto_inv_atTop_zero.const_mul (1 / (1 - ε))
          rw [mul_zero] at h0
          exact tendsto_const_nhds.add (h0.congr fun u => (div_eq_mul_inv _ _).symm)
        rw [add_zero] at hc
        refine hc.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
        have h1ε : (1 - ε) ≠ 0 := by linarith
        field_simp [h1ε, hu.ne']
      have hp := ha.mul hb; rw [zero_mul] at hp
      refine hp.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      have h2u : 2 * u + 1 ≠ 0 := by linarith
      field_simp [h2u]
    exact h1.comp hLL
  -- Choose `δ > 0` so that `(1 - ε) * exp(-ε / (2 * (1 - ε)) - δ) ≥ 1 - 2ε`!
  -- Note `(1 - ε) * exp(-ε / (2 * (1 - ε))) ≥ (1 - ε) * (1 - ε / (2 * (1 - ε))) = 1 - (3/2) * ε > 1 - 2ε`!
  have hgap_pos : 0 < (1 - ε) * Real.exp (-ε / (2 * (1 - ε))) - (1 - 2 * ε) := by
    have h1 : 1 - ε / (2 * (1 - ε)) ≤ Real.exp (-ε / (2 * (1 - ε))) := by
      have h := Real.add_one_le_exp (-ε / (2 * (1 - ε)))
      have heq : -ε / (2 * (1 - ε)) = -(ε / (2 * (1 - ε))) := neg_div _ _
      linarith
    have h2 : (1 - ε) * (1 - ε / (2 * (1 - ε))) = 1 - (3 / 2 : ℝ) * ε := by
      have hne : (1 - ε) ≠ 0 := by linarith
      field_simp [hne]; ring
    nlinarith
  have hratio_gt1 : 1 < ((1 - ε) * Real.exp (-ε / (2 * (1 - ε)))) / (1 - 2 * ε) := by
    rw [one_lt_div (by linarith)]
    linarith
  set δ : ℝ := Real.log (((1 - ε) * Real.exp (-ε / (2 * (1 - ε)))) / (1 - 2 * ε))
  have hδ_pos : 0 < δ := Real.log_pos hratio_gt1
  filter_upwards [
    eventually_ge_atTop 16,
    hLL.eventually_ge_atTop (4 / (1 - ε)),
    hsmall_tend.eventually (gt_mem_nhds hδ_pos)
  ] with N hN16 hLL_big hsmall
  intro A h0 hRA hω
  set LL : ℝ := Real.log (Real.log (N : ℝ))
  have hLL_pos : 0 < LL := by
    have h1ε_pos : 0 < 1 - ε := by linarith
    have : (0 : ℝ) < 4 / (1 - ε) := div_pos (by norm_num) h1ε_pos
    linarith
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  set X : ℝ := ∑ q ∈ ppowersInSet A, (1 : ℝ) / (q : ℝ)
  set t₀ : ℝ := (1 - ε) * LL
  have ht₀_ge4 : 4 ≤ t₀ := by
    have h1 := mul_le_mul_of_nonneg_left hLL_big (by linarith : 0 ≤ 1 - ε)
    have h2 : (1 - ε) * (4 / (1 - ε)) = 4 := by
      have hne : (1 - ε) ≠ 0 := by linarith
      field_simp [hne]
    linarith
  -- Easy case: if `t₀ ≤ X`, done immediately!
  by_cases hX_big : t₀ ≤ X
  · have hexp_le1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have hexp_pos : 0 < Real.exp (-1) := Real.exp_pos (-1)
    have h1 : (1 - 2 * ε) * Real.exp (-1) ≤ 1 - ε := by nlinarith
    have h2 : (1 - 2 * ε) * Real.exp (-1) * LL ≤ (1 - ε) * LL :=
      mul_le_mul_of_nonneg_right h1 hLL_pos.le
    exact h2.trans hX_big
  push Not at hX_big
  -- Since `R(A) ≥ (log N)^{-ε/2} > 0`, `A` is nonempty, and every `n ∈ A` has `ω(n) ≥ 4`, so `X > 0`!
  have hA_ne : A.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty.mp hemp, recSumReal_empty] at hRA
    linarith [Real.rpow_pos_of_pos hlogN_pos (-ε / 2)]
  have hX_pos : 0 < X := by
    obtain ⟨n, hn⟩ := hA_ne
    have hωn : 1 ≤ omega n := by
      have h1 := (hω n hn).1
      have : (1 : ℝ) ≤ (omega n : ℝ) := by linarith
      exact_mod_cast this
    have hep_ne : (exactPrimePowers n).Nonempty := by
      rw [← Finset.card_pos, card_exactPrimePowers]; exact hωn
    obtain ⟨q, hq⟩ := hep_ne
    have hq_mem : q ∈ ppowersInSet A := Finset.mem_biUnion.mpr ⟨n, hn, hq⟩
    have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (mem_ppowersInSet_pos h0 hq_mem)
    have hle : (1 : ℝ) / (q : ℝ) ≤ X :=
      Finset.single_le_sum (f := fun q : ℕ => (1 : ℝ) / (q : ℝ)) (fun _ _ => by positivity) hq_mem
    linarith [one_div_pos.mpr hq_pos]
  -- Partition `A` by `t = omega n ∈ I = Icc ⌈t₀⌉₊ ⌊2 * LL⌋₊`
  set I : Finset ℕ := Finset.Icc ⌈t₀⌉₊ ⌊2 * LL⌋₊
  have hA_part : recSumReal A = ∑ t ∈ I, recSumReal (A.filter (fun n => omega n = t)) := by
    have hcov : A = I.biUnion (fun t => A.filter (fun n => omega n = t)) := by
      ext n
      simp only [Finset.mem_biUnion, Finset.mem_filter, I, Finset.mem_Icc]
      constructor
      · intro hn
        refine ⟨omega n, ⟨Nat.ceil_le.mpr (hω n hn).1, Nat.le_floor (hω n hn).2⟩, hn, rfl⟩
      · rintro ⟨_, _, hn, _⟩; exact hn
    have hpair : (I : Set ℕ).PairwiseDisjoint (fun t => A.filter (fun n => omega n = t)) := by
      intro t₁ _ t₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      exact hne ((Finset.mem_filter.mp hn1).2.symm.trans (Finset.mem_filter.mp hn2).2)
    conv_lhs => rw [hcov]
    unfold recSumReal
    rw [Finset.sum_biUnion hpair]
  have hterm_le : ∀ t ∈ I,
      recSumReal (A.filter (fun n => omega n = t)) ≤ (Real.exp 1 * X / t₀) ^ t₀ := by
    intro t ht
    have ht_ge : t₀ ≤ (t : ℝ) := (Nat.le_ceil t₀).trans (by exact_mod_cast (Finset.mem_Icc.mp ht).1)
    have hfac := factorial_mul_recSumReal_omega_eq_le A h0 t
    have hstirl := div_exp_pow_le_factorial t
    have hfac_pos : (0 : ℝ) < (t.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos t)
    have ht_pos : (0 : ℝ) < (t : ℝ) := by linarith
    have h1 : recSumReal (A.filter (fun n => omega n = t)) ≤ (Real.exp 1 * X / (t : ℝ)) ^ t := by
      calc recSumReal (A.filter (fun n => omega n = t))
          ≤ X ^ t / (t.factorial : ℝ) := (le_div_iff₀ hfac_pos).mpr (by linarith)
        _ ≤ X ^ t / (((t : ℝ) / Real.exp 1) ^ t) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hstirl
        _ = (Real.exp 1 * X / (t : ℝ)) ^ t := by
            rw [← div_pow]; congr 1; field_simp [ht_pos.ne', (Real.exp_pos 1).ne']
    rw [← Real.rpow_natCast] at h1
    exact h1.trans (exp_mul_div_rpow_antitone hX_pos hX_big.le ht_ge)
  have hI_card : (I.card : ℝ) ≤ 2 * LL + 1 := by
    have hle : I.card ≤ ⌊2 * LL⌋₊ + 1 := by
      dsimp only [I]; rw [Nat.card_Icc]; omega
    have hfl : (⌊2 * LL⌋₊ : ℝ) ≤ 2 * LL := Nat.floor_le (by positivity)
    have hleR : (I.card : ℝ) ≤ (⌊2 * LL⌋₊ : ℝ) + 1 := by exact_mod_cast hle
    linarith
  have hmain : (Real.log (N : ℝ)) ^ (-ε / 2) ≤ (2 * LL + 1) * (Real.exp 1 * X / t₀) ^ t₀ := by
    calc (Real.log (N : ℝ)) ^ (-ε / 2)
        ≤ recSumReal A := hRA
      _ = ∑ t ∈ I, recSumReal (A.filter (fun n => omega n = t)) := hA_part
      _ ≤ ∑ _t ∈ I, (Real.exp 1 * X / t₀) ^ t₀ := Finset.sum_le_sum hterm_le
      _ = (I.card : ℝ) * (Real.exp 1 * X / t₀) ^ t₀ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * LL + 1) * (Real.exp 1 * X / t₀) ^ t₀ :=
          mul_le_mul_of_nonneg_right hI_card (by positivity)
  -- Take logs and unwrap!
  have hlog_in := Real.log_le_log (Real.rpow_pos_of_pos hlogN_pos _) hmain
  rw [Real.log_rpow hlogN_pos, Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity)] at hlog_in
  have hlog_ratio : -ε / (2 * (1 - ε)) - δ ≤ Real.log (Real.exp 1 * X / t₀) := by
    have hdiv := (div_le_iff₀ (by linarith : (0 : ℝ) < t₀)).mpr (by linarith :
      (-ε / 2) * LL - Real.log (2 * LL + 1) ≤ Real.log (Real.exp 1 * X / t₀) * t₀)
    have hrew : ((-ε / 2) * LL - Real.log (2 * LL + 1)) / t₀ =
        -ε / (2 * (1 - ε)) - Real.log (2 * LL + 1) / ((1 - ε) * LL) := by
      dsimp only [t₀]
      have h1ε : (1 - ε) ≠ 0 := by linarith
      field_simp [h1ε, hLL_pos.ne']
    rw [hrew] at hdiv
    linarith
  have hexp_in := Real.exp_le_exp.mpr hlog_ratio
  rw [Real.exp_log (by positivity), Real.exp_sub] at hexp_in
  have hδ_exp : Real.exp δ = ((1 - ε) * Real.exp (-ε / (2 * (1 - ε)))) / (1 - 2 * ε) :=
    Real.exp_log (by positivity)
  rw [hδ_exp] at hexp_in
  have hsimp : Real.exp (-ε / (2 * (1 - ε))) /
      (((1 - ε) * Real.exp (-ε / (2 * (1 - ε)))) / (1 - 2 * ε)) = (1 - 2 * ε) / (1 - ε) := by
    have h1 : Real.exp (-ε / (2 * (1 - ε))) ≠ 0 := (Real.exp_pos _).ne'
    have h2 : (1 - ε) ≠ 0 := by linarith
    have h3 : (1 - 2 * ε) ≠ 0 := by linarith
    field_simp [h1, h2, h3]
  rw [hsimp] at hexp_in
  have hmul := (le_div_iff₀ (by linarith : (0 : ℝ) < t₀)).mp hexp_in
  have hLHS : (1 - 2 * ε) / (1 - ε) * t₀ = (1 - 2 * ε) * LL := by
    dsimp only [t₀]
    have h2 : (1 - ε) ≠ 0 := by linarith
    field_simp [h2]
  rw [hLHS] at hmul
  have hexp_inv := mul_le_mul_of_nonneg_left hmul (Real.exp_pos (-1)).le
  have hcancel : Real.exp (-1) * (Real.exp 1 * X) = X := by
    rw [← mul_assoc, ← Real.exp_add]; simp
  linarith

/-! ## Section 3: `ppl024_lem_usingq` (Bloom's Lemma 3) -/

/-- Split any `m ≥ 1` at prime-power threshold `y ≥ 1` into `m = d * s` with `Nat.Coprime d s`,
all exact prime powers of `d` exceeding `y`, and `s ≤ y ^ (omega m)`. -/
private lemma exists_rough_smooth_split (m : ℕ) (hm : 1 ≤ m) {y : ℝ} (hy : 1 ≤ y) :
    ∃ d s : ℕ, 1 ≤ d ∧ 1 ≤ s ∧ m = d * s ∧ Nat.Coprime d s ∧
      (∀ r, ppowDiv r d → y < (r : ℝ)) ∧ (s : ℝ) ≤ y ^ (omega m) := by
  have hm0 : m ≠ 0 := by omega
  set E := exactPrimePowers m
  set E_hi : Finset ℕ := E.filter (fun r : ℕ => y < (r : ℝ))
  set E_lo : Finset ℕ := E.filter (fun r : ℕ => ¬ y < (r : ℝ))
  set d : ℕ := ∏ r ∈ E_hi, r
  set s : ℕ := ∏ r ∈ E_lo, r
  have hpos_E : ∀ r ∈ E, 0 < r := fun r hr =>
    ((ppowDiv_iff_mem_exactPrimePowers hm0).mpr hr).1.pos
  have hd1 : 1 ≤ d := Finset.one_le_prod' fun r hr => hpos_E r (Finset.mem_filter.mp hr).1
  have hs1 : 1 ≤ s := Finset.one_le_prod' fun r hr => hpos_E r (Finset.mem_filter.mp hr).1
  have hmul : m = d * s := by
    rw [← prod_exactPrimePowers hm0]
    exact (Finset.prod_filter_mul_prod_filter_not E (fun r => y < (r : ℝ)) id).symm
  have hcop_E : Set.Pairwise (E : Set ℕ) Nat.Coprime := by
    intro r₁ hr₁ r₂ hr₂ hne
    obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hr₁
    obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.mp hr₂
    have h1 := Nat.prime_of_mem_primeFactors hp₁
    have h2 := Nat.prime_of_mem_primeFactors hp₂
    have hpne : p₁ ≠ p₂ := fun h => hne (by subst h; rfl)
    exact ((Nat.coprime_primes h1 h2).mpr hpne).pow _ _
  have hcop : Nat.Coprime d s := by
    apply Nat.Coprime.prod_left
    intro r₁ hr₁
    apply Nat.Coprime.prod_right
    intro r₂ hr₂
    have hne : r₁ ≠ r₂ := by
      intro h; subst h
      exact (Finset.mem_filter.mp hr₂).2 (Finset.mem_filter.mp hr₁).2
    exact hcop_E (Finset.mem_filter.mp hr₁).1 (Finset.mem_filter.mp hr₂).1 hne
  have hrough : ∀ r, ppowDiv r d → y < (r : ℝ) := by
    intro r hr
    -- Since `d ∣ m` and `Nat.Coprime d s` with `m = d * s`, `ppowDiv r d → ppowDiv r m`
    have hd_pos : 0 < d := by omega
    have hrm : ppowDiv r m := by
      refine ⟨hr.1, dvd_trans hr.2.1 (by rw [hmul]; exact dvd_mul_right d s), ?_⟩
      have hdiv : m / r = (d / r) * s := by
        rw [hmul, Nat.mul_comm d s, Nat.mul_div_assoc s hr.2.1, Nat.mul_comm]
      rw [hdiv]
      exact hr.2.2.mul_right (Nat.Coprime.coprime_dvd_left hr.2.1 hcop)
    have hrE : r ∈ E := (ppowDiv_iff_mem_exactPrimePowers hm0).mp hrm
    by_contra hnot
    have hr_lo : r ∈ E_lo := Finset.mem_filter.mpr ⟨hrE, hnot⟩
    have hr_dvd_s : r ∣ s := Finset.dvd_prod_of_mem _ hr_lo
    have hr1 : r ∣ 1 := by
      rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd hr.2.1 hr_dvd_s
    have := hr.1.two_le
    have := Nat.le_of_dvd one_pos hr1
    omega
  have hs_le : (s : ℝ) ≤ y ^ (omega m) := by
    have h1 : (s : ℝ) ≤ y ^ E_lo.card := by
      dsimp only [s]
      rw [Nat.cast_prod]
      calc ∏ r ∈ E_lo, (r : ℝ)
          ≤ ∏ _r ∈ E_lo, y := by
            refine Finset.prod_le_prod (fun _ _ => by positivity) fun r hr => ?_
            exact le_of_not_gt (Finset.mem_filter.mp hr).2
        _ = y ^ E_lo.card := Finset.prod_const y
    have hcard : E_lo.card ≤ omega m := by
      rw [← card_exactPrimePowers]; exact Finset.card_le_card (Finset.filter_subset _ _)
    exact h1.trans (pow_le_pow_right₀ hy hcard)
  exact ⟨d, s, hd1, hs1, hmul, hcop, hrough, hs_le⟩

/-- **Bloom's Lemma 3 (`lem-usingq`, specialized for Proposition 3)**:
For all sufficiently large `N : ℕ`, for `M ∈ [N^{1/2}, N]`, `A ⊆ [M, N]` with `ω(n) ≤ 2 log log N`,
and `q ≥ 1` with `R(A; q) ≥ (log N)^{-1/2}`, there exists `d ≥ 1` coprime to `q` such that:
1. `M * N^{-2 / log log N} < q * d`,
2. `ω(d) < (1 / 500) * log log N`,
3. `R(A; q) / (log log N)^3 ≤ ∑_{n ∈ A_q, qd ∥ n} qd / n`. -/
theorem ppl024_lem_usingq :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℝ) (A : Finset ℕ) (q : ℕ),
      (N : ℝ) ^ (1 / 2 : ℝ) ≤ M → M ≤ (N : ℝ) →
      (∀ n ∈ A, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ (N : ℝ) ∧ (omega n : ℝ) ≤ 2 * Real.log (Real.log (N : ℝ))) →
      1 ≤ q → (Real.log (N : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ recSumQ A q →
      ∃ d : ℕ, 1 ≤ d ∧ Nat.Coprime q d ∧
        M * (N : ℝ) ^ (-(2 : ℝ) / Real.log (Real.log (N : ℝ))) < ((q * d : ℕ) : ℝ) ∧
        (omega d : ℝ) < (1 / 500 : ℝ) * Real.log (Real.log (N : ℝ)) ∧
        recSumQ A q / (Real.log (Real.log (N : ℝ))) ^ 3 ≤
          ∑ n ∈ (exactSlice A q).filter (fun n => q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))),
            ((q * d : ℕ) : ℝ) / (n : ℝ) := by
  obtain ⟨C_eul, hCeul_pos, hCeul⟩ := Prize.PPL024.sum_rough_k_pow_omega_div_le
  have hLL : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hk_tend : Tendsto (fun N : ℕ =>
      Real.log (Real.log (N : ℝ)) / Real.log (2 * Real.log (Real.log (N : ℝ)))) atTop atTop := by
    have h1 : Tendsto (fun u : ℝ => Real.log (2 * u) / u) atTop (𝓝 0) := by
      have ha : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
        simpa [Real.rpow_one] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      have hb := (ha.comp (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id)).const_mul 2
      rw [mul_zero] at hb
      refine hb.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      simp only [Function.comp_apply, id_eq]; field_simp [hu.ne']
    have hpos : ∀ᶠ u : ℝ in atTop, 0 < Real.log (2 * u) / u := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
      exact div_pos (Real.log_pos (by linarith)) (by linarith)
    have hinv : Tendsto (fun u : ℝ => (Real.log (2 * u) / u)⁻¹) atTop atTop :=
      Filter.Tendsto.inv_tendsto_nhdsGT_zero (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 hpos)
    exact (hinv.congr fun u => inv_div _ _).comp hLL
  have hlogN_div_LL2 : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (2 * Real.log (Real.log (N : ℝ))) ^ 2)
      atTop atTop := by
    have hexp : Tendsto (fun u : ℝ => Real.exp u / (4 * u ^ 2)) atTop atTop := by
      have h0 : Tendsto (fun u : ℝ => Real.exp u / u ^ 2) atTop atTop := by
        simpa using Real.tendsto_exp_div_pow_atTop 2
      exact (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 4) h0).congr fun u => by ring
    refine (hexp.comp hLL).congr' ?_
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    simp only [Function.comp_apply, Real.exp_log hlogpos]; ring
  have hk_div_LL : Tendsto (fun N : ℕ =>
      (Real.log (Real.log (N : ℝ)) / Real.log (2 * Real.log (Real.log (N : ℝ)))) /
        Real.log (Real.log (N : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => (Real.log (2 * u))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (Real.tendsto_log_atTop.comp (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id))
    refine (h1.comp hLL).congr' ?_
    filter_upwards [hLL.eventually_gt_atTop 1] with N hN
    simp only [Function.comp_apply]
    field_simp [(by linarith : Real.log (Real.log (N : ℝ)) ≠ 0)]
  filter_upwards [
    eventually_ge_atTop 16,
    hLL.eventually_ge_atTop (max 16 (8 * Real.exp C_eul)),
    hk_tend.eventually_ge_atTop (max 4 (Real.exp 2501)),
    hlogN_div_LL2.eventually_ge_atTop 4,
    hk_div_LL.eventually (gt_mem_nhds (by positivity : 0 < 1 / (2 * C_eul)))
  ] with N hN16 hLL_ge hk_ge hy_log_ge hk_small
  intro M A q hMN_lo hMN_hi hA hq1 hRq
  set LL : ℝ := Real.log (Real.log (N : ℝ))
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hLL_ge16 : 16 ≤ LL := le_trans (le_max_left _ _) hLL_ge
  have hLL_pos : 0 < LL := by linarith
  have hM_pos : 0 < M := lt_of_lt_of_le (Real.rpow_pos_of_pos hN_pos _) hMN_lo
  set k : ℝ := LL / Real.log (2 * LL)
  have hk_ge4 : 4 ≤ k := le_trans (le_max_left _ _) hk_ge
  have hk_pos : 0 < k := by linarith
  have hlog2LL_pos : 0 < Real.log (2 * LL) := Real.log_pos (by linarith)
  have hlogk_gt : 2501 ≤ Real.log k := by
    have h1 : Real.exp 2501 ≤ k := le_trans (le_max_right _ _) hk_ge
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 2501) h1
  set y : ℝ := Real.exp (Real.log (N : ℝ) / (2 * LL) ^ 2)
  have hy_ge16 : 16 ≤ y := by
    calc (16 : ℝ) ≤ Real.exp 4 := by
          have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          have h2 : (2 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
          rw [← Real.exp_nat_mul] at h2; norm_num at h2; linarith
      _ ≤ y := Real.exp_le_exp.mpr hy_log_ge
  have hy_le_N : y ≤ (N : ℝ) := by
    rw [← Real.exp_log hN_pos]
    apply Real.exp_le_exp.mpr
    have h1 : (1 : ℝ) ≤ (2 * LL) ^ 2 := by nlinarith
    exact div_le_self hlogN_pos.le h1
  have hlog_y : Real.log y = Real.log (N : ℝ) / (2 * LL) ^ 2 := Real.log_exp _
  have hlog_ratio : Real.log (N : ℝ) / Real.log y = (2 * LL) ^ 2 := by
    rw [hlog_y]; field_simp [hlogN_pos.ne']
  have hrpow_eq : (Real.log (N : ℝ) / Real.log y) ^ k = (Real.log (N : ℝ)) ^ 2 := by
    rw [hlog_ratio, Real.rpow_def_of_pos (by positivity)]
    have harg : Real.log ((2 * LL) ^ 2) * k = 2 * LL := by
      rw [Real.log_pow]; push_cast; dsimp only [k]; field_simp [hlog2LL_pos.ne']
    rw [harg, show (2 : ℝ) * LL = ((2 : ℕ) : ℝ) * Real.log (Real.log (N : ℝ)) by dsimp only [LL]; norm_num,
      Real.exp_nat_mul, Real.exp_log hlogN_pos]
  -- Define `D`: coprime rough divisors `d ∈ Icc 1 N` with `M * N^{-1 / (2 LL)} ≤ q * d`
  set D : Finset ℕ := (Finset.Icc 1 N).filter fun d =>
    Nat.Coprime q d ∧ (∀ r, ppowDiv r d → y < (r : ℝ)) ∧
      M * (N : ℝ) ^ (-(1 : ℝ) / (2 * LL)) ≤ ((q * d : ℕ) : ℝ)
  -- Every `n ∈ exactSlice A q` is divisible by some `q * d` (`d ∈ D`) with `Coprime (q * d) (n / (q * d))`
  have hcover : ∀ n ∈ exactSlice A q, ∃ d ∈ D, q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)) := by
    intro n hn
    obtain ⟨hnA, hqn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hMn, hnN, hωn⟩ := hA n hnA
    have hn_pos : 0 < n := by
      have : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hM_pos hMn
      exact_mod_cast this
    set m : ℕ := n / q
    have hqm : q * m = n := Nat.mul_div_cancel' hqn.2.1
    have hm1 : 1 ≤ m := by
      by_contra h0
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos (by omega)
      rw [hm0, mul_zero] at hqm; omega
    obtain ⟨d, s, hd1, hs1, hmds, hcop_ds, hrough, hs_le⟩ :=
      exists_rough_smooth_split m hm1 (y := y) (by linarith)
    have hcop_qd : Nat.Coprime q d := Nat.Coprime.coprime_dvd_right (show d ∣ m by rw [hmds]; exact dvd_mul_right d s) hqn.2.2
    have hcop_qs : Nat.Coprime q s := Nat.Coprime.coprime_dvd_right (show s ∣ m by rw [hmds]; exact dvd_mul_left s d) hqn.2.2
    have hqd_dvd : q * d ∣ n := ⟨s, by rw [← hqm, hmds]; ring⟩
    have hdiv_eq : n / (q * d) = s := by
      have hne : 0 < q * d := Nat.mul_pos (by omega) (by omega)
      have hmul' : n = (q * d) * s := by rw [← hqm, hmds]; ring
      rw [hmul', Nat.mul_div_cancel_left s hne]
    have hcop_all : Nat.Coprime (q * d) (n / (q * d)) := by
      rw [hdiv_eq]; exact hcop_qs.mul_left hcop_ds
    have hd_le_N : d ≤ N := by
      have : d ≤ n := Nat.le_of_dvd hn_pos (dvd_trans (dvd_mul_left d q) hqd_dvd)
      exact this.trans (by exact_mod_cast hnN)
    have hs_bound : (s : ℝ) ≤ (N : ℝ) ^ (1 / (2 * LL)) := by
      have hωm : (omega m : ℝ) ≤ 2 * LL := by
        have hsub : m.primeFactors ⊆ n.primeFactors := by
          intro p hp
          have hp' := Nat.mem_primeFactors.mp hp
          exact Nat.mem_primeFactors.mpr ⟨hp'.1, dvd_trans hp'.2.1 (by rw [← hqm]; exact dvd_mul_left m q), hn_pos.ne'⟩
        exact ((by exact_mod_cast Finset.card_le_card hsub) : (omega m : ℝ) ≤ (omega n : ℝ)).trans hωn
      calc (s : ℝ) ≤ y ^ (omega m) := hs_le
        _ = y ^ ((omega m : ℝ)) := (Real.rpow_natCast y _).symm
        _ ≤ y ^ (2 * LL) := Real.rpow_le_rpow_of_exponent_le (by linarith) hωm
        _ = (N : ℝ) ^ (1 / (2 * LL)) := by
            rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hN_pos, hlog_y]
            congr 1; field_simp [hLL_pos.ne']
    have hqd_lo : M * (N : ℝ) ^ (-(1 : ℝ) / (2 * LL)) ≤ ((q * d : ℕ) : ℝ) := by
      have hns : (n : ℝ) = ((q * d : ℕ) : ℝ) * (s : ℝ) := by
        have : n = (q * d) * s := by rw [← hqm, hmds]; ring
        exact_mod_cast this
      have hinv : (N : ℝ) ^ (-(1 : ℝ) / (2 * LL)) = ((N : ℝ) ^ (1 / (2 * LL)))⁻¹ := by
        rw [neg_div, Real.rpow_neg hN_pos.le]
      rw [hinv]
      have hs_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr hs1
      calc M * ((N : ℝ) ^ (1 / (2 * LL)))⁻¹
          ≤ (n : ℝ) * (s : ℝ)⁻¹ :=
            mul_le_mul hMn (inv_anti₀ hs_pos hs_bound) (by positivity) (by linarith)
        _ = ((q * d : ℕ) : ℝ) := by rw [hns]; field_simp [hs_pos.ne']
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, hd_le_N⟩, hcop_qd, hrough, hqd_lo⟩,
      hqd_dvd, hcop_all⟩
  set sliceSum : ℕ → ℝ := fun d =>
    ∑ n ∈ (exactSlice A q).filter (fun n => q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))),
      ((q * d : ℕ) : ℝ) / (n : ℝ)
  have hRq_le : recSumQ A q ≤ ∑ d ∈ D, (1 : ℝ) / (d : ℝ) * sliceSum d := by
    have hterm_eq : ∀ d ∈ D, (1 : ℝ) / (d : ℝ) * sliceSum d =
        ∑ n ∈ (exactSlice A q).filter (fun n => q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))),
          (q : ℝ) / (n : ℝ) := by
      intro d hd
      have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
      dsimp only [sliceSum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Nat.cast_mul]; field_simp [hd_pos.ne']
    rw [Finset.sum_congr rfl hterm_eq]
    -- Every `n ∈ exactSlice A q` appears in at least one `d ∈ D`
    calc recSumQ A q
        = ∑ n ∈ exactSlice A q, (q : ℝ) / (n : ℝ) := rfl
      _ ≤ ∑ n ∈ exactSlice A q, ∑ d ∈ D.filter (fun d => q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))),
            (q : ℝ) / (n : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          obtain ⟨d, hd, h1, h2⟩ := hcover n hn
          exact Finset.single_le_sum (f := fun _ : ℕ => (q : ℝ) / (n : ℝ))
            (fun _ _ => by positivity) (Finset.mem_filter.mpr ⟨hd, h1, h2⟩)
      _ = ∑ d ∈ D, ∑ n ∈ (exactSlice A q).filter (fun n => q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))),
            (q : ℝ) / (n : ℝ) := by
          simp_rw [Finset.sum_filter]
          exact Finset.sum_comm
  -- Split `D` at `ω₀ = (5 / log k) * LL`
  set ω₀ : ℝ := (5 / Real.log k) * LL
  have hω₀_lt : ω₀ < (1 / 500 : ℝ) * LL := by
    dsimp only [ω₀]
    have h1 : 5 / Real.log k < 1 / 500 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
    exact mul_lt_mul_of_pos_right h1 hLL_pos
  set D_hi := D.filter (fun d => ω₀ ≤ (omega d : ℝ))
  set D_lo := D.filter (fun d => ¬ ω₀ ≤ (omega d : ℝ))
  have hD_prop : ∀ d ∈ D, 1 ≤ d ∧ d ≤ N ∧ ∀ r, ppowDiv r d → y < (r : ℝ) := fun d hd =>
    ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1,
     (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2,
     (Finset.mem_filter.mp hd).2.2.1⟩
  have hslice_triv : ∀ d ∈ D, sliceSum d ≤ 2 * Real.log (N : ℝ) := by
    intro d hd
    have hqd_pos : 0 < q * d := Nat.mul_pos (by omega) (hD_prop d hd).1
    set S := (exactSlice A q).filter (fun n => q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))
    have hinj : Set.InjOn (fun n => n / (q * d)) (S : Set ℕ) := by
      intro n₁ hn₁ n₂ hn₂ heq
      dsimp only at heq
      have h1 := (Finset.mem_filter.mp hn₁).2.1
      have h2 := (Finset.mem_filter.mp hn₂).2.1
      rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
    have hmaps : ∀ n ∈ S, n / (q * d) ∈ Finset.Icc 1 N := by
      intro n hn
      have hnA := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
      have hdvd := (Finset.mem_filter.mp hn).2.1
      have hn_pos : 0 < n := by
        have : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hM_pos (hA n hnA).1
        exact_mod_cast this
      have hnN : n ≤ N := by exact_mod_cast (hA n hnA).2.1
      exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn_pos hdvd) hqd_pos,
        (Nat.div_le_self n (q * d)).trans hnN⟩
    calc sliceSum d
        = ∑ n ∈ S, (1 : ℝ) / ((n / (q * d) : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          have hdvd := (Finset.mem_filter.mp hn).2.1
          have hmul_eq : n = (q * d) * (n / (q * d)) := (Nat.mul_div_cancel' hdvd).symm
          have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (hD_prop d hd).1; omega)
          conv_lhs => rw [hmul_eq]
          push_cast
          field_simp [hq0, hd0]
      _ = ∑ m ∈ S.image (fun n => n / (q * d)), (1 : ℝ) / (m : ℝ) :=
          (Finset.sum_image (f := fun m : ℕ => (1 : ℝ) / (m : ℝ)) hinj).symm
      _ ≤ ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps) fun _ _ _ => by positivity
      _ ≤ Real.log (N : ℝ) + 1 := Prize.PPL024.harmonic_le_log_add_one (by omega)
      _ ≤ 2 * Real.log (N : ℝ) := by
          have : (1 : ℝ) ≤ Real.log (N : ℝ) := by
            have h3N : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 3 ≤ N)
            have h1 := Real.log_le_log (by norm_num : (0 : ℝ) < 3) h3N
            have h2 : (1 : ℝ) ≤ Real.log 3 := by
              rw [← Real.log_exp 1]
              exact Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_d9.le.trans (by norm_num))
            linarith
          linarith
  -- Bound the tail `D_hi` via Rankin's trick + `sum_rough_k_pow_omega_div_le`
  have htail_le : ∑ d ∈ D_hi, (1 : ℝ) / (d : ℝ) * sliceSum d ≤ (1 / 2 : ℝ) * recSumQ A q := by
    have hrankin : ∑ d ∈ D_hi, (1 : ℝ) / (d : ℝ) ≤ k ^ (-ω₀) * ∑ d ∈ D_hi, k ^ (omega d) / (d : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun d hd => ?_
      have hωd : ω₀ ≤ (omega d : ℝ) := (Finset.mem_filter.mp hd).2
      have h1 : (1 : ℝ) ≤ k ^ (-ω₀) * k ^ (omega d) := by
        rw [← Real.rpow_natCast k (omega d), ← Real.rpow_add hk_pos]
        exact Real.one_le_rpow (by linarith) (by linarith)
      calc (1 : ℝ) / (d : ℝ) = 1 * ((1 : ℝ) / (d : ℝ)) := (one_mul _).symm
        _ ≤ (k ^ (-ω₀) * k ^ (omega d)) * ((1 : ℝ) / (d : ℝ)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = k ^ (-ω₀) * (k ^ (omega d) / (d : ℝ)) := by ring
    have heul_k : ∑ d ∈ D_hi, k ^ (omega d) / (d : ℝ) ≤ Real.exp (C_eul * k) * (Real.log (N : ℝ)) ^ 2 := by
      rw [← hrpow_eq]
      exact hCeul y hy_ge16 N hy_le_N k (by linarith) D_hi fun d hd =>
        hD_prop d (Finset.mem_filter.mp hd).1
    have hk_neg_ω₀ : k ^ (-ω₀) = (Real.log (N : ℝ)) ^ (-(5 : ℝ)) := by
      rw [Real.rpow_def_of_pos hk_pos, Real.rpow_def_of_pos hlogN_pos]
      congr 1; dsimp only [ω₀, LL]
      have hne : Real.log k ≠ 0 := by linarith
      field_simp [hne]
    have hexp_Ck_le : Real.exp (C_eul * k) ≤ Real.log (N : ℝ) := by
      rw [← Real.exp_log hlogN_pos]
      apply Real.exp_le_exp.mpr
      have h1 := (div_lt_iff₀ hLL_pos).mp hk_small
      have h2 := mul_le_mul_of_nonneg_left h1.le hCeul_pos.le
      have h3 : C_eul * (1 / (2 * C_eul) * LL) = LL / 2 := by field_simp [hCeul_pos.ne']
      linarith
    have hlogN_ge16 : 16 ≤ Real.log (N : ℝ) := by
      have h1 : (4 : ℝ) ≤ Real.log (N : ℝ) / (2 * LL) ^ 2 := hy_log_ge
      have h2 : (16 : ℝ) ≤ (2 * LL) ^ 2 := by nlinarith
      have h3 := (le_div_iff₀ (by positivity : (0 : ℝ) < (2 * LL) ^ 2)).mp h1
      nlinarith
    have hsum_hi : ∑ d ∈ D_hi, (1 : ℝ) / (d : ℝ) ≤ (Real.log (N : ℝ)) ^ (-(2 : ℝ)) := by
      calc ∑ d ∈ D_hi, (1 : ℝ) / (d : ℝ)
          ≤ (Real.log (N : ℝ)) ^ (-(5 : ℝ)) * (Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ 2) := by
            rw [← hk_neg_ω₀]
            exact hrankin.trans (mul_le_mul_of_nonneg_left
              (heul_k.trans (mul_le_mul_of_nonneg_right hexp_Ck_le (by positivity))) (by positivity))
        _ = (Real.log (N : ℝ)) ^ (-(2 : ℝ)) := by
            have hpow3 : Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ 2 = (Real.log (N : ℝ)) ^ (3 : ℝ) := by
              rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
            rw [hpow3, ← Real.rpow_add hlogN_pos]; norm_num
    calc ∑ d ∈ D_hi, (1 : ℝ) / (d : ℝ) * sliceSum d
        ≤ ∑ d ∈ D_hi, (1 : ℝ) / (d : ℝ) * (2 * Real.log (N : ℝ)) :=
          Finset.sum_le_sum fun d hd =>
            mul_le_mul_of_nonneg_left (hslice_triv d (Finset.mem_filter.mp hd).1) (by positivity)
      _ = (∑ d ∈ D_hi, (1 : ℝ) / (d : ℝ)) * (2 * Real.log (N : ℝ)) := (Finset.sum_mul _ _ _).symm
      _ ≤ (Real.log (N : ℝ)) ^ (-(2 : ℝ)) * (2 * Real.log (N : ℝ)) :=
          mul_le_mul_of_nonneg_right hsum_hi (by positivity)
      _ = 2 / Real.log (N : ℝ) := by
          rw [Real.rpow_neg hlogN_pos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          field_simp [hlogN_pos.ne']
      _ ≤ (1 / 2 : ℝ) * (Real.log (N : ℝ)) ^ (-(1 / 2 : ℝ)) := by
          rw [Real.rpow_neg hlogN_pos.le, ← one_div, mul_one_div,
            div_le_div_iff₀ hlogN_pos (by positivity)]
          have hsqrt : (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) ≤ Real.log (N : ℝ) / 4 := by
            have hsq : ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 = Real.log (N : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hlogN_pos.le]; norm_num
            nlinarith [Real.rpow_nonneg hlogN_pos.le (1 / 2 : ℝ)]
          nlinarith
      _ ≤ (1 / 2 : ℝ) * recSumQ A q := mul_le_mul_of_nonneg_left hRq (by norm_num)
  -- Therefore the main part `D_lo` contributes at least `(1/2) * recSumQ A q`
  have hlo_ge : (1 / 2 : ℝ) * recSumQ A q ≤ ∑ d ∈ D_lo, (1 : ℝ) / (d : ℝ) * sliceSum d := by
    have hsplit : ∑ d ∈ D, (1 : ℝ) / (d : ℝ) * sliceSum d =
        (∑ d ∈ D_hi, (1 : ℝ) / (d : ℝ) * sliceSum d) +
        ∑ d ∈ D_lo, (1 : ℝ) / (d : ℝ) * sliceSum d :=
      (Finset.sum_filter_add_sum_filter_not D (fun d => ω₀ ≤ (omega d : ℝ)) _).symm
    linarith
  -- Bound `∑ d ∈ D_lo, 1/d ≤ (1/2) * LL^3` via `sum_rough_k_pow_omega_div_le` with `k = 1`
  have hDlo_sum : ∑ d ∈ D_lo, (1 : ℝ) / (d : ℝ) ≤ (1 / 2 : ℝ) * LL ^ 3 := by
    have h1 := hCeul y hy_ge16 N hy_le_N 1 le_rfl D_lo fun d hd =>
      hD_prop d (Finset.mem_filter.mp hd).1
    simp only [one_pow, mul_one, Real.rpow_one] at h1
    rw [hlog_ratio] at h1
    have h8exp : 8 * Real.exp C_eul ≤ LL := le_trans (le_max_right _ _) hLL_ge
    nlinarith
  -- Pigeonhole on `d ∈ D_lo`!
  have hex_d : ∃ d ∈ D_lo, recSumQ A q / LL ^ 3 ≤ sliceSum d := by
    by_contra hlt_all
    push Not at hlt_all
    have hne : D_lo.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.sum_empty] at hlo_ge
      linarith [Real.rpow_pos_of_pos hlogN_pos (-(1 / 2 : ℝ))]
    have hsum_lt : ∑ d ∈ D_lo, (1 : ℝ) / (d : ℝ) * sliceSum d <
        (∑ d ∈ D_lo, (1 : ℝ) / (d : ℝ)) * (recSumQ A q / LL ^ 3) := by
      rw [Finset.sum_mul]
      refine Finset.sum_lt_sum_of_nonempty hne fun d hd => ?_
      have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (hD_prop d (Finset.mem_filter.mp hd).1).1
      exact mul_lt_mul_of_pos_left (hlt_all d hd) (one_div_pos.mpr hd_pos)
    have hupper : (∑ d ∈ D_lo, (1 : ℝ) / (d : ℝ)) * (recSumQ A q / LL ^ 3) ≤ (1 / 2 : ℝ) * recSumQ A q := by
      have hRq_pos : 0 < recSumQ A q := lt_of_lt_of_le (Real.rpow_pos_of_pos hlogN_pos _) hRq
      calc (∑ d ∈ D_lo, (1 : ℝ) / (d : ℝ)) * (recSumQ A q / LL ^ 3)
          ≤ ((1 / 2 : ℝ) * LL ^ 3) * (recSumQ A q / LL ^ 3) :=
            mul_le_mul_of_nonneg_right hDlo_sum (by positivity)
        _ = (1 / 2 : ℝ) * recSumQ A q := by field_simp [hLL_pos.ne']
    linarith
  obtain ⟨d, hd_lo, hslice_ge⟩ := hex_d
  have hd_D := (Finset.mem_filter.mp hd_lo).1
  have hωd_lt : (omega d : ℝ) < ω₀ := lt_of_not_ge (Finset.mem_filter.mp hd_lo).2
  have hqd_strict : M * (N : ℝ) ^ (-(2 : ℝ) / LL) < ((q * d : ℕ) : ℝ) := by
    have hlt_exp : -(2 : ℝ) / LL < -(1 : ℝ) / (2 * LL) := by
      rw [div_lt_div_iff₀ hLL_pos (by positivity)]; nlinarith
    have hlt_rpow : (N : ℝ) ^ (-(2 : ℝ) / LL) < (N : ℝ) ^ (-(1 : ℝ) / (2 * LL)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < N)) hlt_exp
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hlt_rpow hM_pos) (Finset.mem_filter.mp hd_D).2.2.2
  exact ⟨d, (hD_prop d hd_D).1, (Finset.mem_filter.mp hd_D).2.1, hqd_strict,
    lt_trans hωd_lt hω₀_lt, hslice_ge⟩

/-! ## Section 4: `ppl024_lem_pisqa` & `ppl024_lem_pisq` (Bloom's Lemmas 6–7) -/

/-- Greedy prime-power pruning engine: given `A` (`0 ∉ A`) and threshold `τ ≥ 0`,
there exists `B ⊆ A` such that `R(B; q) ≥ τ` for all `q ∈ 𝒬_B` and
`R(A) - R(B) ≤ τ * ∑_{q ∈ 𝒬_A \ 𝒬_B} 1/q`. -/
private lemma greedy_prune_exact (A : Finset ℕ) (h0 : 0 ∉ A) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ B : Finset ℕ, B ⊆ A ∧
      (∀ q ∈ ppowersInSet B, τ ≤ recSumQ B q) ∧
      recSumReal A - recSumReal B ≤ τ * ∑ q ∈ ppowersInSet A \ ppowersInSet B, (1 : ℝ) / (q : ℝ) := by
  induction hn : A.card using Nat.strong_induction_on generalizing A with
  | _ k ih =>
    by_cases hgood : ∀ q ∈ ppowersInSet A, τ ≤ recSumQ A q
    · exact ⟨A, Finset.Subset.rfl, hgood, by simp⟩
    · push Not at hgood
      obtain ⟨q, hqA, hq_lt⟩ := hgood
      set A' := A \ exactSlice A q
      have hne_sl : (exactSlice A q).Nonempty := (mem_ppowersInSet_iff h0).mp hqA
      have hsl_sub : exactSlice A q ⊆ A := Finset.filter_subset _ _
      have hcard_lt : A'.card < k := by
        rw [← hn]
        have h1 : A'.card = A.card - (exactSlice A q).card := by
          dsimp only [A']; rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsl_sub]
        have h2 : 0 < (exactSlice A q).card := Finset.card_pos.mpr hne_sl
        have h3 : (exactSlice A q).card ≤ A.card := Finset.card_le_card hsl_sub
        omega
      have h0' : 0 ∉ A' := fun h => h0 (Finset.sdiff_subset h)
      obtain ⟨B, hBA', hBgood, hBloss⟩ := ih A'.card hcard_lt A' h0' rfl
      have hBA : B ⊆ A := hBA'.trans Finset.sdiff_subset
      have hq_not_A' : q ∉ ppowersInSet A' := by
        rw [mem_ppowersInSet_iff h0', Finset.not_nonempty_iff_eq_empty]
        ext n
        simp only [exactSlice, A', Finset.mem_filter, Finset.mem_sdiff, Finset.notMem_empty, iff_false]
        rintro ⟨⟨hnA, hnot⟩, hqn⟩
        exact hnot ⟨hnA, hqn⟩
      have hq_not_B : q ∉ ppowersInSet B := fun h => hq_not_A' (ppowersInSet_mono hBA' h)
      have hq_ne0 : q ≠ 0 := (mem_ppowersInSet_pos h0 hqA).ne'
      have hstep_loss : recSumReal A - recSumReal A' ≤ τ * ((1 : ℝ) / (q : ℝ)) := by
        have h1 : recSumReal A' = recSumReal A - recSumReal (exactSlice A q) := recSumReal_sdiff hsl_sub
        have h2 : recSumReal (exactSlice A q) = (1 / (q : ℝ)) * recSumQ A q :=
          (inv_mul_recSumQ_eq A hq_ne0).symm
        have h3 : (1 / (q : ℝ)) * recSumQ A q ≤ (1 / (q : ℝ)) * τ :=
          mul_le_mul_of_nonneg_left hq_lt.le (by positivity)
        linarith
      have hsub_sdiff : insert q (ppowersInSet A' \ ppowersInSet B) ⊆ ppowersInSet A \ ppowersInSet B := by
        intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr'
        · exact Finset.mem_sdiff.mpr ⟨hqA, hq_not_B⟩
        · have h1 := Finset.mem_sdiff.mp hr'
          exact Finset.mem_sdiff.mpr ⟨ppowersInSet_mono Finset.sdiff_subset h1.1, h1.2⟩
      have hq_not_mem : q ∉ ppowersInSet A' \ ppowersInSet B := fun h =>
        hq_not_A' (Finset.mem_sdiff.mp h).1
      have hsum_inc : (1 : ℝ) / (q : ℝ) + ∑ r ∈ ppowersInSet A' \ ppowersInSet B, (1 : ℝ) / (r : ℝ) ≤
          ∑ r ∈ ppowersInSet A \ ppowersInSet B, (1 : ℝ) / (r : ℝ) := by
        rw [← Finset.sum_insert (f := fun r : ℕ => (1 : ℝ) / (r : ℝ)) hq_not_mem]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub_sdiff fun _ _ _ => by positivity
      refine ⟨B, hBA, hBgood, ?_⟩
      have hmul_inc := mul_le_mul_of_nonneg_left hsum_inc hτ
      linarith

/-- **Bloom's Lemma 6 (`lem-pisqa`)**:
For sufficiently large `N` and any `A ⊆ [1, N]`, there exists `B ⊆ A` with
`R(B) ≥ R(A) - (log N)^{-1/200}` and `R(B; q) ≥ 2 / (log N)^{1/100}` for all `q ∈ 𝒬_B`. -/
theorem ppl024_lem_pisqa :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, (∀ n ∈ A, 1 ≤ n ∧ n ≤ N) →
      ∃ B : Finset ℕ, B ⊆ A ∧
        recSumReal A - (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) ≤ recSumReal B ∧
        ∀ q ∈ ppowersInSet B, 2 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ recSumQ B q := by
  obtain ⟨C_pp, hCpp_pos, hCpp⟩ := Prize.PPL024.sum_inv_ppow_le
  have htend : Tendsto (fun N : ℕ =>
      (Real.log (Real.log (N : ℝ)) + C_pp) / (Real.log (N : ℝ)) ^ (1 / 200 : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => (Real.log u + C_pp) / u ^ (1 / 200 : ℝ)) atTop (𝓝 0) := by
      have ha : Tendsto (fun u : ℝ => Real.log u / u ^ (1 / 200 : ℝ)) atTop (𝓝 0) := by
        have hexp : Tendsto (fun v : ℝ => 200 * (v / Real.exp v)) atTop (𝓝 0) := by
          have h0 : Tendsto (fun v : ℝ => Real.exp v / v) atTop atTop := by
            simpa using Real.tendsto_exp_div_pow_atTop 1
          simpa [inv_div] using (tendsto_inv_atTop_zero.comp h0).const_mul 200
        refine (hexp.comp (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 200)
          Real.tendsto_log_atTop)).congr' ?_
        filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
        simp only [Function.comp_apply]
        rw [Real.rpow_def_of_pos (by linarith), mul_comm (Real.log u)]; ring
      have hb : Tendsto (fun u : ℝ => C_pp / u ^ (1 / 200 : ℝ)) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200))).const_mul C_pp
      have hs := ha.add hb; rw [add_zero] at hs
      exact hs.congr fun u => by ring
    exact h1.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [
    eventually_ge_atTop 3,
    htend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  ] with N hN3 hsmall
  intro A hA
  have h0 : 0 ∉ A := fun h => by linarith [(hA 0 h).1]
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  set τ : ℝ := 2 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ)
  obtain ⟨B, hBA, hBgood, hBloss⟩ := greedy_prune_exact A h0 (by positivity : 0 ≤ τ)
  refine ⟨B, hBA, ?_, hBgood⟩
  have hsub : ppowersInSet A \ ppowersInSet B ⊆ (Finset.Icc 1 N).filter IsPrimePow := by
    intro q hq
    have hqA := (Finset.mem_sdiff.mp hq).1
    exact Finset.mem_filter.mpr ⟨ppowersInSet_subset_Icc hA hqA, mem_ppowersInSet_isPrimePow h0 hqA⟩
  have hsum_le : ∑ q ∈ ppowersInSet A \ ppowersInSet B, (1 : ℝ) / (q : ℝ) ≤
      Real.log (Real.log (N : ℝ)) + C_pp :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans (hCpp N hN3)
  have h2le : 2 * (Real.log (Real.log (N : ℝ)) + C_pp) ≤ (Real.log (N : ℝ)) ^ (1 / 200 : ℝ) := by
    have h1 := (div_lt_iff₀ (Real.rpow_pos_of_pos hlogN_pos _)).mp hsmall
    linarith
  have htau_le : τ * (Real.log (Real.log (N : ℝ)) + C_pp) ≤ (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) := by
    dsimp only [τ]
    have hpow_split : (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) =
        (Real.log (N : ℝ)) ^ (1 / 200 : ℝ) * (Real.log (N : ℝ)) ^ (1 / 200 : ℝ) := by
      rw [← Real.rpow_add hlogN_pos]; congr 1; norm_num
    rw [Real.rpow_neg hlogN_pos.le, ← one_div, hpow_split]
    have hp : 0 < (Real.log (N : ℝ)) ^ (1 / 200 : ℝ) := Real.rpow_pos_of_pos hlogN_pos _
    calc 2 / ((Real.log (N : ℝ)) ^ (1 / 200 : ℝ) * (Real.log (N : ℝ)) ^ (1 / 200 : ℝ)) *
          (Real.log (Real.log (N : ℝ)) + C_pp)
        = (2 * (Real.log (Real.log (N : ℝ)) + C_pp)) /
            ((Real.log (N : ℝ)) ^ (1 / 200 : ℝ) * (Real.log (N : ℝ)) ^ (1 / 200 : ℝ)) := by ring
      _ ≤ (Real.log (N : ℝ)) ^ (1 / 200 : ℝ) /
            ((Real.log (N : ℝ)) ^ (1 / 200 : ℝ) * (Real.log (N : ℝ)) ^ (1 / 200 : ℝ)) := by gcongr
      _ = 1 / (Real.log (N : ℝ)) ^ (1 / 200 : ℝ) := by field_simp [hp.ne']
  have hloss : recSumReal A - recSumReal B ≤ (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) :=
    hBloss.trans ((mul_le_mul_of_nonneg_left hsum_le (by positivity)).trans htau_le)
  linarith

/-- **Bloom's Lemma 7 (`lem-pisq`)**:
For sufficiently large `N`, `M ∈ [N^{1/2}, N]`, `α > 2 (log N)^{-1/200}`, and `A ⊆ [M, N]`
with `R(A) ≥ α + (log N)^{-1/200}` and `q ≤ M / (log N)^{1/100}` for all `q ∈ 𝒬_A`,
there exists `B ⊆ A` with `R(B) ∈ [α - 1/M, α)` and `R(B; q) ≥ 1 / (log N)^{1/100}` for all `q ∈ 𝒬_B`. -/
theorem ppl024_lem_pisq :
    ∀ᶠ N : ℕ in atTop, ∀ (M α : ℝ) (A : Finset ℕ),
      (N : ℝ) ^ (1 / 2 : ℝ) ≤ M → M ≤ (N : ℝ) →
      2 * (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) < α →
      (∀ n ∈ A, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ (N : ℝ)) →
      α + (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) ≤ recSumReal A →
      (∀ q ∈ ppowersInSet A, (q : ℝ) ≤ M / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ)) →
      ∃ B : Finset ℕ, B ⊆ A ∧
        α - 1 / M ≤ recSumReal B ∧ recSumReal B < α ∧
        ∀ q ∈ ppowersInSet B, 1 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ recSumQ B q := by
  filter_upwards [ppl024_lem_pisqa, eventually_ge_atTop 4] with N hpisqa hN4
  intro M α A hMN_lo hMN_hi hα hA hRA hq_le
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hM_ge2 : 2 ≤ M := by
    have h1 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      have h4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
      have := Real.rpow_le_rpow (by norm_num) h4 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)] at this
      norm_num at this; exact this
    linarith
  have hM_pos : 0 < M := by linarith
  have hA_icc : ∀ n ∈ A, 1 ≤ n ∧ n ≤ N := fun n hn =>
    ⟨by exact_mod_cast (by linarith [(hA n hn).1] : (1 : ℝ) ≤ (n : ℝ)),
     by exact_mod_cast (hA n hn).2⟩
  -- Step 1: initial pruning to `A'` with `R(A') ≥ α` and `R(A'; q) ≥ 2 / (log N)^{1/100}`
  obtain ⟨A', hA'A, hRA', hA'q⟩ := hpisqa A hA_icc
  have hRA'_ge : α ≤ recSumReal A' := by linarith
  -- Step 2: inductively remove one element at a time while preserving `R(D; q) ≥ 1 / (log N)^{1/100}`
  suffices hstep : ∀ D : Finset ℕ, D ⊆ A → α ≤ recSumReal D →
      (∀ q ∈ ppowersInSet D, 1 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ recSumQ D q) →
      ∃ B : Finset ℕ, B ⊆ D ∧ α - 1 / M ≤ recSumReal B ∧ recSumReal B < α ∧
        ∀ q ∈ ppowersInSet B, 1 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ recSumQ B q by
    obtain ⟨B, hBA', hB1, hB2, hB3⟩ := hstep A' hA'A hRA'_ge fun q hq => by
      have h1 := hA'q q hq
      have hp : 0 < (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) := Real.rpow_pos_of_pos hlogN_pos _
      have : 1 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ 2 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) := by
        gcongr; norm_num
      linarith
    exact ⟨B, hBA'.trans hA'A, hB1, hB2, hB3⟩
  intro D
  induction hn : D.card using Nat.strong_induction_on generalizing D with
  | _ k ih =>
    intro hDA hRD hDq
    -- Apply `hpisqa` to `D` to get a nonempty subset `E ⊆ D` with `R(E; q) ≥ 2 / (log N)^{1/100}`
    obtain ⟨E, hED, hRE, hEq⟩ := hpisqa D fun n hn => hA_icc n (hDA hn)
    have hE_ne : E.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty.mp hemp, recSumReal_empty] at hRE
      have hp := Real.rpow_pos_of_pos hlogN_pos (-(1 / 200 : ℝ))
      linarith
    obtain ⟨x, hxE⟩ := hE_ne
    have hxD : x ∈ D := hED hxE
    have hxA : x ∈ A := hDA hxD
    set D' := D.erase x
    have hD'D : D' ⊆ D := Finset.erase_subset x D
    have hD'q : ∀ q ∈ ppowersInSet D', 1 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) ≤ recSumQ D' q := by
      intro q hqD'
      have hqD : q ∈ ppowersInSet D := ppowersInSet_mono hD'D hqD'
      have hqA : q ∈ ppowersInSet A := ppowersInSet_mono hDA hqD
      by_cases hx_sl : x ∈ exactSlice D q
      · have hqE : q ∈ ppowersInSet E := by
          have h0E : 0 ∉ E := fun h => by linarith [(hA_icc 0 (hDA (hED h))).1]
          rw [mem_ppowersInSet_iff h0E]
          exact ⟨x, Finset.mem_filter.mpr ⟨hxE, (Finset.mem_filter.mp hx_sl).2⟩⟩
        have hEq_ge := hEq q hqE
        have hdiff : recSumQ D' q = recSumQ D q - (q : ℝ) / (x : ℝ) := by
          have heq_sl : exactSlice D' q = (exactSlice D q).erase x := by
            ext n; simp only [exactSlice, D', Finset.mem_filter, Finset.mem_erase]; tauto
          unfold recSumQ
          rw [heq_sl, Finset.sum_erase_eq_sub hx_sl]
        have hq_div_x : (q : ℝ) / (x : ℝ) ≤ 1 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) := by
          have hxM : M ≤ (x : ℝ) := (hA x hxA).1
          have hqM := hq_le q hqA
          calc (q : ℝ) / (x : ℝ) ≤ (q : ℝ) / M := div_le_div_of_nonneg_left (by positivity) hM_pos hxM
            _ ≤ (M / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ)) / M := div_le_div_of_nonneg_right hqM hM_pos.le
            _ = 1 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) := by field_simp [hM_pos.ne']
        have hmono : recSumQ E q ≤ recSumQ D q := recSumQ_mono hED q
        have h21 : 2 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ) = 2 * (1 / (Real.log (N : ℝ)) ^ (1 / 100 : ℝ)) := by ring
        linarith
      · have heq_sl : exactSlice D' q = exactSlice D q := by
          ext n
          simp only [exactSlice, D', Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨⟨_, hnD⟩, hqn⟩; exact ⟨hnD, hqn⟩
          · rintro ⟨hnD, hqn⟩
            refine ⟨⟨?_, hnD⟩, hqn⟩
            rintro rfl
            exact hx_sl (Finset.mem_filter.mpr ⟨hnD, hqn⟩)
        change recSumQ D' q ≥ _
        unfold recSumQ
        rw [heq_sl]
        exact hDq q hqD
    have hRD' : recSumReal D' = recSumReal D - (1 : ℝ) / (x : ℝ) := by
      unfold recSumReal D'
      exact Finset.sum_erase_eq_sub hxD
    have hx_inv : (1 : ℝ) / (x : ℝ) ≤ 1 / M :=
      one_div_le_one_div_of_le hM_pos (hA x hxA).1
    by_cases hlt : recSumReal D' < α
    · exact ⟨D', hD'D, by linarith, hlt, hD'q⟩
    · push Not at hlt
      have hcard_lt : D'.card < k := by
        rw [← hn]; exact Finset.card_erase_lt_of_mem hxD
      obtain ⟨B, hBD', hB1, hB2, hB3⟩ := ih D'.card hcard_lt D' rfl (hD'D.trans hDA) hlt hD'q
      exact ⟨B, hBD'.trans hD'D, hB1, hB2, hB3⟩

end PPL024
