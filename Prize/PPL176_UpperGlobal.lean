import Prize.PPL176_UpperBinPack
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt

open scoped BigOperators Nat

namespace PPL176

/-! ## Dirichlet-Jensen Consecutive-Block Bound and Unconditional Global `O(n √(log n))` Bound -/

/-- Elementary identity: `B ^ v = 1 + (B - 1) * ∑_{k=1}^v B^(k-1)` in `ℝ`. -/
lemma real_pow_eq_one_add_geom (B : ℕ) (v : ℕ) :
    ((B : ℝ) ^ v) = 1 + ((B : ℝ) - 1) * ∑ k ∈ Finset.Icc 1 v, (B : ℝ) ^ (k - 1) := by
  induction v with
  | zero => simp
  | succ v ih =>
    have hIcc : Finset.Icc 1 (v + 1) = insert (v + 1) (Finset.Icc 1 v) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : v + 1 ∉ Finset.Icc 1 v := by simp [Finset.mem_Icc]
    rw [hIcc, Finset.sum_insert hnot, Nat.add_sub_cancel]
    have hpow : (B : ℝ) ^ (v + 1) = (B : ℝ) * (B : ℝ) ^ v := by rw [pow_succ]; ring
    linarith

/-- Finite geometric bound: for `2 ≤ B < p`,
    `((B : ℝ) - 1) * ∑_{k=1}^M (B^(k-1) / p^k) ≤ (B - 1) / (p - B)`. -/
lemma geom_prime_power_sum_le {B p : ℕ} (hB : 2 ≤ B) (hp : B < p) (M : ℕ) :
    ((B : ℝ) - 1) * ∑ k ∈ Finset.Icc 1 M, ((B : ℝ) ^ (k - 1) / (p : ℝ) ^ k) ≤
      ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ)) := by
  have hB_pos : (0 : ℝ) < (B : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    linarith
  have hp_gt : (B : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hsub_pos : (0 : ℝ) < (p : ℝ) - (B : ℝ) := by linarith
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hB_pos)
  -- Show `(p - B) * ∑_{k=1}^M B^(k-1) / p^k ≤ 1` by telescoping!
  rw [← one_div, le_div_iff₀ hsub_pos]
  have htele : ∀ N : ℕ,
      (∑ k ∈ Finset.Icc 1 N, ((B : ℝ) ^ (k - 1) / (p : ℝ) ^ k)) * ((p : ℝ) - (B : ℝ)) =
        1 - ((B : ℝ) / (p : ℝ)) ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : N + 1 ∉ Finset.Icc 1 N := by simp [Finset.mem_Icc]
      rw [hIcc, Finset.sum_insert hnot, add_mul, ih, Nat.add_sub_cancel]
      have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
      have hpow_ne : (p : ℝ) ^ N ≠ 0 := pow_ne_zero N hp_ne
      rw [div_pow, div_pow, pow_succ, pow_succ]
      field_simp [hp_ne, hpow_ne]
      ring
  rw [htele M]
  have hnonneg : (0 : ℝ) ≤ ((B : ℝ) / (p : ℝ)) ^ M :=
    pow_nonneg (div_nonneg (by positivity) (le_of_lt hp_pos)) M
  linarith

/-- **Elementary Finite Dirichlet Exponential Sum Bound (Induction on `S`)**:
    For any base `B ≥ 2`, any `M : ℕ`, and any finite set `S` of primes strictly exceeding `B`:
    `∑_{a=1}^M B^{Ω_S(a)} ≤ M * ∏_{p ∈ S} (1 + (B - 1) / (p - B))`. -/
theorem dirichlet_exp_sum_bound (B : ℕ) (hB : 2 ≤ B) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ B < p) :
    ∀ M : ℕ,
      ∑ a ∈ Finset.Icc 1 M, ((B : ℝ) ^ (∑ p ∈ S, a.factorization p)) ≤
        (M : ℝ) * ∏ p ∈ S, (1 + ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ))) := by
  induction S using Finset.induction_on with
  | empty =>
    intro M
    simp [Nat.card_Icc]
  | insert p S hpS ih =>
    intro M
    have hp_info := hS p (Finset.mem_insert_self p S)
    have hp_prime : p.Prime := hp_info.1
    have hp_gt : B < p := hp_info.2
    have hS_sub : ∀ q ∈ S, q.Prime ∧ B < q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have ih' := ih hS_sub
    have hB_pos : (0 : ℝ) < (B : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
      linarith
    have hprod_nonneg : 0 ≤ ∏ q ∈ S, (1 + ((B : ℝ) - 1) / ((q : ℝ) - (B : ℝ))) := by
      apply Finset.prod_nonneg
      intro q hq
      have hqB : (B : ℝ) < (q : ℝ) := by exact_mod_cast (hS_sub q hq).2
      have : 0 ≤ ((B : ℝ) - 1) / ((q : ℝ) - (B : ℝ)) :=
        div_nonneg (le_of_lt hB_pos) (by linarith)
      linarith
    -- Rewrite each term `a ∈ Icc 1 M` using `B^{v_p(a)} = 1 + (B - 1) ∑_{k=1}^M [p^k ∣ a] B^{k-1}`
    have hterm : ∀ a ∈ Finset.Icc 1 M,
        ((B : ℝ) ^ (∑ q ∈ insert p S, a.factorization q)) =
          ((B : ℝ) ^ (∑ q ∈ S, a.factorization q)) +
            ((B : ℝ) - 1) * ∑ k ∈ Finset.Icc 1 M,
              (if p ^ k ∣ a then ((B : ℝ) ^ (k - 1)) * ((B : ℝ) ^ (∑ q ∈ S, a.factorization q)) else 0) := by
      intro a ha
      rw [Finset.sum_insert hpS, pow_add]
      have hm := Finset.mem_Icc.mp ha
      have ha0 : a ≠ 0 := by omega
      rw [real_pow_eq_one_add_geom B (a.factorization p)]
      have hfilt_eq : ∑ k ∈ Finset.Icc 1 M,
          (if p ^ k ∣ a then ((B : ℝ) ^ (k - 1)) * ((B : ℝ) ^ (∑ q ∈ S, a.factorization q)) else 0) =
          (∑ k ∈ Finset.Icc 1 (a.factorization p), (B : ℝ) ^ (k - 1)) *
            ((B : ℝ) ^ (∑ q ∈ S, a.factorization q)) := by
        rw [Finset.sum_mul, ← Finset.sum_filter]
        have hleM : a.factorization p ≤ M := by
          have h1 : a.factorization p < 2 ^ (a.factorization p) := Nat.lt_two_pow_self
          have h2 : 2 ^ (a.factorization p) ≤ p ^ (a.factorization p) :=
            Nat.pow_le_pow_left hp_prime.two_le _
          have h3 : p ^ (a.factorization p) ≤ a :=
            Nat.le_of_dvd (by omega) (Nat.ordProj_dvd a p)
          omega
        have hset : (Finset.Icc 1 M).filter (fun k => p ^ k ∣ a) =
            Finset.Icc 1 (a.factorization p) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · rintro ⟨⟨hk1, _⟩, hdvd⟩
            exact ⟨hk1, (hp_prime.pow_dvd_iff_le_factorization ha0).mp hdvd⟩
          · rintro ⟨hk1, hkv⟩
            exact ⟨⟨hk1, le_trans hkv hleM⟩, (hp_prime.pow_dvd_iff_le_factorization ha0).mpr hkv⟩
        rw [hset]
      rw [hfilt_eq]
      ring
    -- Bijection: `{a ∈ Icc 1 M | p^k ∣ a} ≃ Icc 1 (M / p^k)` preserving `Ω_S`!
    have hmult_sum : ∀ k ∈ Finset.Icc 1 M,
        ∑ a ∈ Finset.Icc 1 M,
          (if p ^ k ∣ a then ((B : ℝ) ^ (k - 1)) * ((B : ℝ) ^ (∑ q ∈ S, a.factorization q)) else 0) =
        ((B : ℝ) ^ (k - 1)) * ∑ t ∈ Finset.Icc 1 (M / p ^ k), ((B : ℝ) ^ (∑ q ∈ S, t.factorization q)) := by
      intro k _
      rw [← Finset.sum_filter, ← Finset.mul_sum]
      congr 1
      have hpk_pos : 0 < p ^ k := pow_pos hp_prime.pos k
      refine Finset.sum_bij (fun a _ => a / p ^ k) ?_ ?_ ?_ ?_
      · intro a ha
        rw [Finset.mem_filter, Finset.mem_Icc] at ha
        rcases ha with ⟨⟨ha1, haM⟩, ⟨t, rfl⟩⟩
        have ht1 : 1 ≤ t := Nat.pos_of_mul_pos_left ha1
        rw [Nat.mul_div_cancel_left t hpk_pos, Finset.mem_Icc]
        exact ⟨ht1, (Nat.le_div_iff_mul_le hpk_pos).mpr (by linarith)⟩
      · intro a₁ ha₁ a₂ ha₂ heq
        rw [Finset.mem_filter] at ha₁ ha₂
        rcases ha₁.2 with ⟨t₁, rfl⟩
        rcases ha₂.2 with ⟨t₂, rfl⟩
        rw [Nat.mul_div_cancel_left t₁ hpk_pos, Nat.mul_div_cancel_left t₂ hpk_pos] at heq
        rw [heq]
      · intro t ht
        rw [Finset.mem_Icc] at ht
        refine ⟨p ^ k * t, ?_, Nat.mul_div_cancel_left t hpk_pos⟩
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.mul_pos hpk_pos ht.1, ?_⟩, dvd_mul_right _ _⟩
        calc p ^ k * t ≤ p ^ k * (M / p ^ k) := Nat.mul_le_mul_left _ ht.2
          _ ≤ M := Nat.mul_div_le M (p ^ k)
      · intro a ha
        rw [Finset.mem_filter, Finset.mem_Icc] at ha
        rcases ha with ⟨⟨ha1, _⟩, ⟨t, rfl⟩⟩
        have ht0 : t ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mul_pos_left ha1)
        have hpk0 : p ^ k ≠ 0 := Nat.ne_of_gt hpk_pos
        rw [Nat.mul_div_cancel_left t hpk_pos]
        congr 1
        apply Finset.sum_congr rfl
        intro q hq
        rw [Nat.factorization_mul hpk0 ht0, Finsupp.add_apply,
            Nat.Prime.factorization_pow hp_prime, Finsupp.single_apply]
        have hqp : p ≠ q := fun h => hpS (h ▸ hq)
        simp [hqp]
    -- Assemble!
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
    rw [Finset.sum_congr rfl hmult_sum]
    set P := ∏ q ∈ S, (1 + ((B : ℝ) - 1) / ((q : ℝ) - (B : ℝ)))
    have hstep1 :
        ∑ a ∈ Finset.Icc 1 M, ((B : ℝ) ^ (∑ q ∈ S, a.factorization q)) +
          ((B : ℝ) - 1) * ∑ k ∈ Finset.Icc 1 M,
            ((B : ℝ) ^ (k - 1)) * ∑ t ∈ Finset.Icc 1 (M / p ^ k), ((B : ℝ) ^ (∑ q ∈ S, t.factorization q))
        ≤ (M : ℝ) * P + ((B : ℝ) - 1) * ∑ k ∈ Finset.Icc 1 M,
            ((B : ℝ) ^ (k - 1)) * (((M / p ^ k : ℕ) : ℝ) * P) := by
      apply add_le_add (ih' M)
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hB_pos)
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (ih' (M / p ^ k)) (by positivity)
    have hstep2 :
        (M : ℝ) * P + ((B : ℝ) - 1) * ∑ k ∈ Finset.Icc 1 M,
            ((B : ℝ) ^ (k - 1)) * (((M / p ^ k : ℕ) : ℝ) * P)
        ≤ (M : ℝ) * (1 + ((B : ℝ) - 1) * ∑ k ∈ Finset.Icc 1 M, ((B : ℝ) ^ (k - 1) / (p : ℝ) ^ k)) * P := by
      have hdiv_le : ∀ k ∈ Finset.Icc 1 M,
          ((B : ℝ) ^ (k - 1)) * (((M / p ^ k : ℕ) : ℝ) * P) ≤
            (M : ℝ) * ((B : ℝ) ^ (k - 1) / (p : ℝ) ^ k) * P := by
        intro k _
        have hpk_pos : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (by exact_mod_cast hp_prime.pos) k
        have hcast : ((M / p ^ k : ℕ) : ℝ) ≤ (M : ℝ) / (p : ℝ) ^ k := by
          rw [le_div_iff₀ hpk_pos]
          have : (M / p ^ k) * p ^ k ≤ M := Nat.div_mul_le_self M (p ^ k)
          exact_mod_cast this
        calc
          ((B : ℝ) ^ (k - 1)) * (((M / p ^ k : ℕ) : ℝ) * P)
              ≤ ((B : ℝ) ^ (k - 1)) * (((M : ℝ) / (p : ℝ) ^ k) * P) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcast hprod_nonneg) (by positivity)
          _ = (M : ℝ) * ((B : ℝ) ^ (k - 1) / (p : ℝ) ^ k) * P := by ring
      calc
        (M : ℝ) * P + ((B : ℝ) - 1) * ∑ k ∈ Finset.Icc 1 M,
            ((B : ℝ) ^ (k - 1)) * (((M / p ^ k : ℕ) : ℝ) * P)
            ≤ (M : ℝ) * P + ((B : ℝ) - 1) * ∑ k ∈ Finset.Icc 1 M,
                (M : ℝ) * ((B : ℝ) ^ (k - 1) / (p : ℝ) ^ k) * P :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hdiv_le) (le_of_lt hB_pos))
        _ = (M : ℝ) * (1 + ((B : ℝ) - 1) * ∑ k ∈ Finset.Icc 1 M, ((B : ℝ) ^ (k - 1) / (p : ℝ) ^ k)) * P := by
              rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
    have hstep3 :
        (M : ℝ) * (1 + ((B : ℝ) - 1) * ∑ k ∈ Finset.Icc 1 M, ((B : ℝ) ^ (k - 1) / (p : ℝ) ^ k)) * P
        ≤ (M : ℝ) * ((1 + ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ))) * P) := by
      have hg := geom_prime_power_sum_le hB hp_gt M
      have h1 : 1 + ((B : ℝ) - 1) * ∑ k ∈ Finset.Icc 1 M, ((B : ℝ) ^ (k - 1) / (p : ℝ) ^ k) ≤
          1 + ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ)) := add_le_add le_rfl hg
      have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg M)
      have h3 := mul_le_mul_of_nonneg_right h2 hprod_nonneg
      linarith
    rw [Finset.prod_insert hpS]
    exact le_trans (le_trans hstep1 hstep2) hstep3

/-- **Jensen Exponential Prime-Valuation Bound**:
    For any `B ≥ 2`, `A ⊆ Icc 1 M` (`A.Nonempty`), and any set `S` of primes `> B`:
    `∑_{p ∈ S} ∑_{a ∈ A} v_p(a) ≤ (|A| * log(M / |A|) + (B - 1) * |A| * ∑_{p ∈ S} 1/(p - B)) / log B`. -/
theorem jensen_prime_sum_bound {B M : ℕ} (hB : 2 ≤ B) {A S : Finset ℕ}
    (hA_ne : A.Nonempty) (hA : A ⊆ Finset.Icc 1 M)
    (hS : ∀ p ∈ S, p.Prime ∧ B < p) :
    (∑ p ∈ S, ∑ a ∈ A, (a.factorization p : ℝ)) ≤
      ((A.card : ℝ) * Real.log ((M : ℝ) / (A.card : ℝ)) +
        ((B : ℝ) - 1) * (A.card : ℝ) * ∑ p ∈ S, (1 / ((p : ℝ) - (B : ℝ)))) / Real.log (B : ℝ) := by
  have hn_pos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA_ne
  have hM_ge_n : A.card ≤ M := by
    calc A.card ≤ (Finset.Icc 1 M).card := Finset.card_le_card hA
      _ = M := by rw [Nat.card_Icc]; omega
  have hM_pos : (0 : ℝ) < (M : ℝ) := by
    have : (A.card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_n
    linarith
  have hB_gt1 : (1 : ℝ) < (B : ℝ) := by
    have : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    linarith
  have hB_pos : (0 : ℝ) < (B : ℝ) := by linarith
  have hlogB_pos : 0 < Real.log (B : ℝ) := Real.log_pos hB_gt1
  -- Apply Jensen's inequality (`convexOn_exp.map_sum_le`)!
  let w : ℕ → ℝ := fun _ => (1 : ℝ) / (A.card : ℝ)
  let x : ℕ → ℝ := fun a => (∑ p ∈ S, (a.factorization p : ℝ)) * Real.log (B : ℝ)
  have hw_nonneg : ∀ a ∈ A, 0 ≤ w a := fun _ _ => div_nonneg zero_le_one (le_of_lt hn_pos)
  have hw_sum : ∑ a ∈ A, w a = 1 := by
    simp only [w, Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hjensen := convexOn_exp.map_sum_le hw_nonneg hw_sum (fun a _ => Set.mem_univ (x a))
  -- Rewrite LHS and RHS of Jensen
  have hexp_eq : ∀ a ∈ A, Real.exp (x a) = (B : ℝ) ^ (∑ p ∈ S, a.factorization p) := by
    intro a _
    dsimp [x]
    rw [← Nat.cast_sum, Real.exp_nat_mul, Real.exp_log hB_pos]
  have hrhs_le : ∑ a ∈ A, w a * Real.exp (x a) ≤
      ((M : ℝ) / (A.card : ℝ)) * ∏ p ∈ S, (1 + ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ))) := by
    have h1 : ∑ a ∈ A, w a * Real.exp (x a) =
        (1 / (A.card : ℝ)) * ∑ a ∈ A, (B : ℝ) ^ (∑ p ∈ S, a.factorization p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      dsimp [w]
      rw [hexp_eq a ha]
    rw [h1]
    have hsub_le : ∑ a ∈ A, (B : ℝ) ^ (∑ p ∈ S, a.factorization p) ≤
        ∑ a ∈ Finset.Icc 1 M, (B : ℝ) ^ (∑ p ∈ S, a.factorization p) :=
      Finset.sum_le_sum_of_subset_of_nonneg hA (fun _ _ _ => by positivity)
    have hdir := dirichlet_exp_sum_bound B hB S hS M
    calc
      (1 / (A.card : ℝ)) * ∑ a ∈ A, (B : ℝ) ^ (∑ p ∈ S, a.factorization p)
          ≤ (1 / (A.card : ℝ)) * ((M : ℝ) * ∏ p ∈ S, (1 + ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ)))) :=
            mul_le_mul_of_nonneg_left (le_trans hsub_le hdir) (div_nonneg zero_le_one (le_of_lt hn_pos))
      _ = ((M : ℝ) / (A.card : ℝ)) * ∏ p ∈ S, (1 + ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ))) := by ring
  have hcomb : Real.exp (∑ a ∈ A, w a * x a) ≤
      ((M : ℝ) / (A.card : ℝ)) * ∏ p ∈ S, (1 + ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ))) :=
    le_trans hjensen hrhs_le
  -- Take `Real.log` of both sides!
  have hprod_pos : 0 < ∏ p ∈ S, (1 + ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ))) := by
    apply Finset.prod_pos
    intro p hp
    have hpB : (B : ℝ) < (p : ℝ) := by exact_mod_cast (hS p hp).2
    have : 0 ≤ ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ)) :=
      div_nonneg (by linarith) (by linarith)
    linarith
  have hlog_le := Real.log_le_log (Real.exp_pos _) hcomb
  rw [Real.log_exp, Real.log_mul (ne_of_gt (div_pos hM_pos hn_pos)) (ne_of_gt hprod_pos)] at hlog_le
  have hlog_prod : Real.log (∏ p ∈ S, (1 + ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ)))) ≤
      ((B : ℝ) - 1) * ∑ p ∈ S, (1 / ((p : ℝ) - (B : ℝ))) := by
    rw [Real.log_prod]
    · calc
        ∑ p ∈ S, Real.log (1 + ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ)))
            ≤ ∑ p ∈ S, ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ)) := by
              apply Finset.sum_le_sum
              intro p hp
              have hpB : (B : ℝ) < (p : ℝ) := by exact_mod_cast (hS p hp).2
              have hpos : 0 < 1 + ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ)) := by
                have : 0 ≤ ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ)) :=
                  div_nonneg (by linarith) (by linarith)
                linarith
              have h1 := Real.log_le_sub_one_of_pos hpos
              linarith
        _ = ((B : ℝ) - 1) * ∑ p ∈ S, (1 / ((p : ℝ) - (B : ℝ))) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p _; ring
    · intro p hp
      have hpB : (B : ℝ) < (p : ℝ) := by exact_mod_cast (hS p hp).2
      have : 0 ≤ ((B : ℝ) - 1) / ((p : ℝ) - (B : ℝ)) :=
        div_nonneg (by linarith) (by linarith)
      linarith
  have hlhs_eq : ∑ a ∈ A, w a * x a =
      ((∑ p ∈ S, ∑ a ∈ A, (a.factorization p : ℝ)) / (A.card : ℝ)) * Real.log (B : ℝ) := by
    dsimp [w, x]
    rw [Finset.sum_comm]
    have h1 : ∀ a ∈ A, 1 / (A.card : ℝ) * ((∑ p ∈ S, (a.factorization p : ℝ)) * Real.log (B : ℝ)) =
        (∑ p ∈ S, (a.factorization p : ℝ)) * (Real.log (B : ℝ) / (A.card : ℝ)) := by
      intro a _; ring
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, Finset.sum_comm]
    ring
  rw [hlhs_eq] at hlog_le
  have hfinal : ((∑ p ∈ S, ∑ a ∈ A, (a.factorization p : ℝ)) / (A.card : ℝ)) * Real.log (B : ℝ) ≤
      Real.log ((M : ℝ) / (A.card : ℝ)) + ((B : ℝ) - 1) * ∑ p ∈ S, (1 / ((p : ℝ) - (B : ℝ))) :=
    le_trans hlog_le (add_le_add le_rfl hlog_prod)
  rw [le_div_iff₀ hlogB_pos]
  have hmul := mul_le_mul_of_nonneg_left hfinal (le_of_lt hn_pos)
  have hsimp : (A.card : ℝ) *
      (((∑ p ∈ S, ∑ a ∈ A, (a.factorization p : ℝ)) / (A.card : ℝ)) * Real.log (B : ℝ)) =
      (∑ p ∈ S, ∑ a ∈ A, (a.factorization p : ℝ)) * Real.log (B : ℝ) := by
    field_simp
  linarith

/-- Lower bound on prime valuation in `K!` via counting multiples of `p` in `{1, ..., K}`. -/
lemma div_le_factorial_factorization {K p : ℕ} (hp : p.Prime) :
    K / p ≤ (K !).factorization p := by
  have hfac : ∏ a ∈ Erdos708Interval 0 K, a = K ! := by
    have := mul_prod_Icc_eq_factorial 0 K
    simpa using this
  have hne : ∀ a ∈ Erdos708Interval 0 K, a ≠ 0 :=
    fun a ha => Nat.ne_of_gt (erdos708Interval_pos ha)
  rw [← hfac, Nat.factorization_prod hne]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  calc
    K / p ≤ ((Erdos708Interval 0 K).filter (fun a => p ∣ a)).card :=
      card_multiples_Icc_ge 0 K p hp.pos
    _ = ∑ _a ∈ (Erdos708Interval 0 K).filter (fun a => p ∣ a), 1 := by simp
    _ ≤ ∑ a ∈ (Erdos708Interval 0 K).filter (fun a => p ∣ a), a.factorization p := by
      apply Finset.sum_le_sum
      intro a ha
      rw [Finset.mem_filter] at ha
      have ha0 : a ≠ 0 := hne a ha.1
      have h1 : p ^ 1 ∣ a := by simpa [pow_one] using ha.2
      exact (hp.pow_dvd_iff_le_factorization ha0).mp h1
    _ ≤ ∑ a ∈ Erdos708Interval 0 K, a.factorization p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

/-- Numerical constant check: `3 / log 2 ≤ 5` (since `e^3 < 32 = 2^5`). -/
lemma three_div_log_two_le_five : (3 : ℝ) / Real.log 2 ≤ 5 := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ hlog2_pos]
  have hexp1 : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp3 : Real.exp 3 < 32 := by
    have h1 : Real.exp 3 = (Real.exp 1) ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    have hpos : (0 : ℝ) ≤ Real.exp 1 := le_of_lt (Real.exp_pos 1)
    nlinarith [sq_nonneg (Real.exp 1)]
  have hlog : Real.log (Real.exp 3) < Real.log (2 ^ 5 : ℝ) :=
    Real.log_lt_log (Real.exp_pos 3) (by norm_num; linarith)
  rw [Real.log_exp, Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- **Dirichlet–Jensen Consecutive-Block Upper Bound (`M ≤ 9 n^2`)**:
    For every `A ⊆ [1, ∞)` with `2 ≤ |A|` and `max(A) ≤ 9 * |A|^2`, and every `m : ℕ`:
    `|B| ≤ 10 * |A| + |A| * (Nat.log 2 (max(A) / |A|) + 1)`. -/
theorem erdos708_block_jensen_base2 {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) (m : ℕ)
    (hn : 2 ≤ A.card) (hM_le : A.sup id ≤ 9 * A.card ^ 2) :
    Erdos708Covers A m (10 * A.card + A.card * (Nat.log 2 (A.sup id / A.card) + 1)) := by
  set n := A.card
  set M := A.sup id
  set I := Erdos708Interval m M
  have hA_ne : A.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hsmall : M ≤ 7 * n
  · obtain ⟨B, hBI, hBcard, hBdvd⟩ := erdos708_trivial_max_bound hA m
    exact ⟨B, hBI, le_trans hBcard (by omega), hBdvd⟩
  push Not at hsmall
  -- 1. Consecutive block `B₀ = Erdos708Interval m (7 * n) ⊆ I`
  let B₀ := Erdos708Interval m (7 * n)
  have hB₀_sub : B₀ ⊆ I := by
    intro b hb
    simp only [B₀, I, Erdos708Interval, Finset.mem_Icc] at hb ⊢
    omega
  have hB₀_card : B₀.card = 7 * n := erdos708Interval_card m (7 * n)
  have hB₀_val : ∀ p : ℕ, p.Prime → 7 * n / p ≤ ∑ b ∈ B₀, b.factorization p := by
    intro p hp
    have hdvd := factorial_dvd_prod_Icc m (7 * n)
    have hfac_ne : (7 * n) ! ≠ 0 := Nat.factorial_ne_zero _
    have hprod_ne : (∏ b ∈ B₀, b) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun b hb => Nat.ne_of_gt (erdos708Interval_pos (hB₀_sub hb)))
    have hle := (Nat.factorization_le_iff_dvd hfac_ne hprod_ne).mpr hdvd p
    rw [Nat.factorization_prod (fun b hb => Nat.ne_of_gt (erdos708Interval_pos (hB₀_sub hb)))] at hle
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply] at hle
    exact le_trans (div_le_factorial_factorization hp) hle
  -- 2. Prime `p = 2`: cover via `exists_cover_prime_by_card`
  obtain ⟨B₁, hB₁_sub, hB₁_card, hB₁_val⟩ :=
    exists_cover_prime_by_card (m := m) (M := M) Nat.prime_two (subset_Icc_one_sup hA)
  -- Helper: total interval `I` always dominates `A` at every prime `p`.
  have hI_dom : ∀ p : ℕ, ∑ a ∈ A, a.factorization p ≤ ∑ b ∈ I, b.factorization p := by
    intro p
    have hdvd := dvd_trans (prod_subset_Icc_dvd_factorial (subset_Icc_one_sup hA))
      (factorial_dvd_prod_Icc m M)
    have hAne : ∏ a ∈ A, a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun a ha => by have := hA a ha; omega)
    have hIne : ∏ b ∈ I, b ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun b hb => Nat.ne_of_gt (erdos708Interval_pos hb))
    have hle := (Nat.factorization_le_iff_dvd hAne hIne).mpr hdvd p
    rw [Nat.factorization_prod (fun a ha => by have := hA a ha; omega),
        Nat.factorization_prod (fun b hb => Nat.ne_of_gt (erdos708Interval_pos hb))] at hle
    simpa [Finsupp.coe_finsetSum, Finset.sum_apply] using hle
  -- 3. Primes `p > 2 * n`: every `a ∈ A` has `∑_{p > 2n} v_p(a) ≤ 2` since `M ≤ 9 n^2 < (2n)^3`!
  set P_all := A.biUnion Nat.primeFactors
  set P_big := P_all.filter (fun p => 2 * n < p)
  have hbig_cover : ∀ p ∈ P_big, ∃ C ⊆ I,
      C.card ≤ ∑ a ∈ A, a.factorization p ∧
      ∑ a ∈ A, a.factorization p ≤ ∑ b ∈ C, b.factorization p :=
    fun p _ => exists_cover_prime_deficit (hI_dom p)
  choose Cbig hCbig_sub hCbig_card hCbig_val using hbig_cover
  let B₂ := P_big.attach.biUnion (fun ⟨p, hp⟩ => Cbig p hp)
  have hB₂_sub : B₂ ⊆ I := by
    intro b hb
    rcases Finset.mem_biUnion.mp hb with ⟨⟨p, hp⟩, _, hbc⟩
    exact hCbig_sub p hp hbc
  have hB₂_card : B₂.card ≤ 2 * n := by
    have hper_a : ∀ a ∈ A, ∑ p ∈ P_big, a.factorization p ≤ 2 := by
      intro a ha
      have ha0 : a ≠ 0 := by have := hA a ha; omega
      have haM : a ≤ M := Finset.le_sup (f := id) ha
      have hpow_le : (2 * n) ^ (∑ p ∈ P_big, a.factorization p) ≤ a := by
        have h1 : (2 * n) ^ (∑ p ∈ P_big, a.factorization p) =
            ∏ p ∈ P_big, (2 * n) ^ (a.factorization p) := by
          induction P_big using Finset.induction_on with
          | empty => simp
          | insert p s hp ih => rw [Finset.sum_insert hp, pow_add, Finset.prod_insert hp, ih]
        rw [h1]
        have h2 : ∏ p ∈ P_big, (2 * n) ^ (a.factorization p) ≤
            ∏ p ∈ P_big, p ^ (a.factorization p) := by
          apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          intro p hp
          exact Nat.pow_le_pow_left (le_of_lt (Finset.mem_filter.mp hp).2) _
        have h3 : ∏ p ∈ P_big, p ^ (a.factorization p) =
            ∏ p ∈ P_big ∩ a.primeFactors, p ^ (a.factorization p) := by
          symm
          apply Finset.prod_subset Finset.inter_subset_left
          intro p hp hnot
          have hp_not : p ∉ a.primeFactors := fun h => hnot (Finset.mem_inter.mpr ⟨hp, h⟩)
          rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hp_not
          simp [hp_not]
        have h4 : (∏ p ∈ P_big ∩ a.primeFactors, p ^ (a.factorization p)) ∣ a := by
          have ha_eq := Nat.prod_factorization_pow_eq_self ha0
          rw [Finsupp.prod, Nat.support_factorization] at ha_eq
          have hd : (∏ p ∈ P_big ∩ a.primeFactors, p ^ (a.factorization p)) ∣
              (∏ p ∈ a.primeFactors, p ^ (a.factorization p)) :=
            Finset.prod_dvd_prod_of_subset _ _ _ Finset.inter_subset_right
          rwa [ha_eq] at hd
        exact le_trans h2 (h3 ▸ Nat.le_of_dvd (by omega) h4)
      have hlt3 : (2 * n) ^ (∑ p ∈ P_big, a.factorization p) < (2 * n) ^ 3 := by
        have hcube : 9 * n ^ 2 < (2 * n) ^ 3 := by
          have : (2 * n) ^ 3 = 8 * n * n ^ 2 := by ring
          nlinarith
        omega
      have h2n_gt1 : 1 < 2 * n := by omega
      have hlt := (Nat.pow_lt_pow_iff_right h2n_gt1).mp hlt3
      omega
    calc
      B₂.card ≤ ∑ x ∈ P_big.attach, (Cbig x.1 x.2).card := Finset.card_biUnion_le
      _ ≤ ∑ x ∈ P_big.attach, ∑ a ∈ A, a.factorization x.1 :=
        Finset.sum_le_sum (fun x _ => hCbig_card x.1 x.2)
      _ = ∑ p ∈ P_big, ∑ a ∈ A, a.factorization p :=
        Finset.sum_attach P_big (fun p => ∑ a ∈ A, a.factorization p)
      _ = ∑ a ∈ A, ∑ p ∈ P_big, a.factorization p := Finset.sum_comm
      _ ≤ ∑ _a ∈ A, 2 := Finset.sum_le_sum hper_a
      _ = 2 * n := by simp [n, mul_comm]
  -- 4. Odd primes `3 ≤ p ≤ 2 * n` with deficit after `B₀`: apply Dirichlet–Jensen (`B = 2`)!
  set S := P_all.filter (fun p => 3 ≤ p ∧ p ≤ 2 * n ∧
      ∑ b ∈ B₀, b.factorization p < ∑ a ∈ A, a.factorization p)
  have hS_primes : ∀ p ∈ S, p.Prime ∧ 2 < p := by
    intro p hp
    have hf := Finset.mem_filter.mp hp
    rcases Finset.mem_biUnion.mp hf.1 with ⟨a, _, hap⟩
    exact ⟨Nat.prime_of_mem_primeFactors hap, by omega⟩
  have hdef_cover : ∀ p ∈ S, ∃ C ⊆ I \ B₀,
      C.card ≤ (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) ∧
      (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) ≤ ∑ b ∈ C, b.factorization p := by
    intro p _
    apply exists_cover_prime_deficit
    have hsplit : ∑ b ∈ I, b.factorization p =
        ∑ b ∈ B₀, b.factorization p + ∑ b ∈ I \ B₀, b.factorization p := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hB₀_sub]
    have hdom := hI_dom p
    omega
  choose Cdef hCdef_sub hCdef_card hCdef_val using hdef_cover
  let B₃ := S.attach.biUnion (fun ⟨p, hp⟩ => Cdef p hp)
  have hB₃_sub : B₃ ⊆ I := by
    intro b hb
    rcases Finset.mem_biUnion.mp hb with ⟨⟨p, hp⟩, _, hbc⟩
    exact Finset.sdiff_subset (hCdef_sub p hp hbc)
  have hB₃_card : B₃.card ≤ n * (Nat.log 2 (M / n) + 1) := by
    have hcard_le_sum : B₃.card ≤ ∑ p ∈ S, ((∑ a ∈ A, a.factorization p) - 7 * n / p) := by
      calc
        B₃.card ≤ ∑ x ∈ S.attach, (Cdef x.1 x.2).card := Finset.card_biUnion_le
        _ ≤ ∑ x ∈ S.attach, ((∑ a ∈ A, a.factorization x.1) - ∑ b ∈ B₀, b.factorization x.1) :=
          Finset.sum_le_sum (fun x _ => hCdef_card x.1 x.2)
        _ = ∑ p ∈ S, ((∑ a ∈ A, a.factorization p) - ∑ b ∈ B₀, b.factorization p) :=
          Finset.sum_attach S (fun p => (∑ a ∈ A, a.factorization p) - ∑ b ∈ B₀, b.factorization p)
        _ ≤ ∑ p ∈ S, ((∑ a ∈ A, a.factorization p) - 7 * n / p) := by
          apply Finset.sum_le_sum
          intro p hp
          have hp_pr := (hS_primes p hp).1
          have hge := hB₀_val p hp_pr
          omega
    -- Bound the sum in `ℝ` via `jensen_prime_sum_bound`!
    have hreal_le : ((∑ p ∈ S, ((∑ a ∈ A, a.factorization p) - 7 * n / p) : ℕ) : ℝ) ≤
        ((n * (Nat.log 2 (M / n) + 1) : ℕ) : ℝ) := by
      have hjen := jensen_prime_sum_bound (B := 2) (M := M) (le_refl 2) hA_ne
        (subset_Icc_one_sup hA) hS_primes
      have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      -- Each `p ∈ S` has `7 * n / p ≤ ∑ a ∈ A, a.factorization p` and `(5 * n : ℝ) / p ≤ (7 * n / p : ℕ)`.
      have hsub_cast : ((∑ p ∈ S, ((∑ a ∈ A, a.factorization p) - 7 * n / p) : ℕ) : ℝ) =
          (∑ p ∈ S, ∑ a ∈ A, (a.factorization p : ℝ)) - ∑ p ∈ S, ((7 * n / p : ℕ) : ℝ) := by
        rw [Nat.cast_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        have hlt := (Finset.mem_filter.mp hp).2.2.2
        have hge := hB₀_val p (hS_primes p hp).1
        rw [Nat.cast_sub (by omega), Nat.cast_sum]
      rw [hsub_cast]
      -- Bound `∑_{p ∈ S} 1/(p - 2) ≤ 3 * ∑_{p ∈ S} 1/p`
      have hinv : ∑ p ∈ S, (1 / ((p : ℝ) - 2)) ≤ 3 * ∑ p ∈ S, (1 / (p : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p hp
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.1
        have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
        have hpm2_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
        rw [mul_one_div, div_le_div_iff₀ hpm2_pos hp_pos]
        linarith
      -- Bound `(5 * n) * ∑_{p ∈ S} 1/p ≤ ∑_{p ∈ S} (7 * n / p : ℕ)`
      have hblock_ge : 5 * (n : ℝ) * ∑ p ∈ S, (1 / (p : ℝ)) ≤ ∑ p ∈ S, ((7 * n / p : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p hp
        have hp_le : p ≤ 2 * n := (Finset.mem_filter.mp hp).2.2.1
        have hp_pos : 0 < p := (hS_primes p hp).1.pos
        have hp_rpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
        have hdm : 7 * n < (7 * n / p + 1) * p := by
          have := Nat.div_add_mod (7 * n) p
          have := Nat.mod_lt (7 * n) hp_pos
          nlinarith
        have hdm_r : (7 : ℝ) * (n : ℝ) < ((7 * n / p : ℕ) : ℝ) * (p : ℝ) + (p : ℝ) := by
          have : (7 * n : ℝ) < ((7 * n / p + 1) * p : ℕ) := by exact_mod_cast hdm
          push_cast at this
          linarith
        have hp_le_r : (p : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hp_le
        have h5 : 5 * (n : ℝ) ≤ ((7 * n / p : ℕ) : ℝ) * (p : ℝ) := by linarith
        rw [mul_one_div, div_le_iff₀ hp_rpos]
        exact h5
      -- Bound `log(M / n) / log 2 ≤ Nat.log 2 (M / n) + 1`
      have hlog_mn : Real.log ((M : ℝ) / (n : ℝ)) / Real.log 2 ≤ ((Nat.log 2 (M / n) + 1 : ℕ) : ℝ) := by
        rw [div_le_iff₀ hlog2_pos]
        have h1 : M / n < 2 ^ (Nat.log 2 (M / n) + 1) := Nat.lt_pow_succ_log_self (by omega) _
        have h2 : M < (M / n + 1) * n := by
          have := Nat.div_add_mod M n
          have := Nat.mod_lt M (by omega : 0 < n)
          nlinarith
        have h3 : (M : ℝ) / (n : ℝ) ≤ ((2 ^ (Nat.log 2 (M / n) + 1) : ℕ) : ℝ) := by
          rw [div_le_iff₀ hn_pos]
          have hle_nat : M ≤ 2 ^ (Nat.log 2 (M / n) + 1) * n := by
            have : M / n + 1 ≤ 2 ^ (Nat.log 2 (M / n) + 1) := h1
            exact le_trans (le_of_lt h2) (Nat.mul_le_mul_right n this)
          exact_mod_cast hle_nat
        have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
        have hlog_le := Real.log_le_log (div_pos hM_pos hn_pos) h3
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlog_le
        exact hlog_le
      -- Combine everything!
      have h3div5 := three_div_log_two_le_five
      have hsum_inv_nonneg : 0 ≤ ∑ p ∈ S, (1 / (p : ℝ)) :=
        Finset.sum_nonneg (fun p _ => by positivity)
      have hjen_simp : (∑ p ∈ S, ∑ a ∈ A, (a.factorization p : ℝ)) ≤
          (n : ℝ) * (Real.log ((M : ℝ) / (n : ℝ)) / Real.log 2) +
            5 * (n : ℝ) * ∑ p ∈ S, (1 / (p : ℝ)) := by
        have hsplit_jen :
            ((n : ℝ) * Real.log ((M : ℝ) / (n : ℝ)) +
              ((2 : ℝ) - 1) * (n : ℝ) * ∑ p ∈ S, (1 / ((p : ℝ) - 2))) / Real.log 2 =
            (n : ℝ) * (Real.log ((M : ℝ) / (n : ℝ)) / Real.log 2) +
              ((n : ℝ) * ∑ p ∈ S, (1 / ((p : ℝ) - 2))) / Real.log 2 := by ring
        rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num] at hjen
        rw [hsplit_jen] at hjen
        have hsecond : ((n : ℝ) * ∑ p ∈ S, (1 / ((p : ℝ) - 2))) / Real.log 2 ≤
            5 * (n : ℝ) * ∑ p ∈ S, (1 / (p : ℝ)) := by
          calc
            ((n : ℝ) * ∑ p ∈ S, (1 / ((p : ℝ) - 2))) / Real.log 2
                ≤ ((n : ℝ) * (3 * ∑ p ∈ S, (1 / (p : ℝ)))) / Real.log 2 :=
                  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hinv (le_of_lt hn_pos))
                    (le_of_lt hlog2_pos)
            _ = ((3 : ℝ) / Real.log 2) * ((n : ℝ) * ∑ p ∈ S, (1 / (p : ℝ))) := by ring
            _ ≤ 5 * ((n : ℝ) * ∑ p ∈ S, (1 / (p : ℝ))) :=
                  mul_le_mul_of_nonneg_right h3div5 (mul_nonneg (le_of_lt hn_pos) hsum_inv_nonneg)
            _ = 5 * (n : ℝ) * ∑ p ∈ S, (1 / (p : ℝ)) := by ring
        linarith
      have hlog_part : (n : ℝ) * (Real.log ((M : ℝ) / (n : ℝ)) / Real.log 2) ≤
          ((n * (Nat.log 2 (M / n) + 1) : ℕ) : ℝ) := by
        rw [Nat.cast_mul]
        exact mul_le_mul_of_nonneg_left hlog_mn (le_of_lt hn_pos)
      linarith
    exact le_trans hcard_le_sum (Nat.cast_le.mp hreal_le)
  -- 5. Assemble `B = B₀ ∪ B₁ ∪ B₂ ∪ B₃`!
  let B := ((B₀ ∪ B₁) ∪ B₂) ∪ B₃
  refine ⟨B, ?_, ?_, ?_⟩
  · exact Finset.union_subset (Finset.union_subset (Finset.union_subset hB₀_sub hB₁_sub) hB₂_sub) hB₃_sub
  · calc
      B.card ≤ ((B₀ ∪ B₁) ∪ B₂).card + B₃.card := Finset.card_union_le _ _
      _ ≤ (B₀ ∪ B₁).card + B₂.card + B₃.card := by
        have := Finset.card_union_le (B₀ ∪ B₁) B₂; omega
      _ ≤ B₀.card + B₁.card + B₂.card + B₃.card := by
        have := Finset.card_union_le B₀ B₁; omega
      _ ≤ 10 * n + n * (Nat.log 2 (M / n) + 1) := by omega
  · apply prod_dvd_prod_of_factorization_le
    · intro a ha; have := hA a ha; omega
    · intro b hb
      have hBI := (Finset.union_subset (Finset.union_subset (Finset.union_subset hB₀_sub hB₁_sub) hB₂_sub) hB₃_sub) hb
      exact Nat.ne_of_gt (erdos708Interval_pos hBI)
    · intro p hp
      by_cases hp2 : p = 2
      · subst hp2
        have hsub : B₁ ⊆ B := Finset.Subset.trans Finset.subset_union_right
          (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)
        exact le_trans hB₁_val (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))
      · by_cases hp_in : p ∈ P_all
        · by_cases hp_big : 2 * n < p
          · have hp_mem : p ∈ P_big := Finset.mem_filter.mpr ⟨hp_in, hp_big⟩
            have hsub : Cbig p hp_mem ⊆ B := by
              intro b hb
              have hb2 : b ∈ B₂ := Finset.mem_biUnion.mpr ⟨⟨p, hp_mem⟩, Finset.mem_attach _ _, hb⟩
              exact Finset.mem_union_left _ (Finset.mem_union_right _ hb2)
            exact le_trans (hCbig_val p hp_mem)
              (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))
          · push Not at hp_big
            have hp3 : 3 ≤ p := by have := hp.two_le; omega
            by_cases hdef : ∑ b ∈ B₀, b.factorization p < ∑ a ∈ A, a.factorization p
            · have hpS : p ∈ S := Finset.mem_filter.mpr ⟨hp_in, hp3, hp_big, hdef⟩
              have hdisj : Disjoint B₀ (Cdef p hpS) :=
                Finset.disjoint_of_subset_right (hCdef_sub p hpS) Finset.disjoint_sdiff
              have hsub : B₀ ∪ Cdef p hpS ⊆ B := by
                apply Finset.union_subset
                · exact Finset.Subset.trans Finset.subset_union_left
                    (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)
                · intro b hb
                  exact Finset.mem_union_right _
                    (Finset.mem_biUnion.mpr ⟨⟨p, hpS⟩, Finset.mem_attach _ _, hb⟩)
              have hsum_u : ∑ b ∈ B₀ ∪ Cdef p hpS, b.factorization p =
                  ∑ b ∈ B₀, b.factorization p + ∑ b ∈ Cdef p hpS, b.factorization p :=
                Finset.sum_union hdisj
              have hle_B : ∑ b ∈ B₀ ∪ Cdef p hpS, b.factorization p ≤ ∑ b ∈ B, b.factorization p :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
              have hv := hCdef_val p hpS
              omega
            · push Not at hdef
              have hsub : B₀ ⊆ B := Finset.Subset.trans Finset.subset_union_left
                (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)
              exact le_trans hdef (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))
        · have hzero : ∀ a ∈ A, a.factorization p = 0 := by
            intro a ha
            have hnot : p ∉ a.primeFactors := fun h => hp_in (Finset.mem_biUnion.mpr ⟨a, ha, h⟩)
            rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hnot
            exact hnot
          rw [Finset.sum_eq_zero hzero]
          exact Nat.zero_le _

/-- Elementary inequality: `3 * s < 2 ^ (s / 2)` for all `s ≥ 12`. -/
lemma three_mul_lt_two_pow_half (s : ℕ) (hs : 12 ≤ s) : 3 * s < 2 ^ (s / 2) := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases h14 : s < 14
    · interval_cases s <;> norm_num
    · have hih := ih (s - 2) (by omega) (by omega)
      have hdiv : s / 2 = (s - 2) / 2 + 1 := by omega
      rw [hdiv, pow_succ]
      omega

/-- **UNCONDITIONAL GLOBAL SUB-LOGARITHMIC UPPER BOUND (`O(n √(log n))`)**:
    For ALL `A ⊆ [1, ∞)` (any size `n = |A|`, any `max(A)`, any interval `I` of length `max(A)`):
    `∃ B ⊆ I, |B| ≤ 3 * max 12 (Nat.sqrt (2 * Nat.log 2 |A| + 2) + 1) * |A| ∧ ∏ A ∣ ∏ B`. -/
theorem erdos708_global_sqrt_log {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) (m : ℕ) :
    Erdos708Covers A m (3 * max 12 (Nat.sqrt (2 * Nat.log 2 A.card + 2) + 1) * A.card) := by
  set n := A.card
  set M := A.sup id
  set s := max 12 (Nat.sqrt (2 * Nat.log 2 n + 2) + 1)
  have hs12 : 12 ≤ s := le_max_left _ _
  have hs_sq : 2 * Nat.log 2 n + 2 ≤ s ^ 2 := by
    have h1 : Nat.sqrt (2 * Nat.log 2 n + 2) + 1 ≤ s := le_max_right _ _
    have h2 : 2 * Nat.log 2 n + 2 < (Nat.sqrt (2 * Nat.log 2 n + 2) + 1) ^ 2 := by
      simpa [sq] using Nat.lt_succ_sqrt (2 * Nat.log 2 n + 2)
    have h3 : (Nat.sqrt (2 * Nat.log 2 n + 2) + 1) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left h1 2
    omega
  -- Handle `n = 0` and `n = 1` first
  by_cases hn0 : n = 0
  · have hemp : A = ∅ := Finset.card_eq_zero.mp hn0
    subst hemp
    exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  by_cases hn1 : n = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hn1
    have ha1 : 1 ≤ a := hA a (Finset.mem_singleton_self a)
    have hmult := card_multiples_Icc_ge m a a (by omega)
    rw [Nat.div_self (by omega)] at hmult
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < ((Erdos708Interval m a).filter (a ∣ ·)).card)
    rw [Finset.mem_filter] at hb
    refine ⟨{b}, ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_singleton] at hx; subst hx
      simpa using hb.1
    · simp only [Finset.card_singleton]
      have : 1 ≤ 3 * s * 1 := by omega
      exact this
    · simpa using hb.2
  have hn2 : 2 ≤ n := by omega
  -- Case 1: `9 * n ^ 2 ≤ M` → `3 * n` via Bin-Packing!
  by_cases hlarge : 9 * n ^ 2 ≤ M
  · obtain ⟨B, hBI, hBcard, hBdvd⟩ := erdos708_three_n_of_ge_9n2 hA m hlarge
    refine ⟨B, hBI, le_trans hBcard ?_, hBdvd⟩
    exact Nat.mul_le_mul_right n (by omega)
  push Not at hlarge
  -- Case 2: `M / n < 2 ^ s` → `10 * n + n * s ≤ 3 * s * n` via Dirichlet–Jensen!
  by_cases hmed : M / n < 2 ^ s
  · obtain ⟨B, hBI, hBcard, hBdvd⟩ := erdos708_block_jensen_base2 hA m hn2 (le_of_lt hlarge)
    refine ⟨B, hBI, le_trans hBcard ?_, hBdvd⟩
    have hlog_lt : Nat.log 2 (M / n) < s := by
      by_cases h0 : M / n = 0
      · rw [h0, Nat.log_zero_right]; omega
      · exact (Nat.log_lt_iff_lt_pow (by omega) h0).mpr hmed
    have hle_s : Nat.log 2 (M / n) + 1 ≤ s := hlog_lt
    change 10 * n + n * (Nat.log 2 (M / n) + 1) ≤ 3 * s * n
    have h1 : 10 * n + n * (Nat.log 2 (M / n) + 1) ≤ (10 + s) * n := by nlinarith
    have h2 : (10 + s) * n ≤ 3 * s * n := Nat.mul_le_mul_right n (by omega)
    omega
  -- Case 3: `2 ^ s ≤ M / n` (so `n * 2 ^ s ≤ M`) → `3 * s * n` via Bin-Packing (`k = 3 * s`)!
  push Not at hmed
  set k := 3 * s
  have hk2 : 2 ≤ k := by omega
  apply erdos708_binpack_kn hA m k hk2
  -- Need `(k * n) ^ (k + 1) ≤ M ^ (k - 1)`!
  have hM_ge : n * 2 ^ s ≤ M := by
    calc n * 2 ^ s ≤ n * (M / n) := Nat.mul_le_mul_left n hmed
      _ ≤ M := Nat.mul_div_le M n
  have hk_lt : k < 2 ^ (s / 2) := three_mul_lt_two_pow_half s hs12
  have hn_lt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hexp_le : (k + 1) * (s / 2) + (2 * Nat.log 2 n + 2) ≤ s * (k - 1) := by
    -- `(3*s + 1) * (s / 2) + s^2 ≤ s * (3*s - 1) = 3*s^2 - s`
    have hhalf : 2 * (s / 2) ≤ s := Nat.mul_div_le s 2
    have h1 : 2 * ((3 * s + 1) * (s / 2)) ≤ (3 * s + 1) * s := by
      calc 2 * ((3 * s + 1) * (s / 2)) = (3 * s + 1) * (2 * (s / 2)) := by ring
        _ ≤ (3 * s + 1) * s := Nat.mul_le_mul_left _ hhalf
    have h2 : (3 * s + 1) * s + 2 * s ^ 2 ≤ 2 * (s * (3 * s - 1)) := by
      zify [show 1 ≤ 3 * s by omega]
      nlinarith
    have h3 : 2 * ((k + 1) * (s / 2) + (2 * Nat.log 2 n + 2)) ≤ 2 * (s * (k - 1)) := by
      dsimp [k]
      nlinarith
    omega
  calc
    (k * n) ^ (k + 1) = k ^ (k + 1) * n ^ (k + 1) := mul_pow k n (k + 1)
    _ = k ^ (k + 1) * n ^ 2 * n ^ (k - 1) := by
      rw [mul_assoc, ← pow_add]
      congr 2; omega
    _ ≤ (2 ^ (s / 2)) ^ (k + 1) * (2 ^ (Nat.log 2 n + 1)) ^ 2 * n ^ (k - 1) := by
      apply Nat.mul_le_mul_right
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (le_of_lt hk_lt) _)
        (Nat.pow_le_pow_left (le_of_lt hn_lt) 2)
    _ = 2 ^ ((k + 1) * (s / 2) + (2 * Nat.log 2 n + 2)) * n ^ (k - 1) := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 2; ring
    _ ≤ 2 ^ (s * (k - 1)) * n ^ (k - 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hexp_le)
    _ = (n * 2 ^ s) ^ (k - 1) := by
      rw [pow_mul, mul_comm ((2 ^ s) ^ (k - 1)), ← mul_pow]
    _ ≤ M ^ (k - 1) := Nat.pow_le_pow_left hM_ge (k - 1)

#print axioms dirichlet_exp_sum_bound
#print axioms jensen_prime_sum_bound
#print axioms erdos708_block_jensen_base2
#print axioms erdos708_global_sqrt_log

end PPL176
