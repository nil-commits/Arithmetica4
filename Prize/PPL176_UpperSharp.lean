import Prize.PPL176_UpperGlobal

open scoped BigOperators Nat

namespace PPL176

/-! ## General-Base Dirichlet–Jensen Bound, `O(n √(log n / log log n))` Global Upper Bound, and LP Dual Certificate -/

/-- `1 / 2 ≤ Real.log 2` (since `e < 4 = 2^2`). -/
lemma half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have hexp1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlog := Real.log_lt_log (Real.exp_pos 1) hexp1
  rw [Real.log_exp] at hlog
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [this, Real.log_pow]
    norm_num
  linarith

/-- For any `B ≥ 2`, `(Nat.log 2 B : ℝ) / 2 ≤ Real.log (B : ℝ)`. -/
lemma nat_log_two_div_two_le_real_log {B : ℕ} (hB : 2 ≤ B) :
    ((Nat.log 2 B : ℕ) : ℝ) / 2 ≤ Real.log (B : ℝ) := by
  have hpow : (2 : ℕ) ^ (Nat.log 2 B) ≤ B := Nat.pow_log_le_self 2 (by omega)
  have hpow_r : ((2 : ℝ) ^ (Nat.log 2 B)) ≤ (B : ℝ) := by exact_mod_cast hpow
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 B) := by positivity
  have hlog := Real.log_le_log hpos hpow_r
  rw [Real.log_pow] at hlog
  have hhalf := half_le_log_two
  have hnn : (0 : ℝ) ≤ ((Nat.log 2 B : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **General-Base Dirichlet–Jensen Consecutive-Block Upper Bound (`M ≤ 9 n^2`)**:
    For every `A ⊆ [1, ∞)` with `2 ≤ |A|`, `max(A) ≤ 9 * |A|^2`, and every base `B ≥ 2`:
    `|B_cover| ≤ (6 * B + 7 + (Nat.log 2 (max(A) / |A|) + 1) / Nat.log 2 B + 1) * |A|`. -/
theorem erdos708_block_jensen_general {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) (m B : ℕ)
    (hn : 2 ≤ A.card) (hM_le : A.sup id ≤ 9 * A.card ^ 2) (hB : 2 ≤ B) :
    Erdos708Covers A m
      ((6 * B + 7 + (Nat.log 2 (A.sup id / A.card) + 1) / Nat.log 2 B) * A.card) := by
  set n := A.card
  set M := A.sup id
  set I := Erdos708Interval m M
  set d := Nat.log 2 B
  have hd_pos : 1 ≤ d := Nat.log_pos (by omega) hB
  have hA_ne : A.Nonempty := Finset.card_pos.mp (by omega)
  set K_B := 4 * B / d + 3
  have hKB_le : K_B ≤ 4 * B + 3 := by
    have : 4 * B / d ≤ 4 * B := Nat.div_le_self (4 * B) d
    omega
  by_cases hsmall : M ≤ K_B * n
  · obtain ⟨C, hCI, hCcard, hCdvd⟩ := erdos708_trivial_max_bound hA m
    refine ⟨C, hCI, le_trans hCcard ?_, hCdvd⟩
    have hK_le : K_B ≤ 6 * B + 7 + (Nat.log 2 (M / n) + 1) / d :=
      le_trans hKB_le (le_trans (by omega : 4 * B + 3 ≤ 6 * B + 7) (Nat.le_add_right _ _))
    exact le_trans hsmall (Nat.mul_le_mul_right n hK_le)
  push Not at hsmall
  -- 1. Consecutive block `B₀ = Erdos708Interval m (K_B * n) ⊆ I`
  let B₀ := Erdos708Interval m (K_B * n)
  have hB₀_sub : B₀ ⊆ I := by
    intro b hb
    simp only [B₀, I, Erdos708Interval, Finset.mem_Icc] at hb ⊢
    omega
  have hB₀_card : B₀.card = K_B * n := erdos708Interval_card m (K_B * n)
  have hB₀_val : ∀ p : ℕ, p.Prime → K_B * n / p ≤ ∑ b ∈ B₀, b.factorization p := by
    intro p hp
    have hdvd := factorial_dvd_prod_Icc m (K_B * n)
    have hfac_ne : (K_B * n) ! ≠ 0 := Nat.factorial_ne_zero _
    have hprod_ne : (∏ b ∈ B₀, b) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun b hb => Nat.ne_of_gt (erdos708Interval_pos (hB₀_sub hb)))
    have hle := (Nat.factorization_le_iff_dvd hfac_ne hprod_ne).mpr hdvd p
    rw [Nat.factorization_prod (fun b hb => Nat.ne_of_gt (erdos708Interval_pos (hB₀_sub hb)))] at hle
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply] at hle
    exact le_trans (div_le_factorial_factorization hp) hle
  -- Helper: total interval `I` dominates `A` at every prime `p`.
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
  set P_all := A.biUnion Nat.primeFactors
  -- 2. Small primes `p ≤ 2 * B`: cover each via `exists_cover_prime_by_card` (at most `2 * B` primes!).
  set P_small := P_all.filter (fun p => p ≤ 2 * B)
  have hsmall_cover : ∀ p ∈ P_small, ∃ C ⊆ I,
      C.card ≤ n ∧ ∑ a ∈ A, a.factorization p ≤ ∑ b ∈ C, b.factorization p := by
    intro p hp
    rcases Finset.mem_biUnion.mp (Finset.mem_filter.mp hp).1 with ⟨a, _, hap⟩
    exact exists_cover_prime_by_card (Nat.prime_of_mem_primeFactors hap) (subset_Icc_one_sup hA)
  choose Csmall hCsmall_sub hCsmall_card hCsmall_val using hsmall_cover
  let B₁ := P_small.attach.biUnion (fun ⟨p, hp⟩ => Csmall p hp)
  have hB₁_sub : B₁ ⊆ I := by
    intro b hb
    rcases Finset.mem_biUnion.mp hb with ⟨⟨p, hp⟩, _, hbc⟩
    exact hCsmall_sub p hp hbc
  have hB₁_card : B₁.card ≤ 2 * B * n := by
    have hPsmall_card : P_small.card ≤ 2 * B := by
      have hsub : P_small ⊆ Finset.Icc 1 (2 * B) := by
        intro p hp
        have hf := Finset.mem_filter.mp hp
        rcases Finset.mem_biUnion.mp hf.1 with ⟨a, _, hap⟩
        have hpr := Nat.prime_of_mem_primeFactors hap
        rw [Finset.mem_Icc]
        exact ⟨hpr.pos, hf.2⟩
      calc P_small.card ≤ (Finset.Icc 1 (2 * B)).card := Finset.card_le_card hsub
        _ = 2 * B := by rw [Nat.card_Icc]; omega
    calc
      B₁.card ≤ ∑ x ∈ P_small.attach, (Csmall x.1 x.2).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ P_small.attach, n := Finset.sum_le_sum (fun x _ => hCsmall_card x.1 x.2)
      _ = P_small.card * n := by simp
      _ ≤ 2 * B * n := Nat.mul_le_mul_right n hPsmall_card
  -- 3. Large primes `p > 2 * n`: every `a ∈ A` has `∑_{p > 2n} v_p(a) ≤ 2` since `M ≤ 9 n^2 < (2n)^3`!
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
      have hlt := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2 * n)).mp hlt3
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
  -- 4. Medium primes `2 * B < p ≤ 2 * n` with deficit after `B₀`: apply general-base `jensen_prime_sum_bound`!
  set S := P_all.filter (fun p => 2 * B < p ∧ p ≤ 2 * n ∧
      ∑ b ∈ B₀, b.factorization p < ∑ a ∈ A, a.factorization p)
  have hS_primes : ∀ p ∈ S, p.Prime ∧ B < p := by
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
  have hB₃_card : B₃.card ≤ ((Nat.log 2 (M / n) + 1) / d + 2) * n := by
    have hcard_le_sum : B₃.card ≤ ∑ p ∈ S, ((∑ a ∈ A, a.factorization p) - K_B * n / p) := by
      calc
        B₃.card ≤ ∑ x ∈ S.attach, (Cdef x.1 x.2).card := Finset.card_biUnion_le
        _ ≤ ∑ x ∈ S.attach, ((∑ a ∈ A, a.factorization x.1) - ∑ b ∈ B₀, b.factorization x.1) :=
          Finset.sum_le_sum (fun x _ => hCdef_card x.1 x.2)
        _ = ∑ p ∈ S, ((∑ a ∈ A, a.factorization p) - ∑ b ∈ B₀, b.factorization p) :=
          Finset.sum_attach S (fun p => (∑ a ∈ A, a.factorization p) - ∑ b ∈ B₀, b.factorization p)
        _ ≤ ∑ p ∈ S, ((∑ a ∈ A, a.factorization p) - K_B * n / p) := by
          apply Finset.sum_le_sum
          intro p hp
          have hge := hB₀_val p (hS_primes p hp).1
          omega
    -- Bound in `ℝ` via `jensen_prime_sum_bound`!
    have hreal_le : ((∑ p ∈ S, ((∑ a ∈ A, a.factorization p) - K_B * n / p) : ℕ) : ℝ) ≤
        ((((Nat.log 2 (M / n) + 1) / d + 2) * n : ℕ) : ℝ) := by
      have hjen := jensen_prime_sum_bound (B := B) (M := M) hB hA_ne
        (subset_Icc_one_sup hA) hS_primes
      have hB_gt1 : (1 : ℝ) < (B : ℝ) := by
        have : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
        linarith
      have hlogB_pos : (0 : ℝ) < Real.log (B : ℝ) := Real.log_pos hB_gt1
      have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hd_rpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hsub_cast : ((∑ p ∈ S, ((∑ a ∈ A, a.factorization p) - K_B * n / p) : ℕ) : ℝ) =
          (∑ p ∈ S, ∑ a ∈ A, (a.factorization p : ℝ)) - ∑ p ∈ S, ((K_B * n / p : ℕ) : ℝ) := by
        rw [Nat.cast_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        have hlt := (Finset.mem_filter.mp hp).2.2.2
        have hge := hB₀_val p (hS_primes p hp).1
        rw [Nat.cast_sub (by omega), Nat.cast_sum]
      rw [hsub_cast]
      -- For `p > 2 * B`, `1 / (p - B) ≤ 2 / p`.
      have hinv : ∑ p ∈ S, (1 / ((p : ℝ) - (B : ℝ))) ≤ 2 * ∑ p ∈ S, (1 / (p : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p hp
        have hp2B : (2 : ℝ) * (B : ℝ) < (p : ℝ) := by
          have : 2 * B < p := (Finset.mem_filter.mp hp).2.1
          exact_mod_cast this
        have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
        have hpmB_pos : (0 : ℝ) < (p : ℝ) - (B : ℝ) := by linarith
        rw [mul_one_div, div_le_div_iff₀ hpmB_pos hp_pos]
        linarith
      -- Coefficient bound: `2 * (B - 1) / log B ≤ 4 * B / d ≤ K_B - 2` (since `K_B = 4 * B / d + 3`)!
      have hcoeff : 2 * ((B : ℝ) - 1) / Real.log (B : ℝ) ≤ ((K_B - 2 : ℕ) : ℝ) := by
        have hlogB_ge : (d : ℝ) / 2 ≤ Real.log (B : ℝ) := nat_log_two_div_two_le_real_log hB
        have h1 : 2 * ((B : ℝ) - 1) / Real.log (B : ℝ) ≤ 4 * (B : ℝ) / (d : ℝ) := by
          rw [div_le_div_iff₀ hlogB_pos hd_rpos]
          nlinarith
        have h2 : 4 * (B : ℝ) / (d : ℝ) ≤ ((4 * B / d + 1 : ℕ) : ℝ) := by
          rw [div_le_iff₀ hd_rpos]
          have hdm : 4 * B < (4 * B / d + 1) * d := by
            have := Nat.div_add_mod (4 * B) d
            have := Nat.mod_lt (4 * B) (by omega : 0 < d)
            nlinarith
          have : (4 * B : ℝ) < ((4 * B / d + 1) * d : ℕ) := by exact_mod_cast hdm
          push_cast at this ⊢
          linarith
        have hKB_sub : K_B - 2 = 4 * B / d + 1 := by
          show (4 * B / d + 1 + 2) - 2 = 4 * B / d + 1
          exact Nat.add_sub_cancel _ 2
        rw [hKB_sub]
        exact le_trans h1 h2
      -- Block lower bound: `(K_B - 2) * n * ∑_{p ∈ S} 1/p ≤ ∑_{p ∈ S} (K_B * n / p : ℕ)`.
      have hblock_ge : ((K_B - 2 : ℕ) : ℝ) * (n : ℝ) * ∑ p ∈ S, (1 / (p : ℝ)) ≤
          ∑ p ∈ S, ((K_B * n / p : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p hp
        have hp_le : p ≤ 2 * n := (Finset.mem_filter.mp hp).2.2.1
        have hp_pos : 0 < p := (hS_primes p hp).1.pos
        have hp_rpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
        have hdm : K_B * n < (K_B * n / p + 1) * p := by
          have := Nat.div_add_mod (K_B * n) p
          have := Nat.mod_lt (K_B * n) hp_pos
          nlinarith
        have hdm_r : (K_B : ℝ) * (n : ℝ) < ((K_B * n / p : ℕ) : ℝ) * (p : ℝ) + (p : ℝ) := by
          have : ((K_B * n : ℕ) : ℝ) < (((K_B * n / p + 1) * p : ℕ) : ℝ) := by exact_mod_cast hdm
          push_cast at this
          linarith
        have hp_le_r : (p : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hp_le
        have hKB2 : ((K_B - 2 : ℕ) : ℝ) = (K_B : ℝ) - 2 := by
          have : 2 ≤ K_B := le_trans (by norm_num : 2 ≤ 3) (Nat.le_add_left 3 (4 * B / d))
          exact Nat.cast_sub this
        rw [hKB2, mul_one_div, div_le_iff₀ hp_rpos]
        nlinarith
      -- Log term bound: `log(M / n) / log B ≤ (Nat.log 2 (M / n) + 1) / d + 2`.
      have hlog_mn : Real.log ((M : ℝ) / (n : ℝ)) / Real.log (B : ℝ) ≤
          (((Nat.log 2 (M / n) + 1) / d + 2 : ℕ) : ℝ) := by
        -- Use `log B ≥ d * log 2` (from `2 ^ d ≤ B`)!
        have hlogB_ge2 : (d : ℝ) * Real.log 2 ≤ Real.log (B : ℝ) := by
          have hpow : (2 : ℕ) ^ d ≤ B := Nat.pow_log_le_self 2 (by omega)
          have hpow_r : ((2 : ℝ) ^ d) ≤ (B : ℝ) := by exact_mod_cast hpow
          have h := Real.log_le_log (by positivity) hpow_r
          rwa [Real.log_pow] at h
        have hlog_num : Real.log ((M : ℝ) / (n : ℝ)) ≤ ((Nat.log 2 (M / n) + 1 : ℕ) : ℝ) * Real.log 2 := by
          have h1 : M / n < 2 ^ (Nat.log 2 (M / n) + 1) := Nat.lt_pow_succ_log_self (by omega) _
          have h2 : M < (M / n + 1) * n := by
            have := Nat.div_add_mod M n
            have := Nat.mod_lt M (by omega : 0 < n)
            nlinarith
          have h3 : (M : ℝ) / (n : ℝ) ≤ ((2 ^ (Nat.log 2 (M / n) + 1) : ℕ) : ℝ) := by
            rw [div_le_iff₀ hn_pos]
            have hle_nat : M ≤ 2 ^ (Nat.log 2 (M / n) + 1) * n := by
              exact le_trans (le_of_lt h2) (Nat.mul_le_mul_right n h1)
            exact_mod_cast hle_nat
          have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
          have hl := Real.log_le_log (div_pos hM_pos hn_pos) h3
          rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hl
          exact hl
        have hquot : ((Nat.log 2 (M / n) + 1 : ℕ) : ℝ) / (d : ℝ) ≤
            (((Nat.log 2 (M / n) + 1) / d + 2 : ℕ) : ℝ) := by
          rw [div_le_iff₀ hd_rpos]
          have hdm : Nat.log 2 (M / n) + 1 < ((Nat.log 2 (M / n) + 1) / d + 1) * d := by
            have := Nat.div_add_mod (Nat.log 2 (M / n) + 1) d
            have := Nat.mod_lt (Nat.log 2 (M / n) + 1) (by omega : 0 < d)
            nlinarith
          have : ((Nat.log 2 (M / n) + 1 : ℕ) : ℝ) <
              ((((Nat.log 2 (M / n) + 1) / d + 1) * d : ℕ) : ℝ) := by exact_mod_cast hdm
          push_cast at this ⊢
          nlinarith
        rw [div_le_iff₀ hlogB_pos]
        have hstep1 : ((Nat.log 2 (M / n) + 1 : ℕ) : ℝ) * Real.log 2 ≤
            (((Nat.log 2 (M / n) + 1) / d + 2 : ℕ) : ℝ) * ((d : ℝ) * Real.log 2) := by
          have hq := (div_le_iff₀ hd_rpos).mp hquot
          have := mul_le_mul_of_nonneg_right hq (le_of_lt hlog2_pos)
          linarith
        have hstep2 : (((Nat.log 2 (M / n) + 1) / d + 2 : ℕ) : ℝ) * ((d : ℝ) * Real.log 2) ≤
            (((Nat.log 2 (M / n) + 1) / d + 2 : ℕ) : ℝ) * Real.log (B : ℝ) :=
          mul_le_mul_of_nonneg_left hlogB_ge2 (Nat.cast_nonneg _)
        exact le_trans hlog_num (le_trans hstep1 hstep2)
      -- Combine!
      have hsum_inv_nonneg : 0 ≤ ∑ p ∈ S, (1 / (p : ℝ)) :=
        Finset.sum_nonneg (fun p _ => by positivity)
      have hB1_nonneg : (0 : ℝ) ≤ (B : ℝ) - 1 := by linarith
      have hsecond : (((B : ℝ) - 1) * (n : ℝ) * ∑ p ∈ S, (1 / ((p : ℝ) - (B : ℝ)))) / Real.log (B : ℝ) ≤
          ((K_B - 2 : ℕ) : ℝ) * (n : ℝ) * ∑ p ∈ S, (1 / (p : ℝ)) := by
        calc
          (((B : ℝ) - 1) * (n : ℝ) * ∑ p ∈ S, (1 / ((p : ℝ) - (B : ℝ)))) / Real.log (B : ℝ)
              ≤ (((B : ℝ) - 1) * (n : ℝ) * (2 * ∑ p ∈ S, (1 / (p : ℝ)))) / Real.log (B : ℝ) :=
                div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hinv (mul_nonneg hB1_nonneg (le_of_lt hn_pos)))
                  (le_of_lt hlogB_pos)
          _ = (2 * ((B : ℝ) - 1) / Real.log (B : ℝ)) * ((n : ℝ) * ∑ p ∈ S, (1 / (p : ℝ))) := by ring
          _ ≤ ((K_B - 2 : ℕ) : ℝ) * ((n : ℝ) * ∑ p ∈ S, (1 / (p : ℝ))) :=
                mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (le_of_lt hn_pos) hsum_inv_nonneg)
          _ = ((K_B - 2 : ℕ) : ℝ) * (n : ℝ) * ∑ p ∈ S, (1 / (p : ℝ)) := by ring
      have hfirst : ((n : ℝ) * Real.log ((M : ℝ) / (n : ℝ))) / Real.log (B : ℝ) ≤
          ((((Nat.log 2 (M / n) + 1) / d + 2) * n : ℕ) : ℝ) := by
        rw [Nat.cast_mul, mul_div_assoc]
        have := mul_le_mul_of_nonneg_left hlog_mn (le_of_lt hn_pos)
        linarith
      have hsplit_jen :
          ((n : ℝ) * Real.log ((M : ℝ) / (n : ℝ)) +
            ((B : ℝ) - 1) * (n : ℝ) * ∑ p ∈ S, (1 / ((p : ℝ) - (B : ℝ)))) / Real.log (B : ℝ) =
          ((n : ℝ) * Real.log ((M : ℝ) / (n : ℝ))) / Real.log (B : ℝ) +
            (((B : ℝ) - 1) * (n : ℝ) * ∑ p ∈ S, (1 / ((p : ℝ) - (B : ℝ)))) / Real.log (B : ℝ) := by
        ring
      rw [hsplit_jen] at hjen
      linarith
    exact le_trans hcard_le_sum (Nat.cast_le.mp hreal_le)
  -- 5. Assemble `B_cov = B₀ ∪ B₁ ∪ B₂ ∪ B₃`!
  let B_cov := ((B₀ ∪ B₁) ∪ B₂) ∪ B₃
  refine ⟨B_cov, ?_, ?_, ?_⟩
  · exact Finset.union_subset (Finset.union_subset (Finset.union_subset hB₀_sub hB₁_sub) hB₂_sub) hB₃_sub
  · have htot : B_cov.card ≤ B₀.card + B₁.card + B₂.card + B₃.card := by
      have h1 := Finset.card_union_le ((B₀ ∪ B₁) ∪ B₂) B₃
      have h2 := Finset.card_union_le (B₀ ∪ B₁) B₂
      have h3 := Finset.card_union_le B₀ B₁
      change (((B₀ ∪ B₁) ∪ B₂) ∪ B₃).card ≤ _
      omega
    have hsum_k : K_B * n + 2 * B * n + 2 * n + ((Nat.log 2 (M / n) + 1) / d + 2) * n ≤
        (6 * B + 7 + (Nat.log 2 (M / n) + 1) / d) * n := by
      have : K_B + 2 * B + 2 + ((Nat.log 2 (M / n) + 1) / d + 2) ≤
          6 * B + 7 + (Nat.log 2 (M / n) + 1) / d := by omega
      have := Nat.mul_le_mul_right n this
      linarith
    omega
  · apply prod_dvd_prod_of_factorization_le
    · intro a ha; have := hA a ha; omega
    · intro b hb
      have hBI := (Finset.union_subset (Finset.union_subset (Finset.union_subset hB₀_sub hB₁_sub) hB₂_sub) hB₃_sub) hb
      exact Nat.ne_of_gt (erdos708Interval_pos hBI)
    · intro p hp
      by_cases hp_in : p ∈ P_all
      · by_cases hp_sm : p ≤ 2 * B
        · have hp_mem : p ∈ P_small := Finset.mem_filter.mpr ⟨hp_in, hp_sm⟩
          have hsub : Csmall p hp_mem ⊆ B_cov := by
            intro b hb
            have hb1 : b ∈ B₁ := Finset.mem_biUnion.mpr ⟨⟨p, hp_mem⟩, Finset.mem_attach _ _, hb⟩
            exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hb1))
          exact le_trans (hCsmall_val p hp_mem)
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))
        · push Not at hp_sm
          by_cases hp_big : 2 * n < p
          · have hp_mem : p ∈ P_big := Finset.mem_filter.mpr ⟨hp_in, hp_big⟩
            have hsub : Cbig p hp_mem ⊆ B_cov := by
              intro b hb
              have hb2 : b ∈ B₂ := Finset.mem_biUnion.mpr ⟨⟨p, hp_mem⟩, Finset.mem_attach _ _, hb⟩
              exact Finset.mem_union_left _ (Finset.mem_union_right _ hb2)
            exact le_trans (hCbig_val p hp_mem)
              (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))
          · push Not at hp_big
            by_cases hdef : ∑ b ∈ B₀, b.factorization p < ∑ a ∈ A, a.factorization p
            · have hpS : p ∈ S := Finset.mem_filter.mpr ⟨hp_in, hp_sm, hp_big, hdef⟩
              have hdisj : Disjoint B₀ (Cdef p hpS) :=
                Finset.disjoint_of_subset_right (hCdef_sub p hpS) Finset.disjoint_sdiff
              have hsub : B₀ ∪ Cdef p hpS ⊆ B_cov := by
                apply Finset.union_subset
                · exact Finset.Subset.trans Finset.subset_union_left
                    (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)
                · intro b hb
                  exact Finset.mem_union_right _
                    (Finset.mem_biUnion.mpr ⟨⟨p, hpS⟩, Finset.mem_attach _ _, hb⟩)
              have hsum_u : ∑ b ∈ B₀ ∪ Cdef p hpS, b.factorization p =
                  ∑ b ∈ B₀, b.factorization p + ∑ b ∈ Cdef p hpS, b.factorization p :=
                Finset.sum_union hdisj
              have hle_B : ∑ b ∈ B₀ ∪ Cdef p hpS, b.factorization p ≤
                  ∑ b ∈ B_cov, b.factorization p :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
              have hv := hCdef_val p hpS
              omega
            · push Not at hdef
              have hsub : B₀ ⊆ B_cov := Finset.Subset.trans Finset.subset_union_left
                (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)
              exact le_trans hdef (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))
      · have hzero : ∀ a ∈ A, a.factorization p = 0 := by
          intro a ha
          have hnot : p ∉ a.primeFactors := fun h => hp_in (Finset.mem_biUnion.mpr ⟨a, ha, h⟩)
          rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hnot
          exact hnot
        rw [Finset.sum_eq_zero hzero]
        exact Nat.zero_le _

/-- Elementary inequality: `x < 2 ^ (x / 2)` for all `x ≥ 6`. -/
lemma lt_two_pow_half_of_ge_six (x : ℕ) (hx : 6 ≤ x) : x < 2 ^ (x / 2) := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    by_cases h8 : x < 8
    · interval_cases x <;> norm_num
    · have hih := ih (x - 2) (by omega) (by omega)
      have hdiv : x / 2 = (x - 2) / 2 + 1 := by omega
      rw [hdiv, pow_succ]
      omega

/-- **UNCONDITIONAL GLOBAL `O(n √(log n / log log n))` UPPER BOUND (State-of-the-Art Asymptotic Rate)**:
    For ALL `A ⊆ [1, ∞)` of ANY size `n = |A|` and ALL intervals `I = {m + 1, ..., m + max(A)}`:
    `∃ B ⊆ I, |B| ≤ 24 * max 16 (Nat.sqrt (Nat.log 2 |A| / max 1 (Nat.log 2 (Nat.log 2 |A|))) + 1) * |A| ∧ ∏ A ∣ ∏ B`. -/
theorem erdos708_global_sqrt_log_div_loglog {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) (m : ℕ) :
    Erdos708Covers A m
      (24 * max 16 (Nat.sqrt (Nat.log 2 A.card / max 1 (Nat.log 2 (Nat.log 2 A.card))) + 1) * A.card) := by
  set n := A.card
  set M := A.sup id
  set L := Nat.log 2 n
  set LL := max 1 (Nat.log 2 L)
  set q := Nat.sqrt (L / LL) + 1
  -- Case 0: `L < 1024` → our already-proved `erdos708_global_sqrt_log` gives `≤ 138 * n ≤ 384 * n`!
  by_cases hL_small : L < 1024
  · obtain ⟨B, hBI, hBcard, hBdvd⟩ := erdos708_global_sqrt_log hA m
    refine ⟨B, hBI, le_trans hBcard ?_, hBdvd⟩
    have hsq : Nat.sqrt (2 * L + 2) ≤ 46 := by
      have : 2 * L + 2 < 47 * 47 := by omega
      have hle := Nat.sqrt_le_sqrt (by omega : 2 * L + 2 ≤ 46 * 46 + 92)
      have hlt : Nat.sqrt (2 * L + 2) < 47 := by
        rw [Nat.sqrt_lt']
        omega
      omega
    have hmax1 : max 12 (Nat.sqrt (2 * L + 2) + 1) ≤ 47 := by omega
    have hmax2 : 16 ≤ max 16 q := le_max_left _ _
    have hmul_le : 3 * max 12 (Nat.sqrt (2 * L + 2) + 1) ≤ 24 * max 16 q := by omega
    exact Nat.mul_le_mul_right n hmul_le
  push Not at hL_small
  -- Now `L ≥ 1024`, so `n ≥ 2 ^ 1024 ≥ 2` and `LL = Nat.log 2 L ≥ 10`!
  have hn2 : 2 ≤ n := by
    have hn_ne : n ≠ 0 := by
      intro h; simp [L, h] at hL_small
    have h1 : 2 ^ 1 ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn_ne
    omega
  have hLL_ge10 : 10 ≤ Nat.log 2 L := by
    have : 2 ^ 10 ≤ L := by omega
    exact (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr this
  have hLL_eq : LL = Nat.log 2 L := max_eq_right (by omega)
  have hLL_ge10' : 10 ≤ LL := by omega
  have hL_pow : 2 ^ LL ≤ L := by
    rw [hLL_eq]
    exact Nat.pow_log_le_self 2 (by omega)
  have hL_lt : L < 2 ^ (LL + 1) := by
    rw [hLL_eq]
    exact Nat.lt_pow_succ_log_self (by omega) L
  -- Show `LL / 4 ≤ Nat.log 2 q` and `q ≥ 11`!
  have hLL_lt_pow : LL < 2 ^ (LL / 2) := lt_two_pow_half_of_ge_six LL (by omega)
  have hq_ge_pow : 2 ^ (LL / 4) ≤ q := by
    have h1 : 2 ^ (2 * (LL / 4)) * LL ≤ L := by
      have hle1 : 2 * (LL / 4) ≤ LL / 2 := by omega
      calc
        2 ^ (2 * (LL / 4)) * LL ≤ 2 ^ (LL / 2) * 2 ^ (LL / 2) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hle1) (le_of_lt hLL_lt_pow)
        _ = 2 ^ (LL / 2 + LL / 2) := (pow_add 2 _ _).symm
        _ ≤ 2 ^ LL := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ L := hL_pow
    have h2 : (2 ^ (LL / 4)) ^ 2 ≤ L / LL := by
      rw [← pow_mul, mul_comm, Nat.le_div_iff_mul_le (by omega)]
      exact h1
    have h3 : 2 ^ (LL / 4) ≤ Nat.sqrt (L / LL) := Nat.le_sqrt.mpr (by simpa [sq] using h2)
    omega
  have hq_ge11 : 11 ≤ q := by
    -- `LL ≤ 2 ^ (LL / 2)` and `L ≥ 1024`, let's show `100 ≤ L / LL`!
    -- Wait: `L / LL ≥ 2 ^ (LL / 2) ≥ 2 ^ 5 = 32` is NOT enough for 100! Wait: check `LL = 10`:
    -- `L ≥ 1024`, `LL = 10` => `1024 / 10 = 102 ≥ 100`!
    -- For `LL ≥ 11`: `L ≥ 2 ^ LL`, `LL < 2 ^ (LL / 2)`, wait: `2^LL / LL ≥ 2^11 / 11 = 186 ≥ 100`!
    -- Prove `100 * LL ≤ L`!
    have h100 : 100 * LL ≤ L := by
      by_cases h11 : LL = 10
      · omega
      · have hLL11 : 11 ≤ LL := by omega
        -- For `LL ≥ 11`: `100 * LL ≤ 2 ^ LL ≤ L`!
        have hpow_ge : 100 * LL ≤ 2 ^ LL := by
          have haux : ∀ x : ℕ, 11 ≤ x → 100 * x ≤ 2 ^ x := by
            intro x hx
            induction x, hx using Nat.le_induction with
            | base => norm_num
            | succ m hm ih =>
              rw [pow_succ]
              omega
          exact haux LL hLL11
        exact le_trans hpow_ge hL_pow
    have hdiv100 : 100 ≤ L / LL := (Nat.le_div_iff_mul_le (by omega)).mpr h100
    have hsq10 : 10 ≤ Nat.sqrt (L / LL) := Nat.le_sqrt.mpr (by omega)
    omega
  have hq2 : 2 ≤ q := by omega
  have hd_ge : LL / 4 ≤ Nat.log 2 q := (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr hq_ge_pow
  have hd_pos : 1 ≤ Nat.log 2 q := by omega
  have h6d_ge : LL ≤ 6 * Nat.log 2 q := by omega
  -- Case 1: `9 * n ^ 2 ≤ M` → `3 * n` via Bin-Packing!
  by_cases hlarge : 9 * n ^ 2 ≤ M
  · obtain ⟨B, hBI, hBcard, hBdvd⟩ := erdos708_three_n_of_ge_9n2 hA m hlarge
    refine ⟨B, hBI, le_trans hBcard ?_, hBdvd⟩
    have : 16 ≤ max 16 q := le_max_left _ _
    exact Nat.mul_le_mul_right n (by omega)
  push Not at hlarge
  -- Set threshold `s = q * LL`!
  set s := q * LL
  -- Case 2: `M / n < 2 ^ s` → general-base Dirichlet–Jensen with base `B = q`!
  by_cases hmed : M / n < 2 ^ s
  · obtain ⟨B, hBI, hBcard, hBdvd⟩ := erdos708_block_jensen_general hA m q hn2 (le_of_lt hlarge) hq2
    refine ⟨B, hBI, le_trans hBcard ?_, hBdvd⟩
    have hlog_le : Nat.log 2 (M / n) + 1 ≤ s := by
      by_cases h0 : M / n = 0
      · rw [h0, Nat.log_zero_right]; dsimp [s]; nlinarith
      · exact (Nat.log_lt_iff_lt_pow (by omega) h0).mpr hmed
    have hdiv_le : (Nat.log 2 (M / n) + 1) / Nat.log 2 q ≤ 6 * q := by
      rw [Nat.div_le_iff_le_mul_add_pred hd_pos]
      have h1 : s ≤ Nat.log 2 q * (6 * q) := by
        dsimp [s]
        calc q * LL ≤ q * (6 * Nat.log 2 q) := Nat.mul_le_mul_left q h6d_ge
          _ = Nat.log 2 q * (6 * q) := by ring
      omega
    have hmax_ge : q ≤ max 16 q := le_max_right _ _
    have hcoef_le : 6 * q + 7 + (Nat.log 2 (M / n) + 1) / Nat.log 2 q ≤ 24 * max 16 q := by omega
    exact Nat.mul_le_mul_right n hcoef_le
  -- Case 3: `2 ^ s ≤ M / n` (so `n * 2 ^ s ≤ M`) → Bin-Packing with `k = 24 * max 16 q`!
  push Not at hmed
  set k := 24 * max 16 q
  have hk2 : 2 ≤ k := by omega
  apply erdos708_binpack_kn hA m k hk2
  have hM_ge : n * 2 ^ s ≤ M := by
    calc n * 2 ^ s ≤ n * (M / n) := Nat.mul_le_mul_left n hmed
      _ ≤ M := Nat.mul_div_le M n
  -- Bound `k < 2 ^ (2 * LL)` (since `q ≤ L < 2 ^ (LL + 1)` and `max 16 q ≤ 2 * q`? Wait: `q ≥ 11`, so `max 16 q ≤ 2 * q`,
  -- hence `k = 24 * max 16 q ≤ 48 * q < 64 * L < 64 * 2 ^ (LL + 1) = 2 ^ (LL + 7) ≤ 2 ^ (2 * LL)` since `LL ≥ 10`!!)
  have hq_le_L : q ≤ L := by
    have h1 : Nat.sqrt (L / LL) ≤ L / LL := Nat.sqrt_le_self _
    have h2 : L / LL + 1 ≤ L := by
      have : L / LL ≤ L / 2 := Nat.div_le_div_left (by omega) (by omega)
      omega
    omega
  have hk_lt : k < 2 ^ (2 * LL) := by
    have hmax_le : max 16 q ≤ 2 * q := by omega
    have hk_le : k ≤ 48 * q := by dsimp [k]; omega
    have h1 : 48 * q < 64 * 2 ^ (LL + 1) := by nlinarith
    have h2 : 64 * 2 ^ (LL + 1) = 2 ^ (LL + 7) := by
      have : (64 : ℕ) = 2 ^ 6 := by norm_num
      rw [this, ← pow_add]
      congr 1; omega
    have h3 : 2 ^ (LL + 7) ≤ 2 ^ (2 * LL) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hn_lt : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by omega) n
  -- Check exponent inequality: `(k + 1) * (2 * LL) + (2 * L + 2) ≤ s * (k - 1)`!
  have hL_le_sq : L ≤ q ^ 2 * LL := by
    have hlt_sq : L / LL < q ^ 2 := by
      simpa [sq, q] using Nat.lt_succ_sqrt (L / LL)
    have hdm := Nat.div_add_mod L LL
    have hml := Nat.mod_lt L (by omega : 0 < LL)
    nlinarith
  have hexp_le : (k + 1) * (2 * LL) + (2 * L + 2) ≤ s * (k - 1) := by
    have hk_ge : 24 * q ≤ k := by dsimp [k]; have := le_max_right 16 q; omega
    have hk_ge_16 : 384 ≤ k := by dsimp [k]; have := le_max_left 16 q; omega
    -- `s * (k - 1) = q * LL * (k - 1) ≥ 11 * LL * (k - 1)`!
    -- Wait: `2 * L + 2 ≤ 2 * q ^ 2 * LL + 2 ≤ 3 * q ^ 2 * LL`!
    -- And `k * q * LL ≥ 24 * q ^ 2 * LL`, while `(k + 1) * (2 * LL) = 2 * k * LL + 2 * LL`!
    -- Compare `(k + 1) * 2 * LL + 2 * q ^ 2 * LL + 2` vs `q * LL * (k - 1)`:
    -- Since `q ≥ 11`, `q * (k - 1) = q * k - q`, and `2 * q ^ 2 ≤ k * q / 12` (since `24 * q ≤ k`)!
    -- So `q * LL * (k - 1) ≥ 11 * k * LL - q * LL`? Better: split `q * (k - 1) = (q - 3) * k + 3 * k - q`:
    -- Wait: `q * k = 3 * k + (q - 3) * k ≥ 3 * k + 8 * k`!
    -- Even cleaner with `nlinarith`:
    -- `2 * q^2 * LL ≤ k * q * LL / 12` => multiply whole inequality? No, `24 * q ≤ k ⟹ 2 * q^2 ≤ q * k / 12`,
    -- just note `2 * q ≤ k / 12`, wait: `q * k ≥ 24 * q ^ 2` so `2 * q ^ 2 ≤ q * k - 22 * q ^ 2`!
    have h1 : 2 * q ^ 2 ≤ q * k - 22 * q ^ 2 := by
      have : 24 * q ^ 2 ≤ q * k := by nlinarith
      omega
    have h2 : 3 * k ≤ 8 * k := by omega
    -- Direct `nlinarith` on `q ≥ 11`, `LL ≥ 10`, `24 * q ≤ k`, `L ≤ q ^ 2 * LL`:
    -- Need `(k + 1) * (2 * LL) + (2 * L + 2) ≤ q * LL * (k - 1)`
    -- Rewrite LHS ≤ `(2 * k + 2 + 2 * q^2 + 1) * LL` (since `2 ≤ LL`),
    -- and RHS = `(q * k - q) * LL`!
    -- So we only need `2 * k + 2 * q ^ 2 + 3 ≤ q * k - q`!
    have hcore : 2 * k + 2 * q ^ 2 + 3 + q ≤ q * k := by
      -- Since `q ≥ 11` and `24 * q ≤ k`: `2 * q^2 ≤ q * k / 12`, i.e., `12 * (2 * q^2) ≤ q * k`!
      -- Split `q * k = 3 * k + (q - 3) * k`: since `q ≥ 11`, `(q - 3) * k ≥ 8 * k ≥ 8 * 24 * q`?
      -- Even simpler: `nlinarith` with `q ≥ 11` and `24 * q ≤ k`!
      -- Wait: `q * k - 2 * k - 2 * q^2 - q = (q - 2) * k - 2 * q^2 - q ≥ (q - 2) * 24 * q - 2 * q^2 - q`
      -- = `22 * q^2 - 49 * q ≥ 22 * 11 * q - 49 * q = 193 * q ≥ 3`!
      nlinarith
    have hmul : (2 * k + 2 * q ^ 2 + 3) * LL ≤ q * (k - 1) * LL := by
      have hsub : q * (k - 1) = q * k - q := by
        rw [Nat.mul_sub_left_distrib, mul_one]
      have hle : 2 * k + 2 * q ^ 2 + 3 ≤ q * (k - 1) := by omega
      exact Nat.mul_le_mul_right LL hle
    dsimp [s]
    nlinarith
  calc
    (k * n) ^ (k + 1) = k ^ (k + 1) * n ^ (k + 1) := mul_pow k n (k + 1)
    _ = k ^ (k + 1) * n ^ 2 * n ^ (k - 1) := by
      rw [mul_assoc, ← pow_add]
      congr 2; omega
    _ ≤ (2 ^ (2 * LL)) ^ (k + 1) * (2 ^ (L + 1)) ^ 2 * n ^ (k - 1) := by
      apply Nat.mul_le_mul_right
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (le_of_lt hk_lt) _)
        (Nat.pow_le_pow_left (le_of_lt hn_lt) 2)
    _ = 2 ^ ((k + 1) * (2 * LL) + (2 * L + 2)) * n ^ (k - 1) := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 2; ring
    _ ≤ 2 ^ (s * (k - 1)) * n ^ (k - 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hexp_le)
    _ = (n * 2 ^ s) ^ (k - 1) := by
      rw [pow_mul, mul_comm ((2 ^ s) ^ (k - 1)), ← mul_pow]
    _ ≤ M ^ (k - 1) := Nat.pow_le_pow_left hM_ge (k - 1)

/-- **LP Weak Duality Certificate for Erdős Problem #708**:
    For ANY non-negative completely additive weight function `W : ℕ → ℝ`, ANY `A ⊆ [1, ∞)`,
    and ANY covering subset `B ⊆ I` (`∏ A ∣ ∏ B`):
    `∑ a ∈ A, W a - ∑ b ∈ I, max 0 (W b - 1) ≤ B.card`. -/
theorem erdos708_dual_lower_bound {A B I : Finset ℕ} {W : ℕ → ℝ}
    (hW0 : W 1 = 0) (hW_mul : ∀ x y, 1 ≤ x → 1 ≤ y → W (x * y) = W x + W y)
    (hW_nn : ∀ x, 1 ≤ x → 0 ≤ W x)
    (hA : ∀ a ∈ A, 1 ≤ a) (hI : ∀ b ∈ I, 1 ≤ b)
    (hBI : B ⊆ I) (hdvd : (∏ a ∈ A, a) ∣ (∏ b ∈ B, b)) :
    (∑ a ∈ A, W a) - (∑ b ∈ I, max (0 : ℝ) (W b - 1)) ≤ (B.card : ℝ) := by
  have hW_prod : ∀ S : Finset ℕ, (∀ x ∈ S, 1 ≤ x) → W (∏ x ∈ S, x) = ∑ x ∈ S, W x := by
    intro S hS
    induction S using Finset.induction_on with
    | empty => simpa using hW0
    | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.sum_insert hx]
      have hx1 : 1 ≤ x := hS x (Finset.mem_insert_self x s)
      have hs1 : 1 ≤ ∏ y ∈ s, y := Finset.one_le_prod' (fun y hy => hS y (Finset.mem_insert_of_mem hy))
      rw [hW_mul x (∏ y ∈ s, y) hx1 hs1, ih (fun y hy => hS y (Finset.mem_insert_of_mem hy))]
  have hprodA_pos : 1 ≤ ∏ a ∈ A, a := Finset.one_le_prod' hA
  have hprodB_pos : 1 ≤ ∏ b ∈ B, b := Finset.one_le_prod' (fun b hb => hI b (hBI hb))
  rcases hdvd with ⟨q, hq⟩
  have hq1 : 1 ≤ q := by
    by_contra h
    have hq0 : q = 0 := by omega
    subst hq0; simp at hq; omega
  have hWA_le_WB : ∑ a ∈ A, W a ≤ ∑ b ∈ B, W b := by
    rw [← hW_prod A hA, ← hW_prod B (fun b hb => hI b (hBI hb)), hq,
        hW_mul (∏ a ∈ A, a) q hprodA_pos hq1]
    linarith [hW_nn q hq1]
  have hWB_le : ∑ b ∈ B, W b ≤ (B.card : ℝ) + ∑ b ∈ B, max (0 : ℝ) (W b - 1) := by
    have h1 : ∑ b ∈ B, W b ≤ ∑ b ∈ B, (1 + max (0 : ℝ) (W b - 1)) := by
      apply Finset.sum_le_sum
      intro b _
      have := le_max_right (0 : ℝ) (W b - 1)
      linarith
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    exact h1
  have hsub_le : ∑ b ∈ B, max (0 : ℝ) (W b - 1) ≤ ∑ b ∈ I, max (0 : ℝ) (W b - 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg hBI (fun _ _ _ => le_max_left _ _)
  linarith

#print axioms erdos708_block_jensen_general
#print axioms erdos708_global_sqrt_log_div_loglog
#print axioms erdos708_dual_lower_bound

end PPL176
