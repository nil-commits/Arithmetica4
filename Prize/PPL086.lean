import Prize.PPL086_Constructions
import RHDirect.Stage8MertensTheorems
import RHDirect.Stage8ExplicitPrimeBounds

/-!
# PPL 086 (Erdős Problem #470): Weird & Primitive Weird Numbers — Master Theorem File

This module combines our structural theory (`Prize.PPL086_Defs`), Kravitz/Melfi constructions
(`Prize.PPL086_Constructions`), and unconditional analytic number theory from `Arithmetica4`
(`RHDirect.Stage8MertensTheorems` and `RHDirect.Stage8ExplicitPrimeBounds`) to prove:

## Unconditional Theorems (0 assumptions, 0 sorry, 0 axioms)
1. `isWeird_mul_of_sigma_sub_lt`: **Benkoski–Erdős Generalized Weird-Multiple Criterion** —
   if `w` is weird, `m ≥ 1`, `Nat.Coprime m w`, and `σ(w) * (σ(m) - m) < m`, then `w * m` is weird.
2. `isWeird_mul_prime_of_gt_sigma`: if `w` is weird and `p > σ(w)` is prime, then `w * p` is weird.
3. `infinite_isWeird`: `{n : ℕ | IsWeird n}.Infinite`.
4. `weird_positive_lower_density`: **Benkoski–Erdős (1974) Positive Lower Asymptotic Density of Weird Numbers**,
   powered by `RHDirect.Stage8MertensTheorems.mertens_third_theorem`.
5. `exists_weird_in_short_interval`: **Unconditional Effective Short-Interval Existence of Weird Numbers**
   in `(x, x + x * exp(-c * √(log x))]`, powered by `RHDirect.Stage8ExplicitPrimeBounds.exists_prime_short_interval_effective`.
6. All structural theorems (re-exported from `Prize.PPL086_Defs` and `Prize.PPL086_Constructions`):
   - `isPrimitiveWeird_iff_properDivisors_deficient`
   - `infinite_primitiveWeird_of_unbounded_min_odd_prime`
   - `odd_prime_gt_two_pow_of_even_weird`
   - `not_dvd_three_of_even_weird`
   - `three_le_card_primeFactors_of_isWeird` (universal for even OR odd weird numbers!)
   - `seven_le_card_primeFactors_of_odd_abundant_not_dvd_three` (Erdős #470 Part B)
   - `not_dvd_945_of_isWeird`
   - `isPrimitiveWeird_kravitz` (Kravitz 1976)
   - `isPrimitiveWeird_mersenne_partner`
   - `isPrimitiveWeird_melfi_sharp` (Sharp Melfi 2015)
   - `isPrimitiveWeird_70`, `isPrimitiveWeird_836`, `isPrimitiveWeird_7192`, `isPrimitiveWeird_4128448`

## Conditional Resolution of Erdős Problem #470 Part A
- `infinite_primitiveWeird_of_sqrt_prime_gap`: for any `0 < c` with `6 * c^2 < 1`
  (e.g., `c = 2/5`, sharpening Melfi's `1/10` by `4×`), `SqrtPrimeGap c → {n | IsPrimitiveWeird n}.Infinite`.
-/

namespace PPL086

open Finset Filter Topology

/-! ## Section 1: Benkoski–Erdős Generalized Weird-Multiple Criterion -/

/-- **Benkoski–Erdős Generalized Weird-Multiple Criterion (100% Unconditional):**
If `w` is weird, `0 < m`, `Nat.Coprime m w`, and `sigma w * (sigma m - m) < m`, then `w * m` is weird. -/
theorem isWeird_mul_of_sigma_sub_lt {w m : ℕ} (hw : IsWeird w) (hm : 0 < m)
    (hcop : Nat.Coprime m w) (hsmall : sigma w * (sigma m - m) < m) :
    IsWeird (w * m) := by
  have hw0 : 0 < w := hw.1.1
  have hwm0 : 0 < w * m := Nat.mul_pos hw0 hm
  have hsig_wm : sigma (w * m) = sigma w * sigma m := sigma_mul_of_coprime hcop.symm
  -- Step 1: Abundance
  have hab : IsAbundant (w * m) := by
    refine ⟨hwm0, ?_⟩
    rw [hsig_wm]
    have h1 : 2 * w ≤ sigma w := hw.1.2
    have h2 : m ≤ sigma m := le_sigma hm
    calc 2 * (w * m) = (2 * w) * m := by ring
      _ ≤ sigma w * sigma m := Nat.mul_le_mul h1 h2
  refine ⟨hab, ?_⟩
  -- Step 2: Non-pseudoperfectness
  rintro ⟨_, S, hS, hsum⟩
  set S₁ := S.filter (fun d => m ∣ d)
  set S₂ := S.filter (fun d => ¬ m ∣ d)
  have hsplit : ∑ d ∈ S₁, d + ∑ d ∈ S₂, d = w * m := by
    rw [Finset.sum_filter_add_sum_filter_not, hsum]
  -- Map `S₁` via `d ↦ d / m` to a subset `T ⊆ w.properDivisors`
  set T := S₁.image (fun d => d / m)
  have hS1_eq : ∑ d ∈ S₁, d = (∑ e ∈ T, e) * m := by
    rw [Finset.sum_mul, Finset.sum_image]
    · refine Finset.sum_congr rfl fun d hd => ?_
      exact (Nat.div_mul_cancel (Finset.mem_filter.mp hd).2).symm
    · intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      dsimp only at hxy
      rw [← Nat.div_mul_cancel hx', ← Nat.div_mul_cancel hy', hxy]
  have hT_sub : T ⊆ w.properDivisors := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨d, hd1, rfl⟩
    have ⟨hdS, hmd⟩ := Finset.mem_filter.mp hd1
    have hd_prop := Nat.mem_properDivisors.mp (hS hdS)
    obtain ⟨e', he'⟩ := hmd
    have he_eq : d / m = e' := by rw [he', Nat.mul_div_cancel_left _ hm]
    rw [he_eq]
    refine Nat.mem_properDivisors.mpr ⟨?_, ?_⟩
    · have hdvd : m * e' ∣ m * w := by rw [← he', mul_comm m w]; exact hd_prop.1
      exact (mul_dvd_mul_iff_left hm.ne').mp hdvd
    · have hlt : m * e' < m * w := by rw [← he', mul_comm m w]; exact hd_prop.2
      exact Nat.lt_of_mul_lt_mul_left hlt
  -- Since `w` is not pseudoperfect, `∑ e ∈ T, e ≠ w`, and since `(∑ e ∈ T, e) * m ≤ w * m`, `∑ e ∈ T, e ≤ w - 1`
  have hT_ne : ∑ e ∈ T, e ≠ w := fun heq => hw.2 ⟨hw0, T, hT_sub, heq⟩
  have hT_le : ∑ e ∈ T, e ≤ w := by
    have : (∑ e ∈ T, e) * m ≤ w * m := by omega
    exact Nat.le_of_mul_le_mul_right this hm
  have hS2_ge : m ≤ ∑ d ∈ S₂, d := by
    have hT_lt : ∑ e ∈ T, e + 1 ≤ w := by omega
    have : (∑ e ∈ T, e) * m + m ≤ w * m := by
      calc (∑ e ∈ T, e) * m + m = (∑ e ∈ T, e + 1) * m := by ring
        _ ≤ w * m := Nat.mul_le_mul_right m hT_lt
    omega
  -- Upper bound `∑ d ∈ S₂, d` via `(w * m).divisors \ w.divisors.image (· * m)`
  set I := w.divisors.image (fun e => e * m)
  have hI_sub : I ⊆ (w * m).divisors := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨e, he, rfl⟩
    exact Nat.mem_divisors.mpr ⟨mul_dvd_mul_right (Nat.dvd_of_mem_divisors he) m, hwm0.ne'⟩
  have hI_sum : ∑ d ∈ I, d = sigma w * m := by
    rw [Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_right hm h), ← Finset.sum_mul]
    rfl
  have hS2_sub : S₂ ⊆ (w * m).divisors \ I := by
    intro d hd2
    have ⟨hdS, hnmd⟩ := Finset.mem_filter.mp hd2
    refine Finset.mem_sdiff.mpr ⟨Nat.properDivisors_subset_divisors (hS hdS), ?_⟩
    intro hdI
    rcases Finset.mem_image.mp hdI with ⟨e, _, rfl⟩
    exact hnmd (dvd_mul_left m e)
  have hS2_le : ∑ d ∈ S₂, d ≤ sigma w * (sigma m - m) := by
    have h1 : ∑ d ∈ S₂, d ≤ ∑ d ∈ (w * m).divisors \ I, d := Finset.sum_le_sum_of_subset hS2_sub
    have h2 : ∑ d ∈ (w * m).divisors \ I, d + ∑ d ∈ I, d = sigma (w * m) :=
      Finset.sum_sdiff hI_sub
    have h3 : sigma w * m + sigma w * (sigma m - m) = sigma w * sigma m := by
      have hm_le : m ≤ sigma m := le_sigma hm
      rw [← mul_add, Nat.add_sub_of_le hm_le]
    omega
  omega

/-- If `w` is weird and `p` is prime with `sigma w < p`, then `w * p` is weird. -/
theorem isWeird_mul_prime_of_gt_sigma {w p : ℕ} (hw : IsWeird w) (hp : p.Prime)
    (hgt : sigma w < p) : IsWeird (w * p) := by
  have hw_lt_p : w < p := lt_of_le_of_lt (le_sigma hw.1.1) hgt
  have hcop : Nat.Coprime p w := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hw.1.1 hw_lt_p)
  refine isWeird_mul_of_sigma_sub_lt hw hp.pos hcop ?_
  rw [sigma_prime hp]
  simpa using hgt

/-- **Unconditional Infinitude of Weird Numbers:** `{n : ℕ | IsWeird n}.Infinite`. -/
theorem infinite_isWeird : {n : ℕ | IsWeird n}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨p, hge, hp⟩ := Nat.exists_infinite_primes (max N (sigma 70 + 1))
  have hpgt : sigma 70 < p := lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_right _ _) hge)
  have hp_ge_N : N ≤ p := le_trans (le_max_left _ _) hge
  refine ⟨70 * p, isWeird_mul_prime_of_gt_sigma isPrimitiveWeird_70.1 hp hpgt, ?_⟩
  have hp0 : 0 < p := hp.pos
  omega

lemma sigma_70 : sigma 70 = 144 := by
  have h := sigma_two_pow_mul_prime_mul_prime (k := 1) (p := 5) (q := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-! ## Section 2: Elementary Helpers for Benkoski–Erdős Positive Lower Density -/

/-- Totient of a squarefree product of primes `∏ p ∈ S, p` equals `∏ p ∈ S, (p - 1)`. -/
private lemma totient_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Nat.totient (∏ p ∈ S, p) = ∏ p ∈ S, (p - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    have hp_prime : p.Prime := hS p (Finset.mem_insert_self p s)
    have hs_primes : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hq_prime := hs_primes q hq
      have hne : p ≠ q := fun heq => hp (heq ▸ hq)
      exact (Nat.coprime_primes hp_prime hq_prime).mpr hne
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.totient_mul hcop,
        Nat.totient_prime hp_prime, ih hs_primes]

/-- Ratio `φ(P) / P = ∏_{p ∈ S} (1 - 1/p)` for `P = ∏_{p ∈ S} p` a product of primes. -/
private lemma totient_div_prod_primes_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ((Nat.totient (∏ p ∈ S, p) : ℝ) / ((∏ p ∈ S, p : ℕ) : ℝ)) =
      ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
  rw [totient_prod_primes S hS, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp_prime := hS p hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
  have hp1 : 1 ≤ p := hp_prime.one_le
  rw [Nat.cast_sub hp1, Nat.cast_one, sub_div, div_self hp_pos.ne', one_div]

/-- Counting integers in `[1, X]` coprime to `P`: `(X / P) * φ(P) ≤ |{m ∈ Icc 1 X | Coprime m P}|`. -/
private lemma card_coprime_Icc_ge {P X : ℕ} (hP : 0 < P) :
    (X / P) * Nat.totient P ≤ ((Finset.Icc 1 X).filter (fun m => Nat.Coprime m P)).card := by
  -- Map `(j, r) ∈ range (X / P) ×ˢ (range P).filter (Coprime · P)` to `j * P + (if r = 0 then P else r)`
  set U := (Finset.range P).filter (fun r => Nat.Coprime r P)
  have hU_card : U.card = Nat.totient P := by
    unfold Nat.totient U
    congr 1
    ext r
    simp [Nat.coprime_comm]
  set f : ℕ × ℕ → ℕ := fun jr => jr.1 * P + (if jr.2 = 0 then P else jr.2)
  have hf_maps : ∀ jr ∈ Finset.range (X / P) ×ˢ U,
      f jr ∈ (Finset.Icc 1 X).filter (fun m => Nat.Coprime m P) := by
    intro ⟨j, r⟩ hjr
    rcases Finset.mem_product.mp hjr with ⟨hj, hr⟩
    have hj_lt : j < X / P := Finset.mem_range.mp hj
    have ⟨hr_lt, hr_cop⟩ := Finset.mem_filter.mp hr
    have hr_lt' : r < P := Finset.mem_range.mp hr_lt
    simp only [f, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · split_ifs <;> omega
    · have hmul : (j + 1) * P ≤ (X / P) * P := Nat.mul_le_mul_right P (by omega)
      have hdiv : (X / P) * P ≤ X := Nat.div_mul_le_self X P
      split_ifs <;> nlinarith
    · split_ifs with hr0
      · subst hr0
        have hP1 : P = 1 := by simpa using hr_cop
        rw [hP1]; exact Nat.coprime_one_right _
      · rw [add_comm, mul_comm j P, Nat.coprime_add_mul_left_left]
        exact hr_cop
  have hf_inj : Set.InjOn f ((Finset.range (X / P) ×ˢ U : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro ⟨j₁, r₁⟩ h₁ ⟨j₂, r₂⟩ h₂ hfeq
    rcases Finset.mem_product.mp h₁ with ⟨_, hr₁⟩
    rcases Finset.mem_product.mp h₂ with ⟨_, hr₂⟩
    have hr₁_lt : r₁ < P := Finset.mem_range.mp (Finset.mem_filter.mp hr₁).1
    have hr₂_lt : r₂ < P := Finset.mem_range.mp (Finset.mem_filter.mp hr₂).1
    have hcop1 : Nat.Coprime r₁ P := (Finset.mem_filter.mp hr₁).2
    have hcop2 : Nat.Coprime r₂ P := (Finset.mem_filter.mp hr₂).2
    simp only [f] at hfeq
    by_cases hP1 : P = 1
    · subst hP1
      have : r₁ = 0 := by omega
      have : r₂ = 0 := by omega
      subst_vars; simp at hfeq; ext <;> omega
    · have hr1_ne : r₁ ≠ 0 := by
        intro h0; subst h0; simp at hcop1; exact hP1 hcop1
      have hr2_ne : r₂ ≠ 0 := by
        intro h0; subst h0; simp at hcop2; exact hP1 hcop2
      simp only [hr1_ne, hr2_ne, ↓reduceIte] at hfeq
      have hmod := congrArg (· % P) hfeq
      rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right,
          Nat.mod_eq_of_lt hr₁_lt, Nat.mod_eq_of_lt hr₂_lt] at hmod
      subst hmod
      have hj_eq : j₁ = j₂ := Nat.eq_of_mul_eq_mul_right hP (by omega)
      subst hj_eq; rfl
  have hcard := Finset.card_le_card_of_injOn f hf_maps hf_inj
  rw [Finset.card_product, Finset.card_range, hU_card] at hcard
  exact hcard

/-- Telescoping tail bound: `∑ e ∈ Icc (Y + 1) X, (1 / e^2 : ℝ) ≤ 1 / Y` for `Y ≥ 1`. -/
private lemma sum_inv_sq_Icc_le {Y : ℕ} (hY : 1 ≤ Y) (X : ℕ) :
    ∑ e ∈ Finset.Icc (Y + 1) X, ((e : ℝ)⁻¹) ^ 2 ≤ (Y : ℝ)⁻¹ := by
  induction X with
  | zero =>
    have hemp : Finset.Icc (Y + 1) 0 = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hemp, Finset.sum_empty]
    positivity
  | succ X ih =>
    by_cases hlt : X < Y
    · have hemp : Finset.Icc (Y + 1) (X + 1) = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hemp, Finset.sum_empty]
      positivity
    · -- Prove sharper telescoping bound `≤ 1 / Y - 1 / max Y (X + 1)`
      suffices htel : ∀ M : ℕ, Y ≤ M →
          ∑ e ∈ Finset.Icc (Y + 1) M, ((e : ℝ)⁻¹) ^ 2 ≤ (Y : ℝ)⁻¹ - (M : ℝ)⁻¹ by
        have := htel (X + 1) (by omega)
        have hpos : (0 : ℝ) ≤ ((X + 1 : ℕ) : ℝ)⁻¹ := by positivity
        linarith
      intro M hYM
      induction M, hYM using Nat.le_induction with
      | base =>
        have hemp : Finset.Icc (Y + 1) Y = ∅ := Finset.Icc_eq_empty (by omega)
        rw [hemp, Finset.sum_empty, sub_self]
      | succ k hk ihk =>
        have hsplit : Finset.Icc (Y + 1) (k + 1) = insert (k + 1) (Finset.Icc (Y + 1) k) := by
          ext e; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnot : k + 1 ∉ Finset.Icc (Y + 1) k := by simp
        rw [hsplit, Finset.sum_insert hnot]
        have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
        have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
        have hstep : (((k + 1 : ℕ) : ℝ)⁻¹) ^ 2 ≤ (k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹ := by
          have h1 : (k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹ = ((k : ℝ) * ((k + 1 : ℕ) : ℝ))⁻¹ := by
            push_cast
            field_simp
            ring
          rw [h1, sq, ← mul_inv]
          exact inv_anti₀ (by positivity) (by push_cast; nlinarith)
        linarith

/-- For any `m ≥ 1`, `(sigma m - m) / m = ∑ e ∈ m.divisors.filter (1 < ·), 1 / e`. -/
private lemma aliquotSum_div_eq_sum_inv_divisors {m : ℕ} (hm : 0 < m) :
    ((sigma m - m : ℕ) : ℝ) / (m : ℝ) =
      ∑ e ∈ m.divisors.filter (fun e => 1 < e), (e : ℝ)⁻¹ := by
  have hsig : sigma m - m = aliquotSum m := by
    rw [sigma_eq_aliquotSum_add hm]; omega
  rw [hsig]
  unfold aliquotSum
  rw [Nat.cast_sum, Finset.sum_div]
  -- Bijection `d ↦ m / d` from `m.properDivisors` to `m.divisors.filter (1 < ·)`
  refine Finset.sum_bij (fun d _ => m / d) ?_ ?_ ?_ ?_
  · intro d hd
    have ⟨hd_dvd, hd_lt⟩ := Nat.mem_properDivisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd hm
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd_dvd, hm.ne'⟩, ?_⟩
    have hmul : (m / d) * d = m := Nat.div_mul_cancel hd_dvd
    nlinarith
  · intro d₁ hd₁ d₂ hd₂ heq
    have h1 := Nat.div_mul_cancel (Nat.mem_properDivisors.mp hd₁).1
    have h2 := Nat.div_mul_cancel (Nat.mem_properDivisors.mp hd₂).1
    have hq_pos : 0 < m / d₁ := by
      have hd1_pos : 0 < d₁ := Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp hd₁).1 hm
      exact Nat.div_pos (le_of_lt (Nat.mem_properDivisors.mp hd₁).2) hd1_pos
    rw [heq] at h1
    exact Nat.eq_of_mul_eq_mul_left (heq ▸ hq_pos) (h1.trans h2.symm)
  · intro e he
    have ⟨he_div, he_gt1⟩ := Finset.mem_filter.mp he
    have he_dvd : e ∣ m := Nat.dvd_of_mem_divisors he_div
    refine ⟨m / e, Nat.mem_properDivisors.mpr ⟨Nat.div_dvd_of_dvd he_dvd, ?_⟩, ?_⟩
    · exact Nat.div_lt_self hm he_gt1
    · exact Nat.div_div_self he_dvd hm.ne'
  · intro d hd
    have hd_dvd := (Nat.mem_properDivisors.mp hd).1
    have hd_pos : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_dvd_of_pos hd_dvd hm
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hmul : ((m / d : ℕ) : ℝ) * (d : ℝ) = (m : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hd_dvd
    have hq_pos : (0 : ℝ) < ((m / d : ℕ) : ℝ) := by nlinarith
    rw [div_eq_iff hm_pos.ne', eq_inv_mul_iff_mul_eq₀ hq_pos.ne']
    exact hmul

/-- Number of multiples of `e ≥ 1` in `Icc 1 X` is at most `X / e`. -/
private lemma card_multiples_Icc_le {e X : ℕ} (he : 0 < e) :
    ((Finset.Icc 1 X).filter (fun m => e ∣ m)).card ≤ X / e := by
  have hmaps : ∀ m ∈ (Finset.Icc 1 X).filter (fun m => e ∣ m), m / e ∈ Finset.Icc 1 (X / e) := by
    intro m hm
    have ⟨hm_icc, hem⟩ := Finset.mem_filter.mp hm
    have ⟨hm1, hmX⟩ := Finset.mem_Icc.mp hm_icc
    refine Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hmX⟩
    have hm_ge_e : e ≤ m := Nat.le_of_dvd (by omega) hem
    exact Nat.div_pos hm_ge_e he
  have hinj : Set.InjOn (fun m => m / e) (((Finset.Icc 1 X).filter (fun m => e ∣ m) : Finset ℕ) : Set ℕ) := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    dsimp only at hxy
    rw [← Nat.div_mul_cancel hx', ← Nat.div_mul_cancel hy', hxy]
  have hcard := Finset.card_le_card_of_injOn (fun m => m / e) hmaps hinj
  simpa [Nat.card_Icc] using hcard

/-! ## Section 3: Benkoski–Erdős (1974) Positive Lower Asymptotic Density of Weird Numbers -/

open Classical in
/-- **BENKOSKI–ERDŐS (1974) — POSITIVE LOWER ASYMPTOTIC DENSITY OF WEIRD NUMBERS (UNCONDITIONAL!):**
Powered by `RHDirect.Stage8MertensTheorems.mertens_third_theorem`, there exists `c > 0` and `N₀`
such that for all `N ≥ N₀`, at least `c * N` integers in `[1, N]` are weird! -/
theorem weird_positive_lower_density :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ≤ (((Finset.Icc 1 N).filter IsWeird).card : ℝ) := by
  -- Step 1: Use Mertens' Third Theorem from Arithmetica4 to pick `Y ≥ 10` with `288 / Y < ∏_{p ≤ Y} (1 - 1/p)`
  have hm3 := RHDirect.Stage8MertensTheorems.mertens_third_theorem
  set C₀ : ℝ := Real.exp (-Real.eulerMascheroniConstant)
  have hC0_pos : 0 < C₀ := Real.exp_pos _
  have hev1 : ∀ᶠ x : ℝ in atTop, C₀ / 2 < Real.log x *
      ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 - (p : ℝ)⁻¹) :=
    hm3.eventually (Ioi_mem_nhds (by linarith : C₀ / 2 < C₀))
  have hlog_div : Tendsto (fun x : ℝ => (288 : ℝ) * (Real.log x / x)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using h0.const_mul (288 : ℝ)
  have hev2 : ∀ᶠ x : ℝ in atTop, (288 : ℝ) * (Real.log x / x) < C₀ / 2 :=
    hlog_div.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < C₀ / 2))
  have hev3 : ∀ᶠ x : ℝ in atTop, (10 : ℝ) ≤ x := eventually_ge_atTop 10
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp (hev1.and (hev2.and hev3))
  set Y : ℕ := max 10 ⌈Y₀⌉₊ with hY_def
  have hY_ge10 : 10 ≤ Y := le_max_left _ _
  have hY_ge_Y0 : Y₀ ≤ (Y : ℝ) := le_trans (Nat.le_ceil Y₀) (by exact_mod_cast le_max_right 10 ⌈Y₀⌉₊)
  have ⟨hMert, hLog, _⟩ := hY₀ (Y : ℝ) hY_ge_Y0
  have hfloorY : ⌊(Y : ℝ)⌋₊ = Y := Nat.floor_natCast Y
  rw [hfloorY] at hMert
  have hlogY_pos : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Y))
  have hY_pos : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  set S : Finset ℕ := (Finset.Icc 1 Y).filter Nat.Prime
  set P : ℕ := ∏ p ∈ S, p
  have hS_primes : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hP_pos : 0 < P := Finset.prod_pos fun p hp => (hS_primes p hp).pos
  set α : ℝ := (Nat.totient P : ℝ) / (P : ℝ)
  have hα_eq : α = ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := totient_div_prod_primes_eq S hS_primes
  have hα_gt : (288 : ℝ) / (Y : ℝ) < α := by
    rw [hα_eq]
    have h1 : (288 : ℝ) * (Real.log (Y : ℝ) / (Y : ℝ)) < Real.log (Y : ℝ) * ∏ p ∈ S, (1 - (p : ℝ)⁻¹) :=
      lt_trans hLog hMert
    have h2 : (288 : ℝ) * (Real.log (Y : ℝ) / (Y : ℝ)) = Real.log (Y : ℝ) * ((288 : ℝ) / (Y : ℝ)) := by ring
    rw [h2] at h1
    exact lt_of_mul_lt_mul_left h1 hlogY_pos.le
  have hα_pos : 0 < α := lt_trans (by positivity) hα_gt
  -- Step 2: Set density constant `c = α / 280` and threshold `N₀`
  set c : ℝ := α / 280
  have hc_pos : 0 < c := by positivity
  -- Choose `N₀` large enough that `(α / 2) * (N / 70 - 1) - φ(P) ≥ (α / 280) * N`
  -- i.e. `(α / 280) * N ≥ α / 2 + φ(P)`, so `N₀ = ⌈280 * (1 + φ(P) / α)⌉₊ + 140` suffices!
  set N₀ : ℕ := ⌈280 * (1 + (Nat.totient P : ℝ) / α)⌉₊ + 140
  refine ⟨c, hc_pos, N₀, fun N hN => ?_⟩
  set X : ℕ := N / 70
  set R : Finset ℕ := (Finset.Icc 1 X).filter (fun m => Nat.Coprime m P)
  set B : Finset ℕ := R.filter (fun m => m ≤ 144 * (sigma m - m))
  set G : Finset ℕ := R \ B
  -- Lower bound `|R|`
  have hR_card : α * (X : ℝ) - (Nat.totient P : ℝ) ≤ (R.card : ℝ) := by
    have h1 : (((X / P) * Nat.totient P : ℕ) : ℝ) ≤ (R.card : ℝ) := by
      exact_mod_cast card_coprime_Icc_ge hP_pos
    rw [Nat.cast_mul] at h1
    have hP_pos_r : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP_pos
    have hdiv : (X : ℝ) / (P : ℝ) - 1 ≤ ((X / P : ℕ) : ℝ) := by
      have hlt : X < (X / P + 1) * P := by
        have := Nat.div_add_mod X P
        have := Nat.mod_lt X hP_pos
        nlinarith
      have hlt_r : (X : ℝ) < ((X / P : ℕ) : ℝ) * (P : ℝ) + (P : ℝ) := by
        exact_mod_cast (show X < (X / P) * P + P by nlinarith)
      rw [sub_le_iff_le_add, div_le_iff₀ hP_pos_r]
      linarith
    have htot_nonneg : (0 : ℝ) ≤ (Nat.totient P : ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hdiv htot_nonneg
    have hα_X : α * (X : ℝ) = (X : ℝ) / (P : ℝ) * (Nat.totient P : ℝ) := by
      dsimp only [α]; ring
    linarith
  -- Upper bound `|B|` via Markov's inequality on `∑_{m ∈ R} (σ(m) - m) / m ≤ X / Y`
  have hsum_le : ∑ m ∈ R, ((sigma m - m : ℕ) : ℝ) / (m : ℝ) ≤ (X : ℝ) / (Y : ℝ) := by
    have hterm_le : ∀ m ∈ R, ((sigma m - m : ℕ) : ℝ) / (m : ℝ) ≤
        ∑ e ∈ (Finset.Icc (Y + 1) X).filter (fun e => e ∣ m), (e : ℝ)⁻¹ := by
      intro m hm
      have ⟨hm_icc, hm_cop⟩ := Finset.mem_filter.mp hm
      have ⟨hm1, hmX⟩ := Finset.mem_Icc.mp hm_icc
      rw [aliquotSum_div_eq_sum_inv_divisors (by omega)]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
      intro e he
      have ⟨he_div, he_gt1⟩ := Finset.mem_filter.mp he
      have he_dvd : e ∣ m := Nat.dvd_of_mem_divisors he_div
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, le_trans (Nat.le_of_dvd (by omega) he_dvd) hmX⟩, he_dvd⟩
      -- Every prime factor `p ∣ e` satisfies `p > Y` (else `p ∣ P`, contradicting `Coprime m P`)
      obtain ⟨p, hp_prime, hpe⟩ := Nat.exists_prime_and_dvd (by omega : e ≠ 1)
      have hpm : p ∣ m := dvd_trans hpe he_dvd
      have hp_gt_Y : Y < p := by
        by_contra hle
        have hp_mem_S : p ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_prime.one_le, by omega⟩, hp_prime⟩
        have hpP : p ∣ P := Finset.dvd_prod_of_mem _ hp_mem_S
        have hp_dvd_gcd : p ∣ Nat.gcd m P := Nat.dvd_gcd hpm hpP
        rw [hm_cop] at hp_dvd_gcd
        exact hp_prime.not_dvd_one hp_dvd_gcd
      have hpe_le : p ≤ e := Nat.le_of_dvd (by omega) hpe
      omega
    calc ∑ m ∈ R, ((sigma m - m : ℕ) : ℝ) / (m : ℝ)
        ≤ ∑ m ∈ R, ∑ e ∈ (Finset.Icc (Y + 1) X).filter (fun e => e ∣ m), (e : ℝ)⁻¹ :=
          Finset.sum_le_sum hterm_le
      _ = ∑ m ∈ R, ∑ e ∈ Finset.Icc (Y + 1) X, if e ∣ m then (e : ℝ)⁻¹ else 0 := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_filter]
      _ = ∑ e ∈ Finset.Icc (Y + 1) X, ∑ m ∈ R, if e ∣ m then (e : ℝ)⁻¹ else 0 := Finset.sum_comm
      _ = ∑ e ∈ Finset.Icc (Y + 1) X, ((R.filter (fun m => e ∣ m)).card : ℝ) * (e : ℝ)⁻¹ := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ e ∈ Finset.Icc (Y + 1) X, ((X : ℝ) / (e : ℝ)) * (e : ℝ)⁻¹ := by
          refine Finset.sum_le_sum fun e he => ?_
          have he_pos : 0 < e := by have := (Finset.mem_Icc.mp he).1; omega
          have hsub : R.filter (fun m => e ∣ m) ⊆ (Finset.Icc 1 X).filter (fun m => e ∣ m) :=
            Finset.filter_subset_filter _ (Finset.filter_subset _ _)
          have hcard : (R.filter (fun m => e ∣ m)).card ≤ X / e :=
            le_trans (Finset.card_le_card hsub) (card_multiples_Icc_le he_pos)
          have hcard_r : ((R.filter (fun m => e ∣ m)).card : ℝ) ≤ (X : ℝ) / (e : ℝ) := by
            have h1 : ((R.filter (fun m => e ∣ m)).card : ℝ) ≤ ((X / e : ℕ) : ℝ) := by exact_mod_cast hcard
            have h2 : ((X / e : ℕ) : ℝ) ≤ (X : ℝ) / (e : ℝ) := Nat.cast_div_le
            exact le_trans h1 h2
          exact mul_le_mul_of_nonneg_right hcard_r (by positivity)
      _ = (X : ℝ) * ∑ e ∈ Finset.Icc (Y + 1) X, ((e : ℝ)⁻¹) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => by ring
      _ ≤ (X : ℝ) * (Y : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le (by omega) X) (Nat.cast_nonneg X)
      _ = (X : ℝ) / (Y : ℝ) := by rw [div_eq_mul_inv]
  have hB_card : (B.card : ℝ) ≤ (144 : ℝ) * ((X : ℝ) / (Y : ℝ)) := by
    have hmarkov : (B.card : ℝ) * (144 : ℝ)⁻¹ ≤ ∑ m ∈ B, ((sigma m - m : ℕ) : ℝ) / (m : ℝ) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun m hm => ?_
      have ⟨hmR, hmbad⟩ := Finset.mem_filter.mp hm
      have hm_pos : (0 : ℝ) < (m : ℝ) := by
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmR).1).1
        exact_mod_cast (by omega : 0 < m)
      rw [inv_eq_one_div, div_le_div_iff₀ (by norm_num) hm_pos, one_mul]
      exact_mod_cast (by omega : m ≤ (sigma m - m) * 144)
    have hsub : ∑ m ∈ B, ((sigma m - m : ℕ) : ℝ) / (m : ℝ) ≤
        ∑ m ∈ R, ((sigma m - m : ℕ) : ℝ) / (m : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    linarith
  -- Inject `G = R \ B` into `(Icc 1 N).filter IsWeird` via `m ↦ 70 * m`
  have hG_maps : ∀ m ∈ G, 70 * m ∈ (Finset.Icc 1 N).filter IsWeird := by
    intro m hm
    have ⟨hmR, hm_notB⟩ := Finset.mem_sdiff.mp hm
    have ⟨hm_icc, hm_copP⟩ := Finset.mem_filter.mp hmR
    have ⟨hm1, hmX⟩ := Finset.mem_Icc.mp hm_icc
    have hm_good : 144 * (sigma m - m) < m := by
      by_contra hge
      exact hm_notB (Finset.mem_filter.mpr ⟨hmR, by omega⟩)
    -- `Coprime m 70` follows from `Coprime m P` since `2, 5, 7 ∈ S`
    have h70_dvd_P : 70 ∣ P := by
      have h2 : 2 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩, by norm_num⟩
      have h5 : 5 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩, by norm_num⟩
      have h7 : 7 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩, by norm_num⟩
      have h2P : 2 ∣ P := Finset.dvd_prod_of_mem _ h2
      have h5P : 5 ∣ P := Finset.dvd_prod_of_mem _ h5
      have h7P : 7 ∣ P := Finset.dvd_prod_of_mem _ h7
      have h10P : 10 ∣ P := (by norm_num : Nat.Coprime 2 5).mul_dvd_of_dvd_of_dvd h2P h5P
      exact (by norm_num : Nat.Coprime 10 7).mul_dvd_of_dvd_of_dvd h10P h7P
    have hm_cop70 : Nat.Coprime m 70 := hm_copP.coprime_dvd_right h70_dvd_P
    have hweird : IsWeird (70 * m) :=
      isWeird_mul_of_sigma_sub_lt isPrimitiveWeird_70.1 (by omega) hm_cop70 (by rw [sigma_70]; exact hm_good)
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hweird⟩
    calc 70 * m ≤ 70 * (N / 70) := Nat.mul_le_mul_left 70 hmX
      _ ≤ N := Nat.mul_div_le N 70
  have hG_inj : Set.InjOn (fun m => 70 * m) (G : Set ℕ) :=
    fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hG_le : (G.card : ℝ) ≤ (((Finset.Icc 1 N).filter IsWeird).card : ℝ) := by
    exact_mod_cast Finset.card_le_card_of_injOn (fun m => 70 * m) hG_maps hG_inj
  -- Combine `|G| = |R| - |B|` with the bounds on `|R|`, `|B|`, and `X = N / 70`
  have hB_sub_R : B ⊆ R := Finset.filter_subset _ _
  have hG_card : (R.card : ℝ) - (B.card : ℝ) = (G.card : ℝ) := by
    have hnat : G.card + B.card = R.card := by
      rw [Finset.card_sdiff_add_card_eq_card hB_sub_R]
    have hreal : (G.card : ℝ) + (B.card : ℝ) = (R.card : ℝ) := by exact_mod_cast hnat
    linarith
  have hX_ge : (N : ℝ) / 70 - 1 ≤ (X : ℝ) := by
    have hlt : N < (N / 70 + 1) * 70 := by
      have := Nat.div_add_mod N 70
      have := Nat.mod_lt N (by norm_num : 0 < 70)
      omega
    have hlt_r : (N : ℝ) < ((X : ℝ) + 1) * 70 := by exact_mod_cast hlt
    linarith
  have hN_ge : 280 * (1 + (Nat.totient P : ℝ) / α) ≤ (N : ℝ) := by
    have h1 : 280 * (1 + (Nat.totient P : ℝ) / α) ≤ (⌈280 * (1 + (Nat.totient P : ℝ) / α)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : (⌈280 * (1 + (Nat.totient P : ℝ) / α)⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : ⌈280 * (1 + (Nat.totient P : ℝ) / α)⌉₊ ≤ N)
    linarith
  have hstep1 : (α / 2) * (X : ℝ) - (Nat.totient P : ℝ) ≤ (G.card : ℝ) := by
    have hcoef : (144 : ℝ) / (Y : ℝ) ≤ α / 2 := by
      have : (288 : ℝ) / (Y : ℝ) = 2 * ((144 : ℝ) / (Y : ℝ)) := by ring
      linarith
    have hmul : (144 : ℝ) * ((X : ℝ) / (Y : ℝ)) ≤ (α / 2) * (X : ℝ) := by
      have hX_nonneg : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
      calc (144 : ℝ) * ((X : ℝ) / (Y : ℝ)) = ((144 : ℝ) / (Y : ℝ)) * (X : ℝ) := by ring
        _ ≤ (α / 2) * (X : ℝ) := mul_le_mul_of_nonneg_right hcoef hX_nonneg
    linarith
  have hstep2 : (α / 280) * (N : ℝ) ≤ (α / 2) * ((N : ℝ) / 70 - 1) - (Nat.totient P : ℝ) := by
    have hmul_α := mul_le_mul_of_nonneg_left hN_ge hα_pos.le
    have hsimp : α * (280 * (1 + (Nat.totient P : ℝ) / α)) = 280 * α + 280 * (Nat.totient P : ℝ) := by
      field_simp [hα_pos.ne']
    linarith
  have hstep3 : (α / 2) * ((N : ℝ) / 70 - 1) ≤ (α / 2) * (X : ℝ) :=
    mul_le_mul_of_nonneg_left hX_ge (by positivity)
  have hc_eq : c * (N : ℝ) = (α / 280) * (N : ℝ) := rfl
  linarith

/-! ## Section 4: Unconditional Effective Short-Interval Existence of Weird Numbers -/

/-- **UNCONDITIONAL EFFECTIVE SHORT-INTERVAL EXISTENCE OF WEIRD NUMBERS (0 ASSUMPTIONS!):**
Powered by `RHDirect.Stage8ExplicitPrimeBounds.exists_prime_short_interval_effective`,
there exist `c > 0` and `X₀` such that for all `x ≥ X₀`, there is a weird number `n` in
`(x, x + x * exp(-c * √(log x))]`. -/
theorem exists_weird_in_short_interval :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x →
      ∃ n : ℕ, IsWeird n ∧ x < (n : ℝ) ∧
        (n : ℝ) ≤ x + x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c₀, hc₀, X₁, hshort⟩ := RHDirect.Stage8ExplicitPrimeBounds.exists_prime_short_interval_effective
  set c : ℝ := c₀ / Real.sqrt 2
  have hc_pos : 0 < c := div_pos hc₀ (Real.sqrt_pos.mpr (by norm_num))
  refine ⟨c, hc_pos, max (70 * max X₁ 145) (70 ^ 2), fun x hx => ?_⟩
  have hx1 : 70 * max X₁ 145 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (70 : ℝ) ^ 2 ≤ x := le_trans (le_max_right _ _) hx
  have hy_ge_X1 : X₁ ≤ x / 70 := by
    have : X₁ ≤ max X₁ 145 := le_max_left _ _
    linarith
  have hy_ge_145 : (145 : ℝ) ≤ x / 70 := by
    have : (145 : ℝ) ≤ max X₁ 145 := le_max_right _ _
    linarith
  obtain ⟨p, hp, hlt_p, hp_le⟩ := hshort (x / 70) hy_ge_X1
  have hp_gt_144 : sigma 70 < p := by
    rw [sigma_70]
    have : (144 : ℝ) < (p : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨70 * p, isWeird_mul_prime_of_gt_sigma isPrimitiveWeird_70.1 hp hp_gt_144, ?_, ?_⟩
  · push_cast; linarith
  · have hx_pos : 0 < x := by linarith
    have hlog_ge : (1 / 2 : ℝ) * Real.log x ≤ Real.log (x / 70) := by
      rw [Real.log_div hx_pos.ne' (by norm_num)]
      have hlog70 : Real.log 70 ≤ (1 / 2 : ℝ) * Real.log x := by
        have h1 : Real.log ((70 : ℝ) ^ 2) ≤ Real.log x := Real.log_le_log (by positivity) hx2
        rw [Real.log_pow] at h1
        push_cast at h1
        linarith
      linarith
    have hsqrt_ge : Real.sqrt (Real.log x) / Real.sqrt 2 ≤ Real.sqrt (Real.log (x / 70)) := by
      have h1 : Real.sqrt ((1 / 2 : ℝ) * Real.log x) ≤ Real.sqrt (Real.log (x / 70)) :=
        Real.sqrt_le_sqrt hlog_ge
      rw [Real.sqrt_mul (by norm_num), one_div, Real.sqrt_inv, inv_mul_eq_div] at h1
      exact h1
    have hexp_le : Real.exp (-c₀ * Real.sqrt (Real.log (x / 70))) ≤
        Real.exp (-c * Real.sqrt (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      have hmul : c * Real.sqrt (Real.log x) = c₀ * (Real.sqrt (Real.log x) / Real.sqrt 2) := by
        dsimp only [c]; ring
      nlinarith
    have h70p : ((70 * p : ℕ) : ℝ) ≤ x + x * Real.exp (-c₀ * Real.sqrt (Real.log (x / 70))) := by
      push_cast
      linarith
    have hmul_x : x * Real.exp (-c₀ * Real.sqrt (Real.log (x / 70))) ≤
        x * Real.exp (-c * Real.sqrt (Real.log x)) :=
      mul_le_mul_of_nonneg_left hexp_le hx_pos.le
    linarith

/-! ## Axiom Audit for All Headline Theorems -/

#print axioms isPrimitiveWeird_iff_properDivisors_deficient
#print axioms infinite_primitiveWeird_of_unbounded_min_odd_prime
#print axioms odd_prime_gt_two_pow_of_even_weird
#print axioms not_dvd_three_of_even_weird
#print axioms three_le_card_primeFactors_of_isWeird
#print axioms seven_le_card_primeFactors_of_odd_abundant_not_dvd_three
#print axioms not_dvd_945_of_isWeird
#print axioms isPrimitiveWeird_kravitz
#print axioms isPrimitiveWeird_mersenne_partner
#print axioms isPrimitiveWeird_melfi_sharp
#print axioms infinite_primitiveWeird_of_sqrt_prime_gap
#print axioms infinite_primitiveWeird_of_two_fifths_sqrt_prime_gap
#print axioms isPrimitiveWeird_70
#print axioms isPrimitiveWeird_836
#print axioms isPrimitiveWeird_7192
#print axioms isPrimitiveWeird_4128448
#print axioms isWeird_mul_of_sigma_sub_lt
#print axioms isWeird_mul_prime_of_gt_sigma
#print axioms infinite_isWeird
#print axioms weird_positive_lower_density
#print axioms exists_weird_in_short_interval

end PPL086
