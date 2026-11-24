import RHDirect.VinogradovParseval

/-!
# Vinogradov — Wave 2: Ramanujan sums and the prime local factor of the singular series

The singular series for three primes is `𝔖(n) = ∑_q (μ(q)/φ(q))³ c_q(n)` with
Ramanujan sum `c_q(n) = ∑_{a mod q, (a,q)=1} e(an/q)`. Its Euler-product local
factor at a prime `p` is governed by `c_p(n) = if p ∣ n then p−1 else −1`.

This module defines `ramanujanSum` on native Mathlib objects and proves the prime
case via the geometric-sum / roots-of-unity identity. No `sorry`, no custom axioms.
-/

open Real Complex Finset MeasureTheory intervalIntegral

namespace RHDirect.Vinogradov

noncomputable section

/-- `e(a·x) = e(x)^a` for a natural multiplier. -/
theorem e_natCast_mul (x : ℝ) (a : ℕ) : e ((a : ℝ) * x) = e x ^ a := by
  induction a with
  | zero => simp [e]
  | succ a ih =>
    rw [Nat.cast_succ, add_mul, one_mul, e_add, ih, pow_succ]

/-- `e(x) = 1` iff `x` is an integer. -/
theorem e_eq_one_iff (x : ℝ) : e x = 1 ↔ ∃ k : ℤ, x = k := by
  simp only [e]
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    use k
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    have hcx : (x : ℂ) = (k : ℂ) := by
      apply mul_left_cancel₀ hne
      push_cast at hk ⊢
      linear_combination hk
    exact_mod_cast hcx
  · rintro ⟨k, rfl⟩
    use k
    push_cast
    ring

/-- Ramanujan sum `c_q(n) = ∑_{a<q, (a,q)=1} e(an/q)`. -/
def ramanujanSum (q n : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    e (((a : ℝ) * (n : ℝ)) / (q : ℝ))

/-- The full roots-of-unity sum `∑_{a<p} e(an/p) = if p ∣ n then p else 0`. -/
theorem sum_e_div_prime (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (∑ a ∈ Finset.range p, e (((a : ℝ) * (n : ℝ)) / (p : ℝ))) =
      if p ∣ n then (p : ℂ) else 0 := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  by_cases hdiv : p ∣ n
  · simp only [hdiv, ite_true]
    have hterm : ∀ a ∈ Finset.range p, e (((a : ℝ) * (n : ℝ)) / (p : ℝ)) = 1 := by
      intro a _
      obtain ⟨k, hk⟩ := hdiv
      rw [hk]
      have harg : ((a : ℝ) * ((p * k : ℕ) : ℝ)) / (p : ℝ) = ((a * k : ℕ) : ℝ) := by
        push_cast
        field_simp [hp0]
      rw [harg]
      exact e_intCast (a * k)
    rw [Finset.sum_congr rfl hterm]
    simp
  · simp only [hdiv, ite_false]
    set z := e ((n : ℝ) / (p : ℝ)) with hz
    have hterm : ∀ a ∈ Finset.range p, e (((a : ℝ) * (n : ℝ)) / (p : ℝ)) = z ^ a := by
      intro a _
      have harg : ((a : ℝ) * (n : ℝ)) / (p : ℝ) = (a : ℝ) * ((n : ℝ) / (p : ℝ)) := by ring
      rw [harg, e_natCast_mul, hz]
    rw [Finset.sum_congr rfl hterm]
    have hzp : z ^ p = 1 := by
      rw [hz, ← e_natCast_mul]
      have harg : (p : ℝ) * ((n : ℝ) / (p : ℝ)) = (n : ℝ) := by field_simp [hp0]
      rw [harg]
      exact e_intCast n
    have hz1 : z ≠ 1 := by
      intro hzone
      apply hdiv
      rw [hz, e_eq_one_iff] at hzone
      obtain ⟨k, hk⟩ := hzone
      -- n / p = k, so n = p * k; k ≥ 0 since n / p ≥ 0
      have hknonneg : 0 ≤ k := by
        have : 0 ≤ (n : ℝ) / (p : ℝ) := div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg p)
        rw [hk] at this
        exact_mod_cast this
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hknonneg
      use m
      have hnp : (n : ℝ) = (p : ℝ) * (k : ℝ) := by
        field_simp [hp0] at hk ⊢
        linarith
      rw [hm] at hnp
      exact_mod_cast hnp
    have hgeom := geom_sum_mul z p
    rw [hzp, sub_self] at hgeom
    have hzne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    exact (mul_eq_zero.mp hgeom).resolve_right hzne

/-- Prime Ramanujan sum: `c_p(n) = if p ∣ n then p−1 else −1`. -/
theorem ramanujanSum_prime (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ramanujanSum p n = if p ∣ n then ((p : ℂ) - 1) else -1 := by
  have hp : p.Prime := Fact.out
  -- the coprime residues mod p are exactly 1..p-1
  have hfilter : (Finset.range p).filter (fun a => Nat.Coprime a p) = Finset.Ico 1 p := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨ha, hcop⟩
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0, Nat.coprime_zero_left] at hcop
        exact hp.ne_one hcop
      exact ⟨Nat.pos_of_ne_zero ha0, ha⟩
    · rintro ⟨h1, ha⟩
      refine ⟨ha, ?_⟩
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hdvd
      have : p ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.ne_of_gt h1)) hdvd
      omega
  simp only [ramanujanSum, hfilter]
  -- ∑_{a∈Ico 1 p} = ∑_{a∈range p} − (a=0 term)
  have hsplit : (∑ a ∈ Finset.Ico 1 p, e (((a : ℝ) * (n : ℝ)) / (p : ℝ))) =
      (∑ a ∈ Finset.range p, e (((a : ℝ) * (n : ℝ)) / (p : ℝ))) - 1 := by
    have hrange' : Finset.range p = insert 0 (Finset.Ico 1 p) := by
      ext a
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      constructor
      · intro h
        by_cases ha0 : a = 0
        · exact Or.inl ha0
        · exact Or.inr ⟨Nat.pos_of_ne_zero ha0, h⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact hp.pos
        · exact h2
    have h0notin : (0 : ℕ) ∉ Finset.Ico 1 p := by simp
    have hsum : (∑ a ∈ Finset.range p, e (((a : ℝ) * (n : ℝ)) / (p : ℝ))) =
        1 + ∑ a ∈ Finset.Ico 1 p, e (((a : ℝ) * (n : ℝ)) / (p : ℝ)) := by
      rw [hrange', Finset.sum_insert h0notin]
      simp [e]
    linear_combination -hsum
  rw [hsplit, sum_e_div_prime]
  split_ifs with h
  · ring
  · ring

/-- The Euler-product local factor of the three-prime singular series at a prime `p`:
`1 − c_p(n)/(p−1)³`, using `c_p(n) = if p ∣ n then p−1 else −1`. -/
def singularLocalFactor (p n : ℕ) : ℝ :=
  1 - (if p ∣ n then (p : ℝ) - 1 else -1) / ((p : ℝ) - 1) ^ 3

/-- At `p = 2` and odd `n`, the local factor is `2`. -/
theorem singularLocalFactor_two_of_odd {n : ℕ} (hn : Odd n) :
    singularLocalFactor 2 n = 2 := by
  have h2n : ¬ 2 ∣ n := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have hmod : n % 2 = 1 := Nat.odd_iff.mp hn
    omega
  simp only [singularLocalFactor, h2n, ite_false]
  norm_num

/-- For odd `n`, every prime local factor is strictly positive. -/
theorem singularLocalFactor_pos_of_odd {n : ℕ} (hn : Odd n) (p : ℕ) [Fact p.Prime] :
    0 < singularLocalFactor p n := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  by_cases h2 : p = 2
  · subst h2
    rw [singularLocalFactor_two_of_odd hn]
    norm_num
  · have hp3 : 3 ≤ p := by omega
    have hpm1 : (2 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      linarith
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    simp only [singularLocalFactor]
    split_ifs with hdiv
    · -- p ∣ n: factor = 1 − 1/(p−1)² ≥ 3/4 > 0
      have hfrac : ((p : ℝ) - 1) / ((p : ℝ) - 1) ^ 3 = 1 / ((p : ℝ) - 1) ^ 2 := by
        field_simp [hne]
      rw [hfrac]
      have hsq : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by
        nlinarith
      have hle : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 :=
        one_div_le_one_div_of_le (by positivity) hsq
      linarith
    · -- p ∤ n: factor = 1 + 1/(p−1)³ > 0
      have hpos : 0 < ((p : ℝ) - 1) ^ 3 := by positivity
      have : 1 - (-1 : ℝ) / ((p : ℝ) - 1) ^ 3 = 1 + 1 / ((p : ℝ) - 1) ^ 3 := by ring
      rw [this]
      positivity

end

#print axioms RHDirect.Vinogradov.ramanujanSum_prime
#print axioms RHDirect.Vinogradov.singularLocalFactor_pos_of_odd

end RHDirect.Vinogradov
