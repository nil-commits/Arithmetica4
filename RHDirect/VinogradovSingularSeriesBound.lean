import RHDirect.VinogradovSingularSeries
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Vinogradov — Wave 2b: uniform positive lower bound for the singular series (odd n)

The three-prime singular series is the Euler product `𝔖(n) = ∏_p (1 − c_p(n)/(p−1)³)`.
For odd `n` every local factor is positive (Wave 2a), and the partial products are
uniformly bounded below by a positive constant: the odd-prime factors dominate
`∏ (1 − 1/(p−1)²)`, whose Weierstrass lower bound `1 − ∑ 1/(p−1)²` is controlled by
the convergent tail `∑_{m≥2} 1/m² = π²/6 − 1 < 1`. No `sorry`, no custom axioms.
-/

open Real Complex Finset MeasureTheory intervalIntegral

set_option linter.style.haveILetI false

namespace RHDirect.Vinogradov

noncomputable section

/-- Finite Weierstrass product inequality: `∏ (1 − fᵢ) ≥ 1 − ∑ fᵢ` for `fᵢ ∈ [0,1]`. -/
theorem prod_one_sub_ge_one_sub_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  revert h0 h1
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih h0 h1
    have h0s : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert.mpr (Or.inr hi))
    have h1s : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_insert.mpr (Or.inr hi))
    have h0a : 0 ≤ f a := h0 a (Finset.mem_insert.mpr (Or.inl rfl))
    have h1a : f a ≤ 1 := h1 a (Finset.mem_insert.mpr (Or.inl rfl))
    have ihs := ih h0s h1s
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    have hfac : 0 ≤ 1 - f a := by linarith
    have hcross : 0 ≤ f a * ∑ i ∈ s, f i :=
      mul_nonneg h0a (Finset.sum_nonneg (fun i hi => h0s i hi))
    nlinarith [mul_le_mul_of_nonneg_left ihs hfac]

/-- The convergent tail `∑_{m≥2} 1/m²`, indexed as `j ↦ 1/(j+2)²`. -/
def zetaTail2 (j : ℕ) : ℝ := 1 / ((j + 2) : ℝ) ^ 2

theorem summable_one_div_nat_sq : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) := by
  have h := (summable_nat_pow_inv (p := 2)).mpr (by norm_num : 1 < 2)
  convert h using 1
  ext n
  exact (inv_eq_one_div _).symm

theorem summable_zetaTail2 : Summable zetaTail2 := by
  have h := (summable_nat_pow_inv (p := 2)).mpr (by norm_num : 1 < 2)
  have hs := (summable_nat_add_iff 2).mpr h
  refine hs.congr (fun j => ?_)
  simp only [zetaTail2]
  field_simp
  push_cast
  ring

theorem tsum_zetaTail2 : ∑' j, zetaTail2 j = Real.pi ^ 2 / 6 - 1 := by
  have hsplit := summable_one_div_nat_sq.sum_add_tsum_nat_add 2
  have hsum2 : ∑ i ∈ Finset.range 2, (1 / ((i : ℝ) ^ 2)) = 1 := by
    norm_num [Finset.sum_range_succ]
  have htsum : ∑' n : ℕ, 1 / ((n : ℝ) ^ 2) = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
  rw [hsum2, htsum] at hsplit
  have hcong : (∑' j, (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) (j + 2)) = ∑' j, zetaTail2 j := by
    congr 1
    ext j
    simp [zetaTail2]
  rw [hcong] at hsplit
  linarith

/-- For an odd prime `p`, the local factor dominates `1 − 1/(p−1)²`. -/
theorem singularLocalFactor_ge_one_sub (p n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ singularLocalFactor p n := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpm : (2 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    linarith
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  simp only [singularLocalFactor]
  split_ifs with hdiv
  · have hfrac : ((p : ℝ) - 1) / ((p : ℝ) - 1) ^ 3 = 1 / ((p : ℝ) - 1) ^ 2 := by
      field_simp [hne]
    linarith
  · have hpos : 0 ≤ 1 / ((p : ℝ) - 1) ^ 3 := by
      apply div_nonneg zero_le_one
      exact pow_nonneg (by linarith) 3
    have hsub : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
      apply div_nonneg zero_le_one
      exact pow_nonneg (by linarith) 2
    have hneg : (-1 : ℝ) / ((p : ℝ) - 1) ^ 3 = -(1 / ((p : ℝ) - 1) ^ 3) := by ring
    rw [hneg]
    linarith

/-- The odd-prime sum is bounded by the convergent zeta tail. -/
theorem sum_odd_prime_inv_sq_le (X : ℕ) :
    ∑ p ∈ (Finset.range (X + 1)).filter (fun p => Nat.Prime p ∧ p ≠ 2),
        1 / ((p : ℝ) - 1) ^ 2 ≤ ∑' j, zetaTail2 j := by
  let s := (Finset.range (X + 1)).filter (fun p => Nat.Prime p ∧ p ≠ 2)
  have hp3 : ∀ p ∈ s, 3 ≤ p := by
    intro p hp
    have hprime := (Finset.mem_filter.mp hp).2.1
    have hne2 := (Finset.mem_filter.mp hp).2.2
    have := hprime.two_le
    omega
  have hterm : ∀ p ∈ s, 1 / ((p : ℝ) - 1) ^ 2 = zetaTail2 (p - 3) := by
    intro p hp
    have h3 := hp3 p hp
    have harg : ((p - 3 : ℕ) : ℝ) + 2 = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 3 ≤ p)]
      ring
    simp only [zetaTail2, harg]
  have hinj : Set.InjOn (fun p : ℕ => p - 3) s := by
    intro p hp q hq heq
    have := congrArg (· + 3) heq
    rw [Nat.sub_add_cancel (hp3 p hp), Nat.sub_add_cancel (hp3 q hq)] at this
    exact this
  calc ∑ p ∈ s, 1 / ((p : ℝ) - 1) ^ 2
      = ∑ p ∈ s, zetaTail2 (p - 3) := by
        apply Finset.sum_congr rfl; intro p hp; exact hterm p hp
    _ = ∑ j ∈ s.image (fun p => p - 3), zetaTail2 j := by
        rw [← Finset.sum_image hinj]
    _ ≤ ∑' j, zetaTail2 j :=
        summable_zetaTail2.sum_le_tsum _ (fun j _ => div_nonneg zero_le_one (sq_nonneg _))

/-- The positive constant lower-bounding the singular series for odd `n`. -/
theorem singular_series_constant_pos : 0 < 2 * (2 - Real.pi ^ 2 / 6) := by
  have hpi2 : Real.pi ^ 2 < 12 := by
    have := Real.pi_lt_d4
    norm_num at this ⊢
    nlinarith [Real.pi_pos]
  have : Real.pi ^ 2 / 6 < 2 := by linarith
  linarith

/-- Uniform positive lower bound on the singular-series partial products for odd `n`. -/
theorem singularPartialProd_lower_bound {n : ℕ} (hn : Odd n) (X : ℕ) (hX : 2 ≤ X) :
    2 * (2 - Real.pi ^ 2 / 6) ≤
      ∏ p ∈ (Finset.range (X + 1)).filter Nat.Prime, singularLocalFactor p n := by
  let s := (Finset.range (X + 1)).filter Nat.Prime
  let sodd := s.filter (fun p => p ≠ 2)
  have h2s : 2 ∈ s := by
    simp only [s, Finset.mem_filter]
    refine ⟨?_, Nat.prime_two⟩
    rw [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr hX
  have hsplit : s = insert 2 sodd := by
    have hsodd : sodd = s.erase 2 := by
      ext p
      simp only [sodd, Finset.mem_filter, Finset.mem_erase]
      tauto
    rw [hsodd]
    exact (Finset.insert_erase h2s).symm
  have h2not : 2 ∉ sodd := by simp [sodd]
  have hprod : ∏ p ∈ s, singularLocalFactor p n =
      singularLocalFactor 2 n * ∏ p ∈ sodd, singularLocalFactor p n := by
    rw [hsplit, Finset.prod_insert h2not]
  rw [hprod, singularLocalFactor_two_of_odd hn]
  have hp3odd : ∀ p ∈ sodd, 3 ≤ p := by
    intro p hp
    have hps : p ∈ s := (Finset.mem_filter.mp hp).1
    have hne2 : p ≠ 2 := (Finset.mem_filter.mp hp).2
    have hprime : p.Prime := (Finset.mem_filter.mp hps).2
    have := hprime.two_le
    omega
  have hpm_of : ∀ p ∈ sodd, (2 : ℝ) ≤ (p : ℝ) - 1 := by
    intro p hp
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3odd p hp
    linarith
  have hge : ∏ p ∈ sodd, (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤
      ∏ p ∈ sodd, singularLocalFactor p n := by
    apply Finset.prod_le_prod
    · intro p hp
      have hsq : 1 ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith [hpm_of p hp]
      have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hsq
      linarith
    · intro p hp
      have hne2 : p ≠ 2 := (Finset.mem_filter.mp hp).2
      have hps : p ∈ s := (Finset.mem_filter.mp hp).1
      have hprime : p.Prime := (Finset.mem_filter.mp hps).2
      haveI : Fact p.Prime := ⟨hprime⟩
      exact singularLocalFactor_ge_one_sub p n hne2
  have hweier : 1 - ∑ p ∈ sodd, 1 / ((p : ℝ) - 1) ^ 2 ≤
      ∏ p ∈ sodd, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    apply prod_one_sub_ge_one_sub_sum
    · intro p hp; positivity
    · intro p hp
      have hsq : 1 ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith [hpm_of p hp]
      exact (div_le_one (by positivity)).mpr hsq
  have hsumle : ∑ p ∈ sodd, 1 / ((p : ℝ) - 1) ^ 2 ≤ ∑' j, zetaTail2 j := by
    have hfeq : sodd = (Finset.range (X + 1)).filter (fun p => Nat.Prime p ∧ p ≠ 2) := by
      ext p
      simp only [s, sodd, Finset.mem_filter]
      tauto
    rw [hfeq]
    exact sum_odd_prime_inv_sq_le X
  have hprod_ge : 2 - Real.pi ^ 2 / 6 ≤ ∏ p ∈ sodd, singularLocalFactor p n := by
    calc 2 - Real.pi ^ 2 / 6
        = 1 - (Real.pi ^ 2 / 6 - 1) := by ring
      _ = 1 - ∑' j, zetaTail2 j := by rw [tsum_zetaTail2]
      _ ≤ 1 - ∑ p ∈ sodd, 1 / ((p : ℝ) - 1) ^ 2 := sub_le_sub_left hsumle 1
      _ ≤ ∏ p ∈ sodd, (1 - 1 / ((p : ℝ) - 1) ^ 2) := hweier
      _ ≤ ∏ p ∈ sodd, singularLocalFactor p n := hge
  nlinarith

end

#print axioms RHDirect.Vinogradov.singularPartialProd_lower_bound
#print axioms RHDirect.Vinogradov.singular_series_constant_pos

end RHDirect.Vinogradov
